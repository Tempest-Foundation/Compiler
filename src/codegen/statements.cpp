#include "internal.hpp"

namespace stellac {

void Codegen::emit_active_defers(size_t retain_depth, FnDecl &ctx, Module &m) {
	if (retain_depth > defer_scopes_.size()) {
		return;
	}
	for (size_t depth = defer_scopes_.size(); depth > retain_depth; --depth) {
		for (Stmt *defer_body : defer_scopes_[depth - 1].active) {
			if (defer_body) {
				emit_stmt(*defer_body, ctx, m);
			}
		}
	}
}

void Codegen::emit_stmt(Stmt &s, FnDecl &ctx, Module &m) {
	auto &B = *builder_;
	switch (s.kind) {
	case StmtKind::Block: {
		bool dead = B.GetInsertBlock() == sink_block_;
		local_stack_.emplace_back();
		defer_scopes_.emplace_back();
		for (auto &st : s.body) {
			emit_stmt(*st, ctx, m);
		}
		if (!dead && B.GetInsertBlock() != sink_block_) {
			emit_active_defers(defer_scopes_.size() - 1, ctx, m);
		}
		defer_scopes_.pop_back();
		local_stack_.pop_back();
		return;
	}
	case StmtKind::ExprStmt:
		if (s.expr) {
			(void)emit_expr(*s.expr, ctx, m);
			// A noreturn call must terminate its containing basic block.
			bool nonreturn_call = s.expr->kind == ExprKind::Call && s.expr->resolved_fn &&
								  has_negated_attr(s.expr->resolved_fn->attrs, "return");
			if (nonreturn_call && !B.GetInsertBlock()->hasTerminator()) {
				B.CreateUnreachable();
				if (!sink_block_) {
					sink_block_ = llvm::BasicBlock::Create(l_.ctx(), "dead", cur_fn(ctx));
				}
				B.SetInsertPoint(sink_block_);
			}
		}
		return;
	case StmtKind::VarDecl:
	case StmtKind::ConstDecl: {
		for (auto &var : s.vars) {
			StType *ty =
				var.resolved ? var.resolved : (var.ty ? sema_.resolve_type(*var.ty, m) : nullptr);
			if (!ty && var.init) {
				StType *ity = underlying_type(var.init->ty);
				ty			= ity;
			}
			if (!ty) {
				ty = t_.void_ty();
			}
			llvm::Type	*lt	  = map_type(ty);
			llvm::Value *slot = nullptr;
			if (var.is_static || var.is_thread_local) {
				const std::string name = fn_symbol_name(ctx) + ".static.local." +
					std::to_string(static_local_counter_++) + "." + var.name;
				llvm::Constant *init = var.init
									  ? lower_const_expr(*var.init, m, ty, lt, name)
									  : nullptr;
				if (var.init && !init) {
					log::report(log::Level::Error, var.init->loc,
								"static local initializer is not a compile-time constant");
				}
				auto *gv = new llvm::GlobalVariable(
					l_.module(), lt, !var.is_mutable || var.is_const,
					llvm::GlobalValue::InternalLinkage,
					init ? init : llvm::Constant::getNullValue(lt), name);
				if (var.is_thread_local) {
					gv->setThreadLocal(true);
				}
				gv->setAlignment(storage_align(ty, lt));
				apply_global_attrs(gv, var.attrs);
				slot = gv;
			} else {
				slot = alloca_in_entry_typed(ty, lt, var.name.c_str());
			}
			if (underlying_type(ty) && underlying_type(ty)->kind == TypeKind::VaList) {
				va_list_storage_[&var] = slot;
			}
			if (var.init && !var.is_static && !var.is_thread_local) {
				StType *uty = underlying_type(ty);
				if (var.init->kind == ExprKind::ArrayLit && uty && uty->kind == TypeKind::Array) {
					StType					  *elem_ty = underlying_type(uty->base);
					llvm::Type				  *elem_lt = map_type(elem_ty);
					// Emit each element once. If every element is an LLVM constant
					// whose type already matches the array element type, collapse
					// zero-init + N per-element stores into a single
					// `store ConstantArray` into the slot (slot remains mutable).
					std::vector<llvm::Value *> vals;
					vals.reserve(var.init->args.size());
					bool all_const = !var.init->args.empty();
					for (auto &arg : var.init->args) {
						llvm::Value *v = emit_expr(*arg, ctx, m);
						vals.push_back(v);
						if (!llvm::isa<llvm::Constant>(v) || v->getType() != elem_lt) {
							all_const = false;
						}
					}
					if (all_const) {
						auto						 *arrTy = llvm::cast<llvm::ArrayType>(lt);
						std::vector<llvm::Constant *> consts;
						consts.reserve(arrTy->getNumElements());
						for (auto *v : vals) {
							consts.push_back(llvm::cast<llvm::Constant>(v));
						}
						while (consts.size() < arrTy->getNumElements()) {
							consts.push_back(llvm::ConstantAggregateZero::get(elem_lt));
						}
						B.CreateStore(llvm::ConstantArray::get(arrTy, consts), slot);
					} else {
						B.CreateStore(llvm::ConstantAggregateZero::get(lt), slot);
						llvm::Type *index_ty = l_.llvm_int(t_.pointer_width());
						for (size_t i = 0; i < var.init->args.size(); ++i) {
							llvm::Value *elem	  = vals[i];
							llvm::Type	*elem_vty = elem->getType();
							if (elem_vty != elem_lt) {
								if (elem_vty->isIntegerTy() && elem_lt->isIntegerTy()) {
									unsigned from = elem_vty->getIntegerBitWidth();
									unsigned to	  = elem_lt->getIntegerBitWidth();
									if (from > to) {
										elem = B.CreateTrunc(elem, elem_lt);
									} else {
										elem = B.CreateZExt(elem, elem_lt);
									}
								}
							}
							llvm::Value *ptr = B.CreateInBoundsGEP(
								lt, slot,
								{llvm::ConstantInt::get(index_ty, 0),
								 llvm::ConstantInt::get(index_ty, static_cast<uint64_t>(i), false)},
								"arr.init");
							B.CreateStore(elem, ptr);
						}
					}
				} else {
					StType *uty = underlying_type(ty);
					const bool is_agg = uty && (uty->kind == TypeKind::Struct ||
												uty->kind == TypeKind::Union ||
												uty->kind == TypeKind::Array);
					llvm::Value *src_addr = is_agg ? emit_lvalue(*var.init, ctx, m) : nullptr;
					if (src_addr) {
						auto &dl = l_.module().getDataLayout();
						uint64_t sz = dl.getTypeAllocSize(lt);
						StType *src_st = underlying_type(var.init->ty);
						llvm::Align dst_align = pointer_align(slot, ty, lt);
						llvm::Align src_align = pointer_align(src_addr, src_st, map_type(src_st));
						B.CreateMemCpy(slot, dst_align, src_addr, src_align, sz,
									   is_volatile_access(*var.init));
					} else {
						llvm::Value *v		= emit_expr(*var.init, ctx, m);
						StType		*src_st = underlying_type(var.init->ty);
						store_value(slot, v, ty, src_st, s.loc);
					}
				}
			}
			if (var.name != "_") {
				local_stack_.back().emplace(var.name, LocalVal{slot, ty, true});
			}
		}
		return;
	}
	case StmtKind::Defer:
		if (!defer_scopes_.empty() && s.defer_body) {
			defer_scopes_.back().active.push_back(s.defer_body.get());
		}
		return;
	case StmtKind::If: {
		if (s.cond && s.cond->is_const_bool) {
			bool val = s.cond->const_bool_val;
			if (val) {
				if (s.then_block) {
					emit_stmt(*s.then_block, ctx, m);
				}
			} else {
				if (s.else_block) {
					emit_stmt(*s.else_block, ctx, m);
				}
			}
			return;
		}
		llvm::Value *c =
			s.cond ? emit_expr(*s.cond, ctx, m) : llvm::ConstantInt::get(l_.llvm_bool(), 1);
		c						  = coerce_cond(B, c);
		llvm::Function	 *fn	  = cur_fn(ctx);
		llvm::BasicBlock *thenBB  = llvm::BasicBlock::Create(l_.ctx(), "then", fn);
		llvm::BasicBlock *mergeBB = llvm::BasicBlock::Create(l_.ctx(), "merge", fn);
		llvm::BasicBlock *elseBB =
			s.else_block ? llvm::BasicBlock::Create(l_.ctx(), "else", fn) : nullptr;
		B.CreateCondBr(c, thenBB, elseBB ? elseBB : mergeBB);

		B.SetInsertPoint(thenBB);
		if (s.then_block) {
			emit_stmt(*s.then_block, ctx, m);
		}
		br_or_absorb(B, mergeBB);

		if (elseBB) {
			B.SetInsertPoint(elseBB);
			if (s.else_block) {
				emit_stmt(*s.else_block, ctx, m);
			}
			br_or_absorb(B, mergeBB);
		}
		B.SetInsertPoint(mergeBB);
		return;
	}
	case StmtKind::For: {
		llvm::Function *fn = cur_fn(ctx);
		local_stack_.emplace_back();
		if (s.for_init) {
			emit_stmt(*s.for_init, ctx, m);
		}
		llvm::BasicBlock *condBB = llvm::BasicBlock::Create(l_.ctx(), "fcond", fn);
		llvm::BasicBlock *bodyBB = llvm::BasicBlock::Create(l_.ctx(), "fbody", fn);
		llvm::BasicBlock *stepBB = llvm::BasicBlock::Create(l_.ctx(), "fstep", fn);
		llvm::BasicBlock *endBB	 = llvm::BasicBlock::Create(l_.ctx(), "fend", fn);
		B.CreateBr(condBB);
		B.SetInsertPoint(condBB);
		if (s.for_cond) {
			llvm::Value *c = emit_expr(*s.for_cond, ctx, m);
			c			   = coerce_cond(B, c);
			B.CreateCondBr(c, bodyBB, endBB);
		} else {
			B.CreateBr(bodyBB);
		}
		B.SetInsertPoint(bodyBB);
		size_t loop_defer_depth = defer_scopes_.size();
		break_stack_.push_back({endBB, loop_defer_depth});
		continue_stack_.push_back({stepBB, loop_defer_depth});
		if (s.loop_body) {
			emit_stmt(*s.loop_body, ctx, m);
		}
		continue_stack_.pop_back();
		break_stack_.pop_back();
		br_or_absorb(B, stepBB);
		B.SetInsertPoint(stepBB);
		if (s.for_step) {
			(void)emit_expr(*s.for_step, ctx, m);
		}
		B.CreateBr(condBB);
		B.SetInsertPoint(endBB);
		local_stack_.pop_back();
		return;
	}
	case StmtKind::Switch: {
		llvm::Function *fn	  = cur_fn(ctx);
		llvm::Value	   *scrut = s.scrutinee ? emit_expr(*s.scrutinee, ctx, m) : nullptr;
		if (!scrut) {
			return;
		}
		llvm::Type					   *scrut_t = scrut->getType();

		llvm::BasicBlock			   *endBB = llvm::BasicBlock::Create(l_.ctx(), "sw.end", fn);
		llvm::BasicBlock			   *defaultBB = endBB;
		std::vector<llvm::BasicBlock *> armBBs;
		std::vector<std::pair<llvm::ConstantInt *, llvm::BasicBlock *>> cases;

		// Pre-create arm blocks so the switch instruction can reference them.
		for (auto &arm : s.arms) {
			llvm::BasicBlock *armBB =
				llvm::BasicBlock::Create(l_.ctx(), arm.is_default ? "sw.default" : "sw.case", fn);
			armBBs.push_back(armBB);
			if (arm.is_default) {
				defaultBB = armBB;
			} else {
				llvm::ConstantInt *cv = nullptr;
				if (arm.case_expr && contains_layout_intrinsic(*arm.case_expr)) {
					auto *value = llvm::dyn_cast<llvm::ConstantInt>(emit_expr(*arm.case_expr, ctx, m));
					if (!value) {
						log::report(log::Level::Error, arm.loc,
									"layout-dependent switch case is not an integer constant");
						continue;
					}
					llvm::APInt bits = value->getValue();
					StType *case_st = underlying_type(arm.case_expr->ty);
					if (case_st && case_st->kind == TypeKind::Enum) {
						case_st = underlying_type(case_st->base);
					}
					const bool case_is_unsigned = case_st && case_st->kind == TypeKind::UInt;
					const unsigned dest_width = llvm::cast<llvm::IntegerType>(scrut_t)->getBitWidth();
					StType *scrutinee_type = underlying_type(s.scrutinee->ty);
					if (scrutinee_type && scrutinee_type->kind == TypeKind::Enum) {
						scrutinee_type = underlying_type(scrutinee_type->base);
					}
					const bool dest_is_unsigned =
						scrutinee_type && scrutinee_type->kind == TypeKind::UInt;
					const bool fits = dest_is_unsigned
						? (case_is_unsigned ? bits.isIntN(dest_width)
														: !bits.isNegative() && bits.isIntN(dest_width))
						: (case_is_unsigned ? bits.getActiveBits() < dest_width
													: bits.isSignedIntN(dest_width));
					if (!fits) {
						log::report(log::Level::Error, arm.loc,
									"case value out of range for switch scrutinee");
					}
					cv = llvm::cast<llvm::ConstantInt>(llvm::ConstantInt::get(scrut_t, bits));
				} else {
					cv = llvm::cast<llvm::ConstantInt>(
						llvm::ConstantInt::get(scrut_t, (uint64_t)arm.case_value, true));
				}
				if (std::any_of(cases.begin(), cases.end(), [cv](const auto &entry) {
						return entry.first->getValue() == cv->getValue();
					})) {
					log::report(log::Level::Error, arm.loc, "duplicate case value in switch");
					continue;
				}
				cases.emplace_back(cv, armBB);
			}
		}

		// The LLVM 'switch' -- single instruction; mid-end lowers to jump table
		// / balanced tree / bit test per the case density.
		auto *sw = B.CreateSwitch(scrut, defaultBB, cases.size());
		for (auto &[cv, bb] : cases) {
			sw->addCase(cv, bb);
		}

		// Push break target so inner 'break' jumps to sw.end.
		size_t switch_defer_depth = defer_scopes_.size();
		break_stack_.push_back({endBB, switch_defer_depth});

		// Emit each arm. No fallthrough: every arm body terminates with an
		// explicit `br endBB` if it didn't already terminate
		// (return/break/unreachable). A break/return mid-body leaves the builder on
		// a synthetic empty dead block (no predecessors). Detect it and erase it
		// instead of adding a spurious `br endBB` that would leave an unreachable
		// block in the IR.
		for (size_t i = 0; i < s.arms.size(); ++i) {
			B.SetInsertPoint(armBBs[i]);
			if (s.arms[i].body) {
				emit_stmt(*s.arms[i].body, ctx, m);
			}
			br_or_absorb(B, endBB);
		}

		break_stack_.pop_back();
		B.SetInsertPoint(endBB);
		return;
	}
	case StmtKind::Return:
		// `return noreturn_call()` has no return instruction to emit
		if (s.ret_val && s.ret_val->kind == ExprKind::Call && s.ret_val->resolved_fn &&
			has_negated_attr(s.ret_val->resolved_fn->attrs, "return")) {
			(void)emit_expr(*s.ret_val, ctx, m);
			if (!B.GetInsertBlock()->hasTerminator()) {
				B.CreateUnreachable();
			}
			if (!sink_block_) {
				sink_block_ = llvm::BasicBlock::Create(l_.ctx(), "dead", cur_fn(ctx));
			}
			B.SetInsertPoint(sink_block_);
			return;
		}
		if (s.ret_val) {
			Expr *previous_abi_result_expr = abi_result_expr_;
			if (has_attr(ctx.attrs, "must_tail") && s.ret_val->kind == ExprKind::Call) {
				abi_result_expr_ = s.ret_val.get();
			}
			llvm::Value *val = emit_expr(*s.ret_val, ctx, m);
			abi_result_expr_ = previous_abi_result_expr;
			llvm::CallInst *must_tail_call = nullptr;
			if (has_attr(ctx.attrs, "must_tail") && s.ret_val->kind == ExprKind::Call) {
				must_tail_call = llvm::dyn_cast<llvm::CallInst>(val);
				if (must_tail_call) {
					must_tail_call->setTailCallKind(llvm::CallInst::TCK_MustTail);
				}
			}
			StType	   *ret_ty	= ctx.fn_sig
									  ? ctx.fn_sig->fn_ret
									  : (ctx.ret ? sema_.resolve_type(*ctx.ret, m) : t_.void_ty());
			llvm::Type *ret_fty = map_abi_type(ret_ty);
			if (val->getType() != ret_fty) {
				if (ret_fty->isIntegerTy() && val->getType()->isIntegerTy()) {
					unsigned dst_bits = ret_fty->getIntegerBitWidth();
					unsigned src_bits = val->getType()->getIntegerBitWidth();
					if (src_bits < dst_bits) {
						StType *ret_u = underlying_type(ret_ty);
						bool	ret_unsigned =
							ret_u && (ret_u->kind == TypeKind::UInt ||
									  (ret_u->kind == TypeKind::Enum && underlying_type(ret_u->base) &&
									   underlying_type(ret_u->base)->kind == TypeKind::UInt));
						val =
							ret_unsigned ? B.CreateZExt(val, ret_fty) : B.CreateSExt(val, ret_fty);
					} else if (src_bits > dst_bits) {
						val = B.CreateTrunc(val, ret_fty);
					}
				} else if (ret_fty->isPointerTy() && val->getType()->isIntegerTy()) {
					val = B.CreateIntToPtr(val, ret_fty);
				} else if (ret_fty->isIntegerTy() && val->getType()->isPointerTy()) {
					val = B.CreatePtrToInt(val, ret_fty);
					} else {
						val = to_abi_value(val, ret_fty);
					}
				}
				emit_active_defers(0, ctx, m);
				if (B.GetInsertBlock() == sink_block_) {
					return;
				}
				B.CreateRet(val);
			} else {
				emit_active_defers(0, ctx, m);
				if (B.GetInsertBlock() == sink_block_) {
					return;
				}
				B.CreateRetVoid();
		}
		{
			// Park the builder on the per-function sink block instead of
			// allocating a fresh "ret.dead" BB on every return. The sink is
			// lazily created and either recycled across multiple returns or
			// erased (and reset to null) by absorb_dead_fallthrough at a
			// subsequent merge point.
			if (!sink_block_) {
				sink_block_ = llvm::BasicBlock::Create(l_.ctx(), "dead", cur_fn(ctx));
			}
			B.SetInsertPoint(sink_block_);
		}
		return;
	case StmtKind::Break:
		if (!break_stack_.empty()) {
			const ControlTarget target = break_stack_.back();
			emit_active_defers(target.defer_scope_depth, ctx, m);
			if (B.GetInsertBlock() != sink_block_ && !B.GetInsertBlock()->hasTerminator()) {
				B.CreateBr(target.target);
			}
		} else {
			B.CreateUnreachable();
		}
		{
			if (!sink_block_) {
				sink_block_ = llvm::BasicBlock::Create(l_.ctx(), "dead", cur_fn(ctx));
			}
			B.SetInsertPoint(sink_block_);
		}
		return;
	case StmtKind::Unreachable:
		if (B.GetInsertBlock() != sink_block_ && !B.GetInsertBlock()->hasTerminator()) {
			B.CreateUnreachable();
		}
		if (!sink_block_) {
			sink_block_ = llvm::BasicBlock::Create(l_.ctx(), "dead", cur_fn(ctx));
		}
		B.SetInsertPoint(sink_block_);
		return;
	case StmtKind::Continue:
		if (!continue_stack_.empty()) {
			const ControlTarget target = continue_stack_.back();
			emit_active_defers(target.defer_scope_depth, ctx, m);
			if (B.GetInsertBlock() != sink_block_ && !B.GetInsertBlock()->hasTerminator()) {
				B.CreateBr(target.target);
			}
		} else {
			B.CreateUnreachable();
		}
		{
			if (!sink_block_) {
				sink_block_ = llvm::BasicBlock::Create(l_.ctx(), "dead", cur_fn(ctx));
			}
			B.SetInsertPoint(sink_block_);
		}
		return;
	case StmtKind::Yield: {
		if (block_expr_stack_.empty() || !s.ret_val) {
			log::report(log::Level::Error, s.loc,
						"internal compiler error: invalid yield reached codegen",
						"E_CODEGEN_FAILURE", "backend");
			return;
		}
		llvm::Value *value = emit_expr(*s.ret_val, ctx, m);
		auto &state = block_expr_stack_.back();
		emit_active_defers(state.defer_scope_depth, ctx, m);
		if (B.GetInsertBlock() == sink_block_ || B.GetInsertBlock()->hasTerminator()) {
			return;
		}
		state.values.emplace_back(value, B.GetInsertBlock());
		B.CreateBr(state.merge);
		llvm::BasicBlock *dead = llvm::BasicBlock::Create(l_.ctx(), "yield.dead", cur_fn(ctx));
		sink_block_ = dead;
		B.SetInsertPoint(dead);
		return;
	}
	case StmtKind::Asm:
		emit_asm(s, ctx, m);
		return;
	default:
		return;
	}
}

} // namespace stellac