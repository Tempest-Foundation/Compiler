#include "internal.hpp"

#include <array>

namespace stellac {

llvm::Value *Codegen::emit_lvalue(Expr &e, FnDecl &ctx, Module &m) {
	auto &B = *builder_;
	switch (e.kind) {
	case ExprKind::Ident: {
		Module &expr_module = e.binding_module ? *e.binding_module : m;
		if (e.path.size() == 1) {
			if (ctx.generic_const_subst.count(e.path[0])) {
				return llvm::ConstantInt::get(
					map_type(e.ty), static_cast<uint64_t>(ctx.generic_const_subst.at(e.path[0])),
					false);
			}
			if (ctx.generic_const_string_subst.count(e.path[0])) {
				return cstring_global(ctx.generic_const_string_subst.at(e.path[0]),
									  ".generic.const");
			}
			const bool allow_local_lookup = !e.binding_module || e.macro_argument ||
				e.path[0].rfind("$macro.", 0) == 0;
			if (allow_local_lookup) {
				if (auto *lv = find_local(e.path[0])) {
				if (lv->is_addr) {
					return lv->val;
				}
				// value (e.g. param-by-value never happens since we alloca), fallback
				return lv->val;
				}
			}
		}
		// global var/const
		std::vector<std::string> segs = expr_module.mod_path;
		segs.push_back(e.path.back());
		std::string nm = mangle(segs);
		auto		it = globals_.find(nm);
		if (it == globals_.end()) {
			nm += private_global_scope_suffix(expr_module);
			it = globals_.find(nm);
		}
		if (it != globals_.end()) {
			ensure_tls_initialized(B, nm);
			return it->second;
		}
		// try cross-module
		Symbol *sym = sema_.resolve_path(e.path, expr_module);
		if (sym && (sym->kind == SymKind::Var || sym->kind == SymKind::Const)) {
			auto git = globals_.find(sym->mangled);
			if (git != globals_.end()) {
				ensure_tls_initialized(B, sym->mangled);
				return git->second;
			}
		}
		return nullptr;
	}
	case ExprKind::Member: {
		Module &expr_module = e.binding_module ? *e.binding_module : m;
		if (!e.lhs) {
			return nullptr;
		}
		std::vector<std::string> qualified_path;
		if (flatten_member_path(e, qualified_path) && qualified_path.size() >= 2) {
			if (Symbol *sym = sema_.resolve_path(qualified_path, expr_module)) {
				if ((sym->kind == SymKind::Var || sym->kind == SymKind::Const) &&
					globals_.count(sym->mangled)) {
					ensure_tls_initialized(B, sym->mangled);
					return globals_[sym->mangled];
				}
			}
		}
		llvm::Value *base = nullptr;
		StType		*bt	  = e.lhs->ty;
		bt				  = underlying_type(bt);
		if (bt && bt->kind == TypeKind::Pointer) {
			// Load pointer layers until the final pointer points at the aggregate.
			// Preserve that last pointer value for the field GEP rather than
			// loading the aggregate itself.
			base = emit_expr(*e.lhs, ctx, m);
			while (bt && bt->kind == TypeKind::Pointer) {
				StType *pointee = underlying_type(bt->base);
				if (pointee &&
					(pointee->kind == TypeKind::Struct || pointee->kind == TypeKind::Union)) {
					bt = pointee;
					break;
				}
				if (!pointee || pointee->kind != TypeKind::Pointer || !base) {
					return nullptr;
				}
				auto *load = B.CreateLoad(map_type(pointee), base, "autoref");
				load->setVolatile(bt->is_volatile);
				base = load;
				bt	 = pointee;
			}
		} else {
			base = emit_lvalue(*e.lhs, ctx, m);
			if (!base && bt && (bt->kind == TypeKind::Struct || bt->kind == TypeKind::Union)) {
				llvm::Value *value = emit_expr(*e.lhs, ctx, m);
				llvm::Value *tmp   = alloca_in_entry_typed(bt, map_type(bt), "member.tmp");
				B.CreateStore(value, tmp);
				base = tmp;
			}
		}
		if (!base || !bt || (bt->kind != TypeKind::Struct && bt->kind != TypeKind::Union)) {
			return nullptr;
		}
		if (bt->kind == TypeKind::Union) {
			size_t idx = field_index(bt, e.member);
			return idx == SIZE_MAX ? nullptr : base;
		}
		llvm::StructType *st  = llvm::cast<llvm::StructType>(map_type(bt));
		size_t			  idx = field_index(bt, e.member);
		if (idx == SIZE_MAX) {
			return nullptr;
		}
		// GEP expects the struct pointer as a pointer, which base already is
		// (either from emit_lvalue for non-pointer bases, or from emit_expr
		// for pointer bases).
		return B.CreateStructGEP(st, base, (unsigned)idx, "fld");
	}
	case ExprKind::Index: {
		if (!e.lhs || !e.rhs) {
			return nullptr;
		}
		llvm::Value *idx = emit_expr(*e.rhs, ctx, m);
		StType		*bt	 = underlying_type(e.lhs->ty);
		if (bt && bt->kind == TypeKind::Array) {
			// Array indexing: arr[i] -> GEP(arr_ptr, 0, idx)
			llvm::Value *base = emit_lvalue(*e.lhs, ctx, m);
			if (!base) {
				if (e.lhs->is_addressable) {
					return nullptr;
				}
				llvm::Value *array_value = emit_expr(*e.lhs, ctx, m);
				if (!array_value) {
					return nullptr;
				}
				base = alloca_in_entry_typed(bt, map_type(bt), "array.tmp");
				B.CreateStore(array_value, base);
			}
			llvm::Type *arrTy		 = map_type(bt);
			const auto *constant_idx = llvm::dyn_cast<llvm::ConstantInt>(idx);
			StType	   *index_ty	 = underlying_type(e.rhs->ty);
			if (index_ty && index_ty->kind == TypeKind::Enum) {
				index_ty = underlying_type(index_ty->base);
			}
			const bool integer_index =
				index_ty && (index_ty->kind == TypeKind::UInt || index_ty->kind == TypeKind::SInt);
			const bool nonnegative = !constant_idx || !index_ty ||
									 index_ty->kind != TypeKind::SInt ||
									 !constant_idx->isNegative();
			const bool in_bounds =
				constant_idx && integer_index && nonnegative &&
				constant_idx->getValue().ult(
					llvm::APInt(constant_idx->getBitWidth(), static_cast<uint64_t>(bt->array_len)));
			const unsigned address_space =
				llvm::cast<llvm::PointerType>(base->getType())->getAddressSpace();
			const unsigned index_width =
				l_.module().getDataLayout().getIndexSizeInBits(address_space);
			idx = coerce(B, idx, l_.llvm_int(index_width), index_ty, nullptr);
			auto indices =
				std::array<llvm::Value *, 2>{llvm::ConstantInt::get(l_.llvm_int(32), 0), idx};
			return in_bounds ? B.CreateInBoundsGEP(arrTy, base, indices, "arr.idx")
							 : B.CreateGEP(arrTy, base, indices, "arr.idx");
		}
		// Pointer indexing: ptr[i] -> GEP(elem_type, ptr, idx)
		llvm::Value *base = emit_expr(*e.lhs, ctx, m);
		if (!base) {
			return nullptr;
		}
		StType	   *elt	  = (bt && bt->kind == TypeKind::Pointer) ? underlying_type(bt->base) : nullptr;
		llvm::Type *eltTy = map_type(elt);
		const unsigned address_space =
			llvm::cast<llvm::PointerType>(base->getType())->getAddressSpace();
		const unsigned index_width =
			l_.module().getDataLayout().getIndexSizeInBits(address_space);
		StType *index_ty = underlying_type(e.rhs->ty);
		if (index_ty && index_ty->kind == TypeKind::Enum) {
			index_ty = underlying_type(index_ty->base);
		}
		idx = coerce(B, idx, l_.llvm_int(index_width), index_ty, nullptr);
		return B.CreateGEP(eltTy, base, idx, "idx");
	}
	case ExprKind::Deref: {
		if (!e.lhs) {
			return nullptr;
		}
		return emit_expr(*e.lhs, ctx, m);
	}
	case ExprKind::VariadicSplice:
		log::report(log::Level::Error, e.loc, "internal compiler error: macro splice reached codegen",
					"E_CODEGEN_FAILURE", "backend");
		return nullptr;
	default:
		return nullptr;
	}
}

llvm::Value *Codegen::emit_expr(Expr &e, FnDecl &ctx, Module &m) {
	if (&e == compound_lhs_expr_) {
		return compound_lhs_value_;
	}
	auto &B = *builder_;
	if (e.kind == ExprKind::Binary && e.has_const_value && e.ty) {
		if (e.is_const_bool) {
			return llvm::ConstantInt::get(l_.llvm_bool(), e.const_bool_val ? 1 : 0);
		}
		if (e.const_value_is_float) {
			return llvm::ConstantFP::get(map_type(e.ty), e.flt_val);
		}
		if (auto *integer_type = llvm::dyn_cast<llvm::IntegerType>(map_type(e.ty))) {
			llvm::APInt bits(integer_type->getBitWidth(), e.int_val);
			if (bits.getBitWidth() > 64 && e.const_int_high_bits_ones) {
				bits |= llvm::APInt::getHighBitsSet(bits.getBitWidth(), bits.getBitWidth() - 64);
			}
			return llvm::ConstantInt::get(l_.ctx(), bits);
		}
	}
	if (e.kind == ExprKind::Binary && e.ty &&
		(e.str_val == "+%" || e.str_val == "-%" || e.str_val == "+|" || e.str_val == "-|")) {
		if (auto *constant = lower_const_expr(e, m, e.ty, map_type(underlying_type(e.ty)),
													".arith.const")) {
			return constant;
		}
	}
	switch (e.kind) {
	case ExprKind::IntLit: {
		StType	   *t  = e.ty ? e.ty : t_.sint(64);
		llvm::Type *lt = map_type(t);
		if (underlying_type(t) && underlying_type(t)->kind == TypeKind::Float) {
			return llvm::ConstantFP::get(lt, static_cast<double>(e.int_val));
		}
		return llvm::ConstantInt::get(lt, e.int_val, false);
	}
	case ExprKind::FloatLit:
		return llvm::ConstantFP::get(map_type(e.ty ? e.ty : t_.float_ty(64)), e.flt_val);
	case ExprKind::StringLit: {
		StType *t = underlying_type(e.ty);
		if (t && t->kind == TypeKind::Array) {
			StType *elem = underlying_type(t->base);
			if (elem && elem->kind == TypeKind::UInt && elem->width == 8 &&
				t->array_len == e.str_val.size() + 1) {
				return llvm::ConstantDataArray::getString(l_.ctx(), e.str_val, true);
			}
		}
		std::string nm = ".str";
		static int	sc = 0;
		nm += std::to_string(sc++);
		return cstring_global(e.str_val, nm);
	}
	case ExprKind::CharLit:
		return llvm::ConstantInt::get(l_.llvm_int(8), e.int_val, false);
	case ExprKind::BoolLit:
		return llvm::ConstantInt::get(l_.llvm_bool(), e.const_bool_val ? 1 : 0);
	case ExprKind::NullLit:
		return llvm::ConstantPointerNull::get(llvm::cast<llvm::PointerType>(l_.llvm_ptr()));
	case ExprKind::EnumMember: {
		StType *enum_type = underlying_type(e.ty);
		StType *backing = enum_type ? underlying_type(enum_type->base) : nullptr;
		return llvm::ConstantInt::get(map_type(backing), e.int_val,
									  backing && backing->kind == TypeKind::SInt);
	}
	case ExprKind::DefineRef:
		return llvm::ConstantInt::get(
			l_.llvm_bool(),
			sema_.opts().flags.count(e.str_val) && sema_.opts().flags.at(e.str_val) ? 1 : 0);
	case ExprKind::SrcFile:
	case ExprKind::SrcFn:
		return cstring_global(e.str_val, ".src");
	case ExprKind::SrcLine:
	case ExprKind::SrcColumn:
		return llvm::ConstantInt::get(map_type(e.ty ? e.ty : t_.usize_ty()), e.int_val, false);
	case ExprKind::TypeValue:
		// Type values are compile-time-only and are erased before codegen.
		return llvm::UndefValue::get(l_.llvm_ptr());
	case ExprKind::VariadicSplice:
		log::report(log::Level::Error, e.loc,
					"internal compiler error: macro splice reached codegen",
					"E_CODEGEN_FAILURE", "backend");
		return llvm::UndefValue::get(l_.llvm_int(t_.pointer_width()));
	case ExprKind::Stringify:
		log::report(log::Level::Error, e.loc,
					"internal compiler error: syntax stringify reached codegen",
					"E_CODEGEN_FAILURE", "backend");
		return llvm::UndefValue::get(l_.llvm_int(t_.pointer_width()));
	case ExprKind::DiagWarn:
	case ExprKind::DiagErr:
		return nullptr;
	case ExprKind::Block: {
		if (!e.block || !e.ty || underlying_type(e.ty)->kind == TypeKind::Void) {
			return llvm::UndefValue::get(l_.llvm_int(t_.pointer_width()));
		}
		llvm::Function *fn = cur_fn(ctx);
		auto *merge = llvm::BasicBlock::Create(l_.ctx(), "block.expr.end", fn);
		block_expr_stack_.push_back({merge, defer_scopes_.size(), {}});
		emit_stmt(*e.block, ctx, m);
		auto state = std::move(block_expr_stack_.back());
		block_expr_stack_.pop_back();
		if (auto *current = B.GetInsertBlock(); current && current != merge &&
			!current->hasTerminator()) {
			if (!current->hasNPredecessorsOrMore(1) && current->empty()) {
				if (current == sink_block_) {
					sink_block_ = nullptr;
				}
				B.ClearInsertionPoint();
				current->eraseFromParent();
			} else if (current->hasNPredecessorsOrMore(1)) {
				B.CreateBr(merge);
			} else {
				B.CreateUnreachable();
			}
		}
		B.SetInsertPoint(merge);
		auto *phi = B.CreatePHI(map_type(e.ty), state.values.size(), "block.expr.value");
		for (const auto &[value, block] : state.values) {
			if (value) {
				phi->addIncoming(value, block);
			}
		}
		return phi;
	}
	case ExprKind::Ident: {
		Module &expr_module = e.binding_module ? *e.binding_module : m;
		if (e.path.size() == 1) {
			if (ctx.generic_const_subst.count(e.path[0])) {
				return llvm::ConstantInt::get(
					map_type(e.ty), static_cast<uint64_t>(ctx.generic_const_subst.at(e.path[0])),
					false);
			}
			if (ctx.generic_const_string_subst.count(e.path[0])) {
				return cstring_global(ctx.generic_const_string_subst.at(e.path[0]),
									  ".generic.const");
			}
			const bool allow_local_lookup = !e.binding_module || e.macro_argument ||
				e.path[0].rfind("$macro.", 0) == 0;
			if (allow_local_lookup) {
				if (auto *lv = find_local(e.path[0])) {
				if (lv->is_addr) {
					return B.CreateLoad(map_type(lv->ty), lv->val, e.path[0].c_str());
				}
				return lv->val;
				}
			}
		}
		// enum constant: sema resolved to an enum type + integer value.  Do
		// this after local lookup because enum-typed parameters/locals are
		// ordinary values, not enum member references.
		if (e.ty && e.ty->kind == TypeKind::Enum) {
			StType	   *backing = underlying_type(e.ty->base);
			llvm::Type *lt		= map_type(backing);
			return llvm::ConstantInt::get(lt, (uint64_t)e.int_val,
										  backing && backing->kind == TypeKind::SInt);
		}
		// Resolve once against sema and dispatch on the symbol kind. This
		// handles both same- and cross-module identifiers (Pub var/const/fn)
		// without recomputing resolve_path per lookup -- the previous code
		// called it twice for globals and only handled cross-module fns.
		Symbol *sym = sema_.resolve_path(e.path, expr_module);
		if (sym) {
			if (sym->kind == SymKind::Var || sym->kind == SymKind::Const) {
				auto it = globals_.find(sym->mangled);
				if (it != globals_.end()) {
					ensure_tls_initialized(B, sym->mangled);
					return B.CreateLoad(map_type(sym->type ? sym->type : t_.void_ty()), it->second);
				}
			} else if (sym->kind == SymKind::Fn) {
				auto fit = fns_.find(sym->mangled);
				if (fit != fns_.end()) {
					return fit->second;
				}
			}
		}
		// Fallback: own-module global not yet registered via sema (e.g.
		// forward reference inside an emitting fn). Compute the mangled name
		// from the importing module's path -- matches the legacy slow path.
		{
			std::vector<std::string> segs = m.mod_path;
			segs.push_back(e.path.back());
			std::string nm = mangle(segs);
			auto		it = globals_.find(nm);
			if (it == globals_.end()) {
				nm += private_global_scope_suffix(m);
				it = globals_.find(nm);
			}
			if (it != globals_.end()) {
				ensure_tls_initialized(B, nm);
				return B.CreateLoad(map_type(sym && sym->type ? sym->type : t_.void_ty()),
									it->second);
			}
		}
		log::report(log::Level::Error, e.loc, "undefined identifier '" + e.str_val + "'");
		return llvm::UndefValue::get(l_.llvm_ptr());
	}
	case ExprKind::Binary: {
		const std::string &op = e.str_val;
		// short-circuit && / ||
		if (op == "&&" || op == "||") {
			if (e.is_const_bool) {
				return llvm::ConstantInt::get(l_.llvm_bool(), e.const_bool_val ? 1 : 0);
			}
			llvm::Function	 *fn = cur_fn(ctx);
			llvm::BasicBlock *rhsBB =
				llvm::BasicBlock::Create(l_.ctx(), op == "&&" ? "and.rhs" : "or.rhs", fn);
			llvm::BasicBlock *endBB	 = llvm::BasicBlock::Create(l_.ctx(), "logic.end", fn);
			llvm::Value		 *l		 = emit_expr(*e.lhs, ctx, m);
			llvm::BasicBlock *curBB	 = B.GetInsertBlock();
			llvm::Value		 *cond_l = coerce_cond(B, l); // -> i1
			// Result of `&&`/`||` is a bool (sema sets e.ty = bool_ty, which
			// maps to i1 -- a 1-bit unsigned integer). Short-circuit value is
			// a constant i1 (0 for &&, 1 for ||) on the skip path; the
			// evaluated RHS coerced to i1 on the rhs path. PHI over i1.
			llvm::Value *short_val	 = llvm::ConstantInt::get(l_.llvm_bool(), op == "&&" ? 0 : 1);
			if (op == "&&") {
				B.CreateCondBr(cond_l, rhsBB, endBB);
			} else {
				B.CreateCondBr(cond_l, endBB, rhsBB);
			}
			B.SetInsertPoint(rhsBB);
			llvm::Value		 *r		  = emit_expr(*e.rhs, ctx, m);
			llvm::Value		 *cond_r  = coerce_cond(B, r); // -> i1
			llvm::Value		 *rhs_val = cond_r;			   // already i1
			llvm::BasicBlock *rhsEnd  = B.GetInsertBlock();
			B.CreateBr(endBB);
			B.SetInsertPoint(endBB);
			llvm::PHINode *phi = B.CreatePHI(l_.llvm_bool(), 2, "logic");
			phi->addIncoming(short_val, curBB);
			phi->addIncoming(rhs_val, rhsEnd);
			return phi;
		}
		llvm::Value *l	   = emit_expr(*e.lhs, ctx, m);
		llvm::Value *r	   = emit_expr(*e.rhs, ctx, m);
		StType		*lt	   = underlying_type(e.lhs->ty);
		StType		*rt	   = underlying_type(e.rhs->ty);
		bool		 l_ptr = lt && lt->kind == TypeKind::Pointer;
		bool		 r_ptr = rt && rt->kind == TypeKind::Pointer;
		if (l_ptr || r_ptr) {
			// Pointer offsets intentionally use a plain GEP. This is unchecked
			// address arithmetic, so `inbounds` would add poison semantics that
			// Stella does not promise.
				auto emit_pointer_offset = [&](llvm::Value *base, llvm::Value *offset,
										   StType *offset_type, llvm::Type *elem_ty,
										   bool negate) -> llvm::Value * {
				const auto &data_layout = l_.module().getDataLayout();
				const unsigned address_space =
					llvm::cast<llvm::PointerType>(base->getType())->getAddressSpace();
				const unsigned index_width = data_layout.getIndexSizeInBits(address_space);
				// GEP interprets indices as signed. Convert narrower unsigned
				// offsets before GEP sees them, and widen before negation so
				// subtracting a minimum-width unsigned value does not wrap in its
				// original type.
				offset = coerce(B, offset, l_.llvm_int(index_width), offset_type, nullptr);
				if (negate) {
					offset = B.CreateNeg(offset, "ptr.offset.neg");
				}
				return B.CreateGEP(elem_ty, base, offset, "ptr.arith");
			};
			if (l_ptr && r_ptr && op == "-") {
				llvm::Type	*addr_ty   = l_.llvm_int(t_.pointer_width());
				llvm::Value *lhs_addr  = B.CreatePtrToInt(l, addr_ty, "ptr.lhs.addr");
				llvm::Value *rhs_addr  = B.CreatePtrToInt(r, addr_ty, "ptr.rhs.addr");
				llvm::Value *byte_diff = B.CreateSub(lhs_addr, rhs_addr, "ptr.diff.bytes");
				auto		&DL		   = l_.module().getDataLayout();
				uint64_t	 elem_size = DL.getTypeAllocSize(map_type(lt->base));
				const unsigned pointer_width = t_.pointer_width();
				const uint64_t max_signed_size = pointer_width >= 64
					? static_cast<uint64_t>(INT64_MAX)
					: ((uint64_t{1} << (pointer_width - 1)) - 1);
				if (elem_size == 0 || elem_size > max_signed_size) {
					log::report(log::Level::Error, e.loc,
								"pointer difference requires a nonzero pointee size representable "
								"as a positive target pointer difference");
					return llvm::UndefValue::get(addr_ty);
				}
				llvm::Value *size	   = llvm::ConstantInt::get(addr_ty, elem_size, false);
				return B.CreateSDiv(byte_diff, size, "ptr.diff");
			}
			if (l_ptr && (op == "+" || op == "-") && r->getType()->isIntegerTy()) {
				return emit_pointer_offset(l, r, e.rhs->ty, map_type(lt->base), op == "-");
			}
			if (r_ptr && op == "+" && l->getType()->isIntegerTy()) {
				return emit_pointer_offset(r, l, e.lhs->ty, map_type(rt->base), false);
			}
			// Pointer comparisons are handled below by LLVM's ICmp directly.
		}
		bool l_float   = lt && lt->kind == TypeKind::Float;
		bool r_float   = rt && rt->kind == TypeKind::Float;
		bool is_float  = l_float || r_float;
		bool is_signed = is_signed_integer(lt);
		if (is_float) {
			int width = l_float ? lt->width : rt->width;
			if (l_float && r_float) {
				width = std::max(lt->width, rt->width);
			}
			llvm::Type *target = l_.llvm_float(width);
			l				   = coerce(B, l, target, lt, nullptr);
			r				   = coerce(B, r, target, rt, nullptr);
		} else if (l->getType() != r->getType() && l->getType()->isIntegerTy() &&
				   r->getType()->isIntegerTy()) {
			unsigned lw = l->getType()->getIntegerBitWidth();
			unsigned rw = r->getType()->getIntegerBitWidth();
			if (lw != rw) {
				unsigned target = (lw > rw) ? lw : rw;
				l				= coerce(B, l, l_.llvm_int(target), lt, nullptr);
				r				= coerce(B, r, l_.llvm_int(target), rt, nullptr);
			}
		}
		if (op == "+") {
			return is_float ? B.CreateFAdd(l, r) : B.CreateAdd(l, r);
		}
		if (op == "-") {
			return is_float ? B.CreateFSub(l, r) : B.CreateSub(l, r);
		}
		if (op == "+%") {
			return B.CreateAdd(l, r);
		}
		if (op == "-%") {
			return B.CreateSub(l, r);
		}
		if (op == "+|" || op == "-|") {
			const llvm::Intrinsic::ID id = op == "+|"
				? (is_signed ? llvm::Intrinsic::sadd_sat : llvm::Intrinsic::uadd_sat)
				: (is_signed ? llvm::Intrinsic::ssub_sat : llvm::Intrinsic::usub_sat);
			auto *intrinsic = llvm::Intrinsic::getOrInsertDeclaration(
				&l_.module(), id, l->getType(), {l->getType(), r->getType()});
			return B.CreateCall(intrinsic, {l, r});
		}
		if (op == "*") {
			return is_float ? B.CreateFMul(l, r) : B.CreateMul(l, r);
		}
		if (op == "/") {
			if (is_float) {
				return B.CreateFDiv(l, r);
			}
		if (is_signed) {
			auto *integer_type = llvm::cast<llvm::IntegerType>(l->getType());
			auto *minimum = llvm::ConstantInt::get(
				integer_type, llvm::APInt::getSignedMinValue(integer_type->getBitWidth()));
			auto *minus_one = llvm::ConstantInt::getAllOnesValue(integer_type);
			auto *overflow = B.CreateAnd(B.CreateICmpEQ(l, minimum), B.CreateICmpEQ(r, minus_one));
			auto *safe_divisor = B.CreateSelect(overflow, llvm::ConstantInt::get(integer_type, 1), r);
			auto *quotient = B.CreateSDiv(l, safe_divisor);
			return B.CreateSelect(overflow, l, quotient);
		}
		return B.CreateUDiv(l, r);
		}
		if (op == "%") {
			if (is_float) {
				return B.CreateFRem(l, r);
			}
		if (is_signed) {
			auto *integer_type = llvm::cast<llvm::IntegerType>(l->getType());
			auto *minimum = llvm::ConstantInt::get(
				integer_type, llvm::APInt::getSignedMinValue(integer_type->getBitWidth()));
			auto *minus_one = llvm::ConstantInt::getAllOnesValue(integer_type);
			auto *overflow = B.CreateAnd(B.CreateICmpEQ(l, minimum), B.CreateICmpEQ(r, minus_one));
			auto *safe_divisor = B.CreateSelect(overflow, llvm::ConstantInt::get(integer_type, 1), r);
			auto *remainder = B.CreateSRem(l, safe_divisor);
			return B.CreateSelect(overflow, llvm::ConstantInt::get(integer_type, 0), remainder);
		}
		return B.CreateURem(l, r);
		}
		if (op == "&") {
			return B.CreateAnd(l, r);
		}
		if (op == "|") {
			return B.CreateOr(l, r);
		}
		if (op == "^") {
			return B.CreateXor(l, r);
		}
		if (op == "<<") {
			return B.CreateShl(l, r);
		}
		if (op == ">>") {
			return is_signed ? B.CreateAShr(l, r) : B.CreateLShr(l, r);
		}
		if (op == "==") {
			return B.CreateZExt(is_float ? B.CreateFCmpOEQ(l, r) : B.CreateICmpEQ(l, r),
								l_.llvm_bool());
		}
		if (op == "!=") {
			return B.CreateZExt(is_float ? B.CreateFCmpUNE(l, r) : B.CreateICmpNE(l, r),
								l_.llvm_bool());
		}
		if (op == "<") {
			return B.CreateZExt(is_float
									? B.CreateFCmpOLT(l, r)
									: (is_signed ? B.CreateICmpSLT(l, r) : B.CreateICmpULT(l, r)),
								l_.llvm_bool());
		}
		if (op == ">") {
			return B.CreateZExt(is_float
									? B.CreateFCmpOGT(l, r)
									: (is_signed ? B.CreateICmpSGT(l, r) : B.CreateICmpUGT(l, r)),
								l_.llvm_bool());
		}
		if (op == "<=") {
			return B.CreateZExt(is_float
									? B.CreateFCmpOLE(l, r)
									: (is_signed ? B.CreateICmpSLE(l, r) : B.CreateICmpULE(l, r)),
								l_.llvm_bool());
		}
		if (op == ">=") {
			return B.CreateZExt(is_float
									? B.CreateFCmpOGE(l, r)
									: (is_signed ? B.CreateICmpSGE(l, r) : B.CreateICmpUGE(l, r)),
								l_.llvm_bool());
		}
		log::report(log::Level::Error, e.loc, std::string("unknown operator '") + op + "'");
		return llvm::UndefValue::get(l_.llvm_int(t_.pointer_width()));
	}
	case ExprKind::Conditional: {
		if (!e.condition || !e.then_expr || !e.else_expr) {
			return llvm::UndefValue::get(l_.llvm_int(t_.pointer_width()));
		}
		// Sema records the condition independently from the selected result;
		// use the condition flag, not e.is_const_bool (which describes the
		// conditional's result), to eliminate a dead arm.
		if (e.condition->is_const_bool) {
			Expr *selected = e.condition->const_bool_val ? e.then_expr.get() : e.else_expr.get();
			return emit_expr(*selected, ctx, m);
		}

		llvm::Value		 *cond	   = coerce_cond(B, emit_expr(*e.condition, ctx, m));
		llvm::Function	 *fn	   = cur_fn(ctx);
		llvm::BasicBlock *then_bb  = llvm::BasicBlock::Create(l_.ctx(), "cond.then", fn);
		llvm::BasicBlock *else_bb  = llvm::BasicBlock::Create(l_.ctx(), "cond.else", fn);
		llvm::BasicBlock *merge_bb = llvm::BasicBlock::Create(l_.ctx(), "cond.end", fn);
		B.CreateCondBr(cond, then_bb, else_bb);

		StType			 *result_ty = underlying_type(e.ty);
		llvm::AllocaInst *slot		= nullptr;
		if (result_ty && result_ty->kind != TypeKind::Void) {
			slot = llvm::cast<llvm::AllocaInst>(
				alloca_in_entry_typed(e.ty, map_type(e.ty), "cond.result"));
		}

		B.SetInsertPoint(then_bb);
		llvm::Value *then_value = emit_expr(*e.then_expr, ctx, m);
		if (slot && then_value) {
			store_value(slot, then_value, e.ty, e.then_expr->ty, e.loc);
		}
		br_or_absorb(B, merge_bb);

		B.SetInsertPoint(else_bb);
		llvm::Value *else_value = emit_expr(*e.else_expr, ctx, m);
		if (slot && else_value) {
			store_value(slot, else_value, e.ty, e.else_expr->ty, e.loc);
		}
		br_or_absorb(B, merge_bb);

		B.SetInsertPoint(merge_bb);
		return slot ? B.CreateLoad(map_type(e.ty), slot, "cond.value") : nullptr;
	}
	case ExprKind::Unary: {
		const std::string &op = e.str_val;
		if (op == "-") {
			llvm::Value *v	= emit_expr(*e.lhs, ctx, m);
			StType		*lt = underlying_type(e.lhs->ty);
			return lt && lt->kind == TypeKind::Float ? B.CreateFNeg(v) : B.CreateNeg(v);
		}
		if (op == "!") {
			llvm::Value *v = emit_expr(*e.lhs, ctx, m);
			llvm::Value *c = coerce_cond(B, v); // -> i1
			return B.CreateNot(c);				// !c as i1 bool
		}
		if (op == "~") {
			llvm::Value *v = emit_expr(*e.lhs, ctx, m);
			return B.CreateNot(v);
		}
		return llvm::UndefValue::get(l_.llvm_int(t_.pointer_width()));
	}
	case ExprKind::Assign: {
		llvm::Value *addr = emit_lvalue(*e.lhs, ctx, m);
		StType		*dst_st = underlying_type(e.lhs->ty);
		StType		*src_st = underlying_type(e.rhs->ty);
		const bool	 is_agg = dst_st && (dst_st->kind == TypeKind::Struct ||
										dst_st->kind == TypeKind::Union ||
										dst_st->kind == TypeKind::Array);
		if (!e.is_compound_assignment && addr && is_agg) {
			if (llvm::Value *src_addr = emit_lvalue(*e.rhs, ctx, m)) {
				llvm::Type *lt = map_type(dst_st);
				auto	   &dl = l_.module().getDataLayout();
				uint64_t	sz = dl.getTypeAllocSize(lt);
				llvm::Align dst_align = pointer_align(addr, dst_st, lt);
				llvm::Align src_align = pointer_align(src_addr, src_st, map_type(src_st));
				B.CreateMemCpy(addr, dst_align, src_addr, src_align, sz,
							   is_volatile_access(*e.lhs) || is_volatile_access(*e.rhs));
				return nullptr;
			}
		}
		llvm::Value *val = nullptr;
		if (e.is_compound_assignment && addr && e.rhs && e.rhs->kind == ExprKind::Binary &&
			e.rhs->lhs) {
			auto *load = B.CreateLoad(map_type(e.lhs->ty), addr, "compound.old");
			load->setVolatile(is_volatile_access(*e.lhs));
			const Expr *previous_expr = compound_lhs_expr_;
			llvm::Value *previous_value = compound_lhs_value_;
			compound_lhs_expr_ = e.rhs->lhs.get();
			compound_lhs_value_ = load;
			val = emit_expr(*e.rhs, ctx, m);
			compound_lhs_expr_ = previous_expr;
			compound_lhs_value_ = previous_value;
		} else {
			val = emit_expr(*e.rhs, ctx, m);
		}
		if (addr) {
			if (dst_st && dst_st->kind != TypeKind::Struct && dst_st->kind != TypeKind::Union &&
				dst_st->kind != TypeKind::Array) {
				val = coerce(B, val, map_type(dst_st), src_st, dst_st);
			}
			auto *store = B.CreateStore(val, addr);
			store->setVolatile(is_volatile_access(*e.lhs));
		}
		return val;
	}
	case ExprKind::Call:
		return emit_call(e, ctx, m);
	case ExprKind::Member: {
		Module &expr_module = e.binding_module ? *e.binding_module : m;
		// rvalue read of a field
		std::vector<std::string> qualified_path;
		if (flatten_member_path(e, qualified_path) && qualified_path.size() >= 2) {
			std::vector<std::string> enum_head(qualified_path.begin(), qualified_path.end() - 1);
			if (Symbol *en = sema_.resolve_path(enum_head, expr_module)) {
				if (en->kind == SymKind::Enum) {
					StType *backing = underlying_type(en->type->base);
					return llvm::ConstantInt::get(map_type(backing), e.int_val,
												  backing && backing->kind == TypeKind::SInt);
				}
			}
			if (Symbol *sym = sema_.resolve_path(qualified_path, expr_module)) {
				if (sym->kind == SymKind::Enum) {
					return llvm::ConstantInt::get(map_type(sym->type), e.int_val, false);
				}
				if (sym->kind == SymKind::Const && sym->has_const_value) {
					if (sym->const_value_is_float) {
						return llvm::ConstantFP::get(map_type(sym->type), sym->const_flt_val);
					}
					if (sym->type && sym->type->kind == TypeKind::Bool) {
						return llvm::ConstantInt::get(l_.llvm_bool(), sym->const_bool_val ? 1 : 0);
					}
					return llvm::ConstantInt::get(map_type(sym->type), sym->const_int_val, false);
				}
				if ((sym->kind == SymKind::Var || sym->kind == SymKind::Const) &&
					globals_.count(sym->mangled)) {
					ensure_tls_initialized(B, sym->mangled);
					return B.CreateLoad(map_type(sym->type), globals_[sym->mangled]);
				}
				if (sym->kind == SymKind::Fn) {
					std::string mangled = !sym->mangled.empty() ? sym->mangled :
						(sym->fn ? fn_symbol_name(*sym->fn) : "");
					if (!mangled.empty() && fns_.count(mangled)) {
						return fns_[mangled];
					}
				}
			}
		}
		llvm::Value *addr = emit_lvalue(e, ctx, m);
		if (!addr) {
			return llvm::UndefValue::get(l_.llvm_int(t_.pointer_width()));
		}
		StType *bt = underlying_type(e.lhs->ty);
		while (bt && bt->kind == TypeKind::Pointer) {
			StType *pointee = underlying_type(bt->base);
			if (pointee &&
				(pointee->kind == TypeKind::Struct || pointee->kind == TypeKind::Union)) {
				bt = pointee;
				break;
			}
			if (!pointee || pointee->kind != TypeKind::Pointer) {
				return llvm::UndefValue::get(l_.llvm_int(t_.pointer_width()));
			}
			bt = pointee;
		}
		if (!bt || (bt->kind != TypeKind::Struct && bt->kind != TypeKind::Union)) {
			return llvm::UndefValue::get(l_.llvm_int(t_.pointer_width()));
		}
		size_t idx = field_index(bt, e.member);
		if (idx == SIZE_MAX) {
			return llvm::UndefValue::get(l_.llvm_int(t_.pointer_width()));
		}
		StType *ft	 = bt->fields[idx];
		auto   *load = B.CreateLoad(map_type(ft), addr, "fld.v");
		load->setVolatile(is_volatile_access(e));
		return load;
	}
	case ExprKind::Index: {
		if (e.is_bit_range) {
			llvm::Value *value = emit_expr(*e.lhs, ctx, m);
			if (!value) {
				return nullptr;
			}
			if (e.bit_range_low != 0) {
				value = B.CreateLShr(value,
					llvm::ConstantInt::get(value->getType(), e.bit_range_low), "bits.shift");
			}
			auto *result_type = llvm::cast<llvm::IntegerType>(map_type(e.ty));
			if (value->getType()->getIntegerBitWidth() != result_type->getBitWidth()) {
				value = B.CreateTrunc(value, result_type, "bits.extract");
			}
			return value;
		}
		llvm::Value *addr = emit_lvalue(e, ctx, m);
		StType		*bt	  = underlying_type(e.lhs->ty);
		StType		*elt  = nullptr;
		if (bt && bt->kind == TypeKind::Pointer) {
			elt = underlying_type(bt->base);
		} else if (bt && bt->kind == TypeKind::Array) {
			elt = underlying_type(bt->base);
		}
		auto *load = B.CreateLoad(map_type(elt), addr, "idx.v");
		load->setVolatile(is_volatile_access(e));
		return load;
	}
	case ExprKind::StructLit: {
		StType *aggregate = underlying_type(e.ty);
		if (aggregate && aggregate->kind == TypeKind::Union) {
			return emit_union_lit(e, ctx, m);
		}
		return emit_struct_lit(e, ctx, m);
	}
	case ExprKind::ArrayLit: {
		StType *at = underlying_type(e.ty);
		if (!at || at->kind != TypeKind::Array) {
			return llvm::UndefValue::get(l_.llvm_ptr());
		}
		llvm::Type				  *lt	  = map_type(at);
		llvm::Type				  *elt_lt = map_type(underlying_type(at->base));
		// Emit each element once. If every emitted value is an LLVM constant
		// whose type already matches the element type (i.e. no coerce needed),
		// we can collapse the zero-init + N per-element stores into a single
		// `store ConstantArray` into the slot. The slot stays mutable so
		// subsequent code can still write through the returned pointer.
		std::vector<llvm::Value *> vals;
		vals.reserve(e.args.size());
		bool all_const = !e.args.empty();
		for (auto &arg : e.args) {
			llvm::Value *v = emit_expr(*arg, ctx, m);
			vals.push_back(v);
			if (!llvm::isa<llvm::Constant>(v) || v->getType() != elt_lt) {
				all_const = false;
			}
		}
		llvm::Value *slot = alloca_in_entry(lt, "arr");
		if (all_const) {
			auto						 *arrTy = llvm::cast<llvm::ArrayType>(lt);
			std::vector<llvm::Constant *> consts;
			consts.reserve(arrTy->getNumElements());
			for (auto *v : vals) {
				consts.push_back(llvm::cast<llvm::Constant>(v));
			}
			while (consts.size() < arrTy->getNumElements()) {
				consts.push_back(llvm::ConstantAggregateZero::get(elt_lt));
			}
			B.CreateStore(llvm::ConstantArray::get(arrTy, consts), slot);
			return B.CreateLoad(lt, slot, "arr.value");
		}
		B.CreateStore(llvm::ConstantAggregateZero::get(lt), slot);
		llvm::Type *index_ty = l_.llvm_int(t_.pointer_width());
		for (size_t i = 0; i < e.args.size(); ++i) {
			llvm::Value *elem = vals[i];
			llvm::Value *ptr =
				B.CreateInBoundsGEP(lt, slot,
									{llvm::ConstantInt::get(index_ty, 0),
									 llvm::ConstantInt::get(index_ty, static_cast<uint64_t>(i), false)},
									"arr.elem");
			StType *elt_st = underlying_type(at->base);
			if (elt_st && elt_st->kind != TypeKind::Struct && elt_st->kind != TypeKind::Union &&
				elt_st->kind != TypeKind::Array) {
				elem = coerce(B, elem, map_type(elt_st), underlying_type(e.args[i]->ty), elt_st);
			}
			B.CreateStore(elem, ptr);
		}
		return B.CreateLoad(lt, slot, "arr.value");
	}
	case ExprKind::AddrOf: {
		// `&fn_name` is idempotent with bare `fn_name`: a function name already
		// yields its pointer value (see ExprKind::Ident below); functions are
		// not lvalues. Short-circuit before emit_lvalue for any fn-typed lhs.
		if (e.lhs && e.lhs->kind == ExprKind::Ident) {
			Module &expr_module = e.lhs->binding_module ? *e.lhs->binding_module : m;
			Symbol *sym = sema_.resolve_path(e.lhs->path, expr_module);
			if (sym && sym->kind == SymKind::Fn) {
				auto fit = fns_.find(sym->mangled);
				if (fit != fns_.end()) {
					return fit->second;
				}
			}
		}
		return emit_lvalue(*e.lhs, ctx, m);
	}
	case ExprKind::Deref: {
		// rvalue: load from address = pointer value
		llvm::Value *p	  = emit_expr(*e.lhs, ctx, m);
		StType		*bt	  = underlying_type(e.lhs->ty);
		StType		*elt  = (bt && bt->kind == TypeKind::Pointer) ? underlying_type(bt->base) : nullptr;
		auto		*load = B.CreateLoad(map_type(elt), p, "deref");
		load->setVolatile(is_volatile_access(e));
		return load;
	}
	case ExprKind::Sizeof: {
		StType *st = layout_operand_type(e.lhs.get());
		if (!st) {
			st = t_.void_ty();
		}
		llvm::Type *lt = map_type(st);
		auto	   &DL = l_.module().getDataLayout();
		uint64_t	sz = DL.getTypeAllocSize(lt);
		auto	   *result_type = map_type(e.ty ? e.ty : t_.usize_ty());
		if (!fits_target_usize(sz, t_.pointer_width())) {
			log::report(log::Level::Error, e.loc,
						"@of.size result does not fit the target usize type");
			return llvm::UndefValue::get(result_type);
		}
		return llvm::ConstantInt::get(result_type, sz, false);
	}
	case ExprKind::Alignof: {
		StType *st = layout_operand_type(e.lhs.get());
		if (!st) {
			st = t_.void_ty();
		}
		llvm::Type *lt		  = map_type(st);
		auto	   &DL		  = l_.module().getDataLayout();
		uint64_t	align_val = DL.getABITypeAlign(lt).value();
		auto	   *result_type = map_type(e.ty ? e.ty : t_.usize_ty());
		if (!fits_target_usize(align_val, t_.pointer_width())) {
			log::report(log::Level::Error, e.loc,
						"@of.align result does not fit the target usize type");
			return llvm::UndefValue::get(result_type);
		}
		return llvm::ConstantInt::get(result_type, align_val, false);
	}
	case ExprKind::Bitsof: {
		StType *st = layout_operand_type(e.lhs.get());
		if (!st) {
			st = t_.void_ty();
		}
		llvm::Type *lt	 = map_type(st);
		uint64_t bits = 0;
		auto	*result_type = map_type(e.ty ? e.ty : t_.usize_ty());
		if (!bitsof_type(st, t_.pointer_width(), l_.module().getDataLayout(), lt, bits) ||
			!fits_target_usize(bits, t_.pointer_width())) {
			log::report(log::Level::Error, e.loc,
						"@of.bits result does not fit the target usize type");
			return llvm::UndefValue::get(result_type);
		}
		return llvm::ConstantInt::get(result_type, bits, false);
	}
	case ExprKind::Offsetof: {
		llvm::Type *result_lt = map_type(e.ty ? e.ty : t_.usize_ty());
		StType	   *st		  = layout_operand_type(e.lhs.get());
		st					  = underlying_type(st);
		if (!st || (st->kind != TypeKind::Struct && st->kind != TypeKind::Union)) {
			return llvm::ConstantInt::get(result_lt, 0, false);
		}
		if (st->kind == TypeKind::Union) {
			return llvm::ConstantInt::get(result_lt, 0, false);
		}
		llvm::Type *lt = map_type(st);
		if (!lt->isStructTy()) {
			return llvm::ConstantInt::get(result_lt, 0, false);
		}
		auto  *struct_ty = llvm::cast<llvm::StructType>(lt);
		size_t idx		 = field_index(st, e.offsetof_member);
		if (idx == SIZE_MAX || idx >= struct_ty->getNumElements()) {
			return llvm::ConstantInt::get(result_lt, 0, false);
		}
		auto					 &DL		 = l_.module().getDataLayout();
		const llvm::StructLayout *layout	 = DL.getStructLayout(struct_ty);
		uint64_t				  offset_val = layout->getElementOffset(idx);
		return llvm::ConstantInt::get(result_lt, offset_val, false);
	}
	case ExprKind::Cast: {
		StType		*tgt   = e.ty ? e.ty : t_.void_ty();
		StType		*tgt_u = underlying_type(tgt);
		llvm::Type	*lt	   = map_type(tgt);
		llvm::Value *v	   = emit_expr(*e.lhs, ctx, m);
		StType		*from  = underlying_type(e.lhs->ty);
		// bitcast: reinterprets the identical bits as another same-size type.
		// Sema already enforced equal scalar sizes; here we emit the IR that
		// preserves the raw bits. LLVM bitcast handles float<->int and
		// ptr<->ptr directly. For int<->ptr (both 64-bit) LLVM has no direct
		// bitcast -- inttoptr/ptrtoint preserve the bits, so we use those.
		// Same-size int<->int is a no-op identity in LLVM (just return v).
		if (e.is_bitcast) {
			bool fp_src	 = from && from->kind == TypeKind::Float;
			bool fp_dst	 = tgt_u && tgt_u->kind == TypeKind::Float;
			bool int_src = from && (from->kind == TypeKind::UInt || from->kind == TypeKind::SInt ||
									from->kind == TypeKind::Enum);
			bool int_dst =
				tgt_u && (tgt_u->kind == TypeKind::UInt || tgt_u->kind == TypeKind::SInt ||
						  tgt_u->kind == TypeKind::Enum);
			bool ptr_src = from && from->kind == TypeKind::Pointer;
			bool ptr_dst = tgt_u && tgt_u->kind == TypeKind::Pointer;
			if (fp_src != fp_dst) {
				// float <-> int: LLVM bitcast reinterprets the bits.
				return B.CreateBitCast(v, lt);
			}
			if (ptr_src && ptr_dst) {
				return B.CreateBitCast(v, lt);
			}
			if (ptr_src && int_dst) {
				return B.CreatePtrToInt(v, lt);
			}
			if (int_src && ptr_dst) {
				return B.CreateIntToPtr(v, lt);
			}
			// int <-> int (same size) or same kind: identity, no code needed.
			return v;
		}
		// cast: normal value conversion. Same code path the old `as` operator
		// used: pick zext/sext/trunc/fpext/fptrunc/sitofp/fptosi/ptrtoint/
		// inttoptr/bitcast based on the src/dst categories.
		if (from && from->kind == TypeKind::Pointer && tgt_u->kind == TypeKind::Pointer) {
			return B.CreateBitCast(v, lt);
		}
		if (tgt_u->kind == TypeKind::Bool) {
			if (from && from->kind == TypeKind::Float) {
				// Treat NaN as true, just like every other nonzero value.
				return B.CreateFCmpUNE(v, llvm::ConstantFP::get(v->getType(), 0.0));
			}
			if (from && from->kind == TypeKind::Pointer) {
				return B.CreateICmpNE(
					v, llvm::ConstantPointerNull::get(llvm::cast<llvm::PointerType>(v->getType())));
			}
			if (from && is_integer_type(from)) {
				return B.CreateICmpNE(v, llvm::ConstantInt::get(v->getType(), 0));
			}
		}
		if (from && from->kind == TypeKind::Pointer && is_integer_type(tgt_u)) {
			return B.CreatePtrToInt(v, lt);
		}
		if (from && is_integer_type(from) && tgt_u->kind == TypeKind::Pointer) {
			return B.CreateIntToPtr(v, lt);
		}
		if (from && from->kind == TypeKind::Float && is_integer_type(tgt_u)) {
			return is_signed_integer(tgt_u) ? B.CreateFPToSI(v, lt) : B.CreateFPToUI(v, lt);
		}
		if (from && is_integer_type(from) && tgt_u->kind == TypeKind::Float) {
			return is_signed_integer(from) ? B.CreateSIToFP(v, lt) : B.CreateUIToFP(v, lt);
		}
		if (from && from->kind == TypeKind::Float && tgt_u->kind == TypeKind::Float) {
			return B.CreateFPCast(v, lt);
		}
		if (from && is_integer_type(from) && is_integer_type(tgt_u)) {
			return coerce(B, v, lt, from, tgt);
		}
		return v;
	}
	case ExprKind::VaStart: {
		if (!target_supports_va_lists() || e.args.empty()) {
			return llvm::UndefValue::get(l_.llvm_int(t_.pointer_width()));
		}
		llvm::Value *addr = va_list_operand(*e.args[0], ctx, m);
		return B.CreateCall(llvm::Intrinsic::getOrInsertDeclaration(
								&l_.module(), llvm::Intrinsic::vastart, {l_.llvm_ptr()}),
							{addr});
	}
	case ExprKind::VaCopy: {
		if (!target_supports_va_lists() || e.args.size() < 2) {
			return llvm::UndefValue::get(l_.llvm_int(t_.pointer_width()));
		}
		llvm::Value *dst = va_list_operand(*e.args[0], ctx, m);
		llvm::Value *src = va_list_operand(*e.args[1], ctx, m);
		// Let LLVM lower va_copy for the active target. This is important even
		// when the current ABI happens to represent va_list as a copyable
		// aggregate: other ABIs may require target-specific initialization or
		// ownership behavior.
		return B.CreateCall(llvm::Intrinsic::getOrInsertDeclaration(
								&l_.module(), llvm::Intrinsic::vacopy, {l_.llvm_ptr()}),
							{dst, src});
	}
	case ExprKind::VaEnd:
		if (!target_supports_va_lists() || e.args.empty()) {
			return llvm::UndefValue::get(l_.llvm_int(t_.pointer_width()));
		}
		return B.CreateCall(llvm::Intrinsic::getOrInsertDeclaration(
								&l_.module(), llvm::Intrinsic::vaend, {l_.llvm_ptr()}),
							{va_list_operand(*e.args[0], ctx, m)});
	case ExprKind::VaArg: {
		if (!target_supports_va_lists() || e.args.empty() || !e.va_arg_ty) {
			return llvm::UndefValue::get(l_.llvm_int(t_.pointer_width()));
		}
		StType *ty = sema_.resolve_type(*e.va_arg_ty, m);
		if (!ty || ty == t_.void_ty() || !e.ty || e.ty == t_.void_ty()) {
			return llvm::UndefValue::get(l_.llvm_int(t_.pointer_width()));
		}
		return emit_va_arg(va_list_operand(*e.args[0], ctx, m), ty);
	}
	}
	return llvm::UndefValue::get(l_.llvm_int(t_.pointer_width()));
}

llvm::Value *Codegen::emit_call(Expr &e, FnDecl &ctx, Module &m) {
	auto   &B		  = *builder_;
	FnDecl *callee_fn = e.resolved_fn;
	if (callee_fn && callee_fn->is_macro) {
		log::report(log::Level::Error, e.loc,
					"internal compiler error: macro call reached codegen",
					"E_CODEGEN_FAILURE", "backend");
		return llvm::UndefValue::get(l_.llvm_int(t_.pointer_width()));
	}
	if (!callee_fn && e.lhs) {
		std::vector<std::string> path;
		if (e.lhs->kind == ExprKind::Ident) {
			path = e.lhs->path;
		} else if (e.lhs->kind == ExprKind::Member) {
			flatten_member_path(*e.lhs, path);
		}
		if (!path.empty()) {
			Symbol *sym = sema_.resolve_path(path, m);
			if (sym && sym->kind == SymKind::Fn) {
				callee_fn = !sym->overloads.empty() ? sym->overloads[0] : sym->fn;
			}
		}
	}
	if (callee_fn) {
		std::string mangled_name = fn_symbol_name(*callee_fn);
		auto		it			 = fns_.find(mangled_name);
		if (it == fns_.end() && callee_fn->decl_module) {
			declare_fn(*callee_fn, *callee_fn->decl_module);
			it = fns_.find(mangled_name);
		}
		if (it == fns_.end()) {
			log::report(log::Level::Error, e.loc, "no declaration for '" + mangled_name + "'",
						"E_CODEGEN_FAILURE", "backend");
			return llvm::UndefValue::get(l_.llvm_int(t_.pointer_width()));
		}
		llvm::Function			  *fn = it->second;
		std::vector<llvm::Value *> args;
		unsigned				   fn_fixed = fn->arg_size();
		unsigned				   abi_i	= 0;
		for (unsigned i = 0; i < e.args.size(); ++i) {
			if (i < callee_fn->params.size() && callee_fn->params[i].is_comptime) {
				continue;
			}
			llvm::Value *a = emit_expr(*e.args[i], ctx, m);
			if (abi_i < fn_fixed) {
				llvm::Type *pt	   = fn->getFunctionType()->getParamType(abi_i);
				StType	   *src_st = underlying_type(e.args[i]->ty);
				StType	   *dst_st = nullptr;
				if (i < callee_fn->params.size()) {
					dst_st = underlying_type(callee_fn->params[i].resolved
										 ? callee_fn->params[i].resolved
										 : sema_.resolve_type(*callee_fn->params[i].ty, m));
				}
				a = coerce(B, a, pt, src_st, dst_st);
				if (a->getType() != pt && a->getType()->isAggregateType() &&
					pt->isFirstClassType()) {
					a = to_abi_value(a, pt);
				}
			}
			args.push_back(a);
			++abi_i;
		}
		auto *call = B.CreateCall(fn, args);
		return &e == abi_result_expr_ ? call : from_abi_value(call, map_type(e.ty));
	}
	// Indirect call: lhs expr evaluates to a function-pointer value. Sema has
	// already typechecked args against the StType function signature.
	llvm::Value *callee = emit_expr(*e.lhs, ctx, m);
	StType		*lht	= underlying_type(e.lhs->ty);
	StType		*ft		= lht;
	if (ft && ft->kind == TypeKind::Pointer) {
		ft = underlying_type(ft->base);
	}
	if (!ft || ft->kind != TypeKind::Function) {
		log::report(log::Level::Error, e.loc, "indirect call of non-function value");
		return llvm::UndefValue::get(l_.llvm_int(t_.pointer_width()));
	}
	llvm::FunctionType		  *fnTy = map_fn_type(ft);
	std::vector<llvm::Value *> args;
	size_t					   n_fixed = ft->fn_params.size();
	size_t					   abi_i = 0;
	for (size_t i = 0; i < e.args.size(); ++i) {
		StType *param_type = i < n_fixed ? underlying_type(ft->fn_params[i]) : nullptr;
		if (param_type && param_type->kind == TypeKind::Type) {
			continue;
		}
		llvm::Value *a = emit_expr(*e.args[i], ctx, m);
		if (abi_i < fnTy->getNumParams()) {
			llvm::Type *pt	   = fnTy->getParamType(static_cast<unsigned>(abi_i));
			StType	   *src_st = underlying_type(e.args[i]->ty);
			StType	   *dst_st = param_type;
			a				   = coerce(B, a, pt, src_st, dst_st);
			if (a->getType() != pt && a->getType()->isAggregateType() && pt->isFirstClassType()) {
				a = to_abi_value(a, pt);
			}
		}
		args.push_back(a);
		++abi_i;
	}
	auto *call = B.CreateCall(fnTy, callee, args);
	return &e == abi_result_expr_ ? call : from_abi_value(call, map_type(e.ty));
}

llvm::Value *Codegen::emit_struct_lit(Expr &e, FnDecl &ctx, Module &m) {
	auto &B = *builder_;
	(void)m;
	StType *st = underlying_type(e.ty);
	if (!st || st->kind != TypeKind::Struct) {
		return llvm::UndefValue::get(l_.llvm_ptr());
	}
	llvm::Type				  *lt  = map_type(st);
	auto					  *stt = llvm::cast<llvm::StructType>(lt);
	// Emit each field value exactly once. If every emitted value is an LLVM
	// constant of the right field type, we can skip the zero-init and the N
	// per-field stores and emit a single `store ConstantStruct` into the
	// slot (the slot stays mutable, so subsequent writes still work). For
	// uninitialized fields we pad with ConstantAggregateZero.
	std::vector<llvm::Value *> vals(e.field_names.size());
	std::vector<size_t>		   idxs(e.field_names.size(), SIZE_MAX);
	bool					   all_const = !e.field_names.empty();
	assert(e.args.size() == e.field_names.size() &&
		   "Sema failed to validate struct literal fields");
	for (size_t i = 0; i < e.field_names.size(); ++i) {
		idxs[i] = field_index(st, e.field_names[i]);
		if (idxs[i] == SIZE_MAX) {
			log::report(log::Level::Error, e.loc, "no field '" + e.field_names[i] + "'");
			all_const = false;
			continue;
		}
		llvm::Value *v = emit_expr(*e.args[i], ctx, m);
		vals[i]		   = v;
		if (!llvm::isa<llvm::Constant>(v) || v->getType() != stt->getElementType(idxs[i])) {
			all_const = false;
		}
	}
	llvm::Value *slot = alloca_in_entry_typed(st, lt, "lit");
	if (all_const) {
		std::vector<llvm::Constant *> fields;
		fields.reserve(stt->getNumElements());
		for (size_t i = 0; i < stt->getNumElements(); ++i) {
			fields.push_back(llvm::ConstantAggregateZero::get(stt->getElementType(i)));
		}
		for (size_t i = 0; i < e.field_names.size(); ++i) {
			if (idxs[i] != SIZE_MAX) {
				if (auto *cv = llvm::dyn_cast<llvm::Constant>(vals[i])) {
					fields[idxs[i]] = cv;
				}
			}
		}
		B.CreateStore(llvm::ConstantStruct::get(stt, fields), slot);
		return B.CreateLoad(lt, slot, "lit.value");
	}
	// zero init
	B.CreateStore(llvm::ConstantAggregateZero::get(lt), slot);
	for (size_t i = 0; i < e.field_names.size(); ++i) {
		if (idxs[i] == SIZE_MAX) {
			continue;
		}
		llvm::Value *fld   = B.CreateStructGEP(stt, slot, idxs[i], "lit.f");
		llvm::Value *v	   = vals[i];
		StType		*ft_st = underlying_type(st->fields[idxs[i]]);
		if (ft_st && ft_st->kind != TypeKind::Struct && ft_st->kind != TypeKind::Union &&
			ft_st->kind != TypeKind::Array) {
			v = coerce(B, v, map_type(ft_st), underlying_type(e.args[i]->ty), ft_st);
		}
		B.CreateStore(v, fld);
	}
	return B.CreateLoad(lt, slot, "lit.value");
}

llvm::Value *Codegen::emit_union_lit(Expr &e, FnDecl &ctx, Module &m) {
	auto &B = *builder_;
	(void)m;
	StType *u = underlying_type(e.ty);
	if (!u || u->kind != TypeKind::Union || e.field_names.size() != 1 || e.args.size() != 1) {
		return llvm::UndefValue::get(l_.llvm_int(8));
	}
	llvm::Type	*lt	  = map_type(u);
	llvm::Value *slot = alloca_in_entry_typed(u, lt, "union.lit");
	B.CreateStore(llvm::ConstantAggregateZero::get(lt), slot);
	size_t idx = field_index(u, e.field_names[0]);
	if (idx == SIZE_MAX) {
		return B.CreateLoad(lt, slot, "union.value");
	}
	llvm::Value *v	= emit_expr(*e.args[0], ctx, m);
	StType		*ft = underlying_type(u->fields[idx]);
	if (ft && ft->kind != TypeKind::Struct && ft->kind != TypeKind::Union &&
		ft->kind != TypeKind::Array) {
		v = coerce(B, v, map_type(ft), underlying_type(e.args[0]->ty), ft);
	}
	B.CreateStore(v, slot);
	return B.CreateLoad(lt, slot, "union.value");
}

} // namespace stellac