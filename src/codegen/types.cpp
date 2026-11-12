#include "internal.hpp"

namespace stellac {

llvm::Type *Codegen::map_type(StType *t) {
	if (!t) {
		return l_.llvm_void();
	}
	t		= underlying_type(t);
	auto it = type_cache_.find(t);
	if (it != type_cache_.end()) {
		return it->second;
	}
	llvm::Type *r = nullptr;
	switch (t->kind) {
	case TypeKind::Void:
		r = l_.llvm_void();
		break;
	case TypeKind::Bool:
		r = l_.llvm_bool();
		break;
	case TypeKind::UInt:
	case TypeKind::SInt:
		r = l_.llvm_int(t->width > 0 ? t->width : t_.pointer_width());
		break;
	case TypeKind::Float:
		r = l_.llvm_float(t->width);
		break;
	case TypeKind::Pointer:
		r = l_.llvm_ptr();
		break;
	case TypeKind::Array:
		r = llvm::ArrayType::get(map_type(t->base), t->array_len);
		break;
	case TypeKind::Struct:
		r = map_named_struct(t);
		break;
	case TypeKind::Union:
		r = map_named_union(t);
		break;
	case TypeKind::Enum:
		r = map_type(t->base);
		break;
	case TypeKind::Function:
		r = l_.llvm_ptr();
		break;
	case TypeKind::VaList:
		r = va_list_llvm_type();
		break;
	default:
		r = l_.llvm_void();
		break;
	}
	type_cache_[t] = r;
	return r;
}

bool Codegen::target_supports_va_lists() const {
	llvm::Triple triple(l_.module().getTargetTriple());
	return triple.getOS() == llvm::Triple::Linux &&
		(triple.getArch() == llvm::Triple::x86_64 ||
		 triple.getArch() == llvm::Triple::aarch64 ||
		 triple.getArch() == llvm::Triple::riscv64);
}

llvm::StructType *Codegen::va_list_llvm_type() {
	llvm::Triple triple(l_.module().getTargetTriple());
	const char *name = "stella.va_list.unsupported";
	switch (triple.getArch()) {
	case llvm::Triple::x86_64: name = "stella.va_list.sysv_x86_64"; break;
	case llvm::Triple::aarch64: name = "stella.va_list.aapcs64"; break;
	case llvm::Triple::riscv64: name = "stella.va_list.riscv64"; break;
	default: break;
	}
	if (auto *existing = llvm::StructType::getTypeByName(l_.ctx(), name)) {
		return existing;
	}
	auto *ty = llvm::StructType::create(l_.ctx(), name);
	if (target_supports_va_lists()) {
		switch (triple.getArch()) {
		case llvm::Triple::x86_64:
			// gp_offset, fp_offset, overflow_arg_area, reg_save_area.
			ty->setBody({l_.llvm_int(32), l_.llvm_int(32), l_.llvm_ptr(), l_.llvm_ptr()}, false);
			break;
		case llvm::Triple::aarch64:
			// __stack, __gr_top, __vr_top, __gr_offs, __vr_offs.
			ty->setBody({l_.llvm_ptr(), l_.llvm_ptr(), l_.llvm_ptr(),
						 l_.llvm_int(32), l_.llvm_int(32)}, false);
			break;
		case llvm::Triple::riscv64:
			// A pointer into the contiguous register-save and stack argument area.
			ty->setBody({l_.llvm_ptr()}, false);
			break;
		default: break;
		}
	}
	return ty;
}

llvm::Value *Codegen::va_list_operand(Expr &operand, FnDecl &ctx, Module &m) {
	StType *type = underlying_type(operand.ty);
	if (type && type->kind == TypeKind::Pointer) {
		return emit_expr(operand, ctx, m);
	}
	if (operand.va_list_decl) {
		auto it = va_list_storage_.find(operand.va_list_decl);
		if (it != va_list_storage_.end()) {
			return it->second;
		}
	}
	return emit_lvalue(operand, ctx, m);
}

// Lower scalar va_arg explicitly. In particular, LLVM's x86 FastISel
// lowering can lose a non-alloca cursor across its generated control flow.
// Using ordinary IR also makes borrowed cursors work at every opt level.
llvm::Value *Codegen::emit_va_arg(llvm::Value *cursor, StType *type) {
	auto &B = *builder_;
	auto *value_type = map_type(type);
	auto &dl = l_.module().getDataLayout();
	const uint64_t size = dl.getTypeAllocSize(value_type);
	const uint64_t alignment = dl.getABITypeAlign(value_type).value();
	const bool floating = underlying_type(type)->kind == TypeKind::Float;
	llvm::Triple triple(l_.module().getTargetTriple());
	auto *layout = va_list_llvm_type();
	auto field = [&](unsigned index) { return B.CreateStructGEP(layout, cursor, index); };
	auto align_pointer = [&](llvm::Value *pointer, uint64_t align) -> llvm::Value * {
		if (align <= 8) { return pointer; }
		auto *integer = B.CreatePtrToInt(pointer, l_.llvm_int(64));
		integer = B.CreateAnd(B.CreateAdd(integer, B.getInt64(align - 1)),
							 B.getInt64(~(align - 1)));
		return B.CreateIntToPtr(integer, l_.llvm_ptr());
	};
	auto stack_argument = [&](unsigned index) -> llvm::Value * {
		auto *slot = field(index);
		auto *pointer = align_pointer(B.CreateLoad(l_.llvm_ptr(), slot), alignment);
		B.CreateStore(B.CreateGEP(B.getInt8Ty(), pointer, B.getInt64((size + 7) & ~7ULL)), slot);
		return pointer;
	};
	if (triple.getArch() == llvm::Triple::riscv64) {
		return B.CreateAlignedLoad(value_type, stack_argument(0), llvm::Align(1));
	}

	auto *function = B.GetInsertBlock()->getParent();
	auto *register_block = llvm::BasicBlock::Create(l_.ctx(), "va.register", function);
	auto *stack_block = llvm::BasicBlock::Create(l_.ctx(), "va.stack", function);
	auto *merge_block = llvm::BasicBlock::Create(l_.ctx(), "va.merge", function);
	llvm::Value *offset_slot;
	llvm::Value *offset;
	llvm::Value *next_offset;
	unsigned top_index;
	unsigned stack_index;
	if (triple.getArch() == llvm::Triple::aarch64) {
		offset_slot = field(floating ? 4 : 3);
		offset = B.CreateLoad(B.getInt32Ty(), offset_slot);
		if (!floating && alignment > 8) {
			offset = B.CreateAnd(B.CreateAdd(offset, B.getInt32(15)), B.getInt32(~15U));
		}
		next_offset = B.CreateAdd(offset, B.getInt32(floating ? 16 : ((size + 7) & ~7ULL)));
		B.CreateStore(next_offset, offset_slot);
		B.CreateCondBr(B.CreateICmpSLE(next_offset, B.getInt32(0)), register_block, stack_block);
		top_index = floating ? 2 : 1;
		stack_index = 0;
	} else {
		offset_slot = field(floating ? 1 : 0);
		offset = B.CreateLoad(B.getInt32Ty(), offset_slot);
		const unsigned step = floating ? 16 : ((size + 7) & ~7ULL);
		next_offset = B.CreateAdd(offset, B.getInt32(step));
		B.CreateCondBr(B.CreateICmpULE(offset, B.getInt32((floating ? 176 : 48) - step)),
					   register_block, stack_block);
		top_index = 3;
		stack_index = 2;
	}
	B.SetInsertPoint(register_block);
	auto *top = B.CreateLoad(l_.llvm_ptr(), field(top_index));
	auto *wide_offset = triple.getArch() == llvm::Triple::aarch64
		? B.CreateSExt(offset, B.getInt64Ty()) : B.CreateZExt(offset, B.getInt64Ty());
	auto *register_pointer = B.CreateGEP(B.getInt8Ty(), top, wide_offset);
	if (triple.getArch() == llvm::Triple::x86_64) { B.CreateStore(next_offset, offset_slot); }
	B.CreateBr(merge_block);
	B.SetInsertPoint(stack_block);
	auto *stack_pointer = stack_argument(stack_index);
	B.CreateBr(merge_block);
	B.SetInsertPoint(merge_block);
	auto *pointer = B.CreatePHI(l_.llvm_ptr(), 2, "va.argument");
	pointer->addIncoming(register_pointer, register_block);
	pointer->addIncoming(stack_pointer, stack_block);
	return B.CreateAlignedLoad(value_type, pointer, llvm::Align(1));
}

llvm::Type *Codegen::map_abi_type(StType *t) {
	StType *u = underlying_type(t);
	if (!u || u->kind != TypeKind::Union) {
		return map_type(t);
	}
	llvm::Type *storage = map_type(u);
	if (!storage->isStructTy() || u->fields.empty()) {
		return storage;
	}
	auto	   &dl		 = l_.module().getDataLayout();
	uint64_t	max_size = 0;
	llvm::Align max_align(1);
	StType	   *carrier		 = nullptr;
	uint64_t	carrier_size = 0;
	for (auto *f : u->fields) {
		llvm::Type *ft = map_type(f);
		uint64_t	sz = dl.getTypeAllocSize(ft);
		llvm::Align al = dl.getABITypeAlign(ft);
		if (sz > max_size) {
			max_size = sz;
		}
		if (al > max_align || (al == max_align && sz > carrier_size)) {
			max_align	 = al;
			carrier		 = underlying_type(f);
			carrier_size = sz;
		}
	}
	if (carrier && carrier->kind == TypeKind::Array && carrier->base && carrier_size == max_size) {
		StType *elem = underlying_type(carrier->base);
		if (elem && elem->kind == TypeKind::Float) {
			return llvm::VectorType::get(map_type(elem), carrier->array_len, false);
		}
	}
	return storage;
}

llvm::FunctionType *Codegen::map_fn_type(StType *t) {
	t = underlying_type(t);
	if (!t || t->kind != TypeKind::Function) {
		// Treat null/void as a nullary void-returning fn.
		return llvm::FunctionType::get(l_.llvm_void(), false);
	}
	std::vector<llvm::Type *> params;
	for (auto *p : t->fn_params) {
		if (p && p->kind == TypeKind::Type) {
			continue;
		}
		params.push_back(map_abi_type(p));
	}
	return llvm::FunctionType::get(map_abi_type(t->fn_ret), params, t->fn_variadic);
}

llvm::Value *Codegen::to_abi_value(llvm::Value *v, llvm::Type *dst) {
	if (!v || v->getType() == dst) {
		return v;
	}
	if (auto *vec = llvm::dyn_cast<llvm::VectorType>(dst)) {
		llvm::Value *src = v;
		if (auto *st = llvm::dyn_cast<llvm::StructType>(src->getType())) {
			if (st->getNumElements() == 1) {
				src = builder_->CreateExtractValue(src, {0}, "abi.carrier");
			}
		}
		if (auto *arr = llvm::dyn_cast<llvm::ArrayType>(src->getType())) {
			if (arr->getNumElements() == vec->getElementCount().getFixedValue() &&
				arr->getElementType() == vec->getElementType()) {
				llvm::Value *out = llvm::UndefValue::get(dst);
				for (unsigned i = 0; i < arr->getNumElements(); ++i) {
					out = builder_->CreateInsertElement(
						out, builder_->CreateExtractValue(src, {i}, "abi.elem"), i, "abi.vec");
				}
				return out;
			}
		}
	}
	return builder_->CreateBitCast(v, dst);
}

llvm::Value *Codegen::from_abi_value(llvm::Value *v, llvm::Type *dst) {
	if (!v || v->getType() == dst) {
		return v;
	}
	auto *vec = llvm::dyn_cast<llvm::VectorType>(v->getType());
	auto *st  = llvm::dyn_cast<llvm::StructType>(dst);
	if (vec && st && st->getNumElements() == 1) {
		auto *arr = llvm::dyn_cast<llvm::ArrayType>(st->getElementType(0));
		if (arr && arr->getNumElements() == vec->getElementCount().getFixedValue() &&
			arr->getElementType() == vec->getElementType()) {
			llvm::Value *array = llvm::UndefValue::get(arr);
			for (unsigned i = 0; i < arr->getNumElements(); ++i) {
				auto *index = llvm::ConstantInt::get(l_.llvm_int(32), i);
				array = builder_->CreateInsertValue(
					array, builder_->CreateExtractElement(v, index, "abi.elem"), {i}, "abi.array");
			}
			llvm::Value *aggregate = llvm::UndefValue::get(st);
			return builder_->CreateInsertValue(aggregate, array, {0}, "abi.union");
		}
	}
	log::report(log::Level::Error, {}, "cannot convert ABI value to its Stella storage type",
				"E_CODEGEN_FAILURE", "backend");
	return llvm::UndefValue::get(dst);
}

llvm::Type *Codegen::map_named_struct(StType *t) {
	if (!t || t->kind != TypeKind::Struct) {
		return l_.llvm_void();
	}
	auto it = structs_.find(t->name);
	if (it != structs_.end()) {
		return it->second;
	}
	auto *st		  = llvm::StructType::create(l_.ctx(), t->name);
	structs_[t->name] = st;
	if (t->is_opaque) {
		return st;
	}
	std::vector<llvm::Type *> fields;
	for (auto *f : t->fields) {
		fields.push_back(map_type(f));
	}
	st->setBody(fields);
	if (t->layout_size || t->layout_align) {
		const auto &data_layout = l_.module().getDataLayout();
		const uint64_t actual_size = data_layout.getTypeAllocSize(st).getFixedValue();
		const uint64_t actual_align = data_layout.getABITypeAlign(st).value();
		if (t->layout_size && *t->layout_size != actual_size) {
			log::report(log::Level::Error, t->layout_loc,
						"layout guarantee for struct '" + t->name + "' failed: expected size " +
							std::to_string(*t->layout_size) + ", target ABI size is " +
							std::to_string(actual_size), "E_LAYOUT_MISMATCH", "sema");
		}
		if (t->layout_align && *t->layout_align != actual_align) {
			log::report(log::Level::Error, t->layout_loc,
						"layout guarantee for struct '" + t->name + "' failed: expected alignment " +
							std::to_string(*t->layout_align) + ", target ABI alignment is " +
							std::to_string(actual_align), "E_LAYOUT_MISMATCH", "sema");
		}
	}
	return st;
}

llvm::Type *Codegen::map_named_union(StType *t) {
	if (!t || t->kind != TypeKind::Union) {
		return l_.llvm_void();
	}
	std::string key = "union:" + t->name;
	auto		it	= structs_.find(key);
	if (it != structs_.end()) {
		return it->second;
	}
	auto *ut	  = llvm::StructType::create(l_.ctx(), "U_" + t->name);
	structs_[key] = ut;
	if (t->fields.empty()) {
		ut->setBody({llvm::Type::getInt8Ty(l_.ctx())});
		return ut;
	}
	auto	   &dl		 = l_.module().getDataLayout();
	uint64_t	max_size = 0;
	llvm::Align max_align(1);
	StType	   *carrier_st	 = nullptr;
	llvm::Type *carrier_lt	 = nullptr;
	uint64_t	carrier_size = 0;
	for (auto *f : t->fields) {
		llvm::Type *ft	  = map_type(f);
		uint64_t	size  = dl.getTypeAllocSize(ft);
		llvm::Align align = dl.getABITypeAlign(ft);
		if (size > max_size) {
			max_size = size;
		}
		if (align > max_align || (align == max_align && size > carrier_size)) {
			max_align	 = align;
			carrier_size = size;
			carrier_st	 = f;
			carrier_lt	 = ft;
		}
	}
	const uint64_t alignment = max_align.value();
	uint64_t	  union_size = max_size;
	const uint64_t remainder = max_size % alignment;
	if (remainder != 0) {
		const uint64_t padding = alignment - remainder;
		if (max_size > std::numeric_limits<uint64_t>::max() - padding) {
			log::report(log::Level::Error, {},
						"layout of union '" + t->name + "' exceeds the maximum representable size");
			ut->setBody({llvm::Type::getInt8Ty(l_.ctx())});
			return ut;
		}
		union_size += padding;
	}
	const int pointer_width = t_.pointer_width();
	if (pointer_width > 0 && pointer_width < 64 &&
		union_size > ((uint64_t{1} << pointer_width) - 1)) {
		log::report(log::Level::Error, {},
					"layout of union '" + t->name + "' does not fit the target usize type");
		ut->setBody({llvm::Type::getInt8Ty(l_.ctx())});
		return ut;
	}
	uint64_t				  pad = union_size - carrier_size;
	std::vector<llvm::Type *> body{carrier_lt};
	if (pad) {
		body.push_back(llvm::ArrayType::get(l_.llvm_int(8), pad));
	}
	ut->setBody(body, false);
	(void)carrier_st;
	return ut;
}

} // namespace stellac