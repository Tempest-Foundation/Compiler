#include "mangle.hpp"
#include "ast.hpp"
#include "symbol.hpp"


namespace stellac {

std::string join_path(const std::vector<std::string> &segs) {
	std::string r;
	for (size_t i = 0; i < segs.size(); ++i) {
		if (i) {
			r += ".";
		}
		r += segs[i];
	}
	return r;
}

static std::vector<std::string> identity_prefix(const Module &m) {
	if (!m.mod_path.empty()) {
		return m.mod_path;
	}
	// A headerless source file contributes to the global namespace. Its
	// filesystem path only controls import resolution and must not become part
	// of the externally visible symbol identity.
	return {};
}

std::string mangle(const std::vector<std::string> &segs) {
	std::string result = "$";
	result += join_path(segs);
	return result;
}

std::string mangle_in(const Module &m, std::string_view name) {
	std::vector<std::string> segs = identity_prefix(m);
	segs.emplace_back(name);
	return mangle(segs);
}

std::vector<std::string> demangle(const std::string &sym) {
	// The overload part is metadata on the final path component, not another
	// module/name component.  Ignore it here: callers of demangle() use the
	// result to recover module paths, and the type information is already
	// available from the resolved declaration.
	const size_t			 signature	= sym.find('#');
	const size_t			 body_start = sym.compare(0, 1, "$") == 0 ? 1 : 0;
	const size_t			 body_end	= signature == std::string::npos ? sym.size() : signature;

	std::vector<std::string> out;
	if (body_start >= body_end) {
		return out;
	}

	size_t begin = body_start;
	while (begin < body_end) {
		size_t end = sym.find('.', begin);
		if (end == std::string::npos || end > body_end) {
			end = body_end;
		}
		if (end > begin) {
			out.emplace_back(sym, begin, end - begin);
		}
		if (end == body_end) {
			break;
		}
		begin = end + 1;
	}
	return out;
}

std::string mangle_type(const StType *t) {
	t = underlying_type(t);
	if (!t) {
		return "unk";
	}
	switch (t->kind) {
	case TypeKind::Void:
		return "v";
	case TypeKind::Bool:
		return "b";
	case TypeKind::UInt:
		return t->name == "usize" ? "usize" : "u" + std::to_string(t->width);
	case TypeKind::SInt:
		return t->name == "isize" ? "isize" : "i" + std::to_string(t->width);
	case TypeKind::Float:
		return "f" + std::to_string(t->width);
	case TypeKind::Pointer:
		return std::string("P") + (t->is_mutable ? "M" : "") + (t->is_volatile ? "V" : "") +
			   mangle_type(t->base);
	case TypeKind::Array:
		return "A" + std::to_string(t->array_len) + "_" + mangle_type(t->base);
	case TypeKind::Struct:
		return "S_" + t->name;
	case TypeKind::Union:
		return "U_" + t->name;
	case TypeKind::TypeBinding:
		return t->base ? mangle_type(t->base) : "unk";
	case TypeKind::Enum:
	case TypeKind::Opaque:
		return "S_" + t->name;
	case TypeKind::VaList:
		return "va.list";
	case TypeKind::Poison:
		return "poison";
	case TypeKind::Function: {
		std::string r = "F";
		for (auto *p : t->fn_params) {
			r += mangle_type(p) + "_";
		}
		if (t->fn_variadic) {
			r += "V_";
		}
		r += "R_" + mangle_type(t->fn_ret);
		return r;
	}
	case TypeKind::Type:
		return "type";
	case TypeKind::SelfType:
		return "Self";
	}
	return "unk";
}

std::string mangle_fn(const Module &m, const FnDecl &f) {
	const Attribute *ex			 = find_attr(f.attrs, "export");
	std::string		 export_name = ex && !ex->args.empty() ? ex->args[0] : std::string{};
	if (ex || f.is_extern) {
		return export_name.empty() ? f.name : export_name;
	}

	std::vector<std::string> segs = identity_prefix(m);
	if (f.full_path.empty() || m.mod_path.empty()) {
		for (auto &o : f.owner_path) {
			segs.push_back(o);
		}
		segs.push_back(f.name);
	} else {
		segs = f.full_path;
	}
	std::string base = mangle(segs);

	// A function's parameter list is part of its symbol identity whenever it
	// has one.  This keeps separately declared functions distinguishable even
	// before overload resolution and gives symbols the stable, readable form:
	//
	//     $std.math.pow#f64,f64
	//
	// A parameterless function retains the shorter `$module.name` spelling.
	if (f.params.empty() && !f.is_variadic) {
		return base;
	}
	base += "#";
	for (size_t i = 0; i < f.params.size(); ++i) {
		if (i > 0) {
			base += ",";
		}
		base += mangle_type(f.params[i].resolved);
	}
	if (f.is_variadic) {
		if (!f.params.empty()) {
			base += ",";
		}
		base += "...";
	}
	return base;
}

std::string mangle_global(const Module &m, const GlobalDecl &g) {
	const Attribute *ex = find_attr(g.attrs, "export");
	if (ex) {
		return ex->args.empty() ? g.name : ex->args[0];
	}
	std::vector<std::string> segs = identity_prefix(m);
	segs.insert(segs.end(), g.owner_path.begin(), g.owner_path.end());
	segs.push_back(g.name);
	std::string result = mangle(segs);
	if (!g.is_pub) {
		// Private globals can be cloned into an importing LLVM module for
		// optimization. Scope them by the owning source file's path relative to
		// the entry source directory, not by resolver order or checkout location.
		// This keeps same-named declarations distinct in one LLVM module while
		// preserving symbol names when the source tree moves.
		result += private_global_scope_suffix(m);
	}
	return result;
}

std::string private_global_scope_suffix(const Module &m) {
	return "#priv." + m.private_symbol_module_id;
}

} // namespace stellac