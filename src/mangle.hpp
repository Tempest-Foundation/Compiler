#pragma once

#include <string>
#include <string_view>
#include <vector>

namespace stellac {

struct Module;

// Mangle a fully-qualified symbol as `$segment.segment`.
std::string				 mangle(const std::vector<std::string> &segments);

// Demangle a symbol into its path segments. Any `#` signature is discarded.
std::vector<std::string> demangle(const std::string &sym);

// Join a path with "." (no leading $). Used both as the mangle body and as the
// canonical module-key / display-path separator.
std::string				 join_path(const std::vector<std::string> &segs);

// Mangle a top-level symbol `name` declared in module `m`: appends `name` to
// `m.mod_path` then calls mangle(). Convenience for the common 4 decl kinds
// (Struct/TypeBinding/Var/Const/Enum) that have no owner-path.
std::string				 mangle_in(const Module &m, std::string_view name);

struct StType;
struct FnDecl;
struct GlobalDecl;

// Mangle type encoding into string
std::string mangle_type(const StType *t);

// Mangle a function path, adding `#type,type` when it has parameters.
std::string mangle_fn(const Module &m, const FnDecl &f);

// Linker/IR symbol for a global. Private globals receive a deterministic
// source-module scope and use local linkage in their owning object.
std::string mangle_global(const Module &m, const GlobalDecl &g);
std::string private_global_scope_suffix(const Module &m);

} // namespace stellac