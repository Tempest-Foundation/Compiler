#include "codegen.hpp"
#include "ctx.hpp"
#include "depfile.hpp"
#include "lexer.hpp"
#include "log.hpp"
#include "module_resolver.hpp"
#include "parser.hpp"
#include "sema.hpp"
#include "types.hpp"

#include "llvm/Support/FileSystem.h"
#include "llvm/Support/Path.h"
#include "llvm/TargetParser/Host.h"
#include "llvm/TargetParser/Triple.h"

#include <algorithm>
#include <cerrno>
#include <charconv>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <fcntl.h>
#include <filesystem>
#include <fstream>
#include <iostream>
#include <iterator>
#include <optional>
#include <sstream>
#include <string>
#include <sys/wait.h>
#include <unistd.h>
#include <vector>

using namespace stellac;

namespace {

constexpr const char *STELLA_PACKAGE_RELATIVE_DIR = "share/stella";
constexpr const char *STELLA_STD_RELATIVE_DIR	  = "share/stella/std";
constexpr const char *STELLA_RUNTIME_RELATIVE_DIR = "lib/stella";

enum class CliModule { Build, Emit, Opt, Target, Link, Runtime, Source, Diagnostics };
enum class RelroMode { None, Partial, Full };

struct CliOption {
	CliModule		 module;
	std::string_view name;
	std::string_view value;
	bool			 has_value = false;
};

static std::optional<CliModule> cli_module_from_name(std::string_view name) {
	if (name == "build") {
		return CliModule::Build;
	}
	if (name == "emit") {
		return CliModule::Emit;
	}
	if (name == "opt") {
		return CliModule::Opt;
	}
	if (name == "tar") {
		return CliModule::Target;
	}
	if (name == "link") {
		return CliModule::Link;
	}
	if (name == "rt") {
		return CliModule::Runtime;
	}
	if (name == "src") {
		return CliModule::Source;
	}
	if (name == "diag") {
		return CliModule::Diagnostics;
	}
	return std::nullopt;
}

// Parse a command-line option as an actual module/member pair. In particular,
// do not recognize an option merely because it begins with a known module or
// member name: `--link.mode.extra` is not `--link.mode`.
static std::optional<CliOption> parse_cli_option(std::string_view arg) {
	if (arg.size() < 3 || arg.substr(0, 2) != "--") {
		return std::nullopt;
	}

	std::string_view body	= arg.substr(2);
	size_t			 equals = body.find('=');
	std::string_view key	= body.substr(0, equals);
	std::string_view value;
	if (equals != std::string_view::npos) {
		value = body.substr(equals + 1);
	}

	size_t dot = key.find('.');
	if (dot != std::string_view::npos) {
		if (dot == 0 || dot + 1 == key.size() || key.find('.', dot + 1) != std::string_view::npos) {
			return std::nullopt;
		}
		auto module = cli_module_from_name(key.substr(0, dot));
		if (!module) {
			return std::nullopt;
		}
		return CliOption{*module, key.substr(dot + 1), value, equals != std::string_view::npos};
	}

	return std::nullopt;
}

void usage() {
	std::cerr << "Usage: stellac <input.sl> [--build.output=<path>] [--build.compile-only]\n"
				 "                     [--emit.ir] [--emit.depfile[=<path>]]\n"
				 "                     [--opt.level=<none*|low|medium|high|size>]\n"
				 "                     [--opt.lto=<none*|thin|full>]\n"
				 "                     [--tar.triple=<triple>]\n"
				 "                     [--tar.cpu=<generic*|cpu|native>]\n"
				 "                     [--tar.tune=<generic*|cpu|native>]\n"
				 "                     [--tar.relocation=<static*|pic>]\n"
				 "                     [--tar.code-model=<tiny|small*|kernel|medium|large>]\n"
				 "                     [--tar.sysroot=<path>]\n"
				 "                     [--link.lib=<name> ...]\n"
				 "                     [--link.mode=<dynamic*|static>]\n"
				 "                     [--link.relro=<none*|partial|full>]\n"
				 "                     [--link.driver=<driver>]\n"
				 "                     [--link.program=<linker>]\n"
				 "                     [--link.dynamic-loader=<path>]\n"
				 "                     [--rt.start=<stella*|crt>]\n"
				 "                     [--src.define=<flag> ...]\n"
				 "                     [--src.include=<dir>]\n"
				 "                     [--src.no-auto-include]\n"
				 "                     [--diag.warn-error]\n"
				 "                     [--diag.format=<human*|json>]\n"
				 "                     [--diag.color=<auto*|always|never>]\n"
				 "                     [--diag.error-limit=<n>]\n";
}

static void cli_error(const std::string &message,
					  const std::string &code = "E_CLI_INVALID_OPTION") {
	log::report(log::Level::Error, {}, message, code, "cli");
}

static void derive_target_flags(const TargetInfo &t, SemaOptions &opts) {
	opts.flags[std::string("arch_") + t.arch]				  = true;
	opts.flags[std::string("os_") + t.os]					  = true;
	opts.flags[std::string("bits_") + std::to_string(t.bits)] = true;
}

static const char *lto_mode_name(LtoMode mode) {
	switch (mode) {
	case LtoMode::Full:
		return "full";
	case LtoMode::Thin:
		return "thin";
	default:
		return "none";
	}
}

static const char *relocation_model_name(TargetInfo::RelocationModel model) {
	return model == TargetInfo::RelocationModel::PIC ? "pic" : "static";
}

static bool run_command(std::vector<std::string> argv_strs, std::string *detail = nullptr) {
	std::vector<char *> argv_c;
	argv_c.reserve(argv_strs.size() + 1);
	for (auto &s : argv_strs) {
		argv_c.push_back(s.data());
	}
	argv_c.push_back(nullptr);

	char  diagnostic_template[] = "/tmp/stellac-command-XXXXXX";
	int	  diagnostic_fd			= mkstemp(diagnostic_template);
	pid_t pid					= fork();
	if (pid < 0) {
		if (diagnostic_fd >= 0) {
			close(diagnostic_fd);
			unlink(diagnostic_template);
		}
		cli_error("fork() failed", "E_LINK_COMMAND");
		return false;
	}
	if (pid == 0) {
		if (diagnostic_fd >= 0) {
			int redirected = STDERR_FILENO;
			if (diagnostic_fd != STDERR_FILENO) {
				do {
					redirected = dup2(diagnostic_fd, STDERR_FILENO);
				} while (redirected < 0 && errno == EINTR);
			}
			if (redirected < 0) {
				_exit(126);
			}
			if (diagnostic_fd != STDERR_FILENO) {
				close(diagnostic_fd);
			}
		}
		execvp(argv_c[0], argv_c.data());
		_exit(127);
	}
	if (diagnostic_fd >= 0) {
		close(diagnostic_fd);
	}

	int status = 0;
	while (waitpid(pid, &status, 0) < 0) {
		if (errno == EINTR) {
			continue;
		}
		if (diagnostic_fd >= 0) {
			close(diagnostic_fd);
			unlink(diagnostic_template);
		}
		cli_error("waitpid failed", "E_LINK_COMMAND");
		return false;
	}
	if (detail && diagnostic_fd >= 0) {
		std::ifstream	  diagnostics(diagnostic_template, std::ios::binary);
		std::stringstream contents;
		contents << diagnostics.rdbuf();
		*detail = contents.str();
	}
	if (diagnostic_fd >= 0) {
		unlink(diagnostic_template);
	}
	return WIFEXITED(status) && WEXITSTATUS(status) == 0;
}

// Prefer paths next to the installed executable. This makes
// `cmake --install --prefix=...` work as expected even though the compiler
// was built with a different default prefix, and also permits a prefix to be
// moved as one directory tree.
static std::string installed_path(const char *argv0, const char *relative_path) {
	std::string executable =
		llvm::sys::fs::getMainExecutable(argv0, reinterpret_cast<void *>(&installed_path));
	if (!executable.empty()) {
		std::filesystem::path prefix =
			std::filesystem::path(executable).parent_path().parent_path();
		std::filesystem::path candidate = prefix / relative_path;
		if (llvm::sys::fs::exists(candidate.string())) {
			return candidate.string();
		}
	}
	return {};
}

static bool path_is_within(const std::string &path, const std::string &root) {
	if (path.empty() || root.empty()) {
		return false;
	}
	std::error_code		  path_ec;
	std::filesystem::path child = std::filesystem::weakly_canonical(path, path_ec);
	if (path_ec) {
		return false;
	}
	std::filesystem::path parent = std::filesystem::weakly_canonical(root, path_ec);
	if (path_ec) {
		return false;
	}
	child  = child.lexically_normal();
	parent = parent.lexically_normal();
	for (auto child_it = child.begin(), parent_it = parent.begin();
		 child_it != child.end() && parent_it != parent.end(); ++child_it, ++parent_it) {
		if (*child_it != *parent_it) {
			return false;
		}
	}
	return std::distance(parent.begin(), parent.end()) <= std::distance(child.begin(), child.end());
}

static bool shared_runtime_target_matches_host(const std::string &target_triple) {
	llvm::Triple requested(llvm::Triple::normalize(target_triple));
	llvm::Triple host(llvm::Triple::normalize(llvm::sys::getDefaultTargetTriple()));
	return requested.getArch() == host.getArch() && requested.getOS() == host.getOS() &&
		   requested.getEnvironment() == host.getEnvironment() &&
		   requested.getObjectFormat() == host.getObjectFormat();
}

static std::string dynamic_linker_for(const llvm::Triple &triple) {
	if (triple.getOS() != llvm::Triple::Linux) {
		return {};
	}
	switch (triple.getArch()) {
	case llvm::Triple::x86_64:
		return "/lib64/ld-linux-x86-64.so.2";
	case llvm::Triple::x86:
		return "/lib/ld-linux.so.2";
	case llvm::Triple::aarch64:
		return "/lib/ld-linux-aarch64.so.1";
	case llvm::Triple::riscv64:
		return "/lib/ld-linux-riscv64-lp64d.so.1";
	default:
		return {};
	}
}

static bool is_clang_driver(const std::string &driver) {
	const std::string name = std::filesystem::path(driver).filename().string();
	return name == "clang" || name == "clang++" || name.rfind("clang-", 0) == 0 ||
		   name.find("-clang") != std::string::npos;
}

struct TemporaryOutput {
	std::string path;

	~TemporaryOutput() {
		if (!path.empty()) {
			std::error_code ignored;
			std::filesystem::remove(path, ignored);
		}
	}
};

} // namespace

int main(int argc, char **argv) {
	log::reset();
	struct DiagnosticFinish {
		~DiagnosticFinish() {
			log::finish();
		}
	} diagnostic_finish;
	std::string					input;
	std::string					output;
	bool						emit_ir			 = false;
	bool						compile_only	 = false;
	bool						warning_as_error = false;
	bool						emit_depfile	 = false;
	std::string					depfile_path;
	OptLevel					opt_level		 = OptLevel::None;
	LtoMode						lto				 = LtoMode::None;
	std::string					link_mode		 = "dynamic";
	RelroMode					relro_mode		 = RelroMode::None;
	TargetInfo::RelocationModel relocation_model = TargetInfo::RelocationModel::Static;
	std::string					target_triple	 = llvm::sys::getDefaultTargetTriple();
	std::string					cpu_specific	 = "generic";
	std::string					cpu_tune		 = "generic";
	std::string					code_model		 = "small";
	std::string					linker			 = "cc";
	std::string					raw_linker		 = "ld.lld";
	std::string					startup			 = "stella";
	std::string					dynamic_linker;
	std::string					target_sysroot;
	std::vector<std::string>	import_roots;
	bool							 auto_include_packages = true;
	std::vector<std::string>	libraries;
	std::vector<std::string>	user_defines;
	std::string					diagnostic_format = "human";
	std::string					color_mode		  = "auto";
	int							error_limit		  = 20;
	SemaOptions					opts;
	auto						configure_diagnostics = [&]() {
		log::Format format = diagnostic_format == "json" ? log::Format::Json : log::Format::Human;
		log::Color	color  = color_mode == "always"
								 ? log::Color::Always
								 : (color_mode == "never" ? log::Color::Never : log::Color::Auto);
		log::configure(format, color, error_limit);
	};
	configure_diagnostics();

	for (int i = 1; i < argc; ++i) {
		std::string_view a = argv[i];
		if (a == "--help" || a == "-h") {
			usage();
			return 0;
		}

		auto option = parse_cli_option(a);
		if (option) {
			auto require_value = [&]() {
				if (!option->has_value || option->value.empty()) {
					cli_error(std::string(a) + " requires a value");
					return false;
				}
				return true;
			};
			auto reject_value = [&]() {
				if (option->has_value) {
					cli_error(std::string(a) + " does not take a value");
					return false;
				}
				return true;
			};

			if (option->module == CliModule::Build && option->name == "output") {
				if (!require_value()) {
					return 1;
				}
				output = option->value;
			} else if (option->module == CliModule::Build && option->name == "compile-only") {
				if (!reject_value()) {
					return 1;
				}
				compile_only = true;
			} else if (option->module == CliModule::Emit && option->name == "ir") {
				if (!reject_value()) {
					return 1;
				}
				emit_ir = true;
			} else if (option->module == CliModule::Emit && option->name == "depfile") {
				if (option->has_value && option->value.empty()) {
					cli_error(std::string(a) + " requires a path when '=' is used");
					return 1;
				}
				emit_depfile = true;
				if (option->has_value) {
					depfile_path = option->value;
				}
			} else if (option->module == CliModule::Opt && option->name == "level") {
				if (!require_value()) {
					return 1;
				}
				auto level = opt_level_from_string(option->value);
				if (!level) {
					cli_error(std::string(a) + " must be one of: none, low, medium, high, size");
					return 1;
				}
				opt_level = *level;
			} else if (option->module == CliModule::Opt && option->name == "lto") {
				if (!require_value()) {
					return 1;
				}
				auto mode = lto_mode_from_string(std::string(option->value));
				if (!mode) {
					cli_error(std::string(a) + " must be one of: none, thin, full");
					return 1;
				}
				lto = *mode;
			} else if (option->module == CliModule::Target && option->name == "triple") {
				if (!require_value()) {
					return 1;
				}
				target_triple = option->value;
			} else if (option->module == CliModule::Target && option->name == "cpu") {
				if (!require_value()) {
					return 1;
				}
				cpu_specific = option->value;
			} else if (option->module == CliModule::Target && option->name == "tune") {
				if (!require_value()) {
					return 1;
				}
				cpu_tune = option->value;
			} else if (option->module == CliModule::Target && option->name == "relocation") {
				if (!require_value()) {
					return 1;
				}
				auto model = relocation_model_from_string(std::string(option->value));
				if (!model) {
					cli_error(std::string(a) + " must be one of: static, pic");
					return 1;
				}
				relocation_model = *model;
			} else if (option->module == CliModule::Target && option->name == "code-model") {
				if (!require_value()) {
					return 1;
				}
				code_model = option->value;
				if (!code_model_from_string(code_model)) {
					cli_error(std::string(a) +
							  " must be one of: tiny, small, kernel, medium, large");
					return 1;
				}
			} else if (option->module == CliModule::Target && option->name == "sysroot") {
				if (!require_value()) {
					return 1;
				}
				target_sysroot = option->value;
			} else if (option->module == CliModule::Link && option->name == "lib") {
				if (!require_value()) {
					return 1;
				}
				libraries.push_back(std::string(option->value));
			} else if (option->module == CliModule::Link && option->name == "mode") {
				if (!require_value()) {
					return 1;
				}
				link_mode = option->value;
				if (link_mode != "dynamic" && link_mode != "static") {
					cli_error(std::string(a) + " must be one of: dynamic, static");
					return 1;
				}
			} else if (option->module == CliModule::Link && option->name == "relro") {
				if (!require_value()) {
					return 1;
				}
				if (option->value == "none") {
					relro_mode = RelroMode::None;
				} else if (option->value == "partial") {
					relro_mode = RelroMode::Partial;
				} else if (option->value == "full") {
					relro_mode = RelroMode::Full;
				} else {
					cli_error(std::string(a) + " must be one of: none, partial, full");
					return 1;
				}
			} else if (option->module == CliModule::Link && option->name == "driver") {
				if (!require_value()) {
					return 1;
				}
				linker = option->value;
			} else if (option->module == CliModule::Link && option->name == "program") {
				if (!require_value()) {
					return 1;
				}
				raw_linker = option->value;
			} else if (option->module == CliModule::Link && option->name == "dynamic-loader") {
				if (!require_value()) {
					return 1;
				}
				dynamic_linker = option->value;
			} else if (option->module == CliModule::Runtime && option->name == "start") {
				if (!require_value()) {
					return 1;
				}
				startup = option->value;
				if (startup != "stella" && startup != "crt") {
					cli_error(std::string(a) + " must be one of: stella, crt");
					return 1;
				}
			} else if (option->module == CliModule::Source && option->name == "define") {
				if (!require_value()) {
					return 1;
				}
				user_defines.push_back(std::string(option->value));
				opts.flags[std::string(option->value)] = true;
			} else if (option->module == CliModule::Source && option->name == "include") {
				if (!require_value()) {
					return 1;
				}
				import_roots.push_back(std::string(option->value));
			} else if (option->module == CliModule::Source && option->name == "no-auto-include") {
				if (!reject_value()) {
					return 1;
				}
				auto_include_packages = false;
			} else if (option->module == CliModule::Diagnostics && option->name == "warn-error") {
				if (!reject_value()) {
					return 1;
				}
				warning_as_error = true;
			} else if (option->module == CliModule::Diagnostics && option->name == "format") {
				if (!require_value()) {
					return 1;
				}
				diagnostic_format = option->value;
				if (diagnostic_format != "human" && diagnostic_format != "json") {
					cli_error(std::string(a) + " must be one of: human, json");
					return 1;
				}
				configure_diagnostics();
			} else if (option->module == CliModule::Diagnostics && option->name == "color") {
				if (!require_value()) {
					return 1;
				}
				color_mode = option->value;
				if (color_mode != "auto" && color_mode != "always" && color_mode != "never") {
					cli_error(std::string(a) + " must be one of: auto, always, never");
					return 1;
				}
				configure_diagnostics();
			} else if (option->module == CliModule::Diagnostics && option->name == "error-limit") {
				if (!require_value()) {
					return 1;
				}
				int	 parsed = -1;
				auto result = std::from_chars(option->value.data(),
											  option->value.data() + option->value.size(), parsed);
				if (result.ec != std::errc() ||
					result.ptr != option->value.data() + option->value.size() || parsed < 0) {
					cli_error(std::string(a) + " requires a non-negative integer");
					return 1;
				}
				error_limit = parsed;
				configure_diagnostics();
			} else {
				cli_error("unknown option '" + std::string(a) + "'");
				return 1;
			}
			continue;
		}

		if (a.rfind("--", 0) == 0) {
			cli_error("unknown option '" + std::string(a) + "'");
			return 1;
		}
		if (input.empty()) {
			input = a;
		} else {
			cli_error("unexpected argument '" + std::string(a) + "'");
			usage();
			return 1;
		}
	}

	if (input.empty()) {
		cli_error("an input file is required", "E_CLI_MISSING_INPUT");
		usage();
		return 1;
	}
	if (output.empty()) {
		auto		dot	 = input.rfind('.');
		auto		sep	 = input.find_last_of("/\\");
		std::string base = (dot == std::string::npos ||
							 (sep != std::string::npos && dot < sep + 1) ||
							 (dot == (sep == std::string::npos ? 0 : sep + 1))
							 ? input
							 : input.substr(0, dot));
		if (emit_ir) {
			output = base + ".ll";
		} else if (compile_only) {
			output = base + ".o";
		} else {
			output = base;
		}
	}
	// The language package tree is installed as Stella source because imports
	// are resolved semantically before code generation. Add the package root
	// automatically so public paths remain explicit (`std/...`, `bind/...`),
	// while keeping the standard-library source root as a fallback for its
	// root-relative implementation imports (for example `arch/...`). Project
	// modules supplied through --src.include remain earlier in search order.
	const std::string default_package_dir =
		installed_path(argv[0], STELLA_PACKAGE_RELATIVE_DIR);
	const std::string default_std_dir = installed_path(argv[0], STELLA_STD_RELATIVE_DIR);
	auto add_default_import_root = [&](const std::string &root) {
		if (root.empty() || !llvm::sys::fs::exists(root)) {
			return;
		}
		if (std::find(import_roots.begin(), import_roots.end(), root) == import_roots.end()) {
			import_roots.push_back(root);
		}
	};
	if (auto_include_packages) {
		add_default_import_root(default_package_dir);
		add_default_import_root(default_std_dir);
	}

	log::set_file(input);
	log::set_warning_as_error(warning_as_error);

	std::string src;
	if (!read_file(input, src)) {
		cli_error("cannot read input `" + input + "`", "E_INPUT_READ");
		return 1;
	}

	ModuleResolver resolver;
	for (auto &r : import_roots) {
		resolver.add_import_root(r);
	}

	// Root source. A file-level `struct <name>;` header is optional: when it is
	// absent, declarations belong to the flat global namespace. The resolver
	// still marks this module as the executable root for the startup ABI.
	Lexer			   lexer(src, input);
	std::vector<Token> toks;
	if (!lexer.tokenize(toks)) {
		return 1;
	}
	auto   root_mod = std::make_unique<Module>();
	Parser parser(std::move(toks), input, {});
	if (!parser.parse_module(*root_mod)) {
		return 1;
	}

	resolver.set_root(std::move(root_mod));
	if (!resolver.root()) {
		cli_error("entry file declares no root module", "E_MODULE_ROOT");
		return 1;
	}

	// Target
	TargetInfo	 tgt;
	llvm::Triple triple(llvm::Triple::normalize(target_triple));
	tgt.triple = target_triple;
	tgt.arch   = triple.getArchName().str();
	tgt.os	   = triple.getOSName().str();
	tgt.bits   = static_cast<int>(triple.getArchPointerBitWidth());
	if (tgt.bits != 32 && tgt.bits != 64) {
		cli_error("unsupported target pointer width " + std::to_string(tgt.bits) +
					  " bits (only 32-bit and 64-bit targets are supported)",
				  "E_TARGET_UNSUPPORTED");
		return 1;
	}
	tgt.cpu_specific = cpu_specific;
	tgt.cpu_tune	 = cpu_tune;
	tgt.code_model	 = code_model;
	tgt.relocation	 = relocation_model;
	derive_target_flags(tgt, opts);
	opts.arch_flag = std::string("arch_") + tgt.arch;
	opts.os_flag   = std::string("os_") + tgt.os;
	opts.bits_flag = std::string("bits_") + std::to_string(tgt.bits);

	TypeContext types(tgt.bits);
	Sema		sema(resolver, types, std::move(opts));
	if (!sema.run()) {
		return 1;
	}
	const std::string canonical_output = canonicalize_dep_path(output);
	for (const auto &source : resolver.all_files()) {
		if (canonical_output == canonicalize_dep_path(source)) {
			cli_error("build output path must not overwrite an input source file",
				  "E_OUTPUT_PATH_COLLISION");
			return 1;
		}
	}

	LLVMCtx lctx;
	if (!lctx.init(tgt, opt_level)) {
		return 1;
	}

	Codegen cg(lctx, types, sema);
	// Cross-module inlining (a la `llvm-link` + `opt`): fold imported pub
	// function bodies into this TU so the LLVM pipeline can inline and
	// constant-propagate across module boundaries at compile time. Only
	// worthwhile when an optimization pipeline actually runs
	// (--opt.level=low/medium/high/size).
	cg.set_inline_imports(opt_level != OptLevel::None);
	if (!cg.emit_all(resolver)) {
		return 1;
	}

	if (log::has_error()) {
		return 1;
	}

	std::string		 obj_path = output;
	TemporaryOutput temporary_obj;
	if (!compile_only && !emit_ir) {
		char temporary_template[] = "/tmp/stellac-object-XXXXXX";
		int  temporary_fd		 = mkstemp(temporary_template);
		if (temporary_fd < 0) {
			cli_error("cannot create temporary object: " + std::string(std::strerror(errno)),
					  "E_EMIT_TEMP");
			return 1;
		}
		if (close(temporary_fd) != 0) {
			const int close_error = errno;
			std::error_code ignored;
			std::filesystem::remove(temporary_template, ignored);
			cli_error("cannot close temporary object: " + std::string(std::strerror(close_error)),
					  "E_EMIT_TEMP");
			return 1;
		}
		temporary_obj.path = temporary_template;
		obj_path			= temporary_obj.path;
	}

	if (!lctx.finalize_to_file(obj_path, emit_ir, opt_level, lto)) {
		cli_error("emission failed", "E_EMIT_FAILED");
		return 1;
	}

	// Emit depfile after a successful object/IR emit, before the link step:
	// a subsequent link failure must not erase the depfile (it documents the
	// inputs that produced the object, which is what make needs to rebuild).
	if (emit_depfile) {
		std::string df_path = depfile_path;
		if (df_path.empty()) {
			// Default: derive from output path, substitute extension with .d.
			auto sep = output.find_last_of("/\\");
			auto dot = output.find_last_of('.');
			if (dot == std::string::npos ||
				(sep != std::string::npos && dot <= sep + 1) ||
				(dot == 0 && sep == std::string::npos)) {
				df_path = output + ".d";
			} else {
				df_path = output.substr(0, dot) + ".d";
			}
		}
		const std::string canonical_depfile = canonicalize_dep_path(df_path);
		if (canonical_depfile == canonicalize_dep_path(output)) {
			cli_error("depfile path must not overwrite the build output", "E_DEPFILE_PATH_COLLISION");
			return 1;
		}
		for (const auto &source : resolver.all_files()) {
			if (canonical_depfile == canonicalize_dep_path(source)) {
				cli_error("depfile path must not overwrite an input source file",
					  "E_DEPFILE_PATH_COLLISION");
				return 1;
			}
		}
		// The final output is the only persistent make artifact in either mode.
		std::vector<std::string> targets;
		targets.push_back(output);
		// Prereqs: every .sl source that contributed to this translation
		// unit (entry + every file merged during import resolution).
		std::vector<std::string> prereqs = resolver.all_files();
		if (!write_depfile(df_path, targets, prereqs)) {
			cli_error("cannot write depfile `" + df_path + "`", "E_DEPFILE_WRITE");
			return 1;
		}
	}

	if (!compile_only && !emit_ir) {
		const bool		  is_wasm_target	 = tgt.arch == "wasm32" || tgt.arch == "wasm64";
		const bool		  use_crt			 = startup == "crt" && !is_wasm_target;
		const bool		  use_stella_startup = !is_wasm_target && !use_crt;
		// Use the compiler driver for its platform library search paths, while
		// retaining Stella's startup when external libraries are requested.
		const bool		  use_driver		 = !is_wasm_target && (use_crt || !libraries.empty());
		const std::string selected_dynamic_linker =
			dynamic_linker.empty() ? dynamic_linker_for(triple) : dynamic_linker;
		if (!target_sysroot.empty() && !llvm::sys::fs::is_directory(target_sysroot)) {
			cli_error("target sysroot is not a directory: `" + target_sysroot + "`",
					  "E_TARGET_SYSROOT");
			return 1;
		}
		std::string runtime_dir;
		std::string start_obj;
		if (!is_wasm_target) {
			runtime_dir = installed_path(argv[0], STELLA_RUNTIME_RELATIVE_DIR);
			if (!runtime_dir.empty() && llvm::sys::fs::exists(runtime_dir)) {
			} else {
				cli_error("stella runtime not found in `" + runtime_dir + "`",
						  "E_RUNTIME_NOT_FOUND");
				return 1;
			}

			if (use_stella_startup) {
				start_obj = runtime_dir + "/start.o";
				if (!llvm::sys::fs::exists(start_obj)) {
					cli_error("startup object `" + start_obj +
								  "` not found; is stella installed correctly?",
							  "E_RUNTIME_NOT_FOUND");
					return 1;
				}
			}
		}

		const std::string stellalib_shared_runtime = runtime_dir + "/stellalib.so.0";
		const std::string legacy_shared_runtime	   = runtime_dir + "/libstella.so.0";
		const std::string shared_runtime =
			llvm::sys::fs::exists(stellalib_shared_runtime) ? stellalib_shared_runtime : legacy_shared_runtime;
		const bool linker_supports_archive_groups = triple.isOSBinFormatELF();
		const bool shared_runtime_available = !is_wasm_target &&
											  llvm::sys::fs::exists(shared_runtime) &&
											  shared_runtime_target_matches_host(target_triple) &&
											  (use_crt || !selected_dynamic_linker.empty());
		bool	   use_dynamic_stella		= !is_wasm_target && link_mode == "dynamic";
		auto	   report_link_warning		= [&](const std::string &message) {
			log::report(log::Level::Warning, {}, message, "W_LINK_FALLBACK", "linker");
			if (log::warning_as_error()) {
				return false;
			}
			return true;
		};
		if (use_dynamic_stella && !shared_runtime_available) {
			if (!is_wasm_target && !shared_runtime.empty() &&
				!shared_runtime_target_matches_host(target_triple)) {
				if (!report_link_warning("shared Stella runtime does not match target '" +
										 target_triple + "'; falling back to static linking")) {
					return 1;
				}
			} else if (!use_crt && selected_dynamic_linker.empty()) {
				if (!report_link_warning("no dynamic linker configured for target '" +
										 target_triple + "'; falling back to static linking")) {
					return 1;
				}
			} else {
				if (!report_link_warning("shared Stella runtime is unavailable for target '" +
										 target_triple + "'; falling back to static linking")) {
					return 1;
				}
			}
			use_dynamic_stella = false;
		}

		// Imported Stella modules are declarations in the root object at -O0.
		// Link mode compiles them into temporary objects so bindings and local
		// modules work without a separate manual compile step.
		std::vector<std::string> imported_objects;
		char					 temp_template[] = "/tmp/stellac-link-XXXXXX";
		char					*temp_raw		 = mkdtemp(temp_template);
		if (!temp_raw) {
			cli_error("cannot create temporary link directory: " +
						  std::string(std::strerror(errno)),
					  "E_LINK_TEMP");
			return 1;
		}
		std::string temp_dir		= temp_raw;
		auto		cleanup_imports = [&]() {
			for (const auto &obj : imported_objects) {
				unlink(obj.c_str());
			}
			rmdir(temp_dir.c_str());
		};

		const std::string root_file	   = canonicalize_dep_path(input);
		size_t			  import_index = 0;
		for (const auto &source : resolver.all_module_files()) {
			if (canonicalize_dep_path(source) == root_file) {
				continue;
			}
			// Native stellalib owns definitions from the installed standard-library
			// source tree. WebAssembly has no runtime library here, so those sources
			// must remain among the temporary objects instead of being skipped.
			if (!is_wasm_target && path_is_within(source, default_std_dir)) {
				continue;
			}
			std::string obj = temp_dir + "/import-" + std::to_string(import_index++) + ".o";
			// Track the output before running the child: a failed compile can
			// leave a partial object that cleanup must remove with the others.
			imported_objects.push_back(obj);
			std::vector<std::string> child = {
				argv[0],
				source,
				"--build.compile-only",
				"--build.output=" + obj,
				"--tar.triple=" + target_triple,
				"--tar.cpu=" + cpu_specific,
				"--tar.tune=" + cpu_tune,
				"--tar.code-model=" + code_model,
				"--opt.level=" + std::string(opt_level_name(opt_level)),
				"--opt.lto=" + std::string(lto_mode_name(lto)),
				"--tar.relocation=" + std::string(relocation_model_name(relocation_model))};
			if (warning_as_error) {
				child.push_back("--diag.warn-error");
			}
			if (!auto_include_packages) {
				child.push_back("--src.no-auto-include");
			}
			for (const auto &root : import_roots) {
				child.push_back("--src.include=" + root);
			}
			for (const auto &define : user_defines) {
				child.push_back("--src.define=" + define);
			}
			std::string child_detail;
			if (!run_command(std::move(child), &child_detail)) {
				std::vector<log::Attachment> attachments;
				if (!child_detail.empty()) {
					attachments.push_back({"child compiler", child_detail});
				}
				log::report(log::Level::Error, {},
							"compiling imported module `" + source + "` failed", "E_MODULE_COMPILE",
							"resolver", {}, attachments);
				cleanup_imports();
				return 1;
			}
		}

		// Startup selection is independent from external libraries. `stella`
		// uses the installed freestanding startup object and raw linker; `crt`
		// uses the selected compiler driver and expects a C-visible `main`
		// entry point (usually supplied with #[export("main")]).
		std::vector<std::string> argv_strs;
		if (is_wasm_target) {
			// WebAssembly has no ELF CRT or freestanding x86 starter. Link
			// the module without imposing an entry function on Stella code.
			argv_strs = {"wasm-ld", "--no-entry"};
		} else if (use_driver) {
			argv_strs = {linker};
			if (is_clang_driver(linker)) {
				argv_strs.push_back("--target=" + target_triple);
			}
			if (!target_sysroot.empty()) {
				argv_strs.push_back("--sysroot=" + target_sysroot);
			}
			if (!use_crt) {
				// The driver is only a linker frontend in Stella-startup mode.
				// Do not add its CRT, libc, or default entry point.
				argv_strs.push_back("-nostdlib");
				argv_strs.push_back("-no-pie");
				argv_strs.push_back("-Wl,-e,_start");
				if (use_dynamic_stella) {
					argv_strs.push_back("-Wl,-dynamic-linker," + selected_dynamic_linker);
				}
			}
		} else {
			argv_strs = {raw_linker};
			if (!target_sysroot.empty()) {
				argv_strs.push_back("--sysroot=" + target_sysroot);
			}
			argv_strs.push_back("-e");
			argv_strs.push_back("_start");
			if (use_dynamic_stella) {
				argv_strs.push_back("-dynamic-linker");
				argv_strs.push_back(selected_dynamic_linker);
			}
		}
		if (!is_wasm_target) {
			argv_strs.push_back("-L" + runtime_dir);
			if (use_dynamic_stella) {
				argv_strs.push_back(use_driver ? "-Wl,-rpath," + runtime_dir : "-rpath");
				if (!use_driver) {
					argv_strs.push_back(runtime_dir);
				}
			}
		}
		if (use_crt) {
			argv_strs.insert(argv_strs.end(), {"-o", output, obj_path});
		} else if (is_wasm_target) {
			argv_strs.insert(argv_strs.end(), {"-o", output, obj_path});
		} else {
			argv_strs.insert(argv_strs.end(), {"-o", output, start_obj, obj_path});
		}
		if (!imported_objects.empty() && linker_supports_archive_groups) {
			// Treat imported objects like archive members. Passing them as ordinary
			// objects would retain every imported definition, even when the root
			// translation unit references only one function from the module.
			argv_strs.push_back(use_driver ? "-Wl,--start-lib" : "--start-lib");
			argv_strs.insert(argv_strs.end(), imported_objects.begin(), imported_objects.end());
			argv_strs.push_back(use_driver ? "-Wl,--end-lib" : "--end-lib");
		} else {
			argv_strs.insert(argv_strs.end(), imported_objects.begin(), imported_objects.end());
		}
		for (const auto &library : libraries) {
			argv_strs.push_back("-l" + library);
		}
		if (!is_wasm_target) {
			if (use_dynamic_stella) {
				argv_strs.push_back(use_driver ? "-Wl,-Bdynamic" : "-Bdynamic");
			} else {
				argv_strs.push_back(use_driver ? "-Wl,-Bstatic" : "-Bstatic");
			}
			if (use_dynamic_stella && linker_supports_archive_groups) {
				// A shared runtime must not become a DT_NEEDED dependency merely
				// because it is available in the runtime search path. Keep the
				// option scoped to Stella so explicitly requested libraries retain
				// their existing link semantics.
				argv_strs.push_back(use_driver ? "-Wl,--as-needed" : "--as-needed");
			}
			if (use_dynamic_stella) {
				if (llvm::sys::fs::exists(runtime_dir + "/stellalib.so")) {
					argv_strs.push_back("-l:stellalib.so");
				} else if (llvm::sys::fs::exists(runtime_dir + "/stellalib.so.0")) {
					argv_strs.push_back("-l:stellalib.so.0");
				} else if (llvm::sys::fs::exists(runtime_dir + "/libstella.so") ||
						   llvm::sys::fs::exists(runtime_dir + "/libstella.so.0")) {
					argv_strs.push_back("-lstella");
				} else {
					argv_strs.push_back("-l:stellalib.so");
				}
			} else {
				if (llvm::sys::fs::exists(runtime_dir + "/stellalib.a")) {
					argv_strs.push_back("-l:stellalib.a");
				} else if (llvm::sys::fs::exists(runtime_dir + "/libstella.a")) {
					argv_strs.push_back("-lstella");
				} else {
					argv_strs.push_back("-l:stellalib.a");
				}
			}
			if (use_dynamic_stella && linker_supports_archive_groups) {
				argv_strs.push_back(use_driver ? "-Wl,--no-as-needed" : "--no-as-needed");
			}
			// Keep external-library behavior dynamic by default after a static
			// standard-library selection.
			if (!use_dynamic_stella) {
				argv_strs.push_back(use_driver ? "-Wl,-Bdynamic" : "-Bdynamic");
			}
		}
		// Pass link-time optimization options directly to a raw linker, or
		// through the compiler driver when the driver is being used. Passing
		// `--opt.lto=full` would force lld into unified-LTO mode, which requires
		// every input to be bitcode; the Stella runtime is a native archive,
		// so only ThinLTO is selected explicitly here.
		if (lto == LtoMode::Thin) {
			argv_strs.push_back(use_driver ? "-Wl,--lto=thin" : "--lto=thin");
		}
		if (opt_level != OptLevel::None) {
			std::string lto_opt = "--lto-O" + std::to_string(opt_level_lto_value(opt_level));
			argv_strs.push_back(use_driver ? "-Wl," + lto_opt : lto_opt);
		}
		if (triple.isOSBinFormatELF()) {
			auto add_z_option = [&](const char *option) {
				if (use_driver) {
					argv_strs.push_back(std::string("-Wl,-z,") + option);
				} else {
					argv_strs.push_back("-z");
					argv_strs.push_back(option);
				}
			};
			switch (relro_mode) {
			case RelroMode::None:
				add_z_option("norelro");
				break;
			case RelroMode::Partial:
				add_z_option("relro");
				break;
			case RelroMode::Full:
				add_z_option("relro");
				add_z_option("now");
				break;
			}
		}
		std::string linker_detail;
		if (!run_command(std::move(argv_strs), &linker_detail)) {
			std::vector<log::Attachment> attachments;
			if (!linker_detail.empty()) {
				attachments.push_back({"linker", linker_detail});
			}
			log::report(log::Level::Error, {}, "linking failed", "E_LINK_FAILED", "linker", {},
						attachments);
			cleanup_imports();
			return 1;
		}
		cleanup_imports();
	}
	return 0;
}