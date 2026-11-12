#include "internal.hpp"

namespace stellac {

StmtPtr Parser::parse_block() {
	auto s	= std::make_unique<Stmt>();
	s->kind = StmtKind::Block;
	s->loc	= peek().loc;
	expect(TokenKind::LBrace, "'{'");
	while (!at(TokenKind::RBrace) && !at(TokenKind::Eof)) {
		auto st = parse_stmt();
		if (st) {
			s->body.push_back(std::move(st));
		} else {
			consume();
		}
	}
	expect(TokenKind::RBrace, "'}'");
	return s;
}

StmtPtr Parser::try_parse_stmt_keyword_typo(AttributeList &attrs) {
	if (peek().kind != TokenKind::Ident) {
		return nullptr;
	}
	// Check for C-style variable declaration (e.g. `u8 x = 1;`)
	if (is_prim_type_name(peek(0).text) && peek(1).kind == TokenKind::Ident) {
		SourceLoc loc = peek().loc;
		std::string ty_name = peek(0).text;
		std::string var_name = peek(1).text;
		auto diag = log::error(loc, "unexpected type name '" + ty_name + "' at start of statement")
						.code("E_PARSE_EXPECTED_TOKEN")
						.phase("parser")
						.help("declare variables using `let` or `let mut` (e.g. `let " + var_name + ": " + ty_name + " = ...;`)");
		diag.emit();
		auto s = std::make_unique<Stmt>();
		s->kind = StmtKind::VarDecl;
		s->loc = loc;
		consume(); // type name
		std::string name = consume().text; // var name
		std::unique_ptr<Expr> init;
		if (accept(TokenKind::Assign)) {
			init = parse_expr();
		}
		expect(TokenKind::Semicolon, "';'");
		VarDeclInfo var;
		var.name = name;
		var.loc = loc;
		var.is_const = false;
		var.is_mutable = false;
		var.attrs = std::move(attrs);
		auto ty = std::make_unique<TypeRef>();
		ty->name = ty_name;
		ty->loc = loc;
		var.ty = std::move(ty);
		var.init = std::move(init);
		s->vars.push_back(std::move(var));
		return s;
	}

	const Token &t0 = peek(0);
	const Token &t1 = peek(1);
	std::string_view text = t0.text;

	TokenKind best_kw = TokenKind::Unknown;
	size_t best_dist = 999;
	for (TokenKind kw : statement_keywords) {
		const char *kw_name = token_kind_name(kw);
		size_t dist = levenshtein_distance(text, kw_name);
		size_t threshold = (std::strlen(kw_name) <= 3) ? 1 : 2;
		if (dist <= threshold && dist < best_dist) {
			best_dist = dist;
			best_kw = kw;
		}
	}
	if (best_kw == TokenKind::Unknown) {
		return nullptr;
	}

	bool is_match = false;
	if (best_kw == TokenKind::KwLet || best_kw == TokenKind::KwConst) {
		if (t1.kind == TokenKind::Ident || t1.kind == TokenKind::KwStatic || t1.kind == TokenKind::KwMut ||
			t1.kind == TokenKind::KwThreadLocal) {
			is_match = true;
		}
	} else if (best_kw == TokenKind::KwReturn) {
		if (t1.kind == TokenKind::Ident || t1.kind == TokenKind::IntLit ||
			t1.kind == TokenKind::FloatLit || t1.kind == TokenKind::StringLit ||
			t1.kind == TokenKind::CharLit || t1.kind == TokenKind::KwTrue ||
			t1.kind == TokenKind::KwFalse || t1.kind == TokenKind::KwNull ||
			t1.kind == TokenKind::Bang || t1.kind == TokenKind::Tilde ||
			t1.kind == TokenKind::Semicolon) {
			is_match = true;
		}
	} else if (best_kw == TokenKind::KwFor) {
		if (t1.kind == TokenKind::KwConst ||
			t1.kind == TokenKind::KwLet || t1.kind == TokenKind::Ident) {
			is_match = true;
		}
	} else if (best_kw == TokenKind::KwIf || best_kw == TokenKind::KwSwitch) {
		if (t1.kind == TokenKind::LParen || t1.kind == TokenKind::Ident ||
			t1.kind == TokenKind::IntLit || t1.kind == TokenKind::StringLit) {
			is_match = true;
		}
	} else if (best_kw == TokenKind::KwDefer) {
		if (t1.kind == TokenKind::LBrace) {
			is_match = true;
		}
	} else if (best_kw == TokenKind::KwYield) {
		if (t1.kind == TokenKind::Ident || t1.kind == TokenKind::IntLit ||
			t1.kind == TokenKind::FloatLit || t1.kind == TokenKind::StringLit) {
			is_match = true;
		}
	} else if (best_kw == TokenKind::KwBreak || best_kw == TokenKind::KwContinue ||
			   best_kw == TokenKind::KwUnreachable) {
		if (t1.kind == TokenKind::Semicolon) {
			is_match = true;
		}
	}

	if (!is_match) {
		return nullptr;
	}

	const char *kw_name = token_kind_name(best_kw);
	log::error(t0.loc, "unknown keyword '" + t0.text + "'")
		.code("E_PARSE_EXPECTED_TOKEN")
		.phase("parser")
		.help("did you mean `" + std::string(kw_name) + "`?")
		.fixit(t0.loc, kw_name, "replace with `" + std::string(kw_name) + "`")
		.emit();

	toks_[idx_].kind = best_kw;
	switch (best_kw) {
	case TokenKind::KwLet:
	case TokenKind::KwConst:
		return parse_var_or_const(best_kw == TokenKind::KwConst, std::move(attrs));
	case TokenKind::KwReturn:
		return parse_return();
	case TokenKind::KwIf:
		return parse_if();
	case TokenKind::KwFor:
		return parse_for();
	case TokenKind::KwSwitch:
		return parse_switch();
	case TokenKind::KwDefer: {
		auto s = std::make_unique<Stmt>();
		s->kind = StmtKind::Defer;
		s->loc = peek().loc;
		consume();
		s->defer_body = parse_block();
		return s;
	}
	case TokenKind::KwYield:
		return parse_yield();
	case TokenKind::KwBreak: {
		SourceLoc loc = peek().loc;
		consume();
		expect(TokenKind::Semicolon, "';'");
		auto s = std::make_unique<Stmt>();
		s->kind = StmtKind::Break;
		s->loc = loc;
		return s;
	}
	case TokenKind::KwContinue: {
		SourceLoc loc = peek().loc;
		consume();
		expect(TokenKind::Semicolon, "';'");
		auto s = std::make_unique<Stmt>();
		s->kind = StmtKind::Continue;
		s->loc = loc;
		return s;
	}
	case TokenKind::KwUnreachable: {
		SourceLoc loc = peek().loc;
		consume();
		expect(TokenKind::Semicolon, "';'");
		auto s = std::make_unique<Stmt>();
		s->kind = StmtKind::Unreachable;
		s->loc = loc;
		return s;
	}
	default:
		return nullptr;
	}
}

StmtPtr Parser::parse_stmt() {
	AttributeList attrs;
	parse_attributes(attrs);
	if (auto typo_stmt = try_parse_stmt_keyword_typo(attrs)) {
		return typo_stmt;
	}
	if (!attrs.attrs.empty() && peek().kind != TokenKind::KwConst && peek().kind != TokenKind::KwLet) {
		log::report(log::Level::Error, attrs.attrs.front().loc,
					attr_diag_prefix(attrs.attrs.front()) + " is not valid on this statement");
	}
	switch (peek().kind) {
	case TokenKind::LBrace:
		return parse_block();
	case TokenKind::KwIf:
		return parse_if();
	case TokenKind::KwFor:
		return parse_for();
	case TokenKind::KwSwitch:
		return parse_switch();
	case TokenKind::KwReturn:
		return parse_return();
	case TokenKind::KwUnreachable: {
		auto s = std::make_unique<Stmt>();
		s->kind = StmtKind::Unreachable;
		s->loc = peek().loc;
		consume();
		expect(TokenKind::Semicolon, "';'");
		return s;
	}
	case TokenKind::KwBreak:
		{
			SourceLoc loc = peek().loc;
			consume();
			expect(TokenKind::Semicolon, "';'");
			auto s	= std::make_unique<Stmt>();
			s->kind = StmtKind::Break;
			s->loc = loc;
			return s;
		}
	case TokenKind::KwContinue:
		{
			SourceLoc loc = peek().loc;
			consume();
			expect(TokenKind::Semicolon, "';'");
			auto s	= std::make_unique<Stmt>();
			s->kind = StmtKind::Continue;
			s->loc = loc;
			return s;
		}
	case TokenKind::KwDefer: {
		auto s = std::make_unique<Stmt>();
		s->kind = StmtKind::Defer;
		s->loc = peek().loc;
		consume();
		s->defer_body = parse_block();
		return s;
	}
	case TokenKind::KwYield:
		return parse_yield();
	case TokenKind::KwConst:
	case TokenKind::KwLet:
		return parse_var_or_const(peek().kind == TokenKind::KwConst, std::move(attrs));
	case TokenKind::KwAsm:
		return parse_asm();
	case TokenKind::Semicolon:
		consume();
		return nullptr;
	default:
		return parse_expr_stmt_or_decl();
	}
}

StmtPtr Parser::parse_var_or_const(bool is_const, AttributeList attrs) {
	auto s	= std::make_unique<Stmt>();
	s->kind = is_const ? StmtKind::ConstDecl : StmtKind::VarDecl;
	s->loc	= peek().loc;
	consume(); // let or const
	bool is_mutable = false;
	bool is_static = false;
	bool is_thread_local = false;
	while (at(TokenKind::KwMut) || at(TokenKind::KwStatic) || at(TokenKind::KwThreadLocal)) {
		if (accept(TokenKind::KwMut)) {
			if (is_const) {
				log::report(log::Level::Error, peek().loc,
							"'mut' cannot be used with 'const'");
			}
			is_mutable = true;
		} else if (accept(TokenKind::KwStatic)) {
			is_static = true;
		} else if (accept(TokenKind::KwThreadLocal)) {
			is_thread_local = true;
		}
	}
	if (!at(TokenKind::Ident)) {
		log::report(log::Level::Error, peek().loc, "expected binding name");
		return s;
	}
	std::vector<std::pair<std::string, SourceLoc>> names;
	while (true) {
		SourceLoc	vloc = peek().loc;
		std::string name = consume().text;
		reject_reserved_name(vloc, name, "binding name");
		names.emplace_back(std::move(name), vloc);
		if (!accept(TokenKind::Comma)) {
			break;
		}
		if (!at(TokenKind::Ident)) {
			log::report(log::Level::Error, peek().loc, "expected binding name after ','");
			break;
		}
	}
	expect(TokenKind::Colon, "':'");
	auto				  ty = parse_type();
	std::unique_ptr<Expr> init;
	if (accept(TokenKind::Assign)) {
		init = parse_expr();
	}
	expect(TokenKind::Semicolon, "';'");
	for (auto &[name, loc] : names) {
		VarDeclInfo var;
		var.name	 = name;
		var.loc		 = loc;
		var.is_const = is_const;
		var.is_mutable = is_mutable;
		var.is_static = is_static;
		var.is_thread_local = is_thread_local;
		var.attrs	 = attrs;
		if (ty) {
			var.ty = clone_typeref(*ty);
		}
		if (init) {
			var.init = clone_expr(*init);
		}
		s->vars.push_back(std::move(var));
	}
	return s;
}

StmtPtr Parser::parse_if() {
	auto s	= std::make_unique<Stmt>();
	s->kind = StmtKind::If;
	s->loc	= peek().loc;
	consume(); // if
	s->cond		  = parse_expr();
	s->then_block = parse_block();
	if (accept(TokenKind::KwElse)) {
		if (at(TokenKind::KwIf)) {
			s->else_block = parse_if();
		} else {
			s->else_block = parse_block();
		}
	}
	return s;
}

StmtPtr Parser::parse_for() {
	auto s	= std::make_unique<Stmt>();
	s->kind = StmtKind::For;
	s->loc	= peek().loc;
	consume();
	// init: binding decl (no parens -- `for let mut i: T = e; cond; step { }`)
	AttributeList init_attrs;
	parse_attributes(init_attrs);
	if (at(TokenKind::KwLet) || at(TokenKind::KwConst)) {
		s->for_init = parse_var_or_const(at(TokenKind::KwConst), std::move(init_attrs));
	} else {
		if (!init_attrs.attrs.empty()) {
			log::report(log::Level::Error, init_attrs.attrs.front().loc,
						"attributes are only valid on a for-loop binding");
		}
		s->for_cond = parse_expr();
		if (!at(TokenKind::LBrace)) {
			expect(TokenKind::Semicolon, "';'");
			if (!at(TokenKind::LBrace)) {
				s->for_step = parse_expr();
			}
		}
		s->loop_body = parse_block();
		return s;
	}
	if (!at(TokenKind::Semicolon)) {
		s->for_cond = parse_expr();
		expect(TokenKind::Semicolon, "';'");
	} else {
		consume();
	}
	if (!at(TokenKind::LBrace)) {
		s->for_step = parse_expr();
	}
	s->loop_body = parse_block();
	return s;
}

StmtPtr Parser::parse_switch() {
	auto s	= std::make_unique<Stmt>();
	s->kind = StmtKind::Switch;
	s->loc	= peek().loc;
	consume();					 // 'switch'
	s->scrutinee = parse_expr(); // discriminant (no parens)
	expect(TokenKind::LBrace, "'{' after switch expression");
	bool seen_default = false;
	while (!at(TokenKind::RBrace) && !at(TokenKind::Eof)) {
		SwitchArm arm;
		arm.loc = peek().loc;
		if (accept(TokenKind::KwDefault)) {
			if (seen_default) {
				log::report(log::Level::Error, arm.loc, "multiple 'default' arms");
			}
			seen_default   = true;
			arm.is_default = true;
		} else {
			expect(TokenKind::KwCase, "'case' or 'default'");
			arm.case_expr = parse_expr();
		}
		arm.body = parse_block();
		s->arms.push_back(std::move(arm));
	}
	expect(TokenKind::RBrace, "'}'");
	return s;
}

StmtPtr Parser::parse_return() {
	auto s	= std::make_unique<Stmt>();
	s->kind = StmtKind::Return;
	s->loc	= peek().loc;
	consume();
	if (!at(TokenKind::Semicolon)) {
		s->ret_val = parse_expr();
	}
	expect(TokenKind::Semicolon, "';'");
	return s;
}

StmtPtr Parser::parse_yield() {
	auto s = std::make_unique<Stmt>();
	s->kind = StmtKind::Yield;
	s->loc = peek().loc;
	consume();
	if (!at(TokenKind::Semicolon)) {
		s->ret_val = parse_expr();
	}
	expect(TokenKind::Semicolon, "';'");
	return s;
}

StmtPtr Parser::parse_asm() {
	auto s	= std::make_unique<Stmt>();
	s->kind = StmtKind::Asm;
	s->loc	= peek().loc;
	consume(); // asm
	if (at(TokenKind::KwVolatile)) {
		s->asm_volatile = true;
		consume();
	}
	expect(TokenKind::LBrace, "'{'");
	// code string (one or more concatenated string literals allowed)
	if (!at(TokenKind::StringLit)) {
		log::report(log::Level::Error, peek().loc, "expected asm code string");
		return s;
	}
	s->asm_code = consume().text;
	while (at(TokenKind::StringLit)) {
		s->asm_code += consume().text;
	}

	// Helper: parse an operand list. Caller has already consumed the leading ':'.
	auto parse_operand_list = [&](std::vector<AsmOperand> &dest, bool allow_clobber) {
		while (true) {
			if (!at(TokenKind::StringLit)) {
				log::report(log::Level::Error, peek().loc,
							"expected constraint string in asm operand list");
				return;
			}
			std::string c = consume().text;
			if (at(TokenKind::LParen)) {
				consume();
				AsmOperand aop;
				aop.constraint = c;
				aop.operand	   = parse_expr();
				expect(TokenKind::RParen, "')'");
				dest.push_back(std::move(aop));
			} else if (allow_clobber) {
				AsmOperand aop;
				aop.constraint = c;
				aop.is_clobber = true;
				dest.push_back(std::move(aop));
			} else {
				log::report(log::Level::Error, peek().loc,
							"bare clobber string not allowed in output/input list");
			}
			if (!at(TokenKind::Comma)) {
				break;
			}
			consume();
		}
	};

	// outputs: ':' <operands>
	if (accept(TokenKind::Colon)) {
		if (at(TokenKind::StringLit)) {
			parse_operand_list(s->asm_outputs, false);
		}
		// inputs: ':' <operands>
		if (accept(TokenKind::Colon)) {
			if (at(TokenKind::StringLit)) {
				parse_operand_list(s->asm_inputs, false);
			}
			// clobbers: ':' <clobber strings>
			if (accept(TokenKind::Colon)) {
				while (at(TokenKind::StringLit)) {
					s->asm_clobbers.push_back(consume().text);
					if (!at(TokenKind::Comma)) {
						break;
					}
					consume();
				}
			}
		}
	}
	expect(TokenKind::RBrace, "'}'");
	expect(TokenKind::Semicolon, "';'");
	return s;
}

StmtPtr Parser::parse_expr_stmt_or_decl() {
	auto s	= std::make_unique<Stmt>();
	s->kind = StmtKind::ExprStmt;
	s->loc	= peek().loc;
	s->expr = parse_expr();
	expect(TokenKind::Semicolon, "';'");
	return s;
}

// expressions

// Deep-clone an expression. Used only during compound-assignment desugaring
// (`x += y` -> `x = x + y`), which happens before sema fills in resolved
// type pointers -- so we only need to copy the syntactic payload.

} // namespace stellac