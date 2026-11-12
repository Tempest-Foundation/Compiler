#include "internal.hpp"

namespace stellac {

namespace {

enum FlowOutcome : unsigned {
	FlowFallthrough = 1u << 0,
	FlowYield = 1u << 1,
	FlowReturn = 1u << 2,
	FlowBreak = 1u << 3,
	FlowContinue = 1u << 4,
};

static unsigned apply_defer(unsigned outcomes, unsigned cleanup) {
	unsigned result = 0;
	if (cleanup & FlowFallthrough) {
		result |= outcomes;
	}
	if (cleanup & FlowReturn) {
		result |= FlowReturn;
	}
	return result;
}

static bool is_noreturn_call(const Expr *expr) {
	if (!expr) return false;
	if (expr->kind == ExprKind::DiagErr) return true;
	return expr->kind == ExprKind::Call && expr->resolved_fn &&
		has_negated_attr(expr->resolved_fn->attrs, "return");
}

static unsigned flow_outcomes(const Stmt &stmt) {
	switch (stmt.kind) {
	case StmtKind::Return:
	case StmtKind::Unreachable:
		return FlowReturn;
	case StmtKind::Yield:
		return FlowYield;
	case StmtKind::Break:
		return FlowBreak;
	case StmtKind::Continue:
		return FlowContinue;
	case StmtKind::ExprStmt:
		return is_noreturn_call(stmt.expr.get()) ? FlowReturn : FlowFallthrough;
	case StmtKind::VarDecl:
	case StmtKind::ConstDecl:
		for (const auto &var : stmt.vars) {
			if (is_noreturn_call(var.init.get())) {
				return FlowReturn;
			}
		}
		return FlowFallthrough;
	case StmtKind::Block: {
		unsigned outcomes = FlowFallthrough;
		unsigned cleanup_outcomes = 0;
		bool has_defer = false;
		for (const auto &child : stmt.body) {
			if (!child || !(outcomes & FlowFallthrough)) {
				continue;
			}
			if (child->kind == StmtKind::Defer) {
				has_defer = true;
				cleanup_outcomes = child->defer_body ? flow_outcomes(*child->defer_body)
															 : FlowFallthrough;
				continue;
			}
			unsigned child_outcomes = flow_outcomes(*child);
			if (has_defer) {
				child_outcomes = apply_defer(child_outcomes, cleanup_outcomes);
			}
			outcomes = (outcomes & ~FlowFallthrough) | child_outcomes;
		}
		if (has_defer && (outcomes & FlowFallthrough)) {
			outcomes = (outcomes & ~FlowFallthrough) |
				apply_defer(FlowFallthrough, cleanup_outcomes);
		}
		return outcomes;
	}
	case StmtKind::If: {
		if (is_noreturn_call(stmt.cond.get())) {
			return FlowReturn;
		}
		if (stmt.cond && stmt.cond->is_const_bool) {
			const StmtPtr &branch = stmt.cond->const_bool_val ? stmt.then_block : stmt.else_block;
			return branch ? flow_outcomes(*branch) : FlowFallthrough;
		}
		return (stmt.then_block ? flow_outcomes(*stmt.then_block) : FlowFallthrough) |
			(stmt.else_block ? flow_outcomes(*stmt.else_block) : FlowFallthrough);
	}
	case StmtKind::Switch: {
		if (is_noreturn_call(stmt.scrutinee.get())) {
			return FlowReturn;
		}
		unsigned outcomes = 0;
		bool has_default = false;
		for (const auto &arm : stmt.arms) {
			has_default = has_default || arm.is_default;
			unsigned arm_outcomes = arm.body ? flow_outcomes(*arm.body) : FlowFallthrough;
			// A break in a switch arm exits the switch and resumes after it.
			if (arm_outcomes & FlowBreak) {
				arm_outcomes = (arm_outcomes & ~FlowBreak) | FlowFallthrough;
			}
			outcomes |= arm_outcomes;
		}
		if (!has_default) {
			outcomes |= FlowFallthrough;
		}
		return outcomes;
	}
	case StmtKind::For: {
		unsigned prefix = 0;
		if (stmt.for_init) {
			prefix = flow_outcomes(*stmt.for_init);
			if (!(prefix & FlowFallthrough)) {
				return prefix;
			}
		}
		const unsigned preceding = prefix & ~FlowFallthrough;
		if (is_noreturn_call(stmt.for_cond.get())) {
			return preceding | FlowReturn;
		}
		if (stmt.for_cond && stmt.for_cond->is_const_bool && !stmt.for_cond->const_bool_val) {
			return preceding | FlowFallthrough;
		}

		const bool always_true = !stmt.for_cond ||
			(stmt.for_cond->is_const_bool && stmt.for_cond->const_bool_val);
		const unsigned body = stmt.loop_body ? flow_outcomes(*stmt.loop_body) : FlowFallthrough;
		unsigned outcomes = body & (FlowYield | FlowReturn);
		if (body & FlowBreak) {
			outcomes |= FlowFallthrough;
		}
		if (stmt.for_step && is_noreturn_call(stmt.for_step.get())) {
			if (body & (FlowFallthrough | FlowContinue)) {
				outcomes |= FlowReturn;
			}
		} else if (!always_true && (body & (FlowFallthrough | FlowContinue))) {
			outcomes |= FlowFallthrough;
		}
		// A non-constant loop condition can be false before the first iteration.
		if (!always_true) {
			outcomes |= FlowFallthrough;
		}
		return preceding | outcomes;
	}
	default:
		return FlowFallthrough;
	}
}

} // namespace

bool Sema::definite_return(Stmt &s) {
	return (flow_outcomes(s) & FlowFallthrough) == 0;
}

bool Sema::definite_yield(Stmt &s) {
	return (flow_outcomes(s) & FlowFallthrough) == 0;
}

} // namespace stellac