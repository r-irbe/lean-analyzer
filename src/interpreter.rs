//! crates/lean-analyzer/src/interpreter.rs
//! In-process abstract evaluation engine over LeanExpr.
//! Strict 7-bit ASCII only (INV-001).

use crate::ast::LeanExpr;
use crate::lattice::{AbstractBool, AbstractSign, AbstractState};
use std::collections::HashMap;

/// Actionable static diagnostic kind emitted by `LeanAbstractInterpreter::diagnose_expr`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DiagnosticKind {
    /// `Nat.sub` (`a - b`) where `a <= b` always or potentially holds, truncating to `0`.
    NatSubTruncation,
    /// `Nat.div` or `Nat.mod` where divisor interval includes `0` (`a / 0 = 0`, `a % 0 = a`).
    NatDivModByZero,
    /// `ite` / `cond` / `bif` guard whose condition is statically constant (`True` or `False`).
    DeadBranch,
}

/// Structured, human-readable static diagnostic certificate with concrete fix hints.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DiagnosticCertificate {
    pub kind: DiagnosticKind,
    pub operator: String,
    pub summary: String,
    pub hint: String,
}

pub struct LeanAbstractInterpreter {
    environment: HashMap<String, AbstractState>,
}

impl Default for LeanAbstractInterpreter {
    fn default() -> Self {
        Self::new()
    }
}

impl LeanAbstractInterpreter {
    pub fn new() -> Self {
        Self {
            environment: HashMap::new(),
        }
    }

    pub fn set_decl_state(&mut self, name: &str, state: AbstractState) {
        self.environment.insert(name.to_string(), state);
    }

    pub fn get_decl_state(&self, name: &str) -> Option<&AbstractState> {
        self.environment.get(name)
    }

    /// Refines the environment under the assumption that `cond_expr` evaluates to `truth`.
    /// Returns `None` if the branch is provably unreachable (empty interval).
    fn refine_env_for_guard(&self, cond_expr: &LeanExpr, truth: bool) -> Option<Self> {
        if let LeanExpr::App(f, rhs) = cond_expr {
            if let LeanExpr::Const(op_name) = f.as_ref() {
                if op_name == "Bool.not" || op_name == "not" {
                    return self.refine_env_for_guard(rhs, !truth);
                }
            }
            if let LeanExpr::App(f_inner, lhs) = f.as_ref() {
                if let LeanExpr::Const(op_name) = f_inner.as_ref() {
                    if let Some(op) = crate::ops::BinOp::from_name(op_name) {
                        if let Some((var, bound_expr, flipped)) = match (lhs.as_ref(), rhs.as_ref()) {
                            (LeanExpr::Const(v), _) if self.environment.contains_key(v) => {
                                Some((v.as_str(), rhs.as_ref(), false))
                            }
                            (_, LeanExpr::Const(v)) if self.environment.contains_key(v) => {
                                Some((v.as_str(), lhs.as_ref(), true))
                            }
                            _ => None,
                        } {
                            let b_state = self.eval_expr(bound_expr).refine_nat();
                            let orig = self.environment.get(var).copied()?.refine_nat();
                            if let (Some(orig_iv), Some(b_iv)) = (orig.interval, b_state.interval) {
                                use crate::lattice::IntervalBound;
                                use crate::nat_interval::INF;
                                // Orient the relation so `var rel b_iv` holds when `truth == true`.
                                let eff_op = match (op, flipped, truth) {
                                    (crate::ops::BinOp::Le, false, true)
                                    | (crate::ops::BinOp::Ge, true, true)
                                    | (crate::ops::BinOp::Gt, false, false)
                                    | (crate::ops::BinOp::Lt, true, false) => Some(crate::ops::BinOp::Le),
                                    (crate::ops::BinOp::Lt, false, true)
                                    | (crate::ops::BinOp::Gt, true, true)
                                    | (crate::ops::BinOp::Ge, false, false)
                                    | (crate::ops::BinOp::Le, true, false) => Some(crate::ops::BinOp::Lt),
                                    (crate::ops::BinOp::Ge, false, true)
                                    | (crate::ops::BinOp::Le, true, true)
                                    | (crate::ops::BinOp::Lt, false, false)
                                    | (crate::ops::BinOp::Gt, true, false) => Some(crate::ops::BinOp::Ge),
                                    (crate::ops::BinOp::Gt, false, true)
                                    | (crate::ops::BinOp::Lt, true, true)
                                    | (crate::ops::BinOp::Le, false, false)
                                    | (crate::ops::BinOp::Ge, true, false) => Some(crate::ops::BinOp::Gt),
                                    (crate::ops::BinOp::Eq, _, true)
                                    | (crate::ops::BinOp::Ne, _, false) => Some(crate::ops::BinOp::Eq),
                                    (crate::ops::BinOp::Ne, _, true)
                                    | (crate::ops::BinOp::Eq, _, false) => Some(crate::ops::BinOp::Ne),
                                    _ => None,
                                };
                                let refined_iv = match eff_op {
                                    Some(crate::ops::BinOp::Le) => {
                                        Some(IntervalBound::new(orig_iv.min, orig_iv.max.min(b_iv.max)))
                                    }
                                    Some(crate::ops::BinOp::Lt) => {
                                        if b_iv.max == 0 {
                                            return None;
                                        }
                                        let cap = if b_iv.max == INF { INF } else { b_iv.max - 1 };
                                        Some(IntervalBound::new(orig_iv.min, orig_iv.max.min(cap)))
                                    }
                                    Some(crate::ops::BinOp::Ge) => {
                                        Some(IntervalBound::new(orig_iv.min.max(b_iv.min), orig_iv.max))
                                    }
                                    Some(crate::ops::BinOp::Gt) => {
                                        let floor = b_iv.min.saturating_add(1);
                                        Some(IntervalBound::new(orig_iv.min.max(floor), orig_iv.max))
                                    }
                                    Some(crate::ops::BinOp::Eq) => Some(IntervalBound::new(
                                        orig_iv.min.max(b_iv.min),
                                        orig_iv.max.min(b_iv.max),
                                    )),
                                    Some(crate::ops::BinOp::Ne) => {
                                        if b_iv.min == b_iv.max && b_iv.max != INF {
                                            let c = b_iv.min;
                                            let lo = if orig_iv.min == c {
                                                orig_iv.min.saturating_add(1)
                                            } else {
                                                orig_iv.min
                                            };
                                            let hi = if orig_iv.max == c {
                                                orig_iv.max - 1
                                            } else {
                                                orig_iv.max
                                            };
                                            Some(IntervalBound::new(lo, hi))
                                        } else {
                                            Some(orig_iv)
                                        }
                                    }
                                    _ => None,
                                };
                                if let Some(iv) = refined_iv {
                                    if iv.min > iv.max {
                                        return None;
                                    }
                                    let mut env = self.environment.clone();
                                    let mut new_state = orig;
                                    new_state.interval = Some(iv);
                                    env.insert(var.to_string(), new_state.refine_nat());
                                    return Some(Self { environment: env });
                                }
                            }
                        }
                        // Backward arithmetic guard propagation (`COUSOT s64.1 p1`):
                        // Handles `(v + c) rel b`, `(c + v) rel b`, and `(v - c) rel b` (or flipped).
                        if let Some((sub_expr, bound_expr, flipped)) =
                            match (lhs.as_ref(), rhs.as_ref()) {
                                (LeanExpr::App(_, _), _) => Some((lhs.as_ref(), rhs.as_ref(), false)),
                                (_, LeanExpr::App(_, _)) => Some((rhs.as_ref(), lhs.as_ref(), true)),
                                _ => None,
                            }
                        {
                            if let LeanExpr::App(sub_f, sub_r) = sub_expr {
                                if let LeanExpr::App(sub_op_expr, sub_l) = sub_f.as_ref() {
                                    if let LeanExpr::Const(sub_op_name) = sub_op_expr.as_ref() {
                                        if let Some(sub_op) = crate::ops::BinOp::from_name(sub_op_name)
                                        {
                                            let var_and_const = match (sub_op, sub_l.as_ref(), sub_r.as_ref()) {
                                                (
                                                    crate::ops::BinOp::Add,
                                                    LeanExpr::Const(v),
                                                    other,
                                                ) if self.environment.contains_key(v) => {
                                                    Some((v.as_str(), other, true))
                                                }
                                                (
                                                    crate::ops::BinOp::Add,
                                                    other,
                                                    LeanExpr::Const(v),
                                                ) if self.environment.contains_key(v) => {
                                                    Some((v.as_str(), other, true))
                                                }
                                                (
                                                    crate::ops::BinOp::Sub,
                                                    LeanExpr::Const(v),
                                                    other,
                                                ) if self.environment.contains_key(v) => {
                                                    Some((v.as_str(), other, false))
                                                }
                                                _ => None,
                                            };
                                            if let Some((var, c_expr, is_add)) = var_and_const {
                                                let c_state = self.eval_expr(c_expr).refine_nat();
                                                let b_state = self.eval_expr(bound_expr).refine_nat();
                                                let orig =
                                                    self.environment.get(var).copied()?.refine_nat();
                                                if let (Some(orig_iv), Some(c_iv), Some(b_iv)) = (
                                                    orig.interval,
                                                    c_state.interval,
                                                    b_state.interval,
                                                ) {
                                                    use crate::lattice::IntervalBound;
                                                    use crate::nat_interval::INF;
                                                    let eff_op = match (op, flipped, truth) {
                                                        (crate::ops::BinOp::Le, false, true)
                                                        | (crate::ops::BinOp::Ge, true, true)
                                                        | (crate::ops::BinOp::Gt, false, false)
                                                        | (crate::ops::BinOp::Lt, true, false) => {
                                                            Some(crate::ops::BinOp::Le)
                                                        }
                                                        (crate::ops::BinOp::Lt, false, true)
                                                        | (crate::ops::BinOp::Gt, true, true)
                                                        | (crate::ops::BinOp::Ge, false, false)
                                                        | (crate::ops::BinOp::Le, true, false) => {
                                                            Some(crate::ops::BinOp::Lt)
                                                        }
                                                        (crate::ops::BinOp::Ge, false, true)
                                                        | (crate::ops::BinOp::Le, true, true)
                                                        | (crate::ops::BinOp::Lt, false, false)
                                                        | (crate::ops::BinOp::Gt, true, false) => {
                                                            Some(crate::ops::BinOp::Ge)
                                                        }
                                                        (crate::ops::BinOp::Gt, false, true)
                                                        | (crate::ops::BinOp::Lt, true, true)
                                                        | (crate::ops::BinOp::Le, false, false)
                                                        | (crate::ops::BinOp::Ge, true, false) => {
                                                            Some(crate::ops::BinOp::Gt)
                                                        }
                                                        (crate::ops::BinOp::Eq, _, true)
                                                        | (crate::ops::BinOp::Ne, _, false) => {
                                                            Some(crate::ops::BinOp::Eq)
                                                        }
                                                        _ => None,
                                                    };
                                                    // Compute target range [t_lo, t_hi] for the sub_expr (v + c or v - c)
                                                    let target_iv = match eff_op {
                                                        Some(crate::ops::BinOp::Le) => {
                                                            Some(IntervalBound::new(0, b_iv.max))
                                                        }
                                                        Some(crate::ops::BinOp::Lt) => {
                                                            if b_iv.max == 0 {
                                                                return None;
                                                            }
                                                            let cap = if b_iv.max == INF {
                                                                INF
                                                            } else {
                                                                b_iv.max - 1
                                                            };
                                                            Some(IntervalBound::new(0, cap))
                                                        }
                                                        Some(crate::ops::BinOp::Ge) => {
                                                            Some(IntervalBound::new(b_iv.min, INF))
                                                        }
                                                        Some(crate::ops::BinOp::Gt) => {
                                                            Some(IntervalBound::new(
                                                                b_iv.min.saturating_add(1),
                                                                INF,
                                                            ))
                                                        }
                                                        Some(crate::ops::BinOp::Eq) => Some(b_iv),
                                                        _ => None,
                                                    };
                                                    if let Some(t_iv) = target_iv {
                                                        let back_iv = if is_add {
                                                            // v + c in [t_lo, t_hi]  =>  v >= max(0, t_lo - c_hi) and v <= t_hi - c_lo
                                                            if t_iv.max != INF && c_iv.min > t_iv.max {
                                                                return None;
                                                            }
                                                            let lo = if c_iv.max == INF {
                                                                0
                                                            } else {
                                                                (t_iv.min - c_iv.max).max(0)
                                                            };
                                                            let hi = if t_iv.max == INF {
                                                                INF
                                                            } else {
                                                                t_iv.max - c_iv.min
                                                            };
                                                            IntervalBound::new(lo, hi)
                                                        } else {
                                                            // v - c in [t_lo, t_hi] (Nat saturating sub):
                                                            // Lower bound: if t_lo >= 1, v - c >= t_lo requires v >= t_lo + c_lo.
                                                            // Upper bound: v - c <= t_hi allows v <= t_hi + c_hi.
                                                            let lo = if t_iv.min > 0 {
                                                                if t_iv.min == INF || c_iv.min == INF {
                                                                    INF
                                                                } else {
                                                                    t_iv.min.saturating_add(c_iv.min)
                                                                }
                                                            } else {
                                                                0
                                                            };
                                                            let hi = if t_iv.max == INF || c_iv.max == INF {
                                                                INF
                                                            } else {
                                                                t_iv.max.saturating_add(c_iv.max).min(INF)
                                                            };
                                                            IntervalBound::new(lo, hi)
                                                        };
                                                        let iv = IntervalBound::new(
                                                            orig_iv.min.max(back_iv.min),
                                                            orig_iv.max.min(back_iv.max),
                                                        );
                                                        if iv.min > iv.max {
                                                            return None;
                                                        }
                                                        let mut env = self.environment.clone();
                                                        let mut new_state = orig;
                                                        new_state.interval = Some(iv);
                                                        env.insert(
                                                            var.to_string(),
                                                            new_state.refine_nat(),
                                                        );
                                                        return Some(Self { environment: env });
                                                    }
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
        Some(Self {
            environment: self.environment.clone(),
        })
    }

    /// Evaluates a Lean expression into its abstract state.
    pub fn eval_expr(&self, expr: &LeanExpr) -> AbstractState {
        match expr {
            LeanExpr::LitNat(val) => AbstractState::const_nat(*val),
            LeanExpr::Const(name) => {
                if name == "true" || name == "Bool.true" {
                    AbstractState::const_bool(true)
                } else if name == "false" || name == "Bool.false" {
                    AbstractState::const_bool(false)
                } else if name == "Nat.zero" {
                    AbstractState::const_nat(0)
                } else if let Some(state) = self.environment.get(name) {
                    state.refine_nat()
                } else {
                    AbstractState::top()
                }
            }
            LeanExpr::App(f, a) => {
                // Check for 3-argument operators like ite cond then_expr else_expr
                if let LeanExpr::App(f2, then_expr) = f.as_ref() {
                    if let LeanExpr::App(f1, cond_expr) = f2.as_ref() {
                        if let LeanExpr::Const(op_name) = f1.as_ref() {
                            if op_name == "ite" || op_name == "cond" || op_name == "bif" {
                                let c_state = self.eval_expr(cond_expr);
                                let else_expr = a;
                                match c_state.boolean {
                                    Some(AbstractBool::True) => {
                                        let env = self.refine_env_for_guard(cond_expr, true);
                                        return env
                                            .as_ref()
                                            .unwrap_or(self)
                                            .eval_expr(then_expr);
                                    }
                                    Some(AbstractBool::False) => {
                                        let env = self.refine_env_for_guard(cond_expr, false);
                                        return env
                                            .as_ref()
                                            .unwrap_or(self)
                                            .eval_expr(else_expr);
                                    }
                                    Some(AbstractBool::Bottom) => return AbstractState::top(),
                                    _ => {
                                        let t_env = self.refine_env_for_guard(cond_expr, true);
                                        let e_env = self.refine_env_for_guard(cond_expr, false);
                                        return match (t_env, e_env) {
                                            (Some(te), Some(ee)) => {
                                                te.eval_expr(then_expr).join(&ee.eval_expr(else_expr))
                                            }
                                            (Some(te), None) => te.eval_expr(then_expr),
                                            (None, Some(ee)) => ee.eval_expr(else_expr),
                                            (None, None) => {
                                                self.eval_expr(then_expr).join(&self.eval_expr(else_expr))
                                            }
                                        };
                                    }
                                }
                            }
                        }
                    }
                }

                // Check for 1-argument unary operators (table in ops.rs)
                if let LeanExpr::Const(op_name) = f.as_ref() {
                    if let Some(uop) = crate::ops::UnaryOp::from_name(op_name) {
                        let s = self.eval_expr(a);
                        return uop.apply(&s);
                    }
                }

                // 2-argument binary operators (table in ops.rs)
                if let LeanExpr::App(f_inner, arg1) = f.as_ref() {
                    if let LeanExpr::Const(op_name) = f_inner.as_ref() {
                        if let Some(op) = crate::ops::BinOp::from_name(op_name) {
                            let s1 = self.eval_expr(arg1);
                            let s2 = self.eval_expr(a);
                            return op.apply(&s1, &s2);
                        }
                    }
                }
                // Try beta-reduction if the head was an abstraction
                if let Some(reduced) = expr.beta_reduce_once() {
                    return self.eval_expr(&reduced);
                }
                AbstractState::top()
            }
            LeanExpr::Let(var, _ty, val, body) => {
                let val_state = self.eval_expr(val);
                let mut local_interp = LeanAbstractInterpreter {
                    environment: self.environment.clone(),
                };
                local_interp.set_decl_state(var, val_state);
                local_interp.eval_expr(body)
            }
            LeanExpr::LitStr(_) => AbstractState {
                sign: AbstractSign::Top,
                interval: None,
                boolean: None,
                is_deterministic: true,
                is_pure: true,
            },
            _ => AbstractState::top(),
        }
    }

    /// Computes a fixpoint over monotonic state transitions.
    pub fn compute_fixpoint<F>(
        &self,
        init: AbstractState,
        mut transfer: F,
        max_iter: usize,
    ) -> AbstractState
    where
        F: FnMut(&AbstractState) -> AbstractState,
    {
        let mut curr = init;
        for _ in 0..max_iter {
            let next = transfer(&curr);
            if curr == next {
                return curr;
            }
            curr = curr.join(&next);
        }
        curr
    }

    /// Computes a fixpoint with Cousot-Cousot widening and narrowing steps.
    pub fn compute_widening_fixpoint<F>(
        &self,
        init: AbstractState,
        mut transfer: F,
        widen_after_iter: usize,
        max_iter: usize,
    ) -> AbstractState
    where
        F: FnMut(&AbstractState) -> AbstractState,
    {
        let mut curr = init;
        for i in 0..max_iter {
            let next = transfer(&curr);
            if next.is_le(&curr) {
                break;
            }
            if i >= widen_after_iter {
                curr = curr.widen(&next);
            } else {
                curr = curr.join(&next);
            }
        }
        let post = transfer(&curr).refine_nat();
        curr = curr.narrow(&post).refine_nat();
        curr
    }

    /// Computes a fixpoint using threshold widening (`MOLLER-SPA s5.12 p1`, `RIVAL-YI s6.1 p1`)
    /// followed by one narrowing pass to recover exact upper bounds from loop conditions.
    pub fn compute_threshold_widening_fixpoint<F>(
        &self,
        init: AbstractState,
        mut transfer: F,
        thresholds: &[i64],
        widen_after_iter: usize,
        max_iter: usize,
    ) -> AbstractState
    where
        F: FnMut(&AbstractState) -> AbstractState,
    {
        let mut curr = init;
        for i in 0..max_iter {
            let next = transfer(&curr);
            if curr == next {
                return curr;
            }
            if i >= widen_after_iter {
                let joined = curr.join(&next);
                let widened = curr.widen_with_thresholds(&joined, thresholds);
                if widened == curr {
                    break;
                }
                curr = widened;
            } else {
                curr = curr.join(&next);
            }
        }
        let post = transfer(&curr);
        curr.narrow(&post)
    }

    /// Computes a mutual/nested recursive fixpoint over an adjacency graph `adj`
    /// using Bourdoncle's hierarchical Weak Topological Ordering (`WtoOrdering`, Wave 7).
    pub fn compute_wto_fixpoint<F>(
        &self,
        adj: &[Vec<usize>],
        entry: usize,
        init_states: &[AbstractState],
        transfer_vertex: F,
        thresholds: &[i64],
        widen_delay: usize,
        max_component_iters: usize,
    ) -> Vec<AbstractState>
    where
        F: FnMut(usize, &[AbstractState]) -> AbstractState,
    {
        let wto = crate::wto::WtoOrdering::from_adjacency(adj, entry);
        wto.solve_fixpoint(
            init_states,
            transfer_vertex,
            thresholds,
            widen_delay,
            max_component_iters,
        )
    }

    /// Evaluates a Lean expression using Bounded Trace Partitioning (`Rival & Mauborgne 2007`, Wave 7),
    /// maintaining separate `AbstractState` buckets for each control-flow branch sequence up to
    /// `max_depth` nested `ite` / `cond` / `bif` splits before folding via lattice `join`.
    pub fn eval_expr_trace_partitioned(
        &self,
        expr: &LeanExpr,
        max_depth: usize,
    ) -> crate::wto::TracePartitionedState {
        let mut out = crate::wto::TracePartitionedState::new(max_depth);
        self.eval_trace_rec(
            expr,
            crate::wto::TraceToken::root(),
            max_depth,
            &mut out,
        );
        out
    }

    fn eval_trace_rec(
        &self,
        expr: &LeanExpr,
        token: crate::wto::TraceToken,
        max_depth: usize,
        out: &mut crate::wto::TracePartitionedState,
    ) {
        if let LeanExpr::App(f, else_expr) = expr {
            if let LeanExpr::App(f2, then_expr) = f.as_ref() {
                if let LeanExpr::App(f1, cond_expr) = f2.as_ref() {
                    if let LeanExpr::Const(op_name) = f1.as_ref() {
                        if op_name == "ite" || op_name == "cond" || op_name == "bif" {
                            let c_state = self.eval_expr(cond_expr);
                            match c_state.boolean {
                                Some(AbstractBool::True) => {
                                    let tok_t = token.push_branch(1, max_depth);
                                    if let Some(te) = self.refine_env_for_guard(cond_expr, true) {
                                        te.eval_trace_rec(then_expr, tok_t, max_depth, out);
                                    } else {
                                        self.eval_trace_rec(then_expr, tok_t, max_depth, out);
                                    }
                                    return;
                                }
                                Some(AbstractBool::False) => {
                                    let tok_f = token.push_branch(0, max_depth);
                                    if let Some(ee) = self.refine_env_for_guard(cond_expr, false) {
                                        ee.eval_trace_rec(else_expr, tok_f, max_depth, out);
                                    } else {
                                        self.eval_trace_rec(else_expr, tok_f, max_depth, out);
                                    }
                                    return;
                                }
                                Some(AbstractBool::Bottom) => return,
                                _ => {
                                    let tok_t = token.push_branch(1, max_depth);
                                    let tok_f = token.push_branch(0, max_depth);
                                    if let Some(te) = self.refine_env_for_guard(cond_expr, true) {
                                        te.eval_trace_rec(then_expr, tok_t, max_depth, out);
                                    }
                                    if let Some(ee) = self.refine_env_for_guard(cond_expr, false) {
                                        ee.eval_trace_rec(else_expr, tok_f, max_depth, out);
                                    }
                                    return;
                                }
                            }
                        }
                    }
                }
            }
        }
        if let LeanExpr::Let(var, _ty, val, body) = expr {
            let val_tp = self.eval_expr_trace_partitioned(val, max_depth);
            for (sub_tok, val_state) in val_tp.partitions {
                let mut local_interp = LeanAbstractInterpreter {
                    environment: self.environment.clone(),
                };
                local_interp.set_decl_state(var, val_state);
                let mut merged_tok = token.clone();
                for &b in &sub_tok.history {
                    merged_tok = merged_tok.push_branch(b, max_depth);
                }
                local_interp.eval_trace_rec(body, merged_tok, max_depth, out);
            }
            return;
        }
        out.record(token, self.eval_expr(expr));
    }

    /// Evaluates `expr` and collects actionable static `DiagnosticCertificate` warnings
    /// (`NatSubTruncation`, `NatDivModByZero`, `DeadBranch`) across all reachable sub-expressions.
    pub fn diagnose_expr(&self, expr: &LeanExpr) -> (AbstractState, Vec<DiagnosticCertificate>) {
        let mut certs = Vec::new();
        self.collect_diagnostics(expr, &mut certs);
        (self.eval_expr(expr), certs)
    }

    fn collect_diagnostics(&self, expr: &LeanExpr, certs: &mut Vec<DiagnosticCertificate>) {
        match expr {
            LeanExpr::App(f, a) => {
                // 3-argument conditional: ite / cond / bif
                if let LeanExpr::App(f2, then_expr) = f.as_ref() {
                    if let LeanExpr::App(f1, cond_expr) = f2.as_ref() {
                        if let LeanExpr::Const(op_name) = f1.as_ref() {
                            if op_name == "ite" || op_name == "cond" || op_name == "bif" {
                                self.collect_diagnostics(cond_expr, certs);
                                let c_state = self.eval_expr(cond_expr);
                                let else_expr = a;
                                match c_state.boolean {
                                    Some(AbstractBool::True) => {
                                        certs.push(DiagnosticCertificate {
                                            kind: DiagnosticKind::DeadBranch,
                                            operator: op_name.clone(),
                                            summary: format!(
                                                "Condition in `{op_name}` is statically True; else-branch is unreachable."
                                            ),
                                            hint: "Simplify conditional to its then-branch or strengthen guard.".to_string(),
                                        });
                                        if let Some(te) = self.refine_env_for_guard(cond_expr, true) {
                                            te.collect_diagnostics(then_expr, certs);
                                        } else {
                                            self.collect_diagnostics(then_expr, certs);
                                        }
                                        return;
                                    }
                                    Some(AbstractBool::False) => {
                                        certs.push(DiagnosticCertificate {
                                            kind: DiagnosticKind::DeadBranch,
                                            operator: op_name.clone(),
                                            summary: format!(
                                                "Condition in `{op_name}` is statically False; then-branch is unreachable."
                                            ),
                                            hint: "Simplify conditional to its else-branch or check guard direction.".to_string(),
                                        });
                                        if let Some(ee) = self.refine_env_for_guard(cond_expr, false) {
                                            ee.collect_diagnostics(else_expr, certs);
                                        } else {
                                            self.collect_diagnostics(else_expr, certs);
                                        }
                                        return;
                                    }
                                    _ => {
                                        if let Some(te) = self.refine_env_for_guard(cond_expr, true) {
                                            te.collect_diagnostics(then_expr, certs);
                                        }
                                        if let Some(ee) = self.refine_env_for_guard(cond_expr, false) {
                                            ee.collect_diagnostics(else_expr, certs);
                                        }
                                        return;
                                    }
                                }
                            }
                        }
                    }
                }

                // 2-argument binary operator
                if let LeanExpr::App(f_inner, arg1) = f.as_ref() {
                    if let LeanExpr::Const(op_name) = f_inner.as_ref() {
                        if let Some(op) = crate::ops::BinOp::from_name(op_name) {
                            self.collect_diagnostics(arg1, certs);
                            self.collect_diagnostics(a, certs);
                            let s1 = self.eval_expr(arg1).refine_nat();
                            let s2 = self.eval_expr(a).refine_nat();
                            if let (Some(iv1), Some(iv2)) = (s1.interval, s2.interval) {
                                match op {
                                    crate::ops::BinOp::Sub => {
                                        if iv1.max <= iv2.min && iv2.min > 0 {
                                            certs.push(DiagnosticCertificate {
                                                kind: DiagnosticKind::NatSubTruncation,
                                                operator: op_name.clone(),
                                                summary: format!(
                                                    "Natural subtraction `{op_name}` on [{}, {}] - [{}, {}] saturates to [0, 0].",
                                                    iv1.min, iv1.max, iv2.min, iv2.max
                                                ),
                                                hint: "Add guard `b <= a` or switch to `Int` subtraction if negative values are intended.".to_string(),
                                            });
                                        }
                                    }
                                    crate::ops::BinOp::Div | crate::ops::BinOp::Mod => {
                                        if iv2.min <= 0 && 0 <= iv2.max {
                                            certs.push(DiagnosticCertificate {
                                                kind: DiagnosticKind::NatDivModByZero,
                                                operator: op_name.clone(),
                                                summary: format!(
                                                    "Divisor interval [{}, {}] in `{op_name}` includes 0 (Lean total semantics: a / 0 = 0, a % 0 = a).",
                                                    iv2.min, iv2.max
                                                ),
                                                hint: "Prove divisor `d > 0` (`d != 0`) before dividing to avoid total-zero fallback.".to_string(),
                                            });
                                        }
                                    }
                                    _ => {}
                                }
                            }
                            return;
                        }
                    }
                }

                self.collect_diagnostics(f, certs);
                self.collect_diagnostics(a, certs);
            }
            LeanExpr::Let(var, _ty, val, body) => {
                self.collect_diagnostics(val, certs);
                let val_state = self.eval_expr(val);
                let mut local_interp = LeanAbstractInterpreter {
                    environment: self.environment.clone(),
                };
                local_interp.set_decl_state(var, val_state);
                local_interp.collect_diagnostics(body, certs);
            }
            _ => {}
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_eval_lambda_beta_reduction() {
        let interp = LeanAbstractInterpreter::new();
        // (fun x : Nat => x + 1) 41
        let lam = LeanExpr::Lam(
            "x".to_string(),
            Box::new(LeanExpr::Const("Nat".to_string())),
            Box::new(LeanExpr::App(
                Box::new(LeanExpr::App(
                    Box::new(LeanExpr::Const("Nat.add".to_string())),
                    Box::new(LeanExpr::BVar(0)),
                )),
                Box::new(LeanExpr::LitNat(1)),
            )),
        );
        let app = LeanExpr::App(Box::new(lam), Box::new(LeanExpr::LitNat(41)));
        let state = interp.eval_expr(&app);
        assert_eq!(state.sign, AbstractSign::Positive);
        assert_eq!(state.interval, Some(crate::lattice::IntervalBound::new(42, 42)));
    }

    #[test]
    fn test_eval_extended_operators() {
        let interp = LeanAbstractInterpreter::new();

        // 2 ^ 5 = 32
        let pow_expr = LeanExpr::App(
            Box::new(LeanExpr::App(
                Box::new(LeanExpr::Const("Nat.pow".to_string())),
                Box::new(LeanExpr::LitNat(2)),
            )),
            Box::new(LeanExpr::LitNat(5)),
        );
        let s_pow = interp.eval_expr(&pow_expr);
        assert_eq!(s_pow.interval, Some(crate::lattice::IntervalBound::new(32, 32)));
        assert_eq!(s_pow.sign, AbstractSign::Positive);

        // min 15 40 = 15
        let min_expr = LeanExpr::App(
            Box::new(LeanExpr::App(
                Box::new(LeanExpr::Const("Nat.min".to_string())),
                Box::new(LeanExpr::LitNat(15)),
            )),
            Box::new(LeanExpr::LitNat(40)),
        );
        let s_min = interp.eval_expr(&min_expr);
        assert_eq!(s_min.interval, Some(crate::lattice::IntervalBound::new(15, 15)));

        // max 15 40 = 40
        let max_expr = LeanExpr::App(
            Box::new(LeanExpr::App(
                Box::new(LeanExpr::Const("Nat.max".to_string())),
                Box::new(LeanExpr::LitNat(15)),
            )),
            Box::new(LeanExpr::LitNat(40)),
        );
        let s_max = interp.eval_expr(&max_expr);
        assert_eq!(s_max.interval, Some(crate::lattice::IntervalBound::new(40, 40)));

        // 10 != 20 -> True
        let bne_expr = LeanExpr::App(
            Box::new(LeanExpr::App(
                Box::new(LeanExpr::Const("Nat.bne".to_string())),
                Box::new(LeanExpr::LitNat(10)),
            )),
            Box::new(LeanExpr::LitNat(20)),
        );
        let s_bne = interp.eval_expr(&bne_expr);
        assert_eq!(s_bne.boolean, Some(crate::lattice::AbstractBool::True));

        // 25 >= 10 -> True
        let bge_expr = LeanExpr::App(
            Box::new(LeanExpr::App(
                Box::new(LeanExpr::Const("Nat.bge".to_string())),
                Box::new(LeanExpr::LitNat(25)),
            )),
            Box::new(LeanExpr::LitNat(10)),
        );
        let s_bge = interp.eval_expr(&bge_expr);
        assert_eq!(s_bge.boolean, Some(crate::lattice::AbstractBool::True));

        // 10 > 25 -> False
        let bgt_expr = LeanExpr::App(
            Box::new(LeanExpr::App(
                Box::new(LeanExpr::Const("Nat.bgt".to_string())),
                Box::new(LeanExpr::LitNat(10)),
            )),
            Box::new(LeanExpr::LitNat(25)),
        );
        let s_bgt = interp.eval_expr(&bgt_expr);
        assert_eq!(s_bgt.boolean, Some(crate::lattice::AbstractBool::False));

        // true xor true -> False
        let xor_expr = LeanExpr::App(
            Box::new(LeanExpr::App(
                Box::new(LeanExpr::Const("Bool.xor".to_string())),
                Box::new(LeanExpr::Const("true".to_string())),
            )),
            Box::new(LeanExpr::Const("true".to_string())),
        );
        let s_xor = interp.eval_expr(&xor_expr);
        assert_eq!(s_xor.boolean, Some(crate::lattice::AbstractBool::False));
    }

    #[test]
    fn test_backward_arithmetic_guard_refinement() {
        let mut interp = LeanAbstractInterpreter::new();
        interp.set_decl_state(
            "x",
            AbstractState {
                sign: AbstractSign::Top,
                interval: Some(crate::lattice::IntervalBound::new(0, 100)),
                ..AbstractState::top()
            },
        );

        // Guard 1: (x + 5) < 20  =>  in then-branch x in [0, 14]
        let cond_add = LeanExpr::App(
            Box::new(LeanExpr::App(
                Box::new(LeanExpr::Const("Nat.blt".to_string())),
                Box::new(LeanExpr::App(
                    Box::new(LeanExpr::App(
                        Box::new(LeanExpr::Const("Nat.add".to_string())),
                        Box::new(LeanExpr::Const("x".to_string())),
                    )),
                    Box::new(LeanExpr::LitNat(5)),
                )),
            )),
            Box::new(LeanExpr::LitNat(20)),
        );
        let ite_then_x = LeanExpr::App(
            Box::new(LeanExpr::App(
                Box::new(LeanExpr::App(
                    Box::new(LeanExpr::Const("ite".to_string())),
                    Box::new(cond_add.clone()),
                )),
                Box::new(LeanExpr::Const("x".to_string())),
            )),
            Box::new(LeanExpr::LitNat(10)),
        );
        let res_then = interp.eval_expr(&ite_then_x);
        assert_eq!(
            res_then.interval,
            Some(crate::lattice::IntervalBound::new(0, 14))
        );

        // Guard 2: (x - 3) >= 2  =>  in then-branch x >= 5, so [5, 100]
        let cond_sub = LeanExpr::App(
            Box::new(LeanExpr::App(
                Box::new(LeanExpr::Const("Nat.bge".to_string())),
                Box::new(LeanExpr::App(
                    Box::new(LeanExpr::App(
                        Box::new(LeanExpr::Const("Nat.sub".to_string())),
                        Box::new(LeanExpr::Const("x".to_string())),
                    )),
                    Box::new(LeanExpr::LitNat(3)),
                )),
            )),
            Box::new(LeanExpr::LitNat(2)),
        );
        let ite_sub = LeanExpr::App(
            Box::new(LeanExpr::App(
                Box::new(LeanExpr::App(
                    Box::new(LeanExpr::Const("ite".to_string())),
                    Box::new(cond_sub),
                )),
                Box::new(LeanExpr::Const("x".to_string())),
            )),
            Box::new(LeanExpr::LitNat(50)),
        );
        let res_sub = interp.eval_expr(&ite_sub);
        assert_eq!(
            res_sub.interval,
            Some(crate::lattice::IntervalBound::new(5, 100))
        );
    }

    #[test]
    fn test_threshold_widening_fixpoint_and_ast_harvest() {
        let interp = LeanAbstractInterpreter::new();
        // Guard AST mentioning threshold 100: i < 100
        let guard_ast = LeanExpr::App(
            Box::new(LeanExpr::App(
                Box::new(LeanExpr::Const("Nat.blt".to_string())),
                Box::new(LeanExpr::Const("i".to_string())),
            )),
            Box::new(LeanExpr::LitNat(100)),
        );
        let thresholds = guard_ast.collect_nat_thresholds();
        assert!(thresholds.contains(&99));
        assert!(thresholds.contains(&100));
        assert!(thresholds.contains(&101));

        // Loop starting at [0, 0], stepping by +1 while <= 99:
        // Standard widening jumps to [0, INF]; threshold widening stops at [0, 100].
        let init = AbstractState::const_nat(0);
        let fp = interp.compute_threshold_widening_fixpoint(
            init,
            |curr| {
                let iv = curr.interval.unwrap();
                let clamped_max = iv.max.min(99);
                let next_iv = crate::lattice::IntervalBound::new(0, clamped_max + 1);
                AbstractState {
                    sign: AbstractSign::Top,
                    interval: Some(next_iv),
                    ..AbstractState::top()
                }.refine_nat()
            },
            &thresholds,
            2,
            16,
        );
        assert_eq!(fp.interval, Some(crate::lattice::IntervalBound::new(0, 100)));
    }

    #[test]
    fn test_diagnose_expr_certificates() {
        let mut interp = LeanAbstractInterpreter::new();
        interp.set_decl_state(
            "n",
            AbstractState {
                sign: AbstractSign::NonNegative,
                interval: Some(crate::lattice::IntervalBound::new(0, 10)),
                ..AbstractState::top()
            },
        );

        // `if n < 5 then n - 10 else n / n`:
        // - True branch refines `n` to `[0, 4]`, so `n - 10` triggers `NatSubTruncation`.
        // - False branch refines `n` to `[5, 10]`, so `n / n` has divisor `[5, 10]` (NO `NatDivModByZero`).
        let cond_lt5 = LeanExpr::App(
            Box::new(LeanExpr::App(
                Box::new(LeanExpr::Const("Nat.blt".to_string())),
                Box::new(LeanExpr::Const("n".to_string())),
            )),
            Box::new(LeanExpr::LitNat(5)),
        );
        let sub_10 = LeanExpr::App(
            Box::new(LeanExpr::App(
                Box::new(LeanExpr::Const("Nat.sub".to_string())),
                Box::new(LeanExpr::Const("n".to_string())),
            )),
            Box::new(LeanExpr::LitNat(10)),
        );
        let div_n = LeanExpr::App(
            Box::new(LeanExpr::App(
                Box::new(LeanExpr::Const("Nat.div".to_string())),
                Box::new(LeanExpr::Const("n".to_string())),
            )),
            Box::new(LeanExpr::Const("n".to_string())),
        );
        let ite_expr = LeanExpr::App(
            Box::new(LeanExpr::App(
                Box::new(LeanExpr::App(
                    Box::new(LeanExpr::Const("ite".to_string())),
                    Box::new(cond_lt5),
                )),
                Box::new(sub_10),
            )),
            Box::new(div_n),
        );
        let (_state, certs) = interp.diagnose_expr(&ite_expr);
        assert_eq!(certs.len(), 1);
        assert_eq!(certs[0].kind, DiagnosticKind::NatSubTruncation);
        assert!(certs[0].summary.contains("[0, 4] - [10, 10]"));
    }

    #[test]
    fn test_eval_expr_trace_partitioned() {
        let mut interp = LeanAbstractInterpreter::new();
        interp.set_decl_state(
            "x",
            AbstractState {
                sign: AbstractSign::NonNegative,
                interval: Some(crate::lattice::IntervalBound::new(0, 100)),
                ..AbstractState::top()
            },
        );

        // let y = (if x < 50 then 10 else 90) in y + 5
        // Standard `eval_expr` joins y to [10, 90] and produces [15, 95].
        // Trace-partitioned `eval_expr_trace_partitioned` keeps two disjoint partitions:
        //   trace [1] -> [15, 15], trace [0] -> [95, 95].
        let cond_lt50 = LeanExpr::App(
            Box::new(LeanExpr::App(
                Box::new(LeanExpr::Const("Nat.blt".to_string())),
                Box::new(LeanExpr::Const("x".to_string())),
            )),
            Box::new(LeanExpr::LitNat(50)),
        );
        let ite_y = LeanExpr::App(
            Box::new(LeanExpr::App(
                Box::new(LeanExpr::App(
                    Box::new(LeanExpr::Const("ite".to_string())),
                    Box::new(cond_lt50),
                )),
                Box::new(LeanExpr::LitNat(10)),
            )),
            Box::new(LeanExpr::LitNat(90)),
        );
        let body = LeanExpr::App(
            Box::new(LeanExpr::App(
                Box::new(LeanExpr::Const("Nat.add".to_string())),
                Box::new(LeanExpr::Const("y".to_string())),
            )),
            Box::new(LeanExpr::LitNat(5)),
        );
        let let_expr = LeanExpr::Let(
            "y".to_string(),
            Box::new(LeanExpr::Const("Nat".to_string())),
            Box::new(ite_y),
            Box::new(body),
        );

        let tp = interp.eval_expr_trace_partitioned(&let_expr, 2);
        assert_eq!(tp.partitions.len(), 2);
        let tok_true = crate::wto::TraceToken::root().push_branch(1, 2);
        let tok_false = crate::wto::TraceToken::root().push_branch(0, 2);
        assert_eq!(
            tp.partitions.get(&tok_true).unwrap().interval,
            Some(crate::lattice::IntervalBound::new(15, 15))
        );
        assert_eq!(
            tp.partitions.get(&tok_false).unwrap().interval,
            Some(crate::lattice::IntervalBound::new(95, 95))
        );
        assert_eq!(
            tp.collapse().interval,
            Some(crate::lattice::IntervalBound::new(15, 95))
        );
    }
}

