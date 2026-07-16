/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Engine.Eval.Backend

/-!
# Public checked interval evaluation

This module is the authoritative public entry point for evaluating an
expression over a rational box. Backend selection is explicit, every backend
uses its checked evaluator, and a successful result has one backend-independent
enclosure theorem.

Backend-native result types remain available from their advanced engine APIs;
the public outcome intentionally contains only the common interval and the
backend that produced it.
-/

namespace LeanCert

open LeanCert.Core

export LeanCert.Engine (
  BackendChoice
  ConcreteBackend
  EvalError
  EvalResult
  IntervalOutcome
)

/-- Options for the public interval evaluator.

This is initially an alias of the engine dispatcher options so existing
backend configuration remains source-compatible while the public façade
becomes authoritative. -/
abbrev EvalOptions := Engine.BackendOptions

/-- Evaluate an expression over a rational box using a checked certified backend.

The default `.auto` backend currently selects Dyadic evaluation. Explicit
backend requests are honored and invalid domains or configurations return a
structured `EvalError`; they never return a fallback interval. -/
def evalInterval (e : Expr) (box : List IntervalRat)
    (options : EvalOptions := {}) : EvalResult IntervalOutcome :=
  Engine.evalIntervalWith options e box

/-- A successful public interval evaluation encloses the expression value.

Coordinates beyond `box.length` are interpreted as zero, matching the
evaluator's box-to-environment conversion. -/
theorem evalInterval_correct (e : Expr) (box : List IntervalRat)
    (options : EvalOptions) (outcome : IntervalOutcome)
    (hsuccess : evalInterval e box options = .ok outcome)
    (rho : Nat → ℝ)
    (hrho : ∀ i, rho i ∈ box.getD i (IntervalRat.singleton 0)) :
    Expr.eval rho e ∈ outcome.interval := by
  apply Engine.evalIntervalWith_correct options e box outcome hsuccess rho
  intro i
  exact hrho i

end LeanCert
