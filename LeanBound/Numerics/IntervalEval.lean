/-
Copyright (c) 2024 LeanBound Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanBound Contributors
-/
import LeanBound.Core.Support
import LeanBound.Numerics.Eval.Core
import LeanBound.Numerics.Eval.Extended
import LeanBound.Tactic.Bound.Lemmas

/-!
# Interval Evaluation of Expressions

This file re-exports the interval evaluation infrastructure for `LeanBound.Core.Expr`.

## Module structure

The implementation is split across several files:

* `LeanBound.Core.Support` - Expression support predicates (`ExprSupportedCore`,
  `ExprSupported`, `ExprSupportedWithInv`)

* `LeanBound.Numerics.Eval.Core` - Computable interval evaluator (`evalIntervalCore`)
  and transcendental interval bounds

* `LeanBound.Numerics.Eval.Extended` - Noncomputable evaluator (`evalInterval`) and
  partial evaluator with inv/log support (`evalInterval?`)

* `LeanBound.Tactic.Bound.Lemmas` - Tactic-facing lemmas for proving bounds

## Main definitions (re-exported)

### Expression support predicates
* `ExprSupportedCore` - Computable subset (const, var, add, mul, neg, sin, cos, exp, sqrt, sinh, cosh, tanh, pi)
* `ExprSupported` - Noncomputable AD subset (const, var, add, mul, neg, sin, cos, exp)
* `ExprSupportedWithInv` - Syntactic support including inv and log

### Evaluators
* `evalIntervalCore` - Computable interval evaluator (uses Taylor series)
* `evalInterval` - Noncomputable evaluator (uses floor/ceil for exp)
* `evalInterval?` - Partial evaluator with inv/log support

### Correctness theorems
* `evalIntervalCore_correct` - Core evaluator correctness
* `evalInterval_correct` - Extended evaluator correctness
* `evalInterval?_correct` - Partial evaluator correctness

### Tactic lemmas
* `exprCore_le_of_interval_hi` / `exprCore_ge_of_interval_lo` - Core bounds
* `expr_le_of_interval_hi` / `expr_ge_of_interval_lo` - Extended bounds

## Design notes

The evaluators are split by computability:
- `evalIntervalCore` is COMPUTABLE, enabling `native_decide` in tactics
- `evalInterval` is NONCOMPUTABLE, using Real.exp with floor/ceil bounds
- Both are fully verified (no sorry, no axioms)
-/

namespace LeanBound.Numerics

-- Re-export all definitions from component modules
-- All imports are transitive, so users can continue to `import LeanBound.Numerics.IntervalEval`
-- and have access to all definitions as before.

end LeanBound.Numerics
