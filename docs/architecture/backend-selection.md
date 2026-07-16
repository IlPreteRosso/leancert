# Interval Backend Selection

LeanCert exposes one backend policy in `LeanCert.Engine.Eval.Backend`.
Callers use `evalIntervalWith` with `BackendOptions`; JSON callers use the
ordinary `eval_interval`, `check_bound`, `global_min`, and `global_max`
methods with a `backend` field.

Supported selector values are `auto`, `rational`, `dyadic`, and `affine`.

| Operation | `auto` backend | Explicit alternatives |
|---|---|---|
| Interval evaluation and bound checks | Dyadic | Rational, Dyadic, Affine |
| Global optimization | Dyadic | Rational, Dyadic, Affine |
| Integration | Rational | Rational |
| Root finding | Rational | Rational |

`auto` chooses the fastest backend with a certified implementation for the
requested operation. It does not fall through after a domain error. An
explicit unsupported backend is rejected rather than silently changed.

Every successful evaluation comes from a checked evaluator and records the
concrete backend in its result. Reciprocal intervals containing zero,
nonpositive logarithm domains, invalid `atanh` domains, and invalid Dyadic
rounding precision return structured errors. Legacy total evaluators remain
available internally for theorem statements and compatibility, but public
bridge handlers do not expose their finite fallback values.

The historical suffixed JSON methods (`eval_interval_dyadic`,
`eval_interval_affine`, `global_min_dyadic`, and so on) are compatibility
aliases. New clients should use the generic method and selector.

At the Lean API level, division-capable guided optimization and
counterexample search now return `EvalResult`: `globalMinimizeGuidedDiv`,
`globalMaximizeGuidedDiv`, `findViolationDiv`, and `findViolationLowerDiv` can
report a domain failure. The former total `CoreDiv` helpers were removed
because their return type could not distinguish a certified enclosure from a
finite heuristic fallback.

## Options

The common JSON options are:

```json
{
  "backend": "auto",
  "taylorDepth": 10,
  "precision": -53,
  "maxNoiseSymbols": 0
}
```

`precision` must be nonpositive when Dyadic evaluation is selected, because
the correctness theorem for outward conversion requires that condition.
`maxNoiseSymbols` is used only by Affine evaluation. The unused
`roundAfterOps` option was removed: Dyadic arithmetic rounds outward after
each arithmetic operation, exactly as its evaluator and proof specify.

`taylorDepth` configures the Dyadic and Affine evaluators. The checked Rational
evaluator currently has a fixed verified depth of 10; Rational evaluation,
optimization, integration, bisection, and candidate-certification requests
with another value are rejected as invalid configuration rather than silently
ignoring the option.

Checked global optimization supports `useMonotonicity`. For the differentiable
`const/var/add/mul/neg/exp/sin/cos` fragment, a computable interval-AD gradient
may fix monotone coordinates to the minimizing endpoint. The checked loop's
invariant carries a representative point in the pruned box and a proof that its
objective value is no larger than the original point. Expressions outside that
AD fragment remain certified and simply receive no monotonicity reduction.

Checked branch-and-bound computes its lower bound from the current partition
of terminal and active boxes. Subdivision can therefore tighten dependency-
sensitive expressions; the root enclosure is not retained as a permanent
lower bound. Dispatcher-level min/max theorems connect every successful
Rational, Dyadic, or Affine result to the real semantics.
