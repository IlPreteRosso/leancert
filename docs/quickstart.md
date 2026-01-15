# Quickstart

This guide walks through the main use cases for LeanBound.

## Python SDK

### Finding Bounds

```python
import leanbound as lf

x = lf.var('x')
expr = x**2 + lf.sin(x)

# Find min/max on an interval
result = lf.find_bounds(expr, {'x': (0, 1)})

print(f"Minimum: {result.min_bound}")
print(f"Maximum: {result.max_bound}")
```

### Verifying a Bound

```python
# Verify that x^2 + sin(x) ≤ 2 on [0, 1]
verified = lf.verify_bound(expr, {'x': (0, 1)}, upper=2)

if verified.success:
    print("Bound verified!")
    # Get the Lean tactic to prove this formally
    print(verified.certificate.to_lean_tactic())
```

### Finding Roots

```python
# Find where x^2 - 2 = 0 on [1, 2]
roots = lf.find_roots(x**2 - 2, {'x': (1, 2)})

for root in roots.intervals:
    print(f"Root in [{root.lo}, {root.hi}]")
```

### Symbolic Simplification

LeanBound automatically simplifies expressions to avoid interval explosion:

```python
# Without simplification: (x*100 + 5) - (x*100) would have wide bounds
# With simplification: reduces to 5
expr = (x * 100 + 5) - (x * 100)
simplified = lf.simplify(expr)  # Returns const(5)
```

## Lean Tactics

### Point Inequalities (`interval_decide`)

To prove inequalities involving specific numbers (including transcendentals like π or e), use `interval_decide`:

```lean
import LeanBound.Tactic.IntervalAuto

-- Proves π < 3.15
example : Real.pi < 3.15 := by interval_decide

-- Proves e < 3
example : Real.exp 1 < 3 := by interval_decide

-- For complex expressions with constants
example : Real.sin 1 + Real.cos 1 < 1.5 := by interval_decide
```

### Proving Bounds (`interval_bound`)

```lean
import LeanBound.Tactic.IntervalAuto

open LeanBound.Core

-- Use natural Set.Icc syntax with integer bounds
example : ∀ x ∈ Set.Icc (0 : ℝ) 1, Real.exp x ≤ 3 := by interval_bound 15
example : ∀ x ∈ Set.Icc (0 : ℝ) 1, Real.sin x ≤ 1 := by interval_bound
example : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 ≤ Real.exp x := by interval_bound

-- Lower bounds work too
example : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 ≤ x * x := by interval_bound

-- Or use explicit IntervalRat for more control
def I01 : IntervalRat := ⟨0, 1, by norm_num⟩
example : ∀ x ∈ I01, Real.exp x ≤ (3 : ℚ) := by interval_bound 15
```

### Kernel-Verified Bounds (`fast_bound`)

For higher trust, use `fast_bound`. Unlike `interval_bound` which trusts the Lean compiler (`native_decide`), `fast_bound` uses the dyadic backend and reduces proofs entirely within the Lean kernel (`decide`) when possible.

```lean
import LeanBound.Tactic.DyadicAuto

-- Same syntax as interval_bound, but uses dyadic backend
example : ∀ x ∈ Set.Icc (0 : ℝ) 1, x * x + Real.sin x ≤ 2 := by
  fast_bound

-- Increase precision (bits) for tight bounds
example : ∀ x ∈ Set.Icc (0 : ℝ) 1, Real.exp x ≤ 2.72 := by
  fast_bound 100

-- Convenience variants
example : ∀ x ∈ Set.Icc (0 : ℝ) 1, Real.exp x ≤ 2.72 := by
  fast_bound_precise  -- 100 bits precision

example : ∀ x ∈ Set.Icc (0 : ℝ) 1, x * x ≤ 2 := by
  fast_bound_quick    -- 30 bits, faster
```

| Tactic | Backend | Verification | Trust Level |
|--------|---------|--------------|-------------|
| `interval_bound` | Rational | `native_decide` | Compiler + Runtime |
| `fast_bound` | Dyadic | `decide` (when possible) | Kernel only |

### Finding Counter-Examples (`interval_refute`)

If a bound doesn't hold, use `interval_refute` to find a counter-example:

```lean
import LeanBound.Tactic.Refute

-- A false theorem - interval_refute finds where it fails
example : ∀ x ∈ Set.Icc (-2 : ℝ) 2, x * x ≤ 3 := by
  interval_refute
  -- Output: Counter-example found at x ≈ ±2, where x² = 4 > 3
```

### Proving Root Existence

```lean
import LeanBound.Tactic.Discovery

open LeanBound.Core

def I12 : IntervalRat := ⟨1, 2, by norm_num⟩

-- Prove √2 exists via sign change
example : ∃ x ∈ I12, Expr.eval (fun _ => x)
    (Expr.add (Expr.mul (Expr.var 0) (Expr.var 0)) (Expr.neg (Expr.const 2))) = 0 := by
  interval_roots
```

### Discovery Commands

For interactive exploration in the editor:

```lean
import LeanBound.Discovery

-- Find the global minimum
#minimize (fun x => x^2 + Real.sin x) on [-2, 2]

-- Explore function behavior
#explore (Expr.cos (Expr.var 0)) on [0, 4]
```

## High-Performance Dyadic Backend

For deep expressions (neural networks, optimization loops, nested transcendentals), use the dyadic backend to avoid rational denominator explosion:

```lean
import LeanBound.Numerics.IntervalEvalDyadic

open LeanBound.Core LeanBound.Numerics

-- Convert interval to dyadic
def I : IntervalDyadic := IntervalDyadic.ofIntervalRat ⟨0, 1, by norm_num⟩ (-53)

-- Evaluate with standard precision (53 bits)
def result := evalIntervalDyadic expr (fun _ => I) {}

-- Use fast mode for very deep expressions
def fast := evalIntervalDyadic expr (fun _ => I) DyadicConfig.fast

-- Use high precision for tight bounds
def precise := evalIntervalDyadic expr (fun _ => I) DyadicConfig.highPrecision
```

The dyadic backend keeps mantissa size bounded regardless of expression depth, while rational denominators grow exponentially.

## Direct API

For more control, use the certificate API directly:

```lean
import LeanBound.Numerics.Certificate

open LeanBound.Core LeanBound.Numerics LeanBound.Numerics.Certificate

def exprXSq : Expr := Expr.mul (Expr.var 0) (Expr.var 0)

def exprXSq_core : ExprSupportedCore exprXSq :=
  ExprSupportedCore.mul (ExprSupportedCore.var 0) (ExprSupportedCore.var 0)

def I01 : IntervalRat := ⟨0, 1, by norm_num⟩

-- Use native_decide to verify computationally
theorem xsq_le_one : ∀ x ∈ I01, Expr.eval (fun _ => x) exprXSq ≤ (1 : ℚ) :=
  verify_upper_bound exprXSq exprXSq_core I01 1 {} (by native_decide)
```
