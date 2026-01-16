/-
Copyright (c) 2024 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Engine.Optimization.Global

/-!
# Counter-Example Search

This file provides machinery for finding counter-examples to bound claims.
Finding a counter-example is just global optimization: to disprove `f(x) ≤ C`,
we maximize `f(x)` and check if the result exceeds `C`.

## Main definitions

* `CounterExampleStatus` - Whether a counter-example is verified or just a candidate
* `CounterExample` - A point that violates (or may violate) a bound
* `findViolation` - Search for counter-examples to `f(x) ≤ limit`
* `findViolationLower` - Search for counter-examples to `limit ≤ f(x)`

## Counter-Example Types

* **Verified**: The rigorous lower bound of `max(f)` exceeds the limit.
  This is a mathematical proof that the bound is false.

* **Candidate**: The upper bound exceeds the limit, but the lower bound doesn't.
  This might indicate a true violation (precision too low) or a false positive
  (interval wrapping).

## Usage

```lean
-- Check if x² ≤ 3 on [-2, 2]
let result := findViolation (Expr.mul (Expr.var 0) (Expr.var 0)) [⟨-2, 2, by norm_num⟩] 3
-- Returns some { status := .Verified, ... } because max(x²) = 4 > 3
```
-/

namespace LeanCert.Engine.Search

open LeanCert.Core
open LeanCert.Engine.Optimization

/-! ### Counter-example types -/

/-- Status of a counter-example -/
inductive CounterExampleStatus where
  /-- Definitely violates the bound (proof of negation possible) -/
  | Verified
  /-- Likely violates the bound (or precision too low) -/
  | Candidate
  deriving Repr, DecidableEq, Inhabited

/-- A counter-example to a bound claim -/
structure CounterExample where
  /-- The input point (midpoint of the best box) -/
  point : List ℚ
  /-- The computed output interval at/near the point -/
  valueLo : ℚ
  valueHi : ℚ
  /-- Whether the counter-example is verified or just a candidate -/
  status : CounterExampleStatus
  /-- The box containing the counter-example -/
  box : Box
  /-- Number of iterations used -/
  iterations : Nat
  deriving Repr

namespace CounterExample

/-- Is this a verified counter-example? -/
def isVerified (ce : CounterExample) : Bool :=
  ce.status == .Verified

/-- Get the midpoint of each interval in the box -/
def boxMidpoint (B : Box) : List ℚ :=
  B.map (·.midpoint)

end CounterExample

/-! ### Upper bound violation (f(x) ≤ limit) -/

/--
Search for a counter-example to the claim `∀ x ∈ domain, f(x) ≤ limit`.

Returns `some CounterExample` if the bound cannot be verified.
Returns `none` if the theorem appears to be true (no violation found).

**Algorithm**: Maximize `f(x)` over the domain. If `max(f).lo > limit`,
the bound is definitely false. If `max(f).hi > limit` but `lo ≤ limit`,
there might be a violation.
-/
def findViolation (e : Expr) (domain : Box) (limit : ℚ)
    (cfg : GlobalOptConfig := {}) : Option CounterExample :=
  -- Maximize f to find the highest value
  let result := globalMaximizeCore e domain cfg

  let max_lo := result.bound.lo
  let max_hi := result.bound.hi
  let best_box := result.bound.bestBox

  if max_lo > limit then
    -- CASE 1: Verified counter-example
    -- The lower bound of the maximum exceeds the limit.
    -- For ANY point in best_box, f(x) ≥ max_lo > limit.
    some {
      point := CounterExample.boxMidpoint best_box
      valueLo := max_lo
      valueHi := max_hi
      status := .Verified
      box := best_box
      iterations := result.bound.iterations
    }
  else if max_hi > limit then
    -- CASE 2: Candidate counter-example
    -- The upper bound exceeds limit, but lower bound doesn't.
    -- This could be:
    --   (a) A true violation that we can't rigorously prove (precision issue)
    --   (b) A false positive from interval overestimation
    some {
      point := CounterExample.boxMidpoint best_box
      valueLo := max_lo
      valueHi := max_hi
      status := .Candidate
      box := best_box
      iterations := result.bound.iterations
    }
  else
    -- CASE 3: No violation found
    -- max_hi ≤ limit, so the bound appears to be true
    none

/--
Variant of `findViolation` with division support.
-/
def findViolationDiv (e : Expr) (domain : Box) (limit : ℚ)
    (cfg : GlobalOptConfig := {}) : Option CounterExample :=
  let result := globalMaximizeCoreDiv e domain cfg

  let max_lo := result.bound.lo
  let max_hi := result.bound.hi
  let best_box := result.bound.bestBox

  if max_lo > limit then
    some {
      point := CounterExample.boxMidpoint best_box
      valueLo := max_lo
      valueHi := max_hi
      status := .Verified
      box := best_box
      iterations := result.bound.iterations
    }
  else if max_hi > limit then
    some {
      point := CounterExample.boxMidpoint best_box
      valueLo := max_lo
      valueHi := max_hi
      status := .Candidate
      box := best_box
      iterations := result.bound.iterations
    }
  else
    none

/-! ### Lower bound violation (limit ≤ f(x)) -/

/--
Search for a counter-example to the claim `∀ x ∈ domain, limit ≤ f(x)`.

Returns `some CounterExample` if the bound cannot be verified.

**Algorithm**: Minimize `f(x)` over the domain. If `min(f).hi < limit`,
the bound is definitely false.
-/
def findViolationLower (e : Expr) (domain : Box) (limit : ℚ)
    (cfg : GlobalOptConfig := {}) : Option CounterExample :=
  -- Minimize f to find the lowest value
  let result := globalMinimizeCore e domain cfg

  let min_lo := result.bound.lo
  let min_hi := result.bound.hi
  let best_box := result.bound.bestBox

  if min_hi < limit then
    -- CASE 1: Verified counter-example
    -- The upper bound of the minimum is below the limit.
    -- For ANY point in best_box, f(x) ≤ min_hi < limit.
    some {
      point := CounterExample.boxMidpoint best_box
      valueLo := min_lo
      valueHi := min_hi
      status := .Verified
      box := best_box
      iterations := result.bound.iterations
    }
  else if min_lo < limit then
    -- CASE 2: Candidate counter-example
    some {
      point := CounterExample.boxMidpoint best_box
      valueLo := min_lo
      valueHi := min_hi
      status := .Candidate
      box := best_box
      iterations := result.bound.iterations
    }
  else
    -- CASE 3: No violation found
    -- min_lo ≥ limit, so the bound appears to be true
    none

/--
Variant with division support.
-/
def findViolationLowerDiv (e : Expr) (domain : Box) (limit : ℚ)
    (cfg : GlobalOptConfig := {}) : Option CounterExample :=
  let result := globalMinimizeCoreDiv e domain cfg

  let min_lo := result.bound.lo
  let min_hi := result.bound.hi
  let best_box := result.bound.bestBox

  if min_hi < limit then
    some {
      point := CounterExample.boxMidpoint best_box
      valueLo := min_lo
      valueHi := min_hi
      status := .Verified
      box := best_box
      iterations := result.bound.iterations
    }
  else if min_lo < limit then
    some {
      point := CounterExample.boxMidpoint best_box
      valueLo := min_lo
      valueHi := min_hi
      status := .Candidate
      box := best_box
      iterations := result.bound.iterations
    }
  else
    none

/-! ### Strict bound violations -/

/--
Search for a counter-example to `∀ x ∈ domain, f(x) < limit`.
A violation means `f(x) ≥ limit` for some `x`.
-/
def findViolationStrict (e : Expr) (domain : Box) (limit : ℚ)
    (cfg : GlobalOptConfig := {}) : Option CounterExample :=
  let result := globalMaximizeCore e domain cfg

  let max_lo := result.bound.lo
  let max_hi := result.bound.hi
  let best_box := result.bound.bestBox

  -- For strict inequality, we need max(f) ≥ limit (not just >)
  if max_lo ≥ limit then
    some {
      point := CounterExample.boxMidpoint best_box
      valueLo := max_lo
      valueHi := max_hi
      status := .Verified
      box := best_box
      iterations := result.bound.iterations
    }
  else if max_hi ≥ limit then
    some {
      point := CounterExample.boxMidpoint best_box
      valueLo := max_lo
      valueHi := max_hi
      status := .Candidate
      box := best_box
      iterations := result.bound.iterations
    }
  else
    none

/--
Search for a counter-example to `∀ x ∈ domain, limit < f(x)`.
A violation means `f(x) ≤ limit` for some `x`.
-/
def findViolationStrictLower (e : Expr) (domain : Box) (limit : ℚ)
    (cfg : GlobalOptConfig := {}) : Option CounterExample :=
  let result := globalMinimizeCore e domain cfg

  let min_lo := result.bound.lo
  let min_hi := result.bound.hi
  let best_box := result.bound.bestBox

  if min_hi ≤ limit then
    some {
      point := CounterExample.boxMidpoint best_box
      valueLo := min_lo
      valueHi := min_hi
      status := .Verified
      box := best_box
      iterations := result.bound.iterations
    }
  else if min_lo ≤ limit then
    some {
      point := CounterExample.boxMidpoint best_box
      valueLo := min_lo
      valueHi := min_hi
      status := .Candidate
      box := best_box
      iterations := result.bound.iterations
    }
  else
    none

/-! ### Pretty printing -/

/-- Format a counter-example for display -/
def CounterExample.format (ce : CounterExample) (limit : ℚ) : String :=
  let statusStr := match ce.status with
    | .Verified => "VERIFIED"
    | .Candidate => "CANDIDATE (may be false positive)"
  let pointStr := ce.point.map toString |>.intersperse ", " |> String.join
  let intervalStr := s!"[{ce.valueLo}, {ce.valueHi}]"
  s!"Counter-example ({statusStr}):\n\
     • Point: ({pointStr})\n\
     • Value: {intervalStr}\n\
     • Limit: {limit}\n\
     • Iterations: {ce.iterations}"

end LeanCert.Engine.Search
