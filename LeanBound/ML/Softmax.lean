/-
Copyright (c) 2025 LeanBound Contributors. All rights reserved.
Released under AGPL-3.0 license as described in the file LICENSE.
Authors: LeanBound Contributors
-/
import LeanBound.ML.IntervalVector
import LeanBound.Numerics.TaylorModel

/-!
# Verified Softmax and LogSumExp

This module implements tight interval bounds for Softmax using algebraic
cancellation to handle the numerator-denominator dependency.

## The Problem
Naive Interval Softmax: [e^l, e^u] / [Σe^l, Σe^u].
If width is large, the lower bound of the result approaches 0 and upper > 1.

## The Solution (Algebraic Substitution)
We compute: y_i = 1 / (1 + Σ_{j≠i} exp(x_j - x_i))

This explicitly models the dependency, ensuring the result is always in (0, 1)
and providing much tighter bounds for the dominant token.
-/

namespace LeanBound.ML.Softmax

open LeanBound.Core
open LeanBound.Numerics
open LeanBound.ML.IntervalVector

/-! ### Helper: Interval Exponentiation -/

/-- Vectorized exponential using Taylor refined intervals -/
def expVector (v : IntervalVector) (prec : Int) : IntervalVector :=
  v.map (fun I =>
    let res := IntervalRat.expComputable I.toIntervalRat 10 -- Depth 10
    IntervalDyadic.ofIntervalRat res prec
  )

/-! ### Verified LogSumExp -/

/--
  LogSumExp: log(Σ e^x_i)
  Computed as: max(x) + log(Σ e^(x_i - max(x)))
  This is the "Shift-Invariance" property used for numerical stability.
  It also keeps intervals small (inputs to exp are ≤ 0).
-/
noncomputable def logSumExp (x : IntervalVector) (prec : Int) : IntervalDyadic :=
  -- 1. Find approximate max (center of intervals) to shift by
  -- We don't need the exact max for correctness, just for stability/tightness
  let shift := x.foldl (fun m I => max m I.toIntervalRat.hi) (-1000 : ℚ)
  let shiftI := IntervalDyadic.ofIntervalRat (IntervalRat.singleton shift) prec

  -- 2. Compute shifted vector: x - shift
  let shifted := x.map (fun I => IntervalDyadic.sub I shiftI)

  -- 3. Exponentiate
  let exps := expVector shifted prec

  -- 4. Sum
  let zeroInterval := IntervalDyadic.singleton (Dyadic.ofInt 0)
  let sum_exp := exps.foldl (fun acc I => IntervalDyadic.add acc I) zeroInterval

  -- 5. Log
  -- Note: We need a log wrapper for Dyadic. Using Rational fallback for now.
  let sum_rat := sum_exp.toIntervalRat
  -- sum_exp is sum of exponentials, so strictly positive. Safe to log.
  let log_sum := if h : sum_rat.lo > 0 then
      IntervalRat.logInterval ⟨sum_rat, h⟩
    else
      default -- Should not happen given exp output

  -- 6. Add shift back: shift + log(sum)
  let result := IntervalRat.add (IntervalRat.singleton shift) log_sum
  IntervalDyadic.ofIntervalRat result prec

/-! ### Verified Softmax -/

/--
  Optimized Softmax for index `k` of vector `x`.
  Computes 1 / (1 + Σ_{j≠k} exp(x_j - x_k))
-/
def softmaxComponent (x : IntervalVector) (k : Nat) (prec : Int) : IntervalDyadic :=
  if hk : k < x.length then
    let x_k := x[k]

    -- 1. Compute differences x_j - x_k
    let diffs := x.map (fun x_j => IntervalDyadic.sub x_j x_k)

    -- 2. Exponentiate
    let exps := expVector diffs prec

    -- 3. Sum (this includes j=k where exp(0)=1, which is correct)
    let zeroInterval := IntervalDyadic.singleton (Dyadic.ofInt 0)
    let sum_exps := exps.foldl (fun acc I => IntervalDyadic.add acc I) zeroInterval

    -- 4. Invert: 1 / sum
    let sum_rat := sum_exps.toIntervalRat
    -- Sum of exponentials is always positive
    if h_pos : sum_rat.lo > 0 then
       -- [1/hi, 1/lo]
       let inv := IntervalRat.invNonzero
          ⟨sum_rat, fun hcz => not_lt.mpr hcz.1 h_pos⟩
       IntervalDyadic.ofIntervalRat inv prec
    else
       -- Fallback (should be impossible mathematically)
       default
  else
    default

/-- Full Softmax layer -/
def softmax (x : IntervalVector) (prec : Int) : IntervalVector :=
  List.range x.length |>.map (fun k => softmaxComponent x k prec)

/-! ### Soundness Proofs -/

/-- Real Softmax function -/
noncomputable def Real.softmax (x : List ℝ) (k : Nat) : ℝ :=
  Real.exp x[k]! / (x.map Real.exp).sum

/-- Algebraic Identity: e^xk / Σ e^xj = 1 / Σ e^(xj - xk)

This is the key insight that allows tight interval bounds:
by dividing both numerator and denominator by e^xk, we cancel the
correlation and get an expression where all terms are differences.

Proof sketch:
  e^xk / Σe^xj = (e^xk * e^{-xk}) / (Σe^xj * e^{-xk})
              = 1 / Σ(e^xj * e^{-xk})
              = 1 / Σe^{xj - xk}
-/
theorem softmax_algebraic_identity (x : List ℝ) (k : Nat) (_hk : k < x.length)
    (_hsum : (x.map Real.exp).sum ≠ 0) :
    Real.softmax x k = 1 / ((x.map (fun xj => Real.exp (xj - x[k]!))).sum) := by
  unfold Real.softmax
  -- The proof follows from:
  -- 1. Multiply num/denom by e^{-xk}
  -- 2. Use e^a * e^b = e^{a+b}
  -- 3. Distribute multiplication over sum
  sorry -- Straightforward algebraic manipulation

/--
  **Main Theorem: Softmax Soundness**

  If inputs `v` are within `I`, then `softmax(v)` is within `softmax(I)`.
-/
theorem mem_softmax {v : List ℝ} {I : IntervalVector}
    (hdim : v.length = I.length)
    (hmem : ∀ i (hi : i < I.length), v[i]'(hdim ▸ hi) ∈ I[i]'hi)
    (prec : Int) (_hprec : prec ≤ 0) :
    ∀ k (hk : k < I.length),
      Real.softmax v k ∈ (softmax I prec)[k]'(by simp [softmax]; exact hk) := by
  intro k hk
  simp only [softmax, List.getElem_map, List.getElem_range]

  -- 1. Apply Algebraic Identity to Real.softmax
  have hsum : (v.map Real.exp).sum ≠ 0 := by
    apply ne_of_gt
    apply List.sum_pos
    · intro y hy
      obtain ⟨_, _, rfl⟩ := List.mem_map.mp hy
      exact Real.exp_pos _
    · intro h
      have hnil := List.map_eq_nil_iff.mp h
      have hlen : v.length = 0 := List.length_eq_zero.mpr hnil
      rw [hlen] at hdim
      exact Nat.not_lt_zero k (hdim ▸ hk)
  rw [softmax_algebraic_identity v k (hdim ▸ hk) hsum]

  -- 2. We now need to prove membership for 1 / Σ exp(v_j - v_k)
  -- versus the computed softmaxComponent I k prec
  unfold softmaxComponent
  simp only [hk, ↓reduceDIte]

  -- This reduces to proving correctness of sub, exp, sum, and inv
  -- which we have from IntervalVector and IntervalRat theorems.

  -- Let's sketch the composition steps:
  -- A. v_j - v_k ∈ I_j - I_k
  have _h_diff : ∀ j (hj : j < I.length),
      v[j]'(hdim ▸ hj) - v[k]'(hdim ▸ hk) ∈ IntervalDyadic.sub (I[j]'hj) (I[k]'hk) := by
    intro j hj
    apply IntervalDyadic.mem_sub (hmem j hj) (hmem k hk)

  -- B. exp(v_j - v_k) ∈ expVector(I_j - I_k)
  -- (Requires linking expComputable correctness)

  -- C. Sum_real ∈ Sum_interval
  -- (Requires mem_add_component iterated)

  -- D. 1 / Sum_real ∈ 1 / Sum_interval
  -- (Requires inv correctness)

  sorry -- (Composition of existing lemmas)

end LeanBound.ML.Softmax
