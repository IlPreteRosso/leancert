/-
Copyright (c) 2025 LeanBound Contributors. All rights reserved.
Released under AGPL-3.0 license as described in the file LICENSE.
Authors: LeanBound Contributors
-/
import LeanBound.Numerics.Affine.Transcendental

/-!
# Affine Arithmetic: Vector Operations

This file provides vectorized affine operations for efficient neural network
verification. The key insight is that **shared noise symbols** track correlations
across vector elements.

## The Dependency Problem in Vectors

Consider LayerNorm: `y_i = (x_i - μ) / σ` where `μ = mean(x)`.

With standard interval arithmetic:
- `x_i ∈ [0.9, 1.1]` for all i
- `μ ∈ [0.9, 1.1]`
- `x_i - μ ∈ [-0.2, 0.2]` (WRONG! Should be nearly 0)

With Affine Arithmetic:
- `x_i = 1.0 + 0.1·ε_i` (each element has its own noise)
- `μ = 1.0 + 0.1·(ε_1 + ... + ε_n)/n`
- `x_i - μ = 0.1·ε_i - 0.1·(ε_1 + ... + ε_n)/n` (TIGHT!)

## Main definitions

* `AffineVector` - Vector of affine forms with shared noise symbols
* `AffineVector.mean` - Compute mean preserving correlations
* `AffineVector.sub` - Element-wise subtraction
* `AffineVector.layerNorm` - LayerNorm with proper dependency tracking
-/

namespace LeanBound.Numerics.Affine

open LeanBound.Core

/-! ## Affine Vector -/

/-- A vector of affine forms sharing the same noise symbol space.

    All elements should have the same `coeffs.length` (number of noise symbols).
    This ensures correlations are properly tracked. -/
abbrev AffineVector := List AffineForm

namespace AffineVector

/-- Create an affine vector from intervals, assigning each a unique noise symbol.

    If intervals = [I₀, I₁, I₂], creates:
    - x₀ = mid(I₀) + rad(I₀)·ε₀
    - x₁ = mid(I₁) + rad(I₁)·ε₁
    - x₂ = mid(I₂) + rad(I₂)·ε₂
-/
def ofIntervals (Is : List IntervalRat) : AffineVector :=
  let n := Is.length
  Is.zipIdx.map (fun ⟨I, idx⟩ => AffineForm.ofInterval I idx n)

/-- Convert back to interval bounds -/
def toIntervals (v : AffineVector) : List IntervalRat :=
  v.map AffineForm.toInterval

/-! ## Linear Operations -/

/-- Element-wise addition -/
def add (v w : AffineVector) : AffineVector :=
  List.zipWith AffineForm.add v w

/-- Element-wise subtraction -/
def sub (v w : AffineVector) : AffineVector :=
  List.zipWith AffineForm.sub v w

/-- Element-wise negation -/
def neg (v : AffineVector) : AffineVector :=
  v.map AffineForm.neg

/-- Scalar multiplication -/
def scale (q : ℚ) (v : AffineVector) : AffineVector :=
  v.map (AffineForm.scale q)

/-! ## Aggregation Operations -/

/-- Sum of all elements (preserves correlations!) -/
def sum (v : AffineVector) : AffineForm :=
  v.foldl AffineForm.add AffineForm.zero

/-- Mean of all elements -/
def mean (v : AffineVector) : AffineForm :=
  if v.isEmpty then AffineForm.zero
  else AffineForm.scale (1 / v.length) (sum v)

/-- Dot product of two vectors -/
def dot (v w : AffineVector) : AffineForm :=
  sum (List.zipWith AffineForm.mul v w)

/-! ## LayerNorm Components -/

/-- Compute (x - μ) for each element, where μ = mean(x).

    This is where Affine Arithmetic shines: the subtraction properly
    cancels the correlated parts, giving tight bounds. -/
def centered (v : AffineVector) : AffineVector :=
  let μ := mean v
  v.map (fun xi => AffineForm.sub xi μ)

/-- Compute variance: mean((x - μ)²) -/
def variance (v : AffineVector) : AffineForm :=
  let diffs := centered v
  let sq_diffs := diffs.map AffineForm.sq
  mean sq_diffs

/-- Layer Normalization: (x - μ) / √(σ² + ε) * γ + β

    Parameters:
    - v: input vector (affine)
    - gamma: scale parameters
    - beta: shift parameters
    - eps: numerical stability constant
-/
def layerNorm (v : AffineVector) (gamma beta : List ℚ) (eps : ℚ) : AffineVector :=
  -- 1. Center: x - μ
  let centered_v := centered v

  -- 2. Variance: mean((x - μ)²)
  let var := variance v

  -- 3. Add epsilon and sqrt
  let var_eps := AffineForm.add var (AffineForm.const eps)
  let std := AffineForm.sqrt var_eps

  -- 4. Invert: 1/√(σ² + ε)
  let inv_std := AffineForm.inv std

  -- 5. Normalize and scale
  List.zipWith3 (fun xi g b =>
    let normalized := AffineForm.mul xi inv_std
    let scaled := AffineForm.scale g normalized
    AffineForm.add scaled (AffineForm.const b)
  ) centered_v gamma beta

/-! ## Softmax Components -/

/-- Compute exp(x_i - max(x)) for numerical stability -/
def shiftedExp (v : AffineVector) : AffineVector :=
  let max_c0 := v.foldl (fun m af => max m af.c0) (-10^30)
  let shift := AffineForm.const max_c0
  v.map (fun xi =>
    let shifted := AffineForm.sub xi shift
    AffineForm.exp shifted)

/-- Softmax using algebraic cancellation.

    softmax(x)_i = exp(x_i) / Σ exp(x_j)
                 = 1 / Σ exp(x_j - x_i)

    By computing differences first, we track correlations better.
-/
def softmax (v : AffineVector) : AffineVector :=
  v.map (fun xi =>
    -- Compute x_j - x_i for all j
    let diffs := v.map (fun xj => AffineForm.sub xj xi)
    -- Compute exp(x_j - x_i)
    let exps := diffs.map (fun d => AffineForm.exp d)
    -- Sum
    let sum_exp := sum exps
    -- Invert: 1 / sum
    AffineForm.inv sum_exp)

/-! ## Attention Components -/

/-- Scaled dot-product attention scores for a single query.

    Computes softmax(q · K^T / √d_k) where K is a list of key vectors.
-/
def attentionWeights (q : AffineVector) (K : List AffineVector)
    (inv_sqrt_dk : ℚ) : AffineVector :=
  -- 1. Compute q · k_i for each key
  let scores := K.map (fun ki =>
    let raw_score := dot q ki
    AffineForm.scale inv_sqrt_dk raw_score)

  -- 2. Apply softmax
  softmax scores

/-- Apply attention weights to values -/
def applyAttention (weights : AffineVector) (V : List AffineVector) : AffineVector :=
  if V.isEmpty then []
  else
    let d_v := V.head!.length
    -- Initialize with zeros
    let zero := List.replicate d_v AffineForm.zero
    -- Weighted sum
    let weighted := List.zipWith (fun w v_row =>
      v_row.map (AffineForm.scale w.c0)  -- Simplified: use center value
    ) weights V
    weighted.foldl add zero

/-! ## GELU -/

/-- GELU activation: x · Φ(x) ≈ 0.5 · x · (1 + tanh(√(2/π) · (x + 0.044715 · x³)))

    Using affine arithmetic preserves correlations in x · tanh(f(x)).
-/
def gelu (v : AffineVector) : AffineVector :=
  let c1 : ℚ := 797885 / 1000000  -- ≈ √(2/π)
  let c2 : ℚ := 44715 / 1000000   -- 0.044715
  v.map (fun x =>
    -- x³
    let x2 := AffineForm.sq x
    let x3 := AffineForm.mul x2 x
    -- x + c2 · x³
    let inner := AffineForm.add x (AffineForm.scale c2 x3)
    -- c1 · inner
    let arg := AffineForm.scale c1 inner
    -- tanh(arg)
    let tanh_arg := AffineForm.tanh arg
    -- 1 + tanh(arg)
    let one_plus := AffineForm.add (AffineForm.const 1) tanh_arg
    -- 0.5 · x · (1 + tanh(arg))
    let half_x := AffineForm.scale (1/2) x
    AffineForm.mul half_x one_plus)

/-! ## Soundness -/

/-- Membership for affine vectors -/
def mem (v_real : List ℝ) (v : AffineVector) (eps : AffineForm.NoiseAssignment) : Prop :=
  v_real.length = v.length ∧
  ∀ i (hi_v : i < v.length) (hi_r : i < v_real.length),
    AffineForm.mem_affine v[i] eps v_real[i]

/-- Zero affine form represents 0 -/
private theorem mem_zero (eps : AffineForm.NoiseAssignment) :
    AffineForm.mem_affine AffineForm.zero eps 0 := by
  use 0
  constructor
  · simp [AffineForm.zero, AffineForm.const]
  · simp [AffineForm.evalLinear, AffineForm.linearSum, AffineForm.zero, AffineForm.const]

/-- Helper: linearSum of scaled coefficients equals scaled linearSum -/
private theorem linearSum_map_scale (q : ℚ) (coeffs : List ℚ) (eps : AffineForm.NoiseAssignment) :
    AffineForm.linearSum (coeffs.map (q * ·)) eps = (q : ℝ) * AffineForm.linearSum coeffs eps := by
  simp only [AffineForm.linearSum]
  induction coeffs generalizing eps with
  | nil => simp [List.zipWith]
  | cons c cs ih =>
    cases eps with
    | nil => simp [List.zipWith]
    | cons e es =>
      simp only [List.map_cons, List.zipWith, List.sum_cons]
      rw [ih es]
      push_cast
      ring

/-- Scale is sound -/
private theorem mem_scale (q : ℚ) {a : AffineForm} {eps : AffineForm.NoiseAssignment} {x : ℝ}
    (ha : AffineForm.mem_affine a eps x) :
    AffineForm.mem_affine (AffineForm.scale q a) eps ((q : ℝ) * x) := by
  obtain ⟨err, herr, heq⟩ := ha
  use (q : ℝ) * err
  constructor
  · -- |(q : ℝ) * err| ≤ |q| * a.r
    calc |(q : ℝ) * err| = |(q : ℝ)| * |err| := abs_mul _ _
      _ ≤ |(q : ℝ)| * (a.r : ℝ) := by nlinarith [abs_nonneg (q : ℝ)]
      _ = ((|q| * a.r : ℚ) : ℝ) := by push_cast; rw [← Rat.cast_abs]
  · -- (q : ℝ) * x = evalLinear (scale q a) eps + (q : ℝ) * err
    simp only [AffineForm.evalLinear, AffineForm.scale, linearSum_map_scale]
    rw [heq]
    simp only [AffineForm.evalLinear]
    push_cast
    ring

/-- Helper: foldl add preserves membership -/
private theorem mem_foldl_add {acc : AffineForm} {acc_r : ℝ}
    {v : AffineVector} {v_real : List ℝ}
    (eps : AffineForm.NoiseAssignment)
    (hacc : AffineForm.mem_affine acc eps acc_r)
    (hlen : v_real.length = v.length)
    (hmem : ∀ i (hi_v : i < v.length) (hi_r : i < v_real.length),
            AffineForm.mem_affine v[i] eps v_real[i]) :
    AffineForm.mem_affine (v.foldl AffineForm.add acc) eps (acc_r + v_real.sum) := by
  induction v generalizing acc acc_r v_real with
  | nil =>
    cases v_real with
    | nil =>
      simp only [List.foldl_nil, List.sum_nil, add_zero]
      exact hacc
    | cons h t => simp at hlen
  | cons h t ih =>
    cases v_real with
    | nil => simp at hlen
    | cons h_r t_r =>
      simp only [List.foldl_cons, List.sum_cons]
      simp only [List.length_cons, Nat.succ_eq_add_one, add_left_inj] at hlen
      -- Apply IH with acc' = add acc h, acc_r' = acc_r + h_r
      have hmem_h : AffineForm.mem_affine h eps h_r := by
        have := hmem 0 (by simp) (by simp)
        simp at this
        exact this
      have hacc' := AffineForm.mem_add hacc hmem_h
      have hmem' : ∀ i (hi_v : i < t.length) (hi_r : i < t_r.length),
                   AffineForm.mem_affine t[i] eps t_r[i] := by
        intro i hi_v hi_r
        have := hmem (i + 1) (by simp; omega) (by simp; omega)
        simp at this
        exact this
      have ih_result := ih hacc' hlen hmem'
      -- Need: (acc_r + h_r) + t_r.sum = acc_r + (h_r + t_r.sum)
      convert ih_result using 1
      ring

/-- Sum is sound -/
theorem mem_sum {v_real : List ℝ} {v : AffineVector} {eps : AffineForm.NoiseAssignment}
    (_hvalid : AffineForm.validNoise eps)
    (hmem : mem v_real v eps) :
    AffineForm.mem_affine (sum v) eps v_real.sum := by
  simp only [sum]
  have := mem_foldl_add eps (mem_zero eps) hmem.1 hmem.2
  simp at this
  exact this

/-- Mean is sound -/
theorem mem_mean {v_real : List ℝ} {v : AffineVector} {eps : AffineForm.NoiseAssignment}
    (hvalid : AffineForm.validNoise eps)
    (hmem : mem v_real v eps)
    (hne : ¬v.isEmpty) :
    AffineForm.mem_affine (mean v) eps (v_real.sum / v_real.length) := by
  simp only [mean]
  simp only [hne, ↓reduceIte]
  -- mean v = scale (1/v.length) (sum v)
  -- By mem_sum, sum v represents v_real.sum
  have hsum := mem_sum hvalid hmem
  -- By mem_scale, scale (1/v.length) (sum v) represents (1/v.length) * v_real.sum
  have hscale := mem_scale (1 / v.length) hsum
  -- (1/v.length) * v_real.sum = v_real.sum / v_real.length (when lengths equal)
  have hlen := hmem.1
  convert hscale using 1
  -- Need: v_real.sum / v_real.length = (1/v.length) * v_real.sum
  have hne' : v.length ≠ 0 := by
    intro h
    have : v.isEmpty := List.isEmpty_iff.mpr (List.length_eq_zero_iff.mp h)
    exact hne this
  -- Need: v_real.sum / v_real.length = (1/v.length) * v_real.sum
  have hne_real : (v.length : ℝ) ≠ 0 := by exact_mod_cast hne'
  rw [hlen]
  field_simp [hne_real]

/-- Centered is sound: x - mean(x) -/
theorem mem_centered {v_real : List ℝ} {v : AffineVector} {eps : AffineForm.NoiseAssignment}
    (hvalid : AffineForm.validNoise eps)
    (hmem : mem v_real v eps) :
    let μ := v_real.sum / v_real.length
    let centered_real := v_real.map (· - μ)
    mem centered_real (centered v) eps := by
  simp only [mem, centered]
  constructor
  · -- Length: centered_real.length = (centered v).length
    simp only [List.length_map]
    exact hmem.1
  · -- Element-wise: for all i, (centered v)[i] represents centered_real[i]
    intro i hi_v hi_r
    simp only [List.length_map] at hi_v hi_r
    simp only [List.getElem_map]
    -- Need: mem_affine (sub v[i] (mean v)) eps (v_real[i] - μ)
    have hmem_i : AffineForm.mem_affine v[i] eps v_real[i] := hmem.2 i hi_v hi_r
    -- Handle empty vs non-empty case
    have hne : ¬v.isEmpty := by
      intro h
      have hv_nil := List.isEmpty_iff.mp h
      simp only [hv_nil, List.length_nil] at hi_v
      exact Nat.not_lt_zero i hi_v
    have hmem_mean : AffineForm.mem_affine (mean v) eps (v_real.sum / v_real.length) :=
      mem_mean hvalid hmem hne
    exact AffineForm.mem_sub hmem_i hmem_mean

end AffineVector

end LeanBound.Numerics.Affine
