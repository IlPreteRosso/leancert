/-
Copyright (c) 2025 LeanBound Contributors. All rights reserved.
Released under AGPL-3.0 license as described in the file LICENSE.
Authors: LeanBound Contributors
-/
import LeanBound.Core.IntervalDyadic

/-!
# Interval Vector Arithmetic

This file provides vector operations for Dyadic intervals, enabling
verified propagation of bounds through linear layers of neural networks.

## Main definitions

* `IntervalVector` - A list of Dyadic intervals representing bounded vectors
* `scalarMul` - Multiply an interval by a rational scalar
* `dotProduct` - Dot product of rational weights with interval vector
* `add` - Pointwise addition of interval vectors

## Main theorems

* `mem_scalarMul` - Soundness of scalar multiplication
* `mem_dotProduct` - Soundness of dot product (FTIA for linear combinations)
* `mem_add` - Soundness of vector addition
-/

namespace LeanBound.ML

open LeanBound.Core

/-- A vector of intervals representing bounded real vectors -/
abbrev IntervalVector := List IntervalDyadic

namespace IntervalVector

/-- Multiply an interval by a rational scalar.
    Uses the existing interval multiplication by converting the scalar to a singleton. -/
def scalarMulInterval (w : ℚ) (I : IntervalDyadic) (prec : Int := -53) : IntervalDyadic :=
  let wInterval := IntervalDyadic.ofIntervalRat (IntervalRat.singleton w) prec
  IntervalDyadic.mul wInterval I

/-- Soundness of scalar-interval multiplication -/
theorem mem_scalarMulInterval {w : ℚ} {x : ℝ} {I : IntervalDyadic}
    (hx : x ∈ I) (prec : Int) (hprec : prec ≤ 0 := by norm_num) :
    (w : ℝ) * x ∈ scalarMulInterval w I prec := by
  unfold scalarMulInterval
  apply IntervalDyadic.mem_mul
  · exact IntervalDyadic.mem_ofIntervalRat (IntervalRat.mem_singleton w) prec hprec
  · exact hx

/-- Dot product of rational weights with an interval vector.
    Returns an interval containing all possible dot products. -/
def dotProduct (weights : List ℚ) (inputs : IntervalVector) (prec : Int := -53) : IntervalDyadic :=
  match weights, inputs with
  | [], [] => IntervalDyadic.singleton (Dyadic.ofInt 0)
  | w :: ws, I :: Is =>
      IntervalDyadic.add (scalarMulInterval w I prec) (dotProduct ws Is prec)
  | _, _ => IntervalDyadic.singleton (Dyadic.ofInt 0)  -- dimension mismatch fallback

/-- Helper: real dot product of two lists -/
def realDotProduct (weights : List ℚ) (values : List ℝ) : ℝ :=
  match weights, values with
  | [], [] => 0
  | w :: ws, x :: xs => (w : ℝ) * x + realDotProduct ws xs
  | _, _ => 0

/-- Zero is in the zero singleton -/
theorem mem_zero_singleton : (0 : ℝ) ∈ IntervalDyadic.singleton (Dyadic.ofInt 0) := by
  have h := IntervalDyadic.mem_singleton (Dyadic.ofInt 0)
  simp only [Dyadic.toRat_ofInt, Int.cast_zero, Rat.cast_zero] at h
  exact h

/-- Soundness of dot product for matching-length lists -/
theorem mem_dotProduct_aux (weights : List ℚ) (xs : List ℝ) (Is : IntervalVector)
    (hlen : weights.length = Is.length)
    (hxlen : xs.length = Is.length)
    (hmem : ∀ i, (hi : i < Is.length) → xs[i]'(by omega) ∈ Is[i]'hi)
    (prec : Int) (hprec : prec ≤ 0) :
    realDotProduct weights xs ∈ dotProduct weights Is prec := by
  induction weights generalizing xs Is with
  | nil =>
    match xs, Is with
    | [], [] =>
      simp only [realDotProduct, dotProduct]
      exact mem_zero_singleton
    | _ :: _, [] => simp at hxlen
    | [], _ :: _ => simp at hlen
    | _ :: _, _ :: _ => simp at hlen
  | cons w ws ih =>
    match xs, Is with
    | [], [] => simp at hlen
    | [], _ :: _ => simp at hxlen
    | _ :: _, [] => simp at hlen
    | x :: xs', I :: Is' =>
      simp only [realDotProduct, dotProduct]
      apply IntervalDyadic.mem_add
      · apply mem_scalarMulInterval _ _ hprec
        exact hmem 0 (by simp)
      · have hlen' : ws.length = Is'.length := by simp at hlen; exact hlen
        have hxlen' : xs'.length = Is'.length := by simp at hxlen; exact hxlen
        have hmem' : ∀ i, (hi : i < Is'.length) → xs'[i] ∈ Is'[i] := by
          intro i hi
          have h := hmem (i + 1) (by simp; omega)
          simp only [List.getElem_cons_succ] at h
          exact h
        exact ih xs' Is' hlen' hxlen' hmem'

/-- Soundness of dot product: if each x_i ∈ I_i, then ∑ w_i * x_i ∈ dotProduct -/
theorem mem_dotProduct {weights : List ℚ} {xs : List ℝ} {Is : IntervalVector}
    (hlen : weights.length = Is.length)
    (hxlen : xs.length = Is.length)
    (hmem : ∀ i, (hi : i < Is.length) → xs[i]'(by omega) ∈ Is[i]'hi)
    (prec : Int) (hprec : prec ≤ 0 := by norm_num) :
    realDotProduct weights xs ∈ dotProduct weights Is prec :=
  mem_dotProduct_aux weights xs Is hlen hxlen hmem prec hprec

/-- Pointwise addition of two interval vectors -/
def add (Is Js : IntervalVector) : IntervalVector :=
  List.zipWith IntervalDyadic.add Is Js

/-- Soundness of vector addition (component-wise) -/
theorem mem_add_component {x y : ℝ} {I J : IntervalDyadic}
    (hx : x ∈ I) (hy : y ∈ J) : x + y ∈ IntervalDyadic.add I J :=
  IntervalDyadic.mem_add hx hy

/-- Zero interval (singleton at 0) -/
def zero : IntervalDyadic := IntervalDyadic.singleton (Dyadic.ofInt 0)

/-- Membership in zero interval -/
theorem mem_zero : (0 : ℝ) ∈ zero := mem_zero_singleton

/-- ReLU applied to an interval: max(0, x) for all x in the interval.
    Returns [max(0, lo), max(0, hi)] -/
def relu (I : IntervalDyadic) : IntervalDyadic where
  lo := Dyadic.max (Dyadic.ofInt 0) I.lo
  hi := Dyadic.max (Dyadic.ofInt 0) I.hi
  le := by
    simp only [Dyadic.max_toRat, Dyadic.toRat_ofInt, Int.cast_zero]
    exact max_le_max (le_refl (0 : ℚ)) I.le

/-- Soundness of ReLU: if x ∈ I, then max(0, x) ∈ relu I -/
theorem mem_relu {x : ℝ} {I : IntervalDyadic} (hx : x ∈ I) :
    max 0 x ∈ relu I := by
  simp only [IntervalDyadic.mem_def, relu] at *
  simp only [Dyadic.max_toRat, Dyadic.toRat_ofInt, Int.cast_zero]
  constructor
  · -- Lower bound: (max 0 lo : ℚ) ≤ max 0 x
    -- We have lo ≤ x (as reals), need max(0,lo) ≤ max(0,x)
    have hlo := hx.1  -- (I.lo.toRat : ℝ) ≤ x
    -- max is monotone in both arguments
    calc (↑(max (0 : ℚ) I.lo.toRat) : ℝ)
        = max (0 : ℝ) (I.lo.toRat : ℝ) := by simp [Rat.cast_max]
      _ ≤ max 0 x := max_le_max (le_refl 0) hlo
  · -- Upper bound: max 0 x ≤ (max 0 hi : ℚ)
    have hhi := hx.2  -- x ≤ (I.hi.toRat : ℝ)
    calc max 0 x
        ≤ max (0 : ℝ) (I.hi.toRat : ℝ) := max_le_max (le_refl 0) hhi
      _ = (↑(max (0 : ℚ) I.hi.toRat) : ℝ) := by simp [Rat.cast_max]

/-- Apply ReLU to each component of an interval vector -/
def reluVector (Is : IntervalVector) : IntervalVector :=
  Is.map relu

/-- Soundness of vector ReLU -/
theorem mem_reluVector_component {x : ℝ} {I : IntervalDyadic} (hx : x ∈ I) :
    max 0 x ∈ relu I := mem_relu hx

/-! ### Sigmoid Activation -/

/-- Sigmoid interval: conservative bound [0, 1].
    Since sigmoid(x) = 1/(1 + exp(-x)) ∈ (0, 1) for all x,
    [0, 1] is a sound overapproximation for any input interval. -/
def sigmoid (_I : IntervalDyadic) : IntervalDyadic where
  lo := Dyadic.ofInt 0
  hi := Dyadic.ofInt 1
  le := by rw [Dyadic.toRat_ofInt, Dyadic.toRat_ofInt]; norm_num

/-- Real sigmoid function -/
noncomputable def Real.sigmoid (x : ℝ) : ℝ := 1 / (1 + Real.exp (-x))

/-- Sigmoid is bounded in (0, 1) -/
theorem Real.sigmoid_pos (x : ℝ) : 0 < Real.sigmoid x := by
  unfold Real.sigmoid
  apply div_pos one_pos
  linarith [Real.exp_pos (-x)]

theorem Real.sigmoid_lt_one (x : ℝ) : Real.sigmoid x < 1 := by
  unfold Real.sigmoid
  rw [div_lt_one (by linarith [Real.exp_pos (-x)] : 0 < 1 + Real.exp (-x))]
  linarith [Real.exp_pos (-x)]

/-- Soundness of sigmoid: sigmoid(x) ∈ [0, 1] for all x -/
theorem mem_sigmoid {x : ℝ} {I : IntervalDyadic} (_hx : x ∈ I) :
    Real.sigmoid x ∈ sigmoid I := by
  simp only [IntervalDyadic.mem_def, sigmoid]
  simp only [Dyadic.toRat_ofInt, Int.cast_zero, Int.cast_one, Rat.cast_zero, Rat.cast_one]
  exact ⟨le_of_lt (Real.sigmoid_pos x), le_of_lt (Real.sigmoid_lt_one x)⟩

/-- Apply sigmoid to each component of an interval vector -/
def sigmoidVector (Is : IntervalVector) : IntervalVector :=
  Is.map sigmoid

/-! ### Matrix-Vector Operations -/

/-- Matrix-vector multiplication: W · x where W is a matrix of rational weights
    and x is an interval vector. Each row of W is dotted with x. -/
def matVecMul (W : List (List ℚ)) (x : IntervalVector) (prec : Int := -53) : IntervalVector :=
  W.map (fun row => dotProduct row x prec)

/-- Real matrix-vector multiplication -/
def realMatVecMul (W : List (List ℚ)) (x : List ℝ) : List ℝ :=
  W.map (fun row => realDotProduct row x)

/-- Soundness of matrix-vector multiplication -/
theorem mem_matVecMul {W : List (List ℚ)} {xs : List ℝ} {Is : IntervalVector}
    (hWcols : ∀ row ∈ W, row.length = Is.length)
    (hxlen : xs.length = Is.length)
    (hmem : ∀ i, (hi : i < Is.length) → xs[i]'(by omega) ∈ Is[i]'hi)
    (prec : Int) (hprec : prec ≤ 0 := by norm_num) :
    ∀ i, (hi : i < W.length) →
      (realMatVecMul W xs)[i]'(by simp [realMatVecMul]; exact hi) ∈
      (matVecMul W Is prec)[i]'(by simp [matVecMul]; exact hi) := by
  intro i hi
  simp only [realMatVecMul, matVecMul, List.getElem_map]
  exact mem_dotProduct (hWcols (W[i]) (List.getElem_mem hi)) hxlen hmem prec hprec

/-- Add a rational bias vector to an interval vector -/
def addBias (Is : IntervalVector) (bias : List ℚ) (prec : Int := -53) : IntervalVector :=
  List.zipWith (fun I b =>
    IntervalDyadic.add I (IntervalDyadic.ofIntervalRat (IntervalRat.singleton b) prec)
  ) Is bias

/-- Real vector plus bias -/
def realAddBias (xs : List ℝ) (bias : List ℚ) : List ℝ :=
  List.zipWith (fun x (b : ℚ) => x + (b : ℝ)) xs bias

/-- Soundness of bias addition -/
theorem mem_addBias {xs : List ℝ} {Is : IntervalVector} {bias : List ℚ}
    (hlen : xs.length = Is.length)
    (hblen : bias.length = Is.length)
    (hmem : ∀ i, (hi : i < Is.length) → xs[i]'(by omega) ∈ Is[i]'hi)
    (prec : Int) (hprec : prec ≤ 0 := by norm_num) :
    ∀ i, (hi : i < Is.length) →
      (realAddBias xs bias)[i]'(by simp [realAddBias, List.length_zipWith]; omega) ∈
      (addBias Is bias prec)[i]'(by simp [addBias, List.length_zipWith]; omega) := by
  intro i hi
  have hib : i < bias.length := by omega
  have hxi : i < xs.length := by omega
  simp only [realAddBias, addBias, List.getElem_zipWith]
  apply IntervalDyadic.mem_add
  · exact hmem i hi
  · exact IntervalDyadic.mem_ofIntervalRat (IntervalRat.mem_singleton (bias[i])) prec hprec

end IntervalVector

end LeanBound.ML
