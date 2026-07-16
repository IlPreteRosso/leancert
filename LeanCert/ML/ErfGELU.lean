/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.ML.IntervalVector
import LeanCert.Engine.Eval.Core

/-!
# Exact erf-GELU Feed-Forward Blocks

PyTorch `nn.GELU()` defaults to the exact erf form

`gelu(x) = 0.5 * x * (1 + erf(x / sqrt 2))`.

This module provides a computable interval forward pass for the architecture
`Linear -> erf-GELU -> Linear`, using LeanCert's verified `erfInterval`
primitive. It intentionally lives beside the transformer tanh-GELU
approximation instead of replacing it.
-/

namespace LeanCert.ML

open LeanCert.Core
open LeanCert.Engine

/-- Real specification of PyTorch's default exact GELU. -/
noncomputable def Real.erfGELU (x : ℝ) : ℝ :=
  (1 / 2 : ℝ) * x * (1 + Real.erf (x / Real.sqrt 2))

/-- A rational interval enclosing `1 / sqrt 2`. -/
def erfGELUInvSqrt2 : IntervalRat :=
  ⟨7071067811865475 / 10000000000000000,
    7071067811865476 / 10000000000000000,
    by norm_num⟩

/-- Computable interval enclosure for exact erf-GELU over rational intervals. -/
def erfGELUIntervalRat (I : IntervalRat) (taylorDepth : Nat := 15) : IntervalRat :=
  let arg := IntervalRat.mul I erfGELUInvSqrt2
  let poly :=
    IntervalRat.evalTaylorSeries (IntervalRat.erfTaylorCoeffs taylorDepth) arg
  let scaled := IntervalRat.mul IntervalRat.two_div_sqrt_pi poly
  let rem := IntervalRat.erfRemainderBoundComputable arg taylorDepth
  let rawErf := IntervalRat.add scaled rem
  let globalBound : IntervalRat := ⟨-1, 1, by norm_num⟩
  let erfArg :=
    match IntervalRat.intersect rawErf globalBound with
    | some refined => refined
    | none => globalBound
  let onePlus := IntervalRat.add (IntervalRat.singleton 1) erfArg
  let halfX := IntervalRat.scale (1 / 2) I
  IntervalRat.mul halfX onePlus

/-- Computable interval enclosure for exact erf-GELU over dyadic intervals. -/
def erfGELUInterval (I : IntervalDyadic) (prec : Int := -53)
    (taylorDepth : Nat := 15) : IntervalDyadic :=
  IntervalDyadic.ofIntervalRat (erfGELUIntervalRat I.toIntervalRat taylorDepth) prec

/-- Vectorized exact erf-GELU interval transform. -/
def erfGELUVector (v : IntervalVector) (prec : Int := -53)
    (taylorDepth : Nat := 15) : IntervalVector :=
  v.map (fun I => erfGELUInterval I prec taylorDepth)

/-- Pure affine layer: no baked-in activation. -/
structure AffineLayer where
  weights : List (List ℚ)
  bias : List ℚ
  deriving Repr

namespace AffineLayer

/-- Real affine forward pass. -/
noncomputable def forwardReal (l : AffineLayer) (x : List ℝ) : List ℝ :=
  LeanCert.Engine.IntervalVector.realAddBias
    (LeanCert.Engine.IntervalVector.realMatVecMul l.weights x)
    l.bias

/-- Interval affine forward pass. -/
def forwardInterval (l : AffineLayer) (x : IntervalVector)
    (prec : Int := -53) : IntervalVector :=
  LeanCert.Engine.IntervalVector.addBias
    (LeanCert.Engine.IntervalVector.matVecMul l.weights x prec)
    l.bias
    prec

end AffineLayer

/-- A depth-2 MLP cell: `Linear -> exact erf-GELU -> Linear`. -/
structure ErfGELUFFN where
  linear1 : AffineLayer
  linear2 : AffineLayer
  dims_match : True := by trivial
  deriving Repr

namespace ErfGELUFFN

/-- Real forward pass for the exact erf-GELU cell. -/
noncomputable def forwardReal (net : ErfGELUFFN) (x : List ℝ) : List ℝ :=
  let hidden := net.linear1.forwardReal x
  let activated := hidden.map Real.erfGELU
  net.linear2.forwardReal activated

/-- Interval forward pass for the exact erf-GELU cell. -/
def forwardInterval (net : ErfGELUFFN) (x : IntervalVector)
    (prec : Int := -53) (taylorDepth : Nat := 15) : IntervalVector :=
  let hidden := net.linear1.forwardInterval x prec
  let activated := erfGELUVector hidden prec taylorDepth
  net.linear2.forwardInterval activated prec

end ErfGELUFFN

end LeanCert.ML
