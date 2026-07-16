/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert

/-!
# Public evaluation API smoke tests

This file intentionally imports only the umbrella module. It guards the
authoritative checked façade, backend selection, structured failures, and the
backend-independent golden theorem.
-/

namespace LeanCert.Test.PublicEvalAPI

open LeanCert
open LeanCert.Core

def unitInterval : IntervalRat := ⟨0, 1, by norm_num⟩
def crossesZero : IntervalRat := ⟨-1, 1, by norm_num⟩
def identity : Expr := .var 0

def usedBackend (expected : ConcreteBackend)
    (result : EvalResult IntervalOutcome) : Bool :=
  match result with
  | .ok outcome => decide (outcome.backend = expected)
  | .error _ => false

def failed (result : EvalResult IntervalOutcome) : Bool :=
  match result with
  | .ok _ => false
  | .error _ => true

#guard usedBackend .dyadic (evalInterval identity [unitInterval])
#guard usedBackend .rational
  (evalInterval identity [unitInterval] { backend := .rational })
#guard usedBackend .dyadic
  (evalInterval identity [unitInterval] { backend := .dyadic })
#guard usedBackend .affine
  (evalInterval identity [unitInterval] { backend := .affine })

#guard failed (evalInterval (.log identity) [crossesZero])
#guard failed
  (evalInterval identity [unitInterval] { backend := .dyadic, dyadicPrecision := 1 })

example (e : Expr) (box : List IntervalRat) (options : EvalOptions)
    (outcome : IntervalOutcome)
    (hsuccess : evalInterval e box options = .ok outcome)
    (rho : Nat → ℝ)
    (hrho : ∀ i, rho i ∈ box.getD i (IntervalRat.singleton 0)) :
    Expr.eval rho e ∈ outcome.interval :=
  evalInterval_correct e box options outcome hsuccess rho hrho

end LeanCert.Test.PublicEvalAPI
