/-
Copyright (c) 2024 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Tactic.VecSimp
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

/-!
# Tests for vec_simp tactic

These tests verify that `vec_simp` correctly reduces vector indexing
with explicit `Fin.mk` constructors.
-/

namespace VecSimp.Test

-- Basic tests: access with explicit Fin.mk
example : (![1, 2, 3] : Fin 3 → ℕ) ⟨0, by omega⟩ = 1 := by vec_simp
example : (![1, 2, 3] : Fin 3 → ℕ) ⟨1, by omega⟩ = 2 := by vec_simp
example : (![1, 2, 3] : Fin 3 → ℕ) ⟨2, by omega⟩ = 3 := by vec_simp

-- Tests with symbolic elements
example (a b c : ℝ) : (![a, b, c] : Fin 3 → ℝ) ⟨0, by omega⟩ = a := by vec_simp
example (a b c : ℝ) : (![a, b, c] : Fin 3 → ℝ) ⟨1, by omega⟩ = b := by vec_simp
example (a b c : ℝ) : (![a, b, c] : Fin 3 → ℝ) ⟨2, by omega⟩ = c := by vec_simp

-- Tests with longer vectors
example : (![1, 2, 3, 4, 5] : Fin 5 → ℕ) ⟨3, by omega⟩ = 4 := by vec_simp
example : (![1, 2, 3, 4, 5] : Fin 5 → ℕ) ⟨4, by omega⟩ = 5 := by vec_simp

-- Test with Fin 2
example (x y : ℕ) : (![x, y] : Fin 2 → ℕ) ⟨0, by omega⟩ = x := by vec_simp
example (x y : ℕ) : (![x, y] : Fin 2 → ℕ) ⟨1, by omega⟩ = y := by vec_simp

-- Test in expressions
example (a b c : ℝ) : (![a, b, c] : Fin 3 → ℝ) ⟨0, by omega⟩ + 1 = a + 1 := by vec_simp

/-! ### RadiiPolynomial-style tests

These tests mimic the actual use case in Example_7_7_LeanCert_Clean.lean where:
- Named constants are used (ā₀, ā₁, ā₂)
- Expressions involve products and sums
- vec_simp is followed by ring or other tactics
-/

section RadiiPolynomialStyle

-- Mimic the named constant pattern
variable (ā₀ ā₁ ā₂ : ℝ)

-- Test: index 0 (the problematic case in their code)
example : (![ā₀, ā₁, ā₂] : Fin 3 → ℝ) ⟨0, by omega⟩ = ā₀ := by vec_simp

-- Test: all indices with named constants
example : (![ā₀, ā₁, ā₂] : Fin 3 → ℝ) ⟨1, by omega⟩ = ā₁ := by vec_simp
example : (![ā₀, ā₁, ā₂] : Fin 3 → ℝ) ⟨2, by omega⟩ = ā₂ := by vec_simp

-- Test: product expressions (like in CauchyProduct convolution)
example : (![ā₀, ā₁, ā₂] : Fin 3 → ℝ) ⟨0, by omega⟩ * (![ā₀, ā₁, ā₂] : Fin 3 → ℝ) ⟨0, by omega⟩ = ā₀ * ā₀ := by
  vec_simp

-- Test: mixed indices in expression
example : (![ā₀, ā₁, ā₂] : Fin 3 → ℝ) ⟨0, by omega⟩ * (![ā₀, ā₁, ā₂] : Fin 3 → ℝ) ⟨1, by omega⟩ +
          (![ā₀, ā₁, ā₂] : Fin 3 → ℝ) ⟨1, by omega⟩ * (![ā₀, ā₁, ā₂] : Fin 3 → ℝ) ⟨0, by omega⟩ = 2 * ā₀ * ā₁ := by
  vec_simp
  ring

-- Test: pattern from F_fin_0_eq proof (squared term)
example (lam0 : ℝ) :
    (![ā₀, ā₁, ā₂] : Fin 3 → ℝ) ⟨0, by omega⟩ * (![ā₀, ā₁, ā₂] : Fin 3 → ℝ) ⟨0, by omega⟩ - lam0 = ā₀^2 - lam0 := by
  vec_simp
  ring

-- Test: pattern from F_fin_1_eq proof (2*a*b - 1)
example :
    (![ā₀, ā₁, ā₂] : Fin 3 → ℝ) ⟨0, by omega⟩ * (![ā₀, ā₁, ā₂] : Fin 3 → ℝ) ⟨1, by omega⟩ +
    (![ā₀, ā₁, ā₂] : Fin 3 → ℝ) ⟨1, by omega⟩ * (![ā₀, ā₁, ā₂] : Fin 3 → ℝ) ⟨0, by omega⟩ - 1 = 2 * ā₀ * ā₁ - 1 := by
  vec_simp
  ring

end RadiiPolynomialStyle

end VecSimp.Test
