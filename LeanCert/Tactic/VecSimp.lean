/-
Copyright (c) 2024 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Tactic.VecUtil
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Tactic.NormNum

/-!
# vec_simp & dite_simp: Vector and dite simplification

## Tactics

* `vec_simp` - vector indexing: `![a,b,c] 2` → `c`, `![a,b,c] ⟨1, proof⟩` → `b`
* `vec_simp!` - + dite, abs, norm_num; use `vec_simp! [M]` for named matrices
* `dite_simp` - simplify `if h : 1 ≤ 2 then x else y` → `x`

## Why needed

Mathlib's `cons_val` uses `int?` which misses `Fin.mk` applications like `⟨0, by omega⟩`.
Uses `VecUtil.vecConsFinMk` which handles both via `Fin.val` reduction.

Shared utilities in `LeanCert.Tactic.VecUtil`. Debug: `set_option trace.VecUtil.debug true`
-/

/-- Simplify vector indexing: `![a,b,c] ⟨1, proof⟩` → `b`, `![a,b,c] 2` → `c`.
    See `vec_simp!` for dite/abs support. -/
macro "vec_simp" : tactic =>
  `(tactic| simp only [VecUtil.vecConsFinMk, Matrix.cons_val_zero, Matrix.cons_val_zero',
                       Matrix.cons_val_one, Matrix.head_cons])

/-- `vec_simp` + dite conditions + abs + norm_num. Use `vec_simp! [M]` for named matrices. -/
macro "vec_simp!" : tactic =>
  `(tactic| (
    -- Matrix.of_apply: unwraps !![...] notation: (Matrix.of f) i j → f i j
    try simp only [Matrix.of_apply]
    -- Nested indexing (![![...]] i j) is handled by simp's repeated application:
    --   ![![1,2],[3,4]] 0 → ![1,2], then ![1,2] 0 → 1
    try simp (config := { decide := true }) only [
      VecUtil.vecConsFinMk, Matrix.cons_val_zero, Matrix.cons_val_zero',
      Matrix.cons_val_one, Matrix.head_cons, dite_true, dite_false,
      abs_of_pos, abs_of_nonneg
    ]
    try norm_num
  ))

/-- Unfold definitions then `vec_simp!`. E.g., `vec_simp! [M]` for `def M := ![![...]]`. -/
macro "vec_simp!" "[" defs:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| (simp only [$defs,*]; vec_simp!))

/-- Simplify dite with decidable literal conditions: `if h : 1 ≤ 2 then x else y` → `x`.
    Uses `simp (config := { decide := true })`. Requires literal operands (not variables). -/
macro "dite_simp" : tactic =>
  `(tactic| simp (config := { decide := true }) only [dite_true, dite_false])
