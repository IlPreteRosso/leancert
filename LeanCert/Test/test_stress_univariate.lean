import LeanCert

open Set

-- Univariate stress tests for interval_bound.
example : ∀ x ∈ Icc (0 : ℝ) 1, Real.exp x ≤ 3 := by
  interval_bound

example : ∀ x ∈ Icc (-2 : ℝ) 2, Real.sin x + Real.cos x ≤ 2 := by
  interval_bound

example : ∀ x ∈ Icc (-1 : ℝ) 1, x ^ 4 + x ^ 2 ≤ (2 : ℚ) := by
  interval_bound

example : ∀ x ∈ Icc (0 : ℝ) 4, Real.sqrt x ≤ 2 := by
  interval_bound

example : ∀ x ∈ Icc (0 : ℝ) 2, Real.exp (Real.sin x) ≤ 3 := by
  interval_bound
