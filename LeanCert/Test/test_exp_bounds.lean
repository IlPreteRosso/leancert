import LeanCert

-- e ≈ 2.718281828...

-- This should work (from earlier)
example : ∀ x ∈ Set.Icc 0 1, Real.exp x ≤ 2.718282 := by
  interval_bound

-- Tighter bound
example : ∀ x ∈ Set.Icc 0 1, Real.exp x ≤ 2.7182819 := by
  interval_bound

-- Even tighter
example : ∀ x ∈ Set.Icc 0 1, Real.exp x ≤ 2.71828183 := by
  interval_bound

-- Very tight (e ≈ 2.718281828...)
example : ∀ x ∈ Set.Icc 0 1, Real.exp x ≤ 2.718281829 := by
  interval_bound
