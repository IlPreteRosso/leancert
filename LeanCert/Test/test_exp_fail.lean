import LeanCert

-- e ≈ 2.7182818284590452...
-- This should FAIL (bound is below e)
example : ∀ x ∈ Set.Icc 0 1, Real.exp x ≤ 2.718281828 := by
  interval_bound
