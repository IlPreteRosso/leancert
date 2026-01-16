/-
Test file for log support in LeanCert.
-/
import LeanCert.Tactic.IntervalAuto

namespace TestLog

open LeanCert.Core

-- Test atanh Taylor coefficients
#eval
  let coeffs := IntervalRat.atanhTaylorCoeffs 10
  dbg_trace "atanhTaylorCoeffs(10): {coeffs}"
  -- Debug: manually compute what we expect
  let range := List.range 11
  dbg_trace "range: {range}"
  dbg_trace "1 % 2: {1 % 2}"
  dbg_trace "3 % 2: {3 % 2}"
  dbg_trace "1 / (1 : ℚ): {1 / (1 : ℚ)}"
  dbg_trace "1 / (3 : ℚ): {1 / (3 : ℚ)}"
  -- Test condition
  let test1 := if (1 : Nat) % 2 = 1 then (1 : ℚ) / 1 else 0
  let test3 := if (3 : Nat) % 2 = 1 then (1 : ℚ) / 3 else 0
  dbg_trace "test1: {test1}"
  dbg_trace "test3: {test3}"
  pure ()

-- Test atanh at 1/3
#eval
  let result := IntervalRat.atanhPointComputable (1/3) 15
  dbg_trace "atanh(1/3): [{result.lo}, {result.hi}]"
  dbg_trace "Expected: ~0.3466"
  pure ()

-- Compute ln(2) = 2 * atanh(1/3)
#eval
  let result := IntervalRat.ln2Computable 20
  dbg_trace "ln(2) computed: [{result.lo}, {result.hi}]"
  dbg_trace "Expected: ~0.693"
  pure ()

-- Test logReduceMantissa and logReductionExponent
#eval
  let k := IntervalRat.logReductionExponent 10
  let m := IntervalRat.logReduceMantissa 10
  dbg_trace "For q=10: k={k}, m={m}"
  dbg_trace "Verify: m * 2^k = {m * (2 : ℚ) ^ k}"
  pure ()

#eval
  let k := IntervalRat.logReductionExponent 2
  let m := IntervalRat.logReduceMantissa 2
  dbg_trace "For q=2: k={k}, m={m}"
  dbg_trace "Verify: m * 2^k = {m * (2 : ℚ) ^ k}"
  pure ()

#eval
  let k := IntervalRat.logReductionExponent 1
  let m := IntervalRat.logReduceMantissa 1
  dbg_trace "For q=1: k={k}, m={m}"
  dbg_trace "Verify: m * 2^k = {m * (2 : ℚ) ^ k}"
  pure ()

-- Test log at various points
#eval
  let result := IntervalRat.logPointComputable 1 20
  dbg_trace "log(1): [{result.lo}, {result.hi}]"
  dbg_trace "Expected: 0"
  pure ()

#eval
  let result := IntervalRat.logPointComputable 2 20
  dbg_trace "log(2): [{result.lo}, {result.hi}]"
  dbg_trace "Expected: ~0.693"
  pure ()

-- Test interval_bound tactic with log
-- Log is monotone, so testing on intervals containing a single point

-- log(2) ≤ 1 on [2, 2]
example : ∀ x ∈ Set.Icc (2 : ℝ) 2, Real.log x ≤ 1 := by interval_bound

-- 0.693 ≤ log(2) on [2, 2]
example : ∀ x ∈ Set.Icc (2 : ℝ) 2, (0.693 : ℝ) ≤ Real.log x := by interval_bound

-- log(2) ≤ 0.694 on [2, 2]
example : ∀ x ∈ Set.Icc (2 : ℝ) 2, Real.log x ≤ 0.694 := by interval_bound

-- Log on [1, 3] is bounded
example : ∀ x ∈ Set.Icc (1 : ℝ) 3, Real.log x ≤ 2 := by interval_bound

-- log(x) ≥ -1 on [1, 3]  (true because log(1) = 0)
example : ∀ x ∈ Set.Icc (1 : ℝ) 3, (-1 : ℝ) ≤ Real.log x := by interval_bound

-- Test with expression involving log
-- log(1 + x) ≤ x for x ≥ 0 (Taylor-like bound)
example : ∀ x ∈ Set.Icc (0 : ℝ) 1, Real.log (1 + x) ≤ x := by interval_bound

end TestLog
