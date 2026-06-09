/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Examples.Li2Verified

/-!
# Li(2) Bounds

Public interface for the Ramanujan-Soldner constant bounds. This module preserves
the historical `Li2.li2_lower` and `Li2.li2_upper` names, but those names now
refer directly to the verified numerical certificates in `Li2Verified`.
-/

open MeasureTheory LeanCert.Engine.TaylorModel
open scoped ENNReal

namespace Li2

/-- Certified lower bound: li(2) ≥ 1.039. -/
theorem li2_lower : (1039:ℚ)/1000 ≤ li2 :=
  Li2Verified.li2_lower_verified

/-- Certified upper bound: li(2) ≤ 1.06. -/
theorem li2_upper : li2 ≤ (106:ℚ)/100 :=
  Li2Verified.li2_upper_verified

/-- Combined bounds: li(2) ∈ [1.039, 1.06]. -/
theorem li2_bounds : (1039:ℚ)/1000 ≤ li2 ∧ li2 ≤ (106:ℚ)/100 :=
  ⟨li2_lower, li2_upper⟩

/-- li(2) is approximately 1.045 (the Ramanujan-Soldner constant).
    Our bounds show: |li(2) - 1.045| ≤ 0.015. -/
theorem li2_approx_1045 : |li2 - (1045:ℚ)/1000| ≤ (15:ℚ)/1000 := by
  have ⟨hlo, hhi⟩ := li2_bounds
  rw [abs_le]
  constructor
  · linarith
  · linarith

end Li2

