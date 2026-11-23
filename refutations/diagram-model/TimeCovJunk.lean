/-
Supplementary control (class (c)); NOT a refutation of a manuscript claim and not
counted among this item's refutations.  The in-domain refutation of the temporal
kernel `|s_j - s_h|^{-α₀}` is `TimeKernelExponent.lean`.

Control of Lean's totalized arithmetic for the temporal covariance of
`DiagramModel` (`|s_j - s_h|^{-α₀}` in `E:mixed-diagram`, main TeX line 822 at
edf7085f), package definition `StratonovichHAMSecondMoment.DiagramModel.timeCov`
and theorem `timeCov_self`.

Wrong variant: the temporal covariance at equal times is `0` (Lean's real
power `0^{-α₀} = 0`, `Real.zero_rpow`), as a real-valued encoding would give.
Counterexample: `α₀ = 1/2`, `a = b = 0`: the package value is `∞`
(`(0 : ℝ≥0∞)^{-1/2} = ∞`), the analytic value of `|0|^{-α₀}`; the real power is
`0`.  The diagonal is Lebesgue-null in every diagram, so the diagram values do
not depend on this choice; the control pins that `timeCov` is not the junk
value.  `timeCovJunk_contrast` records both values.
Class (c): control of Lean's totalized arithmetic outside the manuscript's
pointwise domain (the TeX never evaluates the kernel at equal times); the
change it tests leaves every diagram integral unchanged.

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.DiagramModel

set_option autoImplicit false

open StratonovichHAMSecondMoment DiagramModel
open scoped ENNReal

namespace Refutations.DiagramModel

/-- The package value is `∞`, the real-power junk value is `0`. -/
theorem timeCovJunk_contrast :
    timeCov (1 / 2) 0 0 = ⊤ ∧ (|(0 : ℝ) - 0|) ^ (-(1 / 2 : ℝ)) = 0 := by
  refine ⟨timeCov_self (by norm_num) 0, ?_⟩
  simp

/-- The temporal covariance at equal times is not `0`. -/
theorem timeCovJunk_refuted : ¬ (timeCov (1 / 2) 0 0 = 0) := by
  rw [timeCovJunk_contrast.1]; exact ENNReal.top_ne_zero

end Refutations.DiagramModel
