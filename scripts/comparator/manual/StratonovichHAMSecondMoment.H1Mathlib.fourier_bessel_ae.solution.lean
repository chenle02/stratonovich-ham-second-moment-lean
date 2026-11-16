namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.H1Mathlib
-- Statement copied from the source (the printed type round-trips only up to definitional equality).
open MeasureTheory Filter Topology FourierTransform TemperedDistribution
open scoped ENNReal ContDiff SchwartzMap LineDeriv Real
open HomogHypothesis (Rd)
open WeakSobolev
open VariationalFloor (grad)
variable {d : ℕ}
/-- For real f in L^2 and W in L^2(R^d; C) with J^1 T_f = T_W: F W = <xi> F f almost everywhere. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.H1Mathlib.fourier_bessel_ae {f : Rd d → ℝ} (hf : MemLp f 2 volume)
    (W : Lp ℂ 2 (volume : Measure (Rd d)))
    (hW : besselPotential (Rd d) ℂ 1 (toDistr hf) = (W : 𝓢'(Rd d, ℂ))) :
    ((𝓕 W : Lp ℂ 2 volume) : Rd d → ℂ) =ᵐ[volume]
      fun x => 1 * besSym d 1 x * (𝓕 (toL2C hf) : Lp ℂ 2 volume) x := by
  bridge_revert_all
  exact @_root_.StratonovichHAMSecondMoment.H1Mathlib.fourier_bessel_ae
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.H1Mathlib
