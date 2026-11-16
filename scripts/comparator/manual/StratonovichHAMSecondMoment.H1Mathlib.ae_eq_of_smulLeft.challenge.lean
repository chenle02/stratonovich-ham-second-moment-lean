namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.H1Mathlib
-- Statement copied from the source (the printed type round-trips only up to definitional equality).
open MeasureTheory Filter Topology FourierTransform TemperedDistribution
open scoped ENNReal ContDiff SchwartzMap LineDeriv Real
open HomogHypothesis (Rd)
open WeakSobolev
open VariationalFloor (grad)
variable {d : ℕ}
/-- For U, V in L^2(R^d; C), h of temperate growth and c complex with c (h T_U) = T_V: V = c h U almost everywhere. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.H1Mathlib.ae_eq_of_smulLeft {U V : Lp ℂ 2 (volume : Measure (Rd d))} {h : Rd d → ℂ}
    (hh : h.HasTemperateGrowth) (c : ℂ)
    (hUV : c • smulLeftCLM ℂ h (U : 𝓢'(Rd d, ℂ)) = (V : 𝓢'(Rd d, ℂ))) :
    (V : Rd d → ℂ) =ᵐ[volume] fun x => c * h x * U x := by
  sorry
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.H1Mathlib
