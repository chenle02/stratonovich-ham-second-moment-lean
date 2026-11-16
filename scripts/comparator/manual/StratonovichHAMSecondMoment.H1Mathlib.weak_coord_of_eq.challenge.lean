namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.H1Mathlib
-- Statement copied from the source (the printed type round-trips only up to definitional equality).
open MeasureTheory Filter Topology FourierTransform TemperedDistribution
open scoped ENNReal ContDiff SchwartzMap LineDeriv Real
open HomogHypothesis (Rd)
open WeakSobolev
open VariationalFloor (grad)
variable {d : ℕ}
/-- For real f in L^2, j, G in L^2(R^d; C) with d_(e_j) T_f = T_G, and a real test function phi: int f * fderiv phi x e_j = -int Re(G x) * phi x. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.H1Mathlib.weak_coord_of_eq {f : Rd d → ℝ} (hf : MemLp f 2 volume) (j : Fin d)
    (G : Lp ℂ 2 (volume : Measure (Rd d)))
    (hG : ∂_{eb d j} (toDistr hf) = (G : 𝓢'(Rd d, ℂ))) {φ : Rd d → ℝ}
    (hφ : IsTestFunction φ) :
    ∫ x, f x * fderiv ℝ φ x (eb d j) = -∫ x, (G x).re * φ x := by
  sorry
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.H1Mathlib
