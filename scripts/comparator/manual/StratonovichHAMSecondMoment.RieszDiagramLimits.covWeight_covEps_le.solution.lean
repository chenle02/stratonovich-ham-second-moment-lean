-- Printed type replaced by the source's statement in its scope (the printed one elaborates another instance path for the measurable space of `Rd 1`, so CheckFidelity's Expr equality fails).
namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.RieszDiagramLimits
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal Nat
open HomogHypothesis (Rd)
open WaveGreen (waveGreen)
open HigherRieszTwo (riesz)
open DiagramModel
open TwoSimplexTime (Zc)
open D1Spatial (Ksp)
/-- For c >= 0, 0 <= alpha < 1, eps > 0, D and y with y_i != y_(D i) for every opener i: covWeight (p_eps * Gamma) D y <= C_alpha^(#openers D) covWeight (c|.|^(-alpha)) D y, Gamma = c|y|^(-alpha) dy. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.RieszDiagramLimits.covWeight_covEps_le {c α ε : ℝ} (hc : 0 ≤ c) (hα0 : 0 ≤ α) (hα : α < 1) (hε : 0 < ε)
    {N : ℕ} (D : Fin N → Fin N) (y : Fin N → Rd 1) (hy : ∀ i ∈ openers D, y i ≠ y (D i)) :
    covWeight (covEps ((volume : Measure (Rd 1)).withDensity (riesz c α)) ε) D y ≤
      ENNReal.ofReal (CA α) ^ (openers D).card * covWeight (riesz c α) D y := by
  apply _root_.StratonovichHAMSecondMoment.RieszDiagramLimits.covWeight_covEps_le <;> assumption
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.RieszDiagramLimits
