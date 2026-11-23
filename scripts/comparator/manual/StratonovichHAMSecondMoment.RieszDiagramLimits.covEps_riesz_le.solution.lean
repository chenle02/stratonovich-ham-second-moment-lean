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
/-- Domination in d = 1: for c >= 0, 0 <= alpha < 1, eps > 0 and x != 0 in R^1, (p_eps * Gamma)(x) <= C_alpha c|x|^(-alpha) for Gamma = c|y|^(-alpha) dy, C_alpha = 2 + 16/(1-alpha), uniformly in eps (route of decision 3). -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.RieszDiagramLimits.covEps_riesz_le {c α ε : ℝ} (hc : 0 ≤ c) (hα0 : 0 ≤ α) (hα : α < 1) (hε : 0 < ε)
    {x : Rd 1} (hx : x ≠ 0) :
    covEps ((volume : Measure (Rd 1)).withDensity (riesz c α)) ε x ≤
      ENNReal.ofReal (CA α) * riesz c α x := by
  apply _root_.StratonovichHAMSecondMoment.RieszDiagramLimits.covEps_riesz_le <;> assumption
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.RieszDiagramLimits
