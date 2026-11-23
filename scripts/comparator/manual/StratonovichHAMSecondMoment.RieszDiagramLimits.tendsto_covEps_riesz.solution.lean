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
/-- Pointwise convergence in d = 1: for c >= 0, 0 <= alpha < 1 and x != 0 in R^1, (p_eps * Gamma)(x) -> c|x|^(-alpha) as eps -> 0+, Gamma = c|y|^(-alpha) dy. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.RieszDiagramLimits.tendsto_covEps_riesz {c α : ℝ} (hc : 0 ≤ c) (hα0 : 0 ≤ α) (hα : α < 1) {x : Rd 1}
    (hx : x ≠ 0) :
    Tendsto (fun ε => covEps ((volume : Measure (Rd 1)).withDensity (riesz c α)) ε x)
      (𝓝[>] 0) (𝓝 (riesz c α x)) := by
  apply _root_.StratonovichHAMSecondMoment.RieszDiagramLimits.tendsto_covEps_riesz <;> assumption
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.RieszDiagramLimits
