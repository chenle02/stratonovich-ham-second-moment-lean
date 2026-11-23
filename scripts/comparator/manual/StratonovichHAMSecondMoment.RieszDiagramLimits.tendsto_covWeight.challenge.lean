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
/-- For c >= 0, 0 <= alpha < 1, D and y off the pair diagonals: covWeight (p_eps * Gamma) D y -> covWeight (c|.|^(-alpha)) D y as eps -> 0+, Gamma = c|y|^(-alpha) dy. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.RieszDiagramLimits.tendsto_covWeight {c α : ℝ} (hc : 0 ≤ c) (hα0 : 0 ≤ α) (hα : α < 1)
    {N : ℕ} (D : Fin N → Fin N) (y : Fin N → Rd 1) (hy : ∀ i ∈ openers D, y i ≠ y (D i)) :
    Tendsto (fun ε => covWeight (covEps ((volume : Measure (Rd 1)).withDensity (riesz c α)) ε) D y)
      (𝓝[>] 0) (𝓝 (covWeight (riesz c α) D y)) := by
  sorry
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.RieszDiagramLimits
