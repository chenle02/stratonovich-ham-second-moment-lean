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
/-- For c >= 0, 0 <= alpha < 1, eps > 0, every m, D, h: the M4 spatial part (waveGreen 1) with covariance p_eps * Gamma is <= C_alpha^(#openers D) times the spatial part with the density c|.|^(-alpha), uniformly in eps. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.RieszDiagramLimits.spatial_covEps_le {c α ε : ℝ} (hc : 0 ≤ c) (hα0 : 0 ≤ α) (hα : α < 1) (hε : 0 < ε)
    (m : ℕ) {N : ℕ} (D : Fin N → Fin N) (h : Fin N → ℝ) :
    spatial (waveGreen 1) (covEps ((volume : Measure (Rd 1)).withDensity (riesz c α)) ε) m D h ≤
      ENNReal.ofReal (CA α) ^ (openers D).card * spatial (waveGreen 1) (riesz c α) m D h := by
  sorry
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.RieszDiagramLimits
