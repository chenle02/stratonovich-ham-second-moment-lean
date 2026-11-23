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
/-- For c >= 0, 0 <= alpha < 1, 0 <= alpha0 < 1, t >= 0, D in Pi2 m n (every order, so order four): the measure-form limit diagramLim 1 (c|y|^(-alpha) dy) alpha0 m n D t equals the density diagram (main TeX lines 5125-5172). -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.RieszDiagramLimits.diagramLim_riesz_eq {c α α₀ t : ℝ} (hc : 0 ≤ c) (hα0 : 0 ≤ α) (hα : α < 1)
    (h0 : 0 ≤ α₀) (h1 : α₀ < 1) (ht : 0 ≤ t) {m n : ℕ} {D : Fin (m + n) → Fin (m + n)}
    (hD : D ∈ Pi2 m n) :
    diagramLim 1 ((volume : Measure (Rd 1)).withDensity (riesz c α)) α₀ m n D t =
      diagram (waveGreen 1) (riesz c α) α₀ m n D t := by
  sorry
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.RieszDiagramLimits
