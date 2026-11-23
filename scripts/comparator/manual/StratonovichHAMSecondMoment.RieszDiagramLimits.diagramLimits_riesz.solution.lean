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
/-- The former named input D1Upper.DiagramLimits proved in the Riesz case: for c >= 0, 0 <= alpha < 1, 0 <= alpha0 < 1, t >= 0, DiagramLimits 1 (c|y|^(-alpha) dy) alpha0 t, nothing supplied (domination route, decision 3). -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.RieszDiagramLimits.diagramLimits_riesz {c α α₀ t : ℝ} (hc : 0 ≤ c) (hα0 : 0 ≤ α) (hα : α < 1)
    (h0 : 0 ≤ α₀) (h1 : α₀ < 1) (ht : 0 ≤ t) :
    D1Upper.DiagramLimits 1 ((volume : Measure (Rd 1)).withDensity (riesz c α)) α₀ t := by
  apply _root_.StratonovichHAMSecondMoment.RieszDiagramLimits.diagramLimits_riesz <;> assumption
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.RieszDiagramLimits
