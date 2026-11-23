-- Printed type replaced by the source's statement in its scope (the printed one elaborates another instance path or universe order, so CheckFidelity's Expr equality fails).
namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SourceVertexCrude
set_option autoImplicit false
open MeasureTheory Set Filter Topology
open scoped ENNReal Real Nat
open HomogHypothesis (Rd HomogCovariance)
open WaveGreen (waveGreen)
open DiagramModel (Pi2 rev)
open TerminalWick (Pt prodL2)
open PairingInterface
open PairingBridge (smoothEdge)
open WickInterface
open SourceInterface
open HomogeneousEnvelope (Khom Khom_pos one_le_Khom)
universe u
variable {d : ℕ}
/-- For f in L2(P) on any measurable space: ||f||^2 = integral of f * f dP. Auxiliary to the Lean proof route. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.SourceVertexCrude.norm_sq_eq_integral {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} (f : Lp ℝ 2 P) :
    ‖f‖ ^ 2 = ∫ ω, (f : Ω → ℝ) ω * (f : Ω → ℝ) ω ∂P := by
  sorry
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SourceVertexCrude
