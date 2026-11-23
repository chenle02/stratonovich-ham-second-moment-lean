-- Printed type replaced by the source's statement in its scope (CheckFidelity: the printed type's instance path differs from the claimed type's, e.g. Lp._proof_4 or the PiLp measurable space).
namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MildTerminalFubini
set_option autoImplicit false
open MeasureTheory Set Filter Topology
open scoped ENNReal Real Nat
universe u
open HomogHypothesis (Rd HomogCovariance)
open WaveGreen (waveGreen)
open FiniteWick (CenteredGaussianField)
open TerminalWick (Pt prodL2 chainWeightReal)
open TerminalWickInputs
open SourceInterface
open MildInterface
variable {d : ℕ}
/-- For any f : R x R^d -> E (no measurability assumed), t >= 0, x: f is mildMeasure d t ht x-integrable iff p -> (lastW t p.1).toReal . f(mildEquiv t x p) is Leb x G_1-integrable. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.MildTerminalFubini.integrable_mildMeasure_iff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (t : ℝ)
    (ht : 0 ≤ t) (x : Rd d) (f : ℝ × Rd d → E) :
    Integrable f (mildMeasure d t ht x) ↔
      Integrable (fun p => (lastW t p.1).toReal • f (mildEquiv t x p))
        ((volume : Measure ℝ).prod (waveGreen d 1)) := by
  sorry
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MildTerminalFubini
