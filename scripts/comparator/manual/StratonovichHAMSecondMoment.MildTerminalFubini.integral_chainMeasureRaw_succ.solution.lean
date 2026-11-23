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
/-- Bochner form, E complete: for strongly measurable F integrable against g_(n+1)^(T,x), p -> (lastW T s).toReal . int F(snoc z (s, x-(T-s)v)) dg_n^(s,x-(T-s)v) (p = (s,v)) is Leb x G_1-integrable and its integral is int F dg_(n+1)^(T,x). -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.MildTerminalFubini.integral_chainMeasureRaw_succ {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (n : ℕ) (T : ℝ) (x : Rd d) (F : (Fin (n + 1) → ℝ × Rd d) → E)
    (hF : StronglyMeasurable F) (hi : Integrable F (chainMeasureRaw d (n + 1) T x)) :
    Integrable (fun p : ℝ × Rd d => (lastW T p.1).toReal • ∫ z, F (Fin.snoc z
        (p.1, x - (T - p.1) • p.2) : Fin (n + 1) → ℝ × Rd d)
          ∂chainMeasureRaw d n p.1 (x - (T - p.1) • p.2))
        ((volume : Measure ℝ).prod (waveGreen d 1)) ∧
    ∫ z, F z ∂chainMeasureRaw d (n + 1) T x =
      ∫ p, (lastW T p.1).toReal • ∫ z, F (Fin.snoc z (p.1, x - (T - p.1) • p.2) :
          Fin (n + 1) → ℝ × Rd d) ∂chainMeasureRaw d n p.1 (x - (T - p.1) • p.2)
        ∂((volume : Measure ℝ).prod (waveGreen d 1)) := by
  set_option smartUnfolding false in
  set_option linter.unusedSimpArgs false in
  (bridge_revert_all; bridge_auto20 _root_.StratonovichHAMSecondMoment.MildTerminalFubini.integral_chainMeasureRaw_succ)
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MildTerminalFubini
