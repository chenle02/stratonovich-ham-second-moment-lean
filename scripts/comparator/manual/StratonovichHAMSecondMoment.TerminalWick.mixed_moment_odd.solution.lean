namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.TerminalWick
open MeasureTheory Set
open scoped ENNReal
open WaveGreen
open FiniteWick Finset
-- Statement copied from the source (the printed type elaborates the `Lp` coercion's topological-group instance through `SeminormedAddCommGroup.toIsTopologicalAddGroup`, the declaration through `MeasureTheory.Lp._proof_4`).
-- The section variables used, written as binders: {X Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : X → Ω → ℝ} {K : X → X → ℝ} [MeasurableSpace X] (ν : ∀ n : ℕ, Measure (Fin n → X)) [∀ n, IsFiniteMeasure (ν n)].
/-- Under the hypotheses of integrable_prodL2: if m + n is odd, the P-integral of Y_m(omega) * Y_n(omega) is 0. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.TerminalWick.mixed_moment_odd {X Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : X → Ω → ℝ} {K : X → X → ℝ} [MeasurableSpace X] (ν : ∀ n : ℕ, Measure (Fin n → X)) [∀ n, IsFiniteMeasure (ν n)] (hW : CenteredGaussianField W K P) (V : ℝ) (hV0 : 0 ≤ V)
    (hV : ∀ x, K x x ≤ V)
    (hmeas : ∀ n, AEStronglyMeasurable (fun z : Fin n → X => prodL2 hW z) (ν n)) (m n : ℕ)
    (hodd : Odd (m + n)) :
    ∫ ω, chainIntegral ν hW m ω * chainIntegral ν hW n ω ∂P = 0 := by
  bridge_revert_all
  bridge_auto _root_.StratonovichHAMSecondMoment.TerminalWick.mixed_moment_odd
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.TerminalWick
