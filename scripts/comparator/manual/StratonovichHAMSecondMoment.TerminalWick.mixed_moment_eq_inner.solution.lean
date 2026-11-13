namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.TerminalWick
open MeasureTheory Set
open scoped ENNReal
open WaveGreen
open FiniteWick Finset
-- Statement copied from the source (the printed type elaborates the `Lp` coercion's topological-group instance through `SeminormedAddCommGroup.toIsTopologicalAddGroup`, the declaration through `MeasureTheory.Lp._proof_4`).
-- The section variables used, written as binders: {X Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : X → Ω → ℝ} {K : X → X → ℝ} [MeasurableSpace X] (ν : ∀ n : ℕ, Measure (Fin n → X)).
/-- For any measures nu n: the P-integral of Y_m(omega) * Y_n(omega) equals the L^2 inner product of Y_m and Y_n. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.TerminalWick.mixed_moment_eq_inner {X Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : X → Ω → ℝ} {K : X → X → ℝ} [MeasurableSpace X] (ν : ∀ n : ℕ, Measure (Fin n → X)) (hW : CenteredGaussianField W K P) (m n : ℕ) :
    ∫ ω, chainIntegral ν hW m ω * chainIntegral ν hW n ω ∂P =
      inner ℝ (chainIntegral ν hW m) (chainIntegral ν hW n) := by
  bridge_revert_all
  bridge_auto _root_.StratonovichHAMSecondMoment.TerminalWick.mixed_moment_eq_inner
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.TerminalWick
