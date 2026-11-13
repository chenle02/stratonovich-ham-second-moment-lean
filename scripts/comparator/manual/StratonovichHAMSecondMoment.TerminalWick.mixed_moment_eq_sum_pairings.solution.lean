namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.TerminalWick
open MeasureTheory Set
open scoped ENNReal
open WaveGreen
open FiniteWick Finset
-- Statement copied from the source (the printed type elaborates the `Lp` coercion's topological-group instance through `SeminormedAddCommGroup.toIsTopologicalAddGroup`, the declaration through `MeasureTheory.Lp._proof_4`).
-- The section variables used, written as binders: {X Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : X → Ω → ℝ} {K : X → X → ℝ} [MeasurableSpace X] (ν : ∀ n : ℕ, Measure (Fin n → X)) [∀ n, IsFiniteMeasure (ν n)].
/-- Under the hypotheses of integrable_prodL2, if (x, y) -> K x y is measurable: E[Y_m Y_n] = sum over D in pairings of univ (Fin (m+n)) of the nu m x nu n integral of the pairWeight of (a, b) -> K (tau a) (tau b) at D. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.TerminalWick.mixed_moment_eq_sum_pairings {X Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : X → Ω → ℝ} {K : X → X → ℝ} [MeasurableSpace X] (ν : ∀ n : ℕ, Measure (Fin n → X)) [∀ n, IsFiniteMeasure (ν n)] (hW : CenteredGaussianField W K P) (V : ℝ) (hV0 : 0 ≤ V)
    (hV : ∀ x, K x x ≤ V)
    (hmeas : ∀ n, AEStronglyMeasurable (fun z : Fin n → X => prodL2 hW z) (ν n))
    (hK : Measurable fun q : X × X => K q.1 q.2) (m n : ℕ) :
    ∫ ω, chainIntegral ν hW m ω * chainIntegral ν hW n ω ∂P =
      ∑ D ∈ pairings (univ : Finset (Fin (m + n))),
        ∫ q, pairWeight (fun a b => K (Fin.append q.1 q.2 a) (Fin.append q.1 q.2 b)) univ D
          ∂((ν m).prod (ν n)) := by
  bridge_revert_all
  bridge_auto _root_.StratonovichHAMSecondMoment.TerminalWick.mixed_moment_eq_sum_pairings
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.TerminalWick
