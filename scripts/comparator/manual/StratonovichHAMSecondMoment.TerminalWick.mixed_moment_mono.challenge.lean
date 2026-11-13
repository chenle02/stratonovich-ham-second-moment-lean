namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.TerminalWick
open MeasureTheory Set
open scoped ENNReal
open WaveGreen
open FiniteWick Finset
-- Statement copied from the source (the printed type elaborates the `Lp` coercion's topological-group instance through `SeminormedAddCommGroup.toIsTopologicalAddGroup`, the declaration through `MeasureTheory.Lp._proof_4`).
-- The section variables used, written as binders: {X Ω₁ Ω₂ : Type*} [MeasurableSpace X] [MeasurableSpace Ω₁] [MeasurableSpace Ω₂] {P₁ : Measure Ω₁} {P₂ : Measure Ω₂} {W₁ : X → Ω₁ → ℝ} {W₂ : X → Ω₂ → ℝ} {K₁ K₂ : X → X → ℝ} (ν : ∀ n : ℕ, Measure (Fin n → X)) [∀ n, IsFiniteMeasure (ν n)].
/-- For CenteredGaussianField W1 K1 P1 and W2 K2 P2 on X, variance bounds 0 <= V1, V2, the same finite measures nu n, a.e. strong measurability for both, and 0 <= K1 <= K2 entrywise: E1[Y1_m Y1_n] <= E2[Y2_m Y2_n] for all m, n. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.TerminalWick.mixed_moment_mono {X Ω₁ Ω₂ : Type*} [MeasurableSpace X] [MeasurableSpace Ω₁] [MeasurableSpace Ω₂] {P₁ : Measure Ω₁} {P₂ : Measure Ω₂} {W₁ : X → Ω₁ → ℝ} {W₂ : X → Ω₂ → ℝ} {K₁ K₂ : X → X → ℝ} (ν : ∀ n : ℕ, Measure (Fin n → X)) [∀ n, IsFiniteMeasure (ν n)] (hW₁ : CenteredGaussianField W₁ K₁ P₁)
    (hW₂ : CenteredGaussianField W₂ K₂ P₂) (V₁ V₂ : ℝ) (hV₁0 : 0 ≤ V₁) (hV₂0 : 0 ≤ V₂)
    (hV₁ : ∀ x, K₁ x x ≤ V₁) (hV₂ : ∀ x, K₂ x x ≤ V₂)
    (hmeas₁ : ∀ n, AEStronglyMeasurable (fun z : Fin n → X => prodL2 hW₁ z) (ν n))
    (hmeas₂ : ∀ n, AEStronglyMeasurable (fun z : Fin n → X => prodL2 hW₂ z) (ν n))
    (h0 : ∀ x y, 0 ≤ K₁ x y) (h12 : ∀ x y, K₁ x y ≤ K₂ x y) (m n : ℕ) :
    ∫ ω, chainIntegral ν hW₁ m ω * chainIntegral ν hW₁ n ω ∂P₁ ≤
      ∫ ω, chainIntegral ν hW₂ m ω * chainIntegral ν hW₂ n ω ∂P₂ := by
  sorry
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.TerminalWick
