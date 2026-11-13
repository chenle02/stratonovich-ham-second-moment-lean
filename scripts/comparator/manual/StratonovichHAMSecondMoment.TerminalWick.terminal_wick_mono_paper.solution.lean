namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.TerminalWick
open MeasureTheory Set
open scoped ENNReal
open WaveGreen
open FiniteWick Finset Filter Topology HomogHypothesis
-- Statement copied from the source (the printed type elaborates the `Lp` coercion's topological-group instance through `SeminormedAddCommGroup.toIsTopologicalAddGroup`, the declaration through `MeasureTheory.Lp._proof_4`).
/-- For T > 0 and two CenteredGaussianFields on [0,T] x R^d with variances bounded above, 0 <= K1 <= K2 entrywise, the same finite nu n and supplied a.e. strong measurability for both: E1[Y1_m Y1_n] <= E2[Y2_m Y2_n] for all m, n. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.TerminalWick.terminal_wick_mono_paper {Ω₁ Ω₂ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
    (P₁ : Measure Ω₁) (P₂ : Measure Ω₂) [IsProbabilityMeasure P₁] [IsProbabilityMeasure P₂]
    (d : ℕ) (_hd : d = 1 ∨ d = 2 ∨ d = 3) (T : ℝ) (hT : 0 < T)
    (W₁ : Pt d T → Ω₁ → ℝ) (K₁ : Pt d T → Pt d T → ℝ) (hW₁ : CenteredGaussianField W₁ K₁ P₁)
    (W₂ : Pt d T → Ω₂ → ℝ) (K₂ : Pt d T → Pt d T → ℝ) (hW₂ : CenteredGaussianField W₂ K₂ P₂)
    (hV₁fin : BddAbove (Set.range fun p => K₁ p p))
    (hV₂fin : BddAbove (Set.range fun p => K₂ p p))
    (_hcell₁ : MeanSquareCellContinuous K₁) (_hcell₂ : MeanSquareCellContinuous K₂)
    (ν : ∀ n : ℕ, Measure (Fin n → Pt d T)) [∀ n, IsFiniteMeasure (ν n)]
    (_hmass : ∀ n, ν n univ = chainMass d n T)
    (hmeas₁ : ∀ n, AEStronglyMeasurable (fun z : Fin n → Pt d T => prodL2 hW₁ z) (ν n))
    (hmeas₂ : ∀ n, AEStronglyMeasurable (fun z : Fin n → Pt d T => prodL2 hW₂ z) (ν n))
    (h0 : ∀ p q, 0 ≤ K₁ p q) (h12 : ∀ p q, K₁ p q ≤ K₂ p q) (m n : ℕ) :
    ∫ ω, chainIntegral ν hW₁ m ω * chainIntegral ν hW₁ n ω ∂P₁ ≤
      ∫ ω, chainIntegral ν hW₂ m ω * chainIntegral ν hW₂ n ω ∂P₂ := by
  bridge_revert_all
  bridge_auto _root_.StratonovichHAMSecondMoment.TerminalWick.terminal_wick_mono_paper
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.TerminalWick
