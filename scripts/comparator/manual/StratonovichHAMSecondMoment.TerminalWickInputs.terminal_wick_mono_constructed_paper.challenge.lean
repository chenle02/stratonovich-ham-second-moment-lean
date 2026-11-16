namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.TerminalWickInputs
-- Statement copied from the source (the printed type is only definitionally equal to the declaration's (an instance path differs: `SeminormedAddCommGroup.toIsTopologicalAddGroup` for `Lp`'s, or `WithLp.measurableSpace`); CheckFidelity requires Expr equality).
open MeasureTheory Set Filter Topology
open scoped ENNReal Pointwise
open TerminalWick FiniteWick WaveGreen HomogHypothesis
open Finset
/-- d in {1,2,3}, T > 0, x; centered Gaussian fields W1, W2 with bounded variance, MeanSquareCellContinuous K1, K2 and 0 <= K1 <= K2: for nu n = chainMeasure d n T x, E[Y1_m Y1_n] <= E[Y2_m Y2_n] for all m, n (terminal_wick_mono_paper with hmass, hmeas1, hmeas2 discharged). -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.TerminalWickInputs.terminal_wick_mono_constructed_paper {Ω₁ Ω₂ : Type*} [MeasurableSpace Ω₁]
    [MeasurableSpace Ω₂] (P₁ : Measure Ω₁) (P₂ : Measure Ω₂) [IsProbabilityMeasure P₁]
    [IsProbabilityMeasure P₂] (d : ℕ) (hd : d = 1 ∨ d = 2 ∨ d = 3) (T : ℝ) (hT : 0 < T)
    (x : Rd d)
    (W₁ : Pt d T → Ω₁ → ℝ) (K₁ : Pt d T → Pt d T → ℝ) (hW₁ : CenteredGaussianField W₁ K₁ P₁)
    (W₂ : Pt d T → Ω₂ → ℝ) (K₂ : Pt d T → Pt d T → ℝ) (hW₂ : CenteredGaussianField W₂ K₂ P₂)
    (hV₁fin : BddAbove (Set.range fun p => K₁ p p))
    (hV₂fin : BddAbove (Set.range fun p => K₂ p p))
    (hcell₁ : MeanSquareCellContinuous K₁) (hcell₂ : MeanSquareCellContinuous K₂)
    (h0 : ∀ p q, 0 ≤ K₁ p q) (h12 : ∀ p q, K₁ p q ≤ K₂ p q) (m n : ℕ) :
    ∫ ω, chainIntegral (fun n => chainMeasure d n T hT.le x) hW₁ m ω *
        chainIntegral (fun n => chainMeasure d n T hT.le x) hW₁ n ω ∂P₁ ≤
      ∫ ω, chainIntegral (fun n => chainMeasure d n T hT.le x) hW₂ m ω *
        chainIntegral (fun n => chainMeasure d n T hT.le x) hW₂ n ω ∂P₂ := by
  sorry
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.TerminalWickInputs
