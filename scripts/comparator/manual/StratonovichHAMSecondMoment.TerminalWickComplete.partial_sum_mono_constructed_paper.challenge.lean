namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.TerminalWickComplete
-- Statement copied from the source (the printed type round-trips only up to definitional equality).
open MeasureTheory Set Filter Topology Finset
open scoped ComplexConjugate
open TerminalWick TerminalWickInputs FiniteWick HomogHypothesis
/-- P1, P2 probabilities (unused), d in {1,2,3}, T > 0, x, centered Gaussian fields W1, W2 with bounded variances, cell continuity, 0 <= K1 <= K2: for real r and N, E(sum_(n<=N) r^n Y1 n)^2 <= E(sum_(n<=N) r^n Y2 n)^2; same for the full series. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.TerminalWickComplete.partial_sum_mono_constructed_paper {Ω₁ Ω₂ : Type*} [MeasurableSpace Ω₁]
    [MeasurableSpace Ω₂] (P₁ : Measure Ω₁) (P₂ : Measure Ω₂) [IsProbabilityMeasure P₁]
    [IsProbabilityMeasure P₂] (d : ℕ) (hd : d = 1 ∨ d = 2 ∨ d = 3) (T : ℝ) (hT : 0 < T)
    (x : Rd d)
    (W₁ : Pt d T → Ω₁ → ℝ) (K₁ : Pt d T → Pt d T → ℝ) (hW₁ : CenteredGaussianField W₁ K₁ P₁)
    (W₂ : Pt d T → Ω₂ → ℝ) (K₂ : Pt d T → Pt d T → ℝ) (hW₂ : CenteredGaussianField W₂ K₂ P₂)
    (hV₁fin : BddAbove (Set.range fun p => K₁ p p))
    (hV₂fin : BddAbove (Set.range fun p => K₂ p p))
    (hcell₁ : MeanSquareCellContinuous K₁) (hcell₂ : MeanSquareCellContinuous K₂)
    (h0 : ∀ p q, 0 ≤ K₁ p q) (h12 : ∀ p q, K₁ p q ≤ K₂ p q) :
    let ν : ∀ n : ℕ, Measure (Fin n → Pt d T) := fun n => chainMeasure d n T hT.le x
    (∀ (r : ℝ) (N : ℕ),
      ∫ ω, ((∑ n ∈ range (N + 1), r ^ n • chainIntegral ν hW₁ n : Lp ℝ 2 P₁) ω) ^ 2 ∂P₁ ≤
        ∫ ω, ((∑ n ∈ range (N + 1), r ^ n • chainIntegral ν hW₂ n : Lp ℝ 2 P₂) ω) ^ 2 ∂P₂) ∧
      ∀ r : ℝ,
        ∫ ω, ((∑' n, r ^ n • chainIntegral ν hW₁ n : Lp ℝ 2 P₁) ω) ^ 2 ∂P₁ ≤
          ∫ ω, ((∑' n, r ^ n • chainIntegral ν hW₂ n : Lp ℝ 2 P₂) ω) ^ 2 ∂P₂ := by
  sorry
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.TerminalWickComplete
