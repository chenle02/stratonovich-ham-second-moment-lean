namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.TerminalWickComplete
-- Statement copied from the source (the printed type round-trips only up to definitional equality).
open MeasureTheory Set Filter Topology Finset
open scoped ComplexConjugate
open TerminalWick TerminalWickInputs FiniteWick HomogHypothesis
/-- P1, P2 probabilities (unused), d in {1,2,3}, T > 0, x, centered Gaussian fields W1, W2, bounded variances, cell continuity: every conclusion of terminal_wick_constructed_paper for W1; complex r; if 0 <= K1 <= K2, mixed moments, partial sums and full series compared. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.TerminalWickComplete.terminal_wick_full_constructed_paper {Ω₁ Ω₂ : Type*} [MeasurableSpace Ω₁]
    [MeasurableSpace Ω₂] (P₁ : Measure Ω₁) (P₂ : Measure Ω₂) [IsProbabilityMeasure P₁]
    [IsProbabilityMeasure P₂] (d : ℕ) (hd : d = 1 ∨ d = 2 ∨ d = 3) (T : ℝ) (hT : 0 < T)
    (x : Rd d)
    (W₁ : Pt d T → Ω₁ → ℝ) (K₁ : Pt d T → Pt d T → ℝ) (hW₁ : CenteredGaussianField W₁ K₁ P₁)
    (hV₁fin : BddAbove (Set.range fun p => K₁ p p)) (hcell₁ : MeanSquareCellContinuous K₁)
    (W₂ : Pt d T → Ω₂ → ℝ) (K₂ : Pt d T → Pt d T → ℝ) (hW₂ : CenteredGaussianField W₂ K₂ P₂)
    (hV₂fin : BddAbove (Set.range fun p => K₂ p p)) (hcell₂ : MeanSquareCellContinuous K₂) :
    let ν : ∀ n : ℕ, Measure (Fin n → Pt d T) := fun n => chainMeasure d n T hT.le x
    ((∀ n, Integrable (fun z : Fin n → Pt d T => prodL2 hW₁ z) (ν n)) ∧
      ((chainIntegral ν hW₁ 0 : Ω₁ → ℝ) =ᵐ[P₁] fun _ => 1) ∧
      (∀ n, ‖chainIntegral ν hW₁ n‖ ≤ Real.sqrt ((2 * n - 1).doubleFactorial) *
        (⨆ p, K₁ p p) ^ ((n : ℝ) / 2) * (T ^ (2 * n) / (2 * n).factorial)) ∧
      (∀ m n, ∫ ω, chainIntegral ν hW₁ m ω * chainIntegral ν hW₁ n ω ∂P₁ =
        ∑ D ∈ pairings (univ : Finset (Fin (m + n))), pairingIntegral ν K₁ m n D) ∧
      (∀ m n (D : Fin (m + n) → Fin (m + n)),
        Integrable (fun q : (Fin m → Pt d T) × (Fin n → Pt d T) =>
          pairWeight (fun a b => K₁ (Fin.append q.1 q.2 a) (Fin.append q.1 q.2 b)) univ D)
          ((ν m).prod (ν n))) ∧
      (∀ m n, Odd (m + n) → ∫ ω, chainIntegral ν hW₁ m ω * chainIntegral ν hW₁ n ω ∂P₁ = 0) ∧
      ((∀ p q, 0 ≤ K₁ p q) →
        (∀ m n (D : Fin (m + n) → Fin (m + n)), 0 ≤ pairingIntegral ν K₁ m n D) ∧
        ∀ m n, 0 ≤ ∫ ω, chainIntegral ν hW₁ m ω * chainIntegral ν hW₁ n ω ∂P₁) ∧
      (∀ r : ℝ, Summable fun n => ‖r ^ n • chainIntegral ν hW₁ n‖) ∧
      ((∀ p q, 0 ≤ K₁ p q) → ∀ r : ℝ,
        UniformSeriesTail.TerminalWickInput P₁ (fun n => chainIntegral ν hW₁ n) r)) ∧
    ((∀ r : ℂ, Summable (fun n => ‖r ^ n • toC (chainIntegral ν hW₁ n)‖) ∧
      Summable (fun n => r ^ n • toC (chainIntegral ν hW₁ n))) ∧
    (∀ (r : ℂ) (N : ℕ),
      ((∫ ω, ‖(∑ n ∈ range (N + 1), r ^ n • toC (chainIntegral ν hW₁ n) : Lp ℂ 2 P₁) ω‖ ^ 2
        ∂P₁ : ℝ) : ℂ) =
        ∑ m ∈ range (N + 1), ∑ n ∈ range (N + 1), r ^ m * conj r ^ n *
          ((∫ ω, chainIntegral ν hW₁ m ω * chainIntegral ν hW₁ n ω ∂P₁ : ℝ) : ℂ)) ∧
    ∀ r : ℂ, Tendsto (fun N => ∑ m ∈ range N, ∑ n ∈ range N, r ^ m * conj r ^ n *
        ((∫ ω, chainIntegral ν hW₁ m ω * chainIntegral ν hW₁ n ω ∂P₁ : ℝ) : ℂ)) atTop
      (𝓝 ((∫ ω, ‖(∑' n, r ^ n • toC (chainIntegral ν hW₁ n) : Lp ℂ 2 P₁) ω‖ ^ 2
        ∂P₁ : ℝ) : ℂ))) ∧
    ((∀ p q, 0 ≤ K₁ p q) → (∀ p q, K₁ p q ≤ K₂ p q) →
      (∀ m n, ∫ ω, chainIntegral ν hW₁ m ω * chainIntegral ν hW₁ n ω ∂P₁ ≤
        ∫ ω, chainIntegral ν hW₂ m ω * chainIntegral ν hW₂ n ω ∂P₂) ∧
      (∀ (r : ℝ) (N : ℕ),
        ∫ ω, ((∑ n ∈ range (N + 1), r ^ n • chainIntegral ν hW₁ n : Lp ℝ 2 P₁) ω) ^ 2 ∂P₁ ≤
          ∫ ω, ((∑ n ∈ range (N + 1), r ^ n • chainIntegral ν hW₂ n : Lp ℝ 2 P₂) ω) ^ 2
            ∂P₂) ∧
      ∀ r : ℝ,
        ∫ ω, ((∑' n, r ^ n • chainIntegral ν hW₁ n : Lp ℝ 2 P₁) ω) ^ 2 ∂P₁ ≤
          ∫ ω, ((∑' n, r ^ n • chainIntegral ν hW₂ n : Lp ℝ 2 P₂) ω) ^ 2 ∂P₂) := by
  bridge_revert_all
  bridge_rw
  intro Ω₁ Ω₂ _ _ P₁ P₂ _ _ d hd T hT x W₁ K₁ hW₁ hV₁fin hcell₁ W₂ K₂ hW₂ hV₂fin hcell₂
  exact _root_.StratonovichHAMSecondMoment.TerminalWickComplete.terminal_wick_full_constructed_paper P₁ P₂ d hd T hT x W₁ K₁
    (StratonovichHamSecondMomentLeanAuditBridge.FiniteWick.cgfToP hW₁) hV₁fin hcell₁ W₂ K₂ (StratonovichHamSecondMomentLeanAuditBridge.FiniteWick.cgfToP hW₂) hV₂fin hcell₂
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.TerminalWickComplete
