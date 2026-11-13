module
import StratonovichHAMSecondMoment.GramScalarAlgebra
set_option autoImplicit false
set_option pp.all true
#check @StratonovichHAMSecondMoment.GramScalarAlgebra.sqrt_dual
#print axioms StratonovichHAMSecondMoment.GramScalarAlgebra.sqrt_dual
#check @StratonovichHAMSecondMoment.GramScalarAlgebra.hilbert_square_eq
#print axioms StratonovichHAMSecondMoment.GramScalarAlgebra.hilbert_square_eq
#check @StratonovichHAMSecondMoment.GramScalarAlgebra.hilbert_square_le
#print axioms StratonovichHAMSecondMoment.GramScalarAlgebra.hilbert_square_le
#check @StratonovichHAMSecondMoment.GramScalarAlgebra.hilbert_square
#print axioms StratonovichHAMSecondMoment.GramScalarAlgebra.hilbert_square
#check @StratonovichHAMSecondMoment.GramScalarAlgebra.gram_identity
#print axioms StratonovichHAMSecondMoment.GramScalarAlgebra.gram_identity
#check @StratonovichHAMSecondMoment.GramScalarAlgebra.gram_scalar_algebra_paper
#print axioms StratonovichHAMSecondMoment.GramScalarAlgebra.gram_scalar_algebra_paper
/-- Consumer: the paper lemma used as in the positive-Gram upper bound, with
`z = ∑ w_i k_i`: `⟪Φ, ∑ w_i k_i⟫ - ‖Φ‖²/2 ≤ (∑_{i,j} w_i C_ij w_j)/2`. -/
private theorem gram_consumer {ι H : Type*} [Fintype ι]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (k : ι → H) (C : ι → ι → ℝ) (hC : ∀ i j, C i j = inner ℝ (k i) (k j))
    (hCnn : ∀ i j, 0 ≤ C i j) (Φ : H) (w : ι → ℝ) :
    inner ℝ Φ (∑ i, w i • k i) - ‖Φ‖ ^ 2 / 2 ≤ (∑ i, ∑ j, w i * C i j * w j) / 2 := by
  obtain ⟨-, hsq, hgram⟩ :=
    StratonovichHAMSecondMoment.GramScalarAlgebra.gram_scalar_algebra_paper k C hC hCnn
  have h1 := hsq Φ (∑ i, w i • k i)
  rw [← hgram w]
  linarith [h1.1, h1.2]
#check @gram_consumer
#print axioms gram_consumer
example : inner ℝ (2 : ℝ) (∑ _i : Fin 1, (1 : ℝ) • (1 : ℝ)) - ‖(2 : ℝ)‖ ^ 2 / 2 ≤
    (∑ _i : Fin 1, ∑ _j : Fin 1, (1 : ℝ) * 1 * 1) / 2 :=
  gram_consumer (ι := Fin 1) (H := ℝ) (fun _ => 1) (fun _ _ => 1)
    (by intro i j; simp) (by intro i j; norm_num) 2 (fun _ => 1)
