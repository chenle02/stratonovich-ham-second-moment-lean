import StratonovichHAMSecondMoment.GramScalarAlgebra

/-!
Refutation for `StratonovichHAMSecondMoment.GramScalarAlgebra.gram_identity`, manuscript
label `L:gram-scalar-algebra` (the finite Gram identity, with `C_ij = ⟪k_i, k_j⟫`).

Wrong variant: `gram_identity` with the double sum `∑_{i,j} w_i C_ij w_j` replaced by
its diagonal `∑_i w_i² C_ii` (correct only for orthogonal `k_i`). It is stated in the
exact shape of the package theorem (same binders and hypothesis `hC`), with the index
type and the space quantified over `Type`. Counterexample: `ι = Fin 2`, `H = ℝ`,
`k_i = 1`, `w_i = 1`, `C_ij = ⟪k_i, k_j⟫ = 1`: `‖1 + 1‖² = 4` while the diagonal sum
is `2`. The contrast theorem applies the package `gram_identity` at this point.

Expected outcome: compiles (refuted).
-/

namespace Refutations.GramScalarAlgebra

/-- `gram_identity` with only the diagonal terms is false. -/
theorem diagonal_only_gram :
    ¬ ∀ (ι : Type) (H : Type) [Fintype ι] [NormedAddCommGroup H] [InnerProductSpace ℝ H]
      (k : ι → H) (C : ι → ι → ℝ), (∀ i j, C i j = inner ℝ (k i) (k j)) →
      ∀ (w : ι → ℝ), ‖∑ i, w i • k i‖ ^ 2 = ∑ i, w i ^ 2 * C i i := by
  intro h
  have := h (Fin 2) ℝ (fun _ => 1) (fun i j => inner ℝ ((fun _ : Fin 2 => (1 : ℝ)) i)
    ((fun _ : Fin 2 => (1 : ℝ)) j)) (fun _ _ => rfl) (fun _ => 1)
  simp only [real_inner_self_eq_norm_sq] at this
  norm_num [Fin.sum_univ_two] at this

/-- Contrast: at the counterexample the package `gram_identity` gives the full double
sum, whose value `4` differs from the diagonal sum `2`. -/
theorem diagonal_only_gram_contrast :
    ‖∑ _i : Fin 2, (1 : ℝ) • (1 : ℝ)‖ ^ 2 =
        ∑ _i : Fin 2, ∑ _j : Fin 2, (1 : ℝ) * inner ℝ (1 : ℝ) (1 : ℝ) * 1 ∧
      ∑ _i : Fin 2, ∑ _j : Fin 2, (1 : ℝ) * inner ℝ (1 : ℝ) (1 : ℝ) * 1 = 4 ∧
      ∑ _i : Fin 2, (1 : ℝ) ^ 2 * inner ℝ (1 : ℝ) (1 : ℝ) = 2 := by
  refine ⟨StratonovichHAMSecondMoment.GramScalarAlgebra.gram_identity
    (fun _ : Fin 2 => (1 : ℝ)) (fun _ _ => inner ℝ (1 : ℝ) (1 : ℝ)) (fun _ _ => rfl)
    (fun _ => 1), ?_, ?_⟩ <;>
  · simp only [real_inner_self_eq_norm_sq]
    norm_num [Fin.sum_univ_two]

end Refutations.GramScalarAlgebra
