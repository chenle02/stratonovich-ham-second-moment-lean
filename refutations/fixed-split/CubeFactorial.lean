/-
Refutation for the simplex count of `E:interval-cross-vector` (main TeX
lines 3954-3967 at edf7085f: "There is no factor `m!` or `1/m!` in this
estimate"), package theorem
`StratonovichHAMSecondMoment.FixedSplit.sum_volume_simplex_le`.

Wrong variant: integrating every ordering over the whole cube (each ordered
Dyson integral charged the full cube), i.e.
`(#orderings) · ∏_{i∈𝒞} (b_i - a_i) ≤ ∏_{i∈𝒞} h_i` whenever
`b_i - a_i ≤ h_i`.  Counterexample: two cross colors, `(a_i, b_i) = (0, 1)`,
`h_i = 1`: `2! · 1 = 2 > 1`.  No junk-value reliance.
`cube_factorial_contrast` is the package bound `∑_π |D_π| ≤ ∏ h_i` for the
same data.

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.FixedSplit

set_option autoImplicit false

namespace Refutations.FixedSplit

open StratonovichHAMSecondMoment.FixedSplit Finset MeasureTheory

/-- Charging every ordering the full cube overcounts by `m!`. -/
theorem cube_factorial_refuted :
    ¬ (∀ (C : Finset (Fin 2)) (a b h : Fin 2 → ℝ), (∀ i ∈ C, 0 ≤ h i) →
        (∀ i ∈ C, b i - a i ≤ h i) →
        (Fintype.card (Fin (Fintype.card C) ≃ C) : ℝ) * ∏ i ∈ C, (b i - a i) ≤ ∏ i ∈ C, h i) := by
  intro hall
  have := hall univ (fun _ => 0) (fun _ => 1) (fun _ => 1) (fun _ _ => zero_le_one)
    (fun _ _ => by norm_num)
  have hc : Fintype.card (Fin (Fintype.card (univ : Finset (Fin 2))) ≃ (univ : Finset (Fin 2))) =
      2 := by
    rw [Fintype.card_equiv (Fintype.equivFin _).symm]
    simp
  rw [hc] at this
  norm_num at this

/-- Contrast: the package bound for the same data, `∑_π |D_π| ≤ 1`. -/
theorem cube_factorial_contrast :
    ∑ o : Fin (Fintype.card (univ : Finset (Fin 2))) ≃ (univ : Finset (Fin 2)),
        volume.real (simplex univ (fun _ => 0) (fun _ => 1) o) ≤
      ∏ i ∈ (univ : Finset (Fin 2)), (fun _ => (1 : ℝ)) i :=
  sum_volume_simplex_le univ _ _ _ (fun _ _ => zero_le_one) fun _ _ => by norm_num

end Refutations.FixedSplit
