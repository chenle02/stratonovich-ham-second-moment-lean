/-
Refutation for `StratonovichHAMSecondMoment.EndpointLemmas.sum_lowEnd_lt` and the arithmetic of
`product_arithmetic` (manuscript `L:product-endpoints`, main TeX lines 7171-7173 and 7220-7235
at 39f2597a): `Σ L_j < 1` (hence `0 < Λ < 1`) needs `θ < 2 - α`.

Wrong variant: `Σ_j L_j < 1` for all `0 ≤ a_j < 1` with `1 < α = Σ a_j < 2` and `0 < θ < 1`
(the bound `θ < 2 - α` weakened to `θ < 1`).  Counterexample: `a = (9/10, 9/10, 0)`,
`α = 9/5`, `θ = 1/2`: `L_1 = L_2 = 4/5`, `Σ L_j = 8/5`.  Class (a): perturbation of the
manuscript claim inside the manuscript's domain.  `dropped_theta_bound_contrast` is the
package lemma at the same `a` with `θ = 1/10 < 2 - α`.  No junk-value reliance
(`θ ≠ 0`).

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.EndpointLemmas

set_option autoImplicit false

namespace Refutations.EndpointLemmas

open StratonovichHAMSecondMoment.EndpointLemmas

/-- The package lemma with `θ = 1/10 < 2 - α = 1/5`. -/
theorem dropped_theta_bound_contrast :
    ∑ j, lowEnd (1 / 10) ![9 / 10, 9 / 10, 0] j < 1 :=
  sum_lowEnd_lt ⟨fun j => by fin_cases j <;> norm_num, fun j => by fin_cases j <;> norm_num,
    by simp [Fin.sum_univ_three]; norm_num, by simp [Fin.sum_univ_three]; norm_num,
    by norm_num, by simp [Fin.sum_univ_three]; norm_num⟩

/-- `Σ L_j < 1` fails once `θ < 2 - α` is weakened to `θ < 1`. -/
theorem dropped_theta_bound_refuted :
    ¬ (∀ (a : Fin 3 → ℝ) (θ : ℝ), (∀ j, 0 ≤ a j) → (∀ j, a j < 1) → 1 < ∑ j, a j →
      ∑ j, a j < 2 → 0 < θ → θ < 1 → ∑ j, lowEnd θ a j < 1) := by
  intro h
  have h1 := h ![9 / 10, 9 / 10, 0] (1 / 2) (fun j => by fin_cases j <;> norm_num)
    (fun j => by fin_cases j <;> norm_num) (by simp [Fin.sum_univ_three]; norm_num)
    (by simp [Fin.sum_univ_three]; norm_num) (by norm_num) (by norm_num)
  simp [lowEnd, Fin.sum_univ_three] at h1
  norm_num at h1

end Refutations.EndpointLemmas
