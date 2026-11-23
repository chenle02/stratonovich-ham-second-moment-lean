/-
Refutation for `StratonovichHAMSecondMoment.EndpointLemmas.plane_exponents` (manuscript
`L:plane-endpoints`, main TeX lines 7343-7347 at edf7085f): the static plane exponents
`v_j = a_j/(1 - θ)` stay below one only because `θ < 2 - α = 1 - (a₁ + a₂)`.

Wrong variant: `v_j < 1` for all `1 < α < 2`, `a_j ≥ 0`, `a₁ + a₂ = α - 1` and `0 < θ < 1`.
Counterexample: `α = 3/2`, `a = (1/2, 0)`, `θ = 3/5`: `v₁ = (1/2)/(2/5) = 5/4`.  Class (a):
perturbation of the manuscript claim inside the manuscript's domain.
`plane_exponent_bound_contrast` is the package lemma at the same `a` with
`θ = 1/5 < 2 - α`.  No junk-value reliance (`1 - θ ≠ 0`).

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.EndpointLemmas

set_option autoImplicit false

namespace Refutations.EndpointLemmas

open StratonovichHAMSecondMoment.EndpointLemmas

/-- The package lemma with `θ = 1/5 < 2 - α = 1/2`. -/
theorem plane_exponent_bound_contrast :
    ![(1 : ℝ) / 2, 0] 0 / (1 - 1 / 5) < 1 :=
  ((plane_exponents (α := 3 / 2) (θ := 1 / 5) (a := ![1 / 2, 0]) (by norm_num) (by norm_num)
    (by norm_num) (fun j => by fin_cases j <;> norm_num) (by norm_num)).2.1 0).2

/-- `v_j < 1` fails once `θ < 2 - α` is weakened to `θ < 1`. -/
theorem plane_exponent_bound_refuted :
    ¬ (∀ (α θ : ℝ) (a : Fin 2 → ℝ), 1 < α → α < 2 → (∀ j, 0 ≤ a j) → a 0 + a 1 = α - 1 →
      0 < θ → θ < 1 → ∀ j, a j / (1 - θ) < 1) := by
  intro h
  have h1 := h (3 / 2) (3 / 5) ![1 / 2, 0] (by norm_num) (by norm_num)
    (fun j => by fin_cases j <;> norm_num) (by norm_num) (by norm_num) (by norm_num) 0
  norm_num at h1

end Refutations.EndpointLemmas
