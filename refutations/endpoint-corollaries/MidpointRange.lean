/-
Refutation for `StratonovichHAMSecondMoment.EndpointCorollaries.midTheta_mem` (manuscript
`C:three-product-riesz` and `C:three-finite-images`, main TeX lines 7946, 7962-7965 at
39f2597a): the midpoint `θ = (α₀ + 2 - α)/2` lies in `(α₀, 2 - α)` only because
`α < 2 - α₀`.

Wrong variant: `θ < 2 - α` for all `0 < α₀ < 1` and `1 < α < 2` (the bound `α < 2 - α₀`
weakened to `α < 2`).  Counterexample: `α₀ = 1/2`, `α = 7/4`: `θ = 3/8 > 1/4 = 2 - α`.
Class (a): perturbation of the manuscript claim inside the manuscript's domain.
`midpoint_range_contrast` is the package lemma at `α₀ = 1/2`, `α = 5/4`.  No junk values.

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.EndpointCorollaries

set_option autoImplicit false

namespace Refutations.EndpointCorollaries

open StratonovichHAMSecondMoment.EndpointCorollaries

/-- The package lemma with `α = 5/4 < 2 - α₀ = 3/2`. -/
theorem midpoint_range_contrast : midTheta (1 / 2) (5 / 4) < 2 - 5 / 4 :=
  (midTheta_mem (by norm_num)).2

/-- `θ < 2 - α` fails once `α < 2 - α₀` is weakened to `α < 2`. -/
theorem midpoint_range_refuted :
    ¬ (∀ α₀ α : ℝ, 0 < α₀ → α₀ < 1 → 1 < α → α < 2 → midTheta α₀ α < 2 - α) := by
  intro h
  have h1 := h (1 / 2) (7 / 4) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [midTheta] at h1

end Refutations.EndpointCorollaries
