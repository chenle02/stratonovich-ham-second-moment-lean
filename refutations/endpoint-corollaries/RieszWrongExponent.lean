/-
Refutation for the affine identity behind
`StratonovichHAMSecondMoment.EndpointCorollaries.riesz_comparison` (manuscript
`C:three-product-riesz`, main TeX lines 7981-7985 at edf7085f: `α = θ + (1 - θ)χ` gives
`γ_α = γ_1^θ γ_χ^{1-θ}`).

Wrong variant: the factorization with a static exponent violating the affine identity, here
`c|x|^{-3/2} = (c|x|^{-1})^{1/2} (c|x|^{-1})^{1/2}` (`c = 1`, `θ = 1/2`, static exponent `1`
instead of `χ = 2`).  Counterexample: `|x| = 4`, where the left side is `1/8` and the right
side `1/4`.  Control of the broader affine-factorization lemma, outside the manuscript's
endpoint range: `α = 3/2`, `θ = 1/2` has `θ = 2 - α` (and the contrast `χ = 2`), while the
manuscript requires `θ < 2 - α`, hence `χ < 2` (main TeX lines 7289-7293). 
`riesz_wrong_exponent_contrast` is the package comparison with `χ = 2`.  No
junk-value reliance (`x ≠ 0`).

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.EndpointCorollaries

set_option autoImplicit false

namespace Refutations.EndpointCorollaries

open MeasureTheory
open StratonovichHAMSecondMoment.EndpointCorollaries StratonovichHAMSecondMoment.EndpointLemmas
open StratonovichHAMSecondMoment.HigherRieszTwo (riesz)
open StratonovichHAMSecondMoment.HomogHypothesis (Rd)

/-- The package comparison with the affine exponent `χ = 2` (`3/2 = 1/2 + (1/2)·2`). -/
theorem riesz_wrong_exponent_contrast :
    GaussComparison (1 / 2) (rieszMeasure 1 (3 / 2)) (rieszMeasure 1 1) (rieszMeasure 1 2) :=
  riesz_comparison one_pos (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- The factorization with the wrong static exponent fails at `|x| = 4`. -/
theorem riesz_wrong_exponent_refuted :
    ¬ (∀ x : Rd 3, riesz 1 (3 / 2) x =
      riesz 1 1 x ^ (1 / 2 : ℝ) * riesz 1 1 x ^ (1 - 1 / 2 : ℝ)) := by
  intro h
  obtain ⟨x, hx⟩ := exists_norm_eq (Rd 3) (by norm_num : (0 : ℝ) ≤ 4)
  have h1 := h x
  have hsplit : riesz (d := 3) 1 1 x ^ (1 / 2 : ℝ) * riesz 1 1 x ^ (1 - 1 / 2 : ℝ) =
      riesz 1 1 x := rpow_mul_rpow_one_sub _ (by norm_num) (by norm_num)
  rw [hsplit] at h1
  simp only [riesz, hx, one_mul] at h1
  have e1 : (4 : ℝ) ^ (-(3 / 2 : ℝ)) = 1 / 8 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
    norm_num
  have e2 : (4 : ℝ) ^ (-(1 : ℝ)) = 1 / 4 := by norm_num
  rw [e1, e2] at h1
  have := (ENNReal.ofReal_eq_ofReal_iff (by norm_num) (by norm_num)).1 h1
  norm_num at this

end Refutations.EndpointCorollaries
