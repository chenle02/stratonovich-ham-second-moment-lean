/-
Refutation for the four-mode expansion of `L:masked-trig-products` (TeX
l. 363-365), package theorems
`StratonovichHAMSecondMoment.MaskedTrigProducts.four_mode` and
`StratonovichHAMSecondMoment.MaskedTrigProducts.cos_cos_expand`.

Wrong variant: the cosine-cosine expansion with every coefficient doubled,
`2 * coef .cos .cos j = 1/2` instead of `coef .cos .cos j = 1/4`, stated with
the package's own `Trig.eval`, `coef` and `freq`. Witness `r = ρ = t = 0`:
`1 = 2` fails. The contrast theorem instantiates the package's
`cos_cos_expand` at the same point (coefficients `1/4`), which holds.

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.MaskedTrigProducts

set_option autoImplicit false

namespace Refutations.MaskedTrigProducts

open StratonovichHAMSecondMoment.MaskedTrigProducts

/-- Doubling the package coefficients `coef .cos .cos` (`1/4 ↦ 1/2`) breaks the
four-mode expansion. -/
theorem cos_cos_coefficient_half :
    ¬ ∀ r ρ t : ℝ,
      Trig.eval .cos (r * t) * Trig.eval .cos (ρ * t) =
        ∑ j : Bool × Bool, 2 * coef .cos .cos j *
          Complex.exp (((freq r ρ j * t : ℝ) : ℂ) * Complex.I) := by
  intro h
  have := h 0 0 0
  simp [Trig.eval, coef, coef1, freq] at this
  norm_num at this

/-- Contrast: the package expansion `cos_cos_expand` (coefficients `1/4`) holds
at the counterexample point `r = ρ = t = 0`. -/
theorem cos_cos_coefficient_half_contrast :
    (Real.cos (0 * 0) : ℂ) * Real.cos (0 * 0) =
      1 / 4 * Complex.exp ((((0 + 0) * 0 : ℝ) : ℂ) * Complex.I)
      + 1 / 4 * Complex.exp ((((0 - 0) * 0 : ℝ) : ℂ) * Complex.I)
      + 1 / 4 * Complex.exp ((((-0 + 0) * 0 : ℝ) : ℂ) * Complex.I)
      + 1 / 4 * Complex.exp ((((-0 - 0) * 0 : ℝ) : ℂ) * Complex.I) :=
  StratonovichHAMSecondMoment.MaskedTrigProducts.cos_cos_expand 0 0 0

end Refutations.MaskedTrigProducts
