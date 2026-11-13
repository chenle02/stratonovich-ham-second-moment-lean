/-
Refutation for the four-mode expansion of `L:masked-trig-products` (TeX
l. 363-365), package theorems
`StratonovichHAMSecondMoment.MaskedTrigProducts.four_mode` and
`StratonovichHAMSecondMoment.MaskedTrigProducts.sin_sin_expand`.

Wrong variant: the sine-sine expansion with the signs dropped, i.e. every
coefficient `coef .sin .sin j` replaced by its modulus `‖coef .sin .sin j‖ = 1/4`
(all four coefficients `+1/4`), stated with the package's own `Trig.eval`,
`coef` and `freq`. Witness `r = ρ = t = 0`: `0 = 1` fails. The correct
coefficients are `-1/4, 1/4, 1/4, -1/4` for the frequencies
`r+ρ, r-ρ, -r+ρ, -r-ρ`; the contrast theorem instantiates the package's
`sin_sin_expand` at the same point.

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.MaskedTrigProducts

set_option autoImplicit false

namespace Refutations.MaskedTrigProducts

open StratonovichHAMSecondMoment.MaskedTrigProducts

/-- Replacing each package coefficient `coef .sin .sin j` by its modulus
(dropping the signs) breaks the four-mode expansion. -/
theorem sin_sin_all_plus :
    ¬ ∀ r ρ t : ℝ,
      Trig.eval .sin (r * t) * Trig.eval .sin (ρ * t) =
        ∑ j : Bool × Bool, (‖coef .sin .sin j‖ : ℂ) *
          Complex.exp (((freq r ρ j * t : ℝ) : ℂ) * Complex.I) := by
  intro h
  have := h 0 0 0
  simp only [norm_coef] at this
  simp [Trig.eval, freq] at this

/-- Contrast: the package expansion `sin_sin_expand` (signed coefficients) holds
at the counterexample point `r = ρ = t = 0`. -/
theorem sin_sin_all_plus_contrast :
    (Real.sin (0 * 0) : ℂ) * Real.sin (0 * 0) =
      -(1 / 4) * Complex.exp ((((0 + 0) * 0 : ℝ) : ℂ) * Complex.I)
      + 1 / 4 * Complex.exp ((((0 - 0) * 0 : ℝ) : ℂ) * Complex.I)
      + 1 / 4 * Complex.exp ((((-0 + 0) * 0 : ℝ) : ℂ) * Complex.I)
      - 1 / 4 * Complex.exp ((((-0 - 0) * 0 : ℝ) : ℂ) * Complex.I) :=
  StratonovichHAMSecondMoment.MaskedTrigProducts.sin_sin_expand 0 0 0

end Refutations.MaskedTrigProducts
