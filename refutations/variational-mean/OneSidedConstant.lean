/-
Refutation for the time-kernel constant used in `L:variational-global-mean`
(`notes/integrated_unmasked_variational.tex` lines 85-91 at a284420: the
change `r = s - t` integrates over both signs of `r`), package theorem
`StratonovichHAMSecondMoment.VariationalMean.abs_rpow_integral`.

Wrong variant: the one-sided constant
`∫_{-1}^{1} |r|^{-a} dr = 1/(1-a)` (forgetting the negative `r`).
Counterexample: `a = 1/2`: the integral is `4`, the variant gives `2`.
`one_sided_contrast` is the package value `2/(1-a)` at `a = 1/2`.
Junk reliance: none (the integrand is integrable, `abs_rpow_integrableOn`).

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.VariationalMean

set_option autoImplicit false

open MeasureTheory Set
open StratonovichHAMSecondMoment VariationalMean

namespace Refutations.VariationalMean.Constant

/-- The package value at `a = 1/2`. -/
theorem one_sided_contrast :
    ∫ r in Ioo (-1 : ℝ) 1, |r| ^ (-(1 / 2 : ℝ)) = 2 / (1 - 1 / 2) :=
  abs_rpow_integral (by norm_num)

/-- The one-sided constant is false. -/
theorem one_sided_false :
    ¬ (∀ a : ℝ, a < 1 → ∫ r in Ioo (-1 : ℝ) 1, |r| ^ (-a) = 1 / (1 - a)) := by
  intro h
  have := h (1 / 2) (by norm_num)
  rw [one_sided_contrast] at this
  norm_num at this

end Refutations.VariationalMean.Constant
