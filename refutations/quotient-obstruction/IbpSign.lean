/-
Refutation for `P:masked-quotient-obstruction`
(`notes/integrated_covariance_foundation.tex` lines 284-285 at a284420:
"integration by parts gives the masked marginal `-I_χ χ(x₁)²`"), package theorem
`StratonovichHAMSecondMoment.QuotientObstruction.integral_chi_mul_chi2`.

Wrong variant: the sign of the integration by parts dropped,
`∫ χ χ'' = I_χ = ∫ (χ')²`.
Counterexample: the package's `χ`, for which `∫ χ χ'' = -I_χ` and `I_χ > 0`.
`ibp_sign_contrast` is the package value: `∫ χ χ'' < 0`.
No junk-value reliance (the package proves the integrability of `χ χ''`
inside `integral_mul_deriv_eq_deriv_mul`).

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.QuotientObstruction

set_option autoImplicit false

open MeasureTheory
open StratonovichHAMSecondMoment QuotientObstruction

namespace Refutations.QuotientObstruction

/-- `∫ χ χ'' = I_χ` is false. -/
theorem ibp_sign_refuted : ¬ (∫ x, chi x * chi2 x = Ichi) := by
  intro h
  rw [integral_chi_mul_chi2] at h
  linarith [Ichi_pos]

/-- The package value: `∫ χ χ'' = -I_χ < 0`. -/
theorem ibp_sign_contrast : ∫ x, chi x * chi2 x < 0 := by
  rw [integral_chi_mul_chi2]
  linarith [Ichi_pos]

end Refutations.QuotientObstruction
