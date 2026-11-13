/-
Refutation for the Wick formula of `FiniteWick` (`E:terminal-wick-formula`'s
Gaussian step, main TeX lines 3662-3673 at a284420), package theorem
`StratonovichHAMSecondMoment.FiniteWick.wick_multivariateGaussian`.

Wrong variant: `E x⁴ = (E x²)² = 1` for `x ~ N(0,1)` (one pairing per
repeated index instead of all three pairings of the four factors).
Counterexample: `multivariateGaussian 0 1` on `ℝ¹`, the coordinate `x_0` taken
four times: the Wick formula gives `3` (three pairings, each of weight `1`).
`fourth_moment_contrast` is the package theorem at the same point.
No junk-value reliance (the identity matrix is positive semidefinite, so
`multivariateGaussian 0 1` is the standard Gaussian, not the Dirac fallback).

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.FiniteWick

set_option autoImplicit false

open MeasureTheory ProbabilityTheory StratonovichHAMSecondMoment FiniteWick

namespace Refutations.FiniteWick

/-- The package value: `E x_0⁴ = 3` under `multivariateGaussian 0 1`. -/
theorem fourth_moment_contrast :
    ∫ x, ∏ _i : Fin 4, x (0 : Fin 1) ∂multivariateGaussian 0 (1 : Matrix (Fin 1) (Fin 1) ℝ) =
      3 := by
  rw [(wick_multivariateGaussian (1 : Matrix (Fin 1) (Fin 1) ℝ) Matrix.PosSemidef.one
    (fun _ : Fin 4 => (0 : Fin 1)) Finset.univ).2]
  simp only [Matrix.one_apply_eq]
  rw [wickSum_const_one, card_pairings_even 2 _ (by simp)]
  norm_num [Nat.doubleFactorial]

/-- `E x⁴ = 1` for a standard Gaussian is false. -/
theorem fourth_moment_refuted :
    ¬ (∫ x, ∏ _i : Fin 4, x (0 : Fin 1) ∂multivariateGaussian 0 (1 : Matrix (Fin 1) (Fin 1) ℝ) =
      1) := by
  rw [fourth_moment_contrast]
  norm_num

end Refutations.FiniteWick
