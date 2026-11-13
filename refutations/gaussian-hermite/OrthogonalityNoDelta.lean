import StratonovichHAMSecondMoment.GaussianHermite

/-!
Refutation for `StratonovichHAMSecondMoment.GaussianHermite.integral_He_mul_He` (Hermite
orthogonality `E[He_n He_m] = n! δ_{nm}`, used in the proofs of `L:fock-form`, main TeX lines
2515-2517, and `E:occupied-multiplication`, lines 1805-1810, at a284420).

Wrong variant: dropping the Kronecker delta, `E[He_n He_m] = n!` for all `n, m`.
Counterexample: `n = 0`, `m = 1`: the package gives `0`, the wrong variant `0! = 1`.
No junk-value reliance.  `orthogonality_contrast` is the package identity at the same point.

Expected outcome: compiles (refuted).
-/

set_option autoImplicit false

namespace Refutations.GaussianHermite

open StratonovichHAMSecondMoment.GaussianHermite ProbabilityTheory
open scoped Nat

/-- `E[He_n He_m] = n!` fails without the Kronecker delta. -/
theorem orthogonality_no_delta_refuted :
    ¬ (∀ n m : ℕ, ∫ x, He n x * He m x ∂gaussianReal 0 1 = (n ! : ℝ)) := by
  intro H
  have h := H 0 1
  rw [(integral_He_mul_He 0 1).2] at h
  norm_num at h

/-- Contrast: the package identity at `n = 0`, `m = 1`. -/
theorem orthogonality_contrast : ∫ x, He 0 x * He 1 x ∂gaussianReal 0 1 = 0 := by
  rw [(integral_He_mul_He 0 1).2]; norm_num

end Refutations.GaussianHermite
