import StratonovichHAMSecondMoment.GaussianHermite

/-!
Refutation for `StratonovichHAMSecondMoment.GaussianHermite.integral_He_mul_He` read as
orthonormality of the unnormalized polynomials (the normalization `hn = He_n/√(n!)` used in
`L:fock-form`, main TeX line 2515 at a284420, is needed).

Wrong variant: `E[He_n²] = 1` for all `n`.  Counterexample: `n = 2`, where `E[He_2²] = 2! = 2`.
No junk-value reliance.  `unnormalized_contrast` is the package value.

Expected outcome: compiles (refuted).
-/

set_option autoImplicit false

namespace Refutations.GaussianHermite

open StratonovichHAMSecondMoment.GaussianHermite ProbabilityTheory

/-- The unnormalized Hermite polynomials are not orthonormal. -/
theorem unnormalized_orthonormal_refuted :
    ¬ (∀ n : ℕ, ∫ x, He n x * He n x ∂gaussianReal 0 1 = 1) := by
  intro H
  have h := H 2
  rw [(integral_He_mul_He 2 2).2] at h
  norm_num [Nat.factorial] at h

/-- Contrast: `E[He_2²] = 2`. -/
theorem unnormalized_contrast : ∫ x, He 2 x * He 2 x ∂gaussianReal 0 1 = 2 := by
  rw [(integral_He_mul_He 2 2).2]; norm_num [Nat.factorial]

end Refutations.GaussianHermite
