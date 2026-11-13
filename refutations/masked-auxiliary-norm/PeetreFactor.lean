/-
Refutation for the Peetre inequality used in the temperedness part of
`P:masked-auxiliary-norm` (`notes/integrated_covariance_foundation.tex`
lines 88-100 at a284420; the Lean route replaces the dyadic argument of
lines 113-114), package theorem
`StratonovichHAMSecondMoment.MaskedAuxiliaryNorm.peetre`
(`(1+|η|)^{-N} ≤ (1+|ξ|)^{-N} (1+|ξ-η|)^N`; auxiliary to the Lean proof
route).

Wrong variant: the factor `(1+|ξ-η|)^N` dropped, i.e.
`(1+|η|)^{-N} ≤ (1+|ξ|)^{-N}` for all `ξ, η` and `N`.  Counterexample: `d = 1`,
`ξ = e₁` (a unit vector), `η = 0`, `N = 1`: `1 ≤ 1/2` is false.
`peetre_factor_contrast` is the package inequality at the same point.  No
junk-value reliance (`rpow` of positive bases only).

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.MaskedAuxiliaryNorm

set_option autoImplicit false

open StratonovichHAMSecondMoment HomogHypothesis MaskedAuxiliaryNorm

namespace Refutations.MaskedAuxiliaryNorm

/-- A unit vector of `ℝ¹`. -/
noncomputable def e1 : Rd 1 := EuclideanSpace.single 0 1

theorem norm_e1 : ‖e1‖ = 1 := by simp [e1]

/-- Peetre's inequality without the factor `(1+|ξ-η|)^N` is false. -/
theorem peetre_factor_refuted :
    ¬ (∀ ξ η : Rd 1, ∀ N : ℕ, (1 + ‖η‖) ^ (-(N : ℝ)) ≤ (1 + ‖ξ‖) ^ (-(N : ℝ))) := by
  intro h
  have h1 := h e1 0 1
  rw [norm_zero, norm_e1, add_zero, Nat.cast_one, Real.one_rpow,
    show (1 : ℝ) + 1 = 2 by norm_num, Real.rpow_neg_one] at h1
  norm_num at h1

/-- The package inequality at the same point. -/
theorem peetre_factor_contrast :
    (1 + ‖(0 : Rd 1)‖) ^ (-((1 : ℕ) : ℝ)) ≤
      (1 + ‖e1‖) ^ (-((1 : ℕ) : ℝ)) * (1 + ‖e1 - 0‖) ^ 1 :=
  peetre e1 0 1

end Refutations.MaskedAuxiliaryNorm
