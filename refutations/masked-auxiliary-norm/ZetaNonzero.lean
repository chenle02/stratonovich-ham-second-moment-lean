/-
Refutation for `L > 0` (`notes/integrated_covariance_foundation.tex`
lines 79-82 at a284420, part of the setup of `P:masked-auxiliary-norm`),
package theorem `StratonovichHAMSecondMoment.MaskedAuxiliaryNorm.Lz_pos`.

Wrong variant: the hypothesis `ζ ≠ 0` ("a real nonzero Schwartz function",
line 79) dropped, i.e. `L = ‖ζ̂‖₁ > 0` for every real Schwartz `ζ`.
Counterexample: `d = 1`, `ζ = 0`: `ζ̂ = 0` and `L = 0`.
`zeta_nonzero_contrast` is the package theorem at the nonzero Gaussian
`e^{-|x|²}`.  No junk-value reliance: `L = 0` here is the genuine value of the
integral of the zero function.

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.MaskedAuxiliaryNorm

set_option autoImplicit false

open StratonovichHAMSecondMoment HomogHypothesis MaskedAuxiliaryNorm

namespace Refutations.MaskedAuxiliaryNorm

/-- `L = 0` for `ζ = 0`. -/
theorem Lz_zero : Lz (0 : SchwartzMap (Rd 1) ℝ) = 0 := by
  simp [Lz, paperHat]

/-- `L > 0` without `ζ ≠ 0` is false. -/
theorem zeta_nonzero_refuted : ¬ (∀ ζ : SchwartzMap (Rd 1) ℝ, 0 < Lz ζ) := by
  intro h
  have := h 0
  rw [Lz_zero] at this
  exact lt_irrefl 0 this

/-- The Gaussian `e^{-|x|²}` on `ℝ¹` as a real Schwartz map. -/
noncomputable def gaussOne : SchwartzMap (Rd 1) ℝ := GaussianTest.gaussSchwartz 1 one_pos

/-- The package theorem at a nonzero `ζ`. -/
theorem zeta_nonzero_contrast : 0 < Lz gaussOne := by
  refine (Lz_pos gaussOne ?_).2
  intro h
  have h0 := congrArg (fun f : SchwartzMap (Rd 1) ℝ => f 0) h
  simp [gaussOne] at h0

end Refutations.MaskedAuxiliaryNorm
