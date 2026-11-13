/-
Refutation for `‖k_R‖₁ = L` (`notes/integrated_covariance_foundation.tex`
lines 80-82 at a284420, the reason the ball bound `E:masked-auxiliary-growth`
of `P:masked-auxiliary-norm`, lines 90-93, is uniform in `R`), package theorem
`StratonovichHAMSecondMoment.MaskedAuxiliaryNorm.integral_norm_kR`.

Wrong variant: the `L¹` norm of the kernel scales with the Jacobian,
`‖k_R‖₁ = R^d L` (which would destroy the uniformity in `R`).
Counterexample: `d = 1`, `ζ = e^{-|x|²}` (the package Gaussian Schwartz map),
`R = 2`: with the package identity it gives `L = 2L`, contradicting `L > 0`
(`Lz_pos`).  `kernel_norm_contrast` is the package identity at the same
point.  No junk-value reliance (all integrands are integrable:
`integrable_kR`, `Lz_pos`).

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.MaskedAuxiliaryNorm

set_option autoImplicit false

open StratonovichHAMSecondMoment HomogHypothesis MaskedAuxiliaryNorm

namespace Refutations.MaskedAuxiliaryNorm

/-- The Gaussian `e^{-|x|²}` on `ℝ¹` as a real Schwartz map. -/
noncomputable def gauss1 : SchwartzMap (Rd 1) ℝ := GaussianTest.gaussSchwartz 1 one_pos

theorem gauss1_ne_zero : gauss1 ≠ 0 := by
  intro h
  have h0 := congrArg (fun f : SchwartzMap (Rd 1) ℝ => f 0) h
  simp [gauss1] at h0

/-- `‖k_R‖₁ = R^d L` is false. -/
theorem kernel_norm_scaling_refuted :
    ¬ (∀ ζ : SchwartzMap (Rd 1) ℝ, ∀ R : ℝ, 0 < R → ∫ u, ‖kR ζ R u‖ = R ^ 1 * Lz ζ) := by
  intro h
  have h1 := h gauss1 2 two_pos
  rw [integral_norm_kR gauss1 two_pos] at h1
  have hL := (Lz_pos gauss1 gauss1_ne_zero).2
  linarith

/-- The package identity at the same point. -/
theorem kernel_norm_contrast : ∫ u, ‖kR gauss1 2 u‖ = Lz gauss1 :=
  integral_norm_kR gauss1 two_pos

end Refutations.MaskedAuxiliaryNorm
