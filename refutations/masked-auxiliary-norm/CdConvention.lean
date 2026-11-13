/-
Refutation for the normalization of the unitary Fourier transform of
`notes/integrated_covariance_foundation.tex` (lines 8-12 at a284420, used in
the Fourier inversion of the proof of `P:masked-auxiliary-norm`, line 121),
package theorem `StratonovichHAMSecondMoment.MaskedAuxiliaryNorm.cd_sq_mul`
(`c_d² (2π)^d = 1` for `c_d = (2π)^{-d/2}`; auxiliary to the Lean proof
route).

Wrong variant: the non-squared normalization `c_d (2π)^d = 1` (the bookkeeping
of a one-sided `(2π)^{-d}` convention).  Counterexample: `d = 2`:
`c_2 (2π)² = (2π)⁻¹ (2π)² = 2π ≠ 1`.  `cd_convention_contrast` is the
package identity at `d = 2`.  No junk-value reliance (`rpow` of `2π > 0`).

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.MaskedAuxiliaryNorm

set_option autoImplicit false

open Real
open StratonovichHAMSecondMoment MaskedAuxiliaryNorm

namespace Refutations.MaskedAuxiliaryNorm

/-- `c_2 = (2π)⁻¹`. -/
theorem cd_two : cd 2 = (2 * π)⁻¹ := by
  rw [cd, show (-((2 : ℕ) : ℝ) / 2) = -1 by norm_num, Real.rpow_neg_one]

/-- `c_d (2π)^d = 1` (the normalization without the square) is false. -/
theorem cd_convention_refuted : ¬ (∀ d : ℕ, cd d * (2 * π) ^ d = 1) := by
  intro h
  have h2 := h 2
  rw [cd_two] at h2
  have hπ : (0 : ℝ) < 2 * π := by positivity
  have : (2 * π)⁻¹ * (2 * π) ^ 2 = 2 * π := by field_simp
  rw [this] at h2
  linarith [Real.pi_gt_three]

/-- The package identity at `d = 2`. -/
theorem cd_convention_contrast : cd 2 ^ 2 * (2 * π) ^ 2 = 1 := cd_sq_mul 2

end Refutations.MaskedAuxiliaryNorm
