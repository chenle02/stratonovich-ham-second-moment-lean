/-
Refutation for the norm of the complexification used in the real-`H` clause
of `P:masked-auxiliary-norm` (`notes/integrated_covariance_foundation.tex`,
line 117 at 39f2597a, "after complexification"), package theorem
`StratonovichHAMSecondMoment.MaskedAuxiliaryReal.Cx.norm_sq_eq`
(`‖x + iy‖² = ‖x‖² + ‖y‖²`).

Wrong variant: the sum norm `‖x + iy‖ = ‖x‖ + ‖y‖` (the norm of `H × H` with
the `ℓ¹` convention), which is not a Hilbert norm.  Counterexample: `H = ℝ`,
`z = 1 + i`: `‖z‖² = 2`, so `‖z‖ = √2 ≠ 2`.  `norm_sum_convention_contrast`
is the package identity at the witness.  No junk value is involved.

Class (b): control of the Lean route (the complexification is built in the
companion; the TeX does not define its norm).

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.MaskedAuxiliaryReal

set_option autoImplicit false

open StratonovichHAMSecondMoment.MaskedAuxiliaryReal

namespace Refutations.MaskedAuxiliaryReal

/-- Contrast: `‖1 + i‖² = 2` in `Cx ℝ`. -/
theorem norm_sum_convention_contrast : ‖(⟨1, 1⟩ : Cx ℝ)‖ ^ 2 = 2 := by
  rw [Cx.norm_sq_eq]; norm_num

/-- The sum norm `‖x + iy‖ = ‖x‖ + ‖y‖` is false for the complexification. -/
theorem norm_sum_convention_refuted :
    ¬ ∀ z : Cx ℝ, ‖z‖ = ‖z.re‖ + ‖z.im‖ := by
  intro h
  have h1 := h ⟨1, 1⟩
  have h2 := norm_sum_convention_contrast
  simp only [norm_one] at h1
  rw [h1] at h2
  norm_num at h2

end Refutations.MaskedAuxiliaryReal
