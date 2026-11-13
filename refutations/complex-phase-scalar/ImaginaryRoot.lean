/-
Refutation for the root bound of `L:complex-phase` (main TeX lines 2395-2396 at
a284420), package theorem
`StratonovichHAMSecondMoment.ComplexPhaseScalar.im_root_le`
(`r² = w`, `|w| ≤ Re w + 2λ²` give `|Im r| ≤ λ`).

Wrong variant: the bound `λ/2`.  Counterexample: `λ = 1`, `w = -1`
(`|w| = 1 = Re w + 2`), `r = i`, `|Im r| = 1 > 1/2`.  `imaginary_root_contrast`
applies the package theorem at the same point, where `λ` is attained.  No
junk-value reliance.

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.ComplexPhaseScalar

set_option autoImplicit false

namespace Refutations.ComplexPhaseScalar

/-- The root bound `λ/2` is false. -/
theorem imaginary_root_half_refuted :
    ¬ (∀ (lam : ℝ) (r w : ℂ), 0 ≤ lam → r ^ 2 = w → ‖w‖ ≤ w.re + 2 * lam ^ 2 →
        |r.im| ≤ lam / 2) := by
  intro h
  have h1 := h 1 Complex.I (-1) (by norm_num) Complex.I_sq (by simp; norm_num)
  norm_num at h1

/-- The package bound at `λ = 1`, `w = -1`, `r = i`. -/
theorem imaginary_root_contrast : |Complex.I.im| ≤ 1 :=
  StratonovichHAMSecondMoment.ComplexPhaseScalar.im_root_le (lam := 1) (w := -1) (by norm_num)
    Complex.I_sq (by simp; norm_num)

end Refutations.ComplexPhaseScalar
