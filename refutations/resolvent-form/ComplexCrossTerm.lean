/-
Refutation for the real-cross-term hypothesis of the real/complex reduction (wave L13, item K5b),
package theorem `StratonovichHAMSecondMoment.ResolventForm.re_diag_split`.

Manuscript side: `L:signed-spectral-wave` (`notes/integrated_signed_static.tex`, line 164 at
39f2597a): "a complex diagonal splits into the two real diagonals" for `u = x + i y` with `x, y`
real.

Wrong variant: the diagonal of every Hermitian form splits at `x + i y` for arbitrary vectors
`x, y`. Counterexample: `W = ℂ`, `B(u,w) = ⟪u, w⟫`, `x = 1`, `y = i`: then `x + i y = 0` while each
real diagonal is `1`. Class (c): a broader Lean generalization outside the manuscript domain (the
vectors are not real profiles; `B(x,y) = i` is not real). `complex_cross_term_contrast` is the
package statement with the reality hypothesis.

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.ResolventForm

set_option autoImplicit false

namespace Refutations.ResolventForm

open StratonovichHAMSecondMoment.ResolventForm

/-- Without a real cross term the diagonal does not split. -/
theorem complex_cross_term :
    ¬ ∀ (B : ℂ →L⋆[ℂ] ℂ →L[ℂ] ℂ), IsHermitianForm B → ∀ x y : ℂ,
      (B (x + Complex.I • y) (x + Complex.I • y)).re = (B x x).re + (B y y).re := by
  intro H
  have h := H _ (isHermitianForm_sesqOf (IsSelfAdjoint.one (ℂ →L[ℂ] ℂ))) 1 Complex.I
  simp [sesqOf_apply] at h
  norm_num at h

/-- Contrast: with `B(x,y)` real the diagonal splits. -/
theorem complex_cross_term_contrast :
    ∀ (B : ℂ →L⋆[ℂ] ℂ →L[ℂ] ℂ), IsHermitianForm B → ∀ x y : ℂ, (B x y).im = 0 →
      (B (x + Complex.I • y) (x + Complex.I • y)).re = (B x x).re + (B y y).re :=
  fun B hH x y hxy => re_diag_split B hH x y hxy

end Refutations.ResolventForm
