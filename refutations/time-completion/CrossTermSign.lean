/-
Refutation for the positivity clause of `L:masked-time-completion`
(`notes/integrated_covariance_foundation.tex` lines 143-147 at a284420), package
theorem `StratonovichHAMSecondMoment.TimeCompletion.timeForm_re_nonneg`.

Wrong variant: positivity of the form off the diagonal, i.e. `Re⟨f,g⟩_a ≥ 0` for all
`f, g ∈ L²(0,T)` (positive semidefiniteness says only `Re⟨f,f⟩_a ≥ 0`).
Counterexample: `a = 1/2`, `T = 1`, `f = 1`, `g = -1`:
`⟨1,-1⟩_a = -⟨1,1⟩_a = -8/3 < 0` (package `timeForm_smul_right`, `timeForm_one`).
`cross_term_contrast` is the package positivity at `f = 1`.
No junk-value reliance.

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.TimeCompletion

set_option autoImplicit false

open MeasureTheory Set
open StratonovichHAMSecondMoment TimeCompletion TimeSchur

namespace Refutations.TimeCompletion

/-- The package positivity at `a = 1/2`, `T = 1`, `f = 1`. -/
theorem cross_term_contrast :
    0 ≤ (timeForm (1 / 2) 1 (fun _ => (1 : ℂ)) (fun _ => (1 : ℂ))).re :=
  timeForm_re_nonneg (by norm_num) (by norm_num) (by norm_num) (memLp_const 1)

/-- Positivity of the off-diagonal form is false. -/
theorem cross_term_refuted :
    ¬ (∀ f g : ℝ → ℂ, MemLp f 2 (volume.restrict (Icc (0 : ℝ) 1)) →
        MemLp g 2 (volume.restrict (Icc (0 : ℝ) 1)) → 0 ≤ (timeForm (1 / 2) 1 f g).re) := by
  intro h
  have h1 := h (fun _ => (1 : ℂ)) ((-1 : ℂ) • fun _ => (1 : ℂ)) (memLp_const 1)
    ((memLp_const 1).const_smul (-1 : ℂ))
  rw [timeForm_smul_right, timeForm_one (by norm_num) (by norm_num)] at h1
  norm_num at h1

end Refutations.TimeCompletion
