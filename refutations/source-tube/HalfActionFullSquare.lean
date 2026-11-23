/-
Refutation for `L:tube-half-action`
(`notes/integrated_gaussian_tubes.tex` lines 581-597 at edf7085f), package
theorem `StratonovichHAMSecondMoment.SourceTube.tube_half_action`.

Class (a): manuscript-claim perturbation in the manuscript domain.
Wrong variant: the radius cost `r²/2` on the left replaced by `r²` (the TeX's
remark that the comparison "retains one half of the squared norm", lines
599-600).  Counterexample: `H = ℝ`, `J(h) = h` (bounded above on every ball):
`sup_{r ≥ 0} {g_J(r) - r²} ≤ 1/4`, while `sup_h {h - h²/2} ≥ 1/2` (at `h = 1`).
`full_square_contrast` is the package identity at the same `J`.
No junk-value reliance (`g_J(r) = r` is a genuine supremum).

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.SourceTube

set_option autoImplicit false

open StratonovichHAMSecondMoment SourceTube

namespace Refutations.SourceTube

/-- Calibration: `J = id` on `ℝ` is bounded above on every closed ball. -/
theorem full_square_bdd (r : ℝ) (_hr : 0 ≤ r) :
    BddAbove ((fun h : ℝ => h) '' Metric.closedBall (0 : ℝ) r) := by
  refine ⟨r, ?_⟩
  rintro _ ⟨h, hh, rfl⟩
  exact (le_abs_self h).trans (by simpa [Real.norm_eq_abs] using hh)

/-- The identity with the cost `r²` on the radius side is false. -/
theorem full_square_refuted :
    ¬ (∀ J : ℝ → ℝ, (∀ r, 0 ≤ r → BddAbove (J '' Metric.closedBall (0 : ℝ) r)) →
        (⨆ (r : ℝ) (_ : 0 ≤ r), ((ballSup J r - r ^ 2 : ℝ) : EReal)) =
          ⨆ h : ℝ, ((J h - ‖h‖ ^ 2 / 2 : ℝ) : EReal)) := by
  intro hall
  have heq := hall (fun h => h) full_square_bdd
  have hl : (⨆ (r : ℝ) (_ : 0 ≤ r), ((ballSup (fun h : ℝ => h) r - r ^ 2 : ℝ) : EReal)) ≤
      ((1 / 4 : ℝ) : EReal) := by
    refine iSup₂_le fun r hr => ?_
    rw [EReal.coe_le_coe_iff]
    have hb : ballSup (fun h : ℝ => h) r ≤ r := ballSup_le _ hr fun h hh =>
      (le_abs_self h).trans (by simpa [Real.norm_eq_abs] using hh)
    nlinarith [sq_nonneg (r - 1 / 2)]
  have hr : ((1 / 2 : ℝ) : EReal) ≤ ⨆ h : ℝ, (((fun h : ℝ => h) h - ‖h‖ ^ 2 / 2 : ℝ) : EReal) :=
    le_iSup_of_le (1 : ℝ) (by norm_num)
  rw [← heq] at hr
  have := (hr.trans hl)
  rw [EReal.coe_le_coe_iff] at this
  norm_num at this

/-- The package identity (cost `r²/2`) at the same `J`. -/
theorem full_square_contrast :
    (⨆ (r : ℝ) (_ : 0 ≤ r), ((ballSup (fun h : ℝ => h) r - r ^ 2 / 2 : ℝ) : EReal)) =
      ⨆ h : ℝ, (((fun h : ℝ => h) h - ‖h‖ ^ 2 / 2 : ℝ) : EReal) :=
  tube_half_action (fun h : ℝ => h) full_square_bdd

end Refutations.SourceTube
