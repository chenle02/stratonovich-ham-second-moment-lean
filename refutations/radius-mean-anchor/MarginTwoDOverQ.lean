/-
Refutation for the margin of `P:radius-mean-anchor` (TeX lines 323-325,
`E:radius-anchor-Q`), package theorem
`StratonovichHAMSecondMoment.RadiusMeanAnchor.anchor_margin_pos`.

Wrong variant: the margin `(1-a)/2 - d/Q > 0` from `Q > 2d/(1-a)` strengthened
to `(1-a)/2 - 2d/Q > 0`, stated in the exact shape of `anchor_margin_pos`
(binders `a Q d : ℝ`, hypotheses `a < 1`, `0 < Q`, `2d/(1-a) < Q`). Witness:
d = 1, a = 1/10, Q = 4 (4 > 2/(9/10) = 20/9); then
(1-a)/2 - 2d/Q = 9/20 - 1/2 < 0. The earlier version also assumed `0 < a`,
`2 ≤ Q` and `1 ≤ d`; the package theorem does not, so the variant is now in
the package's shape, and the witness still satisfies those manuscript side
conditions (0 < a < 1 as in H:homog, Q = 4 even, d = 1); the contrast theorem
records them. The contrast also applies `anchor_margin_pos` at the witness,
where `(1-a)/2 - d/Q = 9/20 - 1/4 > 0` holds.

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.RadiusMeanAnchor

set_option autoImplicit false

namespace Refutations.RadiusMeanAnchor

/-- The margin `(1-a)/2 - d/Q` cannot be replaced by `(1-a)/2 - 2d/Q`. -/
theorem margin_two_d_over_Q :
    ¬ ∀ (a Q d : ℝ), a < 1 → 0 < Q → 2 * d / (1 - a) < Q →
      0 < (1 - a) / 2 - 2 * d / Q := by
  intro h
  have := h (1 / 10) 4 1 (by norm_num) (by norm_num) (by norm_num)
  norm_num at this

/-- Contrast: at the witness `a = 1/10`, `Q = 4`, `d = 1` the manuscript side
conditions hold and the package margin `anchor_margin_pos` is positive. -/
theorem margin_two_d_over_Q_contrast :
    (0 < (1 / 10 : ℝ) ∧ (2 : ℝ) ≤ 4 ∧ (1 : ℝ) ≤ 1) ∧
      0 < (1 - 1 / 10 : ℝ) / 2 - 1 / 4 :=
  ⟨by norm_num,
    StratonovichHAMSecondMoment.RadiusMeanAnchor.anchor_margin_pos (1 / 10) 4 1
      (by norm_num) (by norm_num) (by norm_num)⟩

end Refutations.RadiusMeanAnchor
