import StratonovichHAMSecondMoment.OccupationCeilingFinite

/-!
Refutation for `StratonovichHAMSecondMoment.OccupationCeilingFinite.young_q`
(`E v^{1/q} - v/2 ≤ (k/2)(2E/q)^{q/k}`, the second scalar maximum of the proof of
`T:intrinsic-occupation-ceiling`, `integrated_occupation_ceiling.tex` lines 235-237).

Wrong variant: the maximum `0` (variance penalty alone dominates), with the same binders and
hypotheses. Witness: `α = 0`, `E = 1`, `v = 1`, where the left side is `1/2`. No junk value is
used (`1^{1/4} = 1`). The contrast theorem applies the package theorem there.

Expected outcome: compiles (refuted).
-/

set_option autoImplicit false

namespace Refutations.OccupationCeilingFinite

open StratonovichHAMSecondMoment.OccupationCeilingFinite

/-- Contrast: at `α = 0`, `E = v = 1` the left side is `1/2` and the package bound holds. -/
theorem zero_score_contrast :
    (1 : ℝ) * (1 : ℝ) ^ (1 / (4 - 0 : ℝ)) - 1 / 2 = 1 / 2 ∧
      (1 : ℝ) * (1 : ℝ) ^ (1 / (4 - 0 : ℝ)) - 1 / 2 ≤
        (3 - 0) / 2 * (2 * 1 / (4 - 0 : ℝ)) ^ ((4 - 0) / (3 - 0 : ℝ)) :=
  ⟨by rw [Real.one_rpow]; norm_num, young_q (by norm_num) zero_le_one zero_le_one⟩

/-- The maximum `0` is false. -/
theorem zero_score_max :
    ¬ (∀ alpha E v : ℝ, alpha < 3 → 0 ≤ E → 0 ≤ v →
      E * v ^ (1 / (4 - alpha)) - v / 2 ≤ 0) := by
  intro h
  have := h 0 1 1 (by norm_num) zero_le_one zero_le_one
  linarith [zero_score_contrast.1]

end Refutations.OccupationCeilingFinite
