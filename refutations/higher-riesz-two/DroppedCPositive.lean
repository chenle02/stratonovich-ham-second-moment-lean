/-
Refutation for `StratonovichHAMSecondMoment.HigherRieszTwo.M2_pos` and the
hypothesis `c > 0` of `higher_riesz_two` (manuscript `L:higher-riesz`, main
TeX line 6104 at 39f2597a, "`γ(x) = c|x|^{-α}`, `c > 0`"): Hypothesis
`H:spatial-maximum` asks for `M > 0`, and `M_2 = c{...}` vanishes at `c = 0`.

Wrong variant: `0 < M_2(c, α)` for every `c ≥ 0` and `0 < α < 3/2`
(`c > 0` weakened to `c ≥ 0`).  Counterexample: `c = 0`.
`dropped_c_positive_contrast` is the package positivity at `c = 1`, `α = 1`.
No junk-value reliance.

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.HigherRieszTwo

set_option autoImplicit false

namespace Refutations.HigherRieszTwo

open StratonovichHAMSecondMoment.HigherRieszTwo

/-- The package positivity at `c = 1`, `α = 1`. -/
theorem dropped_c_positive_contrast : 0 < M2 1 1 :=
  M2_pos one_pos one_pos (by norm_num)

/-- `M_2 > 0` for `c ≥ 0` is false. -/
theorem dropped_c_positive_refuted :
    ¬ (∀ c α : ℝ, 0 ≤ c → 0 < α → α < 3 / 2 → 0 < M2 c α) := by
  intro h
  have h1 := h 0 1 le_rfl one_pos (by norm_num)
  simp [M2] at h1

end Refutations.HigherRieszTwo
