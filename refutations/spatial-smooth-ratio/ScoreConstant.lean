/-
Refutation for the scalar identity of the optimisation in
`P:spatial-smooth-ratio` (`notes/integrated_spatial_occupation.tex` lines
200-213 at a284420), package theorem
`StratonovichHAMSecondMoment.SpatialSmoothRatio.score_algebra`
(`M (1+u)² L^q = 2 X^{1/k} u^{α/2} R`, i.e. `C L^q = X^{1/k}` for the TeX's
`C = M(1+u)²/(2 R u^{α/2})` at the maximiser `L = q X^{1/k}`).

Wrong variant: the factor `2` dropped (the cost `v/2` read as `v`), i.e.
`M (1+u)² L^q = X^{1/k} u^{α/2} R` for all `0 < α < 2`, `M, R > 0`.
Counterexample: `α = M = R = 1`.  The package identity gives the same left side
equal to `2Y` with `Y = X^{1/k} u^{α/2} R > 0`, while the variant gives `Y`.
`score_constant_contrast` is the package identity at the same point.
No junk-value reliance (all bases positive).

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.SpatialSmoothRatio

set_option autoImplicit false

open StratonovichHAMSecondMoment SpatialSmoothRatio

namespace Refutations.SpatialSmoothRatio

/-- The scalar identity without the factor `2` is false. -/
theorem score_constant_refuted :
    ¬ (∀ alpha M R : ℝ, 0 < alpha → alpha < 2 → 0 < M → 0 < R →
        M * (1 + alpha / (4 - alpha)) ^ 2 *
          ((4 - alpha) * (R * alpha ^ (alpha / 2) /
            (8 * M * (4 - alpha) ^ ((4 - alpha) / 2))) ^ (1 / (3 - alpha))) ^ (4 - alpha) =
        (R * alpha ^ (alpha / 2) /
            (8 * M * (4 - alpha) ^ ((4 - alpha) / 2))) ^ (1 / (3 - alpha)) *
          (alpha / (4 - alpha)) ^ (alpha / 2) * R) := by
  intro h
  have h1 := h 1 1 1 one_pos (by norm_num) one_pos one_pos
  have h2 := score_algebra (alpha := 1) (M := 1) (R := 1) one_pos (by norm_num) one_pos one_pos
  have hY : 0 < (1 * (1 : ℝ) ^ ((1 : ℝ) / 2) /
      (8 * 1 * (4 - 1) ^ ((4 - (1 : ℝ)) / 2))) ^ (1 / (3 - (1 : ℝ))) *
        ((1 : ℝ) / (4 - 1)) ^ ((1 : ℝ) / 2) * 1 := by
    have : (0 : ℝ) < (4 - 1) ^ ((4 - (1 : ℝ)) / 2) := Real.rpow_pos_of_pos (by norm_num) _
    have : (0 : ℝ) < ((1 : ℝ) / (4 - 1)) ^ ((1 : ℝ) / 2) := Real.rpow_pos_of_pos (by norm_num) _
    have : (0 : ℝ) < (1 * (1 : ℝ) ^ ((1 : ℝ) / 2) /
        (8 * 1 * (4 - 1) ^ ((4 - (1 : ℝ)) / 2))) ^ (1 / (3 - (1 : ℝ))) :=
      Real.rpow_pos_of_pos (by positivity) _
    positivity
  rw [h1] at h2
  linarith

/-- The package identity at the same point. -/
theorem score_constant_contrast :
    1 * (1 + 1 / (4 - 1)) ^ 2 *
        ((4 - 1) * (1 * (1 : ℝ) ^ ((1 : ℝ) / 2) /
          (8 * 1 * (4 - 1) ^ ((4 - (1 : ℝ)) / 2))) ^ (1 / (3 - (1 : ℝ)))) ^ (4 - (1 : ℝ)) =
      2 * (1 * (1 : ℝ) ^ ((1 : ℝ) / 2) /
          (8 * 1 * (4 - 1) ^ ((4 - (1 : ℝ)) / 2))) ^ (1 / (3 - (1 : ℝ))) *
        ((1 : ℝ) / (4 - 1)) ^ ((1 : ℝ) / 2) * 1 :=
  score_algebra one_pos (by norm_num) one_pos one_pos

end Refutations.SpatialSmoothRatio
