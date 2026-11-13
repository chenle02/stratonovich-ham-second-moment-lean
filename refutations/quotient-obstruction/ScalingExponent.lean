/-
Refutation for `P:masked-quotient-obstruction`
(`notes/integrated_covariance_foundation.tex` lines 268-270 at a284420:
`Γ(cA) = cΓ(A)`, hence `α = 1` in `H:homog`), package theorem
`StratonovichHAMSecondMoment.QuotientObstruction.lineMeasure_smul_set` (used for
the `scaling` field of `homogCovariance_Gamma0`).

Wrong variant: the scaling exponent of spatial white noise in `d = 2`,
`Γ(cA) = c² Γ(A)` (i.e. `α = 0` in `Γ(cA) = c^{d-α}Γ(A)`), for every measurable
`A` and `c > 0`.
Counterexample: `A` the open unit disc, `c = 2`: `Γ(A) = 2` (the interval
`(-1,1)` on the axis) and `Γ(2A) = 4`, not `8`.
`scaling_exponent_contrast` is the package scaling at the same point.
No junk-value reliance.

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.QuotientObstruction

set_option autoImplicit false

open MeasureTheory Set Metric
open scoped Pointwise
open StratonovichHAMSecondMoment HomogHypothesis QuotientObstruction

namespace Refutations.QuotientObstruction

/-- `Γ(B(0,1)) = 2`. -/
theorem Gamma0_ball : Gamma0 (ball (0 : Rd 2) 1) = ENNReal.ofReal 2 := by
  rw [Gamma0, lineMeasure_apply norm_e2]
  have : (fun t : ℝ => t • e2) ⁻¹' ball (0 : Rd 2) 1 = ball (0 : ℝ) 1 := by
    ext t; simp [norm_smul, norm_e2]
  rw [this, Real.volume_ball]
  norm_num

/-- The package scaling at `A = B(0,1)`, `c = 2`. -/
theorem scaling_exponent_contrast :
    Gamma0 ((2 : ℝ) • ball (0 : Rd 2) 1) = ENNReal.ofReal 2 * Gamma0 (ball (0 : Rd 2) 1) :=
  lineMeasure_smul_set norm_e2 _ two_pos

/-- The scaling `Γ(cA) = c² Γ(A)` is false for `Γ = δ₀(dx₁) dx₂`. -/
theorem scaling_exponent_refuted :
    ¬ (∀ A : Set (Rd 2), MeasurableSet A → ∀ c : ℝ, 0 < c →
        Gamma0 (c • A) = ENNReal.ofReal (c ^ 2) * Gamma0 A) := by
  intro h
  have h1 := h (ball (0 : Rd 2) 1) isOpen_ball.measurableSet 2 two_pos
  rw [scaling_exponent_contrast, Gamma0_ball, ← ENNReal.ofReal_mul (by norm_num),
    ← ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_eq_ofReal_iff (by norm_num)
    (by norm_num)] at h1
  norm_num at h1

end Refutations.QuotientObstruction
