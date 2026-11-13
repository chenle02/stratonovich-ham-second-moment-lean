/-
Refutation for the length-substitution step of `P:interval-coefficients`
(main TeX lines 3506-3538 at revision a284420), package theorem
`StratonovichHAMSecondMoment.IntervalScalar.singleton_weight_le`, which needs
`L ≥ 1` (the TeX's reduction `L ↦ max{1, L}`, lines 3417-3420).

Wrong variant: dropping `L ≥ 1` (any `L > 0`).  Counterexample:
`α = α₀ = 1` (so `β = 2`), `L = 1/2`, `T = 1`, `k = i = 1`, `h = LT/i = 1/2`:
the singleton weight is `h²(1 + 1/h) = 3/4`, the claimed bound is
`L² T² (1 + 1) = 1/2`.  `length_constant_contrast` is the package bound at the
same data with `L = 1`.  No junk-value reliance (all bases positive).

Expected outcome: compiles (refuted)
-/
import StratonovichHAMSecondMoment.IntervalScalar

set_option autoImplicit false

namespace Refutations.IntervalScalar

/-- Without `L ≥ 1` the singleton substitution fails. -/
theorem length_constant_refuted :
    ¬ (∀ L : ℝ, 0 < L → ∀ h : ℝ, 0 < h → h ≤ L * 1 / ((1 : ℕ) : ℝ) →
        h ^ ((4 : ℝ) - 1 - 1) * (1 + 1 / (((1 : ℕ) : ℝ) / 1 * h)) ≤
          L ^ ((4 : ℝ) - 1 - 1) * (1 : ℝ) ^ ((4 : ℝ) - 1 - 1) *
            ((((1 : ℕ) : ℝ)) ^ (-((4 : ℝ) - 1 - 1)) +
              (((1 : ℕ) : ℝ))⁻¹ * (((1 : ℕ) : ℝ)) ^ (-((4 : ℝ) - 1 - 1 - 1)))) := by
  intro hall
  have h1 := hall (1 / 2) (by norm_num) (1 / 2) (by norm_num) (by norm_num)
  have e2 : (4 : ℝ) - 1 - 1 = 2 := by norm_num
  rw [e2] at h1
  simp only [Real.rpow_two, Nat.cast_one, Real.one_rpow] at h1
  norm_num at h1

/-- The package bound with `L = 1` at `h = 1/2`. -/
theorem length_constant_contrast :
    (1 / 2 : ℝ) ^ ((4 : ℝ) - 1 - 1) * (1 + 1 / (((1 : ℕ) : ℝ) / 1 * (1 / 2))) ≤
      (1 : ℝ) ^ ((4 : ℝ) - 1 - 1) * (1 : ℝ) ^ ((4 : ℝ) - 1 - 1) *
        ((((1 : ℕ) : ℝ)) ^ (-((4 : ℝ) - 1 - 1)) +
          (((1 : ℕ) : ℝ))⁻¹ * (((1 : ℕ) : ℝ)) ^ (-((4 : ℝ) - 1 - 1 - 1))) :=
  StratonovichHAMSecondMoment.IntervalScalar.singleton_weight_le (k := 1) (i := 1)
    (by norm_num) (by norm_num) (by norm_num) le_rfl le_rfl le_rfl (by norm_num)

end Refutations.IntervalScalar
