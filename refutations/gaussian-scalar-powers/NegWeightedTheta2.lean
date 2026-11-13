import StratonovichHAMSecondMoment.GaussianScalarPowers

/-!
Refutation for `StratonovichHAMSecondMoment.GaussianScalarPowers.weighted_power`
(manuscript `L:gaussian-scalar-powers`, display `E:gaussian-weighted-power`):
the hypothesis `θ < 1` cannot be dropped.

The wrong variant is the package statement with `hθ1 : θ < 1` removed (same
binders and remaining hypotheses). Counterexample: `θ = 2`, `u = 1`, `v = 2`:
LHS `= 1 * 2^(-1) = 1/2`, RHS `= 2 - 2 = 0`.
The contrast theorem applies the package theorem at the same `u = 1`, `v = 2`
for every `θ ∈ (0, 1)` and records that `θ = 2` violates only `θ < 1`.

Expected outcome: compiles (refuted).
-/

set_option autoImplicit false

namespace Refutations.GaussianScalarPowers

/-- `weighted_power` without the hypothesis `θ < 1` is false. -/
theorem weighted_power_drop_theta_lt_one :
    ¬ (∀ (θ u v : ℝ), 0 < θ → 0 ≤ u → 0 ≤ v →
      u ^ θ * v ^ (1 - θ) ≤ θ * u + (1 - θ) * v) := by
  intro h
  have := h 2 1 2 (by norm_num) (by norm_num) (by norm_num)
  norm_num [Real.rpow_neg_one] at this

/-- Contrast: the counterexample `θ = 2` violates exactly the dropped hypothesis
`θ < 1`; at `u = 1`, `v = 2` the package theorem holds for every `θ ∈ (0, 1)`. -/
theorem weighted_power_drop_theta_lt_one_contrast :
    ¬ ((2 : ℝ) < 1) ∧ ∀ θ : ℝ, 0 < θ → θ < 1 →
      (1 : ℝ) ^ θ * (2 : ℝ) ^ (1 - θ) ≤ θ * 1 + (1 - θ) * 2 :=
  ⟨by norm_num, fun θ h0 h1 =>
    StratonovichHAMSecondMoment.GaussianScalarPowers.weighted_power θ 1 2 h0 h1
      (by norm_num) (by norm_num)⟩

end Refutations.GaussianScalarPowers
