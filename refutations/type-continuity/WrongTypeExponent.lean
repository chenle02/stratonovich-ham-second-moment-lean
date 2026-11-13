/-
Refutation for `L:positive-series-type` (main TeX lines 7222-7234), package
theorem
`StratonovichHAMSecondMoment.TypeContinuity.positive_series_type_paper`
(`τ = ν K^{1/ν}`, equivalently `K = (τ/ν)^ν`).

Wrong variant: the exponent inverted, `τ = ν K^ν`, under the same
hypotheses. Counterexample: `ν = 2`, `c_k = 4^k/(k!)^2`: `K = 4`
(`coeffType_exp_family`) and the package gives `τ = 2 · 4^{1/2} = 4`
(`seriesType_exp_family`), while `ν K^ν = 32`.
`wrong_type_exponent_contrast` is the package value at the same family.
No junk-value reliance.

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.TypeContinuity

set_option autoImplicit false

open scoped Nat

namespace Refutations.TypeContinuity

open StratonovichHAMSecondMoment.TypeContinuity

/-- `τ = ν K^ν` (inverted exponent) is false. -/
theorem wrong_type_exponent_refuted :
    ¬ (∀ ν : ℝ, 1 ≤ ν → ∀ c : ℕ → ℝ, (∀ k, 0 ≤ c k) → c 0 = 1 →
        (∀ z : ℝ, 0 ≤ z → Summable (fun k => c k * z ^ k)) →
        seriesType ν c < ⊤ →
          seriesType ν c = ((ν * (coeffType ν c).toReal ^ ν : ℝ) : EReal)) := by
  intro h
  obtain ⟨hc, hc0, hF, hτ⟩ :=
    seriesType_exp_family (ν := 2) (A := 4) (by norm_num) (by norm_num)
  have hK := coeffType_exp_family 2 (A := 4) (by norm_num)
  have hwrong := h 2 (by norm_num) _ hc hc0 hF (by rw [hτ]; exact EReal.coe_lt_top _)
  rw [hτ, hK, ENNReal.toReal_ofReal (by norm_num)] at hwrong
  have h1 := EReal.coe_injective hwrong
  have h2 : (4 : ℝ) ^ (1 / (2 : ℝ)) = 2 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
    norm_num
  rw [h2, Real.rpow_two] at h1
  norm_num at h1

/-- The package value at the same family: `τ = 2 · 4^{1/2}`. -/
theorem wrong_type_exponent_contrast :
    seriesType 2 (fun k => (4 : ℝ) ^ k / (k ! : ℝ) ^ (2 : ℝ)) =
      (((2 : ℝ) * (4 : ℝ) ^ (1 / (2 : ℝ)) : ℝ) : EReal) :=
  (seriesType_exp_family (by norm_num) (by norm_num)).2.2.2

end Refutations.TypeContinuity
