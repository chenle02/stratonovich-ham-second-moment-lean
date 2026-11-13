/-
Refutation for `L:positive-series-type` (main TeX lines 7222-7234), package
theorem
`StratonovichHAMSecondMoment.TypeContinuity.positive_series_type_paper`
(`τ = ν K^{1/ν}`).

Wrong variant: the identity without the factor `ν`, `τ = K^{1/ν}`, under the
same hypotheses. Counterexample: `ν = 2`, `c_k = 1/(k!)^2`: the package
(through `seriesType_exp_family` at `A = 1`) gives `τ = 2`, while
`K = 1` (`coeffType_exp_family`), so `K^{1/2} = 1 ≠ 2`.
`missing_nu_factor_contrast` is the package value at the same family.
No junk-value reliance: `τ` is finite and computed by the package, and
`K = 1` is a genuine limit.

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.TypeContinuity

set_option autoImplicit false

open scoped Nat

namespace Refutations.TypeContinuity

open StratonovichHAMSecondMoment.TypeContinuity

/-- `τ = K^{1/ν}` (dropping the factor `ν`) is false. -/
theorem missing_nu_factor_refuted :
    ¬ (∀ ν : ℝ, 1 ≤ ν → ∀ c : ℕ → ℝ, (∀ k, 0 ≤ c k) → c 0 = 1 →
        (∀ z : ℝ, 0 ≤ z → Summable (fun k => c k * z ^ k)) →
        seriesType ν c < ⊤ →
          seriesType ν c = (((coeffType ν c).toReal ^ (1 / ν) : ℝ) : EReal)) := by
  intro h
  obtain ⟨hc, hc0, hF, hτ⟩ := seriesType_exp_family (ν := 2) (A := 1) (by norm_num) zero_le_one
  have hK := coeffType_exp_family 2 (A := 1) zero_le_one
  have hwrong := h 2 (by norm_num) _ hc hc0 hF (by rw [hτ]; exact EReal.coe_lt_top _)
  rw [hτ, hK, ENNReal.toReal_ofReal zero_le_one] at hwrong
  have := EReal.coe_injective hwrong
  norm_num at this

/-- The package value at the same family: `τ = 2 · 1^{1/2}`. -/
theorem missing_nu_factor_contrast :
    seriesType 2 (fun k => (1 : ℝ) ^ k / (k ! : ℝ) ^ (2 : ℝ)) =
      (((2 : ℝ) * (1 : ℝ) ^ (1 / (2 : ℝ)) : ℝ) : EReal) :=
  (seriesType_exp_family (by norm_num) zero_le_one).2.2.2

end Refutations.TypeContinuity
