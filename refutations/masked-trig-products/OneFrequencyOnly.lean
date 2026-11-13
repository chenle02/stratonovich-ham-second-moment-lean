/-
Refutation for the frequency count in `L:masked-trig-products` (TeX
l. 371-373: two modes have `|r-ρ|`, two have `r+ρ`), package theorem
`StratonovichHAMSecondMoment.MaskedTrigProducts.sum_bracket_freq` and
definition `frequencyPair`.

Wrong variant: every one of the four mode brackets `⟨h · freq r ρ j⟩^{a-1}`
(package `bracket` and `freq`) is bounded by the single `r+ρ` bracket
`⟨h(r+ρ)⟩^{a-1}`, under the manuscript's sign conditions. This is a strictly
more faithful form of the earlier Mathlib-only variant (which compared only the
`r-ρ` bracket); the `r-ρ` bracket is the mode `j = (true, false)`. Witness
`a = 0`, `h = 1`, `r = ρ = 1`, `j = (true, false)`: the mode has frequency `0`
and `⟨0⟩^{-1} = 1`, while `⟨2⟩^{-1} = 1/√5 < 1`. The contrast theorem shows
that the package's `frequencyPair` does dominate that `r-ρ` bracket at the same
point.

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.MaskedTrigProducts

set_option autoImplicit false

namespace Refutations.MaskedTrigProducts

open StratonovichHAMSecondMoment.MaskedTrigProducts

/-- The four mode brackets are not all bounded by the `r+ρ` bracket. -/
theorem one_frequency_only :
    ¬ ∀ (a h r ρ : ℝ), 0 ≤ a → a < 1 → 0 < h → h ≤ 1 → 0 ≤ r → 0 ≤ ρ →
      ∀ j : Bool × Bool,
        bracket (h * freq r ρ j) ^ (a - 1) ≤ bracket (h * (r + ρ)) ^ (a - 1) := by
  intro hall
  have h1 := hall 0 1 1 1 le_rfl (by norm_num) one_pos le_rfl zero_le_one zero_le_one
    (true, false)
  simp only [bracket, freq, sgn] at h1
  norm_num at h1
  have h5 : (1 : ℝ) < Real.sqrt 5 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have : (Real.sqrt 5)⁻¹ < 1 := inv_lt_one_of_one_lt₀ h5
  rw [Real.rpow_neg_one] at h1
  linarith

/-- Contrast: at the counterexample point, the package's `frequencyPair`
(which carries the `r-ρ` bracket) dominates the `r-ρ` mode bracket. -/
theorem one_frequency_only_contrast :
    bracket (1 * freq 1 1 (true, false)) ^ ((0 : ℝ) - 1) ≤ frequencyPair 0 1 1 1 := by
  have hf : freq 1 1 (true, false) = 1 - 1 := by simp [freq, sgn]
  rw [hf, frequencyPair, le_add_iff_nonneg_right]
  exact Real.rpow_nonneg (Real.sqrt_nonneg _) _

end Refutations.MaskedTrigProducts
