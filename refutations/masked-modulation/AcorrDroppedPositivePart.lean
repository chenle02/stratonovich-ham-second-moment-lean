/-
Refutation for `StratonovichHAMSecondMoment.MaskedModulation.acorr_bound`
(the bound `|c(v)| ≤ M²(h-v)_+` behind TeX line 318 of
`L:masked-temporal-modulation`).

Wrong variant: the bound with the positive part dropped,
`‖c(v)‖ ≤ M²(h - v)` for every real `v`. Witness `Φ = 0`, `s = 0`, `h = 1`,
`M = 1`, `v = 2`: the variant asserts a norm is at most `-1`. No junk value is
involved. The contrast theorem applies `acorr_bound` at the same point.

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.MaskedModulation

set_option autoImplicit false

namespace Refutations.MaskedModulation

open MeasureTheory Set StratonovichHAMSecondMoment.MaskedModulation

/-- `acorr_bound` without the positive part `max (h - v) 0` is false. -/
theorem acorr_dropped_positive_part :
    ¬ ∀ (Φ : ℝ → ℂ) (s h M v : ℝ), (∀ u ∉ Icc s (s + h), Φ u = 0) → (∀ u, ‖Φ u‖ ≤ M) →
      ‖acorr Φ v‖ ≤ M * M * (h - v) := by
  intro hv
  have := hv (fun _ => 0) 0 1 1 2 (fun _ _ => rfl) (fun _ => by simp)
  have h0 := norm_nonneg (acorr (fun _ => (0 : ℂ)) 2)
  norm_num at this
  linarith

/-- Contrast: the package bound at the counterexample point. -/
theorem acorr_dropped_positive_part_contrast :
    ‖acorr (fun _ => (0 : ℂ)) 2‖ ≤ 1 * 1 * max (1 - 2) 0 :=
  acorr_bound (s := 0) (h := 1) (fun _ _ => rfl) (fun _ => by simp) 2

end Refutations.MaskedModulation
