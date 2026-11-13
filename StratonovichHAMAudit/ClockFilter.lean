module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false

open MeasureTheory Filter

namespace StratonovichHAMAudit.ClockFilter

theorem resolvent_partial_fraction (θ ell r : ℝ) (hθ : 0 < θ) (hell : 0 < ell) :
    (2 * θ + ell) / (2 * θ * (θ ^ 2 + r ^ 2) * ((θ + ell) ^ 2 + r ^ 2)) =
      (1 / (θ ^ 2 + r ^ 2) - 1 / ((θ + ell) ^ 2 + r ^ 2)) / (2 * θ * ell) := by
  have hA : θ ^ 2 + r ^ 2 ≠ 0 := ne_of_gt (by positivity)
  have hB : (θ + ell) ^ 2 + r ^ 2 ≠ 0 := ne_of_gt (by positivity)
  field_simp [hθ.ne', hell.ne', hA, hB]
  ring

theorem clock_filter_bounds (θ ell : ℝ) (hθ : 0 < θ) (hell : 0 < ell) :
    0 < 2 * θ / (2 * θ + ell) ∧ 2 * θ / (2 * θ + ell) < 1 := by
  have hden : 0 < 2 * θ + ell := by linarith
  constructor
  · exact div_pos (by linarith) hden
  · exact (div_lt_one hden).2 (by linarith)

theorem strict_filter_integral (θ : ℝ) (hθ : 0 < θ)
    (σ : Measure ℝ) (hσ : σ ≠ 0)
    (hell : ∀ᵐ ell ∂σ, 0 < ell)
    (w : ℝ → ℝ) (hw : Integrable w σ)
    (hwpos : ∀ᵐ ell ∂σ, 0 < w ell) :
    Integrable (fun ell => 2 * θ / (2 * θ + ell) * w ell) σ ∧
      (∫ ell, 2 * θ / (2 * θ + ell) * w ell ∂σ) < ∫ ell, w ell ∂σ := by
  let f : ℝ → ℝ := fun ell => 2 * θ / (2 * θ + ell) * w ell
  have hmeas : Measurable (fun ell : ℝ => 2 * θ / (2 * θ + ell)) :=
    measurable_const.div (measurable_const.add measurable_id)
  have hfm : AEStronglyMeasurable f σ :=
    hmeas.aestronglyMeasurable.mul hw.aestronglyMeasurable
  have hnonneg : ∀ᵐ ell ∂σ, 0 ≤ f ell := by
    filter_upwards [hell, hwpos] with ell hell0 hw0
    exact (mul_pos (clock_filter_bounds θ ell hθ hell0).1 hw0).le
  have hstrict : ∀ᵐ ell ∂σ, f ell < w ell := by
    filter_upwards [hell, hwpos] with ell hell0 hw0
    calc
      f ell = 2 * θ / (2 * θ + ell) * w ell := rfl
      _ < 1 * w ell := mul_lt_mul_of_pos_right
        (clock_filter_bounds θ ell hθ hell0).2 hw0
      _ = w ell := one_mul _
  have hle : f ≤ᵐ[σ] w := hstrict.mono fun _ h => h.le
  have hfi : Integrable f σ := hw.mono_nonneg hfm hnonneg hle
  have hIntLe : (∫ ell, f ell ∂σ) ≤ ∫ ell, w ell ∂σ :=
    integral_mono_ae hfi hw hle
  have hne : (∫ ell, f ell ∂σ) ≠ ∫ ell, w ell ∂σ := by
    intro heq
    have hae : f =ᵐ[σ] w := (integral_eq_iff_of_ae_le hfi hw hle).1 heq
    let : (ae σ).NeBot := ae_neBot.2 hσ
    obtain ⟨ell, hlt, heqell⟩ := (hstrict.and hae).exists
    exact (ne_of_lt hlt) heqell
  refine ⟨hfi, ?_⟩
  exact lt_of_le_of_ne hIntLe hne

end StratonovichHAMAudit.ClockFilter
