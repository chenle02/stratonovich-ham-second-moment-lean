import StratonovichHAMSecondMoment.DampedSmoothing

/-!
Refutation for a strengthening of
`StratonovichHAMSecondMoment.DampedSmoothing.spectralMeasure_unique` (uniqueness of the
tempered spectral measure, used for the covariance-smoothing assertion of
`L:damped-homogeneous-norms`, main TeX lines 1052-1053): uniqueness holds for the
measure `mμ`, not for the multiplier function `m`.

Class (b), Lean-route-only control (the TeX makes no claim about the function `m`):
with `Γ = 0` and `μ = 0` on `ℝ¹`, both `0 · μ` and `1 · μ` are (equal) tempered
spectral measures, while the multipliers `0` and `1` differ.

Wrong variant: two multipliers giving spectral measures of the same covariance are equal.

Expected outcome: compiles (refuted).
-/

set_option autoImplicit false

open MeasureTheory

namespace Refutations.DampedSmoothing

open StratonovichHAMSecondMoment StratonovichHAMSecondMoment.DampedSmoothing
open HomogHypothesis (Rd IsSpectralMeasure IsTempered)
open DampedNormsHomog (smoothed)

/-- Contrast: with `μ = 0`, `0 · μ` and `1 · μ` are both spectral measures of `Γ = 0`,
equal as measures (`spectralMeasure_unique`), while `(0 : ℝ¹ → ℝ≥0) ≠ 1`. -/
theorem multiplier_not_unique_contrast :
    IsSpectralMeasure (0 : Measure (Rd 1)) (smoothed 0 0) ∧
      IsSpectralMeasure (0 : Measure (Rd 1)) (smoothed 0 1) ∧
      smoothed (0 : Measure (Rd 1)) 0 = smoothed 0 1 ∧
      (0 : Rd 1 → NNReal) ≠ 1 := by
  have h0 : IsSpectralMeasure (0 : Measure (Rd 1)) (smoothed 0 0) := fun φ => by
    simp [smoothed]
  have h1 : IsSpectralMeasure (0 : Measure (Rd 1)) (smoothed 0 1) := fun φ => by
    simp [smoothed]
  have ht : ∀ m : Rd 1 → NNReal, IsTempered (smoothed (0 : Measure (Rd 1)) m) :=
    fun m => ⟨0, by simp [smoothed]⟩
  refine ⟨h0, h1, spectralMeasure_unique (ht 0) (ht 1) h0 h1, fun h => ?_⟩
  have := congrFun h 0
  simp at this

/-- The wrong variant (uniqueness of the multiplier function) is false. -/
theorem multiplier_not_unique :
    ¬ ∀ (Γ μ : Measure (Rd 1)) (m₁ m₂ : Rd 1 → NNReal),
      IsSpectralMeasure Γ (smoothed μ m₁) → IsSpectralMeasure Γ (smoothed μ m₂) → m₁ = m₂ := by
  intro H
  obtain ⟨h0, h1, -, hne⟩ := multiplier_not_unique_contrast
  exact hne (H 0 0 0 1 h0 h1)

end Refutations.DampedSmoothing
