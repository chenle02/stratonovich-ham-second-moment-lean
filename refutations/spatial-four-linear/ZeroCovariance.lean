/-
Refutation for the positivity claim of `P:spatial-four-linear`
(`notes/integrated_spatial_occupation.tex` line 236 at a284420: every nonzero `H¹` profile has
`A_sp(f) > 0`), package theorem `StratonovichHAMSecondMoment.SpatialFourLinear.pairing_sq_pos`,
which assumes `Γ ≠ 0` (the section's standing nonzero covariance, line 4).

Wrong variant: positivity with the hypothesis `Γ ≠ 0` dropped.  Counterexample: `Γ = 0` on
`ℝ¹` and the constant profile `f = 1` (not a.e. zero): `ν = dx ⊗ 0 = 0`, so `A_sp(f) = 0`.
No junk-value reliance (the pairing is a `[0,∞]` lower integral against the zero measure).
`zero_covariance_contrast` is the package theorem for `Γ = volume` (nonzero, with the set
scaling at `α = d = 1`) at the same profile.

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.SpatialFourLinear

set_option autoImplicit false

open MeasureTheory StratonovichHAMSecondMoment StratonovichHAMSecondMoment.SpatialFourLinear

namespace Refutations.SpatialFourLinear

theorem one_not_ae_zero : ¬ (fun _ : HomogHypothesis.Rd 1 => (1 : ℝ)) =ᵐ[volume] 0 := by
  intro h
  have : (volume : Measure (HomogHypothesis.Rd 1)) Set.univ = 0 := by
    rw [Filter.EventuallyEq, ae_iff] at h
    simp at h
  have hne : (volume : Measure (HomogHypothesis.Rd 1)) Set.univ ≠ 0 := by
    rw [measure_univ_of_isAddLeftInvariant]; exact ENNReal.top_ne_zero
  exact hne this

/-- Positivity of `A_sp` without `Γ ≠ 0` is false. -/
theorem zero_covariance_refuted :
    ¬ (∀ f : HomogHypothesis.Rd 1 → ℝ, AEStronglyMeasurable f volume → ¬ f =ᵐ[volume] 0 →
      0 < OccupationKernelRow.pairing (0 : Measure (HomogHypothesis.Rd 1))
        (SpatialStaticControls.zE fun x => f x ^ 2)
        (SpatialStaticControls.zE fun x => f x ^ 2)) := by
  intro h
  have := h (fun _ => 1) aestronglyMeasurable_const one_not_ae_zero
  simp [OccupationKernelRow.pairing, OccupationKernelRow.pairMeasure] at this

/-- The package theorem at the same profile for `Γ = volume` on `ℝ¹` (nonzero, set scaling
with exponent `α = 0`). -/
theorem zero_covariance_contrast :
    0 < OccupationKernelRow.pairing (volume : Measure (HomogHypothesis.Rd 1))
      (SpatialStaticControls.zE fun _ => (1 : ℝ) ^ 2)
      (SpatialStaticControls.zE fun _ => (1 : ℝ) ^ 2) := by
  have hS : VariationalDilation.SetScaling 0 (volume : Measure (HomogHypothesis.Rd 1)) := by
    intro A _ c hc
    rw [Measure.addHaar_smul, finrank_euclideanSpace, Fintype.card_fin, pow_one, abs_of_pos hc]
    norm_num
  have hne : (volume : Measure (HomogHypothesis.Rd 1)) ≠ 0 := by
    intro h0
    have := measure_univ_of_isAddLeftInvariant (μ := (volume : Measure (HomogHypothesis.Rd 1)))
    rw [h0] at this
    exact ENNReal.zero_ne_top this
  exact pairing_sq_pos hS hne (f := fun _ => (1 : ℝ)) aestronglyMeasurable_const one_not_ae_zero

end Refutations.SpatialFourLinear
