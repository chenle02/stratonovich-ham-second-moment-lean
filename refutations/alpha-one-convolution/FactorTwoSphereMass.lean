import StratonovichHAMSecondMoment.AlphaOneConvolution

/-!
Refutation for the mass of the angular measure in the proof of
`L:alpha-one-convolution` (main TeX lines 5657-5659, "Its total mass is `V`"; and
lines 5683-5685, "introduces no factor two"), package theorem
`StratonovichHAMSecondMoment.AlphaOneConvolution.polar_decomposition`.

Wrong variant: `σ(S^{d-1}) = 2V` (a spurious factor two from counting antipodal
directions twice). Witness: Lebesgue measure on `ℝ¹`, which is locally finite and
satisfies `μ(cA) = cμ(A)` (`Measure.addHaar_smul`), with `0 < V < ∞`; the package
gives `σ(univ) = V`, so `V = 2V` would force `V ∈ {0, ∞}`. No junk value is involved.
The contrast theorem applies `polar_decomposition` at the witness.

Expected outcome: compiles (refuted).
-/

set_option autoImplicit false

open MeasureTheory Set Metric
open scoped Pointwise

namespace Refutations.AlphaOneConvolution

open StratonovichHAMSecondMoment.HomogHypothesis StratonovichHAMSecondMoment.SpectralHomog
  StratonovichHAMSecondMoment.AlphaOneConvolution

theorem lebesgue_one_homogeneous : SpectralHomogeneous (volume : Measure (Rd 1)) 1 := by
  intro A _ c hc
  rw [Measure.addHaar_smul, finrank_euclideanSpace_fin, pow_one, abs_of_pos hc,
    Real.rpow_one]

/-- Contrast: for Lebesgue measure on `ℝ¹`, `σ(univ) = V` with `0 < V < ∞`. -/
theorem factor_two_sphere_mass_contrast :
    sphereMeasure (volume : Measure (Rd 1)) univ = volume (closedBall (0 : Rd 1) 1) ∧
      0 < volume (closedBall (0 : Rd 1) 1) ∧ volume (closedBall (0 : Rd 1) 1) < ⊤ :=
  ⟨(polar_decomposition lebesgue_one_homogeneous).2.2.1,
    measure_closedBall_pos _ _ one_pos, measure_closedBall_lt_top⟩

/-- The wrong variant `σ(univ) = 2V` is false. -/
theorem factor_two_sphere_mass :
    ¬ ∀ μ : Measure (Rd 1), IsLocallyFiniteMeasure μ → SpectralHomogeneous μ 1 →
      sphereMeasure μ univ = 2 * μ (closedBall 0 1) := by
  intro H
  obtain ⟨h1, h2, h3⟩ := factor_two_sphere_mass_contrast
  have h := H volume inferInstance lebesgue_one_homogeneous
  rw [h1] at h
  set V := volume (closedBall (0 : Rd 1) 1)
  have hV0 : V ≠ 0 := h2.ne'
  have hVt : V ≠ ⊤ := h3.ne
  have : (1 : ENNReal) * V = 2 * V := by rw [one_mul]; exact h
  have := (ENNReal.mul_left_inj hV0 hVt).1 this
  norm_num at this

end Refutations.AlphaOneConvolution
