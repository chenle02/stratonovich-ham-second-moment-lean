/-
Refutation for the support of the `d = 3` wave Green measure, package theorem
`StratonovichHAMSecondMoment.WaveGreen.waveGreen_compl_closedBall`
(support in the closed radius-`s` ball, notation list line 102).

Wrong variant: a smaller support radius, `G_s((closedBall 0 (s/2))ᶜ) = 0` for all
`s > 0`.  In `d = 3` all the mass sits on the sphere of radius `s`.
Counterexample: `s = 1`: the complement of the radius-`1/2` ball has the full
mass `1`.  `half_radius_support_contrast` is the package support statement at
the same point.  No junk-value reliance.

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.WaveGreen

set_option autoImplicit false

open MeasureTheory Set Metric StratonovichHAMSecondMoment.WaveGreen
open StratonovichHAMSecondMoment.HomogHypothesis

namespace Refutations.WaveGreen

/-- The `d = 3` wave Green measure is not supported in the half-radius ball. -/
theorem half_radius_support_refuted :
    ¬ (∀ s : ℝ, 0 < s → waveGreen 3 s (closedBall (0 : Rd 3) (s / 2))ᶜ = 0) := by
  intro h
  have h1 := h 1 one_pos
  have hpre : ((fun ω : sphere (0 : Rd 3) 1 => (1 : ℝ) • (ω : Rd 3)) ⁻¹'
      (closedBall (0 : Rd 3) (1 / 2))ᶜ) = univ := by
    ext ω
    simp only [one_smul, mem_preimage, mem_compl_iff, mem_closedBall, dist_zero_right,
      norm_eq_of_mem_sphere, mem_univ, iff_true, not_le]
    norm_num
  have hm : waveGreen 3 1 (closedBall (0 : Rd 3) (1 / 2))ᶜ = waveGreen 3 1 univ := by
    simp only [waveGreen, Measure.smul_apply, smul_eq_mul]
    rw [Measure.map_apply (by fun_prop) measurableSet_closedBall.compl,
      Measure.map_apply (by fun_prop) MeasurableSet.univ, hpre, preimage_univ]
  rw [hm, mass_three 1 one_pos] at h1
  simp at h1

/-- The package support statement at the counterexample point `s = 1`. -/
theorem half_radius_support_contrast : waveGreen 3 1 (closedBall (0 : Rd 3) 1)ᶜ = 0 :=
  waveGreen_compl_closedBall 3 1

end Refutations.WaveGreen
