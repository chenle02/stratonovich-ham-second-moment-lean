/-
Refutation for the `d = 1` Green-kernel normalization of `DiagramModel` (main
TeX line 952 at edf7085f: `G(s,y) = ½ 1_{|y|<s}`, of mass `s`), package
definitions `StratonovichHAMSecondMoment.DiagramModel.green1` and theorem
`waveGreen_one_eq`.

Wrong variant: the kernel `1_{|y|<s}` (without the factor `½`).
Counterexample: `s = 1`: the unnormalized kernel has mass `2`, while the wave
Green measure `G_1` has mass `1`; every diagram with `m + n` vertices would be
multiplied by `2^{m+n}`.  `greenNormalization_contrast` is the package mass at
the same point.
Class (a): manuscript-claim perturbation in the manuscript domain.
No junk-value reliance (lower Lebesgue integrals).

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.DiagramModel

set_option autoImplicit false

open MeasureTheory StratonovichHAMSecondMoment DiagramModel
open scoped ENNReal

namespace Refutations.DiagramModel

/-- The package: the kernel `green1 1` has mass `1`. -/
theorem greenNormalization_contrast :
    (volume.withDensity (green1 1)) Set.univ = ENNReal.ofReal 1 := by
  rw [← waveGreen_one_eq]
  exact WaveGreen.waveGreen_mass 1 (Or.inl rfl) 1 zero_le_one

/-- The unnormalized kernel `1_{|y|<1}` does not have mass `1`. -/
theorem greenNormalization_refuted :
    ¬ ((volume : Measure (HomogHypothesis.Rd 1)).withDensity
        ((Metric.ball (0 : HomogHypothesis.Rd 1) 1).indicator 1) Set.univ = ENNReal.ofReal 1) := by
  intro h
  have hc := greenNormalization_contrast
  rw [show green1 1 = (Metric.ball (0 : HomogHypothesis.Rd 1) 1).indicator
      (fun _ => ENNReal.ofReal (1 / 2)) from rfl,
    withDensity_indicator Metric.isOpen_ball.measurableSet, withDensity_const] at hc
  rw [withDensity_indicator Metric.isOpen_ball.measurableSet,
    show (1 : HomogHypothesis.Rd 1 → ℝ≥0∞) = fun _ => 1 from rfl, withDensity_const,
    one_smul] at h
  simp only [Measure.smul_apply, smul_eq_mul] at hc
  simp only [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter] at hc h
  rw [h, ← ENNReal.ofReal_mul (by norm_num),
    ENNReal.ofReal_eq_ofReal_iff (by norm_num) (by norm_num)] at hc
  norm_num at hc

end Refutations.DiagramModel
