/-
Refutation for Archimedes' law of `WaveGreenFourier`, package theorem
`StratonovichHAMSecondMoment.WaveGreenFourier.archimedes` (for `‖e‖ = 1`, the
image of `σ = volume.toSphere` under `ω ↦ ⟪e,ω⟫` is `2π · Lebesgue` on `[-1,1]`).

Wrong variant: the law with the hypothesis `‖e‖ = 1` dropped.  Counterexample:
`e = 0`; the image is then `σ(S²) δ₀ = 4π δ₀`, which charges `{0}`, while
`2π · Lebesgue` on `[-1,1]` gives `{0}` mass `0`.  The proof uses the package
law at a unit vector to get `σ(S²) = 4π ≠ 0`.
No junk-value reliance.

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.WaveGreenFourier

set_option autoImplicit false

open MeasureTheory Real Set

namespace Refutations.WaveGreenFourier

open StratonovichHAMSecondMoment StratonovichHAMSecondMoment.HomogHypothesis
  StratonovichHAMSecondMoment.WaveGreenFourier

/-- Archimedes' law fails without `‖e‖ = 1` (at `e = 0`). -/
theorem archimedes_unit_refuted :
    ¬ (∀ e : Rd 3, ((volume : Measure (Rd 3)).toSphere).map
        (fun ω : Metric.sphere (0 : Rd 3) 1 => inner ℝ e (ω : Rd 3)) =
      ENNReal.ofReal (2 * π) • (volume : Measure ℝ).restrict (Icc (-1) 1)) := by
  intro h
  have h0 := congrArg (fun ν : Measure ℝ => ν {0}) (h 0)
  simp only [inner_zero_left] at h0
  rw [Measure.map_apply (by fun_prop) (measurableSet_singleton 0)] at h0
  have hz : ((volume : Measure ℝ).restrict (Icc (-1) 1)) {0} = 0 := by
    rw [Measure.restrict_apply (measurableSet_singleton 0)]
    exact measure_mono_null inter_subset_left Real.volume_singleton
  simp only [preimage_const, mem_singleton_iff, ite_true, Measure.smul_apply, hz,
    smul_eq_mul, mul_zero] at h0
  exact (Measure.toSphere_ne_zero (μ := (volume : Measure (Rd 3))))
    (Measure.measure_univ_eq_zero.1 h0)

end Refutations.WaveGreenFourier
