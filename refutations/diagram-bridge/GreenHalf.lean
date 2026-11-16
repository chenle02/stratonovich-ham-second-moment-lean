/-
Refutation for the `d = 1` Green normalization in the positions/increments
bridge of `DiagramBridge` (main TeX lines 952 and 5351-5355 at 39f2597a:
`G(h, y) = ½ 1_{|y|<h}`), package theorem
`StratonovichHAMSecondMoment.DiagramBridge.spatial_waveGreen_one_eq_spatialPos`.

Wrong variant: the bridge with the positions kernel `1_{|y|<h}` (the factor `½`
dropped).  Counterexample: `m = n = 1`, the pairing `D = (0 1)`, the covariance
`γ ≡ 1` and `h = (1, 1)`: the increments form is `1` (two Green masses `1`), the
unnormalized positions form is `4 = 2^2`.  `greenHalf_contrast` is the package
bridge at the same point together with its value `1`.
Control of the broader Lean generalization (the bridge for every covariance
`γ : ℝ¹ → [0, ∞]`), outside the manuscript's covariance class: `γ ≡ 1` has degree
`α = 0`, while the manuscript requires an even positive-definite homogeneous covariance
with `α > 0` (main TeX lines 386-399).
No junk-value reliance (lower Lebesgue integrals).

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.DiagramBridge

set_option autoImplicit false

open MeasureTheory StratonovichHAMSecondMoment DiagramModel DiagramBridge
open scoped ENNReal

namespace Refutations.DiagramBridge

/-- The kernel `1_{|y|<s}` without the factor `½`. -/
noncomputable def green1Unnorm (s : ℝ) (y : HomogHypothesis.Rd 1) : ℝ≥0∞ :=
  (Metric.ball (0 : HomogHypothesis.Rd 1) s).indicator (fun _ => 1) y

/-- The pairing `{1, 2}` of the two one-vertex chains. -/
def swap01 : Fin (1 + 1) → Fin (1 + 1) := ⇑(Equiv.swap (0 : Fin (1 + 1)) 1)

theorem green1Unnorm_eq (s : ℝ) (y : HomogHypothesis.Rd 1) :
    green1Unnorm s y = 2 * green1 s y := by
  by_cases hy : y ∈ Metric.ball (0 : HomogHypothesis.Rd 1) s
  · simp only [green1Unnorm, green1, Set.indicator_of_mem hy]
    rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num)]
    norm_num
  · simp [green1Unnorm, green1, Set.indicator_of_notMem hy]

/-- The package increments form at the counterexample point is `1`. -/
theorem spatial_one :
    spatial (WaveGreen.waveGreen 1) (fun _ => 1) 1 swap01 (fun _ => 1) = 1 := by
  unfold spatial covWeight
  simp only [Finset.prod_const_one, lintegral_const, one_mul, Measure.pi_univ]
  simp [WaveGreen.waveGreen_mass 1 (Or.inl rfl) 1 zero_le_one]

/-- The package: the bridge holds at the counterexample point, with value `1`. -/
theorem greenHalf_contrast :
    spatial (WaveGreen.waveGreen 1) (fun _ => 1) 1 swap01 (fun _ => 1) =
        spatialPos green1 (fun _ => 1) 1 swap01 (fun _ => 1) ∧
      spatialPos green1 (fun _ => 1) 1 swap01 (fun _ => 1) = 1 := by
  have h := spatial_waveGreen_one_eq_spatialPos (fun _ => 1) 1 swap01 (fun _ => 1)
  exact ⟨h, h ▸ spatial_one⟩

/-- Without the factor `½` the positions form is not the increments form. -/
theorem greenHalf_refuted :
    ¬ (spatial (WaveGreen.waveGreen 1) (fun _ => 1) 1 swap01 (fun _ => 1) =
        spatialPos green1Unnorm (fun _ => 1) 1 swap01 (fun _ => 1)) := by
  intro h
  have h1 := greenHalf_contrast.2
  have h4 : spatialPos green1Unnorm (fun _ => 1) 1 swap01 (fun _ => 1) =
      4 * spatialPos green1 (fun _ => 1) 1 swap01 (fun _ => 1) := by
    unfold spatialPos
    rw [← lintegral_const_mul' _ _ (by norm_num)]
    refine lintegral_congr fun y => ?_
    simp only [green1Unnorm_eq, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin]
    norm_num [mul_assoc]
  rw [h4, h1, spatial_one] at h
  norm_num at h

end Refutations.DiagramBridge
