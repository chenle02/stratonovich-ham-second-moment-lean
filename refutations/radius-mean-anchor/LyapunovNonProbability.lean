/-
Refutation for the Lyapunov step of `P:radius-mean-anchor` ("Probability
normalization and Lyapunov give ..."), package theorem
`StratonovichHAMSecondMoment.RadiusMeanAnchor.lyapunov_mean_le`.

Wrong variant: `lyapunov_mean_le` with its hypothesis
`[IsProbabilityMeasure μ]` weakened to `[IsFiniteMeasure μ]`, all other
binders and hypotheses as in the package theorem. Witness: Ω = `Unit`,
μ = 4 · dirac, Z = 1, p = 2: ∫ Z = 4 but (∫ Z²)^{1/2} = 2 < 4. The
contrast theorem shows that the witness measure is not a probability measure, and
applies `lyapunov_mean_le` with the same Z and p to the probability measure
dirac on `Unit`, where it holds.

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.RadiusMeanAnchor

set_option autoImplicit false

open MeasureTheory

namespace Refutations.RadiusMeanAnchor

/-- Lyapunov's bound fails without the probability normalization. -/
theorem lyapunov_nonprobability :
    ¬ ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
      (Z : Ω → ℝ) (p : ℝ), 1 ≤ p → (∀ ω, 0 ≤ Z ω) → AEStronglyMeasurable Z μ →
      Integrable (fun ω => Z ω ^ p) μ →
      Integrable Z μ ∧ ∫ ω, Z ω ∂μ ≤ (∫ ω, Z ω ^ p ∂μ) ^ (1 / p) := by
  intro h
  have hfin : IsFiniteMeasure ((4 : ENNReal) • Measure.dirac ()) := ⟨by simp⟩
  have := (@h Unit _ ((4 : ENNReal) • Measure.dirac ()) hfin (fun _ => 1) 2
    (by norm_num) (fun _ => by norm_num) aestronglyMeasurable_const
    (integrable_const _)).2
  simp only [integral_smul_measure, integral_dirac, Real.one_rpow] at this
  norm_num at this

/-- Contrast: the witness measure `4 · dirac` is not a probability measure,
and the package theorem `lyapunov_mean_le` holds for `Z = 1`, `p = 2` under
the probability measure `dirac ()`. -/
theorem lyapunov_nonprobability_contrast :
    ¬ IsProbabilityMeasure ((4 : ENNReal) • Measure.dirac ()) ∧
      (Integrable (fun _ : Unit => (1 : ℝ)) (Measure.dirac ()) ∧
        ∫ _u, (1 : ℝ) ∂(Measure.dirac ()) ≤
          (∫ _u, (1 : ℝ) ^ (2 : ℝ) ∂(Measure.dirac ())) ^ (1 / (2 : ℝ))) := by
  have h4 : ((4 : ENNReal) • Measure.dirac ()) (Set.univ : Set Unit) = 4 := by simp
  refine ⟨fun hP => ?_, ?_⟩
  · have := hP.measure_univ
    rw [h4] at this
    norm_num at this
  · exact StratonovichHAMSecondMoment.RadiusMeanAnchor.lyapunov_mean_le
      (Measure.dirac ()) (fun _ => 1) 2 (by norm_num) (fun _ => by norm_num)
      aestronglyMeasurable_const (integrable_const _)

end Refutations.RadiusMeanAnchor
