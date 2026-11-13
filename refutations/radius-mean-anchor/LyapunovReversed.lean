/-
Refutation for the Lyapunov step of `P:radius-mean-anchor`, package theorem
`StratonovichHAMSecondMoment.RadiusMeanAnchor.lyapunov_mean_le`.

Wrong variant: `lyapunov_mean_le` with its inequality reversed,
`(𝔼 Z^p)^{1/p} ≤ 𝔼 Z`, all binders and hypotheses (including
`[IsProbabilityMeasure μ]`) and the integrability conjunct as in the
package theorem. Witness: the fair coin on `Bool`, `Z = 1` on `true`, `0` on `false`,
p = 2: 𝔼 Z = 1/2 but (𝔼 Z²)^{1/2} = (1/2)^{1/2} > 1/2. The contrast theorem
applies `lyapunov_mean_le` at the same point, where the forward inequality
holds. (`coin` below is a witness measure, not a package definition.)

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.RadiusMeanAnchor

set_option autoImplicit false

open MeasureTheory

namespace Refutations.RadiusMeanAnchor

/-- The fair coin. -/
noncomputable def coin : Measure Bool :=
  (2⁻¹ : ENNReal) • (Measure.dirac true + Measure.dirac false)

theorem coin_integral (f : Bool → ℝ) : ∫ b, f b ∂coin = (f true + f false) / 2 := by
  unfold coin
  rw [integral_smul_measure, integral_add_measure (Integrable.of_finite)
    (Integrable.of_finite), integral_dirac, integral_dirac]
  simp [ENNReal.toReal_inv]
  ring

instance coin_prob : IsProbabilityMeasure coin := by
  constructor
  unfold coin
  simp only [Measure.smul_apply, Measure.add_apply, measure_univ, smul_eq_mul]
  rw [one_add_one_eq_two, ENNReal.inv_mul_cancel (by norm_num) (by norm_num)]

/-- The indicator of `true`. -/
noncomputable def coinZ : Bool → ℝ := fun b => if b then 1 else 0

/-- Lyapunov's inequality cannot be reversed. -/
theorem lyapunov_reversed :
    ¬ ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (Z : Ω → ℝ) (p : ℝ), 1 ≤ p → (∀ ω, 0 ≤ Z ω) → AEStronglyMeasurable Z μ →
      Integrable (fun ω => Z ω ^ p) μ →
      Integrable Z μ ∧ (∫ ω, Z ω ^ p ∂μ) ^ (1 / p) ≤ ∫ ω, Z ω ∂μ := by
  intro h
  have := (@h Bool _ coin coin_prob coinZ 2 (by norm_num)
    (fun b => by cases b <;> simp [coinZ]) Integrable.of_finite.aestronglyMeasurable
    Integrable.of_finite).2
  rw [coin_integral, coin_integral] at this
  simp only [coinZ] at this
  norm_num at this
  -- this : (1/2)^(1/2) ≤ 1/2, i.e. √(1/2) ≤ 1/2
  rw [← Real.sqrt_eq_rpow] at this
  have h2 : (1 / 2 : ℝ) < Real.sqrt (1 / 2) := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  linarith

/-- Contrast: the package theorem `lyapunov_mean_le` (forward inequality)
holds at the witness. -/
theorem lyapunov_reversed_contrast :
    Integrable coinZ coin ∧
      ∫ b, coinZ b ∂coin ≤ (∫ b, coinZ b ^ (2 : ℝ) ∂coin) ^ (1 / (2 : ℝ)) :=
  StratonovichHAMSecondMoment.RadiusMeanAnchor.lyapunov_mean_le coin coinZ 2
    (by norm_num) (fun b => by cases b <;> simp [coinZ])
    Integrable.of_finite.aestronglyMeasurable Integrable.of_finite

end Refutations.RadiusMeanAnchor
