/-
Refutation for the Schur bound of `E:positive-bochner-inclusion`, package theorem
`StratonovichHAMSecondMoment.OccupationCompletion.positive_bochner_inclusion` (third conclusion,
`‖J_G F‖² ≤ K_0 ‖F‖²`, `K_0 = 2^a/(1-a)`; `L:positive-raw-embedding`,
`integrated_intrinsic_constant.tex` lines 27-31 at edf7085f).

Wrong variant (class (a), manuscript-claim perturbation in the manuscript domain): the constant
`K_0` replaced by `1`.  Counterexample: `G = ℝ`, `F = 1` on `I = (0,1)`, any `0 < a < 1`:
`‖F‖² = 1` and `‖J F‖² = ∫∫_{I²} |s-t|^{-a} = 2/((1-a)(2-a)) > 1`.  No junk-value reliance (the
kernel integrand is integrable, `SpaceTimePositivity.kern_integrable`).
`schur_constant_one_contrast` is the package bound with `K_0`.

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.OccupationCompletion

set_option autoImplicit false

open MeasureTheory Set
open scoped RealInnerProductSpace
open StratonovichHAMSecondMoment SpaceTimePositivity TimeSchur OccupationCompletion

namespace Refutations.OccupationCompletion

/-- `∫∫_{I²} |s-t|^{-a} = 2/((1-a)(2-a))` for `a < 1`. -/
theorem integral_kern_eq {a : ℝ} (ha1 : a < 1) :
    ∫ q, kern a (q.1 - q.2) ∂(timeMeasure.prod timeMeasure) = 2 / ((1 - a) * (2 - a)) := by
  have h1 := TimeCompletion.timeForm_one (T := 1) ha1 zero_le_one
  have h2 := TimeCompletion.timeForm_ofReal a 1 (fun _ => (1 : ℝ)) (fun _ => (1 : ℝ))
  simp only [Complex.ofReal_one] at h2
  rw [h2, Real.one_rpow, mul_one] at h1
  have h3 := Complex.ofReal_injective h1
  simp only [one_mul] at h3
  rw [integral_prod _ (kern_integrable ha1), timeMeasure_eq_Icc]
  simpa using h3

/-- The Schur bound fails with the constant `1` in place of `K_0`. -/
theorem schur_constant_one_refuted (p : TParams) :
    ¬ ∀ F : Lp ℝ 2 timeMeasure, ‖J p ℝ F‖ ^ 2 ≤ 1 * ‖F‖ ^ 2 := by
  intro h
  have hm : MemLp (fun _ : ℝ => (1 : ℝ)) 2 timeMeasure := memLp_const 1
  set F := hm.toLp (fun _ : ℝ => (1 : ℝ))
  have hc := hm.coeFn_toLp
  have hF : ‖F‖ ^ 2 = 1 := by
    rw [Lp_norm_sq_eq]
    have e : (fun t => ‖F t‖ ^ 2) =ᵐ[timeMeasure] fun _ => (1 : ℝ) := by
      filter_upwards [hc] with t ht
      rw [ht]; simp
    rw [integral_congr_ae e]
    simp
  have hJ : ‖J p ℝ F‖ ^ 2 = ∫ q, kern p.a (q.1 - q.2) ∂(timeMeasure.prod timeMeasure) := by
    rw [(positive_bochner_inclusion F).2.1]
    refine integral_congr_ae ?_
    filter_upwards [(Measure.quasiMeasurePreserving_fst (μ := timeMeasure)
        (ν := timeMeasure)).ae hc,
      (Measure.quasiMeasurePreserving_snd (μ := timeMeasure) (ν := timeMeasure)).ae hc]
      with q h1 h2
    rw [h1, h2]
    simp
  have hle := h F
  rw [hJ, hF, integral_kern_eq p.ha1] at hle
  have ha0 := p.ha0
  have ha1 := p.ha1
  have hd : 0 < (1 - p.a) * (2 - p.a) := by nlinarith
  rw [div_le_iff₀ hd] at hle
  nlinarith

/-- The package bound with `K_0`. -/
theorem schur_constant_one_contrast (p : TParams) (F : Lp ℝ 2 timeMeasure) :
    ‖J p ℝ F‖ ^ 2 ≤ OccupationCeilingFinite.K0 p.a * ‖F‖ ^ 2 :=
  (positive_bochner_inclusion F).2.2.1

end Refutations.OccupationCompletion
