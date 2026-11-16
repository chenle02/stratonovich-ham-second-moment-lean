/-
Refutation for the separate chain roots in the positions form of the spatial
integral (main TeX lines 811-813 and 818-822 at 39f2597a: "at each first vertex
set `(s_{p(l)}, y_{p(l)}) = (0, 0)`.  Thus, the second chain has its own root,
rather than the last vertex of the first chain"), package theorem
`StratonovichHAMSecondMoment.DiagramBridge.spatial_waveGreen_one_eq_spatialPos`
and definition `StratonovichHAMSecondMoment.DiagramModel.spatialPos`.

Wrong variant: the positions integral of the concatenated chain (global
predecessor), i.e. `spatialPos` with the chain split `m = 2` in place of the
two one-vertex chains `m = n = 1`.  Counterexample: the pairing `D = (0 1)`,
`h = (1, 1)` and the covariance `γ = 1_{|x| ≥ 1}`: in the concatenated chain
`|y_2 - y_1| < 1` on the support, so the integral is `0`; with two roots
`y_1, y_2` range independently over `(-1, 1)` and the integral is positive (it
is at least the Green mass of the box `B(¾, ¼) × B(-¾, ¼)`).
`spatialOwnRoot_contrast` is the package bridge at the same point together
with the positivity.
Control of the broader Lean generalization (the bridge for every covariance
`γ : ℝ¹ → [0, ∞]`), outside the manuscript's covariance class: `1_{|x| ≥ 1}` is not
positive definite (main TeX lines 386-399).
No junk-value reliance (lower Lebesgue integrals).

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.DiagramBridge

set_option autoImplicit false

open MeasureTheory StratonovichHAMSecondMoment DiagramModel DiagramBridge
open scoped ENNReal

namespace Refutations.DiagramBridge

/-- The covariance `1_{|x| ≥ 1}`. -/
noncomputable def gammaFar : HomogHypothesis.Rd 1 → ℝ≥0∞ :=
  {x | 1 ≤ ‖x‖}.indicator 1

/-- The pairing `{1, 2}` of two labels. -/
def Dsw : Fin 2 → Fin 2 := ![1, 0]

/-- The time increments `(1, 1)`. -/
def hOne : Fin 2 → ℝ := fun _ => 1

theorem covWeight_Dsw (γ : HomogHypothesis.Rd 1 → ℝ≥0∞) (y : Fin 2 → HomogHypothesis.Rd 1) :
    covWeight γ Dsw y = γ (y 0 - y 1) := by
  have h : openers Dsw = {0} := by decide
  unfold covWeight
  rw [h]
  simp [Dsw]

/-- The concatenated chain gives `0`. -/
theorem concat_eq_zero : spatialPos green1 gammaFar 2 Dsw hOne = 0 := by
  unfold spatialPos
  refine (lintegral_congr fun y => ?_).trans lintegral_zero
  rw [covWeight_Dsw, Fin.prod_univ_two]
  have hp0 : pred 2 (0 : Fin 2) = none := by decide
  have hp1 : pred 2 (1 : Fin 2) = some 0 := by decide
  rw [predVal_of_none 2 y 0 hp0, predVal_of_some 2 y 1 0 hp1]
  by_cases hy : y 1 - y 0 ∈ Metric.ball (0 : HomogHypothesis.Rd 1) 1
  · have h0 : gammaFar (y 0 - y 1) = 0 := by
      apply Set.indicator_of_notMem
      simp only [Set.mem_ofPred_eq, not_le]
      rw [← norm_neg, neg_sub]
      simpa using hy
    simp [h0]
  · rw [show green1 (hOne 1) (y 1 - y 0) = 0 from Set.indicator_of_notMem hy _]
    simp

/-- The centre `¾ e_0`. -/
noncomputable def cFar : HomogHypothesis.Rd 1 := EuclideanSpace.single 0 (3 / 4)

theorem norm_cFar : ‖cFar‖ = 3 / 4 := by
  rw [cFar, EuclideanSpace.norm_eq]
  simp [Real.sqrt_sq_eq_abs]
  norm_num

/-- The box `B(¾, ¼) × B(-¾, ¼)`. -/
noncomputable def boxFar : Fin 2 → Set (HomogHypothesis.Rd 1) :=
  ![Metric.ball cFar (1 / 4), Metric.ball (-cFar) (1 / 4)]

theorem boxFar_sub (i : Fin 2) : boxFar i ⊆ Metric.ball 0 1 := by
  intro x hx
  rw [Metric.mem_ball]
  fin_cases i
  · have := dist_triangle x cFar 0
    have h2 : dist cFar 0 = 3 / 4 := by rw [dist_zero_right, norm_cFar]
    simp only [boxFar, Fin.zero_eta, Matrix.cons_val_zero, Metric.mem_ball] at hx
    linarith
  · have := dist_triangle x (-cFar) 0
    have h2 : dist (-cFar) 0 = 3 / 4 := by rw [dist_zero_right, norm_neg, norm_cFar]
    simp only [boxFar, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero,
      Metric.mem_ball] at hx
    linarith

theorem far_of_mem {w : Fin 2 → HomogHypothesis.Rd 1} (hw : w ∈ Set.univ.pi boxFar) :
    1 ≤ ‖w 0 - w 1‖ := by
  have h0 : dist (w 0) cFar < 1 / 4 := hw 0 (Set.mem_univ _)
  have h1 : dist (w 1) (-cFar) < 1 / 4 := hw 1 (Set.mem_univ _)
  have hc : dist cFar (-cFar) = 3 / 2 := by
    rw [dist_eq_norm, sub_neg_eq_add, ← two_smul ℝ, norm_smul, norm_cFar]; norm_num
  have := dist_triangle4 cFar (w 0) (w 1) (-cFar)
  rw [dist_comm cFar (w 0)] at this
  rw [← dist_eq_norm]
  linarith

/-- With two roots the integral is positive. -/
theorem ownRoot_ne_zero : spatialPos green1 gammaFar 1 Dsw hOne ≠ 0 := by
  rw [← spatial_waveGreen_one_eq_spatialPos]
  unfold spatial
  have hpos : ∀ w : Fin 2 → HomogHypothesis.Rd 1, pos 1 w = w := fun w => funext fun i => by
    rw [pos_eq_add_predVal, predVal_of_none, add_zero]
    fin_cases i <;> decide
  simp_rw [hpos, covWeight_Dsw]
  have hle : (Set.univ.pi boxFar).indicator 1 ≤
      fun w : Fin 2 → HomogHypothesis.Rd 1 => gammaFar (w 0 - w 1) := by
    intro w
    by_cases hw : w ∈ Set.univ.pi boxFar
    · rw [Set.indicator_of_mem hw]
      simp [gammaFar, Set.indicator_of_mem (show w 0 - w 1 ∈ {x | 1 ≤ ‖x‖} from far_of_mem hw)]
    · rw [Set.indicator_of_notMem hw]; exact zero_le
  have hmeas : ∀ i, MeasurableSet (boxFar i) := fun i => by
    fin_cases i <;> exact Metric.isOpen_ball.measurableSet
  intro hz
  have hm := lintegral_mono (μ := Measure.pi fun i => WaveGreen.waveGreen 1 (hOne i)) hle
  rw [hz, lintegral_indicator_one (MeasurableSet.univ_pi hmeas), Measure.pi_pi] at hm
  refine (Finset.prod_ne_zero_iff.2 fun i _ => ?_) (le_zero_iff.1 hm)
  rw [show WaveGreen.waveGreen 1 (hOne i) = ENNReal.ofReal (1 / 2) •
      volume.restrict (Metric.ball (0 : HomogHypothesis.Rd 1) 1) from rfl,
    Measure.smul_apply, smul_eq_mul, Measure.restrict_apply (hmeas i),
    Set.inter_eq_left.2 (boxFar_sub i)]
  refine mul_ne_zero (by norm_num) ?_
  fin_cases i <;> exact (Metric.measure_ball_pos volume _ (by norm_num)).ne'

/-- The package: the bridge at the counterexample point, and positivity. -/
theorem spatialOwnRoot_contrast :
    spatial (WaveGreen.waveGreen 1) gammaFar 1 Dsw hOne =
        spatialPos green1 gammaFar 1 Dsw hOne ∧
      spatialPos green1 gammaFar 1 Dsw hOne ≠ 0 :=
  ⟨spatial_waveGreen_one_eq_spatialPos gammaFar 1 Dsw hOne, ownRoot_ne_zero⟩

/-- The positions integral of the concatenated chain is not the two-root one. -/
theorem spatialOwnRoot_refuted :
    ¬ (spatialPos green1 gammaFar 1 Dsw hOne = spatialPos green1 gammaFar 2 Dsw hOne) := by
  intro h
  exact ownRoot_ne_zero (h.trans concat_eq_zero)

end Refutations.DiagramBridge
