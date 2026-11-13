module
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic
@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped BigOperators
universe u v
namespace StratonovichHAMAudit.PositiveGram

theorem scalar_sqrt_dual (ell w t : ℝ) (hw : 0 < w) (ht : 0 ≤ t) :
    2 * ell * Real.sqrt t ≤ ell ^ 2 / w + w * t :=
by
  have hs : (w * Real.sqrt t) ^ 2 = w ^ 2 * t := by
    rw [mul_pow, Real.sq_sqrt ht]
  apply (mul_le_mul_iff_left₀ hw).mp
  rw [add_mul, div_mul_cancel₀ _ (ne_of_gt hw)]
  nlinarith [sq_nonneg (ell - w * Real.sqrt t)]

theorem gram_norm_square {ι : Type u} {H : Type v} [Fintype ι]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] (k : ι → H) (w : ι → ℝ) :
    ‖∑ i, w i • k i‖ ^ 2 =
      ∑ i, ∑ j, w i * inner ℝ (k i) (k j) * w j :=
by
  classical
  rw [← real_inner_self_eq_norm_sq]
  simp only [sum_inner, inner_sum, inner_smul_left, inner_smul_right]
  simp only [conj_trivial]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [real_inner_comm (k i) (k j)]
  ring

theorem active_upper_bound {ι : Type u} {H : Type v} [Fintype ι]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (Phi : H) (k : ι → H) (ell b w : ι → ℝ)
    (hw : ∀ i, 0 < w i) (ht : ∀ i, 0 ≤ inner ℝ Phi (k i) - b i) :
    2 * (∑ i, ell i * Real.sqrt (inner ℝ Phi (k i) - b i)) - ‖Phi‖ ^ 2 / 2 ≤
      (∑ i, ell i ^ 2 / w i) - (∑ i, b i * w i) + ‖∑ i, w i • k i‖ ^ 2 / 2 :=
by
  classical
  let z : H := ∑ i, w i • k i
  have hs : 2 * (∑ i, ell i * Real.sqrt (inner ℝ Phi (k i) - b i)) ≤
      (∑ i, ell i ^ 2 / w i) +
        (∑ i, w i * (inner ℝ Phi (k i) - b i)) := by
    calc
      _ = ∑ i, 2 * ell i * Real.sqrt (inner ℝ Phi (k i) - b i) := by
        rw [Finset.mul_sum]
        congr 1
        funext i
        ring
      _ ≤ ∑ i, (ell i ^ 2 / w i + w i * (inner ℝ Phi (k i) - b i)) :=
        Finset.sum_le_sum (fun i hi => scalar_sqrt_dual _ _ _ (hw i) (ht i))
      _ = _ := Finset.sum_add_distrib
  have hz : (∑ i, w i * (inner ℝ Phi (k i) - b i)) =
      inner ℝ Phi z - ∑ i, b i * w i := by
    simp only [z, inner_sum, inner_smul_right, mul_sub, Finset.sum_sub_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hn := norm_sub_sq_real Phi z
  have hnon := sq_nonneg ‖Phi - z‖
  rw [hz] at hs
  dsimp [z] at hn hnon hs
  nlinarith

theorem half_weighted_entrywise_mono {ι : Type u} [Fintype ι]
    (C D : ι → ι → ℝ) (w : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hCD : ∀ i j, C i j ≤ D i j) :
    (1 / 2 : ℝ) * (∑ i, ∑ j, w i * C i j * w j) ≤
      (1 / 2 : ℝ) * (∑ i, ∑ j, w i * D i j * w j) :=
by
  classical
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Finset.sum_le_sum
  intro i hi
  apply Finset.sum_le_sum
  intro j hj
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (hCD i j) (hw i)) (hw j)

end StratonovichHAMAudit.PositiveGram
