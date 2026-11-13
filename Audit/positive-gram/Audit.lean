module
public import StratonovichHAMAudit.PositiveGram
open scoped BigOperators
open StratonovichHAMAudit.PositiveGram
set_option pp.all true
#check @scalar_sqrt_dual
#print axioms scalar_sqrt_dual
#check @gram_norm_square
#print axioms gram_norm_square
#check @active_upper_bound
#print axioms active_upper_bound
#check @half_weighted_entrywise_mono
#print axioms half_weighted_entrywise_mono
set_option pp.all false
#check scalar_sqrt_dual (1 : ℝ) 1 1 (by norm_num) (by norm_num)
#check scalar_sqrt_dual (3 : ℝ) 2 0 (by norm_num) (by norm_num)
#check gram_norm_square (ι := Fin 2) (H := ℝ)
  (fun i => if i = 0 then 1 else 2) (fun i => if i = 0 then 1 else -1)
#check active_upper_bound (ι := Fin 1) (H := ℝ) (1 : ℝ)
  (fun _ => 1) (fun _ => 1) (fun _ => 0) (fun _ => 1)
  (by intro _; norm_num) (by intro _; norm_num [real_inner_self_eq_norm_sq])
#check active_upper_bound (ι := Fin 1) (H := ℝ) (0 : ℝ)
  (fun _ => 1) (fun _ => 1) (fun _ => 0) (fun _ => 1)
  (by intro _; norm_num) (by intro _; simp)
#check half_weighted_entrywise_mono (ι := Fin 2)
  (fun i j => if i = j then 1 else 0)
  (fun i j => if i = j then 1 else 1 / 2)
  (fun i => if i = 0 then 0 else 1)
  (by intro i; split_ifs <;> norm_num)
  (by intro i j; split_ifs <;> norm_num)

universe u v
namespace StratonovichHAMAudit.PositiveGramAudit
private theorem active_consumer {ι : Type u} {H : Type v} [Fintype ι]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (Phi : H) (k : ι → H) (ell b w : ι → ℝ)
    (hw : ∀ i, 0 < w i) (ht : ∀ i, 0 ≤ inner ℝ Phi (k i) - b i) :
    2 * (∑ i, ell i * Real.sqrt (inner ℝ Phi (k i) - b i)) - ‖Phi‖ ^ 2 / 2 ≤
      (∑ i, ell i ^ 2 / w i) - (∑ i, b i * w i) +
        (1 / 2 : ℝ) * (∑ i, ∑ j, w i * inner ℝ (k i) (k j) * w j) :=
by
  have h := active_upper_bound Phi k ell b w hw ht
  rw [gram_norm_square] at h
  have hr : (∑ i, ∑ j, w i * inner ℝ (k i) (k j) * w j) / 2 =
      (1 / 2 : ℝ) * (∑ i, ∑ j, w i * inner ℝ (k i) (k j) * w j) := by ring
  rw [hr] at h
  exact h

set_option pp.all true
#check @active_consumer
#print axioms active_consumer
end StratonovichHAMAudit.PositiveGramAudit
