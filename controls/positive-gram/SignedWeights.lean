module
public import StratonovichHAMAudit.PositiveGram
/-!
Negative control for `StratonovichHAMAudit.PositiveGram.half_weighted_entrywise_mono`.
Wrong variant: entrywise Gram monotonicity without the hypothesis `∀ i, 0 ≤ w i`,
in the exact shape of the package statement, at ι = Fin 2 with the signed weights
w = (1, -1), C = identity and D = the matrix with diagonal 1 and off-diagonal 1 / 2
(so C ≤ D entrywise). The claim becomes `1 ≤ 1 / 2`. The package theorem is put in
context; its hypothesis `0 ≤ w i` fails at i = 1, so it gives nothing.
Expected outcome: rejected (unsolved goal `⊢ False`).
-/
open scoped BigOperators
example : (fun (C D : Fin 2 → Fin 2 → ℝ) (w : Fin 2 → ℝ) =>
    (1 / 2 : ℝ) * (∑ i, ∑ j, w i * C i j * w j) ≤
      (1 / 2 : ℝ) * (∑ i, ∑ j, w i * D i j * w j))
    (fun i j => if i = j then 1 else 0) (fun i j => if i = j then 1 else 1 / 2)
    (fun i => if i = 0 then 1 else -1) := by
  have h := StratonovichHAMAudit.PositiveGram.half_weighted_entrywise_mono
    (fun i j : Fin 2 => if i = j then (1 : ℝ) else 0) (fun i j => if i = j then 1 else 1 / 2)
    (fun i => if i = 0 then 1 else -1)
  norm_num [Fin.sum_univ_two, Fin.forall_fin_two] at h ⊢
