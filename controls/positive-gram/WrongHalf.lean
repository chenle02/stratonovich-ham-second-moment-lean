module
public import StratonovichHAMAudit.PositiveGram
/-!
Negative control for `StratonovichHAMAudit.PositiveGram.active_upper_bound`.
Wrong variant: the active upper bound with the Gram term `‖∑ i, w i • k i‖ ^ 2 / 2`
replaced by `‖∑ i, w i • k i‖ ^ 2 / 4`, in the exact shape of the package statement,
at ι = Fin 1, H = ℝ, Phi = 1, k = 1, ell = 1, b = 0, w = 1. The claim becomes
`3 / 2 ≤ 5 / 4`. The package theorem (with `/ 2`) is put in context and holds
there with equality.
Expected outcome: rejected (unsolved goal `⊢ False`).
-/
open scoped BigOperators
example : (fun (Phi : ℝ) (k ell b w : Fin 1 → ℝ) =>
    2 * (∑ i, ell i * Real.sqrt (inner ℝ Phi (k i) - b i)) - ‖Phi‖ ^ 2 / 2 ≤
      (∑ i, ell i ^ 2 / w i) - (∑ i, b i * w i) + ‖∑ i, w i • k i‖ ^ 2 / 4)
    1 (fun _ => 1) (fun _ => 1) (fun _ => 0) (fun _ => 1) := by
  have h := StratonovichHAMAudit.PositiveGram.active_upper_bound (1 : ℝ) (fun _ : Fin 1 => (1 : ℝ))
    (fun _ => 1) (fun _ => 0) (fun _ => 1) (fun _ => one_pos) (fun _ => by norm_num)
  norm_num at h ⊢
