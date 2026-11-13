module
public import StratonovichHAMAudit.PositiveGram
/-!
Negative control for `StratonovichHAMAudit.PositiveGram.active_upper_bound`.
Wrong variant: the active upper bound without the activity hypothesis
`∀ i, 0 ≤ inner ℝ Phi (k i) - b i`, in the exact shape of the package statement,
at ι = Fin 1, H = ℝ, Phi = 0, k = 1, ell = 1, b = 2, w = 1. The active term is
`inner ℝ 0 1 - 2 = -2 < 0`; with Lean's junk value `Real.sqrt (-2) = 0` the claim
becomes `0 ≤ -1 / 2`. The package theorem is put in context; its activity
hypothesis fails here, so it gives nothing.
Expected outcome: rejected (unsolved goal `⊢ False`).
-/
open scoped BigOperators
example : (fun (Phi : ℝ) (k ell b w : Fin 1 → ℝ) =>
    2 * (∑ i, ell i * Real.sqrt (inner ℝ Phi (k i) - b i)) - ‖Phi‖ ^ 2 / 2 ≤
      (∑ i, ell i ^ 2 / w i) - (∑ i, b i * w i) + ‖∑ i, w i • k i‖ ^ 2 / 2)
    0 (fun _ => 1) (fun _ => 1) (fun _ => 2) (fun _ => 1) := by
  have h := StratonovichHAMAudit.PositiveGram.active_upper_bound (0 : ℝ) (fun _ : Fin 1 => (1 : ℝ))
    (fun _ => 1) (fun _ => 2) (fun _ => 1) (fun _ => one_pos)
  norm_num at h ⊢
