import StratonovichHAMSecondMoment.FockForm

/-!
Refutation for `StratonovichHAMSecondMoment.FockForm.fockColumn_compress` (compression by the
band projection `S_b` preserves the column bound, main TeX lines 2511-2513 at a284420).

Wrong variant: compression by any symmetric `P` (dropping idempotence, so `‖P‖ ≤ 1` is lost).
Counterexample: `X = ℂ`, one mode, `H = id`, `c = 1`, `P = 2 id`: `‖P H P 1‖² = 16 > 1`.
No junk-value reliance.  `compress_contrast` is the package lemma with the projection `P = id`.

Expected outcome: compiles (refuted).
-/

set_option autoImplicit false

namespace Refutations.FockForm

open StratonovichHAMSecondMoment.FockForm

/-- Compression fails for a symmetric non-projection. -/
theorem compress_non_projection_refuted :
    ¬ (∀ (H : Fin 1 → ℂ →L[ℂ] ℂ) (c : ℝ) (P : ℂ →L[ℂ] ℂ), 0 ≤ c → FockColumn H c →
        (∀ u w, inner ℂ (P u) w = inner ℂ u (P w)) →
        FockColumn (fun i => P ∘L H i ∘L P) c) := by
  intro h
  have hcol : FockColumn (fun _ : Fin 1 => ContinuousLinearMap.id ℂ ℂ) 1 := fun u => by simp
  have hsym : ∀ u w : ℂ, inner ℂ (((2 : ℂ) • ContinuousLinearMap.id ℂ ℂ) u) w =
      inner ℂ u (((2 : ℂ) • ContinuousLinearMap.id ℂ ℂ) w) := fun u w => by
    simp
    rw [map_ofNat]; ring
  have := h _ 1 _ zero_le_one hcol hsym 1
  norm_num at this

/-- Contrast: the package lemma with the projection `P = id`. -/
theorem compress_contrast :
    FockColumn (fun _ : Fin 1 => ContinuousLinearMap.id ℂ ℂ ∘L ContinuousLinearMap.id ℂ ℂ ∘L
      ContinuousLinearMap.id ℂ ℂ) 1 :=
  fockColumn_compress zero_le_one (fun u => by simp) (fun u w => rfl) (fun u => rfl)

end Refutations.FockForm
