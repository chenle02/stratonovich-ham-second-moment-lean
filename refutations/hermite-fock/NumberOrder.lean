import StratonovichHAMSecondMoment.HermiteFock

/-!
Refutation for `StratonovichHAMSecondMoment.HermiteFock.number_identity` (`∑_i a_i^* a_i = |k|`
on degree `k`, main TeX lines 2517-2519 at a284420, "∑_i a_i^* a_i = (k+1) I on degree k+1").

Wrong variant: the identity with `|k| + 1` (an off-by-one in the degree, or the order
`a_i a_i^*` with one mode).  Counterexample: `X = ℂ`, one mode, `v = 1`, `k = 0`: the package
gives `0`, the wrong variant `1`.  No junk-value reliance.  `number_contrast` is the package
identity at the same point.

Expected outcome: compiles (refuted).
-/

set_option autoImplicit false

namespace Refutations.HermiteFock

open StratonovichHAMSecondMoment.HermiteFock

/-- The number identity fails with `|k| + 1`. -/
theorem number_order_refuted :
    ¬ (∀ (v : (Fin 1 → ℕ) → ℂ) (k : Fin 1 → ℕ),
        ∑ i, cre i (ann i v) k = (((deg k : ℝ) + 1 : ℝ) : ℂ) • v k) := by
  intro H
  have h := H (fun _ => 1) 0
  rw [number_identity] at h
  norm_num [deg] at h

/-- Contrast: the package identity at `v = 1`, `k = 0`. -/
theorem number_contrast :
    ∑ i, cre i (ann i (fun _ : Fin 1 → ℕ => (1 : ℂ))) 0 = 0 := by
  rw [number_identity]; simp [deg]

end Refutations.HermiteFock
