/-
Refutation for the general telescoping lemma `E:interval-copy-metric` (main
TeX lines 3809-3837 at 39f2597a), package theorem
`StratonovichHAMSecondMoment.FixedSplitCore.metric_telescoping`.

Wrong variant: dropping the order-convexity hypothesis (each color active on
one block of consecutive segments; the TeX's "each connected `I_i^T`").
Counterexample: one color with `ω = 1`, `λ = 1`, active on segments `0` and
`2` only; over the cuts `0, 1, 2` the conversions are `2, 1, 2`, product
`4 > 2 = 1 + ω/λ` (the color ends twice).  `non_convex_contrast` is the
package lemma for the convex pattern active on segment `0` only.
No junk-value reliance (all heights are at least `1`).

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.FixedSplitCore

set_option autoImplicit false

namespace Refutations.FixedSplitCore

open StratonovichHAMSecondMoment.FixedSplitCore Finset

/-- The pattern active on segments `0` and `2`. -/
noncomputable def twoBlocks : ℕ → Finset Unit := fun j => if j = 0 ∨ j = 2 then {()} else ∅

/-- Without order-convexity the telescoping bound fails. -/
theorem non_convex_activity_refuted :
    ¬ (∀ act : ℕ → Finset Unit, (∀ j, act j ⊆ {()}) →
        ∏ j ∈ range 3, max 1 (height 1 (fun _ => 1) act j / height 1 (fun _ => 1) act (j + 1)) ≤
          ∏ i ∈ ({()} : Finset Unit), (1 + (fun _ => (1 : ℝ)) i / 1)) := by
  intro h
  have h1 := h twoBlocks (fun j => by unfold twoBlocks; split_ifs <;> simp)
  simp [twoBlocks, height, Finset.prod_range_succ] at h1
  norm_num at h1

/-- The package lemma for the convex pattern active on segment `0` only. -/
theorem non_convex_contrast :
    ∏ j ∈ range 3, max 1 (height 1 (fun _ => 1) (fun j => if j = 0 then {()} else ∅) j /
        height 1 (fun _ => 1) (fun j => if j = 0 then ({()} : Finset Unit) else ∅) (j + 1)) ≤
      ∏ i ∈ ({()} : Finset Unit), (1 + (fun _ => (1 : ℝ)) i / 1) := by
  refine metric_telescoping 1 one_pos (fun _ => 1) {()} (fun _ _ => zero_le_one) _
    (fun j => by split_ifs <;> simp) ?_ 3
  intro i j₁ j j₂ h1 h2 hi1 hi2
  simp only at hi1 hi2 ⊢
  split_ifs at hi1 hi2 with c1 c2
  · have : j = 0 := by omega
    simp [this]
  all_goals simp at hi1 hi2

end Refutations.FixedSplitCore
