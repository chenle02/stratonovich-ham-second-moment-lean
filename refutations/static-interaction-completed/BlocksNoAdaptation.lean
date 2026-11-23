import StratonovichHAMSecondMoment.StaticInteractionCompleted

/-!
Refutation for
`StratonovichHAMSecondMoment.StaticInteractionCompleted.independent_static_blocks_operator`
(`E:independent-static-blocks`, main TeX lines 3248-3256, proof 3332-3339 at edf7085f).

Wrong variant: the block bound without the adaptation hypothesis `hadapt` (the per-block
interaction bound `hI` is only known on phases adapted to the past, i.e. independent of the
`j`th field; the TeX's tensoring step needs that independence).  Counterexample: `E = ℝ`,
`K = 2`, `P j y := j = 0` (only the initial phase is adapted), `S_j = I_0 = id`,
`I_1 = 2 • id`, `ℓ_j = E_j = 0`, `x = 1`: `hI` holds (vacuously at `j = 1`), and the block
product is `2`, while the bound is `1`.  The counterexample uses that `hI` is vacuous off
`P`; that is the point of the variant.  `blocks_no_adaptation_contrast` is the package bound
for `I_1 = id` with `P := True` (adaptation holds).

Expected outcome: compiles (refuted).
-/

set_option autoImplicit false

namespace Refutations.StaticInteractionCompleted

open StratonovichHAMSecondMoment.StaticInteractionCompleted

/-- The block bound fails without adaptation. -/
theorem blocks_no_adaptation_refuted :
    ¬ (∀ (K : ℕ) (S I : ℕ → ℝ →L[ℝ] ℝ) (lh Eb : ℕ → ℝ) (P : ℕ → ℝ → Prop) (x : ℝ),
        (∀ j, 0 ≤ Eb j) → P 0 x →
        (∀ j, j < K → ∀ y, ‖S j y‖ ^ 2 ≤ Real.exp (lh j) * ‖y‖ ^ 2) →
        (∀ j, j < K → ∀ y, P j y → ‖I j y‖ ^ 2 ≤ (1 + Eb j) * ‖y‖ ^ 2) →
        ‖blockIter S I K x‖ ^ 2 ≤
          Real.exp (∑ j ∈ Finset.range K, lh j + ∑ j ∈ Finset.range K, Eb j) * ‖x‖ ^ 2) := by
  intro H
  have h := H 2 (fun _ => ContinuousLinearMap.id ℝ ℝ)
    (fun j => if j = 0 then ContinuousLinearMap.id ℝ ℝ else (2 : ℝ) • ContinuousLinearMap.id ℝ ℝ)
    (fun _ => 0) (fun _ => 0) (fun j _ => j = 0) 1 (fun _ => le_rfl) rfl
    (fun j _ y => by simp)
    (fun j _ y hy => by subst hy; simp)
  simp [blockIter] at h

/-- Contrast: with `I_1 = id` and every phase adapted, the package bound holds. -/
theorem blocks_no_adaptation_contrast :
    ‖blockIter (fun _ => ContinuousLinearMap.id ℝ ℝ) (fun _ => ContinuousLinearMap.id ℝ ℝ) 2
        (1 : ℝ)‖ ^ 2 ≤
      Real.exp (∑ j ∈ Finset.range 2, (fun _ => (0 : ℝ)) j +
        ∑ j ∈ Finset.range 2, (fun _ => (0 : ℝ)) j) * ‖(1 : ℝ)‖ ^ 2 :=
  independent_static_blocks_operator 2 _ _ (fun _ => 0) (fun _ => 0) (fun _ _ => True) 1
    (fun _ => le_rfl) trivial (fun _ _ _ _ => trivial) (fun j _ y => by simp)
    (fun j _ y _ => by simp)

end Refutations.StaticInteractionCompleted
