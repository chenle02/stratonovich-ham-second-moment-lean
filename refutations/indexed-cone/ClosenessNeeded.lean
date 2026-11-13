/-
Refutation for `L:raw-block-indexed-cone` (TeX lines 232--251), package
theorem `StratonovichHAMSecondMoment.IndexedCone.indexed_cone`.

Wrong variant: the operator-closeness hypothesis
`max_{m≤N} sup_{0≤u≤B} ‖D_m(u) - P_{σ_m}(u)‖ ≤ ε_op` dropped ("no positivity,
composition or independence assumption on the D_m is required" misread as "no
assumption at all").  Counterexample: the package's scalar ground family
`scalarFamily` and `D_m = 0`, whose product is `0`, below the positive right
side.  No junk-value reliance.

`closeness_contrast` applies the package theorem at the same family with the
closeness hypothesis kept (`D_m = P_{σ_m}`).

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.IndexedCone

set_option autoImplicit false

open Set StratonovichHAMSecondMoment.IndexedCone

namespace Refutations.IndexedCone

/-- Dropping the closeness hypothesis is false. -/
theorem closeness_not_droppable :
    ¬ ∀ (G : GroundFamily ℝ) (ϱ : ℝ), 0 < ϱ → ϱ < 1 / 2 →
      ∃ B : ℕ, 1 ≤ B ∧ ∃ cStar : ℝ, 0 < cStar ∧
        ∀ N : ℕ, 1 ≤ N → ∀ σ : ℕ → ℝ, (∀ m ≤ N, σ m ∈ paramI) →
          ∀ D : ℕ → ℝ → ℝ →L[ℝ] ℝ, ∀ u ∈ Icc (0 : ℝ) B,
            cStar * (1 - ϱ) ^ (N - 1) *
                Real.exp ((B : ℝ) * ∑ m ∈ Finset.range N, G.lam (σ m) + u * G.lam (σ N)) ≤
              G.obs (D N u (chainState D B G.e0 N)) := by
  intro h
  obtain ⟨B, _, c, hc, hall⟩ := h scalarFamily (1 / 4) (by norm_num) (by norm_num)
  have h0 : (0 : ℝ) ∈ paramI := by simp [paramI]
  have := hall 1 le_rfl (fun _ => 0) (fun _ _ => h0) (fun _ _ => 0) 0
    ⟨le_rfl, Nat.cast_nonneg _⟩
  simp only [zero_apply, map_zero] at this
  have hpos : 0 < c * (1 - 1 / 4 : ℝ) ^ (1 - 1) *
      Real.exp ((B : ℝ) * ∑ _m ∈ Finset.range 1, scalarFamily.lam 0 + 0 * scalarFamily.lam 0) := by
    positivity
  linarith

/-- With the closeness hypothesis kept, the package theorem applies to the same
family: `D_m = P_{σ_m}` gives the bound. -/
theorem closeness_contrast :
    ∃ B : ℕ, 1 ≤ B ∧ ∃ cStar : ℝ, 0 < cStar ∧
      cStar * (1 - 1 / 4) ^ (1 - 1) *
          Real.exp ((B : ℝ) * ∑ _m ∈ Finset.range 1, scalarFamily.lam 0 + 0 * scalarFamily.lam 0) ≤
        scalarFamily.obs (scalarFamily.P 0 0
          (chainState (fun _ u => scalarFamily.P 0 u) B scalarFamily.e0 1)) := by
  obtain ⟨B, hB, ω, hω, ε, hε, c, hc, _, hall⟩ :=
    indexed_cone scalarFamily (ϱ := 1 / 4) (by norm_num) (by norm_num)
  have h0 : (0 : ℝ) ∈ paramI := by simp [paramI]
  refine ⟨B, hB, c, hc, ?_⟩
  have := (hall 1 le_rfl (fun _ => 0) (fun _ _ => h0) (fun _ _ => by simp [hω.le])
    (fun _ u => scalarFamily.P 0 u) (fun _ _ _ _ => by simp [hε.le]) 0
    ⟨le_rfl, Nat.cast_nonneg _⟩).1
  simpa using this

end Refutations.IndexedCone
