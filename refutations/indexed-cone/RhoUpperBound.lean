/-
Refutation for the parameter range of `L:raw-block-indexed-cone` (TeX line 234,
"Fix 0 < ϱ < 1/2"), package theorem
`StratonovichHAMSecondMoment.IndexedCone.indexed_cone`.

Wrong variant: the upper bound on `ϱ` dropped (every `ϱ > 0`), keeping the
strict positivity `c_*(1-ϱ)^{N-1}exp(⋯) > 0` of
`E:raw-block-positive-product`.  Counterexample: `ϱ = 1`, `N = 2`, where
`(1-ϱ)^{N-1} = 0`, on the package's scalar ground family `scalarFamily`
with `D_m = P_{σ_m}`.  No junk-value reliance (`0^1 = 0` is genuine).

`rho_contrast` applies the package theorem at `ϱ = 1/4` to the same family,
chain, blocks and point, where the positivity holds.

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.IndexedCone

set_option autoImplicit false

open Set StratonovichHAMSecondMoment.IndexedCone

namespace Refutations.IndexedCone

/-- Dropping `ϱ < 1/2` (keeping `ϱ > 0`) is false. -/
theorem rho_upper_bound_needed :
    ¬ ∀ (G : GroundFamily ℝ) (ϱ : ℝ), 0 < ϱ →
      ∃ B : ℕ, 1 ≤ B ∧ ∃ ω : ℝ, 0 < ω ∧ ∃ ε : ℝ, 0 < ε ∧ ∃ cStar : ℝ, 0 < cStar ∧
        ∀ N : ℕ, 1 ≤ N → ∀ σ : ℕ → ℝ, (∀ m ≤ N, σ m ∈ paramI) →
          (∀ m < N, |σ (m + 1) - σ m| ≤ ω) →
          ∀ D : ℕ → ℝ → ℝ →L[ℝ] ℝ,
            (∀ m ≤ N, ∀ u ∈ Icc (0 : ℝ) B, ‖D m u - G.P (σ m) u‖ ≤ ε) →
            ∀ u ∈ Icc (0 : ℝ) B,
              cStar * (1 - ϱ) ^ (N - 1) *
                  Real.exp ((B : ℝ) * ∑ m ∈ Finset.range N, G.lam (σ m) + u * G.lam (σ N)) ≤
                G.obs (D N u (chainState D B G.e0 N)) ∧
              0 < cStar * (1 - ϱ) ^ (N - 1) *
                  Real.exp ((B : ℝ) * ∑ m ∈ Finset.range N, G.lam (σ m) + u * G.lam (σ N)) := by
  intro h
  obtain ⟨B, _, ω, hω, ε, hε, c, _, hall⟩ := h scalarFamily 1 one_pos
  have h0 : (0 : ℝ) ∈ paramI := by simp [paramI]
  have := (hall 2 (by norm_num) (fun _ => 0) (fun _ _ => h0) (fun _ _ => by simp [hω.le])
    (fun _ u => scalarFamily.P 0 u) (fun _ _ _ _ => by simp [hε.le]) 0
    ⟨le_rfl, Nat.cast_nonneg _⟩).2
  simp at this

/-- At `ϱ = 1/4` the package theorem gives the positivity on the same data. -/
theorem rho_contrast :
    ∃ B : ℕ, 1 ≤ B ∧ ∃ cStar : ℝ, 0 < cStar ∧
      0 < cStar * (1 - 1 / 4) ^ (2 - 1) *
          Real.exp ((B : ℝ) * ∑ _m ∈ Finset.range 2, scalarFamily.lam 0 +
            0 * scalarFamily.lam 0) := by
  obtain ⟨B, hB, ω, hω, ε, hε, c, hc, _, hall⟩ :=
    indexed_cone scalarFamily (ϱ := 1 / 4) (by norm_num) (by norm_num)
  have h0 : (0 : ℝ) ∈ paramI := by simp [paramI]
  exact ⟨B, hB, c, hc, (hall 2 (by norm_num) (fun _ => 0) (fun _ _ => h0)
    (fun _ _ => by simp [hω.le]) (fun _ u => scalarFamily.P 0 u)
    (fun _ _ _ _ => by simp [hε.le]) 0 ⟨le_rfl, Nat.cast_nonneg _⟩).2⟩

end Refutations.IndexedCone
