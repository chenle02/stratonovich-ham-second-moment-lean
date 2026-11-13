/-
Refutation for the factor `(1-ϱ)^{N-1}` of `E:raw-block-positive-product`
(`L:raw-block-indexed-cone`, TeX lines 243--248 and 318), package theorem
`StratonovichHAMSecondMoment.IndexedCone.indexed_cone`.

Wrong variant: the geometric loss dropped, i.e. a bound
`c_* exp(BΣ_{m<N}λ_{σ_m} + uλ_{σ_N})` uniform in `N` ("perturbations of size
`ε_op` cost only a constant").  Counterexample: the package's scalar ground
family `scalarFamily` and the damped blocks `D_m(u) = (1-s)e^u`,
`s = min(1/2, ε_op e^{-B}) > 0`, which are `ε_op`-close to `P(u) = e^u` on
`[0,B]`; the product is `(1-s)^{N+1} e^{BN+u}`, and `(1-s)^{N+1} → 0`
defeats every `c_* > 0`.  No junk-value reliance.

`geometric_contrast` applies the package theorem (with its factor
`(1-ϱ)^{N-1}`) to the same family and blocks for every `N ≥ 1`.

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.IndexedCone

set_option autoImplicit false

open Set StratonovichHAMSecondMoment.IndexedCone

noncomputable section

namespace Refutations.IndexedCone

/-- The damped scalar blocks `D_m(u) = (1-s)e^u` on `ℝ` (counterexample data). -/
def dampedBlocks (s : ℝ) : ℕ → ℝ → ℝ →L[ℝ] ℝ :=
  fun _ u => ((1 - s) * Real.exp u) • ContinuousLinearMap.id ℝ ℝ

theorem dampedBlocks_chain (s B : ℝ) (N : ℕ) :
    chainState (dampedBlocks s) B scalarFamily.e0 N = ((1 - s) * Real.exp B) ^ N := by
  induction N with
  | zero => simp [scalarFamily]
  | succ n ih =>
    rw [chainState_succ, ih]
    simp [dampedBlocks, pow_succ, mul_comm]

theorem dampedBlocks_value (s B u : ℝ) (N : ℕ) :
    scalarFamily.obs (dampedBlocks s N u (chainState (dampedBlocks s) B scalarFamily.e0 N)) =
      (1 - s) ^ (N + 1) * Real.exp (B * N + u) := by
  rw [dampedBlocks_chain]
  have h1 : scalarFamily.obs (dampedBlocks s N u (((1 - s) * Real.exp B) ^ N)) =
      (1 - s) * Real.exp u * ((1 - s) * Real.exp B) ^ N := by
    simp [scalarFamily, dampedBlocks]
  rw [h1, mul_pow, Real.exp_add, ← Real.exp_nat_mul, pow_succ, mul_comm (B : ℝ) (N : ℝ)]
  ring

theorem dampedBlocks_close {s : ℝ} (hs : 0 ≤ s) (m : ℕ) (σ u : ℝ) :
    ‖dampedBlocks s m u - scalarFamily.P σ u‖ ≤ s * Real.exp u := by
  have h : dampedBlocks s m u - scalarFamily.P σ u =
      (-(s * Real.exp u)) • ContinuousLinearMap.id ℝ ℝ := by
    ext; simp [dampedBlocks, scalarFamily]; ring
  rw [h]
  refine (norm_smul_le (-(s * Real.exp u)) (ContinuousLinearMap.id ℝ ℝ)).trans ?_
  rw [norm_neg, Real.norm_of_nonneg (by positivity)]
  exact mul_le_of_le_one_right (by positivity) ContinuousLinearMap.norm_id_le

theorem scalar_sum (N : ℕ) (σ : ℕ → ℝ) :
    ∑ m ∈ Finset.range N, scalarFamily.lam (σ m) = N := by
  simp [scalarFamily]

/-- Dropping the geometric loss `(1-ϱ)^{N-1}` is false. -/
theorem geometric_loss_needed :
    ¬ ∀ (G : GroundFamily ℝ) (ϱ : ℝ), 0 < ϱ → ϱ < 1 / 2 →
      ∃ B : ℕ, 1 ≤ B ∧ ∃ ω : ℝ, 0 < ω ∧ ∃ ε : ℝ, 0 < ε ∧ ∃ cStar : ℝ, 0 < cStar ∧
        ∀ N : ℕ, 1 ≤ N → ∀ σ : ℕ → ℝ, (∀ m ≤ N, σ m ∈ paramI) →
          (∀ m < N, |σ (m + 1) - σ m| ≤ ω) →
          ∀ D : ℕ → ℝ → ℝ →L[ℝ] ℝ,
            (∀ m ≤ N, ∀ u ∈ Icc (0 : ℝ) B, ‖D m u - G.P (σ m) u‖ ≤ ε) →
            ∀ u ∈ Icc (0 : ℝ) B,
              cStar *
                  Real.exp ((B : ℝ) * ∑ m ∈ Finset.range N, G.lam (σ m) + u * G.lam (σ N)) ≤
                G.obs (D N u (chainState D B G.e0 N)) := by
  intro h
  obtain ⟨B, _, ω, hω, ε, hε, c, hc, hall⟩ :=
    h scalarFamily (1 / 4) (by norm_num) (by norm_num)
  have h0 : (0 : ℝ) ∈ paramI := by simp [paramI]
  set s := min (1 / 2) (ε / Real.exp B) with hs
  have hs0 : 0 < s := lt_min (by norm_num) (by positivity)
  have hs1 : s ≤ 1 / 2 := min_le_left _ _
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hc (show 1 - s < 1 by linarith)
  have hclose : ∀ m ≤ n + 1, ∀ u ∈ Icc (0 : ℝ) B,
      ‖dampedBlocks s m u - scalarFamily.P ((fun _ => (0 : ℝ)) m) u‖ ≤ ε := by
    intro m _ u hu
    refine (dampedBlocks_close hs0.le m 0 u).trans ?_
    have h1 : s ≤ ε / Real.exp B := min_le_right _ _
    rw [le_div_iff₀ (Real.exp_pos _)] at h1
    have h2 : s * Real.exp u ≤ s * Real.exp B :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hu.2) hs0.le
    linarith
  have := hall (n + 1) (by omega) (fun _ => 0) (fun _ _ => h0) (fun _ _ => by simp [hω.le])
    (dampedBlocks s) hclose 0 ⟨le_rfl, Nat.cast_nonneg _⟩
  rw [dampedBlocks_value, scalar_sum] at this
  simp only [zero_mul, add_zero] at this
  have hmono : (1 - s) ^ (n + 1 + 1) ≤ (1 - s) ^ n :=
    pow_le_pow_of_le_one (by linarith) (by linarith) (by omega)
  have hE := Real.exp_pos ((B : ℝ) * ((n + 1 : ℕ) : ℝ))
  have h2 : c * Real.exp ((B : ℝ) * ((n + 1 : ℕ) : ℝ)) ≤
      (1 - s) ^ n * Real.exp ((B : ℝ) * ((n + 1 : ℕ) : ℝ)) :=
    this.trans (mul_le_mul_of_nonneg_right hmono hE.le)
  have h3 := (mul_le_mul_iff_left₀ hE).mp h2
  linarith

/-- The package bound, with its factor `(1-ϱ)^{N-1}`, at the same family and
blocks, for every `N ≥ 1`. -/
theorem geometric_contrast :
    ∃ B : ℕ, 1 ≤ B ∧ ∃ ε : ℝ, 0 < ε ∧ ∃ cStar : ℝ, 0 < cStar ∧
      ∀ s : ℝ, 0 ≤ s → s * Real.exp B ≤ ε → ∀ N : ℕ, 1 ≤ N →
        cStar * (1 - 1 / 4) ^ (N - 1) *
            Real.exp ((B : ℝ) * ∑ _m ∈ Finset.range N, scalarFamily.lam 0 +
              0 * scalarFamily.lam 0) ≤
          scalarFamily.obs (dampedBlocks s N 0
            (chainState (dampedBlocks s) B scalarFamily.e0 N)) := by
  obtain ⟨B, hB, ω, hω, ε, hε, c, hc, _, hall⟩ :=
    indexed_cone scalarFamily (ϱ := 1 / 4) (by norm_num) (by norm_num)
  have h0 : (0 : ℝ) ∈ paramI := by simp [paramI]
  refine ⟨B, hB, ε, hε, c, hc, fun s hs hsB N hN => ?_⟩
  have hclose : ∀ m ≤ N, ∀ u ∈ Icc (0 : ℝ) B,
      ‖dampedBlocks s m u - scalarFamily.P ((fun _ => (0 : ℝ)) m) u‖ ≤ ε := by
    intro m _ u hu
    refine (dampedBlocks_close hs m 0 u).trans ?_
    have h2 : s * Real.exp u ≤ s * Real.exp B :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hu.2) hs
    linarith
  exact (hall N hN (fun _ => 0) (fun _ _ => h0) (fun _ _ => by simp [hω.le])
    (dampedBlocks s) hclose 0 ⟨le_rfl, Nat.cast_nonneg _⟩).1

end Refutations.IndexedCone

end
