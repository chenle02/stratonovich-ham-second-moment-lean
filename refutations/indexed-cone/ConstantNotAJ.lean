/-
Refutation for the constant of `L:raw-block-indexed-cone` (TeX lines 232--248
and 330--332, `c_* = a_* j_*/4`), package theorem
`StratonovichHAMSecondMoment.IndexedCone.indexed_cone`.

Wrong variant: `c_* = a_* j_*` (no loss factor; the "exact first-mode
amplitude").  Counterexample: the package's scalar ground family
`scalarFamily` (`a_* = j_* = 1`, `λ ≡ 1`) and, for whatever `B, ω, ε_op` the
variant chooses, the damped blocks `D_m(u) = (1-s)e^u` with
`s = min(1/2, ε_op e^{-B}) > 0`, which are `ε_op`-close to `P(u) = e^u` on
`[0,B]`.  At `N = 1`, `u = 0` the product is `(1-s)² e^B < e^B`.  No junk-value
reliance.

`constant_contrast` applies the package theorem (with `c_* = a_* j_*/4`) at the
same family, blocks and point.

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

/-- The variant `c_* = a_* j_*` is false. -/
theorem cStar_eq_aj_fails :
    ¬ ∀ (G : GroundFamily ℝ) (ϱ : ℝ), 0 < ϱ → ϱ < 1 / 2 →
      ∃ B : ℕ, 1 ≤ B ∧ ∃ ω : ℝ, 0 < ω ∧ ∃ ε : ℝ, 0 < ε ∧
        ∀ N : ℕ, 1 ≤ N → ∀ σ : ℕ → ℝ, (∀ m ≤ N, σ m ∈ paramI) →
          (∀ m < N, |σ (m + 1) - σ m| ≤ ω) →
          ∀ D : ℕ → ℝ → ℝ →L[ℝ] ℝ,
            (∀ m ≤ N, ∀ u ∈ Icc (0 : ℝ) B, ‖D m u - G.P (σ m) u‖ ≤ ε) →
            ∀ u ∈ Icc (0 : ℝ) B,
              G.aStar * G.jStar * (1 - ϱ) ^ (N - 1) *
                  Real.exp ((B : ℝ) * ∑ m ∈ Finset.range N, G.lam (σ m) + u * G.lam (σ N)) ≤
                G.obs (D N u (chainState D B G.e0 N)) := by
  intro h
  obtain ⟨B, _, ω, hω, ε, hε, hall⟩ := h scalarFamily (1 / 4) (by norm_num) (by norm_num)
  have h0 : (0 : ℝ) ∈ paramI := by simp [paramI]
  set s := min (1 / 2) (ε / Real.exp B) with hs
  have hs0 : 0 < s := lt_min (by norm_num) (by positivity)
  have hs1 : s ≤ 1 / 2 := min_le_left _ _
  have hclose : ∀ m ≤ 1, ∀ u ∈ Icc (0 : ℝ) B,
      ‖dampedBlocks s m u - scalarFamily.P ((fun _ => (0 : ℝ)) m) u‖ ≤ ε := by
    intro m _ u hu
    refine (dampedBlocks_close hs0.le m 0 u).trans ?_
    have h1 : s ≤ ε / Real.exp B := min_le_right _ _
    rw [le_div_iff₀ (Real.exp_pos _)] at h1
    have h2 : s * Real.exp u ≤ s * Real.exp B :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hu.2) hs0.le
    linarith
  have := hall 1 le_rfl (fun _ => 0) (fun _ _ => h0) (fun _ _ => by simp [hω.le])
    (dampedBlocks s) hclose 0 ⟨le_rfl, Nat.cast_nonneg _⟩
  rw [dampedBlocks_value, scalar_sum, scalarFamily_aStar, scalarFamily_jStar] at this
  simp only [Nat.cast_one, mul_one, one_mul, pow_zero, zero_mul, add_zero,
    Nat.sub_self] at this
  have hlt : (1 - s) ^ (1 + 1) < 1 :=
    pow_lt_one₀ (by linarith) (by linarith) (by norm_num)
  have hE := Real.exp_pos (B : ℝ)
  nlinarith [mul_lt_mul_of_pos_right hlt hE]

/-- The package constant `c_* = a_* j_*/4` at the same family, blocks and
point. -/
theorem constant_contrast :
    ∃ B : ℕ, 1 ≤ B ∧ ∃ ε : ℝ, 0 < ε ∧
      ∀ s : ℝ, 0 ≤ s → s * Real.exp B ≤ ε →
        scalarFamily.aStar * scalarFamily.jStar / 4 * (1 - 1 / 4) ^ (1 - 1) *
            Real.exp ((B : ℝ) * ∑ _m ∈ Finset.range 1, scalarFamily.lam 0 +
              0 * scalarFamily.lam 0) ≤
          scalarFamily.obs (dampedBlocks s 1 0
            (chainState (dampedBlocks s) B scalarFamily.e0 1)) := by
  obtain ⟨B, hB, ω, hω, ε, hε, c, _, hcdef, hall⟩ :=
    indexed_cone scalarFamily (ϱ := 1 / 4) (by norm_num) (by norm_num)
  have h0 : (0 : ℝ) ∈ paramI := by simp [paramI]
  refine ⟨B, hB, ε, hε, fun s hs hsB => ?_⟩
  have hclose : ∀ m ≤ 1, ∀ u ∈ Icc (0 : ℝ) B,
      ‖dampedBlocks s m u - scalarFamily.P ((fun _ => (0 : ℝ)) m) u‖ ≤ ε := by
    intro m _ u hu
    refine (dampedBlocks_close hs m 0 u).trans ?_
    have h2 : s * Real.exp u ≤ s * Real.exp B :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hu.2) hs
    linarith
  have := (hall 1 le_rfl (fun _ => 0) (fun _ _ => h0) (fun _ _ => by simp [hω.le])
    (dampedBlocks s) hclose 0 ⟨le_rfl, Nat.cast_nonneg _⟩).1
  rw [hcdef] at this
  exact this

end Refutations.IndexedCone

end
