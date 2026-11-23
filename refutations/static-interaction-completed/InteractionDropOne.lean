import StratonovichHAMSecondMoment.StaticInteractionCompleted

/-!
Refutation for
`StratonovichHAMSecondMoment.StaticInteractionCompleted.static_interaction_orders`
(`E:static-interaction`, main TeX lines 3238-3240, proof 3264-3311 at edf7085f).

Wrong variant: the bound `‖I‖² ≤ 𝓔(h,σ,λ) ‖(f,g)‖²` without the free term `1`.
Counterexample: `E = ℝ`, `T = S = id`, `(f,g) = 1`, `Z = (1, 0, 0, …)` (no interaction),
`zn = 0`, `α = λ = h = N1 = 1`, `R_α = D_Γ = 0`, `σ = 0`: every hypothesis holds, `I = 1`
and `𝓔 = 0`.  No junk-value reliance (`√0 = 0`, `0^n = 0` for `n ≥ 1` are genuine values).
`interaction_drop_one_contrast` is the package bound at the same point.

Expected outcome: compiles (refuted).
-/

set_option autoImplicit false

open scoped Nat

namespace Refutations.StaticInteractionCompleted

open StratonovichHAMSecondMoment.StaticInteractionCompleted
open StratonovichHAMSecondMoment.StaticPhaseCauchy (allOrdersA)
open StratonovichHAMSecondMoment.IntervalScalar (staticE staticL staticX staticB)

theorem id_norm_le_sqrt_e : ‖ContinuousLinearMap.id ℝ ℝ‖ ≤ √(Real.exp 1) :=
  ContinuousLinearMap.norm_id_le.trans
    (Real.one_le_sqrt.2 (Real.one_le_exp (by norm_num)))

/-- The instance: only the zeroth Duhamel phase is nonzero. -/
noncomputable def zInst : ℕ → ℝ := fun n => if n = 0 then 1 else 0

theorem zInst_succ {n : ℕ} (hn : 1 ≤ n) : zInst n = 0 := by
  simp [zInst]; omega

theorem inst_hcmp : ∀ n : ℕ, 1 ≤ n → ‖zInst n‖ ≤ ((1 : ℝ) * 1)⁻¹ * (fun _ => (0 : ℝ)) n := by
  intro n hn; simp [zInst_succ hn]

theorem inst_horders : ∀ n : ℕ, 1 ≤ n → (fun _ => (0 : ℝ)) n ≤
    (allOrdersA 1 * √0) ^ n * (1 : ℝ) ^ (((4 : ℝ) - 1) * (n : ℝ) / 2) /
      (n ! : ℝ) ^ (((3 : ℝ) - 1) / 2) * 1 := by
  intro n hn
  simp [zero_pow (by omega : n ≠ 0)]

theorem inst_hodd : ∀ r s, Odd (r + s) →
    inner ℝ (ContinuousLinearMap.id ℝ ℝ (zInst r)) (ContinuousLinearMap.id ℝ ℝ (zInst s)) = 0 := by
  intro r s hrs
  rcases Nat.eq_zero_or_pos r with hr | hr
  · have hs : 1 ≤ s := by subst hr; rcases hrs with ⟨k, hk⟩; omega
    simp [zInst_succ hs]
  · simp [zInst_succ hr]

theorem inst_hborn : ‖ContinuousLinearMap.id ℝ ℝ (zInst 1)‖ ^ 2 ≤
    Real.exp 1 * (0 * 1 ^ 2 * (1 : ℝ) ^ ((1 : ℝ) - 2) * (1 + 1 ^ 2 * 1 ^ 2) ^ 2 *
      ‖(1 : ℝ)‖ ^ 2) := by
  simp [zInst]

theorem inst_hmean : |inner ℝ (1 : ℝ) (ContinuousLinearMap.id ℝ ℝ (zInst 2))| ≤
    ‖(1 : ℝ)‖ * (√(Real.exp 1) * (0 * (1 + 1 ^ 2 * 1 ^ 2) * (1 : ℝ) ^ ((3 : ℝ) - 1) /
      (1 * (2 - 1) * (3 - 1)) * ‖(1 : ℝ)‖)) := by
  simp [zInst]

theorem inst_sum : ∑' n, (0 : ℝ) ^ n • zInst n = 1 := by
  rw [tsum_eq_single 0]
  · simp [zInst]
  · intro b hb; simp [zInst, hb]

theorem inst_staticE : staticE 1 (allOrdersA 1) 0 0 1 0 1 = 0 := by
  simp [staticE, staticL, staticX]

/-- `E:static-interaction` fails without the term `1`. -/
theorem interaction_drop_one_refuted :
    ¬ (∀ (T S : ℝ →L[ℝ] ℝ) (f0 : ℝ) (Z zn : ℕ → ℝ) (alpha R D h lam σ N1 : ℝ),
        0 < alpha → alpha < 2 → 0 ≤ R → 0 ≤ D → 0 < lam → 0 < h → lam * h ≤ 1 →
        ‖T‖ ≤ √(Real.exp 1) → ‖S‖ ≤ √(Real.exp 1) → (∀ x, T (S x) = x) → Z 0 = S f0 →
        (∀ n, 1 ≤ n → ‖Z n‖ ≤ (lam * h)⁻¹ * zn n) → N1 ≤ ‖f0‖ →
        (∀ n, 1 ≤ n → zn n ≤ (allOrdersA alpha * √R) ^ n * h ^ ((4 - alpha) * n / 2) /
          (n ! : ℝ) ^ ((3 - alpha) / 2) * N1) →
        (∀ r s, Odd (r + s) → inner ℝ (T (Z r)) (T (Z s)) = 0) →
        ‖T (Z 1)‖ ^ 2 ≤
          Real.exp 1 * (R * h ^ 2 * lam ^ (alpha - 2) * (1 + lam ^ 2 * h ^ 2) ^ 2 * ‖f0‖ ^ 2) →
        |inner ℝ f0 (T (Z 2))| ≤ ‖f0‖ * (√(Real.exp 1) * (D * (1 + lam ^ 2 * h ^ 2) *
          h ^ (3 - alpha) / (lam * (2 - alpha) * (3 - alpha)) * ‖f0‖)) →
        ‖T (∑' n, σ ^ n • Z n)‖ ^ 2 ≤ staticE alpha (allOrdersA alpha) R D h σ lam * ‖f0‖ ^ 2) := by
  intro H
  have h := H (ContinuousLinearMap.id ℝ ℝ) (ContinuousLinearMap.id ℝ ℝ) 1 zInst (fun _ => 0)
    1 0 0 1 1 0 1 (by norm_num) (by norm_num) le_rfl le_rfl (by norm_num) (by norm_num)
    (by norm_num) id_norm_le_sqrt_e id_norm_le_sqrt_e (fun _ => rfl) (by simp [zInst])
    inst_hcmp (by simp) inst_horders inst_hodd inst_hborn inst_hmean
  rw [ContinuousLinearMap.id_apply, inst_sum, inst_staticE] at h
  norm_num at h

/-- Contrast: the package bound at the same point. -/
theorem interaction_drop_one_contrast :
    ‖ContinuousLinearMap.id ℝ ℝ (∑' n, (0 : ℝ) ^ n • zInst n)‖ ^ 2 ≤
      (1 + staticE 1 (allOrdersA 1) 0 0 1 0 1) * ‖(1 : ℝ)‖ ^ 2 :=
  (static_interaction_orders (σ := 0) (ContinuousLinearMap.id ℝ ℝ) (ContinuousLinearMap.id ℝ ℝ)
    1 zInst (fun _ => 0) (alpha := 1) (R := 0) (D := 0) (h := 1) (lam := 1) (N1 := 1)
    (by norm_num) (by norm_num) le_rfl le_rfl (by norm_num) (by norm_num) (by norm_num)
    id_norm_le_sqrt_e id_norm_le_sqrt_e (fun _ => rfl) (by simp [zInst]) inst_hcmp (by simp)
    inst_horders inst_hodd inst_hborn inst_hmean).2.2

end Refutations.StaticInteractionCompleted
