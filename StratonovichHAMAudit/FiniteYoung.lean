module
public import Mathlib.Tactic
public import Mathlib.Analysis.MeanInequalities
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace StratonovichHAMAudit.FiniteYoung

theorem weighted_natural_powers (L q : ℕ) (hL : 0 < L) (hq : q ≤ L) (x y : ℝ) :
    |x| ^ q * |y| ^ (L-q) ≤
      (q : ℝ) / (L : ℝ) * |x| ^ L + ((L-q : ℕ) : ℝ) / (L : ℝ) * |y| ^ L := by
  have hLr : 0 < (L : ℝ) := by exact_mod_cast hL
  have hLn : (L : ℝ) ≠ 0 := ne_of_gt hLr
  have hsum : (q : ℝ) / (L : ℝ) + ((L-q : ℕ) : ℝ) / (L : ℝ) = 1 := by
    rw [← add_div, Nat.cast_sub hq]
    have hn : (q : ℝ) + ((L : ℝ) - (q : ℝ)) = (L : ℝ) := by ring
    rw [hn, div_self hLn]
  have hx : (|x| ^ L) ^ ((q : ℝ) / (L : ℝ)) = |x| ^ q := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg x)]
    have he : (L : ℝ) * ((q : ℝ) / (L : ℝ)) = (q : ℝ) := by exact mul_div_cancel₀ _ hLn
    rw [he, Real.rpow_natCast]
  have hy : (|y| ^ L) ^ (((L-q : ℕ) : ℝ) / (L : ℝ)) = |y| ^ (L-q) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg y)]
    have he : (L : ℝ) * (((L-q : ℕ) : ℝ) / (L : ℝ)) = ((L-q : ℕ) : ℝ) := by
      exact mul_div_cancel₀ _ hLn
    rw [he, Real.rpow_natCast]
  have h := Real.geom_mean_le_arith_mean2_weighted
    (div_nonneg (Nat.cast_nonneg q) hLr.le)
    (div_nonneg (Nat.cast_nonneg (L-q)) hLr.le)
    (pow_nonneg (abs_nonneg x) L) (pow_nonneg (abs_nonneg y) L) hsum
  rw [hx, hy] at h
  exact h

end StratonovichHAMAudit.FiniteYoung
