module
public import Mathlib.Tactic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace StratonovichHAMAudit.ActualEvent

theorem finite_error_accumulation (C e : ℝ) (d : ℕ → ℝ)
    (hC : 1 ≤ C) (he : 0 ≤ e) (hzero : d 0 ≤ 0)
    (hstep : ∀ n, d (n+1) ≤ C*d n+C^n*e) (n : ℕ) :
    d n ≤ (n:ℝ)*C^n*e := by
  have hC0 : 0 ≤ C := by linarith
  induction n with
  | zero => simpa using hzero
  | succ n ih =>
    have hmul := mul_le_mul_of_nonneg_left ih hC0
    have hp : 0 ≤ C^n*e := mul_nonneg (pow_nonneg hC0 n) he
    have hg := mul_le_mul_of_nonneg_right hC hp
    simp only [one_mul] at hg
    rw [pow_succ]
    push_cast
    nlinarith [hstep n, hmul, hg]

theorem moderate_penalty (delta : ℝ) (hd : 0 < delta) :
    delta*(delta^(-(1:ℝ)/4)/Real.sqrt delta)=delta^((1:ℝ)/4) := by
  calc
    delta*(delta^(-(1:ℝ)/4)/Real.sqrt delta)
      = delta^(1:ℝ)*(delta^(-(1:ℝ)/4)/delta^((1:ℝ)/2)) := by
          rw [Real.rpow_one, Real.sqrt_eq_rpow]
    _ = delta^((1:ℝ)+(-(1:ℝ)/4-(1:ℝ)/2)) := by
          rw [Real.rpow_add hd, Real.rpow_sub hd]
    _ = delta^((1:ℝ)/4) := by congr 1; norm_num

end StratonovichHAMAudit.ActualEvent
