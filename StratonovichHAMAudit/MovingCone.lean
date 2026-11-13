module
public import Mathlib.Tactic
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace StratonovichHAMAudit.MovingCone

theorem residual_budget (theta q d e : ℝ) (htheta : 0 ≤ theta)
    (hq : q ≤ 1/8) (hd0 : 0 ≤ d) (hd : d ≤ theta)
    (he : e ≤ theta/4) : q*(theta+d)+e ≤ theta/2 := by
  have hprod := mul_le_mul_of_nonneg_right hq (add_nonneg htheta hd0)
  nlinarith [hprod]

theorem cone_conversion (theta a x y rho : ℝ) (htheta : 0 ≤ theta)
    (ha : 0 < a) (hrho : rho < 1/2)
    (hx : (1-rho)*a ≤ x) (hy : y ≤ theta*a/2) :
    0 < x ∧ y ≤ theta*x := by
  have hprod : 0 < (1/2-rho)*a := mul_pos (by linarith) ha
  have hhalf : a/2 < x := by nlinarith [hprod]
  constructor
  · linarith
  · have hmul := mul_le_mul_of_nonneg_left hhalf.le htheta
    nlinarith [hmul]

theorem terminal_margin (j K theta e y : ℝ) (hj : 0 < j)
    (hbudget : 16*K*theta ≤ j) (he : e ≤ j/8)
    (hy : 3*j/4-2*K*theta-e ≤ y) : j/2 ≤ y ∧ 0 < y := by
  constructor <;> nlinarith

end StratonovichHAMAudit.MovingCone
