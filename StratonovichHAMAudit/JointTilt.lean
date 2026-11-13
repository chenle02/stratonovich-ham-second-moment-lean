module
public import Mathlib.Tactic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace StratonovichHAMAudit.JointTilt

theorem tilt_exponent (r s c v w : ℝ) :
    -s^2*v/2+r*s*c+(r^2*w-2*r*s*c+s^2*v)/2 = r^2*w/2 := by
  ring

theorem wrong_sign_error (r s c v w : ℝ) :
    (-s^2*v/2+r*s*c+(r^2*w+2*r*s*c+s^2*v)/2)-r^2*w/2 = 2*r*s*c := by
  ring

theorem wrong_cost_error (r s c v w : ℝ) :
    (-s^2*v+r*s*c+(r^2*w-2*r*s*c+s^2*v)/2)-r^2*w/2 = -s^2*v/2 := by
  ring

theorem shifted_amplitude (delta a : ℝ) (hd : 0 < delta) :
    delta^((1-a)/2)*delta^(a/2)/Real.sqrt delta = 1 := by
  rw [← Real.rpow_add hd]
  have hsum : (1-a)/2+a/2 = (1:ℝ)/2 := by ring
  rw [hsum, ← Real.sqrt_eq_rpow]
  exact div_self (Real.sqrt_pos.2 hd).ne'

end StratonovichHAMAudit.JointTilt
