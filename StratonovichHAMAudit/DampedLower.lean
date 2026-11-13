module
public import Mathlib.Tactic
public import Mathlib.Analysis.Real.Pi.Bounds
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace StratonovichHAMAudit.DampedLower

theorem exact_margin : (9:ℕ)*2^28 < 157^3*5^4 := by
  norm_num

theorem pi_cube_certificate : (9:ℝ)*2^25/5^10 < Real.pi^3 := by
  have hp := Real.pi_gt_d2
  have hfrac : (3.14:ℝ) = 157/50 := by norm_num
  rw [hfrac] at hp
  have hpi : 0 < Real.pi := Real.pi_pos
  have hs : 0 < Real.pi^2+(157/50:ℝ)*Real.pi+(157/50:ℝ)^2 := by
    positivity
  have hm := mul_pos (sub_pos.mpr hp) hs
  have hr : (9:ℝ)*2^25/5^10 < (157/50:ℝ)^3 := by norm_num
  nlinarith

theorem rational_pi_gain :
    (157:ℝ)^3*5^4/(9*2^28) < Real.pi^3*5^10/(9*2^25) := by
  have hp := Real.pi_gt_d2
  have hfrac : (3.14:ℝ) = 157/50 := by norm_num
  rw [hfrac] at hp
  have hpi : 0 < Real.pi := Real.pi_pos
  have hs : 0 < Real.pi^2+(157/50:ℝ)*Real.pi+(157/50:ℝ)^2 := by
    positivity
  have hm := mul_pos (sub_pos.mpr hp) hs
  nlinarith

end StratonovichHAMAudit.DampedLower
