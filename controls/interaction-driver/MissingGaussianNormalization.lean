module
import StratonovichHAMAudit.InteractionDriver
set_option autoImplicit false
example : (1/Real.sqrt (2:ℝ))*Real.sqrt 8 = 1 := by
  have h8 : Real.sqrt (8:ℝ) = 2*Real.sqrt 2 := by
    rw [show (8:ℝ)=4*2 by norm_num, Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 4)]
    norm_num
  rw [h8]
  have hs : Real.sqrt (2:ℝ) ≠ 0 := (Real.sqrt_pos.2 (by norm_num : (0:ℝ)<2)).ne'
  field_simp [hs]
  norm_num
