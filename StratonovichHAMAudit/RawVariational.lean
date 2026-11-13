module
public import Mathlib.Tactic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace StratonovichHAMAudit.RawVariational

theorem dilation_factors (s alpha : ℝ) (hs : 0 < s) :
    s^(3-alpha)*s^(alpha-1)=s^2 ∧
    s^(3-alpha)*s^2/s=s^(4-alpha) := by
  constructor
  · have hsum : (3-alpha)+(alpha-1)=(2:ℝ) := by ring
    rw [← Real.rpow_add hs, hsum, Real.rpow_two]
  · calc
      s^(3-alpha)*s^2/s = s^((3-alpha)+(2:ℝ))/s := by
        rw [Real.rpow_add hs, Real.rpow_two]
      _ = s^(((3-alpha)+(2:ℝ))-(1:ℝ)) := by
        rw [Real.rpow_sub hs, Real.rpow_one]
      _ = s^(4-alpha) := by congr 1; ring

theorem label_score (c I v alpha : ℝ) (hc : 0 < c) (ha : alpha < 3) :
    c*(c^(1/(3-alpha))*I)-(c^(1/(3-alpha)))^(4-alpha)*v/2
      =c^((4-alpha)/(3-alpha))*(I-v/2) := by
  have hk : 3-alpha ≠ 0 := ne_of_gt (by linarith)
  have hsum : (1:ℝ)+1/(3-alpha)=(4-alpha)/(3-alpha) := by
    field_simp [hk]
    ring
  have hprod : (1/(3-alpha))*(4-alpha)=(4-alpha)/(3-alpha) := by ring
  have hmul : c*c^(1/(3-alpha))=c^((4-alpha)/(3-alpha)) := by
    calc
      c*c^(1/(3-alpha))=c^(1:ℝ)*c^(1/(3-alpha)) := by rw [Real.rpow_one]
      _ = c^((1:ℝ)+1/(3-alpha)) := (Real.rpow_add hc _ _).symm
      _ = c^((4-alpha)/(3-alpha)) := by rw [hsum]
  have hpow : (c^(1/(3-alpha)))^(4-alpha)=c^((4-alpha)/(3-alpha)) := by
    rw [← Real.rpow_mul hc.le, hprod]
  rw [← mul_assoc, hmul, hpow]
  ring

theorem positive_score (I v alpha : ℝ) (hI : 0 < I) (hv : 0 < v)
    (ha : alpha < 3) :
    0 < (I/v)^(1/(3-alpha))*I-((I/v)^(1/(3-alpha)))^(4-alpha)*v/2 := by
  let c : ℝ := I/v
  have hc : 0 < c := div_pos hI hv
  have hk : 3-alpha ≠ 0 := ne_of_gt (by linarith)
  have hsum : (1/(3-alpha))*(4-alpha)=1/(3-alpha)+(1:ℝ) := by
    field_simp [hk]
    ring
  have hpow : (c^(1/(3-alpha)))^(4-alpha)=c^(1/(3-alpha))*c := by
    rw [← Real.rpow_mul hc.le, hsum, Real.rpow_add hc, Real.rpow_one]
  have hcv : c*v=I := by
    dsimp [c]
    field_simp [ne_of_gt hv]
  have heq : c^(1/(3-alpha))*I-(c^(1/(3-alpha)))^(4-alpha)*v/2
      =c^(1/(3-alpha))*I/2 := by
    calc
      c^(1/(3-alpha))*I-(c^(1/(3-alpha)))^(4-alpha)*v/2
        =c^(1/(3-alpha))*I-c^(1/(3-alpha))*(c*v)/2 := by rw [hpow]; ring
      _ = c^(1/(3-alpha))*I/2 := by rw [hcv]; ring
  change 0 < c^(1/(3-alpha))*I-(c^(1/(3-alpha)))^(4-alpha)*v/2
  rw [heq]
  exact div_pos (mul_pos (Real.rpow_pos_of_pos hc _) hI) (by norm_num)

theorem strict_label_factor (alpha : ℝ) (ha : alpha < 3) :
    (2:ℝ) < (2:ℝ)^((4-alpha)/(3-alpha)) := by
  have hk : 0 < 3-alpha := by linarith
  have hm : (1:ℝ) < (4-alpha)/(3-alpha) := by
    apply (lt_div_iff₀ hk).2
    linarith
  have h := Real.rpow_lt_rpow_of_exponent_lt (x := (2:ℝ)) (by norm_num) hm
  simpa only [Real.rpow_one] using h

end StratonovichHAMAudit.RawVariational
