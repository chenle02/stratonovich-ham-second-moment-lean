module
public import Mathlib.Tactic
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace StratonovichHAMAudit.RawValueCeiling

theorem exact_gap : (2:ℕ)*30^60 < 39^39*21^21 := by
  norm_num

theorem strict_log_gap (q a : ℝ) (ha : 0 < a) (hpos : 0 < q-2*a) :
    0 < (q*Real.log q+(q-2*a)*Real.log (q-2*a))/2
          -(q-a)*Real.log (q-a) := by
  have hq : 0 ≤ q := by linarith
  have hne : q ≠ q-2*a := by linarith
  have hc := Real.strictConvexOn_mul_log.2
  have h := hc hq hpos.le hne
    (show 0 < (1:ℝ)/2 by norm_num)
    (show 0 < (1:ℝ)/2 by norm_num)
    (show (1:ℝ)/2+(1:ℝ)/2=1 by norm_num)
  simp only [smul_eq_mul] at h
  have hm : (1:ℝ)/2*q+(1:ℝ)/2*(q-2*a)=q-a := by ring
  rw [hm] at h
  linarith

end StratonovichHAMAudit.RawValueCeiling
