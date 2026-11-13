import StratonovichHAMAudit.RawValueCeiling
-- Dropping a>0 would assert strictness at a=0,q=3, where the gap is zero.
example : 0 < ((3:ℝ)*Real.log 3+3*Real.log 3)/2-3*Real.log 3 := by
  ring_nf
  norm_num
