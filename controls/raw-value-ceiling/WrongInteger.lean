import StratonovichHAMAudit.RawValueCeiling
-- Reversing the exact integer comparison fails at a concrete False.
example : (39:ℕ)^39*21^21 ≤ 2*30^60 := by
  norm_num
