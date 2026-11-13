import StratonovichHAMAudit.GlobalOmega
-- Dividing out the retained P(x) factor recovers the failed weak envelope.
example : StratonovichHAMAudit.GlobalOmega.envelopeRational ((1:ℝ)/10) /
    (1-((1:ℝ)/10)^2+((1:ℝ)/10)^4/2) < 1 := by
  norm_num [StratonovichHAMAudit.GlobalOmega.envelopeRational]
