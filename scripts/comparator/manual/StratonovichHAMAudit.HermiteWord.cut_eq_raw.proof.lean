  intro C B V _ Good J F P v₀ N h0 hJ hF hP w hN
  rw [StratonovichHamSecondMomentLeanAuditBridge.HermiteWord.cut_eq, StratonovichHamSecondMomentLeanAuditBridge.HermiteWord.raw_eq]
  exact _root_.StratonovichHAMAudit.HermiteWord.cut_eq_raw Good J F P v₀ N h0 hJ hF hP w
    (by simpa only [StratonovichHamSecondMomentLeanAuditBridge.HermiteWord.counts_eq] using hN)
