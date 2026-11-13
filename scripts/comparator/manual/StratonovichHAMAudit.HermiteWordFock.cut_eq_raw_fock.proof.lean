  intro X _ _ m B K T u Nc w hN
  rw [StratonovichHamSecondMomentLeanAuditBridge.HermiteWord.cut_eq, StratonovichHamSecondMomentLeanAuditBridge.HermiteWord.raw_eq]
  exact _root_.StratonovichHAMAudit.HermiteWordFock.cut_eq_raw_fock K T u Nc w
    (by simpa only [StratonovichHamSecondMomentLeanAuditBridge.HermiteWord.counts_eq] using hN)
