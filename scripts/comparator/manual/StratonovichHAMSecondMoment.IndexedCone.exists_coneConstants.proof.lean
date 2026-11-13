  intro F _ _ G ϱ hϱ
  obtain ⟨K, ha, hj⟩ :=
    _root_.StratonovichHAMSecondMoment.IndexedCone.exists_coneConstants
      (StratonovichHamSecondMomentLeanAuditBridge.IndexedCone.gToP G) hϱ
  exact ⟨StratonovichHamSecondMomentLeanAuditBridge.IndexedCone.cOfP K, ha, hj⟩
