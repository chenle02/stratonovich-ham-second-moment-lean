  set_option smartUnfolding false in
  (intro d alpha α₀ Γ μ hH ε hε
   obtain ⟨E, h1, h2, h3⟩ := _root_.StratonovichHAMSecondMoment.PairingBridge.m4_bridge_of_ne_top
     (StratonovichHamSecondMomentLeanAuditBridge.HomogHypothesis.homog_toP hH) ε hε
   exact ⟨StratonovichHamSecondMomentLeanAuditBridge.PairingInterface.edOfP E, h1, h2, h3⟩)
