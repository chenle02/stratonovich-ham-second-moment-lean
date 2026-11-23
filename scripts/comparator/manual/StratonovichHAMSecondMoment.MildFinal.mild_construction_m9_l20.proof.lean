  set_option smartUnfolding false in
  set_option linter.unusedSimpArgs false in
  (intro d
   unfold StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MildInterface.MildConstructionM9
   intro alpha α₀ Γ μ hH t ht x
   have h := (_root_.StratonovichHAMSecondMoment.MildFinal.mild_construction_l20.{0} d
     (StratonovichHamSecondMomentLeanAuditBridge.HomogHypothesis.homog_toP hH) _ _
     (StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.sfToP (StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SourceInterface.m9 (StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SourceFinal.source_field_l19 d) hH).field)
     t ht x).2.2
   simp only [StratonovichHamSecondMomentLeanAuditBridge.MildInterface.Ia_eq, StratonovichHamSecondMomentLeanAuditBridge.SourceInterface.uL2_eq]
   exact h)
