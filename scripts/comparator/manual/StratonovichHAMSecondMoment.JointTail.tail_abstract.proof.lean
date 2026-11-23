  set_option smartUnfolding false in
  (intro d alpha α₀ Γ μ hH G g hmeas hN0 Zr t hZr1 ht0 m n k hmn hk D hD T1 T2 ε hε η hη hbr hun hmk
   exact _root_.StratonovichHAMSecondMoment.JointTail.tail_abstract
     (StratonovichHamSecondMomentLeanAuditBridge.HomogHypothesis.homog_toP hH) hmeas hN0 hZr1 ht0
     hmn hk hD T1 T2 hε hη hbr
     (fun E b hb hA hμ => hun (StratonovichHamSecondMomentLeanAuditBridge.PairingInterface.edOfP E) b hb hA hμ)
     (fun E b hb hA hμ => hmk (StratonovichHamSecondMomentLeanAuditBridge.PairingInterface.edOfP E) b hb hA hμ))
