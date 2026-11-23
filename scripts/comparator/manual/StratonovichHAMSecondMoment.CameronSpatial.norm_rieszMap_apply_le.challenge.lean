-- Written as in the source: the printed type elaborates another instance path or universe order.
open scoped ContDiff in
/-- If delta >= 0 and |<x, B z w>| <= delta ||z|| ||w|| for all z, w, then ||rieszMap B x|| <= delta. -/
theorem StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.CameronSpatial.norm_rieszMap_apply_le.{u_1, u_2, u_3} :
    ∀ {X : Type u_1} {Y : Type u_2} {H : Type u_3} [inst : NormedAddCommGroup X]
      [inst_1 : NormedSpace ℝ X] [inst_2 : NormedAddCommGroup Y] [inst_3 : InnerProductSpace ℝ Y]
      [inst_4 : CompleteSpace Y] [inst_5 : NormedAddCommGroup H] [inst_6 : InnerProductSpace ℝ H]
      [inst_7 : CompleteSpace H] (B : X →L[ℝ] Y →L[ℝ] H) {C : ℝ} (hC : (0 : ℝ) ≤ C)
      (hB : ∀ (z : X) (w : Y), ‖B z w‖ ≤ C * ‖z‖ * ‖w‖)
      (x : H) {δ : ℝ},
      (0 : ℝ) ≤ δ →
        (∀ (z : X) (w : Y), |Inner.inner ℝ x (B z w)| ≤ δ * ‖z‖ * ‖w‖) →
          ‖StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.CameronSpatial.rieszMap B hC hB x‖ ≤ δ := by
  sorry
