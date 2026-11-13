-- Statement copied from the source: the printed `‖M‖` loses the explicit
-- L∞-operator norm instance, so it does not elaborate back.
/-- For M : Matrix n n C, ||M_ij|| <= the L-infinity operator norm of M. -/
theorem StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.FiniteGaussianMatrix.norm_entry_le_linfty.{u_1} {n : Type u_1} [Fintype n] (M : Matrix n n ℂ) (i j : n) :
    ‖M i j‖ ≤ @Norm.norm _ (Matrix.linftyOpNormedAddCommGroup).toNorm M := by
  sorry
