-- The printed type elaborates only under the module's scoped instances (`MatrixOrder`).
open scoped MatrixOrder Matrix.Norms.L2Operator in
/-- For a real N x N positive semidefinite matrix K: CFC.sqrt K * (CFC.sqrt K)^T = K. -/
theorem StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.FiniteWick.sqrt_mul_transpose :
    ∀ {N : ℕ} (K : Matrix (Fin N) (Fin N) ℝ), K.PosSemidef → CFC.sqrt K * (CFC.sqrt K).transpose = K := by
  exact @_root_.StratonovichHAMSecondMoment.FiniteWick.sqrt_mul_transpose
