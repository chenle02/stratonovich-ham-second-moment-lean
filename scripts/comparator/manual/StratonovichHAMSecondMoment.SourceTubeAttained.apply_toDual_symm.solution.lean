-- Printed type replaced by the source's statement (CheckFidelity: the printed `Eq (α := ℝ)` elaborates the semiring of ℝ through `RCLike`, the source through `Real.semiring`).
set_option autoImplicit false in
/-- For M : H ->L[R] B with H a complete real inner product space, l in the dual of B and phi in the dual of H: l (M (R^-1 phi)) = phi (R^-1 (l o M)), R the Riesz map of H (auxiliary). -/
theorem StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.SourceTubeAttained.apply_toDual_symm.{u_1, u_2}
    {𝔅 : Type u_1} [NormedAddCommGroup 𝔅] [NormedSpace ℝ 𝔅] {H : Type u_2} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] (M : H →L[ℝ] 𝔅) (ℓ : StrongDual ℝ 𝔅) (φ : StrongDual ℝ H) :
    ℓ (M ((InnerProductSpace.toDual ℝ H).symm φ)) =
      φ ((InnerProductSpace.toDual ℝ H).symm (ℓ.comp M)) := by
  exact _root_.StratonovichHAMSecondMoment.SourceTubeAttained.apply_toDual_symm M ℓ φ
