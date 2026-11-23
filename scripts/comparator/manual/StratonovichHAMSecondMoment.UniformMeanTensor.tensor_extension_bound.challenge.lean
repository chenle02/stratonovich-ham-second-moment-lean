-- Printed type with the printed coercions `(↑(↑v : α →ₘ[μ] E) : α → E)` written as the source's `(v : α → E)` (the printed form elaborates another instance path).
open scoped ContDiff in
/-- For 2 <= r < infinity, bounded A : H_0 -> L^r(I), f_j in H_0, orthonormal e_j in G and F = sum_j (A f_j) e_j a.e. in L^r(I; G): ||F|| <= ||A|| (sum_j ||f_j||^2)^(1/2) (L:uniform-mean-tensor on finite tensors). -/
theorem StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.UniformMeanTensor.tensor_extension_bound :
    ∀ {n : ℕ} {H0 G : Type} [inst : NormedAddCommGroup H0] [inst_1 : InnerProductSpace ℝ H0]
      [inst_2 : NormedAddCommGroup G] [inst_3 : InnerProductSpace ℝ G] {r : ENNReal}
      [inst_4 : Fact ((1 : ENNReal) ≤ r)],
      (2 : ENNReal) ≤ r →
        r ≠ ⊤ →
          ∀
            (A :
              H0 →L[ℝ]
                ↥(MeasureTheory.Lp ℝ r StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SpaceTimePositivity.timeMeasure))
            (f : Fin n → H0) (e : Fin n → G),
            Orthonormal ℝ e →
              ∀
                (F :
                  ↥(MeasureTheory.Lp G r StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SpaceTimePositivity.timeMeasure)),
                ((F : ℝ → G) =ᵐ[StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SpaceTimePositivity.timeMeasure]
                    fun (t : ℝ) =>
                    ∑ j : Fin n,
                      HSMul.hSMul (α := ℝ)
                        ((((A : H0 → ↥(MeasureTheory.Lp ℝ r StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SpaceTimePositivity.timeMeasure)) (f j)) : ℝ → ℝ)
                          t)
                        (e j)) →
                  ‖F‖ ≤ ‖A‖ * √(∑ j : Fin n, ‖f j‖ ^ (2 : ℕ)) := by
  sorry
