-- Printed type with the printed coercions `(↑(↑v : α →ₘ[μ] E) : α → E)` written as the source's `(v : α → E)` (the printed form elaborates another instance path).
open scoped ContDiff in
/-- For bounded A : H_0 -> L^r(I), f in H_0, orthonormal (e_j) in G and F_j = (A f) e_j a.e. in L^r(I; G): ||F_i - F_j|| = sqrt 2 ||A f|| for i != j (the non-compactness sentence of L:uniform-mean-tensor). -/
theorem StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.UniformMeanTensor.tensor_noncompact :
    ∀ {H0 G : Type} [inst : NormedAddCommGroup H0] [inst_1 : InnerProductSpace ℝ H0]
      [inst_2 : NormedAddCommGroup G] [inst_3 : InnerProductSpace ℝ G] {r : ENNReal}
      [inst_4 : Fact ((1 : ENNReal) ≤ r)]
      (A : H0 →L[ℝ] ↥(MeasureTheory.Lp ℝ r StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SpaceTimePositivity.timeMeasure))
      (f : H0) (e : ℕ → G),
      Orthonormal ℝ e →
        ∀ (F : ℕ → ↥(MeasureTheory.Lp G r StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SpaceTimePositivity.timeMeasure)),
          (∀ (j : ℕ),
              ((F j) : ℝ → G) =ᵐ[StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SpaceTimePositivity.timeMeasure]
                fun (t : ℝ) =>
                HSMul.hSMul (α := ℝ)
                  ((((A : H0 → ↥(MeasureTheory.Lp ℝ r StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SpaceTimePositivity.timeMeasure)) f) : ℝ → ℝ)
                    t)
                  (e j)) →
            ∀ (i j : ℕ),
              i ≠ j →
                ‖F i - F j‖ =
                  √(2 : ℝ) *
                    Norm.norm (E :=
                      ↥(MeasureTheory.Lp ℝ r
                          StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SpaceTimePositivity.timeMeasure))
                      ((A :
                            H0 →
                              ↥(MeasureTheory.Lp ℝ r
                                  StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SpaceTimePositivity.timeMeasure))
                          f :
                        ↥(MeasureTheory.Lp ℝ r
                            StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SpaceTimePositivity.timeMeasure)) := by
  sorry
