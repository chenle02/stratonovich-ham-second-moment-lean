-- The printed type elaborates only under the module's scoped instances (`MatrixOrder`).
open scoped MatrixOrder Matrix.Norms.L2Operator in
/-- For a real N x N matrix K and continuous F on EuclideanSpace R (Fin N): F is integrable under multivariateGaussian 0 K iff g -> F(toLp 2 (CFC.sqrt K *v g)) is integrable under stdPi N. -/
theorem StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.FiniteWick.integrable_multivariateGaussian_iff :
    ∀ {N : ℕ} (K : Matrix (Fin N) (Fin N) ℝ) {F : EuclideanSpace ℝ (Fin N) → ℝ},
      Continuous F →
        (MeasureTheory.Integrable F
            (ProbabilityTheory.multivariateGaussian (0 : EuclideanSpace ℝ (Fin N)) K) ↔
          MeasureTheory.Integrable (ε := ℝ)
            (fun (g : Fin N → ℝ) => F (WithLp.toLp (2 : ENNReal) ((CFC.sqrt K).mulVec g)))
            (StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.GaussianIBP.stdPi N)) := by
  sorry
