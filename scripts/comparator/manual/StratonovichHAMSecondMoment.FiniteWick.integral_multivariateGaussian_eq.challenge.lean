-- The printed type elaborates only under the module's scoped instances (`MatrixOrder`).
open scoped MatrixOrder Matrix.Norms.L2Operator in
/-- For a real N x N matrix K and continuous F on EuclideanSpace R (Fin N): the integral of F under multivariateGaussian 0 K equals the stdPi N integral of g -> F(toLp 2 (CFC.sqrt K *v g)). -/
theorem StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.FiniteWick.integral_multivariateGaussian_eq :
    ∀ {N : ℕ} (K : Matrix (Fin N) (Fin N) ℝ) {F : EuclideanSpace ℝ (Fin N) → ℝ},
      Continuous F →
        Eq (α := ℝ)
          (∫ (x : EuclideanSpace ℝ (Fin N)),
            F x ∂ProbabilityTheory.multivariateGaussian (0 : EuclideanSpace ℝ (Fin N)) K)
          (∫ (g : Fin N → ℝ),
            F
              (WithLp.toLp (2 : ENNReal)
                ((CFC.sqrt K).mulVec g)) ∂StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.GaussianIBP.stdPi N) := by
  sorry
