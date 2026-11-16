namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SourceTube
-- Statement copied from the source (the printed type round-trips only up to definitional equality).
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal Pointwise Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
/-- For S positive semidefinite, C >= 0 with C I - S positive semidefinite, vectors v j in a real normed space and p >= 1: both moments are integrable and (int |sum x j v j|^p dN(0,S))^(1/p) <= sqrt(C) (int |sum x j v j|^p dN(0,I))^(1/p). -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.SourceTube.source_finite_comparison_law {S : Matrix ι ι ℝ} (hS : S.PosSemidef) {C : ℝ}
    (hC : 0 ≤ C) (hSC : (C • (1 : Matrix ι ι ℝ) - S).PosSemidef) (v : ι → E) {p : ℝ}
    (hp : 1 ≤ p) :
    Integrable (fun x => ‖∑ j, x j • v j‖ ^ p)
        (multivariateGaussian (0 : EuclideanSpace ℝ ι) S) ∧
      Integrable (fun x => ‖∑ j, x j • v j‖ ^ p)
        (multivariateGaussian (0 : EuclideanSpace ℝ ι) 1) ∧
      (∫ x, ‖∑ j, x j • v j‖ ^ p ∂(multivariateGaussian (0 : EuclideanSpace ℝ ι) S)) ^ (1 / p)
        ≤ Real.sqrt C *
          (∫ x, ‖∑ j, x j • v j‖ ^ p
            ∂(multivariateGaussian (0 : EuclideanSpace ℝ ι) 1)) ^ (1 / p) := by
  bridge_revert_all
  exact @_root_.StratonovichHAMSecondMoment.SourceTube.source_finite_comparison_law
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SourceTube
