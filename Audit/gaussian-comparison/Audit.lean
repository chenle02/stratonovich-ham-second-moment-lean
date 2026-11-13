module
import StratonovichHAMSecondMoment.GaussianComparison
set_option autoImplicit false
set_option pp.all true
#check @StratonovichHAMSecondMoment.GaussianComparison.multivariateGaussian_conv
#print axioms StratonovichHAMSecondMoment.GaussianComparison.multivariateGaussian_conv
#check @StratonovichHAMSecondMoment.GaussianComparison.seminorm_le_mul_norm
#print axioms StratonovichHAMSecondMoment.GaussianComparison.seminorm_le_mul_norm
#check @StratonovichHAMSecondMoment.GaussianComparison.seminorm_continuous
#print axioms StratonovichHAMSecondMoment.GaussianComparison.seminorm_continuous
#check @StratonovichHAMSecondMoment.GaussianComparison.integrable_seminorm_rpow
#print axioms StratonovichHAMSecondMoment.GaussianComparison.integrable_seminorm_rpow
#check @StratonovichHAMSecondMoment.GaussianComparison.convexOn_seminorm_rpow
#print axioms StratonovichHAMSecondMoment.GaussianComparison.convexOn_seminorm_rpow
#check @StratonovichHAMSecondMoment.GaussianComparison.gaussian_seminorm_moment_le
#print axioms StratonovichHAMSecondMoment.GaussianComparison.gaussian_seminorm_moment_le
#check @StratonovichHAMSecondMoment.GaussianComparison.gaussian_seminorm_moment_le_paper
#print axioms StratonovichHAMSecondMoment.GaussianComparison.gaussian_seminorm_moment_le_paper
#check @StratonovichHAMSecondMoment.GaussianComparison.coordSeminorm
#print axioms StratonovichHAMSecondMoment.GaussianComparison.coordSeminorm
#check @StratonovichHAMSecondMoment.GaussianComparison.coordSeminorm_apply
#print axioms StratonovichHAMSecondMoment.GaussianComparison.coordSeminorm_apply
#check @StratonovichHAMSecondMoment.GaussianComparison.integral_coord_sq
#print axioms StratonovichHAMSecondMoment.GaussianComparison.integral_coord_sq

open MeasureTheory ProbabilityTheory StratonovichHAMSecondMoment

namespace StratonovichHAMSecondMoment.Audit.GaussianComparison

open StratonovichHAMSecondMoment.GaussianComparison

/-- Consumer of the wrapper: for positive semidefinite `A`, the second moment of
the Euclidean norm grows when the identity is added to the covariance. -/
private theorem audit_consumer {ι : Type} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℝ} (hA : A.PosSemidef) :
    ∫ x, ‖x‖ ^ (2 : ℝ) ∂(multivariateGaussian (0 : EuclideanSpace ℝ ι) A) ≤
      ∫ x, ‖x‖ ^ (2 : ℝ) ∂(multivariateGaussian (0 : EuclideanSpace ℝ ι) (A + 1)) := by
  have h := (gaussian_seminorm_moment_le_paper hA (B := A + 1)
    (by simpa using Matrix.PosSemidef.one) (normSeminorm ℝ _) 2 (by norm_num)).2.2
  simpa using h

#check @audit_consumer
#print axioms audit_consumer

end StratonovichHAMSecondMoment.Audit.GaussianComparison
