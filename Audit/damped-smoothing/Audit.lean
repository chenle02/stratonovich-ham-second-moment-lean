module
import StratonovichHAMSecondMoment.DampedSmoothing
import StratonovichHAMSecondMoment.WhiteModel
set_option autoImplicit false
set_option pp.all true
#check @StratonovichHAMSecondMoment.DampedSmoothing.smoothedCov
#print axioms StratonovichHAMSecondMoment.DampedSmoothing.smoothedCov
#check @StratonovichHAMSecondMoment.DampedSmoothing.coe_gaussMult_half
#print axioms StratonovichHAMSecondMoment.DampedSmoothing.coe_gaussMult_half
#check @StratonovichHAMSecondMoment.DampedSmoothing.smoothedCov_props
#print axioms StratonovichHAMSecondMoment.DampedSmoothing.smoothedCov_props
#check @StratonovichHAMSecondMoment.DampedSmoothing.smoothedCov_spectral
#print axioms StratonovichHAMSecondMoment.DampedSmoothing.smoothedCov_spectral
#check @StratonovichHAMSecondMoment.DampedSmoothing.spatial_smoothing_multiplier
#print axioms StratonovichHAMSecondMoment.DampedSmoothing.spatial_smoothing_multiplier
#check @StratonovichHAMSecondMoment.DampedSmoothing.spectral_gauss_test
#print axioms StratonovichHAMSecondMoment.DampedSmoothing.spectral_gauss_test
#check @StratonovichHAMSecondMoment.DampedSmoothing.spectral_multiplier_separation
#print axioms StratonovichHAMSecondMoment.DampedSmoothing.spectral_multiplier_separation
#check @StratonovichHAMSecondMoment.DampedSmoothing.charFun_gaussWeighted
#print axioms StratonovichHAMSecondMoment.DampedSmoothing.charFun_gaussWeighted
#check @StratonovichHAMSecondMoment.DampedSmoothing.spectralMeasure_unique
#print axioms StratonovichHAMSecondMoment.DampedSmoothing.spectralMeasure_unique
#check @StratonovichHAMSecondMoment.DampedSmoothing.smoothed_tempered
#print axioms StratonovichHAMSecondMoment.DampedSmoothing.smoothed_tempered
#check @StratonovichHAMSecondMoment.DampedSmoothing.smoothedCov_spectral_unique_paper
#print axioms StratonovichHAMSecondMoment.DampedSmoothing.smoothedCov_spectral_unique_paper
#check @StratonovichHAMSecondMoment.DampedSmoothing.spatial_smoothing_multiplier_paper
#print axioms StratonovichHAMSecondMoment.DampedSmoothing.spatial_smoothing_multiplier_paper
#check @StratonovichHAMSecondMoment.DampedSmoothing.damped_homogeneous_norms_whole_paper
#print axioms StratonovichHAMSecondMoment.DampedSmoothing.damped_homogeneous_norms_whole_paper

open MeasureTheory StratonovichHAMSecondMoment

namespace StratonovichHAMSecondMoment.Audit.DampedSmoothing

open StratonovichHAMSecondMoment.DampedSmoothing

/-- Consumer of the whole wrapper: for the white model (`H:homog` with `d = α = 1`,
`α₀ = 1/2`), the Gaussian-smoothed covariance `p_1 * δ₀` has spectral measure
`e^{-|ξ|²/2} μ`, and its smoothed second norm on `S = (0,∞)` at `θ = 1` is at most the
unsmoothed one. -/
private theorem audit_consumer :
    HomogHypothesis.IsSpectralMeasure (smoothedCov (WhiteModel.whiteCov 1) 1)
        (DampedNormsHomog.smoothed (WhiteModel.whiteSpectral 1)
          (DampedMultiplier.gaussMult (1 / 2))) ∧
      DampedNormsHomog.N2onSq (1 / 2) 1 (Set.Ioi 0)
          (DampedNormsHomog.smoothed (WhiteModel.whiteSpectral 1)
            (DampedMultiplier.gaussMult (1 / 2))) ≤
        DampedNormsHomog.N2onSq (1 / 2) 1 (Set.Ioi 0) (WhiteModel.whiteSpectral 1) := by
  have hH := WhiteModel.white_homogCovariance (c := 1) (a := 1 / 2) zero_le_one
    (by norm_num) (by norm_num)
  obtain ⟨-, -, hsp, -, -, hc⟩ := (damped_homogeneous_norms_whole_paper hH).2.2 1 one_pos
  exact ⟨hsp, (hc 1 one_pos _ _ measurableSet_Ioi measurableSet_Ioi le_rfl).2.2.2⟩

#check @audit_consumer
#print axioms audit_consumer

end StratonovichHAMSecondMoment.Audit.DampedSmoothing
