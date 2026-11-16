module
import StratonovichHAMSecondMoment.WhiteModel
set_option autoImplicit false
set_option pp.all true
#check @StratonovichHAMSecondMoment.WhiteModel.whiteCov
#print axioms StratonovichHAMSecondMoment.WhiteModel.whiteCov
#check @StratonovichHAMSecondMoment.WhiteModel.whiteSpectral
#print axioms StratonovichHAMSecondMoment.WhiteModel.whiteSpectral
#check @StratonovichHAMSecondMoment.WhiteModel.isLocallyFiniteMeasure_smul
#print axioms StratonovichHAMSecondMoment.WhiteModel.isLocallyFiniteMeasure_smul
#check @StratonovichHAMSecondMoment.WhiteModel.whiteCov_radon
#print axioms StratonovichHAMSecondMoment.WhiteModel.whiteCov_radon
#check @StratonovichHAMSecondMoment.WhiteModel.whiteSpectral_radon
#print axioms StratonovichHAMSecondMoment.WhiteModel.whiteSpectral_radon
#check @StratonovichHAMSecondMoment.WhiteModel.whiteCov_even
#print axioms StratonovichHAMSecondMoment.WhiteModel.whiteCov_even
#check @StratonovichHAMSecondMoment.WhiteModel.whiteSpectral_even
#print axioms StratonovichHAMSecondMoment.WhiteModel.whiteSpectral_even
#check @StratonovichHAMSecondMoment.WhiteModel.whiteCov_tempered
#print axioms StratonovichHAMSecondMoment.WhiteModel.whiteCov_tempered
#check @StratonovichHAMSecondMoment.WhiteModel.whiteSpectral_tempered
#print axioms StratonovichHAMSecondMoment.WhiteModel.whiteSpectral_tempered
#check @StratonovichHAMSecondMoment.WhiteModel.integral_whiteCov
#print axioms StratonovichHAMSecondMoment.WhiteModel.integral_whiteCov
#check @StratonovichHAMSecondMoment.WhiteModel.whiteCov_posdef
#print axioms StratonovichHAMSecondMoment.WhiteModel.whiteCov_posdef
#check @StratonovichHAMSecondMoment.WhiteModel.inner_integral_eq_fourier
#print axioms StratonovichHAMSecondMoment.WhiteModel.inner_integral_eq_fourier
#check @StratonovichHAMSecondMoment.WhiteModel.whiteSpectral_isSpectral
#print axioms StratonovichHAMSecondMoment.WhiteModel.whiteSpectral_isSpectral
#check @StratonovichHAMSecondMoment.WhiteModel.whiteCov_scaling
#print axioms StratonovichHAMSecondMoment.WhiteModel.whiteCov_scaling
#check @StratonovichHAMSecondMoment.WhiteModel.whiteSpectral_homogeneous
#print axioms StratonovichHAMSecondMoment.WhiteModel.whiteSpectral_homogeneous
#check @StratonovichHAMSecondMoment.WhiteModel.white_homogCovariance
#print axioms StratonovichHAMSecondMoment.WhiteModel.white_homogCovariance
#check @StratonovichHAMSecondMoment.WhiteModel.whiteSpectral_closedBall
#print axioms StratonovichHAMSecondMoment.WhiteModel.whiteSpectral_closedBall
#check @StratonovichHAMSecondMoment.WhiteModel.whiteSpectral_ball
#print axioms StratonovichHAMSecondMoment.WhiteModel.whiteSpectral_ball
#check @StratonovichHAMSecondMoment.WhiteModel.whiteSpectral_closedBall_toReal
#print axioms StratonovichHAMSecondMoment.WhiteModel.whiteSpectral_closedBall_toReal
#check @StratonovichHAMSecondMoment.WhiteModel.spatialPair_whiteCov
#print axioms StratonovichHAMSecondMoment.WhiteModel.spatialPair_whiteCov
#check @StratonovichHAMSecondMoment.WhiteModel.spatialEnergy_whiteCov
#print axioms StratonovichHAMSecondMoment.WhiteModel.spatialEnergy_whiteCov
#check @StratonovichHAMSecondMoment.WhiteModel.pairing_whiteCov
#print axioms StratonovichHAMSecondMoment.WhiteModel.pairing_whiteCov
#check @StratonovichHAMSecondMoment.WhiteModel.pairing_sq_whiteCov
#print axioms StratonovichHAMSecondMoment.WhiteModel.pairing_sq_whiteCov
#check @StratonovichHAMSecondMoment.WhiteModel.F0_inner_white
#print axioms StratonovichHAMSecondMoment.WhiteModel.F0_inner_white
#check @StratonovichHAMSecondMoment.WhiteModel.F0_white
#print axioms StratonovichHAMSecondMoment.WhiteModel.F0_white
#check @StratonovichHAMSecondMoment.WhiteModel.two_pow_F0_white
#print axioms StratonovichHAMSecondMoment.WhiteModel.two_pow_F0_white
#check @StratonovichHAMSecondMoment.WhiteModel.white_bracket_lower
#print axioms StratonovichHAMSecondMoment.WhiteModel.white_bracket_lower
#check @StratonovichHAMSecondMoment.WhiteModel.white_bracket_upper
#print axioms StratonovichHAMSecondMoment.WhiteModel.white_bracket_upper
#check @StratonovichHAMSecondMoment.WhiteModel.white_model_paper
#print axioms StratonovichHAMSecondMoment.WhiteModel.white_model_paper
#check @StratonovichHAMSecondMoment.WhiteModel.white_pairing_paper
#print axioms StratonovichHAMSecondMoment.WhiteModel.white_pairing_paper
#check @StratonovichHAMSecondMoment.WhiteModel.white_score_arithmetic_paper
#print axioms StratonovichHAMSecondMoment.WhiteModel.white_score_arithmetic_paper

open MeasureTheory StratonovichHAMSecondMoment

namespace StratonovichHAMSecondMoment.Audit.WhiteModel

open StratonovichHAMSecondMoment.WhiteModel

/-- Consumer of the wrappers: for `c > 0`, `0 < a < 1`, the white model satisfies
`H:homog` with `d = α = 1`, its unit-ball spectral mass is `c/π`, and the lower side of the
spatial bracket at `z = c²/6` is the lower formula of `E:white-moment-bounds`. -/
private theorem audit_consumer {c a : ℝ} (hc : 0 < c) (ha0 : 0 < a) (ha1 : a < 1) :
    HomogHypothesis.HomogCovariance 1 1 a (whiteCov c) (whiteSpectral c) ∧
      (whiteSpectral c (Metric.closedBall 0 1)).toReal = c / Real.pi ∧
      (2 : ℝ) ^ (((4 : ℝ) - 1) / (3 - 1)) * TemporalEquilibrium.mass a ^ (-(1 / ((3 : ℝ) - 1))) *
          SpatialFourLinear.F0 1 (c ^ 2 / 6) = WhiteRelativeWidth.lowerFormula c a := by
  obtain ⟨hH, -, hV, -⟩ := white_model_paper hc.le ha0 ha1
  refine ⟨hH, ?_, (white_score_arithmetic_paper hc ha0 ha1).2.2.1⟩
  rw [hV, ENNReal.toReal_ofReal (by positivity)]

end StratonovichHAMSecondMoment.Audit.WhiteModel
