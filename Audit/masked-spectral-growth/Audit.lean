module
import StratonovichHAMSecondMoment.MaskedSpectralGrowth
set_option autoImplicit false
set_option pp.all true
#check @StratonovichHAMSecondMoment.MaskedSpectralGrowth.integrable_gauss_of_tempered
#print axioms StratonovichHAMSecondMoment.MaskedSpectralGrowth.integrable_gauss_of_tempered
#check @StratonovichHAMSecondMoment.MaskedSpectralGrowth.spectral_gaussTest
#print axioms StratonovichHAMSecondMoment.MaskedSpectralGrowth.spectral_gaussTest
#check @StratonovichHAMSecondMoment.MaskedSpectralGrowth.spectral_translated_gauss
#print axioms StratonovichHAMSecondMoment.MaskedSpectralGrowth.spectral_translated_gauss
#check @StratonovichHAMSecondMoment.MaskedSpectralGrowth.sq_rpow_half
#print axioms StratonovichHAMSecondMoment.MaskedSpectralGrowth.sq_rpow_half
#check @StratonovichHAMSecondMoment.MaskedSpectralGrowth.gdens
#print axioms StratonovichHAMSecondMoment.MaskedSpectralGrowth.gdens
#check @StratonovichHAMSecondMoment.MaskedSpectralGrowth.measurable_gdens
#print axioms StratonovichHAMSecondMoment.MaskedSpectralGrowth.measurable_gdens
#check @StratonovichHAMSecondMoment.MaskedSpectralGrowth.coe_gdens
#print axioms StratonovichHAMSecondMoment.MaskedSpectralGrowth.coe_gdens
#check @StratonovichHAMSecondMoment.MaskedSpectralGrowth.charFun_map_withDensity
#print axioms StratonovichHAMSecondMoment.MaskedSpectralGrowth.charFun_map_withDensity
#check @StratonovichHAMSecondMoment.MaskedSpectralGrowth.charFun_smul_withDensity
#print axioms StratonovichHAMSecondMoment.MaskedSpectralGrowth.charFun_smul_withDensity
#check @StratonovichHAMSecondMoment.MaskedSpectralGrowth.scaling_constants
#print axioms StratonovichHAMSecondMoment.MaskedSpectralGrowth.scaling_constants
#check @StratonovichHAMSecondMoment.MaskedSpectralGrowth.map_smul_of_scaling
#print axioms StratonovichHAMSecondMoment.MaskedSpectralGrowth.map_smul_of_scaling
#check @StratonovichHAMSecondMoment.MaskedSpectralGrowth.spectralHomogeneous_of_scaling
#print axioms StratonovichHAMSecondMoment.MaskedSpectralGrowth.spectralHomogeneous_of_scaling
#check @StratonovichHAMSecondMoment.MaskedSpectralGrowth.spectralHomogeneous_of_homog
#print axioms StratonovichHAMSecondMoment.MaskedSpectralGrowth.spectralHomogeneous_of_homog
#check @StratonovichHAMSecondMoment.MaskedSpectralGrowth.MGamma
#print axioms StratonovichHAMSecondMoment.MaskedSpectralGrowth.MGamma
#check @StratonovichHAMSecondMoment.MaskedSpectralGrowth.CGamma
#print axioms StratonovichHAMSecondMoment.MaskedSpectralGrowth.CGamma
#check @StratonovichHAMSecondMoment.MaskedSpectralGrowth.integrable_gauss_zero
#print axioms StratonovichHAMSecondMoment.MaskedSpectralGrowth.integrable_gauss_zero
#check @StratonovichHAMSecondMoment.MaskedSpectralGrowth.MGamma_pos
#print axioms StratonovichHAMSecondMoment.MaskedSpectralGrowth.MGamma_pos
#check @StratonovichHAMSecondMoment.MaskedSpectralGrowth.gauss_const_cancel
#print axioms StratonovichHAMSecondMoment.MaskedSpectralGrowth.gauss_const_cancel
#check @StratonovichHAMSecondMoment.MaskedSpectralGrowth.masked_gaussian_transform
#print axioms StratonovichHAMSecondMoment.MaskedSpectralGrowth.masked_gaussian_transform
#check @StratonovichHAMSecondMoment.MaskedSpectralGrowth.translated_gauss_le
#print axioms StratonovichHAMSecondMoment.MaskedSpectralGrowth.translated_gauss_le
#check @StratonovichHAMSecondMoment.MaskedSpectralGrowth.closedBall_le
#print axioms StratonovichHAMSecondMoment.MaskedSpectralGrowth.closedBall_le
#check @StratonovichHAMSecondMoment.MaskedSpectralGrowth.masked_spectral_growth
#print axioms StratonovichHAMSecondMoment.MaskedSpectralGrowth.masked_spectral_growth
#check @StratonovichHAMSecondMoment.MaskedSpectralGrowth.masked_spectral_growth_paper
#print axioms StratonovichHAMSecondMoment.MaskedSpectralGrowth.masked_spectral_growth_paper

open MeasureTheory StratonovichHAMSecondMoment

namespace StratonovichHAMSecondMoment.Audit.MaskedSpectralGrowth

open StratonovichHAMSecondMoment.MaskedSpectralGrowth

/-- Consumer of the wrapper: under `H:homog` and `Γ ≠ 0`, every unit ball has
finite `μ`-mass, and `μ` is `α`-homogeneous. -/
private theorem audit_consumer {d : ℕ} {alpha alpha0 : ℝ} {Γ μ : Measure (HomogHypothesis.Rd d)}
    (h : HomogHypothesis.HomogCovariance d alpha alpha0 Γ μ) (hΓ : Γ ≠ 0)
    (y : HomogHypothesis.Rd d) :
    μ (Metric.closedBall y 1) < ⊤ ∧ SpectralHomog.SpectralHomogeneous μ alpha :=
  ⟨lt_of_le_of_lt ((masked_spectral_growth_paper h hΓ).2.2 y 1 one_pos).2.2.2.2.2.2
    ENNReal.ofReal_lt_top, spectralHomogeneous_of_homog h⟩

#check @audit_consumer
#print axioms audit_consumer

example : MGamma (0 : Measure (HomogHypothesis.Rd 1)) = 0 := by simp [MGamma]

end StratonovichHAMSecondMoment.Audit.MaskedSpectralGrowth
