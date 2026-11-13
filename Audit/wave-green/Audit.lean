module
import StratonovichHAMSecondMoment.WaveGreen
set_option autoImplicit false
set_option pp.all true
#check @StratonovichHAMSecondMoment.WaveGreen.waveGreen
#print axioms StratonovichHAMSecondMoment.WaveGreen.waveGreen
#check @StratonovichHAMSecondMoment.WaveGreen.waveGreen_other
#print axioms StratonovichHAMSecondMoment.WaveGreen.waveGreen_other
#check @StratonovichHAMSecondMoment.WaveGreen.waveGreen_of_nonpos
#print axioms StratonovichHAMSecondMoment.WaveGreen.waveGreen_of_nonpos
#check @StratonovichHAMSecondMoment.WaveGreen.gamma_three_halves
#print axioms StratonovichHAMSecondMoment.WaveGreen.gamma_three_halves
#check @StratonovichHAMSecondMoment.WaveGreen.mass_one
#print axioms StratonovichHAMSecondMoment.WaveGreen.mass_one
#check @StratonovichHAMSecondMoment.WaveGreen.radial2
#print axioms StratonovichHAMSecondMoment.WaveGreen.radial2
#check @StratonovichHAMSecondMoment.WaveGreen.radial2_nonneg
#print axioms StratonovichHAMSecondMoment.WaveGreen.radial2_nonneg
#check @StratonovichHAMSecondMoment.WaveGreen.radial2_eq_zero
#print axioms StratonovichHAMSecondMoment.WaveGreen.radial2_eq_zero
#check @StratonovichHAMSecondMoment.WaveGreen.hasDerivAt_radial2
#print axioms StratonovichHAMSecondMoment.WaveGreen.hasDerivAt_radial2
#check @StratonovichHAMSecondMoment.WaveGreen.integral_radial2
#print axioms StratonovichHAMSecondMoment.WaveGreen.integral_radial2
#check @StratonovichHAMSecondMoment.WaveGreen.mass_two
#print axioms StratonovichHAMSecondMoment.WaveGreen.mass_two
#check @StratonovichHAMSecondMoment.WaveGreen.mass_three
#print axioms StratonovichHAMSecondMoment.WaveGreen.mass_three
#check @StratonovichHAMSecondMoment.WaveGreen.waveGreen_mass
#print axioms StratonovichHAMSecondMoment.WaveGreen.waveGreen_mass
#check @StratonovichHAMSecondMoment.WaveGreen.isFiniteMeasure_waveGreen
#print axioms StratonovichHAMSecondMoment.WaveGreen.isFiniteMeasure_waveGreen
#check @StratonovichHAMSecondMoment.WaveGreen.instIsFiniteMeasureWaveGreen
#print axioms StratonovichHAMSecondMoment.WaveGreen.instIsFiniteMeasureWaveGreen
#check @StratonovichHAMSecondMoment.WaveGreen.waveGreen_greenMass
#print axioms StratonovichHAMSecondMoment.WaveGreen.waveGreen_greenMass
#check @StratonovichHAMSecondMoment.WaveGreen.waveGreen_compl_closedBall
#print axioms StratonovichHAMSecondMoment.WaveGreen.waveGreen_compl_closedBall
#check @StratonovichHAMSecondMoment.WaveGreen.scaling_one
#print axioms StratonovichHAMSecondMoment.WaveGreen.scaling_one
#check @StratonovichHAMSecondMoment.WaveGreen.scaling_two
#print axioms StratonovichHAMSecondMoment.WaveGreen.scaling_two
#check @StratonovichHAMSecondMoment.WaveGreen.scaling_three
#print axioms StratonovichHAMSecondMoment.WaveGreen.scaling_three
#check @StratonovichHAMSecondMoment.WaveGreen.waveGreen_scaling
#print axioms StratonovichHAMSecondMoment.WaveGreen.waveGreen_scaling
#check @StratonovichHAMSecondMoment.WaveGreen.waveGreen_paper
#print axioms StratonovichHAMSecondMoment.WaveGreen.waveGreen_paper
#check @StratonovichHAMSecondMoment.WaveGreen.N0_waveGreen
#print axioms StratonovichHAMSecondMoment.WaveGreen.N0_waveGreen
#check @StratonovichHAMSecondMoment.WaveGreen.damped_homogeneous_norms_wave
#print axioms StratonovichHAMSecondMoment.WaveGreen.damped_homogeneous_norms_wave
#check @StratonovichHAMSecondMoment.WaveGreen.coordOne
#print axioms StratonovichHAMSecondMoment.WaveGreen.coordOne
#check @StratonovichHAMSecondMoment.WaveGreen.coordOne_apply
#print axioms StratonovichHAMSecondMoment.WaveGreen.coordOne_apply
#check @StratonovichHAMSecondMoment.WaveGreen.coordOne_mp
#print axioms StratonovichHAMSecondMoment.WaveGreen.coordOne_mp
#check @StratonovichHAMSecondMoment.WaveGreen.norm_coord_one
#print axioms StratonovichHAMSecondMoment.WaveGreen.norm_coord_one
#check @StratonovichHAMSecondMoment.WaveGreen.inner_coord_one
#print axioms StratonovichHAMSecondMoment.WaveGreen.inner_coord_one
#check @StratonovichHAMSecondMoment.WaveGreen.ball_eq_preimage_coordOne
#print axioms StratonovichHAMSecondMoment.WaveGreen.ball_eq_preimage_coordOne
#check @StratonovichHAMSecondMoment.WaveGreen.integral_exp_Ioo
#print axioms StratonovichHAMSecondMoment.WaveGreen.integral_exp_Ioo
#check @StratonovichHAMSecondMoment.WaveGreen.single_coord_one
#print axioms StratonovichHAMSecondMoment.WaveGreen.single_coord_one
#check @StratonovichHAMSecondMoment.WaveGreen.waveGreen_fourier_one
#print axioms StratonovichHAMSecondMoment.WaveGreen.waveGreen_fourier_one

open MeasureTheory StratonovichHAMSecondMoment

namespace StratonovichHAMSecondMoment.Audit.WaveGreen

open StratonovichHAMSecondMoment.WaveGreen

/-- Consumer of the wrapper: under `H:homog` alone, `N₀(1) = 1` for the wave
Green measures, the `N₂` scaling at `θ = 2`, and the `N₂` tail limit. -/
private theorem audit_consumer {d : ℕ} {alpha alpha0 : ℝ}
    {Γ μ : Measure (HomogHypothesis.Rd d)}
    (h : HomogHypothesis.HomogCovariance d alpha alpha0 Γ μ) :
    DampedNormsHomog.N0 (waveGreen d) 1 = 1 ∧
      DampedNorms.N2sq alpha0 2 μ = 2 ^ (-(4 - alpha - alpha0)) * DampedNorms.N2sq alpha0 1 μ ∧
      Filter.Tendsto (fun M => DampedNormsHomog.N2tail alpha0 M μ) Filter.atTop (nhds 0) := by
  obtain ⟨h1, -, -, -, h5, -⟩ := damped_homogeneous_norms_wave h
  refine ⟨?_, (h1 2 two_pos).2.2.2.2.2, h5⟩
  rw [(h1 1 one_pos).2.2.2.1, Real.one_rpow]

#check @audit_consumer
#print axioms audit_consumer

end StratonovichHAMSecondMoment.Audit.WaveGreen
