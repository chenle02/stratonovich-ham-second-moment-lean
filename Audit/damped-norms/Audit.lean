module
import StratonovichHAMSecondMoment.DampedNorms
set_option autoImplicit false
set_option pp.all true
#check @StratonovichHAMSecondMoment.DampedNorms.N2integrand
#print axioms StratonovichHAMSecondMoment.DampedNorms.N2integrand
#check @StratonovichHAMSecondMoment.DampedNorms.N2sq
#print axioms StratonovichHAMSecondMoment.DampedNorms.N2sq
#check @StratonovichHAMSecondMoment.DampedNorms.N1
#print axioms StratonovichHAMSecondMoment.DampedNorms.N1
#check @StratonovichHAMSecondMoment.DampedNorms.FK
#print axioms StratonovichHAMSecondMoment.DampedNorms.FK
#check @StratonovichHAMSecondMoment.DampedNorms.ae_L0_pos
#print axioms StratonovichHAMSecondMoment.DampedNorms.ae_L0_pos
#check @StratonovichHAMSecondMoment.DampedNorms.ae_P2
#print axioms StratonovichHAMSecondMoment.DampedNorms.ae_P2
#check @StratonovichHAMSecondMoment.DampedNorms.ae_triple
#print axioms StratonovichHAMSecondMoment.DampedNorms.ae_triple
#check @StratonovichHAMSecondMoment.DampedNorms.one_add_le_exp
#print axioms StratonovichHAMSecondMoment.DampedNorms.one_add_le_exp
#check @StratonovichHAMSecondMoment.DampedNorms.integrable_rpow_div
#print axioms StratonovichHAMSecondMoment.DampedNorms.integrable_rpow_div
#check @StratonovichHAMSecondMoment.DampedNorms.waveHat_measurable
#print axioms StratonovichHAMSecondMoment.DampedNorms.waveHat_measurable
#check @StratonovichHAMSecondMoment.DampedNorms.FK_measurable
#print axioms StratonovichHAMSecondMoment.DampedNorms.FK_measurable
#check @StratonovichHAMSecondMoment.DampedNorms.MK
#print axioms StratonovichHAMSecondMoment.DampedNorms.MK
#check @StratonovichHAMSecondMoment.DampedNorms.FK_le_MK
#print axioms StratonovichHAMSecondMoment.DampedNorms.FK_le_MK
#check @StratonovichHAMSecondMoment.DampedNorms.MK_integrable
#print axioms StratonovichHAMSecondMoment.DampedNorms.MK_integrable
#check @StratonovichHAMSecondMoment.DampedNorms.FK_integrable
#print axioms StratonovichHAMSecondMoment.DampedNorms.FK_integrable
#check @StratonovichHAMSecondMoment.DampedNorms.integral_FK_eq
#print axioms StratonovichHAMSecondMoment.DampedNorms.integral_FK_eq
#check @StratonovichHAMSecondMoment.DampedNorms.N2integrand_integrable
#print axioms StratonovichHAMSecondMoment.DampedNorms.N2integrand_integrable
#check @StratonovichHAMSecondMoment.DampedNorms.N2_outer_integrable
#print axioms StratonovichHAMSecondMoment.DampedNorms.N2_outer_integrable
#check @StratonovichHAMSecondMoment.DampedNorms.N1_integrable
#print axioms StratonovichHAMSecondMoment.DampedNorms.N1_integrable
#check @StratonovichHAMSecondMoment.DampedNorms.damped_norms_finite_paper
#print axioms StratonovichHAMSecondMoment.DampedNorms.damped_norms_finite_paper
open MeasureTheory in
/-- Consumer: the absolute value of the spectral formula for `N₂(θ)²` is
integrable (the manuscript's "absolute integrability"). -/
private theorem damped_consumer {d : ℕ} {alpha alpha0 : ℝ}
    {Γ μ : Measure (StratonovichHAMSecondMoment.HomogHypothesis.Rd d)}
    (h : StratonovichHAMSecondMoment.HomogHypothesis.HomogCovariance d alpha alpha0 Γ μ)
    (hI : StratonovichHAMSecondMoment.SpectralHomog.SpectralHomogeneous μ alpha)
    (θ : ℝ) (hθ : 0 < θ) :
    Integrable (fun z => |StratonovichHAMSecondMoment.DampedNorms.N2integrand alpha0 θ z|)
      (StratonovichHAMSecondMoment.TimeFractional.P2.prod μ) :=
  (StratonovichHAMSecondMoment.DampedNorms.damped_norms_finite_paper h hI θ hθ).1.abs
#check @damped_consumer
#print axioms damped_consumer
/- Example: the degenerate zero witness of `HomogCovariance` (see
`Audit/homog-hypothesis`); it only shows the wrapper's hypotheses are
jointly satisfiable. -/
open MeasureTheory in
example : Integrable (fun z => |StratonovichHAMSecondMoment.DampedNorms.N2integrand
      (d := 1) (1 / 2) 1 z|)
    (StratonovichHAMSecondMoment.TimeFractional.P2.prod 0) :=
  damped_consumer (alpha := 1 / 2) (Γ := 0)
    { dim := Or.inl rfl
      alpha0_pos := by norm_num
      alpha0_lt_one := by norm_num
      Γ_radon := inferInstance
      Γ_even := by simp [StratonovichHAMSecondMoment.HomogHypothesis.IsEven]
      Γ_tempered := ⟨0, by simp⟩
      Γ_posdef := fun _ => by simp
      μ_radon := inferInstance
      μ_even := by simp [StratonovichHAMSecondMoment.HomogHypothesis.IsEven]
      μ_tempered := ⟨0, by simp⟩
      spectral := fun _ => by simp
      scaling := fun _ _ _ _ => by simp
      threshold := by norm_num
      alpha_range := Or.inl ⟨by norm_num, by norm_num⟩ }
    (fun _ _ _ _ => by simp) 1 one_pos
