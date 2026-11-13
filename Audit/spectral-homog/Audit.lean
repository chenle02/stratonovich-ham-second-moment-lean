module
import StratonovichHAMSecondMoment.SpectralHomog
set_option autoImplicit false
set_option pp.all true
#check @StratonovichHAMSecondMoment.SpectralHomog.SpectralHomogeneous
#print axioms StratonovichHAMSecondMoment.SpectralHomog.SpectralHomogeneous
#check @StratonovichHAMSecondMoment.SpectralHomog.map_smul_eq
#print axioms StratonovichHAMSecondMoment.SpectralHomog.map_smul_eq
#check @StratonovichHAMSecondMoment.SpectralHomog.integral_comp_smul
#print axioms StratonovichHAMSecondMoment.SpectralHomog.integral_comp_smul
#check @StratonovichHAMSecondMoment.SpectralHomog.measure_ball
#print axioms StratonovichHAMSecondMoment.SpectralHomog.measure_ball
#check @StratonovichHAMSecondMoment.SpectralHomog.measure_zero
#print axioms StratonovichHAMSecondMoment.SpectralHomog.measure_zero
#check @StratonovichHAMSecondMoment.SpectralHomog.integrable_of_le_inv
#print axioms StratonovichHAMSecondMoment.SpectralHomog.integrable_of_le_inv
#check @StratonovichHAMSecondMoment.SpectralHomog.integrable_inv_one_add_sq
#print axioms StratonovichHAMSecondMoment.SpectralHomog.integrable_inv_one_add_sq
#check @StratonovichHAMSecondMoment.SpectralHomog.resolvent
#print axioms StratonovichHAMSecondMoment.SpectralHomog.resolvent
#check @StratonovichHAMSecondMoment.SpectralHomog.heat
#print axioms StratonovichHAMSecondMoment.SpectralHomog.heat
#check @StratonovichHAMSecondMoment.SpectralHomog.resolvent_integrable
#print axioms StratonovichHAMSecondMoment.SpectralHomog.resolvent_integrable
#check @StratonovichHAMSecondMoment.SpectralHomog.heat_integrable
#print axioms StratonovichHAMSecondMoment.SpectralHomog.heat_integrable
#check @StratonovichHAMSecondMoment.SpectralHomog.resolvent_homog
#print axioms StratonovichHAMSecondMoment.SpectralHomog.resolvent_homog
#check @StratonovichHAMSecondMoment.SpectralHomog.heat_homog
#print axioms StratonovichHAMSecondMoment.SpectralHomog.heat_homog
#check @StratonovichHAMSecondMoment.SpectralHomog.resolvent_sub_pos
#print axioms StratonovichHAMSecondMoment.SpectralHomog.resolvent_sub_pos
#check @StratonovichHAMSecondMoment.SpectralHomog.resolvent_pos
#print axioms StratonovichHAMSecondMoment.SpectralHomog.resolvent_pos
#check @StratonovichHAMSecondMoment.SpectralHomog.heat_pos
#print axioms StratonovichHAMSecondMoment.SpectralHomog.heat_pos
#check @StratonovichHAMSecondMoment.SpectralHomog.spectral_ne_zero
#print axioms StratonovichHAMSecondMoment.SpectralHomog.spectral_ne_zero
open MeasureTheory in
/-- Consumer: under the supplied homogeneity, `R_Γ(2) = 2^{α-2} R_Γ(1)` and the
resolvent integrand at `q = 2` is integrable. -/
private theorem resolvent_consumer {d : ℕ} {alpha : ℝ}
    (μ : Measure (StratonovichHAMSecondMoment.HomogHypothesis.Rd d)) [IsLocallyFiniteMeasure μ]
    (hI : StratonovichHAMSecondMoment.SpectralHomog.SpectralHomogeneous μ alpha)
    (ha : alpha < 2) :
    Integrable (fun ξ : StratonovichHAMSecondMoment.HomogHypothesis.Rd d =>
        1 / ((2 : ℝ) ^ 2 + ‖ξ‖ ^ 2)) μ ∧
      StratonovichHAMSecondMoment.SpectralHomog.resolvent μ 2 =
        2 ^ (alpha - 2) * StratonovichHAMSecondMoment.SpectralHomog.resolvent μ 1 :=
  ⟨StratonovichHAMSecondMoment.SpectralHomog.resolvent_integrable
      (StratonovichHAMSecondMoment.SpectralHomog.integrable_inv_one_add_sq hI ha) 2 two_ne_zero,
    StratonovichHAMSecondMoment.SpectralHomog.resolvent_homog hI 2 two_pos⟩
#check @resolvent_consumer
#print axioms resolvent_consumer
open MeasureTheory in
example : StratonovichHAMSecondMoment.SpectralHomog.SpectralHomogeneous
    (0 : Measure (StratonovichHAMSecondMoment.HomogHypothesis.Rd 1)) 1 := by
  intro _ _ _ _; simp
