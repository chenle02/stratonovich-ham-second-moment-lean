module
import StratonovichHAMSecondMoment.DriverParameters
set_option autoImplicit false
set_option pp.all true
#check @StratonovichHAMSecondMoment.DriverParameters.Homog
#print axioms StratonovichHAMSecondMoment.DriverParameters.Homog
#check @StratonovichHAMSecondMoment.DriverParameters.gamma_interval_nonempty
#print axioms StratonovichHAMSecondMoment.DriverParameters.gamma_interval_nonempty
#check @StratonovichHAMSecondMoment.DriverParameters.theta_beta_interval_nonempty
#print axioms StratonovichHAMSecondMoment.DriverParameters.theta_beta_interval_nonempty
#check @StratonovichHAMSecondMoment.DriverParameters.parameters_nonempty
#print axioms StratonovichHAMSecondMoment.DriverParameters.parameters_nonempty
/-- Consumer: the driver section's choice of `γ, θ, β`, used downstream only
through the cruder ranges `0 < γ < 1/2` and `1/2 < θ < β < 1`. -/
private theorem driver_consumer (d : ℕ) (alpha a : ℝ)
    (h : StratonovichHAMSecondMoment.DriverParameters.Homog d alpha a) :
    ∃ γ θ β : ℝ, 0 < γ ∧ γ < 1 / 2 ∧ 1 / 2 < θ ∧ θ < β ∧ β < 1 := by
  obtain ⟨γ, θ, β, ⟨hγ0, hγ⟩, hθ, hθβ, hβ⟩ :=
    StratonovichHAMSecondMoment.DriverParameters.parameters_nonempty d alpha a h
  have ha : 0 < a := h.2.1
  refine ⟨γ, θ, β, hγ0, lt_of_lt_of_le hγ (min_le_left _ _), hθ, hθβ, ?_⟩
  have := lt_of_lt_of_le hβ (min_le_left _ _)
  linarith
#check @driver_consumer
#print axioms driver_consumer
example : ∃ γ θ β : ℝ, 0 < γ ∧ γ < 1 / 2 ∧ 1 / 2 < θ ∧ θ < β ∧ β < 1 :=
  driver_consumer 1 (1 / 2) (1 / 2)
    ⟨Or.inl rfl, by norm_num, by norm_num, by norm_num, Or.inl ⟨by norm_num, by norm_num⟩⟩
