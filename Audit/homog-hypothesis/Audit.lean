module
import StratonovichHAMSecondMoment.HomogHypothesis
set_option autoImplicit false
set_option pp.all true
#check @StratonovichHAMSecondMoment.HomogHypothesis.Rd
#print axioms StratonovichHAMSecondMoment.HomogHypothesis.Rd
#check @StratonovichHAMSecondMoment.HomogHypothesis.IsTempered
#print axioms StratonovichHAMSecondMoment.HomogHypothesis.IsTempered
#check @StratonovichHAMSecondMoment.HomogHypothesis.IsEven
#print axioms StratonovichHAMSecondMoment.HomogHypothesis.IsEven
#check @StratonovichHAMSecondMoment.HomogHypothesis.IsPosDefDistr
#print axioms StratonovichHAMSecondMoment.HomogHypothesis.IsPosDefDistr
#check @StratonovichHAMSecondMoment.HomogHypothesis.IsSpectralMeasure
#print axioms StratonovichHAMSecondMoment.HomogHypothesis.IsSpectralMeasure
#check @StratonovichHAMSecondMoment.HomogHypothesis.HomogCovariance
#print axioms StratonovichHAMSecondMoment.HomogHypothesis.HomogCovariance
#check @StratonovichHAMSecondMoment.HomogHypothesis.homog_params
#print axioms StratonovichHAMSecondMoment.HomogHypothesis.homog_params
#check @StratonovichHAMSecondMoment.HomogHypothesis.kappa_mem_Ioo_paper
#print axioms StratonovichHAMSecondMoment.HomogHypothesis.kappa_mem_Ioo_paper
#check @StratonovichHAMSecondMoment.HomogHypothesis.parameters_nonempty_paper
#print axioms StratonovichHAMSecondMoment.HomogHypothesis.parameters_nonempty_paper
open MeasureTheory in
/-- Consumer: the two paper wrappers used together, as a section opening with
"retain `H:homog`" does: `κ > 1` and an admissible `θ ∈ (1/2, 1 - α₀/2)`. -/
private theorem homog_consumer {d : ℕ} {alpha alpha0 : ℝ}
    {Γ μ : Measure (StratonovichHAMSecondMoment.HomogHypothesis.Rd d)}
    (h : StratonovichHAMSecondMoment.HomogHypothesis.HomogCovariance d alpha alpha0 Γ μ) :
    1 < StratonovichHAMSecondMoment.KappaRange.kappa alpha alpha0 ∧
      ∃ θ : ℝ, 1 / 2 < θ ∧ θ < 1 - alpha0 / 2 := by
  refine ⟨(StratonovichHAMSecondMoment.HomogHypothesis.kappa_mem_Ioo_paper h).1, ?_⟩
  obtain ⟨_, θ, β, _, hθ, hθβ, hβ⟩ :=
    StratonovichHAMSecondMoment.HomogHypothesis.parameters_nonempty_paper h
  exact ⟨θ, hθ, by linarith [lt_of_lt_of_le hβ (min_le_left _ _)]⟩
#check @homog_consumer
#print axioms homog_consumer
/- Example: the zero measure for both `Γ` and `μ` (d = 1, α = α₀ = 1/2).
This is a degenerate witness that the Lean predicate `HomogCovariance` is
inhabited at admissible parameters; it is not a physical covariance (the
manuscript's `Γ` is a nontrivial Riesz-type measure, which is not constructed
here). -/
open MeasureTheory in
example : 1 < StratonovichHAMSecondMoment.KappaRange.kappa (1 / 2) (1 / 2) ∧
    ∃ θ : ℝ, 1 / 2 < θ ∧ θ < 1 - (1 / 2 : ℝ) / 2 :=
  homog_consumer (d := 1) (Γ := 0) (μ := 0)
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
