module
import StratonovichHAMSecondMoment.KappaRange
set_option autoImplicit false
set_option pp.all true
#check @StratonovichHAMSecondMoment.KappaRange.kappa
#print axioms StratonovichHAMSecondMoment.KappaRange.kappa
#check @StratonovichHAMSecondMoment.KappaRange.kappa_mem_Ioo
#print axioms StratonovichHAMSecondMoment.KappaRange.kappa_mem_Ioo
/-- Consumer: `κ ∈ (1,2)` places the growth scale `t^κ` between `t` and `t²`
for `t ≥ 1` (the comparison with the linear and the crude `t²` scales). -/
private theorem kappa_consumer (d : ℕ) (alpha alpha0 : ℝ) (hd : d = 1 ∨ d = 2 ∨ d = 3)
    (h0 : 0 < alpha0) (h1 : alpha0 < 1) (hthr : alpha0 + alpha < 2)
    (halpha : (0 < alpha ∧ alpha < d) ∨ (alpha = d ∧ d = 1)) (t : ℝ) (ht : 1 ≤ t) :
    t ≤ t ^ StratonovichHAMSecondMoment.KappaRange.kappa alpha alpha0 ∧
      t ^ StratonovichHAMSecondMoment.KappaRange.kappa alpha alpha0 ≤ t ^ (2 : ℝ) := by
  obtain ⟨hk1, hk2⟩ :=
    StratonovichHAMSecondMoment.KappaRange.kappa_mem_Ioo d alpha alpha0 hd h0 h1 hthr halpha
  refine ⟨?_, Real.rpow_le_rpow_of_exponent_le ht hk2.le⟩
  calc t = t ^ (1 : ℝ) := (Real.rpow_one t).symm
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le ht hk1.le
#check @kappa_consumer
#print axioms kappa_consumer
example : (2 : ℝ) ≤ 2 ^ StratonovichHAMSecondMoment.KappaRange.kappa (1 / 2) (1 / 2) ∧
    (2 : ℝ) ^ StratonovichHAMSecondMoment.KappaRange.kappa (1 / 2) (1 / 2) ≤ 2 ^ (2 : ℝ) :=
  kappa_consumer 1 (1 / 2) (1 / 2) (Or.inl rfl) (by norm_num) (by norm_num) (by norm_num)
    (Or.inl ⟨by norm_num, by norm_num⟩) 2 (by norm_num)
