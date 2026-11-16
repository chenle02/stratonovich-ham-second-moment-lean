module
import StratonovichHAMSecondMoment.HigherRieszThree
set_option autoImplicit false
set_option pp.all true
#check @StratonovichHAMSecondMoment.HigherRieszThree.F3w
#print axioms StratonovichHAMSecondMoment.HigherRieszThree.F3w
#check @StratonovichHAMSecondMoment.HigherRieszThree.M3
#print axioms StratonovichHAMSecondMoment.HigherRieszThree.M3
#check @StratonovichHAMSecondMoment.HigherRieszThree.Md
#print axioms StratonovichHAMSecondMoment.HigherRieszThree.Md
#check @StratonovichHAMSecondMoment.HigherRieszThree.F3w_eq
#print axioms StratonovichHAMSecondMoment.HigherRieszThree.F3w_eq
#check @StratonovichHAMSecondMoment.HigherRieszThree.F3w_zero
#print axioms StratonovichHAMSecondMoment.HigherRieszThree.F3w_zero
#check @StratonovichHAMSecondMoment.HigherRieszThree.two_sub_le_rpow
#print axioms StratonovichHAMSecondMoment.HigherRieszThree.two_sub_le_rpow
#check @StratonovichHAMSecondMoment.HigherRieszThree.F3w_le
#print axioms StratonovichHAMSecondMoment.HigherRieszThree.F3w_le
#check @StratonovichHAMSecondMoment.HigherRieszThree.F3w_unit
#print axioms StratonovichHAMSecondMoment.HigherRieszThree.F3w_unit
#check @StratonovichHAMSecondMoment.HigherRieszThree.riesz_three_unsmoothed
#print axioms StratonovichHAMSecondMoment.HigherRieszThree.riesz_three_unsmoothed
#check @StratonovichHAMSecondMoment.HigherRieszThree.M3_pos
#print axioms StratonovichHAMSecondMoment.HigherRieszThree.M3_pos
#check @StratonovichHAMSecondMoment.HigherRieszThree.higher_riesz_three
#print axioms StratonovichHAMSecondMoment.HigherRieszThree.higher_riesz_three
#check @StratonovichHAMSecondMoment.HigherRieszThree.waveGreen_three_point
#print axioms StratonovichHAMSecondMoment.HigherRieszThree.waveGreen_three_point
#check @StratonovichHAMSecondMoment.HigherRieszThree.smoothCov_riesz_tendsto
#print axioms StratonovichHAMSecondMoment.HigherRieszThree.smoothCov_riesz_tendsto
#check @StratonovichHAMSecondMoment.HigherRieszThree.higher_riesz_three_optimal
#print axioms StratonovichHAMSecondMoment.HigherRieszThree.higher_riesz_three_optimal
#check @StratonovichHAMSecondMoment.HigherRieszThree.higher_riesz_three_full
#print axioms StratonovichHAMSecondMoment.HigherRieszThree.higher_riesz_three_full
#check @StratonovichHAMSecondMoment.HigherRieszThree.alpha_lt_two
#print axioms StratonovichHAMSecondMoment.HigherRieszThree.alpha_lt_two
#check @StratonovichHAMSecondMoment.HigherRieszThree.higher_riesz_three_paper
#print axioms StratonovichHAMSecondMoment.HigherRieszThree.higher_riesz_three_paper
#check @StratonovichHAMSecondMoment.HigherRieszThree.higher_riesz_paper
#print axioms StratonovichHAMSecondMoment.HigherRieszThree.higher_riesz_paper

open MeasureTheory StratonovichHAMSecondMoment

namespace StratonovichHAMSecondMoment.Audit.HigherRieszThree

open StratonovichHAMSecondMoment.HigherRieszTwo StratonovichHAMSecondMoment.HigherRieszThree

/-- Consumer of the combined wrapper: under the manuscript's hypotheses of
`L:higher-riesz` in `d = 3`, the real-valued pairing of `E:higher-convolution`
is integrable and bounded by `M_3 h^{-(α-1)}`, and `M_3` is optimal. -/
private theorem audit_consumer {c α α₀ : ℝ} {μ : Measure (HomogHypothesis.Rd 3)}
    (hH : HomogHypothesis.HomogCovariance 3 α α₀ (volume.withDensity (riesz c α)) μ)
    (hc : 0 < c) (hα1 : 1 < α) {h ε η : ℝ} (hh : 0 < h) (hε : 0 < ε)
    (hη : 0 ≤ η) (z : HomogHypothesis.Rd 3) :
    ∫ y, (smoothCov (riesz c α) ε (y + z)).toReal ∂(smoothGreen (WaveGreen.waveGreen 3 h) η)
        ≤ M3 c α * h ^ (-(α - 1)) ∧
      ∀ M : ℝ, SpatialMaximum 3 (riesz c α) (α - 1) M → M3 c α ≤ M := by
  obtain ⟨hS, hopt⟩ := higher_riesz_paper hH (Or.inr rfl) hc hα1 (fun h => absurd h (by norm_num))
  have e : Md 3 c α = M3 c α := by simp [Md]
  rw [e] at hS hopt
  exact ⟨(hS.real_form (measurable_riesz c α) hh z hε hη).2.2, hopt rfl⟩

#check @audit_consumer
#print axioms audit_consumer

end StratonovichHAMSecondMoment.Audit.HigherRieszThree
