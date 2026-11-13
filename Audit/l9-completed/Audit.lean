module
import StratonovichHAMSecondMoment.L9Completed
set_option autoImplicit false
set_option pp.all true
#check @StratonovichHAMSecondMoment.L9Completed.waveFourierThree_holds
#print axioms StratonovichHAMSecondMoment.L9Completed.waveFourierThree_holds
#check @StratonovichHAMSecondMoment.L9Completed.archimedesLaw_holds
#print axioms StratonovichHAMSecondMoment.L9Completed.archimedesLaw_holds
#check @StratonovichHAMSecondMoment.L9Completed.low_alpha_convolution_paper_completed
#print axioms StratonovichHAMSecondMoment.L9Completed.low_alpha_convolution_paper_completed
#check @StratonovichHAMSecondMoment.L9Completed.phase_trace_completed
#print axioms StratonovichHAMSecondMoment.L9Completed.phase_trace_completed
#check @StratonovichHAMSecondMoment.L9Completed.traceT_fourier_completed
#print axioms StratonovichHAMSecondMoment.L9Completed.traceT_fourier_completed
#check @StratonovichHAMSecondMoment.L9Completed.phase_contractions_paper_completed
#print axioms StratonovichHAMSecondMoment.L9Completed.phase_contractions_paper_completed
#check @StratonovichHAMSecondMoment.L9Completed.phase_contractions_homog_completed
#print axioms StratonovichHAMSecondMoment.L9Completed.phase_contractions_homog_completed

namespace StratonovichHAMSecondMoment.Audit.L9Completed

open StratonovichHAMSecondMoment

/-- Consumer: under `H:homog` in `d = 3` with `α < 1` alone, the low-`α` convolution bound
holds for `G_{h,η}` and `|T_ε(a,q)| ≤ D_Γ a^{1-α}`, with no supplied input. -/
private theorem audit_consumer {alpha alpha0 : ℝ}
    {Γ μ : MeasureTheory.Measure (HomogHypothesis.Rd 3)}
    (hH : HomogHypothesis.HomogCovariance 3 alpha alpha0 Γ μ) (ha1 : alpha < 1) (h ε a : ℝ)
    (hh : 0 < h) (hε : 0 < ε) (ha : 0 < a) (z q : HomogHypothesis.Rd 3) :
    ∫ y, LowAlphaConvolution.gammaEps Γ ε (y + z)
        ∂(LowAlphaConvolution.smoothedGreen (WaveGreen.waveGreen 3) h 0) ≤
      (LowAlphaConvolution.specV μ).toReal / (1 - alpha) * h ^ (1 - alpha) ∧
      ‖PhaseContractions.traceT Γ ε a q‖ ≤ PhaseContractions.dGam Γ alpha * a ^ (1 - alpha) :=
  ⟨((L9Completed.low_alpha_convolution_paper_completed hH ha1).2.2.2.2.2 h hh ε hε 0 le_rfl
      z).2.2,
    ((L9Completed.phase_contractions_homog_completed hH).2 a ha ε hε q).2.2.2.2⟩

#check @audit_consumer
#print axioms audit_consumer

end StratonovichHAMSecondMoment.Audit.L9Completed
