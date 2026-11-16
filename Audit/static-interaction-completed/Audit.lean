module
import StratonovichHAMSecondMoment.StaticInteractionCompleted
set_option autoImplicit false
set_option pp.all true
#check @StratonovichHAMSecondMoment.StaticInteractionCompleted.InDisc
#print axioms StratonovichHAMSecondMoment.StaticInteractionCompleted.InDisc
#check @StratonovichHAMSecondMoment.StaticInteractionCompleted.FockSandwich
#print axioms StratonovichHAMSecondMoment.StaticInteractionCompleted.FockSandwich
#check @StratonovichHAMSecondMoment.StaticInteractionCompleted.PropagatorBlock
#print axioms StratonovichHAMSecondMoment.StaticInteractionCompleted.PropagatorBlock
#check @StratonovichHAMSecondMoment.StaticInteractionCompleted.CPInputs
#print axioms StratonovichHAMSecondMoment.StaticInteractionCompleted.CPInputs
#check @StratonovichHAMSecondMoment.StaticInteractionCompleted.CPInputs.cpC
#print axioms StratonovichHAMSecondMoment.StaticInteractionCompleted.CPInputs.cpC
#check @StratonovichHAMSecondMoment.StaticInteractionCompleted.CPInputs.cpF
#print axioms StratonovichHAMSecondMoment.StaticInteractionCompleted.CPInputs.cpF
#check @StratonovichHAMSecondMoment.StaticInteractionCompleted.CPInputs.cpH
#print axioms StratonovichHAMSecondMoment.StaticInteractionCompleted.CPInputs.cpH
#check @StratonovichHAMSecondMoment.StaticInteractionCompleted.CPInputs.meas
#print axioms StratonovichHAMSecondMoment.StaticInteractionCompleted.CPInputs.meas
#check @StratonovichHAMSecondMoment.StaticInteractionCompleted.CPInputs.bound
#print axioms StratonovichHAMSecondMoment.StaticInteractionCompleted.CPInputs.bound
#check @StratonovichHAMSecondMoment.StaticInteractionCompleted.CPInputs.rep
#print axioms StratonovichHAMSecondMoment.StaticInteractionCompleted.CPInputs.rep
#check @StratonovichHAMSecondMoment.StaticInteractionCompleted.circle_of_complex_phase
#print axioms StratonovichHAMSecondMoment.StaticInteractionCompleted.circle_of_complex_phase
#check @StratonovichHAMSecondMoment.StaticInteractionCompleted.static_phase_all_orders_cp
#print axioms StratonovichHAMSecondMoment.StaticInteractionCompleted.static_phase_all_orders_cp
#check @StratonovichHAMSecondMoment.StaticInteractionCompleted.transported_le
#print axioms StratonovichHAMSecondMoment.StaticInteractionCompleted.transported_le
#check @StratonovichHAMSecondMoment.StaticInteractionCompleted.static_interaction_orders
#print axioms StratonovichHAMSecondMoment.StaticInteractionCompleted.static_interaction_orders
#check @StratonovichHAMSecondMoment.StaticInteractionCompleted.constants_nonneg
#print axioms StratonovichHAMSecondMoment.StaticInteractionCompleted.constants_nonneg
#check @StratonovichHAMSecondMoment.StaticInteractionCompleted.static_interaction_completed_paper
#print axioms StratonovichHAMSecondMoment.StaticInteractionCompleted.static_interaction_completed_paper
#check @StratonovichHAMSecondMoment.StaticInteractionCompleted.blockIter
#print axioms StratonovichHAMSecondMoment.StaticInteractionCompleted.blockIter
#check @StratonovichHAMSecondMoment.StaticInteractionCompleted.independent_static_blocks_operator
#print axioms StratonovichHAMSecondMoment.StaticInteractionCompleted.independent_static_blocks_operator
#check @StratonovichHAMSecondMoment.StaticInteractionCompleted.independent_static_blocks_operator_paper
#print axioms StratonovichHAMSecondMoment.StaticInteractionCompleted.independent_static_blocks_operator_paper

namespace StratonovichHAMSecondMoment.Audit.StaticInteractionCompleted

open StratonovichHAMSecondMoment

/-- Consumer: under `H:homog` in `d = 3`, two static blocks with the supplied per-block
interaction bound on adapted phases give the `E:independent-static-blocks` bound. -/
private theorem audit_consumer {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {alpha alpha0 lam : ℝ} {Γ μ : MeasureTheory.Measure (HomogHypothesis.Rd 3)}
    (hH : HomogHypothesis.HomogCovariance 3 alpha alpha0 Γ μ) (h σ : ℕ → ℝ) (hlam : 0 < lam)
    (hh : ∀ j, 0 < h j) (hlh : ∀ j, lam * h j ≤ 1) (S I : ℕ → E →L[ℝ] E) (x : E)
    (hS : ∀ j, j < 2 → ∀ y, ‖S j y‖ ^ 2 ≤ Real.exp (lam * h j) * ‖y‖ ^ 2)
    (hI : ∀ j, j < 2 → ∀ y, ‖I j y‖ ^ 2 ≤
      (1 + IntervalScalar.staticE alpha (StaticPhaseCauchy.allOrdersA alpha)
        (SpectralMassIdentity.ralpha μ alpha) (PhaseContractions.dGam Γ alpha) (h j) (σ j) lam) *
        ‖y‖ ^ 2) :
    ‖StaticInteractionCompleted.blockIter S I 2 x‖ ^ 2 ≤
      Real.exp (lam * ∑ j ∈ Finset.range 2, h j + ∑ j ∈ Finset.range 2,
        IntervalScalar.staticE alpha (StaticPhaseCauchy.allOrdersA alpha)
          (SpectralMassIdentity.ralpha μ alpha) (PhaseContractions.dGam Γ alpha) (h j) (σ j) lam) *
        ‖x‖ ^ 2 :=
  StaticInteractionCompleted.independent_static_blocks_operator_paper
    (PhaseContractions.PhaseCovariance.of_homog hH) 2 h σ hlam hh hlh S I (fun _ _ => True) x
    trivial (fun _ _ _ _ => trivial) hS (fun j hj y _ => hI j hj y)

#check @audit_consumer
#print axioms audit_consumer

end StratonovichHAMSecondMoment.Audit.StaticInteractionCompleted
