module
import StratonovichHAMSecondMoment.MaskedContinuousWaveCompleted
set_option autoImplicit false
set_option pp.all true
#check @StratonovichHAMSecondMoment.MaskedContinuousWaveCompleted.masked_continuous_wave_completed_paper
#print axioms StratonovichHAMSecondMoment.MaskedContinuousWaveCompleted.masked_continuous_wave_completed_paper
#check @StratonovichHAMSecondMoment.MaskedContinuousWaveCompleted.norm_sq_waveFn_cc_zero
#print axioms StratonovichHAMSecondMoment.MaskedContinuousWaveCompleted.norm_sq_waveFn_cc_zero

open MeasureTheory Set StratonovichHAMSecondMoment

namespace StratonovichHAMSecondMoment.Audit.MaskedContinuousWaveCompleted

open StratonovichHAMSecondMoment.MaskedTrigProducts StratonovichHAMSecondMoment.MaskedContinuousWave
  StratonovichHAMSecondMoment.TimeCompletion StratonovichHAMSecondMoment.MaskedContinuousWaveCompleted

/-- Consumer of the wrapper: with no supplied input, the product `1_I c_r b_ρ` has
`H_a`-norm squared at most `C₁(a)(1+T)⁴ h^{2-a} 𝒬_h(r,ρ)`. -/
private theorem audit_consumer (a T s h r ρ : ℝ) (ha0 : 0 < a) (ha1 : a < 1) (hT : 0 < T)
    (hh0 : 0 < h) (hh1 : h ≤ 1) (hs : 0 ≤ s) (hsT : s + h ≤ T) (hr : 0 ≤ r) (hρ : 0 ≤ ρ) :
    ∃ hp : waveFn (Icc s (s + h)) .c .b r ρ ∈ L2fun T,
      ‖emb ⟨a, T, ha0, ha1, hT⟩ ⟨waveFn (Icc s (s + h)) .c .b r ρ, hp⟩‖ ^ 2 ≤
        C₁ a * (1 + T) ^ 4 * h ^ (2 - a) * frequencyPair a h r ρ :=
  let H := masked_continuous_wave_completed_paper a T s h ha0 ha1 hT hh0 hh1 hs hsT r ρ hr hρ
    .c .b
  ⟨H.1, H.2 H.1⟩

#check @audit_consumer
#print axioms audit_consumer

end StratonovichHAMSecondMoment.Audit.MaskedContinuousWaveCompleted
