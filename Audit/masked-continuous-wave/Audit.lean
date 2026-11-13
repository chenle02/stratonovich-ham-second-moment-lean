module
import StratonovichHAMSecondMoment.MaskedContinuousWave
set_option autoImplicit false
set_option pp.all true
#check @StratonovichHAMSecondMoment.MaskedContinuousWave.cFn
#print axioms StratonovichHAMSecondMoment.MaskedContinuousWave.cFn
#check @StratonovichHAMSecondMoment.MaskedContinuousWave.bFn
#print axioms StratonovichHAMSecondMoment.MaskedContinuousWave.bFn
#check @StratonovichHAMSecondMoment.MaskedContinuousWave.Wave
#print axioms StratonovichHAMSecondMoment.MaskedContinuousWave.Wave
#check @StratonovichHAMSecondMoment.MaskedContinuousWave.Wave.eval
#print axioms StratonovichHAMSecondMoment.MaskedContinuousWave.Wave.eval
#check @StratonovichHAMSecondMoment.MaskedContinuousWave.waveFn
#print axioms StratonovichHAMSecondMoment.MaskedContinuousWave.waveFn
#check @StratonovichHAMSecondMoment.MaskedContinuousWave.C₁
#print axioms StratonovichHAMSecondMoment.MaskedContinuousWave.C₁
#check @StratonovichHAMSecondMoment.MaskedContinuousWave.bracket_add_le
#print axioms StratonovichHAMSecondMoment.MaskedContinuousWave.bracket_add_le
#check @StratonovichHAMSecondMoment.MaskedContinuousWave.bracket_pos
#print axioms StratonovichHAMSecondMoment.MaskedContinuousWave.bracket_pos
#check @StratonovichHAMSecondMoment.MaskedContinuousWave.bracket_rpow_shift_le
#print axioms StratonovichHAMSecondMoment.MaskedContinuousWave.bracket_rpow_shift_le
#check @StratonovichHAMSecondMoment.MaskedContinuousWave.frequencyPair_shift_le
#print axioms StratonovichHAMSecondMoment.MaskedContinuousWave.frequencyPair_shift_le
#check @StratonovichHAMSecondMoment.MaskedContinuousWave.amp
#print axioms StratonovichHAMSecondMoment.MaskedContinuousWave.amp
#check @StratonovichHAMSecondMoment.MaskedContinuousWave.trig
#print axioms StratonovichHAMSecondMoment.MaskedContinuousWave.trig
#check @StratonovichHAMSecondMoment.MaskedContinuousWave.fr
#print axioms StratonovichHAMSecondMoment.MaskedContinuousWave.fr
#check @StratonovichHAMSecondMoment.MaskedContinuousWave.eval_eq
#print axioms StratonovichHAMSecondMoment.MaskedContinuousWave.eval_eq
#check @StratonovichHAMSecondMoment.MaskedContinuousWave.fr_spec
#print axioms StratonovichHAMSecondMoment.MaskedContinuousWave.fr_spec
#check @StratonovichHAMSecondMoment.MaskedContinuousWave.bFn_contDiff
#print axioms StratonovichHAMSecondMoment.MaskedContinuousWave.bFn_contDiff
#check @StratonovichHAMSecondMoment.MaskedContinuousWave.amp_contDiff
#print axioms StratonovichHAMSecondMoment.MaskedContinuousWave.amp_contDiff
#check @StratonovichHAMSecondMoment.MaskedContinuousWave.bFn_bounds
#print axioms StratonovichHAMSecondMoment.MaskedContinuousWave.bFn_bounds
#check @StratonovichHAMSecondMoment.MaskedContinuousWave.bracket_le_sqrt_two
#print axioms StratonovichHAMSecondMoment.MaskedContinuousWave.bracket_le_sqrt_two
#check @StratonovichHAMSecondMoment.MaskedContinuousWave.bracket_div_le_sqrt_two
#print axioms StratonovichHAMSecondMoment.MaskedContinuousWave.bracket_div_le_sqrt_two
#check @StratonovichHAMSecondMoment.MaskedContinuousWave.amp_bound
#print axioms StratonovichHAMSecondMoment.MaskedContinuousWave.amp_bound
#check @StratonovichHAMSecondMoment.MaskedContinuousWave.amp_prod_sup
#print axioms StratonovichHAMSecondMoment.MaskedContinuousWave.amp_prod_sup
#check @StratonovichHAMSecondMoment.MaskedContinuousWave.waveFn_eq_prodFn
#print axioms StratonovichHAMSecondMoment.MaskedContinuousWave.waveFn_eq_prodFn
#check @StratonovichHAMSecondMoment.MaskedContinuousWave.masked_continuous_wave_paper
#print axioms StratonovichHAMSecondMoment.MaskedContinuousWave.masked_continuous_wave_paper
#check @StratonovichHAMSecondMoment.MaskedContinuousWave.Wave.c
#print axioms StratonovichHAMSecondMoment.MaskedContinuousWave.Wave.c
#check @StratonovichHAMSecondMoment.MaskedContinuousWave.Wave.b
#print axioms StratonovichHAMSecondMoment.MaskedContinuousWave.Wave.b

open MeasureTheory Set StratonovichHAMSecondMoment

namespace StratonovichHAMSecondMoment.Audit.MaskedContinuousWave

open StratonovichHAMSecondMoment.TimeSchur StratonovichHAMSecondMoment.MaskedTrigProducts
  StratonovichHAMSecondMoment.MaskedModulation StratonovichHAMSecondMoment.MaskedContinuousWave

/-- Consumer of the wrapper: with B24's two inputs, the mixed factor
`1_I c_r b_0` (`b_0(t) = t`, the zero-frequency case of the manuscript) lies in
`V` and its squared norm obeys `E:masked-continuous-wave` with `ρ = 0`. -/
private theorem audit_consumer {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (a T s h r : ℝ) (ha0 : 0 < a) (ha1 : a < 1) (hT : 0 < T)
    (hh0 : 0 < h) (hh1 : h ≤ 1) (hs : 0 ≤ s) (hsT : s + h ≤ T) (hr : 0 ≤ r)
    (V : Submodule ℂ (ℝ → ℂ)) (emb : V →ₗ[ℂ] E)
    (hmem : ∀ A : ℝ → ℂ, ContDiffOn ℝ 1 A (Icc s (s + h)) →
      ∀ ω : ℝ, modeFn (Icc s (s + h)) A ω ∈ V)
    (hnorm : ∀ f : V, MemLp (f : ℝ → ℂ) 2 (volume.restrict (Icc 0 T)) →
      ‖emb f‖ ^ 2 = (timeForm a T f f).re) :
    ∃ hp : waveFn (Icc s (s + h)) .c .b r 0 ∈ V,
      ‖emb ⟨waveFn (Icc s (s + h)) .c .b r 0, hp⟩‖ ^ 2 ≤
        C₁ a * (1 + T) ^ 4 * h ^ (2 - a) * frequencyPair a h r 0 := by
  obtain ⟨hp, hb⟩ := masked_continuous_wave_paper a T s h ha0 ha1 hT hh0 hh1 hs hsT r 0 hr le_rfl
    .c .b V emb hmem hnorm
  exact ⟨hp, hb hp⟩

#check @audit_consumer
#print axioms audit_consumer

/-- The manuscript's `b_0(t) = t`. -/
example (t : ℝ) : bFn 0 t = t := by simp [bFn]

/-- `C₁(a) = 4·3^{1-a}·16/(1-a)`. -/
example (a : ℝ) : C₁ a = 4 * 3 ^ (1 - a) * (16 / (1 - a)) := rfl

end StratonovichHAMSecondMoment.Audit.MaskedContinuousWave
