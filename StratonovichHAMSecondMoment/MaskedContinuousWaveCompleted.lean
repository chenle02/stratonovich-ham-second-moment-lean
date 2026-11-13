module

/-
Copyright 2026 Le Chen. SPDX-License-Identifier: Apache-2.0

Lemma `L:masked-continuous-wave` (Continuous sine factors) of
`notes/integrated_covariance_foundation.tex` at revision a284420 (statement TeX
lines 378-390, display `E:masked-continuous-wave` 385-389, proof 392-423), re-issued
with NOTHING supplied, in the concrete temporal completion `H_a` of
`L:masked-time-completion` (`TimeCompletion`).

Statement formalized (`masked_continuous_wave_completed_paper`).  The hypotheses are
exactly those of `MaskedContinuousWave.masked_continuous_wave_paper` without its
abstract data `E`, `V`, `emb` and its two supplied inputs `hmem`, `hnorm`:
`0 < a < 1`, `T > 0`, `I = [s, s+h] ⊆ [0, T]` (`0 ≤ s`, `s + h ≤ T`), `0 < h ≤ 1`,
`r, ρ ≥ 0`, `F, G ∈ {c, b}`.  No `Γ ≠ 0` (the TeX states none; the section's purely
temporal estimates hold for any `Γ`, TeX lines 5-7).  Conclusion: `1_I F_r G_ρ`
(`MaskedContinuousWave.waveFn`) lies in `L²(0,T)` and its norm in `H_a` satisfies
`‖1_I F_r G_ρ‖_a² ≤ C₁(a) (1+T)⁴ h^{2-a} 𝒬_h(r,ρ)`, `C₁(a) = 4·3^{1-a}·C₀(a)`.

How the inputs are discharged.  `masked_continuous_wave_paper` is applied with
`E = Ha p`, `V = TimeCompletion.L2fun T` and `emb = TimeCompletion.emb p`
(`p = ⟨a, T, ha0, ha1, hT⟩`):
* `hmem` quantifies over EVERY `A ∈ C¹(I; ℂ)` and every real `ω`; for each such `A`,
  `MaskedModulation.envelope_of_contDiffOn` (using `h > 0`) gives continuity and the
  bound `‖A‖ ≤ sup_I ‖A‖` on `I`, and `MaskedModulation.memLp_modeFn` then gives
  `1_I A e^{iω·} ∈ L²(0,T)`;
* `hnorm` is `TimeCompletion.emb_norm_sq` (`‖emb f‖² = Re⟨f,f⟩_a` for every
  `f ∈ L²(0,T)`).
Neither input remains as a hypothesis.  The existing modules are not modified.

Auxiliary (calibration, used by the refutations): `norm_sq_waveFn_cc_zero`, the exact
value `‖1_{[0,h]} c_0 c_0‖_a² = 2h^{2-a}/((1-a)(2-a))` for `0 ≤ h ≤ T`, `a < 1`.
-/
public import Mathlib
public import StratonovichHAMSecondMoment.TimeCompletion
public import StratonovichHAMSecondMoment.MaskedContinuousWave

@[expose] public section

noncomputable section

set_option autoImplicit false

open MeasureTheory Set

namespace StratonovichHAMSecondMoment.MaskedContinuousWaveCompleted

open StratonovichHAMSecondMoment.TimeSchur StratonovichHAMSecondMoment.MaskedTrigProducts
  StratonovichHAMSecondMoment.MaskedContinuousWave StratonovichHAMSecondMoment.TimeCompletion

/-- `L:masked-continuous-wave` (TeX lines 378-423, display `E:masked-continuous-wave`
385-389) with NO supplied input, in the concrete `H_a` of `L:masked-time-completion`.
Hypotheses: exactly the manuscript's (TeX lines 296-298, 378-384, with `T > 0`,
`0 < a < 1` from `L:masked-time-completion`), i.e. those of
`MaskedContinuousWave.masked_continuous_wave_paper` minus `E`, `V`, `emb`, `hmem`,
`hnorm`.  Conclusion: `1_I F_r G_ρ ∈ L²(0,T)` and, in `H_a`,
`‖1_I F_r G_ρ‖_a² ≤ C₁(a) (1+T)⁴ h^{2-a} 𝒬_h(r,ρ)`.  The inputs `hmem` (for every
`C¹` amplitude) and `hnorm` hold by construction (`MaskedModulation.memLp_modeFn`,
`TimeCompletion.emb_norm_sq`).  `T > 0` is needed to build `H_a`; the bound itself
does not use it. -/
theorem masked_continuous_wave_completed_paper
    (a T s h : ℝ) (ha0 : 0 < a) (ha1 : a < 1) (hT : 0 < T)
    (hh0 : 0 < h) (hh1 : h ≤ 1) (hs : 0 ≤ s) (hsT : s + h ≤ T)
    (r ρ : ℝ) (hr : 0 ≤ r) (hρ : 0 ≤ ρ) (F G : Wave) :
    waveFn (Icc s (s + h)) F G r ρ ∈ L2fun T ∧
      ∀ hp : waveFn (Icc s (s + h)) F G r ρ ∈ L2fun T,
        ‖emb ⟨a, T, ha0, ha1, hT⟩ ⟨waveFn (Icc s (s + h)) F G r ρ, hp⟩‖ ^ 2 ≤
          C₁ a * (1 + T) ^ 4 * h ^ (2 - a) * frequencyPair a h r ρ :=
  masked_continuous_wave_paper a T s h ha0 ha1 hT hh0 hh1 hs hsT r ρ hr hρ F G
    (L2fun T) (emb ⟨a, T, ha0, ha1, hT⟩)
    (fun A hA ω => by
      obtain ⟨hc, hMb, -⟩ := MaskedModulation.envelope_of_contDiffOn hh0 A hA _ _ rfl rfl
      exact MaskedModulation.memLp_modeFn (T := T) A hc _ hMb ω)
    (fun f _ => emb_norm_sq (p := ⟨a, T, ha0, ha1, hT⟩) f)

/-- Auxiliary (calibration, used by the refutations): for `0 ≤ h ≤ T` and `a < 1`,
`‖1_{[0,h]} c_0 c_0‖_a² = 2h^{2-a}/((1-a)(2-a))` in `H_a` (here `c_0 ≡ 1`). -/
theorem norm_sq_waveFn_cc_zero (p : TimeParams) {h : ℝ} (hh0 : 0 ≤ h) (hhT : h ≤ p.T)
    (hp : waveFn (Icc 0 h) .c .c 0 0 ∈ L2fun p.T) :
    ‖emb p ⟨waveFn (Icc 0 h) .c .c 0 0, hp⟩‖ ^ 2 =
      2 * h ^ (2 - p.a) / ((1 - p.a) * (2 - p.a)) := by
  rw [emb_norm_sq]
  have hw : waveFn (Icc 0 h) .c .c 0 0 = (Icc 0 h).indicator (fun _ => (1 : ℂ)) := by
    funext t
    simp [waveFn, Wave.eval, cFn]
  have hsub : Icc (0 : ℝ) p.T ∩ Icc 0 h = Icc 0 h :=
    inter_eq_right.2 (Icc_subset_Icc le_rfl hhT)
  have hform : timeForm p.a p.T (waveFn (Icc 0 h) .c .c 0 0) (waveFn (Icc 0 h) .c .c 0 0) =
      timeForm p.a h (fun _ => (1 : ℂ)) (fun _ => (1 : ℂ)) := by
    rw [hw]
    unfold timeForm
    have hin : ∀ t, ∫ s in Icc 0 p.T, (Icc 0 h).indicator (fun _ => (1 : ℂ)) t *
        (starRingEnd ℂ) ((Icc 0 h).indicator (fun _ => (1 : ℂ)) s) *
          ((kern p.a (t - s) : ℝ) : ℂ) =
        (Icc 0 h).indicator (fun t => ∫ s in Icc 0 h, (1 : ℂ) * (starRingEnd ℂ) 1 *
          ((kern p.a (t - s) : ℝ) : ℂ)) t := by
      intro t
      by_cases ht : t ∈ Icc 0 h
      · rw [indicator_of_mem ht, indicator_of_mem ht]
        conv_rhs => rw [← hsub]
        rw [← setIntegral_indicator measurableSet_Icc]
        congr 1
        funext s
        by_cases hs : s ∈ Icc 0 h
        · rw [indicator_of_mem hs, indicator_of_mem hs]
        · rw [indicator_of_notMem hs, indicator_of_notMem hs]; simp
      · rw [indicator_of_notMem ht, indicator_of_notMem ht]; simp
    simp_rw [hin]
    rw [setIntegral_indicator measurableSet_Icc, hsub]
  rw [hform, timeForm_one p.ha1 hh0, Complex.ofReal_re]

end StratonovichHAMSecondMoment.MaskedContinuousWaveCompleted
