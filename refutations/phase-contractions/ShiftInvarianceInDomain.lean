/-
In-domain refutations for the Gaussian Fourier pairing step of
`L:phase-contractions` (main TeX lines 2534-2542 at 39f2597a; lemma statement
lines 2509-2523; standing assumptions of `S:static-phase` lines 2490-2493),
package theorem `StratonovichHAMSecondMoment.PhaseContractions.gauss_shift_le`:
`∫ e^{-s|q+ξ|²} μ(dξ) ≤ ∫ e^{-s|ξ|²} μ(dξ)` for `s > 0`, `q ∈ ℝ³`.

Class (a): manuscript-claim perturbation in the manuscript domain.  Each
refutation is stated for EVERY covariance of the class of `S:static-phase`
(`PhaseCovariance α Γ μ`: `d = 3`, `0 < α < 2`, `Γ(rA) = r^{3-α} Γ(A)`, `μ` the
tempered spectral measure) with `μ ≠ 0`, and every `s > 0`.  This upgrades
`ShiftInvariance.lean`, whose witness (`d = 1`, Lebesgue, `μ = δ_0`, `α = 0`)
lies outside the domain (class (c)).

Wrong variants refuted:
1. shift invariance `∀ q, F(q) = F(0)`, `F(q) = ∫ e^{-s|q+ξ|²} μ(dξ)`;
2. shift invariance at nonzero shifts `∀ q ≠ 0, F(q) = F(0)`;
3. the reversed comparison `∀ q, F(0) ≤ F(q)`.
Proof: `PhaseShiftControl.not_gauss_shift_invariant_phase` (Gaussian window
average: volume growth `t^{-3/2}` against `μ`-mass growth `t^{-α/2}`, `α < 3`).
The hypothesis `μ ≠ 0` is added and necessary: the zero pair is in the class
and satisfies all three variants (contrast 3).  The refutations quantify over
in-domain covariances; the existence of a nonzero member of the class (for
example a Riesz pair) is not formalized here.  No junk-value reliance: the
Gaussian integrals are integrable (`μ` tempered) and `F(0) > 0`.

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.PhaseShiftControl

set_option autoImplicit false

open MeasureTheory Real
open StratonovichHAMSecondMoment HomogHypothesis PhaseContractions PhaseShiftControl

namespace Refutations.PhaseContractions

/-- Variant 1 refuted in the domain: shift invariance fails for every
`PhaseCovariance` with `μ ≠ 0` and every `s > 0`. -/
theorem shift_invariance_in_domain_refuted {alpha : ℝ} {Γ μ : Measure (Rd 3)}
    (h : PhaseCovariance alpha Γ μ) (hμ : μ ≠ 0) {s : ℝ} (hs : 0 < s) :
    ¬ ∀ q : Rd 3, ∫ ξ, Real.exp (-(s * ‖q + ξ‖ ^ 2)) ∂μ =
      ∫ ξ, Real.exp (-(s * ‖ξ‖ ^ 2)) ∂μ :=
  not_gauss_shift_invariant_phase h hμ hs

/-- The package inequality for the same covariance and scale. -/
theorem shift_invariance_in_domain_contrast {alpha : ℝ} {Γ μ : Measure (Rd 3)}
    (h : PhaseCovariance alpha Γ μ) {s : ℝ} (hs : 0 < s) (q : Rd 3) :
    ∫ ξ, Real.exp (-(s * ‖q + ξ‖ ^ 2)) ∂μ ≤ ∫ ξ, Real.exp (-(s * ‖ξ‖ ^ 2)) ∂μ :=
  gauss_shift_le h.spectral s hs q

/-- Variant 2 refuted in the domain: equality at every nonzero shift fails. -/
theorem shift_invariance_nonzero_refuted {alpha : ℝ} {Γ μ : Measure (Rd 3)}
    (h : PhaseCovariance alpha Γ μ) (hμ : μ ≠ 0) {s : ℝ} (hs : 0 < s) :
    ¬ ∀ q : Rd 3, q ≠ 0 → ∫ ξ, Real.exp (-(s * ‖q + ξ‖ ^ 2)) ∂μ =
      ∫ ξ, Real.exp (-(s * ‖ξ‖ ^ 2)) ∂μ := by
  intro H
  refine not_gauss_shift_invariant_phase h hμ hs fun q => ?_
  by_cases hq : q = 0
  · subst hq
    simp only [zero_add]
  · exact H q hq

/-- The package inequality is strict at some nonzero shift. -/
theorem shift_invariance_nonzero_contrast {alpha : ℝ} {Γ μ : Measure (Rd 3)}
    (h : PhaseCovariance alpha Γ μ) (hμ : μ ≠ 0) {s : ℝ} (hs : 0 < s) :
    ∃ q : Rd 3, q ≠ 0 ∧ ∫ ξ, Real.exp (-(s * ‖q + ξ‖ ^ 2)) ∂μ <
      ∫ ξ, Real.exp (-(s * ‖ξ‖ ^ 2)) ∂μ :=
  exists_gauss_shift_lt_phase h hμ hs

/-- Variant 3 refuted in the domain: the reversed comparison fails. -/
theorem reverse_pairing_in_domain_refuted {alpha : ℝ} {Γ μ : Measure (Rd 3)}
    (h : PhaseCovariance alpha Γ μ) (hμ : μ ≠ 0) {s : ℝ} (hs : 0 < s) :
    ¬ ∀ q : Rd 3, ∫ ξ, Real.exp (-(s * ‖ξ‖ ^ 2)) ∂μ ≤
      ∫ ξ, Real.exp (-(s * ‖q + ξ‖ ^ 2)) ∂μ := by
  intro H
  exact not_gauss_shift_invariant_phase h hμ hs fun q =>
    le_antisymm (gauss_shift_le h.spectral s hs q) (H q)

/-- Without `μ ≠ 0` all three variants hold: the zero pair lies in the class
and its shifted Gaussian masses all vanish. -/
theorem reverse_pairing_in_domain_contrast {alpha : ℝ} (ha0 : 0 < alpha)
    (ha2 : alpha < 2) {s : ℝ} :
    PhaseCovariance alpha (0 : Measure (Rd 3)) 0 ∧
      ∀ q : Rd 3, ∫ ξ, Real.exp (-(s * ‖q + ξ‖ ^ 2)) ∂(0 : Measure (Rd 3)) =
        ∫ ξ, Real.exp (-(s * ‖ξ‖ ^ 2)) ∂(0 : Measure (Rd 3)) :=
  ⟨phaseCovariance_zero ha0 ha2, fun _ => by simp⟩

end Refutations.PhaseContractions
