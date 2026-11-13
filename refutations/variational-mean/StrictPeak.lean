/-
Refutation for the envelope bound of `L:variational-heat-envelope`
(`notes/integrated_unmasked_variational.tex` lines 31-32 at a284420), package
theorems `StratonovichHAMSecondMoment.VariationalMean.heat_identity` and
`heat_envelope`.

Wrong variant: a strict peak at the origin,
`(Γ * p_ε)(x) < (Γ * p_ε)(0)` for every `x ≠ 0`, for every `Γ`, `μ` with the
spectral convention.  Counterexample: `d = 1`, `Γ` = Lebesgue measure,
`μ = δ_0`, `ε = 1`: by the package identity `(Γ * p_1)(x) = 1` for every
`x`, so the bound `≤ (Γ * p_ε)(0)` of the manuscript holds with equality and
cannot be strict.  `strict_peak_contrast` is the package identity at `x` and
`0`.  Junk reliance: none.

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.VariationalMean

set_option autoImplicit false

open MeasureTheory
open StratonovichHAMSecondMoment HomogHypothesis VariationalDilation VariationalMean

namespace Refutations.VariationalMean.Peak

/-- Lebesgue measure on `ℝ¹` has spectral measure `δ_0`. -/
theorem leb_spectral : IsSpectralMeasure (volume : Measure (Rd 1)) (Measure.dirac 0) := by
  intro φ
  rw [integral_dirac]
  simp

/-- At `Γ` = Lebesgue, `μ = δ_0`, the convolution is `1` everywhere (package
identity). -/
theorem conv_eq_one (x : Rd 1) : conv (volume : Measure (Rd 1)) (heatK 1) x = 1 := by
  have h := heat_identity leb_spectral one_pos x
  rw [integral_dirac] at h
  simp only [heatSpec, inner_zero_left, Complex.ofReal_zero, mul_zero, Complex.exp_zero,
    norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, neg_zero, zero_div,
    Real.exp_zero, Complex.ofReal_one, mul_one] at h
  exact_mod_cast h

/-- The contrast: equality at `x` and at `0`. -/
theorem strict_peak_contrast (x : Rd 1) :
    conv (volume : Measure (Rd 1)) (heatK 1) x = conv (volume : Measure (Rd 1)) (heatK 1) 0 := by
  rw [conv_eq_one, conv_eq_one]

/-- A strict peak at the origin is false. -/
theorem strict_peak_false :
    ¬ (∀ (Γ μ : Measure (Rd 1)), IsSpectralMeasure Γ μ → ∀ ε : ℝ, 0 < ε → ∀ x : Rd 1,
        x ≠ 0 → conv Γ (heatK ε) x < conv Γ (heatK ε) 0) := by
  intro h
  have hx : (EuclideanSpace.single 0 1 : Rd 1) ≠ 0 := by
    intro h0
    have := congrArg (fun v : Rd 1 => v 0) h0
    simp at this
  have := h volume (Measure.dirac 0) leb_spectral 1 one_pos _ hx
  rw [strict_peak_contrast] at this
  exact lt_irrefl _ this

end Refutations.VariationalMean.Peak
