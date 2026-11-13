/-
Refutation for the derived spectral homogeneity, package theorem
`StratonovichHAMSecondMoment.MaskedSpectralGrowth.spectralHomogeneous_of_scaling`
(main TeX lines 851-852 at a284420: `μ(cA) = c^α μ(A)`).

Wrong variant: the spectral measure inherits the exponent of `Γ`, i.e.
`Γ(cA) = c^{d-α}Γ(A)` implies `μ(cA) = c^{d-α}μ(A)`.  Counterexample: `d = 1`,
`Γ` = Lebesgue measure (`d - α = 1`, `α = 0`), `μ = δ_0` (tempered, the
spectral measure of `Γ`): `δ_0(2·{0}) = 1 ≠ 2 = 2^1 δ_0({0})`.
`spectral_exponent_contrast` is the package conclusion at the same pair,
`SpectralHomogeneous δ_0 0`.  `α = 0` is outside the range of `H:homog`; the
refuted statement is a variant of the general theorem, which has no range
condition on `α`.  No junk-value reliance.

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.MaskedSpectralGrowth

set_option autoImplicit false

open MeasureTheory Real
open StratonovichHAMSecondMoment HomogHypothesis SpectralHomog MaskedSpectralGrowth

namespace Refutations.MaskedSpectralGrowth

/-- Lebesgue measure on `ℝ¹` has spectral measure `δ_0`. -/
theorem leb_spectral : IsSpectralMeasure (volume : Measure (Rd 1)) (Measure.dirac 0) := by
  intro φ
  rw [integral_dirac]
  simp

/-- Lebesgue measure on `ℝ¹` scales with exponent `d - α = 1 - 0`. -/
theorem leb_scaling : SpectralHomogeneous (volume : Measure (Rd 1)) (((1 : ℕ) : ℝ) - 0) := by
  intro A _ c hc
  rw [Measure.addHaar_smul, finrank_euclideanSpace_fin, pow_one, abs_of_pos hc]
  norm_num

/-- `δ_0` is tempered. -/
theorem dirac_tempered : IsTempered (Measure.dirac (0 : Rd 1)) :=
  ⟨0, by rw [lintegral_dirac]; simp⟩

/-- Giving `μ` the exponent `d - α` of `Γ` is false. -/
theorem spectral_exponent_refuted :
    ¬ (∀ (Γ μ : Measure (Rd 1)) (alpha : ℝ), IsTempered μ → IsSpectralMeasure Γ μ →
        SpectralHomogeneous Γ (((1 : ℕ) : ℝ) - alpha) →
          SpectralHomogeneous μ (((1 : ℕ) : ℝ) - alpha)) := by
  intro h
  have := h volume (Measure.dirac 0) 0 dirac_tempered leb_spectral leb_scaling {0}
    (measurableSet_singleton 0) 2 two_pos
  rw [Set.smul_set_singleton, smul_zero,
    Measure.dirac_apply_of_mem (Set.mem_singleton (0 : Rd 1))] at this
  norm_num at this

/-- The package conclusion at the same pair: `δ_0` is `0`-homogeneous. -/
theorem spectral_exponent_contrast : SpectralHomogeneous (Measure.dirac (0 : Rd 1)) 0 := by
  have := spectralHomogeneous_of_scaling dirac_tempered leb_spectral leb_scaling
  exact this

end Refutations.MaskedSpectralGrowth
