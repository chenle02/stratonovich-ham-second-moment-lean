/-
Refutation for `E:variational-score-set-scaling` of
`P:variational-positive-scores` (`notes/integrated_unmasked_variational.tex`
lines 298-304 at a284420), package theorems
`StratonovichHAMSecondMoment.VariationalRate.score_set_scaling` and
`StratonovichHAMSecondMoment.VariationalRate.positive_scores`.

Wrong variant: the homogeneity factor `K_c = c^{(4-α)/(3-α)}` replaced by
`c` (linear scaling of the variational values in the coefficient), i.e.
`c I_{D_{r_c}Ψ} - v_{D_{r_c}Ψ}/2 = c (I_Ψ - v_Ψ/2)` for all `c > 0`,
`Ψ ∈ C_pos`.  Counterexample: `d = 1`, `Γ` = Lebesgue measure (set scaling
with `α = 0`, spectral measure `δ_0`, both tempered), `a = 1/2`, `c = 2`.
`positive_scores` supplies `Ψ ∈ C_pos` with `y = I_Ψ - v_Ψ/2 > 0`, and the
package identity gives `2^{4/3} y = 2 y`, false since `2^{4/3} > 2`.  This
`Γ` lies outside `H:homog` (`α = 0`) but inside the hypotheses of the general
theorems.  No junk-value reliance: `positive_scores` proves `I_Ψ`, `v_Ψ`
genuine.

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.VariationalRate

set_option autoImplicit false

open MeasureTheory
open StratonovichHAMSecondMoment HomogHypothesis VariationalDilation VariationalRate

namespace Refutations.VariationalRate

/-- Lebesgue measure on `ℝ¹` is tempered (`k = 2`). -/
theorem leb_tempered : IsTempered (volume : Measure (Rd 1)) := by
  refine ⟨2, ?_⟩
  have h : Integrable (fun x : Rd 1 => (1 + ‖x‖) ^ (-((2 : ℕ) : ℝ))) volume :=
    integrable_one_add_norm (by simp)
  exact h.lintegral_lt_top

/-- `δ_0` is tempered. -/
theorem dirac_tempered : IsTempered (Measure.dirac (0 : Rd 1)) := by
  refine ⟨0, ?_⟩
  rw [lintegral_dirac]
  exact ENNReal.ofReal_lt_top

/-- Lebesgue measure on `ℝ¹` has spectral measure `δ_0`. -/
theorem leb_spectral : IsSpectralMeasure (volume : Measure (Rd 1)) (Measure.dirac 0) := by
  intro φ
  rw [integral_dirac]
  simp

/-- Lebesgue measure on `ℝ¹` has the set scaling with `α = 0`. -/
theorem leb_scaling : SetScaling (d := 1) 0 volume := by
  intro A _ c hc
  rw [Measure.addHaar_smul, finrank_euclideanSpace_fin, pow_one, abs_of_pos hc, sub_zero,
    Nat.cast_one, Real.rpow_one]

/-- Linear scaling of the variational values in the coefficient is false. -/
theorem score_scaling_linear_refuted :
    ¬ (∀ c : ℝ, 0 < c → ∀ Ψ ∈ CPos 1,
        c * integratedRate (1 / 2) volume (dil 0 (c ^ (3 - (0 : ℝ))⁻¹) Ψ) -
            rawCost (1 / 2) volume (dil 0 (c ^ (3 - (0 : ℝ))⁻¹) Ψ) / 2 =
          c * (integratedRate (1 / 2) volume Ψ - rawCost (1 / 2) volume Ψ / 2)) := by
  intro h
  obtain ⟨-, -, -, ⟨y, ⟨Ψ, hΨ, rfl⟩, hy⟩, hscal, -, -⟩ :=
    positive_scores leb_tempered dirac_tempered leb_spectral leb_scaling (by norm_num)
      (NeZero.ne volume) (a := 1 / 2) (by norm_num) (by norm_num)
  have e1 := h 2 two_pos Ψ hΨ
  have e2 := hscal 2 two_pos Ψ hΨ
  rw [e1] at e2
  have hK : (2 : ℝ) < 2 ^ ((4 - (0 : ℝ)) / (3 - 0)) := by
    have := Real.rpow_lt_rpow_of_exponent_lt (x := 2) (by norm_num)
      (show (1 : ℝ) < (4 - 0) / (3 - 0) by norm_num)
    rwa [Real.rpow_one] at this
  simp only at hy
  nlinarith

end Refutations.VariationalRate
