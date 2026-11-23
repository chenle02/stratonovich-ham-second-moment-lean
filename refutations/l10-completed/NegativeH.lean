import StratonovichHAMSecondMoment.L10Completed

/-!
Refutation for the sign condition of `E:alpha-one-convolution` after integration against `σ`
(`L:alpha-one-convolution`, main TeX lines 5635-5643 and 5702-5704 at edf7085f; the lemma
assumes `h > 0`), package theorem
`StratonovichHAMSecondMoment.L10Completed.alpha_one_convolution_completed` (hypothesis
`0 < h`), whose conclusion equates the pairing with `∫ I_a(h,θ·z) σ(dθ)` and bounds it below
by `0`.

Wrong variant: `0 ≤ ∫ I_a(h,θ·z) σ(dθ)` without `h > 0`.  Witness: Lebesgue measure on `ℝ¹`
(`0 < V < ∞`), `a = 1/4`, `h = -1`, `z = 0`: the spectral side is
`V I_{1/4}(-1,0) = -V I_{1/4}(1,0) < 0` (`Ia_neg_h`, `I_{1/4}(1,0) > π/4 > 0`).  This lifts
the pointwise refutation `alpha-one-convolution/DroppedPositiveH` to the integrated statement.
No junk value: the radial and angular integrands are integrable.  The contrast theorem
evaluates the spectral side at `h = ±1`.

Expected outcome: compiles (refuted).
-/

set_option autoImplicit false

open MeasureTheory Set Real Metric

namespace Refutations.L10Completed.NegH

open StratonovichHAMSecondMoment StratonovichHAMSecondMoment.HomogHypothesis
  StratonovichHAMSecondMoment.SpectralHomog StratonovichHAMSecondMoment.AlphaOneConvolution

theorem leb_homogeneous : SpectralHomogeneous (volume : Measure (Rd 1)) 1 := by
  intro A _ c hc
  rw [Measure.addHaar_smul, finrank_euclideanSpace_fin, pow_one, abs_of_pos hc,
    Real.rpow_one]

theorem leb_tempered : IsTempered (volume : Measure (Rd 1)) := by
  refine ⟨2, ?_⟩
  have h : Integrable (fun x : Rd 1 => (1 + ‖x‖) ^ (-((2 : ℕ) : ℝ))) volume :=
    integrable_one_add_norm (by simp)
  exact h.lintegral_lt_top

/-- Contrast: the spectral side at `h = -1` is negative and at `h = 1` positive. -/
theorem negative_h_contrast :
    ∫ θ, Ia (1 / 4) (-1) (inner ℝ θ (0 : Rd 1)) ∂(sphereMeasure volume) < 0 ∧
      0 < ∫ θ, Ia (1 / 4) 1 (inner ℝ θ (0 : Rd 1)) ∂(sphereMeasure volume) := by
  obtain ⟨-, -, hσV, -, -⟩ := polar_decomposition leb_homogeneous
  have hV : 0 < (volume (closedBall (0 : Rd 1) 1)).toReal :=
    ENNReal.toReal_pos (measure_closedBall_pos _ _ one_pos).ne' measure_closedBall_lt_top.ne
  obtain ⟨-, -, hId, -, -⟩ := alpha_one_radial (1 / 4) 1 0 (by norm_num) zero_le_one
  have hb := boxConv_zero_ge (1 / 4) 1 (by norm_num) zero_le_one
  have hg : 0 < gauss1 (1 / 4) 1 := by unfold gauss1; positivity
  have hpos : 0 < Ia (1 / 4) 1 0 := by rw [hId]; nlinarith [Real.pi_pos]
  simp only [inner_zero_right]
  rw [integral_const, integral_const, smul_eq_mul, smul_eq_mul, measureReal_def, hσV, Ia_neg_h]
  constructor <;> nlinarith

/-- Nonnegativity of the spectral side without `h > 0` is false. -/
theorem negative_h :
    ¬ ∀ μ : Measure (Rd 1), IsLocallyFiniteMeasure μ → SpectralHomogeneous μ 1 →
      IsTempered μ → ∀ a h : ℝ, 0 < a → ∀ z : Rd 1,
        0 ≤ ∫ θ, Ia a h (inner ℝ θ z) ∂(sphereMeasure μ) := by
  intro H
  have := H volume inferInstance leb_homogeneous leb_tempered (1 / 4) (-1) (by norm_num) 0
  linarith [negative_h_contrast.1]

end Refutations.L10Completed.NegH
