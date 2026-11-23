import StratonovichHAMSecondMoment.L10Completed

/-!
Refutation for the constant of `E:alpha-one-convolution` (`L:alpha-one-convolution`, main TeX
lines 5635-5643 and 5702-5704 at edf7085f), package theorem
`StratonovichHAMSecondMoment.L10Completed.alpha_one_convolution_completed`, whose conclusion
equates the pairing with the spectral side `∫ I_a(h,θ·z) σ(dθ)` (`E:alpha-one-polar`) and
bounds it by `πV/2`.

Wrong variant: the bound `πV/4` for the spectral side `∫ I_a(h,θ·z) σ(dθ)`, over all locally
finite tempered `μ` with `μ(cA) = cμ(A)` (the spectral hypotheses of the completed theorem).
Witness: Lebesgue measure on `ℝ¹` (`0 < V < ∞`), `a = 1/4`, `h = 1`, `z = 0`.  Then the spectral
side is `V I_{1/4}(1,0)` and `I_{1/4}(1,0) = π (g_1 * p_{1/2})(0) > π/4`: a two-step lower
Riemann sum gives `(g_1 * p_{1/2})(0) ≥ ½ p(½) + ½ p(1) ≥ ½·3/8 + ½·0.18 > 1/4`, with
`p(w) = π^{-1/2} e^{-w²}`.  So the constant `π/2` cannot be halved (the existing refutation
`alpha-one-convolution/WrongRadialConstant` refutes `π/8` pointwise; this one refutes `π/4`
after integration against `σ`).  No junk value: every integral is shown integrable.
The contrast theorem places the witness value strictly between `πV/4` and `πV/2`.

Expected outcome: compiles (refuted).
-/

set_option autoImplicit false

open MeasureTheory Set Real Metric

namespace Refutations.L10Completed

open StratonovichHAMSecondMoment StratonovichHAMSecondMoment.HomogHypothesis
  StratonovichHAMSecondMoment.SpectralHomog StratonovichHAMSecondMoment.AlphaOneConvolution

theorem leb_one_homogeneous : SpectralHomogeneous (volume : Measure (Rd 1)) 1 := by
  intro A _ c hc
  rw [Measure.addHaar_smul, finrank_euclideanSpace_fin, pow_one, abs_of_pos hc,
    Real.rpow_one]

theorem leb_one_tempered : IsTempered (volume : Measure (Rd 1)) := by
  refine ⟨2, ?_⟩
  have h : Integrable (fun x : Rd 1 => (1 + ‖x‖) ^ (-((2 : ℕ) : ℝ))) volume :=
    integrable_one_add_norm (by simp)
  exact h.lintegral_lt_top

/-- `p_{1/2}(w) = π^{-1/2} e^{-w²}` is antitone in `w²`. -/
theorem gauss1_anti {a w w' : ℝ} (ha : 0 < a) (hw : w' ^ 2 ≤ w ^ 2) :
    gauss1 a w ≤ gauss1 a w' := by
  unfold gauss1
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by positivity)
  have := div_le_div_of_nonneg_right hw (by positivity : (0 : ℝ) ≤ 4 * a)
  linarith

/-- Two-step lower Riemann sum: `k p(k) + (h-k) p(h) ≤ (g_h * p_{2a})(0)`, `0 ≤ k ≤ h`. -/
theorem boxConv_zero_ge_two (a h k : ℝ) (ha : 0 < a) (hk : 0 ≤ k) (hkh : k ≤ h) :
    k * gauss1 a k + (h - k) * gauss1 a h ≤ boxConv a h 0 := by
  have hI := (alpha_one_radial a h 0 ha (hk.trans hkh)).2.1
  set c1 := (1 / 2 : ℝ) * (gauss1 a k - gauss1 a h)
  set c2 := (1 / 2 : ℝ) * gauss1 a h
  have hc : Integrable (fun u => (Ioo (-k) k).indicator (fun _ : ℝ => c1) u +
      (Ioo (-h) h).indicator (fun _ : ℝ => c2) u) :=
    ((integrable_indicator_iff measurableSet_Ioo).2 (integrableOn_const (by simp))).add
      ((integrable_indicator_iff measurableSet_Ioo).2 (integrableOn_const (by simp)))
  have hle : ∀ u, (Ioo (-k) k).indicator (fun _ : ℝ => c1) u +
      (Ioo (-h) h).indicator (fun _ : ℝ => c2) u ≤ gBox h u * gauss1 a (0 - u) := by
    intro u
    by_cases hu : u ∈ Ioo (-h) h
    · rw [gBox, indicator_of_mem hu, indicator_of_mem hu]
      by_cases hu' : u ∈ Ioo (-k) k
      · rw [indicator_of_mem hu']
        have : gauss1 a k ≤ gauss1 a (0 - u) :=
          gauss1_anti ha (by nlinarith [hu'.1, hu'.2])
        simp only [c1, c2]; linarith
      · rw [indicator_of_notMem hu']
        have : gauss1 a h ≤ gauss1 a (0 - u) :=
          gauss1_anti ha (by nlinarith [hu.1, hu.2])
        simp only [c2]; linarith
    · have hu' : u ∉ Ioo (-k) k := fun h' => hu ⟨by linarith [h'.1], by linarith [h'.2]⟩
      rw [gBox, indicator_of_notMem hu, indicator_of_notMem hu', indicator_of_notMem hu]
      simp
  calc k * gauss1 a k + (h - k) * gauss1 a h
      = ∫ u, ((Ioo (-k) k).indicator (fun _ : ℝ => c1) u +
          (Ioo (-h) h).indicator (fun _ : ℝ => c2) u) := by
        rw [integral_add ((integrable_indicator_iff measurableSet_Ioo).2
            (integrableOn_const (by simp)))
          ((integrable_indicator_iff measurableSet_Ioo).2 (integrableOn_const (by simp))),
          integral_indicator_const _ measurableSet_Ioo,
          integral_indicator_const _ measurableSet_Ioo, measureReal_def, measureReal_def,
          Real.volume_Ioo, Real.volume_Ioo, ENNReal.toReal_ofReal (by linarith),
          ENNReal.toReal_ofReal (by linarith), smul_eq_mul, smul_eq_mul]
        simp only [c1, c2]; ring
    _ ≤ boxConv a h 0 := integral_mono hc hI hle

theorem gauss1_quarter_bounds :
    3 / 8 ≤ gauss1 (1 / 4) (1 / 2) ∧ 9 / 50 < gauss1 (1 / 4) 1 := by
  have hpi : 4 * π * (1 / 4) = π := by ring
  have hs : Real.sqrt π ≤ 2 := by
    rw [Real.sqrt_le_left (by norm_num)]; linarith [Real.pi_le_four]
  have hs0 : 0 < Real.sqrt π := Real.sqrt_pos.2 Real.pi_pos
  have h1 : (1 / 2 : ℝ) ≤ (Real.sqrt π)⁻¹ := by
    rw [le_inv_comm₀ (by norm_num) hs0]; linarith
  unfold gauss1
  rw [hpi, Real.rpow_neg Real.pi_pos.le, ← Real.sqrt_eq_rpow]
  constructor
  · have he : (3 / 4 : ℝ) ≤ Real.exp (-((1 / 2) ^ 2 / (4 * (1 / 4)))) := by
      have := Real.add_one_le_exp (-((1 / 2 : ℝ) ^ 2 / (4 * (1 / 4))))
      norm_num at this ⊢; linarith
    nlinarith [Real.exp_pos (-((1 / 2 : ℝ) ^ 2 / (4 * (1 / 4))))]
  · have he : (0.36 : ℝ) < Real.exp (-(1 ^ 2 / (4 * (1 / 4)))) := by
      have := Real.exp_neg_one_gt_d9
      norm_num at this ⊢; linarith
    nlinarith [Real.exp_pos (-(1 ^ 2 / (4 * (1 / 4) : ℝ)))]

/-- `I_{1/4}(1,0) > π/4`. -/
theorem Ia_quarter_gt : π / 4 < Ia (1 / 4) 1 0 := by
  obtain ⟨-, -, hId, -, -⟩ := alpha_one_radial (1 / 4) 1 0 (by norm_num) zero_le_one
  have hb := boxConv_zero_ge_two (1 / 4) 1 (1 / 2) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨g1, g2⟩ := gauss1_quarter_bounds
  rw [hId]
  nlinarith [Real.pi_pos]

/-- Contrast: for Lebesgue `μ` on `ℝ¹`, `a = 1/4`, `h = 1`, `z = 0`, the spectral side lies
strictly between `πV/4` and `πV/2` (the upper bound from the completed general form's
spectral-side bound, `alpha_one_polar`). -/
theorem quarter_bound_contrast :
    π * (volume (closedBall (0 : Rd 1) 1)).toReal / 4 <
        ∫ θ, Ia (1 / 4) 1 (inner ℝ θ (0 : Rd 1)) ∂(sphereMeasure volume) ∧
      ∫ θ, Ia (1 / 4) 1 (inner ℝ θ (0 : Rd 1)) ∂(sphereMeasure volume) ≤
        π * (volume (closedBall (0 : Rd 1) 1)).toReal / 2 := by
  obtain ⟨-, -, hσV, -, -⟩ := polar_decomposition leb_one_homogeneous
  have hV : 0 < (volume (closedBall (0 : Rd 1) 1)).toReal :=
    ENNReal.toReal_pos (measure_closedBall_pos _ _ one_pos).ne' measure_closedBall_lt_top.ne
  refine ⟨?_, (alpha_one_polar leb_one_homogeneous leb_one_tempered (by norm_num : (0 : ℝ) <
    1 / 4) zero_le_one 0).2.2.2.2⟩
  simp only [inner_zero_right]
  rw [integral_const, smul_eq_mul, measureReal_def, hσV]
  nlinarith [Ia_quarter_gt]

/-- The bound `πV/4` for the spectral side of `E:alpha-one-polar` is false. -/
theorem quarter_bound :
    ¬ ∀ μ : Measure (Rd 1), IsLocallyFiniteMeasure μ → SpectralHomogeneous μ 1 →
      IsTempered μ → ∀ a h : ℝ, 0 < a → 0 < h → ∀ z : Rd 1,
        ∫ θ, Ia a h (inner ℝ θ z) ∂(sphereMeasure μ) ≤ π * (μ (closedBall 0 1)).toReal / 4 := by
  intro H
  have := H volume inferInstance leb_one_homogeneous leb_one_tempered (1 / 4) 1 (by norm_num)
    one_pos 0
  linarith [quarter_bound_contrast.1]

end Refutations.L10Completed
