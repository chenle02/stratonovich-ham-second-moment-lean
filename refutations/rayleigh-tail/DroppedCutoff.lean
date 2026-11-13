import StratonovichHAMSecondMoment.RayleighTail

/-!
Refutation for `StratonovichHAMSecondMoment.RayleighTail.rayleigh_tail`
(manuscript `L:tube-rayleigh-tail`, display `E:tube-rayleigh-tail`): the cutoff
hypothesis `4C ≤ M^(2-ν)` cannot be dropped.

The wrong variant is the package statement (same binders and remaining
hypotheses, same conclusion) with `hcut` removed. Witness: the tight step
function `G` (`G = A₀` on `[0, M]`, `A₀ + C M^ν` on `(M, ∞)`) with `C = 10`,
`ν = 3/2`, `M = 1`, `δ = 1`, `A₀ = 0` (so `4C = 40 > 1 = M^(2-ν)`). The tail
integral is `e^{10 - 1/2}`, which exceeds `4 e^{-1/4}`.
The contrast theorem shows the witness violates exactly `hcut`, and applies the
package theorem to the same witness family whenever `hcut` holds.

Expected outcome: compiles (refuted).
-/

set_option autoImplicit false

open MeasureTheory Filter Set Topology

namespace Refutations.RayleighTail

/-- Tight witness (a test function for the refutation, not a package
definition): `G = A₀` up to `M`, then the constant `A₀ + C M^ν`. -/
private noncomputable def tightG (A₀ C ν M : ℝ) (r : ℝ) : ℝ :=
  if M < r then A₀ + C * M ^ ν else A₀

private theorem tightG_measurable (A₀ C ν M : ℝ) : Measurable (tightG A₀ C ν M) :=
  Measurable.ite measurableSet_Ioi measurable_const measurable_const

private theorem tightG_growth (A₀ C ν M : ℝ) (hC : 0 ≤ C) (hν : 0 < ν) (hM : 0 ≤ M) :
    ∀ r, 0 ≤ r → tightG A₀ C ν M r ≤ A₀ + C * r ^ ν := by
  intro r hr
  unfold tightG
  split_ifs with h
  · have := Real.rpow_le_rpow hM h.le hν.le
    nlinarith [mul_le_mul_of_nonneg_left this hC]
  · nlinarith [mul_nonneg hC (Real.rpow_nonneg hr ν)]

/-- Exact tail integral of the tight witness:
`∫_M^∞ (r/δ) e^{(K - r²/2)/δ} dr = e^{(K - M²/2)/δ}`. -/
private theorem tight_integral (A₀ C ν M δ : ℝ) (hδ : 0 < δ) (hM : 0 ≤ M) :
    ∫ r in Ioi M, r / δ * Real.exp ((tightG A₀ C ν M r - r ^ 2 / 2) / δ) =
      Real.exp ((A₀ + C * M ^ ν - M ^ 2 / 2) / δ) := by
  set K := A₀ + C * M ^ ν
  have hcongr : ∫ r in Ioi M, r / δ * Real.exp ((tightG A₀ C ν M r - r ^ 2 / 2) / δ) =
      ∫ r in Ioi M, r / δ * Real.exp ((K - r ^ 2 / 2) / δ) := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun r hr => ?_)
    have h : M < r := hr
    simp [tightG, h, K]
  rw [hcongr]
  set F : ℝ → ℝ := fun r => -Real.exp ((K - r ^ 2 / 2) / δ) with hF
  have hderiv : ∀ x ∈ Ici M,
      HasDerivAt F (x / δ * Real.exp ((K - x ^ 2 / 2) / δ)) x := by
    intro x _
    have h1 : HasDerivAt (fun r : ℝ => (K - r ^ 2 / 2) / δ) ((0 - 2 * x / 2) / δ) x := by
      have := (((hasDerivAt_pow 2 x).div_const 2).const_sub K).div_const δ
      simpa using this
    have h2 := (h1.exp).neg
    convert h2 using 1
    field_simp
    ring
  have hlim : Tendsto F atTop (𝓝 0) := by
    have hq : Tendsto (fun r : ℝ => (K - r ^ 2 / 2) / δ) atTop atBot := by
      have h0 : Tendsto (fun r : ℝ => r ^ 2 / 2) atTop atTop :=
        (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).atTop_div_const (by norm_num)
      have h1 : Tendsto (fun r : ℝ => K - r ^ 2 / 2) atTop atBot :=
        tendsto_atBot_add_const_left _ K (tendsto_neg_atTop_atBot.comp h0) |>.congr
          (fun r => by simp [sub_eq_add_neg])
      exact h1.atBot_div_const hδ
    have := (Real.tendsto_exp_atBot.comp hq).neg
    simpa [hF] using this
  have hpos : ∀ x ∈ Ioi M, 0 ≤ x / δ * Real.exp ((K - x ^ 2 / 2) / δ) := by
    intro x hx
    have hx0 : 0 ≤ x := hM.trans (le_of_lt hx)
    positivity
  have hint := integrableOn_Ioi_deriv_of_nonneg' hderiv hpos hlim
  rw [integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hint hlim]
  simp [hF]

/-- `rayleigh_tail` without the cutoff hypothesis `4C ≤ M^(2-ν)` is false. -/
theorem rayleigh_tail_dropped_cutoff :
    ¬ (∀ (G : ℝ → ℝ), Measurable G → ∀ (A₀ C ν M δ : ℝ),
      (∀ r, 0 ≤ r → G r ≤ A₀ + C * r ^ ν) → 0 ≤ C → 1 < ν → ν < 2 → 0 < δ →
      0 < M →
      IntegrableOn (fun r : ℝ => r / δ * Real.exp ((G r - r ^ 2 / 2) / δ)) (Ioi M) ∧
        ∫ r in Ioi M, r / δ * Real.exp ((G r - r ^ 2 / 2) / δ) ≤
          4 * Real.exp ((A₀ - M ^ 2 / 4) / δ)) := by
  intro h
  set ν : ℝ := 3 / 2
  obtain ⟨_, hle⟩ := h (tightG 0 10 ν 1) (tightG_measurable _ _ _ _) 0 10 ν 1 1
    (tightG_growth 0 10 ν 1 (by norm_num) (by norm_num [ν]) (by norm_num)) (by norm_num)
    (by norm_num [ν]) (by norm_num [ν]) one_pos one_pos
  rw [tight_integral 0 10 ν 1 1 one_pos zero_le_one] at hle
  norm_num at hle
  -- hle : rexp (19/2) ≤ 4 * rexp (-1/4)
  have hbig : (39 / 4 + 1 : ℝ) < Real.exp (39 / 4) :=
    Real.add_one_lt_exp (by norm_num)
  have hsplit : Real.exp (19 / 2) = Real.exp (39 / 4) * Real.exp (-1 / 4) := by
    rw [← Real.exp_add]; norm_num
  have hpos := Real.exp_pos (-1 / 4)
  nlinarith [hsplit]

/-- Contrast: the witness (`C = 10`, `ν = 3/2`, `M = 1`) violates exactly the
dropped hypothesis `4C ≤ M^(2-ν)`; on the same witness family the
package theorem gives the bound for every `C ≥ 0` satisfying the cutoff. -/
theorem rayleigh_tail_dropped_cutoff_contrast :
    ¬ (4 * (10 : ℝ) ≤ (1 : ℝ) ^ (2 - (3 / 2 : ℝ))) ∧
      ∀ C : ℝ, 0 ≤ C → 4 * C ≤ (1 : ℝ) ^ (2 - (3 / 2 : ℝ)) →
        ∫ r in Ioi (1 : ℝ),
            r / 1 * Real.exp ((tightG 0 C (3 / 2) 1 r - r ^ 2 / 2) / 1) ≤
          4 * Real.exp ((0 - (1 : ℝ) ^ 2 / 4) / 1) := by
  refine ⟨by norm_num, fun C hC hcut => ?_⟩
  exact (StratonovichHAMSecondMoment.RayleighTail.rayleigh_tail (tightG 0 C (3 / 2) 1)
    (tightG_measurable _ _ _ _) 0 C (3 / 2) 1 1
    (tightG_growth 0 C (3 / 2) 1 hC (by norm_num) (by norm_num)) hC (by norm_num)
    (by norm_num) one_pos one_pos hcut).2

end Refutations.RayleighTail
