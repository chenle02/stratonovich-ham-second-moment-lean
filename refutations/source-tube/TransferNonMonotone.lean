/-
Refutation for `P:tube-rayleigh-transfer`
(`notes/integrated_gaussian_tubes.tex` lines 225-271 at 39f2597a), package
theorem `StratonovichHAMSecondMoment.SourceTube.tube_rayleigh_transfer_zero`.

Class (a): manuscript-claim perturbation in the manuscript domain (the zero-law
case of the proposition, with the hypothesis "G nondecreasing" dropped).
Counterexample: `δ = 1/2`, `X = 0` on a one-point probability space, `F = 0`,
`G(0) = 0` and `G(r) = -1` for `r > 0`, so `F(0) ≤ G(0)`.  The left side is
`e^0 = 1`; the right side is `e^{-1/δ} · ∫_0^∞ (r/δ) e^{-r²/(2δ)} dr = e^{-2} < 1`.
`non_monotone_contrast` is the package inequality for the nondecreasing `G = 0`
at the same `X`, `F`, `δ`.  No junk-value reliance.

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.SourceTube

set_option autoImplicit false

open MeasureTheory Set
open StratonovichHAMSecondMoment SourceTube

namespace Refutations.SourceTube

/-- The zero-law transfer without monotonicity of `G` is false. -/
theorem non_monotone_refuted :
    ¬ (∀ (F G : ℝ → ℝ), F 0 ≤ G 0 →
        ∫⁻ _ω, ENNReal.ofReal (Real.exp (F ((fun _ : Unit => (0 : ℝ)) _ω) / (1 / 2)))
            ∂(Measure.dirac ()) ≤
          ∫⁻ r in Ioi 0,
            ENNReal.ofReal (r / (1 / 2) * Real.exp ((G r - r ^ 2 / 2) / (1 / 2)))) := by
  intro h
  have := h (fun _ => 0) (fun r => if r ≤ 0 then 0 else -1) (by simp)
  rw [lintegral_dirac] at this
  have hr : ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (r / (1 / 2) *
      Real.exp (((fun r : ℝ => if r ≤ 0 then (0 : ℝ) else -1) r - r ^ 2 / 2) / (1 / 2))) =
      ENNReal.ofReal (Real.exp (-2)) := by
    rw [← mul_one (ENNReal.ofReal (Real.exp (-2))), ← lintegral_rayleigh_one (δ := 1 / 2)
      (by norm_num), ← lintegral_const_mul _ (measurable_rayleighDensity _).ennreal_ofReal]
    refine setLIntegral_congr_fun measurableSet_Ioi fun r hr => ?_
    have hr0 : ¬ r ≤ 0 := not_le.2 hr
    simp only [hr0, ite_false, rayleighDensity]
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
    congr 1
    rw [mul_left_comm, ← Real.exp_add]
    congr 2
    ring
  rw [hr] at this
  simp only [div_eq_mul_inv, zero_mul, Real.exp_zero, ENNReal.ofReal_one] at this
  rw [ENNReal.one_le_ofReal] at this
  have := Real.exp_lt_one_iff.2 (by norm_num : (-2 : ℝ) < 0)
  linarith

/-- The package inequality (zero law) for the nondecreasing `G = 0` at the same point. -/
theorem non_monotone_contrast :
    ∫⁻ _ω, ENNReal.ofReal (Real.exp ((fun _ : ℝ => (0 : ℝ)) ((fun _ : Unit => (0 : ℝ)) _ω) /
        (1 / 2))) ∂(Measure.dirac ()) ≤
      ∫⁻ r in Ioi 0, ENNReal.ofReal (r / (1 / 2) *
        Real.exp (((fun _ : ℝ => (0 : ℝ)) r - r ^ 2 / 2) / (1 / 2))) :=
  tube_rayleigh_transfer_zero (P := Measure.dirac ()) (fun _ : Unit => (0 : ℝ))
    (Filter.Eventually.of_forall fun _ => rfl) (1 / 2) (by norm_num) (fun _ => 0) (fun _ => 0)
    (fun _ _ _ _ _ => le_rfl) le_rfl

end Refutations.SourceTube
