/-
Refutation for the variance part of `L:variational-control-dilation`
(`notes/integrated_unmasked_variational.tex` lines 234-235 and 254-258),
package theorem `StratonovichHAMSecondMoment.VariationalDilation.rawCost_dil`
and package definitions `rawCost`, `mean`, `dil`, `SetScaling`.

Wrong variant: `v_{D_rΨ} = r^{d+4-α} v_Ψ`, i.e. the Lebesgue volume factor
`r^{-d}` of the substitution `z = r x` forgotten (the TeX stresses that the
Radon pushforward and the spatial volume factor must be distinguished).
Counterexample: `d = 1`, `α = 1`, `Γ = δ_0`, `a = 0`, `Ψ(u,x) = b(x)` for a
smooth bump `b ≥ 0` with `b(0) = 1`, `r = 2`; here `v_Ψ = ∫ b² > 0`, and the
wrong factor `2^4` differs from the true `2^3`.  No junk value is used: `v_Ψ`
is the integral of a continuous compactly supported function and is shown
positive.

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.VariationalDilation

set_option autoImplicit false

open MeasureTheory
open scoped Pointwise

namespace Refutations.VariationalDilation.Variance

open StratonovichHAMSecondMoment.VariationalDilation
open StratonovichHAMSecondMoment.HomogHypothesis (Rd)

/-- The Dirac mass at the origin of `ℝ^1` satisfies the `H:homog` set scaling
with `α = d = 1`. -/
theorem dirac_setScaling : SetScaling (d := 1) 1 (Measure.dirac 0) := by
  intro A hA c hc
  rw [Measure.dirac_apply' _ (hA.const_smul_of_ne_zero hc.ne'), Measure.dirac_apply' _ hA]
  have : ((1 : ℕ) : ℝ) - 1 = 0 := by norm_num
  rw [this, Real.rpow_zero, ENNReal.ofReal_one, one_mul]
  by_cases h0 : (0 : Rd 1) ∈ A
  · rw [Set.indicator_of_mem h0, Set.indicator_of_mem ((Set.zero_mem_smul_set_iff hc.ne').mpr h0)]
  · rw [Set.indicator_of_notMem h0,
      Set.indicator_of_notMem (fun h => h0 ((Set.zero_mem_smul_set_iff hc.ne').mp h))]

/-- A smooth bump on `ℝ^1` centred at `0`. -/
def b : ContDiffBump (0 : Rd 1) := ⟨1, 2, one_pos, one_lt_two⟩

/-- The control `Ψ(u,x) = b(x)`. -/
noncomputable def Ψb : ℝ × Rd 1 → ℝ := fun p => b p.2

theorem Ψb_continuous : Continuous Ψb := b.continuous.comp continuous_snd

theorem mean_Ψb (s : ℝ) (x : Rd 1) : mean 0 (Measure.dirac 0) Ψb s x = b x := by
  simp [mean, conv, Ψb]

theorem rawCost_Ψb : rawCost 0 (Measure.dirac 0) Ψb = ∫ x, b x * b x := by
  simp [rawCost, mean_Ψb, Ψb]

theorem rawCost_Ψb_pos : 0 < rawCost 0 (Measure.dirac 0) Ψb := by
  rw [rawCost_Ψb]
  refine Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := 0)
    (b.continuous.mul b.continuous) (b.hasCompactSupport.mul_left) (fun x => ?_) ?_
  · exact mul_nonneg b.nonneg b.nonneg
  · rw [b.one_of_mem_closedBall (Metric.mem_closedBall_self zero_le_one), mul_one]
    exact one_ne_zero

/-- The variant without the Lebesgue volume factor fails. -/
theorem variance_no_jacobian_false :
    ¬ ∀ (d : ℕ) (alpha : ℝ) (Γ : Measure (Rd d)), SetScaling alpha Γ →
      ∀ r : ℝ, 0 < r → ∀ Ψ : ℝ × Rd d → ℝ, Continuous Ψ → ∀ a : ℝ,
        rawCost a Γ (dil alpha r Ψ) = r ^ ((d : ℝ) + 4 - alpha) * rawCost a Γ Ψ := by
  intro h
  have hw := h 1 1 _ dirac_setScaling 2 two_pos Ψb Ψb_continuous 0
  rw [rawCost_dil dirac_setScaling two_pos Ψb_continuous] at hw
  have e1 : ((1 : ℕ) : ℝ) + 4 - 1 = ((4 : ℕ) : ℝ) := by norm_num
  have e2 : (4 : ℝ) - 1 = ((3 : ℕ) : ℝ) := by norm_num
  rw [e1, e2, Real.rpow_natCast, Real.rpow_natCast] at hw
  have hv := rawCost_Ψb_pos
  nlinarith

/-- Contrast: the package factor at the same counterexample is `2^{4-1} = 8`,
and `v_Ψ > 0` makes the two factors distinguishable. -/
theorem variance_jacobian_contrast :
    rawCost 0 (Measure.dirac 0) (dil 1 2 Ψb) = 2 ^ (4 - 1 : ℝ) * rawCost 0 (Measure.dirac 0) Ψb ∧
      0 < rawCost 0 (Measure.dirac 0) Ψb :=
  ⟨rawCost_dil dirac_setScaling two_pos Ψb_continuous 0, rawCost_Ψb_pos⟩

end Refutations.VariationalDilation.Variance
