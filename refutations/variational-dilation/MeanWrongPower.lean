/-
Refutation for the mean part of `L:variational-control-dilation`
(`notes/integrated_unmasked_variational.tex` lines 234-235), package theorem
`StratonovichHAMSecondMoment.VariationalDilation.mean_dil` and package
definitions `mean`, `dil`, `conv`, `SetScaling`.

Wrong variant: `h_{D_rΨ,s}(x) = r h_{Ψ,s}(r x)` (power `r^1` instead of `r^2`,
as if the amplitude `r^{d+2-α}` were not offset by the Radon factor
`r^{α-d}`).  Counterexample: `d = 1`, `α = 1`, `Γ = δ_0` (white noise; it
satisfies the set scaling `Γ(cA) = c^{d-α} Γ(A) = Γ(A)`), `a = 0`, `Ψ ≡ 1`,
`r = 2`, `s = 0`, `x = 0`, where `h_{Ψ,0}(0) = 1`.  No junk value is used:
every integral here is of a bounded function against a finite measure.

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.VariationalDilation

set_option autoImplicit false

open MeasureTheory
open scoped Pointwise

namespace Refutations.VariationalDilation

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

/-- `h_{Ψ,s}(x) = 1` for `Γ = δ_0`, `a = 0`, `Ψ ≡ 1`. -/
theorem mean_one (s : ℝ) (x : Rd 1) :
    mean 0 (Measure.dirac 0) (fun _ : ℝ × Rd 1 => (1 : ℝ)) s x = 1 := by
  simp [mean, conv]

/-- The wrong power `r^1` fails. -/
theorem mean_power_one_false :
    ¬ ∀ (d : ℕ) (alpha : ℝ) (Γ : Measure (Rd d)), SetScaling alpha Γ →
      ∀ r : ℝ, 0 < r → ∀ Ψ : ℝ × Rd d → ℝ, Continuous Ψ → ∀ (a s : ℝ) (x : Rd d),
        mean a Γ (dil alpha r Ψ) s x = r * mean a Γ Ψ s (r • x) := by
  intro h
  have hw := h 1 1 _ dirac_setScaling 2 two_pos (fun _ => 1) continuous_const 0 0 0
  have hp := mean_dil dirac_setScaling two_pos
    (continuous_const : Continuous (fun _ : ℝ × Rd 1 => (1 : ℝ))) 0 0 0
  rw [hp, mean_one] at hw
  norm_num at hw

/-- Contrast: the package identity at the same counterexample gives the factor
`r² = 4`. -/
theorem mean_power_two_contrast :
    mean 0 (Measure.dirac 0) (dil 1 2 (fun _ : ℝ × Rd 1 => (1 : ℝ))) 0 0 = 2 ^ 2 := by
  rw [mean_dil dirac_setScaling two_pos continuous_const, mean_one, mul_one]

end Refutations.VariationalDilation
