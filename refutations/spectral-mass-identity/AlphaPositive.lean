/-
Refutation for the hypothesis `0 < α` of the package theorem
`StratonovichHAMSecondMoment.SpectralMassIdentity.resolvent_one_eq_ralpha`
(`R_Γ(1) = R_α`; `E:intro-spectral-mass`, main TeX lines 526-532, under
`0 < α < 2` as in main TeX line 860 and `H:homog`).

Wrong variant: the identity with the hypothesis `0 < α` dropped.  Witness:
`d = 1`, `μ = δ_0`, `α = 0` (locally finite, homogeneous of degree `0`).
Then `R_Γ(1) = ∫ δ_0(dξ)/(1+|ξ|²) = 1`, while Lean evaluates
`R_0 = 0·π·1/(2 sin 0)` to `0`.
Junk-value reliance: this is a control of Lean's totalized division outside
the manuscript's domain, not a convention-independent counterexample.  The
witness has `α = 0`, outside `H:homog` (`α > 0`), where the TeX gives no
value to `R_α`; `R_0` is then `0/0`, undefined as an ordinary quotient, and
Lean's convention `x/0 = 0` makes it `0`.  The continuous extension of
`α π/(2 sin(π α/2))` at `α = 0` is `1`, which would give `R_0 = 1 = R_Γ(1)`.
(`R_Γ(1) = 1` is a genuine integral.)

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.SpectralMassIdentity

set_option autoImplicit false

open MeasureTheory Set Real

namespace Refutations.SpectralMassIdentity.AlphaPositive

open StratonovichHAMSecondMoment.HomogHypothesis StratonovichHAMSecondMoment.SpectralHomog
  StratonovichHAMSecondMoment.SpectralMassIdentity

theorem dirac_homog : SpectralHomogeneous (Measure.dirac (0 : Rd 1)) 0 := by
  intro A _ c hc
  rw [Real.rpow_zero, ENNReal.ofReal_one, one_mul, Measure.dirac_apply, Measure.dirac_apply]
  by_cases h0 : (0 : Rd 1) ∈ A
  · rw [Set.indicator_of_mem h0, Set.indicator_of_mem ((Set.zero_mem_smul_set_iff hc.ne').2 h0)]
  · rw [Set.indicator_of_notMem h0,
      Set.indicator_of_notMem (fun h => h0 ((Set.zero_mem_smul_set_iff hc.ne').1 h))]

/-- Dropping `0 < α` from `R_Γ(1) = R_α` is false. -/
theorem alpha_positive_refuted :
    ¬ (∀ (μ : Measure (Rd 1)) [IsLocallyFiniteMeasure μ] (alpha : ℝ),
        SpectralHomogeneous μ alpha → alpha < 2 → resolvent μ 1 = ralpha μ alpha) := by
  intro h
  have hv := h (Measure.dirac 0) 0 dirac_homog (by norm_num)
  simp [StratonovichHAMSecondMoment.SpectralHomog.resolvent, ralpha] at hv

/-- At the witness the two sides are `1` and `0`. -/
theorem alpha_positive_contrast :
    resolvent (Measure.dirac (0 : Rd 1)) 1 = 1 ∧ ralpha (Measure.dirac (0 : Rd 1)) 0 = 0 := by
  constructor <;> simp [StratonovichHAMSecondMoment.SpectralHomog.resolvent, ralpha]

end Refutations.SpectralMassIdentity.AlphaPositive
