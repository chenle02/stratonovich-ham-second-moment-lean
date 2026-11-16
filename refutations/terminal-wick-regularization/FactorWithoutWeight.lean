/-
Refutation for the identification of one regularized Green factor (main TeX line 4392 at
39f2597a, `G` replaced by `p_η * G`), package theorem
`StratonovichHAMSecondMoment.TerminalWickRegularization.regFactor_eq_conv`:
`h · law(h V + √η Z) = G_h * p_η`, `V ~ G_1`, `Z ~ N(0, I_d)`.

Wrong variant: without the weight `h`, `G_h * p_η = law(h V + √η Z)` (a probability
measure).  Counterexample: `d = 1`, `h = 2`, `η = 1`: `G_2 * p_1` has mass `2`, the law has
mass `1`.  `factor_without_weight_contrast` computes the mass `2` from the package theorem.
No junk-value reliance (`h = 2 > 0`).

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.TerminalWickRegularization

set_option autoImplicit false

open MeasureTheory StratonovichHAMSecondMoment WaveGreen TerminalWickRegularization

namespace Refutations.TerminalWickRegularization

/-- Auxiliary: the law `law(2V + Z)` (`V ~ G_1`, `Z ~ N(0,1)`) has mass one. -/
theorem law_mass_one :
    ((waveGreen 1 1).prod (stdGaussian 1)).map
        (fun p : HomogHypothesis.Rd 1 × HomogHypothesis.Rd 1 => (2 : ℝ) • p.1 +
          Real.sqrt 1 • p.2) Set.univ = 1 := by
  rw [Measure.map_apply (by fun_prop) MeasurableSet.univ, Set.preimage_univ,
    ← Set.univ_prod_univ, Measure.prod_prod, waveGreen_mass 1 (Or.inl rfl) 1 zero_le_one,
    measure_univ]
  simp

/-- The package value: `G_2 * p_1` has mass `2` in `d = 1`. -/
theorem factor_without_weight_contrast :
    (waveGreen 1 2).conv ((stdGaussian 1).map fun ζ => Real.sqrt 1 • ζ) Set.univ =
      ENNReal.ofReal 2 := by
  rw [← regFactor_eq_conv 1 (Or.inl rfl) two_pos 1, Measure.smul_apply, law_mass_one,
    smul_eq_mul, mul_one]

/-- `G_h * p_η = law(h V + √η Z)` (no weight `h`) is false. -/
theorem factor_without_weight_refuted :
    ¬ (∀ h η : ℝ, 0 < h →
      (waveGreen 1 h).conv ((stdGaussian 1).map fun ζ => Real.sqrt η • ζ) =
        ((waveGreen 1 1).prod (stdGaussian 1)).map
          (fun p : HomogHypothesis.Rd 1 × HomogHypothesis.Rd 1 => h • p.1 +
            Real.sqrt η • p.2)) := by
  intro hyp
  have h1 := congrArg (fun μ : Measure (HomogHypothesis.Rd 1) => μ Set.univ) (hyp 2 1 two_pos)
  rw [factor_without_weight_contrast, law_mass_one] at h1
  have : (2 : ℝ) = 1 := by
    rw [← ENNReal.ofReal_one, ENNReal.ofReal_eq_ofReal_iff (by norm_num) (by norm_num)] at h1
    exact h1
  norm_num at this

end Refutations.TerminalWickRegularization
