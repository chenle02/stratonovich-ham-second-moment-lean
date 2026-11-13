/-
Refutation for the deterministic Fourier bound, package theorem
`StratonovichHAMSecondMoment.SpatialFourierBound.spatial_fourier_bound`
(`A_sp(g) ≤ 2^{1+α} R_Γ(1) b(g)^{α/2}`, the general form of
`E:spatial-fourier-bound` in `L:spatial-fourier-bound`, which the manuscript
uses for "`R_0` finite" of `P:spatial-smooth-ratio`;
`notes/integrated_spatial_occupation.tex` lines 101-111 and 185-188 at
a284420).

Wrong variant: the constant `2^{α-1}` instead of `2^{1+α}`, i.e. under the
hypotheses of the general theorem `A_sp(g) ≤ 2^{α-1} R_Γ(1) b(g)^{α/2}`.
Counterexample: `d = 1`, `Γ` = Lebesgue measure, `μ = δ_0`, `α = 0` (outside
the range of `H:homog`, but inside the hypotheses of the general theorem):
the spectral convention holds, `μ` is `0`-homogeneous, `R_Γ(1) = 1`, and for
every real unit test `g`, `A_sp(g) = (∫ g²)² = 1` while the variant's right
side is `1/2`.  `constant_factor_contrast` applies the package theorem at the
same point: `1 ≤ 2`.
No junk-value reliance (`A_sp(g)` is computed as a genuine integral).

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.SpatialFourierBound
import StratonovichHAMSecondMoment.SpatialSmoothRatio

set_option autoImplicit false

open MeasureTheory StratonovichHAMSecondMoment HomogHypothesis SpatialFourierBound

namespace Refutations.SpatialFourierBound

/-- Lebesgue measure on `ℝ¹` has spectral measure `δ_0`. -/
theorem leb_spectral' : IsSpectralMeasure (volume : Measure (Rd 1)) (Measure.dirac 0) := by
  intro φ
  rw [integral_dirac]
  simp

/-- `δ_0` is homogeneous of degree `0`. -/
theorem dirac_homog : SpectralHomog.SpectralHomogeneous (Measure.dirac (0 : Rd 1)) 0 := by
  intro A _ c hc
  rw [Real.rpow_zero, ENNReal.ofReal_one, one_mul, Measure.dirac_apply, Measure.dirac_apply]
  by_cases h0 : (0 : Rd 1) ∈ A
  · rw [Set.indicator_of_mem h0, Set.indicator_of_mem ((Set.zero_mem_smul_set_iff hc.ne').2 h0)]
  · rw [Set.indicator_of_notMem h0,
      Set.indicator_of_notMem (fun h => h0 ((Set.zero_mem_smul_set_iff hc.ne').1 h))]

/-- `R_{δ_0}(1) = 1`. -/
theorem resolvent_dirac : SpectralHomog.resolvent (Measure.dirac (0 : Rd 1)) 1 = 1 := by
  simp [SpectralHomog.resolvent]

/-- `A_sp(g) = 1` for Lebesgue `Γ` and every real unit test `g` on `ℝ¹`. -/
theorem energy_leb {g : Rd 1 → ℝ} (hg : IsUnitTest g) : spatialEnergy volume g = 1 := by
  have hQc : Continuous (fun x => g x ^ 2) := hg.1.continuous.pow 2
  have hQs : HasCompactSupport (fun x => g x ^ 2) :=
    hg.2.1.comp_left (g := fun r : ℝ => r ^ 2) (by norm_num)
  have h := (SpatialSmoothRatio.integral_conv_mul volume hQc hQs hQc hQs).2
  have hconv : ∀ x, VariationalDilation.conv volume (fun x => g x ^ 2) x = 1 := by
    intro x
    rw [VariationalDilation.conv, integral_sub_left_eq_self (fun y => g y ^ 2) volume x]
    exact hg.2.2
  simp_rw [hconv, one_mul] at h
  rw [spatialEnergy, ← h, hg.2.2]

/-- The constant `2^{α-1}` in the Fourier bound is false. -/
theorem constant_factor_refuted :
    ¬ (∀ (Γ μ : Measure (Rd 1)) [IsLocallyFiniteMeasure Γ] [IsLocallyFiniteMeasure μ],
        IsSpectralMeasure Γ μ → ∀ alpha : ℝ, SpectralHomog.SpectralHomogeneous μ alpha →
        alpha < 2 → ∀ g : Rd 1 → ℝ, IsUnitTest g → 0 < gradEnergy g →
        spatialEnergy Γ g ≤
          2 ^ (alpha - 1) * SpectralHomog.resolvent μ 1 * gradEnergy g ^ (alpha / 2)) := by
  intro h
  obtain ⟨g, hg⟩ := SpatialSmoothRatio.exists_unitTest 1
  have h1 := h volume (Measure.dirac 0) leb_spectral' 0 dirac_homog (by norm_num) g hg
    (gradEnergy_pos one_pos hg)
  rw [energy_leb hg, resolvent_dirac, zero_div, Real.rpow_zero, zero_sub,
    Real.rpow_neg_one] at h1
  norm_num at h1

/-- The package theorem at the same point: `A_sp(g) = 1 ≤ 2^{1+0} · 1 · b^0`. -/
theorem constant_factor_contrast {g : Rd 1 → ℝ} (hg : IsUnitTest g) :
    spatialEnergy volume g ≤ 2 ^ (1 + (0 : ℝ)) *
      SpectralHomog.resolvent (Measure.dirac (0 : Rd 1)) 1 * gradEnergy g ^ ((0 : ℝ) / 2) :=
  (spatial_fourier_bound leb_spectral' dirac_homog (by norm_num) hg
    (gradEnergy_pos one_pos hg)).2.2.2.2.2

end Refutations.SpatialFourierBound
