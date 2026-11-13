/-
Refutation for the hypothesis range of `L:spatial-fourier-bound` with the
constant `R_α` (package theorem
`StratonovichHAMSecondMoment.SpectralMassIdentity.spatial_fourier_bound_ralpha_paper`;
`notes/integrated_spatial_occupation.tex` lines 101-111 at a284420, `R_α` of
`E:intro-spectral-mass`, main TeX lines 526-532).

Wrong variant: the `R_α` form `A_sp(g) ≤ 2^{1+α} R_α b(g)^{α/2}` under the
hypotheses of the general theorem `SpatialFourierBound.spatial_fourier_bound`
(spectral convention, `α`-homogeneous `μ`, `α < 2`), i.e. without `α > 0`.
Witness: `d = 1`, `Γ` = Lebesgue measure, `μ = δ_0`, `α = 0`: `A_sp(g) = 1`
for every real unit test `g`, while `R_0 = 0`.  So the `R_α` form needs
`α > 0`, which `H:homog` supplies; the `R_Γ(1)` form holds at the witness
(`fourier_bound_alpha_zero_contrast`: `1 ≤ 2^{1+0}·1·b^0`).
Junk-value reliance: this is a control of Lean's totalized division outside
the manuscript's domain, not a convention-independent counterexample.  At
`α = 0` (outside `H:homog`, which has `α > 0`) `R_0 = 0·π·1/(2 sin 0)` is `0/0`,
undefined as an ordinary quotient; Lean's convention `x/0 = 0` makes it `0`.
With the continuous extension of `α π/(2 sin(π α/2))` at `α = 0`, which is `1`,
`R_0 = 1` and the `R_α` form holds at the witness (`1 ≤ 2`).

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.SpectralMassIdentity
import StratonovichHAMSecondMoment.SpatialSmoothRatio

set_option autoImplicit false

open MeasureTheory StratonovichHAMSecondMoment HomogHypothesis SpatialFourierBound

namespace Refutations.SpectralMassIdentity.FourierBoundAlphaZero

/-- Lebesgue measure on `ℝ¹` has spectral measure `δ_0`. -/
theorem leb_spectral : IsSpectralMeasure (volume : Measure (Rd 1)) (Measure.dirac 0) := by
  intro φ
  rw [integral_dirac]
  simp

theorem dirac_homog : SpectralHomog.SpectralHomogeneous (Measure.dirac (0 : Rd 1)) 0 := by
  intro A _ c hc
  rw [Real.rpow_zero, ENNReal.ofReal_one, one_mul, Measure.dirac_apply, Measure.dirac_apply]
  by_cases h0 : (0 : Rd 1) ∈ A
  · rw [Set.indicator_of_mem h0, Set.indicator_of_mem ((Set.zero_mem_smul_set_iff hc.ne').2 h0)]
  · rw [Set.indicator_of_notMem h0,
      Set.indicator_of_notMem (fun h => h0 ((Set.zero_mem_smul_set_iff hc.ne').1 h))]

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

/-- The `R_α` form of the Fourier bound without `α > 0` is false. -/
theorem fourier_bound_alpha_zero_refuted :
    ¬ (∀ (Γ μ : Measure (Rd 1)) [IsLocallyFiniteMeasure Γ] [IsLocallyFiniteMeasure μ],
        IsSpectralMeasure Γ μ → ∀ alpha : ℝ, SpectralHomog.SpectralHomogeneous μ alpha →
        alpha < 2 → ∀ g : Rd 1 → ℝ, IsUnitTest g →
        spatialEnergy Γ g ≤
          2 ^ (1 + alpha) * SpectralMassIdentity.ralpha μ alpha * gradEnergy g ^ (alpha / 2)) := by
  intro h
  obtain ⟨g, hg⟩ := SpatialSmoothRatio.exists_unitTest 1
  have h1 := h volume (Measure.dirac 0) leb_spectral 0 dirac_homog (by norm_num) g hg
  rw [energy_leb hg] at h1
  norm_num [SpectralMassIdentity.ralpha] at h1

/-- The general (`R_Γ(1)`) form at the same point: `A_sp(g) ≤ 2^{1+0}·R_Γ(1)·b^0`. -/
theorem fourier_bound_alpha_zero_contrast {g : Rd 1 → ℝ} (hg : IsUnitTest g) :
    spatialEnergy volume g ≤ 2 ^ (1 + (0 : ℝ)) *
      SpectralHomog.resolvent (Measure.dirac (0 : Rd 1)) 1 * gradEnergy g ^ ((0 : ℝ) / 2) :=
  (spatial_fourier_bound leb_spectral dirac_homog (by norm_num) hg
    (gradEnergy_pos one_pos hg)).2.2.2.2.2

end Refutations.SpectralMassIdentity.FourierBoundAlphaZero
