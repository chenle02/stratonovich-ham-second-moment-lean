/-
Refutation for the layer-cake identity of `E:low-alpha-radial` (main TeX
lines 4706-4708 at a284420), package theorem
`StratonovichHAMSecondMoment.LowAlphaConvolution.integral_lowKernel`.

Wrong variant: writing `min{h, |ξ|^{-1}}` naively as `min h ‖ξ‖⁻¹`, which by
Lean's junk value `0⁻¹ = 0` is `0` at `ξ = 0` instead of the manuscript's `h`.
The variant identity `∫ min(h, ‖ξ‖⁻¹) μ(dξ) = V h^{1-α}/(1-α)` fails for the
Dirac mass `μ = δ₀` on `ℝ¹`, which satisfies `μ(cA) = c^0 μ(A)` (`α = 0 < 1`),
has `V = 1`, and is locally finite: at `h = 1` the variant's left side is `0`,
the right side `1`.  This is exactly why `lowKernel` sets the value `h` at `0`.
`junk_kernel_contrast` is the package identity for `δ₀`: `∫ lowKernel 1 dδ₀ = 1`.
Junk-value reliance: the refuted variant uses `0⁻¹ = 0` (that is the point).

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.LowAlphaConvolution

set_option autoImplicit false

open MeasureTheory Metric
open scoped Pointwise

namespace Refutations.LowAlphaConvolution

open StratonovichHAMSecondMoment StratonovichHAMSecondMoment.LowAlphaConvolution

/-- `δ₀` on `ℝ¹` is `0`-homogeneous. -/
theorem dirac_homogeneous :
    SpectralHomog.SpectralHomogeneous (Measure.dirac (0 : HomogHypothesis.Rd 1)) 0 := by
  intro A hA c hc
  rw [Real.rpow_zero, ENNReal.ofReal_one, one_mul,
    Measure.dirac_apply' _ (hA.const_smul₀ c), Measure.dirac_apply' _ hA]
  have hiff : (0 : HomogHypothesis.Rd 1) ∈ c • A ↔ (0 : HomogHypothesis.Rd 1) ∈ A := by
    constructor <;> intro hx
    · obtain ⟨a, ha, hax⟩ := hx
      have : a = 0 := by
        rcases (smul_eq_zero.1 hax) with h | h
        · exact absurd h hc.ne'
        · exact h
      simpa [this] using ha
    · exact ⟨0, hx, smul_zero c⟩
  by_cases h0 : (0 : HomogHypothesis.Rd 1) ∈ A
  · rw [Set.indicator_of_mem h0, Set.indicator_of_mem (hiff.2 h0)]
  · rw [Set.indicator_of_notMem h0, Set.indicator_of_notMem (fun h => h0 (hiff.1 h))]

/-- `V(δ₀) = 1`. -/
theorem specV_dirac : specV (Measure.dirac (0 : HomogHypothesis.Rd 1)) = 1 := by
  rw [specV, Measure.dirac_apply_of_mem (mem_closedBall_self zero_le_one)]

/-- The junk-valued kernel `min h ‖ξ‖⁻¹` does not satisfy the layer-cake identity. -/
theorem junk_kernel_refuted :
    ¬ (∫ ξ, min (1 : ℝ) ‖ξ‖⁻¹ ∂(Measure.dirac (0 : HomogHypothesis.Rd 1)) =
        (specV (Measure.dirac (0 : HomogHypothesis.Rd 1))).toReal / (1 - 0) *
          (1 : ℝ) ^ (1 - (0 : ℝ))) := by
  rw [integral_dirac, specV_dirac]
  norm_num

/-- The package identity for `δ₀`, `h = 1`: `∫ lowKernel 1 dδ₀ = 1`. -/
theorem junk_kernel_contrast :
    ∫ ξ, lowKernel 1 ξ ∂(Measure.dirac (0 : HomogHypothesis.Rd 1)) = 1 := by
  rw [(integral_lowKernel dirac_homogeneous (by norm_num) one_pos).2.2, specV_dirac]
  norm_num

end Refutations.LowAlphaConvolution
