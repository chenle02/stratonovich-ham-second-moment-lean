import StratonovichHAMSecondMoment.SourceHeatGram

/-!
Refutation for the normalization of `E:source-heat-definition`
(`integrated_source_convergence.tex` lines 176-179 at 39f2597a), on which the contraction
conclusions of `StratonovichHAMSecondMoment.SourceHeatGram.source_spatial_heat_paper`
(item 4) rest.

Class (b): Lean-route-only control at the multiplier level.  The transform of the
unnormalized kernel `e^{-|x|²/(2ε)}` is `(2πε)^{d/2} m_ε(ξ)` (`heatDens_fourier` with the
factor `(2πε)^{d/2}`); without the TeX's `(2πε)^{-d/2}` the multiplier exceeds one at `ξ = 0`
(here `d = 1`, `ε = 1`: `(2π)^{1/2} > 1`), so the contraction bound of the route
(`norm_heatLin_le`, from `m_ε ≤ 1`) is unavailable.  `unnormalized_kernel_contrast` is the
bound `m_ε ≤ 1` for the normalized density, through `heatDens_fourier`.

Expected outcome: compiles (refuted).
-/

set_option autoImplicit false

namespace Refutations.SourceHeatGram

open StratonovichHAMSecondMoment
open StratonovichHAMSecondMoment.SourceHeatGram
open LowAlphaConvolution (gaussFactor)

/-- The multiplier of the unnormalized heat kernel is not bounded by one. -/
theorem unnormalized_kernel_refuted :
    ¬ (∀ ε : ℝ, 0 < ε → ∀ ξ : HomogHypothesis.Rd 1,
        (2 * Real.pi * ε) ^ ((1 : ℝ) / 2) * gaussFactor ε ξ ≤ 1) := by
  intro h
  have h1 := h 1 one_pos 0
  simp only [gaussFactor, norm_zero, mul_one] at h1
  norm_num at h1
  have h2 : (1 : ℝ) < (2 * Real.pi) ^ ((1 : ℝ) / 2) :=
    Real.one_lt_rpow (by linarith [Real.pi_gt_three]) (by norm_num)
  linarith

/-- Contrast: the transform of the normalized density `p_ε` is `m_ε ≤ 1`. -/
theorem unnormalized_kernel_contrast (ε : ℝ) (hε : 0 < ε) (ξ : HomogHypothesis.Rd 1) :
    (∫ z, (LowAlphaConvolution.heatDens ε z : ℂ) * SpatialFourierBound.ex ξ z) =
        (gaussFactor ε ξ : ℂ) ∧ gaussFactor ε ξ ≤ 1 :=
  ⟨(heatDens_fourier hε ξ).2, LowAlphaConvolution.gaussFactor_le_one hε.le ξ⟩

end Refutations.SourceHeatGram
