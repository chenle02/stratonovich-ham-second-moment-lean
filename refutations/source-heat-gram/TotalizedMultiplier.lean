import StratonovichHAMSecondMoment.SourceHeatGram

/-!
Refutation for `StratonovichHAMSecondMoment.SourceHeatGram.heatMult` (the multiplier of `C_ε`
in `source_spatial_heat_paper`, manuscript label `L:source-spatial-heat`, TeX line 193 of
`integrated_source_convergence.tex` at 39f2597a).

Class (c): control of Lean's totalization outside the manuscript domain.  The TeX's
multiplier `m_ε(ξ) = e^{-ε|ξ|²/2}` is used only for `ε > 0`; `heatMult` is totalized as `1`
for `ε ≤ 0` (so `heatH` is the identity there).  The wrong variant "`heatMult ε = m_ε` for
every `ε`" fails at `ε = -1`, where `m_{-1}(ξ) = e^{1/2} > 1`.  `totalized_multiplier_contrast`
is the identity in the manuscript domain `ε > 0`.

Expected outcome: compiles (refuted).
-/

set_option autoImplicit false

namespace Refutations.SourceHeatGram

open StratonovichHAMSecondMoment
open StratonovichHAMSecondMoment.SourceHeatGram
open LowAlphaConvolution (gaussFactor)

/-- The totalized multiplier is not `e^{-ε|ξ|²/2}` for `ε < 0`. -/
theorem totalized_multiplier_refuted :
    ¬ (∀ (ε : ℝ) (ξ : HomogHypothesis.Rd 1), heatMult ε ξ = gaussFactor ε ξ) := by
  intro h
  have h1 := h (-1) (EuclideanSpace.single 0 1)
  have hn : ‖(EuclideanSpace.single 0 (1 : ℝ) : HomogHypothesis.Rd 1)‖ = 1 := by
    simp [PiLp.norm_single]
  rw [heatMult, gaussFactor, gaussFactor, hn, max_eq_right (by norm_num)] at h1
  have h2 : Real.exp (-(-1 * 1 ^ 2 / 2)) = Real.exp (1 / 2) := by norm_num
  rw [h2] at h1
  have h3 : (1 : ℝ) < Real.exp (1 / 2) := Real.one_lt_exp_iff.2 (by norm_num)
  simp at h1
  linarith

/-- Contrast: for `ε > 0` the multiplier is `e^{-ε|ξ|²/2}`. -/
theorem totalized_multiplier_contrast (ε : ℝ) (hε : 0 < ε) (ξ : HomogHypothesis.Rd 1) :
    heatMult ε ξ = gaussFactor ε ξ :=
  heatMult_of_pos hε ξ

end Refutations.SourceHeatGram
