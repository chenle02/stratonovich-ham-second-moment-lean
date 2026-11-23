import StratonovichHAMSecondMoment.SourceHeatGram

/-!
Refutation for the strong (not uniform) convergence `C_ε → I` of
`StratonovichHAMSecondMoment.SourceHeatGram.source_spatial_heat_paper` (item 5; manuscript
label `L:source-spatial-heat`, TeX line 181 of `integrated_source_convergence.tex` at
edf7085f, "C_ε → I strongly").

Class (b): Lean-route-only control.  The Lean route proves strong convergence from the
pointwise limit `1 - m_ε(ξ) → 0` (dominated convergence).  The wrong variant "uniformly in
`ξ`, `1 - m_ε(ξ) ≤ 1/2` for all `ε > 0`" fails at `ε = 1`, `|ξ| = 2`
(`1 - e^{-2} > 1/2`); this is the multiplier-level reason the convergence is strong and not
in operator norm when `μ` charges large frequencies (the operator-norm statement itself is not
formalized).  `uniform_convergence_contrast` is the pointwise limit used by the route.

Expected outcome: compiles (refuted).
-/

set_option autoImplicit false

open Filter Topology Set

namespace Refutations.SourceHeatGram

open StratonovichHAMSecondMoment
open StratonovichHAMSecondMoment.SourceHeatGram
open LowAlphaConvolution (gaussFactor)

/-- `1 - m_ε` is not uniformly small. -/
theorem uniform_convergence_refuted :
    ¬ (∀ ε : ℝ, 0 < ε → ∀ ξ : HomogHypothesis.Rd 1, 1 - heatMult ε ξ ≤ 1 / 2) := by
  intro h
  have h1 := h 1 one_pos (EuclideanSpace.single 0 2)
  have hn : ‖(EuclideanSpace.single 0 (2 : ℝ) : HomogHypothesis.Rd 1)‖ = 2 := by
    simp [PiLp.norm_single]
  rw [heatMult_of_pos one_pos, gaussFactor, hn] at h1
  have h2 : Real.exp (-(1 * 2 ^ 2 / 2)) = (Real.exp 2)⁻¹ := by
    rw [← Real.exp_neg]; norm_num
  rw [h2] at h1
  have h3 : (2 : ℝ) + 1 < Real.exp 2 := Real.add_one_lt_exp (by norm_num)
  have h4 : (Real.exp 2)⁻¹ < 1 / 2 := by
    rw [inv_lt_comm₀ (Real.exp_pos 2) (by norm_num)]; linarith
  linarith

/-- Contrast: for each fixed `ξ`, `1 - m_ε(ξ) → 0` as `ε → 0+`. -/
theorem uniform_convergence_contrast (ξ : HomogHypothesis.Rd 1) :
    Tendsto (fun ε => 1 - heatMult ε ξ) (𝓝[>] 0) (𝓝 0) := by
  have hc : Continuous fun ε : ℝ => heatMult ε ξ := by
    unfold heatMult gaussFactor; fun_prop
  have h0 : heatMult 0 ξ = 1 := by simp [heatMult, gaussFactor]
  have := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  rw [h0] at this
  simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub this

end Refutations.SourceHeatGram
