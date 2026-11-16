import StratonovichHAMSecondMoment.SourceHeatGram
import StratonovichHAMSecondMoment.WhiteModel

/-!
Operator-level refutation for the contraction conclusion of
`StratonovichHAMSecondMoment.SourceHeatGram.source_spatial_heat_paper` (item 4; manuscript
label `L:source-spatial-heat`, `integrated_source_convergence.tex` lines 180-181 at 39f2597a,
"heat is a positive self-adjoint contraction on `H_Γ`").

Class (a): manuscript-claim perturbation in the manuscript domain.  The TeX claims
`‖C_ε‖ ≤ 1`.  The strengthened claim "there is `c < 1` with `‖C_ε‖ ≤ c` for every `ε > 0`"
is false for an admissible covariance: the spatial white noise `Γ = δ₀`,
`μ = (2π)^{-1} Leb` on `ℝ¹`, which satisfies `H:homog` with `d = α = 1`, `α₀ = 1/2`
(`WhiteModel.white_homogCovariance`), and `Γ ≠ 0`.  The proof is operator-level: by the
strong convergence `C_ε → I` (`tendsto_heatH`), a uniform bound `c < 1` would force every
vector of `H_Γ` to vanish, while the test `χ = cut 0` (smooth, compact support, `χ(0) = 1`)
has `‖ι χ‖² = B_Γ(χ, χ) = ∫ χ² > 0`.  The general form `no_uniform_strict_contraction`
holds under `H:homog` for any `Γ` with a test of nonzero energy.
`heat_not_strict_contraction_contrast`: the TeX's bound `‖C_ε‖ ≤ 1` holds for the same model.

Expected outcome: compiles (refuted).
-/

set_option autoImplicit false

open Filter Topology Set MeasureTheory

namespace Refutations.SourceHeatGram

open StratonovichHAMSecondMoment
open StratonovichHAMSecondMoment.SourceHeatGram
open StratonovichHAMSecondMoment.WhiteModel (whiteCov whiteSpectral white_homogCovariance
  spatialPair_whiteCov)

/-- Under `H:homog`, if some test `f` has `B_Γ(f, f) ≠ 0`, no constant `c < 1` bounds every
`‖C_ε‖`, `ε > 0` (strong convergence `C_ε → I`). -/
theorem no_uniform_strict_contraction {d : ℕ} {alpha alpha0 : ℝ}
    {Γ μ : MeasureTheory.Measure (HomogHypothesis.Rd d)}
    (hH : HomogHypothesis.HomogCovariance d alpha alpha0 Γ μ) {f : HomogHypothesis.Rd d → ℝ}
    (hf : WeakSobolev.IsTestFunction f) (hf0 : SpatialFourierBound.spatialPair Γ f f ≠ 0) :
    ¬ ∃ c : ℝ, c < 1 ∧ ∀ ε : ℝ, 0 < ε → ‖heatH Γ μ ε‖ ≤ c := by
  rintro ⟨c, hc, hb⟩
  set x : HGamma μ := ⟨vec μ f, vec_mem_HGamma μ hf⟩
  have hx : 0 < ‖x‖ := by
    have h2 : ‖x‖ ^ 2 = SpatialFourierBound.spatialPair Γ f f :=
      norm_vec_sq hH.μ_tempered hH.spectral hf
    rcases (norm_nonneg x).lt_or_eq with h | h
    · exact h
    · exact absurd (by rw [← h2, ← h]; ring) hf0
  have ht : Tendsto (fun ε => ‖heatH Γ μ ε x‖) (𝓝[>] 0) (𝓝 ‖x‖) :=
    (tendsto_heatH hH.Γ_tempered hH.μ_tempered hH.spectral x).norm
  have hle : ‖x‖ ≤ c * ‖x‖ := by
    refine le_of_tendsto ht ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_right (hb ε hε) (norm_nonneg _))
  nlinarith

/-- Auxiliary: the white-noise model with unit intensity and `α₀ = 1/2` satisfies `H:homog`. -/
theorem white_homog :
    HomogHypothesis.HomogCovariance 1 1 (1 / 2) (whiteCov 1) (whiteSpectral 1) :=
  white_homogCovariance zero_le_one (by norm_num) (by norm_num)

/-- Auxiliary: the cutoff `χ = cut 0` has positive white-noise energy `∫ χ² > 0`. -/
theorem white_cut_energy_pos :
    0 < SpatialFourierBound.spatialPair (whiteCov 1) (cut (d := 1) 0) (cut 0) := by
  rw [spatialPair_whiteCov zero_le_one, one_mul]
  have hc : Continuous (cut (d := 1) 0) := (cut_contDiff 0).continuous
  refine Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := 0) (hc.mul hc)
    ((cut_hasCompactSupport 0).mul_left) (fun y => mul_self_nonneg _) ?_
  rw [cut_eq_one (by simp)]
  norm_num

/-- **Refuted (class (a))**: for the admissible white-noise covariance, there is no uniform
strict contraction bound `‖C_ε‖ ≤ c < 1` over `ε > 0`. -/
theorem heat_not_strict_contraction_refuted :
    ¬ ∃ c : ℝ, c < 1 ∧ ∀ ε : ℝ, 0 < ε →
      ‖heatH (whiteCov 1) (whiteSpectral 1) ε‖ ≤ c :=
  no_uniform_strict_contraction white_homog ⟨cut_contDiff 0, cut_hasCompactSupport 0⟩
    white_cut_energy_pos.ne'

/-- Contrast: the TeX's contraction bound `‖C_ε‖ ≤ 1` holds for the same model, and the
model has `Γ ≠ 0`. -/
theorem heat_not_strict_contraction_contrast :
    whiteCov 1 ≠ 0 ∧ ∀ ε : ℝ, 0 < ε → ‖heatH (whiteCov 1) (whiteSpectral 1) ε‖ ≤ 1 := by
  have hΓ0 : whiteCov 1 ≠ 0 := by
    intro h
    have := white_cut_energy_pos
    rw [h, SpatialFourierBound.spatialPair] at this
    simp at this
  exact ⟨hΓ0, fun ε hε =>
    ((source_spatial_heat_paper white_homog hΓ0).2.2.2.2.1 ε hε).2.2.1⟩

end Refutations.SourceHeatGram
