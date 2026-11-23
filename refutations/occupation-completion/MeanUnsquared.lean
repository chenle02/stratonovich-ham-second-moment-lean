/-
Refutation for the second identity of `E:occupation-raw-identities`, package theorems
`StratonovichHAMSecondMoment.OccupationCompletion.inner_incl_rho_mean` and
`occupation_raw_square_paper` (`⟨Ψ, ρ_g⟩_{H_I} = ∫_I ∫ h_{Ψ,s}(x) g_s(x)² dx ds` for
`Ψ ∈ C_pos`, `g ∈ 𝒪`; `L:occupation-raw-square`, `integrated_occupation_ceiling.tex` lines
34-38 and 96-105 at edf7085f).

Wrong variant (class (a), manuscript-claim perturbation in the manuscript domain): the
occupation density `g_s` in place of `g_s²` (`⟨Ψ, ρ_g⟩ = ∫_I ∫ h_{Ψ,s} g_s`).  Counterexample:
under any `H:homog` with `Γ ≠ 0`, a real unit test function `g`, the control
`Ψ_g(s,x) = θ(s) g(x)²` (in `C_pos`) and the two constant fields `g_s = g` and `g_s = -g` (both
in `𝒪`).  The package identity gives the same value `Y = ∫_I ∫ h_{Ψ_g,s} g² > 0`
(`mean_witness`) for both fields, while the wrong variant gives `Z` and `-Z` with
`Z = ∫_I ∫ h_{Ψ_g,s} g`, so `Y = Z = -Y`, impossible.  No junk-value reliance.
`mean_unsquared_contrast` is the package identity (with `g_s²`).

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.OccupationCompletion

set_option autoImplicit false

open MeasureTheory Set
open scoped RealInnerProductSpace ContDiff
open StratonovichHAMSecondMoment OccupationCompletion

namespace Refutations.OccupationCompletion

open HomogHypothesis (Rd HomogCovariance)
open OccupationPhysicalClass (volI IsOccField)
open VariationalDilation (CPos mean rawCost)

variable {d : ℕ}

/-- The constant-in-time field `g_s = g` of a real unit test function `g` lies in `𝒪` (joint
representatives), with weak gradient field `∇g`. -/
theorem const_isOcc {g : Rd d → ℝ} (hg : SpatialFourierBound.IsUnitTest g) :
    IsOccField (fun _ => g) (fun _ => VariationalFloor.grad g) := by
  have hgt : WeakSobolev.IsTestFunction g := ⟨hg.1, hg.2.1⟩
  have hu := SpatialStaticControls.isUnitH1_of_unitTest hg
  refine ⟨(hg.1.continuous.comp continuous_snd).aestronglyMeasurable,
    ((VariationalFloor.continuous_grad hgt).comp continuous_snd).aestronglyMeasurable,
    Filter.Eventually.of_forall fun _ => hu, ?_⟩
  have hTl : OccupationPhysicalClass.Tlin (fun _ : ℝ => VariationalFloor.grad g) =
      OccupationPhysicalClass.gradSqE (VariationalFloor.grad g) := by
    unfold OccupationPhysicalClass.Tlin
    simp only [lintegral_const, OccupationPhysicalClass.volI_univ, mul_one]
  rw [hTl, (OccupationPhysicalClass.gradSqE_eq hu.2.1).2]
  exact ENNReal.ofReal_lt_top

/-- The control `Ψ_g(s,x) = θ(s) g(x)²` with a smooth bump `θ` (`θ(1/2) = 1`, `0 ≤ θ ≤ 1`,
support `[1/4, 3/4]`). -/
noncomputable def ctrl (g : Rd d → ℝ) : ℝ × Rd d → ℝ :=
  fun q => (⟨1 / 8, 1 / 4, by norm_num, by norm_num⟩ : ContDiffBump (1 / 2 : ℝ)) q.1 * g q.2 ^ 2

/-- `Ψ_g ∈ C_pos` for a real unit test function `g`, and `Ψ_g(s,x) ≤ g(x)²`. -/
theorem ctrl_mem {g : Rd d → ℝ} (hg : SpatialFourierBound.IsUnitTest g) :
    ctrl g ∈ CPos d ∧ ∀ q : ℝ × Rd d, ctrl g q ≤ g q.2 ^ 2 := by
  set θ : ContDiffBump (1 / 2 : ℝ) := ⟨1 / 8, 1 / 4, by norm_num, by norm_num⟩ with hθ
  have he : ctrl g = fun q => θ q.1 * g q.2 ^ 2 := rfl
  obtain ⟨x0, hx0⟩ : ∃ x0, g x0 ≠ 0 := by
    by_contra h
    push Not at h
    have := hg.2.2
    simp [h] at this
  have hK : IsCompact (tsupport θ ×ˢ tsupport g) :=
    θ.hasCompactSupport.isCompact.prod hg.2.1.isCompact
  have hzero : ∀ q ∉ tsupport θ ×ˢ tsupport g, ctrl g q = 0 := by
    intro q hq
    rw [he, Set.mem_prod, not_and_or] at *
    rcases hq with h | h
    · simp [image_eq_zero_of_notMem_tsupport h]
    · simp [image_eq_zero_of_notMem_tsupport h]
  have hsupp : tsupport (ctrl g) ⊆ tsupport θ ×ˢ tsupport g :=
    closure_minimal (fun q hq => by_contra fun h => hq (hzero q h)) hK.isClosed
  refine ⟨⟨?_, HasCompactSupport.intro hK hzero, ?_, fun q => ?_, ?_⟩, fun q => ?_⟩
  · rw [he]
    exact (θ.contDiff.comp contDiff_fst).mul ((hg.1.comp contDiff_snd).pow 2)
  · refine hsupp.trans (Set.prod_mono ?_ (subset_univ _))
    rw [θ.tsupport_eq]
    intro t ht
    rw [Metric.mem_closedBall, Real.dist_eq, abs_le] at ht
    constructor <;> linarith [ht.1, ht.2]
  · rw [he]; exact mul_nonneg θ.nonneg (sq_nonneg _)
  · intro h
    have := congrFun h ((1 / 2 : ℝ), x0)
    rw [he] at this
    simp only [Pi.zero_apply] at this
    rw [θ.one_of_mem_closedBall (Metric.mem_closedBall_self (by norm_num)), one_mul] at this
    exact hx0 (pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this)
  · rw [he]
    simp only
    calc θ q.1 * g q.2 ^ 2 ≤ 1 * g q.2 ^ 2 :=
          mul_le_mul_of_nonneg_right θ.le_one (sq_nonneg _)
      _ = _ := one_mul _

/-- **Positivity witness in the manuscript domain.**  Under `H:homog` with `Γ ≠ 0`, for a real
unit test function `g`, the control `Ψ_g` and the constant field `g_s = g` give
`∫_I ∫ h_{Ψ_g,s} g² > 0`: it is at least `v_{Ψ_g} > 0` (`VariationalRate.rawCost_pos`) because
`Ψ_g ≤ g²` and `h ≥ 0`, with the integrability from `occupation_raw_square_paper`. -/
theorem mean_witness {alpha alpha0 : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogCovariance d alpha alpha0 Γ μ) (hΓ : Γ ≠ 0) {g : Rd d → ℝ}
    (hg : SpatialFourierBound.IsUnitTest g) :
    0 < ∫ s in Ioo (0 : ℝ) 1, ∫ x, mean alpha0 Γ (ctrl g) s x * g x ^ 2 := by
  have := hH.Γ_radon
  obtain ⟨hΨ, hle⟩ := ctrl_mem hg
  obtain ⟨-, -, -, -, h5⟩ := occupation_raw_square_paper hH hΓ
  obtain ⟨-, -, h53⟩ := h5 _ _ (const_isOcc hg)
  obtain ⟨-, -, hint, hIon, -⟩ := h53 (ctrl g) hΨ
  have hv : 0 < rawCost alpha0 Γ (ctrl g) :=
    VariationalRate.rawCost_pos hH.Γ_tempered hH.μ_tempered hH.spectral
      (VariationalDilation.setScaling_of_homog hH) hΓ (TParams.ofHomog hH).ha0.le
      (TParams.ofHomog hH).ha1 hΨ
  refine hv.trans_le ?_
  unfold rawCost
  refine integral_mono_of_nonneg ?_ hIon ?_
  · exact Filter.Eventually.of_forall fun σ => integral_nonneg fun x =>
      mul_nonneg (hΨ.2.2.2.1 _) (VariationalMean.mean_nonneg hΨ _ _ _)
  · filter_upwards [hint] with s hs
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun x =>
      mul_nonneg (hΨ.2.2.2.1 _) (VariationalMean.mean_nonneg hΨ _ _ _)) hs
      (Filter.Eventually.of_forall fun x => ?_)
    show ctrl g (s, x) * mean alpha0 Γ (ctrl g) s x ≤ mean alpha0 Γ (ctrl g) s x * g x ^ 2
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_left (hle (s, x)) (VariationalMean.mean_nonneg hΨ _ _ _)

/-- The negative of a real unit test function is a real unit test function. -/
theorem isUnitTest_neg {g : Rd d → ℝ} (hg : SpatialFourierBound.IsUnitTest g) :
    SpatialFourierBound.IsUnitTest fun x => -g x := by
  refine ⟨hg.1.neg, hg.2.1.neg, ?_⟩
  simpa only [neg_sq] using hg.2.2

/-- The second identity of `E:occupation-raw-identities` fails with `g_s` in place of `g_s²`. -/
theorem mean_unsquared_refuted {alpha alpha0 : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogCovariance d alpha alpha0 Γ μ) (hΓ : Γ ≠ 0) :
    ¬ ∀ Ψ ∈ CPos d, ∀ (G : ℝ → Rd d → ℝ) (DG : ℝ → Rd d → Rd d), IsOccField G DG →
      ⟪incl (TParams.ofHomog hH) (SpData.ofHomog hH) Ψ,
        rho (TParams.ofHomog hH) (SpData.ofHomog hH) G⟫ =
        ∫ s in Ioo (0 : ℝ) 1, ∫ x, mean alpha0 Γ Ψ s x * G s x := by
  intro h
  obtain ⟨g, hg⟩ := SpatialSmoothRatio.exists_unitTest d
  have hY := mean_witness hH hΓ hg
  have hΨ := (ctrl_mem hg).1
  have hO := const_isOcc hg
  have hO' := const_isOcc (isUnitTest_neg hg)
  obtain ⟨-, -, -, -, h5⟩ := occupation_raw_square_paper hH hΓ
  have e1 := ((h5 _ _ hO).2.2 _ hΨ).2.2.2.2
  have e2 := ((h5 _ _ hO').2.2 _ hΨ).2.2.2.2
  have w1 := h _ hΨ _ _ hO
  have w2 := h _ hΨ _ _ hO'
  simp only [neg_sq] at e2
  have hneg : (∫ s in Ioo (0 : ℝ) 1, ∫ x, mean alpha0 Γ (ctrl g) s x * -g x) =
      -∫ s in Ioo (0 : ℝ) 1, ∫ x, mean alpha0 Γ (ctrl g) s x * g x := by
    rw [← integral_neg]
    refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
    simp only [mul_neg, integral_neg]
  rw [e1] at w1
  rw [e2, hneg, ← w1] at w2
  linarith

/-- Contrast: the package identity, with the squared occupation `g_s²`. -/
theorem mean_unsquared_contrast {alpha alpha0 : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogCovariance d alpha alpha0 Γ μ) (hΓ : Γ ≠ 0) :
    ∀ Ψ ∈ CPos d, ∀ (G : ℝ → Rd d → ℝ) (DG : ℝ → Rd d → Rd d), IsOccField G DG →
      ⟪incl (TParams.ofHomog hH) (SpData.ofHomog hH) Ψ,
        rho (TParams.ofHomog hH) (SpData.ofHomog hH) G⟫ =
        ∫ s in Ioo (0 : ℝ) 1, ∫ x, mean alpha0 Γ Ψ s x * G s x ^ 2 := by
  intro Ψ hΨ G DG hO
  obtain ⟨-, -, -, -, h5⟩ := occupation_raw_square_paper hH hΓ
  exact ((h5 G DG hO).2.2 Ψ hΨ).2.2.2.2

end Refutations.OccupationCompletion
