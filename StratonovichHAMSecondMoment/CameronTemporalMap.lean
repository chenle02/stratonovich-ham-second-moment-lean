module

/-
Copyright 2026 Le Chen. SPDX-License-Identifier: Apache-2.0

Wave L16, item L16-C (part 4): `P:cameron-temporal-map` (`integrated_cameron_mean.tex` lines
225-237, proof 239-314, at revision edf7085f (book 1.1.3)).

* The isometry `ι : H_t ≅ L²(I)` with `ι [f] = K^{1/2} f` (Step 2, lines 268-275): `‖K^{1/2} f‖₂² =
  ⟪K f, f⟫ = ‖J f‖²_{H_t}`, extended from the dense range of `J` (`LinearMap.extendOfIsometry`);
  onto because `K^{1/2}` has dense range (`ker K = 0`) and the range of an isometry from a
  complete space is closed.
* The `L^r` bound of `K^{1/2}` (Step 3, lines 277-293): `‖K^{1/2} g‖_r ≤ ‖K_a‖_{r/2}^{1/2} ‖g‖₂`, by
  `L^r` duality against bounded test functions (`eLpNorm_le_of_dual`, proved here by
  truncating `|F|^{r-1} sgn F`) and the covariance Cauchy-Schwarz
  `⟪K^{1/2} g, h⟫ = ⟪g, K^{1/2} h⟫ ≤ ‖g‖ ⟪K h, h⟫^{1/2} ≤ ‖g‖ ‖K_a‖^{1/2}_{r/2} ‖h‖_{r'}` (`kform_abs`).
  Hence `C_t = K^{1/2} ι : H_t → L^r(I)` (`coreOf`), and `exists_temporalMeanCore`.
* `TemporalMeanCore.Ct_test`: on tests `C_t [f] = K f` (line 273).
-/
public import Mathlib
public import StratonovichHAMSecondMoment.CameronInterface
public import StratonovichHAMSecondMoment.CameronTemporalYoung
public import StratonovichHAMSecondMoment.CameronTemporalKernel
public import StratonovichHAMSecondMoment.CameronTemporalSqrt

@[expose] public section

noncomputable section

set_option autoImplicit false

open MeasureTheory Set Filter Topology
open scoped ENNReal RealInnerProductSpace

namespace StratonovichHAMSecondMoment.CameronTemporal

open SpaceTimePositivity (timeMeasure)
open TimeSchur (kern kern_nonneg measurable_kern)
open OccupationCompletion (TParams Ht J Jlin inner_Jlin kform kform_congr kform_integrable)
open UniformMeanInterface (kMean IsTimeTest)
open CameronInterface (L2I IsTimeKernelOp IsPosSqrt TemporalMeanCore KaNorm)

/-! ### `L^q` duality against bounded functions -/

/-- Auxiliary: `x^q = x x^{q-1}` for `x ≥ 0`, `q ≠ 0`. -/
theorem rpow_eq_mul_rpow_sub_one {x q : ℝ} (hx : 0 ≤ x) (hq : q ≠ 0) :
    x ^ q = x * x ^ (q - 1) := by
  rcases hx.eq_or_lt with rfl | hx
  · rw [Real.zero_rpow hq, zero_mul]
  · rw [Real.rpow_sub_one hx.ne', mul_div_cancel₀ _ hx.ne']

/-- **`L^q` duality on a finite measure, against bounded functions** (the duality step of
`integrated_cameron_mean.tex` lines 292-295 at revision edf7085f (book 1.1.3)): if `F`
is integrable, `1 < q`, and `∫ F h ≤ C ‖h‖_{q'}` (`q' = q/(q-1)`) for every bounded measurable
`h`, then `‖F‖_q ≤ C`.  Route: test against `h_n = sgn F · min(|F|, n)^{q-1}`, then monotone
convergence. -/
theorem eLpNorm_le_of_dual {μ : Measure ℝ} [IsFiniteMeasure μ] {F : ℝ → ℝ}
    (hF : Integrable F μ) {q C : ℝ} (hq : 1 < q) (hC : 0 ≤ C)
    (h : ∀ g : ℝ → ℝ, Measurable g → (∃ M, ∀ x, |g x| ≤ M) →
      ∫ x, F x * g x ∂μ ≤ C * (eLpNorm g (ENNReal.ofReal (q / (q - 1))) μ).toReal) :
    eLpNorm F (ENNReal.ofReal q) μ ≤ ENNReal.ofReal C := by
  have hq0 : 0 < q := by linarith
  have hq1 : 0 < q - 1 := by linarith
  set q' := q / (q - 1) with hq'
  have hq'0 : 0 < q' := div_pos hq0 hq1
  have hqq : (q - 1) * q' = q := by rw [hq']; field_simp
  set F₀ := hF.aestronglyMeasurable.mk F
  have hF₀ : Measurable F₀ := hF.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  have hFF : F =ᵐ[μ] F₀ := hF.aestronglyMeasurable.ae_eq_mk
  set gr : ℕ → ℝ → ℝ := fun n x => min |F₀ x| n with hgr
  have hgr0 : ∀ n x, 0 ≤ gr n x := fun n x => le_min (abs_nonneg _) (Nat.cast_nonneg n)
  have hgrm : ∀ n, Measurable (gr n) := fun n => hF₀.abs.min measurable_const
  set hn : ℕ → ℝ → ℝ := fun n x => (if 0 ≤ F₀ x then 1 else -1) * gr n x ^ (q - 1) with hhn
  have habs : ∀ n x, |hn n x| = gr n x ^ (q - 1) := by
    intro n x
    simp only [hhn]
    rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg (hgr0 n x) _)]
    split_ifs <;> simp
  have hhm : ∀ n, Measurable (hn n) := fun n =>
    (Measurable.ite (measurableSet_le measurable_const hF₀) measurable_const measurable_const).mul
      ((hgrm n).pow_const _)
  have hbdd : ∀ n x, |hn n x| ≤ (n : ℝ) ^ (q - 1) := fun n x => by
    rw [habs]
    exact Real.rpow_le_rpow (hgr0 n x) (min_le_right _ _) hq1.le
  have hprod : ∀ n x, gr n x ^ q ≤ F₀ x * hn n x := by
    intro n x
    have e : F₀ x * hn n x = |F₀ x| * gr n x ^ (q - 1) := by
      simp only [hhn]
      split_ifs with hx
      · rw [abs_of_nonneg hx]; ring
      · rw [abs_of_neg (not_le.1 hx)]; ring
    rw [e, rpow_eq_mul_rpow_sub_one (hgr0 n x) hq0.ne']
    exact mul_le_mul_of_nonneg_right (min_le_left _ _) (Real.rpow_nonneg (hgr0 n x) _)
  -- the truncated integrals `A n = ∫ min(|F|, n)^q`
  have hAi : ∀ n, Integrable (fun x => gr n x ^ q) μ := fun n =>
    Integrable.of_bound ((hgrm n).pow_const q).aestronglyMeasurable ((n : ℝ) ^ q)
      (ae_of_all _ fun x => by
        rw [Real.norm_of_nonneg (Real.rpow_nonneg (hgr0 n x) _)]
        exact Real.rpow_le_rpow (hgr0 n x) (min_le_right _ _) hq0.le)
  set A : ℕ → ℝ := fun n => ∫ x, gr n x ^ q ∂μ with hA
  have hA0 : ∀ n, 0 ≤ A n := fun n => integral_nonneg fun x => Real.rpow_nonneg (hgr0 n x) _
  have hFh : ∀ n, Integrable (fun x => F x * hn n x) μ := fun n =>
    (hF.norm.const_mul ((n : ℝ) ^ (q - 1))).mono'
      (hF.aestronglyMeasurable.mul (hhm n).aestronglyMeasurable) (ae_of_all _ fun x => by
        rw [norm_mul, Real.norm_eq_abs (hn n x), mul_comm]
        exact mul_le_mul_of_nonneg_right (hbdd n x) (norm_nonneg _))
  have hlow : ∀ n, A n ≤ ∫ x, F x * hn n x ∂μ := fun n => by
    refine integral_mono_ae (hAi n) (hFh n) ?_
    filter_upwards [hFF] with x hx
    rw [hx]
    exact hprod n x
  have hnorm : ∀ n, (eLpNorm (hn n) (ENNReal.ofReal q') μ).toReal = A n ^ (1 / q') := by
    intro n
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simpa using hq'0) ENNReal.ofReal_ne_top
      (hhm n).aestronglyMeasurable, ENNReal.toReal_ofReal hq'0.le]
    have hpt : ∀ x, ‖hn n x‖ₑ ^ q' = ENNReal.ofReal (gr n x ^ q) := by
      intro x
      rw [Real.enorm_eq_ofReal_abs, habs, ENNReal.ofReal_rpow_of_nonneg
        (Real.rpow_nonneg (hgr0 n x) _) hq'0.le, ← Real.rpow_mul (hgr0 n x), hqq]
    simp_rw [hpt]
    rw [← ofReal_integral_eq_lintegral_ofReal (hAi n)
      (ae_of_all _ fun x => Real.rpow_nonneg (hgr0 n x) _), ← ENNReal.toReal_rpow,
      ENNReal.toReal_ofReal (hA0 n)]
  have hAC : ∀ n, A n ≤ C ^ q := by
    intro n
    have hk0 := h (hn n) (hhm n) ⟨(n : ℝ) ^ (q - 1), hbdd n⟩
    rw [hnorm] at hk0
    have hk : A n ≤ C * A n ^ (1 / q') := (hlow n).trans hk0
    rcases (hA0 n).eq_or_lt with h0 | hpos
    · rw [← h0]; exact Real.rpow_nonneg hC _
    · have hsplit : A n = A n ^ (1 / q) * A n ^ (1 / q') := by
        rw [← Real.rpow_add hpos, hq']
        have : 1 / q + 1 / (q / (q - 1)) = 1 := by field_simp; ring
        rw [this, Real.rpow_one]
      have h1 : A n ^ (1 / q) ≤ C := by
        have hp' : 0 < A n ^ (1 / q') := Real.rpow_pos_of_pos hpos _
        exact le_of_mul_le_mul_right (hsplit.symm.le.trans hk) hp'
      calc A n = (A n ^ (1 / q)) ^ q := by
            rw [← Real.rpow_mul hpos.le, one_div_mul_cancel hq0.ne', Real.rpow_one]
        _ ≤ C ^ q := Real.rpow_le_rpow (Real.rpow_nonneg hpos.le _) h1 hq0.le
  -- monotone convergence
  have hlim : Tendsto (fun n => ∫⁻ x, ENNReal.ofReal (gr n x ^ q) ∂μ) atTop
      (𝓝 (∫⁻ x, ‖F₀ x‖ₑ ^ q ∂μ)) := by
    refine lintegral_tendsto_of_tendsto_of_monotone
      (fun n => ((hgrm n).pow_const q).ennreal_ofReal.aemeasurable) (ae_of_all _ fun x => ?_)
      (ae_of_all _ fun x => ?_)
    · intro m n hmn
      refine ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow (hgr0 m x) ?_ hq0.le)
      exact min_le_min le_rfl (Nat.cast_le.2 hmn)
    · have hev : ∀ᶠ n : ℕ in atTop, ENNReal.ofReal (gr n x ^ q) = ‖F₀ x‖ₑ ^ q := by
        filter_upwards [eventually_ge_atTop ⌈|F₀ x|⌉₊] with n hn
        have : gr n x = |F₀ x| := min_eq_left ((Nat.le_ceil _).trans (Nat.cast_le.2 hn))
        rw [this, Real.enorm_eq_ofReal_abs, ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hq0.le]
      exact tendsto_const_nhds.congr' (hev.mono fun n hn => hn.symm)
  have hle : ∫⁻ x, ‖F₀ x‖ₑ ^ q ∂μ ≤ ENNReal.ofReal (C ^ q) := by
    refine le_of_tendsto' hlim fun n => ?_
    rw [← ofReal_integral_eq_lintegral_ofReal (hAi n)
      (ae_of_all _ fun x => Real.rpow_nonneg (hgr0 n x) _)]
    exact ENNReal.ofReal_le_ofReal (hAC n)
  rw [eLpNorm_congr_ae hFF, eLpNorm_eq_lintegral_rpow_enorm_toReal (by simpa using hq0)
    ENNReal.ofReal_ne_top hF₀.aestronglyMeasurable, ENNReal.toReal_ofReal hq0.le]
  calc (∫⁻ x, ‖F₀ x‖ₑ ^ q ∂μ) ^ (1 / q) ≤ ENNReal.ofReal (C ^ q) ^ (1 / q) :=
        ENNReal.rpow_le_rpow hle (by positivity)
    _ = ENNReal.ofReal C := by
        rw [ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg hC _) (by positivity),
          ← Real.rpow_mul hC, mul_one_div_cancel hq0.ne', Real.rpow_one]

/-! ### The square root `S = K^{1/2}` and the isometry `ι` -/

variable {p : TParams} {S : L2I →L[ℝ] L2I}

/-- Auxiliary: `KaNorm a r ≥ 0`. -/
theorem kaNorm_nonneg (a r : ℝ) : 0 ≤ KaNorm a r :=
  Real.rpow_nonneg (setIntegral_nonneg measurableSet_Icc fun _ _ =>
    Real.rpow_nonneg (abs_nonneg _) _) _

/-- Auxiliary: for a positive square root `S` of `K`, `‖S g‖² = ⟪K g, g⟫ = ∫∫ |s-t|^{-a} g g`. -/
theorem norm_sq_of_isPosSqrt (hS : IsPosSqrt (CameronTemporal.kOpK p) S) (g : L2I) :
    ‖S g‖ ^ 2 = kform p.a (g : ℝ → ℝ) (g : ℝ → ℝ) := by
  have hsym : ⟪S g, S g⟫ = ⟪g, S (S g)⟫ := hS.1.isSymmetric g (S g)
  rw [← real_inner_self_eq_norm_sq, hsym, real_inner_comm, ← ContinuousLinearMap.comp_apply,
    hS.2, inner_K_eq_kform (isTimeKernelOp_kOpK p)]

/-- Auxiliary: `‖S g‖ = ‖J g‖_{H_t}` (TeX line 270: on tests `‖K^{1/2} f‖₂ = ‖f‖_{H_t}`). -/
theorem norm_eq_of_isPosSqrt (hS : IsPosSqrt (kOpK p) S) (g : L2I) :
    ‖S g‖ = ‖Jlin p ℝ g‖ := by
  have h1 := norm_sq_of_isPosSqrt hS g
  have h2 : ‖Jlin p ℝ g‖ ^ 2 = kform p.a (g : ℝ → ℝ) (g : ℝ → ℝ) := by
    rw [← real_inner_self_eq_norm_sq, inner_Jlin]
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 (h1.trans h2.symm)

/-- Auxiliary: `J : L²(I) → H_t` has dense range (`H_t` is the completion). -/
theorem denseRange_Jlin : DenseRange (Jlin p ℝ) := by
  have hr : range (Jlin p ℝ) = range (fun F : OccupationCompletion.KPre p ℝ => (F : Ht p)) := by
    ext x
    constructor
    · rintro ⟨F, rfl⟩
      exact ⟨OccupationCompletion.toK F, (OccupationCompletion.Jlin_apply F).symm⟩
    · rintro ⟨F, rfl⟩
      exact ⟨OccupationCompletion.KPre.toLp F, OccupationCompletion.Jlin_apply _⟩
  rw [DenseRange, hr]
  exact UniformSpace.Completion.denseRange_coe

/-- Auxiliary: the isometric extension of `J g ↦ S g` to `H_t`. -/
def iotaI (hS : IsPosSqrt (kOpK p) S) : Ht p →ₗᵢ[ℝ] L2I :=
  (S : L2I →ₗ[ℝ] L2I).extendOfIsometry denseRange_Jlin (norm_eq_of_isPosSqrt hS)

/-- Auxiliary: `ι (J g) = S g`. -/
theorem iotaI_J (hS : IsPosSqrt (kOpK p) S) (g : L2I) : iotaI hS (J p ℝ g) = S g :=
  LinearMap.extendOfIsometry_eq _ _ _ g

/-- Auxiliary: `S = K^{1/2}` has dense range (TeX line 271: `ker K = 0`). -/
theorem denseRange_of_isPosSqrt (hS : IsPosSqrt (kOpK p) S) : DenseRange S := by
  have hinj : ∀ v, S v = 0 → v = 0 := fun v hv =>
    injective_of_isTimeKernelOp (isTimeKernelOp_kOpK p)
      (by rw [← hS.2, ContinuousLinearMap.comp_apply, hv, map_zero, map_zero])
  have hperp : (LinearMap.range (S : L2I →ₗ[ℝ] L2I))ᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro v hv
    have h1 : ⟪S (S v), v⟫ = 0 :=
      (Submodule.mem_orthogonal _ v).1 hv _ (LinearMap.mem_range_self _ (S v))
    have h2 : ⟪S v, S v⟫ = 0 := by
      have hsym : ⟪S v, S v⟫ = ⟪v, S (S v)⟫ := hS.1.isSymmetric v (S v)
      rw [hsym, real_inner_comm]
      exact h1
    exact hinj v (inner_self_eq_zero.1 h2)
  have htop := Submodule.topologicalClosure_eq_top_iff.2 hperp
  have hd := (Submodule.dense_iff_topologicalClosure_eq_top).2 htop
  simpa [DenseRange, LinearMap.coe_range] using hd

/-- Auxiliary: `ι` is onto (TeX line 272: "the isometry extends onto `L²(I)`"). -/
theorem surjective_iotaI (hS : IsPosSqrt (kOpK p) S) : Function.Surjective (iotaI hS) := by
  have hcl : IsClosed (range (iotaI hS)) :=
    (iotaI hS).isometry.isUniformInducing.isComplete_range.isClosed
  have hsub : range S ⊆ range (iotaI hS) := by
    rintro _ ⟨g, rfl⟩
    exact ⟨J p ℝ g, iotaI_J hS g⟩
  have huniv : range (iotaI hS) = univ := by
    refine eq_univ_of_univ_subset ?_
    rw [← (denseRange_of_isPosSqrt hS).closure_range]
    exact hcl.closure_subset_iff.2 hsub
  exact range_eq_univ.1 huniv

/-- **The isometry `ι : H_t ≅ L²(I)`, `ι [f] = K^{1/2} f`** (`integrated_cameron_mean.tex` lines
228-229 and 268-275 at revision edf7085f (book 1.1.3)). -/
def iotaE (hS : IsPosSqrt (kOpK p) S) : Ht p ≃ₗᵢ[ℝ] L2I :=
  LinearIsometryEquiv.ofSurjective (iotaI hS) (surjective_iotaI hS)

/-- `ι (J g) = K^{1/2} g`. -/
theorem iotaE_J (hS : IsPosSqrt (kOpK p) S) (g : L2I) : iotaE hS (J p ℝ g) = S g :=
  iotaI_J hS g

/-! ### The `L^r` bound of `K^{1/2}` (TeX lines 277-295) -/

/-- Auxiliary: `∫∫ |s-t|^{-a} F F ≤ ‖K_a‖_{r/2} ‖F‖²_{r'}` for real `F ∈ L²(I)`, `2 < r < 2/a`
(`kform_abs` with the real form). -/
theorem kform_le_kaNorm {ρ : ℝ} (h2 : 2 < ρ) (hρ : ρ < 2 / p.a) {F : ℝ → ℝ}
    (hF : MemLp F 2 timeMeasure) :
    kform p.a F F ≤
      KaNorm p.a ρ * (eLpNorm F (ENNReal.ofReal (ρ / (ρ - 1))) timeMeasure).toReal ^ 2 := by
  have hρ1 : 0 < ρ - 1 := by linarith
  have hq'2 : ENNReal.ofReal (ρ / (ρ - 1)) ≤ 2 := by
    rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [div_le_iff₀ hρ1]
    linarith
  have hfin : eLpNorm F (ENNReal.ofReal (ρ / (ρ - 1))) timeMeasure ≠ ⊤ :=
    (hF.mono_exponent hq'2).eLpNorm_ne_top
  have hkm : AEMeasurable (fun q : ℝ × ℝ => ENNReal.ofReal (kern p.a (q.1 - q.2)) * ‖F q.1‖ₑ *
      ‖F q.2‖ₑ) (timeMeasure.prod timeMeasure) :=
    (((measurable_kern p.a).comp (measurable_fst.sub measurable_snd)).ennreal_ofReal.aemeasurable.mul
      hF.aestronglyMeasurable.enorm.comp_fst).mul hF.aestronglyMeasurable.enorm.comp_snd
  have hle : ‖kform p.a F F‖ ≤
      (ENNReal.ofReal (KaNorm p.a ρ) *
        eLpNorm F (ENNReal.ofReal (ρ / (ρ - 1))) timeMeasure ^ 2).toReal := by
    refine (norm_integral_le_lintegral_norm _).trans (ENNReal.toReal_mono
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.pow_ne_top hfin)) ?_)
    have hpt : ∀ q : ℝ × ℝ, ENNReal.ofReal ‖kern p.a (q.1 - q.2) * ⟪F q.1, F q.2⟫‖ =
        ENNReal.ofReal (kern p.a (q.1 - q.2)) * ‖F q.1‖ₑ * ‖F q.2‖ₑ := by
      intro q
      rw [ofReal_norm, enorm_mul, Real.enorm_of_nonneg (kern_nonneg _ _)]
      simp only [RCLike.inner_apply, conj_trivial, enorm_mul]
      ring
    simp_rw [hpt]
    rw [lintegral_prod _ hkm]
    exact kform_abs p ρ h2 hρ F hF.aestronglyMeasurable
  have := (le_abs_self _).trans ((Real.norm_eq_abs _).symm.le.trans hle)
  rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (kaNorm_nonneg _ _), ENNReal.toReal_pow] at this

/-- **`‖K^{1/2} g‖_{L^ρ} ≤ ‖K_a‖_{ρ/2}^{1/2} ‖g‖₂`** for `2 < ρ < 2/a` (TeX lines 285-295):
duality against bounded `h` and `⟪S g, h⟫ = ⟪g, S h⟫ ≤ ‖g‖ ‖S h‖`, `‖S h‖² = ⟪K h, h⟫`. -/
theorem eLpNorm_sqrt_le (hS : IsPosSqrt (kOpK p) S) {ρ : ℝ} (h2 : 2 < ρ) (hρ : ρ < 2 / p.a)
    (g : L2I) :
    eLpNorm (S g : ℝ → ℝ) (ENNReal.ofReal ρ) timeMeasure ≤
      ENNReal.ofReal (√(KaNorm p.a ρ) * ‖g‖) := by
  refine eLpNorm_le_of_dual ((Lp.memLp (S g)).integrable one_le_two) (by linarith)
    (by positivity) fun h hm ⟨M, hM⟩ => ?_
  have hhL : MemLp h 2 timeMeasure :=
    MemLp.of_bound hm.aestronglyMeasurable M (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs]; exact hM x)
  set hL : L2I := hhL.toLp h
  have hinner : ∫ x, (S g : ℝ → ℝ) x * h x ∂timeMeasure = ⟪S g, hL⟫ := by
    rw [inner_L2I]
    refine integral_congr_ae ?_
    filter_upwards [hhL.coeFn_toLp] with x hx
    rw [hx]
  have hSh : ‖S hL‖ ≤ √(KaNorm p.a ρ) *
      (eLpNorm h (ENNReal.ofReal (ρ / (ρ - 1))) timeMeasure).toReal := by
    have h1 := norm_sq_of_isPosSqrt hS hL
    have h2' := kform_le_kaNorm h2 hρ (Lp.memLp hL)
    rw [eLpNorm_congr_ae hhL.coeFn_toLp] at h2'
    rw [← h1] at h2'
    calc ‖S hL‖ = √(‖S hL‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ √(KaNorm p.a ρ * (eLpNorm h (ENNReal.ofReal (ρ / (ρ - 1))) timeMeasure).toReal ^ 2) :=
          Real.sqrt_le_sqrt h2'
      _ = _ := by rw [Real.sqrt_mul (kaNorm_nonneg _ _), Real.sqrt_sq ENNReal.toReal_nonneg]
  have hsym : ⟪S g, hL⟫ = ⟪g, S hL⟫ := hS.1.isSymmetric g hL
  rw [hinner, hsym]
  calc ⟪g, S hL⟫ ≤ ‖g‖ * ‖S hL‖ := real_inner_le_norm _ _
    _ ≤ ‖g‖ * (√(KaNorm p.a ρ) *
          (eLpNorm h (ENNReal.ofReal (ρ / (ρ - 1))) timeMeasure).toReal) := by gcongr
    _ = _ := by ring

/-- Auxiliary: the exponent bounds as real numbers. -/
theorem exponent_bounds {r : ℝ≥0∞} (h2 : 2 < r) (hr : r < ENNReal.ofReal (2 / p.a)) :
    r ≠ ⊤ ∧ 2 < r.toReal ∧ r.toReal < 2 / p.a ∧ r = ENNReal.ofReal r.toReal := by
  have htop : r ≠ ⊤ := ne_top_of_lt hr
  refine ⟨htop, ?_, ?_, (ENNReal.ofReal_toReal htop).symm⟩
  · have h2' : ENNReal.ofReal 2 < r := by simpa using h2
    exact (ENNReal.ofReal_lt_iff_lt_toReal (by norm_num) htop).1 h2'
  · exact ENNReal.toReal_lt_of_lt_ofReal hr

/-- Auxiliary: `S g ∈ L^r(I)`. -/
theorem memLp_sqrt (hS : IsPosSqrt (kOpK p) S) {r : ℝ≥0∞} (h2 : 2 < r)
    (hr : r < ENNReal.ofReal (2 / p.a)) (g : L2I) : MemLp (S g : ℝ → ℝ) r timeMeasure := by
  obtain ⟨-, h2', hr', hrr⟩ := exponent_bounds h2 hr
  rw [hrr]
  exact (eLpNorm_sqrt_le hS h2' hr' g).trans_lt ENNReal.ofReal_lt_top

/-- Auxiliary: `g ↦ S g` as a linear map into `L^r(I)`. -/
def sqrtLrL (hS : IsPosSqrt (kOpK p) S) {r : ℝ≥0∞} [Fact (1 ≤ r)] (h2 : 2 < r)
    (hr : r < ENNReal.ofReal (2 / p.a)) : L2I →ₗ[ℝ] Lp ℝ r timeMeasure where
  toFun g := (memLp_sqrt hS h2 hr g).toLp _
  map_add' f g := by
    apply Lp.ext
    filter_upwards [(memLp_sqrt hS h2 hr (f + g)).coeFn_toLp,
      Lp.coeFn_add ((memLp_sqrt hS h2 hr f).toLp _) ((memLp_sqrt hS h2 hr g).toLp _),
      (memLp_sqrt hS h2 hr f).coeFn_toLp, (memLp_sqrt hS h2 hr g).coeFn_toLp,
      Lp.coeFn_add (S f) (S g)] with x h1 h3 h4 h5 h6
    rw [h1, h3, Pi.add_apply, h4, h5, map_add, h6, Pi.add_apply]
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [(memLp_sqrt hS h2 hr (c • f)).coeFn_toLp,
      Lp.coeFn_smul c ((memLp_sqrt hS h2 hr f).toLp _),
      (memLp_sqrt hS h2 hr f).coeFn_toLp, Lp.coeFn_smul c (S f)] with x h1 h3 h4 h5
    rw [h1, RingHom.id_apply, h3, Pi.smul_apply, h4, map_smul, h5, Pi.smul_apply]

/-- **`K^{1/2} : L²(I) → L^r(I)`**, bounded by `‖K_a‖_{r/2}^{1/2}`. -/
def sqrtLr (hS : IsPosSqrt (kOpK p) S) {r : ℝ≥0∞} [Fact (1 ≤ r)] (h2 : 2 < r)
    (hr : r < ENNReal.ofReal (2 / p.a)) : L2I →L[ℝ] Lp ℝ r timeMeasure :=
  (sqrtLrL hS h2 hr).mkContinuous (√(KaNorm p.a r.toReal)) fun g => by
    obtain ⟨-, h2', hr', hrr⟩ := exponent_bounds h2 hr
    change ‖(memLp_sqrt hS h2 hr g).toLp _‖ ≤ _
    rw [Lp.norm_toLp, ← ENNReal.toReal_ofReal (by positivity :
      0 ≤ √(KaNorm p.a r.toReal) * ‖g‖)]
    refine ENNReal.toReal_mono ENNReal.ofReal_ne_top ?_
    conv_lhs => rw [hrr]
    exact eLpNorm_sqrt_le hS h2' hr' g

/-- `sqrtLr g = S g` a.e. -/
theorem coeFn_sqrtLr (hS : IsPosSqrt (kOpK p) S) {r : ℝ≥0∞} [Fact (1 ≤ r)] (h2 : 2 < r)
    (hr : r < ENNReal.ofReal (2 / p.a)) (g : L2I) :
    (sqrtLr hS h2 hr g : ℝ → ℝ) =ᵐ[timeMeasure] (S g : ℝ → ℝ) :=
  (memLp_sqrt hS h2 hr g).coeFn_toLp

/-! ### The temporal mean data -/

/-- **The temporal mean data of `P:cameron-temporal-map`** built from a positive square root `S`
of `K` (`integrated_cameron_mean.tex` lines 225-237 at revision edf7085f (book
1.1.3)): `K`, `S`, `ι` and `C_t = K^{1/2} ι : H_t → L^r(I)`. -/
def coreOf (hS : IsPosSqrt (kOpK p) S) {r : ℝ≥0∞} [Fact (1 ≤ r)] (h2 : 2 < r)
    (hr : r < ENNReal.ofReal (2 / p.a)) : TemporalMeanCore p r where
  two_lt_r := h2
  r_lt := hr
  K := kOpK p
  K_kernel := isTimeKernelOp_kOpK p
  K_pos := isPositive_of_isTimeKernelOp (isTimeKernelOp_kOpK p)
  K_strict _ hf := inner_pos_of_isTimeKernelOp (isTimeKernelOp_kOpK p) hf
  K_injective := injective_of_isTimeKernelOp (isTimeKernelOp_kOpK p)
  S := S
  S_sqrt := hS
  ι := iotaE hS
  ι_J := iotaE_J hS
  Ct := sqrtLr hS h2 hr ∘L (iotaE hS).toContinuousLinearEquiv.toContinuousLinearMap
  Ct_L2 h := coeFn_sqrtLr hS h2 hr (iotaE hS h)

/-- **C target 2: the temporal mean data exist** (`integrated_cameron_mean.tex` lines 225-237,
proof Steps 1-3 lines 246-295, at revision edf7085f (book 1.1.3)), given compactness
of the kernel operator `K` (`hK`; discharged by `isCompactOperator_of_isTimeKernelOp` with B1's
`L²`-kernel lemma, or by `TemporalCompact.K_compact`): the square root comes from the compact
spectral theorem (`exists_isPositive_sqrt`). -/
theorem exists_temporalMeanCore (p : TParams) {r : ℝ≥0∞} [Fact (1 ≤ r)] (h2 : 2 < r)
    (hr : r < ENNReal.ofReal (2 / p.a))
    (hK : ∀ K : L2I →L[ℝ] L2I, IsTimeKernelOp p K → IsCompactOperator K) :
    Nonempty (TemporalMeanCore p r) := by
  obtain ⟨S, hSpos, hSS⟩ := exists_isPositive_sqrt (kOpK p) (hK _ (isTimeKernelOp_kOpK p))
    (isPositive_of_isTimeKernelOp (isTimeKernelOp_kOpK p))
  exact ⟨coreOf ⟨hSpos, hSS⟩ h2 hr⟩

/-- **C target 3: on tests `C_t [f] = K f`** (`integrated_cameron_mean.tex` line 273 at revision
edf7085f (book 1.1.3)), for every temporal mean data `T`: `C_t J f = K^{1/2} ι J f =
K^{1/2} K^{1/2} f = K f`.  (The proof does not use the test hypothesis `IsTimeTest f`, which
this signature keeps; the statement for every `f ∈ L²(I)`, without it, is
`UniformMeanAssembly.core_Ct_J`.) -/
theorem _root_.StratonovichHAMSecondMoment.CameronInterface.TemporalMeanCore.Ct_test
    {p : TParams} {r : ℝ≥0∞} [Fact (1 ≤ r)] (T : TemporalMeanCore p r) :
    ∀ f : ℝ → ℝ, IsTimeTest f → ∀ hf : MemLp f 2 timeMeasure,
      (T.Ct (J p ℝ (hf.toLp f)) : ℝ → ℝ) =ᵐ[timeMeasure] kMean p.a f := by
  intro f _ hf
  have h1 := T.Ct_L2 (J p ℝ (hf.toLp f))
  have h3 : T.S (T.S (hf.toLp f)) = T.K (hf.toLp f) := by
    rw [← ContinuousLinearMap.comp_apply, T.S_sqrt.2]
  rw [T.ι_J, h3] at h1
  refine h1.trans ((T.K_kernel _).trans (ae_of_all _ fun s => ?_))
  exact integral_congr_ae (hf.coeFn_toLp.mono fun t ht => by simp only [ht])

end StratonovichHAMSecondMoment.CameronTemporal
