module

/-
Copyright 2026 Le Chen. SPDX-License-Identifier: Apache-2.0

Wave L16, item L16-D, part 2 of the assembly: the regulator of `P:uniform-mean-regulator`
(first bound and value class), and `L:positive-raw-embedding` for the constructed maps,
decoupled from every compactness statement.

TeX anchors (revision edf7085f, book 1.1.3):
* `integrated_uniform_mean.tex`: `E:uniform-mean-row` lines 22-32, `L:uniform-mean-cutoff`
  40-53 (`E:uniform-spatial-mean`), the objects `U`, `c_t`, `𝒯_R` 257-270,
  `P:uniform-mean-regulator` statement 272-288, proof Step 2 lines 310-318 (first bound and
  the `L^r(I; 𝒦(E))` value class).  The projection/tail half (`P_ret`, `Q_{J,K}`, `ε_J`) is
  out of scope (decision 8 of L16).
* `integrated_intrinsic_constant.tex`: `L:positive-raw-embedding` statement 22-40, proof
  42-132 (Steps 2 and 4).
* `integrated_cameron_mean.tex`: `P:cameron-spatial-map` 104-119, `P:cameron-temporal-map`
  225-237 (`C_t f = K f` on tests, line 273), `L:cameron-fractional-products` 29-42.

Headline results:
* `positive_raw_embedding_constructed` (D target 4): `PositiveRawEmbeddingTarget hH η r` from
  B2's `SpatialMeanMapTarget` and C's `KformAbsTarget` only.  No compactness statement (B1's
  `CutoffCompact`, C's `TemporalCompact`, `CameronSpatialMap`'s compactness fields, the
  compactness of `C_t`) enters.  `YoungTarget` is a frozen hypothesis and is not used.
* `uniform_mean_regulator` (D target 3): `UniformMeanRegulatorTarget hH η r`, i.e. L15's named
  input `UniformMeanRegulator` is constructed from the item outputs (`CameronSpatialTarget`,
  `UniformSpatialMeanTarget`, `UniformCutoffTarget`, `SobolevEmbedTarget`,
  `FractionalProductsTarget`, `TemporalMapTarget`, `UMapTarget`), with
  `M_0 = A_s M_{1/2}²`, `A_s = C_s² √R_sp`, at `s = (α/4 + 1/2)/2`.
* `mean_compact_values`: `MeanCompactValuesTarget` for every regulator.
* `positive_raw_mean_of_items`: the regulator with L15's `positive_raw_mean_paper`, i.e.
  `PositiveRawMeanTarget` for a constructed regulator, nothing supplied beyond the item outputs.

Proof route of the decoupled `E:positive-raw-mean` (`positive_raw_mean_for`): L15's
`PositiveRawMean` proof, restated for bare maps `T_R` with `IsSpatialMeanMap` (the smooth-test
formula and the test-state row) and `U` with `UTensorSpec` (the formula on single smooth
tensors) in place of the fields of `UniformMeanRegulator`.  L15's module is not edited; its
regulator-free lemmas are reused.

Lemmas whose doc comments say "Auxiliary" have no manuscript label.
-/
public import Mathlib
public import StratonovichHAMSecondMoment.CameronUMap

@[expose] public section

noncomputable section

set_option autoImplicit false

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff RealInnerProductSpace

namespace StratonovichHAMSecondMoment.UniformMeanAssembly

open HomogHypothesis (Rd HomogCovariance)
open WeakSobolev (IsTestFunction)
open OccupationCompletion (TParams SpData Hsp toHsp HI J incl sliceField kform)
open VariationalDilation (CPos conv mean)
open SpaceTimePositivity (timeMeasure)
open SpatialFourLinear (Rsp)
open UniformMeanInterface
open PositiveRawMean (UM0Facts um0Facts kBochner inclTwo coeFn_inclTwo)
open CameronInterface

variable {d : ℕ}

/-! ### Step 2 of `L:positive-raw-embedding` for a bare `U` with `UTensorSpec` -/

section Step2

variable {S : SpData d} {p : TParams} {r : ℝ≥0∞} [Fact (1 ≤ r)]

/-- **Step 2 of `L:positive-raw-embedding`, weak form, for a bare `U`** (TeX
`integrated_intrinsic_constant.tex` lines 69-82 at revision edf7085f (book 1.1.3);
L15's `PositiveRawMean.inner_U_J` with `UTensorSpec` in place of the regulator): for every
`φ, F ∈ L²(I; H_sp)`, `⟪φ, U J F⟫_{L²(I;H_sp)} = ⟪J φ, J F⟫_{H_I}`. -/
theorem inner_U_J {U : HI p S →L[ℝ] Lp (Hsp S) r timeMeasure} (hU : UTensorSpec p S r U)
    (hr : 2 ≤ r) (φ F : Lp (Hsp S) 2 timeMeasure) :
    ⟪φ, inclTwo hr (U (J p (Hsp S) F))⟫ = ⟪J p (Hsp S) φ, J p (Hsp S) F⟫ := by
  set A : Lp (Hsp S) 2 timeMeasure →L[ℝ] Lp (Hsp S) 2 timeMeasure :=
    inclTwo hr ∘L U ∘L J p (Hsp S) with hA
  set ℓ : Lp (Hsp S) 2 timeMeasure →L[ℝ] ℝ :=
    innerSL ℝ φ ∘L A - innerSL ℝ (J p (Hsp S) φ) ∘L J p (Hsp S) with hℓ
  have hz : ℓ = 0 := by
    refine PositiveRawMean.clm_eq_zero_of_tensor ℓ fun f hf q hF => ?_
    simp only [hℓ, hA, sub_apply, ContinuousLinearMap.comp_apply,
      innerSL_apply_apply]
    rw [sub_eq_zero, (OccupationCompletion.positive_bochner_inclusion _).2.2.2,
      OccupationCompletion.kform_congr p.a (Filter.EventuallyEq.refl _ _) hF.coeFn_toLp,
      PositiveRawMean.kform_tensor (Lp.memLp φ) hf q, MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [coeFn_inclTwo hr (U (J p (Hsp S) (hF.toLp _))), hU f hf q hF] with s h1 h2
    rw [h1, h2, inner_smul_right]
  have := congrArg (fun L => L F) hz
  simp only [hℓ, hA, sub_apply, ContinuousLinearMap.comp_apply,
    innerSL_apply_apply, zero_apply, sub_eq_zero] at this
  exact this

/-- **Step 2 of `L:positive-raw-embedding`, the identification, for a bare `U`** (TeX lines
69-82 at revision edf7085f (book 1.1.3)): for a smooth compactly supported field `Ψ`,
`U(Ψ)(s) = ∫_I |s-t|^{-a} Ψ_t dt` for a.e. `s`. -/
theorem U_incl_ae {U : HI p S →L[ℝ] Lp (Hsp S) r timeMeasure} (hU : UTensorSpec p S r U)
    (hr : 2 ≤ r) {Ψ : ℝ × Rd d → ℝ} (hΨ : ContDiff ℝ ∞ Ψ) (hΨs : HasCompactSupport Ψ) :
    (U (incl p S Ψ) : ℝ → Hsp S) =ᵐ[timeMeasure] kBochner p.a (sliceField S Ψ) := by
  obtain ⟨hc, C, hC⟩ := OccupationCompletion.sliceField_continuous_bdd (S := S) hΨ hΨs
  have hF₀ := OccupationCompletion.sliceField_memLp (S := S) hΨ hΨs
  set F₀ := hF₀.toLp (sliceField S Ψ) with hF₀def
  have hincl : incl p S Ψ = J p (Hsp S) F₀ := by
    simp only [incl, hΨ, hΨs, and_self, ↓reduceDIte, hF₀def]
  have hY := PositiveRawMean.memLp_kBochner p.ha0.le p.ha1 hc hC
  set Y := hY.toLp (kBochner p.a (sliceField S Ψ)) with hYdef
  set X := inclTwo hr (U (J p (Hsp S) F₀)) with hXdef
  have hXY : X = Y := by
    refine ext_inner_left ℝ fun φ => ?_
    rw [hXdef, inner_U_J hU hr, (OccupationCompletion.positive_bochner_inclusion _).2.2.2,
      OccupationCompletion.kform_congr p.a (Filter.EventuallyEq.refl _ _) hF₀.coeFn_toLp,
      MeasureTheory.L2.inner_def]
    unfold kform
    rw [integral_prod _ (OccupationCompletion.kform_integrable p.ha0.le p.ha1 (Lp.memLp φ) hF₀)]
    refine integral_congr_ae ?_
    filter_upwards [hY.coeFn_toLp, ae_restrict_mem measurableSet_Ioo] with s h1 hs
    rw [h1, kBochner, ← integral_inner (PositiveRawMean.integrable_kern_smul p.ha1
      (Ioo_subset_Icc_self hs) hc.aestronglyMeasurable hC)]
    simp only [inner_smul_right]
  rw [hincl]
  filter_upwards [coeFn_inclTwo hr (U (J p (Hsp S) F₀)), hY.coeFn_toLp] with s h1 h2
  rw [← h1, ← hXdef, hXY, h2]

end Step2

/-! ### Step 4 of `L:positive-raw-embedding` for a bare `T_R` with `IsSpatialMeanMap` -/

section Step4

variable {S : SpData d}

/-- **Step 4 of `L:positive-raw-embedding`, "Dense states extend the identity to `E`", for a
bare `T_R`** (TeX lines 116-126 at revision edf7085f (book 1.1.3); L15's
`PositiveRawMean.T_eq_BE` with the row of `IsSpatialMeanMap`): if `q` has the row
`⟪q, k_R(f,g)⟫ = ∫ V f g` for real tests `f, g` and `M` is the multiplier by `V`, then
`T_R q = B_E(M)`. -/
theorem T_eq_BE (h0 : UM0Facts d) {η : CutoffProfile d} {R : ℝ}
    {T : Hsp S →L[ℝ] (E d →L[ℝ] E d)} (hT : IsSpatialMeanMap S η R T)
    {q : Hsp S} {V : Rd d → ℝ} {M : Hhalf d →L[ℝ] Hmhalf d} (hM : IsMultiplier V M)
    (hq : ∀ f g : Rd d → ℝ, IsTestFunction f → IsTestFunction g →
      ⟪q, rowTest S η R f g⟫ = ∫ x, V x * f x * g x) :
    T q = BE M := by
  set D := T q - BE M with hD
  have hdw : ∀ z ∈ {z : E d | ∃ f z₂, IsTestFunction f ∧ z = toE (toHhalf f) z₂},
      ∀ w ∈ {w : E d | ∃ w₁ g, IsTestFunction g ∧ w = toE w₁ (lam (toHhalf g))},
      ⟪D z, w⟫ = 0 := by
    rintro _ ⟨f, z₂, hf, rfl⟩ _ ⟨w₁, g, hg, rfl⟩
    have hVf : IsTestFunction fun x => V x * f x := ⟨hM.1.mul hf.1, hf.2.mul_left⟩
    rw [hD, sub_apply, inner_sub_left, hT.2 q f g hf hg z₂ w₁,
      h0.BE_apply, PositiveRawMean.inner_toE, inner_zero_left, zero_add, hM.2 f hf,
      h0.inner_toHmhalf_lam hVf hg, hq f g hf hg, sub_eq_zero]
  have hz : ∀ z ∈ {z : E d | ∃ f z₂, IsTestFunction f ∧ z = toE (toHhalf f) z₂}, D z = 0 := by
    intro z hz
    have hcl : IsClosed {w : E d | ⟪D z, w⟫ = 0} :=
      isClosed_eq (continuous_const.inner continuous_id) continuous_const
    have hsub := closure_minimal (fun w hw => hdw z hz w hw) hcl
    rw [(PositiveRawMean.dense_dualStates h0).closure_eq] at hsub
    exact inner_self_eq_zero.1 (hsub (mem_univ _))
  have hcl : IsClosed {z : E d | D z = 0} := isClosed_eq D.continuous continuous_const
  have hsub := closure_minimal hz hcl
  rw [(PositiveRawMean.dense_testStates h0).closure_eq] at hsub
  have hD0 : D = 0 := ContinuousLinearMap.ext fun z => hsub (mem_univ z)
  exact sub_eq_zero.1 hD0

/-- **Step 4 of `L:positive-raw-embedding` for a bare `T_R`** (TeX lines 114-131 at revision
edf7085f (book 1.1.3)): `T_R(∫_I K(s,t) Ψ_t dt) = B_E(M)` for `M` the multiplier by
`m_R h_{Ψ,s}`, `s ∈ [0,1]`. -/
theorem T_kBochner_eq (h0 : UM0Facts d) {p : TParams} {η : CutoffProfile d} {R : ℝ}
    {T : Hsp S →L[ℝ] (E d →L[ℝ] E d)} (hT : IsSpatialMeanMap S η R T)
    {Ψ : ℝ × Rd d → ℝ} (hΨ : ContDiff ℝ ∞ Ψ) (hΨs : HasCompactSupport Ψ) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) {M : Hhalf d →L[ℝ] Hmhalf d}
    (hM : IsMultiplier (fun x => mR η R x * mean p.a S.Γ Ψ s x) M) :
    T (kBochner p.a (sliceField S Ψ) s) = BE M := by
  refine T_eq_BE h0 hT hM fun f g hf hg => ?_
  have hk : IsTestFunction fun x => (etaR η R x * f x) * (etaR η R x * g x) :=
    ⟨((PositiveRawMean.etaR_contDiff η R).mul hf.1).mul
      ((PositiveRawMean.etaR_contDiff η R).mul hg.1), (hf.2.mul_left.mul_right)⟩
  rw [rowTest, PositiveRawMean.inner_kBochner_toHsp p.ha1 hΨ hΨs hk hs]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  simp only [mR_eq]
  ring

end Step4

/-! ### `E:positive-raw-mean` for bare maps -/

section Main

variable {p : TParams} {S : SpData d}

/-- **`E:positive-raw-mean` (mean identity) and the canonical version for bare maps**
(`integrated_intrinsic_constant.tex` lines 32-39, proof 42-132, at revision edf7085f (book
1.1.3)): for maps `T_R` (`R ≥ 1`) with `IsSpatialMeanMap` and `U` with
`UTensorSpec`, `2 ≤ r`, and covariance data whose means `h_{Ψ,s}` are smooth and bounded,
`PositiveRawMeanFor η T U` holds.  No compactness is used. -/
theorem positive_raw_mean_for (h0 : UM0Facts d) {η : CutoffProfile d} {r : ℝ≥0∞}
    [Fact (1 ≤ r)] {T : ∀ R : ℝ, 1 ≤ R → Hsp S →L[ℝ] (E d →L[ℝ] E d)}
    (hT : ∀ R hR, IsSpatialMeanMap S η R (T R hR)) {U : HI p S →L[ℝ] Lp (Hsp S) r timeMeasure}
    (hU : UTensorSpec p S r U) (hr : 2 ≤ r)
    (hmean : ∀ Ψ ∈ CPos d, ∀ s ∈ Ioo (0 : ℝ) 1,
      ContDiff ℝ ∞ (mean p.a S.Γ Ψ s) ∧ ∃ C, ∀ x, |mean p.a S.Γ Ψ s x| ≤ C) :
    PositiveRawMeanFor η T U := by
  intro Ψ hΨ R hR
  set V : ℝ → Rd d → ℝ := fun s x => mR η R x * mean p.a S.Γ Ψ s x with hV
  set Mf : ℝ → (Hhalf d →L[ℝ] Hmhalf d) := fun s =>
    open Classical in if h : ∃ M, IsMultiplier (V s) M then h.choose else 0 with hMfdef
  have hMf : ∀ s ∈ Ioo (0 : ℝ) 1, IsMultiplier (V s) (Mf s) := by
    intro s hs
    obtain ⟨hsm, C, hC⟩ := hmean Ψ hΨ s hs
    have hVs : ContDiff ℝ ∞ (V s) := (PositiveRawMean.mR_contDiff η R).mul hsm
    have hb : ∀ x, |V s x| ≤ C := by
      intro x
      obtain ⟨h1, h2⟩ := PositiveRawMean.mR_mem η R x
      rw [hV, abs_mul, abs_of_nonneg h1]
      calc mR η R x * |mean p.a S.Γ Ψ s x| ≤ 1 * |mean p.a S.Γ Ψ s x| :=
            mul_le_mul_of_nonneg_right h2 (abs_nonneg _)
        _ ≤ C := by rw [one_mul]; exact hC x
    have hex : ∃ M, IsMultiplier (V s) M := (h0.exists_isMultiplier hVs hb).imp fun _ h => h.1
    simp only [hMfdef, hex, ↓reduceDIte]
    exact hex.choose_spec
  have hX := U_incl_ae hU hr hΨ.1 hΨ.2.1
  have hcomp : (meanOp (T R hR) U (incl p S Ψ) : ℝ → E d →L[ℝ] E d) =ᵐ[timeMeasure]
      fun s => T R hR ((U (incl p S Ψ) : ℝ → Hsp S) s) :=
    ContinuousLinearMap.coeFn_compLpL (L := T R hR) (U (incl p S Ψ))
  have hcan : (meanOp (T R hR) U (incl p S Ψ) : ℝ → E d →L[ℝ] E d) =ᵐ[timeMeasure]
      fun s => BE (Mf s) := by
    filter_upwards [hcomp, hX, ae_restrict_mem measurableSet_Ioo] with s h1 h2 hs
    rw [h1, h2]
    exact T_kBochner_eq h0 (hT R hR) hΨ.1 hΨ.2.1 (Ioo_subset_Icc_self hs) (hMf s hs)
  refine ⟨?_, Mf, hMf, hcan⟩
  filter_upwards [hcan, ae_restrict_mem measurableSet_Ioo] with s h1 hs
  exact ⟨Mf s, hMf s hs, h1⟩

end Main

/-! ### D target 4: `L:positive-raw-embedding` for the constructed maps -/

/-- **D target 4, `L:positive-raw-embedding` for the constructed maps, decoupled from
compactness** (`integrated_intrinsic_constant.tex` lines 22-40, proof 42-132, at revision
edf7085f (book 1.1.3)), under `H:homog` with `Γ ≠ 0`, for `2 < r < 2/α₀`: the maps
`T_R` of B2's `SpatialMeanMapTarget` (`R ≥ 1`) and the map `U` built from C's
`KformAbsTarget` alone (`CameronUMap.exists_uTensorSpec_of_kformAbs`, kernel-positivity route)
satisfy the mean identity of `E:positive-raw-mean` and the canonical version.  The proof uses
no compactness statement (neither B1's `CutoffCompact` nor C's `TemporalCompact`, nor the
compactness of `T_R` or `C_t`); the hypothesis `YoungTarget` (frozen signature) is not used. -/
theorem positive_raw_embedding_constructed {alpha alpha0 : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogCovariance d alpha alpha0 Γ μ) (hΓ : Γ ≠ 0) (η : CutoffProfile d)
    {r : ℝ≥0∞} [Fact (1 ≤ r)] (hS : SpatialMeanMapTarget hH η) (_hY : YoungTarget)
    (hk : KformAbsTarget (TParams.ofHomog hH)) : PositiveRawEmbeddingTarget hH η r := by
  intro hr2 hra
  obtain ⟨U, hU, -⟩ := CameronUMap.exists_uTensorSpec_of_kformAbs (SpData.ofHomog hH) hk hr2 hra
  have hR0 : ∀ R : ℝ, 1 ≤ R → 0 < R := fun R hR => lt_of_lt_of_le one_pos hR
  refine ⟨fun R hR => (hS R (hR0 R hR)).choose, U,
    fun R hR => (hS R (hR0 R hR)).choose_spec.1, hU, ?_⟩
  exact positive_raw_mean_for um0Facts (fun R hR => (hS R (hR0 R hR)).choose_spec.1) hU
    hr2.le fun _ hΨ _ hs => PositiveRawMean.mean_smooth_bdd hH hΓ hΨ (Ioo_subset_Icc_self hs)

/-! ### D target 3: the regulator of `P:uniform-mean-regulator` -/

/-- Auxiliary (`C_t f = K f` on tests, `integrated_cameron_mean.tex` line 273 at revision
edf7085f (book 1.1.3)): for a temporal core, `C_t [f] = K f` a.e. for every
`f ∈ L²(I)`, from `C_t = K^{1/2} ι`, `ι J f = K^{1/2} f` and `K^{1/2} K^{1/2} = K`. -/
theorem core_Ct_J {p : TParams} {r : ℝ≥0∞} [Fact (1 ≤ r)] (Tc : TemporalMeanCore p r)
    {f : ℝ → ℝ} (hf : MemLp f 2 timeMeasure) :
    (Tc.Ct (J p ℝ (hf.toLp f)) : ℝ → ℝ) =ᵐ[timeMeasure] kMean p.a f := by
  have hSS : Tc.S (Tc.S (hf.toLp f)) = Tc.K (hf.toLp f) := by
    rw [← Tc.S_sqrt.2, ContinuousLinearMap.comp_apply]
  have hk : kMean p.a ⇑(hf.toLp f) = kMean p.a f := by
    funext s
    refine integral_congr_ae ?_
    filter_upwards [hf.coeFn_toLp] with t ht
    rw [ht]
  filter_upwards [Tc.Ct_L2 (J p ℝ (hf.toLp f)), Tc.K_kernel (hf.toLp f)] with t h1 h2
  rw [h1, Tc.ι_J, hSS, h2, hk]

/-- **D target 3, `P:uniform-mean-regulator`, first bound and value class**
(`integrated_uniform_mean.tex` lines 272-288, proof Step 2 lines 310-318, at revision edf7085f
(book 1.1.3)), under `H:homog`: L15's named input `UniformMeanRegulator` is
constructed, with no field supplied, from the item outputs: the spatial maps `T_R` of
`CameronSpatialTarget` (B2), the temporal core with compact `C_t` of `TemporalMapTarget` (C),
the map `U` with `‖U‖ ≤ ‖C_t‖` of `UMapTarget` (D, `CameronUMap.u_map`), and the uniform bound
`‖T_R‖ ≤ M_0 = A_s M_{1/2}²` of `E:uniform-spatial-mean` (A1), applied with the product map
of `L:cameron-fractional-products` (A2, `A_s = C_s² √R_sp`), the embedding `H^{1/2} ↪ H^s`
(A1) and the cutoff multiplier of norm `≤ M_{1/2}` (A1), at `s = (α/4 + 1/2)/2`.  Then
`‖𝒯_R‖ ≤ ‖T_R‖ ‖U‖ ≤ M_0 c_t` uniformly in `R ≥ 1`.  The projection/tail half is out
(decision 8 of L16). -/
theorem uniform_mean_regulator {alpha alpha0 : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogCovariance d alpha alpha0 Γ μ) (_hΓ : Γ ≠ 0) (η : CutoffProfile d)
    {r : ℝ≥0∞} [Fact (1 ≤ r)] (hB2 : CameronSpatialTarget hH η)
    (hA1 : UniformSpatialMeanTarget (SpData.ofHomog hH))
    (hA1c : ∀ η : CutoffProfile d, UniformCutoffTarget η) (hE : SobolevEmbedTarget d)
    (hA2 : ∀ s, alpha / 4 < s → s < 1 / 2 → FractionalProductsTarget d alpha s)
    (hC : TemporalMapTarget (TParams.ofHomog hH) r)
    (hU : UMapTarget (TParams.ofHomog hH) (SpData.ofHomog hH) r) :
    UniformMeanRegulatorTarget hH η r := by
  intro hr2 hra
  obtain ⟨Tc, -, -, hCt, -⟩ := hC
  obtain ⟨U, hUspec, hUnorm⟩ := hU Tc
  have hR0 : ∀ R : ℝ, 1 ≤ R → 0 < R := fun R hR => lt_of_lt_of_le one_pos hR
  -- the spatial maps
  let Csp : ∀ R : ℝ, 1 ≤ R → CameronSpatialMap (SpData.ofHomog hH) η R :=
    fun R hR => (hB2 R (hR0 R hR)).choose
  have hrow : ∀ R (hR : 1 ≤ R) s, alpha / 4 < s → s < 1 / 2 →
      SpatialRowAll (SpData.ofHomog hH) η R s (Csp R hR).T :=
    fun R hR => (hB2 R (hR0 R hR)).choose_spec
  -- the uniform spatial bound `‖T_R‖ ≤ A_s M_{1/2}²`
  have halpha : alpha < 2 := by linarith [hH.threshold, hH.alpha0_pos]
  set s0 : ℝ := (alpha / 4 + 1 / 2) / 2 with hs0
  have hs1 : alpha / 4 < s0 := by rw [hs0]; linarith
  have hs2 : s0 < 1 / 2 := by rw [hs0]; linarith
  obtain ⟨Cs, -, hP⟩ := hA2 s0 hs1 hs2
  obtain ⟨P, hPspec, -, hPbd, -⟩ := hP alpha0 Γ μ hH
  obtain ⟨ι, hι, hιn⟩ := hE (1 / 2) s0 hs2.le
  set A : ℝ := Cs ^ 2 * √(Rsp Γ alpha) with hAdef
  set M : ℝ := Msigma η (1 / 2) with hMdef
  have hA0 : 0 ≤ A := by positivity
  have hTbd : ∀ R (hR : 1 ≤ R), ‖(Csp R hR).T‖ ≤ A * M ^ 2 := by
    intro R hR
    obtain ⟨Lη, hLη, hLηn⟩ := hA1c η (1 / 2) R hR
    exact (hA1 s0 A M P ι Lη hA0 (fun u v => hPbd u v) hιn hLηn).2 _
      (hrow R hR s0 hs1 hs2 P ι Lη hPspec hι hLη)
  have hM0 : 0 ≤ A * M ^ 2 := by positivity
  refine ⟨{
      two_lt_r := hr2
      r_lt := hra
      Tsp := Csp
      Ct := Tc.Ct
      isCompactOperator_Ct := hCt
      Ct_test := fun f _ hf => core_Ct_J Tc hf
      U := U
      U_tensor := hUspec
      norm_U_le := hUnorm
      M0 := A * M ^ 2
      M0_nonneg := hM0
      mean_bound := fun R hR => ?_ }⟩
  calc ‖meanOp (Csp R hR).T U‖
      ≤ ‖(Csp R hR).T.compLpL r timeMeasure‖ * ‖U‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖(Csp R hR).T‖ * ‖Tc.Ct‖ :=
        mul_le_mul (ContinuousLinearMap.norm_compLpL_le _) hUnorm U.opNorm_nonneg
          (Csp R hR).T.opNorm_nonneg
    _ ≤ A * M ^ 2 * ‖Tc.Ct‖ := mul_le_mul_of_nonneg_right (hTbd R hR) Tc.Ct.opNorm_nonneg

/-- **D target, the value class of `P:uniform-mean-regulator`** (`MeanCompactValuesTarget`;
`integrated_uniform_mean.tex` lines 279-280 and 314-317 at revision edf7085f (book
1.1.3)): for every regulator, `R ≥ 1` and `Φ ∈ H_I`, the mean `𝒯_R Φ` takes compact values
a.e. (`𝒯_R Φ(s) = T_R(UΦ(s))` and `T_R` has values in `𝒦(E)`). -/
theorem mean_compact_values {p : TParams} {S : SpData d} {η : CutoffProfile d} {r : ℝ≥0∞}
    [Fact (1 ≤ r)] (Ureg : UniformMeanRegulator p S η r) : MeanCompactValuesTarget Ureg := by
  intro R hR Φ
  have h : (meanOp (Ureg.Tsp R hR).T Ureg.U Φ : ℝ → E d →L[ℝ] E d) =ᵐ[timeMeasure]
      fun s => (Ureg.Tsp R hR).T ((Ureg.U Φ : ℝ → Hsp S) s) :=
    ContinuousLinearMap.coeFn_compLpL (L := (Ureg.Tsp R hR).T) (Ureg.U Φ)
  filter_upwards [h] with s hs
  rw [hs]
  exact (Ureg.Tsp R hR).isCompactOperator_apply _

/-- **`E:positive-raw-mean` for a constructed regulator** (`integrated_intrinsic_constant.tex`
lines 32-39 at revision edf7085f (book 1.1.3)): under the item outputs of
`uniform_mean_regulator`, for `2 < r < 2/α₀` there is a regulator (L15's named input, now
constructed) with compact values whose completed mean satisfies L15's
`PositiveRawMeanTarget` (`PositiveRawMean.positive_raw_mean_paper`, nothing supplied). -/
theorem positive_raw_mean_of_items {alpha alpha0 : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogCovariance d alpha alpha0 Γ μ) (hΓ : Γ ≠ 0) (η : CutoffProfile d)
    {r : ℝ≥0∞} [Fact (1 ≤ r)] (hB2 : CameronSpatialTarget hH η)
    (hA1 : UniformSpatialMeanTarget (SpData.ofHomog hH))
    (hA1c : ∀ η : CutoffProfile d, UniformCutoffTarget η) (hE : SobolevEmbedTarget d)
    (hA2 : ∀ s, alpha / 4 < s → s < 1 / 2 → FractionalProductsTarget d alpha s)
    (hC : TemporalMapTarget (TParams.ofHomog hH) r)
    (hU : UMapTarget (TParams.ofHomog hH) (SpData.ofHomog hH) r)
    (hr2 : 2 < r) (hra : r < ENNReal.ofReal (2 / alpha0)) :
    ∃ Ureg : UniformMeanRegulator (TParams.ofHomog hH) (SpData.ofHomog hH) η r,
      PositiveRawMeanTarget Ureg ∧ MeanCompactValuesTarget Ureg := by
  obtain ⟨Ureg⟩ := uniform_mean_regulator hH hΓ η hB2 hA1 hA1c hE hA2 hC hU hr2 hra
  exact ⟨Ureg, PositiveRawMean.positive_raw_mean_paper hH hΓ η Ureg, mean_compact_values Ureg⟩

end StratonovichHAMSecondMoment.UniformMeanAssembly
