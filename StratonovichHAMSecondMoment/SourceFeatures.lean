module

/-
Copyright 2026 Le Chen. SPDX-License-Identifier: Apache-2.0

Wave L19, item L19-B: a Hilbert feature map of the source covariance
`E:pairing-source-covariance` and its continuity at fixed widths.  TeX anchors (main file
`notes/notes_stratonovich_ham_second_moment.tex`, TeX lines 1352-1370 at revision edf7085f (book
1.1.3)): Remark item (iii), the common-prefix convention 1352-1353, the cap minimum
`(δ_j ∨ δ_h)⁻¹` 1356-1357, the heat semigroup `p_{ε_j} * p_{ε_h} = p_{ε_j+ε_h}` 1358-1359, the
display 1360-1370.

Formalized (frozen targets of `SourceInterface`, exact statements):
* `source_features d : SourceFeatureTarget d`: under `H:homog` there are a real Hilbert space `H`
  (in `Type`) and a map `feat : SrcPt d → H` with `⟪feat p, feat q⟫ = srcCov α₀ Γ p q` for all
  points with positive widths;
* `source_cov_continuous d : SourceCovContinuousTarget d`: at fixed widths `w, w'` the covariance
  is jointly continuous in the two space-time points.

The feature space and the feature (route of the approved proposal, disclosed):
`H = L²(ν ⊗ dr ⊗ μ)` on `(λ, r, ξ) ∈ ℝ × ℝ × ℝ^d`, with `ν = nuE α₀ univ`
(`ν(dλ) = Γ_E(α₀)⁻¹ λ^{α₀-1} dλ`, the restriction of which to `capSet δ` is the Laplace measure
of `κ_δ`, TeX 1366-1367) and `μ` the spectral measure of `H:homog`.  For `p = ((s, x), (ε, δ))`,
`feat p (λ, r, ξ) = T_{δ,s}(λ, r) S_{ε,x}(ξ)` with
* the temporal factor `T_{δ,s}(λ, r) = 1{λ ∈ (0, δ⁻¹]} h_λ(s, r)`, `h_λ` the decaying-exponential
  feature `PairingTranslatedCS.feat` of L17 (`∫ h_λ(s,r) h_λ(s',r) dr = e^{-λ|s-s'|}`,
  `lintegral_feat_mul`, TeX 1215-1221).  The product of the two cap indicators is the indicator
  of the smaller cap `(0, (δ ∨ δ')⁻¹]` (`capSet_max`, TeX 1356-1357): this is the "common part of
  the two prefixes" of the source's construction;
* the spatial factor `S_{ε,x}(ξ) = e^{-ε|ξ|²/2} (cos ξ·x + sin ξ·x)`.  Then
  `S_{ε,x} S_{ε',y} = e^{-(ε+ε')|ξ|²/2} (cos ξ·(x-y) + sin ξ·(x+y))`; the sine part integrates to
  `0` because `μ` is even (`H:homog`), and the cosine part is `γ_{ε+ε'}(x-y)` by the Gaussian
  spectral representation `LowAlphaConvolution.gammaEps_spectral` (heat widths add,
  TeX 1358-1359).

Route difference (disclosed): the source builds the positive-width fields from independent
Laplace-frequency increments of one noise (common-prefix convention, its (2.11), (2.24)); here the
covariance identity (the TeX's own statement 1360-1365) is realized by an explicit Hilbert
feature map, and the Gaussian field is then the isonormal map of item A
(`SourceInterface.sourceField_of_parts`).  The real feature `cos + sin` against an even spectral
measure replaces a complex feature `e^{iξ·x}` and the proposal's real pair `(cos ξ·x, sin ξ·x)` in
`L²(μ)²`; it needs `IsEven μ` (a field of `H:homog`).

Continuity (`source_cov_continuous`): at a positive cap `δ_m = δ ∨ δ'`,
`κ_{δ_m}(u) = K_{(0,δ_m⁻¹]}(u)` (`JointFixedOrder.kerA_Ioc_eq`), continuous by dominated
convergence (`JointFixedOrder.continuous_KS_Ioc`); `γ_{ε+ε'}` is continuous
(`LowAlphaConvolution.gammaEps_continuous_bounded`, dominated convergence in the spectral
integral).

Fields of `H:homog` used: `alpha0_pos` (through `kerA_capSet_ne_top` and in
`source_cov_continuous`),
`μ_radon` (σ-finiteness of `μ`), `μ_even`, `μ_tempered`, `spectral`.  Nothing is assumed beyond
`HomogCovariance`.  Lemmas marked "Auxiliary to the Lean proof route" have no manuscript label.
-/

public import Mathlib
public import StratonovichHAMSecondMoment.SourceInterface
public import StratonovichHAMSecondMoment.PairingTranslatedCS
public import StratonovichHAMSecondMoment.JointFixedOrder

@[expose] public section

noncomputable section

set_option autoImplicit false

open MeasureTheory Set Filter Topology
open scoped ENNReal Real

namespace StratonovichHAMSecondMoment.SourceFeatures

open HomogHypothesis (Rd HomogCovariance)
open WickInterface (kerA capSet capSet_max capSet_of_pos measurableSet_capSet capSet_subset_Ioi)
open PairingInterface (nuE)
open LowAlphaConvolution (gammaEps gaussFactor gammaEps_spectral integrable_gaussFactor
  gaussFactor_pos gaussFactor_le_one)
open SourceInterface

variable {d : ℕ}

/-! ### The temporal factor (TeX 1356-1357, 1366-1367; L17 feature TeX 1210-1221) -/

/-- The Laplace base measure `ν(dλ) = Γ_E(a)⁻¹ λ^{a-1} dλ` on the whole line (only its
restrictions to the caps `(0, δ⁻¹]` are used). -/
def nuBase (a : ℝ) : Measure ℝ := nuE a univ

/-- Auxiliary to the Lean proof route.  `ν` is s-finite (a density against Lebesgue measure). -/
instance instSFiniteNuBase (a : ℝ) : SFinite (nuBase a) := by
  unfold nuBase nuE
  infer_instance

/-- Auxiliary to the Lean proof route.  `ν` restricted to a cap is the Laplace measure of `κ_δ`. -/
theorem nuBase_restrict (a : ℝ) {S : Set ℝ} (hS : MeasurableSet S) :
    (nuBase a).restrict S = nuE a S := by
  rw [nuBase, nuE, nuE, restrict_withDensity hS, Measure.restrict_restrict hS, inter_univ]

/-- The temporal feature in `[0,∞]`: `1{λ ∈ (0, δ⁻¹]} h_λ(s, r)` at `z = (λ, r)`. -/
def tempE (δ s : ℝ) (z : ℝ × ℝ) : ℝ≥0∞ :=
  (capSet δ).indicator (fun _ => (1 : ℝ≥0∞)) z.1 * PairingTranslatedCS.feat (z.1, s, z.2)

/-- The real temporal feature `T_{δ,s}(λ, r) = 1{λ ∈ (0, δ⁻¹]} h_λ(s, r)`. -/
def temp (δ s : ℝ) (z : ℝ × ℝ) : ℝ := (tempE δ s z).toReal

/-- Auxiliary to the Lean proof route. -/
theorem measurable_tempE (δ s : ℝ) : Measurable (tempE δ s) := by
  have h1 : Measurable fun z : ℝ × ℝ => (capSet δ).indicator (fun _ => (1 : ℝ≥0∞)) z.1 :=
    (measurable_const.indicator (measurableSet_capSet δ)).comp measurable_fst
  have h2 : Measurable fun z : ℝ × ℝ => PairingTranslatedCS.feat (z.1, s, z.2) :=
    PairingTranslatedCS.measurable_feat.comp (by fun_prop)
  exact h1.mul h2

/-- Auxiliary to the Lean proof route. -/
theorem tempE_ne_top (δ s : ℝ) (z : ℝ × ℝ) : tempE δ s z ≠ ⊤ := by
  unfold tempE PairingTranslatedCS.feat
  refine ENNReal.mul_ne_top ?_ ?_
  · by_cases h : z.1 ∈ capSet δ
    · rw [indicator_of_mem h]; exact ENNReal.one_ne_top
    · rw [indicator_of_notMem h]; exact ENNReal.zero_ne_top
  · split_ifs
    · exact ENNReal.ofReal_ne_top
    · exact ENNReal.zero_ne_top

/-- Auxiliary to the Lean proof route.  The product of two temporal features is the indicator of
the common cap `(0, (δ ∨ δ')⁻¹]` (TeX 1356-1357) times the product of the L17 features. -/
theorem tempE_mul (δ δ' s s' : ℝ) (z : ℝ × ℝ) :
    tempE δ s z * tempE δ' s' z =
      (capSet (max δ δ')).indicator
        (fun l => PairingTranslatedCS.feat (l, s, z.2) * PairingTranslatedCS.feat (l, s', z.2))
        z.1 := by
  unfold tempE
  rw [capSet_max]
  by_cases h : z.1 ∈ capSet δ <;> by_cases h' : z.1 ∈ capSet δ'
  · rw [indicator_of_mem h, indicator_of_mem h', indicator_of_mem (mem_inter h h')]
    ring
  · rw [indicator_of_notMem h',
      indicator_of_notMem (show z.1 ∉ capSet δ ∩ capSet δ' from fun hm => h' hm.2)]
    ring
  · rw [indicator_of_notMem h,
      indicator_of_notMem (show z.1 ∉ capSet δ ∩ capSet δ' from fun hm => h hm.1)]
    ring
  · rw [indicator_of_notMem h,
      indicator_of_notMem (show z.1 ∉ capSet δ ∩ capSet δ' from fun hm => h hm.1)]
    ring

/-- **Temporal Gram identity** in `[0,∞]` (TeX 1356-1357, 1366-1367 with 1215-1221):
`∫∫ T_{δ,s} T_{δ',s'} dν dr = κ_{δ∨δ'}(s - s')`. -/
theorem lintegral_tempE_mul (a δ δ' s s' : ℝ) :
    ∫⁻ z, tempE δ s z * tempE δ' s' z ∂(nuBase a).prod volume =
      kerA a (capSet (max δ δ')) (s - s') := by
  rw [lintegral_prod (f := fun z => tempE δ s z * tempE δ' s' z)
    ((measurable_tempE δ s).mul (measurable_tempE δ' s')).aemeasurable]
  have hin : ∀ l : ℝ, ∫⁻ r, tempE δ s (l, r) * tempE δ' s' (l, r) =
      (capSet (max δ δ')).indicator
        (fun l => ENNReal.ofReal (Real.exp (-(l * |s - s'|)))) l := by
    intro l
    simp_rw [tempE_mul]
    by_cases hl : l ∈ capSet (max δ δ')
    · simp only [indicator_of_mem hl]
      exact PairingTranslatedCS.lintegral_feat_mul hl.1 s s'
    · simp only [indicator_of_notMem hl, lintegral_zero]
  simp_rw [hin]
  rw [lintegral_indicator (measurableSet_capSet _), nuBase_restrict a (measurableSet_capSet _)]
  rfl

/-- Auxiliary to the Lean proof route.  Under `H:homog` the real temporal product is integrable
and its integral is `κ_{δ∨δ'}(s - s')` (positive widths). -/
theorem temp_gram {alpha α₀ : ℝ} {Γ μ : Measure (Rd d)} (hH : HomogCovariance d alpha α₀ Γ μ)
    {δ : ℝ} (hδ : 0 < δ) (δ' s s' : ℝ) :
    Integrable (fun z => temp δ s z * temp δ' s' z) ((nuBase α₀).prod volume) ∧
      ∫ z, temp δ s z * temp δ' s' z ∂(nuBase α₀).prod volume =
        (kerA α₀ (capSet (max δ δ')) (s - s')).toReal := by
  have hfin : kerA α₀ (capSet (max δ δ')) (s - s') ≠ ⊤ :=
    kerA_capSet_ne_top hH (lt_max_of_lt_left hδ) _
  have hm : AEMeasurable (fun z => tempE δ s z * tempE δ' s' z) ((nuBase α₀).prod volume) :=
    ((measurable_tempE δ s).mul (measurable_tempE δ' s')).aemeasurable
  have heq : (fun z => temp δ s z * temp δ' s' z) =
      fun z => (tempE δ s z * tempE δ' s' z).toReal := by
    funext z
    simp only [temp, ENNReal.toReal_mul]
  rw [heq]
  refine ⟨integrable_toReal_of_lintegral_ne_top hm ?_, ?_⟩
  · rw [lintegral_tempE_mul]; exact hfin
  · rw [integral_toReal hm (Eventually.of_forall fun z =>
      (ENNReal.mul_ne_top (tempE_ne_top δ s z) (tempE_ne_top δ' s' z)).lt_top),
      lintegral_tempE_mul]

/-! ### The spatial factor (TeX 1358-1359, 1360-1365) -/

/-- The real spatial feature `S_{ε,x}(ξ) = e^{-ε|ξ|²/2} (cos ξ·x + sin ξ·x)`. -/
def spat (ε : ℝ) (x : Rd d) (ξ : Rd d) : ℝ :=
  gaussFactor ε ξ * (Real.cos (inner ℝ ξ x) + Real.sin (inner ℝ ξ x))

/-- Auxiliary to the Lean proof route. -/
theorem continuous_spat (ε : ℝ) (x : Rd d) : Continuous (spat ε x) := by
  unfold spat gaussFactor
  fun_prop

/-- Auxiliary to the Lean proof route.  Heat widths add: `e^{-ε|ξ|²/2} e^{-ε'|ξ|²/2} =
e^{-(ε+ε')|ξ|²/2}` (TeX 1358-1359). -/
theorem gaussFactor_mul (ε ε' : ℝ) (ξ : Rd d) :
    gaussFactor ε ξ * gaussFactor ε' ξ = gaussFactor (ε + ε') ξ := by
  unfold gaussFactor
  rw [← Real.exp_add]
  congr 1
  ring

/-- Auxiliary to the Lean proof route.  `S_{ε,x} S_{ε',y} = e^{-(ε+ε')|ξ|²/2}
(cos ξ·(x-y) + sin ξ·(x+y))`. -/
theorem spat_mul (ε ε' : ℝ) (x y ξ : Rd d) :
    spat ε x ξ * spat ε' y ξ =
      gaussFactor (ε + ε') ξ * Real.cos (inner ℝ ξ (x - y)) +
        gaussFactor (ε + ε') ξ * Real.sin (inner ℝ ξ (x + y)) := by
  unfold spat
  rw [← gaussFactor_mul, inner_sub_right, inner_add_right, Real.cos_sub, Real.sin_add]
  ring

/-- Auxiliary to the Lean proof route.  `ξ ↦ e^{-b|ξ|²/2} f(ξ·z)` is `μ`-integrable for a
bounded continuous `f` (`|f| ≤ 1`), `b > 0`, `μ` tempered. -/
theorem integrable_gauss_trig {μ : Measure (Rd d)} (hμt : HomogHypothesis.IsTempered μ) {b : ℝ}
    (hb : 0 < b) (z : Rd d) {f : ℝ → ℝ} (hf : Continuous f) (hf1 : ∀ t, |f t| ≤ 1) :
    Integrable (fun ξ => gaussFactor b ξ * f (inner ℝ ξ z)) μ := by
  refine (integrable_gaussFactor hμt hb).mono ?_ (Eventually.of_forall fun ξ => ?_)
  · exact (by unfold gaussFactor; fun_prop :
      Continuous fun ξ : Rd d => gaussFactor b ξ * f (inner ℝ ξ z)).aestronglyMeasurable
  · rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_of_pos (gaussFactor_pos b ξ)]
    calc gaussFactor b ξ * |f (inner ℝ ξ z)| ≤ gaussFactor b ξ * 1 :=
          mul_le_mul_of_nonneg_left (hf1 _) (gaussFactor_pos b ξ).le
      _ = gaussFactor b ξ := mul_one _

/-- Auxiliary to the Lean proof route.  The sine part vanishes against an even measure:
`∫ e^{-b|ξ|²/2} sin(ξ·z) μ(dξ) = 0`. -/
theorem integral_gauss_sin {μ : Measure (Rd d)} (hμe : HomogHypothesis.IsEven μ) (b : ℝ)
    (z : Rd d) : ∫ ξ, gaussFactor b ξ * Real.sin (inner ℝ ξ z) ∂μ = 0 := by
  set f : Rd d → ℝ := fun ξ => gaussFactor b ξ * Real.sin (inner ℝ ξ z) with hf
  have hfc : Continuous f := by rw [hf]; unfold gaussFactor; fun_prop
  have hodd : ∀ ξ, f (-ξ) = -f ξ := by
    intro ξ
    simp only [hf, gaussFactor, norm_neg, inner_neg_left, Real.sin_neg, mul_neg]
  have h1 : ∫ ξ, f ξ ∂μ = ∫ ξ, f (-ξ) ∂μ := by
    conv_lhs => rw [← hμe]
    exact integral_map (by fun_prop) hfc.aestronglyMeasurable
  have h2 : ∫ ξ, f (-ξ) ∂μ = -∫ ξ, f ξ ∂μ := by
    simp_rw [hodd]
    exact integral_neg _
  change ∫ ξ, f ξ ∂μ = 0
  linarith

/-- Auxiliary to the Lean proof route.  The cosine part is the smoothed covariance:
`∫ e^{-b|ξ|²/2} cos(ξ·z) μ(dξ) = γ_b(z)` for `b > 0` (real part of
`LowAlphaConvolution.gammaEps_spectral`). -/
theorem integral_gauss_cos {Γ μ : Measure (Rd d)} (hμt : HomogHypothesis.IsTempered μ)
    (hsp : HomogHypothesis.IsSpectralMeasure Γ μ) {b : ℝ} (hb : 0 < b) (z : Rd d) :
    ∫ ξ, gaussFactor b ξ * Real.cos (inner ℝ ξ z) ∂μ = gammaEps Γ b z := by
  have hF : Integrable (fun ξ : Rd d =>
      Complex.exp (Complex.I * (inner ℝ ξ z : ℝ)) * (gaussFactor b ξ : ℂ)) μ := by
    refine (Integrable.ofReal (𝕜 := ℂ) (integrable_gaussFactor hμt hb)).mono ?_ (Eventually.of_forall fun ξ => ?_)
    · exact (by unfold gaussFactor; fun_prop : Continuous fun ξ : Rd d =>
        Complex.exp (Complex.I * (inner ℝ ξ z : ℝ)) * (gaussFactor b ξ : ℂ)).aestronglyMeasurable
    · rw [norm_mul, mul_comm Complex.I, Complex.norm_exp_ofReal_mul_I, one_mul]
      exact le_rfl
  have h := congrArg Complex.re (gammaEps_spectral hsp hb z)
  rw [Complex.ofReal_re] at h
  have hre := integral_re hF
  simp only [RCLike.re_to_complex] at hre
  rw [h, ← hre]
  refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero, Complex.exp_re, Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul,
    one_mul, zero_add, Real.exp_zero]
  ring

/-- **Spatial Gram identity** (TeX 1358-1365): under `H:homog`, for `ε, ε' > 0`,
`∫ S_{ε,x} S_{ε',y} dμ = (p_{ε+ε'} * Γ)(x - y)`, with integrability. -/
theorem spat_gram {alpha α₀ : ℝ} {Γ μ : Measure (Rd d)} (hH : HomogCovariance d alpha α₀ Γ μ)
    {ε ε' : ℝ} (hε : 0 < ε) (hε' : 0 < ε') (x y : Rd d) :
    Integrable (fun ξ => spat ε x ξ * spat ε' y ξ) μ ∧
      ∫ ξ, spat ε x ξ * spat ε' y ξ ∂μ = gammaEps Γ (ε + ε') (x - y) := by
  have hb : 0 < ε + ε' := add_pos hε hε'
  have hc := integrable_gauss_trig hH.μ_tempered hb (x - y) Real.continuous_cos Real.abs_cos_le_one
  have hs := integrable_gauss_trig hH.μ_tempered hb (x + y) Real.continuous_sin Real.abs_sin_le_one
  have heq : (fun ξ => spat ε x ξ * spat ε' y ξ) = fun ξ =>
      gaussFactor (ε + ε') ξ * Real.cos (inner ℝ ξ (x - y)) +
        gaussFactor (ε + ε') ξ * Real.sin (inner ℝ ξ (x + y)) := funext (spat_mul ε ε' x y)
  rw [heq]
  refine ⟨hc.add hs, ?_⟩
  rw [integral_add hc hs, integral_gauss_cos hH.μ_tempered hH.spectral hb,
    integral_gauss_sin hH.μ_even, add_zero]

/-! ### The feature map (TeX 1360-1370) -/

/-- The measure of the feature space: `ν ⊗ dr ⊗ μ` on `(λ, r, ξ)`. -/
def featMeasure (α₀ : ℝ) (μ : Measure (Rd d)) : Measure ((ℝ × ℝ) × Rd d) :=
  ((nuBase α₀).prod volume).prod μ

/-- The feature function of a point `p = ((s, x), (ε, δ))`:
`(λ, r, ξ) ↦ T_{δ,s}(λ, r) S_{ε,x}(ξ)`. -/
def featFun (p : SrcPt d) (z : (ℝ × ℝ) × Rd d) : ℝ :=
  temp p.2.del (p.1.1 : ℝ) z.1 * spat p.2.eps p.1.2 z.2

/-- Auxiliary to the Lean proof route. -/
theorem measurable_featFun (p : SrcPt d) : Measurable (featFun p) := by
  have h1 : Measurable fun z : (ℝ × ℝ) × Rd d => temp p.2.del (p.1.1 : ℝ) z.1 :=
    ((measurable_tempE _ _).ennreal_toReal).comp measurable_fst
  have h2 : Measurable fun z : (ℝ × ℝ) × Rd d => spat p.2.eps p.1.2 z.2 :=
    (continuous_spat _ _).measurable.comp measurable_snd
  exact h1.mul h2

/-- Auxiliary to the Lean proof route.  The product of two feature functions splits over the
product measure. -/
theorem featFun_mul (p q : SrcPt d) (z : (ℝ × ℝ) × Rd d) :
    featFun p z * featFun q z =
      (temp p.2.del (p.1.1 : ℝ) z.1 * temp q.2.del (q.1.1 : ℝ) z.1) *
        (spat p.2.eps p.1.2 z.2 * spat q.2.eps q.1.2 z.2) := by
  unfold featFun
  ring

/-- Auxiliary to the Lean proof route.  Under `H:homog` the feature functions are pairwise
product-integrable and `∫ F_p F_q = srcCov α₀ Γ p q`. -/
theorem featFun_gram {alpha α₀ : ℝ} {Γ μ : Measure (Rd d)} (hH : HomogCovariance d alpha α₀ Γ μ)
    (p q : SrcPt d) :
    Integrable (fun z => featFun p z * featFun q z) (featMeasure α₀ μ) ∧
      ∫ z, featFun p z * featFun q z ∂featMeasure α₀ μ = srcCov α₀ Γ p q := by
  have := hH.μ_radon
  have hT := temp_gram hH p.2.del_pos q.2.del (p.1.1 : ℝ) (q.1.1 : ℝ)
  have hS := spat_gram hH p.2.eps_pos q.2.eps_pos p.1.2 q.1.2
  have heq : (fun z => featFun p z * featFun q z) = fun z : (ℝ × ℝ) × Rd d =>
      (fun w => temp p.2.del (p.1.1 : ℝ) w * temp q.2.del (q.1.1 : ℝ) w) z.1 *
        (fun ξ => spat p.2.eps p.1.2 ξ * spat q.2.eps q.1.2 ξ) z.2 :=
    funext (featFun_mul p q)
  rw [heq]
  refine ⟨hT.1.mul_prod hS.1, ?_⟩
  have hpm := integral_prod_mul (μ := (nuBase α₀).prod volume) (ν := μ)
    (fun w => temp p.2.del (p.1.1 : ℝ) w * temp q.2.del (q.1.1 : ℝ) w)
    (fun ξ => spat p.2.eps p.1.2 ξ * spat q.2.eps q.1.2 ξ)
  rw [featMeasure, hpm, hT.2, hS.2]
  rfl

/-- Auxiliary to the Lean proof route.  Each feature function is in `L²(ν ⊗ dr ⊗ μ)`. -/
theorem memLp_featFun {alpha α₀ : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogCovariance d alpha α₀ Γ μ) (p : SrcPt d) :
    MemLp (featFun p) 2 (featMeasure α₀ μ) := by
  rw [memLp_two_iff_integrable_sq (measurable_featFun p).aestronglyMeasurable]
  have h := (featFun_gram hH p p).1
  refine h.congr (Eventually.of_forall fun z => ?_)
  simp only [sq]

/-- **The feature map of `E:pairing-source-covariance`** (TeX 1352-1370 at revision edf7085f
(book 1.1.3)): `p ↦ F_p ∈ L²(ν ⊗ dr ⊗ μ)`. -/
def featL2 {alpha α₀ : ℝ} {Γ μ : Measure (Rd d)} (hH : HomogCovariance d alpha α₀ Γ μ)
    (p : SrcPt d) : Lp ℝ 2 (featMeasure α₀ μ) :=
  (memLp_featFun hH p).toLp (featFun p)

/-- **Gram identity of the feature map** (TeX 1360-1370 at revision edf7085f (book 1.1.3)):
`⟪F_p, F_q⟫_{L²} = κ_{δ_p∨δ_q}(s_p - s_q) (p_{ε_p+ε_q} * Γ)(x_p - x_q)`. -/
theorem inner_featL2 {alpha α₀ : ℝ} {Γ μ : Measure (Rd d)} (hH : HomogCovariance d alpha α₀ Γ μ)
    (p q : SrcPt d) : inner ℝ (featL2 hH p) (featL2 hH q) = srcCov α₀ Γ p q := by
  rw [L2.inner_def, ← (featFun_gram hH p q).2]
  refine integral_congr_ae ?_
  filter_upwards [(memLp_featFun hH p).coeFn_toLp, (memLp_featFun hH q).coeFn_toLp] with z hp hq
  rw [featL2, featL2, hp, hq]
  exact mul_comm _ _

/-- **`E:pairing-source-covariance` as a feature identity** (TeX 1352-1370 at revision edf7085f
(book 1.1.3)): under `H:homog`, the source covariance `srcCov α₀ Γ` is the Gram kernel of a map
into a real Hilbert space (`L²(ν ⊗ dr ⊗ μ)`, `featL2`).  Route: the temporal factor is L17's
decaying-exponential feature on the common cap `(0, (δ∨δ')⁻¹]`, the spatial factor the real
spectral feature `e^{-ε|ξ|²/2}(cos ξ·x + sin ξ·x)` against the even spectral measure (see the
module docstring for the route difference from the source's common-prefix construction). -/
theorem source_features (d : ℕ) : SourceFeatureTarget d := by
  intro alpha α₀ Γ μ hH
  exact ⟨Lp ℝ 2 (featMeasure α₀ μ), inferInstance, inferInstance, inferInstance, featL2 hH,
    inner_featL2 hH⟩

/-! ### Continuity at fixed widths -/

/-- Auxiliary to the Lean proof route.  At a positive width `δ`, `u ↦ κ_δ(u)` (real) is
continuous (`κ_δ = K_{(0,δ⁻¹]}`, dominated convergence). -/
theorem continuous_kerA_capSet {a δ : ℝ} (ha : 0 < a) (hδ : 0 < δ) :
    Continuous fun u => (kerA a (capSet δ) u).toReal := by
  have heq : (fun u => (kerA a (capSet δ) u).toReal) =
      fun u => DampedNormsHomog.KS a (Ioc 0 δ⁻¹) u := by
    funext u
    rw [capSet_of_pos hδ, JointFixedOrder.kerA_Ioc_eq ha,
      ENNReal.toReal_ofReal (DampedNormsHomog.KS_nonneg _ _ _ ha)]
  rw [heq]
  exact JointFixedOrder.continuous_KS_Ioc ha _

/-- **Continuity of the source covariance at fixed widths** (TeX 1360-1370 at revision edf7085f
(book 1.1.3)): for fixed `w, w'`, `((s,x),(s',y)) ↦ κ_{δ∨δ'}(s-s') γ_{ε+ε'}(x-y)` is continuous
on `([0,∞) × ℝ^d)²`. -/
theorem source_cov_continuous (d : ℕ) : SourceCovContinuousTarget d := by
  intro alpha α₀ Γ μ hH w w'
  have hK := continuous_kerA_capSet (a := α₀) hH.alpha0_pos (lt_max_of_lt_left w.del_pos)
    (δ := max w.del w'.del)
  have hG := (LowAlphaConvolution.gammaEps_continuous_bounded hH.μ_tempered hH.spectral
    (add_pos w.eps_pos w'.eps_pos)).1
  have heq : (fun pq : (↥(Set.Ici (0 : ℝ)) × Rd d) × (↥(Set.Ici (0 : ℝ)) × Rd d) =>
      srcCov α₀ Γ (pq.1, w) (pq.2, w')) = fun pq =>
      (fun u => (kerA α₀ (capSet (max w.del w'.del)) u).toReal)
          ((pq.1.1 : ℝ) - (pq.2.1 : ℝ)) *
        gammaEps Γ (w.eps + w'.eps) (pq.1.2 - pq.2.2) := by
    funext pq
    rfl
  rw [heq]
  refine (hK.comp (f := fun pq : (↥(Set.Ici (0 : ℝ)) × Rd d) × (↥(Set.Ici (0 : ℝ)) × Rd d) =>
      (pq.1.1 : ℝ) - (pq.2.1 : ℝ)) (by fun_prop)).mul ?_
  exact hG.comp (f := fun pq : (↥(Set.Ici (0 : ℝ)) × Rd d) × (↥(Set.Ici (0 : ℝ)) × Rd d) =>
    pq.1.2 - pq.2.2) (by fun_prop)

end StratonovichHAMSecondMoment.SourceFeatures
