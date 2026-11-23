module

/-
Copyright 2026 Le Chen. SPDX-License-Identifier: Apache-2.0

Wave L14, item K1b.  TeX at revision 39f2597a (checked with `git show`;
the numbers are unchanged at edf7085f):
* `L:source-spatial-heat` (Original spatial space and heat),
  `notes/integrated_source_convergence.tex` lines 169-202 (statement 169-182, display 171-174,
  `E:source-heat-definition` 176-179, proof 184-202); standing hypotheses of the section
  lines 10-16 (`H:homog`, `Γ ≠ 0`; the fixed `R, T, ζ_R, E` and the driver parameters do not
  enter this lemma).
* `L:positive-physical-gram` (Finite covariance vectors and entrywise order),
  `notes/integrated_intrinsic_constant.tex` lines 143-196 (statement 143-161, proof 163-196);
  standing hypotheses lines 4-21 (`H:homog`, `a = α₀`, `I = (0,1)`, `K(s,t) = |s-t|^{-a}`,
  `Γ ≠ 0`); the mask `m_R = η(·/R)²` of `integrated_uniform_mean.tex` lines 8-10.

Objects.
* `H_Γ` (`HGamma μ`) is realized as the closure, in `L²(μ; ℂ)` viewed as a real Hilbert space,
  of the real span of the vectors `ι f = [fourierQ f]` of the real tests (`vec`), where
  `fourierQ f (ξ) = ∫ f(x) e^{iξ·x} dx`.  Since `⟪ι f, ι g⟫ = B_Γ(f,g)` (`inner_vec`), `ι` is an
  isometry from the tests with the seminorm `B_Γ(f,f)^{1/2}`, so this closure is the TeX's
  real test-null completion (the null quotient is the kernel of `ι`).  It is an `Lp`
  completion as in wave L14 decision 4.
* `C_ε` (`heatH Γ μ ε`) is the restriction to `H_Γ` of multiplication by
  `m_ε(ξ) = e^{-ε|ξ|²/2}` on `L²(μ)` (`heatL`), and `C_ε (ι f) = ι(p_ε * f)` on tests
  (`heatH_vec`), with `p_ε` the TeX's density (`LowAlphaConvolution.heatDens`).
* `H_I` (`HI p G`) for a real Hilbert space `G` is Mathlib's completion of `L²(I; G)` for the
  kernel form `⟨F,H⟩ = ∫∫_{I²} |s-t|^{-a} ⟪F(s),H(t)⟫ ds dt` (`kForm`, positive by
  `kForm_self_nonneg`), with `J = JI`; here `G = H_Γ`.  Since the wave-L14 integration these
  are the objects of `OccupationCompletion` (item K1a): `KernParams = TParams`,
  `kForm a F H = kform a F H`, `HI p G = HK p G`, `JI p G = J p G`, so the companion has one
  kernel form and one completion.  The spatial factors differ: K1a's `HI p S = HK p (Hsp S)`
  uses the completion `Hsp S` of the tests under `B_Γ`, this module uses the Fourier-side
  closure `HGamma μ`; no isometry `Hsp S ≅ HGamma μ` is formalized here.  No identification
  with a Hilbert tensor product `H_t ⊗ H_Γ` is made (wave L14 decision 4).  The vectors are
  `k = J(h_A ⊗ ι q)` (`gramVec`), `h_A = 1_A/|A|` (`stepVec`).

Formalized.
* `source_spatial_heat_paper`: `L:source-spatial-heat` WHOLE under the section's hypotheses:
  the display in both forms (physical, and `(2π)^d ∫ \hat f conj(\hat g) dμ` with the TeX's
  unitary `\hat f`, `texHat`), `H_Γ` complete (closed) and separable, real Schwartz tests in
  `H_Γ` (with the cutoff approximation of the proof), and for `ε > 0` the operator `C_ε`
  positive, self-adjoint, `‖C_ε‖ ≤ 1`, `‖I - C_ε‖ ≤ 1`, `C_ε f = p_ε * f` on tests, and
  `C_ε → I` strongly as `ε → 0+`.
* `positive_physical_gram_paper`: `L:positive-physical-gram` NARROWER.  Proved: the vectors
  `k_i^R`, `k_i^∞` as elements of `H_I`, the factorization
  `⟨k_i,k_j⟩ = ⟨h_i,h_j⟩_{H_t} B_Γ(q_i,q_j)` and the positive semidefiniteness (and symmetry)
  of both Grams `C^R`, `D`.  Missing: (i) the label row `E:positive-label-row` (TeX 153-158;
  it needs the uniform mean operator `T_R` and the multiplier form `v_L` of
  `S:uniform-physical-products`, which the companion does not construct); (ii) the
  entrywise order `0 ≤ C^R_{ij} ≤ D_{ij}` (TeX 159-161, proof 189-195), EXCLUDED by wave
  L14 decision 5 (adjacent to the reserved board item B3) and deliberately not formalized.
  The temporal factor `tPair` is the double integral `∫∫ K h_i h_j`; the TeX's statement
  that `h_i ∈ H_t` (via `L:positive-raw-embedding`) is represented by the `L²(I; G)` route.

Supplied inputs: none (no named analytic hypotheses).

Implicit hypotheses made explicit: the TeX's tests are `WeakSobolev.IsTestFunction` (smooth,
compact support); the cells are measurable sets (the TeX's cells of a partition); `η` is
smooth (the TeX's fixed cutoff profile).  Integrability is claimed only where a conclusion
states it (`memLp_fourierQ`, `rapid_mem_HGamma`, `kint`); the B_Γ display uses Bochner
integrals whose integrands are integrable (`spatialPair_spectral`, `memLp_fourierQ`).

Hypotheses carried but unused (checked against every lemma the proofs call): in both
wrappers `Γ ≠ 0`.  From `H:homog` the heat wrapper uses only `Γ` even and tempered, `μ`
locally finite and tempered, and the spectral relation; the Gram wrapper uses only `Γ` even,
`μ` tempered, the spectral relation and `0 < α₀ < 1`.  Unused in both: `d ∈ {1,2,3}`, the
local finiteness of `Γ`, `Γ` positive-definite, `μ` even, the scaling law, the threshold
`α₀ + α < 2` and the range of `α` (and `α₀ ∈ (0,1)` in the heat wrapper; `Γ` tempered and
`μ` locally finite in the Gram wrapper).  In the Gram wrapper also the cells' inclusion in
`I`, disjointness, nonemptiness,
`ℓ_i > 0`, `Σ ℓ_i = 1`, `‖f_i‖₂ = 1`, `0 ≤ η ≤ 1`, `η = 1` on the unit ball, `supp η ⊂ B_2`
and `R ≥ 1` are unused (they serve the excluded order sentence and the label row).

Totalizations (outside the manuscript domain): `vec μ F = 0` when `F̂ ∉ L²(μ)`;
`heatMult ε = 1` and `heatH Γ μ ε = id` for `ε ≤ 0` or when the spectral data fail;
`spatialVec μ q = 0` when `ι q ∉ H_Γ`.  Every wrapper conclusion is in the domain where these
are the TeX's objects.

Proof route and differences from the TeX.
* Display: the cross-correlation `c_{f,g}` is a smooth compactly supported test with
  transform `f̂ conj(ĝ)` (`fourier_crossCorr`), and `IsSpectralMeasure` gives
  `B_Γ(f,g) = ∫ f̂ conj(ĝ) dμ` (`spatialPair_spectral`); no evenness of `μ` is needed (the TeX
  uses it for reality).  `f̂ ∈ L²(μ)` from Mathlib's Fourier transform on Schwartz space
  (`fourierQ_decay`) and temperedness of `μ`.
* Separability: `H_Γ` is a subspace of the separable `L²(μ)` (the TeX uses the local bound
  and countable smooth approximation).
* Schwartz tests (as the TeX): expanding smooth cutoffs `f χ_n`, the weighted bound
  `abs_spatialPair_le_weight` against tempered `Γ` (Cauchy in `H_Γ`), and identification of
  the limit with `f̂` by pointwise dominated convergence and an a.e. subsequence; proved for
  all smooth rapidly decreasing functions (`IsRapid`), which also covers `p_ε * f`.
* Heat: the TeX argues on dense Schwartz tests and extends by uniform boundedness; here the
  claims hold for the multiplier on all of `L²(μ)` (pointwise `0 < m_ε ≤ 1`, dominated
  convergence) and pass to the invariant closed subspace `H_Γ`; invariance from
  `C_ε (ι f) = ι(p_ε * f)` (`fourierQ_heatConv`, Gaussian transform from
  `GaussianTest.gaussTest_fourier`) and `p_ε * f ∈ IsRapid`.
* `H_I`: positivity of the kernel form on `G`-valued fields is K1a's
  `OccupationCompletion.kform_self_nonneg` (the mixture `TimeCompletion.kern_eq_mixture` and
  Fubini with Bochner integrals in `G`), integrability through the temporal Schur estimate
  (`TimeCompletion.cross_integrable`).

Declarations whose doc comments say "Auxiliary" have no manuscript label.
-/
public import Mathlib
public import StratonovichHAMSecondMoment.SpaceTimePositivity
public import StratonovichHAMSecondMoment.LowAlphaConvolution
public import StratonovichHAMSecondMoment.GaussianTest
public import StratonovichHAMSecondMoment.TimeCompletion
public import StratonovichHAMSecondMoment.OccupationCompletion

@[expose] public section

noncomputable section

set_option autoImplicit false

open MeasureTheory Set Filter Metric Topology
open scoped ContDiff ENNReal ComplexConjugate

namespace StratonovichHAMSecondMoment.SourceHeatGram

open HomogHypothesis (Rd HomogCovariance IsSpectralMeasure IsEven IsTempered)
open WeakSobolev (IsTestFunction)
open SpatialFourierBound (spatialPair fourierQ ex ex_continuous norm_ex ex_sub)
open LowAlphaConvolution (heatDens gaussFactor gaussFactor_pos gaussFactor_le_one heatDens_nonneg)

variable {d : ℕ}

/-! ### The cross-correlation and its spectral form -/

/-- Auxiliary to the Lean proof route: the cross-correlation
`c_{F,G}(y) = ∫ F(x) G(x - y) dx`, the inner integral of `B_Γ(F,G)` (TeX line 172 at
edf7085f, `integrated_source_convergence.tex`). -/
def crossCorr (F G : Rd d → ℝ) (y : Rd d) : ℝ := ∫ x, F x * G (x - y)

/-- Auxiliary: `B_Γ(F,G) = ∫ c_{F,G} dΓ` (definitional). -/
theorem spatialPair_eq_crossCorr (Γ : Measure (Rd d)) (F G : Rd d → ℝ) :
    spatialPair Γ F G = ∫ y, crossCorr F G y ∂Γ := rfl

/-- Auxiliary: the cross-correlation is the convolution `F ⋆ G(-·)`. -/
theorem crossCorr_eq_convolution (F G : Rd d → ℝ) :
    crossCorr F G = convolution F (fun x => G (-x)) (ContinuousLinearMap.lsmul ℝ ℝ) volume := by
  funext y
  simp only [crossCorr, convolution, ContinuousLinearMap.lsmul_apply, smul_eq_mul, neg_sub]

/-- Auxiliary: the cross-correlation of two tests is smooth. -/
theorem crossCorr_contDiff {F G : Rd d → ℝ} (hF : IsTestFunction F) (hG : IsTestFunction G) :
    ContDiff ℝ ∞ (crossCorr F G) := by
  rw [crossCorr_eq_convolution]
  have hl : LocallyIntegrable (fun x => G (-x)) volume :=
    (hG.1.continuous.comp continuous_neg).locallyIntegrable
  exact hF.2.contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ) hF.1 hl

/-- Auxiliary: the cross-correlation of two compactly supported functions has compact support. -/
theorem crossCorr_hasCompactSupport {F G : Rd d → ℝ} (hF : HasCompactSupport F)
    (hG : HasCompactSupport G) : HasCompactSupport (crossCorr F G) := by
  rw [crossCorr_eq_convolution]
  exact hF.convolution (ContinuousLinearMap.lsmul ℝ ℝ) (hG.comp_homeomorph (Homeomorph.neg _))

/-- Auxiliary: a compact set containing the support of `(x, z) ↦ F(z) G(z - x) e_ξ(x)`. -/
theorem prod_hasCompactSupport {F G : Rd d → ℝ} (hF : HasCompactSupport F)
    (hG : HasCompactSupport G) (ξ : Rd d) :
    HasCompactSupport (Function.uncurry fun (x z : Rd d) =>
      ((F z * G (z - x) : ℝ) : ℂ) * ex ξ x) := by
  have hK : IsCompact (tsupport F) := hF.isCompact
  have hL : IsCompact (tsupport G) := hG.isCompact
  refine HasCompactSupport.intro
    (((hK.prod hL).image (continuous_fst.sub continuous_snd)).prod hK) ?_
  rintro ⟨x, z⟩ hxz
  simp only [Function.uncurry_apply_pair]
  by_cases hz : z ∈ tsupport F
  · by_cases hzx : z - x ∈ tsupport G
    · exfalso
      apply hxz
      exact ⟨⟨(z, z - x), ⟨hz, hzx⟩, by simp⟩, hz⟩
    · rw [image_eq_zero_of_notMem_tsupport hzx]; simp
  · rw [image_eq_zero_of_notMem_tsupport hz]; simp

/-- Auxiliary to the Lean proof route: the Fourier transform of the cross-correlation,
`∫ c_{F,G}(x) e^{iξ·x} dx = F̂(ξ) conj(Ĝ(ξ))` for continuous compactly supported real `F`, `G`
(`F̂ = fourierQ F`). -/
theorem fourier_crossCorr {F G : Rd d → ℝ} (hF : Continuous F) (hFc : HasCompactSupport F)
    (hG : Continuous G) (hGc : HasCompactSupport G) (ξ : Rd d) :
    ∫ x, (crossCorr F G x : ℂ) * ex ξ x = fourierQ F ξ * conj (fourierQ G ξ) := by
  have hint : Integrable (Function.uncurry fun (x z : Rd d) =>
      ((F z * G (z - x) : ℝ) : ℂ) * ex ξ x) (volume.prod volume) := by
    refine Continuous.integrable_of_hasCompactSupport ?_ (prod_hasCompactSupport hFc hGc ξ)
    refine Continuous.mul ?_ ((ex_continuous ξ).comp continuous_fst)
    exact Complex.continuous_ofReal.comp ((hF.comp continuous_snd).mul
      (hG.comp (continuous_snd.sub continuous_fst)))
  have step1 : ∀ x, (crossCorr F G x : ℂ) * ex ξ x =
      ∫ z, ((F z * G (z - x) : ℝ) : ℂ) * ex ξ x := by
    intro x
    rw [crossCorr, integral_mul_const, integral_complex_ofReal]
  simp_rw [step1]
  rw [integral_integral_swap hint]
  have inner : ∀ z, ∫ x, ((F z * G (z - x) : ℝ) : ℂ) * ex ξ x =
      (F z : ℂ) * ex ξ z * conj (fourierQ G ξ) := by
    intro z
    have h1 : ∀ x, ((F z * G (z - x) : ℝ) : ℂ) * ex ξ x =
        (F z : ℂ) * ((fun w => (G w : ℂ) * ex ξ (z - w)) (z - x)) := by
      intro x
      simp only [sub_sub_cancel]
      push_cast; ring
    simp_rw [h1]
    rw [integral_const_mul, integral_sub_left_eq_self (fun w => (G w : ℂ) * ex ξ (z - w))]
    simp_rw [ex_sub]
    have h2 : ∀ w, (G w : ℂ) * (ex ξ z * conj (ex ξ w)) =
        ex ξ z * conj ((G w : ℂ) * ex ξ w) := by
      intro w; rw [map_mul, Complex.conj_ofReal]; ring
    simp_rw [h2]
    rw [integral_const_mul, integral_conj]
    rw [fourierQ]
    ring
  simp_rw [inner]
  rw [integral_mul_const]
  rfl

/-- The spectral form of the physical pairing on tests (the second equality of the display of
`L:source-spatial-heat`, `integrated_source_convergence.tex` lines 171-173 at edf7085f, in the
transform `fourierQ F ξ = ∫ F(x) e^{iξ·x} dx`): for real tests `F`, `G` and a spectral measure
`μ` of `Γ` in the manuscript's convention,
`B_Γ(F,G) = ∫ F̂(ξ) conj(Ĝ(ξ)) μ(dξ)` (Bochner integrals; integrability of the right side is
`integrable_fourier_mul`). -/
theorem spatialPair_spectral {Γ μ : Measure (Rd d)} (hsp : IsSpectralMeasure Γ μ)
    {F G : Rd d → ℝ} (hF : IsTestFunction F) (hG : IsTestFunction G) :
    (spatialPair Γ F G : ℂ) = ∫ ξ, fourierQ F ξ * conj (fourierQ G ξ) ∂μ := by
  have hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => (crossCorr F G x : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (crossCorr_contDiff hF hG)
  have hcs : HasCompactSupport (fun x => (crossCorr F G x : ℂ)) :=
    (crossCorr_hasCompactSupport hF.2 hG.2).comp_left Complex.ofReal_zero
  have h := hsp (hcs.toSchwartzMap hsm)
  simp only [HasCompactSupport.toSchwartzMap_toFun] at h
  have h2 : ∀ ξ, ∫ x, (crossCorr F G x : ℂ) * Complex.exp (Complex.I * (inner ℝ ξ x : ℝ)) =
      fourierQ F ξ * conj (fourierQ G ξ) := fun ξ =>
    fourier_crossCorr hF.1.continuous hF.2 hG.1.continuous hG.2 ξ
  simp_rw [h2] at h
  rw [spatialPair_eq_crossCorr, ← h, integral_complex_ofReal]

/-! ### Decay of the transform of a test and the vectors `ι f` -/

/-- Auxiliary: a tempered measure integrates its weight `(1 + ‖x‖)^{-k}`. -/
theorem integrable_weight_of_tempered {ν : Measure (Rd d)} (hν : IsTempered ν) :
    ∃ k : ℕ, Integrable (fun x : Rd d => ((1 + ‖x‖) ^ k)⁻¹) ν := by
  obtain ⟨k, hk⟩ := hν
  refine ⟨k, ⟨(by fun_prop : Measurable fun x : Rd d => ((1 + ‖x‖) ^ k)⁻¹).aestronglyMeasurable,
    ?_⟩⟩
  have he : ∀ x : Rd d, ((1 + ‖x‖) ^ k)⁻¹ = (1 + ‖x‖) ^ (-(k : ℝ)) := fun x => by
    rw [Real.rpow_neg (by positivity), Real.rpow_natCast]
  simp_rw [he]
  exact (hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun x =>
    Real.rpow_nonneg (by positivity) _)).2 hk

/-- Auxiliary: `fourierQ F ξ` is Mathlib's Fourier transform of `F` at `-(2π)⁻¹ ξ`. -/
theorem fourierQ_eq_fourier {F : Rd d → ℝ} (ξ : Rd d) :
    fourierQ F ξ = FourierTransform.fourier (fun x => (F x : ℂ)) (-(2 * Real.pi)⁻¹ • ξ) := by
  rw [Real.fourier_eq, fourierQ]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [Real.fourierChar_apply, inner_smul_right, Circle.smul_def, smul_eq_mul]
  rw [mul_comm]
  congr 1
  rw [real_inner_comm]
  congr 1
  push_cast
  field_simp

/-- Auxiliary to the Lean proof route (the rapid decay of the transform of a test, through
Mathlib's Fourier transform on Schwartz space): for a real test `F` and every `k`, there is
`C` with `(1 + ‖ξ‖)^k ‖F̂(ξ)‖ ≤ C`. -/
theorem fourierQ_decay {F : Rd d → ℝ} (hF : IsTestFunction F) (k : ℕ) :
    ∃ C, ∀ ξ : Rd d, (1 + ‖ξ‖) ^ k * ‖fourierQ F ξ‖ ≤ C := by
  have hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => (F x : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hF.1
  have hcs : HasCompactSupport (fun x => (F x : ℂ)) := hF.2.comp_left Complex.ofReal_zero
  set S : SchwartzMap (Rd d) ℂ := hcs.toSchwartzMap hsm
  set T : SchwartzMap (Rd d) ℂ := SchwartzMap.fourierTransformCLM ℂ S
  set C0 := 2 ^ k * ((Finset.Iic (k, 0)).sup fun m => SchwartzMap.seminorm ℂ m.1 m.2) T
  refine ⟨(2 * Real.pi) ^ k * C0, fun ξ => ?_⟩
  have hT : ∀ w, T w = FourierTransform.fourier (fun x => (F x : ℂ)) w := fun w => by
    simp only [T, SchwartzMap.fourierTransformCLM_apply]
    rfl
  set w : Rd d := -(2 * Real.pi)⁻¹ • ξ
  have hb := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ) (m := (k, 0)) (k := k) (n := 0)
    le_rfl le_rfl T w
  rw [norm_iteratedFDeriv_zero, hT, ← fourierQ_eq_fourier] at hb
  have hpi : 1 ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
  have hw : ‖w‖ = ‖ξ‖ / (2 * Real.pi) := by
    simp only [w, norm_smul, norm_neg, norm_inv, Real.norm_eq_abs,
      abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
    field_simp
  have h1 : 1 + ‖ξ‖ ≤ 2 * Real.pi * (1 + ‖w‖) := by
    rw [hw, mul_add, mul_div_cancel₀ _ (by positivity)]
    linarith
  have h2 : (1 + ‖ξ‖) ^ k ≤ (2 * Real.pi) ^ k * (1 + ‖w‖) ^ k := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) h1 k
  calc (1 + ‖ξ‖) ^ k * ‖fourierQ F ξ‖
      ≤ (2 * Real.pi) ^ k * (1 + ‖w‖) ^ k * ‖fourierQ F ξ‖ :=
        mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
    _ = (2 * Real.pi) ^ k * ((1 + ‖w‖) ^ k * ‖fourierQ F ξ‖) := by ring
    _ ≤ (2 * Real.pi) ^ k * C0 := mul_le_mul_of_nonneg_left hb (by positivity)

/-- Auxiliary: the transform of an integrable function is continuous, hence measurable. -/
theorem fourierQ_aesm {F : Rd d → ℝ} (hF : Integrable F volume) (μ : Measure (Rd d)) :
    AEStronglyMeasurable (fourierQ F) μ :=
  (SpatialFourierBound.fourierQ_continuous hF).aestronglyMeasurable

/-- For a real test `F` and a tempered `μ`, the transform `F̂` is in `L²(μ)` (the TeX's
`(2π)^d ∫ |f̂|² dμ < ∞`; a step of `L:source-spatial-heat`). -/
theorem memLp_fourierQ {μ : Measure (Rd d)} (hμ : IsTempered μ) {F : Rd d → ℝ}
    (hF : IsTestFunction F) : MemLp (fourierQ F) 2 μ := by
  obtain ⟨k, hk⟩ := integrable_weight_of_tempered hμ
  obtain ⟨C, hC⟩ := fourierQ_decay hF k
  have hFi : Integrable F volume := hF.1.continuous.integrable_of_hasCompactSupport hF.2
  rw [memLp_two_iff_integrable_sq_norm (fourierQ_aesm hFi μ)]
  refine Integrable.mono' (hk.const_mul (C ^ 2))
    ((continuous_norm.comp (SpatialFourierBound.fourierQ_continuous hFi)).pow 2
      |>.aestronglyMeasurable) (Eventually.of_forall fun ξ => ?_)
  have hp : 0 < (1 + ‖ξ‖) ^ k := by positivity
  have hp1 : 1 ≤ (1 + ‖ξ‖) ^ k := one_le_pow₀ (by linarith [norm_nonneg ξ])
  have hn : ‖fourierQ F ξ‖ ≤ C / (1 + ‖ξ‖) ^ k := by
    rw [le_div_iff₀ hp, mul_comm]; exact hC ξ
  have hC0 : 0 ≤ C := le_trans (by positivity) (hC ξ)
  rw [Real.norm_of_nonneg (by positivity)]
  calc ‖fourierQ F ξ‖ ^ 2 ≤ (C / (1 + ‖ξ‖) ^ k) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hn 2
    _ = C ^ 2 * ((1 + ‖ξ‖) ^ k)⁻¹ * ((1 + ‖ξ‖) ^ k)⁻¹ := by ring
    _ ≤ C ^ 2 * ((1 + ‖ξ‖) ^ k)⁻¹ * 1 := by
        gcongr
        exact inv_le_one_of_one_le₀ hp1
    _ = C ^ 2 * ((1 + ‖ξ‖) ^ k)⁻¹ := mul_one _

open Classical in
/-- The vector of a real function in `L²(μ; ℂ)`: the class of its transform `fourierQ F`
(the TeX's `F ↦ (2π)^{d/2} \widehat F`, up to complex conjugation), and `0` when the
transform is not in `L²(μ)` (a totalization; every statement below uses it only where
`MemLp (fourierQ F) 2 μ` holds). -/
def vec (μ : Measure (Rd d)) (F : Rd d → ℝ) : Lp ℂ 2 μ :=
  if h : MemLp (fourierQ F) 2 μ then h.toLp (fourierQ F) else 0

/-- Auxiliary. -/
theorem vec_eq {μ : Measure (Rd d)} {F : Rd d → ℝ} (h : MemLp (fourierQ F) 2 μ) :
    vec μ F = h.toLp (fourierQ F) := by
  simp [vec, h]

/-- Auxiliary. -/
theorem coeFn_vec {μ : Measure (Rd d)} {F : Rd d → ℝ} (h : MemLp (fourierQ F) 2 μ) :
    (vec μ F : Rd d → ℂ) =ᵐ[μ] fourierQ F := by
  rw [vec_eq h]; exact h.coeFn_toLp

/-- **The covariance space `H_Γ`** (TeX: the real test-null completion of the tests for
`B_Γ`), realized as the closure in `L²(μ; ℂ)` (a real Hilbert space with
`⟪u,v⟫ = ∫ Re(conj u · v) dμ`) of the real span of the vectors of the real tests.  The map
`F ↦ vec μ F` is an isometry from the tests with the seminorm `B_Γ(F,F)^{1/2}`
(`inner_vec`), so this closure is the null-quotient completion. -/
def HGamma (μ : Measure (Rd d)) : Submodule ℝ (Lp ℂ 2 μ) :=
  (Submodule.span ℝ (vec μ '' {F | IsTestFunction F})).topologicalClosure

/-- Auxiliary: the vector of a test lies in `H_Γ`. -/
theorem vec_mem_HGamma (μ : Measure (Rd d)) {F : Rd d → ℝ} (hF : IsTestFunction F) :
    vec μ F ∈ HGamma μ :=
  Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨F, hF, rfl⟩)

/-- `H_Γ` is closed, hence complete. -/
theorem isClosed_HGamma (μ : Measure (Rd d)) : IsClosed (HGamma μ : Set (Lp ℂ 2 μ)) :=
  Submodule.isClosed_topologicalClosure _

/-- Auxiliary: `H_Γ` is complete. -/
instance instCompleteSpaceHGamma (μ : Measure (Rd d)) : CompleteSpace (HGamma μ) :=
  (isClosed_HGamma μ).completeSpace_coe

/-- `H_Γ` is separable (first conclusion of `L:source-spatial-heat`). -/
instance separableSpace_HGamma (μ : Measure (Rd d)) [IsLocallyFiniteMeasure μ] :
    TopologicalSpace.SeparableSpace (HGamma μ) := by
  have : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by norm_num⟩
  exact (TopologicalSpace.IsSeparable.of_separableSpace
    (HGamma μ : Set (Lp ℂ 2 μ))).separableSpace

/-- Auxiliary: the real inner product of two `L²(μ; ℂ)` classes of functions. -/
theorem inner_toLp {μ : Measure (Rd d)} {u v : Rd d → ℂ} (hu : MemLp u 2 μ) (hv : MemLp v 2 μ) :
    inner ℝ (hu.toLp u) (hv.toLp v) = (∫ ξ, v ξ * conj (u ξ) ∂μ).re := by
  rw [MeasureTheory.L2.inner_def]
  have hi := MeasureTheory.L2.integrable_inner (𝕜 := ℂ) (hu.toLp u) (hv.toLp v)
  have hae : (fun ξ => inner ℂ ((hu.toLp u : Rd d → ℂ) ξ) ((hv.toLp v : Rd d → ℂ) ξ))
      =ᵐ[μ] fun ξ => v ξ * conj (u ξ) := by
    filter_upwards [hu.coeFn_toLp, hv.coeFn_toLp] with ξ h1 h2
    rw [h1, h2]; simp
  rw [← integral_congr_ae hae, ← RCLike.re_eq_complex_re, ← integral_re hi]
  refine integral_congr_ae ?_
  filter_upwards [hu.coeFn_toLp, hv.coeFn_toLp] with ξ h1 h2
  rw [Complex.inner, h1, h2]; simp [mul_comm]

/-- **The covariance pairing is the inner product of `H_Γ`** (the display of
`L:source-spatial-heat`): for real tests `F`, `G` and a tempered spectral measure `μ` of `Γ`,
`⟪ι F, ι G⟫ = B_Γ(G,F)`; with `Γ` even it is `B_Γ(F,G)` (`inner_vec_comm`). -/
theorem inner_vec {Γ μ : Measure (Rd d)} (hμ : IsTempered μ) (hsp : IsSpectralMeasure Γ μ)
    {F G : Rd d → ℝ} (hF : IsTestFunction F) (hG : IsTestFunction G) :
    inner ℝ (vec μ F) (vec μ G) = spatialPair Γ G F := by
  rw [vec_eq (memLp_fourierQ hμ hF), vec_eq (memLp_fourierQ hμ hG), inner_toLp,
    ← spatialPair_spectral hsp hG hF, Complex.ofReal_re]

/-- The norm identity `‖ι F‖² = B_Γ(F,F)` on tests. -/
theorem norm_vec_sq {Γ μ : Measure (Rd d)} (hμ : IsTempered μ) (hsp : IsSpectralMeasure Γ μ)
    {F : Rd d → ℝ} (hF : IsTestFunction F) :
    ‖vec μ F‖ ^ 2 = spatialPair Γ F F := by
  rw [← real_inner_self_eq_norm_sq, inner_vec hμ hsp hF hF]

/-- Auxiliary: `x ↦ F(x) e_ξ(x)` is integrable for integrable `F`. -/
theorem integrable_mul_ex {F : Rd d → ℝ} (hF : Integrable F volume) (ξ : Rd d) :
    Integrable (fun x => (F x : ℂ) * ex ξ x) volume := by
  refine Integrable.mono' hF.norm
    (hF.ofReal.aestronglyMeasurable.mul (ex_continuous ξ).aestronglyMeasurable)
    (Eventually.of_forall fun x => ?_)
  rw [norm_mul, norm_ex, mul_one, Complex.norm_real]

/-- Auxiliary: tests are integrable. -/
theorem test_integrable {F : Rd d → ℝ} (hF : IsTestFunction F) : Integrable F volume :=
  hF.1.continuous.integrable_of_hasCompactSupport hF.2

/-- Auxiliary: `F ↦ F̂` is linear on integrable functions. -/
theorem fourierQ_add_smul {F G : Rd d → ℝ} (hF : Integrable F volume) (hG : Integrable G volume)
    (c : ℝ) (ξ : Rd d) :
    fourierQ (fun x => F x + c * G x) ξ = fourierQ F ξ + (c : ℂ) * fourierQ G ξ := by
  have i1 := integrable_mul_ex hF ξ
  have i2 := (integrable_mul_ex hG ξ).const_mul (c : ℂ)
  simp only [fourierQ]
  rw [← integral_const_mul, ← integral_add i1 i2]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  push_cast; ring

/-- Auxiliary: `vec` is linear on functions whose transforms are in `L²(μ)`. -/
theorem vec_add_smul {μ : Measure (Rd d)} {F G : Rd d → ℝ} (hF : Integrable F volume)
    (hG : Integrable G volume) (hF2 : MemLp (fourierQ F) 2 μ) (hG2 : MemLp (fourierQ G) 2 μ)
    (c : ℝ) : vec μ (fun x => F x + c * G x) = vec μ F + c • vec μ G := by
  have he : fourierQ (fun x => F x + c * G x) = fourierQ F + c • fourierQ G := by
    funext ξ
    rw [fourierQ_add_smul hF hG c ξ]
    simp [Complex.real_smul]
  have h2 : MemLp (fourierQ (fun x => F x + c * G x)) 2 μ := by
    rw [he]; exact hF2.add (hG2.const_smul c)
  rw [vec_eq h2, vec_eq hF2, vec_eq hG2, ← MemLp.toLp_const_smul, ← MemLp.toLp_add]
  exact MemLp.toLp_congr _ _ (Eventually.of_forall fun ξ => by rw [he])

/-! ### Rapidly decreasing smooth functions; real Schwartz tests enter `H_Γ` -/

/-- Smooth `F` with `(1 + ‖x‖)^k |F(x)| ≤ C_k` for every `k`.  It contains the real Schwartz
tests (`isRapid_schwartz`) and the heat images `p_ε * f` of tests (`isRapid_heatConv`). -/
def IsRapid (F : Rd d → ℝ) : Prop :=
  ContDiff ℝ ∞ F ∧ ∀ k : ℕ, ∃ C, ∀ x, (1 + ‖x‖) ^ k * |F x| ≤ C

/-- Real Schwartz tests are rapidly decreasing. -/
theorem isRapid_schwartz (f : SchwartzMap (Rd d) ℝ) : IsRapid (f : Rd d → ℝ) := by
  refine ⟨f.smooth ⊤, fun k =>
    ⟨2 ^ k * ((Finset.Iic (k, 0)).sup fun m => SchwartzMap.seminorm ℝ m.1 m.2) f, fun x => ?_⟩⟩
  have h := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (k, 0)) (k := k) (n := 0)
    le_rfl le_rfl f x
  rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at h

/-- Tests are rapidly decreasing. -/
theorem isRapid_of_test {F : Rd d → ℝ} (hF : IsTestFunction F) : IsRapid F := by
  refine ⟨hF.1, fun k => ?_⟩
  have hc : HasCompactSupport fun x => (1 + ‖x‖) ^ k * |F x| :=
    (hF.2.comp_left (g := abs) abs_zero).mul_left
  obtain ⟨C, hC⟩ := (((continuous_const.add continuous_norm).pow k).mul
    hF.1.continuous.abs).bounded_above_of_compact_support hc
  exact ⟨C, fun x => (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using hC x)⟩

/-- Auxiliary: `x ↦ (1 + ‖x‖)^{-N}` is Lebesgue integrable on `ℝ^d` for `N > d`. -/
theorem integrable_inv_pow {N : ℕ} (hN : d < N) :
    Integrable (fun x : Rd d => ((1 + ‖x‖) ^ N)⁻¹) volume := by
  have h := integrable_one_add_norm (E := Rd d) (μ := volume) (r := N)
    (by rw [finrank_euclideanSpace_fin]; exact_mod_cast hN)
  refine h.congr (Eventually.of_forall fun x => ?_)
  simp only
  rw [Real.rpow_neg (by positivity), Real.rpow_natCast]

/-- Auxiliary. -/
theorem abs_le_of_decay {F : Rd d → ℝ} {k : ℕ} {C : ℝ}
    (hC : ∀ x, (1 + ‖x‖) ^ k * |F x| ≤ C) (x : Rd d) : |F x| ≤ C * ((1 + ‖x‖) ^ k)⁻¹ := by
  rw [← div_eq_mul_inv, le_div_iff₀ (by positivity), mul_comm]; exact hC x

/-- Rapidly decreasing functions are integrable. -/
theorem IsRapid.integrable {F : Rd d → ℝ} (hF : IsRapid F) : Integrable F volume := by
  obtain ⟨C, hC⟩ := hF.2 (d + 1)
  exact Integrable.mono' ((integrable_inv_pow (N := d + 1) (by omega)).const_mul C)
    hF.1.continuous.aestronglyMeasurable
    (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact abs_le_of_decay hC x)

/-- Auxiliary: `1 + ‖y‖ ≤ (1 + ‖x‖)(1 + ‖x - y‖)`. -/
theorem one_add_norm_le (x y : Rd d) : 1 + ‖y‖ ≤ (1 + ‖x‖) * (1 + ‖x - y‖) := by
  have : ‖y‖ ≤ ‖x‖ + ‖x - y‖ := by
    calc ‖y‖ = ‖x - (x - y)‖ := by rw [sub_sub_cancel]
      _ ≤ ‖x‖ + ‖x - y‖ := norm_sub_le _ _
  nlinarith [norm_nonneg x, norm_nonneg (x - y)]

/-- Auxiliary to the Lean proof route (the TeX's "its covariance correlation pairing converges
against tempered `Γ`", line 191): if `|U(x)| ≤ A (1 + ‖x‖)^{-2N}` with `N > d` and
`(1 + ‖y‖)^{-N}` is `Γ`-integrable, then
`|B_Γ(U,U)| ≤ A² ∫ (1 + ‖x‖)^{-N} dx ∫ (1 + ‖y‖)^{-N} Γ(dy)`. -/
theorem abs_spatialPair_le_weight (Γ : Measure (Rd d)) {N : ℕ} (hN : d < N)
    (hΓN : Integrable (fun y : Rd d => ((1 + ‖y‖) ^ N)⁻¹) Γ) {U : Rd d → ℝ} {A : ℝ}
    (hU : ∀ x, |U x| ≤ A * (((1 + ‖x‖) ^ N)⁻¹) ^ 2) :
    |spatialPair Γ U U| ≤
      A ^ 2 * (∫ x : Rd d, ((1 + ‖x‖) ^ N)⁻¹) * ∫ y, ((1 + ‖y‖) ^ N)⁻¹ ∂Γ := by
  have hWi := integrable_inv_pow (d := d) hN
  set w : Rd d → ℝ := fun x => ((1 + ‖x‖) ^ N)⁻¹ with hw
  have hw0 : ∀ x, 0 ≤ w x := fun x => by simp only [hw]; positivity
  have hw1 : ∀ x, w x ≤ 1 := fun x =>
    inv_le_one_of_one_le₀ (one_le_pow₀ (by linarith [norm_nonneg x]))
  have hwxy : ∀ x y, w x * w (x - y) ≤ w y := by
    intro x y
    simp only [hw]
    rw [← mul_inv, inv_le_inv₀ (by positivity) (by positivity), ← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (one_add_norm_le x y) N
  have hin : ∀ y, ‖∫ x, U x * U (x - y)‖ ≤ A ^ 2 * (∫ x, w x) * w y := by
    intro y
    have hb : ∀ x, ‖U x * U (x - y)‖ ≤ A ^ 2 * w y * w x := by
      intro x
      rw [Real.norm_eq_abs, abs_mul]
      have h1 := hU x
      have h2 := hU (x - y)
      have hA1 : 0 ≤ A * w x ^ 2 := (abs_nonneg _).trans h1
      have hAx : 0 ≤ A ^ 2 * w x := mul_nonneg (sq_nonneg A) (hw0 x)
      calc |U x| * |U (x - y)| ≤ (A * w x ^ 2) * (A * w (x - y) ^ 2) :=
            mul_le_mul h1 h2 (abs_nonneg _) hA1
        _ = A ^ 2 * w x * (w x * w (x - y)) * w (x - y) := by ring
        _ ≤ A ^ 2 * w x * w y * 1 :=
            mul_le_mul (mul_le_mul_of_nonneg_left (hwxy x y) hAx) (hw1 _) (hw0 _)
              (mul_nonneg hAx (hw0 y))
        _ = A ^ 2 * w y * w x := by ring
    refine (norm_integral_le_of_norm_le (hWi.const_mul (A ^ 2 * w y))
      (Eventually.of_forall hb)).trans (le_of_eq ?_)
    rw [integral_const_mul]; ring
  unfold spatialPair
  rw [← Real.norm_eq_abs]
  refine (norm_integral_le_of_norm_le (hΓN.const_mul (A ^ 2 * ∫ x, w x))
    (Eventually.of_forall hin)).trans (le_of_eq ?_)
  rw [integral_const_mul]

/-- Auxiliary: the bump `χ` used for the cutoffs (one on the unit ball, zero outside the
ball of radius 2). -/
def bump : ContDiffBump (0 : Rd d) := ⟨1, 2, one_pos, one_lt_two⟩

/-- The expanding smooth cutoffs `χ_n(x) = χ(x/(n+1))` of the proof (TeX line 190). -/
def cut (n : ℕ) (x : Rd d) : ℝ := bump ((n + 1 : ℝ)⁻¹ • x)

/-- Auxiliary. -/
theorem cut_contDiff (n : ℕ) : ContDiff ℝ ∞ (cut (d := d) n) :=
  bump.contDiff.comp (contDiff_const_smul _)

/-- Auxiliary. -/
theorem cut_hasCompactSupport (n : ℕ) : HasCompactSupport (cut (d := d) n) :=
  bump.hasCompactSupport.comp_smul (inv_ne_zero (by positivity))

/-- Auxiliary. -/
theorem cut_nonneg (n : ℕ) (x : Rd d) : 0 ≤ cut n x := bump.nonneg

/-- Auxiliary. -/
theorem cut_le_one (n : ℕ) (x : Rd d) : cut n x ≤ 1 := bump.le_one

/-- Auxiliary. -/
theorem cut_eq_one {n : ℕ} {x : Rd d} (hx : ‖x‖ ≤ n + 1) : cut n x = 1 := by
  refine bump.one_of_mem_closedBall ?_
  show _ ≤ (1 : ℝ)
  rw [dist_zero_right, norm_smul, norm_inv, Real.norm_eq_abs,
    abs_of_pos (by positivity : (0 : ℝ) < n + 1), ← div_eq_inv_mul,
    div_le_one (by positivity)]
  exact hx

/-- Auxiliary: `F χ_n` is a test. -/
theorem test_mul_cut {F : Rd d → ℝ} (hF : ContDiff ℝ ∞ F) (n : ℕ) :
    IsTestFunction fun x => F x * cut n x :=
  ⟨hF.mul (cut_contDiff n), (cut_hasCompactSupport n).mul_left⟩

/-- Auxiliary: a linear combination of tests is a test. -/
theorem test_add_smul {F G : Rd d → ℝ} (hF : IsTestFunction F) (hG : IsTestFunction G)
    (c : ℝ) : IsTestFunction fun x => F x + c * G x :=
  ⟨hF.1.add (contDiff_const.mul hG.1), hF.2.add hG.2.mul_left⟩

/-- Auxiliary: the tail estimate for the cutoffs of a rapidly decreasing `F`: for
`N₀ ≤ n, m`, `|F(x)(χ_n(x) - χ_m(x))| ≤ C/(N₀+2) · (1 + ‖x‖)^{-2N}`, where
`(1 + ‖x‖)^{2N+1} |F| ≤ C`. -/
theorem abs_cut_diff_le {F : Rd d → ℝ} {N : ℕ} {C : ℝ}
    (hC : ∀ x, (1 + ‖x‖) ^ (2 * N + 1) * |F x| ≤ C) {N₀ n m : ℕ} (hn : N₀ ≤ n)
    (hm : N₀ ≤ m) (x : Rd d) :
    |F x * cut n x + (-1) * (F x * cut m x)| ≤
      C / ((N₀ : ℝ) + 2) * (((1 + ‖x‖) ^ N)⁻¹) ^ 2 := by
  have hC0 : 0 ≤ C := le_trans (by positivity) (hC 0)
  by_cases hx : ‖x‖ ≤ N₀ + 1
  · have h1 : cut n x = 1 := cut_eq_one (by
      have : (N₀ : ℝ) ≤ n := by exact_mod_cast hn
      linarith)
    have h2 : cut m x = 1 := cut_eq_one (by
      have : (N₀ : ℝ) ≤ m := by exact_mod_cast hm
      linarith)
    rw [h1, h2]
    simp only [mul_one, neg_mul, one_mul, add_neg_cancel, abs_zero]
    positivity
  · push Not at hx
    have he : F x * cut n x + (-1) * (F x * cut m x) = F x * (cut n x - cut m x) := by ring
    rw [he, abs_mul]
    have hd : |cut n x - cut m x| ≤ 1 := by
      rw [abs_sub_le_iff]
      constructor <;> linarith [cut_nonneg n x, cut_le_one n x, cut_nonneg m x, cut_le_one m x]
    have hF := abs_le_of_decay hC x
    have hp : 0 < 1 + ‖x‖ := by positivity
    have hk : ((1 + ‖x‖) ^ (2 * N + 1))⁻¹ = (((1 + ‖x‖) ^ N)⁻¹) ^ 2 * (1 + ‖x‖)⁻¹ := by
      have hp' : (1 + ‖x‖) ≠ 0 := hp.ne'
      field_simp
      ring
    have hq : (1 + ‖x‖)⁻¹ ≤ ((N₀ : ℝ) + 2)⁻¹ := by
      rw [inv_le_inv₀ hp (by positivity)]; linarith
    calc |F x| * |cut n x - cut m x| ≤ |F x| * 1 :=
          mul_le_mul_of_nonneg_left hd (abs_nonneg _)
      _ ≤ C * ((1 + ‖x‖) ^ (2 * N + 1))⁻¹ := by rw [mul_one]; exact hF
      _ = C * (((1 + ‖x‖) ^ N)⁻¹) ^ 2 * (1 + ‖x‖)⁻¹ := by rw [hk]; ring
      _ ≤ C * (((1 + ‖x‖) ^ N)⁻¹) ^ 2 * ((N₀ : ℝ) + 2)⁻¹ :=
          mul_le_mul_of_nonneg_left hq (by positivity)
      _ = C / ((N₀ : ℝ) + 2) * (((1 + ‖x‖) ^ N)⁻¹) ^ 2 := by ring

/-- **Rapidly decreasing functions, in particular real Schwartz tests, enter `H_Γ`** (the
"includes Schwartz tests" conclusion of `L:source-spatial-heat`, with the TeX's proof route,
lines 189-192): for tempered `Γ`, `μ` with `IsSpectralMeasure Γ μ` and rapidly decreasing
smooth `F`, the transform `F̂` is in `L²(μ)`, its class lies in `H_Γ`, and it is the `L²(μ)`
limit of the vectors of the expanding smooth cutoffs `F χ_n` (tests). -/
theorem rapid_mem_HGamma {Γ μ : Measure (Rd d)} (hΓ : IsTempered Γ) (hμ : IsTempered μ)
    (hsp : IsSpectralMeasure Γ μ) {F : Rd d → ℝ} (hF : IsRapid F) :
    MemLp (fourierQ F) 2 μ ∧ vec μ F ∈ HGamma μ ∧
      Tendsto (fun n : ℕ => vec μ (fun x => F x * cut n x)) atTop (𝓝 (vec μ F)) := by
  obtain ⟨k, hk⟩ := integrable_weight_of_tempered hΓ
  set N : ℕ := k + d + 1 with hNdef
  have hNd : d < N := by omega
  have hΓN : Integrable (fun y : Rd d => ((1 + ‖y‖) ^ N)⁻¹) Γ := by
    refine Integrable.mono' hk (by fun_prop : Measurable fun y : Rd d =>
      ((1 + ‖y‖) ^ N)⁻¹).aestronglyMeasurable (Eventually.of_forall fun y => ?_)
    rw [Real.norm_of_nonneg (by positivity), inv_le_inv₀ (by positivity) (by positivity)]
    exact pow_le_pow_right₀ (by linarith [norm_nonneg y]) (by omega)
  obtain ⟨C, hC⟩ := hF.2 (2 * N + 1)
  have hC0 : 0 ≤ C := le_trans (by positivity) (hC 0)
  set a : ℕ → Lp ℂ 2 μ := fun n => vec μ (fun x => F x * cut n x) with ha
  have hT : ∀ n, IsTestFunction fun x => F x * cut n x := test_mul_cut hF.1
  set B : ℝ := (∫ x : Rd d, ((1 + ‖x‖) ^ N)⁻¹) * ∫ y, ((1 + ‖y‖) ^ N)⁻¹ ∂Γ with hB
  have hB0 : 0 ≤ B := mul_nonneg (integral_nonneg fun x => by positivity)
    (integral_nonneg fun y => by positivity)
  have hdist : ∀ n m N₀ : ℕ, N₀ ≤ n → N₀ ≤ m →
      dist (a n) (a m) ≤ C * Real.sqrt B / ((N₀ : ℝ) + 2) := by
    intro n m N₀ hn hm
    have hU := test_add_smul (hT n) (hT m) (-1)
    have hdiff : a n - a m = vec μ (fun x => F x * cut n x + (-1) * (F x * cut m x)) := by
      rw [vec_add_smul (test_integrable (hT n)) (test_integrable (hT m))
        (memLp_fourierQ hμ (hT n)) (memLp_fourierQ hμ (hT m)) (-1)]
      simp [ha, sub_eq_add_neg]
    rw [dist_eq_norm, hdiff]
    have hsq := norm_vec_sq hμ hsp hU
    have hb := abs_spatialPair_le_weight Γ hNd hΓN (abs_cut_diff_le hC hn hm)
    have h2 : ‖vec μ (fun x => F x * cut n x + (-1) * (F x * cut m x))‖ ^ 2 ≤
        (C / ((N₀ : ℝ) + 2)) ^ 2 * B := by
      rw [hsq, hB, ← mul_assoc]; exact (le_abs_self _).trans hb
    have h3 := Real.sqrt_le_sqrt h2
    rw [Real.sqrt_sq (norm_nonneg _), Real.sqrt_mul (sq_nonneg _),
      Real.sqrt_sq (by positivity)] at h3
    calc _ ≤ C / ((N₀ : ℝ) + 2) * Real.sqrt B := h3
      _ = C * Real.sqrt B / ((N₀ : ℝ) + 2) := by ring
  have hcs : CauchySeq a := by
    refine cauchySeq_of_le_tendsto_0 (fun N₀ : ℕ => C * Real.sqrt B / ((N₀ : ℝ) + 2)) hdist ?_
    exact Tendsto.div_atTop tendsto_const_nhds
      (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hcs
  have hLmem : L ∈ HGamma μ :=
    (isClosed_HGamma μ).mem_of_tendsto hL (Eventually.of_forall fun n => vec_mem_HGamma μ (hT n))
  -- pointwise convergence of the transforms of the cutoffs
  have hFi := hF.integrable
  have hpt : ∀ ξ, Tendsto (fun n => fourierQ (fun x => F x * cut n x) ξ) atTop
      (𝓝 (fourierQ F ξ)) := by
    intro ξ
    refine tendsto_integral_of_dominated_convergence (fun x => ‖F x‖)
      (fun n => (integrable_mul_ex (test_integrable (hT n)) ξ).aestronglyMeasurable) hFi.norm
      (fun n => Eventually.of_forall fun x => ?_)
      (Eventually.of_forall fun x => ?_)
    · simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      rw [show ‖Complex.exp (Complex.I * (inner ℝ ξ x : ℝ))‖ = 1 from norm_ex ξ x, mul_one,
        abs_of_nonneg (cut_nonneg n x)]
      exact mul_le_of_le_one_right (abs_nonneg _) (cut_le_one n x)
    · refine tendsto_const_nhds.congr' ?_
      obtain ⟨n0, hn0⟩ := exists_nat_ge ‖x‖
      filter_upwards [eventually_ge_atTop n0] with n hn
      rw [cut_eq_one (by
        have : (n0 : ℝ) ≤ n := by exact_mod_cast hn
        linarith), mul_one]
  have hae : ∀ᵐ ξ ∂μ, ∀ n, (a n : Rd d → ℂ) ξ = fourierQ (fun x => F x * cut n x) ξ :=
    ae_all_iff.2 fun n => coeFn_vec (memLp_fourierQ hμ (hT n))
  have hmeas := tendstoInMeasure_of_tendsto_eLpNorm (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    ((Lp.tendsto_Lp_iff_tendsto_eLpNorm' a L).1 hL)
  obtain ⟨ns, hns, hns_ae⟩ := hmeas.exists_seq_tendsto_ae
  have hLeq : (L : Rd d → ℂ) =ᵐ[μ] fourierQ F := by
    filter_upwards [hae, hns_ae] with ξ h1 h2
    refine tendsto_nhds_unique h2 ?_
    simp_rw [h1]
    exact (hpt ξ).comp hns.tendsto_atTop
  have hmem : MemLp (fourierQ F) 2 μ := (Lp.memLp L).ae_eq hLeq
  have hvec : vec μ F = L := Lp.ext ((coeFn_vec hmem).trans hLeq.symm)
  exact ⟨hmem, hvec ▸ hLmem, hvec ▸ hL⟩

/-! ### The heat convolution `p_ε * f` of a test -/

/-- `C_ε f = p_ε * f`, `(p_ε * f)(x) = ∫ f(t) p_ε(x - t) dt`, with the heat density
`p_ε(x) = (2πε)^{-d/2} e^{-|x|²/(2ε)}` (`LowAlphaConvolution.heatDens`), as in
`E:source-heat-definition` (TeX lines 177-179). -/
def heatConv (ε : ℝ) (f : Rd d → ℝ) : Rd d → ℝ :=
  convolution f (heatDens ε) (ContinuousLinearMap.lsmul ℝ ℝ) volume

/-- Auxiliary. -/
theorem heatConv_apply (ε : ℝ) (f : Rd d → ℝ) (x : Rd d) :
    heatConv ε f x = ∫ t, f t * heatDens ε (x - t) := by
  simp only [heatConv, convolution, ContinuousLinearMap.lsmul_apply, smul_eq_mul]

/-- Auxiliary. -/
theorem heatDens_continuous (ε : ℝ) : Continuous (heatDens (d := d) ε) := by
  unfold heatDens; fun_prop

/-- Auxiliary: `p_ε(z) = (2πε)^{-d/2} e^{-(2ε)^{-1}|z|²}`. -/
theorem heatDens_eq (ε : ℝ) (z : Rd d) :
    heatDens ε z = (2 * Real.pi * ε) ^ (-((d : ℝ) / 2)) * Real.exp (-((2 * ε)⁻¹ * ‖z‖ ^ 2)) := by
  unfold heatDens; congr 3; ring

/-- The heat image of a test is smooth and rapidly decreasing (`ε > 0`). -/
theorem isRapid_heatConv {ε : ℝ} (hε : 0 < ε) {f : Rd d → ℝ} (hf : IsTestFunction f) :
    IsRapid (heatConv ε f) := by
  refine ⟨hf.2.contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ) hf.1
    (heatDens_continuous ε).locallyIntegrable, fun k => ?_⟩
  obtain ⟨R, hR⟩ := hf.2.isCompact.isBounded.subset_closedBall (0 : Rd d)
  have hR0 : ∀ t : Rd d, R < ‖t‖ → f t = 0 := fun t ht =>
    image_eq_zero_of_notMem_tsupport fun h => by
      have := hR h; rw [mem_closedBall, dist_zero_right] at this; linarith
  obtain ⟨B, hB⟩ := hf.1.continuous.bounded_above_of_compact_support hf.2
  set c : ℝ := (2 * Real.pi * ε) ^ (-((d : ℝ) / 2)) with hc
  have hc0 : 0 ≤ c := Real.rpow_nonneg (by positivity) _
  set E : ℝ := Real.exp ((k : ℝ) ^ 2 / (4 * (2 * ε)⁻¹)) with hE
  set K : ℝ := B * ((1 + |R|) ^ k * (c * E)) with hK
  refine ⟨K * volume.real (closedBall (0 : Rd d) R), fun x => ?_⟩
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  rw [heatConv_apply, ← abs_of_nonneg (by positivity : (0 : ℝ) ≤ (1 + ‖x‖) ^ k), ← abs_mul,
    ← integral_const_mul, ← Real.norm_eq_abs]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := closedBall (0 : Rd d) R)
    fun t ht => by
      rw [mem_closedBall, dist_zero_right, not_le] at ht
      rw [hR0 t ht, zero_mul, mul_zero]]
  refine norm_setIntegral_le_of_norm_le_const measure_closedBall_lt_top fun t ht => ?_
  rw [mem_closedBall, dist_zero_right] at ht
  have h1 : 1 + ‖x‖ ≤ (1 + |R|) * (1 + ‖x - t‖) := by
    have := one_add_norm_le t x
    rw [norm_sub_rev] at this
    refine this.trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
    linarith [le_abs_self R]
  have h2 : (1 + ‖x‖) ^ k ≤ (1 + |R|) ^ k * (1 + ‖x - t‖) ^ k := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) h1 k
  have h3 := GaussianTest.poly_mul_exp_neg_sq_le k (c := (2 * ε)⁻¹) (by positivity)
    (norm_nonneg (x - t))
  rw [heatDens_eq, ← hc, Real.norm_eq_abs, abs_mul, abs_mul,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ (1 + ‖x‖) ^ k),
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ c * Real.exp (-((2 * ε)⁻¹ * ‖x - t‖ ^ 2)))]
  have hft : |f t| ≤ B := by simpa [Real.norm_eq_abs] using hB t
  calc (1 + ‖x‖) ^ k * (|f t| * (c * Real.exp (-((2 * ε)⁻¹ * ‖x - t‖ ^ 2))))
      ≤ ((1 + |R|) ^ k * (1 + ‖x - t‖) ^ k) *
          (B * (c * Real.exp (-((2 * ε)⁻¹ * ‖x - t‖ ^ 2)))) :=
        mul_le_mul h2 (mul_le_mul_of_nonneg_right hft (by positivity)) (by positivity)
          (by positivity)
    _ = B * ((1 + |R|) ^ k * (c * ((1 + ‖x - t‖) ^ k *
          Real.exp (-((2 * ε)⁻¹ * ‖x - t‖ ^ 2))))) := by ring
    _ ≤ K := by
        rw [hK]
        gcongr

/-- Auxiliary: `∫ p_ε(z) e^{iξ·z} dz = e^{-ε|ξ|²/2}` with integrability (`ε > 0`). -/
theorem heatDens_fourier {ε : ℝ} (hε : 0 < ε) (ξ : Rd d) :
    Integrable (fun z => (heatDens ε z : ℂ) * ex ξ z) volume ∧
      ∫ z, (heatDens ε z : ℂ) * ex ξ z = (gaussFactor ε ξ : ℂ) := by
  have hs : 0 < (2 * ε)⁻¹ := by positivity
  set g := GaussianTest.gaussTest (E := Rd d) (2 * ε)⁻¹ hs 0 0
  have hpt : ∀ z : Rd d, (heatDens ε z : ℂ) * ex ξ z =
      (((2 * Real.pi * ε) ^ (-((d : ℝ) / 2)) : ℝ) : ℂ) *
        (g z * Complex.exp (Complex.I * (inner ℝ ξ z : ℝ))) := by
    intro z
    simp only [g, GaussianTest.gaussTest_apply, inner_zero_left, Complex.ofReal_zero, mul_zero,
      neg_zero, Complex.exp_zero, one_mul, sub_zero, heatDens_eq]
    push_cast; ring
  have hgi : Integrable (fun z => g z * Complex.exp (Complex.I * (inner ℝ ξ z : ℝ))) volume :=
    Integrable.mono' g.integrable.norm
      (g.integrable.aestronglyMeasurable.mul (ex_continuous ξ).aestronglyMeasurable)
      (Eventually.of_forall fun z => by
        rw [norm_mul, show ‖Complex.exp (Complex.I * (inner ℝ ξ z : ℝ))‖ = 1 from norm_ex ξ z,
          mul_one])
  refine ⟨?_, ?_⟩
  · simp_rw [hpt]; exact hgi.const_mul _
  · simp_rw [hpt]
    rw [integral_const_mul, GaussianTest.gaussTest_fourier]
    simp only [sub_zero, inner_zero_right, Complex.ofReal_zero, mul_zero, Complex.exp_zero,
      mul_one]
    have hpi : Real.pi / (2 * ε)⁻¹ = 2 * Real.pi * ε := by field_simp
    rw [hpi, ← mul_assoc, ← Complex.ofReal_mul, ← Real.rpow_add (by positivity),
      neg_add_cancel, Real.rpow_zero, Complex.ofReal_one, one_mul, gaussFactor]
    congr 2
    field_simp
    ring

/-- The heat multiplier on tests: `(p_ε * f)^(ξ) = e^{-ε|ξ|²/2} f̂(ξ)` (the Fourier multiplier
`m_ε` of `C_ε`, TeX lines 192-193), for a test `f` and `ε > 0`. -/
theorem fourierQ_heatConv {ε : ℝ} (hε : 0 < ε) {f : Rd d → ℝ} (hf : IsTestFunction f)
    (ξ : Rd d) : fourierQ (heatConv ε f) ξ = (gaussFactor ε ξ : ℂ) * fourierQ f ξ := by
  obtain ⟨hGi, hG⟩ := heatDens_fourier (d := d) hε ξ
  have hFi := integrable_mul_ex (test_integrable hf) ξ
  have hc := integral_convolution (L := ContinuousLinearMap.mul ℂ ℂ) (μ := volume)
    (ν := volume) hFi hGi
  have hpt : ∀ x, convolution (fun t => (f t : ℂ) * ex ξ t) (fun z => (heatDens ε z : ℂ) * ex ξ z)
      (ContinuousLinearMap.mul ℂ ℂ) volume x = (heatConv ε f x : ℂ) * ex ξ x := by
    intro x
    rw [heatConv_apply, convolution_def, ← integral_complex_ofReal, ← integral_mul_const]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp only [ContinuousLinearMap.mul_apply']
    have he : ex ξ t * ex ξ (x - t) = ex ξ x := by
      simp only [ex, ← Complex.exp_add, inner_sub_right]
      congr 1; push_cast; ring
    push_cast
    rw [← he]; ring
  simp_rw [hpt] at hc
  rw [fourierQ]
  rw [show (fun x => ((heatConv ε f x : ℝ) : ℂ) * Complex.exp (Complex.I * (inner ℝ ξ x : ℝ))) =
    fun x => (heatConv ε f x : ℂ) * ex ξ x from rfl, hc, hG, ContinuousLinearMap.mul_apply',
    mul_comm]
  rfl

/-! ### The heat operator on `L²(μ)` and on `H_Γ` -/

/-- The heat multiplier `m_ε(ξ) = e^{-ε|ξ|²/2}` (TeX line 193), totalized as `1` for `ε ≤ 0`
(through `max ε 0`); every statement about `C_ε` below takes `ε > 0`, where it is
`gaussFactor ε`. -/
def heatMult (ε : ℝ) (ξ : Rd d) : ℝ := gaussFactor (max ε 0) ξ

/-- Auxiliary. -/
theorem heatMult_of_pos {ε : ℝ} (hε : 0 < ε) (ξ : Rd d) : heatMult ε ξ = gaussFactor ε ξ := by
  rw [heatMult, max_eq_left hε.le]

/-- Auxiliary. -/
theorem heatMult_pos (ε : ℝ) (ξ : Rd d) : 0 < heatMult ε ξ := gaussFactor_pos _ _

/-- Auxiliary. -/
theorem heatMult_le_one (ε : ℝ) (ξ : Rd d) : heatMult ε ξ ≤ 1 :=
  gaussFactor_le_one (le_max_right _ _) ξ

/-- Auxiliary. -/
theorem heatMult_continuous (ε : ℝ) : Continuous (heatMult (d := d) ε) := by
  unfold heatMult gaussFactor; fun_prop

variable {μ : Measure (Rd d)}

/-- Auxiliary: `m_ε F ∈ L²(μ)`. -/
theorem memLp_heatMult (ε : ℝ) (F : Lp ℂ 2 μ) :
    MemLp (fun ξ => (heatMult ε ξ : ℂ) * F ξ) 2 μ :=
  (Lp.memLp F).of_le
    ((Complex.continuous_ofReal.comp (heatMult_continuous ε)).aestronglyMeasurable.mul
      (Lp.aestronglyMeasurable F))
    (Eventually.of_forall fun ξ => by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (heatMult_pos ε ξ).le]
      exact mul_le_of_le_one_left (norm_nonneg _) (heatMult_le_one ε ξ))

/-- Auxiliary: multiplication by `m_ε` on `L²(μ; ℂ)` as a real linear map. -/
def heatLin (μ : Measure (Rd d)) (ε : ℝ) : Lp ℂ 2 μ →ₗ[ℝ] Lp ℂ 2 μ where
  toFun F := (memLp_heatMult ε F).toLp _
  map_add' F G := by
    refine Lp.ext ?_
    filter_upwards [(memLp_heatMult ε (F + G)).coeFn_toLp, (memLp_heatMult ε F).coeFn_toLp,
      (memLp_heatMult ε G).coeFn_toLp, Lp.coeFn_add F G,
      Lp.coeFn_add ((memLp_heatMult ε F).toLp _) ((memLp_heatMult ε G).toLp _)]
      with ξ h1 h2 h3 h4 h5
    rw [h5, Pi.add_apply, h1, h2, h3, h4, Pi.add_apply, mul_add]
  map_smul' c F := by
    refine Lp.ext ?_
    filter_upwards [(memLp_heatMult ε (c • F)).coeFn_toLp, (memLp_heatMult ε F).coeFn_toLp,
      Lp.coeFn_smul c F, Lp.coeFn_smul c ((memLp_heatMult ε F).toLp _)]
      with ξ h1 h2 h3 h4
    rw [RingHom.id_apply, h4, Pi.smul_apply, h1, h2, h3, Pi.smul_apply, Complex.real_smul,
      Complex.real_smul]
    ring

/-- Auxiliary. -/
theorem heatLin_ae (ε : ℝ) (F : Lp ℂ 2 μ) :
    (heatLin μ ε F : Rd d → ℂ) =ᵐ[μ] fun ξ => (heatMult ε ξ : ℂ) * F ξ :=
  (memLp_heatMult ε F).coeFn_toLp

/-- Auxiliary. -/
theorem norm_heatLin_le (ε : ℝ) (F : Lp ℂ 2 μ) : ‖heatLin μ ε F‖ ≤ ‖F‖ := by
  refine Lp.norm_le_norm_of_ae_le ?_
  filter_upwards [heatLin_ae ε F] with ξ h
  rw [h, norm_mul, Complex.norm_real, Real.norm_of_nonneg (heatMult_pos ε ξ).le]
  exact mul_le_of_le_one_left (norm_nonneg _) (heatMult_le_one ε ξ)

/-- The heat operator on `L²(μ; ℂ)`: multiplication by `m_ε`, a real continuous linear map. -/
def heatL (μ : Measure (Rd d)) (ε : ℝ) : Lp ℂ 2 μ →L[ℝ] Lp ℂ 2 μ :=
  (heatLin μ ε).mkContinuous 1 fun F => by rw [one_mul]; exact norm_heatLin_le ε F

/-- Auxiliary. -/
theorem heatL_ae (ε : ℝ) (F : Lp ℂ 2 μ) :
    (heatL μ ε F : Rd d → ℂ) =ᵐ[μ] fun ξ => (heatMult ε ξ : ℂ) * F ξ :=
  heatLin_ae ε F

/-- Auxiliary: `I - C_ε` is multiplication by `1 - m_ε`. -/
theorem sub_heatL_ae (ε : ℝ) (F : Lp ℂ 2 μ) :
    ((F - heatL μ ε F : Lp ℂ 2 μ) : Rd d → ℂ) =ᵐ[μ]
      fun ξ => ((1 - heatMult ε ξ : ℝ) : ℂ) * F ξ := by
  filter_upwards [Lp.coeFn_sub F (heatL μ ε F), heatL_ae ε F] with ξ h1 h2
  rw [h1, Pi.sub_apply, h2]; push_cast; ring

/-- Auxiliary: `⟪u, v⟫` on `L²(μ; ℂ)` with a real factor. -/
theorem inner_real_mul (m : ℝ) (a b : ℂ) :
    inner ℝ ((m : ℂ) * a) b = m * inner ℝ a b := by
  simp only [Complex.inner, map_mul, Complex.conj_ofReal]
  rw [show b * ((m : ℂ) * (starRingEnd ℂ) a) = (m : ℂ) * (b * (starRingEnd ℂ) a) by ring,
    Complex.re_ofReal_mul]

/-- Auxiliary. -/
theorem inner_mul_real (m : ℝ) (a b : ℂ) :
    inner ℝ a ((m : ℂ) * b) = m * inner ℝ a b := by
  rw [real_inner_comm, inner_real_mul, real_inner_comm]

/-- `C_ε` is symmetric on `L²(μ; ℂ)`. -/
theorem inner_heatL_left (ε : ℝ) (F G : Lp ℂ 2 μ) :
    inner ℝ (heatL μ ε F) G = inner ℝ F (heatL μ ε G) := by
  rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [heatL_ae ε F, heatL_ae ε G] with ξ h1 h2
  rw [h1, h2, inner_real_mul, inner_mul_real]

/-- `C_ε` is positive on `L²(μ; ℂ)`: `⟪C_ε F, F⟫ = ∫ m_ε |F|² ≥ 0`. -/
theorem inner_heatL_self_nonneg (ε : ℝ) (F : Lp ℂ 2 μ) : 0 ≤ inner ℝ (heatL μ ε F) F := by
  rw [MeasureTheory.L2.inner_def]
  refine integral_nonneg_of_ae ?_
  filter_upwards [heatL_ae ε F] with ξ h
  rw [h, inner_real_mul, real_inner_self_eq_norm_sq]
  exact mul_nonneg (heatMult_pos ε ξ).le (sq_nonneg _)

/-- `‖F - C_ε F‖ ≤ ‖F‖` on `L²(μ; ℂ)`. -/
theorem norm_sub_heatL_le (ε : ℝ) (F : Lp ℂ 2 μ) : ‖F - heatL μ ε F‖ ≤ ‖F‖ := by
  refine Lp.norm_le_norm_of_ae_le ?_
  filter_upwards [sub_heatL_ae ε F] with ξ h
  rw [h, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (by linarith [heatMult_le_one ε ξ])]
  exact mul_le_of_le_one_left (norm_nonneg _) (by linarith [heatMult_pos ε ξ])

/-- `C_ε → I` strongly on `L²(μ; ℂ)` as `ε → 0+` (dominated convergence). -/
theorem tendsto_heatL (F : Lp ℂ 2 μ) :
    Tendsto (fun ε => heatL μ ε F) (𝓝[>] 0) (𝓝 F) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hsq : ∀ ε, ‖heatL μ ε F - F‖ ^ 2 =
      ∫ ξ, (1 - heatMult ε ξ) ^ 2 * ‖F ξ‖ ^ 2 ∂μ := by
    intro ε
    rw [norm_sub_rev, ← real_inner_self_eq_norm_sq, MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [sub_heatL_ae ε F] with ξ h
    rw [h, inner_real_mul, inner_mul_real, real_inner_self_eq_norm_sq]
    ring
  have hFi : Integrable (fun ξ => ‖F ξ‖ ^ 2) μ := by
    have := MeasureTheory.L2.integrable_inner (𝕜 := ℝ) F F
    exact this.congr (Eventually.of_forall fun ξ => real_inner_self_eq_norm_sq _)
  have hlim : Tendsto (fun ε => ∫ ξ, (1 - heatMult ε ξ) ^ 2 * ‖F ξ‖ ^ 2 ∂μ) (𝓝[>] 0)
      (𝓝 (∫ ξ, (0 : ℝ) ∂μ)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun ξ => ‖F ξ‖ ^ 2)
      (Eventually.of_forall fun ε => ?_) (Eventually.of_forall fun ε =>
        Eventually.of_forall fun ξ => ?_) hFi (Eventually.of_forall fun ξ => ?_)
    · exact (((continuous_const.sub (heatMult_continuous ε)).pow 2).aestronglyMeasurable).mul
        hFi.aestronglyMeasurable
    · have h0 := heatMult_pos ε ξ
      have h1 := heatMult_le_one ε ξ
      rw [Real.norm_of_nonneg (by positivity)]
      refine mul_le_of_le_one_left (by positivity) ?_
      nlinarith
    · have hc : Continuous fun ε : ℝ => heatMult ε ξ := by
        unfold heatMult gaussFactor; fun_prop
      have h0 : heatMult 0 ξ = 1 := by simp [heatMult, gaussFactor]
      have := ((hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ))))
      rw [h0] at this
      have := (((tendsto_const_nhds (x := (1 : ℝ))).sub this).pow 2).mul_const (‖F ξ‖ ^ 2)
      simpa using this
  rw [integral_zero] at hlim
  have h2 : Tendsto (fun ε => ‖heatL μ ε F - F‖ ^ 2) (𝓝[>] 0) (𝓝 0) := by
    simp_rw [hsq]; exact hlim
  have h3 := (Real.continuous_sqrt.tendsto 0).comp h2
  rw [Real.sqrt_zero] at h3
  refine h3.congr fun ε => ?_
  simp [Real.sqrt_sq (norm_nonneg _)]

/-- For a test `f` and `ε > 0`, `C_ε (ι f) = ι (p_ε * f)`, the TeX's definition
`C_ε f = p_ε * f` (`E:source-heat-definition`), through `fourierQ_heatConv`. -/
theorem heatL_vec {Γ : Measure (Rd d)} (hΓ : IsTempered Γ) (hμ : IsTempered μ)
    (hsp : IsSpectralMeasure Γ μ) {ε : ℝ} (hε : 0 < ε) {f : Rd d → ℝ}
    (hf : IsTestFunction f) : heatL μ ε (vec μ f) = vec μ (heatConv ε f) := by
  obtain ⟨hm, -, -⟩ := rapid_mem_HGamma hΓ hμ hsp (isRapid_heatConv hε hf)
  refine Lp.ext ?_
  filter_upwards [heatL_ae ε (vec μ f), coeFn_vec (memLp_fourierQ hμ hf), coeFn_vec hm]
    with ξ h1 h2 h3
  rw [h1, h2, h3, fourierQ_heatConv hε hf, heatMult_of_pos hε]

/-- `H_Γ` is invariant under `C_ε` (`ε > 0`). -/
theorem heatL_mem {Γ : Measure (Rd d)} (hΓ : IsTempered Γ) (hμ : IsTempered μ)
    (hsp : IsSpectralMeasure Γ μ) {ε : ℝ} (hε : 0 < ε) {x : Lp ℂ 2 μ} (hx : x ∈ HGamma μ) :
    heatL μ ε x ∈ HGamma μ := by
  have hle : HGamma μ ≤ (HGamma μ).comap (heatL μ ε : Lp ℂ 2 μ →ₗ[ℝ] Lp ℂ 2 μ) := by
    refine Submodule.topologicalClosure_minimal _ ?_ ?_
    · refine Submodule.span_le.2 ?_
      rintro _ ⟨f, hf, rfl⟩
      show heatL μ ε (vec μ f) ∈ HGamma μ
      rw [heatL_vec hΓ hμ hsp hε hf]
      exact (rapid_mem_HGamma hΓ hμ hsp (isRapid_heatConv hε hf)).2.1
    · exact (isClosed_HGamma μ).preimage (heatL μ ε).continuous
  exact hle hx

open Classical in
/-- **The heat operator `C_ε` on `H_Γ`** (`L:source-spatial-heat`): the restriction of
multiplication by `m_ε` to `H_Γ` for `ε > 0` (invariance `heatL_mem`); the identity for
`ε ≤ 0` (a totalization outside the TeX's range `ε > 0`).  The tempered spectral pair
`(Γ, μ)` is part of the data because invariance uses it. -/
def heatH (Γ μ : Measure (Rd d)) (ε : ℝ) : HGamma μ →L[ℝ] HGamma μ :=
  if h : IsTempered Γ ∧ IsTempered μ ∧ IsSpectralMeasure Γ μ ∧ 0 < ε then
    ((heatL μ ε).comp (HGamma μ).subtypeL).codRestrict (HGamma μ) fun x =>
      heatL_mem h.1 h.2.1 h.2.2.1 h.2.2.2 x.2
  else ContinuousLinearMap.id ℝ _

/-- Auxiliary: the values of `C_ε` on `H_Γ`. -/
theorem coe_heatH {Γ : Measure (Rd d)} (hΓ : IsTempered Γ) (hμ : IsTempered μ)
    (hsp : IsSpectralMeasure Γ μ) {ε : ℝ} (hε : 0 < ε) (x : HGamma μ) :
    (heatH Γ μ ε x : Lp ℂ 2 μ) = heatL μ ε x := by
  unfold heatH
  split_ifs with h
  · rfl
  · exact absurd ⟨hΓ, hμ, hsp, hε⟩ h

section HeatOnHGamma

variable {Γ : Measure (Rd d)} (hΓ : IsTempered Γ) (hμ : IsTempered μ)
  (hsp : IsSpectralMeasure Γ μ) {ε : ℝ} (hε : 0 < ε)
include hΓ hμ hsp hε

/-- `C_ε` is symmetric on `H_Γ`. -/
theorem heatH_symm (x y : HGamma μ) :
    inner ℝ (heatH Γ μ ε x) y = inner ℝ x (heatH Γ μ ε y) := by
  rw [Submodule.coe_inner, Submodule.coe_inner, coe_heatH hΓ hμ hsp hε,
    coe_heatH hΓ hμ hsp hε, inner_heatL_left]

/-- `C_ε` is self-adjoint on `H_Γ`. -/
theorem heatH_isSelfAdjoint : IsSelfAdjoint (heatH Γ μ ε) :=
  ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.2 fun x y => heatH_symm hΓ hμ hsp hε x y

/-- `C_ε` is a positive operator on `H_Γ` (self-adjoint with `⟪C_ε x, x⟫ ≥ 0`). -/
theorem heatH_isPositive : (heatH Γ μ ε).IsPositive := by
  refine ContinuousLinearMap.isPositive_def.2
    ⟨fun x y => heatH_symm hΓ hμ hsp hε x y, fun x => ?_⟩
  rw [ContinuousLinearMap.reApplyInnerSelf_apply, Submodule.coe_inner, coe_heatH hΓ hμ hsp hε]
  exact inner_heatL_self_nonneg ε _

/-- `C_ε` is a contraction on `H_Γ`. -/
theorem norm_heatH_le : ‖heatH Γ μ ε‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_
  rw [one_mul, ← Submodule.norm_coe, ← Submodule.norm_coe, coe_heatH hΓ hμ hsp hε]
  exact norm_heatLin_le ε _

/-- `I - C_ε` is a contraction on `H_Γ`. -/
theorem norm_id_sub_heatH_le : ‖ContinuousLinearMap.id ℝ (HGamma μ) - heatH Γ μ ε‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_
  rw [one_mul, sub_apply, ContinuousLinearMap.id_apply, ← Submodule.norm_coe,
    ← Submodule.norm_coe, Submodule.coe_sub, coe_heatH hΓ hμ hsp hε]
  exact norm_sub_heatL_le ε _

/-- On the vector of a test, `C_ε` is the heat convolution: `C_ε (ι f) = ι (p_ε * f)`. -/
theorem heatH_vec {f : Rd d → ℝ} (hf : IsTestFunction f) :
    (heatH Γ μ ε ⟨vec μ f, vec_mem_HGamma μ hf⟩ : Lp ℂ 2 μ) = vec μ (heatConv ε f) := by
  rw [coe_heatH hΓ hμ hsp hε]
  exact heatL_vec hΓ hμ hsp hε hf

end HeatOnHGamma

/-- `C_ε → I` strongly on `H_Γ` as `ε → 0+`. -/
theorem tendsto_heatH {Γ : Measure (Rd d)} (hΓ : IsTempered Γ) (hμ : IsTempered μ)
    (hsp : IsSpectralMeasure Γ μ) (x : HGamma μ) :
    Tendsto (fun ε => heatH Γ μ ε x) (𝓝[>] 0) (𝓝 x) := by
  rw [tendsto_subtype_rng]
  refine (tendsto_heatL (x : Lp ℂ 2 μ)).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (coe_heatH hΓ hμ hsp hε x).symm

/-! ### The TeX's unitary normalization of the pairing -/

/-- The unitary transform of `integrated_covariance_foundation.tex` lines 11-13 at edf7085f:
`\hat f(ξ) = (2π)^{-d/2} ∫ e^{-iξ·x} f(x) dx`. -/
def texHat (f : Rd d → ℝ) (ξ : Rd d) : ℂ :=
  (((2 * Real.pi) ^ (-((d : ℝ) / 2)) : ℝ) : ℂ) *
    ∫ x, (f x : ℂ) * Complex.exp (-(Complex.I * (inner ℝ ξ x : ℝ)))

/-- Auxiliary: `\hat f = (2π)^{-d/2} conj(fourierQ f)` for real `f`. -/
theorem texHat_eq (f : Rd d → ℝ) (ξ : Rd d) :
    texHat f ξ = (((2 * Real.pi) ^ (-((d : ℝ) / 2)) : ℝ) : ℂ) * conj (fourierQ f ξ) := by
  rw [texHat, fourierQ, ← integral_conj]
  congr 2
  funext x
  rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj, map_mul, Complex.conj_I,
    Complex.conj_ofReal]
  ring_nf

/-- **The display of `L:source-spatial-heat` in the TeX's normalization**: for real tests
`f`, `g`, a locally finite even `Γ` and a tempered spectral measure `μ`,
`B_Γ(f,g) = ∫ Γ(dy) ∫ f(x) g(x-y) dx = (2π)^d ∫ \hat f(ξ) conj(\hat g(ξ)) μ(dξ)`. -/
theorem spatialPair_texHat {Γ : Measure (Rd d)} (hsp : IsSpectralMeasure Γ μ)
    {f g : Rd d → ℝ} (hf : IsTestFunction f) (hg : IsTestFunction g) :
    (spatialPair Γ f g : ℂ) =
      (((2 * Real.pi) ^ (d : ℝ) : ℝ) : ℂ) * ∫ ξ, texHat f ξ * conj (texHat g ξ) ∂μ := by
  have hpt : ∀ ξ, texHat f ξ * conj (texHat g ξ) =
      (((2 * Real.pi) ^ (-(d : ℝ)) : ℝ) : ℂ) * conj (fourierQ f ξ * conj (fourierQ g ξ)) := by
    intro ξ
    rw [texHat_eq, texHat_eq, map_mul, map_mul, Complex.conj_ofReal, Complex.conj_conj]
    have h2 : ((2 * Real.pi) ^ (-(d : ℝ)) : ℝ) =
        (2 * Real.pi) ^ (-((d : ℝ) / 2)) * (2 * Real.pi) ^ (-((d : ℝ) / 2)) := by
      rw [← Real.rpow_add (by positivity)]; ring_nf
    rw [h2]; push_cast; ring
  simp_rw [hpt]
  rw [integral_const_mul, integral_conj, ← spatialPair_spectral hsp hf hg, Complex.conj_ofReal,
    ← mul_assoc, ← Complex.ofReal_mul, ← Real.rpow_add (by positivity), add_neg_cancel,
    Real.rpow_zero, Complex.ofReal_one, one_mul]

/-! ### `H_I`: the kernel form and completion of `OccupationCompletion` (one construction) -/

open SpaceTimePositivity (timeMeasure timeMeasure_eq_Icc)
open TimeSchur (kern kern_nonneg measurable_kern kern_sub_comm)

/-- The kernel parameter: `a = α₀` with `0 < a < 1` (TeX: `integrated_intrinsic_constant.tex`
line 5 at edf7085f, `K(s,t) = |s-t|^{-a}` on `I = (0,1)`).  Integration (wave L14): this is
`OccupationCompletion.TParams`, the single temporal parameter of `H_I` in the companion. -/
abbrev KernParams := OccupationCompletion.TParams

section KernelForm

variable {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G]

/-- The kernel form on `L²(I; G)`:
`⟨F,H⟩ = ∫∫_{I²} |s-t|^{-a} ⟪F(s), H(t)⟫ ds dt` (the left side of
`E:positive-bochner-inclusion`, TeX lines 27-31).  Integration (wave L14): this is
`OccupationCompletion.kform` evaluated on representatives of the `L²` classes, so the
companion has one kernel form (`kForm_eq_integral` unfolds it). -/
def kForm (a : ℝ) (F H : Lp G 2 timeMeasure) : ℝ := OccupationCompletion.kform a ⇑F ⇑H

/-- Auxiliary: the kernel form as the Bochner integral over `I²`. -/
theorem kForm_eq_integral (a : ℝ) (F H : Lp G 2 timeMeasure) :
    kForm a F H =
      ∫ q, kern a (q.1 - q.2) * inner ℝ (F q.1) (H q.2) ∂(timeMeasure.prod timeMeasure) :=
  rfl

omit [InnerProductSpace ℝ G] in
/-- Auxiliary (the temporal Schur estimate, `TimeCompletion.cross_integrable`):
`|s-t|^{-a} ‖F(s)‖ ‖H(t)‖` is integrable on `I²` (`a < 1`). -/
theorem kint_norm {a : ℝ} (ha1 : a < 1) (F H : Lp G 2 timeMeasure) :
    Integrable (fun q : ℝ × ℝ => kern a (q.1 - q.2) * (‖F q.1‖ * ‖H q.2‖))
      (timeMeasure.prod timeMeasure) := by
  have hF : MemLp (fun t => ((‖F t‖ : ℝ) : ℂ)) 2 (volume.restrict (Icc (0 : ℝ) 1)) := by
    rw [← timeMeasure_eq_Icc]; exact (Lp.memLp F).norm.ofReal
  have hH : MemLp (fun t => ((‖H t‖ : ℝ) : ℂ)) 2 (volume.restrict (Icc (0 : ℝ) 1)) := by
    rw [← timeMeasure_eq_Icc]; exact (Lp.memLp H).norm.ofReal
  have h := TimeCompletion.cross_integrable ha1 zero_le_one _ _ hF hH
  rw [← timeMeasure_eq_Icc] at h
  refine h.norm.congr (Eventually.of_forall fun q => ?_)
  simp only [norm_mul, Complex.norm_real, RCLike.norm_conj, Real.norm_eq_abs, abs_norm,
    abs_of_nonneg (kern_nonneg _ _)]
  ring

/-- Auxiliary. -/
theorem kForm_aesm (a : ℝ) (F H : Lp G 2 timeMeasure) :
    AEStronglyMeasurable (fun q : ℝ × ℝ => kern a (q.1 - q.2) * inner ℝ (F q.1) (H q.2))
      (timeMeasure.prod timeMeasure) :=
  ((measurable_kern a).comp (measurable_fst.sub measurable_snd)).aestronglyMeasurable.mul
    ((Lp.aestronglyMeasurable F).comp_fst.inner (Lp.aestronglyMeasurable H).comp_snd)

/-- The integrand of the kernel form is integrable (`a < 1`). -/
theorem kint {a : ℝ} (ha1 : a < 1) (F H : Lp G 2 timeMeasure) :
    Integrable (fun q : ℝ × ℝ => kern a (q.1 - q.2) * inner ℝ (F q.1) (H q.2))
      (timeMeasure.prod timeMeasure) :=
  Integrable.mono' (kint_norm ha1 F H) (kForm_aesm a F H) (Eventually.of_forall fun q => by
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (kern_nonneg _ _)]
    exact mul_le_mul_of_nonneg_left (abs_real_inner_le_norm _ _) (kern_nonneg _ _))

/-- Symmetry of the kernel form. -/
theorem kForm_comm (a : ℝ) (F H : Lp G 2 timeMeasure) : kForm a F H = kForm a H F :=
  OccupationCompletion.kform_comm a ⇑H ⇑F

/-- Auxiliary: an a.e. statement on `I` transfers to the first coordinate of `I²`. -/
theorem ae_fst {P : ℝ → Prop} (h : ∀ᵐ t ∂timeMeasure, P t) :
    ∀ᵐ q ∂(timeMeasure.prod timeMeasure), P q.1 :=
  QuasiMeasurePreserving.ae Measure.quasiMeasurePreserving_fst h

/-- Auxiliary: an a.e. statement on `I` transfers to the second coordinate of `I²`. -/
theorem ae_snd {P : ℝ → Prop} (h : ∀ᵐ t ∂timeMeasure, P t) :
    ∀ᵐ q ∂(timeMeasure.prod timeMeasure), P q.2 :=
  QuasiMeasurePreserving.ae Measure.quasiMeasurePreserving_snd h

/-- Additivity of the kernel form in its first argument. -/
theorem kForm_add_left {a : ℝ} (ha1 : a < 1) (F F' H : Lp G 2 timeMeasure) :
    kForm a (F + F') H = kForm a F H + kForm a F' H := by
  rw [kForm_eq_integral, kForm_eq_integral, kForm_eq_integral]
  rw [← integral_add (kint ha1 F H) (kint ha1 F' H)]
  refine integral_congr_ae ?_
  filter_upwards [ae_fst (Lp.coeFn_add F F')] with q hq
  rw [hq, Pi.add_apply, inner_add_left, mul_add]

/-- Homogeneity of the kernel form in its first argument. -/
theorem kForm_smul_left (a c : ℝ) (F H : Lp G 2 timeMeasure) :
    kForm a (c • F) H = c * kForm a F H := by
  rw [kForm_eq_integral, kForm_eq_integral]
  rw [← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [ae_fst (Lp.coeFn_smul c F)] with q hq
  rw [hq, Pi.smul_apply, real_inner_smul_left]
  ring

/-- **Positivity of the kernel form on `L²(I; G)`** (`0 < a < 1`): this is
`OccupationCompletion.kform_self_nonneg` (the Gamma-subordination mixture
`|s-t|^{-a} = ∫ ρ(w) φ_w(s) φ_w(t) dν(w)` and Fubini with Bochner integrals in `G`). -/
theorem kForm_self_nonneg [CompleteSpace G] {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    (F : Lp G 2 timeMeasure) :
    0 ≤ kForm a F F :=
  OccupationCompletion.kform_self_nonneg ha0 ha1 (Lp.memLp F)

end KernelForm

section Completion

variable (p : KernParams) (G : Type*) [NormedAddCommGroup G] [InnerProductSpace ℝ G]
  [CompleteSpace G]

/-- **The covariance space `H_I`** for spatial factor `G`: Mathlib's completion of `L²(I; G)`
for the seminorm `⟨F,F⟩^{1/2}` of the kernel form (the null quotient is part of the
completion).  Integration (wave L14): this is `OccupationCompletion.HK p G`, the single
completion of the companion (`OccupationCompletion.HI p S = HK p (Hsp S)` is the same
construction with the test-completion spatial factor).  It is the `Lp G 2` completion of wave
L14 decision 4; it is not identified with a Hilbert tensor product `H_t ⊗ G`. -/
abbrev HI : Type _ := OccupationCompletion.HK p G

/-- The map `J_G : L²(I; G) → H_I`, i.e. `OccupationCompletion.J p G`. -/
def JI (F : Lp G 2 timeMeasure) : HI p G := OccupationCompletion.J p G F

variable {p G}

/-- `⟪J F, J H⟫_{H_I} = ∫∫ |s-t|^{-a} ⟪F(s), H(t)⟫ ds dt`. -/
theorem inner_JI (F H : Lp G 2 timeMeasure) :
    inner ℝ (JI p G F) (JI p G H) = kForm p.a F H := by
  rw [JI, JI, OccupationCompletion.J_apply, OccupationCompletion.J_apply]
  exact OccupationCompletion.inner_Jlin F H

end Completion

/-! ### The finite covariance vectors `k_i` of `L:positive-physical-gram` -/

/-- Auxiliary: `timeMeasure` is finite on every set. -/
theorem timeMeasure_ne_top (A : Set ℝ) : timeMeasure A ≠ ⊤ := by
  refine ne_top_of_le_ne_top ?_ (measure_mono (subset_univ A))
  rw [Measure.restrict_apply_univ, Real.volume_Ioo]; exact ENNReal.ofReal_ne_top

section Step

variable {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G]

/-- The temporal step vector `h_A ⊗ v = (1_A/|A|) v` in `L²(I; G)` (TeX: `h_i = 1_{I_i}/ℓ_i`,
`integrated_intrinsic_constant.tex` lines 149-151). -/
def stepVec (A : Set ℝ) (hA : MeasurableSet A) (v : G) : Lp G 2 timeMeasure :=
  indicatorConstLp 2 hA (timeMeasure_ne_top A) ((volume.real A)⁻¹ • v)

/-- The temporal pairing `⟨h_A, h_B⟩_{H_t} = ∫∫_{I²} |s-t|^{-a} h_A(s) h_B(t) ds dt`. -/
def tPair (a : ℝ) (A B : Set ℝ) : ℝ :=
  ∫ q, kern a (q.1 - q.2) * (A.indicator (fun _ => (volume.real A)⁻¹) q.1 *
    B.indicator (fun _ => (volume.real B)⁻¹) q.2) ∂(timeMeasure.prod timeMeasure)

/-- The kernel form of two step vectors factors:
`⟨h_A ⊗ v, h_B ⊗ w⟩ = ⟨h_A, h_B⟩_{H_t} ⟪v, w⟫_G`. -/
theorem kForm_stepVec (a : ℝ) {A B : Set ℝ} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (v w : G) : kForm a (stepVec A hA v) (stepVec B hB w) = tPair a A B * inner ℝ v w := by
  rw [kForm_eq_integral]
  unfold tPair
  rw [← integral_mul_const]
  refine integral_congr_ae ?_
  filter_upwards [ae_fst (indicatorConstLp_coeFn (p := 2) (hs := hA)
      (hμs := timeMeasure_ne_top A) (c := (volume.real A)⁻¹ • v)),
    ae_snd (indicatorConstLp_coeFn (p := 2) (hs := hB)
      (hμs := timeMeasure_ne_top B) (c := (volume.real B)⁻¹ • w))] with q h1 h2
  rw [stepVec, stepVec, h1, h2]
  by_cases a1 : q.1 ∈ A
  · by_cases b1 : q.2 ∈ B
    · simp [Set.indicator, a1, b1, real_inner_smul_left, real_inner_smul_right]; ring
    · simp [Set.indicator, a1, b1]
  · simp [Set.indicator, a1]

end Step

variable {μ : Measure (Rd d)}

open Classical in
/-- The spatial vector of a real function in `H_Γ` (`ι q` when it lies in `H_Γ`, which holds
for every test, `coe_spatialVec`; `0` otherwise, a totalization). -/
def spatialVec (μ : Measure (Rd d)) (q : Rd d → ℝ) : HGamma μ :=
  if h : vec μ q ∈ HGamma μ then ⟨vec μ q, h⟩ else 0

/-- Auxiliary. -/
theorem coe_spatialVec {q : Rd d → ℝ} (hq : IsTestFunction q) :
    (spatialVec μ q : Lp ℂ 2 μ) = vec μ q := by
  simp [spatialVec, vec_mem_HGamma μ hq]

/-- **The covariance vector** `k = h_A ⊗ q ∈ H_I` (`H_I` with spatial factor `H_Γ`): for a
cell `A` and a spatial test `q`, `J(h_A ⊗ ι q)`. -/
def gramVec (p : KernParams) (μ : Measure (Rd d)) (A : Set ℝ) (hA : MeasurableSet A)
    (q : Rd d → ℝ) : HI p (HGamma μ) :=
  JI p (HGamma μ) (stepVec A hA (spatialVec μ q))

/-- **The Gram entries factor** (`L:positive-physical-gram`, proof lines 187-189): for cells
`A`, `B`, spatial tests `q`, `q'`, a tempered spectral measure `μ` of an even `Γ`,
`⟨h_A ⊗ q, h_B ⊗ q'⟩_{H_I} = ⟨h_A, h_B⟩_{H_t} B_Γ(q, q')`. -/
theorem inner_gramVec (p : KernParams) {Γ : Measure (Rd d)} (hE : IsEven Γ) (hμ : IsTempered μ)
    (hsp : IsSpectralMeasure Γ μ)
    {A B : Set ℝ} (hA : MeasurableSet A) (hB : MeasurableSet B) {q q' : Rd d → ℝ}
    (hq : IsTestFunction q) (hq' : IsTestFunction q') :
    inner ℝ (gramVec p μ A hA q) (gramVec p μ B hB q') = tPair p.a A B * spatialPair Γ q q' := by
  rw [gramVec, gramVec, inner_JI, kForm_stepVec, Submodule.coe_inner, coe_spatialVec hq,
    coe_spatialVec hq', inner_vec hμ hsp hq hq',
    SpatialFourLinear.spatialPair_comm hE hq.1.continuous hq'.1.continuous hq'.2]

/-- **The Grams are symmetric positive semidefinite** (`L:positive-physical-gram`, line 187):
for any finite family of covariance vectors `k_i ∈ H_I`, the matrix `⟨k_i, k_j⟩` is positive
semidefinite (`Matrix.posSemidef_gram`). -/
theorem gram_posSemidef {ι : Type*} [Fintype ι] {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (k : ι → E) :
    (Matrix.of fun i j => inner ℝ (k i) (k j)).PosSemidef := by
  have h := Matrix.posSemidef_gram ℝ k
  convert h using 1
  ext i j
  rw [Matrix.gram_apply, Matrix.of_apply]

/-! ### The manuscript wrappers -/

/-- **`L:source-spatial-heat`** (`integrated_source_convergence.tex` lines 169-202 at edf7085f),
with the section's standing hypotheses (`H:homog`; `Γ ≠ 0`, carried, unused).  `H_Γ` is the
closure of the vectors of the real tests in `L²(μ; ℂ)` (`HGamma`, the null-quotient
completion through the isometry `vec`), and `C_ε = heatH Γ μ ε`.
1. The display: on real tests `⟪ι f, ι g⟫ = B_Γ(f,g)
   = ∫ Γ(dy) ∫ f(x) g(x-y) dx = (2π)^d ∫ \hat f conj(\hat g) dμ` (TeX normalization).
2. `H_Γ` is closed in `L²(μ; ℂ)` (so complete) and separable.
3. Real Schwartz tests enter `H_Γ`: `\hat f ∈ L²(μ)`, `ι f ∈ H_Γ`, and `ι f` is the limit of
   the vectors of the expanding smooth cutoffs `f χ_n`.
4. For `ε > 0`: `C_ε` is positive and self-adjoint, `‖C_ε‖ ≤ 1`, `‖I - C_ε‖ ≤ 1`, and on
   tests `C_ε (ι f) = ι (p_ε * f)` (`E:source-heat-definition`).
5. `C_ε → I` strongly as `ε → 0+`. -/
theorem source_spatial_heat_paper {alpha alpha0 : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogCovariance d alpha alpha0 Γ μ) (_hΓ0 : Γ ≠ 0) :
    (∀ f g : Rd d → ℝ, IsTestFunction f → IsTestFunction g →
      inner ℝ (vec μ f) (vec μ g) = spatialPair Γ f g ∧
      (spatialPair Γ f g : ℂ) =
        (((2 * Real.pi) ^ (d : ℝ) : ℝ) : ℂ) * ∫ ξ, texHat f ξ * conj (texHat g ξ) ∂μ) ∧
    IsClosed (HGamma μ : Set (Lp ℂ 2 μ)) ∧ TopologicalSpace.SeparableSpace (HGamma μ) ∧
    (∀ f : SchwartzMap (Rd d) ℝ, MemLp (fourierQ f) 2 μ ∧ vec μ f ∈ HGamma μ ∧
      Tendsto (fun n : ℕ => vec μ (fun x => f x * cut n x)) atTop (𝓝 (vec μ f))) ∧
    (∀ ε : ℝ, 0 < ε → (heatH Γ μ ε).IsPositive ∧ IsSelfAdjoint (heatH Γ μ ε) ∧
      ‖heatH Γ μ ε‖ ≤ 1 ∧ ‖ContinuousLinearMap.id ℝ (HGamma μ) - heatH Γ μ ε‖ ≤ 1 ∧
      ∀ (f : Rd d → ℝ) (hf : IsTestFunction f),
        (heatH Γ μ ε ⟨vec μ f, vec_mem_HGamma μ hf⟩ : Lp ℂ 2 μ) = vec μ (heatConv ε f)) ∧
    (∀ x : HGamma μ, Tendsto (fun ε => heatH Γ μ ε x) (𝓝[>] 0) (𝓝 x)) := by
  have := hH.μ_radon
  have hΓ := hH.Γ_tempered
  have hμ := hH.μ_tempered
  have hsp := hH.spectral
  refine ⟨fun f g hf hg => ⟨?_, spatialPair_texHat hsp hf hg⟩, isClosed_HGamma μ,
    separableSpace_HGamma μ, fun f => rapid_mem_HGamma hΓ hμ hsp (isRapid_schwartz f),
    fun ε hε => ⟨heatH_isPositive hΓ hμ hsp hε, heatH_isSelfAdjoint hΓ hμ hsp hε,
      norm_heatH_le hΓ hμ hsp hε, norm_id_sub_heatH_le hΓ hμ hsp hε,
      fun f hf => heatH_vec hΓ hμ hsp hε hf⟩, tendsto_heatH hΓ hμ hsp⟩
  rw [inner_vec hμ hsp hf hg,
    SpatialFourLinear.spatialPair_comm hH.Γ_even hf.1.continuous hg.1.continuous hg.2]

/-- **`L:positive-physical-gram`, narrower** (`integrated_intrinsic_constant.tex` lines 143-196
at edf7085f), with the section's standing hypotheses (`H:homog`, `a = α₀`, `Γ ≠ 0`) and the
lemma's own data: cells `A_i` (measurable, inside `I = (0,1)`, nonempty, disjoint, lengths
`ℓ_i > 0` summing to one), real tests `f_i` with `‖f_i‖₂ = 1`, and the mask
`m_R(x) = η(x/R)²` of the fixed cutoff `η` (smooth, `0 ≤ η ≤ 1`, one on the unit ball, zero
outside the ball of radius two), `R ≥ 1`.  With `h_i = 1_{A_i}/ℓ_i`,
`k_i^R = J(h_i ⊗ ι(m_R f_i²))`, `k_i^∞ = J(h_i ⊗ ι(f_i²))` in `H_I = HI ⟨α₀,…⟩ (HGamma μ)`:
1. the entries factor, `⟨k_i^R, k_j^R⟩ = ⟨h_i, h_j⟩_{H_t} B_Γ(m_R f_i², m_R f_j²)` and
   `⟨k_i^∞, k_j^∞⟩ = ⟨h_i, h_j⟩_{H_t} B_Γ(f_i², f_j²)`;
2. both Grams `C^R`, `D` are symmetric positive semidefinite.
Not formalized: the label row `E:positive-label-row` (it needs the uniform mean operator
`T_R` and the multiplier form `v_L`, not in the companion) and the entrywise order
`0 ≤ C^R_{ij} ≤ D_{ij}` (excluded by wave L14 decision 5, adjacent to board item B3). -/
theorem positive_physical_gram_paper {alpha alpha0 : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogCovariance d alpha alpha0 Γ μ) (_hΓ0 : Γ ≠ 0)
    {ι : Type*} [Fintype ι] (A : ι → Set ℝ) (hA : ∀ i, MeasurableSet (A i))
    (_hAI : ∀ i, A i ⊆ Ioo 0 1) (_hdisj : Pairwise (Function.onFun Disjoint A))
    (_hne : ∀ i, (A i).Nonempty) (_hpos : ∀ i, 0 < volume.real (A i))
    (_hsum : ∑ i, volume.real (A i) = 1)
    (f : ι → Rd d → ℝ) (hf : ∀ i, IsTestFunction (f i)) (_hf2 : ∀ i, ∫ x, f i x ^ 2 = 1)
    (η : Rd d → ℝ) (hη : ContDiff ℝ ∞ η) (_hη01 : ∀ x, 0 ≤ η x ∧ η x ≤ 1)
    (_hη1 : ∀ x, ‖x‖ ≤ 1 → η x = 1) (_hη2 : ∀ x, 2 < ‖x‖ → η x = 0) {R : ℝ} (_hR : 1 ≤ R) :
    let p : KernParams := ⟨alpha0, hH.alpha0_pos, hH.alpha0_lt_one⟩
    let qR : ι → Rd d → ℝ := fun i x => η (R⁻¹ • x) ^ 2 * f i x ^ 2
    let qI : ι → Rd d → ℝ := fun i x => f i x ^ 2
    let kR : ι → HI p (HGamma μ) := fun i => gramVec p μ (A i) (hA i) (qR i)
    let kI : ι → HI p (HGamma μ) := fun i => gramVec p μ (A i) (hA i) (qI i)
    (∀ i j, inner ℝ (kR i) (kR j) = tPair alpha0 (A i) (A j) * spatialPair Γ (qR i) (qR j)) ∧
    (∀ i j, inner ℝ (kI i) (kI j) = tPair alpha0 (A i) (A j) * spatialPair Γ (qI i) (qI j)) ∧
    (Matrix.of fun i j => inner ℝ (kR i) (kR j)).PosSemidef ∧
    (Matrix.of fun i j => inner ℝ (kI i) (kI j)).PosSemidef := by
  intro p qR qI kR kI
  have hqI : ∀ i, IsTestFunction (qI i) := fun i => SpatialFourLinear.isTest_sq (hf i)
  have hqR : ∀ i, IsTestFunction (qR i) := fun i =>
    ⟨((hη.comp (contDiff_const_smul _)).pow 2).mul (hqI i).1, (hqI i).2.mul_left⟩
  exact ⟨fun i j => inner_gramVec p hH.Γ_even hH.μ_tempered hH.spectral (hA i) (hA j)
      (hqR i) (hqR j),
    fun i j => inner_gramVec p hH.Γ_even hH.μ_tempered hH.spectral (hA i) (hA j)
      (hqI i) (hqI j),
    gram_posSemidef kR, gram_posSemidef kI⟩

end StratonovichHAMSecondMoment.SourceHeatGram
