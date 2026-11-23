module

/-
Copyright 2026 Le Chen. SPDX-License-Identifier: Apache-2.0

Wave L14, item K1a: the completion spaces of `L:positive-raw-embedding`
(`notes/integrated_intrinsic_constant.tex`, statement lines 23-40, proof 42-132 at revision
edf7085f) and `L:occupation-raw-square` (`notes/integrated_occupation_ceiling.tex`, statement
lines 24-43, proof 45-108), built as `L²` completions with no tensor identification (decision 4
of waves L9 and L14).  `H_sp` follows `notes/integrated_cameron_mean.tex` lines 8-11.

Objects (new):
* `kform a F F' = ∫∫_{I²} |s-t|^{-a} ⟨F(s), F'(t)⟩_G` on `G`-valued functions, `I = (0,1)`;
* `HK p G`: the completion of `L²(I; G)` under `kform` (the TeX's `H_t ⊗ G`); `Ht p = HK p ℝ`;
  `J p G : L²(I; G) →L[ℝ] HK p G` (the TeX's `J_G`);
* `Hsp S`: the completion of `C_c^∞(ℝ^d)` under `B_Γ` (`SpatialFourierBound.spatialPair`);
  `toHsp S φ` the class of a test function;
* `HI p S = HK p (Hsp S)` (the TeX's `H_I`), `incl p S Ψ = J(s ↦ [Ψ_s])` (the inclusion of
  `C_pos`);
* `Q S f = lim [f_n²]` for test functions `f_n → f` in `H¹` (the TeX's `Q`), `sqField S G` the
  field `s ↦ Q(g_s)`, `rho p S G = J(s ↦ Q(g_s))` (the TeX's `ρ_g`); `testSqPair S φ f` the signed
  physical pairing `B_Γ(φ, f²)`.
Reused: `TimeSchur.kern`, `OccupationCeilingFinite.K0` (`K_0 = 2^a/(1-a)`),
`TimeCompletion.kern_eq_mixture` (positivity), `SpaceTimePositivity` (`timeMeasure`, `stForm`,
`stForm_self_eq_rawCost`, local bounds), `SpatialFourLinear` (`C₄`, its bounds and continuity,
`SquareBound`), `OccupationPhysicalClass` (`IsOccField`, `sqPair`, `lintegral_rpow_le`),
`RawOccupationEnergy` (`A`, `Araw`), `H1Density.h1TestDense`.

Formalized (headline theorems):
* `positive_raw_embedding_paper` (`L:positive-raw-embedding`, narrower):
  `E:positive-bochner-inclusion` for every real Hilbert space `G` (integrability,
  `‖J_G F‖² = ∫∫ K ⟨F(s),F(t)⟩ ≤ K_0 ‖F‖²`) and the first identity `‖Ψ‖²_{H_I} = v_Ψ` of
  `E:positive-raw-mean` for `Ψ ∈ C_pos`.  Missing: the mean identity
  `T_R Ψ(s) = B_E(m_R h_{Ψ,s})` and the canonical-version sentence (lines 36-39), i.e. the
  Bochner-integral paragraph (71-80) and the `E`-row paragraph (116-131).
* `occupation_raw_square_paper` (`L:occupation-raw-square`, narrower): `Q : H¹ → H_sp` with
  `⟨Q f, Q h⟩ = B_Γ(f², h²)`, `‖Q f‖² = A_sp(f)`, sequential continuity and a.e.-class
  invariance; for `g ∈ 𝒪` (joint representatives) `s ↦ Q(g_s) ∈ L²(I; H_sp)`, `ρ_g ∈ H_I`,
  `‖ρ_g‖² = A(g)`, `⟨Ψ, ρ_g⟩ = ∫∫ |s-t|^{-a} B_Γ(Ψ_s, g_t²)`, `⟨Ψ, ρ_g⟩ ≤ √(v_Ψ A(g))`, and
  the second identity of `E:occupation-raw-identities`, `⟨Ψ,ρ_g⟩ = ∫_I ∫ h_{Ψ,s} g_s²` (with the
  integrability of its inner and outer integrands; evenness/Tonelli step of lines 102-105).
  Missing: the class `𝒪` as strongly `H¹`-measurable fields (joint representatives here, as in
  L7/L9, until item L14-O); topological continuity of `Q` (sequential form only; the package
  has no `H¹` type); `ρ_g` lies in the kernel completion `HI` of `L²(I; H_sp)`, whose
  identification with the TeX's "original `H_I`" (the completion of space-time tests) is not
  formalized (decision 4).
* Also: `kform_self_nonneg` (positivity of the kernel form on all of `L²(I; G)`),
  `separableSpace_Hsp`, `sqField_aestronglyMeasurable`.

Supplied inputs: none.  `SquareBound Γ α R_0` is `SpatialFourLinear.squareBound_R0` with
`H1Density.h1TestDense`, `SquarePairingBounds Γ α R_0` is
`SpatialOccupationL7Completed.squarePairingBounds_holds` (both under `H:homog`, `Γ ≠ 0`).

Implicit hypotheses made explicit: `0 < a < 1` (`TParams`; positivity needs `a > 0`,
integrability `a < 1`); `Γ` locally finite, even, with a spectral measure (`SpData`); `H¹` profiles
are pairs `(f, g)` with `g` an `L²` weak gradient (`SpatialFourLinear.IsH1Pair`); integrability of
every integral in a conclusion is stated or proved (`kform_integrable`).  Total definitions take
junk values off their domain (`toHsp` of a non-test is `0`, `Q` off `H¹` is the limit of the zero
sequence, `incl` of a non-smooth field and `rho` of a field with `s ↦ Q(g_s) ∉ L²` are `0`); every
theorem assumes the domain.

Proof route and differences from the TeX:
* positivity of the kernel form by the Gamma-subordination mixture for `G`-valued `L²` fields
  directly (`inner_form_nonneg_of_mixture`), instead of scalar tests, finite tensors and simple
  fields;
* `J_G` is defined on all of `L²(I; G)` by completing `L²(I; G)` itself, so no extension step is
  needed; `H_t ⊗ G` is not identified with a tensor product (decision 4);
* `Q` is well defined and continuous by the continuity of `C₄` (`SpatialFourLinear.C4_tendsto`)
  along sequences, instead of the explicit difference bound of lines 57-61;
* strong measurability of `s ↦ Q(g_s)` from a joint representative: `H_sp` is separable (tests
  on balls are `L²`-Lipschitz into `H_sp`, `spatialPair_self_le_L2`), and the distances to the
  dense test classes are measurable (`measurable_of_dist_dense`), instead of the TeX's continuity
  of `Q` on strongly `H¹`-measurable fields;
* `⟨[φ], Q(f)⟩ = B_Γ(φ, f²)` as in the TeX (a test `χ = 1` on the support of `φ` and `C₄`);
* the second identity of `E:occupation-raw-identities` as in the TeX (polarized form, evenness
  of `Γ`, Tonelli), carried out on `[0,∞]`-valued lower integrals (`lintegral_kern_pair_even`)
  and converted back with the finiteness given by the Schur-integrable polarized integrand.

Lemmas whose doc comments say "Auxiliary" have no manuscript label.
-/
public import Mathlib
public import StratonovichHAMSecondMoment.SpaceTimePositivity
public import StratonovichHAMSecondMoment.RawOccupationEnergy
public import StratonovichHAMSecondMoment.SpatialOccupationL7Completed

@[expose] public section

noncomputable section

set_option autoImplicit false

open MeasureTheory Set Filter Metric Topology
open scoped ContDiff ENNReal RealInnerProductSpace

namespace StratonovichHAMSecondMoment.OccupationCompletion

open HomogHypothesis (Rd HomogCovariance IsSpectralMeasure IsEven)
open TimeSchur (kern kern_nonneg measurable_kern kern_sub_comm)
open SpaceTimePositivity (timeMeasure timeMeasure_eq_Icc)
open OccupationCeilingFinite (K0 K0_pos)

/-! ### The temporal Schur bound with the sharp constant `K_0` -/

/-- Auxiliary to the Lean proof route (the Schur step of `L:positive-raw-embedding`,
`integrated_intrinsic_constant.tex` lines 52-59 at edf7085f, in Tonelli form): for
`0 ≤ a < 1` and an a.e.-measurable `g : ℝ → [0,∞]` on `I = (0,1)`,
`∫∫_{I²} g(s) g(t) |s-t|^{-a} ≤ K_0 ∫_I g²`, `K_0 = 2^a/(1-a)`. -/
theorem schur_K0 {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) (g : ℝ → ℝ≥0∞)
    (hg : AEMeasurable g timeMeasure) :
    ∫⁻ p : ℝ × ℝ, g p.1 * g p.2 * ENNReal.ofReal (kern a (p.1 - p.2))
        ∂(timeMeasure.prod timeMeasure) ≤
      ENNReal.ofReal (K0 a) * ∫⁻ t, g t ^ 2 ∂timeMeasure := by
  set μ := timeMeasure
  set R := ENNReal.ofReal (K0 a)
  have hk : Measurable fun p : ℝ × ℝ => ENNReal.ofReal (kern a (p.1 - p.2)) :=
    ENNReal.measurable_ofReal.comp ((measurable_kern a).comp (measurable_fst.sub measurable_snd))
  have hf1 : AEMeasurable (fun p : ℝ × ℝ => g p.1) (μ.prod μ) := hg.comp_fst
  have hf2 : AEMeasurable (fun p : ℝ × ℝ => g p.2) (μ.prod μ) := hg.comp_snd
  have hg1 : AEMeasurable (fun p : ℝ × ℝ => g p.1 ^ 2 * ENNReal.ofReal (kern a (p.1 - p.2)))
      (μ.prod μ) := (hf1.pow_const 2).mul hk.aemeasurable
  have hg2 : AEMeasurable (fun p : ℝ × ℝ => g p.2 ^ 2 * ENNReal.ofReal (kern a (p.1 - p.2)))
      (μ.prod μ) := (hf2.pow_const 2).mul hk.aemeasurable
  have hrow : ∀ x ∈ Ioo (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (kern a (x - y)) ∂μ ≤ R :=
    fun x hx => OccupationCeilingFinite.row_le ha0 ha1 (Ioo_subset_Icc_self hx)
  have hA : ∫⁻ p : ℝ × ℝ, g p.1 ^ 2 * ENNReal.ofReal (kern a (p.1 - p.2)) ∂(μ.prod μ) ≤
      R * ∫⁻ t, g t ^ 2 ∂μ := by
    rw [lintegral_prod _ hg1]
    calc ∫⁻ x, ∫⁻ y, g x ^ 2 * ENNReal.ofReal (kern a (x - y)) ∂μ ∂μ
        = ∫⁻ x, g x ^ 2 * ∫⁻ y, ENNReal.ofReal (kern a (x - y)) ∂μ ∂μ := by
          refine lintegral_congr fun x => ?_
          exact lintegral_const_mul _ (ENNReal.measurable_ofReal.comp
            ((measurable_kern a).comp (measurable_const.sub measurable_id)))
      _ ≤ ∫⁻ x, g x ^ 2 * R ∂μ := by
          refine lintegral_mono_ae ?_
          filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
          gcongr
          exact hrow x hx
      _ = R * ∫⁻ t, g t ^ 2 ∂μ := by
          rw [lintegral_mul_const'' _ (hg.pow_const 2), mul_comm]
  have hB : ∫⁻ p : ℝ × ℝ, g p.2 ^ 2 * ENNReal.ofReal (kern a (p.1 - p.2)) ∂(μ.prod μ) ≤
      R * ∫⁻ t, g t ^ 2 ∂μ := by
    rw [lintegral_prod_symm _ hg2]
    calc ∫⁻ y, ∫⁻ x, g y ^ 2 * ENNReal.ofReal (kern a (x - y)) ∂μ ∂μ
        = ∫⁻ y, g y ^ 2 * ∫⁻ x, ENNReal.ofReal (kern a (y - x)) ∂μ ∂μ := by
          refine lintegral_congr fun y => ?_
          simp_rw [kern_sub_comm a _ y]
          exact lintegral_const_mul _ (ENNReal.measurable_ofReal.comp
            ((measurable_kern a).comp (measurable_const.sub measurable_id)))
      _ ≤ ∫⁻ y, g y ^ 2 * R ∂μ := by
          refine lintegral_mono_ae ?_
          filter_upwards [ae_restrict_mem measurableSet_Ioo] with y hy
          gcongr
          exact hrow y hy
      _ = R * ∫⁻ t, g t ^ 2 ∂μ := by
          rw [lintegral_mul_const'' _ (hg.pow_const 2), mul_comm]
  have h2 : 2 * ∫⁻ p : ℝ × ℝ, g p.1 * g p.2 * ENNReal.ofReal (kern a (p.1 - p.2)) ∂(μ.prod μ)
      ≤ 2 * (R * ∫⁻ t, g t ^ 2 ∂μ) := by
    rw [← lintegral_const_mul' _ _ (by norm_num)]
    calc ∫⁻ p : ℝ × ℝ, 2 * (g p.1 * g p.2 * ENNReal.ofReal (kern a (p.1 - p.2))) ∂(μ.prod μ)
        ≤ ∫⁻ p : ℝ × ℝ, (g p.1 ^ 2 * ENNReal.ofReal (kern a (p.1 - p.2)) +
            g p.2 ^ 2 * ENNReal.ofReal (kern a (p.1 - p.2))) ∂(μ.prod μ) := by
          refine lintegral_mono fun p => ?_
          rw [← add_mul, ← mul_assoc, ← mul_assoc]
          gcongr
          exact TimeSchur.two_mul_le_add_sq_ennreal _ _
      _ = ∫⁻ p : ℝ × ℝ, g p.1 ^ 2 * ENNReal.ofReal (kern a (p.1 - p.2)) ∂(μ.prod μ) +
            ∫⁻ p : ℝ × ℝ, g p.2 ^ 2 * ENNReal.ofReal (kern a (p.1 - p.2)) ∂(μ.prod μ) :=
          lintegral_add_left' hg1 _
      _ ≤ R * ∫⁻ t, g t ^ 2 ∂μ + R * ∫⁻ t, g t ^ 2 ∂μ := add_le_add hA hB
      _ = 2 * (R * ∫⁻ t, g t ^ 2 ∂μ) := by rw [two_mul]
  exact (ENNReal.mul_le_mul_iff_right (by norm_num) (by norm_num)).mp h2

/-! ### The kernel form on `L²(I; G)` -/

section KernelForm

variable {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G]

/-- The kernel form `∫∫_{I²} |s-t|^{-a} ⟨F(s), F'(t)⟩_G ds dt` of
`E:positive-bochner-inclusion` (`integrated_intrinsic_constant.tex` lines 27-31 at edf7085f),
for functions `F, F' : ℝ → G`, as a Bochner integral over `I² = (0,1)²`.  It is the
manuscript's integral where the integrand is integrable; `kform_integrable` proves this for
`F, F' ∈ L²(I; G)`. -/
def kform (a : ℝ) (F F' : ℝ → G) : ℝ :=
  ∫ p, kern a (p.1 - p.2) * ⟪F p.1, F' p.2⟫ ∂(timeMeasure.prod timeMeasure)

/-- Auxiliary to the Lean proof route: the Schur bound for the kernel integrand.  If
`‖F‖, ‖F'‖ ≤ h` pointwise with `h ∈ L²(I)`, then
`∫∫ ‖|s-t|^{-a} ⟨F(s), F'(t)⟩‖ ≤ K_0 ∫ h²` (`0 ≤ a < 1`). -/
theorem lintegral_kform_le {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) {F F' : ℝ → G} {h : ℝ → ℝ}
    (hh : MemLp h 2 timeMeasure) (hF : ∀ t, ‖F t‖ ≤ h t) (hF' : ∀ t, ‖F' t‖ ≤ h t) :
    ∫⁻ p, ‖kern a (p.1 - p.2) * ⟪F p.1, F' p.2⟫‖ₑ ∂(timeMeasure.prod timeMeasure) ≤
      ENNReal.ofReal (K0 a * ∫ t, h t ^ 2 ∂timeMeasure) := by
  have hh0 : ∀ t, 0 ≤ h t := fun t => (norm_nonneg _).trans (hF t)
  set g : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal (h t) with hgdef
  have hg : AEMeasurable g timeMeasure := hh.aestronglyMeasurable.aemeasurable.ennreal_ofReal
  have hpt : ∀ p : ℝ × ℝ, ‖kern a (p.1 - p.2) * ⟪F p.1, F' p.2⟫‖ₑ ≤
      g p.1 * g p.2 * ENNReal.ofReal (kern a (p.1 - p.2)) := by
    intro p
    have h1 := hh0 p.1
    have h2 := hh0 p.2
    have hk := kern_nonneg a (p.1 - p.2)
    rw [← ofReal_norm, hgdef, ← ENNReal.ofReal_mul h1, ← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    rw [norm_mul, Real.norm_of_nonneg hk]
    calc kern a (p.1 - p.2) * ‖⟪F p.1, F' p.2⟫‖
        ≤ kern a (p.1 - p.2) * (‖F p.1‖ * ‖F' p.2‖) :=
          mul_le_mul_of_nonneg_left (norm_inner_le_norm _ _) hk
      _ ≤ kern a (p.1 - p.2) * (h p.1 * h p.2) :=
          mul_le_mul_of_nonneg_left (mul_le_mul (hF _) (hF' _) (norm_nonneg _) h1) hk
      _ = h p.1 * h p.2 * kern a (p.1 - p.2) := by ring
  have hI2 : Integrable (fun t => h t ^ 2) timeMeasure := hh.integrable_sq
  have hg2 : ∫⁻ t, g t ^ 2 ∂timeMeasure = ENNReal.ofReal (∫ t, h t ^ 2 ∂timeMeasure) := by
    rw [ofReal_integral_eq_lintegral_ofReal hI2 (ae_of_all _ fun t => by positivity)]
    refine lintegral_congr fun t => ?_
    simp only [hgdef, ENNReal.ofReal_pow (hh0 t)]
  calc _ ≤ ∫⁻ p : ℝ × ℝ, g p.1 * g p.2 * ENNReal.ofReal (kern a (p.1 - p.2))
          ∂(timeMeasure.prod timeMeasure) := lintegral_mono hpt
    _ ≤ ENNReal.ofReal (K0 a) * ∫⁻ t, g t ^ 2 ∂timeMeasure := schur_K0 ha0 ha1 g hg
    _ = _ := by rw [hg2, ← ENNReal.ofReal_mul (K0_pos ha1).le]

/-- Auxiliary to the Lean proof route: the kernel integrand is a.e.-strongly measurable for
a.e.-strongly measurable fields. -/
theorem kIntegrand_aesm (a : ℝ) {F F' : ℝ → G} (hF : AEStronglyMeasurable F timeMeasure)
    (hF' : AEStronglyMeasurable F' timeMeasure) :
    AEStronglyMeasurable (fun p : ℝ × ℝ => kern a (p.1 - p.2) * ⟪F p.1, F' p.2⟫)
      (timeMeasure.prod timeMeasure) :=
  ((measurable_kern a).comp (measurable_fst.sub measurable_snd)).aestronglyMeasurable.mul
    (hF.comp_fst.inner hF'.comp_snd)

/-- **Absolute convergence in `E:positive-bochner-inclusion`**: for `0 ≤ a < 1` and
`F, F' ∈ L²(I; G)` the integrand `|s-t|^{-a} ⟨F(s), F'(t)⟩` is integrable on `I²`. -/
theorem kform_integrable {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) {F F' : ℝ → G}
    (hF : MemLp F 2 timeMeasure) (hF' : MemLp F' 2 timeMeasure) :
    Integrable (fun p : ℝ × ℝ => kern a (p.1 - p.2) * ⟪F p.1, F' p.2⟫)
      (timeMeasure.prod timeMeasure) := by
  refine ⟨kIntegrand_aesm a hF.aestronglyMeasurable hF'.aestronglyMeasurable, ?_⟩
  refine lt_of_le_of_lt (lintegral_kform_le ha0 ha1 (hF.norm.add hF'.norm)
    (fun t => ?_) (fun t => ?_)) ENNReal.ofReal_lt_top
  · simp only [Pi.add_apply]; linarith [norm_nonneg (F' t)]
  · simp only [Pi.add_apply]; linarith [norm_nonneg (F t)]

/-- Auxiliary to the Lean proof route: `|∫∫ K ⟨F(s),F(t)⟩| ≤ K_0 ∫ ‖F‖²` (`0 ≤ a < 1`,
`F ∈ L²(I; G)`). -/
theorem abs_kform_self_le {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) {F : ℝ → G}
    (hF : MemLp F 2 timeMeasure) :
    |kform a F F| ≤ K0 a * ∫ t, ‖F t‖ ^ 2 ∂timeMeasure := by
  have hb := lintegral_kform_le (F := F) (F' := F) ha0 ha1 hF.norm (fun _ => le_rfl)
    (fun _ => le_rfl)
  have hc : 0 ≤ K0 a * ∫ t, ‖F t‖ ^ 2 ∂timeMeasure :=
    mul_nonneg (K0_pos ha1).le (integral_nonneg fun _ => by positivity)
  have h := (enorm_integral_le_lintegral_enorm _).trans hb
  rw [← ofReal_norm] at h
  rw [← Real.norm_eq_abs]
  exact (ENNReal.ofReal_le_ofReal_iff hc).1 h

/-- Auxiliary to the Lean proof route: the kernel form depends only on the a.e.-classes of its
arguments on `I`. -/
theorem kform_congr (a : ℝ) {F₁ F₂ F₁' F₂' : ℝ → G} (h : F₁ =ᵐ[timeMeasure] F₂)
    (h' : F₁' =ᵐ[timeMeasure] F₂') : kform a F₁ F₁' = kform a F₂ F₂' := by
  unfold kform
  refine integral_congr_ae ?_
  filter_upwards [(Measure.quasiMeasurePreserving_fst (μ := timeMeasure)
      (ν := timeMeasure)).ae h,
    (Measure.quasiMeasurePreserving_snd (μ := timeMeasure) (ν := timeMeasure)).ae h']
    with p hp hp'
  rw [hp, hp']

/-- Symmetry of the kernel form (Fubini swap, evenness of `|x|^{-a}`, symmetry of the real
inner product); no integrability needed. -/
theorem kform_comm (a : ℝ) (F F' : ℝ → G) : kform a F' F = kform a F F' := by
  unfold kform
  rw [← integral_prod_swap (fun p : ℝ × ℝ => kern a (p.1 - p.2) * ⟪F p.1, F' p.2⟫)]
  congr 1
  funext p
  simp only [Prod.fst_swap, Prod.snd_swap]
  rw [kern_sub_comm, real_inner_comm]

/-- Additivity of the kernel form in its first argument on `L²(I; G)`. -/
theorem kform_add_left {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) {F₁ F₂ F' : ℝ → G}
    (h₁ : MemLp F₁ 2 timeMeasure) (h₂ : MemLp F₂ 2 timeMeasure) (h' : MemLp F' 2 timeMeasure) :
    kform a (F₁ + F₂) F' = kform a F₁ F' + kform a F₂ F' := by
  unfold kform
  rw [← integral_add (kform_integrable ha0 ha1 h₁ h') (kform_integrable ha0 ha1 h₂ h')]
  congr 1
  funext p
  simp only [Pi.add_apply, inner_add_left]
  ring

/-- Homogeneity of the kernel form in its first argument (no integrability needed). -/
theorem kform_smul_left (a c : ℝ) (F F' : ℝ → G) :
    kform a (c • F) F' = c * kform a F F' := by
  unfold kform
  rw [← integral_const_mul]
  congr 1
  funext p
  simp only [Pi.smul_apply, real_inner_smul_left]
  ring

/-! ### Positivity of the kernel form (Gamma subordination) -/

/-- Auxiliary to the Lean proof route: for an integrable `u : ℝ → G` and an s-finite `μ`,
`∫∫ ⟨u(s), u(t)⟩ dμ(s) dμ(t) = ‖∫ u dμ‖²` (as `⟨∫u, ∫u⟩`). -/
theorem integral_inner_prod_self [CompleteSpace G] {μ : Measure ℝ} [SFinite μ] {u : ℝ → G}
    (hu : Integrable u μ) :
    ∫ p, ⟪u p.1, u p.2⟫ ∂(μ.prod μ) = ⟪∫ t, u t ∂μ, ∫ t, u t ∂μ⟫ := by
  have hi : Integrable (fun p : ℝ × ℝ => ⟪u p.1, u p.2⟫) (μ.prod μ) := by
    refine Integrable.mono' (hu.norm.mul_prod hu.norm)
      (hu.aestronglyMeasurable.comp_fst.inner hu.aestronglyMeasurable.comp_snd)
      (ae_of_all _ fun p => ?_)
    exact norm_inner_le_norm _ _
  rw [integral_prod _ hi]
  have h1 : ∀ s, ∫ t, ⟪u s, u t⟫ ∂μ = ⟪u s, ∫ t, u t ∂μ⟫ := fun s => integral_inner hu (u s)
  simp_rw [h1]
  have h2 : ∀ s, ⟪u s, ∫ t, u t ∂μ⟫ = ⟪∫ t, u t ∂μ, u s⟫ := fun s => real_inner_comm _ _
  simp_rw [h2]
  exact integral_inner hu _

/-- Auxiliary to the Lean proof route (the abstract form of the positivity step of
`L:positive-raw-embedding`, "its quadratic form is an integral of a square", for `G`-valued
fields): let `μ` on `ℝ` and `ν` on `W` be s-finite, `ρ ≥ 0` measurable, `φ ≥ 0` jointly
measurable, `K ≥ 0` with `K(s,t) = ∫ ρ(w) φ_w(s) φ_w(t) dν(w)` (in `[0,∞]`) for `μ⊗μ`-a.e.
`(s,t)`.  If `f : ℝ → G` is a.e.-strongly measurable, `K(s,t) ‖f(s)‖ ‖f(t)‖` is integrable and
every `φ_w f` is `μ`-integrable, then `∫∫ K(s,t) ⟨f(s), f(t)⟩ ≥ 0`: it equals
`∫ ρ(w) ‖∫ φ_w f dμ‖² dν(w)`. -/
theorem inner_form_nonneg_of_mixture [CompleteSpace G] {W : Type*} [MeasurableSpace W]
    (μ : Measure ℝ) [SFinite μ] (ν : Measure W) [SFinite ν]
    (ρ : W → ℝ) (hρ : Measurable ρ) (hρ0 : ∀ w, 0 ≤ ρ w)
    (φ : W → ℝ → ℝ) (hφ : Measurable (Function.uncurry φ)) (hφ0 : ∀ w t, 0 ≤ φ w t)
    (K : ℝ × ℝ → ℝ) (hK0 : ∀ p, 0 ≤ K p)
    (hK : ∀ᵐ p ∂(μ.prod μ),
      ENNReal.ofReal (K p) = ∫⁻ w, ENNReal.ofReal (ρ w * φ w p.1 * φ w p.2) ∂ν)
    (f : ℝ → G) (hf : AEStronglyMeasurable f μ)
    (hint : Integrable (fun p : ℝ × ℝ => K p * (‖f p.1‖ * ‖f p.2‖)) (μ.prod μ))
    (hφi : ∀ w, Integrable (fun t => φ w t • f t) μ) :
    0 ≤ ∫ p, K p * ⟪f p.1, f p.2⟫ ∂(μ.prod μ) := by
  set m := μ.prod μ
  have hkm : Measurable fun q : (ℝ × ℝ) × W => ρ q.2 * φ q.2 q.1.1 * φ q.2 q.1.2 := by
    have h1 : Measurable fun q : (ℝ × ℝ) × W => φ q.2 q.1.1 :=
      hφ.comp (measurable_snd.prodMk (measurable_fst.comp measurable_fst))
    have h2 : Measurable fun q : (ℝ × ℝ) × W => φ q.2 q.1.2 :=
      hφ.comp (measurable_snd.prodMk (measurable_snd.comp measurable_fst))
    exact ((hρ.comp measurable_snd).mul h1).mul h2
  have hknn : ∀ q : (ℝ × ℝ) × W, 0 ≤ ρ q.2 * φ q.2 q.1.1 * φ q.2 q.1.2 := fun q =>
    mul_nonneg (mul_nonneg (hρ0 _) (hφ0 _ _)) (hφ0 _ _)
  set F : (ℝ × ℝ) × W → ℝ := fun q =>
    ρ q.2 * φ q.2 q.1.1 * φ q.2 q.1.2 * ⟪f q.1.1, f q.1.2⟫ with hFdef
  have hf1 : AEStronglyMeasurable (fun q : (ℝ × ℝ) × W => f q.1.1) (m.prod ν) :=
    hf.comp_fst.comp_fst
  have hf2 : AEStronglyMeasurable (fun q : (ℝ × ℝ) × W => f q.1.2) (m.prod ν) :=
    hf.comp_snd.comp_fst
  have hFm : AEStronglyMeasurable F (m.prod ν) :=
    hkm.aestronglyMeasurable.mul (hf1.inner hf2)
  -- the a.e. section identity
  have hsec : ∀ᵐ p ∂m, ∫ w, F (p, w) ∂ν = K p * ⟪f p.1, f p.2⟫ := by
    filter_upwards [hK] with p hp
    have hmw : Measurable fun w => ρ w * φ w p.1 * φ w p.2 :=
      hkm.comp (measurable_const.prodMk measurable_id)
    have hKr : ∫ w, ρ w * φ w p.1 * φ w p.2 ∂ν = K p := by
      rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun w => hknn (p, w))
        hmw.aestronglyMeasurable, ← hp, ENNReal.toReal_ofReal (hK0 p)]
    simp only [hFdef]
    rw [integral_mul_const, hKr]
  -- integrability on the triple product
  have hFi : Integrable F (m.prod ν) := by
    refine ⟨hFm, ?_⟩
    have hle : ∀ q : (ℝ × ℝ) × W, ‖F q‖ₑ ≤
        ENNReal.ofReal (ρ q.2 * φ q.2 q.1.1 * φ q.2 q.1.2) * (‖f q.1.1‖ₑ * ‖f q.1.2‖ₑ) := by
      intro q
      rw [← ofReal_norm, ← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul (norm_nonneg _),
        ← ENNReal.ofReal_mul (hknn q)]
      apply ENNReal.ofReal_le_ofReal
      simp only [hFdef]
      rw [norm_mul, Real.norm_of_nonneg (hknn q)]
      exact mul_le_mul_of_nonneg_left (norm_inner_le_norm _ _) (hknn q)
    have hm2 : AEMeasurable (fun q : (ℝ × ℝ) × W =>
        ENNReal.ofReal (ρ q.2 * φ q.2 q.1.1 * φ q.2 q.1.2) * (‖f q.1.1‖ₑ * ‖f q.1.2‖ₑ))
        (m.prod ν) :=
      (ENNReal.measurable_ofReal.comp hkm).aemeasurable.mul (hf1.enorm.mul hf2.enorm)
    refine lt_of_le_of_lt (lintegral_mono hle) ?_
    rw [lintegral_prod _ hm2]
    have heq : ∀ᵐ p ∂m, ∫⁻ w, ENNReal.ofReal (ρ w * φ w p.1 * φ w p.2) *
        (‖f p.1‖ₑ * ‖f p.2‖ₑ) ∂ν = ‖K p * (‖f p.1‖ * ‖f p.2‖)‖ₑ := by
      filter_upwards [hK] with p hp
      have hmw : Measurable fun w => ENNReal.ofReal (ρ w * φ w p.1 * φ w p.2) :=
        ENNReal.measurable_ofReal.comp (hkm.comp (measurable_const.prodMk measurable_id))
      rw [lintegral_mul_const _ hmw, ← hp, enorm_mul, enorm_mul, Real.enorm_of_nonneg (hK0 p),
        enorm_norm, enorm_norm]
    rw [lintegral_congr_ae heq]
    exact hint.2
  -- assemble
  have hswap : ∫ p, ∫ w, F (p, w) ∂ν ∂m = ∫ w, ∫ p, F (p, w) ∂m ∂ν :=
    integral_integral_swap (f := fun p w => F (p, w)) hFi
  have hinner : ∀ w, ∫ p, F (p, w) ∂m = ρ w * ⟪∫ t, φ w t • f t ∂μ, ∫ t, φ w t • f t ∂μ⟫ := by
    intro w
    have hpt : ∀ p : ℝ × ℝ, F (p, w) = ρ w * ⟪φ w p.1 • f p.1, φ w p.2 • f p.2⟫ := by
      intro p
      simp only [hFdef, real_inner_smul_left, real_inner_smul_right]
      ring
    simp_rw [hpt]
    rw [integral_const_mul, integral_inner_prod_self (hφi w)]
  rw [integral_congr_ae (Filter.EventuallyEq.symm hsec), hswap]
  simp_rw [hinner]
  exact integral_nonneg fun w => mul_nonneg (hρ0 w) (real_inner_self_nonneg)

/-- Auxiliary to the Lean proof route: for fixed parameters `w = (λ, u)` the profile
`t ↦ 1_{u ≤ t} e^{-λ(t-u)}` is bounded on `I = (0,1)` by `e^{|λ|(1+|u|)}`. -/
theorem mixProfile_le (w : ℝ × ℝ) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    TimeCompletion.mixProfile w t ≤ Real.exp (|w.1| * (1 + |w.2|)) := by
  unfold TimeCompletion.mixProfile
  split_ifs with h
  · apply Real.exp_le_exp.mpr
    have h1 : |t - w.2| ≤ 1 + |w.2| := by
      have h2 := abs_sub t w.2
      have h3 : |t| ≤ 1 := by rw [abs_of_pos ht.1]; exact ht.2.le
      linarith
    calc -(w.1 * (t - w.2)) ≤ |w.1 * (t - w.2)| := neg_le_abs _
      _ = |w.1| * |t - w.2| := abs_mul _ _
      _ ≤ |w.1| * (1 + |w.2|) := mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
  · exact (Real.exp_pos _).le

/-- **Positivity of the kernel form on `L²(I; G)`** (the positivity half of the construction of
`H_t ⊗ G` in `L:positive-raw-embedding`, `integrated_intrinsic_constant.tex` lines 52-64 at
edf7085f; the TeX proves positivity on scalar tests and passes to finite tensors and Bochner
fields): for `0 < a < 1` and `F ∈ L²(I; G)`, `∫∫_{I²} |s-t|^{-a} ⟨F(s), F(t)⟩ ≥ 0`.  Route:
the Gamma-subordination mixture `TimeCompletion.kern_eq_mixture` and
`inner_form_nonneg_of_mixture`. -/
theorem kform_self_nonneg [CompleteSpace G] {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {F : ℝ → G}
    (hF : MemLp F 2 timeMeasure) : 0 ≤ kform a F F := by
  have hK : ∀ᵐ p ∂(timeMeasure.prod timeMeasure), ENNReal.ofReal (kern a (p.1 - p.2)) =
      ∫⁻ w, ENNReal.ofReal (TimeCompletion.mixWeight a w * TimeCompletion.mixProfile w p.1 *
        TimeCompletion.mixProfile w p.2) ∂TimeCompletion.mixMeasure := by
    rw [timeMeasure_eq_Icc]
    filter_upwards [TimeCompletion.ae_ne_diag 1] with p hp
    exact TimeCompletion.kern_eq_mixture a ha0 p.1 p.2 hp
  have hn : MemLp (fun t => ‖F t‖) 2 timeMeasure := hF.norm
  have hint : Integrable (fun p : ℝ × ℝ => kern a (p.1 - p.2) * (‖F p.1‖ * ‖F p.2‖))
      (timeMeasure.prod timeMeasure) :=
    (kform_integrable (G := ℝ) ha0.le ha1 hn hn).congr (ae_of_all _ fun p => by
      simp only [RCLike.inner_apply, conj_trivial]
      ring)
  have hFi : Integrable F timeMeasure := hF.integrable one_le_two
  have hφi : ∀ w, Integrable (fun t => TimeCompletion.mixProfile w t • F t) timeMeasure := by
    intro w
    refine (hFi.norm.const_mul (Real.exp (|w.1| * (1 + |w.2|)))).mono'
      (((TimeCompletion.measurable_mixProfile.comp
        (measurable_const.prodMk measurable_id)).aestronglyMeasurable).smul
          hF.aestronglyMeasurable) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    rw [norm_smul, Real.norm_of_nonneg (TimeCompletion.mixProfile_nonneg w t)]
    exact mul_le_mul_of_nonneg_right (mixProfile_le w ht) (norm_nonneg _)
  exact inner_form_nonneg_of_mixture timeMeasure TimeCompletion.mixMeasure
    (TimeCompletion.mixWeight a) (TimeCompletion.measurable_mixWeight a)
    (TimeCompletion.mixWeight_nonneg a ha0) TimeCompletion.mixProfile
    TimeCompletion.measurable_mixProfile TimeCompletion.mixProfile_nonneg
    (fun p => kern a (p.1 - p.2)) (fun p => kern_nonneg _ _) hK F hF.aestronglyMeasurable hint hφi

end KernelForm

/-! ### The completion `H_t ⊗ G` and the map `J_G` -/

/-- The standing temporal parameter of `L:positive-raw-embedding`: `a = α₀` with `0 < a < 1`
(`integrated_intrinsic_constant.tex` lines 4-5 at edf7085f; `H:homog` gives `0 < α₀ < 1`). -/
structure TParams where
  /-- the exponent `a = α₀`. -/
  a : ℝ
  ha0 : 0 < a
  ha1 : a < 1

/-- The temporal parameter of `H:homog` (`a = α₀`). -/
def TParams.ofHomog {d : ℕ} {alpha alpha0 : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogCovariance d alpha alpha0 Γ μ) : TParams :=
  ⟨alpha0, hH.alpha0_pos, hH.alpha0_lt_one⟩

section Completion

variable (p : TParams) (G : Type*) [NormedAddCommGroup G] [InnerProductSpace ℝ G]

/-- The pre-Hilbert space: `L²(I; G)` (Bochner a.e.-classes, `I = (0,1)`) with the degenerate
inner product `⟪F, F'⟫ = ∫∫_{I²} |s-t|^{-a} ⟨F(s), F'(t)⟩_G` (`kform`). -/
def KPre (_p : TParams) (G : Type*) [NormedAddCommGroup G] : Type _ := Lp G 2 timeMeasure

instance instAddCommGroupKPre : AddCommGroup (KPre p G) :=
  inferInstanceAs (AddCommGroup (Lp G 2 timeMeasure))
instance instModuleKPre : Module ℝ (KPre p G) := inferInstanceAs (Module ℝ (Lp G 2 timeMeasure))

variable {p G}

/-- Auxiliary: an element of `L²(I; G)` viewed in the pre-Hilbert space. -/
def toK (F : Lp G 2 timeMeasure) : KPre p G := F

/-- Auxiliary: the `L²` class underlying an element of the pre-Hilbert space. -/
def KPre.toLp (F : KPre p G) : Lp G 2 timeMeasure := F

variable (p G)

/-- The inner-product core of `KPre p G`; its positivity is `kform_self_nonneg`. -/
@[instance_reducible] def kcore [CompleteSpace G] : PreInnerProductSpace.Core ℝ (KPre p G) where
  inner F F' := kform p.a (⇑(KPre.toLp F)) (⇑(KPre.toLp F'))
  conj_inner_symm F F' := by
    simp only [conj_trivial]
    exact kform_comm p.a _ _
  re_inner_nonneg F := by
    simp only [RCLike.re_to_real]
    exact kform_self_nonneg p.ha0 p.ha1 (Lp.memLp _)
  add_left F F' F'' := by
    change kform p.a ⇑(KPre.toLp F + KPre.toLp F') _ = _
    rw [kform_congr p.a (Lp.coeFn_add _ _) (Filter.EventuallyEq.refl _ _)]
    exact kform_add_left p.ha0.le p.ha1 (Lp.memLp _) (Lp.memLp _) (Lp.memLp _)
  smul_left F F' r := by
    change kform p.a ⇑(r • KPre.toLp F) _ = _
    rw [kform_congr p.a (Lp.coeFn_smul _ _) (Filter.EventuallyEq.refl _ _), conj_trivial]
    exact kform_smul_left p.a r _ _

instance instSeminormedKPre [CompleteSpace G] : SeminormedAddCommGroup (KPre p G) :=
  @InnerProductSpace.Core.toSeminormedAddCommGroup ℝ _ _ _ _ (kcore p G)

instance instInnerKPre [CompleteSpace G] : InnerProductSpace ℝ (KPre p G) :=
  InnerProductSpace.ofCore (kcore p G)

/-- **The completion `H_t ⊗ G`** of `L:positive-raw-embedding` (`integrated_intrinsic_constant.tex`
lines 23-26 at edf7085f), built as the `L²` completion of decision 4 of waves L9 and L14: the
(Hausdorff) completion of `L²(I; G)` for the seminorm `(∫∫ |s-t|^{-a} ⟨F(s), F(t)⟩)^{1/2}`.  It is a
real Hilbert space (Mathlib instances).  No identification with an algebraic or Hilbert tensor
product `H_t ⊗ G` is made (decision 4); for `G = ℝ` it is `H_t` (`Ht`). -/
abbrev HK [CompleteSpace G] := UniformSpace.Completion (KPre p G)

/-- `H_t` (`integrated_cameron_mean.tex` lines 8-11 at edf7085f: the completion of `C_c^∞(I)` with
the time kernel `|s-t|^{-a}`), built here as the completion of `L²(I; ℝ)` under the same form. -/
abbrev Ht := HK p ℝ

/-- Auxiliary: the linear map `L²(I; G) → H_t ⊗ G`. -/
def Jlin [CompleteSpace G] : Lp G 2 timeMeasure →ₗ[ℝ] HK p G :=
  (UniformSpace.Completion.toComplₗᵢ (𝕜 := ℝ) (E := KPre p G)).toLinearMap

variable {p G}

/-- Auxiliary: `Jlin p G F` is the image of `F` in the completion. -/
theorem Jlin_apply [CompleteSpace G] (F : Lp G 2 timeMeasure) :
    Jlin p G F = ((toK F : KPre p G) : HK p G) := rfl

/-- Auxiliary: the inner product of `KPre p G` is the kernel form. -/
theorem inner_toK [CompleteSpace G] (F F' : Lp G 2 timeMeasure) :
    ⟪(toK F : KPre p G), toK F'⟫ = kform p.a ⇑F ⇑F' := rfl

/-- Auxiliary: `⟪Jlin F, Jlin F'⟫ = ∫∫ |s-t|^{-a} ⟨F(s), F'(t)⟩`. -/
theorem inner_Jlin [CompleteSpace G] (F F' : Lp G 2 timeMeasure) :
    ⟪Jlin p G F, Jlin p G F'⟫ = kform p.a ⇑F ⇑F' := by
  rw [Jlin_apply, Jlin_apply, UniformSpace.Completion.inner_coe, inner_toK]

/-- Auxiliary: `‖F‖²_{L²(I;G)} = ∫_I ‖F‖²`. -/
theorem Lp_norm_sq_eq [CompleteSpace G] (F : Lp G 2 timeMeasure) :
    ‖F‖ ^ 2 = ∫ t, ‖F t‖ ^ 2 ∂timeMeasure := by
  rw [← real_inner_self_eq_norm_sq, MeasureTheory.L2.inner_def]
  simp_rw [real_inner_self_eq_norm_sq]

/-- Auxiliary: `‖Jlin F‖² ≤ K_0 ‖F‖²`. -/
theorem norm_Jlin_sq_le [CompleteSpace G] (F : Lp G 2 timeMeasure) :
    ‖Jlin p G F‖ ^ 2 ≤ K0 p.a * ‖F‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, inner_Jlin, Lp_norm_sq_eq]
  exact (le_abs_self _).trans (abs_kform_self_le p.ha0.le p.ha1 (Lp.memLp F))

/-- Auxiliary: `‖Jlin F‖ ≤ √K_0 ‖F‖`. -/
theorem norm_Jlin_le [CompleteSpace G] (F : Lp G 2 timeMeasure) :
    ‖Jlin p G F‖ ≤ Real.sqrt (K0 p.a) * ‖F‖ := by
  calc ‖Jlin p G F‖ = Real.sqrt (‖Jlin p G F‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt (K0 p.a * ‖F‖ ^ 2) := Real.sqrt_le_sqrt (norm_Jlin_sq_le F)
    _ = Real.sqrt (K0 p.a) * ‖F‖ := by
        rw [Real.sqrt_mul' _ (by positivity), Real.sqrt_sq (norm_nonneg _)]

variable (p G)

/-- **The bounded map `J_G : L²(I; G) → H_t ⊗ G`** of `L:positive-raw-embedding`
(`integrated_intrinsic_constant.tex` lines 25-31 at edf7085f), a continuous linear map of norm at
most `√K_0` (`norm_J_sq_le`), defined on Bochner `L²` classes. -/
def J [CompleteSpace G] : Lp G 2 timeMeasure →L[ℝ] HK p G :=
  (Jlin p G).mkContinuous (Real.sqrt (K0 p.a)) norm_Jlin_le

variable {p G}

/-- Auxiliary: `J` agrees with `Jlin`. -/
theorem J_apply [CompleteSpace G] (F : Lp G 2 timeMeasure) : J p G F = Jlin p G F := rfl

/-- **`E:positive-bochner-inclusion`** (`integrated_intrinsic_constant.tex` lines 27-31 at
edf7085f): for a real Hilbert space `G` and `F ∈ L²(I; G)`, the integrand
`|s-t|^{-a} ⟨F(s), F(t)⟩_G` is integrable on `I²`,
`‖J_G F‖² = ∫∫_{I²} |s-t|^{-a} ⟨F(s), F(t)⟩_G ds dt ≤ K_0 ‖F‖²_{L²(I;G)}`,
`K_0 = 2^a/(1-a)`; more generally `⟨J_G F, J_G F'⟩ = ∫∫ |s-t|^{-a} ⟨F(s), F'(t)⟩`. -/
theorem positive_bochner_inclusion [CompleteSpace G] (F : Lp G 2 timeMeasure) :
    Integrable (fun q : ℝ × ℝ => kern p.a (q.1 - q.2) * ⟪F q.1, F q.2⟫)
        (timeMeasure.prod timeMeasure) ∧
      ‖J p G F‖ ^ 2 = ∫ q, kern p.a (q.1 - q.2) * ⟪F q.1, F q.2⟫
        ∂(timeMeasure.prod timeMeasure) ∧
      ‖J p G F‖ ^ 2 ≤ K0 p.a * ‖F‖ ^ 2 ∧
      ∀ F' : Lp G 2 timeMeasure, ⟪J p G F, J p G F'⟫ = kform p.a ⇑F ⇑F' := by
  refine ⟨kform_integrable p.ha0.le p.ha1 (Lp.memLp F) (Lp.memLp F), ?_, norm_Jlin_sq_le F,
    fun F' => inner_Jlin F F'⟩
  rw [J_apply, ← real_inner_self_eq_norm_sq, inner_Jlin]
  rfl

end Completion

/-! ### The spatial covariance space `H_sp` -/

section Spatial

open WeakSobolev (IsTestFunction)
open SpatialFourierBound (spatialPair)

variable {d : ℕ}

/-- The covariance data used by `H_sp`: a locally finite even measure `Γ` with a spectral measure
`μ` in the manuscript's convention (the parts of `H:homog` that the construction uses). -/
structure SpData (d : ℕ) where
  /-- the spatial covariance `Γ`. -/
  Γ : Measure (Rd d)
  /-- its spectral measure. -/
  μ : Measure (Rd d)
  radon : IsLocallyFiniteMeasure Γ
  even : IsEven Γ
  spectral : IsSpectralMeasure Γ μ

/-- The covariance data of `H:homog`. -/
def SpData.ofHomog {alpha alpha0 : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogCovariance d alpha alpha0 Γ μ) : SpData d :=
  ⟨Γ, μ, hH.Γ_radon, hH.Γ_even, hH.spectral⟩

attribute [instance] SpData.radon

/-- The real test functions `C_c^∞(ℝ^d)` as a subspace of `ℝ^d → ℝ`. -/
def testSub (d : ℕ) : Submodule ℝ (Rd d → ℝ) where
  carrier := {φ | IsTestFunction φ}
  add_mem' := fun ha hb => ⟨ha.1.add hb.1, ha.2.add hb.2⟩
  zero_mem' := ⟨contDiff_const, HasCompactSupport.zero⟩
  smul_mem' := fun c _ h => ⟨h.1.const_smul c, h.2.smul_left (f := fun _ => c)⟩

/-- Auxiliary to the Lean proof route: additivity of the real pairing in its first argument for
continuous compactly supported profiles. -/
theorem spatialPair_add_left (Γ : Measure (Rd d)) [IsLocallyFiniteMeasure Γ] {P Q Z : Rd d → ℝ}
    (hP : Continuous P) (hPs : HasCompactSupport P) (hQ : Continuous Q)
    (hQs : HasCompactSupport Q) (hZ : Continuous Z) (hZs : HasCompactSupport Z) :
    spatialPair Γ (P + Q) Z = spatialPair Γ P Z + spatialPair Γ Q Z := by
  have hin : ∀ y, ∫ x, (P + Q) x * Z (x - y) = (∫ x, P x * Z (x - y)) + ∫ x, Q x * Z (x - y) := by
    intro y
    rw [← integral_add (SpatialFourLinear.inner_integrable hP hPs hZ y)
      (SpatialFourLinear.inner_integrable hQ hQs hZ y)]
    congr 1; funext x; simp only [Pi.add_apply]; ring
  unfold spatialPair
  simp_rw [hin]
  exact integral_add (SpatialFourLinear.cross_integrable Γ hP hPs hZ hZs)
    (SpatialFourLinear.cross_integrable Γ hQ hQs hZ hZs)

/-- Auxiliary to the Lean proof route: homogeneity of the real pairing in its first argument. -/
theorem spatialPair_smul_left (Γ : Measure (Rd d)) (c : ℝ) (P Z : Rd d → ℝ) :
    spatialPair Γ (c • P) Z = c * spatialPair Γ P Z := by
  unfold spatialPair
  rw [← integral_const_mul]
  congr 1; funext y
  rw [← integral_const_mul]
  congr 1; funext x
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

variable (S : SpData d)

/-- The pre-Hilbert space of `H_sp`: `C_c^∞(ℝ^d)` with the (degenerate) inner product
`B_Γ(φ, ψ) = ∫ (∫ φ(x) ψ(x-y) dx) Γ(dy)` (`SpatialFourierBound.spatialPair`). -/
def SpPre (_S : SpData d) : Type := testSub d

instance instAddCommGroupSpPre : AddCommGroup (SpPre S) :=
  inferInstanceAs (AddCommGroup (testSub d))
instance instModuleSpPre : Module ℝ (SpPre S) := inferInstanceAs (Module ℝ (testSub d))

variable {S}

/-- Auxiliary: the test function underlying an element of `SpPre S`. -/
def SpPre.toFun (φ : SpPre S) : Rd d → ℝ := ((show testSub d from φ) : Rd d → ℝ)

/-- Auxiliary: the underlying function is a test function. -/
theorem SpPre.isTest (φ : SpPre S) : IsTestFunction φ.toFun := (show testSub d from φ).2

variable (S)

/-- The inner-product core of `SpPre S`: positivity is `SpatialFourLinear.spatialPair_self_nonneg`
(spectral measure), symmetry is `SpatialFourLinear.spatialPair_comm` (evenness of `Γ`). -/
@[instance_reducible] def spcore : PreInnerProductSpace.Core ℝ (SpPre S) where
  inner φ ψ := spatialPair S.Γ φ.toFun ψ.toFun
  conj_inner_symm φ ψ := by
    simp only [conj_trivial]
    exact SpatialFourLinear.spatialPair_comm S.even φ.isTest.1.continuous ψ.isTest.1.continuous
      ψ.isTest.2
  re_inner_nonneg φ := by
    simp only [RCLike.re_to_real]
    exact SpatialFourLinear.spatialPair_self_nonneg S.spectral φ.isTest
  add_left φ ψ χ := spatialPair_add_left S.Γ φ.isTest.1.continuous φ.isTest.2
    ψ.isTest.1.continuous ψ.isTest.2 χ.isTest.1.continuous χ.isTest.2
  smul_left φ ψ r := by
    rw [conj_trivial]
    exact spatialPair_smul_left S.Γ r φ.toFun ψ.toFun

instance instSeminormedSpPre : SeminormedAddCommGroup (SpPre S) :=
  @InnerProductSpace.Core.toSeminormedAddCommGroup ℝ _ _ _ _ (spcore S)

instance instInnerSpPre : InnerProductSpace ℝ (SpPre S) := InnerProductSpace.ofCore (spcore S)

/-- **The spatial covariance space `H_sp`** (`integrated_cameron_mean.tex` lines 8-10 at
edf7085f: "the real covariance-null completion of `C_c^∞(ℝ^d)` with inner product `B_Γ`"): the
(Hausdorff) completion of `C_c^∞(ℝ^d)` for the seminorm `B_Γ(φ,φ)^{1/2}`, a real Hilbert space. -/
abbrev Hsp := UniformSpace.Completion (SpPre S)

variable {S}

/-- Auxiliary: a test function as an element of `SpPre S`. -/
def toSp (φ : Rd d → ℝ) (hφ : IsTestFunction φ) : SpPre S := (⟨φ, hφ⟩ : testSub d)

variable (S)

/-- The class in `H_sp` of a function: the image of `q` if `q` is a test function, and `0`
otherwise (a total function; it is used only on test functions). -/
def toHsp (q : Rd d → ℝ) : Hsp S :=
  open Classical in if h : IsTestFunction q then ((toSp q h : SpPre S) : Hsp S) else 0

variable {S}

/-- Auxiliary: `toHsp` on a test function. -/
theorem toHsp_of_test {q : Rd d → ℝ} (hq : IsTestFunction q) :
    toHsp S q = ((toSp q hq : SpPre S) : Hsp S) := by
  simp only [toHsp, hq, ↓reduceDIte]

/-- `⟨[φ], [ψ]⟩_{H_sp} = B_Γ(φ, ψ)` for test functions. -/
theorem inner_toHsp {φ ψ : Rd d → ℝ} (hφ : IsTestFunction φ) (hψ : IsTestFunction ψ) :
    ⟪toHsp S φ, toHsp S ψ⟫ = spatialPair S.Γ φ ψ := by
  rw [toHsp_of_test hφ, toHsp_of_test hψ, UniformSpace.Completion.inner_coe]
  rfl

/-- `toHsp` is additive on test functions. -/
theorem toHsp_sub {φ ψ : Rd d → ℝ} (hφ : IsTestFunction φ) (hψ : IsTestFunction ψ) :
    toHsp S (φ - ψ) = toHsp S φ - toHsp S ψ := by
  have hd : IsTestFunction (φ - ψ) := (testSub d).sub_mem hφ hψ
  rw [toHsp_of_test hd, toHsp_of_test hφ, toHsp_of_test hψ, ← UniformSpace.Completion.coe_sub]
  rfl

/-- `toHsp` is homogeneous on test functions. -/
theorem toHsp_smul (c : ℝ) {φ : Rd d → ℝ} (hφ : IsTestFunction φ) :
    toHsp S (c • φ) = c • toHsp S φ := by
  have hd : IsTestFunction (c • φ) := (testSub d).smul_mem c hφ
  rw [toHsp_of_test hd, toHsp_of_test hφ, ← UniformSpace.Completion.coe_smul]
  rfl

/-- `‖[φ]‖²_{H_sp} = B_Γ(φ, φ)` for a test function. -/
theorem norm_toHsp_sq {φ : Rd d → ℝ} (hφ : IsTestFunction φ) :
    ‖toHsp S φ‖ ^ 2 = spatialPair S.Γ φ φ := by
  rw [← real_inner_self_eq_norm_sq, inner_toHsp hφ hφ]

/-- The image of the test functions is dense in `H_sp`. -/
theorem dense_range_toHsp : Dense {x : Hsp S | ∃ φ, IsTestFunction φ ∧ x = toHsp S φ} := by
  refine (UniformSpace.Completion.denseRange_coe (α := SpPre S)).mono ?_
  rintro x ⟨φ, rfl⟩
  exact ⟨φ.toFun, φ.isTest, by rw [toHsp_of_test φ.isTest]; rfl⟩

/-! #### Separability of `H_sp` -/

/-- Auxiliary to the Lean proof route (a local `L²` bound in the spirit of
`E:positive-local-spatial-bound`, `integrated_intrinsic_constant.tex` lines 86-94 at edf7085f):
for a test function `q` vanishing for `|x| > R`,
`B_Γ(q, q) ≤ Γ(B_{2R}) ∫ q²`. -/
theorem spatialPair_self_le_L2 (Γ : Measure (Rd d)) [IsLocallyFiniteMeasure Γ] {q : Rd d → ℝ}
    (hq : IsTestFunction q) {R : ℝ} (hR : ∀ x, R < ‖x‖ → q x = 0) :
    spatialPair Γ q q ≤ Γ.real (closedBall (0 : Rd d) (2 * R)) * ∫ x, q x ^ 2 := by
  have hq2 : Integrable (fun x => q x ^ 2) := (VariationalFloor.memLp_test hq).integrable_sq
  have hrow : ∀ y, |∫ x, q x * q (x - y)| ≤ ∫ x, q x ^ 2 := by
    intro y
    have hqy : Integrable (fun x => q (x - y) ^ 2) := by
      have := hq2.comp_sub_right y
      simpa using this
    have hsum : ∫ x, (q x ^ 2 + q (x - y) ^ 2) / 2 = ∫ x, q x ^ 2 := by
      rw [integral_div, integral_add hq2 hqy, integral_sub_right_eq_self (fun x => q x ^ 2) y]
      ring
    rw [← hsum, ← Real.norm_eq_abs]
    refine norm_integral_le_of_norm_le ((hq2.add hqy).div_const 2) (ae_of_all _ fun x => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    nlinarith [sq_abs (q x), sq_abs (q (x - y)), sq_nonneg (|q x| - |q (x - y)|)]
  unfold spatialPair
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := closedBall (0 : Rd d) (2 * R))
    fun y hy => by
      rw [mem_closedBall, dist_zero_right, not_le] at hy
      exact SpaceTimePositivity.cross_eq_zero hR hR hy]
  refine (le_abs_self _).trans ?_
  rw [← Real.norm_eq_abs]
  exact (norm_setIntegral_le_of_norm_le_const (measure_closedBall_lt_top (μ := Γ)) fun y _ =>
    (Real.norm_eq_abs _).trans_le (hrow y)).trans_eq (mul_comm _ _)

/-- Auxiliary: the `L²` class of a test function. -/
def testToL2 (φ : SpPre S) : Lp ℝ 2 (volume : Measure (Rd d)) :=
  (VariationalFloor.memLp_test φ.isTest).toLp φ.toFun

/-- Auxiliary: on test functions vanishing for `|x| > R`, the covariance seminorm is bounded by
`√Γ(B_{2R})` times the `L²` distance. -/
theorem dist_le_L2 {R : ℝ} {φ ψ : SpPre S} (hφ : ∀ x, R < ‖x‖ → φ.toFun x = 0)
    (hψ : ∀ x, R < ‖x‖ → ψ.toFun x = 0) :
    dist φ ψ ≤ Real.sqrt (S.Γ.real (closedBall (0 : Rd d) (2 * R))) *
      dist (testToL2 φ) (testToL2 ψ) := by
  have hd : IsTestFunction (φ.toFun - ψ.toFun) := (testSub d).sub_mem φ.isTest ψ.isTest
  have hdR : ∀ x, R < ‖x‖ → (φ.toFun - ψ.toFun) x = 0 := fun x hx => by
    simp [hφ x hx, hψ x hx]
  have hb := spatialPair_self_le_L2 S.Γ hd hdR
  have e1 : dist φ ψ ^ 2 = spatialPair S.Γ (φ.toFun - ψ.toFun) (φ.toFun - ψ.toFun) := by
    rw [dist_eq_norm, ← real_inner_self_eq_norm_sq]
    rfl
  have e2 : dist (testToL2 φ) (testToL2 ψ) ^ 2 = ∫ x, (φ.toFun - ψ.toFun) x ^ 2 := by
    rw [dist_eq_norm, Lp.norm_def]
    have hae : ⇑(testToL2 φ - testToL2 ψ) =ᵐ[volume] (φ.toFun - ψ.toFun) := by
      filter_upwards [Lp.coeFn_sub (testToL2 φ) (testToL2 ψ),
        (VariationalFloor.memLp_test φ.isTest).coeFn_toLp,
        (VariationalFloor.memLp_test ψ.isTest).coeFn_toLp] with x h1 h2 h3
      rw [h1, Pi.sub_apply, Pi.sub_apply]
      unfold testToL2
      rw [h2, h3]
    rw [eLpNorm_congr_ae hae, SpatialFourLinear.integral_sq_eq_l2_sq
      (VariationalFloor.memLp_test hd)]
    rfl
  have hc : 0 ≤ S.Γ.real (closedBall (0 : Rd d) (2 * R)) := measureReal_nonneg
  have hsq : dist φ ψ ^ 2 ≤ (Real.sqrt (S.Γ.real (closedBall (0 : Rd d) (2 * R))) *
      dist (testToL2 φ) (testToL2 ψ)) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hc, e1, e2]
    exact hb
  exact (pow_le_pow_iff_left₀ dist_nonneg (by positivity) two_ne_zero).1 hsq

/-- Auxiliary: the tests vanishing outside the ball of radius `n` form a separable subset of
`SpPre S` (pulled back from the separable `L²(ℝ^d)` through `dist_le_L2`). -/
theorem isSeparable_ball (n : ℕ) :
    TopologicalSpace.IsSeparable {φ : SpPre S | ∀ x, (n : ℝ) < ‖x‖ → φ.toFun x = 0} := by
  classical
  set Sn := {φ : SpPre S | ∀ x, (n : ℝ) < ‖x‖ → φ.toFun x = 0} with hSn
  have : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by norm_num⟩
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense (Lp ℝ 2 (volume : Measure (Rd d)))
  have : Countable D := hDc.to_subtype
  set c : D × ℕ → SpPre S := fun dk =>
    if h : ∃ φ ∈ Sn, dist (testToL2 φ) (dk.1 : Lp ℝ 2 volume) < 1 / ((dk.2 : ℝ) + 1)
    then h.choose else 0 with hcdef
  refine ⟨range c, countable_range c, fun φ hφ => Metric.mem_closure_iff.2 fun ε hε => ?_⟩
  set C := Real.sqrt (S.Γ.real (closedBall (0 : Rd d) (2 * n)))
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt (show 0 < ε / (2 * (C + 1)) by positivity)
  obtain ⟨e, he, hde⟩ := hDd.exists_dist_lt (testToL2 φ)
    (show (0 : ℝ) < 1 / ((k : ℝ) + 1) by positivity)
  have hex : ∃ ψ ∈ Sn, dist (testToL2 ψ) ((⟨e, he⟩ : D) : Lp ℝ 2 volume) < 1 / ((k : ℝ) + 1) :=
    ⟨φ, hφ, hde⟩
  refine ⟨c (⟨e, he⟩, k), mem_range_self _, ?_⟩
  have hc : c (⟨e, he⟩, k) = hex.choose := by simp only [hcdef, hex, ↓reduceDIte]
  rw [hc]
  obtain ⟨hψS, hψd⟩ := hex.choose_spec
  have hL : dist (testToL2 φ) (testToL2 hex.choose) < 2 / ((k : ℝ) + 1) := by
    have := dist_triangle_right (testToL2 φ) (testToL2 hex.choose) e
    have e2 : 2 / ((k : ℝ) + 1) = 1 / ((k : ℝ) + 1) + 1 / ((k : ℝ) + 1) := by ring
    simp only at hψd
    linarith
  have hC : 0 ≤ C := Real.sqrt_nonneg _
  calc dist φ hex.choose ≤ C * dist (testToL2 φ) (testToL2 hex.choose) := dist_le_L2 hφ hψS
    _ ≤ C * (2 / ((k : ℝ) + 1)) := mul_le_mul_of_nonneg_left hL.le hC
    _ ≤ (C + 1) * (2 * (1 / ((k : ℝ) + 1))) := by
        rw [mul_one_div]
        exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ < (C + 1) * (2 * (ε / (2 * (C + 1)))) := by gcongr
    _ = ε := by field_simp

/-- `SpPre S` is separable. -/
instance separableSpace_SpPre : TopologicalSpace.SeparableSpace (SpPre S) := by
  refine TopologicalSpace.isSeparable_univ_iff.1 ?_
  have hU : (univ : Set (SpPre S)) =
      ⋃ n : ℕ, {φ : SpPre S | ∀ x, (n : ℝ) < ‖x‖ → φ.toFun x = 0} := by
    refine (eq_univ_of_forall fun φ => ?_).symm
    obtain ⟨R, -, hR⟩ := φ.isTest.2.exists_pos_le_norm
    obtain ⟨n, hn⟩ := exists_nat_ge R
    exact mem_iUnion.2 ⟨n, fun x hx => hR x (by linarith)⟩
  rw [hU]
  exact TopologicalSpace.IsSeparable.iUnion fun n => isSeparable_ball n

/-- `H_sp` is separable (`integrated_cameron_mean.tex` lines 213-214 at edf7085f: "countable
smooth-test density ... in `H_sp`"). -/
theorem separableSpace_Hsp : TopologicalSpace.SeparableSpace (Hsp S) := inferInstance

end Spatial

/-! ### The space `H_I` and the inclusion of `C_pos` -/

section Inclusion

open WeakSobolev (IsTestFunction)
open SpatialFourierBound (spatialPair)
open VariationalDilation (CPos rawCost)

variable {d : ℕ}

/-- **The space `H_I`** of `integrated_intrinsic_constant.tex` line 5 at edf7085f
(`H_I = H_t ⊗ H_sp`), built under decision 4 as the kernel completion of `L²(I; H_sp)`
(`HK p (Hsp S)`).  The TeX's identifications of `H_I` with the completion of space-time tests
(`integrated_cameron_mean.tex` lines 11-13) and with the Hilbert tensor product
(`L:cameron-supported-tensor`, lines 194-198) are not formalized. -/
abbrev HI (p : TParams) (S : SpData d) := HK p (Hsp S)

/-- Auxiliary: the slices `x ↦ Ψ(s,x)` of a smooth compactly supported space-time field are
test functions. -/
theorem slice_isTest {Ψ : ℝ × Rd d → ℝ} (hΨ : ContDiff ℝ ∞ Ψ) (hΨs : HasCompactSupport Ψ)
    (s : ℝ) : IsTestFunction fun x => Ψ (s, x) := by
  obtain ⟨R, -, hR⟩ := VariationalMean.exists_radius hΨs
  exact ⟨hΨ.comp (contDiff_const.prodMk contDiff_id),
    SpaceTimePositivity.slice_hasCompactSupport hR s⟩

variable (S : SpData d)

/-- The `H_sp`-valued field `s ↦ [Ψ(s,·)]` of a space-time field (its slices taken in `H_sp`). -/
def sliceField (Ψ : ℝ × Rd d → ℝ) (s : ℝ) : Hsp S := toHsp S fun x => Ψ (s, x)

variable {S}

/-- Auxiliary to the Lean proof route (the TeX's "`t ↦ Ψ_t` is continuous, bounded and compactly
supported as an `H_sp`-valued field", `integrated_intrinsic_constant.tex` lines 94-96 at
edf7085f): for a smooth compactly supported `Ψ`, `s ↦ [Ψ(s,·)]` is continuous into `H_sp` and
bounded. -/
theorem sliceField_continuous_bdd {Ψ : ℝ × Rd d → ℝ} (hΨ : ContDiff ℝ ∞ Ψ)
    (hΨs : HasCompactSupport Ψ) :
    Continuous (sliceField S Ψ) ∧ ∃ C, ∀ s, ‖sliceField S Ψ s‖ ≤ C := by
  obtain ⟨M, R, hM0, -, hM, hR⟩ := SpaceTimePositivity.field_data hΨ.continuous hΨs
  set C := volume.real (closedBall (0 : Rd d) R) * S.Γ.real (closedBall (0 : Rd d) (2 * R))
  have hC : 0 ≤ C := mul_nonneg measureReal_nonneg measureReal_nonneg
  have hsl := slice_isTest hΨ hΨs
  -- the squared distance of two slices
  have hdist : ∀ s t δ, (∀ x, |Ψ (s, x) - Ψ (t, x)| ≤ δ) →
      ‖sliceField S Ψ s - sliceField S Ψ t‖ ^ 2 ≤ δ * δ * C := by
    intro s t δ hδ
    unfold sliceField
    rw [← toHsp_sub (hsl s) (hsl t), norm_toHsp_sq ((testSub d).sub_mem (hsl s) (hsl t))]
    refine (le_abs_self _).trans ?_
    have h := SpaceTimePositivity.abs_spatialPair_le S.Γ
      (F := (fun x => Ψ (s, x)) - fun x => Ψ (t, x))
      (G := (fun x => Ψ (s, x)) - fun x => Ψ (t, x)) (R := R)
      (fun x hx => by simp [hR s x hx, hR t x hx]) (fun x hx => by simp [hR s x hx, hR t x hx])
      hδ hδ
    simpa only [C, mul_assoc] using h
  refine ⟨Metric.continuous_iff.2 fun s ε hε => ?_, ⟨Real.sqrt (M * M * C), fun s => ?_⟩⟩
  · set η := ε / (Real.sqrt C + 1)
    have hη : 0 < η := by positivity
    obtain ⟨δ, hδ, hδc⟩ := Metric.uniformContinuous_iff.mp
      (hΨs.uniformContinuous_of_continuous hΨ.continuous) η hη
    refine ⟨δ, hδ, fun t ht => ?_⟩
    have hpt : ∀ x, |Ψ (t, x) - Ψ (s, x)| ≤ η := by
      intro x
      have hd : dist (t, x) (s, x) < δ := by
        rw [Prod.dist_eq, dist_self, max_eq_left dist_nonneg]; exact ht
      exact (hδc hd).le
    have h2 := hdist t s η hpt
    rw [dist_eq_norm]
    have hs : ‖sliceField S Ψ t - sliceField S Ψ s‖ ≤ η * Real.sqrt C := by
      rw [← Real.sqrt_sq (norm_nonneg _), ← Real.sqrt_mul_self hη.le, ← Real.sqrt_mul
        (mul_self_nonneg η)]
      exact Real.sqrt_le_sqrt h2
    calc ‖sliceField S Ψ t - sliceField S Ψ s‖ ≤ η * Real.sqrt C := hs
      _ < ε := by
        have : η * Real.sqrt C < η * (Real.sqrt C + 1) := by
          have := Real.sqrt_nonneg C; nlinarith
        calc η * Real.sqrt C < η * (Real.sqrt C + 1) := this
          _ = ε := div_mul_cancel₀ _ (by positivity)
  · have h2 : ‖sliceField S Ψ s‖ ^ 2 ≤ M * M * C := by
      unfold sliceField
      rw [norm_toHsp_sq (hsl s)]
      refine (le_abs_self _).trans ?_
      have h := SpaceTimePositivity.abs_spatialPair_le S.Γ (F := fun x => Ψ (s, x))
        (G := fun x => Ψ (s, x)) (R := R) (hR s) (hR s) (fun x => hM _) (fun x => hM _)
      simpa only [C, mul_assoc] using h
    rw [← Real.sqrt_sq (norm_nonneg _)]
    exact Real.sqrt_le_sqrt h2

/-- The slice field of a smooth compactly supported field lies in `L²(I; H_sp)`. -/
theorem sliceField_memLp {Ψ : ℝ × Rd d → ℝ} (hΨ : ContDiff ℝ ∞ Ψ)
    (hΨs : HasCompactSupport Ψ) : MemLp (sliceField S Ψ) 2 timeMeasure := by
  obtain ⟨hc, C, hC⟩ := sliceField_continuous_bdd (S := S) hΨ hΨs
  exact MemLp.of_bound hc.aestronglyMeasurable C (ae_of_all _ hC)

/-- **The natural inclusion `C_pos → H_I`** of `L:positive-raw-embedding`
(`integrated_intrinsic_constant.tex` lines 32-33 and 95-97 at edf7085f): `Ψ ↦ J_{H_sp}(s ↦ Ψ_s)`,
the image of the `H_sp`-valued slice field; defined for smooth compactly supported fields (the
value `0` is taken otherwise). -/
def incl (p : TParams) (S : SpData d) (Ψ : ℝ × Rd d → ℝ) : HI p S :=
  open Classical in
  if h : ContDiff ℝ ∞ Ψ ∧ HasCompactSupport Ψ then
    J p (Hsp S) ((sliceField_memLp h.1 h.2).toLp (sliceField S Ψ))
  else 0

variable {p : TParams}

/-- `⟪incl Ψ, incl Φ⟫_{H_I} = ∫∫_{I²} |s-t|^{-a} B_Γ(Ψ(s,·), Φ(t,·))` (the space-time form
`SpaceTimePositivity.stForm`), for smooth compactly supported `Ψ, Φ`. -/
theorem inner_incl {Ψ Φ : ℝ × Rd d → ℝ} (hΨ : ContDiff ℝ ∞ Ψ) (hΨs : HasCompactSupport Ψ)
    (hΦ : ContDiff ℝ ∞ Φ) (hΦs : HasCompactSupport Φ) :
    ⟪incl p S Ψ, incl p S Φ⟫ = SpaceTimePositivity.stForm p.a S.Γ Ψ Φ := by
  simp only [incl, hΨ, hΨs, hΦ, hΦs, and_self, ↓reduceDIte]
  rw [(positive_bochner_inclusion _).2.2.2, kform_congr p.a
    (sliceField_memLp (S := S) hΨ hΨs).coeFn_toLp (sliceField_memLp (S := S) hΦ hΦs).coeFn_toLp]
  unfold kform SpaceTimePositivity.stForm SpaceTimePositivity.stPair
  congr 1; funext q
  unfold sliceField
  rw [inner_toHsp (slice_isTest hΨ hΨs q.1) (slice_isTest hΦ hΦs q.2)]

/-- **The first identity of `E:positive-raw-mean`** (`integrated_intrinsic_constant.tex`
lines 34-37 and 102-108 at edf7085f): for `Ψ ∈ C_pos`, `‖Ψ‖²_{H_I} = v_Ψ`
(`VariationalDilation.rawCost`, `E:compact-raw-cost`); with the integral form
`‖Ψ‖²_{H_I} = ∫∫ |s-t|^{-a} B_Γ(Ψ_s, Ψ_t)` and `v_Ψ ≥ 0`. -/
theorem norm_incl_sq {Ψ : ℝ × Rd d → ℝ} (hΨ : Ψ ∈ CPos d) :
    ‖incl p S Ψ‖ ^ 2 = SpaceTimePositivity.stForm p.a S.Γ Ψ Ψ ∧
      ‖incl p S Ψ‖ ^ 2 = rawCost p.a S.Γ Ψ ∧ 0 ≤ rawCost p.a S.Γ Ψ := by
  have h1 : ‖incl p S Ψ‖ ^ 2 = SpaceTimePositivity.stForm p.a S.Γ Ψ Ψ := by
    rw [← real_inner_self_eq_norm_sq, inner_incl hΨ.1 hΨ.2.1 hΨ.1 hΨ.2.1]
  have h2 : ‖incl p S Ψ‖ ^ 2 = rawCost p.a S.Γ Ψ := by
    rw [h1, SpaceTimePositivity.stForm_self_eq_rawCost p.ha1 S.Γ hΨ.1.continuous hΨ.2.1]
  exact ⟨h1, h2, h2 ▸ sq_nonneg _⟩

end Inclusion

/-! ### The square map `Q : H¹ → H_sp` -/

section Square

open WeakSobolev (IsTestFunction HasWeakGradient)
open SpatialFourierBound (spatialPair)
open SpatialFourLinear (IsH1Pair H1Tendsto C4 SquareBound isH1Pair_test C4_tendsto C4_test_eq
  isTest_sq four_integrable)
open OccupationKernelRow (pairMeasure)
open VariationalFloor (grad)

variable {d : ℕ}

variable (S : SpData d)

/-- `[φ²] ∈ H_sp` (the class of the square of a function; meaningful for test functions). -/
def sqHsp (φ : Rd d → ℝ) : Hsp S := toHsp S fun x => φ x ^ 2

variable {S}

/-- Auxiliary: `⟨[φ²], [ψ²]⟩_{H_sp} = C₄(φ,φ,ψ,ψ)` for test functions. -/
theorem inner_sqHsp {φ ψ : Rd d → ℝ} (hφ : IsTestFunction φ) (hψ : IsTestFunction ψ) :
    ⟪sqHsp S φ, sqHsp S ψ⟫ = C4 S.Γ φ φ ψ ψ := by
  unfold sqHsp
  rw [inner_toHsp (isTest_sq hφ) (isTest_sq hψ), C4_test_eq hφ hψ]

/-- Auxiliary: along test sequences converging in `H¹`, the inner products of the squares
converge to `C₄(f,f,h,h)` (`SpatialFourLinear.C4_tendsto`). -/
theorem tendsto_inner_sqHsp {alpha R : ℝ} (hB : SquareBound S.Γ alpha R) (hR0 : 0 ≤ R)
    (ha0 : 0 < alpha) (ha4 : alpha < 4) {φ ψ : ℕ → Rd d → ℝ} (hφ : ∀ n, IsTestFunction (φ n))
    (hψ : ∀ n, IsTestFunction (ψ n)) {f h : Rd d → ℝ} {g k : Rd d → Rd d} (hf : IsH1Pair f g)
    (hh : IsH1Pair h k) (hcφ : H1Tendsto φ (fun n => grad (φ n)) f g)
    (hcψ : H1Tendsto ψ (fun n => grad (ψ n)) h k) :
    Tendsto (fun n => ⟪sqHsp S (φ n), sqHsp S (ψ n)⟫) atTop (𝓝 (C4 S.Γ f f h h)) := by
  have e : (fun n => ⟪sqHsp S (φ n), sqHsp S (ψ n)⟫) =
      fun n => C4 S.Γ (φ n) (φ n) (ψ n) (ψ n) := funext fun n => inner_sqHsp (hφ n) (hψ n)
  rw [e]
  exact C4_tendsto hB hR0 ha0 ha4 (fun n => isH1Pair_test (hφ n)) (fun n => isH1Pair_test (hφ n))
    (fun n => isH1Pair_test (hψ n)) (fun n => isH1Pair_test (hψ n)) hf hf hh hh hcφ hcφ hcψ hcψ

/-- Auxiliary: `‖[φ_n²] - [ψ_n²]‖² → C₄(f,f,f,f) - 2C₄(f,f,h,h) + C₄(h,h,h,h)`. -/
theorem tendsto_norm_sub_sqHsp {alpha R : ℝ} (hB : SquareBound S.Γ alpha R) (hR0 : 0 ≤ R)
    (ha0 : 0 < alpha) (ha4 : alpha < 4) {φ ψ : ℕ → Rd d → ℝ} (hφ : ∀ n, IsTestFunction (φ n))
    (hψ : ∀ n, IsTestFunction (ψ n)) {f h : Rd d → ℝ} {g k : Rd d → Rd d} (hf : IsH1Pair f g)
    (hh : IsH1Pair h k) (hcφ : H1Tendsto φ (fun n => grad (φ n)) f g)
    (hcψ : H1Tendsto ψ (fun n => grad (ψ n)) h k) :
    Tendsto (fun n => ‖sqHsp S (φ n) - sqHsp S (ψ n)‖ ^ 2) atTop
      (𝓝 (C4 S.Γ f f f f - 2 * C4 S.Γ f f h h + C4 S.Γ h h h h)) := by
  have e : (fun n => ‖sqHsp S (φ n) - sqHsp S (ψ n)‖ ^ 2) = fun n =>
      ⟪sqHsp S (φ n), sqHsp S (φ n)⟫ - 2 * ⟪sqHsp S (φ n), sqHsp S (ψ n)⟫ +
        ⟪sqHsp S (ψ n), sqHsp S (ψ n)⟫ := by
    funext n
    rw [norm_sub_sq_real, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
  rw [e]
  exact ((tendsto_inner_sqHsp hB hR0 ha0 ha4 hφ hφ hf hf hcφ hcφ).sub
    ((tendsto_inner_sqHsp hB hR0 ha0 ha4 hφ hψ hf hh hcφ hcψ).const_mul 2)).add
    (tendsto_inner_sqHsp hB hR0 ha0 ha4 hψ hψ hh hh hcψ hcψ)

/-- Auxiliary to the Lean proof route (the Cauchy step of `L:occupation-raw-square`,
`integrated_occupation_ceiling.tex` lines 55-63 at edf7085f): for test functions `φ_n → f` in
`H¹`, the squares `[φ_n²]` form a Cauchy sequence in `H_sp`.  Route: by contradiction along two
subsequences, with the continuity of `C₄` (instead of the TeX's explicit difference bound). -/
theorem cauchySeq_sqHsp {alpha R : ℝ} (hB : SquareBound S.Γ alpha R) (hR0 : 0 ≤ R)
    (ha0 : 0 < alpha) (ha4 : alpha < 4) {φ : ℕ → Rd d → ℝ} (hφ : ∀ n, IsTestFunction (φ n))
    {f : Rd d → ℝ} {g : Rd d → Rd d} (hf : IsH1Pair f g)
    (hc : H1Tendsto φ (fun n => grad (φ n)) f g) : CauchySeq fun n => sqHsp S (φ n) := by
  rw [Metric.cauchySeq_iff]
  by_contra hcon
  push Not at hcon
  obtain ⟨ε, hε, hN⟩ := hcon
  choose m hm n hn hd using hN
  have hmt : Tendsto m atTop atTop := Filter.tendsto_atTop_mono hm tendsto_id
  have hnt : Tendsto n atTop atTop := Filter.tendsto_atTop_mono hn tendsto_id
  have h1 : H1Tendsto (fun k => φ (m k)) (fun k => grad (φ (m k))) f g :=
    And.intro (hc.1.comp hmt) (hc.2.comp hmt)
  have h2 : H1Tendsto (fun k => φ (n k)) (fun k => grad (φ (n k))) f g :=
    And.intro (hc.1.comp hnt) (hc.2.comp hnt)
  have T := tendsto_norm_sub_sqHsp hB hR0 ha0 ha4 (fun k => hφ (m k)) (fun k => hφ (n k)) hf hf
    h1 h2
  have hz : C4 S.Γ f f f f - 2 * C4 S.Γ f f f f + C4 S.Γ f f f f = 0 := by ring
  rw [hz] at T
  have hge : ∀ k, ε ^ 2 ≤ ‖sqHsp S (φ (m k)) - sqHsp S (φ (n k))‖ ^ 2 := fun k => by
    rw [← dist_eq_norm]; exact pow_le_pow_left₀ hε.le (hd k) 2
  have h0 := ge_of_tendsto' T hge
  have : 0 < ε ^ 2 := by positivity
  linarith

/-- Auxiliary: a fixed `H¹`-approximating sequence of test functions for every `H¹` profile
(`H1Density.h1TestDense`; the zero sequence otherwise). -/
def approx (f : Rd d → ℝ) : ℕ → Rd d → ℝ :=
  open Classical in
  if h : ∃ g, IsH1Pair f g then
    Classical.choose (H1Density.h1TestDense d f h.choose h.choose_spec.1 h.choose_spec.2.1
      h.choose_spec.2.2)
  else fun _ _ => 0

/-- Auxiliary: the approximating sequence consists of test functions converging in `H¹`. -/
theorem approx_spec {f : Rd d → ℝ} (h : ∃ g, IsH1Pair f g) :
    (∀ n, IsTestFunction (approx f n)) ∧
      H1Tendsto (approx f) (fun n => grad (approx f n)) f h.choose := by
  have hc := Classical.choose_spec (H1Density.h1TestDense d f h.choose h.choose_spec.1
    h.choose_spec.2.1 h.choose_spec.2.2)
  have e : approx f = Classical.choose (H1Density.h1TestDense d f h.choose h.choose_spec.1
      h.choose_spec.2.1 h.choose_spec.2.2) := by
    simp only [approx, h, ↓reduceDIte]
  rw [e]
  exact ⟨hc.1, hc.2.1, hc.2.2⟩

variable (S)

/-- **The square map `Q : H¹(ℝ^d;ℝ) → H_sp`** of `L:occupation-raw-square`
(`integrated_occupation_ceiling.tex` lines 26-30 and 55-63 at edf7085f): `Q(f) = lim [f_n²]` for
test functions `f_n → f` in `H¹`.  Defined on all functions (the limit of a fixed approximating
sequence; junk off `H¹`); `tendsto_Q` shows that every approximating sequence gives the same
limit. -/
def Q (f : Rd d → ℝ) : Hsp S := limUnder atTop fun n => sqHsp S (approx f n)

variable {S}

/-- **Well-definedness of `Q`** (TeX lines 62-63, "interlacing two approximating sequences
proves independence"): for every `H¹` pair `(f, g)` and test functions `φ_n → f` in `H¹`,
`[φ_n²] → Q(f)` in `H_sp`.  Hypotheses: `SquareBound Γ α R` (`P:spatial-four-linear`), `R ≥ 0`,
`0 < α < 4`. -/
theorem tendsto_Q {alpha R : ℝ} (hB : SquareBound S.Γ alpha R) (hR0 : 0 ≤ R) (ha0 : 0 < alpha)
    (ha4 : alpha < 4) {f : Rd d → ℝ} {g : Rd d → Rd d} (hf : IsH1Pair f g)
    {φ : ℕ → Rd d → ℝ} (hφ : ∀ n, IsTestFunction (φ n))
    (hc : H1Tendsto φ (fun n => grad (φ n)) f g) :
    Tendsto (fun n => sqHsp S (φ n)) atTop (𝓝 (Q S f)) := by
  have hex : ∃ g, IsH1Pair f g := ⟨g, hf⟩
  obtain ⟨hψt, hψc⟩ := approx_spec hex
  have hlim : Tendsto (fun n => sqHsp S (approx f n)) atTop (𝓝 (Q S f)) :=
    (cauchySeq_sqHsp hB hR0 ha0 ha4 hψt hex.choose_spec hψc).tendsto_limUnder
  have hd := tendsto_norm_sub_sqHsp hB hR0 ha0 ha4 hφ hψt hf hex.choose_spec hc hψc
  have hz : C4 S.Γ f f f f - 2 * C4 S.Γ f f f f + C4 S.Γ f f f f = 0 := by ring
  rw [hz] at hd
  have hd' : Tendsto (fun n => sqHsp S (φ n) - sqHsp S (approx f n)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have := hd.sqrt
    simpa only [Real.sqrt_zero, Real.sqrt_sq (norm_nonneg _)] using this
  simpa using hd'.add hlim

/-- Auxiliary: a test sequence converging in `H¹` to every `H¹` pair (`H1Density`). -/
theorem exists_test_seq {f : Rd d → ℝ} {g : Rd d → Rd d} (hf : IsH1Pair f g) :
    ∃ φ : ℕ → Rd d → ℝ, (∀ n, IsTestFunction (φ n)) ∧
      H1Tendsto φ (fun n => grad (φ n)) f g := by
  obtain ⟨φ, hφ, h1, h2⟩ := H1Density.h1TestDense d f g hf.1 hf.2.1 hf.2.2
  exact ⟨φ, hφ, And.intro h1 h2⟩

/-- **The inner products of `Q`** (the first display of `L:occupation-raw-square`,
`integrated_occupation_ceiling.tex` lines 28-30 at edf7085f): for `H¹` pairs,
`⟨Q(f), Q(h)⟩_{H_sp} = C₄(f,f,h,h)`, which is the physical `B_Γ(f², h²)` (`sqPair_toReal_eq`). -/
theorem inner_Q {alpha R : ℝ} (hB : SquareBound S.Γ alpha R) (hR0 : 0 ≤ R) (ha0 : 0 < alpha)
    (ha4 : alpha < 4) {f h : Rd d → ℝ} {g k : Rd d → Rd d} (hf : IsH1Pair f g)
    (hh : IsH1Pair h k) : ⟪Q S f, Q S h⟫ = C4 S.Γ f f h h := by
  obtain ⟨φ, hφ, hcφ⟩ := exists_test_seq hf
  obtain ⟨ψ, hψ, hcψ⟩ := exists_test_seq hh
  exact tendsto_nhds_unique ((tendsto_Q hB hR0 ha0 ha4 hf hφ hcφ).inner
    (tendsto_Q hB hR0 ha0 ha4 hh hψ hcψ)) (tendsto_inner_sqHsp hB hR0 ha0 ha4 hφ hψ hf hh hcφ hcψ)

/-- The real value of the physical pairing `B_Γ(f², h²)` (`OccupationPhysicalClass.sqPair`) is
the Bochner integral `C₄(f,f,h,h)`, for a.e.-strongly measurable `f, h`. -/
theorem sqPair_toReal_eq {f h : Rd d → ℝ} (hf : AEStronglyMeasurable f volume)
    (hh : AEStronglyMeasurable h volume) :
    (OccupationPhysicalClass.sqPair S.Γ f h).toReal = C4 S.Γ f f h h :=
  SpatialFourLinear.pairing_toReal_eq_C4 hf hh

/-- Auxiliary: the constant sequence converges in `H¹`. -/
theorem h1Tendsto_const (f : Rd d → ℝ) (g : Rd d → Rd d) :
    H1Tendsto (fun _ : ℕ => f) (fun _ => g) f g :=
  And.intro (by simp) (by simp)

/-- **Continuity of `Q`** (`integrated_occupation_ceiling.tex` lines 64-66), in sequential form: if `H¹` pairs `(u_n, v_n)`
converge in `H¹` to `(f, g)`, then `Q(u_n) → Q(f)` in `H_sp`. -/
theorem tendsto_Q_of_H1 {alpha R : ℝ} (hB : SquareBound S.Γ alpha R) (hR0 : 0 ≤ R)
    (ha0 : 0 < alpha) (ha4 : alpha < 4) {u : ℕ → Rd d → ℝ} {v : ℕ → Rd d → Rd d}
    {f : Rd d → ℝ} {g : Rd d → Rd d} (hu : ∀ n, IsH1Pair (u n) (v n)) (hf : IsH1Pair f g)
    (hc : H1Tendsto u v f g) : Tendsto (fun n => Q S (u n)) atTop (𝓝 (Q S f)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have e : (fun n => ‖Q S (u n) - Q S f‖ ^ 2) = fun n =>
      C4 S.Γ (u n) (u n) (u n) (u n) - 2 * C4 S.Γ (u n) (u n) f f + C4 S.Γ f f f f := by
    funext n
    rw [norm_sub_sq_real, ← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq,
      inner_Q hB hR0 ha0 ha4 (hu n) (hu n), inner_Q hB hR0 ha0 ha4 (hu n) hf,
      inner_Q hB hR0 ha0 ha4 hf hf]
  have t1 := C4_tendsto hB hR0 ha0 ha4 hu hu hu hu hf hf hf hf hc hc hc hc
  have t2 := C4_tendsto hB hR0 ha0 ha4 hu hu (fun _ => hf) (fun _ => hf) hf hf hf hf hc hc
    (h1Tendsto_const f g) (h1Tendsto_const f g)
  have T : Tendsto (fun n => ‖Q S (u n) - Q S f‖ ^ 2) atTop (𝓝 0) := by
    rw [e]
    have := (t1.sub (t2.const_mul 2)).add (tendsto_const_nhds (x := C4 S.Γ f f f f))
    convert this using 2
    ring
  have := T.sqrt
  simpa only [Real.sqrt_zero, Real.sqrt_sq (norm_nonneg _)] using this

/-- On a test function, `Q(φ) = [φ²]` (the constant approximating sequence). -/
theorem Q_of_test {alpha R : ℝ} (hB : SquareBound S.Γ alpha R) (hR0 : 0 ≤ R) (ha0 : 0 < alpha)
    (ha4 : alpha < 4) {φ : Rd d → ℝ} (hφ : IsTestFunction φ) : Q S φ = sqHsp S φ :=
  tendsto_nhds_unique (tendsto_Q hB hR0 ha0 ha4 (isH1Pair_test hφ) (fun _ => hφ)
    (h1Tendsto_const φ (grad φ))) tendsto_const_nhds

/-- Auxiliary: `H¹` pairs are stable under a.e. changes of the function. -/
theorem isH1Pair_congr_ae {f f' : Rd d → ℝ} {g : Rd d → Rd d} (hf : IsH1Pair f g)
    (h : f =ᵐ[volume] f') : IsH1Pair f' g := by
  refine ⟨hf.1.ae_eq h, hf.2.1, fun φ hφ v => ?_⟩
  rw [← hf.2.2 φ hφ v]
  refine integral_congr_ae ?_
  filter_upwards [h] with x hx
  rw [hx]

/-- `Q(f)` depends only on the a.e.-class of `f ∈ H¹`. -/
theorem Q_congr_ae {alpha R : ℝ} (hB : SquareBound S.Γ alpha R) (hR0 : 0 ≤ R) (ha0 : 0 < alpha)
    (ha4 : alpha < 4) {f f' : Rd d → ℝ} {g : Rd d → Rd d} (hf : IsH1Pair f g)
    (h : f =ᵐ[volume] f') : Q S f' = Q S f := by
  obtain ⟨φ, hφ, hcφ⟩ := exists_test_seq hf
  have hc' : H1Tendsto φ (fun n => grad (φ n)) f' g := by
    refine And.intro ?_ hcφ.2
    have e : ∀ n, eLpNorm (fun x => φ n x - f' x) 2 volume =
        eLpNorm (fun x => φ n x - f x) 2 volume := fun n =>
      eLpNorm_congr_ae (h.mono fun x hx => by simp only; rw [hx])
    simp_rw [e]
    exact hcφ.1
  exact tendsto_nhds_unique (tendsto_Q hB hR0 ha0 ha4 (isH1Pair_congr_ae hf h) hφ hc')
    (tendsto_Q hB hR0 ha0 ha4 hf hφ hcφ)

/-- Auxiliary: for test functions, `C₄(a,b,c,e) = B_Γ(ab, ce)` (Fubini). -/
theorem C4_test_eq_gen {alpha R : ℝ} (hB : SquareBound S.Γ alpha R) (hR0 : 0 ≤ R)
    {a b c e : Rd d → ℝ} (ha : IsTestFunction a) (hb : IsTestFunction b)
    (hc : IsTestFunction c) (he : IsTestFunction e) :
    C4 S.Γ a b c e = spatialPair S.Γ (fun x => a x * b x) (fun x => c x * e x) := by
  have hi := four_integrable hB hR0 (isH1Pair_test ha) (isH1Pair_test hb) (isH1Pair_test hc)
    (isH1Pair_test he)
  unfold C4 spatialPair
  rw [integral_prod_symm _ hi]
  congr 1; funext y; congr 1; funext x; ring

/-- The physical pairing `B_Γ(φ, f²) = ∫ φ(x) f(x-y)² dx Γ(dy)` (`E:spatial-physical-pair`,
signed, as a Bochner integral over `ν = dx Γ(dy)`). -/
def testSqPair (S : SpData d) (φ f : Rd d → ℝ) : ℝ :=
  ∫ q, φ q.1 * f (q.1 - q.2) ^ 2 ∂(pairMeasure S.Γ)

/-- **Pairing of a test function with `Q(f)`** (`integrated_occupation_ceiling.tex` lines 88-95 at edf7085f,
`⟨Ψ_t, Q(f)⟩_{H_sp} = B_Γ(Ψ_t, f²)`): for a test function `φ` and an `H¹` pair `(f, g)`,
`⟨[φ], Q(f)⟩_{H_sp} = ∫ φ(x) f(x-y)² dx Γ(dy)`.  Route as in the TeX: a test `χ = 1` on the
support of `φ` and the continuity of `C₄(χ, φ, ·, ·)`. -/
theorem inner_toHsp_Q {alpha R : ℝ} (hB : SquareBound S.Γ alpha R) (hR0 : 0 ≤ R)
    (ha0 : 0 < alpha) (ha4 : alpha < 4) {φ : Rd d → ℝ} (hφ : IsTestFunction φ)
    {f : Rd d → ℝ} {g : Rd d → Rd d} (hf : IsH1Pair f g) :
    ⟪toHsp S φ, Q S f⟫ = testSqPair S φ f := by
  obtain ⟨Rφ, -, hRφ⟩ := hφ.2.exists_pos_le_norm
  obtain ⟨n, hn⟩ := exists_nat_ge Rφ
  set χ : Rd d → ℝ := H1Density.cutoff n with hχdef
  have hχ : IsTestFunction χ :=
    ⟨H1Density.cutoff_contDiff n, H1Density.cutoff_hasCompactSupport n⟩
  have hχφ : ∀ x, χ x * φ x = φ x := by
    intro x
    by_cases hx : ‖x‖ ≤ (n : ℝ) + 1
    · rw [hχdef, H1Density.cutoff_eq_one hx, one_mul]
    · rw [hRφ x (by linarith), mul_zero]
  obtain ⟨ψ, hψ, hcψ⟩ := exists_test_seq hf
  have e : ∀ m, ⟪toHsp S φ, sqHsp S (ψ m)⟫ = C4 S.Γ χ φ (ψ m) (ψ m) := by
    intro m
    unfold sqHsp
    rw [inner_toHsp hφ (isTest_sq (hψ m)), C4_test_eq_gen hB hR0 hχ hφ (hψ m) (hψ m)]
    congr 1
    · funext x; exact (hχφ x).symm
    · funext x; ring
  have T1 : Tendsto (fun m => ⟪toHsp S φ, sqHsp S (ψ m)⟫) atTop (𝓝 ⟪toHsp S φ, Q S f⟫) :=
    tendsto_const_nhds.inner (tendsto_Q hB hR0 ha0 ha4 hf hψ hcψ)
  have T2 : Tendsto (fun m => ⟪toHsp S φ, sqHsp S (ψ m)⟫) atTop (𝓝 (C4 S.Γ χ φ f f)) := by
    simp_rw [e]
    exact C4_tendsto hB hR0 ha0 ha4 (fun _ => isH1Pair_test hχ) (fun _ => isH1Pair_test hφ)
      (fun m => isH1Pair_test (hψ m)) (fun m => isH1Pair_test (hψ m)) (isH1Pair_test hχ)
      (isH1Pair_test hφ) hf hf (h1Tendsto_const _ _) (h1Tendsto_const _ _) hcψ hcψ
  rw [tendsto_nhds_unique T1 T2]
  unfold C4 testSqPair
  congr 1; funext q
  rw [hχφ q.1]
  ring

end Square

/-! ### Measurability in a separable metric space -/

/-- Auxiliary to the Lean proof route (in place of the TeX's strong measurability of
`s ↦ Q(g_s)` from the continuity of `Q`, `integrated_occupation_ceiling.tex` line 72): a map into a
second-countable metric space is measurable as soon as its distances to the points of a dense set
are measurable functions. -/
theorem measurable_of_dist_dense {X : Type*} [MetricSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X] {α : Type*} [MeasurableSpace α] {F : α → X} {D : Set X}
    (hD : Dense D) (h : ∀ x ∈ D, Measurable fun s => dist (F s) x) : Measurable F := by
  obtain ⟨T, hTD, hTc, hTd⟩ := hD.exists_countable_dense_subset
  refine measurable_of_isOpen fun U hU => ?_
  have hrepr : F ⁻¹' U = ⋃ x ∈ T, ⋃ q : ℚ, {s | ball x q ⊆ U ∧ dist (F s) x < q} := by
    ext s
    simp only [mem_preimage, mem_iUnion, Set.mem_ofPred_eq, exists_prop]
    constructor
    · intro hs
      obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.1 hU _ hs
      obtain ⟨x, hxT, hx⟩ := hTd.exists_dist_lt (F s) (show 0 < r / 3 by positivity)
      obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show r / 3 < 2 * r / 3 by linarith)
      refine ⟨x, hxT, q, fun z hz => hrU ?_, by linarith⟩
      rw [mem_ball] at hz ⊢
      have := dist_triangle z x (F s)
      rw [dist_comm x (F s)] at this
      linarith
    · rintro ⟨x, -, q, hU', hd⟩
      exact hU' (mem_ball.2 hd)
  rw [hrepr]
  refine MeasurableSet.biUnion hTc fun x hx => MeasurableSet.iUnion fun q => ?_
  rw [Set.ofPred_and]
  exact (MeasurableSet.const _).inter (measurableSet_lt (h x (hTD hx)) measurable_const)

/-! ### The occupation element `ρ_g` -/

section Occupation

open WeakSobolev (IsTestFunction)
open SpatialFourierBound (spatialPair)
open SpatialFourLinear (IsH1Pair C4 SquareBound)
open OccupationPhysicalClass (volI sqPair gradSqE Tlin IsOccField SquarePairingBounds)
open OccupationKernelRow (pairMeasure pairing)
open SpatialStaticControls (IsUnitH1)
open VariationalDilation (CPos rawCost)

variable {d : ℕ} (S : SpData d)

/-- The `H_sp`-valued field `F_g(s) = Q(g_s)` of `L:occupation-raw-square`
(`integrated_occupation_ceiling.tex` line 72 at edf7085f), for a field given by its joint
representative `G` (`g_s = G s`). -/
def sqField (G : ℝ → Rd d → ℝ) (s : ℝ) : Hsp S := Q S (G s)

variable {S}

/-- Auxiliary: for a jointly measurable `Gm`, `s ↦ B_Γ(φ, Gm(s,·)²)` is measurable. -/
theorem measurable_testSqPair {Gm : ℝ × Rd d → ℝ} (hGm : Measurable Gm) {φ : Rd d → ℝ}
    (hφ : Continuous φ) : Measurable fun s => testSqPair S φ fun x => Gm (s, x) := by
  have hm : StronglyMeasurable (Function.uncurry fun (s : ℝ) (q : Rd d × Rd d) =>
      φ q.1 * Gm (s, q.1 - q.2) ^ 2) := by
    apply Measurable.stronglyMeasurable
    exact (hφ.measurable.comp measurable_snd.fst).mul
      ((hGm.comp (measurable_fst.prodMk (measurable_snd.fst.sub measurable_snd.snd))).pow_const 2)
  exact (hm.integral_prod_right (ν := pairMeasure S.Γ)).measurable

/-- Auxiliary: for a jointly measurable `Gm`, `s ↦ B_Γ(Gm(s,·)², Gm(s,·)²)` is measurable. -/
theorem measurable_sqPair_diag {Gm : ℝ × Rd d → ℝ} (hGm : Measurable Gm) :
    Measurable fun s => sqPair S.Γ (fun x => Gm (s, x)) (fun x => Gm (s, x)) := by
  have hF : Measurable fun q : ℝ × (Rd d × Rd d) =>
      ENNReal.ofReal (Gm (q.1, q.2.1) ^ 2) * ENNReal.ofReal (Gm (q.1, q.2.1 - q.2.2) ^ 2) := by
    have h1 : Measurable fun q : ℝ × (Rd d × Rd d) => Gm (q.1, q.2.1) :=
      hGm.comp (measurable_fst.prodMk measurable_snd.fst)
    have h2 : Measurable fun q : ℝ × (Rd d × Rd d) => Gm (q.1, q.2.1 - q.2.2) :=
      hGm.comp (measurable_fst.prodMk (measurable_snd.fst.sub measurable_snd.snd))
    exact (ENNReal.measurable_ofReal.comp (h1.pow_const 2)).mul
      (ENNReal.measurable_ofReal.comp (h2.pow_const 2))
  unfold sqPair pairing
  exact hF.lintegral_prod_right'

/-- **Strong measurability of `s ↦ Q(g_s)`** (`integrated_occupation_ceiling.tex` line 72 at
edf7085f) for a field of the class `𝒪` modelled by joint representatives
(`OccupationPhysicalClass.IsOccField`).  Route (differs from the TeX, which derives it from the
strong `H¹`-measurability of the field and the continuity of `Q`): `H_sp` is separable, and the
distances `‖Q(g_s) - [φ]‖² = A_sp(g_s) - 2 B_Γ(φ, g_s²) + B_Γ(φ, φ)` to the dense test classes
are measurable by Tonelli/Fubini on a measurable joint representative. -/
theorem sqField_aestronglyMeasurable {alpha R : ℝ} (hB : SquareBound S.Γ alpha R) (hR0 : 0 ≤ R)
    (ha0 : 0 < alpha) (ha4 : alpha < 4) {G : ℝ → Rd d → ℝ} {DG : ℝ → Rd d → Rd d}
    (hO : IsOccField G DG) : AEStronglyMeasurable (sqField S G) volI := by
  classical
  let : MeasurableSpace (Hsp S) := borel _
  have : BorelSpace (Hsp S) := ⟨rfl⟩
  set Gm : ℝ × Rd d → ℝ := hO.meas.mk _ with hGmdef
  have hGm : Measurable Gm := hO.meas.stronglyMeasurable_mk.measurable
  have hae : ∀ᵐ s ∂volI, G s =ᵐ[volume] fun x => Gm (s, x) :=
    Measure.ae_ae_of_ae_prod hO.meas.ae_eq_mk
  have hP : ∀ᵐ s ∂volI, IsH1Pair (G s) (DG s) ∧ (G s =ᵐ[volume] fun x => Gm (s, x)) := by
    filter_upwards [hO.unit, hae] with s hu he
    exact ⟨⟨hu.1, hu.2.1, hu.2.2.1⟩, he⟩
  set N := toMeasurable volI {s | ¬ ∃ g, IsH1Pair (fun x => Gm (s, x)) g} with hNdef
  have hNae : ∀ᵐ s ∂volI, s ∉ N := by
    have h1 : ∀ᵐ s ∂volI, ∃ g, IsH1Pair (fun x => Gm (s, x)) g :=
      hP.mono fun s hs => ⟨DG s, isH1Pair_congr_ae hs.1 hs.2⟩
    rw [ae_iff] at h1 ⊢
    simpa [hNdef, measure_toMeasurable] using h1
  have hgood : ∀ s ∉ N, ∃ g, IsH1Pair (fun x => Gm (s, x)) g := fun s hs => by
    by_contra h
    exact hs (subset_toMeasurable _ _ h)
  set Fm : ℝ → Hsp S := fun s => if s ∈ N then 0 else Q S (fun x => Gm (s, x)) with hFmdef
  have hFm : Measurable Fm := by
    refine measurable_of_dist_dense (dense_range_toHsp (S := S)) ?_
    rintro x ⟨φ, hφ, rfl⟩
    have hA : Measurable fun s =>
        (sqPair S.Γ (fun x => Gm (s, x)) (fun x => Gm (s, x))).toReal :=
      (measurable_sqPair_diag hGm).ennreal_toReal
    have hBm := measurable_testSqPair (S := S) hGm hφ.1.continuous
    have e : (fun s => dist (Fm s) (toHsp S φ)) = fun s => if s ∈ N then ‖toHsp S φ‖ else
        Real.sqrt ((sqPair S.Γ (fun x => Gm (s, x)) (fun x => Gm (s, x))).toReal -
          2 * testSqPair S φ (fun x => Gm (s, x)) + spatialPair S.Γ φ φ) := by
      funext s
      by_cases hs : s ∈ N
      · simp only [hFmdef, hs, ↓reduceIte, dist_eq_norm, zero_sub, norm_neg]
      · obtain ⟨g, hg⟩ := hgood s hs
        simp only [hFmdef, hs, ↓reduceIte]
        rw [dist_eq_norm, ← Real.sqrt_sq (norm_nonneg _), norm_sub_sq_real, real_inner_comm,
          inner_toHsp_Q hB hR0 ha0 ha4 hφ hg, ← real_inner_self_eq_norm_sq,
          inner_Q hB hR0 ha0 ha4 hg hg, norm_toHsp_sq hφ,
          sqPair_toReal_eq hg.1.aestronglyMeasurable hg.1.aestronglyMeasurable]
    rw [e]
    exact Measurable.ite (measurableSet_toMeasurable _ _) measurable_const
      ((hA.sub (hBm.const_mul 2)).add measurable_const).sqrt
  have hFae : Fm =ᵐ[volI] sqField S G := by
    filter_upwards [hP, hNae] with s hs hsN
    simp only [hFmdef, hsN, ↓reduceIte, sqField]
    exact Q_congr_ae hB hR0 ha0 ha4 hs.1 hs.2
  exact hFm.stronglyMeasurable.aestronglyMeasurable.congr hFae

/-- **Square integrability of `s ↦ Q(g_s)`** (`integrated_occupation_ceiling.tex` lines 72-78
at edf7085f: `∫_I ‖F_g(s)‖² ≤ R_sp ∫_I b_s^{α/2} ≤ R_sp T(g)^{α/2} < ∞`) for a field of `𝒪`
(joint representatives), with the bounds `SquarePairingBounds Γ α R` (`P:spatial-four-linear`)
and `0 < α < 2`. -/
theorem sqField_memLp {alpha R : ℝ} (hB : SquareBound S.Γ alpha R)
    (hSPB : SquarePairingBounds S.Γ alpha R) (hR0 : 0 ≤ R) (ha0 : 0 < alpha) (ha2 : alpha < 2)
    {G : ℝ → Rd d → ℝ} {DG : ℝ → Rd d → Rd d} (hO : IsOccField G DG) :
    MemLp (sqField S G) 2 volI := by
  have hm := sqField_aestronglyMeasurable hB hR0 ha0 (by linarith) hO
  refine (memLp_two_iff_integrable_sq_norm hm).2 ⟨hm.norm.pow 2, ?_⟩
  have hle : ∀ᵐ s ∂volI, ‖‖sqField S G s‖ ^ 2‖ₑ ≤
      ENNReal.ofReal R * gradSqE (DG s) ^ (alpha / 2) := by
    filter_upwards [hO.unit] with s hu
    have hp : IsH1Pair (G s) (DG s) := ⟨hu.1, hu.2.1, hu.2.2.1⟩
    rw [sqField, ← real_inner_self_eq_norm_sq, inner_Q hB hR0 ha0 (by linarith) hp hp,
      ← sqPair_toReal_eq hp.1.aestronglyMeasurable hp.1.aestronglyMeasurable,
      Real.enorm_of_nonneg ENNReal.toReal_nonneg]
    exact ENNReal.ofReal_toReal_le.trans
      (OccupationPhysicalClass.sqPair_self_le hR0 ha0.le hSPB hu)
  refine lt_of_le_of_lt (lintegral_mono_ae hle) ?_
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top (lt_of_le_of_lt
    (OccupationPhysicalClass.lintegral_rpow_le
      (OccupationPhysicalClass.gradSqE_aemeasurable hO.meas_grad) (by positivity)
      (by linarith)) ?_)
  exact ENNReal.rpow_lt_top_of_nonneg (by positivity) hO.energy_lt_top.ne

/-- **The occupation element `ρ_g = J_{H_sp}(s ↦ Q(g_s)) ∈ H_I`** of `L:occupation-raw-square`
(`integrated_occupation_ceiling.tex` lines 32-33 and 79-80 at edf7085f), for a field given by its
joint representative `G`; the value `0` is taken when `s ↦ Q(g_s)` is not in `L²(I; H_sp)`
(never on `𝒪`: `sqField_memLp`). -/
def rho (p : TParams) (S : SpData d) (G : ℝ → Rd d → ℝ) : HI p S :=
  open Classical in
  if h : MemLp (sqField S G) 2 timeMeasure then J p (Hsp S) (h.toLp (sqField S G)) else 0

variable {p : TParams}

/-- **`‖ρ_g‖²_{H_I} = A(g)`** (the first identity of `E:occupation-raw-identities`,
`integrated_occupation_ceiling.tex` lines 34-38 at edf7085f), for a field of `𝒪` (joint
representatives): `A(g) = ∫∫_{I²} |s-t|^{-a} B_Γ(g_s², g_t²)` is
`RawOccupationEnergy.A` (the real value of the extended integral `RawOccupationEnergy.Araw`). -/
theorem norm_rho_sq {alpha R : ℝ} (hB : SquareBound S.Γ alpha R)
    (hSPB : SquarePairingBounds S.Γ alpha R) (hR0 : 0 ≤ R) (ha0 : 0 < alpha) (ha2 : alpha < 2)
    {G : ℝ → Rd d → ℝ} {DG : ℝ → Rd d → Rd d} (hO : IsOccField G DG) :
    ‖rho p S G‖ ^ 2 = RawOccupationEnergy.A p.a S.Γ G := by
  have ha4 : alpha < 4 := by linarith
  have hm := sqField_memLp hB hSPB hR0 ha0 ha2 hO
  simp only [rho, hm, ↓reduceDIte]
  rw [(positive_bochner_inclusion _).2.1]
  change kform p.a _ _ = _
  rw [kform_congr p.a hm.coeFn_toLp hm.coeFn_toLp]
  have hfin : ∀ {f h : Rd d → ℝ} {gf gh : Rd d → Rd d}, IsUnitH1 f gf → IsUnitH1 h gh →
      sqPair S.Γ f h ≠ ⊤ := by
    intro f h gf gh hf hh htop
    have h1 := hSPB.homogeneous f gf hf.1 hf.2.1 hf.2.2.1
    have h2 := hSPB.homogeneous h gh hh.1 hh.2.1 hh.2.2.1
    have h3 := hSPB.squareCS f gf h gh hf.1 hf.2.1 hf.2.2.1 hh.1 hh.2.1 hh.2.2.1
    rw [htop] at h3
    have : (⊤ : ℝ≥0∞) ^ 2 = ⊤ := by norm_num
    rw [this] at h3
    exact (ENNReal.mul_lt_top (h1.trans_lt ENNReal.ofReal_lt_top)
      (h2.trans_lt ENNReal.ofReal_lt_top)).ne (top_le_iff.1 h3)
  have hpair : ∀ᵐ q ∂(volI.prod volI), kern p.a (q.1 - q.2) * ⟪sqField S G q.1, sqField S G q.2⟫ =
      kern p.a (q.1 - q.2) * (sqPair S.Γ (G q.1) (G q.2)).toReal := by
    filter_upwards [OccupationPhysicalClass.ae_prod_both hO.unit] with q hq
    have h1 : IsH1Pair (G q.1) (DG q.1) := ⟨hq.1.1, hq.1.2.1, hq.1.2.2.1⟩
    have h2 : IsH1Pair (G q.2) (DG q.2) := ⟨hq.2.1, hq.2.2.1, hq.2.2.2.1⟩
    rw [sqField, sqField, inner_Q hB hR0 ha0 ha4 h1 h2,
      sqPair_toReal_eq h1.1.aestronglyMeasurable h2.1.aestronglyMeasurable]
  unfold kform
  rw [integral_congr_ae hpair]
  have hsm := OccupationPhysicalClass.sqPair_aemeasurable S.Γ hO.meas
  have hkm : Measurable fun q : ℝ × ℝ => kern p.a (q.1 - q.2) :=
    (measurable_kern p.a).comp (measurable_fst.sub measurable_snd)
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun q => mul_nonneg (kern_nonneg _ _)
    ENNReal.toReal_nonneg) (hkm.aestronglyMeasurable.mul hsm.ennreal_toReal.aestronglyMeasurable)]
  unfold RawOccupationEnergy.A RawOccupationEnergy.Araw
  congr 1
  have hmeas : AEMeasurable (fun q : ℝ × ℝ =>
      ENNReal.ofReal (kern p.a (q.1 - q.2)) * sqPair S.Γ (G q.1) (G q.2)) (volI.prod volI) :=
    (RawOccupationEnergy.kern_meas p.a).aemeasurable.mul hsm
  rw [← lintegral_prod _ hmeas]
  refine lintegral_congr_ae ?_
  filter_upwards [OccupationPhysicalClass.ae_prod_both hO.unit] with q hq
  rw [ENNReal.ofReal_mul (kern_nonneg _ _), ENNReal.ofReal_toReal (hfin hq.1 hq.2)]

/-- **The final display of `L:occupation-raw-square`** (`integrated_occupation_ceiling.tex`
lines 40-42 and 105-106 at edf7085f), in `H_I`: for `Ψ ∈ C_pos` and a field of `𝒪` (joint
representatives), `⟨Ψ, ρ_g⟩_{H_I} ≤ √(v_Ψ A(g))`, by Hilbert Cauchy-Schwarz with
`‖Ψ‖² = v_Ψ` and `‖ρ_g‖² = A(g)`. -/
theorem inner_incl_rho_le {alpha R : ℝ} (hB : SquareBound S.Γ alpha R)
    (hSPB : SquarePairingBounds S.Γ alpha R) (hR0 : 0 ≤ R) (ha0 : 0 < alpha) (ha2 : alpha < 2)
    {G : ℝ → Rd d → ℝ} {DG : ℝ → Rd d → Rd d} (hO : IsOccField G DG) {Ψ : ℝ × Rd d → ℝ}
    (hΨ : Ψ ∈ CPos d) :
    ⟪incl p S Ψ, rho p S G⟫ ≤ Real.sqrt (rawCost p.a S.Γ Ψ * RawOccupationEnergy.A p.a S.Γ G) := by
  calc ⟪incl p S Ψ, rho p S G⟫ ≤ ‖incl p S Ψ‖ * ‖rho p S G‖ := real_inner_le_norm _ _
    _ = Real.sqrt (‖incl p S Ψ‖ ^ 2 * ‖rho p S G‖ ^ 2) := by
        rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _),
          Real.sqrt_sq (norm_nonneg _)]
    _ = _ := by rw [(norm_incl_sq hΨ).2.1, norm_rho_sq hB hSPB hR0 ha0 ha2 hO]

/-- **The polarized pairing of `L:occupation-raw-square`** (`integrated_occupation_ceiling.tex`
lines 96-101 at edf7085f): for a smooth compactly supported `Ψ` and a field of `𝒪` (joint
representatives),
`⟨Ψ, ρ_g⟩_{H_I} = ∫∫_{I²} |s-t|^{-a} B_Γ(Ψ_s, g_t²) ds dt` with the physical
`B_Γ(Ψ_s, g_t²) = ∫ Ψ(s,x) g_t(x-y)² dx Γ(dy)` (`testSqPair`).  The remaining step of the TeX
(evenness of `Γ` and Tonelli, giving `∫_I ∫ h_{Ψ,s} g_s²`) is `inner_incl_rho_mean`. -/
theorem inner_incl_rho {alpha R : ℝ} (hB : SquareBound S.Γ alpha R)
    (hSPB : SquarePairingBounds S.Γ alpha R) (hR0 : 0 ≤ R) (ha0 : 0 < alpha) (ha2 : alpha < 2)
    {G : ℝ → Rd d → ℝ} {DG : ℝ → Rd d → Rd d} (hO : IsOccField G DG) {Ψ : ℝ × Rd d → ℝ}
    (hΨ : ContDiff ℝ ∞ Ψ) (hΨs : HasCompactSupport Ψ) :
    ⟪incl p S Ψ, rho p S G⟫ = ∫ q, kern p.a (q.1 - q.2) *
      testSqPair S (fun x => Ψ (q.1, x)) (G q.2) ∂(timeMeasure.prod timeMeasure) := by
  have hm := sqField_memLp hB hSPB hR0 ha0 ha2 hO
  simp only [incl, rho, hm, hΨ, hΨs, and_self, ↓reduceDIte]
  rw [(positive_bochner_inclusion _).2.2.2, kform_congr p.a
    (sliceField_memLp (S := S) hΨ hΨs).coeFn_toLp hm.coeFn_toLp]
  unfold kform
  refine integral_congr_ae ?_
  filter_upwards [(Measure.quasiMeasurePreserving_snd (μ := volI) (ν := volI)).ae hO.unit]
    with q hq
  have h2 : IsH1Pair (G q.2) (DG q.2) := ⟨hq.1, hq.2.1, hq.2.2.1⟩
  unfold sliceField sqField
  rw [inner_toHsp_Q hB hR0 ha0 (by linarith) (slice_isTest hΨ hΨs q.1) h2]

end Occupation

/-! ### The mean form of `⟨Ψ, ρ_g⟩` (evenness and Tonelli) -/

section MeanIdentity

open WeakSobolev (IsTestFunction)
open SpatialFourLinear (IsH1Pair SquareBound four_integrable isH1Pair_test)
open OccupationPhysicalClass (volI IsOccField SquarePairingBounds)
open OccupationKernelRow (pairMeasure)
open VariationalDilation (CPos mean conv)

variable {d : ℕ}

/-- Auxiliary to the Lean proof route (the evenness/Tonelli step of `L:occupation-raw-square`,
`integrated_occupation_ceiling.tex` lines 103-105 at edf7085f, in one spatial slice pair): for an even
s-finite `Γ` and measurable `A, B : ℝ^d → [0,∞]`,
`∫∫ A(x) B(x-y) dx Γ(dy) = ∫ B(x) (∫ A(x-y) Γ(dy)) dx` (Tonelli, translation invariance of
Lebesgue measure, and `Γ(-dy) = Γ(dy)`). -/
theorem lintegral_pair_even {Γ : Measure (Rd d)} [SFinite Γ] (hE : IsEven Γ)
    {A B : Rd d → ℝ≥0∞} (hA : Measurable A) (hB : Measurable B) :
    ∫⁻ z, A z.1 * B (z.1 - z.2) ∂(pairMeasure Γ) = ∫⁻ x, B x * ∫⁻ y, A (x - y) ∂Γ := by
  have h1 : Measurable fun z : Rd d × Rd d => A z.1 * B (z.1 - z.2) :=
    (hA.comp measurable_fst).mul (hB.comp (measurable_fst.sub measurable_snd))
  have hH : Measurable fun y : Rd d => ∫⁻ x, A (x + y) * B x := by
    have : Measurable fun w : Rd d × Rd d => A (w.2 + w.1) * B w.2 :=
      (hA.comp (measurable_snd.add measurable_fst)).mul (hB.comp measurable_snd)
    exact this.lintegral_prod_right'
  have h2 : Measurable fun w : Rd d × Rd d => A (w.2 - w.1) * B w.2 :=
    (hA.comp (measurable_snd.sub measurable_fst)).mul (hB.comp measurable_snd)
  calc ∫⁻ z, A z.1 * B (z.1 - z.2) ∂(pairMeasure Γ)
      = ∫⁻ x, ∫⁻ y, A x * B (x - y) ∂Γ := lintegral_prod _ h1.aemeasurable
    _ = ∫⁻ y, ∫⁻ x, A x * B (x - y) ∂volume ∂Γ := lintegral_lintegral_swap h1.aemeasurable
    _ = ∫⁻ y, ∫⁻ x, A (x + y) * B x ∂volume ∂Γ := lintegral_congr fun y => by
          rw [← lintegral_add_right_eq_self (fun x => A x * B (x - y)) y]
          simp only [add_sub_cancel_right]
    _ = ∫⁻ y, ∫⁻ x, A (x + y) * B x ∂volume ∂(Γ.map fun x => -x) := by rw [hE]
    _ = ∫⁻ y, ∫⁻ x, A (x + -y) * B x ∂volume ∂Γ := lintegral_map hH measurable_neg
    _ = ∫⁻ y, ∫⁻ x, A (x - y) * B x ∂volume ∂Γ := by simp only [← sub_eq_add_neg]
    _ = ∫⁻ x, ∫⁻ y, A (x - y) * B x ∂Γ ∂volume := lintegral_lintegral_swap h2.aemeasurable
    _ = ∫⁻ x, B x * ∫⁻ y, A (x - y) ∂Γ := lintegral_congr fun x => by
          have hAx : Measurable fun y => A (x - y) := hA.comp (measurable_const.sub measurable_id)
          exact (lintegral_mul_const (B x) hAx).trans (mul_comm _ _)

/-- Auxiliary to the Lean proof route (the evenness/Tonelli step of `L:occupation-raw-square`,
`integrated_occupation_ceiling.tex` lines 102-105 at edf7085f, in `[0,∞]`): for an even s-finite
`Γ` and measurable real `ψ, Gm` on `ℝ × ℝ^d`,
`∫∫_{I²} |u-s|^{-a} ∫∫ ψ(u,x) Gm(s,x-y)² dx Γ(dy) du ds
  = ∫_I ∫ (∫_I |s-u|^{-a} ∫ ψ(u,x-y) Γ(dy) du) Gm(s,x)² dx ds`,
all as lower integrals of the nonnegative parts `ENNReal.ofReal` (no finiteness assumed). -/
theorem lintegral_kern_pair_even {Γ : Measure (Rd d)} [SFinite Γ] (hE : IsEven Γ) (a : ℝ)
    {ψ Gm : ℝ × Rd d → ℝ} (hψ : Measurable ψ) (hGm : Measurable Gm) :
    ∫⁻ q, ENNReal.ofReal (kern a (q.1 - q.2)) * ∫⁻ z, ENNReal.ofReal (ψ (q.1, z.1)) *
        ENNReal.ofReal (Gm (q.2, z.1 - z.2) ^ 2) ∂(pairMeasure Γ)
        ∂(timeMeasure.prod timeMeasure) =
      ∫⁻ s, ∫⁻ x, (∫⁻ u, ENNReal.ofReal (kern a (s - u)) *
        ∫⁻ y, ENNReal.ofReal (ψ (u, x - y)) ∂Γ ∂timeMeasure) * ENNReal.ofReal (Gm (s, x) ^ 2)
        ∂volume ∂timeMeasure := by
  have hC : Measurable fun w : ℝ × Rd d => ∫⁻ y, ENNReal.ofReal (ψ (w.1, w.2 - y)) ∂Γ := by
    have : Measurable fun w : (ℝ × Rd d) × Rd d => ENNReal.ofReal (ψ (w.1.1, w.1.2 - w.2)) :=
      ENNReal.measurable_ofReal.comp (hψ.comp (measurable_fst.fst.prodMk
        (measurable_fst.snd.sub measurable_snd)))
    exact this.lintegral_prod_right'
  have hBm : Measurable fun w : ℝ × Rd d => ENNReal.ofReal (Gm w ^ 2) :=
    ENNReal.measurable_ofReal.comp (hGm.pow_const 2)
  have hin : ∀ u s, ∫⁻ z, ENNReal.ofReal (ψ (u, z.1)) *
      ENNReal.ofReal (Gm (s, z.1 - z.2) ^ 2) ∂(pairMeasure Γ) =
        ∫⁻ x, ENNReal.ofReal (Gm (s, x) ^ 2) * ∫⁻ y, ENNReal.ofReal (ψ (u, x - y)) ∂Γ :=
    fun u s => lintegral_pair_even hE
      (ENNReal.measurable_ofReal.comp (hψ.comp (measurable_const.prodMk measurable_id)))
      (ENNReal.measurable_ofReal.comp
        ((hGm.comp (measurable_const.prodMk measurable_id)).pow_const 2))
  simp_rw [hin]
  have hF : Measurable fun q : ℝ × ℝ => ENNReal.ofReal (kern a (q.1 - q.2)) *
      ∫⁻ x, ENNReal.ofReal (Gm (q.2, x) ^ 2) * ∫⁻ y, ENNReal.ofReal (ψ (q.1, x - y)) ∂Γ := by
    refine (ENNReal.measurable_ofReal.comp ((measurable_kern a).comp
      (measurable_fst.sub measurable_snd))).mul ?_
    have : Measurable fun w : (ℝ × ℝ) × Rd d => ENNReal.ofReal (Gm (w.1.2, w.2) ^ 2) *
        ∫⁻ y, ENNReal.ofReal (ψ (w.1.1, w.2 - y)) ∂Γ :=
      (hBm.comp (measurable_fst.snd.prodMk measurable_snd)).mul
        (hC.comp (measurable_fst.fst.prodMk measurable_snd))
    exact this.lintegral_prod_right'
  rw [lintegral_prod _ hF.aemeasurable, lintegral_lintegral_swap hF.aemeasurable]
  refine lintegral_congr fun s => ?_
  have hG2 : Measurable fun w : ℝ × Rd d => ENNReal.ofReal (kern a (s - w.1)) *
      (∫⁻ y, ENNReal.ofReal (ψ (w.1, w.2 - y)) ∂Γ) * ENNReal.ofReal (Gm (s, w.2) ^ 2) :=
    ((ENNReal.measurable_ofReal.comp ((measurable_kern a).comp
      (measurable_const.sub measurable_fst))).mul hC).mul
      (hBm.comp (measurable_const.prodMk measurable_snd))
  calc ∫⁻ u, ENNReal.ofReal (kern a (u - s)) * ∫⁻ x, ENNReal.ofReal (Gm (s, x) ^ 2) *
        ∫⁻ y, ENNReal.ofReal (ψ (u, x - y)) ∂Γ ∂volume ∂timeMeasure
      = ∫⁻ u, ∫⁻ x, ENNReal.ofReal (kern a (s - u)) *
          (∫⁻ y, ENNReal.ofReal (ψ (u, x - y)) ∂Γ) * ENNReal.ofReal (Gm (s, x) ^ 2)
          ∂volume ∂timeMeasure := lintegral_congr fun u => by
        rw [kern_sub_comm, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        refine lintegral_congr fun x => ?_
        ring
    _ = ∫⁻ x, ∫⁻ u, ENNReal.ofReal (kern a (s - u)) *
          (∫⁻ y, ENNReal.ofReal (ψ (u, x - y)) ∂Γ) * ENNReal.ofReal (Gm (s, x) ^ 2)
          ∂timeMeasure ∂volume := lintegral_lintegral_swap hG2.aemeasurable
    _ = _ := lintegral_congr fun x => lintegral_mul_const' _ _ ENNReal.ofReal_ne_top

variable {S : SpData d}

/-- Auxiliary: for a test function `φ` and an `H¹` pair `(f, g)`, the integrand
`φ(x) f(x-y)²` of `B_Γ(φ, f²)` is `ν`-integrable, `ν = dx Γ(dy)` (`P:spatial-four-linear`
through `C₄(χ, φ, f, f)` with a test `χ = 1` on the support of `φ`; TeX lines 88-95). -/
theorem testSqPair_integrable {alpha R : ℝ} (hB : SquareBound S.Γ alpha R) (hR0 : 0 ≤ R)
    {φ : Rd d → ℝ} (hφ : IsTestFunction φ) {f : Rd d → ℝ} {g : Rd d → Rd d}
    (hf : IsH1Pair f g) :
    Integrable (fun q : Rd d × Rd d => φ q.1 * f (q.1 - q.2) ^ 2) (pairMeasure S.Γ) := by
  obtain ⟨Rφ, -, hRφ⟩ := hφ.2.exists_pos_le_norm
  obtain ⟨n, hn⟩ := exists_nat_ge Rφ
  set χ : Rd d → ℝ := H1Density.cutoff n with hχdef
  have hχ : IsTestFunction χ :=
    ⟨H1Density.cutoff_contDiff n, H1Density.cutoff_hasCompactSupport n⟩
  have hχφ : ∀ x, χ x * φ x = φ x := by
    intro x
    by_cases hx : ‖x‖ ≤ (n : ℝ) + 1
    · rw [hχdef, H1Density.cutoff_eq_one hx, one_mul]
    · rw [hRφ x (by linarith), mul_zero]
  refine (four_integrable hB hR0 (isH1Pair_test hχ) (isH1Pair_test hφ) hf hf).congr
    (ae_of_all _ fun q => ?_)
  simp only
  rw [hχφ q.1]
  ring

/-- Auxiliary: `B_Γ(φ, f²)` depends only on the Lebesgue a.e.-class of `f` (locally finite
`Γ`, `OccupationKernelRow.ae_pair_of_ae`). -/
theorem testSqPair_congr {φ f f' : Rd d → ℝ} (h : f =ᵐ[volume] f') :
    testSqPair S φ f = testSqPair S φ f' := by
  unfold testSqPair
  refine integral_congr_ae ?_
  filter_upwards [OccupationKernelRow.ae_pair_of_ae S.Γ h] with q hq
  rw [hq.2]

/-- Auxiliary: for measurable `φ ≥ 0` and measurable `f`, `B_Γ(φ, f²)` is the real value of
the lower integral `∫∫ φ(x) f(x-y)² dx Γ(dy)` (no integrability assumed). -/
theorem testSqPair_eq_toReal {φ f : Rd d → ℝ} (hφ : Measurable φ) (hφ0 : ∀ x, 0 ≤ φ x)
    (hf : Measurable f) :
    testSqPair S φ f = (∫⁻ q, ENNReal.ofReal (φ q.1) * ENNReal.ofReal (f (q.1 - q.2) ^ 2)
      ∂(pairMeasure S.Γ)).toReal := by
  have hm : AEStronglyMeasurable (fun q : Rd d × Rd d => φ q.1 * f (q.1 - q.2) ^ 2)
      (pairMeasure S.Γ) := ((hφ.comp measurable_fst).mul
        ((hf.comp (measurable_fst.sub measurable_snd)).pow_const 2)).aestronglyMeasurable
  unfold testSqPair
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun q => mul_nonneg (hφ0 _) (sq_nonneg _))
    hm]
  congr 1
  refine lintegral_congr fun q => ?_
  exact ENNReal.ofReal_mul (hφ0 _)

variable {p : TParams}

/-- **The second identity of `E:occupation-raw-identities`** (`L:occupation-raw-square`,
`integrated_occupation_ceiling.tex` lines 34-38 and proof lines 96-105 at edf7085f): for
`Ψ ∈ C_pos` and a field of `𝒪` (joint representatives),
`⟨Ψ, ρ_g⟩_{H_I} = ∫_I ∫ h_{Ψ,s}(x) g_s(x)² dx ds`, with
`h_{Ψ,s}(x) = ∫_I |s-u|^{-a} (Γ * Ψ(u,·))(x) du` (`VariationalDilation.mean`,
`E:compact-raw-mean`).  Also (TeX lines 102-105, "the absolute integrals are finite"): for a.e.
`s ∈ I` the function `x ↦ h_{Ψ,s}(x) g_s(x)²` is integrable, and `s ↦ ∫ h_{Ψ,s} g_s²` is
integrable on `I`.  Hypotheses: `SquareBound Γ α R` and `SquarePairingBounds Γ α R`
(`P:spatial-four-linear`), `R ≥ 0`, `0 < α < 2`; `Γ` even (`SpData`).  Route as in the TeX:
the polarized form `inner_incl_rho`, then evenness of `Γ` and Tonelli for the nonnegative
physical integrands (`lintegral_kern_pair_even`), with finiteness from the Schur-integrable
polarized integrand (`kform_integrable`). -/
theorem inner_incl_rho_mean {alpha R : ℝ} (hB : SquareBound S.Γ alpha R)
    (hSPB : SquarePairingBounds S.Γ alpha R) (hR0 : 0 ≤ R) (ha0 : 0 < alpha) (ha2 : alpha < 2)
    {G : ℝ → Rd d → ℝ} {DG : ℝ → Rd d → Rd d} (hO : IsOccField G DG) {Ψ : ℝ × Rd d → ℝ}
    (hΨ : Ψ ∈ CPos d) :
    (∀ᵐ s ∂volI, Integrable fun x => mean p.a S.Γ Ψ s x * G s x ^ 2) ∧
      IntegrableOn (fun s => ∫ x, mean p.a S.Γ Ψ s x * G s x ^ 2) (Ioo (0 : ℝ) 1) ∧
      ⟪incl p S Ψ, rho p S G⟫ = ∫ s in Ioo (0 : ℝ) 1, ∫ x, mean p.a S.Γ Ψ s x * G s x ^ 2 := by
  have hΨc : Continuous Ψ := hΨ.1.continuous
  have hΨs : HasCompactSupport Ψ := hΨ.2.1
  have hΨ0 : ∀ q, 0 ≤ Ψ q := hΨ.2.2.2.1
  obtain ⟨MΨ, RΨ, -, -, hMΨ, hRΨ⟩ := SpaceTimePositivity.field_data hΨc hΨs
  set Gm : ℝ × Rd d → ℝ := hO.meas.mk _ with hGmdef
  have hGm : Measurable Gm := hO.meas.stronglyMeasurable_mk.measurable
  have hae : ∀ᵐ s ∂volI, G s =ᵐ[volume] fun x => Gm (s, x) :=
    Measure.ae_ae_of_ae_prod hO.meas.ae_eq_mk
  have hP : ∀ᵐ s ∂volI, IsH1Pair (fun x => Gm (s, x)) (DG s) ∧
      (G s =ᵐ[volume] fun x => Gm (s, x)) := by
    filter_upwards [hO.unit, hae] with s hu he
    exact ⟨isH1Pair_congr_ae ⟨hu.1, hu.2.1, hu.2.2.1⟩ he, he⟩
  -- the extended-real objects
  set C : ℝ → Rd d → ℝ≥0∞ := fun u x => ∫⁻ y, ENNReal.ofReal (Ψ (u, x - y)) ∂S.Γ with hCdef
  set M : ℝ → Rd d → ℝ≥0∞ := fun s x =>
    ∫⁻ u, ENNReal.ofReal (kern p.a (s - u)) * C u x ∂timeMeasure with hMdef
  set L : ℝ → ℝ≥0∞ := fun s => ∫⁻ x, M s x * ENNReal.ofReal (Gm (s, x) ^ 2) with hLdef
  set P : ℝ → ℝ → ℝ≥0∞ := fun u s => ∫⁻ z, ENNReal.ofReal (Ψ (u, z.1)) *
    ENNReal.ofReal (Gm (s, z.1 - z.2) ^ 2) ∂(pairMeasure S.Γ) with hPdef
  have hCm : Measurable fun w : ℝ × Rd d => C w.1 w.2 := by
    have : Measurable fun w : (ℝ × Rd d) × Rd d => ENNReal.ofReal (Ψ (w.1.1, w.1.2 - w.2)) :=
      ENNReal.measurable_ofReal.comp (hΨc.measurable.comp (measurable_fst.fst.prodMk
        (measurable_fst.snd.sub measurable_snd)))
    exact this.lintegral_prod_right'
  have hMm : Measurable fun w : ℝ × Rd d => M w.1 w.2 := by
    have : Measurable fun v : (ℝ × Rd d) × ℝ =>
        ENNReal.ofReal (kern p.a (v.1.1 - v.2)) * C v.2 v.1.2 :=
      (ENNReal.measurable_ofReal.comp ((measurable_kern _).comp
        (measurable_fst.fst.sub measurable_snd))).mul (hCm.comp (measurable_snd.prodMk
          measurable_fst.snd))
    exact this.lintegral_prod_right'
  have hBm : Measurable fun w : ℝ × Rd d => ENNReal.ofReal (Gm w ^ 2) :=
    ENNReal.measurable_ofReal.comp (hGm.pow_const 2)
  have hLm : Measurable L := by
    have : Measurable fun w : ℝ × Rd d => M w.1 w.2 * ENNReal.ofReal (Gm (w.1, w.2) ^ 2) :=
      hMm.mul hBm
    exact this.lintegral_prod_right'
  have hPm : Measurable fun q : ℝ × ℝ => ENNReal.ofReal (kern p.a (q.1 - q.2)) * P q.1 q.2 := by
    refine (ENNReal.measurable_ofReal.comp ((measurable_kern _).comp
      (measurable_fst.sub measurable_snd))).mul ?_
    have : Measurable fun w : (ℝ × ℝ) × (Rd d × Rd d) => ENNReal.ofReal (Ψ (w.1.1, w.2.1)) *
        ENNReal.ofReal (Gm (w.1.2, w.2.1 - w.2.2) ^ 2) :=
      (ENNReal.measurable_ofReal.comp (hΨc.measurable.comp
        (measurable_fst.fst.prodMk measurable_snd.fst))).mul
        (hBm.comp (measurable_fst.snd.prodMk (measurable_snd.fst.sub measurable_snd.snd)))
    exact this.lintegral_prod_right'
  -- finiteness of `C` and `M`
  have hCle : ∀ u x, C u x ≤ ENNReal.ofReal MΨ * S.Γ (closedBall x RΨ) := by
    intro u x
    calc C u x ≤ ∫⁻ y, (closedBall x RΨ).indicator (fun _ => ENNReal.ofReal MΨ) y ∂S.Γ := by
          refine lintegral_mono fun y => ?_
          by_cases hy : y ∈ closedBall x RΨ
          · rw [indicator_of_mem hy]
            exact ENNReal.ofReal_le_ofReal ((le_abs_self _).trans (hMΨ _))
          · rw [indicator_of_notMem hy]
            rw [mem_closedBall, dist_eq_norm, not_le, norm_sub_rev] at hy
            rw [hRΨ u (x - y) hy, ENNReal.ofReal_zero]
      _ = _ := lintegral_indicator_const measurableSet_closedBall _
  have hCfin : ∀ u x, C u x < ⊤ := fun u x => (hCle u x).trans_lt
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top measure_closedBall_lt_top)
  have hMfin : ∀ s ∈ Icc (0 : ℝ) 1, ∀ x, M s x < ⊤ := by
    intro s hs x
    have hk : Integrable (fun u => kern p.a (s - u)) timeMeasure :=
      ((TimeSchur.integral_row (T := 1) p.ha1 hs).1).mono_set Ioo_subset_Icc_self
    calc M s x ≤ ∫⁻ u, ENNReal.ofReal (kern p.a (s - u)) *
          (ENNReal.ofReal MΨ * S.Γ (closedBall x RΨ)) ∂timeMeasure :=
          lintegral_mono fun u => mul_le_mul' le_rfl (hCle u x)
      _ = (∫⁻ u, ENNReal.ofReal (kern p.a (s - u)) ∂timeMeasure) *
          (ENNReal.ofReal MΨ * S.Γ (closedBall x RΨ)) :=
          lintegral_mul_const' _ _
            (ENNReal.mul_lt_top ENNReal.ofReal_lt_top measure_closedBall_lt_top).ne
      _ < ⊤ := ENNReal.mul_lt_top hk.lintegral_lt_top
          (ENNReal.mul_lt_top ENNReal.ofReal_lt_top measure_closedBall_lt_top)
  -- the mean as the real value of `M`
  have hmean : ∀ s x, mean p.a S.Γ Ψ s x = (M s x).toReal := by
    intro s x
    have hum : Measurable fun u => ENNReal.ofReal (kern p.a (s - u)) * C u x :=
      (ENNReal.measurable_ofReal.comp ((measurable_kern _).comp
        (measurable_const.sub measurable_id))).mul (hCm.comp (measurable_id.prodMk
          measurable_const))
    simp only [hMdef]
    rw [← integral_toReal hum.aemeasurable
      (ae_of_all _ fun u => ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hCfin u x))]
    unfold mean
    refine integral_congr_ae (ae_of_all _ fun u => ?_)
    simp only
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (kern_nonneg _ _)]
    unfold conv
    rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun y => hΨ0 _)
      (hΨc.comp (by fun_prop)).aestronglyMeasurable]
    rfl
  -- the rows `∫ h_s g_s²`
  have hrow : ∀ᵐ s ∂volI, ∫ x, mean p.a S.Γ Ψ s x * G s x ^ 2 = (L s).toReal ∧
      (L s ≠ ⊤ → Integrable fun x => mean p.a S.Γ Ψ s x * G s x ^ 2) := by
    filter_upwards [hP, ae_restrict_mem measurableSet_Ioo] with s hs hsI
    have hsx : Measurable fun x : Rd d => (s, x) := measurable_const.prodMk measurable_id
    have hxm : Measurable fun x => M s x * ENNReal.ofReal (Gm (s, x) ^ 2) :=
      (hMm.comp hsx).mul (hBm.comp hsx)
    have heq : (fun x => mean p.a S.Γ Ψ s x * G s x ^ 2) =ᵐ[volume]
        fun x => (M s x * ENNReal.ofReal (Gm (s, x) ^ 2)).toReal := by
      filter_upwards [hs.2] with x hx
      rw [hx, ENNReal.toReal_mul, ENNReal.toReal_ofReal (sq_nonneg _), hmean]
    refine ⟨?_, fun hL => (integrable_toReal_of_lintegral_ne_top hxm.aemeasurable hL).congr
      heq.symm⟩
    rw [integral_congr_ae heq, integral_toReal hxm.aemeasurable (ae_of_all _ fun x =>
      ENNReal.mul_lt_top (hMfin s (Ioo_subset_Icc_self hsI) x) ENNReal.ofReal_lt_top)]
  -- the left side as the real value of `T`
  have hqae : ∀ᵐ q ∂(timeMeasure.prod timeMeasure), IsH1Pair (fun x => Gm (q.2, x)) (DG q.2) ∧
      (G q.2 =ᵐ[volume] fun x => Gm (q.2, x)) ∧ IsH1Pair (G q.2) (DG q.2) := by
    filter_upwards [(Measure.quasiMeasurePreserving_snd (μ := volI) (ν := volI)).ae
      (hP.and hO.unit)] with q hq
    exact ⟨hq.1.1, hq.1.2, hq.2.1, hq.2.2.1, hq.2.2.2.1⟩
  have hts : ∀ u s, testSqPair S (fun x => Ψ (u, x)) (fun x => Gm (s, x)) = (P u s).toReal :=
    fun u s => testSqPair_eq_toReal (hΨc.measurable.comp (measurable_const.prodMk measurable_id))
      (fun x => hΨ0 _) (hGm.comp (measurable_const.prodMk measurable_id))
  have hPfin : ∀ u s, IsH1Pair (fun x => Gm (s, x)) (DG s) → P u s < ⊤ := by
    intro u s hs
    have hi := testSqPair_integrable (S := S) hB hR0 (slice_isTest hΨ.1 hΨs u) hs
    calc P u s = ∫⁻ z, ENNReal.ofReal (Ψ (u, z.1) * Gm (s, z.1 - z.2) ^ 2)
          ∂(pairMeasure S.Γ) := lintegral_congr fun z => (ENNReal.ofReal_mul (hΨ0 _)).symm
      _ < ⊤ := hi.lintegral_lt_top
  have hInt : Integrable (fun q : ℝ × ℝ => kern p.a (q.1 - q.2) *
      testSqPair S (fun x => Ψ (q.1, x)) (G q.2)) (timeMeasure.prod timeMeasure) := by
    refine (kform_integrable p.ha0.le p.ha1 (sliceField_memLp (S := S) hΨ.1 hΨs)
      (sqField_memLp hB hSPB hR0 ha0 ha2 hO)).congr ?_
    filter_upwards [hqae] with q hq
    unfold sliceField sqField
    rw [inner_toHsp_Q hB hR0 ha0 (by linarith) (slice_isTest hΨ.1 hΨs q.1) hq.2.2]
  have hTae : (fun q : ℝ × ℝ => ENNReal.ofReal (kern p.a (q.1 - q.2)) * P q.1 q.2) =ᵐ[
      timeMeasure.prod timeMeasure] fun q => ENNReal.ofReal (kern p.a (q.1 - q.2) *
        testSqPair S (fun x => Ψ (q.1, x)) (G q.2)) := by
    filter_upwards [hqae] with q hq
    rw [testSqPair_congr hq.2.1, hts, ENNReal.ofReal_mul (kern_nonneg _ _),
      ENNReal.ofReal_toReal (hPfin _ _ hq.1).ne]
  have hTfin : ∫⁻ q, ENNReal.ofReal (kern p.a (q.1 - q.2)) * P q.1 q.2
      ∂(timeMeasure.prod timeMeasure) < ⊤ := by
    rw [lintegral_congr_ae hTae]
    exact hInt.lintegral_lt_top
  have hTL : ∫⁻ q, ENNReal.ofReal (kern p.a (q.1 - q.2)) * P q.1 q.2
      ∂(timeMeasure.prod timeMeasure) = ∫⁻ s, L s ∂timeMeasure :=
    lintegral_kern_pair_even S.even p.a hΨc.measurable hGm
  have hLne : ∫⁻ s, L s ∂timeMeasure ≠ ⊤ := hTL ▸ hTfin.ne
  have hLfin : ∀ᵐ s ∂timeMeasure, L s ≠ ⊤ := (ae_lt_top hLm hLne).mono fun s hs => hs.ne
  refine ⟨?_, ?_, ?_⟩
  · filter_upwards [hrow, hLfin] with s hs hL
    exact hs.2 hL
  · refine (integrable_toReal_of_lintegral_ne_top hLm.aemeasurable hLne).congr ?_
    filter_upwards [hrow] with s hs
    exact hs.1.symm
  · rw [inner_incl_rho hB hSPB hR0 ha0 ha2 hO hΨ.1 hΨs]
    calc ∫ q, kern p.a (q.1 - q.2) * testSqPair S (fun x => Ψ (q.1, x)) (G q.2)
          ∂(timeMeasure.prod timeMeasure)
        = ∫ q, (ENNReal.ofReal (kern p.a (q.1 - q.2)) * P q.1 q.2).toReal
          ∂(timeMeasure.prod timeMeasure) := by
          refine integral_congr_ae ?_
          filter_upwards [hqae] with q hq
          rw [testSqPair_congr hq.2.1, hts, ENNReal.toReal_mul,
            ENNReal.toReal_ofReal (kern_nonneg _ _)]
      _ = (∫⁻ s, L s ∂timeMeasure).toReal := by
          rw [integral_toReal hPm.aemeasurable (ae_lt_top hPm hTfin.ne), hTL]
      _ = _ := by
          rw [← integral_toReal hLm.aemeasurable (hLfin.mono fun s hs => lt_top_iff_ne_top.2 hs)]
          refine integral_congr_ae ?_
          filter_upwards [hrow] with s hs
          exact hs.1.symm

end MeanIdentity

/-! ### The `_paper` wrappers -/

section Paper

open SpatialFourLinear (IsH1Pair H1Tendsto)
open OccupationPhysicalClass (volI sqPair IsOccField)
open VariationalDilation (CPos rawCost)

variable {d : ℕ}

/-- **`L:positive-raw-embedding`** (`integrated_intrinsic_constant.tex` lines 23-40 at edf7085f),
narrower, under the section's standing assumptions (`H:homog` with `a = α₀`, `Γ ≠ 0`; lines
4-19).  Conclusions:
* `E:positive-bochner-inclusion` (lines 25-31) for every real Hilbert space `G`: for
  `F ∈ L²(I; G)` the integrand is integrable,
  `‖J_G F‖² = ∫∫_{I²} |s-t|^{-a} ⟨F(s), F(t)⟩_G ≤ K_0 ‖F‖²`, `K_0 = 2^a/(1-a)`; `H_t ⊗ G` is
  the kernel completion `HK` of `L²(I; G)` (decision 4: no tensor identification);
* the natural inclusion `C_pos → H_I` (`incl`) and the first identity of
  `E:positive-raw-mean` (lines 34-37): `‖Ψ‖²_{H_I} = v_Ψ`, with the integral form
  `‖Ψ‖²_{H_I} = ∫∫ |s-t|^{-a} B_Γ(Ψ_s, Ψ_t)`.
Not formalized: the mean identity `T_R Ψ(s) = B_E(m_R h_{Ψ,s})` of `E:positive-raw-mean` and the
sentence on canonical versions (lines 38-39), with the Bochner-integral paragraph of the proof
(lines 71-80) and the `E`-row paragraph (lines 116-131).  `Γ ≠ 0` is carried, unused. -/
theorem positive_raw_embedding_paper {alpha alpha0 : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogCovariance d alpha alpha0 Γ μ) (_hΓ : Γ ≠ 0) (G : Type*) [NormedAddCommGroup G]
    [InnerProductSpace ℝ G] [CompleteSpace G] :
    (∀ F : Lp G 2 timeMeasure,
      Integrable (fun q : ℝ × ℝ => kern alpha0 (q.1 - q.2) * ⟪F q.1, F q.2⟫)
        (timeMeasure.prod timeMeasure) ∧
      ‖J (TParams.ofHomog hH) G F‖ ^ 2 =
        ∫ q, kern alpha0 (q.1 - q.2) * ⟪F q.1, F q.2⟫ ∂(timeMeasure.prod timeMeasure) ∧
      ‖J (TParams.ofHomog hH) G F‖ ^ 2 ≤ K0 alpha0 * ‖F‖ ^ 2) ∧
    ∀ Ψ ∈ CPos d,
      ‖incl (TParams.ofHomog hH) (SpData.ofHomog hH) Ψ‖ ^ 2 = rawCost alpha0 Γ Ψ ∧
      ‖incl (TParams.ofHomog hH) (SpData.ofHomog hH) Ψ‖ ^ 2 =
        SpaceTimePositivity.stForm alpha0 Γ Ψ Ψ := by
  refine ⟨fun F => ?_, fun Ψ hΨ => ?_⟩
  · obtain ⟨h1, h2, h3, -⟩ := positive_bochner_inclusion (p := TParams.ofHomog hH) F
    exact ⟨h1, h2, h3⟩
  · obtain ⟨h1, h2, -⟩ := norm_incl_sq (p := TParams.ofHomog hH) (S := SpData.ofHomog hH) hΨ
    exact ⟨h2, h1⟩

/-- **`L:occupation-raw-square`** (`integrated_occupation_ceiling.tex` lines 24-43 at
edf7085f), narrower, under the section's standing assumptions (`H:homog` with `a = α₀`, `Γ ≠ 0`;
lines 4-21).  With `H_sp` the covariance completion of `C_c^∞(ℝ^d)` (`Hsp`) and
`H_I = HK p H_sp` (decision 4):
* `Q : H¹ → H_sp` (`Q`) with `⟨Q(f), Q(h)⟩ = B_Γ(f², h²)` (finite) and `‖Q(f)‖² = A_sp(f)`
  for real `H¹` pairs; `Q` is continuous in the sequential form (`H¹` convergence of functions
  and weak gradients) and depends only on the a.e.-class of `f`;
* for every field of `𝒪`, modelled by joint representatives (`IsOccField`): `s ↦ Q(g_s)` is in
  `L²(I; H_sp)` (in particular strongly measurable), `ρ_g = J_{H_sp}(s ↦ Q(g_s)) ∈ H_I` with
  `‖ρ_g‖² = A(g)` (first identity of `E:occupation-raw-identities`), and for every
  `Ψ ∈ C_pos`: `⟨Ψ, ρ_g⟩_{H_I} = ∫∫ |s-t|^{-a} B_Γ(Ψ_s, g_t²)` (lines 96-101),
  `⟨Ψ, ρ_g⟩_{H_I} ≤ √(v_Ψ A(g))` (line 41), and the second identity of
  `E:occupation-raw-identities` (lines 36-38, proof 102-105):
  `⟨Ψ, ρ_g⟩_{H_I} = ∫_I ∫ h_{Ψ,s}(x) g_s(x)² dx ds` (`h_{Ψ,s} = VariationalDilation.mean`), with
  `x ↦ h_{Ψ,s} g_s²` integrable for a.e. `s` and `s ↦ ∫ h_{Ψ,s} g_s²` integrable on `I`.
Not formalized: the class `𝒪` itself
(strongly `H¹`-measurable fields; here joint representatives, until wave item L14-O);
topological (non-sequential) continuity of `Q` (no `H¹` type); the identification of `HI` with
the TeX's "original `H_I`" (completion of space-time tests; decision 4). -/
theorem occupation_raw_square_paper {alpha alpha0 : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogCovariance d alpha alpha0 Γ μ) (hΓ : Γ ≠ 0) :
    (∀ (f h : Rd d → ℝ) (g k : Rd d → Rd d), IsH1Pair f g → IsH1Pair h k →
      sqPair Γ f h < ⊤ ∧
      ⟪Q (SpData.ofHomog hH) f, Q (SpData.ofHomog hH) h⟫ = (sqPair Γ f h).toReal) ∧
    (∀ (f : Rd d → ℝ) (g : Rd d → Rd d), IsH1Pair f g →
      ‖Q (SpData.ofHomog hH) f‖ ^ 2 = (sqPair Γ f f).toReal) ∧
    (∀ (u : ℕ → Rd d → ℝ) (v : ℕ → Rd d → Rd d) (f : Rd d → ℝ) (g : Rd d → Rd d),
      (∀ n, IsH1Pair (u n) (v n)) → IsH1Pair f g → H1Tendsto u v f g →
      Tendsto (fun n => Q (SpData.ofHomog hH) (u n)) atTop (𝓝 (Q (SpData.ofHomog hH) f))) ∧
    (∀ (f f' : Rd d → ℝ) (g : Rd d → Rd d), IsH1Pair f g → f =ᵐ[volume] f' →
      Q (SpData.ofHomog hH) f' = Q (SpData.ofHomog hH) f) ∧
    ∀ (G : ℝ → Rd d → ℝ) (DG : ℝ → Rd d → Rd d), IsOccField G DG →
      MemLp (sqField (SpData.ofHomog hH) G) 2 volI ∧
      ‖rho (TParams.ofHomog hH) (SpData.ofHomog hH) G‖ ^ 2 =
        RawOccupationEnergy.A alpha0 Γ G ∧
      ∀ Ψ ∈ CPos d,
        ⟪incl (TParams.ofHomog hH) (SpData.ofHomog hH) Ψ,
          rho (TParams.ofHomog hH) (SpData.ofHomog hH) G⟫ =
          ∫ q, kern alpha0 (q.1 - q.2) *
            testSqPair (SpData.ofHomog hH) (fun x => Ψ (q.1, x)) (G q.2)
            ∂(timeMeasure.prod timeMeasure) ∧
        ⟪incl (TParams.ofHomog hH) (SpData.ofHomog hH) Ψ,
          rho (TParams.ofHomog hH) (SpData.ofHomog hH) G⟫ ≤
          Real.sqrt (rawCost alpha0 Γ Ψ * RawOccupationEnergy.A alpha0 Γ G) ∧
        (∀ᵐ s ∂volI, Integrable fun x => VariationalDilation.mean alpha0 Γ Ψ s x * G s x ^ 2) ∧
        IntegrableOn (fun s => ∫ x, VariationalDilation.mean alpha0 Γ Ψ s x * G s x ^ 2)
          (Ioo (0 : ℝ) 1) ∧
        ⟪incl (TParams.ofHomog hH) (SpData.ofHomog hH) Ψ,
          rho (TParams.ofHomog hH) (SpData.ofHomog hH) G⟫ =
          ∫ s in Ioo (0 : ℝ) 1, ∫ x, VariationalDilation.mean alpha0 Γ Ψ s x * G s x ^ 2 := by
  have := hH.Γ_radon
  obtain ⟨-, ha0, ha2, -, -, hR0, hB⟩ :=
    SpatialFourLinear.squareBound_R0 hH hΓ (H1Density.h1TestDense d)
  have hSPB := SpatialOccupationL7Completed.squarePairingBounds_holds hH hΓ
  set S := SpData.ofHomog hH
  set p := TParams.ofHomog hH
  have ha4 : alpha < 4 := by linarith
  refine ⟨fun f h g k hf hh => ?_, fun f g hf => ?_, fun u v f g hu hf hc => ?_,
    fun f f' g hf he => ?_, fun G DG hO => ?_⟩
  · refine ⟨(SpatialOccupationL7Completed.spatial_square_CS_paper_completed hH hΓ hf hh).1, ?_⟩
    rw [inner_Q (S := S) hB hR0.le ha0 ha4 hf hh,
      ← sqPair_toReal_eq (S := S) hf.1.aestronglyMeasurable hh.1.aestronglyMeasurable]
    rfl
  · rw [← real_inner_self_eq_norm_sq, inner_Q (S := S) hB hR0.le ha0 ha4 hf hf,
      ← sqPair_toReal_eq (S := S) hf.1.aestronglyMeasurable hf.1.aestronglyMeasurable]
    rfl
  · exact tendsto_Q_of_H1 (S := S) hB hR0.le ha0 ha4 hu hf hc
  · exact Q_congr_ae (S := S) hB hR0.le ha0 ha4 hf he
  · refine ⟨sqField_memLp (S := S) hB hSPB hR0.le ha0 ha2 hO,
      norm_rho_sq (p := p) (S := S) hB hSPB hR0.le ha0 ha2 hO, fun Ψ hΨ => ⟨?_, ?_, ?_⟩⟩
    · exact inner_incl_rho (p := p) (S := S) hB hSPB hR0.le ha0 ha2 hO hΨ.1 hΨ.2.1
    · exact inner_incl_rho_le (p := p) (S := S) hB hSPB hR0.le ha0 ha2 hO hΨ
    · exact inner_incl_rho_mean (p := p) (S := S) hB hSPB hR0.le ha0 ha2 hO hΨ

end Paper

end StratonovichHAMSecondMoment.OccupationCompletion
