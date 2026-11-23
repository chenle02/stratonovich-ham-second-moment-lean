module

/-
Copyright 2026 Le Chen. SPDX-License-Identifier: Apache-2.0

Wave L15, item L15-UM, part UM-2 (scope (a), approved by Le on 2026-11-19): the mean identity
of `E:positive-raw-mean` and the canonical-version sentence of `L:positive-raw-embedding`
(`notes/integrated_intrinsic_constant.tex`, statement lines 23-40, `E:positive-raw-mean` lines
34-37, canonical-version sentence lines 38-39, proof Steps 2 and 4 lines 69-82 and 114-131, all
at revision edf7085f (book 1.1.3)), from the named input `UniformMeanRegulator` of the frozen
interface `UniformMeanInterface`.

Headline theorem:
* `positive_raw_mean_paper`: `PositiveRawMeanTarget Ureg` under `H:homog` with `Γ ≠ 0`, for every
  regulator `Ureg : UniformMeanRegulator`.  Supplied inputs: only the interface's
  `UniformMeanRegulator` (which contains `CameronSpatialMap`).  The four UM-0 lemmas used
  (`denseRange_toHhalf`, `inner_toHmhalf_lam`, `exists_isMultiplier`, `BE_apply`, agent A's
  `UniformMeanFoundation`) are bundled in `UM0Facts` and discharged by `um0Facts`.

Objects (new):
* `kBochner a F s = ∫_I |s-t|^{-a} F(t) dt` (the Bochner time integral of Step 2, TeX lines
  71-72, for a `G`-valued field `F`);
* `inclTwo hr : L^r(I; G) → L²(I; G)` (`2 ≤ r`), the inclusion `L^r ⊆ L²` on `I = (0,1)` (Step 2,
  "hence also in `L²`", TeX line 79).

Proof route and differences from the TeX:
* Step 2 (TeX lines 69-82).  The TeX approximates by smooth finite tensors and uses the Schur
  bound for the Bochner map.  Here, for a fixed `φ ∈ L²(I; H_sp)` the two continuous functionals
  `F ↦ ⟪φ, U J F⟫_{L²}` and `F ↦ ⟪J φ, J F⟫_{H_I}` (the second is the kernel form, by
  `E:positive-bochner-inclusion`) agree on single smooth tensors `f ⊗ q` (`U_tensor` and
  Fubini).  A continuous functional on `L²(I; G)` vanishing on these tensors vanishes
  (`clm_eq_zero_of_tensor`: Riesz representation, the fundamental lemma of the calculus of
  variations on `(0,1)` against each vector of a countable dense subset of the separable `G`).
  Hence `⟪φ, U J F⟫ = ⟪J φ, J F⟫` for all `F`; at `F = (s ↦ Ψ_s)` the right side is
  `∫ ⟪φ(s), ∫ K(s,t) Ψ_t dt⟫ ds` (Fubini, and the inner product commutes with the Bochner
  integral), so `U(incl Ψ) = ∫ K(·,t) Ψ_t dt` a.e. (`U_incl_ae`).  No Hilbert-valued Schur
  operator is built: the bounded Bochner field enters only through its `L²` class.
* Step 4 (TeX lines 114-131).  For every `s ∈ [0,1]` and real test `φ`,
  `⟪∫ K(s,t) Ψ_t dt, [φ]⟫_{H_sp} = ∫ h_{Ψ,s} φ` (`inner_kBochner_toHsp`: Fubini in time and
  space, as in `SpaceTimePositivity.integral_mean_mul_eq_stForm_swap`).  With the row of
  `CameronSpatialMap` this gives `⟪T_R q z, w⟫ = ⟪B_E(M) z, w⟫` on the dense test states
  `z = (f, z₂)`, `w = (w₁, Λ g)`, hence `T_R q = B_E(M)` (`T_eq_BE`), at every `s ∈ (0,1)`;
  the explicit version is `s ↦ B_E(M_s)`.

Lemmas whose doc comments say "Auxiliary" have no manuscript label.
-/
public import Mathlib
public import StratonovichHAMSecondMoment.UniformMeanInterface
public import StratonovichHAMSecondMoment.UniformMeanFoundation
public import StratonovichHAMSecondMoment.VariationalMeanDerivatives

@[expose] public section

noncomputable section

set_option autoImplicit false

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff RealInnerProductSpace

namespace StratonovichHAMSecondMoment.PositiveRawMean

open HomogHypothesis (Rd HomogCovariance)
open WeakSobolev (IsTestFunction)
open OccupationCompletion (TParams SpData Hsp toHsp HK HI J incl sliceField kform)
open VariationalDilation (CPos conv mean)
open SpaceTimePositivity (timeMeasure)
open SpatialFourierBound (spatialPair)
open TimeSchur (kern kern_nonneg measurable_kern)
open OccupationCeilingFinite (K0)
open UniformMeanInterface

variable {d : ℕ}

/-! ### The UM-0 facts used here (agent A's lemmas, carried with their frozen signatures) -/

/-- The four UM-0 lemmas of `docs/l15/INTERFACE.md` section 3 that UM-2 uses, with exactly the
frozen signatures (`denseRange_toHhalf`, `inner_toHmhalf_lam`, `exists_isMultiplier`,
`BE_apply`), proved by agent A in `UniformMeanFoundation` (`um0Facts`). -/
structure UM0Facts (d : ℕ) : Prop where
  denseRange_toHhalf : Dense {x : Hhalf d | ∃ φ, IsTestFunction φ ∧ x = toHhalf φ}
  inner_toHmhalf_lam : ∀ {v g : Rd d → ℝ}, IsTestFunction v → IsTestFunction g →
    ⟪toHmhalf v, lam (toHhalf g)⟫ = ∫ x, v x * g x
  exists_isMultiplier : ∀ {V : Rd d → ℝ}, ContDiff ℝ ∞ V → ∀ {C : ℝ}, (∀ x, |V x| ≤ C) →
    ∃ M, IsMultiplier V M ∧ ‖M‖ ≤ C
  BE_apply : ∀ (M : Hhalf d →L[ℝ] Hmhalf d) (u : Hhalf d) (v : Hmhalf d),
    BE M (toE u v) = toE 0 (M u)

/-- The UM-0 facts hold (agent A's `UniformMeanFoundation`). -/
theorem um0Facts : UM0Facts d :=
  ⟨denseRange_toHhalf, inner_toHmhalf_lam, exists_isMultiplier, BE_apply⟩

/-! ### The inclusion `L^r(I; G) ⊆ L²(I; G)` -/

section Inclusion

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- Auxiliary: `I = (0,1)` has measure one. -/
theorem timeMeasure_univ : timeMeasure Set.univ = 1 := by
  rw [Measure.restrict_apply_univ, Real.volume_Ioo]
  norm_num

omit [NormedSpace ℝ G] in
/-- Auxiliary: on `I`, `‖f‖_{L²} ≤ ‖f‖_{L^r}` for `2 ≤ r`. -/
theorem eLpNorm_two_le {r : ℝ≥0∞} (hr : 2 ≤ r) {f : ℝ → G}
    (hf : AEStronglyMeasurable f timeMeasure) :
    eLpNorm f 2 timeMeasure ≤ eLpNorm f r timeMeasure := by
  have h := eLpNorm_le_eLpNorm_mul_rpow_measure_univ hr hf
  rwa [timeMeasure_univ, ENNReal.one_rpow, mul_one] at h

/-- Auxiliary: the linear inclusion `L^r(I; G) → L²(I; G)`, `2 ≤ r`. -/
def inclTwoₗ {r : ℝ≥0∞} (hr : 2 ≤ r) : Lp G r timeMeasure →ₗ[ℝ] Lp G 2 timeMeasure where
  toFun f := ((Lp.memLp f).mono_exponent hr).toLp f
  map_add' f g := by
    refine Lp.ext ?_
    filter_upwards [((Lp.memLp (f + g)).mono_exponent hr).coeFn_toLp,
      ((Lp.memLp f).mono_exponent hr).coeFn_toLp, ((Lp.memLp g).mono_exponent hr).coeFn_toLp,
      Lp.coeFn_add f g,
      Lp.coeFn_add (((Lp.memLp f).mono_exponent hr).toLp f)
        (((Lp.memLp g).mono_exponent hr).toLp g)] with t h1 h2 h3 h4 h5
    rw [h1, h5, h4, Pi.add_apply, Pi.add_apply, h2, h3]
  map_smul' c f := by
    refine Lp.ext ?_
    filter_upwards [((Lp.memLp (c • f)).mono_exponent hr).coeFn_toLp,
      ((Lp.memLp f).mono_exponent hr).coeFn_toLp, Lp.coeFn_smul c f,
      Lp.coeFn_smul c (((Lp.memLp f).mono_exponent hr).toLp f)] with t h1 h2 h3 h4
    rw [h1, RingHom.id_apply, h4, h3, Pi.smul_apply, Pi.smul_apply, h2]

/-- **The inclusion `L^r(I; G) ⊆ L²(I; G)`** for `2 ≤ r` (TeX line 79 at revision edf7085f (book
1.1.3): "converges in `L^r(I;G)` ... hence also in `L²`"), a contraction since `|I| = 1`. -/
def inclTwo {r : ℝ≥0∞} [Fact (1 ≤ r)] (hr : 2 ≤ r) : Lp G r timeMeasure →L[ℝ] Lp G 2 timeMeasure :=
  (inclTwoₗ hr).mkContinuous 1 fun f => by
    rw [one_mul]
    show ‖((Lp.memLp f).mono_exponent hr).toLp f‖ ≤ ‖f‖
    rw [Lp.norm_toLp, Lp.norm_def]
    exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top f)
      (eLpNorm_two_le hr (Lp.aestronglyMeasurable f))

/-- Auxiliary: `inclTwo` does not change the class. -/
theorem coeFn_inclTwo {r : ℝ≥0∞} [Fact (1 ≤ r)] (hr : 2 ≤ r) (f : Lp G r timeMeasure) :
    (inclTwo hr f : ℝ → G) =ᵐ[timeMeasure] f :=
  ((Lp.memLp f).mono_exponent hr).coeFn_toLp

end Inclusion

/-! ### Density of single smooth tensors in `L²(I; G)` -/

section Tensor

variable {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G] [CompleteSpace G]

omit [CompleteSpace G] in
/-- Auxiliary: a single smooth tensor `t ↦ f(t) q`, `f` a time test, lies in `L²(I; G)`. -/
theorem memLp_tensor {f : ℝ → ℝ} (hf : IsTimeTest f) (q : G) :
    MemLp (fun t => f t • q) 2 timeMeasure := by
  obtain ⟨C, hC⟩ := hf.1.continuous.bounded_above_of_compact_support hf.2.1
  refine MemLp.of_bound (hf.1.continuous.smul continuous_const).aestronglyMeasurable (C * ‖q‖)
    (ae_of_all _ fun t => ?_)
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_right (hC t) (norm_nonneg _)

/-- **Density of single smooth tensors** (auxiliary to Step 2 of `L:positive-raw-embedding`,
TeX lines 76-77 at revision edf7085f (book 1.1.3): "Approximation by such tensors converges in
`L²(I;G)`").  For a separable real Hilbert space `G`, a continuous linear functional on
`L²(I; G)` that vanishes on every single smooth tensor `t ↦ f(t) q` (`f` a time test, `q ∈ G`)
is zero.  Proof: its Riesz vector `w` satisfies `∫ f ⟪w, q⟫ = 0` for every time test `f`, so
`⟪w(t), q⟫ = 0` a.e. on `(0,1)` (fundamental lemma); a countable dense set of `q` gives `w = 0`. -/
theorem clm_eq_zero_of_tensor [TopologicalSpace.SeparableSpace G]
    (ℓ : Lp G 2 timeMeasure →L[ℝ] ℝ)
    (h : ∀ f : ℝ → ℝ, IsTimeTest f → ∀ q : G, ∀ hF : MemLp (fun t => f t • q) 2 timeMeasure,
      ℓ (hF.toLp fun t => f t • q) = 0) : ℓ = 0 := by
  set w := (InnerProductSpace.toDual ℝ (Lp G 2 timeMeasure)).symm ℓ with hwdef
  have hw : ∀ F, ⟪w, F⟫ = ℓ F := fun F => InnerProductSpace.toDual_symm_apply
  -- each coordinate `⟪w(t), q⟫` vanishes a.e.
  have hq : ∀ q : G, ∀ᵐ t ∂timeMeasure, ⟪(w : ℝ → G) t, q⟫ = 0 := by
    intro q
    have hint : Integrable (fun t => ⟪(w : ℝ → G) t, q⟫) timeMeasure := by
      have hw1 : Integrable (fun t => ‖(w : ℝ → G) t‖) timeMeasure :=
        ((Lp.memLp w).integrable one_le_two).norm
      refine (hw1.mul_const ‖q‖).mono' ?_ (ae_of_all _ fun t => ?_)
      · exact (Lp.aestronglyMeasurable w).inner aestronglyMeasurable_const
      · rw [Real.norm_eq_abs]
        exact abs_real_inner_le_norm _ _
    have hint' : IntegrableOn (fun t => ⟪(w : ℝ → G) t, q⟫) (Ioo (0 : ℝ) 1) volume := hint
    have hloc : LocallyIntegrableOn (fun t => ⟪(w : ℝ → G) t, q⟫) (Ioo (0 : ℝ) 1) volume :=
      hint'.locallyIntegrableOn
    have h0 := isOpen_Ioo.ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc ?_
    · exact (ae_restrict_iff' measurableSet_Ioo).2 h0
    intro g hg hgs hsub
    have hT : IsTimeTest g := ⟨hg, hgs, hsub⟩
    have hF := memLp_tensor hT q
    have e1 := h g hT q hF
    rw [← hw, MeasureTheory.L2.inner_def] at e1
    have e2 : ∫ t, ⟪(w : ℝ → G) t, (hF.toLp fun t => g t • q : ℝ → G) t⟫ ∂timeMeasure =
        ∫ t, g t • ⟪(w : ℝ → G) t, q⟫ ∂timeMeasure := by
      refine integral_congr_ae ?_
      filter_upwards [hF.coeFn_toLp] with t ht
      rw [ht, inner_smul_right, smul_eq_mul]
    rw [e2] at e1
    rw [← e1]
    exact (setIntegral_eq_integral_of_forall_compl_eq_zero fun t ht =>
      by rw [image_eq_zero_of_notMem_tsupport (fun h' => ht (hsub h')), zero_smul]).symm
  -- a countable dense set of directions
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense G
  have hall : ∀ᵐ t ∂timeMeasure, ∀ q ∈ D, ⟪(w : ℝ → G) t, q⟫ = 0 :=
    (ae_ball_iff hDc).2 fun q _ => hq q
  have hw0 : ∀ᵐ t ∂timeMeasure, (w : ℝ → G) t = 0 := by
    filter_upwards [hall] with t ht
    have hcl : IsClosed {q : G | ⟪(w : ℝ → G) t, q⟫ = 0} :=
      isClosed_eq (continuous_const.inner continuous_id) continuous_const
    have hsub : closure D ⊆ {q : G | ⟪(w : ℝ → G) t, q⟫ = 0} := closure_minimal ht hcl
    rw [hDd.closure_eq] at hsub
    exact inner_self_eq_zero.1 (hsub (mem_univ _))
  have hwz : w = 0 := by
    refine Lp.ext ?_
    filter_upwards [hw0, Lp.coeFn_zero G 2 timeMeasure] with t h1 h2
    rw [h1, h2, Pi.zero_apply]
  ext F
  rw [← hw, hwz, inner_zero_left, zero_apply]

end Tensor

/-! ### The Bochner time integral `∫_I K(s,t) F(t) dt` -/

section Bochner

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- **The Bochner time integral** `s ↦ ∫_I |s-t|^{-a} F(t) dt` of Step 2 of
`L:positive-raw-embedding` (TeX lines 71-72 at revision edf7085f (book 1.1.3)), for a field
`F : ℝ → G`; Step 4 (TeX lines 126-127) uses it at every `s` for `F = (t ↦ Ψ_t)`. -/
def kBochner (a : ℝ) (F : ℝ → G) (s : ℝ) : G := ∫ t, kern a (s - t) • F t ∂timeMeasure

/-- Auxiliary: for `s ∈ [0,1]`, `t ↦ |s-t|^{-a}` is integrable on `I` (`a < 1`). -/
theorem kern_integrable_row {a s : ℝ} (ha1 : a < 1) (hs : s ∈ Icc (0 : ℝ) 1) :
    Integrable (fun t => kern a (s - t)) timeMeasure :=
  ((TimeSchur.integral_row (T := 1) ha1 hs).1).mono_set Ioo_subset_Icc_self

/-- Auxiliary: for `s ∈ [0,1]`, `∫_I |s-t|^{-a} dt ≤ K_0` (`0 ≤ a < 1`). -/
theorem integral_kern_row_le {a s : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) (hs : s ∈ Icc (0 : ℝ) 1) :
    ∫ t, kern a (s - t) ∂timeMeasure ≤ K0 a := by
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun t => kern_nonneg _ _)
    (kern_integrable_row ha1 hs).aestronglyMeasurable]
  exact ENNReal.toReal_le_of_le_ofReal (OccupationCeilingFinite.K0_pos ha1).le
    (OccupationCeilingFinite.row_le ha0 ha1 hs)

/-- Auxiliary: for a bounded strongly measurable `F` and `s ∈ [0,1]`, the integrand of
`kBochner` is integrable. -/
theorem integrable_kern_smul {a s : ℝ} (ha1 : a < 1) (hs : s ∈ Icc (0 : ℝ) 1) {F : ℝ → G}
    (hF : AEStronglyMeasurable F timeMeasure) {C : ℝ} (hC : ∀ t, ‖F t‖ ≤ C) :
    Integrable (fun t => kern a (s - t) • F t) timeMeasure := by
  refine ((kern_integrable_row ha1 hs).mul_const C).mono' ?_ (ae_of_all _ fun t => ?_)
  · exact (((measurable_kern a).comp (measurable_const.sub measurable_id)).aestronglyMeasurable
      ).smul hF
  · rw [norm_smul, Real.norm_of_nonneg (kern_nonneg _ _)]
    exact mul_le_mul_of_nonneg_left (hC t) (kern_nonneg _ _)

/-- Auxiliary: `‖∫_I K(s,t) F(t) dt‖ ≤ K_0 C` for `‖F‖ ≤ C`, `s ∈ [0,1]` (the TeX's "norm at most
`K_0 sup_t ‖Ψ_t‖`", line 127). -/
theorem norm_kBochner_le {a s : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) (hs : s ∈ Icc (0 : ℝ) 1)
    {F : ℝ → G} {C : ℝ} (hC : ∀ t, ‖F t‖ ≤ C) : ‖kBochner a F s‖ ≤ K0 a * C := by
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  unfold kBochner
  refine (norm_integral_le_of_norm_le ((kern_integrable_row ha1 hs).mul_const C)
    (ae_of_all _ fun t => ?_)).trans ?_
  · rw [norm_smul, Real.norm_of_nonneg (kern_nonneg _ _)]
    exact mul_le_mul_of_nonneg_left (hC t) (kern_nonneg _ _)
  · rw [integral_mul_const]
    exact mul_le_mul_of_nonneg_right (integral_kern_row_le ha0 ha1 hs) hC0

/-- Auxiliary: for a continuous field, `kBochner a F` is strongly measurable. -/
theorem stronglyMeasurable_kBochner (a : ℝ) {F : ℝ → G} (hF : Continuous F) : StronglyMeasurable (kBochner a F) :=
  StronglyMeasurable.integral_prod_right' (ν := timeMeasure)
    (f := fun z : ℝ × ℝ => kern a (z.1 - z.2) • F z.2)
    ((((measurable_kern a).comp (measurable_fst.sub measurable_snd)).stronglyMeasurable).smul
      (hF.stronglyMeasurable.comp_measurable measurable_snd))

/-- Auxiliary: for a continuous bounded field, `kBochner a F ∈ L²(I; G)`. -/
theorem memLp_kBochner {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) {F : ℝ → G} (hF : Continuous F) {C : ℝ}
    (hC : ∀ t, ‖F t‖ ≤ C) : MemLp (kBochner a F) 2 timeMeasure := by
  refine MemLp.of_bound (stronglyMeasurable_kBochner a hF).aestronglyMeasurable (K0 a * C) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
  exact norm_kBochner_le ha0 ha1 (Ioo_subset_Icc_self hs) hC

end Bochner

/-! ### Step 2: the completed temporal mean is the Bochner integral -/

section Step2

variable {S : SpData d} {p : TParams}

/-- Auxiliary: the kernel form against a single smooth tensor,
`∫∫ K(s,t) ⟪φ(s), f(t) q⟫ = ∫ (K f)(s) ⟪φ(s), q⟫ ds` (Fubini). -/
theorem kform_tensor {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G] [CompleteSpace G]
    {φ : ℝ → G} (hφ : MemLp φ 2 timeMeasure) {f : ℝ → ℝ} (hf : IsTimeTest f) (q : G) :
    kform p.a φ (fun t => f t • q) = ∫ s, kMean p.a f s * ⟪φ s, q⟫ ∂timeMeasure := by
  unfold kform
  rw [integral_prod _ (OccupationCompletion.kform_integrable p.ha0.le p.ha1 hφ
    (memLp_tensor (G := G) hf q))]
  refine integral_congr_ae (ae_of_all _ fun s => ?_)
  simp only [inner_smul_right, kMean]
  rw [← integral_mul_const]
  refine integral_congr_ae (ae_of_all _ fun t => ?_)
  simp only
  ring

/-- **Step 2 of `L:positive-raw-embedding`** (TeX lines 69-82 at revision edf7085f (book
1.1.3)), weak form: for every `φ, F ∈ L²(I; H_sp)`,
`⟪φ, (C_t ⊗ I) J F⟫_{L²(I;H_sp)} = ⟪J φ, J F⟫_{H_I}`. -/
theorem inner_U_J {η : CutoffProfile d} {r : ℝ≥0∞} [Fact (1 ≤ r)]
    (Ureg : UniformMeanRegulator p S η r) (φ F : Lp (Hsp S) 2 timeMeasure) :
    ⟪φ, inclTwo Ureg.two_lt_r.le (Ureg.U (J p (Hsp S) F))⟫ = ⟪J p (Hsp S) φ, J p (Hsp S) F⟫ := by
  set A : Lp (Hsp S) 2 timeMeasure →L[ℝ] Lp (Hsp S) 2 timeMeasure :=
    inclTwo Ureg.two_lt_r.le ∘L Ureg.U ∘L J p (Hsp S) with hA
  set ℓ : Lp (Hsp S) 2 timeMeasure →L[ℝ] ℝ :=
    innerSL ℝ φ ∘L A - innerSL ℝ (J p (Hsp S) φ) ∘L J p (Hsp S) with hℓ
  have hz : ℓ = 0 := by
    refine clm_eq_zero_of_tensor ℓ fun f hf q hF => ?_
    simp only [hℓ, hA, sub_apply, ContinuousLinearMap.comp_apply,
      innerSL_apply_apply]
    rw [sub_eq_zero, (OccupationCompletion.positive_bochner_inclusion _).2.2.2,
      OccupationCompletion.kform_congr p.a (Filter.EventuallyEq.refl _ _) hF.coeFn_toLp,
      kform_tensor (Lp.memLp φ) hf q, MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [coeFn_inclTwo Ureg.two_lt_r.le (Ureg.U (J p (Hsp S) (hF.toLp _))),
      Ureg.U_tensor f hf q hF] with s h1 h2
    rw [h1, h2, inner_smul_right]
  have := congrArg (fun L => L F) hz
  simp only [hℓ, hA, sub_apply, ContinuousLinearMap.comp_apply,
    innerSL_apply_apply, zero_apply, sub_eq_zero] at this
  exact this

/-- **Step 2 of `L:positive-raw-embedding`, the identification** (TeX lines 69-82 at revision
edf7085f (book 1.1.3)): for a smooth compactly supported field `Ψ`, the completed temporal mean
of its inclusion is the Bochner integral, `U(Ψ)(s) = ∫_I |s-t|^{-a} Ψ_t dt` for a.e. `s`. -/
theorem U_incl_ae {η : CutoffProfile d} {r : ℝ≥0∞} [Fact (1 ≤ r)]
    (Ureg : UniformMeanRegulator p S η r) {Ψ : ℝ × Rd d → ℝ} (hΨ : ContDiff ℝ ∞ Ψ)
    (hΨs : HasCompactSupport Ψ) :
    (Ureg.U (incl p S Ψ) : ℝ → Hsp S) =ᵐ[timeMeasure] kBochner p.a (sliceField S Ψ) := by
  obtain ⟨hc, C, hC⟩ := OccupationCompletion.sliceField_continuous_bdd (S := S) hΨ hΨs
  have hF₀ := OccupationCompletion.sliceField_memLp (S := S) hΨ hΨs
  set F₀ := hF₀.toLp (sliceField S Ψ) with hF₀def
  have hincl : incl p S Ψ = J p (Hsp S) F₀ := by
    simp only [incl, hΨ, hΨs, and_self, ↓reduceDIte, hF₀def]
  have hY := memLp_kBochner p.ha0.le p.ha1 hc hC
  set Y := hY.toLp (kBochner p.a (sliceField S Ψ)) with hYdef
  set X := inclTwo Ureg.two_lt_r.le (Ureg.U (J p (Hsp S) F₀)) with hXdef
  have hXY : X = Y := by
    refine ext_inner_left ℝ fun φ => ?_
    rw [hXdef, inner_U_J, (OccupationCompletion.positive_bochner_inclusion _).2.2.2,
      OccupationCompletion.kform_congr p.a (Filter.EventuallyEq.refl _ _) hF₀.coeFn_toLp,
      MeasureTheory.L2.inner_def]
    unfold kform
    rw [integral_prod _ (OccupationCompletion.kform_integrable p.ha0.le p.ha1 (Lp.memLp φ) hF₀)]
    refine integral_congr_ae ?_
    filter_upwards [hY.coeFn_toLp, ae_restrict_mem measurableSet_Ioo] with s h1 hs
    rw [h1, kBochner, ← integral_inner (integrable_kern_smul p.ha1 (Ioo_subset_Icc_self hs)
      hc.aestronglyMeasurable hC)]
    simp only [inner_smul_right]
  rw [hincl]
  filter_upwards [coeFn_inclTwo Ureg.two_lt_r.le (Ureg.U (J p (Hsp S) F₀)), hY.coeFn_toLp]
    with s h1 h2
  rw [← h1, ← hXdef, hXY, h2]

end Step2

/-! ### Step 4: the masked operator mean at every time -/

section Step4

/-- Auxiliary to Step 4 (the "Fubini step [with] two fixed compact supports and integrable time
kernel", TeX line 123 at revision edf7085f (book 1.1.3)): for `a < 1`, locally finite `Γ`, a
continuous compactly supported field `Ψ`, a continuous compactly supported `φ` and `s ∈ [0,1]`,
`∫ h_{Ψ,s}(x) φ(x) dx = ∫_I |s-t|^{-a} B_Γ(φ, Ψ_t) dt` (same route as the row identity inside
`SpaceTimePositivity.integral_mean_mul_eq_stForm_swap`). -/
theorem integral_mean_mul_test {a : ℝ} (ha1 : a < 1) (Γ : Measure (Rd d))
    [IsLocallyFiniteMeasure Γ] {Ψ : ℝ × Rd d → ℝ} (hΨ : Continuous Ψ)
    (hΨs : HasCompactSupport Ψ) {φ : Rd d → ℝ} (hφ : Continuous φ) (hφs : HasCompactSupport φ)
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    ∫ x, mean a Γ Ψ s x * φ x =
      ∫ t, kern a (s - t) * spatialPair Γ φ (fun x => Ψ (t, x)) ∂timeMeasure := by
  obtain ⟨MΨ, RΨ, hMΨ0, -, hMΨ, hRΨ⟩ := SpaceTimePositivity.field_data hΨ hΨs
  obtain ⟨Mφ, hMφ⟩ := hφ.bounded_above_of_compact_support hφs
  obtain ⟨Rφ, -, hRφ⟩ := hφs.exists_pos_le_norm
  set R := max RΨ Rφ with hR
  have hRΨ' : ∀ t x, R < ‖x‖ → Ψ (t, x) = 0 := fun t x hx =>
    hRΨ t x (lt_of_le_of_lt (le_max_left _ _) hx)
  have hRφ' : ∀ x, R < ‖x‖ → φ x = 0 := fun x hx =>
    hRφ x ((le_max_right _ _).trans hx.le)
  have hMφ' : ∀ x, |φ x| ≤ Mφ := fun x => by simpa using hMφ x
  have hMφ0 : 0 ≤ Mφ := (abs_nonneg _).trans (hMφ' 0)
  set C : ℝ := Mφ * (MΨ * Γ.real (Metric.closedBall (0 : Rd d) (2 * R))) with hC
  have hC0 : 0 ≤ C := by positivity
  set Jf : ℝ → Rd d → ℝ := fun t x =>
    kern a (s - t) * (φ x * conv Γ (fun y => Ψ (t, y)) x) with hJ
  have hcm := SpaceTimePositivity.conv_stronglyMeasurable Γ hΨ
  have hJi : Integrable (Function.uncurry Jf) (timeMeasure.prod (volume : Measure (Rd d))) := by
    have hk := kern_integrable_row ha1 hs
    have hind : Integrable ((Metric.closedBall (0 : Rd d) R).indicator fun _ => C)
        (volume : Measure (Rd d)) :=
      (integrable_indicator_iff measurableSet_closedBall).2
        (integrableOn_const (measure_closedBall_lt_top
          (μ := (volume : Measure (Rd d)))).ne)
    refine (hk.mul_prod hind).mono' ?_ (ae_of_all _ fun z => ?_)
    · exact (((measurable_kern a).comp
        (measurable_const.sub measurable_fst)).aestronglyMeasurable).mul
        ((hφ.comp continuous_snd).aestronglyMeasurable.mul hcm.aestronglyMeasurable)
    · simp only [Function.uncurry, hJ]
      rw [norm_mul, Real.norm_eq_abs (kern a _), abs_of_nonneg (kern_nonneg _ _)]
      by_cases hx : R < ‖z.2‖
      · rw [hRφ' _ hx, zero_mul, norm_zero, mul_zero]
        exact mul_nonneg (kern_nonneg _ _) (indicator_nonneg (fun _ _ => hC0) _)
      · have hz : z.2 ∈ Metric.closedBall (0 : Rd d) R := by
          rw [Metric.mem_closedBall, dist_zero_right]; exact not_lt.1 hx
        rw [indicator_of_mem hz]
        refine mul_le_mul_of_nonneg_left ?_ (kern_nonneg _ _)
        rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, hC]
        exact mul_le_mul (hMφ' _) (SpaceTimePositivity.abs_conv_le Γ hMΨ hRΨ' z.1
          (not_lt.1 hx)) (abs_nonneg _) hMφ0
  have hsx : ∀ x, ∫ t, Jf t x ∂timeMeasure = mean a Γ Ψ s x * φ x := by
    intro x
    have e : ∀ t, Jf t x = φ x * (kern a (s - t) * conv Γ (fun y => Ψ (t, y)) x) := by
      intro t; simp only [hJ]; ring
    simp_rw [e]
    rw [integral_const_mul, mul_comm]
    rfl
  have hxs : ∀ t, ∫ x, Jf t x = kern a (s - t) * spatialPair Γ φ (fun x => Ψ (t, x)) := by
    intro t
    simp only [hJ]
    rw [integral_const_mul, SpaceTimePositivity.spatialPair_eq_conv Γ (F := φ)
      (G := fun x => Ψ (t, x)) hφ (hΨ.comp (by fun_prop)) hMφ' (fun x => hMΨ (t, x)) hRφ'
      (fun x hx => hRΨ' t x hx)]
  simp_rw [← hsx, ← hxs]
  exact (integral_integral_swap hJi).symm

variable {S : SpData d}

/-- **Step 4 of `L:positive-raw-embedding`, the row of the Bochner mean** (TeX lines 116-122 at
revision edf7085f (book 1.1.3)): for `Ψ` smooth compactly supported, every `s ∈ [0,1]` and every
real test `φ`, `⟪∫_I K(s,t) Ψ_t dt, [φ]⟫_{H_sp} = ∫ h_{Ψ,s} φ`. -/
theorem inner_kBochner_toHsp {a : ℝ} (ha1 : a < 1) {Ψ : ℝ × Rd d → ℝ} (hΨ : ContDiff ℝ ∞ Ψ)
    (hΨs : HasCompactSupport Ψ) {φ : Rd d → ℝ} (hφ : IsTestFunction φ) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) :
    ⟪kBochner a (sliceField S Ψ) s, toHsp S φ⟫ = ∫ x, mean a S.Γ Ψ s x * φ x := by
  obtain ⟨hc, C, hC⟩ := OccupationCompletion.sliceField_continuous_bdd (S := S) hΨ hΨs
  rw [integral_mean_mul_test ha1 S.Γ hΨ.continuous hΨs hφ.1.continuous hφ.2 hs,
    real_inner_comm, kBochner, ← integral_inner (integrable_kern_smul ha1 hs
      hc.aestronglyMeasurable hC)]
  refine integral_congr_ae (ae_of_all _ fun t => ?_)
  simp only [inner_smul_right, sliceField]
  rw [OccupationCompletion.inner_toHsp hφ
    (OccupationCompletion.slice_isTest hΨ hΨs t)]

/-- Auxiliary: `⟪(u,v), (u',v')⟫_E = ⟪u,u'⟫ + ⟪v,v'⟫`. -/
theorem inner_toE (u u' : Hhalf d) (v v' : Hmhalf d) :
    ⟪toE u v, toE u' v'⟫ = ⟪u, u'⟫ + ⟪v, v'⟫ :=
  WithLp.prod_inner_apply (toE u v : WithLp 2 (Hhalf d × Hmhalf d)) (toE u' v')

/-- Auxiliary: the states `(f, z₂)`, `f` a real test, are dense in `E`. -/
theorem dense_testStates (h0 : UM0Facts d) :
    Dense {z : E d | ∃ f z₂, IsTestFunction f ∧ z = toE (toHhalf f) z₂} := by
  have hA := h0.denseRange_toHhalf.prod (dense_univ (X := Hmhalf d))
  have hsurj : DenseRange (eEquiv (d := d)).symm := (eEquiv (d := d)).symm.surjective.denseRange
  refine (hsurj.dense_image (eEquiv (d := d)).symm.continuous hA).mono ?_
  rintro _ ⟨⟨u, v⟩, ⟨⟨f, hf, rfl⟩, -⟩, rfl⟩
  exact ⟨f, v, hf, rfl⟩

/-- Auxiliary: the states `(w₁, Λ g)`, `g` a real test, are dense in `E`. -/
theorem dense_dualStates (h0 : UM0Facts d) :
    Dense {w : E d | ∃ w₁ g, IsTestFunction g ∧ w = toE w₁ (lam (toHhalf g))} := by
  have hB : Dense ((lam (d := d)) '' {x : Hhalf d | ∃ φ, IsTestFunction φ ∧ x = toHhalf φ}) :=
    (lam (d := d)).surjective.denseRange.dense_image (lam (d := d)).continuous
      h0.denseRange_toHhalf
  have hA := (dense_univ (X := Hhalf d)).prod hB
  have hsurj : DenseRange (eEquiv (d := d)).symm := (eEquiv (d := d)).symm.surjective.denseRange
  refine (hsurj.dense_image (eEquiv (d := d)).symm.continuous hA).mono ?_
  rintro _ ⟨⟨u, v⟩, ⟨-, ⟨_, ⟨g, hg, rfl⟩, rfl⟩⟩, rfl⟩
  exact ⟨u, g, hg, rfl⟩

/-- **Step 4 of `L:positive-raw-embedding`, "Dense states extend the identity to `E`"** (TeX lines
116-126 at revision edf7085f (book 1.1.3)): if `q ∈ H_sp` has the row
`⟪q, k_R(f,g)⟫ = ∫ V f g` for all real tests `f, g` and `M` is the multiplier by `V`, then
`T_R q = B_E(M)`. -/
theorem T_eq_BE (h0 : UM0Facts d) {η : CutoffProfile d} {R : ℝ} (Tc : CameronSpatialMap S η R)
    {q : Hsp S} {V : Rd d → ℝ} {M : Hhalf d →L[ℝ] Hmhalf d} (hM : IsMultiplier V M)
    (hq : ∀ f g : Rd d → ℝ, IsTestFunction f → IsTestFunction g →
      ⟪q, rowTest S η R f g⟫ = ∫ x, V x * f x * g x) :
    Tc.T q = BE M := by
  set D := Tc.T q - BE M with hD
  have hdw : ∀ z ∈ {z : E d | ∃ f z₂, IsTestFunction f ∧ z = toE (toHhalf f) z₂},
      ∀ w ∈ {w : E d | ∃ w₁ g, IsTestFunction g ∧ w = toE w₁ (lam (toHhalf g))},
      ⟪D z, w⟫ = 0 := by
    rintro _ ⟨f, z₂, hf, rfl⟩ _ ⟨w₁, g, hg, rfl⟩
    have hVf : IsTestFunction fun x => V x * f x := ⟨hM.1.mul hf.1, hf.2.mul_left⟩
    rw [hD, sub_apply, inner_sub_left, Tc.row q f g hf hg z₂ w₁,
      h0.BE_apply, inner_toE, inner_zero_left, zero_add, hM.2 f hf,
      h0.inner_toHmhalf_lam hVf hg, hq f g hf hg, sub_eq_zero]
  have hz : ∀ z ∈ {z : E d | ∃ f z₂, IsTestFunction f ∧ z = toE (toHhalf f) z₂}, D z = 0 := by
    intro z hz
    have hcl : IsClosed {w : E d | ⟪D z, w⟫ = 0} :=
      isClosed_eq (continuous_const.inner continuous_id) continuous_const
    have hsub := closure_minimal (fun w hw => hdw z hz w hw) hcl
    rw [(dense_dualStates h0).closure_eq] at hsub
    exact inner_self_eq_zero.1 (hsub (mem_univ _))
  have hcl : IsClosed {z : E d | D z = 0} := isClosed_eq D.continuous continuous_const
  have hsub := closure_minimal hz hcl
  rw [(dense_testStates h0).closure_eq] at hsub
  have hD0 : D = 0 := ContinuousLinearMap.ext fun z => hsub (mem_univ z)
  exact sub_eq_zero.1 hD0

/-- Auxiliary: `η_R = η(·/R)` is smooth. -/
theorem etaR_contDiff (η : CutoffProfile d) (R : ℝ) : ContDiff ℝ ∞ (etaR η R) :=
  η.smooth.comp (contDiff_id.const_smul R⁻¹)

/-- Auxiliary: `m_R = η(·/R)²` is smooth. -/
theorem mR_contDiff (η : CutoffProfile d) (R : ℝ) : ContDiff ℝ ∞ (mR η R) := by
  have : mR η R = fun x => etaR η R x ^ 2 := funext (mR_eq η R)
  rw [this]
  exact (etaR_contDiff η R).pow 2

/-- Auxiliary: `0 ≤ m_R ≤ 1`. -/
theorem mR_mem (η : CutoffProfile d) (R : ℝ) (x : Rd d) : 0 ≤ mR η R x ∧ mR η R x ≤ 1 := by
  rw [mR_eq, etaR]
  exact ⟨sq_nonneg _, pow_le_one₀ (η.nonneg _) (η.le_one _)⟩

/-- **Step 4 of `L:positive-raw-embedding`** (TeX lines 114-131 at revision edf7085f (book
1.1.3)): for `Ψ` smooth compactly supported, `s ∈ [0,1]` and `M` the multiplier by
`m_R h_{Ψ,s}`, `T_R(∫_I K(s,t) Ψ_t dt) = B_E(M)`. -/
theorem T_kBochner_eq (h0 : UM0Facts d) {p : TParams} {η : CutoffProfile d} {R : ℝ}
    (Tc : CameronSpatialMap S η R) {Ψ : ℝ × Rd d → ℝ} (hΨ : ContDiff ℝ ∞ Ψ)
    (hΨs : HasCompactSupport Ψ) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) {M : Hhalf d →L[ℝ] Hmhalf d}
    (hM : IsMultiplier (fun x => mR η R x * mean p.a S.Γ Ψ s x) M) :
    Tc.T (kBochner p.a (sliceField S Ψ) s) = BE M := by
  refine T_eq_BE h0 Tc hM fun f g hf hg => ?_
  have hk : IsTestFunction fun x => (etaR η R x * f x) * (etaR η R x * g x) :=
    ⟨((etaR_contDiff η R).mul hf.1).mul ((etaR_contDiff η R).mul hg.1),
      (hf.2.mul_left.mul_right)⟩
  rw [rowTest, inner_kBochner_toHsp p.ha1 hΨ hΨs hk hs]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  simp only [mR_eq]
  ring

end Step4

/-! ### The mean identity of `E:positive-raw-mean` and the canonical version -/

section Main

variable {p : TParams} {S : SpData d}

/-- **`E:positive-raw-mean` (mean identity) and the canonical-version sentence of
`L:positive-raw-embedding`** (TeX lines 32-39, proof 42-132, at revision edf7085f (book 1.1.3)),
from the regulator and the UM-0 facts, for any covariance data `S` whose means `h_{Ψ,s}`
(`s ∈ (0,1)`) are smooth and bounded. -/
theorem positive_raw_mean_of (h0 : UM0Facts d) {η : CutoffProfile d} {r : ℝ≥0∞} [Fact (1 ≤ r)]
    (Ureg : UniformMeanRegulator p S η r)
    (hmean : ∀ Ψ ∈ CPos d, ∀ s ∈ Ioo (0 : ℝ) 1,
      ContDiff ℝ ∞ (mean p.a S.Γ Ψ s) ∧ ∃ C, ∀ x, |mean p.a S.Γ Ψ s x| ≤ C) :
    PositiveRawMeanTarget Ureg := by
  intro Ψ hΨ R hR
  set Tc := Ureg.Tsp R hR
  set V : ℝ → Rd d → ℝ := fun s x => mR η R x * mean p.a S.Γ Ψ s x with hV
  set Mf : ℝ → (Hhalf d →L[ℝ] Hmhalf d) := fun s =>
    open Classical in if h : ∃ M, IsMultiplier (V s) M then h.choose else 0 with hMfdef
  have hMf : ∀ s ∈ Ioo (0 : ℝ) 1, IsMultiplier (V s) (Mf s) := by
    intro s hs
    obtain ⟨hsm, C, hC⟩ := hmean Ψ hΨ s hs
    have hVs : ContDiff ℝ ∞ (V s) := (mR_contDiff η R).mul hsm
    have hb : ∀ x, |V s x| ≤ C := by
      intro x
      obtain ⟨h1, h2⟩ := mR_mem η R x
      rw [hV, abs_mul, abs_of_nonneg h1]
      calc mR η R x * |mean p.a S.Γ Ψ s x| ≤ 1 * |mean p.a S.Γ Ψ s x| :=
            mul_le_mul_of_nonneg_right h2 (abs_nonneg _)
        _ ≤ C := by rw [one_mul]; exact hC x
    have hex : ∃ M, IsMultiplier (V s) M := (h0.exists_isMultiplier hVs hb).imp fun _ h => h.1
    simp only [hMfdef, hex, ↓reduceDIte]
    exact hex.choose_spec
  have hX := U_incl_ae Ureg hΨ.1 hΨ.2.1
  have hcomp : (meanOp Tc.T Ureg.U (incl p S Ψ) : ℝ → E d →L[ℝ] E d) =ᵐ[timeMeasure]
      fun s => Tc.T ((Ureg.U (incl p S Ψ) : ℝ → Hsp S) s) :=
    ContinuousLinearMap.coeFn_compLpL (L := Tc.T) (Ureg.U (incl p S Ψ))
  have hcan : (meanOp Tc.T Ureg.U (incl p S Ψ) : ℝ → E d →L[ℝ] E d) =ᵐ[timeMeasure]
      fun s => BE (Mf s) := by
    filter_upwards [hcomp, hX, ae_restrict_mem measurableSet_Ioo] with s h1 h2 hs
    rw [h1, h2]
    exact T_kBochner_eq h0 Tc hΨ.1 hΨ.2.1 (Ioo_subset_Icc_self hs) (hMf s hs)
  refine ⟨?_, Mf, hMf, hcan⟩
  filter_upwards [hcan, ae_restrict_mem measurableSet_Ioo] with s h1 hs
  exact ⟨Mf s, hMf s hs, h1⟩

/-- Auxiliary: under `H:homog` with `Γ ≠ 0`, the means `h_{Ψ,s}`, `Ψ ∈ C_pos`, are smooth and
bounded for every `s ∈ [0,1]` (`L:variational-global-mean`,
`VariationalMeanDerivatives.variational_global_mean_whole_paper`). -/
theorem mean_smooth_bdd {alpha alpha0 : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogCovariance d alpha alpha0 Γ μ) (hΓ : Γ ≠ 0) {Ψ : ℝ × Rd d → ℝ}
    (hΨ : Ψ ∈ CPos d) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    ContDiff ℝ ∞ (mean alpha0 Γ Ψ s) ∧ ∃ C, ∀ x, |mean alpha0 Γ Ψ s x| ≤ C := by
  obtain ⟨⟨hsm, -, -⟩, M, -, hM0, -, hM, -⟩ :=
    VariationalMeanDerivatives.variational_global_mean_whole_paper hH hΓ hΨ
  refine ⟨hsm.comp (contDiff_const.prodMk contDiff_id), M, fun x => ?_⟩
  obtain ⟨h1, h2⟩ := hM s hs x
  rw [abs_of_nonneg h1]
  exact h2

/-- **`E:positive-raw-mean` (mean identity) and the canonical version under `H:homog`**, with the
UM-0 facts as an explicit argument (the form used until agent A's UM-0 lemmas land; TeX lines
32-39 at revision edf7085f (book 1.1.3)). -/
theorem positive_raw_mean_paper_of_um0 (h0 : UM0Facts d) {alpha alpha0 : ℝ}
    {Γ μ : Measure (Rd d)} (hH : HomogCovariance d alpha alpha0 Γ μ) (hΓ : Γ ≠ 0)
    (η : CutoffProfile d) {r : ℝ≥0∞} [Fact (1 ≤ r)]
    (Ureg : UniformMeanRegulator (TParams.ofHomog hH) (SpData.ofHomog hH) η r) :
    PositiveRawMeanTarget Ureg :=
  positive_raw_mean_of h0 Ureg fun _ hΨ _ hs => mean_smooth_bdd hH hΓ hΨ (Ioo_subset_Icc_self hs)

/-- **UM-2: the mean identity of `E:positive-raw-mean` and the canonical-version sentence of
`L:positive-raw-embedding`** (`integrated_intrinsic_constant.tex` lines 32-39, proof lines
42-132, at revision edf7085f (book 1.1.3)), under `H:homog` with `Γ ≠ 0`, for every regulator
`Ureg` (the named input of `P:uniform-mean-regulator`): for `Ψ ∈ C_pos` and `R ≥ 1`,
`𝒯_R Ψ(s) = B_E(m_R h_{Ψ,s})` for a.e. `s`, and `s ↦ B_E(m_R h_{Ψ,s})` (multipliers at every
`s ∈ I`) is a version of `𝒯_R Ψ`. -/
theorem positive_raw_mean_paper {alpha alpha0 : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogCovariance d alpha alpha0 Γ μ) (hΓ : Γ ≠ 0) (η : CutoffProfile d)
    {r : ℝ≥0∞} [Fact (1 ≤ r)]
    (Ureg : UniformMeanRegulator (TParams.ofHomog hH) (SpData.ofHomog hH) η r) :
    PositiveRawMeanTarget Ureg :=
  positive_raw_mean_paper_of_um0 um0Facts hH hΓ η Ureg

end Main

end StratonovichHAMSecondMoment.PositiveRawMean
