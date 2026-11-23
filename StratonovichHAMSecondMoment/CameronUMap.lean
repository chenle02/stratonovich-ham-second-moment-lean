module

/-
Copyright 2026 Le Chen. SPDX-License-Identifier: Apache-2.0

Wave L16, item L16-D, part 1 of the assembly: the completed time map
`U = C_t ⊗ I_G : H_t ⊗ G → L^r(I; G)` on the kernel completion `HK p G` of `L²(I; G)`, its
defining formula on single smooth tensors (`UTensorSpec`) and its norm bound, by the
**kernel-positivity route** (decision 4 of L16; disclosed).

TeX anchors (revision edf7085f, book 1.1.3):
* `integrated_uniform_mean.tex` lines 257-270 (`U = C_t ⊗ I_{H_sp}`, `c_t = ‖C_t‖`), and
  `L:uniform-mean-tensor` lines 198-206 (used at `A = C_t`, line 312-313);
* `integrated_cameron_mean.tex` lines 225-237 (`P:cameron-temporal-map`, `C_t`), 283-293 (the
  bound `‖g‖²_{H_t} ≤ ‖K_a‖_{r/2} ‖g‖²_{r'}`), 322-369 (`P:cameron-full-mean`, the map `𝒰`
  and its Step 1 bound).

Route (differs from the TeX, disclosed).  The TeX bounds `U` by `L:uniform-mean-tensor`
(Gaussian moments, finite tensors, density of finite tensors in `H_t ⊗ H_sp`).  The Lean `H_I`
is the kernel completion of `L²(I; H_sp)` (decision 4 of L9/L14), not a tensor product, so
here `U` is built directly: on `F ∈ L²(I; G)`, `U(J F)` is the Bochner field
`s ↦ ∫_I |s-t|^{-a} F(t) dt` (`PositiveRawMean.kBochner`), and the bound
`‖U(J F)‖_{L^r} ≤ B ‖J F‖` follows from a **dual bound** `‖J g‖ ≤ B ‖g‖_{r'}` on bounded
fields `g` (`DualBound`) by testing against the truncated duality fields
`g_n = 1_{‖Y‖ ≤ n} ‖Y‖^{r-2} Y` (`lintegral_rpow_kBochner_le`).  The dual bound holds
* with `B = ‖C_t‖` for every temporal core `T : TemporalMeanCore` (`dualBound_of_core`):
  kernel positivity `|s-t|^{-a} ≥ 0` gives `‖J_G g‖ ≤ ‖J_ℝ |g|‖`, and
  `‖J_ℝ h‖² = ⟪h, K h⟫ = ∫ h · C_t(J h) ≤ ‖h‖_{r'} ‖C_t‖ ‖J h‖` (Hölder);
* with `B = ‖K_a‖_{r/2}^{1/2}` from the absolute kernel bound `KformAbsTarget`
  (`dualBound_of_kformAbs`; C's `kform_abs`), with **no** temporal core and no compactness.
The extension to the completion is Mathlib's `LinearMap.extendOfNorm`.

Headline results:
* `u_map`: `UMapTarget p S r` (D target 2; `YoungTarget`, `KformAbsTarget` are the frozen
  hypotheses of the interface and are not used by this route);
* `exists_uTensorSpec_of_kformAbs`: a `U` with `UTensorSpec` and `‖U‖ ≤ √(KaNorm a r)` from
  `KformAbsTarget` alone (used by `positive_raw_embedding_constructed`).

Lemmas whose doc comments say "Auxiliary" have no manuscript label.
-/
public import Mathlib
public import StratonovichHAMSecondMoment.CameronInterface

@[expose] public section

noncomputable section

set_option autoImplicit false

open MeasureTheory Set Filter Topology
open scoped ENNReal RealInnerProductSpace

namespace StratonovichHAMSecondMoment.CameronUMap

open HomogHypothesis (Rd HomogCovariance)
open OccupationCompletion (TParams SpData Hsp HK Ht HI J Jlin kform)
open SpaceTimePositivity (timeMeasure)
open TimeSchur (kern kern_nonneg measurable_kern)
open UniformMeanInterface (kMean IsTimeTest)
open PositiveRawMean (kBochner)
open CameronInterface

/-! ### The Bochner field of an `L²(I; G)` class -/

section Field

variable {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G] [CompleteSpace G]

omit [CompleteSpace G] in
/-- Auxiliary: for `F ∈ L²(I; G)` the field `(s,t) ↦ |s-t|^{-a} F(t)` is integrable on `I²`. -/
theorem integrable_kern_smul_prod {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) {F : ℝ → G}
    (hF : MemLp F 2 timeMeasure) :
    Integrable (fun z : ℝ × ℝ => kern a (z.1 - z.2) • F z.2) (timeMeasure.prod timeMeasure) := by
  have h1 : MemLp (fun _ : ℝ => (1 : ℝ)) 2 timeMeasure := memLp_const 1
  have hi := OccupationCompletion.kform_integrable ha0 ha1 h1 hF.norm
  refine hi.mono' (((measurable_kern a).comp
    (measurable_fst.sub measurable_snd)).aestronglyMeasurable.smul
      hF.aestronglyMeasurable.comp_snd) (ae_of_all _ fun z => ?_)
  have hz : ⟪(1 : ℝ), ‖F z.2‖⟫ = ‖F z.2‖ := by simp
  rw [norm_smul, Real.norm_of_nonneg (kern_nonneg _ _), hz]

omit [CompleteSpace G] in
/-- Auxiliary: for `F ∈ L²(I; G)` and a.e. `s`, `t ↦ |s-t|^{-a} F(t)` is integrable on `I`. -/
theorem ae_integrable_row {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) {F : ℝ → G}
    (hF : MemLp F 2 timeMeasure) :
    ∀ᵐ s ∂timeMeasure, Integrable (fun t => kern a (s - t) • F t) timeMeasure :=
  (integrable_kern_smul_prod ha0 ha1 hF).prod_right_ae

omit [CompleteSpace G] in
/-- Auxiliary: for a strongly measurable `F`, `kBochner a F` is strongly measurable. -/
theorem stronglyMeasurable_kBochner' (a : ℝ) {F : ℝ → G} (hF : StronglyMeasurable F) :
    StronglyMeasurable (kBochner a F) :=
  StronglyMeasurable.integral_prod_right' (ν := timeMeasure)
    (f := fun z : ℝ × ℝ => kern a (z.1 - z.2) • F z.2)
    ((((measurable_kern a).comp (measurable_fst.sub measurable_snd)).stronglyMeasurable).smul
      (hF.comp_measurable measurable_snd))

/-- Auxiliary (Fubini): for `g, F ∈ L²(I; G)`,
`∫∫ |s-t|^{-a} ⟪g(s), F(t)⟫ = ∫ ⟪g(s), ∫ |s-t|^{-a} F(t) dt⟫ ds`. -/
theorem kform_eq_integral_inner {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) {g F : ℝ → G}
    (hg : MemLp g 2 timeMeasure) (hF : MemLp F 2 timeMeasure) :
    kform a g F = ∫ s, ⟪g s, kBochner a F s⟫ ∂timeMeasure := by
  unfold kform
  rw [integral_prod _ (OccupationCompletion.kform_integrable ha0 ha1 hg hF)]
  refine integral_congr_ae ?_
  filter_upwards [ae_integrable_row ha0 ha1 hF] with s hs
  rw [kBochner, ← integral_inner hs (g s)]
  refine integral_congr_ae (ae_of_all _ fun t => ?_)
  simp only [inner_smul_right]

omit [CompleteSpace G] in
/-- Auxiliary: `kBochner` is additive a.e. on `L²` classes. -/
theorem kBochner_add_ae {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) (F F' : Lp G 2 timeMeasure) :
    kBochner a ⇑(F + F') =ᵐ[timeMeasure] kBochner a ⇑F + kBochner a ⇑F' := by
  filter_upwards [ae_integrable_row ha0 ha1 (Lp.memLp F),
    ae_integrable_row ha0 ha1 (Lp.memLp F')] with s h1 h2
  rw [Pi.add_apply, kBochner, kBochner, kBochner, ← integral_add h1 h2]
  refine integral_congr_ae ?_
  filter_upwards [Lp.coeFn_add F F'] with t ht
  rw [ht, Pi.add_apply, smul_add]

omit [CompleteSpace G] in
/-- Auxiliary: `kBochner` is homogeneous on `L²` classes. -/
theorem kBochner_smul_ae (a c : ℝ) (F : Lp G 2 timeMeasure) :
    kBochner a ⇑(c • F) =ᵐ[timeMeasure] c • kBochner a ⇑F := by
  refine ae_of_all _ fun s => ?_
  rw [Pi.smul_apply, kBochner, kBochner, ← integral_smul]
  refine integral_congr_ae ?_
  filter_upwards [Lp.coeFn_smul c F] with t ht
  rw [ht, Pi.smul_apply, smul_comm]

end Field

/-! ### The dual bound and the `L^r` estimate -/

section Estimate

variable {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G] [CompleteSpace G]

/-- **The dual bound** `‖J_G g‖_{H_t ⊗ G} ≤ B ‖g‖_{L^{r'}(I;G)}` (`r' = r/(r-1)`) for bounded
strongly measurable fields `g` (`integrated_cameron_mean.tex` lines 283-287 at revision
edf7085f (book 1.1.3), with `B = C_{a,r}`; for `B = ‖C_t‖` it is the adjoint form of
`‖C_t ⊗ I‖ ≤ ‖C_t‖`). -/
def DualBound (p : TParams) (G : Type*) [NormedAddCommGroup G] [InnerProductSpace ℝ G]
    [CompleteSpace G] (r B : ℝ) : Prop :=
  ∀ g : ℝ → G, StronglyMeasurable g → (∃ C, ∀ t, ‖g t‖ ≤ C) → ∀ hg : MemLp g 2 timeMeasure,
    ‖J p G (hg.toLp g)‖ ≤ B * (eLpNorm g (ENNReal.ofReal (r / (r - 1))) timeMeasure).toReal

/-- Auxiliary: `x^{r-2} x = x^{r-1}` for `x ≥ 0`. -/
theorem rpow_sub_two_mul {x r : ℝ} (hx : 0 ≤ x) (hr : 2 < r) :
    x ^ (r - 2) * x = x ^ (r - 1) := by
  rw [show r - 1 = (r - 2) + 1 by ring, Real.rpow_add' hx (by linarith), Real.rpow_one]

/-- Auxiliary: `x^{r-2} x² = x^r` for `x ≥ 0`. -/
theorem rpow_sub_two_mul_sq {x r : ℝ} (hx : 0 ≤ x) (hr : 2 < r) :
    x ^ (r - 2) * x ^ 2 = x ^ r := by
  rw [← Real.rpow_natCast x 2, ← Real.rpow_add' hx (by norm_num; linarith)]
  norm_num

/-- **The `L^r` estimate of the completed temporal mean** (`integrated_uniform_mean.tex` Step 2
lines 310-313, `integrated_cameron_mean.tex` lines 352-369, at revision edf7085f (book
1.1.3)), by duality: under the dual bound `B`, for every `F ∈ L²(I; G)`,
`∫_I ‖∫_I |s-t|^{-a} F(t) dt‖^r ds ≤ (B ‖J F‖)^r`.  Proof: test against the truncated
duality fields `g_n = 1_{‖Y‖≤n} ‖Y‖^{r-2} Y`, `Y = ∫ K(·,t) F(t) dt`:
`N_n = ∫ ⟪g_n, Y⟫ = ⟪J g_n, J F⟫ ≤ B ‖g_n‖_{r'} ‖J F‖ = B N_n^{1/r'} ‖J F‖`, then monotone
convergence. -/
theorem lintegral_rpow_kBochner_le {p : TParams} {r B : ℝ} (hr : 2 < r) (hB0 : 0 ≤ B)
    (hB : DualBound p G r B) (F : Lp G 2 timeMeasure) :
    ∫⁻ s, ‖kBochner p.a (⇑F) s‖ₑ ^ r ∂timeMeasure ≤ ENNReal.ofReal ((B * ‖J p G F‖) ^ r) := by
  set Y := kBochner p.a (⇑F) with hYdef
  have hYm : StronglyMeasurable Y := stronglyMeasurable_kBochner' p.a (Lp.stronglyMeasurable F)
  have hYn : Measurable fun s => ‖Y s‖ := hYm.norm.measurable
  have hYe : Measurable fun s => ‖Y s‖ₑ := by
    simpa only [ofReal_norm] using hYn.ennreal_ofReal
  set c := B * ‖J p G F‖ with hc
  have hc0 : 0 ≤ c := mul_nonneg hB0 (norm_nonneg _)
  have hr0 : 0 < r := by linarith
  set r' := r / (r - 1) with hr'
  have hr'0 : 0 < r' := div_pos hr0 (by linarith)
  have hr1 : r - 1 ≠ 0 := by linarith
  have hconj : 1 / r + 1 / r' = 1 := by
    rw [hr']
    field_simp
    ring
  set A : ℕ → Set ℝ := fun n => {s | ‖Y s‖ ≤ n} with hA
  have hAm : ∀ n, MeasurableSet (A n) := fun n =>
    measurableSet_le hYn measurable_const
  -- the pointwise identities on `A n`
  have hind : ∀ (n : ℕ) (s : ℝ), (A n).indicator (fun s => ‖Y s‖ₑ ^ r) s =
      ENNReal.ofReal ((A n).indicator (fun s => ‖Y s‖ ^ r) s) := by
    intro n s
    by_cases hs : s ∈ A n
    · rw [indicator_of_mem hs, indicator_of_mem hs, ← ofReal_norm,
        ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hr0.le]
    · rw [indicator_of_notMem hs, indicator_of_notMem hs, ENNReal.ofReal_zero]
  have key : ∀ n : ℕ, ∫⁻ s, (A n).indicator (fun s => ‖Y s‖ₑ ^ r) s ∂timeMeasure ≤
      ENNReal.ofReal (c ^ r) := by
    intro n
    set g : ℝ → G := (A n).indicator (fun s => ‖Y s‖ ^ (r - 2) • Y s) with hg
    have hgm : StronglyMeasurable g :=
      ((hYn.pow_const (r - 2)).stronglyMeasurable.smul hYm).indicator (hAm n)
    have hgnorm : ∀ s, ‖g s‖ = (A n).indicator (fun s => ‖Y s‖ ^ (r - 1)) s := by
      intro s
      by_cases hs : s ∈ A n
      · rw [hg, indicator_of_mem hs, indicator_of_mem hs, norm_smul, Real.norm_eq_abs,
          abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _),
          rpow_sub_two_mul (norm_nonneg _) hr]
      · rw [hg, indicator_of_notMem hs, indicator_of_notMem hs, norm_zero]
    have hgb : ∀ s, ‖g s‖ ≤ (n : ℝ) ^ (r - 1) := by
      intro s
      rw [hgnorm]
      by_cases hs : s ∈ A n
      · rw [indicator_of_mem hs]
        exact Real.rpow_le_rpow (norm_nonneg _) hs (by linarith)
      · rw [indicator_of_notMem hs]
        exact Real.rpow_nonneg (Nat.cast_nonneg n) _
    have hgL2 : MemLp g 2 timeMeasure :=
      MemLp.of_bound hgm.aestronglyMeasurable _ (ae_of_all _ hgb)
    set Nn : ℝ := ∫ s, (A n).indicator (fun s => ‖Y s‖ ^ r) s ∂timeMeasure with hNn
    have hNint : Integrable (fun s => (A n).indicator (fun s => ‖Y s‖ ^ r) s) timeMeasure := by
      refine Integrable.of_bound
        ((hYn.pow_const r).indicator (hAm n)).aestronglyMeasurable
        ((n : ℝ) ^ r) (ae_of_all _ fun s => ?_)
      by_cases hs : s ∈ A n
      · rw [indicator_of_mem hs, Real.norm_eq_abs,
          abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
        exact Real.rpow_le_rpow (norm_nonneg _) hs hr0.le
      · rw [indicator_of_notMem hs, norm_zero]
        exact Real.rpow_nonneg (Nat.cast_nonneg n) _
    have hN0 : 0 ≤ Nn := integral_nonneg fun s => indicator_nonneg
      (fun s _ => Real.rpow_nonneg (norm_nonneg _) _) s
    have hlin : ∫⁻ s, (A n).indicator (fun s => ‖Y s‖ₑ ^ r) s ∂timeMeasure =
        ENNReal.ofReal Nn := by
      rw [hNn, ofReal_integral_eq_lintegral_ofReal hNint
        (ae_of_all _ fun s => indicator_nonneg (fun s _ => Real.rpow_nonneg (norm_nonneg _) _) s)]
      exact lintegral_congr fun s => hind n s
    -- `N_n = ⟪J g, J F⟫`
    have hinner : ∀ s, ⟪g s, Y s⟫ = (A n).indicator (fun s => ‖Y s‖ ^ r) s := by
      intro s
      by_cases hs : s ∈ A n
      · rw [hg, indicator_of_mem hs, indicator_of_mem hs, real_inner_smul_left,
          real_inner_self_eq_norm_sq, rpow_sub_two_mul_sq (norm_nonneg _) hr]
      · rw [hg, indicator_of_notMem hs, indicator_of_notMem hs, inner_zero_left]
    have hNJ : Nn = ⟪J p G (hgL2.toLp g), J p G F⟫ := by
      rw [(OccupationCompletion.positive_bochner_inclusion _).2.2.2 F,
        OccupationCompletion.kform_congr p.a hgL2.coeFn_toLp (Filter.EventuallyEq.refl _ _),
        kform_eq_integral_inner p.ha0.le p.ha1 hgL2 (Lp.memLp F)]
      exact integral_congr_ae (ae_of_all _ fun s => (hinner s).symm)
    -- the `L^{r'}` norm of `g`
    have he : (eLpNorm g (ENNReal.ofReal r') timeMeasure).toReal = Nn ^ (1 / r') := by
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simpa using hr'0) ENNReal.ofReal_ne_top
        hgm.aestronglyMeasurable, ENNReal.toReal_ofReal hr'0.le]
      have hpt : ∀ s, ‖g s‖ₑ ^ r' = (A n).indicator (fun s => ‖Y s‖ₑ ^ r) s := by
        intro s
        rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hr'0.le, hind,
          hgnorm]
        congr 1
        by_cases hs : s ∈ A n
        · rw [indicator_of_mem hs, indicator_of_mem hs, ← Real.rpow_mul (norm_nonneg _), hr']
          congr 1
          field_simp
        · rw [indicator_of_notMem hs, indicator_of_notMem hs, Real.zero_rpow hr'0.ne']
      simp_rw [hpt]
      rw [hlin, ← ENNReal.toReal_rpow, ENNReal.toReal_ofReal hN0]
    have hle : Nn ≤ c * Nn ^ (1 / r') := by
      calc Nn = ⟪J p G (hgL2.toLp g), J p G F⟫ := hNJ
        _ ≤ ‖J p G (hgL2.toLp g)‖ * ‖J p G F‖ := real_inner_le_norm _ _
        _ ≤ B * Nn ^ (1 / r') * ‖J p G F‖ := by
            refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
            rw [← he]
            exact hB g hgm ⟨_, hgb⟩ hgL2
        _ = c * Nn ^ (1 / r') := by rw [hc]; ring
    have hNc : Nn ≤ c ^ r := by
      rcases hN0.eq_or_lt with h0 | hpos
      · rw [← h0]
        exact Real.rpow_nonneg hc0 _
      · have hsplit : Nn = Nn ^ (1 / r) * Nn ^ (1 / r') := by
          rw [← Real.rpow_add hpos, hconj, Real.rpow_one]
        have hq : 0 < Nn ^ (1 / r') := Real.rpow_pos_of_pos hpos _
        have h1 : Nn ^ (1 / r) ≤ c := by
          have h2 : Nn ^ (1 / r) * Nn ^ (1 / r') ≤ c * Nn ^ (1 / r') := hsplit ▸ hle
          exact le_of_mul_le_mul_right h2 hq
        calc Nn = (Nn ^ (1 / r)) ^ r := by
              rw [← Real.rpow_mul hN0, one_div_mul_cancel hr0.ne', Real.rpow_one]
          _ ≤ c ^ r := Real.rpow_le_rpow (Real.rpow_nonneg hN0 _) h1 hr0.le
    rw [hlin]
    exact ENNReal.ofReal_le_ofReal hNc
  -- monotone convergence
  have hmono : Monotone fun (n : ℕ) (s : ℝ) => (A n).indicator (fun s => ‖Y s‖ₑ ^ r) s := by
    intro n m hnm s
    refine indicator_le_indicator_of_subset (fun s hs => ?_) (fun _ => zero_le) s
    exact le_trans (show ‖Y s‖ ≤ (n : ℝ) from hs) (by exact_mod_cast hnm)
  have hmeas : ∀ n : ℕ, Measurable fun s => (A n).indicator (fun s => ‖Y s‖ₑ ^ r) s :=
    fun n => (hYe.pow_const r).indicator (hAm n)
  have hsup : ∀ s, ‖Y s‖ₑ ^ r = ⨆ n : ℕ, (A n).indicator (fun s => ‖Y s‖ₑ ^ r) s := by
    intro s
    refine le_antisymm ?_ (iSup_le fun n => indicator_le_self _ _ s)
    obtain ⟨n, hn⟩ := exists_nat_ge ‖Y s‖
    exact le_iSup_of_le n (by rw [indicator_of_mem (show s ∈ A n from hn)])
  rw [lintegral_congr hsup, lintegral_iSup hmeas hmono]
  exact iSup_le key

/-- **The `L^r` bound of the completed temporal mean**, `eLpNorm` form: under the dual bound,
`‖∫_I |·-t|^{-a} F(t) dt‖_{L^r(I;G)} ≤ B ‖J F‖`. -/
theorem eLpNorm_kBochner_le {p : TParams} {r B : ℝ} (hr : 2 < r) (hB0 : 0 ≤ B)
    (hB : DualBound p G r B) (F : Lp G 2 timeMeasure) :
    eLpNorm (kBochner p.a ⇑F) (ENNReal.ofReal r) timeMeasure ≤
      ENNReal.ofReal (B * ‖J p G F‖) := by
  have hr0 : 0 < r := by linarith
  have hc0 : 0 ≤ B * ‖J p G F‖ := mul_nonneg hB0 (norm_nonneg _)
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simpa using hr0) ENNReal.ofReal_ne_top
    (stronglyMeasurable_kBochner' p.a (Lp.stronglyMeasurable F)).aestronglyMeasurable,
    ENNReal.toReal_ofReal hr0.le]
  calc (∫⁻ s, ‖kBochner p.a (⇑F) s‖ₑ ^ r ∂timeMeasure) ^ (1 / r)
      ≤ (ENNReal.ofReal ((B * ‖J p G F‖) ^ r)) ^ (1 / r) :=
        ENNReal.rpow_le_rpow (lintegral_rpow_kBochner_le hr hB0 hB F) (by positivity)
    _ = ENNReal.ofReal (B * ‖J p G F‖) := by
        rw [ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg hc0 _) (by positivity),
          ← Real.rpow_mul hc0, mul_one_div_cancel hr0.ne', Real.rpow_one]

/-- Auxiliary: `2 < r`, `r ≠ ∞` give `2 < r.toReal`. -/
theorem two_lt_toReal {r : ℝ≥0∞} (hr2 : 2 < r) (hrt : r ≠ ⊤) : 2 < r.toReal := by
  have h := (ENNReal.toReal_lt_toReal (by simp) hrt).2 hr2
  simpa using h

/-- Auxiliary: under the dual bound, the Bochner field of `F ∈ L²(I; G)` lies in `L^r(I; G)`. -/
theorem memLp_kBochner_of_dual {p : TParams} {r : ℝ≥0∞} (hr2 : 2 < r) (hrt : r ≠ ⊤) {B : ℝ}
    (hB0 : 0 ≤ B) (hB : DualBound p G r.toReal B) (F : Lp G 2 timeMeasure) :
    MemLp (kBochner p.a ⇑F) r timeMeasure := by
  have h := eLpNorm_kBochner_le (two_lt_toReal hr2 hrt) hB0 hB F
  rw [ENNReal.ofReal_toReal hrt] at h
  exact h.trans_lt ENNReal.ofReal_lt_top

end Estimate

/-! ### The map `U` -/

section Map

variable {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G] [CompleteSpace G]
variable {p : TParams} {r : ℝ≥0∞} [Fact (1 ≤ r)] {B : ℝ}

/-- Auxiliary: the linear map `F ↦ [s ↦ ∫_I |s-t|^{-a} F(t) dt]`, `L²(I; G) → L^r(I; G)`. -/
def Vlin (hr2 : 2 < r) (hrt : r ≠ ⊤) (hB0 : 0 ≤ B) (hB : DualBound p G r.toReal B) :
    Lp G 2 timeMeasure →ₗ[ℝ] Lp G r timeMeasure where
  toFun F := (memLp_kBochner_of_dual hr2 hrt hB0 hB F).toLp _
  map_add' F F' := by
    rw [← MemLp.toLp_add]
    exact MemLp.toLp_congr _ _ (kBochner_add_ae p.ha0.le p.ha1 F F')
  map_smul' c F := by
    rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
    exact MemLp.toLp_congr _ _ (kBochner_smul_ae p.a c F)

omit [Fact (1 ≤ r)] in
/-- Auxiliary: the class of `Vlin F` is the Bochner field. -/
theorem coeFn_Vlin (hr2 : 2 < r) (hrt : r ≠ ⊤) (hB0 : 0 ≤ B) (hB : DualBound p G r.toReal B)
    (F : Lp G 2 timeMeasure) :
    (Vlin hr2 hrt hB0 hB F : ℝ → G) =ᵐ[timeMeasure] kBochner p.a ⇑F :=
  (memLp_kBochner_of_dual hr2 hrt hB0 hB F).coeFn_toLp

omit [Fact (1 ≤ r)] in
/-- Auxiliary: `‖V F‖_{L^r} ≤ B ‖J F‖`. -/
theorem norm_Vlin_le (hr2 : 2 < r) (hrt : r ≠ ⊤) (hB0 : 0 ≤ B) (hB : DualBound p G r.toReal B)
    (F : Lp G 2 timeMeasure) : ‖Vlin hr2 hrt hB0 hB F‖ ≤ B * ‖Jlin p G F‖ := by
  show ‖(memLp_kBochner_of_dual hr2 hrt hB0 hB F).toLp _‖ ≤ B * ‖Jlin p G F‖
  rw [Lp.norm_toLp]
  have h := eLpNorm_kBochner_le (two_lt_toReal hr2 hrt) hB0 hB F
  rw [ENNReal.ofReal_toReal hrt] at h
  calc (eLpNorm (kBochner p.a ⇑F) r timeMeasure).toReal
      ≤ (ENNReal.ofReal (B * ‖J p G F‖)).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top h
    _ = B * ‖Jlin p G F‖ := ENNReal.toReal_ofReal (mul_nonneg hB0 (norm_nonneg _))

/-- Auxiliary: `J_G` has dense range in `H_t ⊗ G`. -/
theorem denseRange_Jlin : DenseRange (Jlin p G) := by
  show DenseRange ((↑) : OccupationCompletion.KPre p G → HK p G)
  exact UniformSpace.Completion.denseRange_coe

/-- **The completed temporal mean `U = C_t ⊗ I_G : H_t ⊗ G → L^r(I; G)`**
(`integrated_uniform_mean.tex` lines 257-261, `𝒰` of `integrated_cameron_mean.tex` lines
324-330, at revision edf7085f (book 1.1.3)), as the bounded extension of
`J F ↦ [s ↦ ∫_I |s-t|^{-a} F(t) dt]` from the dense range of `J`, under a dual bound `B`
(kernel-positivity route, see the module docstring). -/
def Umap (hr2 : 2 < r) (hrt : r ≠ ⊤) (hB0 : 0 ≤ B) (hB : DualBound p G r.toReal B) :
    HK p G →L[ℝ] Lp G r timeMeasure :=
  (Vlin hr2 hrt hB0 hB).extendOfNorm (Jlin p G)

/-- Auxiliary: `U (J F) = [∫_I |·-t|^{-a} F(t) dt]`. -/
theorem Umap_J (hr2 : 2 < r) (hrt : r ≠ ⊤) (hB0 : 0 ≤ B) (hB : DualBound p G r.toReal B)
    (F : Lp G 2 timeMeasure) : Umap hr2 hrt hB0 hB (J p G F) = Vlin hr2 hrt hB0 hB F :=
  LinearMap.extendOfNorm_eq denseRange_Jlin ⟨B, norm_Vlin_le hr2 hrt hB0 hB⟩ F

/-- **`‖U‖ ≤ B`.** -/
theorem norm_Umap_le (hr2 : 2 < r) (hrt : r ≠ ⊤) (hB0 : 0 ≤ B) (hB : DualBound p G r.toReal B) :
    ‖Umap hr2 hrt hB0 hB‖ ≤ B :=
  LinearMap.opNorm_extendOfNorm_le denseRange_Jlin hB0 (norm_Vlin_le hr2 hrt hB0 hB)

/-- **`U` on single smooth tensors**: `U(f ⊗ q)(s) = (Kf)(s) q` (`UTensorSpec`). -/
theorem Umap_tensor {d : ℕ} {S : SpData d} (hr2 : 2 < r) (hrt : r ≠ ⊤) (hB0 : 0 ≤ B)
    (hB : DualBound p (Hsp S) r.toReal B) : UTensorSpec p S r (Umap hr2 hrt hB0 hB) := by
  intro f _ q hF
  rw [Umap_J]
  filter_upwards [coeFn_Vlin hr2 hrt hB0 hB (hF.toLp fun t => f t • q)] with s hs
  rw [hs, kBochner, kMean, ← integral_smul_const]
  refine integral_congr_ae ?_
  filter_upwards [hF.coeFn_toLp] with t ht
  rw [ht, smul_smul]

end Map

/-! ### The dual bounds -/

section Dual

/-- Auxiliary: `‖K_a‖_{r/2} ≥ 0`. -/
theorem KaNorm_nonneg (a r : ℝ) : 0 ≤ KaNorm a r :=
  Real.rpow_nonneg (setIntegral_nonneg measurableSet_Icc fun v _ =>
    Real.rpow_nonneg (abs_nonneg v) _) _

variable {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G] [CompleteSpace G]

omit [InnerProductSpace ℝ G] [CompleteSpace G] in
/-- Auxiliary: a bounded strongly measurable field has finite `L^q` norm on `I`. -/
theorem eLpNorm_ne_top_of_bdd {g : ℝ → G} (hgm : StronglyMeasurable g) {C : ℝ}
    (hC : ∀ t, ‖g t‖ ≤ C) (q : ℝ≥0∞) : eLpNorm g q timeMeasure ≠ ⊤ :=
  (MemLp.of_bound hgm.aestronglyMeasurable C (ae_of_all _ hC)).eLpNorm_ne_top

/-- **The dual bound from the absolute kernel estimate** (`integrated_cameron_mean.tex` lines
283-293 at revision edf7085f (book 1.1.3)): `KformAbsTarget` (C's `kform_abs`)
gives `‖J_G g‖² ≤ ∫∫ |s-t|^{-a} ‖g(s)‖ ‖g(t)‖ ≤ ‖K_a‖_{r/2} ‖g‖²_{r'}`, so `DualBound` holds
with `B = ‖K_a‖_{r/2}^{1/2}`; no temporal core and no compactness is used. -/
theorem dualBound_of_kformAbs {p : TParams} (hk : KformAbsTarget p) {r : ℝ} (hr2 : 2 < r)
    (hra : r < 2 / p.a) : DualBound p G r √(KaNorm p.a r) := by
  intro g hgm ⟨C, hC⟩ hg
  set r' := ENNReal.ofReal (r / (r - 1)) with hr'
  set e := eLpNorm g r' timeMeasure with he
  have hefin : e ≠ ⊤ := eLpNorm_ne_top_of_bdd hgm hC r'
  have hK0 := KaNorm_nonneg p.a r
  have hge : Measurable fun s => ‖g s‖ₑ := by
    simpa only [ofReal_norm] using hgm.norm.measurable.ennreal_ofReal
  -- the absolute bound
  have hmeas : AEMeasurable (fun z : ℝ × ℝ =>
      ENNReal.ofReal (kern p.a (z.1 - z.2)) * ‖g z.1‖ₑ * ‖g z.2‖ₑ)
      (timeMeasure.prod timeMeasure) :=
    ((((measurable_kern p.a).comp (measurable_fst.sub measurable_snd)).ennreal_ofReal.mul
      (hge.comp measurable_fst)).mul (hge.comp measurable_snd)).aemeasurable
  have habs := hk r hr2 hra (fun t => ‖g t‖) hgm.aestronglyMeasurable.norm
  simp only [enorm_norm] at habs
  rw [eLpNorm_norm g hgm.aestronglyMeasurable] at habs
  have hsq : ‖J p G (hg.toLp g)‖ ^ 2 ≤ KaNorm p.a r * e.toReal ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, (OccupationCompletion.positive_bochner_inclusion _).2.2.2,
      OccupationCompletion.kform_congr p.a hg.coeFn_toLp hg.coeFn_toLp]
    have h1 : kform p.a g g ≤ ‖kform p.a g g‖ := Real.le_norm_self _
    refine h1.trans ?_
    unfold kform
    refine (norm_integral_le_lintegral_norm _).trans ?_
    have h2 : ∫⁻ z, ENNReal.ofReal ‖kern p.a (z.1 - z.2) * ⟪g z.1, g z.2⟫‖
        ∂(timeMeasure.prod timeMeasure) ≤ ENNReal.ofReal (KaNorm p.a r) * e ^ 2 := by
      calc ∫⁻ z, ENNReal.ofReal ‖kern p.a (z.1 - z.2) * ⟪g z.1, g z.2⟫‖
            ∂(timeMeasure.prod timeMeasure)
          ≤ ∫⁻ z, ENNReal.ofReal (kern p.a (z.1 - z.2)) * ‖g z.1‖ₑ * ‖g z.2‖ₑ
            ∂(timeMeasure.prod timeMeasure) := by
            refine lintegral_mono fun z => ?_
            rw [← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul (kern_nonneg _ _),
              ← ENNReal.ofReal_mul (mul_nonneg (kern_nonneg _ _) (norm_nonneg _))]
            refine ENNReal.ofReal_le_ofReal ?_
            rw [norm_mul, Real.norm_of_nonneg (kern_nonneg _ _), mul_assoc]
            exact mul_le_mul_of_nonneg_left (norm_inner_le_norm _ _) (kern_nonneg _ _)
        _ = ∫⁻ s, ∫⁻ t, ENNReal.ofReal (kern p.a (s - t)) * ‖g s‖ₑ * ‖g t‖ₑ
            ∂timeMeasure ∂timeMeasure := lintegral_prod _ hmeas
        _ ≤ ENNReal.ofReal (KaNorm p.a r) * e ^ 2 := habs
    have hfin : ENNReal.ofReal (KaNorm p.a r) * e ^ 2 ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.pow_ne_top hefin)
    calc (∫⁻ z, ENNReal.ofReal ‖kern p.a (z.1 - z.2) * ⟪g z.1, g z.2⟫‖
          ∂(timeMeasure.prod timeMeasure)).toReal
        ≤ (ENNReal.ofReal (KaNorm p.a r) * e ^ 2).toReal := ENNReal.toReal_mono hfin h2
      _ = KaNorm p.a r * e.toReal ^ 2 := by
          rw [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal hK0]
  have he0 : 0 ≤ e.toReal := ENNReal.toReal_nonneg
  calc ‖J p G (hg.toLp g)‖ = √(‖J p G (hg.toLp g)‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ √(KaNorm p.a r * e.toReal ^ 2) := Real.sqrt_le_sqrt hsq
    _ = √(KaNorm p.a r) * e.toReal := by rw [Real.sqrt_mul hK0, Real.sqrt_sq he0]

/-- Auxiliary: the real Hölder inequality on `I` for the conjugate pair `(r', r)`,
`|∫ ⟪h, φ⟫| ≤ ‖h‖_{r'} ‖φ‖_r` (finite norms). -/
theorem abs_integral_inner_le {r : ℝ} (hr : 1 < r) {h φ : ℝ → ℝ}
    (hh : AEStronglyMeasurable h timeMeasure) (hφ : AEStronglyMeasurable φ timeMeasure)
    (hhf : eLpNorm h (ENNReal.ofReal (r / (r - 1))) timeMeasure ≠ ⊤)
    (hφf : eLpNorm φ (ENNReal.ofReal r) timeMeasure ≠ ⊤) :
    |∫ t, ⟪h t, φ t⟫ ∂timeMeasure| ≤
      (eLpNorm h (ENNReal.ofReal (r / (r - 1))) timeMeasure).toReal *
        (eLpNorm φ (ENNReal.ofReal r) timeMeasure).toReal := by
  have hconj : (r / (r - 1)).HolderConjugate r := (Real.HolderConjugate.conjExponent hr).symm
  have : ENNReal.HolderTriple (ENNReal.ofReal (r / (r - 1))) (ENNReal.ofReal r) 1 := by
    have := hconj.ennrealOfReal
    exact this
  have hH := eLpNorm_le_eLpNorm_mul_eLpNorm_of_norm (μ := timeMeasure)
    (p := ENNReal.ofReal (r / (r - 1))) (q := ENNReal.ofReal r) (r := 1)
    (fun x y : ℝ => ⟪x, y⟫) 1 (by fun_prop) hh hφ
    (ae_of_all _ fun t => by
      simp only [NNReal.coe_one, one_mul]
      exact norm_inner_le_norm _ _)
  rw [ENNReal.coe_one, one_mul] at hH
  have hfin : eLpNorm h (ENNReal.ofReal (r / (r - 1))) timeMeasure *
      eLpNorm φ (ENNReal.ofReal r) timeMeasure ≠ ⊤ := ENNReal.mul_ne_top hhf hφf
  rw [← Real.norm_eq_abs]
  refine (norm_integral_le_integral_norm _).trans ?_
  rw [integral_norm_eq_lintegral_enorm (hh.inner hφ), ← eLpNorm_one_eq_lintegral_enorm,
    ← ENNReal.toReal_mul]
  · exact ENNReal.toReal_mono hfin hH
  · exact hh.inner hφ

/-- **The scalar dual bound from a temporal core** (`integrated_cameron_mean.tex` lines 228-234
at revision edf7085f (book 1.1.3): `ι J h = K^{1/2} h`, `C_t = K^{1/2} ι`):
for `h ∈ L²(I)` with `‖h‖_{r'} < ∞`, `‖J h‖_{H_t} ≤ ‖C_t‖ ‖h‖_{r'}`.  Proof:
`‖J h‖² = ‖K^{1/2} h‖² = ⟪h, K^{1/2}(ι J h)⟫ = ∫ h · C_t(J h) ≤ ‖h‖_{r'} ‖C_t‖ ‖J h‖`. -/
theorem norm_J_real_le {p : TParams} {r : ℝ≥0∞} [Fact (1 ≤ r)] (T : TemporalMeanCore p r)
    (h : L2I) (hhf : eLpNorm h (ENNReal.ofReal (r.toReal / (r.toReal - 1))) timeMeasure ≠ ⊤) :
    ‖J p ℝ h‖ ≤ ‖T.Ct‖ *
      (eLpNorm h (ENNReal.ofReal (r.toReal / (r.toReal - 1))) timeMeasure).toReal := by
  have hrt : r ≠ ⊤ := (T.r_lt.trans ENNReal.ofReal_lt_top).ne
  have hr : 1 < r.toReal := by linarith [two_lt_toReal T.two_lt_r hrt]
  set e := (eLpNorm h (ENNReal.ofReal (r.toReal / (r.toReal - 1))) timeMeasure).toReal with he
  have hsym := T.S_sqrt.1.isSymmetric
  have hsq : ‖J p ℝ h‖ ^ 2 ≤ e * (‖T.Ct‖ * ‖J p ℝ h‖) := by
    have e1 : ‖J p ℝ h‖ ^ 2 = ⟪h, T.S (T.ι (J p ℝ h))⟫ := by
      rw [← real_inner_self_eq_norm_sq, ← T.ι.inner_map_map, T.ι_J]
      exact hsym h (T.S h)
    have e2 : ⟪h, T.S (T.ι (J p ℝ h))⟫ = ∫ t, ⟪h t, (T.Ct (J p ℝ h) : ℝ → ℝ) t⟫ ∂timeMeasure := by
      rw [MeasureTheory.L2.inner_def]
      refine integral_congr_ae ?_
      filter_upwards [T.Ct_L2 (J p ℝ h)] with t ht
      rw [ht]
    have hφf : eLpNorm (T.Ct (J p ℝ h) : ℝ → ℝ) (ENNReal.ofReal r.toReal) timeMeasure ≠ ⊤ := by
      rw [ENNReal.ofReal_toReal hrt]
      exact Lp.eLpNorm_ne_top _
    have hH := abs_integral_inner_le hr (Lp.aestronglyMeasurable h)
      (Lp.aestronglyMeasurable (T.Ct (J p ℝ h))) hhf hφf
    rw [ENNReal.ofReal_toReal hrt, ← Lp.norm_def] at hH
    rw [e1, e2]
    refine (le_abs_self _).trans (hH.trans ?_)
    exact mul_le_mul_of_nonneg_left (T.Ct.le_opNorm _) ENNReal.toReal_nonneg
  have he0 : 0 ≤ e := ENNReal.toReal_nonneg
  rcases (norm_nonneg (J p ℝ h)).eq_or_lt with h0 | hpos
  · rw [← h0]
    exact mul_nonneg T.Ct.opNorm_nonneg he0
  · have h2 : ‖J p ℝ h‖ * ‖J p ℝ h‖ ≤ (‖T.Ct‖ * e) * ‖J p ℝ h‖ := by
      nlinarith [hsq]
    exact le_of_mul_le_mul_right h2 hpos

/-- **The dual bound from a temporal core, by kernel positivity** (decision 4 of L16, the
"kernel-positivity route"; `integrated_uniform_mean.tex` lines 312-313 at revision edf7085f
(book 1.1.3) obtain `‖U‖ ≤ ‖C_t‖` from `L:uniform-mean-tensor` instead): since
`|s-t|^{-a} ≥ 0`, `‖J_G g‖² = ∫∫ K ⟪g(s), g(t)⟫ ≤ ∫∫ K ‖g(s)‖ ‖g(t)‖ = ‖J_ℝ ‖g‖‖²`, and the
scalar bound `norm_J_real_le` gives `DualBound` with `B = ‖C_t‖`. -/
theorem dualBound_of_core {p : TParams} {r : ℝ≥0∞} [Fact (1 ≤ r)] (T : TemporalMeanCore p r) :
    DualBound p G r.toReal ‖T.Ct‖ := by
  intro g hgm ⟨C, hC⟩ hg
  set r' := ENNReal.ofReal (r.toReal / (r.toReal - 1)) with hr'
  have hnL2 : MemLp (fun t => ‖g t‖) 2 timeMeasure := hg.norm
  set hn := hnL2.toLp (fun t => ‖g t‖) with hhn
  have hefin : eLpNorm g r' timeMeasure ≠ ⊤ := eLpNorm_ne_top_of_bdd hgm hC r'
  have hnf : eLpNorm (hn : ℝ → ℝ) r' timeMeasure = eLpNorm g r' timeMeasure := by
    rw [eLpNorm_congr_ae hnL2.coeFn_toLp, eLpNorm_norm g hgm.aestronglyMeasurable]
  have hscalar := norm_J_real_le T hn (by rw [hnf]; exact hefin)
  rw [hnf] at hscalar
  -- kernel positivity
  have hpos : ‖J p G (hg.toLp g)‖ ^ 2 ≤ ‖J p ℝ hn‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq,
      (OccupationCompletion.positive_bochner_inclusion _).2.2.2,
      (OccupationCompletion.positive_bochner_inclusion _).2.2.2,
      OccupationCompletion.kform_congr p.a hg.coeFn_toLp hg.coeFn_toLp,
      OccupationCompletion.kform_congr p.a hnL2.coeFn_toLp hnL2.coeFn_toLp]
    unfold kform
    refine integral_mono (OccupationCompletion.kform_integrable p.ha0.le p.ha1 hg hg)
      (OccupationCompletion.kform_integrable p.ha0.le p.ha1 hnL2 hnL2) fun z => ?_
    refine mul_le_mul_of_nonneg_left ?_ (kern_nonneg _ _)
    have hz : ⟪‖g z.1‖, ‖g z.2‖⟫ = ‖g z.1‖ * ‖g z.2‖ := by simp [mul_comm]
    rw [hz]
    exact real_inner_le_norm _ _
  calc ‖J p G (hg.toLp g)‖ ≤ ‖J p ℝ hn‖ :=
        (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 hpos
    _ ≤ _ := hscalar

end Dual

/-! ### The targets -/

section Targets

variable {d : ℕ}

/-- Auxiliary: a temporal core has `r ≠ ∞`. -/
theorem core_r_ne_top {p : TParams} {r : ℝ≥0∞} [Fact (1 ≤ r)]
    (T : TemporalMeanCore p r) : r ≠ ⊤ :=
  (T.r_lt.trans ENNReal.ofReal_lt_top).ne

/-- **D target 2: the completed temporal mean `U` with `‖U‖ ≤ ‖C_t‖`** (`UMapTarget`;
`P:cameron-full-mean` Step 1, `integrated_cameron_mean.tex` lines 352-369, and
`integrated_uniform_mean.tex` lines 257-270 and 312-313, at revision edf7085f (book
1.1.3)).  **Route: kernel positivity** (decision 4 of L16; the book's Gaussian route
through `L:uniform-mean-tensor` is not used here, because the Lean `H_I` is the kernel
completion of `L²(I; H_sp)` rather than a Hilbert tensor product): `U` is the bounded
extension of `J F ↦ ∫ K(·,t) F(t) dt` (`Umap`), and `‖U‖ ≤ ‖C_t‖` is `dualBound_of_core`.
The frozen hypotheses `YoungTarget` and `KformAbsTarget p` are not needed by this route. -/
theorem u_map (p : TParams) {d : ℕ} (S : SpData d) (r : ℝ≥0∞) [Fact (1 ≤ r)]
    (_hY : YoungTarget) (_hk : KformAbsTarget p) : UMapTarget p S r := by
  intro T
  exact ⟨Umap T.two_lt_r (core_r_ne_top T) T.Ct.opNorm_nonneg (dualBound_of_core T),
    Umap_tensor T.two_lt_r (core_r_ne_top T) T.Ct.opNorm_nonneg (dualBound_of_core T),
    norm_Umap_le T.two_lt_r (core_r_ne_top T) T.Ct.opNorm_nonneg (dualBound_of_core T)⟩

/-- **`U` with `UTensorSpec` and no temporal core** (D target 2, the core-free form used by
`positive_raw_embedding_constructed`; `integrated_cameron_mean.tex` lines 283-293 and
352-358 at revision edf7085f (book 1.1.3)): from `KformAbsTarget` alone, for
`2 < r < 2/a`, a bounded `U : H_I → L^r(I; H_sp)` with the defining formula on single smooth
tensors and `‖U‖ ≤ ‖K_a‖_{r/2}^{1/2}`.  No compactness (B1, C) is used. -/
theorem exists_uTensorSpec_of_kformAbs {p : TParams} (S : SpData d) {r : ℝ≥0∞} [Fact (1 ≤ r)]
    (hk : KformAbsTarget p) (hr2 : 2 < r) (hra : r < ENNReal.ofReal (2 / p.a)) :
    ∃ U : HI p S →L[ℝ] Lp (Hsp S) r timeMeasure,
      UTensorSpec p S r U ∧ ‖U‖ ≤ √(KaNorm p.a r.toReal) := by
  have hrt : r ≠ ⊤ := (hra.trans ENNReal.ofReal_lt_top).ne
  have hB := dualBound_of_kformAbs (G := Hsp S) hk (two_lt_toReal hr2 hrt)
    (ENNReal.toReal_lt_of_lt_ofReal hra)
  exact ⟨Umap hr2 hrt (Real.sqrt_nonneg _) hB, Umap_tensor hr2 hrt (Real.sqrt_nonneg _) hB,
    norm_Umap_le hr2 hrt (Real.sqrt_nonneg _) hB⟩

end Targets

end StratonovichHAMSecondMoment.CameronUMap
