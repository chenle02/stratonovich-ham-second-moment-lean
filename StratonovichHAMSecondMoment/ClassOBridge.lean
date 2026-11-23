module

/-
Copyright 2026 Le Chen. SPDX-License-Identifier: Apache-2.0

Wave L14, item O (part 2): the class `𝒪` of strongly `H¹`-measurable fields and its bridge to
joint representatives (debt D3), with the results that range over `𝒪` re-issued on the class
itself, and their zero-covariance cases.  Revision edf7085f:
* `notes/integrated_spatial_occupation.tex`: the class `𝒪` (lines 497-500), Proposition
  `P:occupation-physical-class` (statement 503-521, proof 523-575; the joint representatives are
  constructed in lines 534-540), the zero-covariance remark (577-582);
* `notes/integrated_occupation_ceiling.tex`: `E:raw-occupation-definitions` (lines 4-21),
  `P:raw-occupation-energy` (111-131, proof 133-177), `L:occupation-rayleigh-selection`
  (180-188, proof 190-236), `T:intrinsic-occupation-ceiling` (249-264, proof 266-316),
  `C:intrinsic-spatial-bracket` (319-333, proof 335-371), the direct zero case (379-385).

Objects.  `H¹ = ClassOH1.H1R d` (the graph of the weak gradient in `L² × L²`, with the topology
of Mathlib's `H^{1}`; part 1).  New: `IsClassO u` (the class `𝒪`: `u : ℝ → H¹` a.e.-strongly
measurable on `(0,1)`, `‖g_s‖₂ = 1` at a.e. time, `T(g) < ∞`), the spatial versions `gO u`,
`dgO u`, and the value sets and suprema over `𝒪`: `energySetO`/`EstarClassO` (`𝓔_⋆^𝒪`),
`ratioSetO`/`CoccO` (`C_occ`), `rawEnergySetO`/`EOO` (`𝓔_ζ^𝒪`).  Reused: `J`, `Jlin`, `T`,
`Tlin`, `sqPair` (`OccupationPhysicalClass`), `A`, `Araw` (`RawOccupationEnergy`), `Rsp`, `Esp`,
`F0` (`SpatialFourLinear`), `ceilingValue`, `Fb`, `Dzeta` (`SpatialBracket`).

The bridge (no supplied input):
* `exists_joint`: an a.e.-strongly measurable `F : ℝ → L²(ℝ^d;E)` on a finite time measure has a
  strongly measurable joint representative `G` with `G(s,·) = F(s)` a.e. at a.e. time (TeX lines
  534-540: simple approximations, then an a.e.-convergent subsequence of their joint versions);
  `exists_aesm_of_joint`: the converse (a joint representative with `L²` slices gives an
  a.e.-strongly measurable `L²`-valued field);
* `isOccField_of_classO`, `classO_of_isOccField`: `𝒪` corresponds to the earlier model
  `OccupationPhysicalClass.IsOccField` up to versions at a.e. time, in both directions;
  `values_eq`: every functional unchanged by such changes takes the same values on both, hence
  `energySetO_eq`, `ratioSetO_eq`, `rawEnergySetO_eq` and `EstarClassO_eq`, `CoccO_eq`, `EOO_eq`.

Formalized wrappers (standing assumptions `H:homog` as `HomogCovariance d α α₀ Γ μ` with
`a = α₀`, and `Γ ≠ 0` except in the zero case; nothing supplied):
* `occupation_physical_class_whole_paper`: every conclusion of `P:occupation-physical-class` on
  `𝒪` (also `D = q - 2a`);
* `raw_occupation_energy_whole_paper`: every conclusion of `P:raw-occupation-energy` on `𝒪`, the
  dilation `U_ℓ` stated up to versions (`∃ u' ∈ 𝒪` with `g'_s = U_ℓ g_s` a.e.);
* `occupation_rayleigh_selection_whole_paper`: `L:occupation-rayleigh-selection` with
  `g_ε ∈ 𝒪`;
* `intrinsic_occupation_ceiling_classO_paper`: `T:intrinsic-occupation-ceiling` for `S_c^pos`
  with `C_occ` and `𝓔_ζ^𝒪` over `𝒪` (narrower: the sentence `C_2(Γ,a) ≤ U_2`, line 261, needs
  `T:intrinsic-second-moment`, foundation D1);
* `intrinsic_spatial_comparison_classO_paper`: the comparison of `C:intrinsic-spatial-bracket`
  for `S_2^pos` with `𝓔_{1/2}^𝒪` over `𝒪` (narrower: `C_2` instead of `S_2^pos` needs D1; the
  bracket itself is `SpatialBracket.intrinsic_spatial_bracket_paper`);
* `zero_covariance_paper` (`Γ = 0`; TeX 577-582 and 379-385): all pairings vanish, `R_sp = 0`,
  `𝓔_sp = 0`, `J = A = 0` on `𝒪`, `𝓔_⋆^𝒪 = C_occ = 𝓔_ζ^𝒪 = 0` (nonempty value sets), `F_b(0) = 0`
  and the ceiling identities at zero; standalone forms `Rsp_zero`, `Esp_zero`,
  `EstarClassO_zero`, `CoccO_zero`, `EOO_zero`.  Not formalized: `C_2 = 0` and the vanishing of
  the variational values `S_c^pos` (line 379).

Modelling (recorded): "strongly `H¹`-measurable" is read as a.e.-strongly measurable (Bochner)
for Lebesgue measure on `(0,1)`, the reading of the TeX's own proof ("use a separably valued
strong representative", line 534); the dilation of `P:raw-occupation-energy` and the pairings
are stated on the spatial versions `gO u` (representatives of the `L²` classes), which the TeX's
representative independence makes harmless.

Implicit hypotheses made explicit: the time measure `volI` is finite (`isFiniteMeasure_volI`);
`T(g)` and the energies are extended integrals whose finiteness is a conclusion; every `sSup` is
used with nonemptiness and boundedness proved.  Hypotheses carried but unused: in
`zero_covariance_paper` only `α < 2` of `H:homog` is used.  Proof route: the wrappers transfer the
joint-representative results of `SpatialOccupationL7Completed`, `RawOccupationEnergy` and
`OccupationCeilingExact` through the bridge and representative independence
(`sqPair_Jlin_congr`, `Tlin_congr`, `Araw_congr`).  Differences from the TeX: measurability of
the pairings is by Tonelli on the joint representative (not by the continuity of the pairing
map); the field is first normalized to `F/max(1,‖F‖)` and its bounded simple approximations
are shown Cauchy in `L²((0,1) × ℝ^d)`, instead of the TeX's summable `L²(0,1;H¹)` errors.
Lemmas marked "Auxiliary to the Lean proof route" have no manuscript label.
-/
public import Mathlib
public import StratonovichHAMSecondMoment.ClassOH1
public import StratonovichHAMSecondMoment.OccupationCeilingExact

@[expose] public section

noncomputable section

set_option autoImplicit false

open MeasureTheory Set Real Filter Topology
open scoped ENNReal

namespace StratonovichHAMSecondMoment.ClassOBridge

open HomogHypothesis (Rd HomogCovariance)

variable {d : ℕ}

/-! ### `L²`-valued fields and joint representatives (generic) -/

section Generic

variable {E : Type*} [NormedAddCommGroup E]

/-- Auxiliary to the Lean proof route: `∫ ‖f‖^2 = eLpNorm(f)^2` for the exponent `2`, in
`[0,∞]` with real powers. -/
theorem lintegral_rpow_two_eq {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → E}
    (hf : AEStronglyMeasurable f μ) :
    ∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂μ = eLpNorm f 2 μ ^ (2 : ℝ) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top hf,
    ← ENNReal.rpow_mul]
  norm_num

/-- Auxiliary to the Lean proof route: membership in `L²` through the extended integral of
`‖f‖²`. -/
theorem memLp_two_iff {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → E}
    (hf : AEStronglyMeasurable f μ) :
    MemLp f 2 μ ↔ ∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂μ < ⊤ := by
  have h := eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (p := 2) two_ne_zero
    ENNReal.ofNat_ne_top hf
  simp only [ENNReal.toReal_ofNat] at h
  exact memLp_iff.trans h

/-- Auxiliary to the Lean proof route: a simple `L²`-valued function of time has a strongly
measurable joint representative `(s,x) ↦ (φ s)(x)` (finite sum of indicators of measurable
time sets times fixed representatives). -/
theorem stronglyMeasurable_simple_joint (φ : SimpleFunc ℝ (Lp E 2 (volume : Measure (Rd d)))) :
    StronglyMeasurable (fun p : ℝ × Rd d => (φ p.1 : Rd d → E) p.2) := by
  classical
  have e : (fun p : ℝ × Rd d => (φ p.1 : Rd d → E) p.2) =
      ∑ v ∈ φ.range, (Prod.fst ⁻¹' (φ ⁻¹' {v})).indicator
        (fun p : ℝ × Rd d => (v : Rd d → E) p.2) := by
    funext p
    rw [Finset.sum_apply, Finset.sum_eq_single (φ p.1)]
    · rw [Set.indicator_of_mem (by simp)]
    · intro v _ hv
      rw [Set.indicator_of_notMem]
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      exact fun h => hv h.symm
    · intro h
      exact absurd (φ.mem_range_self p.1) h
  rw [e]
  refine Finset.stronglyMeasurable_sum _ fun v _ => ?_
  exact ((Lp.stronglyMeasurable v).comp_measurable measurable_snd).indicator
    (measurable_fst (φ.measurableSet_fiber v))

/-- Auxiliary to the Lean proof route: the slice identity `∫ ‖(φ s)(x) - (ψ s)(x)‖² dx =
‖φ s - ψ s‖²_{L²}` for `L²` classes. -/
theorem lintegral_slice (u v : Lp E 2 (volume : Measure (Rd d))) :
    ∫⁻ x, ‖(u : Rd d → E) x - v x‖ₑ ^ (2 : ℝ) = ‖u - v‖ₑ ^ (2 : ℝ) := by
  rw [Lp.enorm_def, eLpNorm_congr_ae (Lp.coeFn_sub u v),
    ← lintegral_rpow_two_eq ((Lp.aestronglyMeasurable u).sub (Lp.aestronglyMeasurable v))]
  rfl

/-- Auxiliary to the Lean proof route: `L²` classes of norm at most `1` (the bounded case of
`exists_joint`). -/
theorem exists_joint_of_bounded [NormedSpace ℝ E] [CompleteSpace E] {ν : Measure ℝ}
    [IsFiniteMeasure ν]
    {F : ℝ → Lp E 2 (volume : Measure (Rd d))} (hF : StronglyMeasurable F)
    (hb : ∀ s, ‖F s‖ ≤ 1) :
    ∃ G : ℝ × Rd d → E, StronglyMeasurable G ∧
      ∀ᵐ s ∂ν, (fun x => G (s, x)) =ᵐ[volume] (F s : Rd d → E) := by
  set φ : ℕ → SimpleFunc ℝ (Lp E 2 (volume : Measure (Rd d))) :=
    fun n => hF.approxBounded 1 n with hφdef
  have hφb : ∀ n s, ‖φ n s‖ ≤ 1 := fun n s => hF.norm_approxBounded_le zero_le_one n s
  have hφt : ∀ s, Tendsto (fun n => φ n s) atTop (𝓝 (F s)) := fun s =>
    hF.tendsto_approxBounded_of_norm_le (hb s)
  set Gn : ℕ → ℝ × Rd d → E := fun n p => (φ n p.1 : Rd d → E) p.2 with hGndef
  have hGn : ∀ n, StronglyMeasurable (Gn n) := fun n => stronglyMeasurable_simple_joint (φ n)
  -- the joint norms are the time integrals of the `L²` norms
  have hjoint : ∀ n m, ∫⁻ p, ‖Gn n p - Gn m p‖ₑ ^ (2 : ℝ) ∂(ν.prod volume) =
      ∫⁻ s, ‖φ n s - φ m s‖ₑ ^ (2 : ℝ) ∂ν := by
    intro n m
    rw [lintegral_prod (fun p => ‖Gn n p - Gn m p‖ₑ ^ (2 : ℝ))
      ((((hGn n).sub (hGn m)).enorm).pow_const _).aemeasurable]
    exact lintegral_congr fun s => lintegral_slice (φ n s) (φ m s)
  have hjoint0 : ∀ n, ∫⁻ p, ‖Gn n p‖ₑ ^ (2 : ℝ) ∂(ν.prod volume) =
      ∫⁻ s, ‖φ n s‖ₑ ^ (2 : ℝ) ∂ν := by
    intro n
    rw [lintegral_prod (fun p => ‖Gn n p‖ₑ ^ (2 : ℝ)) (((hGn n).enorm).pow_const _).aemeasurable]
    refine lintegral_congr fun s => ?_
    have := lintegral_slice (φ n s) 0
    simp only [sub_zero] at this
    rw [← this]
    refine lintegral_congr_ae ?_
    filter_upwards [Lp.coeFn_zero E 2 (volume : Measure (Rd d))] with x hx
    rw [hx, Pi.zero_apply, sub_zero]
  have hmeas : ∀ n m, Measurable fun s => ‖φ n s - φ m s‖ₑ ^ (2 : ℝ) := by
    intro n m
    have : (fun s => ‖φ n s - φ m s‖ₑ ^ (2 : ℝ)) =
        ((φ n - φ m).map fun v => ‖v‖ₑ ^ (2 : ℝ) : SimpleFunc ℝ ℝ≥0∞) := by
      funext s; simp [SimpleFunc.map_apply, SimpleFunc.coe_sub]
    rw [this]
    exact SimpleFunc.measurable _
  have hle1 : ∀ v : Lp E 2 (volume : Measure (Rd d)), ‖v‖ ≤ 2 → ‖v‖ₑ ^ (2 : ℝ) ≤ 4 := by
    intro v hv
    rw [← ofReal_norm]
    calc ENNReal.ofReal ‖v‖ ^ (2 : ℝ) ≤ ENNReal.ofReal 2 ^ (2 : ℝ) :=
          ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal hv) (by norm_num)
      _ = 4 := by
          rw [ENNReal.ofReal_ofNat, ENNReal.rpow_two]; norm_num
  have hmem : ∀ n, MemLp (Gn n) 2 (ν.prod volume) := by
    intro n
    refine (memLp_two_iff (hGn n).aestronglyMeasurable).2 ?_
    rw [hjoint0 n]
    calc ∫⁻ s, ‖φ n s‖ₑ ^ (2 : ℝ) ∂ν ≤ ∫⁻ _, 4 ∂ν :=
          lintegral_mono fun s => hle1 _ ((hφb n s).trans (by norm_num))
      _ < ⊤ := by rw [lintegral_const]; exact ENNReal.mul_lt_top (by norm_num) (measure_lt_top _ _)
  set gp : ℕ → Lp E 2 (ν.prod volume) := fun n => (hmem n).toLp _ with hgpdef
  -- the sequence is Cauchy in `L²((0,1) × ℝ^d)`
  have hD : Tendsto (fun nm : ℕ × ℕ => ∫⁻ s, ‖φ nm.1 s - φ nm.2 s‖ₑ ^ (2 : ℝ) ∂ν) atTop
      (𝓝 0) := by
    have h0 : (0 : ℝ≥0∞) = ∫⁻ _ : ℝ, 0 ∂ν := by simp
    rw [h0]
    refine tendsto_lintegral_filter_of_dominated_convergence (fun _ => 4)
      (Eventually.of_forall fun nm => hmeas nm.1 nm.2)
      (Eventually.of_forall fun nm => Eventually.of_forall fun s =>
        hle1 _ ((norm_sub_le _ _).trans (by linarith [hφb nm.1 s, hφb nm.2 s])))
      (by rw [lintegral_const]; exact ENNReal.mul_ne_top (by norm_num) (measure_ne_top _ _))
      (Eventually.of_forall fun s => ?_)
    have h1 : Tendsto (fun nm : ℕ × ℕ => φ nm.1 s - φ nm.2 s) atTop (𝓝 (F s - F s)) := by
      rw [← prod_atTop_atTop_eq]
      exact ((hφt s).comp tendsto_fst).sub ((hφt s).comp tendsto_snd)
    rw [sub_self] at h1
    have h2 := (ENNReal.continuous_rpow_const (y := (2 : ℝ))).tendsto _ |>.comp
      ((continuous_enorm.tendsto _).comp h1)
    simpa [Function.comp_def] using h2
  have hc : CauchySeq gp := by
    refine cauchySeq_iff_tendsto_dist_atTop_0.2 ?_
    have e : ∀ nm : ℕ × ℕ, dist (gp nm.1) (gp nm.2) =
        ((∫⁻ s, ‖φ nm.1 s - φ nm.2 s‖ₑ ^ (2 : ℝ) ∂ν) ^ (1 / 2 : ℝ)).toReal := by
      intro nm
      rw [Lp.dist_def, eLpNorm_congr_ae ((hmem nm.1).coeFn_toLp.sub (hmem nm.2).coeFn_toLp),
        eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top
          (((hGn _).sub (hGn _)).aestronglyMeasurable), ← hjoint]
      norm_num
    simp_rw [e]
    have h3 := ((ENNReal.continuous_rpow_const (y := (1 / 2 : ℝ))).tendsto _).comp hD
    rw [ENNReal.zero_rpow_of_pos (by norm_num)] at h3
    have h4 := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h3
    simpa [Function.comp_def] using h4
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hc
  have hLe := (Lp.tendsto_Lp_iff_tendsto_eLpNorm' gp L).1 hL
  obtain ⟨ns, hns_mono, hns⟩ :=
    (tendstoInMeasure_of_tendsto_eLpNorm two_ne_zero hLe).exists_seq_tendsto_ae
  have hrep : ∀ᵐ p ∂(ν.prod volume), ∀ n, (gp n : ℝ × Rd d → E) p = Gn n p :=
    ae_all_iff.2 fun n => (hmem n).coeFn_toLp
  have hlim : ∀ᵐ p ∂(ν.prod volume),
      Tendsto (fun i => Gn (ns i) p) atTop (𝓝 ((L : ℝ × Rd d → E) p)) := by
    filter_upwards [hns, hrep] with p hp hr
    simpa only [hr] using hp
  refine ⟨L, Lp.stronglyMeasurable L, ?_⟩
  filter_upwards [Measure.ae_ae_of_ae_prod hlim] with s hs
  have hts : Tendsto (fun i => φ (ns i) s) atTop (𝓝 (F s)) :=
    (hφt s).comp hns_mono.tendsto_atTop
  obtain ⟨ms, hms_mono, hms⟩ := (tendstoInMeasure_of_tendsto_eLpNorm two_ne_zero
    ((Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ _).1 hts)).exists_seq_tendsto_ae
  filter_upwards [hs, hms] with x hx1 hx2
  exact tendsto_nhds_unique (hx1.comp hms_mono.tendsto_atTop) hx2

/-- **From a strongly measurable `L²`-valued field to a joint representative** (the
construction of TeX lines 534-540 of `integrated_spatial_occupation.tex`, "approximate this
Bochner `L²` field by simple functions ... a subsequence has a measurable spacetime limit"):
for a finite measure `ν` on time and an a.e.-strongly measurable `F : ℝ → L²(ℝ^d;E)`, there is a
strongly measurable `G : ℝ × ℝ^d → E` with `G(s,·) = F(s)` a.e., for `ν`-a.e. `s`.
Route: normalization `F/max(1,‖F‖)`, bounded simple approximations, completeness of
`L²(ν ⊗ dx)` and an a.e.-convergent subsequence (no square integrability in time is needed). -/
theorem exists_joint [NormedSpace ℝ E] [CompleteSpace E] {ν : Measure ℝ} [IsFiniteMeasure ν]
    {F : ℝ → Lp E 2 (volume : Measure (Rd d))} (hF : AEStronglyMeasurable F ν) :
    ∃ G : ℝ × Rd d → E, StronglyMeasurable G ∧
      ∀ᵐ s ∂ν, (fun x => G (s, x)) =ᵐ[volume] (F s : Rd d → E) := by
  set F' := hF.mk F with hF'def
  have hF' : StronglyMeasurable F' := hF.stronglyMeasurable_mk
  set c : ℝ → ℝ := fun s => max 1 ‖F' s‖ with hcdef
  have hc : Measurable c := measurable_const.max hF'.norm.measurable
  have hcpos : ∀ s, 0 < c s := fun s => lt_of_lt_of_le one_pos (le_max_left _ _)
  set F₁ : ℝ → Lp E 2 (volume : Measure (Rd d)) := fun s => (c s)⁻¹ • F' s with hF₁def
  have hF₁ : StronglyMeasurable F₁ := hc.inv.stronglyMeasurable.smul hF'
  have hb : ∀ s, ‖F₁ s‖ ≤ 1 := by
    intro s
    rw [hF₁def, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 (hcpos s)),
      inv_mul_le_iff₀ (hcpos s), mul_one]
    exact le_max_right _ _
  obtain ⟨G₁, hG₁, hG₁F⟩ := exists_joint_of_bounded (ν := ν) hF₁ hb
  refine ⟨fun p => c p.1 • G₁ p, (hc.comp measurable_fst).stronglyMeasurable.smul hG₁, ?_⟩
  filter_upwards [hG₁F, hF.ae_eq_mk] with s hs hs'
  rw [hs']
  filter_upwards [hs, Lp.coeFn_smul (c s)⁻¹ (F' s)] with x hx hx'
  rw [hx, hx', Pi.smul_apply, smul_smul, mul_inv_cancel₀ (hcpos s).ne', one_smul]

/-- **From a joint representative to a strongly measurable `L²`-valued field** (the converse
direction, used to show that the class of joint representatives is exactly the TeX's class):
for an s-finite `ν` and an a.e.-strongly measurable `G : ℝ × ℝ^d → E` on `ν ⊗ dx` whose slices
are in `L²` at `ν`-a.e. time, the field of `L²` classes `s ↦ [G(s,·)]` has an a.e.-strongly
measurable version. Route: `L²(ℝ^d;E)` is second countable and the distances to its points are
measurable in `s` by Tonelli (`OccupationCompletion.measurable_of_dist_dense`). -/
theorem exists_aesm_of_joint [SecondCountableTopology E] {ν : Measure ℝ} [SFinite ν]
    {G : ℝ × Rd d → E}
    (hG : AEStronglyMeasurable G (ν.prod volume))
    (hL : ∀ᵐ s ∂ν, MemLp (fun x => G (s, x)) 2 volume) :
    ∃ F : ℝ → Lp E 2 (volume : Measure (Rd d)), AEStronglyMeasurable F ν ∧
      ∀ᵐ s ∂ν, (F s : Rd d → E) =ᵐ[volume] fun x => G (s, x) := by
  classical
  set Gm := hG.mk G with hGmdef
  have hGm : StronglyMeasurable Gm := hG.stronglyMeasurable_mk
  have hae : ∀ᵐ s ∂ν, ∀ᵐ x ∂(volume : Measure (Rd d)), G (s, x) = Gm (s, x) :=
    Measure.ae_ae_of_ae_prod hG.ae_eq_mk
  have hsl : ∀ s, AEStronglyMeasurable (fun x => Gm (s, x)) (volume : Measure (Rd d)) :=
    fun s => (hGm.comp_measurable measurable_prodMk_left).aestronglyMeasurable
  set F : ℝ → Lp E 2 (volume : Measure (Rd d)) := fun s =>
    if h : MemLp (fun x => Gm (s, x)) 2 volume then h.toLp _ else 0 with hFdef
  let _ : MeasurableSpace (Lp E 2 (volume : Measure (Rd d))) := borel _
  have _ : BorelSpace (Lp E 2 (volume : Measure (Rd d))) := ⟨rfl⟩
  have _ : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨ENNReal.ofNat_ne_top⟩
  set I : ℝ → ℝ≥0∞ := fun s => ∫⁻ x, ‖Gm (s, x)‖ₑ ^ (2 : ℝ) with hIdef
  have hI : Measurable I := ((hGm.enorm).pow_const _).lintegral_prod_right'
  have hmeas : Measurable F := by
    refine OccupationCompletion.measurable_of_dist_dense dense_univ fun v _ => ?_
    set Iv : ℝ → ℝ≥0∞ := fun s => ∫⁻ x, ‖Gm (s, x) - v x‖ₑ ^ (2 : ℝ) with hIvdef
    have hIv : Measurable Iv :=
      (((hGm.sub ((Lp.stronglyMeasurable v).comp_measurable measurable_snd)).enorm
        ).pow_const _).lintegral_prod_right'
    have e : (fun s => dist (F s) v) =
        fun s => if I s < ⊤ then (Iv s ^ (1 / 2 : ℝ)).toReal else ‖v‖ := by
      funext s
      by_cases h : MemLp (fun x => Gm (s, x)) 2 volume
      · have hIs : I s < ⊤ := (memLp_two_iff (hsl s)).1 h
        simp only [hFdef, h, hIs, ↓reduceDIte, ↓reduceIte]
        rw [Lp.dist_def, eLpNorm_congr_ae (h.coeFn_toLp.sub (ae_eq_refl _)),
          eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top
            ((hsl s).sub (Lp.aestronglyMeasurable v))]
        simp only [ENNReal.toReal_ofNat]
        rfl
      · have hIs : ¬ I s < ⊤ := fun h' => h ((memLp_two_iff (hsl s)).2 h')
        simp only [hFdef, h, hIs, ↓reduceDIte, ↓reduceIte, dist_zero_left]
    rw [e]
    exact Measurable.ite (measurableSet_lt hI measurable_const)
      ((hIv.pow_const _).ennreal_toReal) measurable_const
  refine ⟨F, hmeas.aestronglyMeasurable, ?_⟩
  filter_upwards [hae, hL] with s hs hLs
  have hm : MemLp (fun x => Gm (s, x)) 2 volume := hLs.ae_eq hs
  have hF : F s = hm.toLp _ := by simp only [hFdef, hm, ↓reduceDIte]
  rw [hF]
  filter_upwards [hm.coeFn_toLp, hs] with x hx hx'
  rw [hx, hx']

end Generic

/-! ### The class `𝒪` of strongly `H¹`-measurable fields -/

open ClassOH1 (H1R fn grd L2R L2V isH1Pair hasWeakGradient_congr_ae)
open OccupationPhysicalClass (volI sqPair Tlin T Jlin J IsOccField sqPair_congr sqPair_Jlin_congr
  Tlin_congr)
open SpatialStaticControls (IsUnitH1)
open OccupationKernelRow (Kstar Rstar)
open WeakSobolev (HasWeakGradient)

/-- The spatial versions `s ↦ g_s` of a field `u : (0,1) → H¹` (representatives of the `L²`
classes). -/
def gO (u : ℝ → H1R d) : ℝ → Rd d → ℝ := fun s => fn (u s)

/-- The gradient versions `s ↦ ∇g_s` of a field `u : (0,1) → H¹`. -/
def dgO (u : ℝ → H1R d) : ℝ → Rd d → Rd d := fun s => grd (u s)

/-- **The class `𝒪`** (`integrated_spatial_occupation.tex` lines 497-500): fields
`s ↦ g_s ∈ H¹(ℝ^d;ℝ)` on `(0,1)` that are strongly measurable (a.e.-strongly measurable for
Lebesgue measure on `(0,1)`, for the topology of `H¹ = ClassOH1.H1R d`, which is Mathlib's
`H^{1}` topology by `ClassOH1.isEmbedding_toMH1`), with `‖g_s‖₂ = 1` at a.e. time and
`T(g) = ∫_0^1 b(g_s) ds < ∞`. -/
structure IsClassO (u : ℝ → H1R d) : Prop where
  meas : AEStronglyMeasurable u volI
  unit : ∀ᵐ s ∂volI, ∫ x, gO u s x ^ 2 = 1
  energy_lt_top : Tlin (dgO u) < ⊤

/-- Auxiliary to the Lean proof route: Lebesgue measure on `(0,1)` is finite. -/
theorem isFiniteMeasure_volI : IsFiniteMeasure volI :=
  ⟨by simp⟩

/-- Auxiliary to the Lean proof route: the zero element of `H¹`. -/
def zeroH1 : H1R d :=
  ⟨(0, 0), hasWeakGradient_congr_ae (f := fun _ => 0) (g := fun _ => 0)
    (fun φ _ v => by simp) (Lp.coeFn_zero ℝ 2 volume).symm (Lp.coeFn_zero (Rd d) 2 volume).symm⟩

/-- **From the class `𝒪` to joint representatives** (TeX lines 534-540): a field of `𝒪` has
a.e.-strongly measurable joint representatives `(s,x) ↦ g_s(x)`, `(s,x) ↦ ∇g_s(x)` forming a
field of `OccupationPhysicalClass.IsOccField`, equal to the spatial versions of the field at a.e.
time. -/
theorem isOccField_of_classO {u : ℝ → H1R d} (hu : IsClassO u) :
    ∃ (G : ℝ → Rd d → ℝ) (DG : ℝ → Rd d → Rd d), IsOccField G DG ∧
      ∀ᵐ s ∂volI, G s =ᵐ[volume] gO u s ∧ DG s =ᵐ[volume] dgO u s := by
  have := isFiniteMeasure_volI
  have h1 : AEStronglyMeasurable (fun s => (u s : L2R d × L2V d).1) volI :=
    (continuous_fst.comp continuous_subtype_val).comp_aestronglyMeasurable hu.meas
  have h2 : AEStronglyMeasurable (fun s => (u s : L2R d × L2V d).2) volI :=
    (continuous_snd.comp continuous_subtype_val).comp_aestronglyMeasurable hu.meas
  obtain ⟨G₀, hG₀, hG₀e⟩ := exists_joint h1
  obtain ⟨D₀, hD₀, hD₀e⟩ := exists_joint h2
  have he : ∀ᵐ s ∂volI, (fun x => G₀ (s, x)) =ᵐ[volume] gO u s ∧
      (fun x => D₀ (s, x)) =ᵐ[volume] dgO u s := hG₀e.and hD₀e
  refine ⟨fun s x => G₀ (s, x), fun s x => D₀ (s, x),
    ⟨hG₀.aestronglyMeasurable, hD₀.aestronglyMeasurable, ?_, ?_⟩, he⟩
  · filter_upwards [he, hu.unit] with s hs hu1
    have hp := isH1Pair (u s)
    refine ⟨hp.1.ae_eq hs.1.symm, hp.2.1.ae_eq hs.2.symm,
      hasWeakGradient_congr_ae hp.2.2 hs.1.symm hs.2.symm, ?_⟩
    rw [← hu1]
    exact integral_congr_ae (hs.1.mono fun x hx => by simp only [hx])
  · rw [Tlin_congr (he.mono fun s hs => hs.2)]
    exact hu.energy_lt_top

/-- **From joint representatives to the class `𝒪`** (the converse): every field of
`OccupationPhysicalClass.IsOccField` is, at a.e. time, a.e. equal to the spatial versions of a
field of `𝒪`. -/
theorem classO_of_isOccField {G : ℝ → Rd d → ℝ} {DG : ℝ → Rd d → Rd d}
    (hO : IsOccField G DG) :
    ∃ u : ℝ → H1R d, IsClassO u ∧
      ∀ᵐ s ∂volI, G s =ᵐ[volume] gO u s ∧ DG s =ᵐ[volume] dgO u s := by
  classical
  obtain ⟨F₁, hF₁, hF₁e⟩ := exists_aesm_of_joint (G := fun p : ℝ × Rd d => G p.1 p.2) hO.meas
    (hO.unit.mono fun s hs => hs.1)
  obtain ⟨F₂, hF₂, hF₂e⟩ := exists_aesm_of_joint (G := fun p : ℝ × Rd d => DG p.1 p.2)
    hO.meas_grad (hO.unit.mono fun s hs => hs.2.1)
  set u : ℝ → H1R d := fun s =>
    if h : HasWeakGradient (F₁ s : Rd d → ℝ) (F₂ s : Rd d → Rd d) then ⟨(F₁ s, F₂ s), h⟩
    else zeroH1 with hudef
  have hval : ∀ᵐ s ∂volI, (u s : L2R d × L2V d) = (F₁ s, F₂ s) ∧
      (F₁ s : Rd d → ℝ) =ᵐ[volume] G s ∧ (F₂ s : Rd d → Rd d) =ᵐ[volume] DG s := by
    filter_upwards [hO.unit, hF₁e, hF₂e] with s hs h1 h2
    have hw : HasWeakGradient (F₁ s : Rd d → ℝ) (F₂ s : Rd d → Rd d) :=
      hasWeakGradient_congr_ae hs.2.2.1 h1.symm h2.symm
    exact ⟨by simp only [hudef, hw, ↓reduceDIte], h1, h2⟩
  have hmeas : AEStronglyMeasurable u volI := by
    refine (IsEmbedding.subtypeVal.aestronglyMeasurable_comp_iff).1 ?_
    exact (hF₁.prodMk hF₂).congr (hval.mono fun s hs => hs.1.symm)
  have he : ∀ᵐ s ∂volI, G s =ᵐ[volume] gO u s ∧ DG s =ᵐ[volume] dgO u s := by
    filter_upwards [hval] with s hs
    have e1 : gO u s = (F₁ s : Rd d → ℝ) := by
      simp only [gO, fn]; rw [hs.1]
    have e2 : dgO u s = (F₂ s : Rd d → Rd d) := by
      simp only [dgO, grd]; rw [hs.1]
    rw [e1, e2]
    exact ⟨hs.2.1.symm, hs.2.2.symm⟩
  refine ⟨u, ⟨hmeas, ?_, ?_⟩, he⟩
  · filter_upwards [he, hO.unit] with s hs hu1
    rw [← hu1.2.2.2]
    exact integral_congr_ae (hs.1.mono fun x hx => by simp only [hx])
  · rw [← Tlin_congr (he.mono fun s hs => hs.2)]
    exact hO.energy_lt_top

/-- **Value sets over `𝒪` and over joint representatives coincide**: for any functional of
(field, gradient field) that is unchanged by a.e. changes at a.e. time, its values over the
class `𝒪` are exactly its values over `OccupationPhysicalClass.IsOccField`. -/
theorem values_eq {Φ : (ℝ → Rd d → ℝ) → (ℝ → Rd d → Rd d) → ℝ}
    (hΦ : ∀ (G G' : ℝ → Rd d → ℝ) (DG DG' : ℝ → Rd d → Rd d),
      (∀ᵐ s ∂volI, G s =ᵐ[volume] G' s ∧ DG s =ᵐ[volume] DG' s) → Φ G DG = Φ G' DG') :
    {r | ∃ u : ℝ → H1R d, IsClassO u ∧ r = Φ (gO u) (dgO u)} =
      {r | ∃ (G : ℝ → Rd d → ℝ) (DG : ℝ → Rd d → Rd d), IsOccField G DG ∧ r = Φ G DG} := by
  ext r
  constructor
  · rintro ⟨u, hu, rfl⟩
    obtain ⟨G, DG, hO, he⟩ := isOccField_of_classO hu
    exact ⟨G, DG, hO, (hΦ _ _ _ _ he).symm⟩
  · rintro ⟨G, DG, hO, rfl⟩
    obtain ⟨u, hu, he⟩ := classO_of_isOccField hO
    exact ⟨u, hu, hΦ _ _ _ _ he⟩

/-- Auxiliary to the Lean proof route: `A(g)` (original kernel) is unchanged by a.e. changes at
a.e. time. -/
theorem Araw_congr (a : ℝ) (Γ : Measure (Rd d)) [IsLocallyFiniteMeasure Γ]
    {G G' : ℝ → Rd d → ℝ} (h : ∀ᵐ s ∂volI, G s =ᵐ[volume] G' s) :
    RawOccupationEnergy.Araw a Γ G = RawOccupationEnergy.Araw a Γ G' := by
  unfold RawOccupationEnergy.Araw
  refine lintegral_congr_ae ?_
  filter_upwards [h] with s hs
  refine lintegral_congr_ae ?_
  filter_upwards [h] with t ht
  rw [sqPair_congr Γ hs ht]

/-! ### The value sets and suprema over `𝒪` -/

/-- `{J(g) - T(g)/2 : g ∈ 𝒪}` (TeX line 518) over the class `𝒪` itself. -/
def energySetO (a D : ℝ) (Γ : Measure (Rd d)) : Set ℝ :=
  {v | ∃ u : ℝ → H1R d, IsClassO u ∧ v = J a D Γ (gO u) - T (dgO u) / 2}

/-- `𝓔_⋆^𝒪 = sup_{g ∈ 𝒪} (J(g) - T(g)/2)` (TeX lines 516-518) over the class `𝒪`. -/
def EstarClassO (a D : ℝ) (Γ : Measure (Rd d)) : ℝ := sSup (energySetO a D Γ)

/-- `{A(g)/T(g)^{α/2} : g ∈ 𝒪}` (`integrated_occupation_ceiling.tex` lines 13-14) over `𝒪`. -/
def ratioSetO (a alpha : ℝ) (Γ : Measure (Rd d)) : Set ℝ :=
  {r | ∃ u : ℝ → H1R d, IsClassO u ∧
    r = RawOccupationEnergy.A a Γ (gO u) / T (dgO u) ^ (alpha / 2)}

/-- `C_occ = sup_{g ∈ 𝒪} A(g)/T(g)^{α/2}` (lines 13-14) over the class `𝒪`. -/
def CoccO (a alpha : ℝ) (Γ : Measure (Rd d)) : ℝ := sSup (ratioSetO a alpha Γ)

/-- `{A(g) - ζ T(g) : g ∈ 𝒪}` (lines 15-16) over the class `𝒪`. -/
def rawEnergySetO (a : ℝ) (Γ : Measure (Rd d)) (ζ : ℝ) : Set ℝ :=
  {v | ∃ u : ℝ → H1R d, IsClassO u ∧ v = RawOccupationEnergy.A a Γ (gO u) - ζ * T (dgO u)}

/-- `𝓔_ζ^𝒪 = sup_{g ∈ 𝒪} {A(g) - ζ T(g)}` (lines 15-16) over the class `𝒪`. -/
def EOO (a : ℝ) (Γ : Measure (Rd d)) (ζ : ℝ) : ℝ := sSup (rawEnergySetO a Γ ζ)

/-- The energy set over `𝒪` is the energy set over joint representatives. -/
theorem energySetO_eq (a D : ℝ) (Γ : Measure (Rd d)) [IsLocallyFiniteMeasure Γ] :
    energySetO a D Γ = OccupationPhysicalClass.energySet a D Γ :=
  values_eq (Φ := fun G DG => J a D Γ G - T DG / 2) fun G G' DG DG' h => by
    simp only [J, T, (sqPair_Jlin_congr a D Γ (h.mono fun s hs => hs.1)).2,
      Tlin_congr (h.mono fun s hs => hs.2)]

/-- The ratio set over `𝒪` is the ratio set over joint representatives. -/
theorem ratioSetO_eq (a alpha : ℝ) (Γ : Measure (Rd d)) [IsLocallyFiniteMeasure Γ] :
    ratioSetO a alpha Γ = RawOccupationEnergy.ratioSet a alpha Γ :=
  values_eq (Φ := fun G DG => RawOccupationEnergy.A a Γ G / T DG ^ (alpha / 2))
    fun G G' DG DG' h => by
      simp only [RawOccupationEnergy.A, T, Araw_congr a Γ (h.mono fun s hs => hs.1),
        Tlin_congr (h.mono fun s hs => hs.2)]

/-- The raw energy set over `𝒪` is the raw energy set over joint representatives. -/
theorem rawEnergySetO_eq (a : ℝ) (Γ : Measure (Rd d)) [IsLocallyFiniteMeasure Γ] (ζ : ℝ) :
    rawEnergySetO a Γ ζ = RawOccupationEnergy.energySet a Γ ζ :=
  values_eq (Φ := fun G DG => RawOccupationEnergy.A a Γ G - ζ * T DG)
    fun G G' DG DG' h => by
      simp only [RawOccupationEnergy.A, T, Araw_congr a Γ (h.mono fun s hs => hs.1),
        Tlin_congr (h.mono fun s hs => hs.2)]

/-- `𝓔_⋆^𝒪` over `𝒪` equals the joint-representative value `OccupationPhysicalClass.EstarO`. -/
theorem EstarClassO_eq (a D : ℝ) (Γ : Measure (Rd d)) [IsLocallyFiniteMeasure Γ] :
    EstarClassO a D Γ = OccupationPhysicalClass.EstarO a D Γ := by
  rw [EstarClassO, energySetO_eq]; rfl

/-- `C_occ` over `𝒪` equals `RawOccupationEnergy.Cocc`. -/
theorem CoccO_eq (a alpha : ℝ) (Γ : Measure (Rd d)) [IsLocallyFiniteMeasure Γ] :
    CoccO a alpha Γ = RawOccupationEnergy.Cocc a alpha Γ := by
  rw [CoccO, ratioSetO_eq]; rfl

/-- `𝓔_ζ^𝒪` over `𝒪` equals `RawOccupationEnergy.EO`. -/
theorem EOO_eq (a : ℝ) (Γ : Measure (Rd d)) [IsLocallyFiniteMeasure Γ] (ζ : ℝ) :
    EOO a Γ ζ = RawOccupationEnergy.EO a Γ ζ := by
  rw [EOO, rawEnergySetO_eq]; rfl

/-! ### The re-issued results on the class `𝒪` -/

open SpatialFourLinear (Rsp Esp F0)
open RawOccupationEnergy (A)
open OccupationCeilingFinite (K0)
open SpatialBracket (Dzeta)
open VariationalDilation (CPos integratedRate rawCost)
open VariationalRate (scoreSet)

/-- **`P:occupation-physical-class`, every conclusion** (`integrated_spatial_occupation.tex`
lines 497-521, proof 523-575), on the class `𝒪` of strongly `H¹`-measurable fields
(`IsClassO`), under the section's standing assumptions (lines 4-10: `H:homog` with `a = α₀`,
`Γ ≠ 0`, `D = q - 2a`, `q = 4 - α`), with no supplied input: for every `g ∈ 𝒪` the pairings
`(s,t) ↦ B_Γ(g_s², g_t²)` (the physical integrals, `sqPair`) are a.e.-measurable on `(0,1)²` and
representative independent (with `J`); `s ↦ b(g_s)` is integrable with integral `T(g)`;
`J(g) < ∞`, its integrand is integrable with integral `J(g)`, and
`0 ≤ J(g) ≤ R_⋆ R_sp T(g)^{α/2}` (`E:occupation-physical-bound`); the energy value set over `𝒪`
is nonempty and bounded above and `0 < 𝓔_⋆^𝒪 ≤ R_⋆^{2/(2-α)} 𝓔_sp` with `𝓔_sp > 0`
(`E:occupation-own-energy`).  Route: `isOccField_of_classO` (TeX lines 534-540) and
`SpatialOccupationL7Completed.occupation_physical_class_completed_paper` /
`occupation_physical_class_Esp_paper`, transferred by representative independence;
`energySetO_eq`. -/
theorem occupation_physical_class_whole_paper {alpha a : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogCovariance d alpha a Γ μ) (hΓ : Γ ≠ 0) (D : ℝ) (hD : D = (4 - alpha) - 2 * a) :
    (∀ u : ℝ → H1R d, IsClassO u →
      AEMeasurable (fun p : ℝ × ℝ => sqPair Γ (gO u p.1) (gO u p.2)) (volI.prod volI) ∧
      (∀ G' : ℝ → Rd d → ℝ, (∀ᵐ s ∂volI, gO u s =ᵐ[volume] G' s) →
        (fun p : ℝ × ℝ => sqPair Γ (gO u p.1) (gO u p.2)) =ᵐ[volI.prod volI]
          (fun p : ℝ × ℝ => sqPair Γ (G' p.1) (G' p.2)) ∧
        Jlin a D Γ (gO u) = Jlin a D Γ G') ∧
      Integrable (fun s => ∫ x, ‖dgO u s x‖ ^ 2) volI ∧
      ∫ s, (∫ x, ‖dgO u s x‖ ^ 2) ∂volI = T (dgO u) ∧
      Jlin a D Γ (gO u) < ⊤ ∧
      Integrable (fun p : ℝ × ℝ =>
        Kstar a D (p.1 - p.2) * (sqPair Γ (gO u p.1) (gO u p.2)).toReal) (volI.prod volI) ∧
      ∫ p, Kstar a D (p.1 - p.2) * (sqPair Γ (gO u p.1) (gO u p.2)).toReal
        ∂(volI.prod volI) = J a D Γ (gO u) ∧
      0 ≤ J a D Γ (gO u) ∧
      J a D Γ (gO u) ≤ Rstar a D * Rsp Γ alpha * T (dgO u) ^ (alpha / 2)) ∧
    (energySetO a D Γ).Nonempty ∧ BddAbove (energySetO a D Γ) ∧
    0 < EstarClassO a D Γ ∧
    EstarClassO a D Γ ≤ Rstar a D ^ (2 / (2 - alpha)) * Esp Γ ∧ 0 < Esp Γ := by
  have := hH.Γ_radon
  obtain ⟨hall, h1, h2, h3, -⟩ :=
    SpatialOccupationL7Completed.occupation_physical_class_completed_paper hH hΓ D hD
  obtain ⟨hallE, -, -, -, h5, h6⟩ :=
    SpatialOccupationL7Completed.occupation_physical_class_Esp_paper hH hΓ D hD
  rw [EstarClassO_eq, energySetO_eq]
  refine ⟨fun u hu => ?_, h1, h2, h3, h5, h6⟩
  obtain ⟨G, DG, hO, he⟩ := isOccField_of_classO hu
  obtain ⟨m1, -, i1, i2, f1, i3, i4, j0, -⟩ := hall G DG hO
  obtain ⟨-, -, jle⟩ := hallE G DG hO
  have hpe := sqPair_Jlin_congr a D Γ (he.mono fun s hs => hs.1)
  have hJ : J a D Γ G = J a D Γ (gO u) := by simp only [J, hpe.2]
  have hTr : T DG = T (dgO u) := by simp only [T, Tlin_congr (he.mono fun s hs => hs.2)]
  have hb : (fun s => ∫ x, ‖DG s x‖ ^ 2) =ᵐ[volI] fun s => ∫ x, ‖dgO u s x‖ ^ 2 :=
    he.mono fun s hs => integral_congr_ae (hs.2.mono fun x hx => by simp only [hx])
  have hk : (fun p : ℝ × ℝ => Kstar a D (p.1 - p.2) * (sqPair Γ (G p.1) (G p.2)).toReal)
      =ᵐ[volI.prod volI]
      fun p => Kstar a D (p.1 - p.2) * (sqPair Γ (gO u p.1) (gO u p.2)).toReal :=
    hpe.1.mono fun p hp => by simp only [hp]
  refine ⟨m1.congr hpe.1, fun G' hG' => sqPair_Jlin_congr a D Γ hG', i1.congr hb, ?_, ?_,
    i3.congr hk, ?_, hJ ▸ j0, ?_⟩
  · rw [← integral_congr_ae hb, i2, hTr]
  · rw [← hpe.2]; exact f1
  · rw [← integral_congr_ae hk, i4, hJ]
  · rw [← hJ, ← hTr]; exact jle

/-- Auxiliary to the Lean proof route: the `L²` dilation `U_ℓ` respects a.e. equality
(`ℓ ≠ 0`; `x ↦ ℓx` is quasi-measure-preserving for Lebesgue measure). -/
theorem dilL2_congr {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {r : ℝ} (hr : r ≠ 0)
    {f f' : Rd d → E} (h : f =ᵐ[volume] f') :
    WeakSobolev.dilL2 r f =ᵐ[volume] WeakSobolev.dilL2 r f' := by
  have hq := Measure.quasiMeasurePreserving_smul (volume : Measure (Rd d)) hr
  filter_upwards [hq.ae_eq_comp h] with x hx
  simp only [WeakSobolev.dilL2, Function.comp] at hx ⊢
  rw [hx]

/-- **`P:raw-occupation-energy`, every conclusion** (`integrated_occupation_ceiling.tex` lines
111-131, proof 133-177), on the class `𝒪` of strongly `H¹`-measurable fields, under the
section's standing assumptions (lines 4-21: `H:homog` with `a = α₀`, `Γ ≠ 0`), with no supplied
input: `0 < C_occ ≤ K_0 R_sp` (the ratio set over `𝒪` nonempty and bounded above); for every
`g ∈ 𝒪`: `0 < T(g)`, `A(g) < ∞`, `0 ≤ A(g) ≤ K_0 R_sp T(g)^{α/2}` (`E:raw-occupation-bound`), and
for every `ℓ > 0` the dilation `U_ℓ g` (`ℓ^{d/2} g_s(ℓ ·)`, up to versions) is in `𝒪` with
`A(U_ℓ g) = ℓ^α A(g)` and `T(U_ℓ g) = ℓ² T(g)`; `U_{1/ℓ} U_ℓ = id`; for every `ζ > 0` the
energy value set over `𝒪` is nonempty and bounded above,
`𝓔_ζ^𝒪 = D_ζ C_occ^{2/(2-α)}` (`E:raw-occupation-energy`),
`C_occ = (2𝓔_ζ^𝒪/(2-α))^{(2-α)/2}(2ζ/α)^{α/2}` (`E:raw-occupation-ratio`), `𝓔_ζ^𝒪 > 0` and
`𝓔_ζ^𝒪 = ζ^{-α/(2-α)} 𝓔_1^𝒪`.  Route: `RawOccupationEnergy.raw_occupation_energy_paper` and
the bridge (`isOccField_of_classO`, `classO_of_isOccField`, `ratioSetO_eq`,
`rawEnergySetO_eq`). -/
theorem raw_occupation_energy_whole_paper {alpha a : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogCovariance d alpha a Γ μ) (hΓ : Γ ≠ 0) :
    (ratioSetO a alpha Γ).Nonempty ∧ BddAbove (ratioSetO a alpha Γ) ∧
    0 < CoccO a alpha Γ ∧ CoccO a alpha Γ ≤ K0 a * Rsp Γ alpha ∧
    (∀ u : ℝ → H1R d, IsClassO u →
      0 < T (dgO u) ∧ RawOccupationEnergy.Araw a Γ (gO u) < ⊤ ∧ 0 ≤ A a Γ (gO u) ∧
      A a Γ (gO u) ≤ K0 a * Rsp Γ alpha * T (dgO u) ^ (alpha / 2) ∧
      ∀ ℓ : ℝ, 0 < ℓ → ∃ u' : ℝ → H1R d, IsClassO u' ∧
        (∀ᵐ s ∂volI, gO u' s =ᵐ[volume] WeakSobolev.dilL2 ℓ (gO u s)) ∧
        A a Γ (gO u') = ℓ ^ alpha * A a Γ (gO u) ∧ T (dgO u') = ℓ ^ 2 * T (dgO u)) ∧
    (∀ ℓ : ℝ, 0 < ℓ → ∀ f : Rd d → ℝ,
      WeakSobolev.dilL2 ℓ⁻¹ (WeakSobolev.dilL2 ℓ f) = f) ∧
    ∀ ζ : ℝ, 0 < ζ →
      (rawEnergySetO a Γ ζ).Nonempty ∧ BddAbove (rawEnergySetO a Γ ζ) ∧
      EOO a Γ ζ = Dzeta alpha ζ * CoccO a alpha Γ ^ (2 / (2 - alpha)) ∧
      CoccO a alpha Γ = (2 * EOO a Γ ζ / (2 - alpha)) ^ ((2 - alpha) / 2) *
        (2 * ζ / alpha) ^ (alpha / 2) ∧
      0 < EOO a Γ ζ ∧
      EOO a Γ ζ = ζ ^ (-(alpha / (2 - alpha))) * EOO a Γ 1 := by
  have := hH.Γ_radon
  obtain ⟨h1, h2, h3, h4, hall, h5⟩ := RawOccupationEnergy.raw_occupation_energy_paper hH hΓ
  have eE : ∀ ζ, EOO a Γ ζ = RawOccupationEnergy.EO a Γ ζ := EOO_eq a Γ
  have eS : ∀ ζ, rawEnergySetO a Γ ζ = RawOccupationEnergy.energySet a Γ ζ :=
    rawEnergySetO_eq a Γ
  rw [CoccO_eq, ratioSetO_eq]
  simp only [eE, eS]
  refine ⟨h1, h2, h3, h4, fun u hu => ?_, fun ℓ hℓ f => ?_, h5⟩
  · obtain ⟨G, DG, hO, he⟩ := isOccField_of_classO hu
    obtain ⟨t0, b1, b2, b3, hdil⟩ := hall G DG hO
    have hAr := Araw_congr a Γ (he.mono fun s hs => hs.1)
    have hA : A a Γ G = A a Γ (gO u) := by simp only [A, hAr]
    have hTr : T DG = T (dgO u) := by simp only [T, Tlin_congr (he.mono fun s hs => hs.2)]
    refine ⟨hTr ▸ t0, hAr ▸ b1, hA ▸ b2, by rw [← hA, ← hTr]; exact b3, fun ℓ hℓ => ?_⟩
    obtain ⟨hOd, hAd, hTd, -, -⟩ := hdil ℓ hℓ
    obtain ⟨u', hu', he'⟩ := classO_of_isOccField hOd
    have hA' : A a Γ (RawOccupationEnergy.dilField ℓ G) = A a Γ (gO u') := by
      simp only [A, Araw_congr a Γ (he'.mono fun s hs => hs.1)]
    have hT' : T (RawOccupationEnergy.dilGrad ℓ DG) = T (dgO u') := by
      simp only [T, Tlin_congr (he'.mono fun s hs => hs.2)]
    refine ⟨u', hu', ?_, ?_, ?_⟩
    · filter_upwards [he', he] with s hs hs0
      exact hs.1.symm.trans (dilL2_congr hℓ.ne' hs0.1)
    · rw [← hA', hAd, hA]
    · rw [← hT', hTd, hTr]
  · funext x
    exact congrFun (congrFun (RawOccupationEnergy.dil_inv hℓ (fun _ => f)
      (fun _ => (0 : Rd d → Rd d))).1 0) x

/-- **`L:occupation-rayleigh-selection`** (`integrated_occupation_ceiling.tex` lines 180-188,
proof 190-236) with the selected field in the class `𝒪` of strongly `H¹`-measurable fields,
under the section's standing assumptions (`H:homog` with `a = α₀`, `Γ ≠ 0`): for
`Ψ ∈ C_pos` and `ε > 0` there is `g_ε ∈ 𝒪` with `I_Ψ² + T(g_ε) ≤ √(v_Ψ A(g_ε)) + ε`
(`E:occupation-rayleigh-selection`).  Route:
`OccupationCeilingExact.occupation_rayleigh_selection_paper` and `classO_of_isOccField`. -/
theorem occupation_rayleigh_selection_whole_paper {alpha a : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogCovariance d alpha a Γ μ) (hΓ0 : Γ ≠ 0) {Ψ : ℝ × Rd d → ℝ} (hΨ : Ψ ∈ CPos d)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ u : ℝ → H1R d, IsClassO u ∧
      integratedRate a Γ Ψ ^ 2 + T (dgO u) ≤ Real.sqrt (rawCost a Γ Ψ * A a Γ (gO u)) + ε := by
  have := hH.Γ_radon
  obtain ⟨G, DG, hO, hsel⟩ :=
    OccupationCeilingExact.occupation_rayleigh_selection_paper hH hΓ0 hΨ hε
  obtain ⟨u, hu, he⟩ := classO_of_isOccField hO
  have hA : A a Γ G = A a Γ (gO u) := by
    simp only [A, Araw_congr a Γ (he.mono fun s hs => hs.1)]
  have hTr : T DG = T (dgO u) := by simp only [T, Tlin_congr (he.mono fun s hs => hs.2)]
  exact ⟨u, hu, by rw [← hA, ← hTr]; exact hsel⟩

/-- **`T:intrinsic-occupation-ceiling` for `S_c^pos`** (`integrated_occupation_ceiling.tex`
lines 249-264, proof 266-316) with `C_occ` and `𝓔_ζ^𝒪` over the class `𝒪` of strongly
`H¹`-measurable fields, under the section's standing assumptions (`H:homog` with `a = α₀`,
`Γ ≠ 0`): for every `c > 0` the value set is nonempty and bounded above, `c I_Ψ - v_Ψ/2 ≤ U_c` for
`Ψ ∈ C_pos`, `S_c^pos ≤ U_c = c^m k[α^{α/2} C_occ/(8q^{q/2})]^{1/k}`, and
`U_c = c^m (2ζ)^{α/(2k)} F_0(𝓔_ζ^𝒪)` for every `ζ > 0`.  Narrower than the TeX: the moment
sentence `C_2(Γ,a) ≤ U_2` (line 261) needs `T:intrinsic-second-moment` (foundation D1) and is
not formalized.  Route: `OccupationCeilingExact.intrinsic_occupation_ceiling_paper`,
`CoccO_eq`, `EOO_eq`. -/
theorem intrinsic_occupation_ceiling_classO_paper {alpha a : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogCovariance d alpha a Γ μ) (hΓ0 : Γ ≠ 0) :
    ∀ c : ℝ, 0 < c →
      (scoreSet a Γ c).Nonempty ∧ BddAbove (scoreSet a Γ c) ∧
      (∀ Ψ ∈ CPos d, c * integratedRate a Γ Ψ - rawCost a Γ Ψ / 2 ≤
        SpatialBracket.ceilingValue alpha c (CoccO a alpha Γ)) ∧
      sSup (scoreSet a Γ c) ≤ SpatialBracket.ceilingValue alpha c (CoccO a alpha Γ) ∧
      ∀ ζ : ℝ, 0 < ζ → SpatialBracket.ceilingValue alpha c (CoccO a alpha Γ) =
        c ^ ((4 - alpha) / (3 - alpha)) * (2 * ζ) ^ (alpha / (2 * (3 - alpha))) *
          F0 alpha (EOO a Γ ζ) := by
  have := hH.Γ_radon
  simp only [CoccO_eq, EOO_eq]
  exact OccupationCeilingExact.intrinsic_occupation_ceiling_paper hH hΓ0

/-- **The comparison of `C:intrinsic-spatial-bracket` for `S_2^pos`**
(`integrated_occupation_ceiling.tex` lines 328-332, proof 346-361) with `𝓔_{1/2}^𝒪` over the
class `𝒪` of strongly `H¹`-measurable fields, under the standing assumptions (`H:homog` with
`a = α₀`, `Γ ≠ 0`): the value set at `c = 2` is nonempty and bounded above and
`S_2^pos ≤ 2^m F_0(𝓔_{1/2}^𝒪) < 2^m F_a(𝓔_{1/2}^𝒪)`.  Narrower than the TeX: stated for
`S_2^pos`, not `C_2(Γ,a)` (`T:intrinsic-second-moment`, foundation D1); the bracket
`E:intrinsic-spatial-bracket` itself (no class `𝒪`) is
`SpatialBracket.intrinsic_spatial_bracket_paper`.  Route:
`OccupationCeilingExact.intrinsic_spatial_comparison_paper` and `EOO_eq`. -/
theorem intrinsic_spatial_comparison_classO_paper {alpha a : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogCovariance d alpha a Γ μ) (hΓ0 : Γ ≠ 0) :
    (scoreSet a Γ 2).Nonempty ∧ BddAbove (scoreSet a Γ 2) ∧
      sSup (scoreSet a Γ 2) ≤
        2 ^ ((4 - alpha) / (3 - alpha)) * F0 alpha (EOO a Γ (1 / 2)) ∧
      2 ^ ((4 - alpha) / (3 - alpha)) * F0 alpha (EOO a Γ (1 / 2)) <
        2 ^ ((4 - alpha) / (3 - alpha)) * SpatialBracket.Fb alpha a (EOO a Γ (1 / 2)) := by
  have := hH.Γ_radon
  rw [EOO_eq]
  exact OccupationCeilingExact.intrinsic_spatial_comparison_paper hH hΓ0

/-! ### The zero covariance -/

/-- For `Γ = 0` every physical pairing vanishes (TeX `integrated_spatial_occupation.tex` line
577; `integrated_occupation_ceiling.tex` line 380). -/
theorem sqPair_zero (f h : Rd d → ℝ) : sqPair (0 : Measure (Rd d)) f h = 0 := by
  simp [sqPair, OccupationKernelRow.pairing, OccupationKernelRow.pairMeasure]

/-- Auxiliary to the Lean proof route: `‖∇g‖₂²` through the named gradient is `gradEnergy`. -/
theorem integral_norm_grad_sq (g : Rd d → ℝ) :
    ∫ x, ‖VariationalFloor.grad g x‖ ^ 2 = SpatialFourierBound.gradEnergy g := by
  unfold SpatialFourierBound.gradEnergy VariationalFloor.grad
  congr 1; funext x
  rw [LinearIsometryEquiv.norm_map]

/-- Auxiliary to the Lean proof route: a set of nonpositive reals with members above every
`-ε` has supremum `0`. -/
theorem sSup_eq_zero_of_small {S : Set ℝ} (hle : ∀ v ∈ S, v ≤ 0)
    (hsmall : ∀ ε : ℝ, 0 < ε → ∃ v ∈ S, -ε < v) : sSup S = 0 := by
  obtain ⟨v, hv, -⟩ := hsmall 1 one_pos
  refine csSup_eq_of_forall_le_of_forall_lt_exists_gt ⟨v, hv⟩ hle fun w hw => ?_
  obtain ⟨v, hv, hlt⟩ := hsmall (-w) (by linarith)
  exact ⟨v, hv, by linarith⟩

/-- The class `𝒪` has members of arbitrarily small `T` (TeX lines 578-580 of
`integrated_spatial_occupation.tex`: small spatial dilations of one fixed unit compact profile,
constant in time). -/
theorem exists_classO_small {ε : ℝ} (hε : 0 < ε) :
    ∃ u : ℝ → H1R d, IsClassO u ∧ T (dgO u) < ε := by
  obtain ⟨g, hg⟩ := SpatialSmoothRatio.exists_unitTest d
  obtain ⟨hO, -⟩ := OccupationCeilingExact.stepField_isOcc (N := 0) (f := fun _ => g)
    (fun _ => hg)
  set T0 := T (OccupationCeilingExact.stepDG 0 (fun _ => g)) with hT0def
  have hT0 : 0 ≤ T0 := ENNReal.toReal_nonneg
  set ℓ := Real.sqrt (ε / (2 * (T0 + 1))) with hℓdef
  have hℓ : 0 < ℓ := Real.sqrt_pos.2 (by positivity)
  have hℓ2 : ℓ ^ 2 = ε / (2 * (T0 + 1)) := Real.sq_sqrt (by positivity)
  obtain ⟨hOd, hTd⟩ := RawOccupationEnergy.isOccField_dil hℓ hO
  obtain ⟨u, hu, he⟩ := classO_of_isOccField hOd
  refine ⟨u, hu, ?_⟩
  have e : T (dgO u) = ℓ ^ 2 * T0 := by
    rw [T, ← Tlin_congr (he.mono fun s hs => hs.2), hTd, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (by positivity)]
    rfl
  rw [e, hℓ2, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
  nlinarith

/-- `F_b(0) = 0` (TeX `integrated_occupation_ceiling.tex` line 238 defines `F_b(0) = 0`; here it
is computed, for `α < 2`). -/
theorem Fb_zero {alpha : ℝ} (ha2 : alpha < 2) (b : ℝ) : SpatialBracket.Fb alpha b 0 = 0 := by
  have hk : 1 / (3 - alpha) ≠ 0 := one_div_ne_zero (by linarith)
  have hq : (2 - alpha) / 2 ≠ 0 := div_ne_zero (by linarith) two_ne_zero
  unfold SpatialBracket.Fb
  rw [mul_zero, zero_div, Real.zero_rpow hq, mul_zero, Real.zero_rpow hk, mul_zero]

/-- `F_0(0) = 0` for the map of `E:spatial-static-energy-score` (`α < 2`). -/
theorem F0_zero {alpha : ℝ} (ha2 : alpha < 2) : F0 alpha 0 = 0 := by
  have hk : 1 / (3 - alpha) ≠ 0 := one_div_ne_zero (by linarith)
  have hq : (2 - alpha) / 2 ≠ 0 := div_ne_zero (by linarith) two_ne_zero
  unfold F0
  rw [mul_zero, zero_div, Real.zero_rpow hq, zero_div, Real.zero_rpow hk, mul_zero]

/-- The ceiling value vanishes at `C_occ = 0` (`α < 2`). -/
theorem ceilingValue_zero {alpha : ℝ} (ha2 : alpha < 2) (c : ℝ) :
    SpatialBracket.ceilingValue alpha c 0 = 0 := by
  have hk : 1 / (3 - alpha) ≠ 0 := one_div_ne_zero (by linarith)
  unfold SpatialBracket.ceilingValue
  rw [mul_zero, zero_div, Real.zero_rpow hk, mul_zero, mul_zero]

/-- At `Γ = 0` the extended pairing vanishes. -/
theorem pairing_zero (f h : Rd d → ℝ≥0∞) :
    OccupationKernelRow.pairing (0 : Measure (Rd d)) f h = 0 := by
  simp [OccupationKernelRow.pairing, OccupationKernelRow.pairMeasure]

/-- At `Γ = 0`, `J(g) = 0` for every field. -/
theorem J_zero (a D : ℝ) (G : ℝ → Rd d → ℝ) : J a D (0 : Measure (Rd d)) G = 0 := by
  simp [J, Jlin, sqPair_zero]

/-- At `Γ = 0`, `A(g) = 0` for every field. -/
theorem A_zero (a : ℝ) (G : ℝ → Rd d → ℝ) : A a (0 : Measure (Rd d)) G = 0 := by
  simp [A, RawOccupationEnergy.Araw, sqPair_zero]

/-- `R_sp = 0` at `Γ = 0` (TeX line 577: "set `R_sp = 0`"; here it is the supremum of the zero
ratios over the nonempty unit class). -/
theorem Rsp_zero (alpha : ℝ) : Rsp (0 : Measure (Rd d)) alpha = 0 := by
  obtain ⟨g, hg⟩ := SpatialSmoothRatio.exists_unitTest d
  have hset : SpatialFourLinear.ratioSetH1 (0 : Measure (Rd d)) alpha = {0} := by
    refine Set.eq_singleton_iff_unique_mem.2
      ⟨⟨g, _, SpatialStaticControls.isUnitH1_of_unitTest hg, ?_⟩, ?_⟩
    · simp [pairing_zero]
    · rintro r ⟨f, k, -, rfl⟩
      simp [pairing_zero]
  rw [Rsp, hset, csSup_singleton]

/-- `𝓔_sp = 0` at `Γ = 0` (TeX lines 578-580 and 382: the supremum of `-b/2`, approached by
small dilations of one fixed unit compact profile). -/
theorem Esp_zero : Esp (0 : Measure (Rd d)) = 0 := by
  obtain ⟨g, hg⟩ := SpatialSmoothRatio.exists_unitTest d
  refine sSup_eq_zero_of_small ?_ fun ε hε => ?_
  · rintro v ⟨f, k, -, rfl⟩
    simp only [pairing_zero, ENNReal.toReal_zero, zero_sub, neg_nonpos]
    exact div_nonneg (integral_nonneg fun x => by positivity) two_pos.le
  · set b0 := SpatialFourierBound.gradEnergy g
    have hb0 : 0 ≤ b0 := SpatialFourierBound.gradEnergy_nonneg _
    set ℓ := Real.sqrt (ε / (b0 + 1)) with hℓdef
    have hℓ : 0 < ℓ := Real.sqrt_pos.2 (by positivity)
    have hℓ2 : ℓ ^ 2 = ε / (b0 + 1) := Real.sq_sqrt (by positivity)
    have hgd := SpatialSmoothRatio.isUnitTest_dilL2 hℓ hg
    refine ⟨_, ⟨_, _, SpatialStaticControls.isUnitH1_of_unitTest hgd, rfl⟩, ?_⟩
    rw [pairing_zero, ENNReal.toReal_zero, zero_sub, integral_norm_grad_sq,
      SpatialSmoothRatio.gradEnergy_dilL2 hℓ (hg.1.differentiable (by simp)), hℓ2]
    have : ε / (b0 + 1) * b0 / 2 < ε := by
      rw [div_mul_eq_mul_div, div_div, div_lt_iff₀ (by positivity)]; nlinarith
    linarith

/-- `𝓔_⋆^𝒪 = 0` at `Γ = 0` (TeX lines 578-580: the supremum of `-T/2` over `𝒪`, approached by
small dilations of a constant-in-time unit compact profile). -/
theorem EstarClassO_zero (a D : ℝ) : EstarClassO a D (0 : Measure (Rd d)) = 0 := by
  refine sSup_eq_zero_of_small ?_ fun ε hε => ?_
  · rintro v ⟨u, -, rfl⟩
    have hT : 0 ≤ T (dgO u) := ENNReal.toReal_nonneg
    rw [J_zero]
    linarith
  · obtain ⟨u, hu, hTu⟩ := exists_classO_small (d := d) hε
    exact ⟨_, ⟨u, hu, rfl⟩, by rw [J_zero]; linarith⟩

/-- `C_occ = 0` at `Γ = 0` (TeX line 380), with the ratio set `{0}` (nonempty). -/
theorem ratioSetO_zero (a alpha : ℝ) : ratioSetO a alpha (0 : Measure (Rd d)) = {0} := by
  obtain ⟨u, hu, -⟩ := exists_classO_small (d := d) one_pos
  refine Set.eq_singleton_iff_unique_mem.2 ⟨⟨u, hu, by rw [A_zero, zero_div]⟩, ?_⟩
  rintro r ⟨u', -, rfl⟩
  rw [A_zero, zero_div]

/-- `C_occ = 0` at `Γ = 0` (TeX line 380). -/
theorem CoccO_zero (a alpha : ℝ) : CoccO a alpha (0 : Measure (Rd d)) = 0 := by
  rw [CoccO, ratioSetO_zero, csSup_singleton]

/-- `𝓔_ζ^𝒪 = 0` at `Γ = 0` for `ζ > 0` (TeX lines 380-382). -/
theorem EOO_zero (a : ℝ) {ζ : ℝ} (hζ : 0 < ζ) : EOO a (0 : Measure (Rd d)) ζ = 0 := by
  refine sSup_eq_zero_of_small ?_ fun ε hε => ?_
  · rintro v ⟨u, -, rfl⟩
    have hT : 0 ≤ T (dgO u) := ENNReal.toReal_nonneg
    rw [A_zero]
    nlinarith [mul_nonneg hζ.le hT]
  · obtain ⟨u, hu, hTu⟩ := exists_classO_small (d := d) (div_pos hε hζ)
    refine ⟨_, ⟨u, hu, rfl⟩, ?_⟩
    rw [A_zero]
    rw [lt_div_iff₀ hζ] at hTu
    nlinarith

/-- **The direct zero case** (`integrated_spatial_occupation.tex` lines 577-582 and
`integrated_occupation_ceiling.tex` lines 379-385), under `H:homog` with `a = α₀` and `Γ = 0`:
all physical pairings vanish; `R_sp = 0` and `𝓔_sp = 0`; on the class `𝒪`, `J(g) = 0` and
`A(g) = 0`, the occupation energy `𝓔_⋆^𝒪 = 0`, `C_occ = 0` and `𝓔_ζ^𝒪 = 0` for `ζ > 0`, all
suprema with nonempty value sets (small dilations of one fixed unit compact profile, constant in
time, without a zero-gradient unit state); with `F_b(0) = 0`, the ceiling `U_c` and its
`𝓔_ζ^𝒪` form are both `0` (the non-strict bounds become the zero identity).  Of `H:homog` only
`α < 2` is used (for `F_b(0) = 0`).  Not formalized here: `C_2 = 0` and the vanishing of the
variational values `S_c^pos` (line 379; `C_2` needs foundation D1). -/
theorem zero_covariance_paper {alpha a : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogCovariance d alpha a Γ μ) (hΓ : Γ = 0) (D : ℝ) :
    (∀ f h : Rd d → ℝ, sqPair Γ f h = 0) ∧
    Rsp Γ alpha = 0 ∧ Esp Γ = 0 ∧
    (∀ u : ℝ → H1R d, IsClassO u → J a D Γ (gO u) = 0 ∧ A a Γ (gO u) = 0) ∧
    (energySetO a D Γ).Nonempty ∧ EstarClassO a D Γ = 0 ∧
    (ratioSetO a alpha Γ).Nonempty ∧ CoccO a alpha Γ = 0 ∧
    (∀ ζ : ℝ, 0 < ζ → (rawEnergySetO a Γ ζ).Nonempty ∧ EOO a Γ ζ = 0) ∧
    (∀ c ζ : ℝ, 0 < ζ → SpatialBracket.ceilingValue alpha c (CoccO a alpha Γ) = 0 ∧
      c ^ ((4 - alpha) / (3 - alpha)) * (2 * ζ) ^ (alpha / (2 * (3 - alpha))) *
        F0 alpha (EOO a Γ ζ) = 0) ∧
    ∀ b : ℝ, SpatialBracket.Fb alpha b 0 = 0 := by
  subst hΓ
  obtain ⟨-, -, ha2, -⟩ := SpatialSmoothRatio.homog_consequences hH
  obtain ⟨u, hu, -⟩ := exists_classO_small (d := d) one_pos
  refine ⟨sqPair_zero, Rsp_zero alpha, Esp_zero, fun u _ => ⟨J_zero _ _ _, A_zero _ _⟩,
    ⟨_, u, hu, rfl⟩, EstarClassO_zero a D, ⟨_, u, hu, rfl⟩, CoccO_zero a alpha,
    fun ζ hζ => ⟨⟨_, u, hu, rfl⟩, EOO_zero a hζ⟩, fun c ζ hζ => ⟨?_, ?_⟩, Fb_zero ha2⟩
  · rw [CoccO_zero, ceilingValue_zero ha2]
  · rw [EOO_zero a hζ, F0_zero ha2, mul_zero]

end StratonovichHAMSecondMoment.ClassOBridge
