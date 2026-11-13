module

/-
Copyright 2026 Le Chen. SPDX-License-Identifier: Apache-2.0

Proposition `P:occupation-physical-class` (The full physical occupation class) of
`notes/integrated_spatial_occupation.tex` (revision a284420): the class `𝒪` (lines 381-384),
the statement (lines 386-404: displays `E:occupation-physical-bound`, lines 395-397, and
`E:occupation-own-energy`, lines 399-403) and its proof (lines 406-442), under the section's
standing assumptions (lines 4-10: a nonzero covariance satisfying `H:homog`, `a = α₀`,
`q = 4 - α`, `D = q - 2a`).

Objects (reused from the package: `OccupationKernelRow.Kstar` (`K_⋆`), `Rstar` (`R_⋆`) and
`pairing` (`B_Γ`, `L:spatial-physical-pair`); `SpatialStaticControls.IsUnitH1` (unit `H¹` pairs);
`WeakSobolev.HasWeakGradient`; `SpatialSmoothRatio.R0` (`R_0`)):
* `sqPair Γ f h = B_Γ(f², h²)` (the physical, extended nonnegative pairing of the squares);
  `gradSqE gf = b(f) = ‖∇f‖₂²`; `Nnorm α f gf = N(f)` of `P:spatial-four-linear`;
* `IsOccField G DG`: the class `𝒪`, modelled through joint representatives (see below);
* `Tlin`, `T` (`T(g)`), `Jlin`, `J` (`J(g)`), `energySet`, `EstarO` (`𝓔_⋆^𝒪`) and
  `spEnergyVal α R = (2-α)/2 · α^{α/(2-α)} · R^{2/(2-α)}` (the right side of
  `E:spatial-energy-map`, lines 309-314, at `R_sp = R`).

Formalized:
* `occupation_physical_class_paper` (the `_paper` wrapper, with `H:homog` as
  `HomogHypothesis.HomogCovariance d α a Γ μ`, `Γ ≠ 0`, `D = (4 - α) - 2a` and the named input
  below at `R = R_0`): for every field in `𝒪`, the pairings `(s,t) ↦ B_Γ(g_s², g_t²)` are
  a.e.-measurable on `(0,1)²`, representative independent (a.e. in `(s,t)`, and `J` unchanged,
  under Lebesgue-a.e. changes of the spatial versions at a.e. time) and are the physical
  integrals by definition (`sqPair` is `pairing`); `s ↦ b(g_s)` is integrable with integral
  `T(g)`; `J(g) < ∞`, the real integrand `K_⋆(s-t) B_Γ(g_s², g_t²)` is integrable on `(0,1)²`
  with integral `J(g)`, and `0 ≤ J(g) ≤ R_⋆ R_0 T(g)^{α/2}` (`E:occupation-physical-bound`);
  the energy value set is nonempty and bounded above, and
  `0 < 𝓔_⋆^𝒪 ≤ R_⋆^{2/(2-α)} spEnergyVal α R_0` (`E:occupation-own-energy`).
* General forms: `occupation_physical_bound` and `occupation_own_energy` (for `0 < a < 1`,
  `D > 0`, `0 < α < 2`, a locally finite `Γ`, any real `R ≥ 0` in the named input; the energy
  form also assumes the scaling `VariationalDilation.SetScaling α Γ` and `Γ ≠ 0`, used only for
  positivity); `Jlin_le`; `sqPair_aemeasurable`, `sqPair_Jlin_congr` (locally finite `Γ` only);
  `Tlin_congr`, `Tlin_unique` (`T(g)` depends only on `g`); `T_eq_integral`; `scalar_max` (the
  scalar maximum of lines 431-433); `exists_pos_member` (the positivity witness of lines
  434-439).

Supplied input (named hypothesis, no stronger than its source): `SquarePairingBounds Γ α R`,
two conclusions of `P:spatial-four-linear` (lines 219-237; wave item L7-d) for real `H¹`
profiles: `E:spatial-homogeneous-bound` `A_sp(f) ≤ R N(f)⁴` (in `[0,∞]`) and
`E:spatial-square-CS` in the equivalent squared form `B_Γ(f²,h²)² ≤ A_sp(f) A_sp(h)` in `[0,∞]`
(`squareCS_of_sqrt` converts the real `√` form).  The wrapper takes `R = R_0`.  The TeX's bound
is stated with `R_sp`; `R_sp = R_0` is the last claim of `P:spatial-four-linear`, and the TeX
proof uses `E:spatial-homogeneous-bound`, which carries `R_0`.  The identification of
`spEnergyVal α R_0` with `𝓔_sp` is `E:spatial-energy-map` (`P:spatial-energy-map`, L7-d), not
used or assumed here.

Modelling of `𝒪` (narrower than the TeX, recorded): the TeX's fields are strongly
`H¹(ℝ^d;ℝ)`-measurable maps on `(0,1)` (the package has no `H¹`-valued type).  `IsOccField`
instead asks for a.e.-strongly measurable joint representatives `(s,x) ↦ g_s(x)` and
`(s,x) ↦ ∇g_s(x)` on `(0,1) × ℝ^d` (Lebesgue), a unit `H¹` pair at a.e. time, and `T(g) < ∞`.
The TeX proof (lines 409-414) constructs such joint representatives from strong measurability
(for `g`; the same argument applies to `∇g`); that construction, and the converse (Pettis), are
not formalized, so `𝒪` and `𝓔_⋆^𝒪` here are over fields given by joint representatives.

Implicit hypotheses made explicit: the measurability above; `T(g)` and `J(g)` as extended
integrals (their finiteness and the Bochner forms are conclusions); `0 < a < 1`, `D > 0`,
`0 < α < 2` (derived from `H:homog` in the wrapper).

Proof route.  As in the TeX for the bound (lines 421-429): `B_Γ(g_s², g_t²)` is bounded by
`R_0 F(s) F(t)` with `F(s) = b(g_s)^{α/4}`, then `2F(s)F(t) ≤ F(s)² + F(t)²`, the row bound
`E:occupation-kernel-row` and its column form by evenness, and Tonelli.  Differences:
measurability (lines 407-419) is proved directly by Tonelli on the joint representative
(no continuity of the pairing map on `H¹ × H¹` is used); the concavity step
`∫_0^1 b^{α/2} ≤ T^{α/2}` is proved by Hölder (`lintegral_rpow_le`); positivity (lines
434-439) uses the lower bound `J ≥ K_⋆(1) ℓ^α A_sp(g)` (`K_⋆` decreasing) instead of the
exact value `J_0 ℓ^α A_sp(g)`, with an explicit `ℓ`.  The remark on zero covariance (lines
444-449) is outside this proposition and is not formalized.  Lemmas marked "auxiliary to the
Lean proof route" have no manuscript label.
-/

public import Mathlib
public import StratonovichHAMSecondMoment.OccupationKernelRow
public import StratonovichHAMSecondMoment.SpatialStaticControls
public import StratonovichHAMSecondMoment.SpatialSmoothRatio

@[expose] public section

noncomputable section

set_option autoImplicit false

open MeasureTheory Set Real Filter
open scoped ENNReal

namespace StratonovichHAMSecondMoment.OccupationPhysicalClass

open HomogHypothesis (Rd HomogCovariance)
open OccupationKernelRow (Kstar Rstar row pairing pairMeasure)
open WeakSobolev (HasWeakGradient)
open SpatialStaticControls (IsUnitH1)

variable {d : ℕ}

/-- Auxiliary to the Lean proof route: Lebesgue measure on the time interval `(0,1)` (the
`ds`, `dt` of TeX lines 382-393). -/
abbrev volI : Measure ℝ := volume.restrict (Ioo (0 : ℝ) 1)

/-- `B_Γ(f², h²)` (TeX line 388): the physical pairing `E:spatial-physical-pair` (lines 15-17)
of the squares, i.e. `OccupationKernelRow.pairing` (the extended nonnegative integral
`∫ f(x)² h(x-y)² ν(dx,dy)`) at `x ↦ f(x)²`, `x ↦ h(x)²`.  `A_sp(f) = sqPair Γ f f` (line 35).
On `C_c^∞` profiles it is `ofReal` of the real pairing `SpatialFourierBound.spatialPair`
(`SpatialStaticControls.pairing_eq_spatialPair`). -/
def sqPair (Γ : Measure (Rd d)) (f h : Rd d → ℝ) : ℝ≥0∞ :=
  pairing Γ (fun x => ENNReal.ofReal (f x ^ 2)) (fun x => ENNReal.ofReal (h x ^ 2))

/-- `b(f) = ‖∇f‖₂²` (line 35) on `H¹`, as the extended integral `∫⁻ ‖gf‖²` of a weak gradient
`gf` of `f`.  For `gf ∈ L²` it is `ofReal (∫ ‖gf‖²)` (`gradSqE_eq`); by a.e. uniqueness of `L²`
weak gradients (`WeakSobolev.weakGradient_ae_unique`) it depends only on `f`. -/
def gradSqE (gf : Rd d → Rd d) : ℝ≥0∞ := ∫⁻ x, ‖gf x‖ₑ ^ 2

/-- `N(f) = ‖f‖₂^{1-α/4} ‖∇f‖₂^{α/4}` of `P:spatial-four-linear` (line 221), with
`‖f‖₂ = (∫ f²)^{1/2}` and `‖∇f‖₂ = (∫ ‖gf‖²)^{1/2}` for a weak gradient `gf` of `f` (genuine
Bochner integrals when `f, gf ∈ L²`, which is how it is used). -/
def Nnorm (alpha : ℝ) (f : Rd d → ℝ) (gf : Rd d → Rd d) : ℝ :=
  Real.sqrt (∫ x, f x ^ 2) ^ (1 - alpha / 4) * Real.sqrt (∫ x, ‖gf x‖ ^ 2) ^ (alpha / 4)

/-- SUPPLIED INPUT (named hypothesis): two conclusions of `P:spatial-four-linear`
(`integrated_spatial_occupation.tex` lines 219-237, proved in parallel by wave item L7-d), for
real `f, h ∈ H¹(ℝ^d)` given as `f ∈ L²` with an `L²` weak gradient `gf`
(`WeakSobolev.MemH1` with the gradient named):
* `homogeneous`: `E:spatial-homogeneous-bound` (line 224), `A_sp(f) ≤ R N(f)⁴`, read as an
  inequality in `[0,∞]` (so it includes the finiteness of `A_sp(f)`, line 222);
* `squareCS`: `E:spatial-square-CS` (lines 225-227),
  `0 ≤ B_Γ(f²,h²) ≤ √(A_sp(f) A_sp(h))`, in the equivalent squared form
  `B_Γ(f²,h²)² ≤ A_sp(f) A_sp(h)` in `[0,∞]` (`0 ≤` is automatic there; squaring is an order
  isomorphism of `[0,∞]`).  `squareCS_of_sqrt` derives it from the real `√` form.
The manuscript has `R = R_0` (`SpatialSmoothRatio.R0`); the `_paper` wrapper uses exactly that. -/
structure SquarePairingBounds (Γ : Measure (Rd d)) (alpha R : ℝ) : Prop where
  homogeneous : ∀ (f : Rd d → ℝ) (gf : Rd d → Rd d), MemLp f 2 volume → MemLp gf 2 volume →
    HasWeakGradient f gf → sqPair Γ f f ≤ ENNReal.ofReal (R * Nnorm alpha f gf ^ 4)
  squareCS : ∀ (f : Rd d → ℝ) (gf : Rd d → Rd d) (h : Rd d → ℝ) (gh : Rd d → Rd d),
    MemLp f 2 volume → MemLp gf 2 volume → HasWeakGradient f gf →
    MemLp h 2 volume → MemLp gh 2 volume → HasWeakGradient h gh →
    sqPair Γ f h ^ 2 ≤ sqPair Γ f f * sqPair Γ h h

/-- `T(g) = ∫_0^1 b(g_s) ds` (lines 382-383) as an extended integral of `gradSqE`. -/
def Tlin (DG : ℝ → Rd d → Rd d) : ℝ≥0∞ := ∫⁻ s, gradSqE (DG s) ∂volI

/-- The class `𝒪` (TeX lines 381-384), modelled through joint representatives: a field
`s ↦ g_s` is given by `G : ℝ → ℝ^d → ℝ` (`g_s = G s`) and a gradient field `DG`
(`∇g_s = DG s`) such that
* `(s,x) ↦ G s x` and `(s,x) ↦ DG s x` are a.e.-strongly measurable for Lebesgue measure on
  `(0,1) × ℝ^d` (this replaces "strongly `H¹`-measurable": the TeX proof, lines 409-414, derives
  such joint representatives from strong measurability; that derivation is not formalized);
* for a.e. `s ∈ (0,1)`, `(G s, DG s)` is a unit `H¹` pair (`SpatialStaticControls.IsUnitH1`:
  `G s ∈ L²`, `DG s ∈ L²` a weak gradient of `G s`, `‖G s‖₂ = 1`);
* `T(g) < ∞`.
No time smoothness, common support or optimizer condition is imposed (line 384). -/
structure IsOccField (G : ℝ → Rd d → ℝ) (DG : ℝ → Rd d → Rd d) : Prop where
  meas : AEStronglyMeasurable (fun p : ℝ × Rd d => G p.1 p.2) (volI.prod volume)
  meas_grad : AEStronglyMeasurable (fun p : ℝ × Rd d => DG p.1 p.2) (volI.prod volume)
  unit : ∀ᵐ s ∂volI, IsUnitH1 (G s) (DG s)
  energy_lt_top : Tlin DG < ⊤

/-- `J(g) = ∫_0^1 ∫_0^1 K_⋆(s-t) B_Γ(g_s², g_t²)` (TeX lines 390-393) as an iterated extended
nonnegative integral ("positive Tonelli is valid before finiteness is known", line 428).
`occupation_physical_bound` shows it is finite and equal to the Bochner integral over
`(0,1)²`. -/
def Jlin (a D : ℝ) (Γ : Measure (Rd d)) (G : ℝ → Rd d → ℝ) : ℝ≥0∞ :=
  ∫⁻ s, ∫⁻ t, ENNReal.ofReal (Kstar a D (s - t)) * sqPair Γ (G s) (G t) ∂volI ∂volI

/-- Auxiliary to the Lean proof route: the real `√` form of `E:spatial-square-CS` gives the
squared `[0,∞]` form used in `SquarePairingBounds.squareCS` (for finite values). -/
theorem squareCS_of_sqrt {X A B : ℝ≥0∞} (hX : X ≠ ⊤) (hA : A ≠ ⊤) (hB : B ≠ ⊤)
    (h : X.toReal ≤ Real.sqrt (A.toReal * B.toReal)) : X ^ 2 ≤ A * B := by
  have h2 : X.toReal ^ 2 ≤ A.toReal * B.toReal := by
    calc X.toReal ^ 2 ≤ Real.sqrt (A.toReal * B.toReal) ^ 2 :=
          pow_le_pow_left₀ ENNReal.toReal_nonneg h 2
      _ = A.toReal * B.toReal := Real.sq_sqrt (by positivity)
  rw [← ENNReal.ofReal_toReal hX, ← ENNReal.ofReal_toReal hA, ← ENNReal.ofReal_toReal hB,
    ← ENNReal.ofReal_pow ENNReal.toReal_nonneg, ← ENNReal.ofReal_mul ENNReal.toReal_nonneg]
  exact ENNReal.ofReal_le_ofReal h2

/-- Auxiliary to the Lean proof route: a property holding at a.e. time in `(0,1)` holds a.e. on
`(0,1)²` at both coordinates. -/
theorem ae_prod_both {P : ℝ → Prop} (h : ∀ᵐ s ∂volI, P s) :
    ∀ᵐ p ∂(volI.prod volI), P p.1 ∧ P p.2 :=
  ((Measure.quasiMeasurePreserving_fst (μ := volI) (ν := volI)).ae h).and
    ((Measure.quasiMeasurePreserving_snd (μ := volI) (ν := volI)).ae h)

/-- Auxiliary to the Lean proof route: `B_Γ(f², h²)` is unchanged when `f`, `h` are replaced
by Lebesgue-a.e. equal functions (`Γ` locally finite; from `L:spatial-physical-pair`,
`OccupationKernelRow.spatial_physical_pair`). -/
theorem sqPair_congr (Γ : Measure (Rd d)) [IsLocallyFiniteMeasure Γ] {f f' h h' : Rd d → ℝ}
    (hf : f =ᵐ[volume] f') (hh : h =ᵐ[volume] h') : sqPair Γ f h = sqPair Γ f' h' := by
  unfold sqPair
  refine (OccupationKernelRow.spatial_physical_pair Γ).2.1 _ _ _ _ ?_ ?_
  · filter_upwards [hf] with x hx; rw [hx]
  · filter_upwards [hh] with x hx; rw [hx]

/-- Measurability of the pairings (TeX lines 388, 407-419): for a locally finite `Γ` and a field
with an a.e.-strongly measurable joint representative `(s,x) ↦ G s x` on `(0,1) × ℝ^d`,
`(s,t) ↦ B_Γ(G_s², G_t²)` (the physical integral itself) is a.e.-measurable on `(0,1)²`.
Route: Tonelli on the joint representative and representative independence (not the
continuity of the pairing map on `H¹ × H¹` used by the TeX). -/
theorem sqPair_aemeasurable (Γ : Measure (Rd d)) [IsLocallyFiniteMeasure Γ]
    {G : ℝ → Rd d → ℝ}
    (hG : AEStronglyMeasurable (fun p : ℝ × Rd d => G p.1 p.2) (volI.prod volume)) :
    AEMeasurable (fun p : ℝ × ℝ => sqPair Γ (G p.1) (G p.2)) (volI.prod volI) := by
  set Gm : ℝ × Rd d → ℝ := hG.mk _ with hGm
  have hGmm : Measurable (fun p : ℝ × Rd d => Gm p) := hG.stronglyMeasurable_mk.measurable
  have hae : ∀ᵐ s ∂volI, G s =ᵐ[volume] fun x => Gm (s, x) :=
    Measure.ae_ae_of_ae_prod hG.ae_eq_mk
  have hmeas : Measurable fun p : ℝ × ℝ =>
      sqPair Γ (fun x => Gm (p.1, x)) (fun x => Gm (p.2, x)) := by
    have hF : Measurable fun q : (ℝ × ℝ) × (Rd d × Rd d) =>
        ENNReal.ofReal (Gm (q.1.1, q.2.1) ^ 2) *
          ENNReal.ofReal (Gm (q.1.2, q.2.1 - q.2.2) ^ 2) := by
      have h1 : Measurable fun q : (ℝ × ℝ) × (Rd d × Rd d) => Gm (q.1.1, q.2.1) :=
        hGmm.comp (measurable_fst.fst.prodMk measurable_snd.fst)
      have h2 : Measurable fun q : (ℝ × ℝ) × (Rd d × Rd d) => Gm (q.1.2, q.2.1 - q.2.2) :=
        hGmm.comp (measurable_fst.snd.prodMk (measurable_snd.fst.sub measurable_snd.snd))
      exact (ENNReal.measurable_ofReal.comp (h1.pow_const 2)).mul
        (ENNReal.measurable_ofReal.comp (h2.pow_const 2))
    unfold sqPair pairing
    exact hF.lintegral_prod_right'
  refine ⟨_, hmeas, ?_⟩
  filter_upwards [ae_prod_both hae] with p hp
  exact sqPair_congr Γ hp.1 hp.2


/-- Auxiliary to the Lean proof route: for `gf ∈ L²`, `‖gf‖²` is integrable and
`gradSqE gf = ofReal (∫ ‖gf‖²)`. -/
theorem gradSqE_eq {gf : Rd d → Rd d} (hg : MemLp gf 2 volume) :
    Integrable (fun x => ‖gf x‖ ^ 2) volume ∧
      gradSqE gf = ENNReal.ofReal (∫ x, ‖gf x‖ ^ 2) := by
  have hi : Integrable (fun x => ‖gf x‖ ^ 2) volume := by
    have := hg.integrable_norm_pow (by norm_num)
    simpa using this
  refine ⟨hi, ?_⟩
  rw [ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall fun x => by positivity)]
  unfold gradSqE
  congr 1; funext x
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

/-- Auxiliary to the Lean proof route: the supplied homogeneous bound at a unit `H¹` pair
(`‖g‖₂ = 1`, so `N(g)⁴ = b(g)^{α/2}`): `A_sp(g) ≤ R b(g)^{α/2}` (`R ≥ 0`, `α ≥ 0`). -/
theorem sqPair_self_le {Γ : Measure (Rd d)} {alpha R : ℝ} (hR : 0 ≤ R) (ha : 0 ≤ alpha)
    (hB : SquarePairingBounds Γ alpha R) {f : Rd d → ℝ} {gf : Rd d → Rd d}
    (hu : IsUnitH1 f gf) :
    sqPair Γ f f ≤ ENNReal.ofReal R * gradSqE gf ^ (alpha / 2) := by
  obtain ⟨hf, hg, hw, h1⟩ := hu
  have h := hB.homogeneous f gf hf hg hw
  obtain ⟨-, he⟩ := gradSqE_eq hg
  set b := ∫ x, ‖gf x‖ ^ 2 with hb
  have hb0 : 0 ≤ b := integral_nonneg fun x => by positivity
  have hN : Nnorm alpha f gf ^ 4 = b ^ (alpha / 2) := by
    unfold Nnorm
    rw [h1, ← hb, Real.sqrt_one, Real.one_rpow, one_mul, ← Real.rpow_natCast,
      ← Real.rpow_mul (Real.sqrt_nonneg _), Real.sqrt_eq_rpow, ← Real.rpow_mul hb0]
    congr 1; push_cast; ring
  rw [hN, ENNReal.ofReal_mul hR, ← ENNReal.ofReal_rpow_of_nonneg hb0 (by linarith), ← he] at h
  exact h

/-- Auxiliary to the Lean proof route, combining the TeX steps of lines 421-426 at one pair of
times: for unit `H¹` pairs, `B_Γ(f², h²) ≤ (R/2)(b(f)^{α/2} + b(h)^{α/2})` (the supplied
homogeneous and square Cauchy-Schwarz bounds, then `2xy ≤ x² + y²`; `R ≥ 0`, `α ≥ 0`). -/
theorem sqPair_le_half {Γ : Measure (Rd d)} {alpha R : ℝ} (hR : 0 ≤ R) (ha : 0 ≤ alpha)
    (hB : SquarePairingBounds Γ alpha R) {f h : Rd d → ℝ} {gf gh : Rd d → Rd d}
    (hf : IsUnitH1 f gf) (hh : IsUnitH1 h gh) :
    sqPair Γ f h ≤
      ENNReal.ofReal (R / 2) * (gradSqE gf ^ (alpha / 2) + gradSqE gh ^ (alpha / 2)) := by
  have hA := sqPair_self_le hR ha hB hf
  have hC := sqPair_self_le hR ha hB hh
  have hX := hB.squareCS f gf h gh hf.1 hf.2.1 hf.2.2.1 hh.1 hh.2.1 hh.2.2.1
  have hfin : ∀ {u : Rd d → ℝ} {gu : Rd d → Rd d}, IsUnitH1 u gu →
      gradSqE gu ^ (alpha / 2) ≠ ⊤ := by
    intro u gu hu
    rw [(gradSqE_eq hu.2.1).2]
    exact (ENNReal.rpow_lt_top_of_nonneg (by linarith) ENNReal.ofReal_ne_top).ne
  set u := gradSqE gf ^ (alpha / 2)
  set v := gradSqE gh ^ (alpha / 2)
  have hu : u ≠ ⊤ := hfin hf
  have hv : v ≠ ⊤ := hfin hh
  have hAt : sqPair Γ f f ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hu) hA
  have hCt : sqPair Γ h h ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hv) hC
  have hXt : sqPair Γ f h ≠ ⊤ := by
    intro hx
    rw [hx] at hX
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, ENNReal.top_pow, top_le_iff] at hX
    exact ENNReal.mul_ne_top hAt hCt hX
  -- pass to real numbers
  have hX' : (sqPair Γ f h).toReal ^ 2 ≤ (sqPair Γ f f).toReal * (sqPair Γ h h).toReal := by
    rw [← ENNReal.toReal_pow, ← ENNReal.toReal_mul]
    exact ENNReal.toReal_mono (ENNReal.mul_ne_top hAt hCt) hX
  have hA' : (sqPair Γ f f).toReal ≤ R * u.toReal := by
    have := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hu) hA
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hR] at this
  have hC' : (sqPair Γ h h).toReal ≤ R * v.toReal := by
    have := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hv) hC
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hR] at this
  have hx0 : 0 ≤ (sqPair Γ f h).toReal := ENNReal.toReal_nonneg
  have hA0 : 0 ≤ (sqPair Γ f f).toReal := ENNReal.toReal_nonneg
  have hC0 : 0 ≤ (sqPair Γ h h).toReal := ENNReal.toReal_nonneg
  have hu0 : 0 ≤ u.toReal := ENNReal.toReal_nonneg
  have hv0 : 0 ≤ v.toReal := ENNReal.toReal_nonneg
  have key : (sqPair Γ f h).toReal ≤ R / 2 * (u.toReal + v.toReal) := by
    have h1 : (sqPair Γ f h).toReal ^ 2 ≤ (R * u.toReal) * (R * v.toReal) :=
      hX'.trans (mul_le_mul hA' hC' hC0 (by positivity))
    nlinarith [sq_nonneg (R * u.toReal - R * v.toReal), mul_nonneg hR hu0, mul_nonneg hR hv0]
  calc sqPair Γ f h = ENNReal.ofReal (sqPair Γ f h).toReal := (ENNReal.ofReal_toReal hXt).symm
    _ ≤ ENNReal.ofReal (R / 2 * (u.toReal + v.toReal)) := ENNReal.ofReal_le_ofReal key
    _ = ENNReal.ofReal (R / 2) * (u + v) := by
      rw [ENNReal.ofReal_mul (by linarith), ENNReal.ofReal_add hu0 hv0,
        ENNReal.ofReal_toReal hu, ENNReal.ofReal_toReal hv]


/-- Auxiliary to the Lean proof route: the row bound `E:occupation-kernel-row` as an extended
integral, `∫_0^1 K_⋆(s-t) dt ≤ R_⋆` for `s ∈ [0,1]` (`0 < a < 1`, `D > 0`). -/
theorem row_lintegral_le {a D : ℝ} (ha : 0 < a) (ha1 : a < 1) (hD : 0 < D) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) :
    ∫⁻ t, ENNReal.ofReal (Kstar a D (s - t)) ∂volI ≤ ENNReal.ofReal (Rstar a D) := by
  obtain ⟨-, -, -, -, -, hint, hmax, -, -⟩ :=
    OccupationKernelRow.occupation_kernel_row a D ha ha1 hD
  have hI := hint s hs
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one] at hI
  have hIoo : IntegrableOn (fun t => Kstar a D (s - t)) (Ioo 0 1) := hI.mono_set Ioo_subset_Ioc_self
  rw [← ofReal_integral_eq_lintegral_ofReal hIoo
    (Eventually.of_forall fun t => OccupationKernelRow.Kstar_nonneg a D _ ha hD)]
  refine ENNReal.ofReal_le_ofReal ?_
  have : ∫ t in Ioo (0 : ℝ) 1, Kstar a D (s - t) = row a D s := by
    rw [OccupationKernelRow.row, intervalIntegral.integral_of_le zero_le_one,
      integral_Ioc_eq_integral_Ioo]
  rw [this]
  exact hmax.2 ⟨s, hs, rfl⟩

/-- Auxiliary to the Lean proof route: the column bound `∫_0^1 K_⋆(s-t) ds ≤ R_⋆` for
`t ∈ [0,1]` (evenness of `K_⋆`, TeX lines 426-427; `0 < a < 1`, `D > 0`). -/
theorem col_lintegral_le {a D : ℝ} (ha : 0 < a) (ha1 : a < 1) (hD : 0 < D) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) :
    ∫⁻ s, ENNReal.ofReal (Kstar a D (s - t)) ∂volI ≤ ENNReal.ofReal (Rstar a D) := by
  have : (fun s => ENNReal.ofReal (Kstar a D (s - t))) =
      fun s => ENNReal.ofReal (Kstar a D (t - s)) := by
    funext s; rw [← OccupationKernelRow.Kstar_neg a D (s - t), neg_sub]
  rw [this]
  exact row_lintegral_le ha ha1 hD ht

/-- Auxiliary to the Lean proof route (the TeX's concavity step, lines 423-425, proved by
Hölder with exponents `1/p`, `1/(1-p)`): `∫_0^1 f^p ≤ (∫_0^1 f)^p` for `0 < p < 1` and an
a.e.-measurable `f : ℝ → [0,∞]`. -/
theorem lintegral_rpow_le {f : ℝ → ℝ≥0∞} (hf : AEMeasurable f volI) {p : ℝ} (hp : 0 < p)
    (hp1 : p < 1) : ∫⁻ s, f s ^ p ∂volI ≤ (∫⁻ s, f s ∂volI) ^ p := by
  have hpq : (1 / p).HolderConjugate (1 / (1 - p)) := by
    rw [Real.holderConjugate_iff]
    refine ⟨?_, ?_⟩
    · rw [lt_div_iff₀ hp]; linarith
    · field_simp; ring
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq volI hpq (hf.pow_const p) aemeasurable_const
    (g := fun _ => (1 : ℝ≥0∞))
  have e1 : ∀ s, (f s ^ p) ^ (1 / p) = f s := by
    intro s; rw [← ENNReal.rpow_mul, mul_one_div_cancel hp.ne', ENNReal.rpow_one]
  have hvol : volI (univ : Set ℝ) = 1 := by
    rw [Measure.restrict_apply MeasurableSet.univ, univ_inter, Real.volume_Ioo]; simp
  simp only [Pi.mul_apply, mul_one, e1, ENNReal.one_rpow, lintegral_const, hvol,
    one_div_one_div] at h
  simpa using h


/-- Auxiliary to the Lean proof route: for an a.e.-strongly measurable joint gradient field,
`s ↦ b(g_s)` (`gradSqE`) is a.e.-measurable on `(0,1)` (TeX line 407). -/
theorem gradSqE_aemeasurable {DG : ℝ → Rd d → Rd d}
    (hm : AEStronglyMeasurable (fun p : ℝ × Rd d => DG p.1 p.2) (volI.prod volume)) :
    AEMeasurable (fun s => gradSqE (DG s)) volI := by
  have h : AEMeasurable (fun p : ℝ × Rd d => ‖DG p.1 p.2‖ₑ ^ 2) (volI.prod volume) :=
    hm.enorm.pow_const 2
  exact h.lintegral_prod_right'

/-- `E:occupation-physical-bound` (TeX lines 394-397) for the extended integral:
`J(g) ≤ R_⋆ R T(g)^{α/2}` for every field of `𝒪`, given the supplied bounds
`SquarePairingBounds Γ α R` with `R ≥ 0`, `0 < a < 1`, `D > 0`, `0 < α < 2` (any measure `Γ`). -/
theorem Jlin_le {a D alpha R : ℝ} (ha : 0 < a) (ha1 : a < 1) (hD : 0 < D)
    (hal : 0 < alpha) (hal2 : alpha < 2) (hR : 0 ≤ R)
    {Γ : Measure (Rd d)} (hB : SquarePairingBounds Γ alpha R)
    {G : ℝ → Rd d → ℝ} {DG : ℝ → Rd d → Rd d} (hO : IsOccField G DG) :
    Jlin a D Γ G ≤ ENNReal.ofReal (Rstar a D * R * (Tlin DG).toReal ^ (alpha / 2)) := by
  set p := alpha / 2 with hp
  set β : ℝ → ℝ≥0∞ := fun s => gradSqE (DG s) ^ p with hβ
  set c : ℝ≥0∞ := ENNReal.ofReal (R / 2) with hc
  set Rs : ℝ≥0∞ := ENNReal.ofReal (Rstar a D) with hRs
  set k : ℝ → ℝ → ℝ≥0∞ := fun s t => ENNReal.ofReal (Kstar a D (s - t)) with hk
  have hkm : Measurable fun q : ℝ × ℝ => k q.1 q.2 :=
    ENNReal.measurable_ofReal.comp
      ((OccupationKernelRow.Kstar_measurable a D).comp (measurable_fst.sub measurable_snd))
  have hkt : ∀ s, Measurable fun t => k s t := fun s =>
    ENNReal.measurable_ofReal.comp
      ((OccupationKernelRow.Kstar_measurable a D).comp (measurable_const.sub measurable_id))
  have hks : ∀ t, Measurable fun s => k s t := fun t =>
    ENNReal.measurable_ofReal.comp
      ((OccupationKernelRow.Kstar_measurable a D).comp (measurable_id.sub measurable_const))
  have hβm : AEMeasurable β volI := (gradSqE_aemeasurable hO.meas_grad).pow_const p
  have hF : AEMeasurable (fun q : ℝ × ℝ => k q.1 q.2 * β q.1) (volI.prod volI) :=
    hkm.aemeasurable.mul (hβm.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst)
  have hH : AEMeasurable (fun q : ℝ × ℝ => k q.1 q.2 * β q.2) (volI.prod volI) :=
    hkm.aemeasurable.mul (hβm.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd)
  have hIcc : ∀ᵐ s ∂volI, s ∈ Icc (0 : ℝ) 1 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs using Ioo_subset_Icc_self hs
  -- step 1: the pointwise bound
  have step1 : Jlin a D Γ G ≤ ∫⁻ s, ∫⁻ t, c * (k s t * β s) + c * (k s t * β t) ∂volI ∂volI := by
    unfold Jlin
    refine lintegral_mono_ae ?_
    filter_upwards [hO.unit] with s hs
    refine lintegral_mono_ae ?_
    filter_upwards [hO.unit] with t ht
    have := sqPair_le_half hR hal.le hB hs ht
    calc k s t * sqPair Γ (G s) (G t) ≤ k s t * (c * (β s + β t)) := by gcongr
      _ = c * (k s t * β s) + c * (k s t * β t) := by ring
  -- step 2: split
  have hI1 : ∀ s, ∫⁻ t, k s t * β s ∂volI = (∫⁻ t, k s t ∂volI) * β s := fun s =>
    lintegral_mul_const _ (hkt s)
  have step2 : ∫⁻ s, ∫⁻ t, c * (k s t * β s) + c * (k s t * β t) ∂volI ∂volI =
      c * ∫⁻ s, ∫⁻ t, k s t * β s ∂volI ∂volI + c * ∫⁻ s, ∫⁻ t, k s t * β t ∂volI ∂volI := by
    have e : ∀ s, ∫⁻ t, c * (k s t * β s) + c * (k s t * β t) ∂volI =
        c * ∫⁻ t, k s t * β s ∂volI + c * ∫⁻ t, k s t * β t ∂volI := by
      intro s
      rw [lintegral_add_left' (((hkt s).mul_const _).const_mul c).aemeasurable,
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    simp_rw [e]
    rw [lintegral_add_left' (hF.lintegral_prod_right'.const_mul c),
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  -- step 3: row and column bounds
  have row1 : ∫⁻ s, ∫⁻ t, k s t * β s ∂volI ∂volI ≤ Rs * ∫⁻ s, β s ∂volI := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono_ae ?_
    filter_upwards [hIcc] with s hs
    rw [hI1 s]
    gcongr; exact row_lintegral_le ha ha1 hD hs
  have col1 : ∫⁻ s, ∫⁻ t, k s t * β t ∂volI ∂volI ≤ Rs * ∫⁻ s, β s ∂volI := by
    rw [lintegral_lintegral_swap hH, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono_ae ?_
    filter_upwards [hIcc] with t ht
    rw [lintegral_mul_const _ (hks t)]
    gcongr; exact col_lintegral_le ha ha1 hD ht
  -- step 4: Jensen
  have hJ : ∫⁻ s, β s ∂volI ≤ Tlin DG ^ p :=
    lintegral_rpow_le (gradSqE_aemeasurable hO.meas_grad) (by positivity) (by linarith)
  have hT : Tlin DG ^ p = ENNReal.ofReal ((Tlin DG).toReal ^ p) := by
    rw [← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg (by positivity),
      ENNReal.ofReal_toReal hO.energy_lt_top.ne]
  have hRst : 0 ≤ Rstar a D :=
    (OccupationKernelRow.occupation_kernel_row a D ha ha1 hD).2.2.2.2.2.2.2.2.le
  have hcc : c + c = ENNReal.ofReal R := by
    rw [hc, ← ENNReal.ofReal_add (by linarith) (by linarith)]; congr 1; ring
  calc Jlin a D Γ G ≤ _ := step1
    _ = _ := step2
    _ ≤ c * (Rs * ∫⁻ s, β s ∂volI) + c * (Rs * ∫⁻ s, β s ∂volI) := by
      gcongr
    _ = ENNReal.ofReal R * Rs * ∫⁻ s, β s ∂volI := by rw [← hcc]; ring
    _ ≤ ENNReal.ofReal R * Rs * Tlin DG ^ p := by gcongr
    _ = ENNReal.ofReal (Rstar a D * R * (Tlin DG).toReal ^ p) := by
      rw [hT, hRs, ← ENNReal.ofReal_mul hR, ← ENNReal.ofReal_mul (by positivity)]
      congr 1; ring


/-- Representative independence (TeX lines 388-389, 415-416, 428-429): for a locally finite `Γ`,
if `G' s = G s` Lebesgue-a.e. in space for a.e. `s ∈ (0,1)`, the pairings agree a.e. on
`(0,1)²` and `J` is unchanged (this covers changes of spatial versions and null-time
modifications). -/
theorem sqPair_Jlin_congr (a D : ℝ) (Γ : Measure (Rd d)) [IsLocallyFiniteMeasure Γ]
    {G G' : ℝ → Rd d → ℝ} (h : ∀ᵐ s ∂volI, G s =ᵐ[volume] G' s) :
    (fun p : ℝ × ℝ => sqPair Γ (G p.1) (G p.2)) =ᵐ[volI.prod volI]
        (fun p : ℝ × ℝ => sqPair Γ (G' p.1) (G' p.2)) ∧
      Jlin a D Γ G = Jlin a D Γ G' := by
  refine ⟨?_, ?_⟩
  · filter_upwards [ae_prod_both h] with p hp
    exact sqPair_congr Γ hp.1 hp.2
  · unfold Jlin
    refine lintegral_congr_ae ?_
    filter_upwards [h] with s hs
    refine lintegral_congr_ae ?_
    filter_upwards [h] with t ht
    rw [sqPair_congr Γ hs ht]

/-- Auxiliary to the Lean proof route: `T(g)` is unchanged when the gradient field is changed
Lebesgue-a.e. in space at a.e. time. -/
theorem Tlin_congr {DG DG' : ℝ → Rd d → Rd d} (h : ∀ᵐ s ∂volI, DG s =ᵐ[volume] DG' s) :
    Tlin DG = Tlin DG' := by
  unfold Tlin gradSqE
  refine lintegral_congr_ae ?_
  filter_upwards [h] with s hs
  refine lintegral_congr_ae ?_
  filter_upwards [hs] with x hx
  rw [hx]

/-- Auxiliary to the Lean proof route: `T(g)` depends only on `G` (two gradient fields that are
`L²` weak gradients of `G s` at a.e. time give the same `T`, by
`WeakSobolev.weakGradient_ae_unique`). -/
theorem Tlin_unique {G : ℝ → Rd d → ℝ} {DG DG' : ℝ → Rd d → Rd d}
    (h : ∀ᵐ s ∂volI, IsUnitH1 (G s) (DG s)) (h' : ∀ᵐ s ∂volI, IsUnitH1 (G s) (DG' s)) :
    Tlin DG = Tlin DG' := by
  refine Tlin_congr ?_
  filter_upwards [h, h'] with s hs hs'
  exact WeakSobolev.weakGradient_ae_unique hs.2.2.1 hs'.2.2.1 hs.2.1 hs'.2.1

/-- The real value `J(g)` (finite on `𝒪`: `occupation_physical_bound`). -/
def J (a D : ℝ) (Γ : Measure (Rd d)) (G : ℝ → Rd d → ℝ) : ℝ := (Jlin a D Γ G).toReal

/-- The real value `T(g)` (finite on `𝒪` by definition of the class). -/
def T (DG : ℝ → Rd d → Rd d) : ℝ := (Tlin DG).toReal

/-- For a field of `𝒪`, `s ↦ b(g_s) = ∫ ‖∇g_s‖²` (real Bochner integrals) is integrable on
`(0,1)` and its integral is `T(g)` (TeX lines 382-383, 407-408). -/
theorem T_eq_integral {G : ℝ → Rd d → ℝ} {DG : ℝ → Rd d → Rd d} (hO : IsOccField G DG) :
    Integrable (fun s => ∫ x, ‖DG s x‖ ^ 2) volI ∧ ∫ s, (∫ x, ‖DG s x‖ ^ 2) ∂volI = T DG := by
  have hm := gradSqE_aemeasurable hO.meas_grad
  have hfin : ∀ᵐ s ∂volI, gradSqE (DG s) < ⊤ := by
    filter_upwards [hO.unit] with s hs
    rw [(gradSqE_eq hs.2.1).2]; exact ENNReal.ofReal_lt_top
  have heq : (fun s => (gradSqE (DG s)).toReal) =ᵐ[volI] fun s => ∫ x, ‖DG s x‖ ^ 2 := by
    filter_upwards [hO.unit] with s hs
    rw [(gradSqE_eq hs.2.1).2, ENNReal.toReal_ofReal (integral_nonneg fun x => by positivity)]
  refine ⟨(integrable_toReal_of_lintegral_ne_top hm hO.energy_lt_top.ne).congr heq, ?_⟩
  rw [← integral_congr_ae heq, integral_toReal hm hfin]
  rfl


/-- `E:occupation-physical-bound` (TeX lines 394-397), general form: for `0 < a < 1`, `D > 0`,
`0 < α < 2`, a locally finite `Γ`, the supplied `SquarePairingBounds Γ α R` with `R ≥ 0`, and
a field of `𝒪`: the pairings are a.e.-measurable on `(0,1)²`, `J(g) ≤ R_⋆ R T(g)^{α/2}` and
`J(g) < ∞` as extended integrals, the real integrand `K_⋆(s-t) B_Γ(g_s², g_t²)` is integrable
on `(0,1)²` with integral `J(g)`, and `0 ≤ J(g) ≤ R_⋆ R T(g)^{α/2}`. -/
theorem occupation_physical_bound {a D alpha R : ℝ} (ha : 0 < a) (ha1 : a < 1) (hD : 0 < D)
    (hal : 0 < alpha) (hal2 : alpha < 2) (hR : 0 ≤ R)
    {Γ : Measure (Rd d)} [IsLocallyFiniteMeasure Γ] (hB : SquarePairingBounds Γ alpha R)
    {G : ℝ → Rd d → ℝ} {DG : ℝ → Rd d → Rd d} (hO : IsOccField G DG) :
    AEMeasurable (fun p : ℝ × ℝ => sqPair Γ (G p.1) (G p.2)) (volI.prod volI) ∧
    Jlin a D Γ G ≤ ENNReal.ofReal (Rstar a D * R * T DG ^ (alpha / 2)) ∧
    Jlin a D Γ G < ⊤ ∧
    Integrable (fun p : ℝ × ℝ => Kstar a D (p.1 - p.2) * (sqPair Γ (G p.1) (G p.2)).toReal)
      (volI.prod volI) ∧
    ∫ p, Kstar a D (p.1 - p.2) * (sqPair Γ (G p.1) (G p.2)).toReal ∂(volI.prod volI) =
      J a D Γ G ∧
    0 ≤ J a D Γ G ∧ J a D Γ G ≤ Rstar a D * R * T DG ^ (alpha / 2) := by
  have hP := sqPair_aemeasurable Γ hO.meas
  have hle := Jlin_le ha ha1 hD hal hal2 hR hB hO
  have hfin : Jlin a D Γ G < ⊤ := lt_of_le_of_lt hle ENNReal.ofReal_lt_top
  have hkm : Measurable fun q : ℝ × ℝ => ENNReal.ofReal (Kstar a D (q.1 - q.2)) :=
    ENNReal.measurable_ofReal.comp
      ((OccupationKernelRow.Kstar_measurable a D).comp (measurable_fst.sub measurable_snd))
  have hF : AEMeasurable (fun q : ℝ × ℝ =>
      ENNReal.ofReal (Kstar a D (q.1 - q.2)) * sqPair Γ (G q.1) (G q.2)) (volI.prod volI) :=
    hkm.aemeasurable.mul hP
  have hprod : Jlin a D Γ G = ∫⁻ q, ENNReal.ofReal (Kstar a D (q.1 - q.2)) *
      sqPair Γ (G q.1) (G q.2) ∂(volI.prod volI) := by
    rw [lintegral_prod _ hF]; rfl
  have hPfin : ∀ᵐ q ∂(volI.prod volI),
      ENNReal.ofReal (Kstar a D (q.1 - q.2)) * sqPair Γ (G q.1) (G q.2) < ⊤ := by
    filter_upwards [ae_prod_both hO.unit] with q hq
    refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (lt_of_le_of_lt (sqPair_le_half hR hal.le hB hq.1 hq.2) ?_)
    refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.add_lt_top.2 ⟨?_, ?_⟩)
    · rw [(gradSqE_eq hq.1.2.1).2]
      exact ENNReal.rpow_lt_top_of_nonneg (by linarith) ENNReal.ofReal_ne_top
    · rw [(gradSqE_eq hq.2.2.1).2]
      exact ENNReal.rpow_lt_top_of_nonneg (by linarith) ENNReal.ofReal_ne_top
  have htr : (fun q : ℝ × ℝ => (ENNReal.ofReal (Kstar a D (q.1 - q.2)) *
      sqPair Γ (G q.1) (G q.2)).toReal) =
      fun q => Kstar a D (q.1 - q.2) * (sqPair Γ (G q.1) (G q.2)).toReal := by
    funext q
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (OccupationKernelRow.Kstar_nonneg a D _ ha hD)]
  have hint := integrable_toReal_of_lintegral_ne_top hF (hprod ▸ hfin.ne)
  rw [htr] at hint
  have hJ0 : 0 ≤ J a D Γ G := ENNReal.toReal_nonneg
  have hRst : 0 ≤ Rstar a D :=
    (OccupationKernelRow.occupation_kernel_row a D ha ha1 hD).2.2.2.2.2.2.2.2.le
  refine ⟨hP, hle, hfin, hint, ?_, hJ0, ?_⟩
  · rw [← htr, integral_toReal hF hPfin, ← hprod]; rfl
  · have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hle
    rwa [ENNReal.toReal_ofReal (by positivity)] at this


/-- The right side of `E:spatial-energy-map` (lines 309-314) with `R_sp` replaced by a real
`R`: `(2-α)/2 · α^{α/(2-α)} · R^{2/(2-α)}`. -/
def spEnergyVal (alpha R : ℝ) : ℝ :=
  (2 - alpha) / 2 * alpha ^ (alpha / (2 - alpha)) * R ^ (2 / (2 - alpha))

/-- The scalar maximum (TeX lines 431-433): for `c ≥ 0`, `T ≥ 0`, `0 < α < 2`,
`c T^{α/2} - T/2 ≤ (2-α)/2 · α^{α/(2-α)} · c^{2/(2-α)}`. -/
theorem scalar_max {alpha c T : ℝ} (hal : 0 < alpha) (hal2 : alpha < 2) (hc : 0 ≤ c)
    (hT : 0 ≤ T) : c * T ^ (alpha / 2) - T / 2 ≤ spEnergyVal alpha c := by
  set Y : ℝ := c ^ (2 / (2 - alpha)) * alpha ^ (alpha / (2 - alpha)) with hY
  have h2a : 0 < 2 - alpha := by linarith
  have hY0 : 0 ≤ Y := by positivity
  have hAM := Real.geom_mean_le_arith_mean2_weighted (w₁ := alpha / 2) (w₂ := 1 - alpha / 2)
    (p₁ := T / alpha) (p₂ := Y) (by positivity) (by linarith) (by positivity) hY0 (by ring)
  have e1 : (T / alpha) ^ (alpha / 2) = T ^ (alpha / 2) / alpha ^ (alpha / 2) :=
    Real.div_rpow hT hal.le _
  have e2 : Y ^ (1 - alpha / 2) = c * alpha ^ (alpha / 2) := by
    rw [hY, Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hc,
      ← Real.rpow_mul hal.le]
    have i1 : 2 / (2 - alpha) * (1 - alpha / 2) = 1 := by field_simp
    have i2 : alpha / (2 - alpha) * (1 - alpha / 2) = alpha / 2 := by field_simp
    rw [i1, i2, Real.rpow_one]
  rw [e1, e2] at hAM
  have hpos : 0 < alpha ^ (alpha / 2) := Real.rpow_pos_of_pos hal _
  have e3 : T ^ (alpha / 2) / alpha ^ (alpha / 2) * (c * alpha ^ (alpha / 2)) =
      c * T ^ (alpha / 2) := by field_simp
  rw [e3] at hAM
  have e4 : alpha / 2 * (T / alpha) = T / 2 := by field_simp
  rw [e4] at hAM
  have e5 : spEnergyVal alpha c = (1 - alpha / 2) * Y := by
    unfold spEnergyVal; rw [hY]; ring
  rw [e5]
  linarith


/-- Auxiliary to the Lean proof route: `K_⋆(1) ≤ K_⋆(s-t)` for distinct `s, t ∈ (0,1)`
(evenness and monotonicity of `K_⋆`; `a > 0`, `D > 0`). -/
theorem Kstar_one_le {a D : ℝ} (ha : 0 < a) (hD : 0 < D) {s t : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1)
    (ht : t ∈ Ioo (0 : ℝ) 1) (hst : t ≠ s) : Kstar a D 1 ≤ Kstar a D (s - t) := by
  have hu : s - t ≠ 0 := sub_ne_zero.2 (Ne.symm hst)
  have habs : Kstar a D (s - t) = Kstar a D |s - t| := by
    rcases le_or_gt 0 (s - t) with h | h
    · rw [abs_of_nonneg h]
    · rw [abs_of_neg h, OccupationKernelRow.Kstar_neg]
  rw [habs]
  have h1 : |s - t| ≤ 1 := by
    rw [abs_le]; constructor <;> linarith [hs.1, hs.2, ht.1, ht.2]
  exact (OccupationKernelRow.Kstar_strictAntiOn a D ha hD).antitoneOn
    (show (0 : ℝ) < |s - t| from abs_pos.2 hu) (show (0 : ℝ) < 1 from one_pos) h1

/-- Auxiliary to the Lean proof route: `(0,1)` has Lebesgue measure `1`. -/
theorem volI_univ : volI (univ : Set ℝ) = 1 := by
  rw [Measure.restrict_apply MeasurableSet.univ, univ_inter, Real.volume_Ioo]; simp

/-- Positivity step of the proof (TeX lines 434-439): for `0 < a < 1`, `D > 0`, `0 < α < 2`, a
locally finite `Γ ≠ 0` with the scaling `Γ(cA) = c^{d-α}Γ(A)` (`SetScaling`), and the supplied
bounds with `R ≥ 0` (used only for the finiteness of `J`), a constant-in-time dilated unit
compact profile `U_ℓ g` lies in `𝒪` and has `J - T/2 > 0`.  Route: the lower bound
`J ≥ K_⋆(1) ℓ^α A_sp(g)` and an explicit `ℓ`, instead of the TeX's exact value
`J_0 ℓ^α A_sp(g)`. -/
theorem exists_pos_member {a D alpha R : ℝ} (ha : 0 < a) (ha1 : a < 1) (hD : 0 < D)
    (hal : 0 < alpha) (hal2 : alpha < 2) (hR : 0 ≤ R)
    {Γ : Measure (Rd d)} [IsLocallyFiniteMeasure Γ] (hS : VariationalDilation.SetScaling alpha Γ)
    (hΓ : Γ ≠ 0) (hB : SquarePairingBounds Γ alpha R) :
    ∃ (G : ℝ → Rd d → ℝ) (DG : ℝ → Rd d → Rd d), IsOccField G DG ∧
      0 < J a D Γ G - T DG / 2 := by
  obtain ⟨g, hg⟩ := SpatialSmoothRatio.exists_unitTest d
  set A0 := SpatialFourierBound.spatialEnergy Γ g with hA0
  have hA0p : 0 < A0 := SpatialSmoothRatio.spatialEnergy_pos hS hΓ hg
  set b0 := SpatialFourierBound.gradEnergy g with hb0
  have hb00 : 0 ≤ b0 := integral_nonneg fun x => by positivity
  set K1 := Kstar a D 1 with hK1
  have hK1p : 0 < K1 := OccupationKernelRow.Kstar_pos a D 1 ha hD one_ne_zero
  have h2a : 0 < 2 - alpha := by linarith
  set ℓ := (K1 * A0 / (b0 + 1)) ^ (1 / (2 - alpha)) with hℓdef
  have hℓ : 0 < ℓ := Real.rpow_pos_of_pos (by positivity) _
  set gl := WeakSobolev.dilL2 ℓ g with hgldef
  have hgl : SpatialFourierBound.IsUnitTest gl := SpatialSmoothRatio.isUnitTest_dilL2 hℓ hg
  have hglt : WeakSobolev.IsTestFunction gl := ⟨hgl.1, hgl.2.1⟩
  -- the pairing of the constant profile
  have hsq : Continuous fun x => gl x ^ 2 := hgl.1.continuous.pow 2
  have hsqc : HasCompactSupport fun x => gl x ^ 2 :=
    hgl.2.1.comp_left (g := fun r : ℝ => r ^ 2) (by norm_num)
  have hP : sqPair Γ gl gl = ENNReal.ofReal (ℓ ^ alpha * A0) := by
    unfold sqPair
    rw [(SpatialStaticControls.pairing_eq_spatialPair hsq hsqc (fun x => sq_nonneg _) hsq hsqc
      (fun x => sq_nonneg _)).2.1]
    congr 1
    exact SpatialSmoothRatio.spatialEnergy_dilL2 hS hℓ hg.1.continuous hg.2.1
  -- the gradient energy
  have hgr : gradSqE (VariationalFloor.grad gl) = ENNReal.ofReal (ℓ ^ 2 * b0) := by
    have hu := SpatialStaticControls.isUnitH1_of_unitTest hgl
    rw [(gradSqE_eq hu.2.1).2]
    congr 1
    rw [hb0, ← SpatialSmoothRatio.gradEnergy_dilL2 hℓ (hg.1.differentiable (by simp))]
    unfold SpatialFourierBound.gradEnergy VariationalFloor.grad
    congr 1; funext x
    rw [LinearIsometryEquiv.norm_map]
  set G : ℝ → Rd d → ℝ := fun _ => gl with hG
  set DG : ℝ → Rd d → Rd d := fun _ => VariationalFloor.grad gl with hDG
  have hTl : Tlin DG = ENNReal.ofReal (ℓ ^ 2 * b0) := by
    unfold Tlin
    simp only [hDG, hgr, lintegral_const, volI_univ, mul_one]
  have hO : IsOccField G DG := by
    refine ⟨(hgl.1.continuous.comp continuous_snd).aestronglyMeasurable,
      ((VariationalFloor.continuous_grad hglt).comp continuous_snd).aestronglyMeasurable,
      Eventually.of_forall fun _ => SpatialStaticControls.isUnitH1_of_unitTest hgl, ?_⟩
    rw [hTl]; exact ENNReal.ofReal_lt_top
  refine ⟨G, DG, hO, ?_⟩
  -- lower bound on `J`
  have hJlow : ENNReal.ofReal (K1 * (ℓ ^ alpha * A0)) ≤ Jlin a D Γ G := by
    have hc : ∫⁻ s, ∫⁻ t, ENNReal.ofReal (K1 * (ℓ ^ alpha * A0)) ∂volI ∂volI =
        ENNReal.ofReal (K1 * (ℓ ^ alpha * A0)) := by
      simp only [lintegral_const, volI_univ, mul_one]
    rw [← hc]
    unfold Jlin
    refine lintegral_mono_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    refine lintegral_mono_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo,
      ae_restrict_of_ae (Measure.ae_ne volume s)] with t ht hts
    simp only [hG, hP]
    rw [← ENNReal.ofReal_mul (OccupationKernelRow.Kstar_nonneg a D _ ha hD)]
    exact ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (Kstar_one_le ha hD hs ht hts) (by positivity))
  have hfin := (occupation_physical_bound ha ha1 hD hal hal2 hR hB hO).2.2.1
  have hJ : K1 * (ℓ ^ alpha * A0) ≤ J a D Γ G := by
    have := ENNReal.toReal_mono hfin.ne hJlow
    rwa [ENNReal.toReal_ofReal (by positivity)] at this
  have hT : T DG = ℓ ^ 2 * b0 := by
    unfold T; rw [hTl, ENNReal.toReal_ofReal (by positivity)]
  rw [hT]
  -- the scalar inequality
  have hsplit : ℓ ^ 2 = ℓ ^ alpha * ℓ ^ (2 - alpha) := by
    rw [← Real.rpow_add hℓ, ← Real.rpow_natCast]; norm_num
  have hpow : ℓ ^ (2 - alpha) = K1 * A0 / (b0 + 1) := by
    rw [hℓdef, one_div, Real.rpow_inv_rpow (by positivity) h2a.ne']
  have hX : 0 < ℓ ^ alpha * (K1 * A0) := by positivity
  have key : ℓ ^ 2 * b0 / 2 < K1 * (ℓ ^ alpha * A0) := by
    rw [hsplit, hpow]
    have e : ℓ ^ alpha * (K1 * A0 / (b0 + 1)) * b0 / 2 =
        ℓ ^ alpha * (K1 * A0) * (b0 / (2 * (b0 + 1))) := by
      field_simp
    rw [e]
    have hlt : b0 / (2 * (b0 + 1)) < 1 := by
      rw [div_lt_one (by positivity)]; linarith
    nlinarith
  linarith


/-- The value set `{J(g) - T(g)/2 : g ∈ 𝒪}` of `E:occupation-own-energy` (line 401). -/
def energySet (a D : ℝ) (Γ : Measure (Rd d)) : Set ℝ :=
  {v | ∃ (G : ℝ → Rd d → ℝ) (DG : ℝ → Rd d → Rd d), IsOccField G DG ∧
    v = J a D Γ G - T DG / 2}

/-- `𝓔_⋆^𝒪 = sup_{g ∈ 𝒪} (J(g) - T(g)/2)` (TeX lines 399-401), as `sSup`; the statements below
prove the set nonempty and bounded above, so this is not Lean's junk value. -/
def EstarO (a D : ℝ) (Γ : Measure (Rd d)) : ℝ := sSup (energySet a D Γ)

/-- `E:occupation-own-energy` (TeX lines 398-403), general form: for `0 < a < 1`, `D > 0`,
`0 < α < 2`, a locally finite `Γ ≠ 0` with `SetScaling α Γ`, and the supplied
`SquarePairingBounds Γ α R` with `R ≥ 0`: the value set is nonempty and bounded above and
`0 < 𝓔_⋆^𝒪 ≤ R_⋆^{2/(2-α)} · (2-α)/2 · α^{α/(2-α)} · R^{2/(2-α)}`. -/
theorem occupation_own_energy {a D alpha R : ℝ} (ha : 0 < a) (ha1 : a < 1) (hD : 0 < D)
    (hal : 0 < alpha) (hal2 : alpha < 2) (hR : 0 ≤ R)
    {Γ : Measure (Rd d)} [IsLocallyFiniteMeasure Γ] (hS : VariationalDilation.SetScaling alpha Γ)
    (hΓ : Γ ≠ 0) (hB : SquarePairingBounds Γ alpha R) :
    (energySet a D Γ).Nonempty ∧ BddAbove (energySet a D Γ) ∧
      0 < EstarO a D Γ ∧
      EstarO a D Γ ≤ Rstar a D ^ (2 / (2 - alpha)) * spEnergyVal alpha R := by
  have hRst : 0 ≤ Rstar a D :=
    (OccupationKernelRow.occupation_kernel_row a D ha ha1 hD).2.2.2.2.2.2.2.2.le
  have hub : ∀ v ∈ energySet a D Γ, v ≤ Rstar a D ^ (2 / (2 - alpha)) * spEnergyVal alpha R := by
    rintro v ⟨G, DG, hO, rfl⟩
    have hJ := (occupation_physical_bound ha ha1 hD hal hal2 hR hB hO).2.2.2.2.2.2
    have hT0 : 0 ≤ T DG := ENNReal.toReal_nonneg
    have h := scalar_max hal hal2 (mul_nonneg hRst hR) hT0
    have e : spEnergyVal alpha (Rstar a D * R) =
        Rstar a D ^ (2 / (2 - alpha)) * spEnergyVal alpha R := by
      unfold spEnergyVal; rw [Real.mul_rpow hRst hR]; ring
    rw [← e]
    linarith
  obtain ⟨G, DG, hO, hpos⟩ := exists_pos_member ha ha1 hD hal hal2 hR hS hΓ hB
  have hmem : J a D Γ G - T DG / 2 ∈ energySet a D Γ := ⟨G, DG, hO, rfl⟩
  have hbdd : BddAbove (energySet a D Γ) := ⟨_, hub⟩
  exact ⟨⟨_, hmem⟩, hbdd, lt_of_lt_of_le hpos (le_csSup hbdd hmem), csSup_le ⟨_, hmem⟩ hub⟩


/-- `P:occupation-physical-class` (TeX lines 386-404) under the section's standing assumptions
(lines 4-10: `H:homog` with `a = α₀`, a nonzero covariance `Γ`, `D = q - 2a`, `q = 4 - α`),
with the named input `SquarePairingBounds Γ α R_0` (two conclusions of
`P:spatial-four-linear`).  For every field of `𝒪` (modelled as `IsOccField`):
the pairings `(s,t) ↦ B_Γ(g_s², g_t²)` are a.e.-measurable on `(0,1)²` and, as physical
integrals, unchanged (a.e. in `(s,t)`, and in `J`) under Lebesgue-a.e. changes of the spatial
versions at a.e. time; `b(g_s)` is integrable on `(0,1)` with integral `T(g)`; `J(g)` is finite,
its real integrand is integrable on `(0,1)²` with integral `J(g)`, and
`0 ≤ J(g) ≤ R_⋆ R_0 T(g)^{α/2}` (`E:occupation-physical-bound`, with `R_sp = R_0`, which is
the last claim of `P:spatial-four-linear`).  For the energy (`E:occupation-own-energy`): the
value set is nonempty and bounded above and
`0 < 𝓔_⋆^𝒪 ≤ R_⋆^{2/(2-α)} · (2-α)/2 · α^{α/(2-α)} · R_0^{2/(2-α)}`, the last factor being
`𝓔_sp` by `E:spatial-energy-map` at `R_sp = R_0` (`P:spatial-energy-map`, not formalized here);
the bound is a real number, hence finite. -/
theorem occupation_physical_class_paper {alpha a : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogCovariance d alpha a Γ μ) (hΓ : Γ ≠ 0) (D : ℝ) (hD : D = (4 - alpha) - 2 * a)
    (hB : SquarePairingBounds Γ alpha (SpatialSmoothRatio.R0 Γ alpha)) :
    (∀ (G : ℝ → Rd d → ℝ) (DG : ℝ → Rd d → Rd d), IsOccField G DG →
      AEMeasurable (fun p : ℝ × ℝ => sqPair Γ (G p.1) (G p.2)) (volI.prod volI) ∧
      (∀ G' : ℝ → Rd d → ℝ, (∀ᵐ s ∂volI, G s =ᵐ[volume] G' s) →
        (fun p : ℝ × ℝ => sqPair Γ (G p.1) (G p.2)) =ᵐ[volI.prod volI]
          (fun p : ℝ × ℝ => sqPair Γ (G' p.1) (G' p.2)) ∧
        Jlin a D Γ G = Jlin a D Γ G') ∧
      Integrable (fun s => ∫ x, ‖DG s x‖ ^ 2) volI ∧
      ∫ s, (∫ x, ‖DG s x‖ ^ 2) ∂volI = T DG ∧
      Jlin a D Γ G < ⊤ ∧
      Integrable (fun p : ℝ × ℝ => Kstar a D (p.1 - p.2) * (sqPair Γ (G p.1) (G p.2)).toReal)
        (volI.prod volI) ∧
      ∫ p, Kstar a D (p.1 - p.2) * (sqPair Γ (G p.1) (G p.2)).toReal ∂(volI.prod volI) =
        J a D Γ G ∧
      0 ≤ J a D Γ G ∧
      J a D Γ G ≤ Rstar a D * SpatialSmoothRatio.R0 Γ alpha * T DG ^ (alpha / 2)) ∧
    (energySet a D Γ).Nonempty ∧ BddAbove (energySet a D Γ) ∧
    0 < EstarO a D Γ ∧
    EstarO a D Γ ≤
      Rstar a D ^ (2 / (2 - alpha)) * spEnergyVal alpha (SpatialSmoothRatio.R0 Γ alpha) := by
  have := hH.Γ_radon
  obtain ⟨-, hal, hal2, -⟩ := SpatialSmoothRatio.homog_consequences hH
  have hR : 0 ≤ SpatialSmoothRatio.R0 Γ alpha :=
    (SpatialSmoothRatio.spatial_smooth_ratio_R0_paper hH hΓ).2.2.2.2.1.le
  have ha := hH.alpha0_pos
  have ha1 := hH.alpha0_lt_one
  have hD0 : 0 < D := by rw [hD]; linarith [hH.threshold]
  refine ⟨fun G DG hO => ?_, occupation_own_energy ha ha1 hD0 hal hal2 hR hH.scaling hΓ hB⟩
  obtain ⟨h1, -, h3, h4, h5, h6, h7⟩ := occupation_physical_bound ha ha1 hD0 hal hal2 hR hB hO
  obtain ⟨hT1, hT2⟩ := T_eq_integral hO
  exact ⟨h1, fun G' hG' => sqPair_Jlin_congr a D Γ hG', hT1, hT2, h3, h4, h5, h6, h7⟩

end StratonovichHAMSecondMoment.OccupationPhysicalClass
