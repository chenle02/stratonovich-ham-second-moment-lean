module

/-
Copyright 2026 Le Chen. SPDX-License-Identifier: Apache-2.0

Wave item L9-A1: Proposition `P:raw-occupation-energy` (Original occupation energy and
dilation) of `notes/integrated_occupation_ceiling.tex` at revision a284420 (statement lines
92-112, proof lines 114-147), with the objects of `E:raw-occupation-definitions` (lines 4-18).
Standing assumptions of the section (lines 4-21): the original covariance under `H:homog`
(`HomogHypothesis.HomogCovariance d α α₀ Γ μ`), `a = α₀`, the ORIGINAL kernel
`K(s,t) = |s-t|^{-a}` on `I = (0,1)` (`TimeSchur.kern a (s - t)`; its diagonal value is Lean's
`0 ^ (-a)`, on a null set), and `Γ ≠ 0` (line 20).

Objects (reused, not redefined): the class `𝒪` is `OccupationPhysicalClass.IsOccField`
(`integrated_spatial_occupation.tex` lines 381-384), `B_Γ(f²,h²)` is
`OccupationPhysicalClass.sqPair`, `T(g)` is `OccupationPhysicalClass.T`/`Tlin`, `K_0 = 2^a/(1-a)`
is `OccupationCeilingFinite.K0` (the same body as `SpatialBracket.K0`), `D_ζ` is
`SpatialBracket.Dzeta`, `R_sp` is `SpatialFourLinear.Rsp`.  New: `Araw`/`A` (`A(g)`, the
extended and the real value), `ratioSet`, `Cocc` (`C_occ`), `energySet`, `EO` (`𝓔_ζ^𝒪`), the
dilation `dilField`/`dilGrad` (`U_ℓ`, line 127).

Formalized:
* `raw_occupation_energy_paper` (the `_paper` wrapper; hypotheses `H:homog` with `a = α₀` and
  `Γ ≠ 0`, exactly the section's): `0 < C_occ ≤ K_0 R_sp` with the ratio set nonempty and bounded
  above; for every field of `𝒪`: `0 < T(g) < ∞`, `A(g) < ∞` and
  `0 ≤ A(g) ≤ K_0 R_sp T(g)^{α/2}` (`E:raw-occupation-bound`, lines 120-122), `U_ℓ g ∈ 𝒪`,
  `A(U_ℓ g) = ℓ^α A(g)`, `T(U_ℓ g) = ℓ² T(g)` and `U_{1/ℓ} U_ℓ = id` (lines 127-136); for every
  `ζ > 0`: the energy value set is nonempty and bounded above, `𝓔_ζ^𝒪 = D_ζ C_occ^{2/(2-α)}`
  (`E:raw-occupation-energy`, lines 100-104), `C_occ = (2𝓔_ζ^𝒪/(2-α))^{(2-α)/2}(2ζ/α)^{α/2}`
  (`E:raw-occupation-ratio`, lines 105-108), `𝓔_ζ^𝒪 > 0` and `𝓔_ζ^𝒪 = ζ^{-α/(2-α)} 𝓔_1^𝒪`
  (lines 110-111).
* General forms: `raw_occupation_energy` (`d ≥ 1`, `0 ≤ a < 1`, `0 < α < 2`, a locally finite
  `Γ ≠ 0` with `VariationalDilation.SetScaling α Γ`, the bounds `SquarePairingBounds Γ α R` with
  `R ≥ 0`, giving `C_occ ≤ K_0 R`), `raw_occupation_bound`, `Araw_le`, `T_pos`,
  `exists_pos_member`, `isOccField_dil`, `Araw_dil`, `sqPair_dil` (for ALL real functions),
  `dil_inv`, `scalar_max_zeta`, `scalar_attain_zeta`.

Supplied inputs: none.  `SquarePairingBounds Γ α R_0` is
`SpatialOccupationL7Completed.squarePairingBounds_holds` and `R_sp = R_0` is
`SpatialOccupationL7Completed.spatial_ratio_H1_paper_completed` (both under `H:homog`,
`Γ ≠ 0`).

Narrower than the TeX (recorded): the class `𝒪` is modelled by joint representatives
(`IsOccField`: a.e.-strongly measurable `(s,x) ↦ g_s(x)` and `(s,x) ↦ ∇g_s(x)`, a unit `H¹`
pair at a.e. time, `T(g) < ∞`), exactly as in `P:occupation-physical-class` (wave L7); the
TeX's strongly `H¹`-measurable fields are not formalized.  Otherwise the statement is the TeX's.

Implicit hypotheses made explicit: `A(g)` and `T(g)` are extended integrals whose finiteness is
a conclusion; `C_occ` and `𝓔_ζ^𝒪` are `sSup`s whose sets are proved nonempty and bounded above;
`T(g) > 0` (needs `d ≥ 1`, from `H:homog`) so no ratio is Lean's `x/0 = 0`; the dilation lemmas
take an s-finite `Γ` (`SFinite`, automatic for the locally finite `Γ` of `H:homog`).

Proof route.  As in the TeX (lines 115-145), with these differences: the spatial bound
`B_Γ(g_s²,g_t²) ≤ R b_s^{α/4} b_t^{α/4}` enters as `≤ (R/2)(b_s^{α/2} + b_t^{α/2})`
(`OccupationPhysicalClass.sqPair_le_half`), followed by the sharp row bound
`∫_0^1 |s-t|^{-a} dt ≤ K_0` in both variables and Hölder for the concavity step (same constant
`K_0 R`); positivity uses `|s-t|^{-a} ≥ 1` on `(0,1)²`, so `A(g) ≥ A_sp(g) > 0` for a
constant-in-time unit test; the dilation identity `A(U_ℓ g) = ℓ^α A(g)` is proved for all
functions by the change of variables `(x,y) ↦ (ℓx,ℓy)` on `dx Γ(dy)` (no approximation step is
needed for the extended pairing); the lower bound in `E:raw-occupation-energy` dilates members
whose ratios tend to `C_occ` to the scalar optimizer.  Lemmas marked "Auxiliary to the Lean proof
route" have no manuscript label.  The fallback scope (`RawOccupationDilation` as a named input)
was not needed.
-/
public import Mathlib
public import StratonovichHAMSecondMoment.OccupationPhysicalClass
public import StratonovichHAMSecondMoment.OccupationCeilingFinite
public import StratonovichHAMSecondMoment.SpatialBracket

@[expose] public section

noncomputable section

set_option autoImplicit false

open MeasureTheory Set Real Filter
open scoped ENNReal

namespace StratonovichHAMSecondMoment.RawOccupationEnergy

open HomogHypothesis (Rd HomogCovariance)
open OccupationPhysicalClass (volI sqPair gradSqE Tlin T IsOccField SquarePairingBounds)
open TimeSchur (kern kern_nonneg measurable_kern kern_sub_comm)
open OccupationCeilingFinite (K0 K0_pos)
open SpatialStaticControls (IsUnitH1)
open SpatialBracket (Dzeta)

variable {d : ℕ}

/-! ### The objects of `E:raw-occupation-definitions` -/

/-- `A(g) = ∫_{I²} K(s,t) B_Γ(g_s², g_t²) ds dt` with the ORIGINAL kernel `K(s,t) = |s-t|^{-a}`
(`TimeSchur.kern a (s - t)`; its diagonal value is Lean's `0 ^ (-a)`, on a null set) on
`I = (0,1)` (`integrated_occupation_ceiling.tex` lines 4-12), as an iterated extended
nonnegative integral; `B_Γ(g_s², g_t²)` is the physical pairing
`OccupationPhysicalClass.sqPair`.  `raw_occupation_bound` shows it is finite on `𝒪`. -/
def Araw (a : ℝ) (Γ : Measure (Rd d)) (G : ℝ → Rd d → ℝ) : ℝ≥0∞ :=
  ∫⁻ s, ∫⁻ t, ENNReal.ofReal (kern a (s - t)) * sqPair Γ (G s) (G t) ∂volI ∂volI

/-- The real value `A(g)` (finite on `𝒪`: `raw_occupation_bound`). -/
def A (a : ℝ) (Γ : Measure (Rd d)) (G : ℝ → Rd d → ℝ) : ℝ := (Araw a Γ G).toReal

/-- The ratio set `{A(g)/T(g)^{α/2} : g ∈ 𝒪}` of `E:raw-occupation-definitions` (TeX lines
13-14), over the class `𝒪` modelled by `OccupationPhysicalClass.IsOccField`.  On `𝒪`,
`T(g) > 0` when `d ≥ 1` (`T_pos`), so no quotient is Lean's `x/0 = 0`. -/
def ratioSet (a alpha : ℝ) (Γ : Measure (Rd d)) : Set ℝ :=
  {r | ∃ (G : ℝ → Rd d → ℝ) (DG : ℝ → Rd d → Rd d), IsOccField G DG ∧
    r = A a Γ G / T DG ^ (alpha / 2)}

/-- `C_occ = sup_{g ∈ 𝒪} A(g)/T(g)^{α/2}` (TeX lines 13-14), as `sSup`; `raw_occupation_energy`
proves the set nonempty and bounded above, so this is not Lean's junk value. -/
def Cocc (a alpha : ℝ) (Γ : Measure (Rd d)) : ℝ := sSup (ratioSet a alpha Γ)

/-- The value set `{A(g) - ζ T(g) : g ∈ 𝒪}` of `E:raw-occupation-definitions` (TeX lines
15-16). -/
def energySet (a : ℝ) (Γ : Measure (Rd d)) (ζ : ℝ) : Set ℝ :=
  {v | ∃ (G : ℝ → Rd d → ℝ) (DG : ℝ → Rd d → Rd d), IsOccField G DG ∧
    v = A a Γ G - ζ * T DG}

/-- `𝓔_ζ^𝒪 = sup_{g ∈ 𝒪} {A(g) - ζ T(g)}` (TeX lines 15-16), as `sSup`; for `ζ > 0`
`raw_occupation_energy` proves the set nonempty and bounded above. -/
def EO (a : ℝ) (Γ : Measure (Rd d)) (ζ : ℝ) : ℝ := sSup (energySet a Γ ζ)

/-! ### The bound `E:raw-occupation-bound` -/

/-- Auxiliary to the Lean proof route: `(s,t) ↦ ofReal |s-t|^{-a}` is measurable. -/
theorem kern_meas (a : ℝ) : Measurable fun q : ℝ × ℝ => ENNReal.ofReal (kern a (q.1 - q.2)) :=
  ENNReal.measurable_ofReal.comp ((measurable_kern a).comp (measurable_fst.sub measurable_snd))

/-- `E:raw-occupation-bound`, upper half, for the extended integral (TeX lines 117-122): for
`0 ≤ a < 1`, `0 < α < 2`, the supplied bounds `SquarePairingBounds Γ α R` with `R ≥ 0` and a
field of `𝒪`, `A(g) ≤ K_0 R T(g)^{α/2}`, `K_0 = 2^a/(1-a)`.  Route: the TeX's spatial
Cauchy-Schwarz bound `B_Γ(g_s², g_t²) ≤ R b_s^{α/4} b_t^{α/4}` is used in the form
`≤ (R/2)(b_s^{α/2} + b_t^{α/2})` (`OccupationPhysicalClass.sqPair_le_half`), then the sharp row
bound `∫_0^1 |s-t|^{-a} dt ≤ K_0` (`OccupationCeilingFinite.row_le`) in both variables, and
the concavity step `∫_0^1 b^{α/2} ≤ T^{α/2}` (`OccupationPhysicalClass.lintegral_rpow_le`). -/
theorem Araw_le {a alpha R : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) (hal : 0 < alpha)
    (hal2 : alpha < 2) (hR : 0 ≤ R) {Γ : Measure (Rd d)} (hB : SquarePairingBounds Γ alpha R)
    {G : ℝ → Rd d → ℝ} {DG : ℝ → Rd d → Rd d} (hO : IsOccField G DG) :
    Araw a Γ G ≤ ENNReal.ofReal (K0 a * R * (Tlin DG).toReal ^ (alpha / 2)) := by
  set p := alpha / 2 with hp
  set β : ℝ → ℝ≥0∞ := fun s => gradSqE (DG s) ^ p with hβ
  set c : ℝ≥0∞ := ENNReal.ofReal (R / 2) with hc
  set Rs : ℝ≥0∞ := ENNReal.ofReal (K0 a) with hRs
  set k : ℝ → ℝ → ℝ≥0∞ := fun s t => ENNReal.ofReal (kern a (s - t)) with hk
  have hkm : Measurable fun q : ℝ × ℝ => k q.1 q.2 := kern_meas a
  have hkt : ∀ s, Measurable fun t => k s t := fun s =>
    ENNReal.measurable_ofReal.comp ((measurable_kern a).comp (measurable_const.sub measurable_id))
  have hks : ∀ t, Measurable fun s => k s t := fun t =>
    ENNReal.measurable_ofReal.comp ((measurable_kern a).comp (measurable_id.sub measurable_const))
  have hβm : AEMeasurable β volI :=
    (OccupationPhysicalClass.gradSqE_aemeasurable hO.meas_grad).pow_const p
  have hH : AEMeasurable (fun q : ℝ × ℝ => k q.1 q.2 * β q.2) (volI.prod volI) :=
    hkm.aemeasurable.mul (hβm.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd)
  have hF : AEMeasurable (fun q : ℝ × ℝ => k q.1 q.2 * β q.1) (volI.prod volI) :=
    hkm.aemeasurable.mul (hβm.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst)
  have hIcc : ∀ᵐ s ∂volI, s ∈ Icc (0 : ℝ) 1 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs using Ioo_subset_Icc_self hs
  have step1 : Araw a Γ G ≤ ∫⁻ s, ∫⁻ t, c * (k s t * β s) + c * (k s t * β t) ∂volI ∂volI := by
    unfold Araw
    refine lintegral_mono_ae ?_
    filter_upwards [hO.unit] with s hs
    refine lintegral_mono_ae ?_
    filter_upwards [hO.unit] with t ht
    have := OccupationPhysicalClass.sqPair_le_half hR hal.le hB hs ht
    calc k s t * sqPair Γ (G s) (G t) ≤ k s t * (c * (β s + β t)) := by gcongr
      _ = c * (k s t * β s) + c * (k s t * β t) := by ring
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
  have row1 : ∫⁻ s, ∫⁻ t, k s t * β s ∂volI ∂volI ≤ Rs * ∫⁻ s, β s ∂volI := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono_ae ?_
    filter_upwards [hIcc] with s hs
    rw [hI1 s]
    gcongr
    exact OccupationCeilingFinite.row_le ha0 ha1 hs
  have col1 : ∫⁻ s, ∫⁻ t, k s t * β t ∂volI ∂volI ≤ Rs * ∫⁻ s, β s ∂volI := by
    rw [lintegral_lintegral_swap hH, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono_ae ?_
    filter_upwards [hIcc] with t ht
    rw [lintegral_mul_const _ (hks t)]
    gcongr
    have e : (fun s => k s t) = fun s => ENNReal.ofReal (kern a (t - s)) := by
      funext s; simp only [hk]; rw [kern_sub_comm]
    rw [e]
    exact OccupationCeilingFinite.row_le ha0 ha1 ht
  have hJ : ∫⁻ s, β s ∂volI ≤ Tlin DG ^ p :=
    OccupationPhysicalClass.lintegral_rpow_le
      (OccupationPhysicalClass.gradSqE_aemeasurable hO.meas_grad) (by positivity) (by linarith)
  have hT : Tlin DG ^ p = ENNReal.ofReal ((Tlin DG).toReal ^ p) := by
    rw [← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg (by positivity),
      ENNReal.ofReal_toReal hO.energy_lt_top.ne]
  have hK : 0 ≤ K0 a := (K0_pos ha1).le
  have hcc : c + c = ENNReal.ofReal R := by
    rw [hc, ← ENNReal.ofReal_add (by linarith) (by linarith)]; congr 1; ring
  calc Araw a Γ G ≤ _ := step1
    _ = _ := step2
    _ ≤ c * (Rs * ∫⁻ s, β s ∂volI) + c * (Rs * ∫⁻ s, β s ∂volI) := by gcongr
    _ = ENNReal.ofReal R * Rs * ∫⁻ s, β s ∂volI := by rw [← hcc]; ring
    _ ≤ ENNReal.ofReal R * Rs * Tlin DG ^ p := by gcongr
    _ = ENNReal.ofReal (K0 a * R * (Tlin DG).toReal ^ p) := by
      rw [hT, hRs, ← ENNReal.ofReal_mul hR, ← ENNReal.ofReal_mul (by positivity)]
      congr 1; ring

/-- `E:raw-occupation-bound` (TeX lines 117-122): under the hypotheses of `Araw_le`, for every
field of `𝒪`: `A(g) < ∞` as an extended integral (so `A` is its genuine real value) and
`0 ≤ A(g) ≤ K_0 R T(g)^{α/2}`. -/
theorem raw_occupation_bound {a alpha R : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) (hal : 0 < alpha)
    (hal2 : alpha < 2) (hR : 0 ≤ R) {Γ : Measure (Rd d)} (hB : SquarePairingBounds Γ alpha R)
    {G : ℝ → Rd d → ℝ} {DG : ℝ → Rd d → Rd d} (hO : IsOccField G DG) :
    Araw a Γ G < ⊤ ∧ 0 ≤ A a Γ G ∧ A a Γ G ≤ K0 a * R * T DG ^ (alpha / 2) := by
  have hle := Araw_le ha0 ha1 hal hal2 hR hB hO
  refine ⟨lt_of_le_of_lt hle ENNReal.ofReal_lt_top, ENNReal.toReal_nonneg, ?_⟩
  have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hle
  rwa [ENNReal.toReal_ofReal (by
    have := (K0_pos ha1).le
    have : 0 ≤ (Tlin DG).toReal ^ (alpha / 2) := Real.rpow_nonneg ENNReal.toReal_nonneg _
    positivity)] at this

/-- Every field of `𝒪` has positive gradient budget (TeX lines 115-117): for `d ≥ 1`,
`0 < T(g) < ∞` (a unit `H¹` profile has `b > 0`, `SpatialFourLinear.gradL2_pos`). -/
theorem T_pos (hd : 0 < d) {G : ℝ → Rd d → ℝ} {DG : ℝ → Rd d → Rd d} (hO : IsOccField G DG) :
    0 < T DG := by
  have hm := OccupationPhysicalClass.gradSqE_aemeasurable hO.meas_grad
  have hpos : ∀ᵐ s ∂volI, 0 < gradSqE (DG s) := by
    filter_upwards [hO.unit] with s hs
    rw [(OccupationPhysicalClass.gradSqE_eq hs.2.1).2]
    exact ENNReal.ofReal_pos.2 (SpatialFourLinear.gradL2_pos hd hs)
  have hne : Tlin DG ≠ 0 := by
    intro h0
    have hz := (lintegral_eq_zero_iff' hm).1 h0
    have hvol : volI ≠ 0 := by
      intro h; have := OccupationPhysicalClass.volI_univ; rw [h] at this; simp at this
    have : (ae volI).NeBot := ae_neBot.2 hvol
    obtain ⟨s, hs1, hs2⟩ := (hpos.and hz).exists
    simp only [Pi.zero_apply] at hs2
    rw [hs2] at hs1
    exact lt_irrefl _ hs1
  exact ENNReal.toReal_pos hne hO.energy_lt_top.ne

/-- Auxiliary to the Lean proof route: `|s-t|^{-a} ≥ 1` for distinct `s, t ∈ (0,1)`, `a ≥ 0`. -/
theorem one_le_kern {a : ℝ} (ha0 : 0 ≤ a) {s t : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1)
    (ht : t ∈ Ioo (0 : ℝ) 1) (hst : t ≠ s) : 1 ≤ kern a (s - t) := by
  unfold kern
  refine Real.one_le_rpow_of_pos_of_le_one_of_nonpos (abs_pos.2 (sub_ne_zero.2 (Ne.symm hst)))
    ?_ (by linarith)
  rw [abs_le]; constructor <;> linarith [hs.1, hs.2, ht.1, ht.2]

/-- Positivity witness (TeX lines 123-125): for `0 ≤ a < 1`, `0 < α < 2`, a locally finite
`Γ ≠ 0` with the scaling `Γ(cA) = c^{d-α}Γ(A)` (`SetScaling`) and the supplied bounds with
`R ≥ 0` (for finiteness), a fixed compact smooth unit profile, constant in time, lies in `𝒪` and
has `A(g) > 0`.  Route: the kernel is `≥ 1` on `(0,1)²` off the diagonal, so the proof bounds
`A(g)` below by `A_sp(g) > 0` (`SpatialSmoothRatio.spatialEnergy_pos`). -/
theorem exists_pos_member {a alpha R : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) (hal : 0 < alpha)
    (hal2 : alpha < 2) (hR : 0 ≤ R) {Γ : Measure (Rd d)} [IsLocallyFiniteMeasure Γ]
    (hS : VariationalDilation.SetScaling alpha Γ) (hΓ : Γ ≠ 0)
    (hB : SquarePairingBounds Γ alpha R) :
    ∃ (G : ℝ → Rd d → ℝ) (DG : ℝ → Rd d → Rd d), IsOccField G DG ∧ 0 < A a Γ G := by
  obtain ⟨g, hg⟩ := SpatialSmoothRatio.exists_unitTest d
  set A0 := SpatialFourierBound.spatialEnergy Γ g with hA0
  have hA0p : 0 < A0 := SpatialSmoothRatio.spatialEnergy_pos hS hΓ hg
  have hgt : WeakSobolev.IsTestFunction g := ⟨hg.1, hg.2.1⟩
  have hsq : Continuous fun x => g x ^ 2 := hg.1.continuous.pow 2
  have hsqc : HasCompactSupport fun x => g x ^ 2 :=
    hg.2.1.comp_left (g := fun r : ℝ => r ^ 2) (by norm_num)
  have hP : sqPair Γ g g = ENNReal.ofReal A0 :=
    (SpatialStaticControls.pairing_eq_spatialPair hsq hsqc (fun x => sq_nonneg _) hsq hsqc
      (fun x => sq_nonneg _)).2.1
  have hu := SpatialStaticControls.isUnitH1_of_unitTest hg
  set G : ℝ → Rd d → ℝ := fun _ => g with hG
  set DG : ℝ → Rd d → Rd d := fun _ => VariationalFloor.grad g with hDG
  have hTl : Tlin DG = gradSqE (VariationalFloor.grad g) := by
    unfold Tlin
    simp only [hDG, lintegral_const, OccupationPhysicalClass.volI_univ, mul_one]
  have hO : IsOccField G DG := by
    refine ⟨(hg.1.continuous.comp continuous_snd).aestronglyMeasurable,
      ((VariationalFloor.continuous_grad hgt).comp continuous_snd).aestronglyMeasurable,
      Eventually.of_forall fun _ => hu, ?_⟩
    rw [hTl, (OccupationPhysicalClass.gradSqE_eq hu.2.1).2]
    exact ENNReal.ofReal_lt_top
  refine ⟨G, DG, hO, ?_⟩
  have hlow : ENNReal.ofReal A0 ≤ Araw a Γ G := by
    have hc : ∫⁻ s, ∫⁻ t, ENNReal.ofReal A0 ∂volI ∂volI = ENNReal.ofReal A0 := by
      simp only [lintegral_const, OccupationPhysicalClass.volI_univ, mul_one]
    rw [← hc]
    unfold Araw
    refine lintegral_mono_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    refine lintegral_mono_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo,
      ae_restrict_of_ae (Measure.ae_ne volume s)] with t ht hts
    simp only [hG, hP]
    rw [← ENNReal.ofReal_mul (kern_nonneg _ _)]
    exact ENNReal.ofReal_le_ofReal (le_mul_of_one_le_left hA0p.le (one_le_kern ha0 hs ht hts))
  have hfin := (raw_occupation_bound ha0 ha1 hal hal2 hR hB hO).1
  have := ENNReal.toReal_mono hfin.ne hlow
  rw [ENNReal.toReal_ofReal hA0p.le] at this
  exact lt_of_lt_of_le hA0p this

/-! ### Dilation of `𝒪` -/

/-- The dilated field `(U_ℓ g)_s = ℓ^{d/2} g_s(ℓ ·)` (TeX line 127), with
`WeakSobolev.dilL2`. -/
def dilField (ℓ : ℝ) (G : ℝ → Rd d → ℝ) : ℝ → Rd d → ℝ := fun s => WeakSobolev.dilL2 ℓ (G s)

/-- The gradient of the dilated field, `∇(U_ℓ g)_s = ℓ U_ℓ(∇g_s)` (TeX line 127;
`WeakSobolev.hasWeakGradient_dilL2`). -/
def dilGrad (ℓ : ℝ) (DG : ℝ → Rd d → Rd d) : ℝ → Rd d → Rd d :=
  fun s x => ℓ • WeakSobolev.dilL2 ℓ (DG s) x

/-- Auxiliary to the Lean proof route: Lebesgue substitution `y = ℓ x` for extended integrals,
`∫⁻ F(ℓ x) dx = ℓ^{-d} ∫⁻ F` (`ℓ > 0`, any `F`; `Measure.map_addHaar_smul`). -/
theorem lintegral_comp_smul_rd {ℓ : ℝ} (hℓ : 0 < ℓ) (F : Rd d → ℝ≥0∞) :
    ∫⁻ x, F (ℓ • x) = ENNReal.ofReal ((ℓ ^ d)⁻¹) * ∫⁻ x, F x := by
  have h := lintegral_map_equiv F (MeasurableEquiv.smul₀ ℓ hℓ.ne' (α := Rd d))
    (μ := (volume : Measure (Rd d)))
  have hm : Measure.map (MeasurableEquiv.smul₀ ℓ hℓ.ne' (α := Rd d)) (volume : Measure (Rd d)) =
      ENNReal.ofReal ((ℓ ^ d)⁻¹) • (volume : Measure (Rd d)) := by
    have e := Measure.map_addHaar_smul (volume : Measure (Rd d)) hℓ.ne'
    rw [finrank_euclideanSpace_fin, abs_of_pos (by positivity)] at e
    exact e
  rw [hm, lintegral_smul_measure, smul_eq_mul] at h
  exact h.symm

/-- Auxiliary to the Lean proof route: the pushforward of `ν(dx,dy) = dx Γ(dy)` under
`(x,y) ↦ (ℓx, ℓy)` is `ℓ^{-d} ℓ^{α-d} ν` (`ℓ > 0`, `Γ` s-finite with `SetScaling α Γ`). -/
theorem map_pairMeasure {alpha : ℝ} {Γ : Measure (Rd d)} [SFinite Γ]
    (hS : VariationalDilation.SetScaling alpha Γ) {ℓ : ℝ} (hℓ : 0 < ℓ) :
    Measure.map (Prod.map (fun x : Rd d => ℓ • x) (fun y : Rd d => ℓ • y))
        ((volume : Measure (Rd d)).prod Γ) =
      (ENNReal.ofReal ((ℓ ^ d)⁻¹) * ENNReal.ofReal (ℓ ^ (alpha - d))) •
        ((volume : Measure (Rd d)).prod Γ) := by
  rw [← Measure.map_prod_map _ _ (measurable_const_smul ℓ) (measurable_const_smul ℓ),
    VariationalDilation.map_dilation hS hℓ]
  have e := Measure.map_addHaar_smul (volume : Measure (Rd d)) hℓ.ne'
  rw [finrank_euclideanSpace_fin, abs_of_pos (by positivity)] at e
  rw [e, Measure.prod_smul_left, Measure.prod_smul_right, smul_smul]

/-- **The dilation of the pairing** (TeX lines 130-135, "the two densities contribute `ℓ^{2d}`,
`dx` contributes `ℓ^{-d}`, and the pushforward of `Γ` contributes `ℓ^{α-d}`"): for `ℓ > 0` and an
s-finite `Γ` with `SetScaling α Γ`, `B_Γ((U_ℓ f)², (U_ℓ h)²) = ℓ^α B_Γ(f², h²)` for ALL real
functions `f, h` (an identity of extended integrals; no approximation is needed). -/
theorem sqPair_dil {alpha : ℝ} {Γ : Measure (Rd d)} [SFinite Γ]
    (hS : VariationalDilation.SetScaling alpha Γ) {ℓ : ℝ} (hℓ : 0 < ℓ) (f h : Rd d → ℝ) :
    sqPair Γ (WeakSobolev.dilL2 ℓ f) (WeakSobolev.dilL2 ℓ h) =
      ENNReal.ofReal (ℓ ^ alpha) * sqPair Γ f h := by
  have hsq : ∀ (u : Rd d → ℝ) (x : Rd d),
      ENNReal.ofReal (WeakSobolev.dilL2 ℓ u x ^ 2) =
        ENNReal.ofReal (ℓ ^ d) * ENNReal.ofReal (u (ℓ • x) ^ 2) := by
    intro u x
    have := WeakSobolev.norm_dilL2_sq hℓ u x
    simp only [Real.norm_eq_abs, sq_abs, smul_eq_mul] at this
    rw [this, ENNReal.ofReal_mul (by positivity)]
  set K : Rd d × Rd d → ℝ≥0∞ := fun q =>
    ENNReal.ofReal (f q.1 ^ 2) * ENNReal.ofReal (h (q.1 - q.2) ^ 2) with hK
  set e : Rd d × Rd d ≃ᵐ Rd d × Rd d :=
    MeasurableEquiv.prodCongr (MeasurableEquiv.smul₀ ℓ hℓ.ne') (MeasurableEquiv.smul₀ ℓ hℓ.ne')
    with he
  have hpt : ∀ p : Rd d × Rd d,
      ENNReal.ofReal (WeakSobolev.dilL2 ℓ f p.1 ^ 2) *
          ENNReal.ofReal (WeakSobolev.dilL2 ℓ h (p.1 - p.2) ^ 2) =
        (ENNReal.ofReal (ℓ ^ d) * ENNReal.ofReal (ℓ ^ d)) * K (e p) := by
    intro p
    have hep : e p = (ℓ • p.1, ℓ • p.2) := rfl
    rw [hsq, hsq, hep, hK]
    simp only [smul_sub]
    ring
  have hmap : Measure.map e ((volume : Measure (Rd d)).prod Γ) =
      (ENNReal.ofReal ((ℓ ^ d)⁻¹) * ENNReal.ofReal (ℓ ^ (alpha - d))) •
        ((volume : Measure (Rd d)).prod Γ) := map_pairMeasure hS hℓ
  unfold sqPair OccupationKernelRow.pairing OccupationKernelRow.pairMeasure
  simp_rw [hpt]
  rw [lintegral_const_mul' _ _ (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top),
    ← lintegral_map_equiv K e, hmap, lintegral_smul_measure, smul_eq_mul, ← mul_assoc]
  congr 1
  rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  have h1 : ((ℓ : ℝ) ^ d : ℝ) = ℓ ^ (d : ℝ) := (Real.rpow_natCast ℓ d).symm
  rw [h1, ← Real.rpow_neg hℓ.le, ← Real.rpow_add hℓ, ← Real.rpow_add hℓ, ← Real.rpow_add hℓ]
  congr 1; ring

/-- Auxiliary to the Lean proof route: `b(ℓ U_ℓ g) = ℓ² b(g)` for the extended gradient energy,
for every vector field `g` (`ℓ > 0`). -/
theorem gradSqE_dil {ℓ : ℝ} (hℓ : 0 < ℓ) (g : Rd d → Rd d) :
    gradSqE (fun x => ℓ • WeakSobolev.dilL2 ℓ g x) = ENNReal.ofReal (ℓ ^ 2) * gradSqE g := by
  unfold gradSqE
  have hpt : ∀ x, ‖ℓ • WeakSobolev.dilL2 ℓ g x‖ₑ ^ 2 =
      ENNReal.ofReal (ℓ ^ 2 * ℓ ^ d) * ‖g (ℓ • x)‖ₑ ^ 2 := by
    intro x
    have hn := WeakSobolev.norm_dilL2_sq hℓ g x
    rw [smul_eq_mul] at hn
    rw [← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _),
      ← ENNReal.ofReal_pow (norm_nonneg _), ← ENNReal.ofReal_mul (by positivity), norm_smul,
      mul_pow, hn, Real.norm_eq_abs, sq_abs]
    congr 1; ring
  simp_rw [hpt]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_comp_smul_rd hℓ (fun y => ‖g y‖ₑ ^ 2), ← mul_assoc,
    ← ENNReal.ofReal_mul (by positivity)]
  congr 2
  field_simp

/-- Auxiliary to the Lean proof route: `(s,x) ↦ (s, ℓx)` is quasi-measure-preserving for
`(0,1) × ℝ^d` with Lebesgue measure (`ℓ > 0`). -/
theorem qmp_dil {ℓ : ℝ} (hℓ : 0 < ℓ) :
    QuasiMeasurePreserving (Prod.map (id : ℝ → ℝ) (fun x : Rd d => ℓ • x))
      (volI.prod (volume : Measure (Rd d))) (volI.prod (volume : Measure (Rd d))) := by
  refine (QuasiMeasurePreserving.id volI).prodMap ⟨measurable_const_smul ℓ, ?_⟩
  have e := Measure.map_addHaar_smul (volume : Measure (Rd d)) hℓ.ne'
  rw [e]
  exact Measure.smul_absolutelyContinuous

/-- **`U_ℓ` maps `𝒪` into `𝒪`** (TeX lines 127-129): for `ℓ > 0` and a field of `𝒪`, the dilated
field `U_ℓ g` with gradient field `ℓ U_ℓ ∇g` lies in `𝒪` (joint measurability is preserved, the
unit `H¹` condition by `SpatialStaticControls.isUnitH1_dil`), and `T(U_ℓ g) = ℓ² T(g)`
(as extended integrals). -/
theorem isOccField_dil {ℓ : ℝ} (hℓ : 0 < ℓ) {G : ℝ → Rd d → ℝ} {DG : ℝ → Rd d → Rd d}
    (hO : IsOccField G DG) :
    IsOccField (dilField ℓ G) (dilGrad ℓ DG) ∧
      Tlin (dilGrad ℓ DG) = ENNReal.ofReal (ℓ ^ 2) * Tlin DG := by
  have hT : Tlin (dilGrad ℓ DG) = ENNReal.ofReal (ℓ ^ 2) * Tlin DG := by
    unfold Tlin dilGrad
    simp_rw [gradSqE_dil hℓ]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine ⟨⟨?_, ?_, ?_, ?_⟩, hT⟩
  · have h := (hO.meas.comp_quasiMeasurePreserving (qmp_dil hℓ)).const_smul
      (ℓ ^ ((d : ℝ) / 2))
    refine h.congr (ae_of_all _ fun p => ?_)
    simp [dilField, WeakSobolev.dilL2, Function.comp]
  · have h := ((hO.meas_grad.comp_quasiMeasurePreserving (qmp_dil hℓ)).const_smul
      (ℓ ^ ((d : ℝ) / 2))).const_smul ℓ
    refine h.congr (ae_of_all _ fun p => ?_)
    simp [dilGrad, WeakSobolev.dilL2, Function.comp]
  · filter_upwards [hO.unit] with s hs
    exact (SpatialStaticControls.isUnitH1_dil hs hℓ).1
  · rw [hT]; exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hO.energy_lt_top

/-- **The dilation identities** (TeX lines 130-133): for `ℓ > 0`, an s-finite `Γ` with
`SetScaling α Γ` and any field `G`, `A(U_ℓ g) = ℓ^α A(g)` (for the extended and the real
values). -/
theorem Araw_dil {alpha : ℝ} {Γ : Measure (Rd d)} [SFinite Γ]
    (hS : VariationalDilation.SetScaling alpha Γ) {ℓ : ℝ} (hℓ : 0 < ℓ) (a : ℝ)
    (G : ℝ → Rd d → ℝ) :
    Araw a Γ (dilField ℓ G) = ENNReal.ofReal (ℓ ^ alpha) * Araw a Γ G ∧
      A a Γ (dilField ℓ G) = ℓ ^ alpha * A a Γ G := by
  have h : Araw a Γ (dilField ℓ G) = ENNReal.ofReal (ℓ ^ alpha) * Araw a Γ G := by
    unfold Araw dilField
    simp_rw [sqPair_dil hS hℓ, mul_left_comm (ENNReal.ofReal (kern a _))]
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_congr fun s => ?_
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine ⟨h, ?_⟩
  unfold A
  rw [h, ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.rpow_nonneg hℓ.le _)]

/-- `U_{1/ℓ}` inverts `U_ℓ` on fields and gradient fields (TeX line 128: "It has inverse
`U_{1/ℓ}` and is a bijection on `𝒪`", with `isOccField_dil`). -/
theorem dil_inv {ℓ : ℝ} (hℓ : 0 < ℓ) (G : ℝ → Rd d → ℝ) (DG : ℝ → Rd d → Rd d) :
    dilField ℓ⁻¹ (dilField ℓ G) = G ∧ dilGrad ℓ⁻¹ (dilGrad ℓ DG) = DG := by
  have hc : (ℓ⁻¹) ^ ((d : ℝ) / 2) * ℓ ^ ((d : ℝ) / 2) = 1 := by
    rw [Real.inv_rpow hℓ.le, inv_mul_cancel₀ (by positivity)]
  have hx : ∀ x : Rd d, ℓ • ℓ⁻¹ • x = x := fun x => by
    rw [smul_smul, mul_inv_cancel₀ hℓ.ne', one_smul]
  refine ⟨?_, ?_⟩
  · funext s x
    simp only [dilField, WeakSobolev.dilL2, smul_eq_mul, hx]
    rw [← mul_assoc, hc, one_mul]
  · funext s x
    simp only [dilGrad, WeakSobolev.dilL2, hx, smul_smul]
    rw [show ℓ⁻¹ * (ℓ⁻¹ ^ ((d : ℝ) / 2) * (ℓ * ℓ ^ ((d : ℝ) / 2))) = 1 by
      calc ℓ⁻¹ * (ℓ⁻¹ ^ ((d : ℝ) / 2) * (ℓ * ℓ ^ ((d : ℝ) / 2))) =
          (ℓ⁻¹ * ℓ) * (ℓ⁻¹ ^ ((d : ℝ) / 2) * ℓ ^ ((d : ℝ) / 2)) := by ring
        _ = 1 := by rw [inv_mul_cancel₀ hℓ.ne', one_mul, hc], one_smul]

/-! ### The scalar maximum with penalty `ζ` -/

/-- The scalar maximum (TeX lines 137-141, upper half), by weighted AM-GM: for `0 < α < 2`,
`ζ > 0`, `C ≥ 0`, `X ≥ 0`, `C X^{α/2} - ζ X ≤ D_ζ C^{2/(2-α)}`,
`D_ζ = (2-α)/2 (α/(2ζ))^{α/(2-α)}` (`SpatialBracket.Dzeta`). -/
theorem scalar_max_zeta {alpha ζ C X : ℝ} (hal : 0 < alpha) (hal2 : alpha < 2) (hζ : 0 < ζ)
    (hC : 0 ≤ C) (hX : 0 ≤ X) :
    C * X ^ (alpha / 2) - ζ * X ≤ Dzeta alpha ζ * C ^ (2 / (2 - alpha)) := by
  have h2a : 0 < 2 - alpha := by linarith
  have hu : 0 < alpha / (2 * ζ) := by positivity
  set Y := C ^ (2 / (2 - alpha)) * (alpha / (2 * ζ)) ^ (alpha / (2 - alpha)) with hY
  have hY0 : 0 ≤ Y := by positivity
  have hAM := Real.geom_mean_le_arith_mean2_weighted (w₁ := alpha / 2) (w₂ := 1 - alpha / 2)
    (p₁ := 2 * ζ * X / alpha) (p₂ := Y) (by positivity) (by linarith) (by positivity) hY0
    (by ring)
  have e1 : (2 * ζ * X / alpha) ^ (alpha / 2) =
      (2 * ζ / alpha) ^ (alpha / 2) * X ^ (alpha / 2) := by
    rw [show 2 * ζ * X / alpha = 2 * ζ / alpha * X by ring, Real.mul_rpow (by positivity) hX]
  have e2 : Y ^ (1 - alpha / 2) = C * (alpha / (2 * ζ)) ^ (alpha / 2) := by
    rw [hY, Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hC,
      ← Real.rpow_mul hu.le]
    have i1 : 2 / (2 - alpha) * (1 - alpha / 2) = 1 := by field_simp
    have i2 : alpha / (2 - alpha) * (1 - alpha / 2) = alpha / 2 := by field_simp
    rw [i1, i2, Real.rpow_one]
  have e3 : (2 * ζ / alpha) ^ (alpha / 2) * (alpha / (2 * ζ)) ^ (alpha / 2) = 1 := by
    rw [← Real.mul_rpow (by positivity) hu.le,
      show 2 * ζ / alpha * (alpha / (2 * ζ)) = 1 by field_simp, Real.one_rpow]
  rw [e1, e2] at hAM
  have e4 : (2 * ζ / alpha) ^ (alpha / 2) * X ^ (alpha / 2) *
      (C * (alpha / (2 * ζ)) ^ (alpha / 2)) = C * X ^ (alpha / 2) := by
    calc _ = ((2 * ζ / alpha) ^ (alpha / 2) * (alpha / (2 * ζ)) ^ (alpha / 2)) *
          (C * X ^ (alpha / 2)) := by ring
      _ = _ := by rw [e3, one_mul]
  rw [e4] at hAM
  have e5 : alpha / 2 * (2 * ζ * X / alpha) = ζ * X := by field_simp
  rw [e5] at hAM
  have e6 : Dzeta alpha ζ * C ^ (2 / (2 - alpha)) = (1 - alpha / 2) * Y := by
    unfold Dzeta; rw [hY]; ring
  rw [e6]
  linarith

/-- The scalar maximum is attained (TeX lines 139-140): for `0 < α < 2`, `ζ > 0`, `r > 0`, at
`X = (α r/(2ζ))^{2/(2-α)}`, `r X^{α/2} - ζ X = D_ζ r^{2/(2-α)}`. -/
theorem scalar_attain_zeta {alpha ζ r : ℝ} (hal : 0 < alpha) (hal2 : alpha < 2) (hζ : 0 < ζ)
    (hr : 0 < r) :
    r * ((alpha * r / (2 * ζ)) ^ (2 / (2 - alpha))) ^ (alpha / 2) -
        ζ * (alpha * r / (2 * ζ)) ^ (2 / (2 - alpha)) =
      Dzeta alpha ζ * r ^ (2 / (2 - alpha)) := by
  have h2a : 0 < 2 - alpha := by linarith
  set u := alpha * r / (2 * ζ) with hu
  have hu0 : 0 < u := by positivity
  set e := alpha / (2 - alpha) with he
  have e0 : 2 / (2 - alpha) = 1 + e := by rw [he]; field_simp; ring
  have e1 : (u ^ (2 / (2 - alpha))) ^ (alpha / 2) = u ^ e := by
    rw [← Real.rpow_mul hu0.le, he]; congr 1; field_simp
  have e2 : u ^ (2 / (2 - alpha)) = u * u ^ e := by
    rw [e0, Real.rpow_add hu0, Real.rpow_one]
  have e3 : Dzeta alpha ζ * r ^ (2 / (2 - alpha)) = (2 - alpha) / 2 * r * u ^ e := by
    unfold Dzeta
    rw [e0, Real.rpow_add hr, Real.rpow_one, hu,
      show alpha * r / (2 * ζ) = alpha / (2 * ζ) * r by ring,
      Real.mul_rpow (by positivity) hr.le, ← he]
    ring
  rw [e1, e2, e3, hu]
  field_simp

/-! ### `P:raw-occupation-energy`, general form -/

/-- **`P:raw-occupation-energy`, general form** (TeX lines 92-147): for `d ≥ 1`, `0 ≤ a < 1`,
`0 < α < 2`, a locally finite `Γ ≠ 0` with `SetScaling α Γ`, and the supplied bounds
`SquarePairingBounds Γ α R` with `R ≥ 0`:
* the ratio set is nonempty and bounded above and `0 < C_occ ≤ K_0 R`;
* for every `ζ > 0`: the energy value set is nonempty and bounded above,
  `𝓔_ζ^𝒪 = D_ζ C_occ^{2/(2-α)}` (`E:raw-occupation-energy`),
  `C_occ = (2𝓔_ζ^𝒪/(2-α))^{(2-α)/2} (2ζ/α)^{α/2}` (`E:raw-occupation-ratio`),
  `𝓔_ζ^𝒪 > 0`, and `𝓔_ζ^𝒪 = ζ^{-α/(2-α)} 𝓔_1^𝒪`.
Route as in the TeX (lines 137-145): every member is bounded through its ratio and the scalar
maximum; the lower bound dilates members whose ratios approach `C_occ` (`isOccField_dil`,
`Araw_dil`) to the scalar optimizer and uses continuity of the positive power. -/
theorem raw_occupation_energy {a alpha R : ℝ} (hd : 0 < d) (ha0 : 0 ≤ a) (ha1 : a < 1)
    (hal : 0 < alpha) (hal2 : alpha < 2) (hR : 0 ≤ R) {Γ : Measure (Rd d)}
    [IsLocallyFiniteMeasure Γ] (hS : VariationalDilation.SetScaling alpha Γ) (hΓ : Γ ≠ 0)
    (hB : SquarePairingBounds Γ alpha R) :
    (ratioSet a alpha Γ).Nonempty ∧ BddAbove (ratioSet a alpha Γ) ∧
      0 < Cocc a alpha Γ ∧ Cocc a alpha Γ ≤ K0 a * R ∧
      ∀ ζ : ℝ, 0 < ζ →
        (energySet a Γ ζ).Nonempty ∧ BddAbove (energySet a Γ ζ) ∧
        EO a Γ ζ = Dzeta alpha ζ * Cocc a alpha Γ ^ (2 / (2 - alpha)) ∧
        Cocc a alpha Γ = (2 * EO a Γ ζ / (2 - alpha)) ^ ((2 - alpha) / 2) *
          (2 * ζ / alpha) ^ (alpha / 2) ∧
        0 < EO a Γ ζ ∧
        EO a Γ ζ = ζ ^ (-(alpha / (2 - alpha))) * EO a Γ 1 := by
  have h2a : 0 < 2 - alpha := by linarith
  -- the ratio set
  have hratio : ∀ (G : ℝ → Rd d → ℝ) (DG : ℝ → Rd d → Rd d), IsOccField G DG →
      0 ≤ A a Γ G / T DG ^ (alpha / 2) ∧ A a Γ G / T DG ^ (alpha / 2) ≤ K0 a * R := by
    intro G DG hO
    obtain ⟨-, h0, hle⟩ := raw_occupation_bound ha0 ha1 hal hal2 hR hB hO
    have hTp := Real.rpow_pos_of_pos (T_pos hd hO) (alpha / 2)
    exact ⟨div_nonneg h0 hTp.le, (div_le_iff₀ hTp).2 hle⟩
  have hbdd : BddAbove (ratioSet a alpha Γ) := by
    refine ⟨K0 a * R, ?_⟩
    rintro _ ⟨G, DG, hO, rfl⟩
    exact (hratio G DG hO).2
  obtain ⟨G0, DG0, hO0, hA0⟩ := exists_pos_member ha0 ha1 hal hal2 hR hS hΓ hB
  have hmem0 : A a Γ G0 / T DG0 ^ (alpha / 2) ∈ ratioSet a alpha Γ := ⟨G0, DG0, hO0, rfl⟩
  have hne : (ratioSet a alpha Γ).Nonempty := ⟨_, hmem0⟩
  have hCpos : 0 < Cocc a alpha Γ :=
    lt_of_lt_of_le (div_pos hA0 (Real.rpow_pos_of_pos (T_pos hd hO0) _)) (le_csSup hbdd hmem0)
  have hCle : Cocc a alpha Γ ≤ K0 a * R := by
    refine csSup_le hne ?_
    rintro _ ⟨G, DG, hO, rfl⟩
    exact (hratio G DG hO).2
  set C := Cocc a alpha Γ with hCdef
  -- each member satisfies `A ≤ C T^{α/2}`
  have hAle : ∀ (G : ℝ → Rd d → ℝ) (DG : ℝ → Rd d → Rd d), IsOccField G DG →
      A a Γ G ≤ C * T DG ^ (alpha / 2) := by
    intro G DG hO
    have hTp := Real.rpow_pos_of_pos (T_pos hd hO) (alpha / 2)
    have := le_csSup hbdd (⟨G, DG, hO, rfl⟩ : A a Γ G / T DG ^ (alpha / 2) ∈ ratioSet a alpha Γ)
    rwa [div_le_iff₀ hTp] at this
  have hE : ∀ ζ : ℝ, 0 < ζ → (energySet a Γ ζ).Nonempty ∧ BddAbove (energySet a Γ ζ) ∧
      EO a Γ ζ = Dzeta alpha ζ * C ^ (2 / (2 - alpha)) := by
    intro ζ hζ
    have hup : ∀ v ∈ energySet a Γ ζ, v ≤ Dzeta alpha ζ * C ^ (2 / (2 - alpha)) := by
      rintro _ ⟨G, DG, hO, rfl⟩
      have h1 := hAle G DG hO
      have h2 := scalar_max_zeta hal hal2 hζ hCpos.le (T_pos hd hO).le
      linarith
    have hneE : (energySet a Γ ζ).Nonempty := ⟨_, G0, DG0, hO0, rfl⟩
    have hbddE : BddAbove (energySet a Γ ζ) := ⟨_, hup⟩
    -- every positive ratio is realized at the scalar optimum by a dilation
    have hval : ∀ r ∈ ratioSet a alpha Γ, 0 < r →
        Dzeta alpha ζ * r ^ (2 / (2 - alpha)) ≤ EO a Γ ζ := by
      rintro r ⟨G, DG, hO, rfl⟩ hr
      set r := A a Γ G / T DG ^ (alpha / 2) with hrdef
      have hT := T_pos hd hO
      set X := (alpha * r / (2 * ζ)) ^ (2 / (2 - alpha)) with hX
      have hX0 : 0 < X := Real.rpow_pos_of_pos (by positivity) _
      set ℓ := Real.sqrt (X / T DG) with hℓdef
      have hℓ : 0 < ℓ := Real.sqrt_pos.2 (div_pos hX0 hT)
      obtain ⟨hOd, hTd⟩ := isOccField_dil hℓ hO
      have := hΓ
      have hAd := (Araw_dil hS hℓ a G).2
      have hℓ2 : ℓ ^ 2 = X / T DG := Real.sq_sqrt (div_pos hX0 hT).le
      have hTd' : T (dilGrad ℓ DG) = X := by
        unfold T; rw [hTd, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]
        unfold T at hℓ2 hT
        rw [hℓ2, div_mul_cancel₀ _ hT.ne']
      have hℓα : ℓ ^ alpha = X ^ (alpha / 2) / T DG ^ (alpha / 2) := by
        rw [show ℓ ^ alpha = (ℓ ^ 2) ^ (alpha / 2) by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hℓ.le]; congr 1; push_cast; ring, hℓ2,
          Real.div_rpow hX0.le hT.le]
      have hAr : A a Γ G = r * T DG ^ (alpha / 2) := by
        rw [hrdef, div_mul_cancel₀ _ (Real.rpow_pos_of_pos hT _).ne']
      have hv : A a Γ (dilField ℓ G) - ζ * T (dilGrad ℓ DG) =
          Dzeta alpha ζ * r ^ (2 / (2 - alpha)) := by
        rw [hAd, hTd', hℓα, hAr, ← scalar_attain_zeta hal hal2 hζ hr, ← hX]
        field_simp
      rw [← hv]
      exact le_csSup hbddE ⟨_, _, hOd, rfl⟩
    have hge : Dzeta alpha ζ * C ^ (2 / (2 - alpha)) ≤ EO a Γ ζ := by
      obtain ⟨u, -, hu, hmem⟩ := exists_seq_tendsto_sSup hne hbdd
      have hcont : Continuous fun x : ℝ => Dzeta alpha ζ * x ^ (2 / (2 - alpha)) :=
        continuous_const.mul (Real.continuous_rpow_const (by positivity))
      refine le_of_tendsto ((hcont.tendsto _).comp hu) ?_
      filter_upwards [hu.eventually (lt_mem_nhds hCpos)] with n hn
      exact hval (u n) (hmem n) hn
    exact ⟨hneE, hbddE, le_antisymm (csSup_le hneE hup) hge⟩
  refine ⟨hne, hbdd, hCpos, hCle, fun ζ hζ => ?_⟩
  obtain ⟨hneE, hbddE, hEq⟩ := hE ζ hζ
  have hDpos : ∀ z : ℝ, 0 < z → 0 < Dzeta alpha z := fun z hz => by
    unfold Dzeta
    exact mul_pos (by linarith) (Real.rpow_pos_of_pos (by positivity) _)
  have hEpos : 0 < EO a Γ ζ := by
    rw [hEq]; exact mul_pos (hDpos ζ hζ) (Real.rpow_pos_of_pos hCpos _)
  refine ⟨hneE, hbddE, hEq, ?_, hEpos, ?_⟩
  · -- `E:raw-occupation-ratio`
    have hu : 0 < alpha / (2 * ζ) := by positivity
    have e1 : 2 * EO a Γ ζ / (2 - alpha) =
        (alpha / (2 * ζ)) ^ (alpha / (2 - alpha)) * C ^ (2 / (2 - alpha)) := by
      rw [hEq]; unfold Dzeta; field_simp
    rw [e1, Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hu.le,
      ← Real.rpow_mul hCpos.le,
      show alpha / (2 - alpha) * ((2 - alpha) / 2) = alpha / 2 by field_simp,
      show 2 / (2 - alpha) * ((2 - alpha) / 2) = 1 by field_simp, Real.rpow_one,
      mul_comm ((alpha / (2 * ζ)) ^ (alpha / 2)) C, mul_assoc, ← Real.mul_rpow hu.le
        (by positivity), show alpha / (2 * ζ) * (2 * ζ / alpha) = 1 by field_simp,
      Real.one_rpow, mul_one]
  · -- penalty scaling
    rw [hEq, (hE 1 one_pos).2.2]
    unfold Dzeta
    rw [Real.div_rpow hal.le (by positivity), Real.div_rpow hal.le (by norm_num),
      Real.mul_rpow (by norm_num) hζ.le, Real.rpow_neg hζ.le, mul_one]
    field_simp

/-! ### The manuscript's statement -/

/-- **`P:raw-occupation-energy`** (`integrated_occupation_ceiling.tex` lines 92-112, proof
114-147, at a284420), under the section's standing assumptions (lines 4-21: the original
covariance under `H:homog` with `a = α₀`, `Γ ≠ 0`), with `K_0 = 2^a/(1-a)` and
`R_sp = SpatialFourLinear.Rsp`:
* `0 < C_occ ≤ K_0 R_sp`, the ratio set being nonempty and bounded above (a real number,
  hence finite);
* for every field of `𝒪`: `0 < T(g) < ∞`, `A(g) < ∞` and `0 ≤ A(g) ≤ K_0 R_sp T(g)^{α/2}`
  (`E:raw-occupation-bound`); for every `ℓ > 0`, `U_ℓ g` lies in `𝒪`,
  `A(U_ℓ g) = ℓ^α A(g)`, `T(U_ℓ g) = ℓ² T(g)`, and `U_{1/ℓ}` inverts `U_ℓ`;
* for every `ζ > 0`: the energy value set is nonempty and bounded above,
  `𝓔_ζ^𝒪 = D_ζ C_occ^{2/(2-α)}` (`E:raw-occupation-energy`),
  `C_occ = (2𝓔_ζ^𝒪/(2-α))^{(2-α)/2}(2ζ/α)^{α/2}` (`E:raw-occupation-ratio`),
  `𝓔_ζ^𝒪 > 0` and `𝓔_ζ^𝒪 = ζ^{-α/(2-α)} 𝓔_1^𝒪`.
Narrower than the TeX (recorded): the class `𝒪` is modelled by joint representatives
(`OccupationPhysicalClass.IsOccField`), as for `P:occupation-physical-class`.  No input is
supplied: `SquarePairingBounds Γ α R_0` is `SpatialOccupationL7Completed.squarePairingBounds_holds`
and `R_sp = R_0` is `SpatialOccupationL7Completed.spatial_ratio_H1_paper_completed`. -/
theorem raw_occupation_energy_paper {alpha a : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogCovariance d alpha a Γ μ) (hΓ : Γ ≠ 0) :
    (ratioSet a alpha Γ).Nonempty ∧ BddAbove (ratioSet a alpha Γ) ∧
    0 < Cocc a alpha Γ ∧ Cocc a alpha Γ ≤ K0 a * SpatialFourLinear.Rsp Γ alpha ∧
    (∀ (G : ℝ → Rd d → ℝ) (DG : ℝ → Rd d → Rd d), IsOccField G DG →
      0 < T DG ∧ Araw a Γ G < ⊤ ∧ 0 ≤ A a Γ G ∧
      A a Γ G ≤ K0 a * SpatialFourLinear.Rsp Γ alpha * T DG ^ (alpha / 2) ∧
      ∀ ℓ : ℝ, 0 < ℓ → IsOccField (dilField ℓ G) (dilGrad ℓ DG) ∧
        A a Γ (dilField ℓ G) = ℓ ^ alpha * A a Γ G ∧
        T (dilGrad ℓ DG) = ℓ ^ 2 * T DG ∧
        dilField ℓ⁻¹ (dilField ℓ G) = G ∧ dilGrad ℓ⁻¹ (dilGrad ℓ DG) = DG) ∧
    ∀ ζ : ℝ, 0 < ζ →
      (energySet a Γ ζ).Nonempty ∧ BddAbove (energySet a Γ ζ) ∧
      EO a Γ ζ = Dzeta alpha ζ * Cocc a alpha Γ ^ (2 / (2 - alpha)) ∧
      Cocc a alpha Γ = (2 * EO a Γ ζ / (2 - alpha)) ^ ((2 - alpha) / 2) *
        (2 * ζ / alpha) ^ (alpha / 2) ∧
      0 < EO a Γ ζ ∧
      EO a Γ ζ = ζ ^ (-(alpha / (2 - alpha))) * EO a Γ 1 := by
  have := hH.Γ_radon
  obtain ⟨hd, hal, hal2, -⟩ := SpatialSmoothRatio.homog_consequences hH
  have hR : 0 ≤ SpatialSmoothRatio.R0 Γ alpha :=
    (SpatialSmoothRatio.spatial_smooth_ratio_R0_paper hH hΓ).2.2.2.2.1.le
  have hB := SpatialOccupationL7Completed.squarePairingBounds_holds hH hΓ
  have hRsp := (SpatialOccupationL7Completed.spatial_ratio_H1_paper_completed hH hΓ).2.2.2
  have ha0 := hH.alpha0_pos.le
  have ha1 := hH.alpha0_lt_one
  obtain ⟨h1, h2, h3, h4, h5⟩ := raw_occupation_energy hd ha0 ha1 hal hal2 hR hH.scaling hΓ hB
  rw [hRsp]
  refine ⟨h1, h2, h3, h4, fun G DG hO => ?_, h5⟩
  obtain ⟨b1, b2, b3⟩ := raw_occupation_bound ha0 ha1 hal hal2 hR hB hO
  refine ⟨T_pos hd hO, b1, b2, b3, fun ℓ hℓ => ?_⟩
  obtain ⟨hOd, hTd⟩ := isOccField_dil hℓ hO
  refine ⟨hOd, (Araw_dil hH.scaling hℓ a G).2, ?_, (dil_inv hℓ G DG).1, (dil_inv hℓ G DG).2⟩
  unfold T
  rw [hTd, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]

end StratonovichHAMSecondMoment.RawOccupationEnergy
