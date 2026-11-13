module

/-
Copyright 2026 Le Chen. SPDX-License-Identifier: Apache-2.0

Wave L8, item L8-c1: step (c) of the deterministic discharge of `S1Bdd`
(`VariationalRate.S1Bdd`, the boundedness claim of `P:variational-positive-scores`) by the
route of feasibility report R2 (finite hat partition in place of the countable selection;
decision 3 of wave L8).  Everything here is a route step, auxiliary to the Lean route, except
where a doc comment names a TeX display it formalizes in narrower form.  TeX at revision
a284420:
* `notes/integrated_occupation_ceiling.tex` (whole section lines 1-308): standing
  assumptions lines 4-21 (`a = α₀`, `K(s,t) = |s-t|^{-a}` on `I = (0,1)`, `Γ ≠ 0`); the
  form `A(g)` of `E:raw-occupation-definitions` (lines 10-18); `L:occupation-raw-square`
  (statement lines 23-42, proof 44-90): `E:occupation-raw-identities` (lines 33-37) and the
  bound `⟨Ψ,ρ_g⟩ ≤ √(v_Ψ A(g))` (line 40).
* `notes/integrated_intrinsic_constant.tex`: `L:positive-raw-embedding` (statement lines
  22-39): `E:positive-bochner-inclusion` (lines 26-30) and the first identity
  `‖Ψ‖²_{H_I} = v_Ψ` of `E:positive-raw-mean` (lines 33-36).
* `notes/integrated_unmasked_variational.tex` lines 4-19 and
  `notes/integrated_compact_mean_family.tex` lines 402-411: `C_pos`, `h_{Ψ,s}`
  (`E:compact-raw-mean`) and `v_Ψ` (`E:compact-raw-cost`), reused here as
  `VariationalDilation.CPos`, `VariationalDilation.mean`, `VariationalDilation.rawCost`.

Objects (reused, not redefined): the physical pairing `B_Γ(F,G) = ∫ (∫ F(x) G(x-y) dx) Γ(dy)`
is `SpatialFourierBound.spatialPair`; the time kernel is `TimeSchur.kern a (s - t) =
|s-t|^{-a}`; its mixture is `TimeCompletion.mixWeight`, `mixProfile`, `mixMeasure`.  New:
`timeMeasure` (Lebesgue measure on `(0,1)`), `stPair Γ Φ₁ Φ₂ (s,t) = B_Γ(Φ₁(s,·), Φ₂(t,·))`
and the space-time form
`stForm a Γ Φ₁ Φ₂ = F(Φ₁,Φ₂) = ∫∫_{(0,1)²} |s-t|^{-a} B_Γ(Φ₁(s,·), Φ₂(t,·)) ds dt`
(a Bochner integral over the product measure); fields are `Φ : ℝ × ℝ^d → ℝ`, the convention of
`CPos`.  The field class of every statement is: continuous with compact support in
`ℝ × ℝ^d` (in space-time).  Auxiliary definitions: `tAvg`, `mixIntegrand`.

Interfaces for the integrator and for item L8-c2 (exact statements in the theorems):
* `stIntegrand_integrable` (`a < 1`, locally finite `Γ`, `Φ₁, Φ₂` continuous compactly
  supported): the integrand of `stForm a Γ Φ₁ Φ₂` is integrable on `(0,1)²`.
* (1) `stForm_self_nonneg` (`0 < a < 1`, locally finite `Γ`, `IsSpectralMeasure Γ μ`, `Φ`
  continuous compactly supported): `0 ≤ stForm a Γ Φ Φ`.
* (2) `stForm_sq_le` (`0 < a < 1`, locally finite even `Γ`, `IsSpectralMeasure Γ μ`, `Ψ, G`
  continuous compactly supported): `stForm a Γ Ψ G ^ 2 ≤ stForm a Γ Ψ Ψ * stForm a Γ G G`.
* (3a) `stForm_self_eq_rawCost` (`a < 1`, locally finite `Γ`, `Ψ` continuous compactly
  supported; in particular `Ψ ∈ CPos d`): `stForm a Γ Ψ Ψ = rawCost a Γ Ψ`.
* (3b) `integral_mean_mul_eq_stForm` (`a < 1`, locally finite even `Γ`, `Ψ, Φ` continuous
  compactly supported): integrability of `x ↦ mean a Γ Ψ t x * Φ (t, x)` for `t ∈ [0,1]` and
  of `t ↦ ∫ x, mean a Γ Ψ t x * Φ (t, x)` on `(0,1)`, and
  `∫ t in Ioo 0 1, ∫ x, mean a Γ Ψ t x * Φ (t, x) = stForm a Γ Ψ Φ`; the squared-field
  instance `integral_mean_mul_sq_eq_stForm` (`Φ = G²`), and the order-swapped form
  `integral_mean_mul_eq_stForm_swap` (`= stForm a Γ Φ Ψ`, no evenness).
* `integral_mean_mul_le_sqrt`: (2) + (3a) + (3b), `∫∫ h_Ψ Φ ≤ √(v_Ψ F(Φ,Φ))`.
* Bilinearity and symmetry: `stForm_quad`, `stForm_comm`.
* Under `H:homog` with `a = α₀`: `space_time_positivity_homog` (all of the above, `Ψ ∈ CPos`).
* For item L8-c2: `spaceTimeCS_holds : SpaceTimeCS α₀ Γ` under `H:homog`, where `SpaceTimeCS`
  and `stFormIter` are verbatim `OccupationCeilingFinite.SpaceTimeCS` and
  `OccupationCeilingFinite.stForm` (iterated integral); `stFormIter_eq` identifies
  `stFormIter` with `stForm` for continuous compactly supported fields.

Formalized (narrower forms of TeX displays):
* `occupation_raw_square_cc_paper`: `L:occupation-raw-square` for continuous compactly
  supported profiles `g` in place of the class `O`: `A(g) = F(g²,g²) ≥ 0`,
  `∫_I ∫ h_{Ψ,t} g_t² = F(Ψ, g²)` and the bound `≤ √(v_Ψ A(g))`, with the section's exact
  standing hypotheses (`H:homog`, `a = α₀`, `Γ ≠ 0`; `Γ ≠ 0` carried, unused).  Not
  formalized: `H_sp`, the map `Q`, `ρ_g ∈ H_I`, `‖ρ_g‖² = A(g)`, the class `O`.
* `positive_raw_variance_form_paper`: the integral form of `‖Ψ‖²_{H_I} = v_Ψ`
  (`E:positive-raw-mean`, via `E:positive-bochner-inclusion`) with the section's standing
  hypotheses (`Γ ≠ 0` carried, unused).  Not formalized: `H_t`, `H_I`, `J_G`, the bound by
  `K_0`, the mean identity `T_R Ψ(s) = B_E(m_R h_{Ψ,s})`.

Supplied inputs: none (no named analytic hypotheses; the fallback `SpaceTimePosDef` of
decision 3 was not needed).

Implicit hypotheses made explicit: continuity and compact support of the fields (the TeX's
fields live in `L²(I; H_sp)`); integrability of every integrand is a conclusion
(`stIntegrand_integrable`, the first two clauses of `integral_mean_mul_eq_stForm`), so no
statement holds through Lean's junk value `0` of a non-integrable Bochner integral;
`0 < a` for positivity (the mixture `TimeCompletion.kern_eq_mixture` needs it; `H:homog` has
`α₀ > 0`) and `a < 1` for integrability.  Local finiteness of `Γ` replaces the TeX's
physical covariance bound `E:positive-local-spatial-bound` (intrinsic lines 68-75).

Proof route (differs from the TeX, which works in the completed Hilbert spaces `H_sp`,
`H_t ⊗ H_sp`):
* spatial positivity `B_Γ(Q,Q) ≥ 0` for continuous compactly supported `Q`: uniform
  approximation by mollification (`exists_smooth_approx`, from `H1Density.mollify`),
  `SpatialFourLinear.spatialPair_self_nonneg` for the smooth approximants, the bilinear
  expansion `SpatialFourLinear.spatialPair_quad` and the local bound `abs_spatialPair_le`;
* space-time positivity: `|s-t|^{-a} = ∫ ρ(w) φ_w(s) φ_w(t) dν(w)` off the diagonal
  (`TimeCompletion.kern_eq_mixture`), Fubini on `I² × ((0,∞) × ℝ)` (`mixIntegrand_data`),
  and `∫∫ φ_w(s) φ_w(t) B_Γ(Φ_s,Φ_t) = B_Γ(Q_w,Q_w)` with `Q_w = ∫_I φ_w Φ_s ds`
  (`weighted_stPair`, a four-fold Fubini), so `F(Φ,Φ) = ∫ ρ(w) B_Γ(Q_w,Q_w) dν(w) ≥ 0`;
* Cauchy-Schwarz by the discriminant (`discrim_le_zero`) of `t ↦ F(Ψ+tG, Ψ+tG)`, with
  symmetry from the evenness of `Γ` (`SpatialFourLinear.spatialPair_comm`);
* the identities by Fubini: `B_Γ(F,G) = ∫ F (Γ * G)` (`spatialPair_eq_conv`), then the time
  integral `∫_I |t-s|^{-a} (Γ * Ψ_s)(x) ds = h_{Ψ,t}(x)` (`integral_mean_mul_eq_stForm_swap`).

Lemmas whose doc comments say "Auxiliary" have no manuscript label.
-/
public import Mathlib
public import StratonovichHAMSecondMoment.SpatialFourLinear
public import StratonovichHAMSecondMoment.TimeCompletion
public import StratonovichHAMSecondMoment.VariationalRate
public import StratonovichHAMSecondMoment.H1Density

@[expose] public section

noncomputable section

set_option autoImplicit false

open MeasureTheory Set Filter Metric Topology
open scoped ContDiff ENNReal

namespace StratonovichHAMSecondMoment.SpaceTimePositivity

open HomogHypothesis (Rd HomogCovariance IsSpectralMeasure IsEven)
open WeakSobolev (IsTestFunction)
open SpatialFourierBound (spatialPair)
open TimeSchur (kern kern_nonneg measurable_kern)
open VariationalDilation (CPos conv mean rawCost)

variable {d : ℕ}

/-! ### The spatial pairing on continuous compactly supported profiles -/

/-- Auxiliary to the Lean proof route: if `F` vanishes for `|x| > R` and `G` vanishes for
`|x| > R`, then the inner integral `y ↦ ∫ F(x) G(x-y) dx` of `B_Γ(F,G)` vanishes for
`|y| > 2R`. -/
theorem cross_eq_zero {F G : Rd d → ℝ} {R : ℝ} (hFR : ∀ x, R < ‖x‖ → F x = 0)
    (hGR : ∀ x, R < ‖x‖ → G x = 0) {y : Rd d} (hy : 2 * R < ‖y‖) :
    ∫ x, F x * G (x - y) = 0 := by
  have h : ∀ x, F x * G (x - y) = 0 := by
    intro x
    by_cases hx : R < ‖x‖
    · rw [hFR x hx, zero_mul]
    · have h1 : ‖y‖ ≤ ‖x‖ + ‖x - y‖ := by
        have := norm_sub_le x (x - y)
        simpa using this
      rw [hGR (x - y) (by linarith), mul_zero]
  simp [h]

/-- Auxiliary to the Lean proof route: the inner integral is bounded,
`|∫ F(x) G(x-y) dx| ≤ |B_R| A B` when `F` vanishes for `|x| > R`, `|F| ≤ A`, `|G| ≤ B`
(no integrability assumed: a non-integrable integrand has Bochner integral `0`). -/
theorem abs_cross_le {F G : Rd d → ℝ} {R A B : ℝ} (hFR : ∀ x, R < ‖x‖ → F x = 0)
    (hA : ∀ x, |F x| ≤ A) (hB : ∀ x, |G x| ≤ B) (y : Rd d) :
    |∫ x, F x * G (x - y)| ≤ A * B * volume.real (closedBall (0 : Rd d) R) := by
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := closedBall (0 : Rd d) R)
    fun x hx => by
      rw [mem_closedBall, dist_zero_right, not_le] at hx
      rw [hFR x hx, zero_mul], ← Real.norm_eq_abs]
  refine norm_setIntegral_le_of_norm_le_const
    (measure_closedBall_lt_top (μ := (volume : Measure (Rd d))))
    fun x _ => ?_
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul (hA x) (hB _) (abs_nonneg _) ((abs_nonneg _).trans (hA x))

/-- Auxiliary to the Lean proof route (the local bound `E:positive-local-spatial-bound` of
`L:positive-raw-embedding`, in bilinear form): for a locally finite `Γ` and `F`, `G` vanishing
for `|x| > R` with `|F| ≤ A`, `|G| ≤ B`,
`|B_Γ(F,G)| ≤ A B |B_R| Γ(B_{2R})`. -/
theorem abs_spatialPair_le (Γ : Measure (Rd d)) [IsLocallyFiniteMeasure Γ] {F G : Rd d → ℝ}
    {R A B : ℝ} (hFR : ∀ x, R < ‖x‖ → F x = 0) (hGR : ∀ x, R < ‖x‖ → G x = 0)
    (hA : ∀ x, |F x| ≤ A) (hB : ∀ x, |G x| ≤ B) :
    |spatialPair Γ F G| ≤
      A * B * volume.real (closedBall (0 : Rd d) R) * Γ.real (closedBall (0 : Rd d) (2 * R)) := by
  unfold spatialPair
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := closedBall (0 : Rd d) (2 * R))
    fun y hy => by
      rw [mem_closedBall, dist_zero_right, not_le] at hy
      exact cross_eq_zero hFR hGR hy]
  rw [← Real.norm_eq_abs]
  exact norm_setIntegral_le_of_norm_le_const measure_closedBall_lt_top fun y _ => by
    rw [Real.norm_eq_abs]; exact abs_cross_le hFR hA hB y

/-- Auxiliary to the Lean proof route: a continuous `Q` vanishing for `|x| > R` has compact
support. -/
theorem hasCompactSupport_of_radius {Q : Rd d → ℝ} {R : ℝ} (hQR : ∀ x, R < ‖x‖ → Q x = 0) :
    HasCompactSupport Q :=
  HasCompactSupport.intro (isCompact_closedBall (0 : Rd d) R) fun x hx => by
    rw [mem_closedBall, dist_zero_right, not_le] at hx
    exact hQR x hx

/-- Auxiliary to the Lean proof route (mollification, in place of the TeX's smooth
approximation in `L:occupation-raw-square`): a continuous `Q` vanishing for `|x| > R` is
uniformly within `δ > 0` of a test function vanishing for `|x| > R + 1`. -/
theorem exists_smooth_approx {Q : Rd d → ℝ} (hQ : Continuous Q) {R : ℝ}
    (hQR : ∀ x, R < ‖x‖ → Q x = 0) {δ : ℝ} (hδ : 0 < δ) :
    ∃ P : Rd d → ℝ, IsTestFunction P ∧ (∀ x, R + 1 < ‖x‖ → P x = 0) ∧
      ∀ x, |P x - Q x| ≤ δ := by
  have hQc := hasCompactSupport_of_radius hQR
  obtain ⟨η, hη, hηc⟩ := Metric.uniformContinuous_iff.mp
    (hQc.uniformContinuous_of_continuous hQ) δ hδ
  set r : ℝ := min η 1 with hr
  have hr0 : 0 < r := lt_min hη one_pos
  let φ : ContDiffBump (0 : Rd d) := ⟨r / 2, r, half_pos hr0, half_lt_self hr0⟩
  refine ⟨H1Density.mollify φ Q, ⟨H1Density.contDiff_mollify φ hQ.locallyIntegrable,
    φ.hasCompactSupport_normed.convolution _ hQc⟩, fun x hx => ?_, fun x => ?_⟩
  · by_contra hne
    have hs := (support_convolution_subset (L := ContinuousLinearMap.lsmul ℝ ℝ)
      (μ := volume) (f := φ.normed volume) (g := Q)) hne
    rw [φ.support_normed_eq] at hs
    obtain ⟨u, hu, v, hv, rfl⟩ := hs
    have hu' : ‖u‖ < r := by simpa using hu
    have hv' : ‖v‖ ≤ R := by
      by_contra h
      exact hv (hQR v (not_le.1 h))
    have : ‖u + v‖ ≤ ‖u‖ + ‖v‖ := norm_add_le u v
    have : r ≤ 1 := min_le_right _ _
    linarith
  · rw [← Real.dist_eq]
    refine φ.dist_normed_convolution_le hQ.aestronglyMeasurable fun y hy => ?_
    have hy' : dist y x < r := hy
    exact (hηc (lt_of_lt_of_le hy' (min_le_left _ _))).le

/-- **Spatial positivity for continuous compactly supported profiles** (a step of the route,
auxiliary; the TeX obtains it inside the covariance space `H_sp`, `L:occupation-raw-square`):
for a locally finite `Γ` with spectral measure `μ` in the manuscript's convention and a
continuous `Q` vanishing for `|x| > R`, `B_Γ(Q,Q) ≥ 0`.  Route: smooth uniform approximants
(mollification) with `SpatialFourLinear.spatialPair_self_nonneg`, the bilinear expansion
`SpatialFourLinear.spatialPair_quad` and the local bound `abs_spatialPair_le`. -/
theorem spatialPair_self_nonneg_of_continuous {Γ μ : Measure (Rd d)} [IsLocallyFiniteMeasure Γ]
    (hsp : IsSpectralMeasure Γ μ) {Q : Rd d → ℝ} (hQ : Continuous Q) {R : ℝ}
    (hQR : ∀ x, R < ‖x‖ → Q x = 0) : 0 ≤ spatialPair Γ Q Q := by
  have hQc := hasCompactSupport_of_radius hQR
  obtain ⟨A, hA⟩ := hQ.bounded_above_of_compact_support hQc
  have hA' : ∀ x, |Q x| ≤ A := fun x => by simpa using hA x
  have hA0 : 0 ≤ A := (abs_nonneg _).trans (hA' 0)
  set c : ℝ := volume.real (closedBall (0 : Rd d) (R + 1)) *
    Γ.real (closedBall (0 : Rd d) (2 * (R + 1))) with hc
  have hc0 : 0 ≤ c := mul_nonneg measureReal_nonneg measureReal_nonneg
  have hQR1 : ∀ x, R + 1 < ‖x‖ → Q x = 0 := fun x hx => hQR x (by linarith)
  refine le_of_forall_pos_le_add fun ε hε => ?_
  set δ : ℝ := min 1 (ε / (c * (2 * A + 1) + 1)) with hδ
  have hD : 0 < c * (2 * A + 1) + 1 := by positivity
  have hδ0 : 0 < δ := lt_min one_pos (div_pos hε hD)
  obtain ⟨P, hP, hPR, hPQ⟩ := exists_smooth_approx hQ hQR hδ0
  set D : Rd d → ℝ := fun x => P x - Q x with hDdef
  have hDc : Continuous D := hP.1.continuous.sub hQ
  have hDR : ∀ x, R + 1 < ‖x‖ → D x = 0 := fun x hx => by
    simp [hDdef, hPR x hx, hQR1 x hx]
  have hDs := hasCompactSupport_of_radius hDR
  have hquad := SpatialFourLinear.spatialPair_quad Γ hQ hQc hDc hDs 1
  have hPe : (fun x => Q x + 1 * D x) = P := by funext x; simp [hDdef]
  rw [hPe, one_mul, one_pow, one_mul] at hquad
  have hPP := SpatialFourLinear.spatialPair_self_nonneg hsp hP
  have b1 := abs_spatialPair_le Γ hQR1 hDR hA' hPQ
  have b2 := abs_spatialPair_le Γ hDR hQR1 hPQ hA'
  have b3 := abs_spatialPair_le Γ hDR hDR hPQ hPQ
  have e1 : A * δ * volume.real (closedBall (0 : Rd d) (R + 1)) *
      Γ.real (closedBall (0 : Rd d) (2 * (R + 1))) = c * (A * δ) := by rw [hc]; ring
  have e2 : δ * A * volume.real (closedBall (0 : Rd d) (R + 1)) *
      Γ.real (closedBall (0 : Rd d) (2 * (R + 1))) = c * (A * δ) := by rw [hc]; ring
  have e3 : δ * δ * volume.real (closedBall (0 : Rd d) (R + 1)) *
      Γ.real (closedBall (0 : Rd d) (2 * (R + 1))) = c * (δ * δ) := by rw [hc]; ring
  rw [e1] at b1; rw [e2] at b2; rw [e3] at b3
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδε : δ * (c * (2 * A + 1) + 1) ≤ ε := by
    have := min_le_right 1 (ε / (c * (2 * A + 1) + 1))
    rw [← hδ] at this
    calc δ * (c * (2 * A + 1) + 1) ≤ ε / (c * (2 * A + 1) + 1) * (c * (2 * A + 1) + 1) :=
          mul_le_mul_of_nonneg_right this hD.le
      _ = ε := div_mul_cancel₀ _ hD.ne'
  have hsq : c * (δ * δ) ≤ c * δ := mul_le_mul_of_nonneg_left
    (by nlinarith) hc0
  have k1 := le_abs_self (spatialPair Γ Q D)
  have k2 := le_abs_self (spatialPair Γ D Q)
  have k3 := le_abs_self (spatialPair Γ D D)
  have hcA : 0 ≤ c * (A * δ) := by positivity
  have hlin : δ * (c * (2 * A + 1) + 1) = 2 * (c * (A * δ)) + c * δ + δ := by ring
  linarith

/-- Auxiliary to the Lean proof route: bilinear expansion of the real pairing,
`B_Γ(Q₁+tP₁, Q₂+tP₂) = B_Γ(Q₁,Q₂) + t (B_Γ(Q₁,P₂) + B_Γ(P₁,Q₂)) + t² B_Γ(P₁,P₂)`, for
continuous compactly supported profiles and locally finite `Γ` (the two-slot form of
`SpatialFourLinear.spatialPair_quad`). -/
theorem spatialPair_bilin (Γ : Measure (Rd d)) [IsLocallyFiniteMeasure Γ]
    {Q₁ Q₂ P₁ P₂ : Rd d → ℝ} (hQ₁ : Continuous Q₁) (hQ₁s : HasCompactSupport Q₁)
    (hQ₂ : Continuous Q₂) (hQ₂s : HasCompactSupport Q₂) (hP₁ : Continuous P₁)
    (hP₁s : HasCompactSupport P₁) (hP₂ : Continuous P₂) (hP₂s : HasCompactSupport P₂) (t : ℝ) :
    spatialPair Γ (fun x => Q₁ x + t * P₁ x) (fun x => Q₂ x + t * P₂ x) =
      spatialPair Γ Q₁ Q₂ + t * (spatialPair Γ Q₁ P₂ + spatialPair Γ P₁ Q₂) +
        t ^ 2 * spatialPair Γ P₁ P₂ := by
  have hin : ∀ y, ∫ x, (Q₁ x + t * P₁ x) * (Q₂ (x - y) + t * P₂ (x - y)) =
      (∫ x, Q₁ x * Q₂ (x - y)) + (t * ((∫ x, Q₁ x * P₂ (x - y)) + ∫ x, P₁ x * Q₂ (x - y)) +
        t ^ 2 * ∫ x, P₁ x * P₂ (x - y)) := by
    intro y
    have i1 := SpatialFourLinear.inner_integrable hQ₁ hQ₁s hQ₂ y
    have i2 := SpatialFourLinear.inner_integrable hQ₁ hQ₁s hP₂ y
    have i3 := SpatialFourLinear.inner_integrable hP₁ hP₁s hQ₂ y
    have i4 := SpatialFourLinear.inner_integrable hP₁ hP₁s hP₂ y
    have e : (fun x => (Q₁ x + t * P₁ x) * (Q₂ (x - y) + t * P₂ (x - y))) = fun x =>
        Q₁ x * Q₂ (x - y) + (t * (Q₁ x * P₂ (x - y) + P₁ x * Q₂ (x - y)) +
          t ^ 2 * (P₁ x * P₂ (x - y))) := by
      funext x; ring
    have k2 : Integrable (fun x => t * (Q₁ x * P₂ (x - y) + P₁ x * Q₂ (x - y))) volume :=
      (i2.add i3).const_mul t
    have k3 : Integrable (fun x => t ^ 2 * (P₁ x * P₂ (x - y))) volume := i4.const_mul _
    have k1 : Integrable (fun x => t * (Q₁ x * P₂ (x - y) + P₁ x * Q₂ (x - y)) +
        t ^ 2 * (P₁ x * P₂ (x - y))) volume := k2.add k3
    rw [e, integral_add i1 k1, integral_add k2 k3, integral_const_mul,
      integral_const_mul, integral_add i2 i3]
  have j1 := SpatialFourLinear.cross_integrable Γ hQ₁ hQ₁s hQ₂ hQ₂s
  have j2 := SpatialFourLinear.cross_integrable Γ hQ₁ hQ₁s hP₂ hP₂s
  have j3 := SpatialFourLinear.cross_integrable Γ hP₁ hP₁s hQ₂ hQ₂s
  have j4 := SpatialFourLinear.cross_integrable Γ hP₁ hP₁s hP₂ hP₂s
  unfold spatialPair
  simp_rw [hin]
  have k2 : Integrable (fun y => t * ((∫ x, Q₁ x * P₂ (x - y)) + ∫ x, P₁ x * Q₂ (x - y))) Γ :=
    (j2.add j3).const_mul t
  have k3 : Integrable (fun y => t ^ 2 * ∫ x, P₁ x * P₂ (x - y)) Γ := j4.const_mul _
  have k1 : Integrable (fun y => t * ((∫ x, Q₁ x * P₂ (x - y)) + ∫ x, P₁ x * Q₂ (x - y)) +
      t ^ 2 * ∫ x, P₁ x * P₂ (x - y)) Γ := k2.add k3
  rw [integral_add j1 k1, integral_add k2 k3, integral_const_mul, integral_const_mul,
    integral_add j2 j3]
  ring

/-! ### The space-time form -/

/-- Lebesgue measure on the time interval `I = (0,1)` (TeX: `K(s,t) = |s-t|^{-a}` on
`I = (0,1)`, `integrated_occupation_ceiling.tex` lines 5-6). -/
abbrev timeMeasure : Measure ℝ := volume.restrict (Ioo (0 : ℝ) 1)

/-- Auxiliary: `(0,1)` and `[0,1]` carry the same restricted Lebesgue measure. -/
theorem timeMeasure_eq_Icc : timeMeasure = volume.restrict (Icc (0 : ℝ) 1) :=
  Measure.restrict_congr_set Ioo_ae_eq_Icc

/-- The physical pairing of the time slices of two space-time fields,
`(s,t) ↦ B_Γ(Φ₁(s,·), Φ₂(t,·))` (`SpatialFourierBound.spatialPair`, the real form of
`E:spatial-physical-pair`). -/
def stPair (Γ : Measure (Rd d)) (Φ₁ Φ₂ : ℝ × Rd d → ℝ) (p : ℝ × ℝ) : ℝ :=
  spatialPair Γ (fun x => Φ₁ (p.1, x)) (fun x => Φ₂ (p.2, x))

/-- **The space-time form** `F(Φ₁,Φ₂) = ∫∫_{I²} |s-t|^{-a} B_Γ(Φ₁(s,·), Φ₂(t,·)) ds dt`
(the integral on the right of `E:positive-bochner-inclusion`,
`integrated_intrinsic_constant.tex` lines 26-30, for the physical pairing; and the form
`A(g)` of `E:raw-occupation-definitions` at `Φ₁ = Φ₂ = g²`), as a Bochner integral over
`I² = (0,1)²` with the product Lebesgue measure.  The time kernel is
`TimeSchur.kern a (s - t) = |s-t|^{-a}` (Lean's `rpow`; its diagonal value is irrelevant,
the diagonal is null).  It is the manuscript's integral only where the integrand is
integrable; `stIntegrand_integrable` proves this for continuous compactly supported fields. -/
def stForm (a : ℝ) (Γ : Measure (Rd d)) (Φ₁ Φ₂ : ℝ × Rd d → ℝ) : ℝ :=
  ∫ p, kern a (p.1 - p.2) * stPair Γ Φ₁ Φ₂ p ∂(timeMeasure.prod timeMeasure)

/-- Auxiliary to the Lean proof route: the time average `x ↦ ∫_I f(s) Φ(s,x) ds` of a field
against a weight `f` (`Q_w` of the mixture route). -/
def tAvg (f : ℝ → ℝ) (Φ : ℝ × Rd d → ℝ) (x : Rd d) : ℝ := ∫ s, f s * Φ (s, x) ∂timeMeasure

/-- Auxiliary to the Lean proof route: a continuous compactly supported field on `ℝ × ℝ^d` is
bounded and vanishes for `|x| > R`, for some `R ≥ 0`. -/
theorem field_data {Φ : ℝ × Rd d → ℝ} (hΦ : Continuous Φ) (hΦs : HasCompactSupport Φ) :
    ∃ M R : ℝ, 0 ≤ M ∧ 0 ≤ R ∧ (∀ p, |Φ p| ≤ M) ∧ ∀ s x, R < ‖x‖ → Φ (s, x) = 0 := by
  obtain ⟨M, hM⟩ := hΦ.bounded_above_of_compact_support hΦs
  obtain ⟨R, hR0, hR⟩ := VariationalMean.exists_radius hΦs
  exact ⟨M, R, (norm_nonneg _).trans (hM 0), hR0, fun p => by simpa using hM p, hR⟩

/-- Auxiliary to the Lean proof route: two continuous compactly supported fields have bounds
and a common spatial radius. -/
theorem pair_data {Φ₁ Φ₂ : ℝ × Rd d → ℝ} (h₁ : Continuous Φ₁) (h₁s : HasCompactSupport Φ₁)
    (h₂ : Continuous Φ₂) (h₂s : HasCompactSupport Φ₂) :
    ∃ M₁ M₂ R : ℝ, 0 ≤ M₁ ∧ 0 ≤ M₂ ∧ 0 ≤ R ∧ (∀ p, |Φ₁ p| ≤ M₁) ∧ (∀ p, |Φ₂ p| ≤ M₂) ∧
      (∀ s x, R < ‖x‖ → Φ₁ (s, x) = 0) ∧ (∀ s x, R < ‖x‖ → Φ₂ (s, x) = 0) := by
  obtain ⟨M₁, R₁, hM₁, hR₁0, hb₁, hR₁⟩ := field_data h₁ h₁s
  obtain ⟨M₂, R₂, hM₂, hR₂0, hb₂, hR₂⟩ := field_data h₂ h₂s
  refine ⟨M₁, M₂, max R₁ R₂, hM₁, hM₂, le_max_of_le_left hR₁0, hb₁, hb₂,
    fun s x hx => hR₁ s x (lt_of_le_of_lt (le_max_left _ _) hx),
    fun s x hx => hR₂ s x (lt_of_le_of_lt (le_max_right _ _) hx)⟩

/-- Auxiliary to the Lean proof route: the slices `x ↦ Φ(s,x)` of a field vanishing for
`|x| > R` are compactly supported. -/
theorem slice_hasCompactSupport {Φ : ℝ × Rd d → ℝ} {R : ℝ} (hR : ∀ s x, R < ‖x‖ → Φ (s, x) = 0)
    (s : ℝ) : HasCompactSupport fun x => Φ (s, x) :=
  hasCompactSupport_of_radius fun x hx => hR s x hx

/-- Auxiliary to the Lean proof route: the cross-correlation
`((s,t),y) ↦ ∫ Φ₁(s,x) Φ₂(t,x-y) dx` is jointly continuous. -/
theorem cross_continuous {Φ₁ Φ₂ : ℝ × Rd d → ℝ} (h₁ : Continuous Φ₁) (h₂ : Continuous Φ₂)
    {R : ℝ} (hR₁ : ∀ s x, R < ‖x‖ → Φ₁ (s, x) = 0) :
    Continuous fun q : (ℝ × ℝ) × Rd d => ∫ x, Φ₁ (q.1.1, x) * Φ₂ (q.1.2, x - q.2) := by
  have e : (fun q : (ℝ × ℝ) × Rd d => ∫ x, Φ₁ (q.1.1, x) * Φ₂ (q.1.2, x - q.2)) =
      fun q => ∫ x in closedBall (0 : Rd d) R, Φ₁ (q.1.1, x) * Φ₂ (q.1.2, x - q.2) := by
    funext q
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
    intro x hx
    rw [mem_closedBall, dist_zero_right, not_le] at hx
    rw [hR₁ _ _ hx, zero_mul]
  rw [e]
  refine continuous_parametric_integral_of_continuous ?_ (isCompact_closedBall _ _)
  exact (h₁.comp (by fun_prop)).mul (h₂.comp (by fun_prop))

/-- Auxiliary to the Lean proof route: `(s,t) ↦ B_Γ(Φ₁(s,·), Φ₂(t,·))` is continuous for
continuous fields with a common spatial radius and locally finite `Γ`. -/
theorem stPair_continuous (Γ : Measure (Rd d)) [IsLocallyFiniteMeasure Γ]
    {Φ₁ Φ₂ : ℝ × Rd d → ℝ} (h₁ : Continuous Φ₁) (h₂ : Continuous Φ₂) {R : ℝ}
    (hR₁ : ∀ s x, R < ‖x‖ → Φ₁ (s, x) = 0) (hR₂ : ∀ s x, R < ‖x‖ → Φ₂ (s, x) = 0) :
    Continuous (stPair Γ Φ₁ Φ₂) := by
  set c : (ℝ × ℝ) × Rd d → ℝ := fun q => ∫ x, Φ₁ (q.1.1, x) * Φ₂ (q.1.2, x - q.2) with hc
  have e : stPair Γ Φ₁ Φ₂ = fun p => ∫ y in closedBall (0 : Rd d) (2 * R), c (p, y) ∂Γ := by
    funext p
    unfold stPair spatialPair
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
    intro y hy
    rw [mem_closedBall, dist_zero_right, not_le] at hy
    exact cross_eq_zero (fun x hx => hR₁ p.1 x hx) (fun x hx => hR₂ p.2 x hx) hy
  rw [e]
  exact continuous_parametric_integral_of_continuous (f := fun p y => c (p, y))
    (cross_continuous h₁ h₂ hR₁) (isCompact_closedBall _ _)

/-- Auxiliary to the Lean proof route: `|B_Γ(Φ₁(s,·), Φ₂(t,·))| ≤ M₁ M₂ |B_R| Γ(B_{2R})`. -/
theorem abs_stPair_le (Γ : Measure (Rd d)) [IsLocallyFiniteMeasure Γ]
    {Φ₁ Φ₂ : ℝ × Rd d → ℝ} {M₁ M₂ R : ℝ} (hM₁ : ∀ p, |Φ₁ p| ≤ M₁) (hM₂ : ∀ p, |Φ₂ p| ≤ M₂)
    (hR₁ : ∀ s x, R < ‖x‖ → Φ₁ (s, x) = 0) (hR₂ : ∀ s x, R < ‖x‖ → Φ₂ (s, x) = 0)
    (p : ℝ × ℝ) :
    |stPair Γ Φ₁ Φ₂ p| ≤
      M₁ * M₂ * volume.real (closedBall (0 : Rd d) R) * Γ.real (closedBall (0 : Rd d) (2 * R)) :=
  abs_spatialPair_le Γ (fun x hx => hR₁ _ x hx) (fun x hx => hR₂ _ x hx) (fun _ => hM₁ _)
    (fun _ => hM₂ _)

/-- Auxiliary to the Lean proof route: for `a < 1`, `(s,t) ↦ |s-t|^{-a}` is integrable on
`I² = (0,1)²` (`TimeSchur.time_schur_rclike` at `f = 1`). -/
theorem kern_integrable {a : ℝ} (ha1 : a < 1) :
    Integrable (fun p : ℝ × ℝ => kern a (p.1 - p.2)) (timeMeasure.prod timeMeasure) := by
  obtain ⟨hi, -⟩ := TimeSchur.time_schur_rclike (𝕜 := ℝ) ha1 zero_le_one (fun _ => (1 : ℝ))
    (memLp_const 1)
  rw [timeMeasure_eq_Icc]
  refine hi.congr (ae_of_all _ fun p => ?_)
  simp [TimeSchur.integrand]

/-- **Integrability of the space-time integrand.**  For `a < 1`, locally finite `Γ` and
continuous compactly supported fields `Φ₁, Φ₂` on `ℝ × ℝ^d`, the integrand
`(s,t) ↦ |s-t|^{-a} B_Γ(Φ₁(s,·), Φ₂(t,·))` of `stForm` is integrable on `(0,1)²`. -/
theorem stIntegrand_integrable {a : ℝ} (ha1 : a < 1) (Γ : Measure (Rd d))
    [IsLocallyFiniteMeasure Γ] {Φ₁ Φ₂ : ℝ × Rd d → ℝ} (h₁ : Continuous Φ₁)
    (h₁s : HasCompactSupport Φ₁) (h₂ : Continuous Φ₂) (h₂s : HasCompactSupport Φ₂) :
    Integrable (fun p : ℝ × ℝ => kern a (p.1 - p.2) * stPair Γ Φ₁ Φ₂ p)
      (timeMeasure.prod timeMeasure) := by
  obtain ⟨M₁, M₂, R, -, -, -, hb₁, hb₂, hR₁, hR₂⟩ := pair_data h₁ h₁s h₂ h₂s
  refine (kern_integrable ha1).mul_bdd
    (c := M₁ * M₂ * volume.real (closedBall (0 : Rd d) R) * Γ.real (closedBall (0 : Rd d) (2 * R)))
    (stPair_continuous Γ h₁ h₂ hR₁ hR₂).aestronglyMeasurable (ae_of_all _ fun p => ?_)
  rw [Real.norm_eq_abs]
  exact abs_stPair_le Γ hb₁ hb₂ hR₁ hR₂ p

/-- Auxiliary to the Lean proof route: a linear combination of continuous compactly supported
fields is continuous and compactly supported. -/
theorem lin_data {Φ Ψ : ℝ × Rd d → ℝ} (hΦ : Continuous Φ) (hΦs : HasCompactSupport Φ)
    (hΨ : Continuous Ψ) (hΨs : HasCompactSupport Ψ) (t : ℝ) :
    Continuous (fun p => Φ p + t * Ψ p) ∧ HasCompactSupport (fun p => Φ p + t * Ψ p) :=
  ⟨hΦ.add (continuous_const.mul hΨ), hΦs.add hΨs.mul_left⟩

/-- **Bilinear expansion of the space-time form.**  For `a < 1`, locally finite `Γ`,
continuous compactly supported `Φ, Ψ` and real `t`,
`F(Φ+tΨ, Φ+tΨ) = F(Φ,Φ) + t (F(Φ,Ψ) + F(Ψ,Φ)) + t² F(Ψ,Ψ)`. -/
theorem stForm_quad {a : ℝ} (ha1 : a < 1) (Γ : Measure (Rd d)) [IsLocallyFiniteMeasure Γ]
    {Φ Ψ : ℝ × Rd d → ℝ} (hΦ : Continuous Φ) (hΦs : HasCompactSupport Φ) (hΨ : Continuous Ψ)
    (hΨs : HasCompactSupport Ψ) (t : ℝ) :
    stForm a Γ (fun p => Φ p + t * Ψ p) (fun p => Φ p + t * Ψ p) =
      stForm a Γ Φ Φ + t * (stForm a Γ Φ Ψ + stForm a Γ Ψ Φ) + t ^ 2 * stForm a Γ Ψ Ψ := by
  obtain ⟨-, -, R, -, -, -, -, -, hRΦ, hRΨ⟩ := pair_data hΦ hΦs hΨ hΨs
  have hpt : ∀ p : ℝ × ℝ, kern a (p.1 - p.2) *
      stPair Γ (fun p => Φ p + t * Ψ p) (fun p => Φ p + t * Ψ p) p =
      kern a (p.1 - p.2) * stPair Γ Φ Φ p + (t * (kern a (p.1 - p.2) * stPair Γ Φ Ψ p +
        kern a (p.1 - p.2) * stPair Γ Ψ Φ p) + t ^ 2 * (kern a (p.1 - p.2) * stPair Γ Ψ Ψ p)) := by
    intro p
    have h := spatialPair_bilin Γ (Q₁ := fun x => Φ (p.1, x)) (Q₂ := fun x => Φ (p.2, x))
      (P₁ := fun x => Ψ (p.1, x)) (P₂ := fun x => Ψ (p.2, x))
      (hΦ.comp (by fun_prop)) (slice_hasCompactSupport hRΦ p.1)
      (hΦ.comp (by fun_prop)) (slice_hasCompactSupport hRΦ p.2)
      (hΨ.comp (by fun_prop)) (slice_hasCompactSupport hRΨ p.1)
      (hΨ.comp (by fun_prop)) (slice_hasCompactSupport hRΨ p.2) t
    unfold stPair
    beta_reduce
    rw [h]
    ring
  have i1 := stIntegrand_integrable ha1 Γ hΦ hΦs hΦ hΦs
  have i2 := stIntegrand_integrable ha1 Γ hΦ hΦs hΨ hΨs
  have i3 := stIntegrand_integrable ha1 Γ hΨ hΨs hΦ hΦs
  have i4 := stIntegrand_integrable ha1 Γ hΨ hΨs hΨ hΨs
  have k2 : Integrable (fun p : ℝ × ℝ => t * (kern a (p.1 - p.2) * stPair Γ Φ Ψ p +
      kern a (p.1 - p.2) * stPair Γ Ψ Φ p)) (timeMeasure.prod timeMeasure) :=
    (i2.add i3).const_mul t
  have k3 : Integrable (fun p : ℝ × ℝ => t ^ 2 * (kern a (p.1 - p.2) * stPair Γ Ψ Ψ p))
      (timeMeasure.prod timeMeasure) := i4.const_mul _
  have k1 : Integrable (fun p : ℝ × ℝ => t * (kern a (p.1 - p.2) * stPair Γ Φ Ψ p +
      kern a (p.1 - p.2) * stPair Γ Ψ Φ p) + t ^ 2 * (kern a (p.1 - p.2) * stPair Γ Ψ Ψ p))
      (timeMeasure.prod timeMeasure) := k2.add k3
  unfold stForm
  simp_rw [hpt]
  rw [integral_add i1 k1, integral_add k2 k3, integral_const_mul, integral_const_mul,
    integral_add i2 i3]
  ring

/-- **Symmetry of the space-time form.**  For an even locally finite `Γ` and continuous
compactly supported `Φ₁, Φ₂`, `F(Φ₁,Φ₂) = F(Φ₂,Φ₁)` (evenness of `Γ` in the spatial pairing,
`SpatialFourLinear.spatialPair_comm`; symmetry of `|s-t|^{-a}`; the swap of `(0,1)²`). -/
theorem stForm_comm {a : ℝ} {Γ : Measure (Rd d)} [IsLocallyFiniteMeasure Γ] (hE : IsEven Γ)
    {Φ₁ Φ₂ : ℝ × Rd d → ℝ} (h₁ : Continuous Φ₁) (h₁s : HasCompactSupport Φ₁)
    (h₂ : Continuous Φ₂) (h₂s : HasCompactSupport Φ₂) :
    stForm a Γ Φ₁ Φ₂ = stForm a Γ Φ₂ Φ₁ := by
  obtain ⟨-, -, R, -, -, -, -, -, hR₁, hR₂⟩ := pair_data h₁ h₁s h₂ h₂s
  have hpt : ∀ p : ℝ × ℝ, kern a (p.1 - p.2) * stPair Γ Φ₁ Φ₂ p =
      (fun q : ℝ × ℝ => kern a (q.1 - q.2) * stPair Γ Φ₂ Φ₁ q) p.swap := by
    intro p
    simp only [Prod.fst_swap, Prod.snd_swap, stPair]
    rw [TimeSchur.kern_sub_comm a p.1 p.2,
      SpatialFourLinear.spatialPair_comm hE (Q := fun x => Φ₁ (p.1, x))
        (P := fun x => Φ₂ (p.2, x)) (h₂.comp (by fun_prop)) (h₁.comp (by fun_prop))
        (slice_hasCompactSupport hR₁ p.1)]
  unfold stForm
  simp_rw [hpt]
  exact integral_prod_swap (fun q : ℝ × ℝ => kern a (q.1 - q.2) * stPair Γ Φ₂ Φ₁ q)

/-- **Cauchy-Schwarz for the space-time form, over positivity.**  For `a < 1`, an even locally
finite `Γ` and continuous compactly supported `Ψ, G`: if `F(Φ,Φ) ≥ 0` for every continuous
compactly supported `Φ`, then `F(Ψ,G)² ≤ F(Ψ,Ψ) F(G,G)` (discriminant of
`t ↦ F(Ψ+tG, Ψ+tG) ≥ 0`, `discrim_le_zero`).  The positivity hypothesis is discharged by
`stForm_self_nonneg` (see `stForm_sq_le`). -/
theorem stForm_sq_le_of_nonneg {a : ℝ} (ha1 : a < 1) {Γ : Measure (Rd d)}
    [IsLocallyFiniteMeasure Γ] (hE : IsEven Γ)
    (hpos : ∀ Φ : ℝ × Rd d → ℝ, Continuous Φ → HasCompactSupport Φ → 0 ≤ stForm a Γ Φ Φ)
    {Ψ G : ℝ × Rd d → ℝ} (hΨ : Continuous Ψ) (hΨs : HasCompactSupport Ψ) (hG : Continuous G)
    (hGs : HasCompactSupport G) :
    stForm a Γ Ψ G ^ 2 ≤ stForm a Γ Ψ Ψ * stForm a Γ G G := by
  have hq : ∀ t : ℝ, 0 ≤ stForm a Γ G G * (t * t) + 2 * stForm a Γ Ψ G * t +
      stForm a Γ Ψ Ψ := by
    intro t
    obtain ⟨hc, hcs⟩ := lin_data hΨ hΨs hG hGs t
    have h := hpos _ hc hcs
    rw [stForm_quad ha1 Γ hΨ hΨs hG hGs t, stForm_comm hE hG hGs hΨ hΨs] at h
    nlinarith [h]
  have := discrim_le_zero hq
  unfold discrim at this
  nlinarith [this]

/-! ### Positivity through the mixture of rank-one time kernels -/

/-- Auxiliary to the Lean proof route: for an integrable weight `f` on `I`, the time average
`x ↦ ∫_I f(s) Φ(s,x) ds` of a continuous bounded field vanishing for `|x| > R` is continuous
and vanishes for `|x| > R`. -/
theorem tAvg_data {f : ℝ → ℝ} (hf : Integrable f timeMeasure) {Φ : ℝ × Rd d → ℝ}
    (hΦ : Continuous Φ) {M R : ℝ} (hM : ∀ p, |Φ p| ≤ M) (hR : ∀ s x, R < ‖x‖ → Φ (s, x) = 0) :
    Continuous (tAvg f Φ) ∧ ∀ x, R < ‖x‖ → tAvg f Φ x = 0 := by
  refine ⟨?_, fun x hx => by simp [tAvg, hR _ x hx]⟩
  refine continuous_of_dominated (F := fun x s => f s * Φ (s, x))
    (bound := fun s => ‖f s‖ * M) (fun x => ?_) (fun x => ae_of_all _ fun s => ?_)
    (hf.norm.mul_const M) (ae_of_all _ fun s => ?_)
  · exact hf.aestronglyMeasurable.mul (hΦ.comp (by fun_prop)).aestronglyMeasurable
  · rw [norm_mul, Real.norm_eq_abs (Φ (s, x))]
    exact mul_le_mul_of_nonneg_left (hM _) (norm_nonneg _)
  · exact continuous_const.mul (hΦ.comp (by fun_prop))

/-- Auxiliary to the Lean proof route (Fubini for the weighted pairing): for integrable
weights `f, g` on `I`,
continuous bounded fields `Φ₁, Φ₂` vanishing for `|x| > R`, and locally finite `Γ`,
`∫∫_{I²} f(s) g(t) B_Γ(Φ₁(s,·), Φ₂(t,·)) ds dt = B_Γ(∫_I f Φ₁, ∫_I g Φ₂)`. -/
theorem weighted_stPair (Γ : Measure (Rd d)) [IsLocallyFiniteMeasure Γ] {f g : ℝ → ℝ}
    (hf : Integrable f timeMeasure) (hg : Integrable g timeMeasure) {Φ₁ Φ₂ : ℝ × Rd d → ℝ}
    (h₁ : Continuous Φ₁) (h₂ : Continuous Φ₂) {M₁ M₂ R : ℝ} (hM₁ : ∀ p, |Φ₁ p| ≤ M₁)
    (hM₂ : ∀ p, |Φ₂ p| ≤ M₂) (hR₁ : ∀ s x, R < ‖x‖ → Φ₁ (s, x) = 0)
    (hR₂ : ∀ s x, R < ‖x‖ → Φ₂ (s, x) = 0) :
    ∫ p, f p.1 * g p.2 * stPair Γ Φ₁ Φ₂ p ∂(timeMeasure.prod timeMeasure) =
      spatialPair Γ (tAvg f Φ₁) (tAvg g Φ₂) := by
  set m : Measure (ℝ × ℝ) := timeMeasure.prod timeMeasure with hm
  set c : (ℝ × ℝ) × Rd d → ℝ := fun q => ∫ x, Φ₁ (q.1.1, x) * Φ₂ (q.1.2, x - q.2) with hc
  have hcc : Continuous c := cross_continuous h₁ h₂ hR₁
  have hM₁0 : 0 ≤ M₁ := (abs_nonneg _).trans (hM₁ (0, 0))
  have hM₂0 : 0 ≤ M₂ := (abs_nonneg _).trans (hM₂ (0, 0))
  have hfg : Integrable (fun p : ℝ × ℝ => ‖f p.1‖ * ‖g p.2‖) m := hf.norm.mul_prod hg.norm
  have hfgm : AEStronglyMeasurable (fun p : ℝ × ℝ => f p.1 * g p.2) m :=
    hf.aestronglyMeasurable.comp_fst.mul hg.aestronglyMeasurable.comp_snd
  -- step (a): the inner spatial integral, for each `y`
  have stepA : ∀ y, ∫ x, tAvg f Φ₁ x * tAvg g Φ₂ (x - y) = ∫ p, f p.1 * g p.2 * c (p, y) ∂m := by
    intro y
    set H : Rd d → ℝ × ℝ → ℝ := fun x p =>
      (f p.1 * Φ₁ (p.1, x)) * (g p.2 * Φ₂ (p.2, x - y)) with hH
    have hprod : ∀ x, tAvg f Φ₁ x * tAvg g Φ₂ (x - y) = ∫ p, H x p ∂m := by
      intro x
      rw [hH, hm, integral_prod_mul (fun s => f s * Φ₁ (s, x)) (fun t => g t * Φ₂ (t, x - y))]
      rfl
    have hHi : Integrable (Function.uncurry H) ((volume : Measure (Rd d)).prod m) := by
      have hind : Integrable ((closedBall (0 : Rd d) R).indicator fun _ => M₁ * M₂)
          (volume : Measure (Rd d)) :=
        (integrable_indicator_iff measurableSet_closedBall).2
          (integrableOn_const (measure_closedBall_lt_top (μ := (volume : Measure (Rd d)))).ne)
      refine (hind.mul_prod hfg).mono' ?_ (ae_of_all _ fun z => ?_)
      · refine ((hf.aestronglyMeasurable.comp_fst.comp_snd).mul
          (h₁.comp (by fun_prop)).aestronglyMeasurable).mul
          ((hg.aestronglyMeasurable.comp_snd.comp_snd).mul
          (h₂.comp (by fun_prop)).aestronglyMeasurable)
      · simp only [Function.uncurry, hH]
        by_cases hz : R < ‖z.1‖
        · rw [hR₁ _ _ hz, mul_zero, zero_mul, norm_zero]
          refine mul_nonneg ?_ (by positivity)
          exact indicator_nonneg (fun _ _ => mul_nonneg hM₁0 hM₂0) _
        · have hz' : z.1 ∈ closedBall (0 : Rd d) R := by
            rw [mem_closedBall, dist_zero_right]; exact not_lt.1 hz
          rw [indicator_of_mem hz', norm_mul, norm_mul, norm_mul, Real.norm_eq_abs (Φ₁ _),
            Real.norm_eq_abs (Φ₂ _)]
          have e1 := hM₁ (z.2.1, z.1)
          have e2 := hM₂ (z.2.2, z.1 - y)
          have p1 := norm_nonneg (f z.2.1)
          have p2 := norm_nonneg (g z.2.2)
          calc ‖f z.2.1‖ * |Φ₁ (z.2.1, z.1)| * (‖g z.2.2‖ * |Φ₂ (z.2.2, z.1 - y)|)
              ≤ ‖f z.2.1‖ * M₁ * (‖g z.2.2‖ * M₂) := by gcongr
            _ = M₁ * M₂ * (‖f z.2.1‖ * ‖g z.2.2‖) := by ring
    simp_rw [hprod]
    rw [integral_integral_swap hHi]
    refine integral_congr_ae (ae_of_all _ fun p => ?_)
    simp only [hH, hc]
    rw [← integral_const_mul]
    congr 1; funext x; ring
  -- step (b): the outer integral against `Γ`
  have hGi : Integrable (fun z : Rd d × (ℝ × ℝ) => f z.2.1 * g z.2.2 * c (z.2, z.1))
      (Γ.prod m) := by
    have hind : Integrable ((closedBall (0 : Rd d) (2 * R)).indicator
        fun _ => M₁ * M₂ * volume.real (closedBall (0 : Rd d) R)) Γ :=
      (integrable_indicator_iff measurableSet_closedBall).2
        (integrableOn_const measure_closedBall_lt_top.ne)
    refine (hind.mul_prod hfg).mono' ?_ (ae_of_all _ fun z => ?_)
    · exact hfgm.comp_snd.mul (hcc.comp (by fun_prop)).aestronglyMeasurable
    · by_cases hz : 2 * R < ‖z.1‖
      · have h0 : c (z.2, z.1) = 0 :=
          cross_eq_zero (fun x hx => hR₁ z.2.1 x hx) (fun x hx => hR₂ z.2.2 x hx) hz
        rw [h0, mul_zero, norm_zero]
        refine mul_nonneg ?_ (by positivity)
        exact indicator_nonneg (fun _ _ => by positivity) _
      · have hz' : z.1 ∈ closedBall (0 : Rd d) (2 * R) := by
          rw [mem_closedBall, dist_zero_right]; exact not_lt.1 hz
        rw [indicator_of_mem hz', norm_mul, norm_mul, Real.norm_eq_abs (c _)]
        have hb := abs_cross_le (fun x hx => hR₁ z.2.1 x hx) (fun x => hM₁ (z.2.1, x))
          (fun x => hM₂ (z.2.2, x)) z.1
        have p1 := norm_nonneg (f z.2.1)
        have p2 := norm_nonneg (g z.2.2)
        calc ‖f z.2.1‖ * ‖g z.2.2‖ * |c (z.2, z.1)|
            ≤ ‖f z.2.1‖ * ‖g z.2.2‖ * (M₁ * M₂ * volume.real (closedBall (0 : Rd d) R)) := by
              gcongr
          _ = M₁ * M₂ * volume.real (closedBall (0 : Rd d) R) * (‖f z.2.1‖ * ‖g z.2.2‖) := by
              ring
  have hR : spatialPair Γ (tAvg f Φ₁) (tAvg g Φ₂) =
      ∫ y, ∫ p, f p.1 * g p.2 * c (p, y) ∂m ∂Γ := by
    unfold spatialPair
    simp_rw [stepA]
  rw [hR, integral_integral_swap (f := fun y p => f p.1 * g p.2 * c (p, y)) hGi]
  refine integral_congr_ae (ae_of_all _ fun p => ?_)
  simp only
  rw [integral_const_mul]
  rfl

/-- Auxiliary to the Lean proof route: every profile `t ↦ 1_{u ≤ t} e^{-λ(t-u)}` of the
mixture (`TimeCompletion.mixProfile`) is integrable on `I` (bounded measurable on a finite
measure). -/
theorem mixProfile_integrable (w : ℝ × ℝ) :
    Integrable (TimeCompletion.mixProfile w) timeMeasure := by
  have hm : Measurable (TimeCompletion.mixProfile w) :=
    TimeCompletion.measurable_mixProfile.comp (measurable_const.prodMk measurable_id)
  refine (integrable_const (Real.exp (|w.1| * (1 + |w.2|)))).mono' hm.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  rw [Real.norm_eq_abs, abs_of_nonneg (TimeCompletion.mixProfile_nonneg w t)]
  unfold TimeCompletion.mixProfile
  split_ifs
  · refine Real.exp_le_exp.2 ((neg_le_abs _).trans ?_)
    rw [abs_mul]
    refine mul_le_mul_of_nonneg_left ((abs_sub _ _).trans ?_) (abs_nonneg _)
    have : |t| ≤ 1 := by rw [abs_of_pos ht.1]; exact ht.2.le
    linarith
  · exact (Real.exp_pos _).le

/-- Auxiliary to the Lean proof route: the mixture integrand
`H((s,t),w) = ρ(w) φ_w(s) φ_w(t) P(s,t)` of the kernel `|s-t|^{-a}`
(`TimeCompletion.mixWeight`, `TimeCompletion.mixProfile`). -/
def mixIntegrand (a : ℝ) (P : ℝ × ℝ → ℝ) (q : (ℝ × ℝ) × (ℝ × ℝ)) : ℝ :=
  TimeCompletion.mixWeight a q.2 * TimeCompletion.mixProfile q.2 q.1.1 *
    TimeCompletion.mixProfile q.2 q.1.2 * P q.1

/-- Auxiliary to the Lean proof route (Tonelli/Fubini for the mixture, as in
`TimeCompletion.re_form_nonneg_of_mixture`): for `0 < a`, a continuous `P` on `ℝ²` with
`|s-t|^{-a} P(s,t)` integrable on `I²`, the mixture integrand is integrable on
`I² × ((0,∞) × ℝ)` and its `w`-sections integrate to `|s-t|^{-a} P(s,t)` for a.e. `(s,t)`. -/
theorem mixIntegrand_data {a : ℝ} (ha0 : 0 < a) {P : ℝ × ℝ → ℝ} (hPc : Continuous P)
    (hKP : Integrable (fun p : ℝ × ℝ => kern a (p.1 - p.2) * P p)
      (timeMeasure.prod timeMeasure)) :
    Integrable (mixIntegrand a P) ((timeMeasure.prod timeMeasure).prod TimeCompletion.mixMeasure) ∧
      ∀ᵐ p ∂(timeMeasure.prod timeMeasure),
        ∫ w, mixIntegrand a P (p, w) ∂TimeCompletion.mixMeasure = kern a (p.1 - p.2) * P p := by
  set m : Measure (ℝ × ℝ) := timeMeasure.prod timeMeasure with hm
  set ν : Measure (ℝ × ℝ) := TimeCompletion.mixMeasure with hν
  set ρ := TimeCompletion.mixWeight a with hρ
  set φ := TimeCompletion.mixProfile with hφ
  have hρm : Measurable ρ := TimeCompletion.measurable_mixWeight a
  have hφm : Measurable (Function.uncurry φ) := TimeCompletion.measurable_mixProfile
  have hφw : ∀ t, Measurable fun w => φ w t := fun t =>
    hφm.comp (measurable_id.prodMk measurable_const)
  have hkm : Measurable fun q : (ℝ × ℝ) × (ℝ × ℝ) => ρ q.2 * φ q.2 q.1.1 * φ q.2 q.1.2 := by
    have e1 : Measurable fun q : (ℝ × ℝ) × (ℝ × ℝ) => φ q.2 q.1.1 :=
      hφm.comp (measurable_snd.prodMk (measurable_fst.comp measurable_fst))
    have e2 : Measurable fun q : (ℝ × ℝ) × (ℝ × ℝ) => φ q.2 q.1.2 :=
      hφm.comp (measurable_snd.prodMk (measurable_snd.comp measurable_fst))
    exact ((hρm.comp measurable_snd).mul e1).mul e2
  have hknn : ∀ q : (ℝ × ℝ) × (ℝ × ℝ), 0 ≤ ρ q.2 * φ q.2 q.1.1 * φ q.2 q.1.2 := fun q =>
    mul_nonneg (mul_nonneg (TimeCompletion.mixWeight_nonneg a ha0 _)
      (TimeCompletion.mixProfile_nonneg _ _)) (TimeCompletion.mixProfile_nonneg _ _)
  have hK : ∀ᵐ p ∂m, ENNReal.ofReal (kern a (p.1 - p.2)) =
      ∫⁻ w, ENNReal.ofReal (ρ w * φ w p.1 * φ w p.2) ∂ν := by
    have hd := TimeCompletion.ae_ne_diag 1
    rw [← timeMeasure_eq_Icc] at hd
    filter_upwards [hd] with p hp
    exact TimeCompletion.kern_eq_mixture a ha0 p.1 p.2 hp
  have hHm : Measurable (mixIntegrand a P) := hkm.mul (hPc.measurable.comp measurable_fst)
  refine ⟨⟨hHm.aestronglyMeasurable, ?_⟩, ?_⟩
  · show ∫⁻ q, ‖mixIntegrand a P q‖ₑ ∂(m.prod ν) < (⊤ : ℝ≥0∞)
    have hen : ∀ p w, ‖mixIntegrand a P (p, w)‖ₑ =
        ENNReal.ofReal (ρ w * φ w p.1 * φ w p.2) * ‖P p‖ₑ := by
      intro p w
      show ‖ρ w * φ w p.1 * φ w p.2 * P p‖ₑ = _
      rw [enorm_mul, Real.enorm_eq_ofReal (hknn (p, w))]
    rw [lintegral_prod _ hHm.enorm.aemeasurable]
    have heq : ∀ᵐ p ∂m, ∫⁻ w, ‖mixIntegrand a P (p, w)‖ₑ ∂ν =
        ‖kern a (p.1 - p.2) * P p‖ₑ := by
      filter_upwards [hK] with p hp
      have hmw0 : Measurable fun w => ρ w * φ w p.1 * φ w p.2 :=
        (hρm.mul (hφw p.1)).mul (hφw p.2)
      rw [lintegral_congr (hen p), lintegral_mul_const _ hmw0.ennreal_ofReal, ← hp, enorm_mul,
        Real.enorm_eq_ofReal (kern_nonneg _ _)]
    rw [lintegral_congr_ae heq]
    exact hKP.2
  · filter_upwards [hK] with p hp
    have hmw : Measurable fun w => ρ w * φ w p.1 * φ w p.2 :=
      (hρm.mul (hφw p.1)).mul (hφw p.2)
    have hKr : ∫ w, ρ w * φ w p.1 * φ w p.2 ∂ν = kern a (p.1 - p.2) := by
      rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun w => hknn (p, w))
        hmw.aestronglyMeasurable, ← hp, ENNReal.toReal_ofReal (kern_nonneg _ _)]
    show ∫ w, ρ w * φ w p.1 * φ w p.2 * P p ∂ν = _
    rw [integral_mul_const, hKr]

/-- **Positive semidefiniteness of the space-time form** (step (c) of the route of feasibility
report R2; auxiliary to the Lean route).  For `0 < a < 1`, a locally finite `Γ` with spectral
measure `μ` in the manuscript's convention (`HomogHypothesis.IsSpectralMeasure`) and a
continuous compactly supported real field `Φ` on `ℝ × ℝ^d`,
`F(Φ,Φ) = ∫∫_{I²} |s-t|^{-a} B_Γ(Φ(s,·), Φ(t,·)) ds dt ≥ 0`.  The integrand is integrable
(`stIntegrand_integrable`), so `F(Φ,Φ)` is a genuine integral.  Route: the kernel is a
positive mixture of rank-one kernels (`TimeCompletion.kern_eq_mixture`); by Fubini,
`F(Φ,Φ) = ∫ ρ(w) B_Γ(Q_w,Q_w) dν(w)` with `Q_w = ∫_I φ_w(s) Φ(s,·) ds` continuous and
compactly supported (`weighted_stPair`), and `B_Γ(Q_w,Q_w) ≥ 0`
(`spatialPair_self_nonneg_of_continuous`).  The TeX gets the same positivity from the norm
`‖J_G F‖²` of `L:positive-raw-embedding` (`integrated_intrinsic_constant.tex` lines 22-39). -/
theorem stForm_self_nonneg {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {Γ μ : Measure (Rd d)}
    [IsLocallyFiniteMeasure Γ] (hsp : IsSpectralMeasure Γ μ) {Φ : ℝ × Rd d → ℝ}
    (hΦ : Continuous Φ) (hΦs : HasCompactSupport Φ) : 0 ≤ stForm a Γ Φ Φ := by
  obtain ⟨M, R, -, -, hM, hR⟩ := field_data hΦ hΦs
  obtain ⟨hHi, hsec⟩ := mixIntegrand_data ha0 (stPair_continuous Γ hΦ hΦ hR hR)
    (stIntegrand_integrable ha1 Γ hΦ hΦs hΦ hΦs)
  have hinner : ∀ w, ∫ p, mixIntegrand a (stPair Γ Φ Φ) (p, w) ∂(timeMeasure.prod timeMeasure) =
      TimeCompletion.mixWeight a w * spatialPair Γ (tAvg (TimeCompletion.mixProfile w) Φ)
        (tAvg (TimeCompletion.mixProfile w) Φ) := by
    intro w
    have e : ∀ p : ℝ × ℝ, mixIntegrand a (stPair Γ Φ Φ) (p, w) =
        TimeCompletion.mixWeight a w * (TimeCompletion.mixProfile w p.1 *
          TimeCompletion.mixProfile w p.2 * stPair Γ Φ Φ p) := by
      intro p; simp only [mixIntegrand]; ring
    simp_rw [e]
    rw [integral_const_mul, weighted_stPair Γ (mixProfile_integrable w) (mixProfile_integrable w)
      hΦ hΦ hM hM hR hR]
  have hform : stForm a Γ Φ Φ = ∫ w, TimeCompletion.mixWeight a w *
      spatialPair Γ (tAvg (TimeCompletion.mixProfile w) Φ) (tAvg (TimeCompletion.mixProfile w) Φ)
        ∂TimeCompletion.mixMeasure := by
    unfold stForm
    rw [integral_congr_ae (Filter.EventuallyEq.symm hsec),
      integral_integral_swap (f := fun p w => mixIntegrand a (stPair Γ Φ Φ) (p, w)) hHi]
    simp_rw [hinner]
  rw [hform]
  refine integral_nonneg fun w => mul_nonneg (TimeCompletion.mixWeight_nonneg a ha0 w) ?_
  obtain ⟨hc, hz⟩ := tAvg_data (mixProfile_integrable w) hΦ hM hR
  exact spatialPair_self_nonneg_of_continuous hsp hc hz

/-- **Cauchy-Schwarz for the space-time form** (step (c) of the route, auxiliary).  For
`0 < a < 1`, an even locally finite `Γ` with spectral measure `μ`, and continuous compactly
supported real fields `Ψ, G` on `ℝ × ℝ^d`, `F(Ψ,G)² ≤ F(Ψ,Ψ) F(G,G)`. -/
theorem stForm_sq_le {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {Γ μ : Measure (Rd d)}
    [IsLocallyFiniteMeasure Γ] (hE : IsEven Γ) (hsp : IsSpectralMeasure Γ μ)
    {Ψ G : ℝ × Rd d → ℝ} (hΨ : Continuous Ψ) (hΨs : HasCompactSupport Ψ) (hG : Continuous G)
    (hGs : HasCompactSupport G) :
    stForm a Γ Ψ G ^ 2 ≤ stForm a Γ Ψ Ψ * stForm a Γ G G :=
  stForm_sq_le_of_nonneg ha1 hE (fun _ h hs => stForm_self_nonneg ha0 ha1 hsp h hs) hΨ hΨs hG hGs

/-! ### The identities with the mean and the variance -/

/-- Auxiliary to the Lean proof route: for `|x| ≤ R` and a field bounded by `M` and vanishing
for `|z| > R`, `|(Γ * Ψ(s,·))(x)| ≤ M Γ(B_{2R})` (no integrability assumed). -/
theorem abs_conv_le (Γ : Measure (Rd d)) [IsLocallyFiniteMeasure Γ] {Ψ : ℝ × Rd d → ℝ}
    {M R : ℝ} (hM : ∀ p, |Ψ p| ≤ M) (hR : ∀ s x, R < ‖x‖ → Ψ (s, x) = 0) (s : ℝ) {x : Rd d}
    (hx : ‖x‖ ≤ R) :
    |conv Γ (fun y => Ψ (s, y)) x| ≤ M * Γ.real (closedBall (0 : Rd d) (2 * R)) := by
  unfold conv
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := closedBall (0 : Rd d) (2 * R))
    fun y hy => by
      rw [mem_closedBall, dist_zero_right, not_le] at hy
      refine hR s _ ?_
      have := norm_sub_norm_le y x
      rw [norm_sub_rev] at this
      linarith, ← Real.norm_eq_abs]
  exact norm_setIntegral_le_of_norm_le_const measure_closedBall_lt_top fun y _ => by
    rw [Real.norm_eq_abs]; exact hM _

/-- Auxiliary to the Lean proof route: for a continuous field `Ψ`, the map
`(s,x) ↦ (Γ * Ψ(s,·))(x)` is strongly measurable (s-finite `Γ`). -/
theorem conv_stronglyMeasurable (Γ : Measure (Rd d)) [SFinite Γ] {Ψ : ℝ × Rd d → ℝ}
    (hΨ : Continuous Ψ) :
    StronglyMeasurable fun q : ℝ × Rd d => conv Γ (fun y => Ψ (q.1, y)) q.2 :=
  StronglyMeasurable.integral_prod_right' (ν := Γ)
    (f := fun z : (ℝ × Rd d) × Rd d => Ψ (z.1.1, z.1.2 - z.2))
    (hΨ.comp (by fun_prop)).stronglyMeasurable

/-- Auxiliary to the Lean proof route (Fubini in space): for continuous `F, G` bounded by
`A, B` and vanishing for `|x| > R`, and locally finite `Γ`,
`B_Γ(F,G) = ∫ F(x) (Γ * G)(x) dx`. -/
theorem spatialPair_eq_conv (Γ : Measure (Rd d)) [IsLocallyFiniteMeasure Γ] {F G : Rd d → ℝ}
    (hF : Continuous F) (hG : Continuous G) {A B R : ℝ} (hA : ∀ x, |F x| ≤ A)
    (hB : ∀ x, |G x| ≤ B) (hFR : ∀ x, R < ‖x‖ → F x = 0) (hGR : ∀ x, R < ‖x‖ → G x = 0) :
    spatialPair Γ F G = ∫ x, F x * conv Γ G x := by
  have hA0 : 0 ≤ A := (abs_nonneg _).trans (hA 0)
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  have hi1 : Integrable ((closedBall (0 : Rd d) (2 * R)).indicator fun _ => B) Γ :=
    (integrable_indicator_iff measurableSet_closedBall).2
      (integrableOn_const measure_closedBall_lt_top.ne)
  have hi2 : Integrable ((closedBall (0 : Rd d) R).indicator fun _ => A)
      (volume : Measure (Rd d)) :=
    (integrable_indicator_iff measurableSet_closedBall).2
      (integrableOn_const (measure_closedBall_lt_top (μ := (volume : Measure (Rd d)))).ne)
  have hint : Integrable (Function.uncurry fun (y x : Rd d) => F x * G (x - y))
      (Γ.prod volume) := by
    refine (hi1.mul_prod hi2).mono' ((hF.comp continuous_snd).mul
      (hG.comp (by fun_prop))).aestronglyMeasurable (ae_of_all _ fun z => ?_)
    simp only [Function.uncurry]
    by_cases hx : R < ‖z.2‖
    · rw [hFR _ hx, zero_mul, norm_zero]
      exact mul_nonneg (indicator_nonneg (fun _ _ => hB0) _)
        (indicator_nonneg (fun _ _ => hA0) _)
    · by_cases hy : 2 * R < ‖z.1‖
      · have : R < ‖z.2 - z.1‖ := by
          have := norm_sub_norm_le z.1 z.2
          rw [norm_sub_rev z.1] at this
          linarith [not_lt.1 hx]
        rw [hGR _ this, mul_zero, norm_zero]
        exact mul_nonneg (indicator_nonneg (fun _ _ => hB0) _)
          (indicator_nonneg (fun _ _ => hA0) _)
      · have hz1 : z.1 ∈ closedBall (0 : Rd d) (2 * R) := by
          rw [mem_closedBall, dist_zero_right]; exact not_lt.1 hy
        have hz2 : z.2 ∈ closedBall (0 : Rd d) R := by
          rw [mem_closedBall, dist_zero_right]; exact not_lt.1 hx
        rw [indicator_of_mem hz1, indicator_of_mem hz2, norm_mul, Real.norm_eq_abs,
          Real.norm_eq_abs, mul_comm B A]
        exact mul_le_mul (hA _) (hB _) (abs_nonneg _) hA0
  unfold spatialPair
  rw [integral_integral_swap hint]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  simp only [conv]
  rw [integral_const_mul]

/-- **The mean identity** (the second identity of `E:occupation-raw-identities`,
`integrated_occupation_ceiling.tex` lines 33-37, in the form of the space-time pairing, with
the field `Φ` in place of `g²`; auxiliary to the Lean route).  For `a < 1`, locally finite
`Γ` and continuous compactly supported real fields `Ψ, Φ` on `ℝ × ℝ^d`, with
`h_{Ψ,t}(x) = ∫_I |t-u|^{-a} (Γ * Ψ(u,·))(x) du` (`VariationalDilation.mean`):
for every `t ∈ [0,1]` the function `x ↦ h_{Ψ,t}(x) Φ(t,x)` is integrable, the function
`t ↦ ∫ h_{Ψ,t}(x) Φ(t,x) dx` is integrable on `I = (0,1)`, and
`∫_I ∫ h_{Ψ,t}(x) Φ(t,x) dx dt = F(Φ,Ψ)`.  No evenness of `Γ` is used here (the order of the
arguments of `F` is the one produced by Fubini; `integral_mean_mul_eq_stForm` swaps it for an
even `Γ`). -/
theorem integral_mean_mul_eq_stForm_swap {a : ℝ} (ha1 : a < 1) (Γ : Measure (Rd d))
    [IsLocallyFiniteMeasure Γ] {Ψ Φ : ℝ × Rd d → ℝ} (hΨ : Continuous Ψ)
    (hΨs : HasCompactSupport Ψ) (hΦ : Continuous Φ) (hΦs : HasCompactSupport Φ) :
    (∀ t ∈ Icc (0 : ℝ) 1, Integrable (fun x => mean a Γ Ψ t x * Φ (t, x))) ∧
      IntegrableOn (fun t => ∫ x, mean a Γ Ψ t x * Φ (t, x)) (Ioo (0 : ℝ) 1) ∧
      ∫ t in Ioo (0 : ℝ) 1, ∫ x, mean a Γ Ψ t x * Φ (t, x) = stForm a Γ Φ Ψ := by
  obtain ⟨MΦ, MΨ, R, hMΦ0, hMΨ0, -, hMΦ, hMΨ, hRΦ, hRΨ⟩ := pair_data hΦ hΦs hΨ hΨs
  set C : ℝ := MΦ * (MΨ * Γ.real (closedBall (0 : Rd d) (2 * R))) with hC
  have hC0 : 0 ≤ C := by positivity
  set J : ℝ → ℝ → Rd d → ℝ := fun t s x =>
    kern a (t - s) * (Φ (t, x) * conv Γ (fun y => Ψ (s, y)) x) with hJ
  have hcm := conv_stronglyMeasurable Γ hΨ
  -- integrability of `J t` on `I × ℝ^d` for `t ∈ [0,1]`
  have hJi : ∀ t ∈ Icc (0 : ℝ) 1,
      Integrable (Function.uncurry (J t)) (timeMeasure.prod (volume : Measure (Rd d))) := by
    intro t ht
    have hk : Integrable (fun s => kern a (t - s)) timeMeasure :=
      ((TimeSchur.integral_row (T := 1) ha1 ht).1).mono_set Ioo_subset_Icc_self
    have hind : Integrable ((closedBall (0 : Rd d) R).indicator fun _ => C)
        (volume : Measure (Rd d)) :=
      (integrable_indicator_iff measurableSet_closedBall).2
        (integrableOn_const (measure_closedBall_lt_top (μ := (volume : Measure (Rd d)))).ne)
    refine (hk.mul_prod hind).mono' ?_ (ae_of_all _ fun z => ?_)
    · refine (((measurable_kern a).comp
        (measurable_const.sub measurable_fst)).aestronglyMeasurable).mul
        ((hΦ.comp (by fun_prop)).aestronglyMeasurable.mul hcm.aestronglyMeasurable)
    · simp only [Function.uncurry, hJ]
      rw [norm_mul, Real.norm_eq_abs (kern a _), abs_of_nonneg (kern_nonneg _ _)]
      by_cases hx : R < ‖z.2‖
      · rw [hRΦ _ _ hx, zero_mul, norm_zero, mul_zero]
        exact mul_nonneg (kern_nonneg _ _) (indicator_nonneg (fun _ _ => hC0) _)
      · have hz : z.2 ∈ closedBall (0 : Rd d) R := by
          rw [mem_closedBall, dist_zero_right]; exact not_lt.1 hx
        rw [indicator_of_mem hz]
        refine mul_le_mul_of_nonneg_left ?_ (kern_nonneg _ _)
        rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, hC]
        exact mul_le_mul (hMΦ _) (abs_conv_le Γ hMΨ hRΨ z.1 (not_lt.1 hx)) (abs_nonneg _) hMΦ0
  -- the `s`-integral of `J t s x` is `Φ(t,x) h_t(x)`
  have hsx : ∀ t x, ∫ s, J t s x ∂timeMeasure = mean a Γ Ψ t x * Φ (t, x) := by
    intro t x
    have e : ∀ s, J t s x = Φ (t, x) * (kern a (t - s) * conv Γ (fun y => Ψ (s, y)) x) := by
      intro s; simp only [hJ]; ring
    simp_rw [e]
    rw [integral_const_mul, mul_comm]
    rfl
  -- the `x`-integral of `J t s x` is `|t-s|^{-a} B_Γ(Φ(t,·), Ψ(s,·))`
  have hxs : ∀ t s, ∫ x, J t s x = kern a (t - s) * stPair Γ Φ Ψ (t, s) := by
    intro t s
    simp only [hJ]
    rw [integral_const_mul]
    show _ = kern a (t - s) * spatialPair Γ (fun x => Φ (t, x)) (fun x => Ψ (s, x))
    rw [spatialPair_eq_conv Γ (F := fun x => Φ (t, x)) (G := fun x => Ψ (s, x))
      (hΦ.comp (by fun_prop))
      (hΨ.comp (by fun_prop)) (fun x => hMΦ (t, x)) (fun x => hMΨ (s, x))
      (fun x hx => hRΦ t x hx) (fun x hx => hRΨ s x hx)]
  have hrow : ∀ t ∈ Icc (0 : ℝ) 1, ∫ x, mean a Γ Ψ t x * Φ (t, x) =
      ∫ s, kern a (t - s) * stPair Γ Φ Ψ (t, s) ∂timeMeasure := by
    intro t ht
    simp_rw [← hsx, ← hxs]
    exact (integral_integral_swap (hJi t ht)).symm
  have hpt : ∀ t ∈ Icc (0 : ℝ) 1, Integrable (fun x => mean a Γ Ψ t x * Φ (t, x)) := by
    intro t ht
    have := (hJi t ht).integral_prod_right
    simp only [Function.uncurry] at this
    simpa only [hsx] using this
  have hKP := stIntegrand_integrable ha1 Γ hΦ hΦs hΨ hΨs
  have hae : (fun t => ∫ s, kern a (t - s) * stPair Γ Φ Ψ (t, s) ∂timeMeasure) =ᵐ[timeMeasure]
      fun t => ∫ x, mean a Γ Ψ t x * Φ (t, x) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact (hrow t (Ioo_subset_Icc_self ht)).symm
  refine ⟨hpt, (hKP.integral_prod_left).congr hae, ?_⟩
  show ∫ t, ∫ x, mean a Γ Ψ t x * Φ (t, x) ∂volume ∂timeMeasure = _
  rw [← integral_congr_ae hae, stForm, integral_prod _ hKP]

/-- **The variance identity `F(Ψ,Ψ) = v_Ψ`** (the integral form of the first identity of
`E:positive-raw-mean`, `‖Ψ‖²_{H_I} = v_Ψ`, `integrated_intrinsic_constant.tex` lines 31-36,
through `E:positive-bochner-inclusion`; auxiliary to the Lean route).  For `a < 1`, locally
finite `Γ` and a continuous compactly supported field `Ψ`,
`F(Ψ,Ψ) = ∫_I ∫ Ψ(σ,x) h_{Ψ,σ}(x) dx dσ = v_Ψ` (`VariationalDilation.rawCost`).  In
particular this holds for every control `Ψ ∈ C_pos`. -/
theorem stForm_self_eq_rawCost {a : ℝ} (ha1 : a < 1) (Γ : Measure (Rd d))
    [IsLocallyFiniteMeasure Γ] {Ψ : ℝ × Rd d → ℝ} (hΨ : Continuous Ψ)
    (hΨs : HasCompactSupport Ψ) : stForm a Γ Ψ Ψ = rawCost a Γ Ψ := by
  rw [← (integral_mean_mul_eq_stForm_swap ha1 Γ hΨ hΨs hΨ hΨs).2.2, rawCost]
  congr 1; funext σ; congr 1; funext x; ring

/-- **The mean identity, with the arguments of the manuscript** (the second identity of
`E:occupation-raw-identities`, `integrated_occupation_ceiling.tex` lines 33-37, for a
continuous compactly supported field `Φ` in place of `g²`; auxiliary to the Lean route).  For
`a < 1`, an even locally finite `Γ` and continuous compactly supported `Ψ, Φ`:
`x ↦ h_{Ψ,t}(x) Φ(t,x)` is integrable for every `t ∈ [0,1]`, `t ↦ ∫ h_{Ψ,t} Φ(t,·)` is
integrable on `I`, and `∫_I ∫ h_{Ψ,t}(x) Φ(t,x) dx dt = F(Ψ,Φ)`. -/
theorem integral_mean_mul_eq_stForm {a : ℝ} (ha1 : a < 1) {Γ : Measure (Rd d)}
    [IsLocallyFiniteMeasure Γ] (hE : IsEven Γ) {Ψ Φ : ℝ × Rd d → ℝ} (hΨ : Continuous Ψ)
    (hΨs : HasCompactSupport Ψ) (hΦ : Continuous Φ) (hΦs : HasCompactSupport Φ) :
    (∀ t ∈ Icc (0 : ℝ) 1, Integrable (fun x => mean a Γ Ψ t x * Φ (t, x))) ∧
      IntegrableOn (fun t => ∫ x, mean a Γ Ψ t x * Φ (t, x)) (Ioo (0 : ℝ) 1) ∧
      ∫ t in Ioo (0 : ℝ) 1, ∫ x, mean a Γ Ψ t x * Φ (t, x) = stForm a Γ Ψ Φ := by
  obtain ⟨h1, h2, h3⟩ := integral_mean_mul_eq_stForm_swap ha1 Γ hΨ hΨs hΦ hΦs
  exact ⟨h1, h2, h3.trans (stForm_comm hE hΦ hΦs hΨ hΨs)⟩

/-- Auxiliary: the square `G²` of a continuous compactly supported field is continuous and
compactly supported. -/
theorem sq_data {G : ℝ × Rd d → ℝ} (hG : Continuous G) (hGs : HasCompactSupport G) :
    Continuous (fun p => G p ^ 2) ∧ HasCompactSupport (fun p => G p ^ 2) := by
  refine ⟨hG.pow 2, ?_⟩
  have h : (fun p => G p ^ 2) = G * G := by funext p; simp [sq]
  rw [h]
  exact hGs.mul_left

/-- **The mean identity for a squared field** (`∫_0^1 ∫ h_s(x) G_s(x)² dx ds = F(Ψ, G²)`, the
second identity of `E:occupation-raw-identities`, `integrated_occupation_ceiling.tex`
lines 33-37, for continuous compactly supported `G`; auxiliary to the Lean route).
Hypotheses as in `integral_mean_mul_eq_stForm`. -/
theorem integral_mean_mul_sq_eq_stForm {a : ℝ} (ha1 : a < 1) {Γ : Measure (Rd d)}
    [IsLocallyFiniteMeasure Γ] (hE : IsEven Γ) {Ψ G : ℝ × Rd d → ℝ} (hΨ : Continuous Ψ)
    (hΨs : HasCompactSupport Ψ) (hG : Continuous G) (hGs : HasCompactSupport G) :
    (∀ t ∈ Icc (0 : ℝ) 1, Integrable (fun x => mean a Γ Ψ t x * G (t, x) ^ 2)) ∧
      IntegrableOn (fun t => ∫ x, mean a Γ Ψ t x * G (t, x) ^ 2) (Ioo (0 : ℝ) 1) ∧
      ∫ t in Ioo (0 : ℝ) 1, ∫ x, mean a Γ Ψ t x * G (t, x) ^ 2 =
        stForm a Γ Ψ (fun p => G p ^ 2) :=
  integral_mean_mul_eq_stForm (Φ := fun p => G p ^ 2) ha1 hE hΨ hΨs (sq_data hG hGs).1
    (sq_data hG hGs).2

/-- **The Cauchy-Schwarz bound against the mean** (the final display of
`L:occupation-raw-square`, `integrated_occupation_ceiling.tex` lines 39-41,
`⟨Ψ,ρ_g⟩ ≤ √(v_Ψ A(g))`, in the form of the space-time pairing, for a continuous compactly
supported field `Φ` in place of `g²`; auxiliary to the Lean route).  For `0 < a < 1`, an even
locally finite `Γ` with spectral measure `μ`, and continuous compactly supported `Ψ, Φ`:
`∫_I ∫ h_{Ψ,t}(x) Φ(t,x) dx dt ≤ √(v_Ψ F(Φ,Φ))`, with `v_Ψ ≥ 0` and `F(Φ,Φ) ≥ 0`. -/
theorem integral_mean_mul_le_sqrt {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {Γ μ : Measure (Rd d)}
    [IsLocallyFiniteMeasure Γ] (hE : IsEven Γ) (hsp : IsSpectralMeasure Γ μ)
    {Ψ Φ : ℝ × Rd d → ℝ} (hΨ : Continuous Ψ) (hΨs : HasCompactSupport Ψ) (hΦ : Continuous Φ)
    (hΦs : HasCompactSupport Φ) :
    0 ≤ rawCost a Γ Ψ ∧ 0 ≤ stForm a Γ Φ Φ ∧
      ∫ t in Ioo (0 : ℝ) 1, ∫ x, mean a Γ Ψ t x * Φ (t, x) ≤
        Real.sqrt (rawCost a Γ Ψ * stForm a Γ Φ Φ) := by
  have hv := stForm_self_eq_rawCost ha1 Γ hΨ hΨs
  refine ⟨hv ▸ stForm_self_nonneg ha0 ha1 hsp hΨ hΨs, stForm_self_nonneg ha0 ha1 hsp hΦ hΦs, ?_⟩
  rw [(integral_mean_mul_eq_stForm ha1 hE hΨ hΨs hΦ hΦs).2.2, ← hv]
  exact (le_abs_self _).trans
    (Real.abs_le_sqrt (stForm_sq_le ha0 ha1 hE hsp hΨ hΨs hΦ hΦs))

/-! ### The statements under the manuscript's standing hypotheses -/

/-- **Step (c) of the S1Bdd route under `H:homog`** (auxiliary to the Lean route; the
interface for the integrator).  With the standing hypotheses of
`S:intrinsic-occupation-ceiling` (`integrated_occupation_ceiling.tex` lines 4-6: the
original covariance under `H:homog`, `a = α₀`; the section's `Γ ≠ 0` is not needed and not
assumed), for continuous compactly supported real fields on `ℝ × ℝ^d` and controls
`Ψ ∈ C_pos`:
1. the integrand of `F(Φ₁,Φ₂)` is integrable on `(0,1)²`;
2. `F(Φ,Φ) ≥ 0`;
3. `F(Φ₁,Φ₂)² ≤ F(Φ₁,Φ₁) F(Φ₂,Φ₂)`;
4. `F(Ψ,Ψ) = v_Ψ`;
5. for every `t ∈ [0,1]`, `x ↦ h_{Ψ,t}(x) G(t,x)²` is integrable, `t ↦ ∫ h_{Ψ,t} G(t,·)²` is
   integrable on `(0,1)`, and `∫_0^1 ∫ h_{Ψ,t}(x) G(t,x)² dx dt = F(Ψ, G²)`;
6. `∫_0^1 ∫ h_{Ψ,t}(x) G(t,x)² dx dt ≤ √(v_Ψ F(G², G²))`.
Fields of `H:homog` used: `alpha0_pos`, `alpha0_lt_one`, `Γ_radon`, `Γ_even`, `spectral`. -/
theorem space_time_positivity_homog {alpha alpha0 : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogCovariance d alpha alpha0 Γ μ) :
    (∀ Φ₁ Φ₂ : ℝ × Rd d → ℝ, Continuous Φ₁ → HasCompactSupport Φ₁ → Continuous Φ₂ →
      HasCompactSupport Φ₂ →
      Integrable (fun p : ℝ × ℝ => kern alpha0 (p.1 - p.2) * stPair Γ Φ₁ Φ₂ p)
        (timeMeasure.prod timeMeasure)) ∧
    (∀ Φ : ℝ × Rd d → ℝ, Continuous Φ → HasCompactSupport Φ → 0 ≤ stForm alpha0 Γ Φ Φ) ∧
    (∀ Φ₁ Φ₂ : ℝ × Rd d → ℝ, Continuous Φ₁ → HasCompactSupport Φ₁ → Continuous Φ₂ →
      HasCompactSupport Φ₂ →
      stForm alpha0 Γ Φ₁ Φ₂ ^ 2 ≤ stForm alpha0 Γ Φ₁ Φ₁ * stForm alpha0 Γ Φ₂ Φ₂) ∧
    (∀ Ψ ∈ CPos d, stForm alpha0 Γ Ψ Ψ = rawCost alpha0 Γ Ψ) ∧
    (∀ Ψ ∈ CPos d, ∀ G : ℝ × Rd d → ℝ, Continuous G → HasCompactSupport G →
      (∀ t ∈ Icc (0 : ℝ) 1, Integrable (fun x => mean alpha0 Γ Ψ t x * G (t, x) ^ 2)) ∧
      IntegrableOn (fun t => ∫ x, mean alpha0 Γ Ψ t x * G (t, x) ^ 2) (Ioo (0 : ℝ) 1) ∧
      ∫ t in Ioo (0 : ℝ) 1, ∫ x, mean alpha0 Γ Ψ t x * G (t, x) ^ 2 =
        stForm alpha0 Γ Ψ (fun p => G p ^ 2)) ∧
    (∀ Ψ ∈ CPos d, ∀ G : ℝ × Rd d → ℝ, Continuous G → HasCompactSupport G →
      ∫ t in Ioo (0 : ℝ) 1, ∫ x, mean alpha0 Γ Ψ t x * G (t, x) ^ 2 ≤
        Real.sqrt (rawCost alpha0 Γ Ψ *
          stForm alpha0 Γ (fun p => G p ^ 2) (fun p => G p ^ 2))) := by
  have := hH.Γ_radon
  have ha0 := hH.alpha0_pos
  have ha1 := hH.alpha0_lt_one
  refine ⟨fun Φ₁ Φ₂ h₁ h₁s h₂ h₂s => stIntegrand_integrable ha1 Γ h₁ h₁s h₂ h₂s,
    fun Φ h hs => stForm_self_nonneg ha0 ha1 hH.spectral h hs,
    fun Φ₁ Φ₂ h₁ h₁s h₂ h₂s => stForm_sq_le ha0 ha1 hH.Γ_even hH.spectral h₁ h₁s h₂ h₂s,
    fun Ψ hΨ => stForm_self_eq_rawCost ha1 Γ hΨ.1.continuous hΨ.2.1,
    fun Ψ hΨ G hG hGs => integral_mean_mul_sq_eq_stForm ha1 hH.Γ_even hΨ.1.continuous hΨ.2.1
      hG hGs, fun Ψ hΨ G hG hGs => ?_⟩
  obtain ⟨hc, hcs⟩ := sq_data hG hGs
  exact (integral_mean_mul_le_sqrt ha0 ha1 hH.Γ_even hH.spectral hΨ.1.continuous hΨ.2.1
    hc hcs).2.2

/-- **`L:occupation-raw-square`, narrower form for continuous compactly supported profiles**
(`integrated_occupation_ceiling.tex`, statement lines 23-42, proof 44-90).  Hypotheses: the
section's standing assumptions (lines 4-6 and 20: `H:homog`, `a = α₀`, `Γ ≠ 0`) and
`Ψ ∈ C_pos`.  For a continuous compactly supported real field `g` on `ℝ × ℝ^d` (in place of
the class `O` of strongly `H¹`-measurable unit profiles) and `A(g) = F(g², g²)`
(`E:raw-occupation-definitions` with the original kernel, lines 10-18, for such `g`):
`A(g) ≥ 0` is a genuine integral; `x ↦ h_{Ψ,t}(x) g(t,x)²` is integrable for `t ∈ [0,1]` and
`t ↦ ∫ h_{Ψ,t} g(t,·)²` on `I`; `∫_I ∫ h_{Ψ,t}(x) g(t,x)² dx dt = F(Ψ, g²)` (the pairing
`⟨Ψ,ρ_g⟩` of `E:occupation-raw-identities` in its integral form); and
`∫_I ∫ h_{Ψ,t}(x) g(t,x)² dx dt ≤ √(v_Ψ A(g))` (line 40).  Narrower: the Hilbert space
`H_sp`, the map `Q`, the element `ρ_g ∈ H_I` and the norm identity `‖ρ_g‖² = A(g)` are not
formalized; the profile class is continuous compactly supported fields (no unit-norm
condition is needed for these statements); the Lean route is the mixture positivity of
`stForm_self_nonneg`, not the TeX's completion argument.  `Γ ≠ 0` is carried, unused. -/
theorem occupation_raw_square_cc_paper {alpha alpha0 : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogCovariance d alpha alpha0 Γ μ) (_hΓ : Γ ≠ 0) {a : ℝ} (ha : a = alpha0)
    {Ψ : ℝ × Rd d → ℝ} (hΨ : Ψ ∈ CPos d) {g : ℝ × Rd d → ℝ} (hg : Continuous g)
    (hgs : HasCompactSupport g) :
    Integrable (fun p : ℝ × ℝ => kern a (p.1 - p.2) *
        stPair Γ (fun p => g p ^ 2) (fun p => g p ^ 2) p) (timeMeasure.prod timeMeasure) ∧
      0 ≤ stForm a Γ (fun p => g p ^ 2) (fun p => g p ^ 2) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, Integrable (fun x => mean a Γ Ψ t x * g (t, x) ^ 2)) ∧
      IntegrableOn (fun t => ∫ x, mean a Γ Ψ t x * g (t, x) ^ 2) (Ioo (0 : ℝ) 1) ∧
      ∫ t in Ioo (0 : ℝ) 1, ∫ x, mean a Γ Ψ t x * g (t, x) ^ 2 =
        stForm a Γ Ψ (fun p => g p ^ 2) ∧
      ∫ t in Ioo (0 : ℝ) 1, ∫ x, mean a Γ Ψ t x * g (t, x) ^ 2 ≤
        Real.sqrt (rawCost a Γ Ψ * stForm a Γ (fun p => g p ^ 2) (fun p => g p ^ 2)) := by
  subst ha
  obtain ⟨h1, h2, -, -, h5, h6⟩ := space_time_positivity_homog hH
  obtain ⟨hc, hcs⟩ := sq_data hg hgs
  obtain ⟨e1, e2, e3⟩ := h5 Ψ hΨ g hg hgs
  exact ⟨h1 _ _ hc hcs hc hcs, h2 _ hc hcs, e1, e2, e3, h6 Ψ hΨ g hg hgs⟩

/-- **The variance identity of `L:positive-raw-embedding`, integral form**
(`integrated_intrinsic_constant.tex`, statement lines 22-39; `E:positive-raw-mean`, first
identity `‖Ψ‖²_{H_I} = v_Ψ`, lines 33-36, with `‖J_G F‖²` the integral of
`E:positive-bochner-inclusion`, lines 26-30).  Hypotheses: the section's standing
assumptions (lines 4-5 and 19: the original covariance under `H:homog`, `a = α₀`, `Γ ≠ 0`)
and `Ψ ∈ C_pos`.  Conclusion: the integrand of `F(Ψ,Ψ)` is integrable on `I²`, and
`F(Ψ,Ψ) = ∫∫_{I²} |s-t|^{-a} B_Γ(Ψ_s, Ψ_t) ds dt = v_Ψ` (`VariationalDilation.rawCost`, the
integral form of `E:compact-raw-cost`) and `v_Ψ ≥ 0`.  Narrower: the Hilbert spaces `H_t`,
`H_I`, the map `J_G`, its bound by `K_0`, and the mean identity
`T_R Ψ(s) = B_E(m_R h_{Ψ,s})` are not formalized.  `Γ ≠ 0` is carried, unused (it gives
`v_Ψ > 0`, which is `VariationalRate.rawCost_pos`). -/
theorem positive_raw_variance_form_paper {alpha alpha0 : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogCovariance d alpha alpha0 Γ μ) (_hΓ : Γ ≠ 0) {a : ℝ} (ha : a = alpha0)
    {Ψ : ℝ × Rd d → ℝ} (hΨ : Ψ ∈ CPos d) :
    Integrable (fun p : ℝ × ℝ => kern a (p.1 - p.2) * stPair Γ Ψ Ψ p)
        (timeMeasure.prod timeMeasure) ∧
      stForm a Γ Ψ Ψ = rawCost a Γ Ψ ∧ 0 ≤ rawCost a Γ Ψ := by
  subst ha
  obtain ⟨h1, h2, -, h4, -, -⟩ := space_time_positivity_homog hH
  exact ⟨h1 _ _ hΨ.1.continuous hΨ.2.1 hΨ.1.continuous hΨ.2.1, h4 Ψ hΨ,
    h4 Ψ hΨ ▸ h2 Ψ hΨ.1.continuous hΨ.2.1⟩

/-! ### The interface consumed by item L8-c2 (`OccupationCeilingFinite`) -/

/-- The space-time form as an iterated Bochner integral, verbatim the definition
`OccupationCeilingFinite.stForm` of item L8-c2:
`∫_0^1 ∫_0^1 |s-t|^{-a} B_Γ(Φ(s,·), Φ'(t,·)) dt ds`.  For continuous compactly supported
fields and `a < 1` it equals `stForm` (`stFormIter_eq`). -/
def stFormIter (a : ℝ) (Γ : Measure (Rd d)) (Φ Φ' : ℝ × Rd d → ℝ) : ℝ :=
  ∫ s in Ioo (0 : ℝ) 1, ∫ t in Ioo (0 : ℝ) 1,
    kern a (s - t) * spatialPair Γ (fun x => Φ (s, x)) (fun x => Φ' (t, x))

/-- The iterated form equals the product-measure form (Fubini, `integral_prod`) for `a < 1`,
locally finite `Γ` and continuous compactly supported fields. -/
theorem stFormIter_eq {a : ℝ} (ha1 : a < 1) (Γ : Measure (Rd d)) [IsLocallyFiniteMeasure Γ]
    {Φ Φ' : ℝ × Rd d → ℝ} (hΦ : Continuous Φ) (hΦs : HasCompactSupport Φ) (hΦ' : Continuous Φ')
    (hΦ's : HasCompactSupport Φ') : stFormIter a Γ Φ Φ' = stForm a Γ Φ Φ' := by
  rw [stForm, integral_prod _ (stIntegrand_integrable ha1 Γ hΦ hΦs hΦ' hΦ's)]
  rfl

/-- The three facts of step (c) in the form consumed by item L8-c2, verbatim
`OccupationCeilingFinite.SpaceTimeCS` with its `stForm` written `stFormIter` (the two
structures have definitionally equal fields): Cauchy-Schwarz `cs` (positive semidefiniteness,
`L:positive-raw-embedding`, `integrated_intrinsic_constant.tex` lines 22-39), `self`
(`F(Ψ,Ψ) = v_Ψ`, `E:positive-raw-mean`, line 34) and `mean` (`∫_0^1 ∫ h_{Ψ,s} Φ_s = F(Ψ,Φ)`,
`E:occupation-raw-identities`, `integrated_occupation_ceiling.tex` lines 33-37), for controls
`Ψ ∈ C_pos` and nonnegative continuous compactly supported fields `Φ`. -/
structure SpaceTimeCS (a : ℝ) (Γ : Measure (Rd d)) : Prop where
  cs : ∀ Ψ ∈ CPos d, ∀ Φ : ℝ × Rd d → ℝ, Continuous Φ → HasCompactSupport Φ →
    (∀ p, 0 ≤ Φ p) → stFormIter a Γ Ψ Φ ^ 2 ≤ stFormIter a Γ Ψ Ψ * stFormIter a Γ Φ Φ
  self : ∀ Ψ ∈ CPos d, stFormIter a Γ Ψ Ψ = rawCost a Γ Ψ
  mean : ∀ Ψ ∈ CPos d, ∀ Φ : ℝ × Rd d → ℝ, Continuous Φ → HasCompactSupport Φ →
    (∀ p, 0 ≤ Φ p) → ∫ s in Ioo (0 : ℝ) 1, ∫ x, mean a Γ Ψ s x * Φ (s, x) = stFormIter a Γ Ψ Φ

/-- **`SpaceTimeCS` holds under `H:homog` with `a = α₀`** (step (c) of the S1Bdd route,
discharged; no named input, `Γ ≠ 0` not needed).  Fields of `H:homog` used: `alpha0_pos`,
`alpha0_lt_one`, `Γ_radon`, `Γ_even`, `spectral`.  The nonnegativity hypothesis on `Φ` in
`SpaceTimeCS` is not used (the facts hold for every continuous compactly supported field). -/
theorem spaceTimeCS_holds {alpha alpha0 : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogCovariance d alpha alpha0 Γ μ) : SpaceTimeCS alpha0 Γ := by
  have := hH.Γ_radon
  have ha1 := hH.alpha0_lt_one
  obtain ⟨-, -, h3, h4, -, -⟩ := space_time_positivity_homog hH
  refine ⟨fun Ψ hΨ Φ hΦ hΦs _ => ?_, fun Ψ hΨ => ?_, fun Ψ hΨ Φ hΦ hΦs _ => ?_⟩
  · rw [stFormIter_eq ha1 Γ hΨ.1.continuous hΨ.2.1 hΦ hΦs,
      stFormIter_eq ha1 Γ hΨ.1.continuous hΨ.2.1 hΨ.1.continuous hΨ.2.1,
      stFormIter_eq ha1 Γ hΦ hΦs hΦ hΦs]
    exact h3 Ψ Φ hΨ.1.continuous hΨ.2.1 hΦ hΦs
  · rw [stFormIter_eq ha1 Γ hΨ.1.continuous hΨ.2.1 hΨ.1.continuous hΨ.2.1]
    exact h4 Ψ hΨ
  · rw [stFormIter_eq ha1 Γ hΨ.1.continuous hΨ.2.1 hΦ hΦs]
    exact (integral_mean_mul_eq_stForm ha1 hH.Γ_even hΨ.1.continuous hΨ.2.1 hΦ hΦs).2.2

end StratonovichHAMSecondMoment.SpaceTimePositivity
