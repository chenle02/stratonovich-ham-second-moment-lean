module

/-
Copyright 2026 Le Chen. SPDX-License-Identifier: Apache-2.0

Propositions `P:variational-unmasked-rate` (TeX lines 98-111; proof 113-164)
and `P:variational-positive-scores` (TeX lines 270-284; proof 286-337) of
`notes/integrated_unmasked_variational.tex` at revision a284420.  The
section's standing assumption (line 4) is a nonzero covariance satisfying
`H:homog` with `a = α₀`; the wrappers carry it as
`HomogHypothesis.HomogCovariance`, `Γ ≠ 0`, `a = α₀`.  Definitions reused
from `VariationalDilation`: the class `CPos` (`E:variational-positive-class`),
the mean `h_{Ψ,s}` (`mean`), the integral form `v_Ψ` of `E:compact-raw-cost`
(`rawCost`), the rate `λ_{Ψ,s}` DEFINED as the square root of the real Rayleigh supremum
`E:variational-real-rayleigh` (`rate`, over the hand-rolled weak-gradient
`H¹` of `WeakSobolev`) and `I_Ψ` (`integratedRate`).  New definitions:
`scoreSet a Γ c = {c I_Ψ - v_Ψ/2 : Ψ ∈ C_pos}`, the coefficient-one set
`score1Set` (`= scoreSet a Γ 1`, `scoreSet_one`), `S1pos = sup score1Set`, the
test radius `r_0` (`testRadius`) and the named input `S1Bdd`.  These are the
package's only score set, `S1Bdd` and `S1pos` (`SpatialSmoothRatio` and
`SpatialStaticControls` use them).

Formalized:
* `variational_unmasked_rate_paper` (Rayleigh-form part of
  `P:variational-unmasked-rate`; general form `unmasked_rate`): for
  `Ψ ∈ C_pos` and `s, t ∈ [0,1]`, the Rayleigh value set of `h_s` is
  nonempty and bounded above, with a uniform positive floor and ceiling
  `ε ≤ λ_s² = sup ≤ M`; `|λ_s² - λ_t²| ≤ C_Ψ|s - t|` (from the general
  `abs_sSup_rayleighSet_sub_le`, `|sup R_V - sup R_W| ≤ ‖V - W‖_∞`, TeX line
  156); `√ε ≤ λ_s ≤ √M`; `|λ_s - λ_t| ≤ C_Ψ/(2√ε)|s - t|` (line 158); `λ`
  integrable on `(0,1)`; `√ε ≤ I_Ψ ≤ √M`.
* `variational_positive_scores_paper` (general form `positive_scores`), no
  supplied input: the value sets are nonempty; every `I_Ψ` and `v_Ψ` is a
  genuine (integrable, finite) value with `I_Ψ > 0` and `v_Ψ > 0`
  (`rawCost_genuine`, `rawCost_pos`); the positive test at
  `r_0 = (I_0/v_0)^{1/k}` (lines 290-296); `E:variational-score-set-scaling`
  (lines 298-304, `score_set_scaling`); the set identity of lines 305-307
  (`scoreSet_eq`); boundedness for any `c > 0` is equivalent to `S1Bdd`.
* `variational_positive_scores_sSup_paper` (general form
  `positive_scores_sSup`), over the named input `S1Bdd`: `S_1^pos` is a
  positive real and `S_c^pos = c^{(4-α)/(3-α)} S_1^pos > 0` for every
  `c > 0`.

Supplied input (named, one): `S1Bdd a Γ`, the boundedness above of
`{I_Ψ - v_Ψ/2 : Ψ ∈ C_pos}`, word for word the claim of TeX lines 272-274 for
`c = 1`; by `positive_scores` it is equivalent to the boundedness for any
`c > 0`.  Provenance (lines 309-325): `T:full-upper` and
`E:variational-unmasked-point-lower` (`P:variational-remove-mask`), both
stochastic and not formalized.  It is used only by the supremum statements.
Since `I_Ψ` and `v_Ψ` are proved genuine first, no junk value enters it.

Narrower conclusions (not formalized):
* `P:variational-unmasked-rate`: the operator half (self-adjointness of
  `H_s = -Δ - h_s` on `H²`, form domain `H¹`, the spectral bottom `E_s` and
  `-E_s = sup R_s`), hence the primary definition `λ = √(-E_s)`; this needs
  the unbounded self-adjoint/spectral theory of foundation D8.  Here `λ` is
  the Rayleigh supremum, which the TeX proves equal to `√(-E_s)`.
* `P:variational-positive-scores`: the second identity `Q_2 ≥ S_2^pos` of
  `E:variational-score-homogeneity` (the stochastic point liminf `Q_2`), and
  the boundedness, supplied as `S1Bdd`.  The TeX's remark
  `S_2^pos > 2 S_1^pos` (line 333) is a comment, not part of the statement.
* `v_Ψ` is the integral form of `E:compact-raw-cost`; its identification with
  `E W(Ψ)²` is `L:compact-raw-profile` (foundation D1), not used.

Implicit hypotheses made explicit: `I = [0,1]`; the side condition
`integrable_pot` of `WeakSobolev.IsRayleighTrial` is automatic for `h_s`
(`VariationalMean.isRayleighTrial_mean_iff_paper`); finiteness of `I_Ψ`,
`v_Ψ` and of the suprema is stated as integrability and bounded-above
nonemptiness (Lean's junk values `0` for a non-integrable Bochner integral
and for `sSup` of an empty or unbounded set are thereby excluded).

Proof routes that differ from the TeX:
* Positivity floor: the TeX bounds `E_s ≤ -ε₀` by the compact common trial of
  `P:compact-original-common-trial` (lines 150-155).  Here: `h_s ≥ Γ * Ψ̄`
  for `s ∈ [0,1]` with `Ψ̄ = ∫_0^1 Ψ(u,·) du` (because `|s - u|^{-α₀} ≥ 1`
  on `[0,1]²` off the diagonal, and Fubini), and the dilation floor
  `VariationalFloor.dilation_floor` (uses `α < 2`) gives one unit test with
  value at least `ε` for every `s`.
* `v_Ψ > 0` (TeX: `L:compact-raw-profile`, `v = E W(Ψ)²`): `v_Ψ` is the
  integral of the continuous, nonnegative, compactly supported
  `Ψ(σ,x) h_σ(x)` over `ℝ × ℝ^d`, positive at a point where `Ψ > 0`, because
  `h_σ ≥ Γ * Ψ̄ > 0` there (`VariationalFloor.conv_pos`, which uses
  `Γ(B_r) > 0`).
* `I_Ψ > 0` follows from the floor; the TeX deduces it from the same bound
  `λ ≥ √ε₀`.
Lemmas marked "Auxiliary to the Lean proof route" have no manuscript label.
-/
public import Mathlib
public import StratonovichHAMSecondMoment.HomogHypothesis
public import StratonovichHAMSecondMoment.WeakSobolev
public import StratonovichHAMSecondMoment.VariationalDilation
public import StratonovichHAMSecondMoment.VariationalMean
public import StratonovichHAMSecondMoment.VariationalFloor

@[expose] public section

noncomputable section

set_option autoImplicit false

open MeasureTheory Set Metric
open scoped ContDiff Pointwise

namespace StratonovichHAMSecondMoment.VariationalRate

open HomogHypothesis (Rd HomogCovariance IsTempered IsSpectralMeasure)
open WeakSobolev
open VariationalDilation (CPos SetScaling conv mean rawCost rate integratedRate dil)
open VariationalMean (ctrl_data conv_integrable pt_bound gauss_conv convT_continuous conv_le
  mean_integrableOn global_mean integrable_pot_of_bounded mean_continuous_of_lip dist_same_time
  dist_same_space mean_nonneg)
open VariationalFloor (dilation_floor conv_pos)

variable {d : ℕ}

/-! ### The time-averaged control -/

/-- Auxiliary to the Lean proof route: the time average
`Ψ̄(y) = ∫_{(0,1)} Ψ(u, y) du` of a control. -/
def psiBar (Ψ : ℝ × Rd d → ℝ) (y : Rd d) : ℝ := ∫ u in Ioo (0 : ℝ) 1, Ψ (u, y)

/-- Auxiliary to the Lean proof route: `Ψ̄` is continuous for continuous `Ψ`. -/
theorem psiBar_continuous {Ψ : ℝ × Rd d → ℝ} (hΨ : Continuous Ψ) : Continuous (psiBar Ψ) := by
  have h := continuous_parametric_integral_of_continuous (f := fun (y : Rd d) (u : ℝ) => Ψ (u, y))
    (μ := volume) (s := Icc (0 : ℝ) 1) (hΨ.comp continuous_swap) isCompact_Icc
  refine h.congr fun y => ?_
  exact integral_Icc_eq_integral_Ioo

/-- Auxiliary to the Lean proof route: `Ψ̄ ≥ 0` for `Ψ ≥ 0`. -/
theorem psiBar_nonneg {Ψ : ℝ × Rd d → ℝ} (hΨ0 : ∀ p, 0 ≤ Ψ p) (y : Rd d) : 0 ≤ psiBar Ψ y :=
  setIntegral_nonneg measurableSet_Ioo fun _ _ => hΨ0 _

/-- Auxiliary to the Lean proof route: `Ψ̄` vanishes where every `Ψ(u, ·)` does. -/
theorem psiBar_vanish {Ψ : ℝ × Rd d → ℝ} {R : ℝ} (hR : ∀ u z, R < ‖z‖ → Ψ (u, z) = 0)
    (z : Rd d) (hz : R < ‖z‖) : psiBar Ψ z = 0 := by
  simp [psiBar, hR _ _ hz]

/-- Auxiliary to the Lean proof route: `|Ψ̄| ≤ B` when `|Ψ| ≤ B`. -/
theorem psiBar_le {Ψ : ℝ × Rd d → ℝ} {B : ℝ} (hB : ∀ p, |Ψ p| ≤ B) (y : Rd d) :
    |psiBar Ψ y| ≤ B := by
  have h := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Ioo (0 : ℝ) 1)
    (f := fun u => Ψ (u, y)) (C := B) (by simp) (fun u _ => by
      rw [Real.norm_eq_abs]; exact hB _)
  rw [Real.volume_real_Ioo] at h
  simpa [psiBar] using h

/-- Auxiliary to the Lean proof route: `Ψ̄ > 0` at `x₀` if `Ψ(σ₀, x₀) > 0` for
some `σ₀ ∈ (0,1)` (continuous `Ψ ≥ 0`). -/
theorem psiBar_pos {Ψ : ℝ × Rd d → ℝ} (hΨ : Continuous Ψ) (hΨ0 : ∀ p, 0 ≤ Ψ p) {σ₀ : ℝ}
    {x₀ : Rd d} (hσ : σ₀ ∈ Ioo (0 : ℝ) 1) (hpos : 0 < Ψ (σ₀, x₀)) : 0 < psiBar Ψ x₀ := by
  have hc : Continuous fun u : ℝ => Ψ (u, x₀) := hΨ.comp (by fun_prop)
  have hint : IntegrableOn (fun u : ℝ => Ψ (u, x₀)) (Ioo 0 1) :=
    (hc.integrableOn_Icc (a := 0) (b := 1)).mono_set Ioo_subset_Icc_self
  unfold psiBar
  rw [integral_pos_iff_support_of_nonneg (fun u => hΨ0 _) hint,
    Measure.restrict_apply' measurableSet_Ioo]
  have ho : IsOpen ({u : ℝ | 0 < Ψ (u, x₀)} ∩ Ioo 0 1) :=
    (isOpen_lt continuous_const hc).inter isOpen_Ioo
  refine (ho.measure_pos volume ⟨σ₀, hpos, hσ⟩).trans_le (measure_mono ?_)
  rintro u ⟨hu1, hu2⟩
  exact ⟨(ne_of_gt hu1), hu2⟩

/-- Auxiliary to the Lean proof route: a control in `CPos` is positive at some
point `(σ₀, x₀)` with `σ₀ ∈ (0,1)`. -/
theorem exists_pos_point {Ψ : ℝ × Rd d → ℝ} (hΨ : Ψ ∈ CPos d) :
    ∃ σ₀ x₀, σ₀ ∈ Ioo (0 : ℝ) 1 ∧ 0 < Ψ (σ₀, x₀) := by
  obtain ⟨-, -, ht, h0, hne⟩ := hΨ
  obtain ⟨p, hp⟩ : ∃ p, Ψ p ≠ 0 := by
    by_contra h; push Not at h; exact hne (funext h)
  exact ⟨p.1, p.2, (ht (subset_tsupport Ψ hp)).1, lt_of_le_of_ne (h0 p) (Ne.symm hp)⟩

/-- Auxiliary to the Lean proof route: `Ψ̄` of a control in `CPos` is
continuous, nonnegative, compactly supported, nonzero and bounded by the
bound of `Ψ`. -/
theorem psiBar_data {Ψ : ℝ × Rd d → ℝ} (hΨ : Ψ ∈ CPos d) :
    Continuous (psiBar Ψ) ∧ (∀ y, 0 ≤ psiBar Ψ y) ∧ HasCompactSupport (psiBar Ψ) ∧
      ∃ σ₀ x₀, σ₀ ∈ Ioo (0 : ℝ) 1 ∧ 0 < Ψ (σ₀, x₀) ∧ 0 < psiBar Ψ x₀ := by
  obtain ⟨B, L, R, -, -, hB, hL, hR⟩ := ctrl_data hΨ
  refine ⟨psiBar_continuous hΨ.1.continuous, psiBar_nonneg hΨ.2.2.2.1,
    HasCompactSupport.intro (isCompact_closedBall (0 : Rd d) R) fun z hz => ?_, ?_⟩
  · rw [mem_closedBall, dist_zero_right, not_le] at hz
    exact psiBar_vanish hR z hz
  · obtain ⟨σ₀, x₀, hσ, hpos⟩ := exists_pos_point hΨ
    exact ⟨σ₀, x₀, hσ, hpos, psiBar_pos hΨ.1.continuous hΨ.2.2.2.1 hσ hpos⟩

section genuine

variable {Γ μ : Measure (Rd d)} (hΓt : IsTempered Γ) (hμt : IsTempered μ)
  (hsp : IsSpectralMeasure Γ μ)
include hΓt hμt hsp

/-- Auxiliary to the Lean proof route: `y ↦ Ψ̄(x - y)` is `Γ`-integrable. -/
theorem psiBar_conv_integrable {Ψ : ℝ × Rd d → ℝ} (hΨ : Ψ ∈ CPos d) (x : Rd d) :
    Integrable (fun y => psiBar Ψ (x - y)) Γ := by
  obtain ⟨B, L, R, -, -, hB, hL, hR⟩ := ctrl_data hΨ
  exact conv_integrable (Ψ := fun p : ℝ × Rd d => psiBar Ψ p.2) hΓt hμt hsp
    ((psiBar_continuous hΨ.1.continuous).comp continuous_snd) (fun p => psiBar_le hB p.2)
    (fun _ z hz => psiBar_vanish hR z hz) 0 x

/-- Auxiliary to the Lean proof route (Fubini in `(u, y)`):
`∫_{(0,1)} (Γ * Ψ(u,·))(x) du = (Γ * Ψ̄)(x)`. -/
theorem timeAvg_conv [SFinite Γ] {Ψ : ℝ × Rd d → ℝ} (hΨ : Ψ ∈ CPos d) (x : Rd d) :
    ∫ u in Ioo (0 : ℝ) 1, conv Γ (fun y => Ψ (u, y)) x = conv Γ (psiBar Ψ) x := by
  obtain ⟨B, L, R, hB0, -, hB, hL, hR⟩ := ctrl_data hΨ
  unfold conv psiBar
  refine integral_integral_swap ?_
  have hg := (gauss_conv hΓt hμt hsp x).1
  have h1 : Integrable (fun _ : ℝ => (1 : ℝ)) (volume.restrict (Ioo (0 : ℝ) 1)) :=
    integrableOn_const (by simp)
  have hprod := (h1.mul_prod hg).const_mul (B * Real.exp (R ^ 2 / 2))
  refine hprod.mono' ?_ (Filter.Eventually.of_forall fun p => ?_)
  · exact (hΨ.1.continuous.comp (by fun_prop)).aestronglyMeasurable
  · simp only [Function.uncurry, one_mul, Real.norm_eq_abs]
    have := pt_bound hB hR p.1 (x - p.2)
    linarith

/-- Auxiliary to the Lean proof route: the time integrand of the mean is
integrable on `(0,1)` without its kernel. -/
theorem convT_integrableOn {Ψ : ℝ × Rd d → ℝ} (hΨ : Ψ ∈ CPos d) (x : Rd d) :
    IntegrableOn (fun u => conv Γ (fun y => Ψ (u, y)) x) (Ioo 0 1) := by
  obtain ⟨B, L, R, -, -, hB, hL, hR⟩ := ctrl_data hΨ
  have hc := convT_continuous hΓt hμt hsp hΨ.1.continuous hB hL hR
  exact ((hc.comp (by fun_prop : Continuous fun u : ℝ => (u, x))).integrableOn_Icc
    (a := 0) (b := 1)).mono_set Ioo_subset_Icc_self

/-- The lower envelope of the mean: for `0 ≤ a < 1` and `s ∈ [0,1]`,
`h_s ≥ Γ * Ψ̄`, because `|s - u|^{-a} ≥ 1` for `u ∈ (0,1)`, `u ≠ s`
(auxiliary to the Lean proof route; it replaces the compact common trial of the
TeX). -/
theorem conv_psiBar_le_mean [SFinite Γ] {Ψ : ℝ × Rd d → ℝ} (hΨ : Ψ ∈ CPos d) {a : ℝ}
    (ha0 : 0 ≤ a) (ha : a < 1) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (x : Rd d) :
    conv Γ (psiBar Ψ) x ≤ mean a Γ Ψ s x := by
  obtain ⟨B, L, R, -, -, hB, hL, hR⟩ := ctrl_data hΨ
  rw [← timeAvg_conv hΓt hμt hsp hΨ x, mean]
  refine setIntegral_mono_ae_restrict (convT_integrableOn hΓt hμt hsp hΨ x)
    (mean_integrableOn hΓt hμt hsp hΨ hB hL hR ha hs x) ?_
  have hne : ∀ᵐ u ∂(volume.restrict (Ioo (0 : ℝ) 1)), u ≠ s :=
    ae_restrict_of_ae (compl_mem_ae_iff.mpr (measure_singleton s))
  filter_upwards [hne, ae_restrict_mem measurableSet_Ioo] with u hu hu'
  have hc0 : 0 ≤ conv Γ (fun y => Ψ (u, y)) x := integral_nonneg fun _ => hΨ.2.2.2.1 _
  have hpos : 0 < |s - u| := abs_pos.mpr (sub_ne_zero.mpr (Ne.symm hu))
  have hle : |s - u| ≤ 1 := by
    rw [abs_le]; constructor <;> linarith [hs.1, hs.2, hu'.1, hu'.2]
  have h1 : 1 ≤ |s - u| ^ (-a) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hpos hle (by linarith)
  calc conv Γ (fun y => Ψ (u, y)) x = 1 * conv Γ (fun y => Ψ (u, y)) x := (one_mul _).symm
    _ ≤ |s - u| ^ (-a) * conv Γ (fun y => Ψ (u, y)) x := mul_le_mul_of_nonneg_right h1 hc0

end genuine

/-! ### Rayleigh value sets of bounded potentials -/

/-- Every real Rayleigh value of a potential `V ≤ M` is at most `M`. -/
theorem rayleighValue_le {V : Rd d → ℝ} {M : ℝ} (hVM : ∀ x, V x ≤ M) {q : ℝ}
    (hq : q ∈ rayleighSet V) : q ≤ M := by
  obtain ⟨f, g, hT, rfl⟩ := hq
  have h1 : ∫ x, V x * f x ^ 2 ≤ ∫ x, M * f x ^ 2 :=
    integral_mono hT.integrable_pot (hT.memLp_f.integrable_sq.const_mul M)
      fun x => mul_le_mul_of_nonneg_right (hVM x) (sq_nonneg _)
  rw [integral_const_mul, hT.unit, mul_one] at h1
  have h2 : 0 ≤ ∫ x, ‖g x‖ ^ 2 := integral_nonneg fun _ => sq_nonneg _
  rw [rayleighValue]; linarith

/-- Comparing identical unit tests: if `V - W ≤ D` pointwise, every trial of
`V` is a trial of `W`, `R_V` is nonempty and `R_W` is bounded above, then
`sup R_V ≤ sup R_W + D`. -/
theorem sSup_rayleighSet_le_add {V W : Rd d → ℝ} {D : ℝ} (hD : ∀ x, V x - W x ≤ D)
    (hW : ∀ f : Rd d → ℝ, MemLp f 2 volume → Integrable (fun x => W x * f x ^ 2) volume)
    (hne : (rayleighSet V).Nonempty) (hbdd : BddAbove (rayleighSet W)) :
    sSup (rayleighSet V) ≤ sSup (rayleighSet W) + D := by
  refine csSup_le hne fun q hq => ?_
  obtain ⟨f, g, hT, rfl⟩ := hq
  have hTW : IsRayleighTrial W f g := ⟨hT.memLp_f, hT.memLp_g, hT.weakGrad, hT.unit,
    hW f hT.memLp_f⟩
  have hmem : rayleighValue W f g ∈ rayleighSet W := ⟨f, g, hTW, rfl⟩
  have hdiff : rayleighValue V f g - rayleighValue W f g ≤ D := by
    have e : rayleighValue V f g - rayleighValue W f g = ∫ x, (V x - W x) * f x ^ 2 := by
      rw [rayleighValue, rayleighValue]
      simp_rw [sub_mul]
      rw [integral_sub hT.integrable_pot hTW.integrable_pot]; ring
    rw [e]
    have hint : Integrable (fun x => (V x - W x) * f x ^ 2) volume := by
      simp_rw [sub_mul]; exact hT.integrable_pot.sub hTW.integrable_pot
    calc ∫ x, (V x - W x) * f x ^ 2 ≤ ∫ x, D * f x ^ 2 :=
          integral_mono hint (hT.memLp_f.integrable_sq.const_mul D)
            fun x => mul_le_mul_of_nonneg_right (hD x) (sq_nonneg _)
      _ = D := by rw [integral_const_mul, hT.unit, mul_one]
  linarith [le_csSup hbdd hmem]

/-- `|λ_V² - λ_W²| ≤ ‖V - W‖_∞` in the Rayleigh form: if `|V - W| ≤ D`
pointwise, both `V f²` and `W f²` are integrable for every `f ∈ L²`, and both
value sets are nonempty and bounded above, then
`|sup R_V - sup R_W| ≤ D` (TeX line 156, "comparing identical unit form
tests"). -/
theorem abs_sSup_rayleighSet_sub_le {V W : Rd d → ℝ} {D : ℝ} (hD : ∀ x, |V x - W x| ≤ D)
    (hV : ∀ f : Rd d → ℝ, MemLp f 2 volume → Integrable (fun x => V x * f x ^ 2) volume)
    (hW : ∀ f : Rd d → ℝ, MemLp f 2 volume → Integrable (fun x => W x * f x ^ 2) volume)
    (hneV : (rayleighSet V).Nonempty) (hneW : (rayleighSet W).Nonempty)
    (hbV : BddAbove (rayleighSet V)) (hbW : BddAbove (rayleighSet W)) :
    |sSup (rayleighSet V) - sSup (rayleighSet W)| ≤ D := by
  have h1 := sSup_rayleighSet_le_add (fun x => (le_abs_self _).trans (hD x)) hW hneV hbW
  have h2 := sSup_rayleighSet_le_add (D := D) (fun x => by
    have := hD x; rw [abs_sub_comm] at this; exact (le_abs_self _).trans this) hV hneW hbV
  rw [abs_le]; constructor <;> linarith

/-- Auxiliary to the Lean proof route: `|√a - √b| ≤ |a - b|/(2√ε)` for
`a, b ≥ ε > 0`. -/
theorem abs_sqrt_sub_le {ε a b : ℝ} (hε : 0 < ε) (ha : ε ≤ a) (hb : ε ≤ b) :
    |Real.sqrt a - Real.sqrt b| ≤ |a - b| / (2 * Real.sqrt ε) := by
  have hse : 0 < Real.sqrt ε := Real.sqrt_pos.mpr hε
  have hsa : Real.sqrt ε ≤ Real.sqrt a := Real.sqrt_le_sqrt ha
  have hsb : Real.sqrt ε ≤ Real.sqrt b := Real.sqrt_le_sqrt hb
  have hprod : (Real.sqrt a - Real.sqrt b) * (Real.sqrt a + Real.sqrt b) = a - b := by
    have e1 := Real.sq_sqrt (hε.le.trans ha)
    have e2 := Real.sq_sqrt (hε.le.trans hb)
    nlinarith
  rw [le_div_iff₀ (by positivity)]
  have hsum : 2 * Real.sqrt ε ≤ Real.sqrt a + Real.sqrt b := by linarith
  calc |Real.sqrt a - Real.sqrt b| * (2 * Real.sqrt ε)
      ≤ |Real.sqrt a - Real.sqrt b| * (Real.sqrt a + Real.sqrt b) :=
        mul_le_mul_of_nonneg_left hsum (abs_nonneg _)
    _ = |a - b| := by
        rw [← hprod, abs_mul, abs_of_pos (show 0 < Real.sqrt a + Real.sqrt b by linarith)]

/-! ### `P:variational-unmasked-rate`, Rayleigh-form part -/

/-- **`P:variational-unmasked-rate`, Rayleigh-form part, general form.**  For
tempered `Γ`, `μ` with the spectral convention, `Γ` nonzero and locally
finite with the set scaling of `H:homog`, `α < 2`, `0 ≤ a < 1` and
`Ψ ∈ CPos`: there are reals `ε > 0`, `M ≥ ε`, `C ≥ 0` such that, for
`s, t ∈ [0,1]`, `0 ≤ h_s ≤ M`, `|h_s(x) - h_t(x)| ≤ C|s - t|`, the real
Rayleigh value set `R_s` of `h_s` is nonempty and bounded above with
`ε ≤ sup R_s ≤ M` (a uniform positive floor), `λ_s² = sup R_s`,
`√ε ≤ λ_s ≤ √M`, `|sup R_s - sup R_t| ≤ C|s - t|`,
`|λ_s - λ_t| ≤ C/(2√ε) |s - t|`, `λ` is integrable on `(0,1)`, and
`√ε ≤ I_Ψ ≤ √M` (so `I_Ψ` is positive and finite). -/
theorem unmasked_rate {alpha : ℝ} {Γ μ : Measure (Rd d)} (hΓt : IsTempered Γ)
    (hμt : IsTempered μ) (hsp : IsSpectralMeasure Γ μ) [IsLocallyFiniteMeasure Γ]
    (hS : SetScaling alpha Γ) (hα : alpha < 2) (hΓ : Γ ≠ 0) {a : ℝ} (ha0 : 0 ≤ a) (ha : a < 1)
    {Ψ : ℝ × Rd d → ℝ} (hΨ : Ψ ∈ CPos d) :
    ∃ ε M C : ℝ, 0 < ε ∧ ε ≤ M ∧ 0 ≤ C ∧
      (∀ s ∈ Icc (0 : ℝ) 1, ∀ x, 0 ≤ mean a Γ Ψ s x ∧ mean a Γ Ψ s x ≤ M) ∧
      (∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, ∀ x,
        |mean a Γ Ψ s x - mean a Γ Ψ t x| ≤ C * |s - t|) ∧
      (∀ s ∈ Icc (0 : ℝ) 1,
        (rayleighSet (mean a Γ Ψ s)).Nonempty ∧ BddAbove (rayleighSet (mean a Γ Ψ s)) ∧
        ε ≤ sSup (rayleighSet (mean a Γ Ψ s)) ∧ sSup (rayleighSet (mean a Γ Ψ s)) ≤ M ∧
        rate a Γ Ψ s ^ 2 = sSup (rayleighSet (mean a Γ Ψ s)) ∧
        Real.sqrt ε ≤ rate a Γ Ψ s ∧ rate a Γ Ψ s ≤ Real.sqrt M) ∧
      (∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
        |sSup (rayleighSet (mean a Γ Ψ s)) - sSup (rayleighSet (mean a Γ Ψ t))| ≤
          C * |s - t|) ∧
      (∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
        |rate a Γ Ψ s - rate a Γ Ψ t| ≤ C / (2 * Real.sqrt ε) * |s - t|) ∧
      IntegrableOn (rate a Γ Ψ) (Ioo 0 1) ∧
      Real.sqrt ε ≤ integratedRate a Γ Ψ ∧ integratedRate a Γ Ψ ≤ Real.sqrt M := by
  obtain ⟨M, C, hM0, hC, -, -, hbd, hlip⟩ := global_mean hΓt hμt hsp hΨ ha
  have hcont : ∀ s ∈ Icc (0 : ℝ) 1, Continuous (mean a Γ Ψ s) := fun s hs =>
    mean_continuous_of_lip hC fun x x' => hlip s hs s hs x x'
  have hpot : ∀ s ∈ Icc (0 : ℝ) 1, ∀ f : Rd d → ℝ, MemLp f 2 volume →
      Integrable (fun x => mean a Γ Ψ s x * f x ^ 2) volume := fun s hs f hf =>
    integrable_pot_of_bounded (hcont s hs) (M := M) (fun x => by
      rw [abs_of_nonneg (hbd s hs x).1]; exact (hbd s hs x).2) hf
  have hlipx : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, ∀ x,
      |mean a Γ Ψ s x - mean a Γ Ψ t x| ≤ C * |s - t| := fun s hs t ht x => by
    rw [← dist_same_space s t x]; exact hlip s hs t ht x x
  obtain ⟨hzc, hz0, hzs, σ₀, x₀, -, -, hzpos⟩ := psiBar_data hΨ
  have hzne : psiBar Ψ ≠ 0 := fun h => by rw [h] at hzpos; exact lt_irrefl _ hzpos
  obtain ⟨f, g, ε, hε, -, hf, hg, hw, hu, hval⟩ :=
    dilation_floor hS hα hΓ hzc hzs hz0 hzne (psiBar_conv_integrable hΓt hμt hsp hΨ)
  have hT : ∀ s ∈ Icc (0 : ℝ) 1, IsRayleighTrial (mean a Γ Ψ s) f g := fun s hs =>
    ⟨hf, hg, hw, hu, hpot s hs f hf⟩
  have hmem : ∀ s ∈ Icc (0 : ℝ) 1, rayleighValue (mean a Γ Ψ s) f g ∈
      rayleighSet (mean a Γ Ψ s) := fun s hs => ⟨f, g, hT s hs, rfl⟩
  have hvε : ∀ s ∈ Icc (0 : ℝ) 1, ε ≤ rayleighValue (mean a Γ Ψ s) f g := fun s hs =>
    hval _ (conv_psiBar_le_mean hΓt hμt hsp hΨ ha0 ha hs) (hpot s hs f hf)
  have hne : ∀ s ∈ Icc (0 : ℝ) 1, (rayleighSet (mean a Γ Ψ s)).Nonempty := fun s hs =>
    ⟨_, hmem s hs⟩
  have hbdd : ∀ s ∈ Icc (0 : ℝ) 1, BddAbove (rayleighSet (mean a Γ Ψ s)) := fun s hs =>
    ⟨M, fun q hq => rayleighValue_le (fun x => (hbd s hs x).2) hq⟩
  have hlo : ∀ s ∈ Icc (0 : ℝ) 1, ε ≤ sSup (rayleighSet (mean a Γ Ψ s)) := fun s hs =>
    (hvε s hs).trans (le_csSup (hbdd s hs) (hmem s hs))
  have hhi : ∀ s ∈ Icc (0 : ℝ) 1, sSup (rayleighSet (mean a Γ Ψ s)) ≤ M := fun s hs =>
    csSup_le (hne s hs) fun q hq => rayleighValue_le (fun x => (hbd s hs x).2) hq
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have hεM : ε ≤ M := (hlo 0 h0).trans (hhi 0 h0)
  have hrate : ∀ s, rate a Γ Ψ s = Real.sqrt (sSup (rayleighSet (mean a Γ Ψ s))) :=
    fun s => rfl
  have hsupLip : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      |sSup (rayleighSet (mean a Γ Ψ s)) - sSup (rayleighSet (mean a Γ Ψ t))| ≤
        C * |s - t| := fun s hs t ht =>
    abs_sSup_rayleighSet_sub_le (hlipx s hs t ht) (hpot s hs) (hpot t ht) (hne s hs)
      (hne t ht) (hbdd s hs) (hbdd t ht)
  have hrateLip : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      |rate a Γ Ψ s - rate a Γ Ψ t| ≤ C / (2 * Real.sqrt ε) * |s - t| := by
    intro s hs t ht
    rw [hrate, hrate]
    refine (abs_sqrt_sub_le hε (hlo s hs) (hlo t ht)).trans ?_
    rw [div_mul_eq_mul_div, mul_comm C]
    exact div_le_div_of_nonneg_right (by rw [mul_comm]; exact hsupLip s hs t ht)
      (by positivity)
  have hrateLo : ∀ s ∈ Icc (0 : ℝ) 1, Real.sqrt ε ≤ rate a Γ Ψ s := fun s hs => by
    rw [hrate]; exact Real.sqrt_le_sqrt (hlo s hs)
  have hrateHi : ∀ s ∈ Icc (0 : ℝ) 1, rate a Γ Ψ s ≤ Real.sqrt M := fun s hs => by
    rw [hrate]; exact Real.sqrt_le_sqrt (hhi s hs)
  have hcontOn : ContinuousOn (rate a Γ Ψ) (Icc 0 1) := by
    refine (LipschitzOnWith.of_dist_le_mul
      (K := Real.toNNReal (C / (2 * Real.sqrt ε))) fun s hs t ht => ?_).continuousOn
    rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ (by positivity)]
    exact hrateLip s hs t ht
  have hint : IntegrableOn (rate a Γ Ψ) (Ioo 0 1) :=
    (hcontOn.integrableOn_compact isCompact_Icc).mono_set Ioo_subset_Icc_self
  have hvol : (volume : Measure ℝ).real (Ioo 0 1) = 1 := by simp
  refine ⟨ε, M, C, hε, hεM, hC, hbd, hlipx, fun s hs => ⟨hne s hs, hbdd s hs, hlo s hs,
    hhi s hs, ?_, hrateLo s hs, hrateHi s hs⟩, hsupLip, hrateLip, hint, ?_, ?_⟩
  · rw [hrate]; exact Real.sq_sqrt (hε.le.trans (hlo s hs))
  · have := setIntegral_mono_on (integrableOn_const (C := Real.sqrt ε) (by simp)) hint
      measurableSet_Ioo fun s hs => hrateLo s (Ioo_subset_Icc_self hs)
    rwa [setIntegral_const, hvol, one_smul] at this
  · have := setIntegral_mono_on hint (integrableOn_const (C := Real.sqrt M) (by simp))
      measurableSet_Ioo fun s hs => hrateHi s (Ioo_subset_Icc_self hs)
    rwa [setIntegral_const, hvol, one_smul] at this


/-! ### The variance `v_Ψ` is a genuine positive integral -/

/-- Auxiliary to the Lean proof route: the variance integrand
`G(σ, x) = Ψ(σ, x) h_σ(x)` on `ℝ × ℝ^d`. -/
def costIntegrand (a : ℝ) (Γ : Measure (Rd d)) (Ψ : ℝ × Rd d → ℝ) (p : ℝ × Rd d) : ℝ :=
  Ψ p * mean a Γ Ψ p.1 p.2

/-- Auxiliary to the Lean proof route: for tempered `Γ`, `μ` with the spectral
convention, `a < 1` and `Ψ ∈ CPos`, the variance integrand is continuous with
compact support (joint Lipschitz bound of the mean on `[0,1] × ℝ^d`, and
`tsupport Ψ ⊆ (0,1) × ℝ^d`). -/
theorem costIntegrand_data {Γ μ : Measure (Rd d)} (hΓt : IsTempered Γ) (hμt : IsTempered μ)
    (hsp : IsSpectralMeasure Γ μ) {a : ℝ} (ha : a < 1) {Ψ : ℝ × Rd d → ℝ}
    (hΨ : Ψ ∈ CPos d) :
    Continuous (costIntegrand a Γ Ψ) ∧ HasCompactSupport (costIntegrand a Γ Ψ) := by
  obtain ⟨M, C, -, hC, -, -, -, hlip⟩ := global_mean hΓt hμt hsp hΨ ha
  have hmc : ContinuousOn (fun p : ℝ × Rd d => mean a Γ Ψ p.1 p.2) (Icc 0 1 ×ˢ univ) := by
    refine (LipschitzOnWith.of_dist_le_mul (K := Real.toNNReal C)
      fun p hp q hq => ?_).continuousOn
    rw [Real.dist_eq, Real.coe_toNNReal _ hC]
    exact hlip p.1 hp.1 q.1 hq.1 p.2 q.2
  have hGc : ContinuousOn (costIntegrand a Γ Ψ) (Ioo 0 1 ×ˢ univ) :=
    hΨ.1.continuous.continuousOn.mul
      (hmc.mono (prod_mono Ioo_subset_Icc_self subset_rfl))
  refine ⟨hGc.continuous_of_tsupport_subset (isOpen_Ioo.prod isOpen_univ)
    ((tsupport_mul_subset_left).trans hΨ.2.2.1), hΨ.2.1.mul_right⟩

/-- `v_Ψ` (`VariationalDilation.rawCost`, the integral form of
`E:compact-raw-cost`) is a genuine integral: for tempered `Γ`, `μ` with the
spectral convention, `a < 1` and `Ψ ∈ CPos`, every spatial integrand
`x ↦ Ψ(σ,x) h_σ(x)` is integrable, the time integrand
`σ ↦ ∫ Ψ(σ,x) h_σ(x) dx` is integrable on `(0,1)`, and `v_Ψ` equals the
integral of `Ψ(σ,x) h_σ(x)` over `ℝ × ℝ^d`. -/
theorem rawCost_genuine {Γ μ : Measure (Rd d)} (hΓt : IsTempered Γ) (hμt : IsTempered μ)
    (hsp : IsSpectralMeasure Γ μ) {a : ℝ} (ha : a < 1) {Ψ : ℝ × Rd d → ℝ}
    (hΨ : Ψ ∈ CPos d) :
    (∀ σ, Integrable (fun x => Ψ (σ, x) * mean a Γ Ψ σ x) volume) ∧
      IntegrableOn (fun σ => ∫ x, Ψ (σ, x) * mean a Γ Ψ σ x) (Ioo 0 1) ∧
      rawCost a Γ Ψ = ∫ p, costIntegrand a Γ Ψ p := by
  obtain ⟨hGc, hGs⟩ := costIntegrand_data hΓt hμt hsp ha hΨ
  have hGi : Integrable (costIntegrand a Γ Ψ) (volume.prod volume) := by
    rw [← Measure.volume_eq_prod]; exact hGc.integrable_of_hasCompactSupport hGs
  obtain ⟨B, L, R, -, -, -, -, hR⟩ := ctrl_data hΨ
  refine ⟨fun σ => ?_, (hGi.integral_prod_left).integrableOn, ?_⟩
  · have hc : Continuous fun x => costIntegrand a Γ Ψ (σ, x) := hGc.comp (by fun_prop)
    have hs : HasCompactSupport fun x => costIntegrand a Γ Ψ (σ, x) := by
      refine HasCompactSupport.intro (isCompact_closedBall (0 : Rd d) R) fun z hz => ?_
      rw [mem_closedBall, dist_zero_right, not_le] at hz
      simp [costIntegrand, hR σ z hz]
    exact hc.integrable_of_hasCompactSupport hs
  · rw [rawCost, setIntegral_eq_integral_of_forall_compl_eq_zero, Measure.volume_eq_prod,
      integral_prod _ hGi]
    · rfl
    · intro σ hσ
      simp [VariationalMean.eq_zero_of_time hΨ.2.2.1 hσ]

/-- `v_Ψ > 0`: under the hypotheses of `unmasked_rate`, the variance of every
`Ψ ∈ CPos` is a positive real number.  Lean proof route (not the TeX's, which
identifies `v_Ψ = E W(Ψ)²` and cites `L:compact-raw-profile`): `v_Ψ` is the
integral of the continuous, nonnegative, compactly supported
`Ψ(σ,x) h_σ(x)`, which is positive at a point `(σ₀,x₀)` with
`Ψ(σ₀,x₀) > 0`, because `h_{σ₀}(x₀) ≥ (Γ * Ψ̄)(x₀) > 0`. -/
theorem rawCost_pos {alpha : ℝ} {Γ μ : Measure (Rd d)} (hΓt : IsTempered Γ)
    (hμt : IsTempered μ) (hsp : IsSpectralMeasure Γ μ) [IsLocallyFiniteMeasure Γ]
    (hS : SetScaling alpha Γ) (hΓ : Γ ≠ 0) {a : ℝ} (ha0 : 0 ≤ a) (ha : a < 1)
    {Ψ : ℝ × Rd d → ℝ} (hΨ : Ψ ∈ CPos d) : 0 < rawCost a Γ Ψ := by
  obtain ⟨-, -, he⟩ := rawCost_genuine hΓt hμt hsp ha hΨ
  obtain ⟨hGc, hGs⟩ := costIntegrand_data hΓt hμt hsp ha hΨ
  obtain ⟨hzc, hz0, -, σ₀, x₀, hσ, hpos, hzpos⟩ := psiBar_data hΨ
  have hm : 0 < mean a Γ Ψ σ₀ x₀ :=
    (conv_pos hS hΓ hzc hz0 hzpos (psiBar_conv_integrable hΓt hμt hsp hΨ x₀)).trans_le
      (conv_psiBar_le_mean hΓt hμt hsp hΨ ha0 ha (Ioo_subset_Icc_self hσ) x₀)
  rw [he]
  exact hGc.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := (σ₀, x₀)) hGs
    (fun p => mul_nonneg (hΨ.2.2.2.1 p) (mean_nonneg hΨ a _ _))
    (mul_pos hpos hm).ne'

/-! ### `P:variational-positive-scores` -/

/-- The coefficient-`c` variational value set
`{c I_Ψ - v_Ψ/2 : Ψ ∈ C_pos}` (TeX lines 272-273). -/
def scoreSet (a : ℝ) (Γ : Measure (Rd d)) (c : ℝ) : Set ℝ :=
  (fun Ψ => c * integratedRate a Γ Ψ - rawCost a Γ Ψ / 2) '' CPos d

/-- The coefficient-one set `{I_Ψ - v_Ψ/2 : Ψ ∈ C_pos}` (TeX lines 272-273 at
`c = 1`), whose supremum is `S_1^pos`.  This is the one coefficient-one set of
the package (`SpatialSmoothRatio` and `SpatialStaticControls` use it). -/
def score1Set (a : ℝ) (Γ : Measure (Rd d)) : Set ℝ :=
  (fun Ψ => integratedRate a Γ Ψ - rawCost a Γ Ψ / 2) '' CPos d

/-- The coefficient-`1` value set is the coefficient-one set `score1Set`. -/
theorem scoreSet_one (a : ℝ) (Γ : Measure (Rd d)) : scoreSet a Γ 1 = score1Set a Γ := by
  simp [scoreSet, score1Set]

/-- `E:variational-score-set-scaling` (TeX lines 298-304): with
`k = 3 - α > 0`, `q = 4 - α`, `r_c = c^{1/k}` and `K_c = c^{q/k}`,
`c I_{D_{r_c}Ψ} - v_{D_{r_c}Ψ}/2 = K_c (I_Ψ - v_Ψ/2)` for every continuous
`Ψ` and `c > 0` (an exact identity of the defined quantities, from
`L:variational-control-dilation`). -/
theorem score_set_scaling {alpha : ℝ} {Γ : Measure (Rd d)} (hS : SetScaling alpha Γ)
    (hk : 0 < 3 - alpha) {c : ℝ} (hc : 0 < c) {Ψ : ℝ × Rd d → ℝ} (hΨ : Continuous Ψ)
    (a : ℝ) :
    c * integratedRate a Γ (dil alpha (c ^ (3 - alpha)⁻¹) Ψ) -
        rawCost a Γ (dil alpha (c ^ (3 - alpha)⁻¹) Ψ) / 2 =
      c ^ ((4 - alpha) / (3 - alpha)) * (integratedRate a Γ Ψ - rawCost a Γ Ψ / 2) := by
  have hr : 0 < c ^ (3 - alpha)⁻¹ := Real.rpow_pos_of_pos hc _
  rw [VariationalDilation.integratedRate_dil hS hr hΨ, VariationalDilation.rawCost_dil hS hr hΨ,
    ← Real.rpow_mul hc.le]
  have e1 : c * c ^ (3 - alpha)⁻¹ = c ^ ((4 - alpha) / (3 - alpha)) := by
    rw [← Real.rpow_one_add' hc.le (by positivity)]
    congr 1; field_simp; ring
  have e2 : (3 - alpha)⁻¹ * (4 - alpha) = (4 - alpha) / (3 - alpha) := by
    field_simp
  rw [← mul_assoc, e1, e2]; ring

/-- The whole set identity (TeX lines 305-307): for `c > 0`, the
coefficient-`c` set is `K_c` times the coefficient-one set, because `D_{r_c}`
is a bijection of `C_pos`. -/
theorem scoreSet_eq {alpha : ℝ} {Γ : Measure (Rd d)} (hS : SetScaling alpha Γ)
    (hk : 0 < 3 - alpha) {c : ℝ} (hc : 0 < c) (a : ℝ) :
    scoreSet a Γ c = c ^ ((4 - alpha) / (3 - alpha)) • scoreSet a Γ 1 := by
  have hr : 0 < c ^ (3 - alpha)⁻¹ := Real.rpow_pos_of_pos hc _
  ext y
  constructor
  · rintro ⟨Ψ, hΨ, rfl⟩
    set Φ := dil alpha (1 / c ^ (3 - alpha)⁻¹) Ψ with hΦ
    have hΦm : Φ ∈ CPos d := VariationalDilation.dil_mapsTo alpha (one_div_pos.mpr hr) hΨ
    have hΨΦ : dil alpha (c ^ (3 - alpha)⁻¹) Φ = Ψ := VariationalDilation.dil_dil_inv alpha hr Ψ
    refine ⟨_, ⟨Φ, hΦm, rfl⟩, ?_⟩
    simp only [smul_eq_mul, one_mul]
    rw [← score_set_scaling hS hk hc hΦm.1.continuous, hΨΦ]
  · rintro ⟨_, ⟨Φ, hΦ, rfl⟩, rfl⟩
    refine ⟨dil alpha (c ^ (3 - alpha)⁻¹) Φ, VariationalDilation.dil_mapsTo alpha hr hΦ, ?_⟩
    simp only [smul_eq_mul, one_mul]
    exact score_set_scaling hS hk hc hΦ.1.continuous a

/-- The positive test (TeX lines 290-296): for `Ψ₀` with `I_0 > 0`, `v_0 > 0`
and `r_0 = (I_0/v_0)^{1/k}` (`k = 3 - α > 0`), `D_{r_0}Ψ₀` has variational value
`I - v/2 = r_0 I_0/2 > 0`. -/
theorem positive_test {alpha : ℝ} {Γ : Measure (Rd d)} (hS : SetScaling alpha Γ)
    (hk : 0 < 3 - alpha) {a : ℝ} {Ψ₀ : ℝ × Rd d → ℝ} (hΨ₀ : Ψ₀ ∈ CPos d)
    (hI : 0 < integratedRate a Γ Ψ₀) (hv : 0 < rawCost a Γ Ψ₀) :
    0 < (integratedRate a Γ Ψ₀ / rawCost a Γ Ψ₀) ^ (3 - alpha)⁻¹ ∧
      dil alpha ((integratedRate a Γ Ψ₀ / rawCost a Γ Ψ₀) ^ (3 - alpha)⁻¹) Ψ₀ ∈ CPos d ∧
      integratedRate a Γ (dil alpha ((integratedRate a Γ Ψ₀ / rawCost a Γ Ψ₀) ^ (3 - alpha)⁻¹)
          Ψ₀) -
        rawCost a Γ (dil alpha ((integratedRate a Γ Ψ₀ / rawCost a Γ Ψ₀) ^ (3 - alpha)⁻¹)
          Ψ₀) / 2 =
        (integratedRate a Γ Ψ₀ / rawCost a Γ Ψ₀) ^ (3 - alpha)⁻¹ *
          integratedRate a Γ Ψ₀ / 2 ∧
      0 < (integratedRate a Γ Ψ₀ / rawCost a Γ Ψ₀) ^ (3 - alpha)⁻¹ *
          integratedRate a Γ Ψ₀ / 2 := by
  set I₀ := integratedRate a Γ Ψ₀
  set v₀ := rawCost a Γ Ψ₀
  set r₀ := (I₀ / v₀) ^ (3 - alpha)⁻¹ with hr₀
  have hr : 0 < r₀ := Real.rpow_pos_of_pos (div_pos hI hv) _
  have hrk : r₀ ^ (3 - alpha) = I₀ / v₀ := Real.rpow_inv_rpow (div_pos hI hv).le hk.ne'
  have hrq : r₀ ^ (4 - alpha) = r₀ * (I₀ / v₀) := by
    rw [show (4 : ℝ) - alpha = (3 - alpha) + 1 by ring, Real.rpow_add_one hr.ne', hrk, mul_comm]
  refine ⟨hr, VariationalDilation.dil_mapsTo alpha hr hΨ₀, ?_, by positivity⟩
  rw [VariationalDilation.integratedRate_dil hS hr hΨ₀.1.continuous,
    VariationalDilation.rawCost_dil hS hr hΨ₀.1.continuous, hrq]
  field_simp
  ring

/-- The radius `r_0 = (I_0/v_0)^{1/k}`, `k = 3 - α`, of the positive test
(TeX line 290). -/
def testRadius (alpha a : ℝ) (Γ : Measure (Rd d)) (Ψ₀ : ℝ × Rd d → ℝ) : ℝ :=
  (integratedRate a Γ Ψ₀ / rawCost a Γ Ψ₀) ^ (3 - alpha)⁻¹

/-- The named input `S1Bdd`: the coefficient-one variational value set
`{I_Ψ - v_Ψ/2 : Ψ ∈ C_pos}` is bounded above.  This is word for word the
boundedness claim of `P:variational-positive-scores` for `c = 1`
(`notes/integrated_unmasked_variational.tex` lines 272-274 at a284420).  Its
manuscript proof (lines 309-325) is stochastic: it combines the moment upper
bound of `T:full-upper` (`E|u(T,0)|² ≤ e(T+2)^d e^{C_up T^κ}`) with the point
lower bound `E:variational-unmasked-point-lower` of
`P:variational-remove-mask` for the same canonical solution, so that every
coefficient-two value is at most `Q_2 ≤ C_up`, and then uses
`E:variational-score-set-scaling` at `c = 2`.  Neither ingredient is
formalized, so `S1Bdd` enters only as a hypothesis, and only where the
manuscript's object is the real number `S_1^pos` (its supremum).  Once the
values are genuine (`rawCost_genuine`, `unmasked_rate`: `I_Ψ` and `v_Ψ` are
finite integrals of integrable functions), `S1Bdd` is no stronger than the
manuscript claim it stands for. -/
def S1Bdd (a : ℝ) (Γ : Measure (Rd d)) : Prop :=
  BddAbove (score1Set a Γ)

/-- `S_1^pos = sup {I_Ψ - v_Ψ/2 : Ψ ∈ C_pos}` (TeX line 274 at `c = 1`).  It is
a genuine supremum exactly under `S1Bdd` (the set is nonempty,
`positive_scores`); every statement about it assumes `S1Bdd`. -/
def S1pos (a : ℝ) (Γ : Measure (Rd d)) : ℝ :=
  sSup (score1Set a Γ)

/-- **`P:variational-positive-scores` without `S1Bdd`, general form.**  Under
the hypotheses of `unmasked_rate`, with `k = 3 - α`, `q = 4 - α`: for every
`c` the value set is nonempty; for every `Ψ ∈ C_pos` the rate is integrable on
`(0,1)`, `I_Ψ > 0`, every variance integrand is integrable and `v_Ψ > 0`; the
positive test `D_{r_0}Ψ₀` of every `Ψ₀ ∈ C_pos` has value
`r_0 I_0/2 > 0` (so the coefficient-one set has a positive element);
`E:variational-score-set-scaling` holds for every `c > 0` and `Ψ ∈ C_pos`;
the coefficient-`c` set is `c^{q/k}` times the coefficient-one set; and it is
bounded above exactly when the coefficient-one set is. -/
theorem positive_scores {alpha : ℝ} {Γ μ : Measure (Rd d)} (hΓt : IsTempered Γ)
    (hμt : IsTempered μ) (hsp : IsSpectralMeasure Γ μ) [IsLocallyFiniteMeasure Γ]
    (hS : SetScaling alpha Γ) (hα : alpha < 2) (hΓ : Γ ≠ 0) {a : ℝ} (ha0 : 0 ≤ a)
    (ha : a < 1) :
    (∀ c, (scoreSet a Γ c).Nonempty) ∧
    (∀ Ψ ∈ CPos d, IntegrableOn (rate a Γ Ψ) (Ioo 0 1) ∧ 0 < integratedRate a Γ Ψ ∧
      (∀ σ, Integrable (fun x => Ψ (σ, x) * mean a Γ Ψ σ x) volume) ∧
      IntegrableOn (fun σ => ∫ x, Ψ (σ, x) * mean a Γ Ψ σ x) (Ioo 0 1) ∧
      0 < rawCost a Γ Ψ) ∧
    (∀ Ψ₀ ∈ CPos d, 0 < testRadius alpha a Γ Ψ₀ ∧
      dil alpha (testRadius alpha a Γ Ψ₀) Ψ₀ ∈ CPos d ∧
      integratedRate a Γ (dil alpha (testRadius alpha a Γ Ψ₀) Ψ₀) -
          rawCost a Γ (dil alpha (testRadius alpha a Γ Ψ₀) Ψ₀) / 2 =
        testRadius alpha a Γ Ψ₀ * integratedRate a Γ Ψ₀ / 2 ∧
      0 < testRadius alpha a Γ Ψ₀ * integratedRate a Γ Ψ₀ / 2) ∧
    (∃ y ∈ score1Set a Γ, 0 < y) ∧
    (∀ c, 0 < c → ∀ Ψ ∈ CPos d,
      c * integratedRate a Γ (dil alpha (c ^ (3 - alpha)⁻¹) Ψ) -
          rawCost a Γ (dil alpha (c ^ (3 - alpha)⁻¹) Ψ) / 2 =
        c ^ ((4 - alpha) / (3 - alpha)) * (integratedRate a Γ Ψ - rawCost a Γ Ψ / 2)) ∧
    (∀ c, 0 < c → scoreSet a Γ c = c ^ ((4 - alpha) / (3 - alpha)) • scoreSet a Γ 1) ∧
    (∀ c, 0 < c → (BddAbove (scoreSet a Γ c) ↔ S1Bdd a Γ)) := by
  have hk : 0 < 3 - alpha := by linarith
  have hgen : ∀ Ψ ∈ CPos d, IntegrableOn (rate a Γ Ψ) (Ioo 0 1) ∧ 0 < integratedRate a Γ Ψ ∧
      (∀ σ, Integrable (fun x => Ψ (σ, x) * mean a Γ Ψ σ x) volume) ∧
      IntegrableOn (fun σ => ∫ x, Ψ (σ, x) * mean a Γ Ψ σ x) (Ioo 0 1) ∧
      0 < rawCost a Γ Ψ := by
    intro Ψ hΨ
    obtain ⟨ε, -, -, hε, -, -, -, -, -, -, -, hint, hI, -⟩ :=
      unmasked_rate hΓt hμt hsp hS hα hΓ ha0 ha hΨ
    obtain ⟨h1, h2, -⟩ := rawCost_genuine hΓt hμt hsp ha hΨ
    exact ⟨hint, (Real.sqrt_pos.mpr hε).trans_le hI, h1, h2,
      rawCost_pos hΓt hμt hsp hS hΓ ha0 ha hΨ⟩
  have htest : ∀ Ψ₀ ∈ CPos d, 0 < testRadius alpha a Γ Ψ₀ ∧
      dil alpha (testRadius alpha a Γ Ψ₀) Ψ₀ ∈ CPos d ∧
      integratedRate a Γ (dil alpha (testRadius alpha a Γ Ψ₀) Ψ₀) -
          rawCost a Γ (dil alpha (testRadius alpha a Γ Ψ₀) Ψ₀) / 2 =
        testRadius alpha a Γ Ψ₀ * integratedRate a Γ Ψ₀ / 2 ∧
      0 < testRadius alpha a Γ Ψ₀ * integratedRate a Γ Ψ₀ / 2 := fun Ψ₀ hΨ₀ =>
    positive_test hS hk hΨ₀ (hgen Ψ₀ hΨ₀).2.1 (hgen Ψ₀ hΨ₀).2.2.2.2
  obtain ⟨Ψ₀, hΨ₀⟩ := VariationalDilation.CPos_nonempty d
  obtain ⟨-, hD, hval, hpos⟩ := htest Ψ₀ hΨ₀
  refine ⟨fun c => (VariationalDilation.CPos_nonempty d).image _, hgen, htest,
    ⟨_, ⟨_, hD, rfl⟩, by simp only; rw [hval]; exact hpos⟩,
    fun c hc Ψ hΨ => score_set_scaling hS hk hc hΨ.1.continuous a,
    fun c hc => scoreSet_eq hS hk hc a, fun c hc => ?_⟩
  rw [scoreSet_eq hS hk hc a, bddAbove_smul_iff_of_pos (Real.rpow_pos_of_pos hc _),
    scoreSet_one, S1Bdd]

/-- **`P:variational-positive-scores`, the supremum part, general form, over
the named input `S1Bdd`.**  Under the hypotheses of `unmasked_rate` and
`S1Bdd`, `S_1^pos = sup {I_Ψ - v_Ψ/2 : Ψ ∈ C_pos}` is a positive real number,
and for every `c > 0` the coefficient-`c` set is nonempty and bounded above
with supremum `S_c^pos > 0` and `S_c^pos = c^{(4-α)/(3-α)} S_1^pos`
(`E:variational-score-homogeneity`, first identity). -/
theorem positive_scores_sSup {alpha : ℝ} {Γ μ : Measure (Rd d)} (hΓt : IsTempered Γ)
    (hμt : IsTempered μ) (hsp : IsSpectralMeasure Γ μ) [IsLocallyFiniteMeasure Γ]
    (hS : SetScaling alpha Γ) (hα : alpha < 2) (hΓ : Γ ≠ 0) {a : ℝ} (ha0 : 0 ≤ a)
    (ha : a < 1) (hB : S1Bdd a Γ) :
    0 < S1pos a Γ ∧
    ∀ c, 0 < c → (scoreSet a Γ c).Nonempty ∧ BddAbove (scoreSet a Γ c) ∧
      0 < sSup (scoreSet a Γ c) ∧
      sSup (scoreSet a Γ c) = c ^ ((4 - alpha) / (3 - alpha)) *
        S1pos a Γ := by
  obtain ⟨hne, -, -, ⟨y, hy, hypos⟩, -, hseq, hbdd⟩ :=
    positive_scores hΓt hμt hsp hS hα hΓ ha0 ha
  have hk : 0 < 3 - alpha := by linarith
  have h1 : 0 < S1pos a Γ :=
    hypos.trans_le (le_csSup hB hy)
  refine ⟨h1, fun c hc => ⟨hne c, (hbdd c hc).2 hB, ?_, ?_⟩⟩
  · rw [hseq c hc, Real.sSup_smul_of_nonneg (Real.rpow_pos_of_pos hc _).le, scoreSet_one,
      smul_eq_mul]
    exact mul_pos (Real.rpow_pos_of_pos hc _) h1
  · rw [hseq c hc, Real.sSup_smul_of_nonneg (Real.rpow_pos_of_pos hc _).le, scoreSet_one,
      smul_eq_mul]
    rfl

/-! ### The manuscript's statements -/

/-- Auxiliary to the Lean proof route: `H:homog` gives `α < 2` (from
`α₀ > 0` and `α₀ + α < 2`; the occupation file states this at lines 6-8). -/
theorem alpha_lt_two {alpha alpha0 : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogCovariance d alpha alpha0 Γ μ) : alpha < 2 := by
  linarith [hH.threshold, hH.alpha0_pos]

/-- **`P:variational-unmasked-rate`, Rayleigh-form part** (TeX lines 98-111
at a284420) with the section's standing hypotheses (lines 4-5: a nonzero
covariance satisfying `H:homog`, `a = α₀`) and `Ψ ∈ C_pos`, `I = [0,1]`.
With `λ_{Ψ,s}` DEFINED as the square root of the real Rayleigh supremum
`E:variational-real-rayleigh` (`VariationalDilation.rate`): there are reals
`ε > 0` (the TeX's `ε₀`), `M ≥ ε` and `C ≥ 0` (the `C_Ψ` of
`E:variational-global-mean`) such that, for `s, t ∈ I`: `0 ≤ h_s ≤ M` and
`|h_s(x) - h_t(x)| ≤ C|s - t|`; the Rayleigh value set of `h_s` is nonempty
and bounded above with `ε ≤ λ_s² = sup ≤ M` (uniformly negative bottom
`-M ≤ -λ_s² ≤ -ε` in the TeX's notation `E_s = -λ_s²`);
`|λ_s² - λ_t²| ≤ C|s - t|`; `√ε ≤ λ_s ≤ √M`;
`|λ_s - λ_t| ≤ C/(2√ε) |s - t|` (TeX line 158); `λ` is integrable on
`(0,1)`; and `√ε ≤ I_Ψ ≤ √M`, so `I_Ψ` is positive and finite.

Narrower than the TeX (not formalized, foundation D8): the operator
statements, i.e. that `H_s = -Δ - h_s` is self-adjoint on `H²` with form
domain `H¹`, that its spectral bottom `E_s` satisfies `-E_s = sup R_s`, and
hence the primary definition `λ_{Ψ,s} = √(-E_s)`.  The "no eigenstate"
remark asserts nothing.  Different route: the positive floor `ε` comes from
the dilation floor (`VariationalFloor.dilation_floor`) applied to the lower
envelope `h_s ≥ Γ * Ψ̄` (`Ψ̄ = ∫_0^1 Ψ(u,·) du`, valid because
`|s - u|^{-α₀} ≥ 1` on `[0,1]²`), not from the compact common trial of
`P:compact-original-common-trial` (TeX lines 150-155).  Of `H:homog`, the
fields `Γ_tempered`, `μ_tempered`, `spectral`, `Γ_radon`, `scaling`,
`alpha0_pos`, `alpha0_lt_one`, `threshold` are used; the others are carried,
unused. -/
theorem variational_unmasked_rate_paper {alpha alpha0 : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogCovariance d alpha alpha0 Γ μ) (hΓ0 : Γ ≠ 0) {Ψ : ℝ × Rd d → ℝ}
    (hΨ : Ψ ∈ CPos d) :
    ∃ ε M C : ℝ, 0 < ε ∧ ε ≤ M ∧ 0 ≤ C ∧
      (∀ s ∈ Icc (0 : ℝ) 1, ∀ x, 0 ≤ mean alpha0 Γ Ψ s x ∧ mean alpha0 Γ Ψ s x ≤ M) ∧
      (∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, ∀ x,
        |mean alpha0 Γ Ψ s x - mean alpha0 Γ Ψ t x| ≤ C * |s - t|) ∧
      (∀ s ∈ Icc (0 : ℝ) 1,
        (rayleighSet (mean alpha0 Γ Ψ s)).Nonempty ∧
        BddAbove (rayleighSet (mean alpha0 Γ Ψ s)) ∧
        ε ≤ sSup (rayleighSet (mean alpha0 Γ Ψ s)) ∧
        sSup (rayleighSet (mean alpha0 Γ Ψ s)) ≤ M ∧
        rate alpha0 Γ Ψ s ^ 2 = sSup (rayleighSet (mean alpha0 Γ Ψ s)) ∧
        Real.sqrt ε ≤ rate alpha0 Γ Ψ s ∧ rate alpha0 Γ Ψ s ≤ Real.sqrt M) ∧
      (∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
        |sSup (rayleighSet (mean alpha0 Γ Ψ s)) - sSup (rayleighSet (mean alpha0 Γ Ψ t))| ≤
          C * |s - t|) ∧
      (∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
        |rate alpha0 Γ Ψ s - rate alpha0 Γ Ψ t| ≤ C / (2 * Real.sqrt ε) * |s - t|) ∧
      IntegrableOn (rate alpha0 Γ Ψ) (Ioo 0 1) ∧
      Real.sqrt ε ≤ integratedRate alpha0 Γ Ψ ∧ integratedRate alpha0 Γ Ψ ≤ Real.sqrt M := by
  have := hH.Γ_radon
  exact unmasked_rate hH.Γ_tempered hH.μ_tempered hH.spectral hH.scaling (alpha_lt_two hH) hΓ0
    hH.alpha0_pos.le hH.alpha0_lt_one hΨ

/-- **`P:variational-positive-scores`, input-free part** (TeX lines 270-337 at
a284420, without `S1Bdd`) with the section's standing hypotheses (lines 4-5: a
nonzero covariance satisfying `H:homog`, `a = α₀`); `k = 3 - α`,
`q = 4 - α`.  The value sets `{c I_Ψ - v_Ψ/2 : Ψ ∈ C_pos}` are nonempty; every
value is genuine (for each `Ψ ∈ C_pos`: `λ` integrable on `(0,1)`, every
variance integrand integrable) with `I_Ψ > 0` and `v_Ψ > 0` (deterministically;
the TeX cites `L:compact-raw-profile` for `v_0 > 0`); the positive test of TeX
lines 290-296, `I_{D_{r_0}Ψ₀} - v_{D_{r_0}Ψ₀}/2 = r_0 I_0/2 > 0` with
`r_0 = (I_0/v_0)^{1/k}`, for every `Ψ₀ ∈ C_pos`; the coefficient-one set has
a positive element; `E:variational-score-set-scaling` for every `c > 0`; the
set identity `{c I - v/2} = c^{q/k} {I - v/2}` (lines 305-307); and the
coefficient-`c` set is bounded above iff `S1Bdd` holds.  Not formalized here:
the boundedness itself (`S1Bdd`, stochastic proof, see its doc comment) and
the second identity `Q_2 ≥ S_2^pos` of `E:variational-score-homogeneity`
(it concerns the stochastic point liminf `Q_2`; it needs
`E:variational-unmasked-point-lower`).  `v_Ψ` is the integral form
`VariationalDilation.rawCost` of `E:compact-raw-cost`, not `E W(Ψ)²`. -/
theorem variational_positive_scores_paper {alpha alpha0 : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogCovariance d alpha alpha0 Γ μ) (hΓ0 : Γ ≠ 0) :
    (∀ c, (scoreSet alpha0 Γ c).Nonempty) ∧
    (∀ Ψ ∈ CPos d, IntegrableOn (rate alpha0 Γ Ψ) (Ioo 0 1) ∧ 0 < integratedRate alpha0 Γ Ψ ∧
      (∀ σ, Integrable (fun x => Ψ (σ, x) * mean alpha0 Γ Ψ σ x) volume) ∧
      IntegrableOn (fun σ => ∫ x, Ψ (σ, x) * mean alpha0 Γ Ψ σ x) (Ioo 0 1) ∧
      0 < rawCost alpha0 Γ Ψ) ∧
    (∀ Ψ₀ ∈ CPos d, 0 < testRadius alpha alpha0 Γ Ψ₀ ∧
      dil alpha (testRadius alpha alpha0 Γ Ψ₀) Ψ₀ ∈ CPos d ∧
      integratedRate alpha0 Γ (dil alpha (testRadius alpha alpha0 Γ Ψ₀) Ψ₀) -
          rawCost alpha0 Γ (dil alpha (testRadius alpha alpha0 Γ Ψ₀) Ψ₀) / 2 =
        testRadius alpha alpha0 Γ Ψ₀ * integratedRate alpha0 Γ Ψ₀ / 2 ∧
      0 < testRadius alpha alpha0 Γ Ψ₀ * integratedRate alpha0 Γ Ψ₀ / 2) ∧
    (∃ y ∈ score1Set alpha0 Γ, 0 < y) ∧
    (∀ c, 0 < c → ∀ Ψ ∈ CPos d,
      c * integratedRate alpha0 Γ (dil alpha (c ^ (3 - alpha)⁻¹) Ψ) -
          rawCost alpha0 Γ (dil alpha (c ^ (3 - alpha)⁻¹) Ψ) / 2 =
        c ^ ((4 - alpha) / (3 - alpha)) *
          (integratedRate alpha0 Γ Ψ - rawCost alpha0 Γ Ψ / 2)) ∧
    (∀ c, 0 < c →
      scoreSet alpha0 Γ c = c ^ ((4 - alpha) / (3 - alpha)) • scoreSet alpha0 Γ 1) ∧
    (∀ c, 0 < c → (BddAbove (scoreSet alpha0 Γ c) ↔ S1Bdd alpha0 Γ)) := by
  have := hH.Γ_radon
  exact positive_scores hH.Γ_tempered hH.μ_tempered hH.spectral hH.scaling (alpha_lt_two hH)
    hΓ0 hH.alpha0_pos.le hH.alpha0_lt_one

/-- **`P:variational-positive-scores`, supremum part, over the named input
`S1Bdd`** (TeX lines 272-277 and 327-332 at a284420) with the section's
standing hypotheses (nonzero covariance satisfying `H:homog`, `a = α₀`):
given `S1Bdd` (the boundedness claim of lines 272-274 for `c = 1`; its
manuscript proof at lines 309-325 goes through `T:full-upper` and
`E:variational-unmasked-point-lower`, see `S1Bdd`), the supremum
`S_1^pos` is a positive real, and for every `c > 0` the value set is nonempty
and bounded above with positive supremum `S_c^pos = c^{(4-α)/(3-α)} S_1^pos`
(first identity of `E:variational-score-homogeneity`).  Narrower: the second
identity `Q_2 ≥ S_2^pos` is not formalized. -/
theorem variational_positive_scores_sSup_paper {alpha alpha0 : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogCovariance d alpha alpha0 Γ μ) (hΓ0 : Γ ≠ 0) (hB : S1Bdd alpha0 Γ) :
    0 < S1pos alpha0 Γ ∧
    ∀ c, 0 < c → (scoreSet alpha0 Γ c).Nonempty ∧ BddAbove (scoreSet alpha0 Γ c) ∧
      0 < sSup (scoreSet alpha0 Γ c) ∧
      sSup (scoreSet alpha0 Γ c) = c ^ ((4 - alpha) / (3 - alpha)) *
        S1pos alpha0 Γ := by
  have := hH.Γ_radon
  exact positive_scores_sSup hH.Γ_tempered hH.μ_tempered hH.spectral hH.scaling
    (alpha_lt_two hH) hΓ0 hH.alpha0_pos.le hH.alpha0_lt_one hB

end StratonovichHAMSecondMoment.VariationalRate
