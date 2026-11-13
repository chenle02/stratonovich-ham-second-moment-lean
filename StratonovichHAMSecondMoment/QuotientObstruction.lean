module

/-
Copyright 2026 Le Chen. SPDX-License-Identifier: Apache-2.0

`P:masked-quotient-obstruction` (A physical mask need not preserve noise-null
tests) of `notes/integrated_covariance_foundation.tex` (revision a284420;
statement lines 257-263, proof lines 265-292).

Formalized:
* `masked_quotient_obstruction_paper`, with the manuscript's hypotheses `d = 2`,
  `α = 1`, `0 < a < 1` (`a = α₀`), `Γ = δ₀(dx₁) dx₂` (`Gamma0`) and the section's
  `T > 0`: (i) `Γ` with `μ = (2π)^{-1} dξ₁ δ₀(dξ₂)` (`mu0`) satisfies
  `H:homog` (`HomogHypothesis.HomogCovariance 2 1 a Gamma0 mu0`, TeX lines
  266-270), and `Γ ≠ 0` (the section's standing assumption, lines 5-6);
  (ii) there is a real compact smooth `ζ : ℝ² → ℝ` such that no real
  `C` satisfies `E W(ζF)² ≤ C E W(F)²` for every real compact smooth test `F`
  with time support in `(0,T)` (`IsTest T F`).
* `masked_quotient_obstruction`: the proof's computation with explicit witnesses:
  `ζ = χ ⊗ χ` (`zeta`), `g = χ ⊗ χ''` (`gtest`), a nonnegative nonzero bump `τ`
  supported in `(0,T)`; integrability of the temporal integrand and of both spatial
  integrands, `‖τ‖_a² > 0`, `V(g) = 0`, `V(ζg) = J_χ I_χ²`, `E W(τ⊗g)² = 0` and
  `E W(ζ·(τ⊗g))² = ‖τ‖_a² J_χ I_χ² > 0`.
* TeX steps: `homogCovariance_Gamma0` (with `spectral_Gamma0`, the Fourier
  inversion of lines 266-267, and `posDef_Gamma0`, line 268), `spatialCov_Gamma0`
  (`V(g)` as the spatial covariance, lines 270-274), `integral_chi2` (line 284),
  `integral_chi_mul_chi2` (integration by parts, lines 284-285), `Ichi_pos`,
  `Jchi_pos` (lines 281-283), `covW_tensor` and `timeQ_pos` (lines 286-290).

Definitional boundary (D1).  The noise `W` is not constructed.  `E W(F)²` is
read as the covariance functional of `E:cov` (main TeX
`notes/notes_stratonovich_ham_second_moment.tex`, a284420, lines 219-222):
`covW a Γ F = ∫∫ |t-s|^{-a} ∫ Γ(dz) ∫ F(t,x) F(s,x-z) dx dt ds`, an iterated
Bochner integral with time integrals over `ℝ` (equal to `[0,T]²` for the tests
used).  The theorems prove integrability of the integrands they evaluate, so the
values `0` and `> 0` are not junk values.

Supplied inputs: none (the fallback of the wave plan, `H:homog` membership as a
named input, was not needed).

Implicit hypotheses made explicit: "compact smooth test" is `IsTest T F`
(`C^∞` jointly in `(t,x)`, compact support, time support in `(0,T)`); restricting
the class of tests makes the nonexistence of `C` stronger than over all compact
smooth tests.  "Real" mask: `ζ` is real-valued.  `C` ranges over all reals.

Differences from the TeX.  The bump `χ` is Mathlib's `ContDiffBump` with radii
`1`, `2` (the TeX's explicit formula, lines 276-279, is introduced "for example");
evenness of `χ` and `J_χ ≥ 2` are not used.  `V(g)` is identified with the spatial
covariance through the substitution `x = y + t e₂` and Fubini on `ℝ × ℝ²`
(`autocorr_e2`, auxiliary), for continuous compactly supported `g`.  Positive
definiteness of `Γ` is proved directly (`∫Γ(dz) φ⋆φ̃(z) = ∫ |∫ φ(u,v) dv|² du`),
not via the spectral measure.  The spectral identity is proved by 1-D Fourier
inversion (`Integrable.fourierInv_fourier_eq`) for the marginal
`Φ(u) = ∫ φ(u,v) dv`, whose Fourier transform is the restriction of the
2-D Fourier transform of `φ` to the first axis; the Schwartz decay of that
restriction gives the integrability inversion needs.
-/

public import Mathlib
public import StratonovichHAMSecondMoment.HomogHypothesis
public import StratonovichHAMSecondMoment.TimeSchur

@[expose] public section

noncomputable section

set_option autoImplicit false

open MeasureTheory Set Real Metric
open scoped ContDiff ENNReal Pointwise FourierTransform

namespace StratonovichHAMSecondMoment.QuotientObstruction

open HomogHypothesis

/-! ### Coordinates on `ℝ²` -/

/-- Auxiliary: the point `(u, v)` of `ℝ² = EuclideanSpace ℝ (Fin 2)`. -/
def plane (p : ℝ × ℝ) : Rd 2 := WithLp.toLp 2 ![p.1, p.2]

/-- Auxiliary. -/
@[simp] theorem plane_apply_zero (p : ℝ × ℝ) : plane p 0 = p.1 := rfl

/-- Auxiliary. -/
@[simp] theorem plane_apply_one (p : ℝ × ℝ) : plane p 1 = p.2 := rfl

/-- Auxiliary: `plane` is volume preserving from `ℝ × ℝ` to `ℝ²`. -/
theorem measurePreserving_plane :
    MeasurePreserving plane (volume : Measure (ℝ × ℝ)) (volume : Measure (Rd 2)) := by
  have h := (PiLp.volume_preserving_toLp (Fin 2)).comp
    (volume_preserving_finTwoArrow ℝ).symm
  convert h using 1
  funext p
  ext i; fin_cases i <;> rfl

/-- Auxiliary: `plane` is a measurable embedding. -/
theorem measurableEmbedding_plane : MeasurableEmbedding plane := by
  have h : plane = (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)) ∘
      (MeasurableEquiv.finTwoArrow (α := ℝ)).symm := by
    funext p; rfl
  rw [h]
  exact (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).measurableEmbedding.comp
    (MeasurableEquiv.finTwoArrow (α := ℝ)).symm.measurableEmbedding

/-- Auxiliary: integrals over `ℝ²` in the coordinates `(u, v)`. -/
theorem integral_plane {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : Rd 2 → E) :
    ∫ x, f x = ∫ p : ℝ × ℝ, f (plane p) :=
  (measurePreserving_plane.integral_comp measurableEmbedding_plane f).symm

/-- Auxiliary: integrability over `ℝ²` in the coordinates `(u, v)`. -/
theorem integrable_plane_iff {E : Type*} [NormedAddCommGroup E] {f : Rd 2 → E} :
    Integrable (fun p : ℝ × ℝ => f (plane p)) ↔ Integrable f :=
  measurePreserving_plane.integrable_comp_emb measurableEmbedding_plane

/-- Auxiliary: `plane` is linear in its argument. -/
theorem plane_add (p q : ℝ × ℝ) : plane (p + q) = plane p + plane q := by
  ext i; fin_cases i <;> rfl

/-- Auxiliary. -/
theorem plane_smul (c : ℝ) (p : ℝ × ℝ) : plane (c • p) = c • plane p := by
  ext i; fin_cases i <;> rfl

/-- Auxiliary. -/
theorem plane_neg (p : ℝ × ℝ) : plane (-p) = -plane p := by
  ext i; fin_cases i <;> rfl

/-- Auxiliary: each coordinate is bounded by the norm. -/
theorem abs_fst_le_norm_plane (p : ℝ × ℝ) : |p.1| ≤ ‖plane p‖ := by
  have := PiLp.norm_apply_le (plane p) 0
  simpa using this

/-- Auxiliary. -/
theorem abs_snd_le_norm_plane (p : ℝ × ℝ) : |p.2| ≤ ‖plane p‖ := by
  have := PiLp.norm_apply_le (plane p) 1
  simpa using this

/-- The first unit vector `e₁ = (1, 0)`. -/
def e1 : Rd 2 := plane (1, 0)

/-- The second unit vector `e₂ = (0, 1)`. -/
def e2 : Rd 2 := plane (0, 1)

/-- Auxiliary. -/
theorem smul_e1 (t : ℝ) : t • e1 = plane (t, 0) := by
  rw [e1, ← plane_smul]; simp

/-- Auxiliary. -/
theorem smul_e2 (t : ℝ) : t • e2 = plane (0, t) := by
  rw [e2, ← plane_smul]; simp

/-- Auxiliary: `⟪s e₁, x⟫ = s x₁`. -/
theorem inner_smul_e1 (s : ℝ) (x : Rd 2) : inner ℝ (s • e1) x = s * x 0 := by
  rw [smul_e1]
  simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_two, plane, mul_comm]

/-- Auxiliary. -/
theorem norm_e1 : ‖e1‖ = 1 := by
  rw [e1, EuclideanSpace.norm_eq]; simp [plane, Fin.sum_univ_two]

/-- Auxiliary. -/
theorem norm_e2 : ‖e2‖ = 1 := by
  rw [e2, EuclideanSpace.norm_eq]; simp [plane, Fin.sum_univ_two]

/-- Auxiliary: `plane (u, v) = u e₁ + v e₂`. -/
theorem plane_eq (p : ℝ × ℝ) : plane p = p.1 • e1 + p.2 • e2 := by
  rw [smul_e1, smul_e2, ← plane_add]; simp

/-- Auxiliary. -/
theorem continuous_plane : Continuous plane := by
  have : plane = fun p : ℝ × ℝ => p.1 • e1 + p.2 • e2 := funext plane_eq
  rw [this]; fun_prop

/-! ### Lebesgue measure on a line -/

/-- The pushforward of Lebesgue measure on `ℝ` under `t ↦ t v`.  For the unit
vector `v = e₂` of `ℝ²` this is the manuscript's `Γ = δ₀(dx₁) dx₂`. -/
def lineMeasure {d : ℕ} (v : Rd d) : Measure (Rd d) :=
  Measure.map (fun t : ℝ => t • v) volume

/-- Auxiliary: `t ↦ t v` is an isometry for a unit vector `v`. -/
theorem isometry_smul_unit {d : ℕ} {v : Rd d} (hv : ‖v‖ = 1) :
    Isometry (fun t : ℝ => t • v) :=
  Isometry.of_dist_eq fun (s t : ℝ) => by
    rw [dist_eq_norm, ← sub_smul, norm_smul, hv, mul_one, Real.dist_eq, Real.norm_eq_abs]

/-- Auxiliary. -/
theorem measurableEmbedding_line {d : ℕ} {v : Rd d} (hv : ‖v‖ = 1) :
    MeasurableEmbedding (fun t : ℝ => t • v) :=
  (isometry_smul_unit hv).isClosedEmbedding.measurableEmbedding

/-- Auxiliary: integrals against `lineMeasure v`. -/
theorem integral_lineMeasure {d : ℕ} {v : Rd d} (hv : ‖v‖ = 1) {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (f : Rd d → E) :
    ∫ x, f x ∂lineMeasure v = ∫ t : ℝ, f (t • v) :=
  (measurableEmbedding_line hv).integral_map f

/-- Auxiliary: integrability against `lineMeasure v`. -/
theorem integrable_lineMeasure_iff {d : ℕ} {v : Rd d} (hv : ‖v‖ = 1) {E : Type*}
    [NormedAddCommGroup E] {f : Rd d → E} :
    Integrable f (lineMeasure v) ↔ Integrable (fun t : ℝ => f (t • v)) :=
  (measurableEmbedding_line hv).integrable_map_iff

/-- Auxiliary. -/
theorem lintegral_lineMeasure {d : ℕ} {v : Rd d} (hv : ‖v‖ = 1) (f : Rd d → ℝ≥0∞) :
    ∫⁻ x, f x ∂lineMeasure v = ∫⁻ t : ℝ, f (t • v) :=
  (measurableEmbedding_line hv).lintegral_map f

/-- Auxiliary. -/
theorem lineMeasure_apply {d : ℕ} {v : Rd d} (hv : ‖v‖ = 1) (A : Set (Rd d)) :
    lineMeasure v A = volume ((fun t : ℝ => t • v) ⁻¹' A) :=
  (measurableEmbedding_line hv).map_apply _ _

/-- Auxiliary: `lineMeasure v` is a Radon (locally finite) measure. -/
theorem isLocallyFiniteMeasure_lineMeasure {d : ℕ} {v : Rd d} (hv : ‖v‖ = 1) :
    IsLocallyFiniteMeasure (lineMeasure v) := by
  have : IsFiniteMeasureOnCompacts (lineMeasure v) := ⟨fun K hK => by
    rw [lineMeasure_apply hv]
    exact ((isometry_smul_unit hv).isClosedEmbedding.isCompact_preimage hK).measure_lt_top⟩
  infer_instance

/-- Auxiliary: `lineMeasure v` is even. -/
theorem isEven_lineMeasure {d : ℕ} (v : Rd d) : IsEven (lineMeasure v) := by
  unfold IsEven lineMeasure
  have hm : Measurable (fun t : ℝ => t • v) := by fun_prop
  rw [Measure.map_map measurable_neg hm]
  have : (fun x : Rd d => -x) ∘ (fun t : ℝ => t • v) = (fun t : ℝ => t • v) ∘ (fun t => -t) := by
    funext t; simp [neg_smul]
  rw [this, ← Measure.map_map hm measurable_neg,
    Measure.map_neg_eq_self]

/-- Auxiliary: `lineMeasure v` is tempered (with `k = 2`). -/
theorem isTempered_lineMeasure {d : ℕ} {v : Rd d} (hv : ‖v‖ = 1) :
    IsTempered (lineMeasure v) := by
  refine ⟨2, ?_⟩
  rw [lintegral_lineMeasure hv]
  simp only [norm_smul, hv, mul_one]
  have h := integrable_one_add_norm (E := ℝ) (μ := volume) (r := 2) (by simp)
  simpa using h.lintegral_lt_top

/-- Auxiliary: the scaling `Λ(cA) = c Λ(A)` of a line measure, for `c > 0` and
every set `A`. -/
theorem lineMeasure_smul_set {d : ℕ} {v : Rd d} (hv : ‖v‖ = 1) (A : Set (Rd d)) {c : ℝ}
    (hc : 0 < c) : lineMeasure v (c • A) = ENNReal.ofReal c * lineMeasure v A := by
  rw [lineMeasure_apply hv, lineMeasure_apply hv]
  have hpre : (fun t : ℝ => t • v) ⁻¹' (c • A) = c • ((fun t : ℝ => t • v) ⁻¹' A) := by
    ext t
    simp only [mem_preimage, mem_smul_set_iff_inv_smul_mem₀ hc.ne', smul_smul, smul_eq_mul]
  rw [hpre, Measure.addHaar_smul, Module.finrank_self, pow_one, abs_of_pos hc]

/-! ### Autocorrelation along the second axis -/

/-- Auxiliary weight `w(r) = (1 + |r|)^{-2}`, integrable on `ℝ`. -/
def wt (r : ℝ) : ℝ := ((1 + |r|) ^ 2)⁻¹

/-- Auxiliary. -/
theorem wt_pos (r : ℝ) : 0 < wt r := by
  unfold wt
  have : 0 < 1 + |r| := by linarith [abs_nonneg r]
  positivity

/-- Auxiliary. -/
theorem wt_le_one (r : ℝ) : wt r ≤ 1 := by
  unfold wt
  exact inv_le_one_of_one_le₀ (one_le_pow₀ (by linarith [abs_nonneg r]))

/-- Auxiliary. -/
theorem continuous_wt : Continuous wt := by
  unfold wt
  exact Continuous.inv₀ (by fun_prop) fun r =>
    (pow_pos (show (0 : ℝ) < 1 + |r| by linarith [abs_nonneg r]) 2).ne'

/-- Auxiliary. -/
theorem integrable_wt : Integrable wt := by
  have h := integrable_one_add_norm (E := ℝ) (μ := volume) (r := 2) (by simp)
  refine h.congr (Filter.Eventually.of_forall fun r => ?_)
  simp only [wt, Real.norm_eq_abs]
  rw [Real.rpow_neg (by positivity), Real.rpow_two]

/-- Auxiliary: a function on `ℝ²` with product decay
`‖f(u,v)‖ ≤ C (1+|u|)^{-2} (1+|v|)^{-2}`. -/
def PlaneDecay {𝕜 : Type*} [RCLike 𝕜] (f : Rd 2 → 𝕜) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ p : ℝ × ℝ, ‖f (plane p)‖ ≤ C * (wt p.1 * wt p.2)

/-- Auxiliary: functions with product decay are integrable on `ℝ²`. -/
theorem PlaneDecay.integrable {𝕜 : Type*} [RCLike 𝕜] {f : Rd 2 → 𝕜} (hc : Continuous f)
    (hf : PlaneDecay f) : Integrable f := by
  obtain ⟨C, _, hC⟩ := hf
  rw [← integrable_plane_iff]
  refine ((integrable_wt.mul_prod integrable_wt).const_mul C).mono'
    (hc.comp continuous_plane).aestronglyMeasurable (Filter.Eventually.of_forall fun p => ?_)
  exact hC p

/-- Auxiliary: the marginal `Φ(u) = ∫ f(u, v) dv`. -/
def marg {𝕜 : Type*} [RCLike 𝕜] (f : Rd 2 → 𝕜) (u : ℝ) : 𝕜 := ∫ v, f (plane (u, v))

/-- Auxiliary: the integrand `f(u, v + t) conj f(u, v)` on `ℝ × ℝ²`. -/
def autoInt {𝕜 : Type*} [RCLike 𝕜] (f : Rd 2 → 𝕜) (q : ℝ × (ℝ × ℝ)) : 𝕜 :=
  f (plane (q.2.1, q.2.2 + q.1)) * (starRingEnd 𝕜) (f (plane q.2))

/-- Auxiliary: integrability of `autoInt` for continuous functions with product
decay. -/
theorem integrable_autoInt {𝕜 : Type*} [RCLike 𝕜] {f : Rd 2 → 𝕜} (hc : Continuous f)
    (hf : PlaneDecay f) : Integrable (autoInt f) := by
  obtain ⟨C, hC0, hC⟩ := hf
  set G : ℝ × (ℝ × ℝ) → ℝ := fun q => C * C * (wt (q.2.2 + q.1) * (wt q.2.1 * wt q.2.2))
  have hGm : AEStronglyMeasurable G (volume : Measure (ℝ × (ℝ × ℝ))) := by
    have := continuous_wt
    exact (by fun_prop : Continuous G).aestronglyMeasurable
  have hG : Integrable G := by
    rw [Measure.volume_eq_prod] at hGm ⊢
    rw [integrable_prod_iff' hGm]
    refine ⟨Filter.Eventually.of_forall fun q => ?_, ?_⟩
    · show Integrable (fun t => C * C * (wt (q.2 + t) * (wt q.1 * wt q.2)))
      exact ((integrable_wt.comp_add_left q.2).mul_const _).const_mul _
    · have heq : ∀ q : ℝ × ℝ, ∫ t, ‖G (t, q)‖ =
          C * C * (∫ t, wt t) * (wt q.1 * wt q.2) := by
        intro q
        have h1 : ∀ t, ‖G (t, q)‖ = C * C * (wt (q.2 + t) * (wt q.1 * wt q.2)) := by
          intro t
          rw [Real.norm_of_nonneg]
          have := wt_pos (q.2 + t); have := wt_pos q.1; have := wt_pos q.2
          positivity
        simp_rw [h1]
        rw [integral_const_mul, integral_mul_const,
          integral_add_left_eq_self (fun t => wt t) q.2]
        ring
      simp_rw [heq]
      exact (integrable_wt.mul_prod integrable_wt).const_mul _
  refine hG.mono' ?_ (Filter.Eventually.of_forall fun q => ?_)
  · unfold autoInt
    have h1 : Continuous fun q : ℝ × (ℝ × ℝ) => (q.2.1, q.2.2 + q.1) := by fun_prop
    exact ((hc.comp (continuous_plane.comp h1)).mul (RCLike.continuous_conj.comp
      (hc.comp (continuous_plane.comp continuous_snd)))).aestronglyMeasurable
  · unfold autoInt
    rw [norm_mul, RCLike.norm_conj]
    have h1 := hC (q.2.1, q.2.2 + q.1)
    have h2 := hC q.2
    have h3 : C * (wt q.2.1 * wt (q.2.2 + q.1)) ≤ C * wt (q.2.2 + q.1) := by
      have := wt_le_one q.2.1; have := wt_pos (q.2.2 + q.1)
      exact mul_le_mul_of_nonneg_left (by nlinarith) hC0
    calc ‖f (plane (q.2.1, q.2.2 + q.1))‖ * ‖f (plane q.2)‖
        ≤ (C * wt (q.2.2 + q.1)) * (C * (wt q.2.1 * wt q.2.2)) :=
          mul_le_mul (h1.trans h3) h2 (norm_nonneg _)
            (mul_nonneg hC0 (le_of_lt (wt_pos _)))
      _ = G q := by simp only [G]; ring

/-- Auxiliary: translating by `t e₂` in the coordinates `(u, v)`. -/
theorem integral_shift_e2 {𝕜 : Type*} [RCLike 𝕜] (f : Rd 2 → 𝕜) (t : ℝ) :
    ∫ y, f (y + t • e2) * (starRingEnd 𝕜) (f y) = ∫ q : ℝ × ℝ, autoInt f (t, q) := by
  rw [integral_plane]
  refine integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
  simp only [autoInt, smul_e2, ← plane_add]
  have : q + (0, t) = (q.1, q.2 + t) := by ext <;> simp
  rw [this]

/-- Auxiliary (the computation behind TeX lines 270-274 and the positive
definiteness of `Γ`, line 268): for continuous `f` with product decay, the autocorrelation
along `e₂`, integrated over the shift, is the `L²` norm of the marginal:
`∫_ℝ ∫_{ℝ²} f(y + t e₂) conj f(y) dy dt = ∫_ℝ |∫_ℝ f(u,v) dv|² du`, with the
outer integrand integrable in `t` and each inner integrand integrable in `y`. -/
theorem autocorr_e2 {𝕜 : Type*} [RCLike 𝕜] {f : Rd 2 → 𝕜} (hc : Continuous f)
    (hf : PlaneDecay f) :
    (∀ t : ℝ, Integrable (fun y => f (y + t • e2) * (starRingEnd 𝕜) (f y))) ∧
      Integrable (fun t : ℝ => ∫ y, f (y + t • e2) * (starRingEnd 𝕜) (f y)) ∧
      ∫ t : ℝ, ∫ y, f (y + t • e2) * (starRingEnd 𝕜) (f y) =
        ((∫ u, ‖marg f u‖ ^ 2 : ℝ) : 𝕜) := by
  have hH := integrable_autoInt hc hf
  have hfi := hf.integrable hc
  obtain ⟨C, hC0, hC⟩ := hf
  refine ⟨fun t => ?_, ?_, ?_⟩
  · have hb : ∀ y : Rd 2, ‖f (y + t • e2)‖ ≤ C := by
      intro y
      set p : ℝ × ℝ := ((y + t • e2) 0, (y + t • e2) 1)
      have hp : y + t • e2 = plane p := by ext i; fin_cases i <;> rfl
      rw [hp]
      have hab : wt p.1 * wt p.2 ≤ 1 :=
        (mul_le_mul (wt_le_one _) (wt_le_one _) (wt_pos _).le zero_le_one).trans_eq (one_mul 1)
      exact (hC p).trans (by simpa using mul_le_mul_of_nonneg_left hab hC0)
    have hfc : Integrable (fun y => (starRingEnd 𝕜) (f y)) :=
      hfi.mono (RCLike.continuous_conj.comp hc).aestronglyMeasurable
        (Filter.Eventually.of_forall fun y => by simp)
    refine Integrable.bdd_mul (c := C) hfc ?_ (Filter.Eventually.of_forall hb)
    exact (hc.comp (continuous_id.add continuous_const)).aestronglyMeasurable
  · simp_rw [integral_shift_e2]
    exact hH.integral_prod_left
  · simp_rw [integral_shift_e2]
    rw [integral_integral_swap (f := fun t q => autoInt f (t, q)) hH]
    have hin : ∀ q : ℝ × ℝ, ∫ t, autoInt f (t, q) =
        marg f q.1 * (starRingEnd 𝕜) (f (plane q)) := by
      intro q
      simp only [autoInt]
      rw [integral_mul_const]
      congr 1
      exact integral_add_left_eq_self (fun t => f (plane (q.1, t))) q.2
    simp_rw [hin]
    have hint : Integrable (fun q : ℝ × ℝ => marg f q.1 * (starRingEnd 𝕜) (f (plane q))) := by
      have := hH.integral_prod_right
      simp_rw [hin] at this
      exact this
    rw [Measure.volume_eq_prod] at hint
    rw [Measure.volume_eq_prod, integral_prod _ hint]
    have hu : ∀ u : ℝ, ∫ v, marg f u * (starRingEnd 𝕜) (f (plane (u, v))) =
        ((‖marg f u‖ ^ 2 : ℝ) : 𝕜) := by
      intro u
      rw [integral_const_mul, integral_conj]
      change marg f u * (starRingEnd 𝕜) (marg f u) = _
      rw [RCLike.mul_conj]
      simp
    simp_rw [hu]
    exact integral_ofReal

/-! ### The covariance `Γ = δ₀(dx₁) dx₂` and its spectral measure -/

/-- The manuscript's `Γ = δ₀(dx₁) dx₂` on `ℝ²` (TeX lines 259-260): Lebesgue measure on the
second coordinate axis. -/
def Gamma0 : Measure (Rd 2) := lineMeasure e2

/-- The manuscript's spectral measure `μ = (2π)^{-1} dξ₁ δ₀(dξ₂)` (TeX lines
266-267): `(2π)^{-1}` times Lebesgue measure on the first coordinate axis. -/
def mu0 : Measure (Rd 2) := ENNReal.ofReal (2 * π)⁻¹ • lineMeasure e1

/-- `Γ = δ₀(dx₁) dx₂` is not the zero measure (the section's standing `Γ ≠ 0`,
TeX lines 5-6, holds for it). -/
theorem Gamma0_ne_zero : Gamma0 ≠ 0 := by
  intro h
  have h1 : Gamma0 univ = (⊤ : ℝ≥0∞) := by
    rw [Gamma0, lineMeasure_apply norm_e2, preimage_univ, Real.volume_univ]
  rw [h, Measure.coe_zero, Pi.zero_apply] at h1
  exact ENNReal.zero_ne_top h1

/-- Auxiliary: Schwartz functions on `ℝ²` have product decay. -/
theorem schwartz_planeDecay (φ : SchwartzMap (Rd 2) ℂ) : PlaneDecay (⇑φ) := by
  set C := 2 ^ 4 * ((Finset.Iic ((4 : ℕ), (0 : ℕ))).sup fun m =>
    SchwartzMap.seminorm ℂ m.1 m.2) φ
  have hb : ∀ x, (1 + ‖x‖) ^ 4 * ‖φ x‖ ≤ C := fun x => by
    have := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ) (m := (4, 0)) le_rfl le_rfl φ x
    rwa [norm_iteratedFDeriv_zero] at this
  have hC0 : 0 ≤ C := (mul_nonneg (by positivity) (norm_nonneg _)).trans (hb 0)
  refine ⟨C, hC0, fun p => ?_⟩
  have hu := abs_fst_le_norm_plane p
  have hv := abs_snd_le_norm_plane p
  have hpos : 0 < (1 + ‖plane p‖) ^ 4 := by positivity
  have h1 : ‖φ (plane p)‖ ≤ C * ((1 + ‖plane p‖) ^ 4)⁻¹ := by
    rw [le_mul_inv_iff₀ hpos, mul_comm]; exact hb _
  refine h1.trans (mul_le_mul_of_nonneg_left ?_ hC0)
  unfold wt
  rw [← mul_inv]
  apply inv_anti₀ (by positivity)
  calc (1 + |p.1|) ^ 2 * (1 + |p.2|) ^ 2 ≤ (1 + ‖plane p‖) ^ 2 * (1 + ‖plane p‖) ^ 2 := by
        gcongr
    _ = (1 + ‖plane p‖) ^ 4 := by ring

/-- `Γ = δ₀(dx₁) dx₂` is positive definite as a distribution (TeX line 268). -/
theorem posDef_Gamma0 : IsPosDefDistr Gamma0 := by
  intro φ
  have h := (autocorr_e2 (𝕜 := ℂ) φ.continuous (schwartz_planeDecay φ)).2.2
  have heq : ∫ x, (∫ y, φ (x + y) * (starRingEnd ℂ) (φ y)) ∂Gamma0 =
      ((∫ u, ‖marg (⇑φ) u‖ ^ 2 : ℝ) : ℂ) := by
    rw [Gamma0, integral_lineMeasure norm_e2]
    refine Eq.trans ?_ h
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [add_comm (t • e2) y]
  rw [heq]
  exact ⟨Complex.ofReal_im _, by
    rw [Complex.ofReal_re]; exact integral_nonneg fun u => by positivity⟩

/-- Auxiliary: restrictions of Schwartz functions to the first axis are integrable. -/
theorem integrable_schwartz_e1 (ψ : SchwartzMap (Rd 2) ℂ) :
    Integrable (fun w : ℝ => ψ (w • e1)) := by
  obtain ⟨C, _, hC⟩ := schwartz_planeDecay ψ
  refine ((integrable_wt.mul_const (wt 0)).const_mul C).mono'
    (ψ.continuous.comp (continuous_id.smul continuous_const)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun w => ?_)
  rw [smul_e1]
  exact hC (w, 0)

/-- The spectral identity of TeX lines 266-267: `μ = (2π)^{-1} dξ₁ δ₀(dξ₂)` is the
spectral measure of `Γ = δ₀(dx₁) dx₂` in the convention of `H:homog`
(`∫ φ dΓ = ∫ (∫ φ(x) e^{iξ·x} dx) μ(dξ)` for every Schwartz `φ`).  Route: Fourier
inversion on `ℝ` (`Integrable.fourierInv_fourier_eq`) for the marginal
`Φ(u) = ∫ φ(u,v) dv`, whose Fourier transform is the restriction of the Fourier
transform of `φ` to the first axis. -/
theorem spectral_Gamma0 : IsSpectralMeasure Gamma0 mu0 := by
  intro φ
  set Φ : ℝ → ℂ := marg (⇑φ) with hΦdef
  obtain ⟨C, hC0, hC⟩ := schwartz_planeDecay φ
  have hφp : Integrable (fun p : ℝ × ℝ => φ (plane p)) := integrable_plane_iff.2 φ.integrable
  have hΦi : Integrable Φ := by
    rw [Measure.volume_eq_prod] at hφp; exact hφp.integral_prod_left
  have hΦc : Continuous Φ := by
    refine continuous_of_dominated (bound := fun v => C * wt v)
      (fun u => (φ.continuous.comp (continuous_plane.comp
        (continuous_const.prodMk continuous_id))).aestronglyMeasurable)
      (fun u => Filter.Eventually.of_forall fun v => (hC (u, v)).trans ?_)
      (integrable_wt.const_mul C)
      (Filter.Eventually.of_forall fun v => φ.continuous.comp (continuous_plane.comp
        (continuous_id.prodMk continuous_const)))
    have := wt_le_one u; have := wt_pos v
    exact mul_le_mul_of_nonneg_left (by nlinarith) hC0
  set ψ := SchwartzMap.fourierTransformCLM ℂ φ
  have hψ : ∀ y, ψ y = 𝓕 (⇑φ) y := fun y => by
    simp only [ψ, SchwartzMap.fourierTransformCLM_apply, SchwartzMap.fourier_coe]
  -- the Fourier transform of the marginal is the restriction to the first axis
  have hFΦ : ∀ w : ℝ, 𝓕 Φ w = ψ (w • e1) := by
    intro w
    rw [hψ, Real.fourier_real_eq_integral_exp_smul, Real.fourier_eq', integral_plane]
    have hip : ∀ p : ℝ × ℝ, -2 * π * inner ℝ (plane p) (w • e1) = -2 * π * p.1 * w := by
      intro p
      rw [real_inner_comm, inner_smul_e1, plane_apply_zero]
      ring
    simp_rw [hip]
    have hint : Integrable (fun p : ℝ × ℝ =>
        Complex.exp (↑(-2 * π * p.1 * w) * Complex.I) • φ (plane p))
        ((volume : Measure ℝ).prod volume) := by
      rw [← Measure.volume_eq_prod]
      refine hφp.bdd_mul (c := 1) ?_ (Filter.Eventually.of_forall fun p => ?_)
      · exact (by fun_prop : Continuous fun p : ℝ × ℝ =>
          Complex.exp (↑(-2 * π * p.1 * w) * Complex.I)).aestronglyMeasurable
      · rw [Complex.norm_exp_ofReal_mul_I]
    rw [Measure.volume_eq_prod, integral_prod _ hint]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    simp only [hΦdef, marg]
    rw [← integral_smul]
  have hFi : Integrable (𝓕 Φ) := by
    have : 𝓕 Φ = fun w => ψ (w • e1) := funext hFΦ
    rw [this]; exact integrable_schwartz_e1 ψ
  have hinv : ∫ w, 𝓕 Φ w = Φ 0 := by
    rw [← hΦi.fourierInv_fourier_eq hFi hΦc.continuousAt, Real.fourierInv_eq]
    simp
  -- the inner integral of the right side
  have hinner : ∀ s : ℝ, ∫ x, φ x * Complex.exp (Complex.I * (inner ℝ (s • e1) x : ℝ)) =
      𝓕 Φ (-(2 * π)⁻¹ * s) := by
    intro s
    rw [hFΦ, hψ, Real.fourier_eq']
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    dsimp only
    rw [smul_eq_mul, mul_comm, inner_smul_e1, real_inner_comm, inner_smul_e1]
    congr 1
    push_cast
    field_simp
  -- assemble
  rw [Gamma0, integral_lineMeasure norm_e2, mu0, integral_smul_measure,
    integral_lineMeasure norm_e1]
  simp_rw [hinner]
  rw [Measure.integral_comp_mul_left (fun w => 𝓕 Φ w), hinv]
  have hlhs : ∫ t : ℝ, φ (t • e2) = Φ 0 := by
    simp only [hΦdef, marg, smul_e2]
  rw [hlhs, ENNReal.toReal_ofReal (by positivity), smul_smul]
  have hpi : (2 * π)⁻¹ * |(-(2 * π)⁻¹)⁻¹| = 1 := by
    rw [inv_neg, inv_inv, abs_neg, abs_of_pos (by positivity)]
    field_simp
  rw [hpi, one_smul]

/-- `Γ = δ₀(dx₁) dx₂` and `μ = (2π)^{-1} dξ₁ δ₀(dξ₂)` satisfy `H:homog` with `d = 2`,
`α = 1` and `α₀ = a` for every `0 < a < 1` (TeX lines 266-270). -/
theorem homogCovariance_Gamma0 {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    HomogCovariance 2 1 a Gamma0 mu0 where
  dim := Or.inr (Or.inl rfl)
  alpha0_pos := ha0
  alpha0_lt_one := ha1
  Γ_radon := isLocallyFiniteMeasure_lineMeasure norm_e2
  Γ_even := isEven_lineMeasure e2
  Γ_tempered := isTempered_lineMeasure norm_e2
  Γ_posdef := posDef_Gamma0
  μ_radon := by
    have := isLocallyFiniteMeasure_lineMeasure norm_e1
    exact Measure.isLocallyFiniteMeasure_smul _ ENNReal.ofReal_ne_top
  μ_even := by
    unfold IsEven mu0
    rw [Measure.map_smul, isEven_lineMeasure e1]
    exact measurable_neg.aemeasurable
  μ_tempered := by
    obtain ⟨k, hk⟩ := isTempered_lineMeasure norm_e1
    exact ⟨k, by
      rw [mu0, lintegral_smul_measure]; exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hk⟩
  spectral := spectral_Gamma0
  scaling := fun A _ c hc => by
    rw [Gamma0, lineMeasure_smul_set norm_e2 A hc]
    norm_num
  threshold := by linarith
  alpha_range := Or.inl ⟨one_pos, by norm_num⟩

/-! ### The covariance functional and its factorization on tensors -/

/-- The noise covariance functional of `E:cov` (main TeX file
`notes/notes_stratonovich_ham_second_moment.tex`, a284420, lines 219-222) read as
`E W(F)² = ∫∫ |t-s|^{-a} ∫ Γ(dz) ∫ F(t,x) F(s,x-z) dx dt ds` for a real test `F`
(a definitional D1 reading; `W` itself is not constructed).  Time integrals run over
`ℝ`; for tests supported in `(0,T)` this is the integral over `[0,T]²`.  An
iterated Bochner integral: it is the manuscript's quantity where the integrands are
integrable, which the theorems below prove for the tests they use. -/
def covW {d : ℕ} (a : ℝ) (Γ : Measure (Rd d)) (F : ℝ → Rd d → ℝ) : ℝ :=
  ∫ t, ∫ s, |t - s| ^ (-a) * ∫ z, (∫ x, F t x * F s (x - z)) ∂Γ

/-- The spatial covariance `∫ Γ(dz) ∫ f(x) g(x-z) dx` (the spatial factor of
`covW`). -/
def spatialCov {d : ℕ} (Γ : Measure (Rd d)) (f g : Rd d → ℝ) : ℝ :=
  ∫ z, (∫ x, f x * g (x - z)) ∂Γ

/-- The temporal factor `‖τ‖_a² = ∫∫ τ(t) τ(s) |t-s|^{-a} dt ds`. -/
def timeQ (a : ℝ) (τ : ℝ → ℝ) : ℝ :=
  ∫ t, ∫ s, τ t * τ s * |t - s| ^ (-a)

/-- The manuscript's `V(g) = ∫_ℝ (∫_ℝ g(x₁, x₂) dx₂)² dx₁` (TeX lines 272-274). -/
def margV (g : Rd 2 → ℝ) : ℝ := ∫ u, (∫ v, g (plane (u, v))) ^ 2

/-- On tensors `F(t,x) = τ(t) g(x)` the covariance functional factors as
`‖τ‖_a² · ∫ Γ(dz) ∫ g(x) g(x-z) dx` (TeX lines 286-290).  No integrability is
needed: constants are pulled out of Bochner integrals. -/
theorem covW_tensor {d : ℕ} (a : ℝ) (Γ : Measure (Rd d)) (τ : ℝ → ℝ) (g : Rd d → ℝ) :
    covW a Γ (fun t x => τ t * g x) = timeQ a τ * spatialCov Γ g g := by
  unfold covW timeQ spatialCov
  have h : ∀ t s : ℝ, ∫ z, (∫ x, τ t * g x * (τ s * g (x - z))) ∂Γ =
      τ t * τ s * ∫ z, (∫ x, g x * g (x - z)) ∂Γ := by
    intro t s
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    dsimp only
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    dsimp only
    ring
  simp_rw [h]
  rw [← integral_mul_const]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  dsimp only
  rw [← integral_mul_const]
  refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
  dsimp only
  ring

/-- Auxiliary: continuous compactly supported functions have product decay. -/
theorem planeDecay_of_hasCompactSupport {g : Rd 2 → ℝ} (hc : Continuous g)
    (hs : HasCompactSupport g) : PlaneDecay g := by
  obtain ⟨M, hM⟩ := hc.bounded_above_of_compact_support hs
  obtain ⟨R, hR⟩ := hs.isCompact.isBounded.subset_closedBall 0
  set R' := max R 0
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  refine ⟨M * (1 + R') ^ 4, by positivity, fun p => ?_⟩
  by_cases hp : g (plane p) = 0
  · rw [hp, norm_zero]
    have := wt_pos p.1; have := wt_pos p.2
    positivity
  have hn : ‖plane p‖ ≤ R' := by
    have := hR (subset_tsupport g hp)
    rw [mem_closedBall, dist_zero_right] at this
    exact this.trans (le_max_left _ _)
  have hw : ∀ r : ℝ, |r| ≤ R' → ((1 + R') ^ 2)⁻¹ ≤ wt r := by
    intro r hr
    unfold wt
    exact inv_anti₀ (by positivity) (by gcongr)
  have h1 := hw _ ((abs_fst_le_norm_plane p).trans hn)
  have h2 := hw _ ((abs_snd_le_norm_plane p).trans hn)
  have hpos : 0 < (1 + R') ^ 2 := by positivity
  calc ‖g (plane p)‖ ≤ M := hM _
    _ = M * (1 + R') ^ 4 * (((1 + R') ^ 2)⁻¹ * ((1 + R') ^ 2)⁻¹) := by
        have h1R : (1 + R') ≠ 0 := by positivity
        field_simp
    _ ≤ M * (1 + R') ^ 4 * (wt p.1 * wt p.2) :=
        mul_le_mul_of_nonneg_left (mul_le_mul h1 h2 (by positivity) (wt_pos _).le)
          (by positivity)

/-- `V(g)` is the spatial covariance for `Γ = δ₀(dx₁) dx₂` (TeX lines 270-274):
for real continuous compactly supported `g`, every inner integrand
`x ↦ g(x) g(x-z)` is integrable, `z ↦ ∫ g(x) g(x-z) dx` is `Γ`-integrable, and
`∫ Γ(dz) ∫ g(x) g(x-z) dx = ∫ (∫ g(x₁,x₂) dx₂)² dx₁`.  Route: the substitution
`x = y + t e₂` and `autocorr_e2` (Fubini on `ℝ × ℝ²`); the TeX says "by ordinary
Fubini". -/
theorem spatialCov_Gamma0 {g : Rd 2 → ℝ} (hc : Continuous g) (hs : HasCompactSupport g) :
    (∀ z, Integrable (fun x => g x * g (x - z))) ∧
      Integrable (fun z => ∫ x, g x * g (x - z)) Gamma0 ∧
      spatialCov Gamma0 g g = margV g := by
  have hd := planeDecay_of_hasCompactSupport hc hs
  obtain ⟨_, hint, heq⟩ := autocorr_e2 (𝕜 := ℝ) hc hd
  have hshift : ∀ t : ℝ, ∫ x, g x * g (x - t • e2) =
      ∫ y, g (y + t • e2) * (starRingEnd ℝ) (g y) := by
    intro t
    rw [← integral_add_right_eq_self (fun x => g x * g (x - t • e2)) (t • e2)]
    simp
  refine ⟨fun z => ?_, ?_, ?_⟩
  · obtain ⟨M, hM⟩ := hc.bounded_above_of_compact_support hs
    have := (hc.integrable_of_hasCompactSupport hs (μ := volume)).mul_bdd (c := M)
      (hc.comp (continuous_id.sub continuous_const)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => hM (x - z))
    exact this
  · rw [Gamma0, integrable_lineMeasure_iff norm_e2]
    simp_rw [hshift]
    exact hint
  · rw [spatialCov, Gamma0, integral_lineMeasure norm_e2]
    simp_rw [hshift]
    rw [heq, margV]
    simp [marg]

/-- Auxiliary: `V(p ⊗ q) = (∫ q)² ∫ p²`. -/
theorem margV_tensor (p q : ℝ → ℝ) :
    margV (fun x => p (x 0) * q (x 1)) = (∫ v, q v) ^ 2 * ∫ u, p u ^ 2 := by
  unfold margV
  simp only [plane_apply_zero, plane_apply_one]
  simp_rw [integral_const_mul, mul_pow]
  rw [integral_mul_const, mul_comm]

/-- Auxiliary: smoothness of tensors `x ↦ p(x₁) q(x₂)`. -/
theorem contDiff_tensor {p q : ℝ → ℝ} (hp : ContDiff ℝ ∞ p) (hq : ContDiff ℝ ∞ q) :
    ContDiff ℝ ∞ (fun x : Rd 2 => p (x 0) * q (x 1)) :=
  (hp.comp (by fun_prop)).mul (hq.comp (by fun_prop))

/-- Auxiliary: `‖x‖ ≤ |x₁| + |x₂|` on `ℝ²`. -/
theorem norm_le_abs_add_abs (x : Rd 2) : ‖x‖ ≤ |x 0| + |x 1| := by
  have hx : x = x 0 • e1 + x 1 • e2 := by
    rw [← plane_eq (x 0, x 1)]; ext i; fin_cases i <;> rfl
  calc ‖x‖ = ‖x 0 • e1 + x 1 • e2‖ := by conv_lhs => rw [hx]
    _ ≤ ‖x 0 • e1‖ + ‖x 1 • e2‖ := norm_add_le _ _
    _ = |x 0| + |x 1| := by rw [norm_smul, norm_smul, norm_e1, norm_e2, Real.norm_eq_abs,
          Real.norm_eq_abs, mul_one, mul_one]

/-- Auxiliary: compact support of tensors `x ↦ p(x₁) q(x₂)`. -/
theorem hasCompactSupport_tensor {p q : ℝ → ℝ} (hp : HasCompactSupport p)
    (hq : HasCompactSupport q) : HasCompactSupport (fun x : Rd 2 => p (x 0) * q (x 1)) := by
  obtain ⟨R₁, h₁⟩ := hp.isCompact.isBounded.subset_closedBall 0
  obtain ⟨R₂, h₂⟩ := hq.isCompact.isBounded.subset_closedBall 0
  refine HasCompactSupport.intro (isCompact_closedBall (0 : Rd 2) (R₁ + R₂)) fun x hx => ?_
  rw [mem_closedBall, dist_zero_right, not_le] at hx
  by_cases h0 : x 0 ∈ tsupport p
  · by_cases h1 : x 1 ∈ tsupport q
    · exfalso
      have a1 := h₁ h0; have a2 := h₂ h1
      rw [mem_closedBall, dist_zero_right, Real.norm_eq_abs] at a1 a2
      linarith [norm_le_abs_add_abs x]
    · rw [image_eq_zero_of_notMem_tsupport h1, mul_zero]
  · rw [image_eq_zero_of_notMem_tsupport h0, zero_mul]

/-! ### The bump `χ` and the integrals `I_χ`, `J_χ` -/

/-- Auxiliary: the smooth bump on `ℝ` equal to one on `[-1,1]` and zero outside
`(-2,2)` (Mathlib's `ContDiffBump`; the TeX's explicit formula, lines 276-279, is given
"for example"). -/
def chiBump : ContDiffBump (0 : ℝ) := ⟨1, 2, one_pos, one_lt_two⟩

/-- The manuscript's `χ` (TeX lines 275-279): smooth, compactly supported,
nonnegative, `χ = 1` on `[-1,1]`. -/
def chi (x : ℝ) : ℝ := chiBump x

/-- `χ''`. -/
def chi2 (x : ℝ) : ℝ := deriv (deriv chi) x

/-- Auxiliary. -/
theorem contDiff_chi : ContDiff ℝ ∞ chi := chiBump.contDiff

/-- Auxiliary. -/
theorem hasCompactSupport_chi : HasCompactSupport chi := chiBump.hasCompactSupport

/-- Auxiliary. -/
theorem chi_zero : chi 0 = 1 := chiBump.one_of_mem_closedBall (by simp [chiBump])

/-- Auxiliary. -/
theorem chi_three : chi 3 = 0 :=
  chiBump.zero_of_le_dist (by simp [chiBump]; norm_num)

/-- Auxiliary. -/
theorem contDiff_deriv_chi : ContDiff ℝ ∞ (deriv chi) :=
  (contDiff_infty_iff_deriv.1 contDiff_chi).2

/-- Auxiliary. -/
theorem contDiff_chi2 : ContDiff ℝ ∞ chi2 :=
  (contDiff_infty_iff_deriv.1 contDiff_deriv_chi).2

/-- Auxiliary. -/
theorem hasCompactSupport_chi2 : HasCompactSupport chi2 :=
  hasCompactSupport_chi.deriv.deriv

/-- `∫ χ'' = 0` (TeX line 284). -/
theorem integral_chi2 : ∫ x, chi2 x = 0 := by
  refine integral_eq_zero_of_hasDerivAt_of_integrable (f := deriv chi)
    (fun x => ((contDiff_deriv_chi.differentiable (by simp)) x).hasDerivAt) ?_ ?_
  · exact contDiff_chi2.continuous.integrable_of_hasCompactSupport hasCompactSupport_chi2
  · exact contDiff_deriv_chi.continuous.integrable_of_hasCompactSupport
      hasCompactSupport_chi.deriv

/-- Auxiliary: `χ` and its products vanish eventually at `±∞`. -/
theorem tendsto_zero_of_hasCompactSupport {f : ℝ → ℝ} (hf : HasCompactSupport f) :
    Filter.Tendsto f Filter.atBot (nhds 0) ∧ Filter.Tendsto f Filter.atTop (nhds 0) := by
  obtain ⟨R, hR⟩ := hf.isCompact.isBounded.subset_closedBall 0
  have hz : ∀ x, R < |x| → f x = 0 := fun x hx => by
    refine image_eq_zero_of_notMem_tsupport fun hm => ?_
    have := hR hm
    rw [mem_closedBall, Real.dist_eq, sub_zero] at this
    linarith
  constructor
  · refine tendsto_nhds_of_eventually_eq ?_
    filter_upwards [Filter.eventually_lt_atBot (-R - 1)] with x hx
    exact hz x (lt_of_lt_of_le (by linarith) (neg_le_abs x))
  · refine tendsto_nhds_of_eventually_eq ?_
    filter_upwards [Filter.eventually_gt_atTop (|R| + 1)] with x hx
    exact hz x (by rw [abs_of_pos (by linarith [abs_nonneg R])]; linarith [le_abs_self R])

/-- `I_χ = ∫ (χ')²`. -/
def Ichi : ℝ := ∫ x, deriv chi x ^ 2

/-- `J_χ = ∫ χ⁴`. -/
def Jchi : ℝ := ∫ x, chi x ^ 4

/-- Integration by parts: `∫ χ χ'' = -I_χ` (TeX lines 284-285). -/
theorem integral_chi_mul_chi2 : ∫ x, chi x * chi2 x = -Ichi := by
  have hd : Differentiable ℝ chi := contDiff_chi.differentiable (by simp)
  have hd' : Differentiable ℝ (deriv chi) := contDiff_deriv_chi.differentiable (by simp)
  have hcs : HasCompactSupport (chi * deriv chi) :=
    hasCompactSupport_chi.mul_right
  obtain ⟨hb, ht⟩ := tendsto_zero_of_hasCompactSupport hcs
  have h := integral_mul_deriv_eq_deriv_mul (u := chi) (v := deriv chi) (u' := deriv chi)
    (v' := chi2) (fun x _ => (hd x).hasDerivAt) (fun x _ => (hd' x).hasDerivAt)
    ((contDiff_chi.continuous.mul contDiff_chi2.continuous).integrable_of_hasCompactSupport
      hasCompactSupport_chi.mul_right)
    ((contDiff_deriv_chi.continuous.mul
      contDiff_deriv_chi.continuous).integrable_of_hasCompactSupport
        hasCompactSupport_chi.deriv.mul_right) hb ht
  rw [h, Ichi]
  simp [sq]

/-- `I_χ > 0` (TeX lines 281-282: `χ` is not constant). -/
theorem Ichi_pos : 0 < Ichi := by
  obtain ⟨x, hx⟩ : ∃ x, deriv chi x ≠ 0 := by
    by_contra h
    push Not at h
    have := is_const_of_deriv_eq_zero (contDiff_chi.differentiable (by simp)) h 0 3
    rw [chi_zero, chi_three] at this
    exact one_ne_zero this
  refine (contDiff_deriv_chi.continuous.pow 2).integral_pos_of_hasCompactSupport_nonneg_nonzero
    (hasCompactSupport_chi.deriv.comp_left (g := fun r : ℝ => r ^ 2) (by norm_num))
    (fun y => sq_nonneg _) (x := x) ?_
  exact pow_ne_zero 2 hx

/-- `J_χ > 0` (TeX line 281). -/
theorem Jchi_pos : 0 < Jchi := by
  refine (contDiff_chi.continuous.pow 4).integral_pos_of_hasCompactSupport_nonneg_nonzero
    (hasCompactSupport_chi.comp_left (g := fun r : ℝ => r ^ 4) (by norm_num))
    (fun y => by positivity) (x := 0) ?_
  simp [chi_zero]

/-! ### The temporal factor -/

/-- The temporal factor is finite and strictly positive (TeX lines 287-289): for
`0 < a < 1`, `T > 0` and a continuous `τ ≥ 0` vanishing outside `[0,T]` and not
identically zero, the integrand `τ(t) τ(s) |t-s|^{-a}` is integrable on `ℝ²` and
`‖τ‖_a² > 0`.  Integrability is `TimeSchur.time_schur_paper`; positivity holds
because the nonnegative integrand is positive on a product of two intervals. -/
theorem timeQ_pos {a T : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hT : 0 < T) {τ : ℝ → ℝ}
    (hcont : Continuous τ) (hnn : ∀ t, 0 ≤ τ t) (hsupp : ∀ t, τ t ≠ 0 → t ∈ Icc 0 T)
    {t0 : ℝ} (ht0 : τ t0 ≠ 0) :
    Integrable (fun p : ℝ × ℝ => τ p.1 * τ p.2 * |p.1 - p.2| ^ (-a)) ∧ 0 < timeQ a τ := by
  set f := fun p : ℝ × ℝ => τ p.1 * τ p.2 * |p.1 - p.2| ^ (-a) with hfdef
  have hcs : HasCompactSupport τ := HasCompactSupport.intro isCompact_Icc fun t ht => by
    by_contra h; exact ht (hsupp t h)
  obtain ⟨M, hM⟩ := hcont.bounded_above_of_compact_support hcs
  have hmem : MemLp τ 2 (volume.restrict (Icc 0 T)) :=
    MemLp.of_bound hcont.aestronglyMeasurable M (Filter.Eventually.of_forall hM)
  have hi := (TimeSchur.time_schur_paper ha0 ha1 hT τ hmem).1
  rw [Measure.prod_restrict] at hi
  have hint : Integrable f ((volume : Measure ℝ).prod volume) := by
    refine IntegrableOn.integrable_of_forall_notMem_eq_zero (s := Icc 0 T ×ˢ Icc 0 T) hi
      fun p hp => ?_
    rw [mem_prod, not_and_or] at hp
    rcases hp with h | h
    · have : τ p.1 = 0 := by by_contra h'; exact h (hsupp _ h')
      simp [f, this]
    · have : τ p.2 = 0 := by by_contra h'; exact h (hsupp _ h')
      simp [f, this]
  refine ⟨by rw [Measure.volume_eq_prod]; exact hint, ?_⟩
  have heq : timeQ a τ = ∫ p, f p ∂((volume : Measure ℝ).prod volume) :=
    (integral_prod f hint).symm
  have hfnn : 0 ≤ f := fun p =>
    mul_nonneg (mul_nonneg (hnn _) (hnn _)) (Real.rpow_nonneg (abs_nonneg _) _)
  rw [heq, integral_pos_iff_support_of_nonneg hfnn hint]
  have hpos : 0 < τ t0 := lt_of_le_of_ne (hnn t0) (Ne.symm ht0)
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 (isOpen_lt continuous_const hcont) t0 hpos
  have hsub : Ioo (t0 - δ) t0 ×ˢ Ioo t0 (t0 + δ) ⊆ Function.support f := by
    rintro ⟨t, s⟩ ⟨ht, hs⟩
    have h1 : 0 < τ t := hball (by rw [Real.ball_eq_Ioo]; exact ⟨ht.1, by linarith [ht.2]⟩)
    have h2 : 0 < τ s := hball (by rw [Real.ball_eq_Ioo]; exact ⟨by linarith [hs.1], hs.2⟩)
    have h3 : 0 < |t - s| ^ (-a) :=
      Real.rpow_pos_of_pos (abs_pos.2 (by linarith [ht.2, hs.1])) _
    exact (mul_pos (mul_pos h1 h2) h3).ne'
  refine lt_of_lt_of_le ?_ (measure_mono hsub)
  rw [Measure.prod_prod, Real.volume_Ioo, Real.volume_Ioo]
  exact ENNReal.mul_pos (by simp [hδ]) (by simp [hδ])

/-! ### The obstruction -/

/-- Real compact smooth space-time tests supported in `(0,T) × ℝ^d`: the
manuscript's "compact smooth test `F`" (TeX line 262) with time support in the
section's interval. -/
def IsTest {d : ℕ} (T : ℝ) (F : ℝ → Rd d → ℝ) : Prop :=
  ContDiff ℝ ∞ (fun q : ℝ × Rd d => F q.1 q.2) ∧
    HasCompactSupport (fun q : ℝ × Rd d => F q.1 q.2) ∧
    ∀ t x, F t x ≠ 0 → t ∈ Ioo 0 T

/-- Auxiliary: tensors of tests are tests. -/
theorem isTest_tensor {d : ℕ} {T : ℝ} {τ : ℝ → ℝ} {g : Rd d → ℝ} (hτ : ContDiff ℝ ∞ τ)
    (hτc : HasCompactSupport τ) (hτs : ∀ t, τ t ≠ 0 → t ∈ Ioo 0 T) (hg : ContDiff ℝ ∞ g)
    (hgc : HasCompactSupport g) : IsTest T (fun t x => τ t * g x) := by
  refine ⟨(hτ.comp contDiff_fst).mul (hg.comp contDiff_snd), ?_, fun t x h => hτs t ?_⟩
  · refine HasCompactSupport.intro (hτc.isCompact.prod hgc.isCompact) fun q hq => ?_
    rw [mem_prod, not_and_or] at hq
    rcases hq with h | h
    · simp [image_eq_zero_of_notMem_tsupport h]
    · simp [image_eq_zero_of_notMem_tsupport h]
  · intro h0; exact h (by simp [h0])

/-- The mask `ζ(x) = χ(x₁) χ(x₂)` of TeX line 283. -/
def zeta (x : Rd 2) : ℝ := chi (x 0) * chi (x 1)

/-- The spatial test `g(x) = χ(x₁) χ''(x₂)` of TeX line 283. -/
def gtest (x : Rd 2) : ℝ := chi (x 0) * chi2 (x 1)

/-- `P:masked-quotient-obstruction`, the computation of its proof
(`notes/integrated_covariance_foundation.tex`, a284420, lines 265-292), with
`Γ = δ₀(dx₁) dx₂` and the covariance functional `covW` (`E:cov` read as a
covariance functional; D1).  For `0 < a < 1` and `T > 0` there are a nonnegative
nonzero smooth `τ` supported in `(0,T)` and the explicit `ζ = χ ⊗ χ`,
`g = χ ⊗ χ''` such that `F = τ ⊗ g` is a test, the temporal integrand is
integrable with `‖τ‖_a² > 0`, both spatial integrands are `Γ`-integrable,
`V(g) = 0`, `V(ζg) = J_χ I_χ²`, the unmasked variance `E W(F)²` is `0` and the
masked variance `E W(ζF)² = ‖τ‖_a² J_χ I_χ²` is strictly positive. -/
theorem masked_quotient_obstruction {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {T : ℝ}
    (hT : 0 < T) :
    ∃ τ : ℝ → ℝ, IsTest T (fun t x => τ t * gtest x) ∧
      Integrable (fun p : ℝ × ℝ => τ p.1 * τ p.2 * |p.1 - p.2| ^ (-a)) ∧
      0 < timeQ a τ ∧
      Integrable (fun z => ∫ x, gtest x * gtest (x - z)) Gamma0 ∧
      Integrable (fun z => ∫ x, (zeta x * gtest x) * (zeta (x - z) * gtest (x - z))) Gamma0 ∧
      margV gtest = 0 ∧ margV (fun x => zeta x * gtest x) = Jchi * Ichi ^ 2 ∧
      covW a Gamma0 (fun t x => τ t * gtest x) = 0 ∧
      covW a Gamma0 (fun t x => zeta x * (τ t * gtest x)) = timeQ a τ * (Jchi * Ichi ^ 2) ∧
      0 < covW a Gamma0 (fun t x => zeta x * (τ t * gtest x)) := by
  set b : ContDiffBump (T / 2) := ⟨T / 8, T / 4, by positivity, by linarith⟩
  set τ : ℝ → ℝ := ⇑b
  have hτs : ∀ t, τ t ≠ 0 → t ∈ Ioo 0 T := by
    intro t ht
    have : t ∈ Function.support τ := ht
    rw [b.support_eq, Real.ball_eq_Ioo, show b.rOut = T / 4 from rfl] at this
    exact ⟨by linarith [this.1], by linarith [this.2]⟩
  have hτ1 : τ (T / 2) ≠ 0 := by
    show b (T / 2) ≠ 0
    rw [b.one_of_mem_closedBall (mem_closedBall_self (by positivity))]; exact one_ne_zero
  obtain ⟨hTi, hTpos⟩ := timeQ_pos ha0 ha1 hT b.continuous (fun t => b.nonneg)
    (fun t ht => Ioo_subset_Icc_self (hτs t ht)) hτ1
  have hg : ContDiff ℝ ∞ gtest := contDiff_tensor contDiff_chi contDiff_chi2
  have hgc : HasCompactSupport gtest := hasCompactSupport_tensor hasCompactSupport_chi
    hasCompactSupport_chi2
  have hz : ContDiff ℝ ∞ zeta := contDiff_tensor contDiff_chi contDiff_chi
  have hzg : ContDiff ℝ ∞ (fun x => zeta x * gtest x) := hz.mul hg
  have hzgc : HasCompactSupport (fun x => zeta x * gtest x) := hgc.mul_left
  obtain ⟨_, hgi, hgV⟩ := spatialCov_Gamma0 hg.continuous hgc
  obtain ⟨_, hzgi, hzgV⟩ := spatialCov_Gamma0 hzg.continuous hzgc
  have hV0 : margV gtest = 0 := by
    refine (margV_tensor chi chi2).trans ?_
    rw [integral_chi2]; ring
  have hV1 : margV (fun x => zeta x * gtest x) = Jchi * Ichi ^ 2 := by
    have : (fun x : Rd 2 => zeta x * gtest x) =
        fun x => (fun u => chi u ^ 2) (x 0) * (fun v => chi v * chi2 v) (x 1) := by
      funext x; simp only [zeta, gtest]; ring
    rw [this]
    refine (margV_tensor (fun u => chi u ^ 2) (fun v => chi v * chi2 v)).trans ?_
    rw [integral_chi_mul_chi2, Jchi]
    simp_rw [← pow_mul]
    ring
  have hcov0 : covW a Gamma0 (fun t x => τ t * gtest x) = 0 := by
    rw [covW_tensor, hgV, hV0, mul_zero]
  have hcov1 : covW a Gamma0 (fun t x => zeta x * (τ t * gtest x)) =
      timeQ a τ * (Jchi * Ichi ^ 2) := by
    have : (fun t x => zeta x * (τ t * gtest x)) = fun t x => τ t * (zeta x * gtest x) := by
      funext t x; ring
    rw [this, covW_tensor, hzgV, hV1]
  refine ⟨τ, isTest_tensor b.contDiff b.hasCompactSupport hτs hg hgc, hTi, hTpos, hgi, hzgi,
    hV0, hV1, hcov0, hcov1, ?_⟩
  rw [hcov1]
  exact mul_pos hTpos (mul_pos Jchi_pos (pow_pos Ichi_pos 2))

/-- `P:masked-quotient-obstruction` (A physical mask need not preserve noise-null
tests), `notes/integrated_covariance_foundation.tex`, a284420, statement lines
257-263, proof lines 265-292, with the manuscript's hypotheses: `d = 2`, `α = 1`,
`0 < a < 1` (`a = α₀`), `Γ = δ₀(dx₁) dx₂` and the section's `T > 0`.  Conclusions:
`Γ` with `μ = (2π)^{-1} dξ₁ δ₀(dξ₂)` satisfies `H:homog` (TeX lines 266-270) and
`Γ ≠ 0` (the section's standing assumption, lines 5-6, holds), and there is a
real compact smooth mask `ζ` such that no finite `C` satisfies
`E W(ζF)² ≤ C E W(F)²` for every real compact smooth test `F` supported in
`(0,T) × ℝ²`.  `E W(F)²` is read as the covariance functional `covW` of `E:cov`
(definitional D1 boundary: the noise `W` is not constructed).  Restricting the
tests to time support in `(0,T)` makes the conclusion stronger than for all compact
smooth tests. -/
theorem masked_quotient_obstruction_paper {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {T : ℝ}
    (hT : 0 < T) :
    HomogCovariance 2 1 a Gamma0 mu0 ∧ Gamma0 ≠ 0 ∧
      ∃ ζ : Rd 2 → ℝ, ContDiff ℝ ∞ ζ ∧ HasCompactSupport ζ ∧
        ¬ ∃ C : ℝ, ∀ F : ℝ → Rd 2 → ℝ, IsTest T F →
          covW a Gamma0 (fun t x => ζ x * F t x) ≤ C * covW a Gamma0 F := by
  refine ⟨homogCovariance_Gamma0 ha0 ha1, Gamma0_ne_zero, zeta,
    contDiff_tensor contDiff_chi contDiff_chi, hasCompactSupport_tensor hasCompactSupport_chi hasCompactSupport_chi, ?_⟩
  rintro ⟨C, hC⟩
  obtain ⟨τ, hF, -, -, -, -, -, -, h0, -, hpos⟩ := masked_quotient_obstruction ha0 ha1 hT
  have := hC _ hF
  rw [h0, mul_zero] at this
  linarith

end StratonovichHAMSecondMoment.QuotientObstruction
