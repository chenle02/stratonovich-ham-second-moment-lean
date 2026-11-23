module

/-
Copyright 2026 Le Chen. SPDX-License-Identifier: Apache-2.0

The two dimension-three corollaries of Section `S:three-endpoints` of the main TeX file
`notes/notes_stratonovich_ham_second_moment.tex` at revision edf7085f (all line numbers below
are at edf7085f): `C:three-product-riesz` (statement lines 7944-7959, proof 7961-7988) and
`C:three-finite-images` (statement 7991-8010, proof 8012-8035), assembled from the endpoint
lemmas of `EndpointLemmas` (wave L14-3D) and the conditional transfer `P:three-transfer`
(statement lines 7536-7556), which is supplied, not formalized.

Definitions (new):
* `rieszMeasure c e = c|x|^{-e} dx` on `ℝ³` (density `HigherRieszTwo.riesz c e`, wave L10).
* `ThreeMomentModel`: the quantities of `P:three-transfer` attached to the solution `u` of the
  `d = 3` model with temporal exponent `α₀` and data `(1,0)`, as functions of the spatial
  covariance `Γ`: the coefficients `A_k(t)` (`A Γ k t`), the second moment `E u²(t,x)`
  (`M2 Γ t x`) and the static variational constant `M_st` of `E:three-static-variational`
  (`Mst S`, a function of the static endpoint `S`).  None of them is constructed in the
  package (the solution `u`, its chaos coefficients and the Sobolev variational problem are
  missing constructions); this is the split modelled-object rule, so every statement about
  them is narrower.
* `lowConst`, `staticConst`: `C_low = 2 Z_{b₀} π V_low`, `Z_{b₀} = 2/((1-b₀)(2-b₀))`,
  `Λ_st = 2 (2√M_st/(4-χ))^{4-χ}` (lines 7503-7528), with `V_low = μ_low(closed unit ball)`
  for a spectral measure `μ_low` of `Γ_low` (the convention of `L:alpha-one-convolution`).
* `TransferConclusion`: the three displays `E:three-transfer` (coefficient bound for `k ≥ 1`,
  all-time moment bound) and `E:three-variational-upper` (the `limsup` stated as: for every
  `η > 0`, eventually `t^{-κ} log E u²(t,x) ≤ q (C_low^θ Λ_st^{1-θ})^{1/q} + η`, for every
  spectral measure `μ_low` of `Γ_low` and every `x`), with one constant `C > 0`.
* `ThreeTransfer Mdl α₀ θ`: supplied input, the exact statement of `P:three-transfer` for
  the model `Mdl` (see its doc comment).
* `Component`: the three classes of `C:three-finite-images` (ordinary products, isotropic
  Riesz, plane-supported) with their target and endpoint measures.

Formalized:
* the isotropic Riesz endpoints of `C:three-product-riesz` (lines 7971-7985):
  `riesz_props` (even, tempered, locally finite, scaling `3 - e`, for `0 < e < 3`) and
  `riesz_comparison` (`c|x|^{-α} = (c|x|^{-1})^θ (c|x|^{-χ})^{1-θ}`, Hölder); positive
  definiteness by the supplied input `RieszIsoPD`;
* `three_product_riesz_paper` (`C:three-product-riesz`) and `three_finite_images_paper`
  (`C:three-finite-images`): with the midpoint `θ = (α₀ + 2 - α)/2`, all endpoint hypotheses
  are discharged (endpoint pairs constructed, target a nonzero covariance with scaling
  `3 - α`), and `ThreeTransfer` then yields `TransferConclusion` for the actual target and
  endpoint measures.

Supplied inputs (named hypotheses):
* `EndpointLemmas.RieszProductPD`, `EndpointLemmas.PlaneRieszPD` (from the lemmas) and
  `RieszIsoPD`: `c|x|^{-e} dx` on `ℝ³` is positive definite for `c ≥ 0`, `0 < e < 3`
  (true: Gaussian mixture, lines 7975-7980);
* `ThreeTransfer`: `P:three-transfer` itself (not formalized, as the plan prescribes).

Class: narrower.  Missing: the solution `u`, its coefficients `A_k(t)`, `E u²(t,x)` and the
variational constant `M_st` are not constructed (abstract `ThreeMomentModel`), and
`P:three-transfer` is supplied; moreover no spectral measure is constructed for the product
and Riesz low endpoints (Bochner-Schwartz is absent), so the asymptotic clause is stated
for every spectral measure of `Γ_low` and is vacuous where none is supplied.  For the plane
low endpoint `EndpointLemmas.planeLow_isSpectral` supplies one.  The endpoint construction,
the covariance properties, the nonvanishing of the target and the parameter choice are
proved.

Unused hypotheses carried by the wrappers: none beyond those passed to `ThreeTransfer`
(`α₀ < 1` is used only there).  Differences from the TeX: the product and plane endpoints
come from `EndpointLemmas`; the TeX's "the constant depends only on the data" is implicit in
the statement (`C` is chosen after the data are fixed).
-/

public import Mathlib
public import StratonovichHAMSecondMoment.EndpointLemmas
public import StratonovichHAMSecondMoment.KappaRange

@[expose] public section

noncomputable section

set_option autoImplicit false

open MeasureTheory Set Real Metric Filter
open scoped ENNReal NNReal Pointwise Topology

namespace StratonovichHAMSecondMoment.EndpointCorollaries

open HomogHypothesis (Rd IsTempered IsEven IsPosDefDistr IsSpectralMeasure)
open EndpointLemmas
open HigherRieszTwo (riesz measurable_riesz)

/-! ### Isotropic Riesz endpoints -/

/-- The isotropic Riesz covariance measure `c|x|^{-e} dx` on `ℝ³` (main TeX lines 7956,
7971-7972). -/
def rieszMeasure (c e : ℝ) : Measure (Rd 3) := (volume : Measure (Rd 3)).withDensity (riesz c e)

/-- Supplied input (positive definiteness of isotropic Riesz densities, main TeX lines
7975-7980): `c|x|^{-e} dx` on `ℝ³` is positive definite for `c ≥ 0` and `0 < e < 3`.  TRUE:
`c|x|^{-e} = c Γ(e/2)^{-1} ∫_0^∞ s^{e/2-1} e^{-s|x|²} ds` is a positive mixture of
positive-definite Gaussians, and the Schwartz autocorrelation is absolutely integrable against
it.  Not formalized, for the same reason as `RieszProductPD`. -/
def RieszIsoPD : Prop :=
  ∀ c e : ℝ, 0 ≤ c → 0 < e → e < 3 → IsPosDefDistr (rieszMeasure c e)

/-- Auxiliary to the Lean proof route: `|x|^{-e} (1+|x|)^{-4}` is integrable on `ℝ³` for
`0 < e < 3` (local integrability and temperedness, main TeX lines 7972-7974). -/
theorem integrable_norm_rpow_mul {e : ℝ} (he0 : 0 ≤ e) (he3 : e < 3) :
    Integrable fun x : Rd 3 => ‖x‖ ^ (-e) * (1 + ‖x‖) ^ (-(4 : ℝ)) := by
  set g : Rd 3 → ℝ := fun x => ‖x‖ ^ (-e) * (1 + ‖x‖) ^ (-(4 : ℝ))
  have hgm : Measurable g := by fun_prop
  have hg0 : ∀ x, 0 ≤ g x := fun x => by positivity
  have hb : IntegrableOn g (ball 0 1) := by
    refine integrableOn_ball_of_norm_le_rpow (C := 1) (α := e) (by simp)
      (by simpa using he3) (Eventually.of_forall fun x => ?_) hgm.aestronglyMeasurable
    rw [Real.norm_eq_abs, abs_of_nonneg (hg0 x), one_mul]
    change ‖x‖ ^ (-e) * (1 + ‖x‖) ^ (-(4 : ℝ)) ≤ _
    have hq : (1 + ‖x‖) ^ (-(4 : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by linarith [norm_nonneg x]) (by norm_num)
    have := Real.rpow_nonneg (norm_nonneg x) (-e)
    calc ‖x‖ ^ (-e) * (1 + ‖x‖) ^ (-(4 : ℝ)) ≤ ‖x‖ ^ (-e) * 1 := by gcongr
      _ = _ := mul_one _
  have hc : IntegrableOn g (ball 0 1)ᶜ := by
    have hI : Integrable (fun x : Rd 3 => (1 + ‖x‖) ^ (-(4 : ℝ))) :=
      integrable_one_add_norm (by simp; norm_num)
    refine hI.integrableOn.mono' hgm.aestronglyMeasurable
      ((ae_restrict_iff' measurableSet_ball.compl).2 (Eventually.of_forall fun x hx => ?_))
    have hx1 : 1 ≤ ‖x‖ := by simpa using hx
    rw [Real.norm_eq_abs, abs_of_nonneg (hg0 x)]
    change ‖x‖ ^ (-e) * (1 + ‖x‖) ^ (-(4 : ℝ)) ≤ _
    have : ‖x‖ ^ (-e) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx1 (by linarith)
    calc ‖x‖ ^ (-e) * (1 + ‖x‖) ^ (-(4 : ℝ)) ≤ 1 * (1 + ‖x‖) ^ (-(4 : ℝ)) := by gcongr
      _ = _ := one_mul _
  have := hb.union hc
  rwa [union_compl_self, integrableOn_univ] at this

/-- Auxiliary to the Lean proof route: `c|x|^{-e}` is homogeneous of degree `-e`. -/
theorem riesz_smul (c e : ℝ) {r : ℝ} (hr : 0 < r) (x : Rd 3) :
    riesz c e (r • x) = ENNReal.ofReal (r ^ (-e)) * riesz c e x := by
  unfold riesz
  rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hr.le _), norm_smul, Real.norm_eq_abs,
    abs_of_pos hr, Real.mul_rpow hr.le (norm_nonneg _)]
  ring_nf

/-- The covariance properties of `c|x|^{-e} dx` other than positive definiteness (main TeX
lines 7972-7974): for `c ≥ 0` and `0 < e < 3` it is locally finite, even, tempered, with
measure scaling exponent `3 - e` (covariance homogeneity exponent `e`). -/
theorem riesz_props {c e : ℝ} (hc : 0 ≤ c) (he0 : 0 < e) (he3 : e < 3) :
    IsLocallyFiniteMeasure (rieszMeasure c e) ∧ IsEven (rieszMeasure c e) ∧
      IsTempered (rieszMeasure c e) ∧ Scaling (rieszMeasure c e) (3 - e) := by
  have ht : IsTempered (rieszMeasure c e) := by
    refine ⟨4, ?_⟩
    have hmk : Measurable fun x : Rd 3 => ENNReal.ofReal ((1 + ‖x‖) ^ (-((4 : ℕ) : ℝ))) := by
      fun_prop
    rw [rieszMeasure, lintegral_withDensity_eq_lintegral_mul _ (measurable_riesz c e) hmk]
    have hI := (integrable_norm_rpow_mul he0.le he3).const_mul c
    refine lt_of_le_of_lt (le_of_eq ?_) hI.lintegral_lt_top
    refine lintegral_congr fun x => ?_
    simp only [Pi.mul_apply, riesz]
    rw [← ENNReal.ofReal_mul (mul_nonneg hc (Real.rpow_nonneg (norm_nonneg _) _))]
    congr 1
    push_cast; ring
  refine ⟨isLocallyFiniteMeasure_of_tempered ht,
    isEven_withDensity (measurable_riesz c e) (fun x => by simp [riesz]), ht, ?_⟩
  have := scaling_withDensity (n := 3) (measurable_riesz c e) fun r hr x => riesz_smul c e hr x
  simpa [rieszMeasure] using this

/-- The Riesz comparison of `C:three-product-riesz` (main TeX lines 7981-7985): with
`α = θ + (1 - θ) χ` and `c > 0`, the common-width Gaussian comparison `GaussComparison θ` of
the three Riesz measures.  The proof factors `c|x|^{-α} = (c|x|^{-1})^θ (c|x|^{-χ})^{1-θ}` at
every point (Lean's value `0` at `x = 0` on all three sides) and applies Hölder; the
factorization is not exported. -/
theorem riesz_comparison {c θ α χ : ℝ} (hc : 0 < c) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hα : α ≠ 0) (hrec : α = θ * 1 + (1 - θ) * χ) :
    GaussComparison θ (rieszMeasure c α) (rieszMeasure c 1) (rieszMeasure c χ) := by
  have h1θ : 0 ≤ 1 - θ := by linarith
  have hfac : ∀ x : Rd 3, riesz c α x ≤ riesz c 1 x ^ θ * riesz c χ x ^ (1 - θ) := by
    intro x
    refine le_of_eq ?_
    unfold riesz
    have hP : ∀ e : ℝ, 0 ≤ c * ‖x‖ ^ (-e) := fun e =>
      mul_nonneg hc.le (Real.rpow_nonneg (norm_nonneg _) _)
    rw [ENNReal.ofReal_rpow_of_nonneg (hP 1) hθ0.le, ENNReal.ofReal_rpow_of_nonneg (hP χ) h1θ,
      ← ENNReal.ofReal_mul (Real.rpow_nonneg (hP 1) _)]
    congr 1
    have hf := abs_rpow_factor hθ0 hθ1 hrec (fun h => absurd h hα) (fun _ => Or.inl one_ne_zero)
      ‖x‖
    rw [abs_norm] at hf
    rw [Real.mul_rpow hc.le (Real.rpow_nonneg (norm_nonneg _) _),
      Real.mul_rpow hc.le (Real.rpow_nonneg (norm_nonneg _) _), hf]
    have hcc : c = c ^ θ * c ^ (1 - θ) := by
      rw [← Real.rpow_add hc, add_sub_cancel, Real.rpow_one]
    conv_lhs => rw [hcc]
    ring
  have h := gaussComparison_map_withDensity (ν := (volume : Measure (Rd 3))) (ι := id)
    measurable_id (measurable_riesz c α) (measurable_riesz c 1) (measurable_riesz c χ) hθ0.le
    hθ1.le hfac
  simpa [Measure.map_id, rieszMeasure] using h

/-! ### Nonvanishing of the targets -/

/-- Auxiliary to the Lean proof route: a density measure whose density is a.e. positive is
nonzero. -/
theorem withDensity_ne_zero_of_ae_pos {m : ℕ} {f : Rd m → ℝ≥0∞} (hf : Measurable f)
    (hpos : ∀ᵐ x ∂(volume : Measure (Rd m)), 0 < f x) :
    (volume : Measure (Rd m)).withDensity f ≠ 0 := by
  intro h
  rw [withDensity_eq_zero_iff hf.aemeasurable] at h
  obtain ⟨x, hx1, hx2⟩ := (hpos.and h).exists
  rw [hx2] at hx1
  exact lt_irrefl _ hx1

/-- Auxiliary to the Lean proof route: the product density measure is nonzero for `c > 0`
(the coordinate hyperplanes are Lebesgue-null). -/
theorem prodRieszMeasure_ne_zero {m : ℕ} {c : ℝ} (hc : 0 < c) (e : Fin m → ℝ) :
    prodRieszMeasure c e ≠ 0 := by
  refine withDensity_ne_zero_of_ae_pos (measurable_prodRiesz c e) ?_
  have hj : ∀ j : Fin m, ∀ᵐ x ∂(volume : Measure (Rd m)), x j ≠ 0 := by
    intro j
    have hker : (LinearMap.ker (EuclideanSpace.proj j : Rd m →L[ℝ] ℝ).toLinearMap) ≠ ⊤ := by
      intro htop
      have : EuclideanSpace.single j (1 : ℝ) ∈
          LinearMap.ker (EuclideanSpace.proj j : Rd m →L[ℝ] ℝ).toLinearMap := by
        rw [htop]; trivial
      simp at this
    have h0 := Measure.addHaar_submodule (volume : Measure (Rd m)) _ hker
    rw [measure_eq_zero_iff_ae_notMem] at h0
    filter_upwards [h0] with x hx
    simpa using hx
  filter_upwards [ae_all_iff.2 hj] with x hx
  refine ENNReal.ofReal_pos.2 (mul_pos hc (Finset.prod_pos fun j _ => ?_))
  exact Real.rpow_pos_of_pos (abs_pos.2 (hx j)) _

/-- Auxiliary to the Lean proof route: `c|x|^{-e} dx` is nonzero for `c > 0`. -/
theorem rieszMeasure_ne_zero {c : ℝ} (hc : 0 < c) (e : ℝ) : rieszMeasure c e ≠ 0 := by
  refine withDensity_ne_zero_of_ae_pos (measurable_riesz c e) ?_
  have h0 : ∀ᵐ x ∂(volume : Measure (Rd 3)), x ≠ 0 := by
    have : (volume : Measure (Rd 3)) {0} = 0 := measure_singleton 0
    rw [measure_eq_zero_iff_ae_notMem] at this
    filter_upwards [this] with x hx
    simpa using hx
  filter_upwards [h0] with x hx
  exact ENNReal.ofReal_pos.2 (mul_pos hc (Real.rpow_pos_of_pos (norm_pos_iff.2 hx) _))

/-- Auxiliary to the Lean proof route: a pushforward of a nonzero measure is nonzero. -/
theorem map_ne_zero_of_ne_zero {m : ℕ} {μ : Measure (Rd m)} (hμ : μ ≠ 0) {f : Rd m → Rd 3}
    (hf : Measurable f) : μ.map f ≠ 0 := by
  intro h
  apply hμ
  rw [← Measure.measure_univ_eq_zero] at h ⊢
  rwa [Measure.map_apply hf MeasurableSet.univ, preimage_univ] at h

/-- Auxiliary to the Lean proof route: a weighted sum with a positive weight on a nonzero
component is nonzero. -/
theorem wsum_ne_zero {N : ℕ} {w : Fin N → ℝ} {μ : Fin N → Measure (Rd 3)} {i : Fin N}
    (hwi : 0 < w i) (hμi : μ i ≠ 0) : wsum w μ ≠ 0 := by
  intro h
  apply hμi
  rw [← Measure.measure_univ_eq_zero] at h ⊢
  have hle : ENNReal.ofReal (w i) * μ i univ ≤ wsum w μ univ := by
    simp only [wsum, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply, smul_eq_mul]
    exact Finset.single_le_sum (f := fun j => ENNReal.ofReal (w j) * μ j univ)
      (fun _ _ => bot_le) (Finset.mem_univ i)
  rw [h] at hle
  rcases mul_eq_zero.1 (le_zero_iff.1 hle) with h1 | h1
  · exact absurd h1 (ENNReal.ofReal_pos.2 hwi).ne'
  · exact h1

/-! ### `P:three-transfer` as a supplied input -/

/-- The quantities of `P:three-transfer` (main TeX lines 7536-7556), as functions of the
spatial covariance: `A Γ k t = A_k(t)`, `M2 Γ t x = E u²(t,x)` for the `d = 3` model with
the fixed temporal exponent and data `(1,0)`, and `Mst S = M_st` of
`E:three-static-variational` (lines 7510-7528) for the static endpoint `S`.  Not constructed
in the package (missing constructions: the solution, its chaos coefficients and the Sobolev
variational supremum). -/
structure ThreeMomentModel where
  A : Measure (Rd 3) → ℕ → ℝ → ℝ
  M2 : Measure (Rd 3) → ℝ → Rd 3 → ℝ
  Mst : Measure (Rd 3) → ℝ

/-- `C_low = 2 Z_{b₀} π V_low`, `Z_{b₀} = 2/((1-b₀)(2-b₀))`, `b₀ = α₀/θ` (main TeX lines
7503-7507). -/
def lowConst (α₀ θ Vlow : ℝ) : ℝ :=
  2 * (2 / ((1 - α₀ / θ) * (2 - α₀ / θ))) * π * Vlow

/-- `Λ_st = 2 (2√M_st/(4-χ))^{4-χ}` (main TeX lines 7523-7528). -/
def staticConst (χ Mst : ℝ) : ℝ := 2 * (2 * Real.sqrt Mst / (4 - χ)) ^ (4 - χ)

/-- The conclusions of `P:three-transfer` (`E:three-transfer`, `E:three-variational-upper`,
main TeX lines 7538-7556) for the model `Mdl`, target `Γ` and endpoints `L`, `S`: one
constant `C > 0` with `A_k(t) ≤ C^k t^{(4-α-α₀)k}/(k!)^{3-α}` (`k ≥ 1`, `t > 0`) and
`E u²(t,x) ≤ exp(q C^{1/q} t^κ)`, `q = 3 - α` (`t > 0`, every `x`); and for every spectral
measure `μ_low` of `L` and every `x`, `limsup_{t→∞} t^{-κ} log E u²(t,x) ≤
q (C_low^θ Λ_st^{1-θ})^{1/q}`, in the form "for every `η > 0`, eventually `≤ … + η`". -/
def TransferConclusion (Mdl : ThreeMomentModel) (α₀ α θ : ℝ) (Γ L S : Measure (Rd 3)) :
    Prop :=
  ∃ C : ℝ, 0 < C ∧
    (∀ k : ℕ, 1 ≤ k → ∀ t : ℝ, 0 < t →
      Mdl.A Γ k t ≤ C ^ k * t ^ ((4 - α - α₀) * k) / ((k.factorial : ℝ) ^ (3 - α))) ∧
    (∀ t : ℝ, 0 < t → ∀ x : Rd 3,
      Mdl.M2 Γ t x ≤ Real.exp ((3 - α) * C ^ (1 / (3 - α)) * t ^ KappaRange.kappa α α₀)) ∧
    (∀ μlow : Measure (Rd 3), IsSpectralMeasure L μlow → ∀ x : Rd 3, ∀ η : ℝ, 0 < η →
      ∀ᶠ t in atTop, t ^ (-KappaRange.kappa α α₀) * Real.log (Mdl.M2 Γ t x) ≤
        (3 - α) * (lowConst α₀ θ (μlow (closedBall 0 1)).toReal ^ θ *
          staticConst (chi α θ) (Mdl.Mst S) ^ (1 - θ)) ^ (1 / (3 - α)) + η)

/-- Supplied input: `P:three-transfer` (main TeX lines 7536-7556; proof 7558-7940), the
conditional three-dimensional transfer, for the model `Mdl` and the fixed `α₀`, `θ`: under
the section's assumptions (`0 < α₀ < 1`, `1 < α < 2 - α₀`, `α₀ < θ < 2 - α`; `Γ` a nonzero
covariance with measure scaling `3 - α`) and `H:three-endpoints` with endpoints `L`, `S`,
the conclusions `TransferConclusion` hold.  TRUE for the model whose fields are the
manuscript's `A_k(t)`, `E u²(t,x)` and `M_st` (that is `P:three-transfer`); for an arbitrary
`Mdl` it is an assumption about `Mdl`.  Not formalized (the plan supplies it). -/
def ThreeTransfer (Mdl : ThreeMomentModel) (α₀ θ : ℝ) : Prop :=
  ∀ (α : ℝ) (Γ L S : Measure (Rd 3)), 0 < α₀ → α₀ < 1 → 1 < α → α < 2 - α₀ → α₀ < θ →
    θ < 2 - α → IsCov Γ → Scaling Γ (3 - α) → Γ ≠ 0 → EndpointPair θ (chi α θ) Γ L S →
    TransferConclusion Mdl α₀ α θ Γ L S

/-- The fixed midpoint `θ = (α₀ + 2 - α)/2` of both corollaries (main TeX lines 7962,
8013). -/
def midTheta (α₀ α : ℝ) : ℝ := (α₀ + 2 - α) / 2

/-- Auxiliary to the Lean proof route: `α₀ < θ < 2 - α` for the midpoint. -/
theorem midTheta_mem {α₀ α : ℝ} (h : α < 2 - α₀) : α₀ < midTheta α₀ α ∧ midTheta α₀ α < 2 - α :=
  ⟨by unfold midTheta; linarith, by unfold midTheta; linarith⟩

/-! ### `C:three-product-riesz` -/

/-- The endpoints of the isotropic Riesz covariance (main TeX lines 7971-7985): for `c > 0`,
`1 < α < 2`, `0 < θ < 2 - α`, `(c|x|^{-1}, c|x|^{-χ})` is an endpoint pair for `c|x|^{-α}`,
which is a nonzero covariance with measure scaling `3 - α`. -/
theorem riesz_endpoints (hPD : RieszIsoPD) {c α θ : ℝ} (hc : 0 < c) (hα1 : 1 < α)
    (hθ0 : 0 < θ) (hθ : θ < 2 - α) :
    (IsCov (rieszMeasure c α) ∧ Scaling (rieszMeasure c α) (3 - α) ∧ rieszMeasure c α ≠ 0) ∧
      EndpointPair θ (chi α θ) (rieszMeasure c α) (rieszMeasure c 1)
        (rieszMeasure c (chi α θ)) := by
  have hθ1 : θ < 1 := by linarith
  have h1θ : 0 < 1 - θ := by linarith
  have hχ1 : 1 < chi α θ := by rw [chi, lt_div_iff₀ h1θ]; linarith
  have hχ2 : chi α θ < 2 := by rw [chi, div_lt_iff₀ h1θ]; linarith
  have cov : ∀ e, 0 < e → e < 3 → IsCov (rieszMeasure c e) ∧ Scaling (rieszMeasure c e) (3 - e) :=
    fun e he0 he3 => by
      obtain ⟨h1, h2, h3, h4⟩ := riesz_props hc.le he0 he3
      exact ⟨⟨h1, h2, h3, hPD c e hc.le he0 he3⟩, h4⟩
  have c1 := cov 1 one_pos (by norm_num)
  have cχ := cov (chi α θ) (by linarith) (by linarith)
  have cα := cov α (by linarith) (by linarith)
  norm_num at c1
  refine ⟨⟨cα.1, cα.2, rieszMeasure_ne_zero hc α⟩, c1.1, cχ.1, c1.2, cχ.2,
    riesz_comparison hc hθ0 hθ1 (by linarith) ?_⟩
  rw [chi]; field_simp; ring

/-- The product target of `C:three-product-riesz` is a nonzero covariance with an endpoint
pair (from `L:product-endpoints`). -/
theorem product_target (hPD : RieszProductPD) {c θ : ℝ} {a : Fin 3 → ℝ} (hc : 0 < c)
    (ha : ∀ j, 0 ≤ a j ∧ a j < 1) (hα1 : 1 < ∑ j, a j) (hθ0 : 0 < θ)
    (hθ : θ < 2 - ∑ j, a j) :
    (IsCov (prodRieszMeasure c a) ∧ Scaling (prodRieszMeasure c a) (3 - ∑ j, a j) ∧
        prodRieszMeasure c a ≠ 0) ∧
      EndpointPair θ (chi (∑ j, a j) θ) (prodRieszMeasure c a) (prodRieszMeasure c (bVec θ a))
        (prodRieszMeasure c (vVec θ a)) := by
  have hα2 : ∑ j, a j < 2 := by linarith
  obtain ⟨-, hcov, -, hpair⟩ := product_endpoints_paper hPD (fun j => (ha j).1)
    (fun j => (ha j).2) hα1 hα2 hθ0 hθ hc
  exact ⟨⟨hcov.1.1, hcov.1.2.2, prodRieszMeasure_ne_zero hc a⟩, hpair⟩

/-- `C:three-product-riesz` (main TeX lines 7944-7959; proof 7961-7988), with the manuscript's
hypotheses `0 < α₀ < 1`, `1 < α < 2 - α₀`, `c > 0`, the supplied inputs and the midpoint
`θ`: (1) for `γ = c ∏|x_j|^{-a_j}`, `0 ≤ a_j < 1`, `Σ a_j = α`, and (2) for `γ = c|x|^{-α}`,
the conclusions of `P:three-transfer` hold for the target and the endpoints constructed in
the proof (`L:product-endpoints`; `c|x|^{-1}`, `c|x|^{-χ}`).  NARROWER: the moment
statements are about the abstract `ThreeMomentModel` (the solution is not constructed) and
rest on `ThreeTransfer`. -/
theorem three_product_riesz_paper (hPD : RieszProductPD) (hIso : RieszIsoPD)
    (Mdl : ThreeMomentModel) {α₀ α c : ℝ} (hT : ThreeTransfer Mdl α₀ (midTheta α₀ α))
    (hα₀ : 0 < α₀) (hα₀1 : α₀ < 1) (hα1 : 1 < α) (hα2 : α < 2 - α₀) (hc : 0 < c) :
    (∀ a : Fin 3 → ℝ, (∀ j, 0 ≤ a j ∧ a j < 1) → ∑ j, a j = α →
      TransferConclusion Mdl α₀ α (midTheta α₀ α) (prodRieszMeasure c a)
        (prodRieszMeasure c (bVec (midTheta α₀ α) a))
        (prodRieszMeasure c (vVec (midTheta α₀ α) a))) ∧
    TransferConclusion Mdl α₀ α (midTheta α₀ α) (rieszMeasure c α) (rieszMeasure c 1)
      (rieszMeasure c (chi α (midTheta α₀ α))) := by
  obtain ⟨hθ0, hθ⟩ := midTheta_mem hα2
  have hθpos : 0 < midTheta α₀ α := by linarith
  refine ⟨fun a ha hsum => ?_, ?_⟩
  · subst hsum
    obtain ⟨⟨h1, h2, h3⟩, hpair⟩ := product_target hPD hc ha hα1 hθpos hθ
    exact hT _ _ _ _ hα₀ hα₀1 hα1 hα2 hθ0 hθ h1 h2 h3 hpair
  · obtain ⟨⟨h1, h2, h3⟩, hpair⟩ := riesz_endpoints hIso hc hα1 hθpos hθ
    exact hT _ _ _ _ hα₀ hα₀1 hα1 hα2 hθ0 hθ h1 h2 h3 hpair

/-! ### `C:three-finite-images` -/

/-- The component classes of `C:three-finite-images` (main TeX lines 7994-7999): ordinary
products `c ∏|x_j|^{-a_j}`, isotropic Riesz `c|x|^{-α}`, plane-supported
`c ∏|y_j|^{-a_j} dy δ₀(dz)`. -/
inductive Component
  | product (c : ℝ) (a : Fin 3 → ℝ)
  | riesz (c : ℝ)
  | plane (c : ℝ) (a : Fin 2 → ℝ)

namespace Component

/-- The admissibility of a component for the homogeneity exponent `α` (main TeX lines
7994-7999, 7951-7957, 7317-7318). -/
def Valid (α : ℝ) : Component → Prop
  | product c a => 0 < c ∧ (∀ j, 0 ≤ a j ∧ a j < 1) ∧ ∑ j, a j = α
  | riesz c => 0 < c
  | plane c a => 0 < c ∧ (∀ j, 0 ≤ a j) ∧ a 0 + a 1 = α - 1

/-- The component measure `Γ_i`. -/
def meas (α : ℝ) : Component → Measure (Rd 3)
  | product c a => prodRieszMeasure c a
  | riesz c => rieszMeasure c α
  | plane c a => planeMeasure c a

/-- The low endpoint constructed for the component (main TeX lines 8015-8020). -/
def low (θ : ℝ) : Component → Measure (Rd 3)
  | product c a => prodRieszMeasure c (bVec θ a)
  | riesz c => rieszMeasure c 1
  | plane c _ => planeMeasure c 0

/-- The static endpoint constructed for the component (main TeX lines 8015-8020). -/
def st (α θ : ℝ) : Component → Measure (Rd 3)
  | product c a => prodRieszMeasure c (vVec θ a)
  | riesz c => rieszMeasure c (chi α θ)
  | plane c a => planeMeasure c fun j => a j / (1 - θ)

end Component

/-- Every admissible component has an endpoint pair with the common parameters and is a
nonzero covariance with measure scaling `3 - α` (main TeX lines 8013-8021). -/
theorem component_endpoints (hPD : RieszProductPD) (hIso : RieszIsoPD) (hPl : PlaneRieszPD)
    {α₀ α θ : ℝ} (hα₀ : 0 < α₀) (hα₀1 : α₀ < 1) (hα1 : 1 < α) (hα2 : α < 2 - α₀)
    (hθ0 : α₀ < θ) (hθ : θ < 2 - α) {X : Component} (hX : X.Valid α) :
    (IsCov (X.meas α) ∧ Scaling (X.meas α) (3 - α) ∧ X.meas α ≠ 0) ∧
      EndpointPair θ (chi α θ) (X.meas α) (X.low θ) (X.st α θ) := by
  have hθpos : 0 < θ := by linarith
  cases X with
  | product c a =>
    obtain ⟨hc, ha, hsum⟩ := hX
    subst hsum
    exact product_target hPD hc ha hα1 hθpos hθ
  | riesz c => exact riesz_endpoints hIso hX hα1 hθpos hθ
  | plane c a =>
    obtain ⟨hc, ha, hs⟩ := hX
    obtain ⟨-, hcov, hpair, -⟩ := plane_endpoints_paper hPl hα₀ hα₀1 hα1 hα2 hθ0 hθ hc ha hs
    refine ⟨⟨hcov.1, hcov.2, ?_⟩, hpair⟩
    exact map_ne_zero_of_ne_zero (prodRieszMeasure_ne_zero hc a)
      planeEmb.continuous.measurable

/-- `C:three-finite-images` (main TeX lines 7991-8010; proof 8012-8035), with the
manuscript's hypotheses (`0 < α₀ < 1`, `1 < α < 2 - α₀`, admissible components, invertible
linear `T_i`, `w_i ≥ 0`, `Σ w_i > 0`), the supplied inputs and the midpoint `θ`: the target
`Γ = Σ w_i (T_i)_* Γ_i` is a nonzero covariance with measure scaling `3 - α`, the
constructed endpoints `Σ w_i (T_i)_* Γ_{low,i}`, `Σ w_i (T_i)_* Γ_{st,i}` satisfy
`H:three-endpoints`, and the conclusions of `P:three-transfer` hold for them.  NARROWER as
`three_product_riesz_paper`. -/
theorem three_finite_images_paper (hPD : RieszProductPD) (hIso : RieszIsoPD)
    (hPl : PlaneRieszPD) (Mdl : ThreeMomentModel) {α₀ α : ℝ}
    (hT : ThreeTransfer Mdl α₀ (midTheta α₀ α)) (hα₀ : 0 < α₀) (hα₀1 : α₀ < 1) (hα1 : 1 < α)
    (hα2 : α < 2 - α₀) {N : ℕ} (X : Fin N → Component) (hX : ∀ i, (X i).Valid α)
    (T : Fin N → Rd 3 ≃L[ℝ] Rd 3) {w : Fin N → ℝ} (hw : ∀ i, 0 ≤ w i)
    (hwpos : 0 < ∑ i, w i) :
    (IsCov (wsum w fun i => ((X i).meas α).map (T i)) ∧
      Scaling (wsum w fun i => ((X i).meas α).map (T i)) (3 - α) ∧
      (wsum w fun i => ((X i).meas α).map (T i)) ≠ 0) ∧
    EndpointPair (midTheta α₀ α) (chi α (midTheta α₀ α))
      (wsum w fun i => ((X i).meas α).map (T i))
      (wsum w fun i => ((X i).low (midTheta α₀ α)).map (T i))
      (wsum w fun i => ((X i).st α (midTheta α₀ α)).map (T i)) ∧
    TransferConclusion Mdl α₀ α (midTheta α₀ α)
      (wsum w fun i => ((X i).meas α).map (T i))
      (wsum w fun i => ((X i).low (midTheta α₀ α)).map (T i))
      (wsum w fun i => ((X i).st α (midTheta α₀ α)).map (T i)) := by
  set θ := midTheta α₀ α
  obtain ⟨hθ0, hθ⟩ := midTheta_mem hα2
  have h0 : 0 ≤ θ := by linarith
  have h1 : θ ≤ 1 := by linarith
  have hcomp := fun i => component_endpoints hPD hIso hPl hα₀ hα₀1 hα1 hα2 hθ0 hθ (hX i)
  have hmap := fun i => endpoint_closure_map h0 h1 (hcomp i).1.1 (hcomp i).2 (T i)
  obtain ⟨hpair, hcov, hsc⟩ := endpoint_closure_sum h0 h1 hw fun i => (hmap i).1
  have hcovΓ := hcov fun i => (hmap i).2.1
  have hscΓ := hsc (3 - α) fun i => (hmap i).2.2 _ (hcomp i).1.2.1
  obtain ⟨i, -, hi⟩ := Finset.exists_lt_of_sum_lt (s := Finset.univ) (f := fun _ => (0 : ℝ))
    (g := w) (by simpa using hwpos)
  have hne : (wsum w fun i => ((X i).meas α).map (T i)) ≠ 0 :=
    wsum_ne_zero hi (map_ne_zero_of_ne_zero (hcomp i).1.2.2 (T i).continuous.measurable)
  exact ⟨⟨hcovΓ, hscΓ, hne⟩, hpair,
    hT _ _ _ _ hα₀ hα₀1 hα1 hα2 hθ0 hθ hcovΓ hscΓ hne hpair⟩

end StratonovichHAMSecondMoment.EndpointCorollaries
