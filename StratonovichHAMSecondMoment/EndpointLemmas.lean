module

/-
Copyright 2026 Le Chen. SPDX-License-Identifier: Apache-2.0

The three dimension-three endpoint lemmas of Section `S:three-endpoints` of the main TeX
file `notes/notes_stratonovich_ham_second_moment.tex` at revision edf7085f (all line numbers
below are at edf7085f): `L:product-endpoints` (statement lines 7170-7204, proof 7206-7280),
`L:plane-endpoints` (statement 7316-7332, proof 7334-7415) and `L:endpoint-closure`
(statement 7418-7424, proof 7426-7495), with Hypothesis `H:three-endpoints` (lines
7296-7309) and the parameters `E:three-parameters` (lines 7282-7292).

Definitions (new):
* `hconv Γ ε z = ∫ p_ε(z - y) Γ(dy)`, the Gaussian convolution of a measure, as a lower
  Lebesgue integral (`p_ε = VariationalMean.heatK ε`, covariance `εI`); `hconv_lt_top`:
  finite for tempered `Γ`; for a density measure it is wave L10's
  `HigherRieszTwo.smoothCov` (`hconv_withDensity_eq_smoothCov`).
* `Scaling Γ s`: `Γ(rA) = r^s Γ(A)`; `IsCov Γ`: locally finite (Radon), even, tempered,
  positive definite, with the package's `HomogHypothesis` predicates (nonnegativity is
  automatic for a Lean measure).
* `GaussComparison θ Γ L S` is `E:three-gaussian-comparison` in `[0, ∞]`; `EndpointPair`
  and `ThreeEndpoints θ χ Γ` are `H:three-endpoints` (`L`, `S` covariances with scaling
  `2` and `3 - χ`, comparison for every `ε > 0`, `z`).  The TeX's inequality is between
  finite reals; the `[0, ∞]` form is equivalent for tempered measures (`hconv_lt_top`).
* `lowEnd`, `upEnd`, `lam`, `bVec`, `vVec`, `chi`: `E:product-endpoint-vectors` and `χ`.
* `prodRieszReal c e`, `prodRiesz`, `prodRieszMeasure`: `c ∏_j |x_j|^{-e_j}` on `ℝ^n`.
* `planeEmb` (`y ↦ (y, 0)`), `planeMeasure c e` (`c ∏_j |y_j|^{-e_j} dy δ₀(dz)`), `e3`,
  `lineE3` (`t ↦ t e₃`) and `planeLowSpectral c = (c/2π) δ₀ δ₀ dξ₃`.
* `wsum w μ = Σ_i w_i μ_i` (`w_i` real, entering as `ENNReal.ofReal`).

Formalized results:
* `product_endpoints_paper` (`L:product-endpoints`, all conclusions): the arithmetic
  (`0 < Λ < 1`, `Σ b = 1`, `Σ v = χ`, reconstruction, the sign/zero pattern, `α < χ < 2`);
  the three densities are even, locally integrable, tempered (locally finite measures), with
  measure scaling `3 - α`, `2`, `3 - χ`; positive definite by the supplied input; the
  comparison `E:product-gaussian-comparison`; hence an `EndpointPair`.
* `plane_endpoints_paper` (`L:plane-endpoints`, all conclusions): the exponent facts, the
  covariance properties and scalings of the three plane measures (positive definiteness by the
  supplied input), the comparison, `Γ_low = c m`, the spectral identity
  `IsSpectralMeasure (c m) μ_low` with `μ_low = (c/2π) δ₀ δ₀ dξ₃` (proved:
  projection-slice by Fubini and one-dimensional Fourier inversion, `planeLow_isSpectral`),
  `V_low = μ_low(closed unit ball) = μ_low(open unit ball) = c/π`, and `π V_low/2 = c/2`.
* `endpoint_closure_map`, `endpoint_closure_sum`, `endpoint_closure_paper`
  (`L:endpoint-closure`, all conclusions): invertible linear pushforward and finite
  nonnegative sums preserve the comparison and all covariance properties and scalings of the
  endpoints; the covariance target keeps its properties; zero weights and the all-zero
  target are included.  Nothing supplied.

Supplied inputs (named hypotheses, true statements, used only for positive definiteness):
* `RieszProductPD`: `c ∏_j |x_j|^{-e_j} dx` on `ℝ³` is positive definite for `c ≥ 0`,
  `0 ≤ e_j < 1` (the Gaussian-mixture argument of lines 7253-7266).
* `PlaneRieszPD`: `c ∏_j |y_j|^{-e_j} dy δ₀(dz)` is positive definite for `c ≥ 0`,
  `0 ≤ e_j < 1` (lines 7359-7384).
Class: the three lemmas are whole with these inputs supplied (inputs-supplied, whole), as
the plan's fallback names; `L:endpoint-closure` needs no input.

Hypotheses made explicit: the covariance target of `L:endpoint-closure` is assumed to be a
covariance (`IsCov Γ`, the section's standing assumption, lines 7282-7285) where its
covariance properties are concluded, and it is used (s-finiteness) for Tonelli in the
pushforward comparison.  Unused hypotheses carried by the `_paper` wrappers:
`α₀ < 1` and `α < 2 - α₀` (`plane_endpoints_paper`, `endpoint_closure_paper`).

Differences from the TeX's proof route (statements unchanged):
* `L:endpoint-closure`: instead of extending the comparison to every Gaussian `q_Σ` through
  `q_Σ = p_a * q_{Σ-aI}` (lines 7434-7451), the kernel `y ↦ p_ε(x - Ty)` is written as an
  isotropic heat mixture `∫ p_a(w - y) ρ(dw)` (`exists_heat_mixture`: spectral theorem for
  `T^*T`, the one-dimensional Gaussian convolution identity in each eigendirection); then
  Tonelli, the comparison at width `a` and Hölder on `ρ` (`comparison_of_mixture`).  No
  `|det T|` bookkeeping is needed for the comparison (it cancels inside the mixture).
* Hölder is used on the measure `p_ε(z - y) ν(dy)` itself (any measure, no normalization),
  and the discrete Hölder of the sums as Hölder on counting measure.
* The pointwise factorization `γ_a = γ_b^θ γ_v^{1-θ}` holds at every point with Lean's
  values (the TeX: almost everywhere).

Junk values: `|0|^{-e} = 0` for `e > 0` (the TeX density is infinite there) only on
Lebesgue-null coordinate planes against which nothing is integrated except through
`withDensity`; `|t|^0 = 1` is the TeX's "zero exponent means one".  `ENNReal.ofReal` clamps
negative amplitudes and weights to `0`; every manuscript statement carries `c > 0` or
`w_i ≥ 0`.  Lemmas marked "Auxiliary to the Lean proof route" have no manuscript label.
-/

public import Mathlib
public import StratonovichHAMSecondMoment.HomogHypothesis
public import StratonovichHAMSecondMoment.VariationalMean
public import StratonovichHAMSecondMoment.HigherRieszTwo
public import StratonovichHAMSecondMoment.LowAlphaConvolution

@[expose] public section

noncomputable section

set_option autoImplicit false

open MeasureTheory Set Real Metric Filter
open scoped ENNReal NNReal Pointwise Topology FourierTransform InnerProductSpace

namespace StratonovichHAMSecondMoment.EndpointLemmas

open HomogHypothesis (Rd IsTempered IsEven IsPosDefDistr IsSpectralMeasure)
open VariationalMean (heatK heatK_pos)

variable {n : ℕ}

/-! ### Definitions: covariance measures and the endpoint hypothesis -/

/-- The Gaussian convolution of a measure, `(p_ε * Γ)(z) = ∫ p_ε(z - y) Γ(dy)` (main TeX
lines 7198-7202, 7304-7308), as a lower Lebesgue integral in `[0, ∞]` (never a junk value);
`hconv_lt_top` shows it is finite for a tempered `Γ` and `ε > 0`. -/
def hconv (Γ : Measure (Rd n)) (ε : ℝ) (z : Rd n) : ℝ≥0∞ :=
  ∫⁻ y, ENNReal.ofReal (heatK ε (z - y)) ∂Γ

/-- Measure scaling with exponent `s`: `Γ(rA) = r^s Γ(A)` for Borel `A` and `r > 0` (the
form of `H:homog`; a covariance of homogeneity exponent `e` on `ℝ^n` has `s = n - e`). -/
def Scaling (Γ : Measure (Rd n)) (s : ℝ) : Prop :=
  ∀ A : Set (Rd n), MeasurableSet A → ∀ r : ℝ, 0 < r →
    Γ (r • A) = ENNReal.ofReal (r ^ s) * Γ A

/-- A covariance measure in the sense of `H:three-endpoints` (main TeX lines 7296-7299): a
nonnegative (every Lean measure is), even, positive-definite, tempered Radon measure. -/
structure IsCov (Γ : Measure (Rd n)) : Prop where
  radon : IsLocallyFiniteMeasure Γ
  even : IsEven Γ
  tempered : IsTempered Γ
  posdef : IsPosDefDistr Γ

/-- The common-width Gaussian comparison `E:three-gaussian-comparison` (main TeX lines
7304-7308): `(p_ε * Γ)(z) ≤ (p_ε * L)(z)^θ (p_ε * S)(z)^{1-θ}` for every `ε > 0` and `z`. -/
def GaussComparison (θ : ℝ) (Γ L S : Measure (Rd n)) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ z : Rd n, hconv Γ ε z ≤ hconv L ε z ^ θ * hconv S ε z ^ (1 - θ)

/-- An endpoint pair for the target `Γ` (Hypothesis `H:three-endpoints`, main TeX lines
7296-7309): `Γ_low` and `Γ_st` are covariance measures on `ℝ³` with measure scaling
`Γ_low(rA) = r² Γ_low(A)`, `Γ_st(rA) = r^{3-χ} Γ_st(A)`, and the comparison holds. -/
structure EndpointPair (θ χ : ℝ) (Γ L S : Measure (Rd 3)) : Prop where
  low : IsCov L
  st : IsCov S
  low_scaling : Scaling L 2
  st_scaling : Scaling S (3 - χ)
  comparison : GaussComparison θ Γ L S

/-- Hypothesis `H:three-endpoints` (main TeX lines 7296-7309) for the target `Γ` and the
fixed parameters `θ, χ`: some endpoint pair exists. -/
def ThreeEndpoints (θ χ : ℝ) (Γ : Measure (Rd 3)) : Prop :=
  ∃ L S : Measure (Rd 3), EndpointPair θ χ Γ L S

/-! ### Elementary facts about Gaussian convolution -/

/-- Auxiliary to the Lean proof route: `p_ε` depends only on the norm. -/
theorem heatK_congr_norm {ε : ℝ} {x y : Rd n} (h : ‖x‖ = ‖y‖) : heatK ε x = heatK ε y := by
  unfold heatK; rw [h]

/-- Auxiliary to the Lean proof route: `p_ε(-x) = p_ε(x)`. -/
theorem heatK_neg (ε : ℝ) (x : Rd n) : heatK ε (-x) = heatK ε x :=
  heatK_congr_norm (norm_neg x)

/-- Auxiliary to the Lean proof route: `p_ε` is measurable. -/
theorem measurable_heatK (ε : ℝ) : Measurable (heatK ε : Rd n → ℝ) := by
  unfold heatK; fun_prop

/-- For a tempered `Γ` and `ε > 0`, `(p_ε * Γ)(z)` is finite (main TeX line 7450: "Every
convolution here is finite"). -/
theorem hconv_lt_top {Γ : Measure (Rd n)} (hΓ : IsTempered Γ) {ε : ℝ} (hε : 0 < ε)
    (z : Rd n) : hconv Γ ε z < ⊤ := by
  have h : Integrable (fun y => heatK ε (z - y)) Γ :=
    LowAlphaConvolution.integrable_heatDens hΓ hε z
  have hfi := h.hasFiniteIntegral
  rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun y =>
    (heatK_pos hε (z - y)).le)] at hfi
  exact hfi

/-! ### Hölder's inequality for a pointwise geometric-mean bound -/

/-- Auxiliary to the Lean proof route: `k = k^θ k^{1-θ}` in `[0, ∞]` for `0 ≤ θ ≤ 1`. -/
theorem rpow_mul_rpow_one_sub (k : ℝ≥0∞) {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    k ^ θ * k ^ (1 - θ) = k := by
  rw [← ENNReal.rpow_add_of_nonneg _ _ h0 (by linarith), add_sub_cancel, ENNReal.rpow_one]

/-- Hölder's inequality on the measure `k ν` (the step "Hölder's inequality on the Gaussian
probability measure", main TeX lines 7275-7277, 7388-7399, 7441-7449): if
`f ≤ g^θ h^{1-θ}` pointwise, then `∫ k f dν ≤ (∫ k g dν)^θ (∫ k h dν)^{1-θ}`.  Any measure
`ν` and weight `k`, no normalization. -/
theorem lintegral_holder_of_le {X : Type*} [MeasurableSpace X] {ν : Measure X}
    {k f g h : X → ℝ≥0∞} (hk : AEMeasurable k ν) (hg : AEMeasurable g ν)
    (hh : AEMeasurable h ν) {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1)
    (hle : ∀ x, f x ≤ g x ^ θ * h x ^ (1 - θ)) :
    ∫⁻ x, k x * f x ∂ν ≤ (∫⁻ x, k x * g x ∂ν) ^ θ * (∫⁻ x, k x * h x ∂ν) ^ (1 - θ) := by
  calc ∫⁻ x, k x * f x ∂ν ≤ ∫⁻ x, (k x * g x) ^ θ * (k x * h x) ^ (1 - θ) ∂ν := by
        refine lintegral_mono fun x => ?_
        rw [ENNReal.mul_rpow_of_nonneg _ _ h0, ENNReal.mul_rpow_of_nonneg _ _ (by linarith)]
        calc k x * f x ≤ k x * (g x ^ θ * h x ^ (1 - θ)) := by gcongr; exact hle x
          _ = (k x ^ θ * k x ^ (1 - θ)) * (g x ^ θ * h x ^ (1 - θ)) := by
              rw [rpow_mul_rpow_one_sub _ h0 h1]
          _ = k x ^ θ * g x ^ θ * (k x ^ (1 - θ) * h x ^ (1 - θ)) := by ring
    _ ≤ _ := ENNReal.lintegral_mul_norm_pow_le (hk.mul hg) (hk.mul hh) h0 (by linarith)
        (by ring)

/-- The comparison for densities against a common measure `ν` pushed into `ℝ^n` by a
measurable map `ι` (covers ordinary densities, `ι = id`, and plane-supported densities):
if `f ≤ g^θ h^{1-θ}` pointwise, the three measures `ι_*(f ν)`, `ι_*(g ν)`, `ι_*(h ν)`
satisfy the common-width Gaussian comparison. -/
theorem gaussComparison_map_withDensity {m : ℕ} {ν : Measure (Rd m)} {ι : Rd m → Rd n}
    (hι : Measurable ι) {f g h : Rd m → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g)
    (hh : Measurable h) {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1)
    (hle : ∀ x, f x ≤ g x ^ θ * h x ^ (1 - θ)) :
    GaussComparison θ ((ν.withDensity f).map ι) ((ν.withDensity g).map ι)
      ((ν.withDensity h).map ι) := by
  intro ε _ z
  have hk : Measurable fun y : Rd m => ENNReal.ofReal (heatK ε (z - ι y)) :=
    ((measurable_heatK ε).comp (measurable_const.sub hι)).ennreal_ofReal
  have hk' : Measurable fun y : Rd n => ENNReal.ofReal (heatK ε (z - y)) :=
    ((measurable_heatK ε).comp (measurable_const.sub measurable_id)).ennreal_ofReal
  simp only [hconv]
  rw [lintegral_map hk' hι, lintegral_map hk' hι, lintegral_map hk' hι,
    lintegral_withDensity_eq_lintegral_mul _ hf hk, lintegral_withDensity_eq_lintegral_mul _ hg hk,
    lintegral_withDensity_eq_lintegral_mul _ hh hk]
  simp only [Pi.mul_apply]
  simp_rw [mul_comm (f _), mul_comm (g _), mul_comm (h _)]
  exact lintegral_holder_of_le hk.aemeasurable hg.aemeasurable hh.aemeasurable h0 h1 hle

/-! ### `L:product-endpoints`: the endpoint arithmetic -/

/-- `L_j = max{0, (a_j - 1 + θ)/θ}` (`E:product-endpoint-vectors`, main TeX line 7176). -/
def lowEnd (θ : ℝ) (a : Fin 3 → ℝ) (j : Fin 3) : ℝ := max 0 ((a j - 1 + θ) / θ)

/-- `U_j = min{1, a_j/θ}` (main TeX line 7177). -/
def upEnd (θ : ℝ) (a : Fin 3 → ℝ) (j : Fin 3) : ℝ := min 1 (a j / θ)

/-- `Λ = (1 - Σ L_j)/(Σ U_j - Σ L_j)` (main TeX line 7178). -/
def lam (θ : ℝ) (a : Fin 3 → ℝ) : ℝ :=
  (1 - ∑ j, lowEnd θ a j) / (∑ j, upEnd θ a j - ∑ j, lowEnd θ a j)

/-- `b_j = L_j + Λ(U_j - L_j)` (main TeX line 7179). -/
def bVec (θ : ℝ) (a : Fin 3 → ℝ) (j : Fin 3) : ℝ :=
  lowEnd θ a j + lam θ a * (upEnd θ a j - lowEnd θ a j)

/-- `v_j = (a_j - θ b_j)/(1 - θ)` (main TeX line 7180). -/
def vVec (θ : ℝ) (a : Fin 3 → ℝ) (j : Fin 3) : ℝ := (a j - θ * bVec θ a j) / (1 - θ)

/-- `χ = (α - θ)/(1 - θ)` (main TeX lines 7172-7173, 7291). -/
def chi (α θ : ℝ) : ℝ := (α - θ) / (1 - θ)

/-- Auxiliary to the Lean proof route: `θ L_j = max{0, a_j - 1 + θ}`. -/
theorem mul_lowEnd {θ : ℝ} (hθ : 0 < θ) (a : Fin 3 → ℝ) (j : Fin 3) :
    θ * lowEnd θ a j = max 0 (a j - 1 + θ) := by
  rw [lowEnd, mul_max_of_nonneg _ _ hθ.le, mul_zero, mul_div_cancel₀ _ hθ.ne']

/-- Auxiliary to the Lean proof route: `θ U_j = min{θ, a_j}`. -/
theorem mul_upEnd {θ : ℝ} (hθ : 0 < θ) (a : Fin 3 → ℝ) (j : Fin 3) :
    θ * upEnd θ a j = min θ (a j) := by
  rw [upEnd, mul_min_of_nonneg _ _ hθ.le, mul_one, mul_div_cancel₀ _ hθ.ne']

/-- The standing parameter conditions of `L:product-endpoints` (main TeX lines 7171-7173):
`0 ≤ a_j < 1`, `α = Σ a_j ∈ (1,2)`, `0 < θ < 2 - α`. -/
structure ProductParams (a : Fin 3 → ℝ) (θ : ℝ) : Prop where
  nonneg : ∀ j, 0 ≤ a j
  lt_one : ∀ j, a j < 1
  one_lt : 1 < ∑ j, a j
  lt_two : ∑ j, a j < 2
  θ_pos : 0 < θ
  θ_lt : θ < 2 - ∑ j, a j

/-- Auxiliary to the Lean proof route: `θ Σ L_j < θ` (the case analysis of main TeX lines
7220-7233, as one disjunction over the signs of `a_j - 1 + θ`). -/
theorem sum_lowEnd_lt {a : Fin 3 → ℝ} {θ : ℝ} (hp : ProductParams a θ) :
    ∑ j, lowEnd θ a j < 1 := by
  have hθ := hp.θ_pos
  have key : θ * ∑ j, lowEnd θ a j < θ * 1 := by
    rw [Finset.mul_sum, Fin.sum_univ_three, mul_lowEnd hθ, mul_lowEnd hθ, mul_lowEnd hθ, mul_one]
    have h0 := hp.nonneg 0; have h1 := hp.nonneg 1; have h2 := hp.nonneg 2
    have l0 := hp.lt_one 0; have l1 := hp.lt_one 1; have l2 := hp.lt_one 2
    have hlt := hp.θ_lt
    have hθ1 : θ < 1 := by have := hp.one_lt; linarith
    rw [Fin.sum_univ_three] at hlt
    rcases le_total 0 (a 0 - 1 + θ) with c0 | c0 <;>
    rcases le_total 0 (a 1 - 1 + θ) with c1 | c1 <;>
    rcases le_total 0 (a 2 - 1 + θ) with c2 | c2 <;>
    simp only [max_eq_left, max_eq_right, c0, c1, c2] <;> linarith
  exact lt_of_mul_lt_mul_left key hθ.le

/-- Auxiliary to the Lean proof route: `1 < Σ U_j` (main TeX lines 7233-7235). -/
theorem one_lt_sum_upEnd {a : Fin 3 → ℝ} {θ : ℝ} (hp : ProductParams a θ) :
    1 < ∑ j, upEnd θ a j := by
  have hθ := hp.θ_pos
  have key : θ * 1 < θ * ∑ j, upEnd θ a j := by
    rw [Finset.mul_sum, Fin.sum_univ_three, mul_upEnd hθ, mul_upEnd hθ, mul_upEnd hθ, mul_one]
    have h0 := hp.nonneg 0; have h1 := hp.nonneg 1; have h2 := hp.nonneg 2
    have l0 := hp.lt_one 0; have l1 := hp.lt_one 1; have l2 := hp.lt_one 2
    have hlt := hp.θ_lt; have hgt := hp.one_lt
    rw [Fin.sum_univ_three] at hlt hgt
    rcases le_total θ (a 0) with c0 | c0 <;>
    rcases le_total θ (a 1) with c1 | c1 <;>
    rcases le_total θ (a 2) with c2 | c2 <;>
    simp only [min_eq_left, min_eq_right, c0, c1, c2] <;> linarith
  exact lt_of_mul_lt_mul_left key hθ.le

/-- Auxiliary to the Lean proof route: at a positive coordinate `L_j < U_j`
(main TeX lines 7216-7220). -/
theorem lowEnd_lt_upEnd {a : Fin 3 → ℝ} {θ : ℝ} (hp : ProductParams a θ) {j : Fin 3}
    (hj : 0 < a j) : lowEnd θ a j < upEnd θ a j := by
  have hθ := hp.θ_pos
  have hθ1 : θ < 1 := by
    have := hp.θ_lt; have := hp.one_lt; linarith
  have key : θ * lowEnd θ a j < θ * upEnd θ a j := by
    rw [mul_lowEnd hθ, mul_upEnd hθ]
    have := hp.lt_one j
    exact max_lt (lt_min hθ hj) (lt_min (by linarith) (by linarith))
  exact lt_of_mul_lt_mul_left key hθ.le

/-- Auxiliary to the Lean proof route: at a zero coordinate `L_j = U_j = 0`
(main TeX line 7216). -/
theorem lowEnd_upEnd_of_zero {a : Fin 3 → ℝ} {θ : ℝ} (hp : ProductParams a θ) {j : Fin 3}
    (hj : a j = 0) : lowEnd θ a j = 0 ∧ upEnd θ a j = 0 := by
  have hθ := hp.θ_pos
  have hθ1 : θ < 1 := by
    have := hp.θ_lt; have := hp.one_lt; linarith
  constructor
  · have : θ * lowEnd θ a j = 0 := by
      rw [mul_lowEnd hθ, hj]; exact max_eq_left (by linarith)
    exact (mul_eq_zero.1 this).resolve_left hθ.ne'
  · have : θ * upEnd θ a j = 0 := by
      rw [mul_upEnd hθ, hj]; exact min_eq_right hθ.le
    exact (mul_eq_zero.1 this).resolve_left hθ.ne'

/-- The endpoint arithmetic of `L:product-endpoints` (main TeX lines 7183-7187; proof lines
7215-7244): `0 < Λ < 1`, `Σ b_j = 1`, `Σ v_j = χ`, `a_j = θ b_j + (1-θ) v_j`,
`a_j > 0 ⇒ 0 < b_j, v_j < 1`, `a_j = 0 ⇒ b_j = v_j = 0`, and `α < χ < 2`. -/
theorem product_arithmetic {a : Fin 3 → ℝ} {θ : ℝ} (hp : ProductParams a θ) :
    (0 < lam θ a ∧ lam θ a < 1) ∧ ∑ j, bVec θ a j = 1 ∧
      ∑ j, vVec θ a j = chi (∑ j, a j) θ ∧
      (∀ j, a j = θ * bVec θ a j + (1 - θ) * vVec θ a j) ∧
      (∀ j, 0 < a j → (0 < bVec θ a j ∧ bVec θ a j < 1) ∧
        (0 < vVec θ a j ∧ vVec θ a j < 1)) ∧
      (∀ j, a j = 0 → bVec θ a j = 0 ∧ vVec θ a j = 0) ∧
      (∑ j, a j < chi (∑ j, a j) θ ∧ chi (∑ j, a j) θ < 2) := by
  have hθ := hp.θ_pos
  have hθ1 : θ < 1 := by
    have := hp.θ_lt; have := hp.one_lt; linarith
  have h1θ : 0 < 1 - θ := by linarith
  have hL := sum_lowEnd_lt hp
  have hU := one_lt_sum_upEnd hp
  have hden : 0 < ∑ j, upEnd θ a j - ∑ j, lowEnd θ a j := by linarith
  have hΛ0 : 0 < lam θ a := div_pos (by linarith) hden
  have hΛ1 : lam θ a < 1 := (div_lt_one hden).2 (by linarith)
  have hb : ∑ j, bVec θ a j = 1 := by
    simp only [bVec]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib, lam,
      div_mul_cancel₀ _ hden.ne']
    ring
  have hrec : ∀ j, a j = θ * bVec θ a j + (1 - θ) * vVec θ a j := by
    intro j; simp only [vVec]; field_simp; ring
  refine ⟨⟨hΛ0, hΛ1⟩, hb, ?_, hrec, ?_, ?_, ?_⟩
  · simp only [vVec, chi]
    rw [← Finset.sum_div, Finset.sum_sub_distrib, ← Finset.mul_sum, hb, mul_one]
  · intro j hj
    have hLU := lowEnd_lt_upEnd hp hj
    have hLb : lowEnd θ a j < bVec θ a j := by
      simp only [bVec]; nlinarith
    have hbU : bVec θ a j < upEnd θ a j := by
      simp only [bVec]; nlinarith
    have hL0 : 0 ≤ lowEnd θ a j := le_max_left _ _
    have hU1 : upEnd θ a j ≤ 1 := min_le_left _ _
    have hθU : θ * upEnd θ a j ≤ a j := by rw [mul_upEnd hθ]; exact min_le_right _ _
    have hθL : a j - 1 + θ ≤ θ * lowEnd θ a j := by rw [mul_lowEnd hθ]; exact le_max_right _ _
    refine ⟨⟨by linarith, by linarith⟩, ?_, ?_⟩
    · simp only [vVec]; apply div_pos _ h1θ; nlinarith
    · simp only [vVec]; rw [div_lt_one h1θ]; nlinarith
  · intro j hj
    obtain ⟨hl, hu⟩ := lowEnd_upEnd_of_zero hp hj
    have hb0 : bVec θ a j = 0 := by simp only [bVec, hl, hu]; ring
    refine ⟨hb0, ?_⟩
    simp only [vVec, hb0, hj]; ring
  · have hα1 := hp.one_lt; have hα2 := hp.θ_lt
    constructor
    · rw [chi, lt_div_iff₀ h1θ]; nlinarith
    · rw [chi, div_lt_iff₀ h1θ]; linarith

/-! ### Covariance properties of densities: generic facts -/

/-- Auxiliary to the Lean proof route: a tempered measure on `ℝ^n` is locally finite
(a positive tempered distribution is a Radon measure, main TeX lines 7284-7285). -/
theorem isLocallyFiniteMeasure_of_tempered {ν : Measure (Rd n)} (hν : IsTempered ν) :
    IsLocallyFiniteMeasure ν := by
  obtain ⟨k, hk⟩ := hν
  refine ⟨fun x => ⟨ball x 1, ball_mem_nhds x one_pos, ?_⟩⟩
  set C : ℝ := (2 + ‖x‖) ^ (-(k : ℝ))
  have hC : 0 < C := by positivity
  have hle : ∀ y ∈ ball x 1, ENNReal.ofReal C ≤ ENNReal.ofReal ((1 + ‖y‖) ^ (-(k : ℝ))) := by
    intro y hy
    refine ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_nonpos (by positivity) ?_
      (by simp))
    have : ‖y‖ ≤ ‖x‖ + 1 := by
      have := norm_le_norm_add_norm_sub' y x
      rw [mem_ball, dist_eq_norm] at hy; linarith
    linarith
  have hint : ENNReal.ofReal C * ν (ball x 1) < ⊤ := by
    calc ENNReal.ofReal C * ν (ball x 1) = ∫⁻ _ in ball x 1, ENNReal.ofReal C ∂ν := by
          rw [setLIntegral_const, mul_comm]
      _ ≤ ∫⁻ y in ball x 1, ENNReal.ofReal ((1 + ‖y‖) ^ (-(k : ℝ))) ∂ν :=
          setLIntegral_mono (by fun_prop) hle
      _ ≤ ∫⁻ y, ENNReal.ofReal ((1 + ‖y‖) ^ (-(k : ℝ))) ∂ν := setLIntegral_le_lintegral _ _
      _ < ⊤ := hk
  exact ENNReal.lt_top_of_mul_ne_top_right hint.ne (ENNReal.ofReal_pos.2 hC).ne'

/-- Auxiliary to the Lean proof route: an even density gives an even measure. -/
theorem isEven_withDensity {f : Rd n → ℝ≥0∞} (hf : Measurable f) (he : ∀ x, f (-x) = f x) :
    IsEven ((volume : Measure (Rd n)).withDensity f) := by
  unfold IsEven
  ext s hs
  rw [Measure.map_apply measurable_neg hs, withDensity_apply _ (measurable_neg hs),
    withDensity_apply _ hs]
  have hmp : MeasurePreserving (fun x : Rd n => -x) volume volume :=
    Measure.measurePreserving_neg _
  rw [← hmp.setLIntegral_comp_preimage hs hf]
  simp only [he]

/-- Auxiliary to the Lean proof route: a density homogeneous of degree `-s`,
`f(rx) = r^{-s} f(x)`, gives a measure with scaling exponent `n - s`. -/
theorem scaling_withDensity {f : Rd n → ℝ≥0∞} (hf : Measurable f) {s : ℝ}
    (hhom : ∀ r : ℝ, 0 < r → ∀ x, f (r • x) = ENNReal.ofReal (r ^ (-s)) * f x) :
    Scaling ((volume : Measure (Rd n)).withDensity f) (n - s) := by
  intro A hA r hr
  have hrA : MeasurableSet (r • A) := hA.const_smul₀ r
  rw [withDensity_apply _ hrA, withDensity_apply _ hA]
  have hmap := Measure.map_addHaar_smul (μ := (volume : Measure (Rd n))) hr.ne'
  rw [finrank_euclideanSpace_fin] at hmap
  have hgm : Measurable ((r • A).indicator f) := hf.indicator hrA
  have key : ∫⁻ x, (r • A).indicator f (r • x) =
      ENNReal.ofReal |(r ^ n)⁻¹| * ∫⁻ x in r • A, f x := by
    rw [← lintegral_map hgm (measurable_const_smul r), hmap, lintegral_smul_measure,
      lintegral_indicator hrA, smul_eq_mul]
  have hind : ∀ x, (r • A).indicator f (r • x) =
      A.indicator (fun x => ENNReal.ofReal (r ^ (-s)) * f x) x := by
    intro x
    by_cases hx : x ∈ A
    · rw [indicator_of_mem hx, indicator_of_mem ((smul_mem_smul_set_iff₀ hr.ne' A x).2 hx),
        hhom r hr]
    · rw [indicator_of_notMem hx, indicator_of_notMem (fun h =>
        hx ((smul_mem_smul_set_iff₀ hr.ne' A x).1 h))]
  simp_rw [hind] at key
  rw [lintegral_indicator hA, lintegral_const_mul _ hf] at key
  have hrn : 0 < r ^ n := pow_pos hr n
  rw [abs_of_pos (inv_pos.2 hrn)] at key
  have hinv : ENNReal.ofReal (r ^ n) * ENNReal.ofReal (r ^ n)⁻¹ = 1 := by
    rw [← ENNReal.ofReal_mul hrn.le, mul_inv_cancel₀ hrn.ne', ENNReal.ofReal_one]
  calc ∫⁻ x in r • A, f x
      = ENNReal.ofReal (r ^ n) * (ENNReal.ofReal (r ^ n)⁻¹ * ∫⁻ x in r • A, f x) := by
        rw [← mul_assoc, hinv, one_mul]
    _ = ENNReal.ofReal (r ^ n) * (ENNReal.ofReal (r ^ (-s)) * ∫⁻ x in A, f x) := by rw [key]
    _ = ENNReal.ofReal (r ^ ((n : ℝ) - s)) * ∫⁻ x in A, f x := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul hrn.le, sub_eq_add_neg,
          Real.rpow_add hr, Real.rpow_natCast]

/-- Auxiliary to the Lean proof route: a nonnegative measurable function whose density measure
is locally finite is locally integrable. -/
theorem locallyIntegrable_of_withDensity {f : Rd n → ℝ} (hf : Measurable f) (h0 : ∀ x, 0 ≤ f x)
    (hlf : IsLocallyFiniteMeasure ((volume : Measure (Rd n)).withDensity
      fun x => ENNReal.ofReal (f x))) : LocallyIntegrable f := by
  intro x
  obtain ⟨U, hU, hfin⟩ := hlf.finiteAtNhds x
  refine ⟨U, hU, ⟨hf.aestronglyMeasurable, ?_⟩⟩
  rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall h0)]
  rw [withDensity_apply'] at hfin
  exact hfin

/-! ### Product Riesz densities -/

/-- The product density `γ_e(x) = c ∏_j |x_j|^{-e_j}` (main TeX lines 7188-7195), real-valued.
At a point with `x_j = 0` and `e_j > 0` Lean's real power gives `0^{-e_j} = 0` (the TeX
density is infinite there); the coordinate planes are Lebesgue-null and the density is only
integrated against Lebesgue measure.  A zero exponent gives the factor `|x_j|^0 = 1`
everywhere, as the TeX prescribes (main TeX line 7203). -/
def prodRieszReal (c : ℝ) (e : Fin n → ℝ) (x : Rd n) : ℝ := c * ∏ j, |x j| ^ (-e j)

/-- The product density as an `ℝ≥0∞`-valued function. -/
def prodRiesz (c : ℝ) (e : Fin n → ℝ) (x : Rd n) : ℝ≥0∞ := ENNReal.ofReal (prodRieszReal c e x)

/-- The covariance measure `γ_e(x) dx` of the product density. -/
def prodRieszMeasure (c : ℝ) (e : Fin n → ℝ) : Measure (Rd n) :=
  (volume : Measure (Rd n)).withDensity (prodRiesz c e)

/-- Auxiliary to the Lean proof route. -/
theorem measurable_prodRieszReal (c : ℝ) (e : Fin n → ℝ) : Measurable (prodRieszReal c e) := by
  unfold prodRieszReal
  refine measurable_const.mul (Finset.measurable_prod _ fun j _ => ?_)
  exact ((EuclideanSpace.proj j).continuous.measurable.abs).pow_const _

/-- Auxiliary to the Lean proof route. -/
theorem measurable_prodRiesz (c : ℝ) (e : Fin n → ℝ) : Measurable (prodRiesz c e) :=
  (measurable_prodRieszReal c e).ennreal_ofReal

/-- Auxiliary to the Lean proof route. -/
theorem prodRieszReal_nonneg {c : ℝ} (hc : 0 ≤ c) (e : Fin n → ℝ) (x : Rd n) :
    0 ≤ prodRieszReal c e x :=
  mul_nonneg hc (Finset.prod_nonneg fun _ _ => Real.rpow_nonneg (abs_nonneg _) _)

/-- The product density is even. -/
theorem prodRiesz_neg (c : ℝ) (e : Fin n → ℝ) (x : Rd n) :
    prodRiesz c e (-x) = prodRiesz c e x := by
  simp [prodRiesz, prodRieszReal, abs_neg]

/-- The product density is homogeneous of degree `-Σ e_j`: `γ_e(rx) = r^{-Σe} γ_e(x)`. -/
theorem prodRiesz_smul (c : ℝ) (e : Fin n → ℝ) {r : ℝ} (hr : 0 < r) (x : Rd n) :
    prodRiesz c e (r • x) = ENNReal.ofReal (r ^ (-∑ j, e j)) * prodRiesz c e x := by
  unfold prodRiesz prodRieszReal
  rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hr.le _)]
  congr 1
  have h : ∀ j, |(r • x) j| ^ (-e j) = r ^ (-e j) * |x j| ^ (-e j) := by
    intro j
    rw [PiLp.smul_apply, smul_eq_mul, abs_mul, abs_of_pos hr,
      Real.mul_rpow hr.le (abs_nonneg _)]
  simp_rw [h]
  rw [Finset.prod_mul_distrib, ← Real.rpow_sum_of_pos hr, Finset.sum_neg_distrib]
  ring

/-- Auxiliary to the Lean proof route: the one-dimensional integrability behind local
integrability and temperedness (main TeX lines 7245-7253): for `0 ≤ e < 1`,
`t ↦ |t|^{-e} (1+|t|)^{-2}` is integrable on `ℝ`. -/
theorem integrable_abs_rpow_mul {e : ℝ} (he0 : 0 ≤ e) (he1 : e < 1) :
    Integrable fun t : ℝ => |t| ^ (-e) * (1 + |t|) ^ (-(2 : ℝ)) := by
  set g : ℝ → ℝ := fun t => |t| ^ (-e) * (1 + |t|) ^ (-(2 : ℝ))
  have hgm : Measurable g := by fun_prop
  have hg0 : ∀ t, 0 ≤ g t := fun t => by positivity
  have hq : ∀ t : ℝ, (1 + |t|) ^ (-(2 : ℝ)) ≤ 1 :=
    fun t => Real.rpow_le_one_of_one_le_of_nonpos (by linarith [abs_nonneg t]) (by norm_num)
  have hb : IntegrableOn g (ball 0 1) := by
    refine integrableOn_ball_of_norm_le_rpow (C := 1) (α := e) (by simp) (by simpa using he1)
      (Eventually.of_forall fun t => ?_) hgm.aestronglyMeasurable
    rw [Real.norm_eq_abs, abs_of_nonneg (hg0 t), one_mul, Real.norm_eq_abs]
    have := Real.rpow_nonneg (abs_nonneg t) (-e)
    change |t| ^ (-e) * (1 + |t|) ^ (-(2 : ℝ)) ≤ _
    calc |t| ^ (-e) * (1 + |t|) ^ (-(2 : ℝ)) ≤ |t| ^ (-e) * 1 := by gcongr; exact hq t
      _ = _ := mul_one _
  have hc : IntegrableOn g (ball 0 1)ᶜ := by
    have hI : Integrable (fun t : ℝ => (1 + ‖t‖) ^ (-(2 : ℝ))) :=
      integrable_one_add_norm (by simp)
    refine hI.integrableOn.mono' hgm.aestronglyMeasurable
      ((ae_restrict_iff' measurableSet_ball.compl).2 (Eventually.of_forall fun t ht => ?_))
    have ht1 : 1 ≤ |t| := by simpa [Real.norm_eq_abs] using ht
    rw [Real.norm_eq_abs, abs_of_nonneg (hg0 t), Real.norm_eq_abs]
    have : |t| ^ (-e) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos ht1 (by linarith)
    change |t| ^ (-e) * (1 + |t|) ^ (-(2 : ℝ)) ≤ _
    calc |t| ^ (-e) * (1 + |t|) ^ (-(2 : ℝ)) ≤ 1 * (1 + |t|) ^ (-(2 : ℝ)) := by gcongr
      _ = _ := one_mul _
  have := hb.union hc
  rwa [union_compl_self, integrableOn_univ] at this

/-- Auxiliary to the Lean proof route: integrability on `ℝ^n` of a product of integrable
one-dimensional functions of the coordinates. -/
theorem integrable_prod_coord {g : Fin n → ℝ → ℝ} (hg : ∀ j, Integrable (g j)) :
    Integrable fun x : Rd n => ∏ j, g j (x j) := by
  have hpi : Integrable fun y : Fin n → ℝ => ∏ j, g j (y j) :=
    Integrable.fintype_prod (f := g) hg
  have hmp := EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin n)
  exact (hmp.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _)).2 hpi

/-- Temperedness of the product density (main TeX lines 7245-7253): for `c ≥ 0` and
`0 ≤ e_j < 1`, `∫ (1+|x|)^{-2n} γ_e(x) dx < ∞`. -/
theorem prodRieszMeasure_tempered {c : ℝ} (hc : 0 ≤ c) {e : Fin n → ℝ}
    (he : ∀ j, 0 ≤ e j ∧ e j < 1) : IsTempered (prodRieszMeasure c e) := by
  refine ⟨2 * n, ?_⟩
  set g : Fin n → ℝ → ℝ := fun j t => |t| ^ (-e j) * (1 + |t|) ^ (-(2 : ℝ))
  have hI : Integrable fun x : Rd n => c * ∏ j, g j (x j) :=
    (integrable_prod_coord fun j => integrable_abs_rpow_mul (he j).1 (he j).2).const_mul c
  have hmk : Measurable fun x : Rd n => ENNReal.ofReal ((1 + ‖x‖) ^ (-((2 * n : ℕ) : ℝ))) := by
    fun_prop
  rw [prodRieszMeasure, lintegral_withDensity_eq_lintegral_mul _ (measurable_prodRiesz c e) hmk]
  refine lt_of_le_of_lt (lintegral_mono fun x => ?_) hI.lintegral_lt_top
  simp only [Pi.mul_apply, prodRiesz]
  rw [← ENNReal.ofReal_mul (prodRieszReal_nonneg hc e x)]
  refine ENNReal.ofReal_le_ofReal ?_
  simp only [prodRieszReal, g, Finset.prod_mul_distrib]
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (Finset.prod_nonneg
    fun j _ => Real.rpow_nonneg (abs_nonneg _) _)) hc
  have hpow : (1 + ‖x‖) ^ (-((2 * n : ℕ) : ℝ)) = ∏ _j : Fin n, (1 + ‖x‖) ^ (-(2 : ℝ)) := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← Real.rpow_natCast,
      ← Real.rpow_mul (by positivity)]
    congr 1; push_cast; ring
  rw [hpow]
  refine Finset.prod_le_prod₀ (fun j _ => by positivity) fun j _ => ?_
  refine Real.rpow_le_rpow_of_nonpos (by positivity) ?_ (by norm_num)
  have := PiLp.norm_apply_le x j
  rw [Real.norm_eq_abs] at this
  linarith

/-- The covariance properties of the product density other than positive definiteness
(main TeX lines 7195-7197, 7245-7266): for `c ≥ 0` and `0 ≤ e_j < 1`, the measure
`γ_e(x) dx` is even, tempered and locally finite, its density is locally integrable, and
it has measure scaling exponent `n - Σ e_j` (covariance homogeneity exponent `Σ e_j`). -/
theorem prodRiesz_props {c : ℝ} (hc : 0 ≤ c) {e : Fin n → ℝ}
    (he : ∀ j, 0 ≤ e j ∧ e j < 1) :
    IsLocallyFiniteMeasure (prodRieszMeasure c e) ∧ IsEven (prodRieszMeasure c e) ∧
      IsTempered (prodRieszMeasure c e) ∧ LocallyIntegrable (prodRieszReal c e) ∧
      Scaling (prodRieszMeasure c e) (n - ∑ j, e j) := by
  have ht := prodRieszMeasure_tempered hc he
  have hlf := isLocallyFiniteMeasure_of_tempered ht
  refine ⟨hlf, isEven_withDensity (measurable_prodRiesz c e) (prodRiesz_neg c e), ht,
    locallyIntegrable_of_withDensity (measurable_prodRieszReal c e)
      (prodRieszReal_nonneg hc e) hlf,
    scaling_withDensity (measurable_prodRiesz c e) fun r hr x => prodRiesz_smul c e hr x⟩

/-! ### The pointwise factorization `γ_a = γ_b^θ γ_v^{1-θ}` -/

/-- Auxiliary to the Lean proof route: one coordinate of the factorization, with Lean's
convention at `t = 0` (both sides vanish there unless all exponents are zero). -/
theorem abs_rpow_factor {θ a b v : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hrec : a = θ * b + (1 - θ) * v) (hz : a = 0 → b = 0 ∧ v = 0)
    (hnz : a ≠ 0 → b ≠ 0 ∨ v ≠ 0) (t : ℝ) :
    |t| ^ (-a) = (|t| ^ (-b)) ^ θ * (|t| ^ (-v)) ^ (1 - θ) := by
  rcases eq_or_ne t 0 with rfl | ht
  · rw [abs_zero]
    by_cases ha : a = 0
    · obtain ⟨hb, hv⟩ := hz ha
      simp [ha, hb, hv]
    · rw [Real.zero_rpow (neg_ne_zero.2 ha)]
      rcases hnz ha with hb | hv
      · rw [Real.zero_rpow (neg_ne_zero.2 hb), Real.zero_rpow hθ0.ne', zero_mul]
      · rw [Real.zero_rpow (neg_ne_zero.2 hv), Real.zero_rpow (sub_pos.2 hθ1).ne', mul_zero]
  · have hpos : 0 < |t| := abs_pos.2 ht
    rw [← Real.rpow_mul hpos.le, ← Real.rpow_mul hpos.le, ← Real.rpow_add hpos, hrec]
    congr 1; ring

/-- The pointwise factorization of `L:product-endpoints` (main TeX lines 7267-7274):
`γ_a = γ_b^θ γ_v^{1-θ}` with the common amplitude `c^θ c^{1-θ} = c`; with Lean's values on
the coordinate planes it holds at every point (the TeX states it almost everywhere). -/
theorem prodRiesz_factor {c : ℝ} (hc : 0 < c) {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    {a b v : Fin n → ℝ} (hrec : ∀ j, a j = θ * b j + (1 - θ) * v j)
    (hz : ∀ j, a j = 0 → b j = 0 ∧ v j = 0) (hnz : ∀ j, a j ≠ 0 → b j ≠ 0 ∨ v j ≠ 0)
    (x : Rd n) : prodRiesz c a x = prodRiesz c b x ^ θ * prodRiesz c v x ^ (1 - θ) := by
  have h1θ : 0 ≤ 1 - θ := by linarith
  unfold prodRiesz
  rw [ENNReal.ofReal_rpow_of_nonneg (prodRieszReal_nonneg hc.le b x) hθ0.le,
    ENNReal.ofReal_rpow_of_nonneg (prodRieszReal_nonneg hc.le v x) h1θ,
    ← ENNReal.ofReal_mul (Real.rpow_nonneg (prodRieszReal_nonneg hc.le b x) _)]
  congr 1
  have hP : ∀ (e : Fin n → ℝ), 0 ≤ ∏ j, |x j| ^ (-e j) :=
    fun e => Finset.prod_nonneg fun _ _ => Real.rpow_nonneg (abs_nonneg _) _
  unfold prodRieszReal
  rw [Real.mul_rpow hc.le (hP b), Real.mul_rpow hc.le (hP v),
    ← Real.finsetProd_rpow _ _ (fun j _ => Real.rpow_nonneg (abs_nonneg _) _),
    ← Real.finsetProd_rpow _ _ (fun j _ => Real.rpow_nonneg (abs_nonneg _) _)]
  have hcc : c = c ^ θ * c ^ (1 - θ) := by
    rw [← Real.rpow_add hc, add_sub_cancel, Real.rpow_one]
  calc c * ∏ j, |x j| ^ (-a j)
      = (c ^ θ * c ^ (1 - θ)) * ∏ j, ((|x j| ^ (-b j)) ^ θ * (|x j| ^ (-v j)) ^ (1 - θ)) := by
        rw [← hcc]
        congr 1
        exact Finset.prod_congr rfl fun j _ =>
          abs_rpow_factor hθ0 hθ1 (hrec j) (hz j) (hnz j) (x j)
    _ = _ := by rw [Finset.prod_mul_distrib]; ring


/-! ### `L:product-endpoints`: assembly -/

/-- Supplied input (positive definiteness of product Riesz densities; the Gaussian-mixture
argument of main TeX lines 7253-7266): for `c ≥ 0` and exponents `0 ≤ e_j < 1`, the
measure `c ∏_j |x_j|^{-e_j} dx` on `ℝ³` is positive definite.  TRUE: each active factor is
`|u|^{-e} = Γ(e/2)^{-1} ∫_0^∞ s^{e/2-1} e^{-su²} ds`, a positive mixture of positive-definite
Gaussians, and the Schwartz autocorrelation is absolutely integrable against the density
(Tonelli, then Fubini).  Not formalized: Mathlib has no positive-definiteness theory for
mixtures of Gaussian kernels against a singular density. -/
def RieszProductPD : Prop :=
  ∀ (c : ℝ) (e : Fin 3 → ℝ), 0 ≤ c → (∀ j, 0 ≤ e j ∧ e j < 1) →
    IsPosDefDistr (prodRieszMeasure c e)

/-- The exponent vectors of `L:product-endpoints` lie in `[0,1)`. -/
theorem product_vectors_mem {a : Fin 3 → ℝ} {θ : ℝ} (hp : ProductParams a θ) (j : Fin 3) :
    (0 ≤ bVec θ a j ∧ bVec θ a j < 1) ∧ (0 ≤ vVec θ a j ∧ vVec θ a j < 1) := by
  obtain ⟨-, -, -, -, hpos, hzero, -⟩ := product_arithmetic hp
  rcases (hp.nonneg j).lt_or_eq with hj | hj
  · obtain ⟨⟨hb0, hb1⟩, hv0, hv1⟩ := hpos j hj
    exact ⟨⟨hb0.le, hb1⟩, hv0.le, hv1⟩
  · obtain ⟨hb, hv⟩ := hzero j hj.symm
    rw [hb, hv]; norm_num

/-- The Gaussian comparison `E:product-gaussian-comparison` of `L:product-endpoints` (main TeX
lines 7197-7203; proof lines 7267-7279): for `c > 0`, every `ε > 0` and `z`,
`(p_ε * γ_a)(z) ≤ (p_ε * γ_b)(z)^θ (p_ε * γ_v)(z)^{1-θ}`, through the pointwise
factorization and Hölder on the measure `p_ε(z - y) dy`. -/
theorem product_comparison {a : Fin 3 → ℝ} {θ c : ℝ} (hp : ProductParams a θ) (hc : 0 < c) :
    GaussComparison θ (prodRieszMeasure c a) (prodRieszMeasure c (bVec θ a))
      (prodRieszMeasure c (vVec θ a)) := by
  obtain ⟨-, -, -, hrec, hpos, hzero, -⟩ := product_arithmetic hp
  have hθ1 : θ < 1 := by have := hp.θ_lt; have := hp.one_lt; linarith
  have hfac : ∀ x, prodRiesz c a x ≤
      prodRiesz c (bVec θ a) x ^ θ * prodRiesz c (vVec θ a) x ^ (1 - θ) := fun x =>
    (prodRiesz_factor hc hp.θ_pos hθ1 hrec hzero (fun j hj =>
      Or.inl (hpos j ((hp.nonneg j).lt_of_ne' hj)).1.1.ne') x).le
  have h := gaussComparison_map_withDensity (ν := (volume : Measure (Rd 3))) (ι := id)
    measurable_id (measurable_prodRiesz c a) (measurable_prodRiesz c _)
    (measurable_prodRiesz c _) hp.θ_pos.le hθ1.le hfac
  simpa [Measure.map_id, prodRieszMeasure] using h

/-- Auxiliary to the Lean proof route: for a density measure, `hconv` is the smoothed density
`HigherRieszTwo.smoothCov` of wave L10 (`γ_ε = p_ε * γ`, main TeX line 5916). -/
theorem hconv_withDensity_eq_smoothCov {g : Rd n → ℝ≥0∞} (hg : Measurable g) (ε : ℝ)
    (z : Rd n) :
    hconv ((volume : Measure (Rd n)).withDensity g) ε z = HigherRieszTwo.smoothCov g ε z := by
  unfold hconv HigherRieszTwo.smoothCov
  have hk : Measurable fun y : Rd n => ENNReal.ofReal (heatK ε (z - y)) :=
    ((measurable_heatK ε).comp (measurable_const.sub measurable_id)).ennreal_ofReal
  rw [lintegral_withDensity_eq_lintegral_mul _ hg hk]
  simp only [Pi.mul_apply, mul_comm]

/-- `L:product-endpoints` (main TeX lines 7170-7204; proof 7206-7280), the covariance part:
for `c > 0` the three densities `γ_a, γ_b, γ_v` are even, positive definite (supplied input
`RieszProductPD`), locally integrable and tempered (with locally finite measures), with
measure scaling exponents `3 - α`, `2`, `3 - χ` (covariance homogeneity exponents
`α, 1, χ`), and `α < χ < 2`. -/
theorem product_covariances (hPD : RieszProductPD) {a : Fin 3 → ℝ} {θ c : ℝ}
    (hp : ProductParams a θ) (hc : 0 < c) :
    (IsCov (prodRieszMeasure c a) ∧ LocallyIntegrable (prodRieszReal c a) ∧
        Scaling (prodRieszMeasure c a) (3 - ∑ j, a j)) ∧
      (IsCov (prodRieszMeasure c (bVec θ a)) ∧ LocallyIntegrable (prodRieszReal c (bVec θ a)) ∧
        Scaling (prodRieszMeasure c (bVec θ a)) 2) ∧
      (IsCov (prodRieszMeasure c (vVec θ a)) ∧ LocallyIntegrable (prodRieszReal c (vVec θ a)) ∧
        Scaling (prodRieszMeasure c (vVec θ a)) (3 - chi (∑ j, a j) θ)) ∧
      (∑ j, a j < chi (∑ j, a j) θ ∧ chi (∑ j, a j) θ < 2) := by
  obtain ⟨-, hb, hv, -, -, -, hchi⟩ := product_arithmetic hp
  have hmem := product_vectors_mem hp
  have ha : ∀ j, 0 ≤ a j ∧ a j < 1 := fun j => ⟨hp.nonneg j, hp.lt_one j⟩
  have cov : ∀ e : Fin 3 → ℝ, (∀ j, 0 ≤ e j ∧ e j < 1) →
      IsCov (prodRieszMeasure c e) ∧ LocallyIntegrable (prodRieszReal c e) ∧
        Scaling (prodRieszMeasure c e) (3 - ∑ j, e j) := by
    intro e he
    obtain ⟨h1, h2, h3, h4, h5⟩ := prodRiesz_props hc.le he
    exact ⟨⟨h1, h2, h3, hPD c e hc.le he⟩, h4, by simpa using h5⟩
  refine ⟨cov a ha, ?_, ?_, hchi⟩
  · have := cov (bVec θ a) fun j => (hmem j).1
    rw [hb] at this; norm_num at this ⊢; exact this
  · have := cov (vVec θ a) fun j => (hmem j).2
    rw [hv] at this; exact this

/-- `L:product-endpoints` in full (main TeX lines 7170-7204), with the manuscript's
hypotheses `0 ≤ a_j < 1`, `α = Σ a_j ∈ (1,2)`, `0 < θ < 2 - α`, `c > 0` and the supplied
input `RieszProductPD`: the arithmetic, the covariance properties and exponents, and the
comparison; in particular `(γ_b, γ_v)` is an endpoint pair for `γ_a` in the sense of
`H:three-endpoints` (with `χ = (α - θ)/(1 - θ)`). -/
theorem product_endpoints_paper (hPD : RieszProductPD) {a : Fin 3 → ℝ} {θ c : ℝ}
    (ha0 : ∀ j, 0 ≤ a j) (ha1 : ∀ j, a j < 1) (hα1 : 1 < ∑ j, a j) (hα2 : ∑ j, a j < 2)
    (hθ0 : 0 < θ) (hθ : θ < 2 - ∑ j, a j) (hc : 0 < c) :
    ((0 < lam θ a ∧ lam θ a < 1) ∧ ∑ j, bVec θ a j = 1 ∧
      ∑ j, vVec θ a j = chi (∑ j, a j) θ ∧
      (∀ j, a j = θ * bVec θ a j + (1 - θ) * vVec θ a j) ∧
      (∀ j, 0 < a j → (0 < bVec θ a j ∧ bVec θ a j < 1) ∧
        (0 < vVec θ a j ∧ vVec θ a j < 1)) ∧
      (∀ j, a j = 0 → bVec θ a j = 0 ∧ vVec θ a j = 0)) ∧
    ((IsCov (prodRieszMeasure c a) ∧ LocallyIntegrable (prodRieszReal c a) ∧
        Scaling (prodRieszMeasure c a) (3 - ∑ j, a j)) ∧
      (IsCov (prodRieszMeasure c (bVec θ a)) ∧ LocallyIntegrable (prodRieszReal c (bVec θ a)) ∧
        Scaling (prodRieszMeasure c (bVec θ a)) 2) ∧
      (IsCov (prodRieszMeasure c (vVec θ a)) ∧ LocallyIntegrable (prodRieszReal c (vVec θ a)) ∧
        Scaling (prodRieszMeasure c (vVec θ a)) (3 - chi (∑ j, a j) θ)) ∧
      (∑ j, a j < chi (∑ j, a j) θ ∧ chi (∑ j, a j) θ < 2)) ∧
    GaussComparison θ (prodRieszMeasure c a) (prodRieszMeasure c (bVec θ a))
      (prodRieszMeasure c (vVec θ a)) ∧
    EndpointPair θ (chi (∑ j, a j) θ) (prodRieszMeasure c a) (prodRieszMeasure c (bVec θ a))
      (prodRieszMeasure c (vVec θ a)) := by
  have hp : ProductParams a θ := ⟨ha0, ha1, hα1, hα2, hθ0, hθ⟩
  obtain ⟨h1, h2, h3, h4, h5, h6, -⟩ := product_arithmetic hp
  have hcov := product_covariances hPD hp hc
  have hcmp := product_comparison hp hc
  exact ⟨⟨h1, h2, h3, h4, h5, h6⟩, hcov, hcmp,
    ⟨hcov.2.1.1, hcov.2.2.1.1, hcov.2.1.2.2, hcov.2.2.1.2.2, hcmp⟩⟩


/-! ### Gaussian mixtures for anisotropic Gaussian kernels (route for `L:endpoint-closure`) -/

/-- Auxiliary to the Lean proof route: the one-dimensional Gaussian convolution identity
`∫ e^{-(t-u)²/(2a)} e^{-t²/(2β)} dt = √(2πaβ/(a+β)) e^{-u²/(2(a+β))}` (`a, β > 0`), with
integrability. -/
theorem gauss_conv_one {a β : ℝ} (ha : 0 < a) (hβ : 0 < β) (u : ℝ) :
    Integrable (fun t : ℝ => exp (-(t - u) ^ 2 / (2 * a)) * exp (-t ^ 2 / (2 * β))) ∧
      ∫ t : ℝ, exp (-(t - u) ^ 2 / (2 * a)) * exp (-t ^ 2 / (2 * β)) =
        √(2 * π * a * β / (a + β)) * exp (-u ^ 2 / (2 * (a + β))) := by
  set c : ℝ := (a + β) / (2 * a * β) with hc_def
  set s : ℝ := β * u / (a + β) with hs_def
  have hc : 0 < c := by positivity
  have hpt : ∀ t : ℝ, exp (-(t - u) ^ 2 / (2 * a)) * exp (-t ^ 2 / (2 * β)) =
      exp (-u ^ 2 / (2 * (a + β))) * exp (-c * (t - s) ^ 2) := by
    intro t
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    rw [hc_def, hs_def]
    field_simp
    ring
  have hI : Integrable fun t : ℝ => exp (-c * (t - s) ^ 2) :=
    (integrable_exp_neg_mul_sq hc).comp_sub_right s
  refine ⟨?_, ?_⟩
  · simp_rw [hpt]; exact hI.const_mul _
  · simp_rw [hpt]
    rw [integral_const_mul, integral_sub_right_eq_self (fun t : ℝ => exp (-c * t ^ 2)) s,
      integral_gaussian, mul_comm]
    congr 2
    rw [hc_def]; field_simp

/-- Auxiliary to the Lean proof route: the integral over `ℝ^n` of a product of functions of
the coordinates is the product of the one-dimensional integrals. -/
theorem integral_prod_coord (g : Fin n → ℝ → ℝ) :
    ∫ x : Rd n, ∏ j, g j (x j) = ∏ j, ∫ t, g j t := by
  have hmp := EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin n)
  rw [← integral_fintype_prod_eq_prod (𝕜 := ℝ) g, ← volume_pi,
    ← hmp.integral_comp' (fun y : Fin n → ℝ => ∏ j, g j (y j))]
  rfl

/-- Auxiliary to the Lean proof route (diagonalization): for an invertible linear map `T` of
`ℝ^n` there are an orthonormal basis `b` and numbers `l_i > 0` with
`|Tz|² = Σ_i l_i ⟨b_i, z⟩²` (spectral theorem for `T^*T`). -/
theorem exists_diag (T : Rd n ≃L[ℝ] Rd n) :
    ∃ (b : OrthonormalBasis (Fin n) ℝ (Rd n)) (l : Fin n → ℝ), (∀ i, 0 < l i) ∧
      ∀ z, ‖T z‖ ^ 2 = ∑ i, l i * (b.repr z i) ^ 2 := by
  let A : Rd n →ₗ[ℝ] Rd n := (T : Rd n →L[ℝ] Rd n).toLinearMap
  have hS := LinearMap.isSymmetric_adjoint_mul_self A
  have hn : Module.finrank ℝ (Rd n) = n := finrank_euclideanSpace_fin
  have key : ∀ z, ‖T z‖ ^ 2 =
      ∑ i, hS.eigenvalues hn i * ((hS.eigenvectorBasis hn).repr z i) ^ 2 := by
    intro z
    have h1 : ‖T z‖ ^ 2 = inner ℝ z ((LinearMap.adjoint A * A) z) := by
      rw [Module.End.mul_apply, LinearMap.adjoint_inner_right, real_inner_self_eq_norm_sq]
      rfl
    rw [h1, ← (hS.eigenvectorBasis hn).repr.inner_map_map, PiLp.inner_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hS.eigenvectorBasis_apply_self_apply hn]
    simp only [RCLike.inner_apply, conj_trivial, RCLike.ofReal_real_eq_id, id_eq]
    ring
  set b := hS.eigenvectorBasis hn
  set l := hS.eigenvalues hn
  refine ⟨b, l, fun i => ?_, key⟩
  have hbi : b i ≠ 0 := b.orthonormal.ne_zero i
  have hT : T (b i) ≠ 0 := fun h => hbi (T.injective (h.trans (map_zero T).symm))
  have h := key (b i)
  rw [b.repr_self] at h
  have hsum : ∑ j, l j * (EuclideanSpace.single i (1 : ℝ) j) ^ 2 = l i := by
    rw [Finset.sum_eq_single i (fun j _ hj => by simp [hj])
      (fun h => absurd (Finset.mem_univ i) h)]
    simp
  rw [hsum] at h
  rw [← h]
  exact pow_pos (norm_pos_iff.2 hT) 2

/-- Auxiliary to the Lean proof route (replaces the TeX's general-covariance Gaussian
`q_Σ = p_a * q_{Σ - aI}`, main TeX lines 7434-7437): for invertible `T`, `ε > 0` and `x`, the
anisotropic kernel `y ↦ p_ε(x - Ty)` is an isotropic heat mixture: there are `a > 0` and an
s-finite measure `ρ` with `p_ε(x - Ty) = ∫ p_a(w - y) ρ(dw)` for every `y`. -/
theorem exists_heat_mixture (T : Rd n ≃L[ℝ] Rd n) {ε : ℝ} (hε : 0 < ε) (x : Rd n) :
    ∃ a : ℝ, 0 < a ∧ ∃ ρ : Measure (Rd n), SFinite ρ ∧ ∀ y : Rd n,
      ENNReal.ofReal (heatK ε (x - T y)) = ∫⁻ w, ENNReal.ofReal (heatK a (w - y)) ∂ρ := by
  obtain ⟨b, l, hl, hkey⟩ := exists_diag T
  set L : ℝ := ∑ i, l i with hL
  have hL0 : 0 ≤ L := Finset.sum_nonneg fun i _ => (hl i).le
  set a : ℝ := ε / (2 * (1 + L)) with ha_def
  have ha : 0 < a := by positivity
  have hli : ∀ i, l i ≤ L := fun i =>
    Finset.single_le_sum (f := l) (fun j _ => (hl j).le) (Finset.mem_univ i)
  have hla : ∀ i, a < ε / l i := by
    intro i
    rw [lt_div_iff₀ (hl i), ha_def, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith [hli i]
  set β : Fin n → ℝ := fun i => ε / l i - a with hβ_def
  have hβ : ∀ i, 0 < β i := fun i => by simp only [hβ_def]; linarith [hla i]
  have haβ : ∀ i, a + β i = ε / l i := fun i => by simp only [hβ_def]; ring
  set m : Rd n := T.symm x
  set G : Rd n → ℝ := fun v => ∏ i, exp (-(v i) ^ 2 / (2 * β i)) with hG
  have hGm : Measurable G := by
    refine Finset.measurable_prod _ fun i _ => ?_
    exact Real.measurable_exp.comp ((((EuclideanSpace.proj i).continuous.measurable).pow_const
      2).neg.div_const _)
  set D : ℝ := (2 * π * a) ^ (-((n : ℝ) / 2)) * ∏ i, √(2 * π * a * β i / (a + β i)) with hD
  have hD0 : 0 < D := by
    refine mul_pos (by positivity) (Finset.prod_pos fun i _ => ?_)
    have := hβ i
    exact Real.sqrt_pos.2 (by positivity)
  set K : ℝ := (2 * π * ε) ^ (-((n : ℝ) / 2)) / D with hK
  have hK0 : 0 ≤ K := by positivity
  set R : Rd n → Rd n := fun v => m + b.repr.symm v with hR
  have hRm : Measurable R := (continuous_const.add b.repr.symm.continuous).measurable
  refine ⟨a, ha, ENNReal.ofReal K •
    ((volume : Measure (Rd n)).withDensity (fun v => ENNReal.ofReal (G v))).map R,
    inferInstance, fun y => ?_⟩
  set u : Rd n := b.repr (y - m) with hu
  have hRu : ∀ v, ‖R v - y‖ = ‖v - u‖ := by
    intro v
    have : R v - y = b.repr.symm (v - u) := by
      simp only [hR, hu, map_sub, LinearIsometryEquiv.symm_apply_apply]; abel
    rw [this, LinearIsometryEquiv.norm_map]
  have hmeas : Measurable fun w : Rd n => ENNReal.ofReal (heatK a (w - y)) :=
    ((measurable_heatK a).comp (measurable_id.sub measurable_const)).ennreal_ofReal
  have hmR : Measurable fun v => ENNReal.ofReal (heatK a (R v - y)) := hmeas.comp hRm
  rw [lintegral_smul_measure, lintegral_map hmeas hRm,
    lintegral_withDensity_eq_lintegral_mul _ hGm.ennreal_ofReal hmR, smul_eq_mul]
  have hfac : ∀ v : Rd n, heatK a (v - u) * G v = (2 * π * a) ^ (-((n : ℝ) / 2)) *
      ∏ i, (exp (-((v i) - u i) ^ 2 / (2 * a)) * exp (-(v i) ^ 2 / (2 * β i))) := by
    intro v
    simp only [heatK, hG]
    rw [Finset.prod_mul_distrib, mul_assoc]
    congr 2
    rw [← Real.exp_sum, EuclideanSpace.real_norm_sq_eq, Finset.sum_div, ← Finset.sum_neg_distrib]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [PiLp.sub_apply]; ring
  have hint1 : ∀ i, Integrable fun t : ℝ =>
      exp (-(t - u i) ^ 2 / (2 * a)) * exp (-t ^ 2 / (2 * β i)) :=
    fun i => (gauss_conv_one ha (hβ i) (u i)).1
  have hInt : Integrable fun v : Rd n => (2 * π * a) ^ (-((n : ℝ) / 2)) *
      ∏ i, (exp (-((v i) - u i) ^ 2 / (2 * a)) * exp (-(v i) ^ 2 / (2 * β i))) :=
    (integrable_prod_coord (g := fun i t => exp (-(t - u i) ^ 2 / (2 * a)) *
      exp (-t ^ 2 / (2 * β i))) hint1).const_mul _
  have hpt : ∀ v : Rd n, ENNReal.ofReal (G v) * ENNReal.ofReal (heatK a (R v - y)) =
      ENNReal.ofReal ((2 * π * a) ^ (-((n : ℝ) / 2)) *
        ∏ i, (exp (-((v i) - u i) ^ 2 / (2 * a)) * exp (-(v i) ^ 2 / (2 * β i)))) := by
    intro v
    rw [← hfac, heatK_congr_norm (hRu v), mul_comm,
      ← ENNReal.ofReal_mul (heatK_pos ha _).le]
  simp only [Pi.mul_apply]
  simp_rw [hpt]
  rw [← ofReal_integral_eq_lintegral_ofReal hInt (Eventually.of_forall fun v => by positivity),
    integral_const_mul, integral_prod_coord (fun i t => exp (-(t - u i) ^ 2 / (2 * a)) *
      exp (-t ^ 2 / (2 * β i))), ← ENNReal.ofReal_mul hK0]
  congr 1
  have hone : ∀ i, ∫ t : ℝ, exp (-(t - u i) ^ 2 / (2 * a)) * exp (-t ^ 2 / (2 * β i)) =
      √(2 * π * a * β i / (a + β i)) * exp (-(u i) ^ 2 / (2 * (a + β i))) :=
    fun i => (gauss_conv_one ha (hβ i) (u i)).2
  simp_rw [hone]
  rw [Finset.prod_mul_distrib, ← mul_assoc, ← mul_assoc]
  have hKD : K * ((2 * π * a) ^ (-((n : ℝ) / 2)) * ∏ i, √(2 * π * a * β i / (a + β i))) =
      (2 * π * ε) ^ (-((n : ℝ) / 2)) := by
    rw [← hD, hK, div_mul_cancel₀ _ hD0.ne']
  rw [mul_assoc K, hKD]
  simp only [heatK]
  congr 1
  have hxT : x - T y = T (m - y) := by simp [m, map_sub]
  rw [hxT, hkey, ← Real.exp_sum]
  congr 1
  rw [Finset.sum_div, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hmy : b.repr (m - y) i = -u i := by
    have : m - y = -(y - m) := (neg_sub y m).symm
    rw [hu, this, map_neg, PiLp.neg_apply]
  rw [hmy, haβ i]
  field_simp

/-- The comparison passes to any isotropic heat mixture: if `k(y) = ∫ p_a(w - y) ρ(dw)`, then
`∫ k dΓ ≤ (∫ k dL)^θ (∫ k dS)^{1-θ}` (Tonelli, the comparison at width `a`, Hölder on `ρ`;
the mechanism of main TeX lines 7434-7451). -/
theorem comparison_of_mixture {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) {Γ L S : Measure (Rd n)}
    [SFinite Γ] [SFinite L] [SFinite S] (hcmp : GaussComparison θ Γ L S) {a : ℝ} (ha : 0 < a)
    {ρ : Measure (Rd n)} [SFinite ρ] {k : Rd n → ℝ≥0∞}
    (hk : ∀ y, k y = ∫⁻ w, ENNReal.ofReal (heatK a (w - y)) ∂ρ) :
    ∫⁻ y, k y ∂Γ ≤ (∫⁻ y, k y ∂L) ^ θ * (∫⁻ y, k y ∂S) ^ (1 - θ) := by
  have hF : Measurable (Function.uncurry fun (y w : Rd n) =>
      ENNReal.ofReal (heatK a (w - y))) :=
    ((measurable_heatK a).comp (measurable_snd.sub measurable_fst)).ennreal_ofReal
  have swap : ∀ (J : Measure (Rd n)) [SFinite J], ∫⁻ y, k y ∂J = ∫⁻ w, hconv J a w ∂ρ := by
    intro J _
    simp_rw [hk]
    exact lintegral_lintegral_swap hF.aemeasurable
  have hmeas : ∀ (J : Measure (Rd n)) [SFinite J], Measurable fun w => hconv J a w := by
    intro J _
    have : Measurable (Function.uncurry fun (w y : Rd n) =>
        ENNReal.ofReal (heatK a (w - y))) :=
      ((measurable_heatK a).comp (measurable_fst.sub measurable_snd)).ennreal_ofReal
    exact this.lintegral_prod_right'
  rw [swap Γ, swap L, swap S]
  calc ∫⁻ w, hconv Γ a w ∂ρ ≤ ∫⁻ w, hconv L a w ^ θ * hconv S a w ^ (1 - θ) ∂ρ :=
        lintegral_mono fun w => hcmp a ha w
    _ ≤ _ := ENNReal.lintegral_mul_norm_pow_le (hmeas L).aemeasurable (hmeas S).aemeasurable
        h0 (by linarith) (by ring)

/-! ### `L:endpoint-closure`: invertible linear images -/

/-- Auxiliary to the Lean proof route: Gaussian convolution of a pushforward. -/
theorem hconv_map (T : Rd n ≃L[ℝ] Rd n) (J : Measure (Rd n)) (ε : ℝ) (x : Rd n) :
    hconv (J.map T) ε x = ∫⁻ y, ENNReal.ofReal (heatK ε (x - T y)) ∂J := by
  unfold hconv
  exact lintegral_map ((measurable_heatK ε).comp (measurable_const.sub measurable_id)
    ).ennreal_ofReal T.continuous.measurable

/-- The comparison is preserved by an invertible linear pushforward of all three measures
(main TeX lines 7465-7474). -/
theorem comparison_map {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) {Γ L S : Measure (Rd n)}
    [SFinite Γ] [SFinite L] [SFinite S] (hcmp : GaussComparison θ Γ L S)
    (T : Rd n ≃L[ℝ] Rd n) : GaussComparison θ (Γ.map T) (L.map T) (S.map T) := by
  intro ε hε x
  obtain ⟨a, ha, ρ, hρ, hk⟩ := exists_heat_mixture T hε x
  rw [hconv_map, hconv_map, hconv_map]
  exact comparison_of_mixture h0 h1 hcmp ha hk

/-- Pushforward by an invertible linear map preserves temperedness (main TeX lines
7456-7458). -/
theorem tempered_map {J : Measure (Rd n)} (hJ : IsTempered J) (T : Rd n ≃L[ℝ] Rd n) :
    IsTempered (J.map T) := by
  obtain ⟨k, hk⟩ := hJ
  refine ⟨k, ?_⟩
  set M : ℝ := ‖(T.symm : Rd n →L[ℝ] Rd n)‖
  have hM : 0 ≤ M := norm_nonneg _
  set C : ℝ := (1 + M) ^ (k : ℝ)
  have hmk : Measurable fun x : Rd n => ENNReal.ofReal ((1 + ‖x‖) ^ (-(k : ℝ))) := by fun_prop
  rw [lintegral_map hmk T.continuous.measurable]
  have hle : ∀ y : Rd n, ENNReal.ofReal ((1 + ‖T y‖) ^ (-(k : ℝ))) ≤
      ENNReal.ofReal C * ENNReal.ofReal ((1 + ‖y‖) ^ (-(k : ℝ))) := by
    intro y
    rw [← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hy : ‖y‖ ≤ M * ‖T y‖ := by
      have := (T.symm : Rd n →L[ℝ] Rd n).le_opNorm (T y)
      simpa using this
    have h1 : (1 + ‖y‖) / (1 + M) ≤ 1 + ‖T y‖ := by
      rw [div_le_iff₀ (by positivity)]; nlinarith [norm_nonneg (T y)]
    calc (1 + ‖T y‖) ^ (-(k : ℝ)) ≤ ((1 + ‖y‖) / (1 + M)) ^ (-(k : ℝ)) :=
          Real.rpow_le_rpow_of_nonpos (by positivity) h1 (by simp)
      _ = C * (1 + ‖y‖) ^ (-(k : ℝ)) := by
          rw [Real.div_rpow (by positivity) (by positivity), Real.rpow_neg (by positivity) (k : ℝ),
            Real.rpow_neg (by positivity) (k : ℝ)]
          simp only [C]
          field_simp
  calc ∫⁻ y, ENNReal.ofReal ((1 + ‖T y‖) ^ (-(k : ℝ))) ∂J
      ≤ ∫⁻ y, ENNReal.ofReal C * ENNReal.ofReal ((1 + ‖y‖) ^ (-(k : ℝ))) ∂J :=
        lintegral_mono hle
    _ = ENNReal.ofReal C * ∫⁻ y, ENNReal.ofReal ((1 + ‖y‖) ^ (-(k : ℝ))) ∂J :=
        lintegral_const_mul _ (by fun_prop)
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hk

/-- Pushforward by a linear map preserves evenness (main TeX lines 7456-7458). -/
theorem even_map {J : Measure (Rd n)} (hJ : IsEven J) (T : Rd n ≃L[ℝ] Rd n) :
    IsEven (J.map T) := by
  unfold IsEven at hJ ⊢
  rw [Measure.map_map measurable_neg T.continuous.measurable]
  have : ((fun x : Rd n => -x) ∘ T) = T ∘ fun x => -x := by
    funext x; simp [map_neg]
  rw [this, ← Measure.map_map T.continuous.measurable measurable_neg, hJ]

/-- Auxiliary to the Lean proof route: `T⁻¹(rA) = r T⁻¹(A)` for a linear equivalence. -/
theorem preimage_smul_set (T : Rd n ≃L[ℝ] Rd n) {r : ℝ} (hr : r ≠ 0) (A : Set (Rd n)) :
    T ⁻¹' (r • A) = r • (T ⁻¹' A) := by
  ext y
  rw [mem_preimage, mem_smul_set_iff_inv_smul_mem₀ hr, mem_smul_set_iff_inv_smul_mem₀ hr,
    mem_preimage, map_smul]

/-- Pushforward by an invertible linear map preserves measure scaling, since `T` commutes with
dilations (main TeX lines 7456-7458). -/
theorem scaling_map {J : Measure (Rd n)} {s : ℝ} (hJ : Scaling J s) (T : Rd n ≃L[ℝ] Rd n) :
    Scaling (J.map T) s := by
  intro A hA r hr
  rw [Measure.map_apply T.continuous.measurable (hA.const_smul₀ r),
    Measure.map_apply T.continuous.measurable hA, preimage_smul_set T hr.ne']
  exact hJ _ (T.continuous.measurable hA) r hr

/-- Auxiliary to the Lean proof route: the Lebesgue change of variables under an invertible
linear map, `∫ F = |det T| ∫ F(Tv) dv`. -/
theorem integral_eq_det_mul_comp (T : Rd n ≃L[ℝ] Rd n) (F : Rd n → ℂ) :
    ∫ y, F y = ((|LinearMap.det (T : Rd n →ₗ[ℝ] Rd n)| : ℝ) : ℂ) * ∫ v, F (T v) := by
  set f : Rd n →ₗ[ℝ] Rd n := (T : Rd n →ₗ[ℝ] Rd n)
  have hdet : LinearMap.det f ≠ 0 := (LinearEquiv.isUnit_det' T.toLinearEquiv).ne_zero
  have hmap := Measure.map_linearMap_addHaar_eq_smul_addHaar (μ := (volume : Measure (Rd n))) hdet
  have hcomp : ∫ v, F (T v) = ∫ y, F y ∂(Measure.map f volume) :=
    (T.toHomeomorph.measurableEmbedding.integral_map F).symm
  rw [hcomp, hmap, integral_smul_measure, ENNReal.toReal_ofReal (abs_nonneg _), abs_inv,
    Complex.real_smul, ← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ (abs_ne_zero.2 hdet),
    Complex.ofReal_one, one_mul]

/-- Pushforward by an invertible linear map preserves positive definiteness: the quadratic
form of `T_*J` at `φ` is `|det T|` times that of `J` at `ψ = φ ∘ T` (main TeX lines
7458-7464). -/
theorem posdef_map {J : Measure (Rd n)} (hJ : IsPosDefDistr J) (T : Rd n ≃L[ℝ] Rd n) :
    IsPosDefDistr (J.map T) := by
  intro φ
  set ψ : SchwartzMap (Rd n) ℂ := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ T φ
  have hψ : ∀ v, ψ v = φ (T v) := fun v => rfl
  set δ : ℝ := |LinearMap.det (T : Rd n →ₗ[ℝ] Rd n)|
  have hauto : ∀ z, ∫ y, φ (T z + y) * (starRingEnd ℂ) (φ y) =
      (δ : ℂ) * ∫ v, ψ (z + v) * (starRingEnd ℂ) (ψ v) := by
    intro z
    rw [integral_eq_det_mul_comp T]
    congr 2; funext v
    rw [hψ, hψ, map_add T]
  have hme : MeasurableEmbedding (T : Rd n → Rd n) := T.toHomeomorph.measurableEmbedding
  rw [hme.integral_map]
  change (∫ z, (∫ y, φ (T z + y) * (starRingEnd ℂ) (φ y)) ∂J).im = 0 ∧
    0 ≤ (∫ z, (∫ y, φ (T z + y) * (starRingEnd ℂ) (φ y)) ∂J).re
  simp_rw [hauto]
  rw [integral_const_mul]
  obtain ⟨him, hre⟩ := hJ ψ
  refine ⟨?_, ?_⟩
  · rw [Complex.im_ofReal_mul, him, mul_zero]
  · rw [Complex.re_ofReal_mul]; exact mul_nonneg (abs_nonneg _) hre

/-- Pushforward by an invertible linear map preserves all covariance properties. -/
theorem isCov_map {J : Measure (Rd n)} (hJ : IsCov J) (T : Rd n ≃L[ℝ] Rd n) :
    IsCov (J.map T) :=
  have ht := tempered_map hJ.tempered T
  ⟨isLocallyFiniteMeasure_of_tempered ht, even_map hJ.even T, ht, posdef_map hJ.posdef T⟩

/-- `L:endpoint-closure`, the linear-image half (main TeX lines 7418-7424; proof lines
7426-7474): for `0 ≤ θ ≤ 1`, a covariance target `Γ` with an endpoint pair `(L, S)` and an
invertible linear `T : ℝ³ → ℝ³`, `(T_*L, T_*S)` is an endpoint pair for `T_*Γ`, `T_*Γ` is a
covariance, and every measure scaling of `Γ` passes to `T_*Γ`. -/
theorem endpoint_closure_map {θ χ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) {Γ L S : Measure (Rd 3)}
    (hΓ : IsCov Γ) (hp : EndpointPair θ χ Γ L S) (T : Rd 3 ≃L[ℝ] Rd 3) :
    EndpointPair θ χ (Γ.map T) (L.map T) (S.map T) ∧ IsCov (Γ.map T) ∧
      ∀ s, Scaling Γ s → Scaling (Γ.map T) s := by
  have := hΓ.radon; have := hp.low.radon; have := hp.st.radon
  exact ⟨⟨isCov_map hp.low T, isCov_map hp.st T, scaling_map hp.low_scaling T,
    scaling_map hp.st_scaling T, comparison_map h0 h1 hp.comparison T⟩, isCov_map hΓ T,
    fun _ hs => scaling_map hs T⟩

/-! ### `L:endpoint-closure`: finite nonnegative sums -/

/-- The finite weighted sum `Σ_i w_i μ_i` (`w_i ≥ 0` real). -/
def wsum {N : ℕ} (w : Fin N → ℝ) (μ : Fin N → Measure (Rd n)) : Measure (Rd n) :=
  ∑ i, ENNReal.ofReal (w i) • μ i

/-- Auxiliary to the Lean proof route: Gaussian convolution is additive. -/
theorem hconv_wsum {N : ℕ} (w : Fin N → ℝ) (μ : Fin N → Measure (Rd n)) (ε : ℝ) (z : Rd n) :
    hconv (wsum w μ) ε z = ∑ i, ENNReal.ofReal (w i) * hconv (μ i) ε z := by
  simp only [hconv, wsum, lintegral_finsetSum_measure, lintegral_smul_measure, smul_eq_mul]

/-- Auxiliary to the Lean proof route: discrete Hölder,
`Σ_i f_i^θ g_i^{1-θ} ≤ (Σ f_i)^θ (Σ g_i)^{1-θ}` in `[0, ∞]`. -/
theorem sum_holder {N : ℕ} (f g : Fin N → ℝ≥0∞) {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    ∑ i, f i ^ θ * g i ^ (1 - θ) ≤ (∑ i, f i) ^ θ * (∑ i, g i) ^ (1 - θ) := by
  have h := ENNReal.lintegral_mul_norm_pow_le (μ := Measure.count) (f := f) (g := g)
    (measurable_of_countable f).aemeasurable (measurable_of_countable g).aemeasurable
    (p := θ) (q := 1 - θ) h0 (by linarith) (by ring)
  simpa [lintegral_fintype, Measure.count_singleton] using h

/-- The comparison is preserved by finite nonnegative sums with the same `θ` (main TeX lines
7479-7494; discrete Hölder). -/
theorem comparison_wsum {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) {N : ℕ} (w : Fin N → ℝ)
    {Γ L S : Fin N → Measure (Rd n)} (hcmp : ∀ i, GaussComparison θ (Γ i) (L i) (S i)) :
    GaussComparison θ (wsum w Γ) (wsum w L) (wsum w S) := by
  intro ε hε z
  rw [hconv_wsum, hconv_wsum, hconv_wsum]
  calc ∑ i, ENNReal.ofReal (w i) * hconv (Γ i) ε z
      ≤ ∑ i, ENNReal.ofReal (w i) * (hconv (L i) ε z ^ θ * hconv (S i) ε z ^ (1 - θ)) :=
        Finset.sum_le_sum fun i _ => by gcongr; exact hcmp i ε hε z
    _ = ∑ i, (ENNReal.ofReal (w i) * hconv (L i) ε z) ^ θ *
          (ENNReal.ofReal (w i) * hconv (S i) ε z) ^ (1 - θ) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [ENNReal.mul_rpow_of_nonneg _ _ h0, ENNReal.mul_rpow_of_nonneg _ _ (by linarith)]
        conv_lhs => rw [← rpow_mul_rpow_one_sub (ENNReal.ofReal (w i)) h0 h1]
        ring
    _ ≤ _ := sum_holder _ _ h0 h1

/-- Finite nonnegative sums preserve temperedness (main TeX line 7482). -/
theorem tempered_wsum {N : ℕ} (w : Fin N → ℝ) {μ : Fin N → Measure (Rd n)}
    (hμ : ∀ i, IsTempered (μ i)) : IsTempered (wsum w μ) := by
  choose k hk using hμ
  set K : ℕ := Finset.univ.sup k
  refine ⟨K, ?_⟩
  rw [wsum, lintegral_finsetSum_measure]
  refine ENNReal.sum_lt_top.2 fun i _ => ?_
  rw [lintegral_smul_measure]
  refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top (lt_of_le_of_lt (lintegral_mono fun x => ?_)
    (hk i))
  refine ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_exponent_le (by
    linarith [norm_nonneg x]) ?_)
  have : k i ≤ K := Finset.le_sup (f := k) (Finset.mem_univ i)
  have : (k i : ℝ) ≤ K := by exact_mod_cast this
  linarith

/-- Finite sums preserve evenness. -/
theorem even_wsum {N : ℕ} (w : Fin N → ℝ) {μ : Fin N → Measure (Rd n)}
    (hμ : ∀ i, IsEven (μ i)) : IsEven (wsum w μ) := by
  unfold IsEven at hμ ⊢
  ext s hs
  rw [Measure.map_apply measurable_neg hs]
  simp only [wsum, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  have := congrArg (fun ν : Measure (Rd n) => ν s) (hμ i)
  simp only [Measure.map_apply measurable_neg hs] at this
  exact this

/-- Finite sums preserve a common measure scaling (main TeX line 7482). -/
theorem scaling_wsum {N : ℕ} (w : Fin N → ℝ) {μ : Fin N → Measure (Rd n)} {s : ℝ}
    (hμ : ∀ i, Scaling (μ i) s) : Scaling (wsum w μ) s := by
  intro A hA r hr
  simp only [wsum, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply, smul_eq_mul,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hμ i A hA r hr]; ring

/-- Finite nonnegative sums preserve positive definiteness. -/
theorem posdef_wsum {N : ℕ} {w : Fin N → ℝ} (hw : ∀ i, 0 ≤ w i) {μ : Fin N → Measure (Rd n)}
    (hμ : ∀ i, IsPosDefDistr (μ i)) : IsPosDefDistr (wsum w μ) := by
  intro φ
  set A : Rd n → ℂ := fun x => ∫ y, φ (x + y) * (starRingEnd ℂ) (φ y)
  change (∫ x, A x ∂(wsum w μ)).im = 0 ∧ 0 ≤ (∫ x, A x ∂(wsum w μ)).re
  by_cases hint : Integrable A (wsum w μ)
  · rw [wsum] at hint ⊢
    rw [integral_finsetSum_measure fun i hi => integrable_finsetSum_measure.1 hint i hi]
    simp only [integral_smul_measure, ENNReal.toReal_ofReal (hw _), Complex.real_smul]
    rw [Complex.im_sum, Complex.re_sum]
    refine ⟨Finset.sum_eq_zero fun i _ => ?_, Finset.sum_nonneg fun i _ => ?_⟩
    · rw [Complex.im_ofReal_mul, (hμ i φ).1, mul_zero]
    · rw [Complex.re_ofReal_mul]; exact mul_nonneg (hw i) (hμ i φ).2
  · rw [integral_undef hint]; simp

/-- Finite nonnegative sums preserve all covariance properties. -/
theorem isCov_wsum {N : ℕ} {w : Fin N → ℝ} (hw : ∀ i, 0 ≤ w i) {μ : Fin N → Measure (Rd n)}
    (hμ : ∀ i, IsCov (μ i)) : IsCov (wsum w μ) :=
  have ht := tempered_wsum w fun i => (hμ i).tempered
  ⟨isLocallyFiniteMeasure_of_tempered ht, even_wsum w fun i => (hμ i).even, ht,
    posdef_wsum hw fun i => (hμ i).posdef⟩

/-- `L:endpoint-closure`, the finite-sum half (main TeX lines 7418-7424; proof lines
7479-7495): for `0 ≤ θ ≤ 1`, nonnegative weights and component endpoint pairs with the same
`θ, χ`, the weighted sums of the endpoints form an endpoint pair for the weighted sum of the
targets; the sum of covariance targets is a covariance with any common measure scaling.
Zero weights and the all-zero target are included. -/
theorem endpoint_closure_sum {θ χ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) {N : ℕ} {w : Fin N → ℝ}
    (hw : ∀ i, 0 ≤ w i) {Γ L S : Fin N → Measure (Rd 3)}
    (hp : ∀ i, EndpointPair θ χ (Γ i) (L i) (S i)) :
    EndpointPair θ χ (wsum w Γ) (wsum w L) (wsum w S) ∧
      ((∀ i, IsCov (Γ i)) → IsCov (wsum w Γ)) ∧
      ∀ s, (∀ i, Scaling (Γ i) s) → Scaling (wsum w Γ) s :=
  ⟨⟨isCov_wsum hw fun i => (hp i).low, isCov_wsum hw fun i => (hp i).st,
    scaling_wsum w fun i => (hp i).low_scaling, scaling_wsum w fun i => (hp i).st_scaling,
    comparison_wsum h0 h1 w fun i => (hp i).comparison⟩,
    fun hΓ => isCov_wsum hw hΓ, fun _ hs => scaling_wsum w hs⟩

/-- `L:endpoint-closure` (main TeX lines 7418-7424; proof 7426-7495) with the manuscript's
parameters `E:three-parameters` (`0 < α₀ < 1`, `1 < α < 2 - α₀`, `α₀ < θ < 2 - α`,
`χ = (α - θ)/(1 - θ)`): the comparison of `H:three-endpoints`, with the endpoint covariance
properties and scalings, is preserved by simultaneous invertible linear pushforward and by
finite nonnegative sums; the covariance target keeps its properties and its scaling
`3 - α`. -/
theorem endpoint_closure_paper {α₀ α θ : ℝ} (hα₀ : 0 < α₀) (_hα₀1 : α₀ < 1) (hα1 : 1 < α)
    (_hα2 : α < 2 - α₀) (hθ0 : α₀ < θ) (hθ : θ < 2 - α) :
    (∀ {Γ L S : Measure (Rd 3)} (T : Rd 3 ≃L[ℝ] Rd 3), IsCov Γ →
      EndpointPair θ (chi α θ) Γ L S →
        EndpointPair θ (chi α θ) (Γ.map T) (L.map T) (S.map T) ∧ IsCov (Γ.map T) ∧
          (Scaling Γ (3 - α) → Scaling (Γ.map T) (3 - α))) ∧
    (∀ {N : ℕ} {w : Fin N → ℝ} {Γ L S : Fin N → Measure (Rd 3)}, (∀ i, 0 ≤ w i) →
      (∀ i, EndpointPair θ (chi α θ) (Γ i) (L i) (S i)) →
        EndpointPair θ (chi α θ) (wsum w Γ) (wsum w L) (wsum w S) ∧
          ((∀ i, IsCov (Γ i)) → IsCov (wsum w Γ)) ∧
          ((∀ i, Scaling (Γ i) (3 - α)) → Scaling (wsum w Γ) (3 - α))) := by
  have h0 : 0 ≤ θ := by linarith
  have h1 : θ ≤ 1 := by linarith
  refine ⟨fun T hΓ hp => ?_, fun hw hp => ?_⟩
  · obtain ⟨a, b, c⟩ := endpoint_closure_map h0 h1 hΓ hp T
    exact ⟨a, b, c _⟩
  · obtain ⟨a, b, c⟩ := endpoint_closure_sum h0 h1 hw hp
    exact ⟨a, b, c _⟩


/-! ### `L:plane-endpoints`: plane-supported measures -/

/-- The plane embedding `y ↦ (y, 0)` of `ℝ²` into `ℝ³` (coordinates `(y, z) ∈ ℝ² × ℝ`, main TeX
lines 7318-7319), a linear isometry. -/
def planeEmb : Rd 2 →ₗᵢ[ℝ] Rd 3 where
  toFun y := WithLp.toLp 2 ![y 0, y 1, 0]
  map_add' y y' := by ext i; fin_cases i <;> simp
  map_smul' r y := by ext i; fin_cases i <;> simp
  norm_map' y := by
    simp [EuclideanSpace.norm_eq, Fin.sum_univ_three, Fin.sum_univ_two]

/-- The unit normal `e₃` of the plane. -/
def e3 : Rd 3 := EuclideanSpace.single 2 1

/-- The plane-supported measure `c ∏_{j ≤ 2} |y_j|^{-e_j} dy δ₀(dz)` (main TeX lines 7318-7322):
the image under `planeEmb` of the product density measure on `ℝ²`. -/
def planeMeasure (c : ℝ) (e : Fin 2 → ℝ) : Measure (Rd 3) := (prodRieszMeasure c e).map planeEmb

/-- Supplied input (positive definiteness of plane-supported product Riesz measures; main
TeX lines 7359-7384): for `c ≥ 0` and `0 ≤ e_j < 1` the measure
`c ∏_j |y_j|^{-e_j} dy δ₀(dz)` on `ℝ³` is positive definite.  TRUE: the tangential density is
a positive mixture of positive-definite Gaussians in `y` (a zero exponent gives the constant
one, including the low endpoint `c dy δ₀(dz)`), and the quadratic form is
`∫ dz ∫∫ f_e(y - y') φ(y,z) conj φ(y',z) dy dy'`, absolutely convergent by rapid decay.  Not
formalized, for the same reason as `RieszProductPD`. -/
def PlaneRieszPD : Prop :=
  ∀ (c : ℝ) (e : Fin 2 → ℝ), 0 ≤ c → (∀ j, 0 ≤ e j ∧ e j < 1) → IsPosDefDistr (planeMeasure c e)

/-- Auxiliary to the Lean proof route: the preimage of a dilate under a linear map. -/
theorem preimage_smul_set_linear {m : ℕ} (f : Rd m →ₗ[ℝ] Rd n) {r : ℝ} (hr : r ≠ 0)
    (A : Set (Rd n)) : f ⁻¹' (r • A) = r • (f ⁻¹' A) := by
  ext y
  rw [mem_preimage, mem_smul_set_iff_inv_smul_mem₀ hr, mem_smul_set_iff_inv_smul_mem₀ hr,
    mem_preimage, map_smul]

/-- The covariance properties of plane-supported measures other than positive definiteness
(main TeX lines 7348-7354): for `c ≥ 0` and `0 ≤ e_j < 1` the measure is locally finite,
even, tempered, with measure scaling exponent `2 - e₁ - e₂`. -/
theorem plane_props {c : ℝ} (hc : 0 ≤ c) {e : Fin 2 → ℝ} (he : ∀ j, 0 ≤ e j ∧ e j < 1) :
    IsLocallyFiniteMeasure (planeMeasure c e) ∧ IsEven (planeMeasure c e) ∧
      IsTempered (planeMeasure c e) ∧ Scaling (planeMeasure c e) (2 - ∑ j, e j) := by
  obtain ⟨-, hev, ht, -, hsc⟩ := prodRiesz_props hc he
  have hι : Measurable (planeEmb : Rd 2 → Rd 3) := planeEmb.continuous.measurable
  have htp : IsTempered (planeMeasure c e) := by
    obtain ⟨k, hk⟩ := ht
    refine ⟨k, ?_⟩
    rw [planeMeasure, lintegral_map (by fun_prop) hι]
    simpa only [LinearIsometry.norm_map] using hk
  refine ⟨isLocallyFiniteMeasure_of_tempered htp, ?_, htp, ?_⟩
  · unfold IsEven at hev ⊢
    rw [planeMeasure, Measure.map_map measurable_neg hι]
    have : ((fun x : Rd 3 => -x) ∘ planeEmb) = planeEmb ∘ fun y => -y := by
      funext y; simp
    rw [this, ← Measure.map_map hι measurable_neg, hev]
  · intro A hA r hr
    rw [planeMeasure, Measure.map_apply hι (hA.const_smul₀ r), Measure.map_apply hι hA]
    have hpre := preimage_smul_set_linear (planeEmb.toLinearMap) hr.ne' A
    simp only [LinearIsometry.coe_toLinearMap] at hpre
    rw [hpre, hsc _ (hι hA) r hr]
    norm_num

/-- The low plane endpoint is `c m`, `m(dy,dz) = dy δ₀(dz)` (main TeX lines 7326-7328). -/
theorem planeMeasure_zero (c : ℝ) :
    planeMeasure c 0 = ENNReal.ofReal c • (volume : Measure (Rd 2)).map planeEmb := by
  have h : prodRiesz c (0 : Fin 2 → ℝ) = fun _ => ENNReal.ofReal c := by
    funext y; simp [prodRiesz, prodRieszReal]
  rw [planeMeasure, prodRieszMeasure, h, withDensity_const, Measure.map_smul]
  exact planeEmb.continuous.measurable.aemeasurable

/-- The Gaussian comparison for the plane endpoints (main TeX lines 7388-7400): with
`v_j = a_j/(1 - θ)`, `c f = c^θ (c f^{1/(1-θ)})^{1-θ}` holds pointwise on the plane, and
Hölder on `p_ε(w - (y,z)) m(dy,dz)` gives the comparison. -/
theorem plane_comparison {c θ : ℝ} (hc : 0 < c) (hθ0 : 0 < θ) (hθ1 : θ < 1) (a : Fin 2 → ℝ) :
    GaussComparison θ (planeMeasure c a) (planeMeasure c 0)
      (planeMeasure c fun j => a j / (1 - θ)) := by
  have h1θ : 0 < 1 - θ := by linarith
  have hfac : ∀ y, prodRiesz c a y ≤
      prodRiesz c 0 y ^ θ * prodRiesz c (fun j => a j / (1 - θ)) y ^ (1 - θ) := by
    intro y
    refine (prodRiesz_factor hc hθ0 hθ1 (fun j => ?_) (fun j hj => ?_) (fun j hj => ?_) y).le
    · simp only [Pi.zero_apply, mul_zero, zero_add]; field_simp
    · simp [hj]
    · exact Or.inr (div_ne_zero hj h1θ.ne')
  exact gaussComparison_map_withDensity planeEmb.continuous.measurable
    (measurable_prodRiesz c a) (measurable_prodRiesz c _) (measurable_prodRiesz c _) hθ0.le
    hθ1.le hfac

/-! ### The low spectral measure: `V_low = c/π` -/

/-- Auxiliary to the Lean proof route: the coordinates `(y, z) ↦ (y₁, y₂, z)` of `ℝ³`. -/
def planeCoord (p : Rd 2 × ℝ) : Rd 3 := WithLp.toLp 2 ![p.1 0, p.1 1, p.2]

/-- Auxiliary to the Lean proof route: `planeCoord` as a composite of measurable
equivalences. -/
def planeEquiv : Rd 2 × ℝ ≃ᵐ Rd 3 :=
  ((MeasurableEquiv.prodCongr (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).symm
      (MeasurableEquiv.refl ℝ)).trans MeasurableEquiv.prodComm).trans
    ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) (Fin.last 2)).symm.trans
      (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)))

/-- Auxiliary to the Lean proof route. -/
theorem planeEquiv_eq : (planeEquiv : Rd 2 × ℝ → Rd 3) = planeCoord := by
  funext p
  ext i
  fin_cases i <;> rfl

/-- Auxiliary to the Lean proof route. -/
theorem measurableEmbedding_planeCoord : MeasurableEmbedding planeCoord :=
  planeEquiv_eq ▸ planeEquiv.measurableEmbedding

/-- Auxiliary to the Lean proof route: `planeCoord` is measure preserving from
`ℝ² × ℝ` (product Lebesgue) to `ℝ³`. -/
theorem measurePreserving_planeCoord :
    MeasurePreserving planeCoord ((volume : Measure (Rd 2)).prod (volume : Measure ℝ))
      (volume : Measure (Rd 3)) := by
  have h1 : MeasurePreserving (fun p : Rd 2 × ℝ => (WithLp.ofLp p.1, p.2))
      ((volume : Measure (Rd 2)).prod (volume : Measure ℝ))
      ((volume : Measure (Fin 2 → ℝ)).prod (volume : Measure ℝ)) :=
    (PiLp.volume_preserving_ofLp (Fin 2)).prod (MeasurePreserving.id volume)
  have h2 : MeasurePreserving (Prod.swap : (Fin 2 → ℝ) × ℝ → ℝ × (Fin 2 → ℝ))
      ((volume : Measure (Fin 2 → ℝ)).prod (volume : Measure ℝ))
      ((volume : Measure ℝ).prod (volume : Measure (Fin 2 → ℝ))) :=
    Measure.measurePreserving_swap
  have h3 := (volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) (Fin.last 2)).symm
  have h4 := PiLp.volume_preserving_toLp (Fin 3)
  have hcomp := h4.comp (h3.comp (h2.comp h1))
  rw [← planeEquiv_eq]
  convert hcomp using 1
  funext p; rfl

/-- Auxiliary to the Lean proof route. -/
theorem planeCoord_zero (y : Rd 2) : planeCoord (y, 0) = planeEmb y := rfl

/-- Auxiliary to the Lean proof route: `⟨(y, z), s e₃⟩ = z s`. -/
theorem inner_planeCoord_e3 (p : Rd 2 × ℝ) (s : ℝ) : ⟪planeCoord p, s • e3⟫_ℝ = p.2 * s := by
  simp [planeCoord, e3, inner_smul_right, EuclideanSpace.inner_single_right]
  ring

/-- Auxiliary to the Lean proof route. -/
theorem norm_le_norm_planeCoord (p : Rd 2 × ℝ) : ‖p.1‖ ≤ ‖planeCoord p‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  refine Real.sqrt_le_sqrt ?_
  simp [planeCoord, Fin.sum_univ_three, Fin.sum_univ_two]
  positivity

/-- Auxiliary to the Lean proof route: `t ↦ t e₃` is an isometric linear embedding. -/
def lineE3 : ℝ →ₗᵢ[ℝ] Rd 3 where
  toFun t := t • e3
  map_add' s t := add_smul s t e3
  map_smul' r t := by simp [smul_smul]
  norm_map' t := by simp [e3, norm_smul]

/-- The plane-supported low-endpoint spectral measure
`μ_low = (c/2π) δ₀(dξ₁) δ₀(dξ₂) dξ₃` (main TeX lines 7405-7409): `c/(2π)` times the image of
Lebesgue measure under `t ↦ t e₃`. -/
def planeLowSpectral (c : ℝ) : Measure (Rd 3) :=
  ENNReal.ofReal (c / (2 * π)) • (volume : Measure ℝ).map lineE3

/-- Auxiliary to the Lean proof route: in the convention of `H:homog`,
`∫ φ(x) e^{iξ·x} dx = 𝓕φ(-ξ/(2π))` (Mathlib's `𝓕`), any dimension. -/
theorem inner_integral_eq_fourier (φ : Rd n → ℂ) (ξ : Rd n) :
    ∫ x, φ x * Complex.exp (Complex.I * (inner ℝ ξ x : ℝ)) =
      𝓕 φ (-(2 * Real.pi)⁻¹ • ξ) := by
  rw [Real.fourier_eq]
  congr 1; ext x
  rw [Circle.smul_def, Real.fourierChar_apply, mul_comm]
  congr 2
  rw [real_inner_smul_right, real_inner_comm]
  push_cast
  field_simp

/-- The spectral identity of the low plane endpoint (main TeX lines 7405-7411): for every
Schwartz `φ`, `∫ φ d(c m) = ∫ (∫ φ(x) e^{iξ·x} dx) μ_low(dξ)` with
`μ_low = (c/2π) δ₀ δ₀ dξ₃`; equivalently `∫_ℝ 𝓕φ(s e₃) ds = ∫_{ℝ²} φ(y, 0) dy`
(projection-slice, by Fubini and one-dimensional Fourier inversion). -/
theorem planeLow_isSpectral {c : ℝ} (hc : 0 ≤ c) :
    IsSpectralMeasure (planeMeasure c 0) (planeLowSpectral c) := by
  intro φ
  have hmp := measurePreserving_planeCoord
  have hιe : MeasurableEmbedding (planeEmb : Rd 2 → Rd 3) :=
    planeEmb.isometry.isClosedEmbedding.measurableEmbedding
  have hle : MeasurableEmbedding (lineE3 : ℝ → Rd 3) :=
    lineE3.isometry.isClosedEmbedding.measurableEmbedding
  -- the slice function `Φ(z) = ∫ φ(y, z) dy`
  set Φ : ℝ → ℂ := fun z => ∫ y : Rd 2, φ (planeCoord (y, z)) with hΦ
  have hφint : Integrable (fun p : Rd 2 × ℝ => φ (planeCoord p))
      ((volume : Measure (Rd 2)).prod volume) :=
    hmp.integrable_comp_of_integrable φ.integrable
  have hΦint : Integrable Φ := hφint.integral_prod_right
  -- Schwartz decay of `φ`
  obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ x, (1 + ‖x‖) ^ 3 * ‖φ x‖ ≤ C := by
    refine ⟨2 ^ 3 * (Finset.Iic ((3 : ℕ), (0 : ℕ))).sup
      (fun m => SchwartzMap.seminorm ℂ m.1 m.2) φ, fun x => ?_⟩
    have := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ) (m := ((3 : ℕ), (0 : ℕ)))
      (k := 3) (n := 0) le_rfl le_rfl φ x
    rwa [norm_iteratedFDeriv_zero] at this
  have hΦc : Continuous Φ := by
    refine continuous_of_dominated (bound := fun y : Rd 2 => C * ((1 + ‖y‖) ^ (3 : ℕ))⁻¹)
      (fun z => ?_) (fun z => Eventually.of_forall fun y => ?_) ?_
      (Eventually.of_forall fun y => ?_)
    · exact (φ.continuous.comp (by unfold planeCoord; fun_prop)).aestronglyMeasurable
    · have h1 := hC (planeCoord (y, z))
      have hpos : 0 < (1 + ‖planeCoord (y, z)‖) ^ 3 := by positivity
      have h2 : (1 + ‖y‖) ^ 3 ≤ (1 + ‖planeCoord (y, z)‖) ^ 3 := by
        have := norm_le_norm_planeCoord (y, z)
        gcongr
      rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]
      calc ‖φ (planeCoord (y, z))‖ * (1 + ‖y‖) ^ 3
          ≤ ‖φ (planeCoord (y, z))‖ * (1 + ‖planeCoord (y, z)‖) ^ 3 := by gcongr
        _ ≤ C := by rw [mul_comm]; exact h1
    · have hI := (integrable_one_add_norm (E := Rd 2) (μ := volume) (r := 3)
        (by simp; norm_num)).const_mul C
      refine hI.congr (Eventually.of_forall fun y => ?_)
      simp only
      rw [Real.rpow_neg (by positivity), ← Real.rpow_natCast]
      norm_num
    · exact φ.continuous.comp (by unfold planeCoord; fun_prop)
  -- the Fourier transform of `Φ` is the restriction of `𝓕φ` to the normal line
  have hFΦ : ∀ s : ℝ, 𝓕 Φ s = 𝓕 (φ : Rd 3 → ℂ) (s • e3) := by
    intro s
    rw [Real.fourier_real_eq, Real.fourier_eq]
    have hint2 : Integrable (fun p : Rd 2 × ℝ => 𝐞 (-(p.2 * s)) • φ (planeCoord p))
        ((volume : Measure (Rd 2)).prod volume) := by
      refine hφint.norm.mono' ?_ (Eventually.of_forall fun p => ?_)
      · exact (Continuous.aestronglyMeasurable (by
          unfold planeCoord; fun_prop))
      · rw [Circle.norm_smul]
    calc ∫ v : ℝ, 𝐞 (-(v * s)) • Φ v
        = ∫ v : ℝ, ∫ y : Rd 2, 𝐞 (-(v * s)) • φ (planeCoord (y, v)) := by
          congr 1; funext v
          simp_rw [Circle.smul_def]
          exact (integral_const_mul _ _).symm
      _ = ∫ p : Rd 2 × ℝ, 𝐞 (-(p.2 * s)) • φ (planeCoord p)
            ∂((volume : Measure (Rd 2)).prod volume) := (integral_prod_symm _ hint2).symm
      _ = ∫ p : Rd 2 × ℝ, 𝐞 (-⟪planeCoord p, s • e3⟫_ℝ) • φ (planeCoord p)
            ∂((volume : Measure (Rd 2)).prod volume) := by
          congr 1; funext p; rw [inner_planeCoord_e3]
      _ = ∫ x : Rd 3, 𝐞 (-⟪x, s • e3⟫_ℝ) • φ x :=
          hmp.integral_comp measurableEmbedding_planeCoord (fun x => 𝐞 (-⟪x, s • e3⟫_ℝ) • φ x)
  have hFΦint : Integrable (𝓕 Φ) := by
    have hg : (lineE3 : ℝ → Rd 3).HasTemperateGrowth :=
      lineE3.toContinuousLinearMap.hasTemperateGrowth
    have h'g : AntilipschitzWith 1 (lineE3 : ℝ → Rd 3) := lineE3.isometry.antilipschitzWith
    have hI := (SchwartzMap.compCLMOfAntilipschitz ℂ hg h'g (𝓕 φ)).integrable
      (μ := (volume : Measure ℝ))
    rw [SchwartzMap.compCLMOfAntilipschitz_apply, SchwartzMap.fourier_coe] at hI
    refine hI.congr (Eventually.of_forall fun s => ?_)
    rw [hFΦ]; rfl
  have hinv : ∫ s, 𝓕 Φ s = Φ 0 := by
    have h0 := hΦint.fourierInv_fourier_eq hFΦint hΦc.continuousAt (v := 0)
    rw [Real.fourierInv_eq] at h0
    simpa using h0
  have hL : ∫ x, φ x ∂(planeMeasure c 0) = (c : ℂ) * Φ 0 := by
    rw [planeMeasure_zero, integral_smul_measure, hιe.integral_map, ENNReal.toReal_ofReal hc,
      Complex.real_smul]
    rfl
  have hR : ∫ ξ, (∫ x, φ x * Complex.exp (Complex.I * (inner ℝ ξ x : ℝ)))
      ∂(planeLowSpectral c) = (c : ℂ) * Φ 0 := by
    rw [planeLowSpectral, integral_smul_measure, hle.integral_map,
      ENNReal.toReal_ofReal (by positivity)]
    have hpt : ∀ t : ℝ, (∫ x, φ x * Complex.exp (Complex.I * (inner ℝ (lineE3 t) x : ℝ))) =
        𝓕 Φ (-(2 * π)⁻¹ * t) := by
      intro t
      rw [inner_integral_eq_fourier, hFΦ]
      simp [lineE3, smul_smul]
    simp_rw [hpt]
    rw [Measure.integral_comp_mul_left (fun s => 𝓕 Φ s) (-(2 * π)⁻¹), hinv, inv_neg, inv_inv,
      abs_neg, abs_of_pos (by positivity), smul_smul, Complex.real_smul]
    congr 1
    push_cast
    field_simp
  rw [hL, hR]

/-- `V_low = μ_low(B₁) = c/π` for the closed unit ball (the convention of
`L:alpha-one-convolution`, main TeX lines 5559, 7411-7412), `c ≥ 0`. -/
theorem planeLowSpectral_closedBall {c : ℝ} (hc : 0 ≤ c) :
    planeLowSpectral c (closedBall 0 1) = ENNReal.ofReal (c / π) := by
  have hpre : (lineE3 : ℝ → Rd 3) ⁻¹' closedBall 0 1 = closedBall (0 : ℝ) 1 := by
    ext t; simp
  rw [planeLowSpectral, Measure.smul_apply, Measure.map_apply lineE3.continuous.measurable
    measurableSet_closedBall, hpre, Real.volume_closedBall, smul_eq_mul,
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1; field_simp

/-- The same mass for the open unit ball (`μ(B_1)`, main TeX line 1069). -/
theorem planeLowSpectral_ball {c : ℝ} (hc : 0 ≤ c) :
    planeLowSpectral c (ball 0 1) = ENNReal.ofReal (c / π) := by
  have hpre : (lineE3 : ℝ → Rd 3) ⁻¹' ball 0 1 = ball (0 : ℝ) 1 := by
    ext t; simp
  rw [planeLowSpectral, Measure.smul_apply, Measure.map_apply lineE3.continuous.measurable
    measurableSet_ball, hpre, Real.volume_ball, smul_eq_mul,
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1; field_simp

/-- The exponent facts of `L:plane-endpoints` (main TeX lines 7343-7347): for `0 < θ < 2 - α`,
`a_j ≥ 0`, `a₁ + a₂ = α - 1`: `0 ≤ a_j < 1`, `0 ≤ v_j < 1` with `v_j = a_j/(1 - θ)`, and
`v₁ + v₂ = χ - 1 < 1`. -/
theorem plane_exponents {α θ : ℝ} {a : Fin 2 → ℝ} (hα1 : 1 < α) (hθpos : 0 < θ)
    (hθ : θ < 2 - α) (ha : ∀ j, 0 ≤ a j) (hs : a 0 + a 1 = α - 1) :
    (∀ j, 0 ≤ a j ∧ a j < 1) ∧ (∀ j, 0 ≤ a j / (1 - θ) ∧ a j / (1 - θ) < 1) ∧
      a 0 / (1 - θ) + a 1 / (1 - θ) = chi α θ - 1 ∧ chi α θ - 1 < 1 := by
  have h1θ : 0 < 1 - θ := by linarith
  have hsum : ∀ j : Fin 2, a j ≤ a 0 + a 1 := by
    intro j; fin_cases j <;> simp <;> linarith [ha 0, ha 1]
  have hvs : a 0 / (1 - θ) + a 1 / (1 - θ) = chi α θ - 1 := by
    rw [chi, ← add_div, hs]; field_simp; ring
  refine ⟨fun j => ⟨ha j, by linarith [hsum j]⟩, fun j => ⟨div_nonneg (ha j) h1θ.le,
    (div_lt_one h1θ).2 (by linarith [hsum j])⟩, hvs, ?_⟩
  rw [← hvs, ← add_div, div_lt_one h1θ, hs]; linarith

/-- `L:plane-endpoints` (main TeX lines 7316-7332; proof 7334-7415), with the manuscript's
hypotheses (`E:three-parameters`: `0 < α₀ < 1`, `1 < α < 2 - α₀`, `α₀ < θ < 2 - α`;
`c > 0`, `a₁, a₂ ≥ 0`, `a₁ + a₂ = α - 1`) and the supplied input `PlaneRieszPD`: the
exponent facts, the covariance properties of the three plane measures with scaling exponents
`3 - α`, `2`, `3 - χ`, the comparison (so `(c m, c ∏|y_j|^{-v_j} m)` is an endpoint pair for
`Γ_pl`), `Γ_low = c m`, its spectral measure `μ_low = (c/2π) δ₀ δ₀ dξ₃`, `V_low = c/π`, and
the closing bound `π V_low / 2 = c/2` of `L:alpha-one-convolution`. -/
theorem plane_endpoints_paper (hPD : PlaneRieszPD) {α₀ α θ c : ℝ} {a : Fin 2 → ℝ}
    (hα₀ : 0 < α₀) (_hα₀1 : α₀ < 1) (hα1 : 1 < α) (_hα2 : α < 2 - α₀) (hθ0 : α₀ < θ)
    (hθ : θ < 2 - α) (hc : 0 < c) (ha : ∀ j, 0 ≤ a j) (hs : a 0 + a 1 = α - 1) :
    ((∀ j, 0 ≤ a j ∧ a j < 1) ∧ (∀ j, 0 ≤ a j / (1 - θ) ∧ a j / (1 - θ) < 1) ∧
      a 0 / (1 - θ) + a 1 / (1 - θ) = chi α θ - 1 ∧ chi α θ - 1 < 1) ∧
    (IsCov (planeMeasure c a) ∧ Scaling (planeMeasure c a) (3 - α)) ∧
    EndpointPair θ (chi α θ) (planeMeasure c a) (planeMeasure c 0)
      (planeMeasure c fun j => a j / (1 - θ)) ∧
    planeMeasure c 0 = ENNReal.ofReal c • (volume : Measure (Rd 2)).map planeEmb ∧
    (IsSpectralMeasure (planeMeasure c 0) (planeLowSpectral c) ∧
      planeLowSpectral c (closedBall 0 1) = ENNReal.ofReal (c / π) ∧
      planeLowSpectral c (ball 0 1) = ENNReal.ofReal (c / π) ∧ π * (c / π) / 2 = c / 2) := by
  have hθpos : 0 < θ := by linarith
  have hθ1 : θ < 1 := by linarith
  obtain ⟨ha', hv', hvs, hχ⟩ := plane_exponents hα1 hθpos hθ ha hs
  have h0 : ∀ j, 0 ≤ (0 : Fin 2 → ℝ) j ∧ (0 : Fin 2 → ℝ) j < 1 := fun j => by simp
  have cov : ∀ e : Fin 2 → ℝ, (∀ j, 0 ≤ e j ∧ e j < 1) →
      IsCov (planeMeasure c e) ∧ Scaling (planeMeasure c e) (2 - ∑ j, e j) := by
    intro e he
    obtain ⟨h1, h2, h3, h4⟩ := plane_props hc.le he
    exact ⟨⟨h1, h2, h3, hPD c e hc.le he⟩, h4⟩
  have cpl := cov a ha'
  have clow := cov 0 h0
  have cst := cov _ hv'
  rw [Fin.sum_univ_two, hs, show (2 : ℝ) - (α - 1) = 3 - α by ring] at cpl
  rw [Fin.sum_univ_two, hvs, show (2 : ℝ) - (chi α θ - 1) = 3 - chi α θ by ring] at cst
  simp only [Pi.zero_apply, Finset.sum_const_zero, sub_zero] at clow
  refine ⟨⟨ha', hv', hvs, hχ⟩, cpl, ⟨clow.1, cst.1, clow.2, cst.2,
    plane_comparison hc hθpos hθ1 a⟩, planeMeasure_zero c,
    ⟨planeLow_isSpectral hc.le, planeLowSpectral_closedBall hc.le, planeLowSpectral_ball hc.le,
      by field_simp⟩⟩


end StratonovichHAMSecondMoment.EndpointLemmas
