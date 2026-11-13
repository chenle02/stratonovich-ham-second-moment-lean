module

/-
Copyright 2026 Le Chen. SPDX-License-Identifier: Apache-2.0

`P:clock-copy-obstruction` (Obstruction to unweighted constant-correlation
clock copying), main TeX file `notes/notes_stratonovich_ham_second_moment.tex`
(revision a284420), lines 7754-7905, with its objects defined at lines
7699-7762: `Ψ_a` (`E:averaged-clock-kernel`, in `TimeFractional`),
`h_Γ` and `R_Γ` (in `SpectralHomog`), `K_Γ(θ) = N₂(θ)²` (in `DampedNorms`),
`v_ρ` and the candidate `J_{Γ,ρ}` (`E:naive-clock-candidate`), and the weight
`w_θ` (`E:cross-clock-lambda-weight`).

Statement formalized (`clock_copy_obstruction_paper`), under `H:homog`
(`HomogHypothesis.HomogCovariance`, temporal exponent `a = α₀`), `Γ ≠ 0`,
`θ > 0`, `-1 ≤ ρ ≤ 1`, and the one supplied input
`SpectralHomog.SpectralHomogeneous μ α` (see that module):
* `w_θ(λ) > 0` for `λ > 0` and `w_θ` is integrable on `(0,∞)`;
* `K_Γ(θ) = ∫_0^∞ w_θ` (the outer integrand of `N₂(θ)²` integrable);
* the candidate integrands are integrable, `0 < J_{Γ,ρ}(θ) ≤ J_{Γ,1}(θ)`,
  `J_{Γ,1}(θ) = ∫_0^∞ 2θ/(2θ+λ) w_θ(λ) dλ` (integrable) and
  `J_{Γ,1}(θ) < K_Γ(θ)` (`E:clock-copy-obstruction`);
* if `α = 1`, `J_{Γ,1}(θ) = (2-2^a) K_Γ(θ)` (`E:degree-one-clock-loss`).
Also `damped_N2_nonneg_paper`: `N₂(θ)² ≥ 0` under `H:homog` (the
nonnegativity claim of `L:damped-homogeneous-norms`), as a corollary of the
exact formula.

Conventions made explicit: integrals over `(0,∞)` and `(0,∞)²` are Bochner
integrals for Lebesgue measure (`TimeFractional.L0`, `TimeFractional.P2`);
the candidate's integrand is `Jintegrand`, with `Ψ_a(θ|u-v|, v_ρ)` whose value
on the diagonal `u = v` (a null set; the manuscript notes it is irrelevant) is
Lean's junk value.  Every integral the manuscript asserts to be finite comes
with a proved integrability conclusion; the scaling identity
`integral_rpow_div_add_scaling` is an identity of totalized integrals and
carries none (integrability is `integrable_rpow_div_add`, `0 < a < 1`).

Proof route (differs from the TeX, same statements):
* `K` side: instead of temporarily smoothing the spatial covariance and
  passing to the limit by monotone convergence, the power kernel is expanded
  by subordination and Fubini is applied directly on
  `(0,∞) × ℝ^d × (0,∞)²`, justified by the absolute majorant of
  `DampedNorms.FK_integrable`.  This is not the route after
  "Alternatively" in the manuscript, which bounds the density `w_θ` by
  homogeneity; `weight_integrable` uses bounds of that shape without
  homogeneity.  The inner time integral (`cross_transform`, the
  first display of the proof) is computed from the complex two-time Laplace
  lemma at `a, b = θ ∓ i|ξ|`, using `μ{0} = 0` for `ξ ≠ 0`.
* `J` side: the `q`-integration and the 𝓡 identity
  `R_Γ(q) = ½∫ e^{-q²w/2} h_Γ(w) dw` are replaced by the real two-time
  Laplace lemma at `c = (θ²+|ξ|²)/2`, `λ ↦ θλ+λ²/2`; integrability of the
  `J_{Γ,1}` integrand comes from Tonelli and the finiteness of
  `∫ 2θ/(2θ+λ) w_θ`, and `J_{Γ,ρ}` is dominated by `J_{Γ,1}` (the manuscript's
  majorant via `Ψ_a ≤ r^{-a}` and the homogeneity of `h_Γ` is not needed).
* `α = 1`: only the scaling `∫ λ^{a-1}/(c+λ) dλ = c^{a-1} ∫ λ^{a-1}/(1+λ) dλ`
  is used, not the Beta value (the ratio does not depend on it).
Partial fractions and the strict inequality reuse
`StratonovichHAMAudit.ClockFilter`.
-/

public import Mathlib
public import StratonovichHAMAudit.ClockFilter
public import StratonovichHAMSecondMoment.HomogHypothesis
public import StratonovichHAMSecondMoment.TimeFractional
public import StratonovichHAMSecondMoment.SpectralHomog
public import StratonovichHAMSecondMoment.WaveKernel
public import StratonovichHAMSecondMoment.DampedNorms

@[expose] public section

noncomputable section

set_option autoImplicit false

open MeasureTheory Set Real Filter
open scoped ENNReal

namespace StratonovichHAMSecondMoment.ClockCopy

open HomogHypothesis TimeFractional SpectralHomog WaveKernel DampedNorms

/-- `R_Γ` (`SpectralHomog.resolvent`), written `𝓡` as in the TeX. -/
local notation "𝓡" => SpectralHomog.resolvent

variable {d : ℕ}

/-! ### Definitions -/

/-- `w_θ(λ) = λ^{a-2}/(2θΓ(a)) (R_Γ(θ) - R_Γ(θ+λ))`
(`E:cross-clock-lambda-weight`, lines 7756-7762). -/
def weight (a θ : ℝ) (μ : Measure (Rd d)) (l : ℝ) : ℝ :=
  l ^ (a - 2) / (2 * θ * Real.Gamma a) * (𝓡 μ θ - 𝓡 μ (θ + l))

/-- The integrand `2θ/(2θ+λ) w_θ(λ)` of `J_{Γ,1}` in `E:clock-copy-obstruction`. -/
def filteredWeight (a θ : ℝ) (μ : Measure (Rd d)) (l : ℝ) : ℝ :=
  2 * θ / (2 * θ + l) * weight a θ μ l

/-- `v_ρ(u,v) = u + v - 2ρ min(u,v)` (line 7737). -/
def vRho (ρ u v : ℝ) : ℝ := u + v - 2 * ρ * min u v

/-- The integrand of `E:naive-clock-candidate`:
`e^{-θ²(u+v)/2} h_Γ(u+v) Ψ_a(θ|u-v|, v_ρ(u,v))`. -/
def Jintegrand (a θ : ℝ) (μ : Measure (Rd d)) (ρ : ℝ) (p : ℝ × ℝ) : ℝ :=
  Real.exp (-(θ ^ 2 * (p.1 + p.2) / 2)) * heat μ (p.1 + p.2) *
    Psi a (θ * |p.1 - p.2|) (vRho ρ p.1 p.2)

/-- `J_{Γ,ρ}(θ)` of `E:naive-clock-candidate` (lines 7741-7746). -/
def J (a θ : ℝ) (μ : Measure (Rd d)) (ρ : ℝ) : ℝ :=
  1 / 4 * ∫ p, Jintegrand a θ μ ρ p ∂P2

/-- The subordinated integrand of `J_{Γ,1}` on `(0,∞) × ℝ^d × (0,∞)²`
(auxiliary to the Lean proof route). -/
def FJ (a θ : ℝ) (z : ℝ × (Rd d × (ℝ × ℝ))) : ℝ :=
  1 / 4 * (Real.Gamma a)⁻¹ * |z.1| ^ (a - 1) *
    twoTimeR ((θ ^ 2 + ‖z.2.1‖ ^ 2) / 2) (θ * |z.1| + |z.1| ^ 2 / 2) z.2.2

/-! ### Elementary facts -/

/-- `v_1(u,v) = |u-v|` (line 7844). -/
theorem vRho_one (u v : ℝ) : vRho 1 u v = |u - v| := by
  unfold vRho
  rcases le_total u v with h | h
  · rw [min_eq_left h, abs_of_nonpos (by linarith)]; ring
  · rw [min_eq_right h, abs_of_nonneg (by linarith)]; ring

/-- `v_ρ(u,v) ≥ |u-v|` for `ρ ≤ 1`, `u, v ≥ 0` (line 7844). -/
theorem abs_le_vRho (ρ u v : ℝ) (hρ : ρ ≤ 1) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    |u - v| ≤ vRho ρ u v := by
  rw [← vRho_one]
  unfold vRho
  have : 0 ≤ min u v := le_min hu hv
  nlinarith

/-- Auxiliary to the Lean proof route. -/
theorem resolvent_measurable (μ : Measure (Rd d)) [SFinite μ] :
    Measurable fun q => 𝓡 μ q := by
  have h : StronglyMeasurable fun z : ℝ × Rd d => 1 / (z.1 ^ 2 + ‖z.2‖ ^ 2) :=
    (by fun_prop : Measurable fun z : ℝ × Rd d =>
      1 / (z.1 ^ 2 + ‖z.2‖ ^ 2)).stronglyMeasurable
  exact h.integral_prod_right'.measurable

/-- Auxiliary to the Lean proof route. -/
theorem heat_measurable (μ : Measure (Rd d)) [SFinite μ] :
    Measurable fun w => heat μ w := by
  have h : StronglyMeasurable fun z : ℝ × Rd d => Real.exp (-(z.1 * ‖z.2‖ ^ 2 / 2)) :=
    (by fun_prop : Measurable fun z : ℝ × Rd d =>
      Real.exp (-(z.1 * ‖z.2‖ ^ 2 / 2))).stronglyMeasurable
  exact h.integral_prod_right'.measurable

/-- Auxiliary to the Lean proof route. -/
theorem Psi_measurable (a : ℝ) : Measurable fun z : ℝ × ℝ => Psi a z.1 z.2 := by
  have h : StronglyMeasurable fun z : (ℝ × ℝ) × ℝ => psiKernel a z.1.1 z.1.2 z.2 :=
    (by unfold psiKernel; fun_prop : Measurable fun z : (ℝ × ℝ) × ℝ =>
      psiKernel a z.1.1 z.1.2 z.2).stronglyMeasurable
  exact measurable_const.mul (h.integral_prod_right' (ν := L0)).measurable

/-- Auxiliary to the Lean proof route. -/
theorem heat_nonneg (μ : Measure (Rd d)) (w : ℝ) : 0 ≤ heat μ w :=
  integral_nonneg fun _ => (Real.exp_pos _).le

/-- Auxiliary to the Lean proof route. -/
theorem resolvent_nonneg (μ : Measure (Rd d)) (q : ℝ) : 0 ≤ 𝓡 μ q :=
  integral_nonneg fun _ => by positivity

/-- Auxiliary to the Lean proof route. Partial fractions: `1/(AB) = (1/A - 1/B)/(λ(2θ+λ))` with
`A = θ²+r²`,
`B = (θ+λ)²+r²`. -/
theorem inv_mul_partial (θ l r : ℝ) (hθ : 0 < θ) (hl : 0 < l) :
    1 / ((θ ^ 2 + r ^ 2) * ((θ + l) ^ 2 + r ^ 2)) =
      1 / (l * (2 * θ + l)) * (1 / (θ ^ 2 + r ^ 2) - 1 / ((θ + l) ^ 2 + r ^ 2)) := by
  have hA : θ ^ 2 + r ^ 2 ≠ 0 := ne_of_gt (by positivity)
  have hB : (θ + l) ^ 2 + r ^ 2 ≠ 0 := ne_of_gt (by positivity)
  have hC : l * (2 * θ + l) ≠ 0 := ne_of_gt (by positivity)
  field_simp
  ring

/-- Auxiliary to the Lean proof route. -/
theorem resolvent_le (μ : Measure (Rd d))
    (hR : Integrable (fun ξ : Rd d => 1 / (1 + ‖ξ‖ ^ 2)) μ)
    (q q' : ℝ) (hq : 0 < q) (hqq : q ≤ q') : 𝓡 μ q' ≤ 𝓡 μ q := by
  refine integral_mono (resolvent_integrable hR q' (by linarith))
    (resolvent_integrable hR q hq.ne') fun ξ => ?_
  have : 0 < q ^ 2 + ‖ξ‖ ^ 2 := by positivity
  exact one_div_le_one_div_of_le this (by nlinarith)

/-- Auxiliary to the Lean proof route. `R_Γ(θ) - R_Γ(θ+λ) ≤ λ(2θ+λ)θ⁻² R_Γ(θ)`. -/
theorem resolvent_sub_le (μ : Measure (Rd d))
    (hR : Integrable (fun ξ : Rd d => 1 / (1 + ‖ξ‖ ^ 2)) μ) (θ l : ℝ) (hθ : 0 < θ)
    (hl : 0 < l) :
    𝓡 μ θ - 𝓡 μ (θ + l) ≤ l * (2 * θ + l) / θ ^ 2 * 𝓡 μ θ := by
  unfold SpectralHomog.resolvent
  have h1 := resolvent_integrable hR θ hθ.ne'
  have h2 := resolvent_integrable hR (θ + l) (by linarith)
  rw [← integral_sub h1 h2, ← integral_const_mul]
  refine integral_mono (h1.sub h2) (h1.const_mul _) fun ξ => ?_
  have hA : 0 < θ ^ 2 + ‖ξ‖ ^ 2 := by positivity
  have hB : 0 < (θ + l) ^ 2 + ‖ξ‖ ^ 2 := by positivity
  have e : 1 / (θ ^ 2 + ‖ξ‖ ^ 2) - 1 / ((θ + l) ^ 2 + ‖ξ‖ ^ 2) =
      l * (2 * θ + l) / ((θ ^ 2 + ‖ξ‖ ^ 2) * ((θ + l) ^ 2 + ‖ξ‖ ^ 2)) := by
    field_simp; ring
  simp only
  rw [e, mul_one_div, div_div, div_le_div_iff₀ (by positivity) (by positivity)]
  have hn : 0 ≤ l * (2 * θ + l) := by positivity
  have : θ ^ 2 ≤ (θ + l) ^ 2 + ‖ξ‖ ^ 2 := by nlinarith [sq_nonneg ‖ξ‖]
  have := mul_le_mul_of_nonneg_left this (mul_nonneg hn hA.le)
  nlinarith

/-! ### The weight `w_θ` -/

/-- Auxiliary to the Lean proof route. -/
theorem weight_nonneg (μ : Measure (Rd d))
    (hR : Integrable (fun ξ : Rd d => 1 / (1 + ‖ξ‖ ^ 2)) μ) (a θ l : ℝ) (ha : 0 < a)
    (hθ : 0 < θ) (hl : 0 < l) : 0 ≤ weight a θ μ l := by
  have := Real.Gamma_pos_of_pos ha
  have := resolvent_le μ hR θ (θ + l) hθ (by linarith)
  have := Real.rpow_nonneg hl.le (a - 2)
  unfold weight
  exact mul_nonneg (by positivity) (by linarith)

/-- `w_θ(λ) > 0` for `λ > 0` when `μ ≠ 0`. -/
theorem weight_pos (μ : Measure (Rd d))
    (hR : Integrable (fun ξ : Rd d => 1 / (1 + ‖ξ‖ ^ 2)) μ) (hμ : μ ≠ 0) (a θ l : ℝ)
    (ha : 0 < a) (hθ : 0 < θ) (hl : 0 < l) : 0 < weight a θ μ l := by
  have := Real.Gamma_pos_of_pos ha
  have := resolvent_sub_pos hR hμ θ (θ + l) hθ (by linarith)
  have := Real.rpow_pos_of_pos hl (a - 2)
  unfold weight
  positivity

/-- Auxiliary to the Lean proof route. -/
theorem weight_measurable (μ : Measure (Rd d)) [SFinite μ] (a θ : ℝ) :
    Measurable (weight a θ μ) := by
  have h := resolvent_measurable μ
  have h2 : Measurable fun l : ℝ => 𝓡 μ (θ + l) := h.comp (by fun_prop)
  unfold weight
  fun_prop

/-- `w_θ` is integrable on `(0,∞)`. -/
theorem weight_integrable (μ : Measure (Rd d)) [SFinite μ]
    (hR : Integrable (fun ξ : Rd d => 1 / (1 + ‖ξ‖ ^ 2)) μ) (a θ : ℝ) (ha0 : 0 < a)
    (ha1 : a < 1) (hθ : 0 < θ) : Integrable (weight a θ μ) L0 := by
  have hG := Real.Gamma_pos_of_pos ha0
  have hR0 := resolvent_nonneg μ θ
  set D := 2 * θ * Real.Gamma a
  have hD : 0 < D := by positivity
  refine integrable_of_rpow_bounds (a - 1) (a - 2)
    ((2 * θ + 1) / θ ^ 2 * 𝓡 μ θ / D + 𝓡 μ θ / D) (by linarith) (by linarith)
    (weight_measurable μ a θ).aestronglyMeasurable ?_ ?_
  · intro l hl hl1
    rw [Real.norm_of_nonneg (weight_nonneg μ hR a θ l ha0 hθ hl)]
    have hs := resolvent_sub_le μ hR θ l hθ hl
    have hp : l ^ (a - 1) = l ^ (a - 2) * l := by
      rw [show a - 1 = (a - 2) + 1 by ring, Real.rpow_add_one hl.ne']
    have hq := Real.rpow_nonneg hl.le (a - 2)
    unfold weight
    rw [hp]
    have h1 : l * (2 * θ + l) / θ ^ 2 * 𝓡 μ θ ≤
        l * ((2 * θ + 1) / θ ^ 2 * 𝓡 μ θ) := by
      rw [div_mul_eq_mul_div, div_mul_eq_mul_div, mul_div_assoc', div_le_div_iff_of_pos_right
        (by positivity)]
      have : 2 * θ + l ≤ 2 * θ + 1 := by linarith
      nlinarith [mul_le_mul_of_nonneg_left this (mul_nonneg hl.le hR0)]
    have h2 := hs.trans h1
    have h3 : 0 ≤ 𝓡 μ θ / D := div_nonneg hR0 hD.le
    calc l ^ (a - 2) / D * (𝓡 μ θ - 𝓡 μ (θ + l))
        ≤ l ^ (a - 2) / D * (l * ((2 * θ + 1) / θ ^ 2 * 𝓡 μ θ)) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = (2 * θ + 1) / θ ^ 2 * 𝓡 μ θ / D * (l ^ (a - 2) * l) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_add_of_nonneg_right h3) (by positivity)
  · intro l hl
    have hl0 : 0 < l := lt_trans zero_lt_one hl
    rw [Real.norm_of_nonneg (weight_nonneg μ hR a θ l ha0 hθ hl0)]
    have hR1 := resolvent_nonneg μ (θ + l)
    have hq := Real.rpow_nonneg hl0.le (a - 2)
    unfold weight
    have h0 : 0 ≤ (2 * θ + 1) / θ ^ 2 * 𝓡 μ θ / D := by positivity
    calc l ^ (a - 2) / D * (𝓡 μ θ - 𝓡 μ (θ + l))
        ≤ l ^ (a - 2) / D * 𝓡 μ θ :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = 𝓡 μ θ / D * l ^ (a - 2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_add_of_nonneg_left h0) hq

/-- Auxiliary to the Lean proof route. -/
theorem filteredWeight_integrable (μ : Measure (Rd d)) [SFinite μ]
    (hR : Integrable (fun ξ : Rd d => 1 / (1 + ‖ξ‖ ^ 2)) μ) (a θ : ℝ) (ha0 : 0 < a)
    (ha1 : a < 1) (hθ : 0 < θ) : Integrable (filteredWeight a θ μ) L0 := by
  refine (weight_integrable μ hR a θ ha0 ha1 hθ).mono'
    ((by fun_prop : Measurable fun l : ℝ => 2 * θ / (2 * θ + l)).mul
      (weight_measurable μ a θ)).aestronglyMeasurable ?_
  filter_upwards [ae_L0_pos] with l hl
  have hw := weight_nonneg μ hR a θ l ha0 hθ hl
  have hb := StratonovichHAMAudit.ClockFilter.clock_filter_bounds θ l hθ hl
  rw [filteredWeight, Real.norm_of_nonneg (mul_nonneg hb.1.le hw)]
  exact mul_le_of_le_one_left hw hb.2.le

/-! ### The spectral integrals at fixed `λ` -/

/-- `∫ Γ(a)⁻¹λ^{a-1}/((θ²+|ξ|²)((θ+λ)²+|ξ|²)) μ(dξ) = 2θ/(2θ+λ) w_θ(λ)`. -/
theorem xi_integral_J (μ : Measure (Rd d))
    (hR : Integrable (fun ξ : Rd d => 1 / (1 + ‖ξ‖ ^ 2)) μ) (a θ l : ℝ) (hθ : 0 < θ)
    (hl : 0 < l) :
    Integrable (fun ξ : Rd d => (Real.Gamma a)⁻¹ * l ^ (a - 1) /
        ((θ ^ 2 + ‖ξ‖ ^ 2) * ((θ + l) ^ 2 + ‖ξ‖ ^ 2))) μ ∧
      ∫ ξ, (Real.Gamma a)⁻¹ * l ^ (a - 1) /
          ((θ ^ 2 + ‖ξ‖ ^ 2) * ((θ + l) ^ 2 + ‖ξ‖ ^ 2)) ∂μ =
        filteredWeight a θ μ l := by
  have h1 := resolvent_integrable hR θ hθ.ne'
  have h2 := resolvent_integrable hR (θ + l) (by linarith)
  have hpt : (fun ξ : Rd d => (Real.Gamma a)⁻¹ * l ^ (a - 1) /
      ((θ ^ 2 + ‖ξ‖ ^ 2) * ((θ + l) ^ 2 + ‖ξ‖ ^ 2))) = fun ξ =>
      ((Real.Gamma a)⁻¹ * l ^ (a - 1) * (1 / (l * (2 * θ + l)))) *
        (1 / (θ ^ 2 + ‖ξ‖ ^ 2) - 1 / ((θ + l) ^ 2 + ‖ξ‖ ^ 2)) := by
    funext ξ
    rw [mul_assoc, ← inv_mul_partial θ l ‖ξ‖ hθ hl]
    ring
  rw [hpt]
  refine ⟨(h1.sub h2).const_mul _, ?_⟩
  rw [integral_const_mul, integral_sub h1 h2]
  unfold filteredWeight weight SpectralHomog.resolvent
  have hp : l ^ (a - 1) = l ^ (a - 2) * l := by
    rw [show a - 1 = (a - 2) + 1 by ring, Real.rpow_add_one hl.ne']
  rw [hp]
  rcases eq_or_ne (Real.Gamma a) 0 with hG | hG
  · simp [hG]
  · field_simp

/-- `∫ Γ(a)⁻¹λ^{a-1} (2θ+λ)/(2θ(θ²+|ξ|²)((θ+λ)²+|ξ|²)) μ(dξ) = w_θ(λ)`. -/
theorem xi_integral_K (μ : Measure (Rd d))
    (hR : Integrable (fun ξ : Rd d => 1 / (1 + ‖ξ‖ ^ 2)) μ) (a θ l : ℝ) (hθ : 0 < θ)
    (hl : 0 < l) :
    ∫ ξ, (Real.Gamma a)⁻¹ * l ^ (a - 1) *
        ((2 * θ + l) / (2 * θ * (θ ^ 2 + ‖ξ‖ ^ 2) * ((θ + l) ^ 2 + ‖ξ‖ ^ 2))) ∂μ =
      weight a θ μ l := by
  have h1 := resolvent_integrable hR θ hθ.ne'
  have h2 := resolvent_integrable hR (θ + l) (by linarith)
  simp_rw [StratonovichHAMAudit.ClockFilter.resolvent_partial_fraction θ l _ hθ hl]
  simp_rw [div_eq_mul_inv (1 / (θ ^ 2 + _) - _), mul_comm (1 / (θ ^ 2 + _) - _)]
  simp_rw [← mul_assoc]
  rw [integral_const_mul, integral_sub h1 h2]
  unfold weight SpectralHomog.resolvent
  have hp : l ^ (a - 1) = l ^ (a - 2) * l := by
    rw [show a - 1 = (a - 2) + 1 by ring, Real.rpow_add_one hl.ne']
  rw [hp]
  rcases em (Real.Gamma a = 0) with hG | hG
  · simp [hG]
  · field_simp

/-! ### The cross transform at fixed `(λ, ξ)` -/

/-- The first display of the proof of `P:clock-copy-obstruction` (lines
7787-7793): for
`ξ ≠ 0`, `λ ≥ 0`, `θ > 0`,
`∫∫ e^{-θ(s+t)-λ|s-t|} Ĝ_s(ξ) Ĝ_t(ξ) ds dt
  = (2θ+λ)/(2θ(θ²+|ξ|²)((θ+λ)²+|ξ|²))`. -/
theorem cross_transform (θ l : ℝ) (hθ : 0 < θ) (hl : 0 ≤ l) (ξ : Rd d) (hξ : ξ ≠ 0) :
    Integrable (fun p : ℝ × ℝ => twoTimeR θ l p * (waveHat p.1 ξ * waveHat p.2 ξ)) P2 ∧
      ∫ p, twoTimeR θ l p * (waveHat p.1 ξ * waveHat p.2 ξ) ∂P2 =
        (2 * θ + l) / (2 * θ * (θ ^ 2 + ‖ξ‖ ^ 2) * ((θ + l) ^ 2 + ‖ξ‖ ^ 2)) := by
  set r := ‖ξ‖ with hr_def
  have hr : 0 < r := norm_pos_iff.2 hξ
  set a1 : ℂ := (θ : ℂ) - (r : ℂ) * Complex.I
  set b1 : ℂ := (θ : ℂ) + (r : ℂ) * Complex.I
  have ha1 : 0 < a1.re := by simp [a1, hθ]
  have hb1 : 0 < b1.re := by simp [b1, hθ]
  obtain ⟨hC1, hV1⟩ := twoTimeC_integral a1 b1 l ha1 hb1 hl
  obtain ⟨hC2, hV2⟩ := twoTimeC_integral a1 a1 l ha1 ha1 hl
  have hpt : ∀ p : ℝ × ℝ, twoTimeR θ l p * (waveHat p.1 ξ * waveHat p.2 ξ) =
      1 / (2 * r ^ 2) * (twoTimeC a1 b1 l p - twoTimeC a1 a1 l p).re := by
    intro p
    rw [waveHat_of_ne_zero _ _ hξ, waveHat_of_ne_zero _ _ hξ, ← hr_def, Complex.sub_re]
    simp only [twoTimeC, Complex.exp_re]
    have e1 : (-(a1 * (p.1 : ℂ)) - b1 * (p.2 : ℂ) -
        (l : ℂ) * ((|p.1 - p.2| : ℝ) : ℂ)).re =
        -(θ * (p.1 + p.2)) - l * |p.1 - p.2| := by simp [a1, b1]; ring
    have e2 : (-(a1 * (p.1 : ℂ)) - b1 * (p.2 : ℂ) -
        (l : ℂ) * ((|p.1 - p.2| : ℝ) : ℂ)).im =
        p.1 * r - p.2 * r := by simp [a1, b1]; ring
    have e3 : (-(a1 * (p.1 : ℂ)) - a1 * (p.2 : ℂ) -
        (l : ℂ) * ((|p.1 - p.2| : ℝ) : ℂ)).re =
        -(θ * (p.1 + p.2)) - l * |p.1 - p.2| := by simp [a1]; ring
    have e4 : (-(a1 * (p.1 : ℂ)) - a1 * (p.2 : ℂ) -
        (l : ℂ) * ((|p.1 - p.2| : ℝ) : ℂ)).im =
        p.1 * r + p.2 * r := by simp [a1]; ring
    rw [e1, e2, e3, e4, twoTimeR, Real.cos_sub, Real.cos_add]
    field_simp
    ring
  have hI : Integrable (fun p : ℝ × ℝ => twoTimeR θ l p * (waveHat p.1 ξ * waveHat p.2 ξ))
      P2 := by
    refine (((hC1.sub hC2).re).const_mul (1 / (2 * r ^ 2))).congr
      (Eventually.of_forall fun p => ?_)
    simp only [RCLike.re_to_complex, Pi.sub_apply, hpt]
  refine ⟨hI, ?_⟩
  simp_rw [hpt]
  rw [integral_const_mul]
  have hre := integral_re (hC1.sub hC2)
  simp only [RCLike.re_to_complex, Pi.sub_apply] at hre
  rw [hre, integral_sub hC1 hC2, hV1, hV2, Complex.sub_re]
  -- the first term is real
  have hsum : a1 + b1 + 2 * (l : ℂ) = ((2 * θ + 2 * l : ℝ) : ℂ) := by
    simp only [a1, b1]
    push_cast
    ring
  have hden : (a1 + b1) * (a1 + l) * (b1 + l) =
      ((2 * θ * ((θ + l) ^ 2 + r ^ 2) : ℝ) : ℂ) := by
    simp only [a1, b1]
    push_cast
    linear_combination (-2 * (θ : ℂ) * (r : ℂ) ^ 2) * Complex.I_sq
  rw [hsum, hden, ← Complex.ofReal_div, Complex.ofReal_re]
  -- the second term is `1/(a1 (a1+l))`
  have hne1 : a1 ≠ 0 := fun h => by have := congrArg Complex.re h; simp at this; linarith
  have hne2 : a1 + (l : ℂ) ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp [a1] at this; linarith
  have hsimp : (a1 + a1 + 2 * (l : ℂ)) / ((a1 + a1) * (a1 + l) * (a1 + l)) =
      (a1 * (a1 + l))⁻¹ := by
    field_simp
    ring
  rw [hsimp, Complex.inv_re, Complex.normSq_apply]
  have hwre : (a1 * (a1 + l)).re = θ * (θ + l) - r ^ 2 := by simp [a1]; ring
  have hwim : (a1 * (a1 + l)).im = -(r * (2 * θ + l)) := by simp [a1]; ring
  rw [hwre, hwim]
  have hN : (θ * (θ + l) - r ^ 2) * (θ * (θ + l) - r ^ 2) +
      -(r * (2 * θ + l)) * -(r * (2 * θ + l)) = (θ ^ 2 + r ^ 2) * ((θ + l) ^ 2 + r ^ 2) := by
    ring
  rw [hN]
  have hA : 0 < θ ^ 2 + r ^ 2 := by positivity
  have hB : 0 < (θ + l) ^ 2 + r ^ 2 := by positivity
  field_simp
  ring

/-! ### The `K` side: `N₂(θ)² = ∫ w_θ` -/

/-- `K_Γ(θ) = N₂(θ)² = ∫_0^∞ w_θ(λ) dλ` (lines 7766 and 7806-7819), for a spectral
measure with
`∫(1+|ξ|²)⁻¹ dμ < ∞` and `μ{0} = 0`. -/
theorem K_eq_integral_weight (μ : Measure (Rd d)) [SFinite μ]
    (hR : Integrable (fun ξ : Rd d => 1 / (1 + ‖ξ‖ ^ 2)) μ) (hμ0 : μ {0} = 0)
    (a θ : ℝ) (ha0 : 0 < a) (ha1 : a < 1) (hθ : 0 < θ) :
    N2sq a θ μ = ∫ l in Ioi (0 : ℝ), weight a θ μ l := by
  have hF := FK_integrable μ hR a θ ha0 ha1 hθ
  have hswap := iterated_integral_swap (μX := L0) (μY := μ) (μZ := P2) (FK a θ) hF
  -- left side
  have hL : N2sq a θ μ = ∫ p, ∫ ξ, ∫ l, FK a θ (l, (ξ, p)) ∂L0 ∂μ ∂P2 := by
    unfold N2sq
    refine integral_congr_ae ?_
    filter_upwards [ae_P2] with p hp
    simp_rw [integral_FK_eq a θ ha0 _ p hp.2.2, N2integrand]
    rw [integral_const_mul]
  -- right side
  have hξ0 : ∀ᵐ ξ ∂μ, ξ ≠ 0 := by
    have := measure_eq_zero_iff_ae_notMem.1 hμ0
    filter_upwards [this] with ξ hξ
    simpa using hξ
  have hRgt : (fun l => ∫ ξ, ∫ p, FK a θ (l, (ξ, p)) ∂P2 ∂μ) =ᵐ[L0]
      weight a θ μ := by
    filter_upwards [ae_L0_pos] with l hl
    rw [← xi_integral_K μ hR a θ l hθ hl]
    refine integral_congr_ae ?_
    filter_upwards [hξ0] with ξ hξ
    have e : (fun p : ℝ × ℝ => FK a θ (l, (ξ, p))) = fun p =>
        ((Real.Gamma a)⁻¹ * l ^ (a - 1)) *
          (twoTimeR θ l p * (waveHat p.1 ξ * waveHat p.2 ξ)) := by
      funext p
      simp only [FK, abs_of_pos hl]
      ring
    rw [e, integral_const_mul, (cross_transform θ l hθ hl.le ξ hξ).2]
  rw [hL, hswap]
  exact integral_congr_ae hRgt

/-! ### The `J` side -/

/-- Auxiliary to the Lean proof route. -/
theorem FJ_nonneg (a θ : ℝ) (ha : 0 < a) (z : ℝ × (Rd d × (ℝ × ℝ))) :
    0 ≤ FJ a θ z := by
  have := Real.Gamma_pos_of_pos ha
  have := Real.rpow_nonneg (abs_nonneg z.1) (a - 1)
  have := twoTimeR_pos ((θ ^ 2 + ‖z.2.1‖ ^ 2) / 2) (θ * |z.1| + |z.1| ^ 2 / 2) z.2.2
  unfold FJ
  positivity

/-- Auxiliary to the Lean proof route. -/
theorem FJ_integrable (μ : Measure (Rd d)) [SFinite μ]
    (hR : Integrable (fun ξ : Rd d => 1 / (1 + ‖ξ‖ ^ 2)) μ)
    (a θ : ℝ) (ha0 : 0 < a) (ha1 : a < 1) (hθ : 0 < θ) :
    Integrable (FJ (d := d) a θ) (L0.prod (μ.prod P2)) := by
  have hmeas : Measurable (FJ (d := d) a θ) := by unfold FJ twoTimeR; fun_prop
  refine ⟨hmeas.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal
    (Eventually.of_forall (FJ_nonneg a θ ha0))).2 ?_⟩
  have hT := lintegral_triple_twoTime L0 μ
    (fun l _ => 1 / 4 * (Real.Gamma a)⁻¹ * |l| ^ (a - 1))
    (fun _ ξ => (θ ^ 2 + ‖ξ‖ ^ 2) / 2) (fun l _ => θ * |l| + |l| ^ 2 / 2)
    (by fun_prop) (by fun_prop) (by fun_prop)
    (fun l _ => by have := Real.Gamma_pos_of_pos ha0; positivity)
    (fun _ ξ => by positivity) (fun l _ => by positivity)
  have hfun : (fun z : ℝ × (Rd d × (ℝ × ℝ)) => ENNReal.ofReal (FJ a θ z)) = fun z =>
      ENNReal.ofReal (1 / 4 * (Real.Gamma a)⁻¹ * |z.1| ^ (a - 1) *
        twoTimeR ((θ ^ 2 + ‖z.2.1‖ ^ 2) / 2) (θ * |z.1| + |z.1| ^ 2 / 2) z.2.2) := rfl
  rw [hfun, hT]
  have hcongr : (fun l => ∫⁻ ξ, ENNReal.ofReal (1 / 4 * (Real.Gamma a)⁻¹ * |l| ^ (a - 1) /
      ((θ ^ 2 + ‖ξ‖ ^ 2) / 2 *
        ((θ ^ 2 + ‖ξ‖ ^ 2) / 2 + (θ * |l| + |l| ^ 2 / 2)))) ∂μ)
      =ᵐ[L0] fun l => ENNReal.ofReal (filteredWeight a θ μ l) := by
    filter_upwards [ae_L0_pos] with l hl
    obtain ⟨hi, hv⟩ := xi_integral_J μ hR a θ l hθ hl
    rw [← hv, ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall fun ξ => by
      have := Real.Gamma_pos_of_pos ha0
      have := Real.rpow_nonneg hl.le (a - 1)
      positivity)]
    refine lintegral_congr fun ξ => ?_
    congr 1
    rw [abs_of_pos hl]
    have hA : 0 < θ ^ 2 + ‖ξ‖ ^ 2 := by positivity
    have hB : 0 < (θ + l) ^ 2 + ‖ξ‖ ^ 2 := by positivity
    field_simp
    ring
  rw [lintegral_congr_ae hcongr]
  exact (filteredWeight_integrable μ hR a θ ha0 ha1 hθ).lintegral_lt_top

/-- Auxiliary to the Lean proof route. -/
theorem P2_ne_zero : P2 ≠ 0 := by
  intro h
  have h1 : P2 (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) = 0 := by rw [h]; rfl
  rw [Measure.prod_prod] at h1
  simp [Measure.restrict_apply measurableSet_Ioi] at h1

/-- The `λ`-integral and the spectral integral of `FJ` give the candidate's
integrand, for `u, v > 0`, `u ≠ v` (auxiliary). -/
theorem integral_FJ_eq (μ : Measure (Rd d)) (a θ : ℝ) (p : ℝ × ℝ) :
    ∫ ξ, ∫ l, FJ a θ (l, (ξ, p)) ∂L0 ∂μ = 1 / 4 * Jintegrand a θ μ 1 p := by
  have hA : ∀ ξ : Rd d, ∫ l, FJ a θ (l, (ξ, p)) ∂L0 =
      (1 / 4 * Psi a (θ * |p.1 - p.2|) |p.1 - p.2| * Real.exp (-(θ ^ 2 * (p.1 + p.2) / 2))) *
        Real.exp (-((p.1 + p.2) * ‖ξ‖ ^ 2 / 2)) := by
    intro ξ
    rw [setIntegral_congr_fun measurableSet_Ioi (g := fun l =>
      (1 / 4 * Real.exp (-((θ ^ 2 + ‖ξ‖ ^ 2) / 2 * (p.1 + p.2))) * (Real.Gamma a)⁻¹) *
        psiKernel a (θ * |p.1 - p.2|) |p.1 - p.2| l) ?_]
    · rw [integral_const_mul, Psi]
      have : Real.exp (-((θ ^ 2 + ‖ξ‖ ^ 2) / 2 * (p.1 + p.2))) =
          Real.exp (-(θ ^ 2 * (p.1 + p.2) / 2)) *
            Real.exp (-((p.1 + p.2) * ‖ξ‖ ^ 2 / 2)) := by
        rw [← Real.exp_add]; congr 1; ring
      rw [this]
      ring
    · intro l hl
      have hl0 : (0 : ℝ) < l := hl
      simp only [FJ, twoTimeR, psiKernel, abs_of_pos hl0]
      rw [show -((θ ^ 2 + ‖ξ‖ ^ 2) / 2 * (p.1 + p.2)) - (θ * l + l ^ 2 / 2) * |p.1 - p.2| =
        -((θ ^ 2 + ‖ξ‖ ^ 2) / 2 * (p.1 + p.2)) +
          (-(θ * |p.1 - p.2| * l) - |p.1 - p.2| * l ^ 2 / 2) by ring, Real.exp_add]
      ring
  simp_rw [hA]
  rw [integral_const_mul, Jintegrand, vRho_one]
  unfold heat
  ring

/-- `J_{Γ,1}(θ) = ∫_0^∞ 2θ/(2θ+λ) w_θ(λ) dλ` (lines 7847-7870), with the integrand of
`J_{Γ,1}` integrable. -/
theorem J_one_eq (μ : Measure (Rd d)) [SFinite μ]
    (hR : Integrable (fun ξ : Rd d => 1 / (1 + ‖ξ‖ ^ 2)) μ)
    (a θ : ℝ) (ha0 : 0 < a) (ha1 : a < 1) (hθ : 0 < θ) :
    Integrable (Jintegrand a θ μ 1) P2 ∧
      J a θ μ 1 = ∫ l in Ioi (0 : ℝ), filteredWeight a θ μ l := by
  have hF := FJ_integrable μ hR a θ ha0 ha1 hθ
  have hG := hF.integral_prod_right.integral_prod_right
  have hJ : Integrable (Jintegrand a θ μ 1) P2 := by
    refine (hG.const_mul 4).congr (Eventually.of_forall fun p => ?_)
    simp only
    rw [integral_FJ_eq]
    ring
  refine ⟨hJ, ?_⟩
  have hswap := iterated_integral_swap (μX := L0) (μY := μ) (μZ := P2) (FJ a θ) hF
  simp_rw [integral_FJ_eq] at hswap
  rw [J, ← integral_const_mul, hswap]
  refine integral_congr_ae ?_
  filter_upwards [ae_L0_pos] with l hl
  rw [← (xi_integral_J μ hR a θ l hθ hl).2]
  refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
  have e : (fun p : ℝ × ℝ => FJ a θ (l, (ξ, p))) = fun p =>
      (1 / 4 * (Real.Gamma a)⁻¹ * l ^ (a - 1)) *
        twoTimeR ((θ ^ 2 + ‖ξ‖ ^ 2) / 2) (θ * l + l ^ 2 / 2) p := by
    funext p
    simp only [FJ, abs_of_pos hl]
  simp only
  rw [e, integral_const_mul, (twoTimeR_integral _ _ (by positivity) (by positivity)).2]
  have hA : 0 < θ ^ 2 + ‖ξ‖ ^ 2 := by positivity
  have hB : 0 < (θ + l) ^ 2 + ‖ξ‖ ^ 2 := by positivity
  field_simp
  ring

/-- Auxiliary to the Lean proof route. -/
theorem Jintegrand_measurable (μ : Measure (Rd d)) [SFinite μ] (a θ ρ : ℝ) :
    Measurable (Jintegrand a θ μ ρ) := by
  have h1 : Measurable fun p : ℝ × ℝ => heat μ (p.1 + p.2) :=
    (heat_measurable μ).comp (by fun_prop)
  have h2 : Measurable fun p : ℝ × ℝ => Psi a (θ * |p.1 - p.2|) (vRho ρ p.1 p.2) :=
    (Psi_measurable a).comp
      ((by fun_prop : Measurable fun p : ℝ × ℝ => θ * |p.1 - p.2|).prodMk
      (by fun_prop))
  unfold Jintegrand
  fun_prop

/-- `0 < J_{Γ,ρ}(θ) ≤ J_{Γ,1}(θ)` (lines 7827-7845) for `ρ ≤ 1` and `μ ≠ 0`, with the
integrand of
`J_{Γ,ρ}` integrable. -/
theorem J_rho_props (μ : Measure (Rd d)) [SFinite μ]
    (hR : Integrable (fun ξ : Rd d => 1 / (1 + ‖ξ‖ ^ 2)) μ) (hμ : μ ≠ 0)
    (a θ ρ : ℝ) (ha0 : 0 < a) (ha1 : a < 1) (hθ : 0 < θ) (hρ : ρ ≤ 1) :
    Integrable (Jintegrand a θ μ ρ) P2 ∧ 0 < J a θ μ ρ ∧
      J a θ μ ρ ≤ J a θ μ 1 := by
  have hJ1 := (J_one_eq μ hR a θ ha0 ha1 hθ).1
  have hbd : ∀ᵐ p ∂P2, 0 < Jintegrand a θ μ ρ p ∧
      Jintegrand a θ μ ρ p ≤ Jintegrand a θ μ 1 p := by
    filter_upwards [ae_P2] with p hp
    obtain ⟨hs, ht, hst⟩ := hp
    have hq : 0 < |p.1 - p.2| := abs_pos.2 (sub_ne_zero.2 hst)
    have hr : 0 < θ * |p.1 - p.2| := mul_pos hθ hq
    have hv := abs_le_vRho ρ p.1 p.2 hρ hs.le ht.le
    have hh := heat_pos hR hμ (p.1 + p.2) (by linarith)
    have hE := Real.exp_pos (-(θ ^ 2 * (p.1 + p.2) / 2))
    refine ⟨?_, ?_⟩
    · unfold Jintegrand
      have := Psi_pos a _ _ ha0 hr (hq.le.trans hv)
      positivity
    · unfold Jintegrand
      rw [vRho_one]
      exact mul_le_mul_of_nonneg_left (Psi_antitone a _ _ _ ha0 hr hq.le hv) (by positivity)
  have hI : Integrable (Jintegrand a θ μ ρ) P2 := by
    refine hJ1.mono' (Jintegrand_measurable μ a θ ρ).aestronglyMeasurable ?_
    filter_upwards [hbd] with p hp
    rw [Real.norm_of_nonneg hp.1.le]
    exact hp.2
  refine ⟨hI, ?_, ?_⟩
  · unfold J
    exact mul_pos (by norm_num)
      (integral_pos_of_ae_pos hI P2_ne_zero (hbd.mono fun _ h => h.1))
  · unfold J
    exact mul_le_mul_of_nonneg_left (integral_mono_ae hI hJ1 (hbd.mono fun _ h => h.2))
      (by norm_num)

/-! ### Degree one -/

/-- Auxiliary to the Lean proof route. -/
theorem integrable_rpow_div_add (a c : ℝ) (ha0 : 0 < a) (ha1 : a < 1) (hc : 0 < c) :
    Integrable (fun l : ℝ => l ^ (a - 1) / (c + l)) L0 := by
  refine (integrable_rpow_div a c c ha0 ha1 hc hc.le).congr ?_
  filter_upwards [ae_L0_pos] with l hl
  rw [abs_of_pos hl]
  field_simp

/-- `∫_0^∞ λ^{a-1}/(c+λ) dλ = c^{a-1} ∫_0^∞ λ^{a-1}/(1+λ) dλ` for `c > 0`. -/
theorem integral_rpow_div_add_scaling (a c : ℝ) (hc : 0 < c) :
    ∫ l in Ioi (0 : ℝ), l ^ (a - 1) / (c + l) =
      c ^ (a - 1) * ∫ l in Ioi (0 : ℝ), l ^ (a - 1) / (1 + l) := by
  have h := integral_comp_mul_left_Ioi (fun l : ℝ => l ^ (a - 1) / (c + l)) 0 hc
  rw [mul_zero, smul_eq_mul] at h
  have hpt : ∀ x ∈ Ioi (0 : ℝ), (c * x) ^ (a - 1) / (c + c * x) =
      c ^ (a - 2) * (x ^ (a - 1) / (1 + x)) := by
    intro x hx
    have hx0 : (0 : ℝ) < x := hx
    rw [Real.mul_rpow hc.le hx0.le, show a - 1 = (a - 2) + 1 by ring,
      Real.rpow_add_one hc.ne']
    field_simp
  rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_const_mul] at h
  have hc2 : c ^ (a - 1) = c * c ^ (a - 2) := by
    rw [show a - 1 = (a - 2) + 1 by ring, Real.rpow_add_one hc.ne']; ring
  rw [hc2, mul_assoc, h]
  field_simp

/-- `E:degree-one-clock-loss` (proof at lines 7877-7904): if `α = 1`,
`J_{Γ,1}(θ) = (2-2^a) K_Γ(θ)`. -/
theorem degree_one (μ : Measure (Rd d)) [SFinite μ]
    (hR : Integrable (fun ξ : Rd d => 1 / (1 + ‖ξ‖ ^ 2)) μ) (hμ0 : μ {0} = 0)
    (hI : SpectralHomogeneous μ 1) (a θ : ℝ) (ha0 : 0 < a) (ha1 : a < 1) (hθ : 0 < θ) :
    J a θ μ 1 = (2 - 2 ^ a) * N2sq a θ μ := by
  rw [(J_one_eq μ hR a θ ha0 ha1 hθ).2, K_eq_integral_weight μ hR hμ0 a θ ha0 ha1 hθ]
  set R1 := 𝓡 μ 1
  have hRq : ∀ q : ℝ, 0 < q → 𝓡 μ q = R1 / q := by
    intro q hq
    rw [resolvent_homog hI q hq, show (1 : ℝ) - 2 = -1 by norm_num, Real.rpow_neg_one]
    field_simp
    rfl
  set G := Real.Gamma a
  have hG : 0 < G := Real.Gamma_pos_of_pos ha0
  have hw : ∀ l ∈ Ioi (0 : ℝ),
      weight a θ μ l = R1 / (2 * θ ^ 2 * G) * (l ^ (a - 1) / (θ + l)) := by
    intro l hl
    have hl0 : (0 : ℝ) < l := hl
    unfold weight
    rw [hRq θ hθ, hRq (θ + l) (by linarith), show a - 1 = (a - 2) + 1 by ring,
      Real.rpow_add_one hl0.ne']
    field_simp
    ring
  have hfw : ∀ l ∈ Ioi (0 : ℝ), filteredWeight a θ μ l =
      R1 / (θ ^ 2 * G) * (l ^ (a - 1) / (θ + l) - l ^ (a - 1) / (2 * θ + l)) := by
    intro l hl
    have hl0 : (0 : ℝ) < l := hl
    unfold filteredWeight
    rw [hw l hl]
    field_simp
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi hw, setIntegral_congr_fun measurableSet_Ioi hfw,
    integral_const_mul, integral_const_mul,
    integral_sub (integrable_rpow_div_add a θ ha0 ha1 hθ)
      (integrable_rpow_div_add a (2 * θ) ha0 ha1 (by linarith)),
    integral_rpow_div_add_scaling a θ hθ, integral_rpow_div_add_scaling a (2 * θ) (by linarith),
    Real.mul_rpow (by norm_num) hθ.le]
  have h2 : (2 : ℝ) ^ a = 2 * 2 ^ (a - 1) := by
    rw [show a = (a - 1) + 1 by ring, Real.rpow_add_one (by norm_num : (2 : ℝ) ≠ 0)]
    ring_nf
  rw [h2]
  field_simp

/-! ### The proposition with the manuscript's hypotheses -/

/-- `P:clock-copy-obstruction` (lines 7754-7781) with the manuscript's
hypotheses: `H:homog` with temporal exponent `a = α₀`, a nonzero covariance
`Γ`, `θ > 0`, `-1 ≤ ρ ≤ 1`, and the supplied spectral homogeneity of `μ`
(derived in the TeX proof of `L:damped-homogeneous-norms`).  Conclusions:
`w_θ` is a positive integrable density on `(0,∞)`; `K_Γ(θ) = N₂(θ)² = ∫ w_θ`
(with integrable outer integrand); the candidate integrands are integrable
and `0 < J_{Γ,ρ}(θ) ≤ J_{Γ,1}(θ) = ∫ 2θ/(2θ+λ) w_θ < K_Γ(θ)`
(`E:clock-copy-obstruction`); and `J_{Γ,1}(θ) = (2-2^a) K_Γ(θ)` when `α = 1`
(`E:degree-one-clock-loss`). -/
theorem clock_copy_obstruction_paper {alpha alpha0 : ℝ} {Γ μ : Measure (Rd d)}
    (h : HomogCovariance d alpha alpha0 Γ μ) (hI : SpectralHomogeneous μ alpha)
    (hΓ : Γ ≠ 0) (θ : ℝ) (hθ : 0 < θ) (ρ : ℝ) (hρ : -1 ≤ ρ ∧ ρ ≤ 1) :
    (∀ l : ℝ, 0 < l → 0 < weight alpha0 θ μ l) ∧ Integrable (weight alpha0 θ μ) L0 ∧
      Integrable (fun p : ℝ × ℝ => Real.exp (-(θ * (p.1 + p.2))) * |p.1 - p.2| ^ (-alpha0) *
        ∫ ξ, waveHat p.1 ξ * waveHat p.2 ξ ∂μ) P2 ∧
      N2sq alpha0 θ μ = ∫ l in Ioi (0 : ℝ), weight alpha0 θ μ l ∧
      Integrable (Jintegrand alpha0 θ μ ρ) P2 ∧ Integrable (Jintegrand alpha0 θ μ 1) P2 ∧
      0 < J alpha0 θ μ ρ ∧ J alpha0 θ μ ρ ≤ J alpha0 θ μ 1 ∧
      Integrable (filteredWeight alpha0 θ μ) L0 ∧
      J alpha0 θ μ 1 = ∫ l in Ioi (0 : ℝ), filteredWeight alpha0 θ μ l ∧
      J alpha0 θ μ 1 < N2sq alpha0 θ μ ∧
      (alpha = 1 → J alpha0 θ μ 1 = (2 - 2 ^ alpha0) * N2sq alpha0 θ μ) := by
  have := h.μ_radon
  have := h.Γ_radon
  have ha0 := h.alpha0_pos
  have ha1 := h.alpha0_lt_one
  have hα0 : 0 < alpha := by
    rcases h.alpha_range with h1 | h1
    · exact h1.1
    · rw [h1.1, h1.2]; norm_num
  have hα2 : alpha < 2 := by linarith [h.threshold]
  have hR := integrable_inv_one_add_sq hI hα2
  have hμ0 := measure_zero hI hα0
  have hμ := spectral_ne_zero Γ μ h.spectral hΓ
  have hK := K_eq_integral_weight μ hR hμ0 alpha0 θ ha0 ha1 hθ
  obtain ⟨hJ1i, hJ1⟩ := J_one_eq μ hR alpha0 θ ha0 ha1 hθ
  obtain ⟨hJi, hJpos, hJle⟩ := J_rho_props μ hR hμ alpha0 θ ρ ha0 ha1 hθ hρ.2
  have hwi := weight_integrable μ hR alpha0 θ ha0 ha1 hθ
  obtain ⟨hfi, hlt⟩ := StratonovichHAMAudit.ClockFilter.strict_filter_integral θ hθ L0
    (by simp) ae_L0_pos (weight alpha0 θ μ) hwi
    (ae_L0_pos.mono fun l hl => weight_pos μ hR hμ alpha0 θ l ha0 hθ hl)
  refine ⟨fun l hl => weight_pos μ hR hμ alpha0 θ l ha0 hθ hl, hwi,
    N2_outer_integrable μ hR alpha0 θ ha0 ha1 hθ, hK, hJi, hJ1i, hJpos, hJle, hfi, hJ1, ?_, ?_⟩
  · rw [hJ1, hK]
    exact hlt
  · intro h1
    subst h1
    exact degree_one μ hR hμ0 hI alpha0 θ ha0 ha1 hθ

/-- The nonnegativity `N₂(θ)² ≥ 0` of `L:damped-homogeneous-norms` under
`H:homog` (no `Γ ≠ 0` needed) and the supplied spectral homogeneity, as a
corollary of `N₂(θ)² = ∫ w_θ` (the TeX argues by positive definiteness of the
temporal kernel). -/
theorem damped_N2_nonneg_paper {alpha alpha0 : ℝ} {Γ μ : Measure (Rd d)}
    (h : HomogCovariance d alpha alpha0 Γ μ) (hI : SpectralHomogeneous μ alpha)
    (θ : ℝ) (hθ : 0 < θ) : 0 ≤ N2sq alpha0 θ μ := by
  have := h.μ_radon
  have hα0 : 0 < alpha := by
    rcases h.alpha_range with h1 | h1
    · exact h1.1
    · rw [h1.1, h1.2]; norm_num
  have hR := integrable_inv_one_add_sq hI (by linarith [h.threshold, h.alpha0_pos])
  rw [K_eq_integral_weight μ hR (measure_zero hI hα0) alpha0 θ h.alpha0_pos h.alpha0_lt_one hθ]
  exact setIntegral_nonneg measurableSet_Ioi fun l hl =>
    weight_nonneg μ hR alpha0 θ l h.alpha0_pos hθ hl

end StratonovichHAMSecondMoment.ClockCopy
