module

/-
Copyright 2026 Le Chen. SPDX-License-Identifier: Apache-2.0

Cauchy and scalar steps of `P:static-phase-all-orders` (All regularized static
phase orders) of `notes/notes_stratonovich_ham_second_moment.tex` (main TeX
file; line numbers at revision a284420; statement lines 2577-2605, proof
2607-2683).  The proposition is an operator and stochastic statement; this
module formalizes the complex-analytic, scalar and Banach-space deductions of
its proof.  Every result here is a STEP of the proposition (class: inputs
supplied, conclusion weaker than the labelled statement): the operator and
Gaussian inputs enter as named hypotheses whose doc comments name their labels
and lines.

Constants (formalized, nothing supplied):
* `phaseI`, `deltaA`: `I_a = ∫_0^∞ s^{-1/2}(1+s)^{(a-3)/2} ds` and
  `δ_a = min{1/4, π/(8 I_a)}` of `L:complex-phase` (lines 2298-2299), with
  `I_a > 0` and `δ_a > 0` proved for `a < 2` (the TeX uses `a = α/2 ∈ (0,1)`).
* `allOrdersA`: `A_α = 400 √2 e²/δ_{α/2}` (lines 2585-2587), positive.
* `fockD`: `d_N = 2 √(N+1) √R_α` (`E:fock-sandwich`, lines 2484-2488).

Steps (formalized):
* the Cauchy estimate for an entire map with values in a complex Banach space
  (operator-valued included) bounded on a circle (lines 2616-2624):
  `norm_taylorCoeff_le`, `norm_taylorCoeff_le_of_disc`, and the identification
  of the Taylor coefficient with the power-series coefficient
  (`taylorCoeff_eq_coeff`);
* the arithmetic at `λ = n/h` (lines 2631-2641): `d_n ≤ 2√(2n)√R_α`, the
  display of lines 2636-2638, `100 n ≤ 200^n`, `n! ≤ n^n`
  (`fockD_le`, `order_display_eq`, `all_orders_arith`); and the pointwise
  multiplier form of the norm comparisons of lines 2632-2633
  (`phase_weight_le`);
* `E:all-static-phase-orders` from these, at fixed cutoffs
  (`static_phase_order_cutoff`) and after both cutoff removals given as
  convergence of norms (`static_phase_all_orders_step`, wrapper
  `static_phase_all_orders_paper`);
* `E:all-static-phase-sum` (lines 2669-2681) from the order bounds and
  `‖Z_0(h)‖_{1/h} ≤ √e ‖(f,g)‖_{1/h}`, with the elementary series bound
  `SeriesType.seriesNu_le_two_exp_three` (`all_static_phase_sum_step`, wrapper
  `all_static_phase_sum_paper`).

Supplied (named hypotheses, not formalized): `L:fock-form` and
`L:complex-phase` (the circle bound `100 e^{2λh}`, lines 2611-2614), entireness
of the phase entries in the coupling (lines 2616-2617), the identification of
the coefficient with the cutoff Duhamel phase via `L:finite-word-cutoff` (lines
2625-2630), the `X_λ` norm comparisons after integration (lines 2632-2633), the
cutoff removals (lines 2643-2667, as convergence of norms), and the free bound
`‖Z_0(h)‖_{1/h} ≤ √e ‖(f,g)‖_{1/h}` (line 2679).  Abstract complex (orders) and
real (sum) Banach spaces stand for `L²(Ω; X_λ)`; the Gaussian polynomial
structure of `Z_n^ε(h)` and the uniformity in `ε` are those of the inputs.
Narrower than the TeX: the conclusions are the two displays for the quantities
named by the inputs; that the phases are Gaussian polynomials of degree at most
`n`, and convergence of `∑ σ^n Z_n^ε(h)` as an `L²` phase identified with the
Duhamel series, are only as good as the supplied identification.

The section's standing class (lines 2054-2066) enters the wrappers as in
`IntervalScalar.static_interaction_paper`: locally finite `μ, Γ` on `ℝ³`,
`0 < α < 2` and `R_α = απ μ(B_1)/(2 sin(πα/2))`; evenness, positive
definiteness and scaling enter only through the supplied inputs.

Junk values: `δ_a` is a genuine positive number (`I_a` is a proved-integrable
positive integral); every real power has a positive base or is `(n!)^γ`,
`(√R)^n`, `(|σ|²R)^{1/(3-α)}` with nonnegative base and positive exponent; no
division by `d_N` occurs (the circle radius is quantified over `d' > 0`);
summability is proved, never assumed through `tsum`.
-/
public import Mathlib
public import StratonovichHAMSecondMoment.SeriesType
public import StratonovichHAMSecondMoment.IntervalScalar

@[expose] public section

noncomputable section

set_option autoImplicit false

open Real Finset Filter Topology MeasureTheory Set
open scoped Nat

namespace StratonovichHAMSecondMoment.StaticPhaseCauchy

open StratonovichHAMSecondMoment.SeriesType

/-! ## Constants -/

/-- `I_a = ∫_0^∞ s^{-1/2}(1+s)^{(a-3)/2} ds` (`L:complex-phase`, main TeX line
2298), as a set integral over `(0, ∞)`; integrable for `a < 2`
(`phaseI_integrableOn`). -/
def phaseI (a : ℝ) : ℝ :=
  ∫ s in Ioi (0 : ℝ), s ^ (-(1 / 2 : ℝ)) * (1 + s) ^ ((a - 3) / 2)

/-- Auxiliary (Lean route): for `a < 2`, the integrand
`s^{-1/2}(1+s)^{(a-3)/2}` of `I_a` is integrable on `(0, ∞)` (it is bounded by
`s^{-1/2}` on `(0,1]` and by `s^{(a-4)/2}` on `(1, ∞)`).  The TeX uses only
`0 < a < 1` (`L:complex-phase`, main TeX line 2291). -/
theorem phaseI_integrableOn {a : ℝ} (ha : a < 2) :
    IntegrableOn (fun s : ℝ => s ^ (-(1 / 2 : ℝ)) * (1 + s) ^ ((a - 3) / 2)) (Ioi 0) := by
  have hmeas : Measurable (fun s : ℝ => s ^ (-(1 / 2 : ℝ)) * (1 + s) ^ ((a - 3) / 2)) := by
    fun_prop
  have hexp : (a - 3) / 2 ≤ 0 := by linarith
  rw [← Ioc_union_Ioi_eq_Ioi (zero_le_one' ℝ)]
  refine IntegrableOn.union ?_ ?_
  · have h0 : IntegrableOn (fun s : ℝ => s ^ (-(1 / 2 : ℝ))) (Ioc 0 1) := by
      rw [integrableOn_Ioc_iff_integrableOn_Ioo]
      exact (intervalIntegral.integrableOn_Ioo_rpow_iff one_pos).2 (by norm_num)
    refine h0.mono' hmeas.aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall ?_)
    intro s hs
    have hs0 : 0 < s := hs.1
    have h1 : (1 + s) ^ ((a - 3) / 2) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by linarith) hexp
    have h2 : 0 ≤ (1 + s) ^ ((a - 3) / 2) := Real.rpow_nonneg (by linarith) _
    have h3 : 0 < s ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos hs0 _
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc s ^ (-(1 / 2 : ℝ)) * (1 + s) ^ ((a - 3) / 2) ≤ s ^ (-(1 / 2 : ℝ)) * 1 := by gcongr
      _ = _ := mul_one _
  · have h0 : IntegrableOn (fun s : ℝ => s ^ ((a - 4) / 2)) (Ioi 1) :=
      integrableOn_Ioi_rpow_of_lt (by linarith) one_pos
    refine h0.mono' hmeas.aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall ?_)
    intro s hs
    have hs0 : 0 < s := lt_trans one_pos hs
    have h1 : (1 + s) ^ ((a - 3) / 2) ≤ s ^ ((a - 3) / 2) :=
      Real.rpow_le_rpow_of_nonpos hs0 (by linarith) hexp
    have h3 : 0 < s ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos hs0 _
    have h2 : 0 ≤ (1 + s) ^ ((a - 3) / 2) := Real.rpow_nonneg (by linarith) _
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc s ^ (-(1 / 2 : ℝ)) * (1 + s) ^ ((a - 3) / 2)
        ≤ s ^ (-(1 / 2 : ℝ)) * s ^ ((a - 3) / 2) := by gcongr
      _ = s ^ ((a - 4) / 2) := by
          rw [← Real.rpow_add hs0]; congr 1; ring

/-- `I_a > 0` for `a < 2`, so `δ_a = min{1/4, π/(8 I_a)}` is not a junk value
(main TeX lines 2298-2299, used for `a = α/2 ∈ (0,1)`).  Integrability of the
integrand is proved (`phaseI_integrableOn`), so `I_a` is the genuine integral. -/
theorem phaseI_pos {a : ℝ} (ha : a < 2) : 0 < phaseI a := by
  unfold phaseI
  rw [setIntegral_pos_iff_support_of_nonneg_ae _ (phaseI_integrableOn ha)]
  · have : Ioi (0 : ℝ) ⊆ Function.support
        (fun s : ℝ => s ^ (-(1 / 2 : ℝ)) * (1 + s) ^ ((a - 3) / 2)) := by
      intro s hs
      have hs0 : (0 : ℝ) < s := hs
      exact (mul_pos (Real.rpow_pos_of_pos hs0 _) (Real.rpow_pos_of_pos (by linarith) _)).ne'
    rw [Set.inter_eq_right.2 this]
    simp
  · refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall ?_)
    intro s hs
    have hs0 : (0 : ℝ) < s := hs
    exact (mul_pos (Real.rpow_pos_of_pos hs0 _) (Real.rpow_pos_of_pos (by linarith) _)).le

/-- `δ_a = min{1/4, π/(8 I_a)}` (`L:complex-phase`, main TeX line 2299). -/
def deltaA (a : ℝ) : ℝ := min (1 / 4) (π / (8 * phaseI a))

/-- `δ_a > 0` for `a < 2` (in the TeX, `0 < a < 1`). -/
theorem deltaA_pos {a : ℝ} (ha : a < 2) : 0 < deltaA a := by
  unfold deltaA
  have := phaseI_pos ha
  exact lt_min (by norm_num) (by positivity)

/-- `δ_a ≤ 1/4` (main TeX line 2299). -/
theorem deltaA_le_quarter (a : ℝ) : deltaA a ≤ 1 / 4 := min_le_left _ _

/-! ## Cauchy estimate (main TeX lines 2616-2624) -/

/-- The `n`th Taylor coefficient at `0` of a map `F : ℂ → G`,
`(n!)⁻¹ F^{(n)}(0)`.  For an entire `F` with operator-valued power series
`F(z) = ∑ z^n C_n` it is `C_n` (`taylorCoeff_eq_coeff`); in the proof of
`P:static-phase-all-orders` (main TeX lines 2616-2625), `F` is the phase
propagator `z ↦ 𝓜_z(h)` and the coefficient applied to the initial phase is the
`n`th Duhamel phase at the cutoffs. -/
def taylorCoeff {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G] (F : ℂ → G) (n : ℕ) : G :=
  ((n ! : ℂ))⁻¹ • iteratedDeriv n F 0

/-- Auxiliary (Lean route): if `F` has the power series `p` at `0` on a ball of
any positive radius, its `n`th series coefficient `p.coeff n` (the `C_n` of
`F(z) = ∑ z^n C_n`) is `taylorCoeff F n`.  This lets the coefficient bound be
applied to "the operator-valued series" of main TeX lines 2616-2618. -/
theorem taylorCoeff_eq_coeff {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G] [CompleteSpace G]
    {F : ℂ → G} {p : FormalMultilinearSeries ℂ ℂ G} {r : ENNReal}
    (hp : HasFPowerSeriesOnBall F p 0 r) (n : ℕ) : p.coeff n = taylorCoeff F n := by
  unfold taylorCoeff
  rw [iteratedDeriv_eq_iteratedFDeriv, ← hp.factorial_smul 1 n]
  have hn : (n ! : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos n).ne'
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hn, one_smul]
  rfl

/-- **Step of `P:static-phase-all-orders`, Cauchy's estimate** (main TeX lines
2616-2624), general form: for a complete complex normed space `G` (for example
`E →L[ℂ] E`, operator-valued), an entire `F : ℂ → G` with `‖F z‖ ≤ M` on the
circle `|z| = ρ`, `ρ > 0`, has `‖(n!)⁻¹ F^{(n)}(0)‖ ≤ M/ρ^n`.  From Mathlib's
`Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le`. -/
theorem norm_taylorCoeff_le {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G] [CompleteSpace G]
    {F : ℂ → G} (hF : Differentiable ℂ F) {ρ M : ℝ} (hρ : 0 < ρ)
    (hM : ∀ z ∈ Metric.sphere (0 : ℂ) ρ, ‖F z‖ ≤ M) (n : ℕ) :
    ‖taylorCoeff F n‖ ≤ M / ρ ^ n := by
  unfold taylorCoeff
  have h := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n hρ hF.diffContOnCl hM
  have hn : (0 : ℝ) < n ! := by exact_mod_cast Nat.factorial_pos n
  rw [norm_smul, norm_inv, Complex.norm_natCast]
  calc (n ! : ℝ)⁻¹ * ‖iteratedDeriv n F 0‖ ≤ (n ! : ℝ)⁻¹ * (n ! * M / ρ ^ n) := by gcongr
    _ = M / ρ ^ n := by field_simp


/-- **Step of `P:static-phase-all-orders`, the coefficient bound of main TeX
lines 2619-2623** in the form used there: if `‖F z‖ ≤ M` whenever
`|z| ≤ c/d'` for every `d' > 0` with `d ≤ d'` (`c > 0`, `d ≥ 0`), then
`‖C_n‖ ≤ M (d/c)^n`.  With `c = δ_{α/2} λ^{2-α/2}`, `d = d_N` and
`M = 100 e^{2λh}` this is the TeX's display.  Quantifying over every `d' ≥ d`,
`d' > 0`, is what `L:complex-phase` (which requires `d > 0`) gives from
`L:fock-form` (a sandwich bound with constant `d_N` also holds with every larger
constant); it also covers `d = 0` (the TeX's `R_α = 0` case, line 2608) without
dividing by zero.  Proof route (Lean): Cauchy on the circle of radius `c/d'`,
then `d' ↓ d`. -/
theorem norm_taylorCoeff_le_of_disc {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G]
    [CompleteSpace G] {F : ℂ → G} (hF : Differentiable ℂ F) {c d M : ℝ} (hc : 0 < c)
    (hd : 0 ≤ d) (hM : ∀ d' : ℝ, 0 < d' → d ≤ d' → ∀ z : ℂ, ‖z‖ ≤ c / d' → ‖F z‖ ≤ M)
    (n : ℕ) : ‖taylorCoeff F n‖ ≤ M * (d / c) ^ n := by
  have key : ∀ d' : ℝ, d < d' → ‖taylorCoeff F n‖ ≤ M * (d' / c) ^ n := by
    intro d' hd'
    have hd'0 : 0 < d' := lt_of_le_of_lt hd hd'
    have hρ : 0 < c / d' := div_pos hc hd'0
    have h := norm_taylorCoeff_le hF hρ
      (fun z hz => hM d' hd'0 hd'.le z (le_of_eq (mem_sphere_zero_iff_norm.1 hz))) n
    calc ‖taylorCoeff F n‖ ≤ M / (c / d') ^ n := h
      _ = M * (d' / c) ^ n := by rw [div_pow, div_pow]; field_simp
  have hcont : Tendsto (fun d' : ℝ => M * (d' / c) ^ n) (𝓝[>] d) (𝓝 (M * (d / c) ^ n)) := by
    have : Continuous (fun d' : ℝ => M * (d' / c) ^ n) := by fun_prop
    exact (this.tendsto d).mono_left nhdsWithin_le_nhds
  exact ge_of_tendsto hcont (eventually_nhdsWithin_of_forall (fun d' hd' => key d' hd'))

/-- `d_N = 2 √(N+1) √R` (`E:fock-sandwich`, main TeX lines 2484-2488, with
`R = R_α`). -/
def fockD (N : ℕ) (R : ℝ) : ℝ := 2 * √((N : ℝ) + 1) * √R

/-- Auxiliary: `d_N ≥ 0`. -/
theorem fockD_nonneg (N : ℕ) (R : ℝ) : 0 ≤ fockD N R := by unfold fockD; positivity

/-- Step of `P:static-phase-all-orders` (main TeX lines 2633-2634):
`d_n ≤ 2 √(2n) √R` for `n ≥ 1`. -/
theorem fockD_le {n : ℕ} (hn : 1 ≤ n) (R : ℝ) : fockD n R ≤ 2 * √(2 * n) * √R := by
  unfold fockD
  have : ((n : ℝ) + 1) ≤ 2 * n := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  gcongr

/-- `400 √2 e²/δ`: with `δ = δ_{α/2}` this is the TeX's
`A_α = 400 √2 e²/δ_{α/2}` (main TeX lines 2585-2587, `allOrdersA`). -/
def orderConst (δ : ℝ) : ℝ := 400 * √2 * Real.exp 2 / δ

/-- `A_α = 400 √2 e²/δ_{α/2}` (main TeX lines 2585-2587). -/
def allOrdersA (alpha : ℝ) : ℝ := orderConst (deltaA (alpha / 2))

/-- `A_α > 0` for `α < 4` (in the TeX, `0 < α < 2`). -/
theorem allOrdersA_pos {alpha : ℝ} (hα : alpha < 4) : 0 < allOrdersA alpha := by
  unfold allOrdersA orderConst
  have := deltaA_pos (a := alpha / 2) (by linarith)
  positivity

/-- Step of `P:static-phase-all-orders`, pointwise multiplier form of the norm
comparisons (main TeX lines 2632-2633).  The `X_λ` norm is
`‖(f,g)‖_λ² = ‖f‖² + ‖A_λ^{-1/2} g‖²` with `A_λ = λ² - Δ` (line 2307), whose
`g`-part has Fourier multiplier `(λ² + r)⁻¹`, `r = |η|²`.  For `n ≥ 1`, `h > 0`,
`r ≥ 0`: `((1/h)² + r)⁻¹ ≤ n² ((n/h)² + r)⁻¹` and `((n/h)² + r)⁻¹ ≤ ((1/h)² + r)⁻¹`.
Integrating against `|ĝ|²` (and `1 ≤ n²` for the `f`-part) gives
`‖z‖_{1/h} ≤ n ‖z‖_{n/h}` and `‖(f,g)‖_{n/h} ≤ ‖(f,g)‖_{1/h}`; that integration
is not formalized here. -/
theorem phase_weight_le {n : ℕ} (hn : 1 ≤ n) {h r : ℝ} (hh : 0 < h) (hr : 0 ≤ r) :
    ((1 / h) ^ 2 + r)⁻¹ ≤ (n : ℝ) ^ 2 * ((n / h) ^ 2 + r)⁻¹ ∧
      ((n / h) ^ 2 + r)⁻¹ ≤ ((1 / h) ^ 2 + r)⁻¹ := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hp : 0 < (1 / h) ^ 2 + r := by positivity
  have hq : 0 < ((n : ℝ) / h) ^ 2 + r := by positivity
  have hle : (1 / h) ^ 2 + r ≤ ((n : ℝ) / h) ^ 2 + r := by
    have : (1 / h) ^ 2 ≤ ((n : ℝ) / h) ^ 2 := by gcongr
    linarith
  refine ⟨?_, inv_anti₀ hp hle⟩
  rw [← div_eq_mul_inv, le_div_iff₀ hq, inv_mul_eq_div, div_le_iff₀ hp]
  have hn2 : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
  have : ((n : ℝ) / h) ^ 2 = (n : ℝ) ^ 2 * (1 / h) ^ 2 := by ring
  rw [this]
  nlinarith

/-- Step of `P:static-phase-all-orders` (main TeX lines 2632-2638): at
`λ = n/h`, the coefficient factor with `d = 2√(2n)√R` equals the TeX's display,
`e^{2λh} (2√(2n)√R/(δ λ^{2-α/2}))^n
 = (2√2 e²/δ)^n R^{n/2} h^{(4-α)n/2} n^{-(3-α)n/2}`
(`R^{n/2}` written `(√R)^n`). -/
theorem order_display_eq {n : ℕ} (hn : 1 ≤ n) {h R δ alpha : ℝ} (hh : 0 < h) (hδ : 0 < δ) :
    Real.exp (2 * (n / h) * h) * (2 * √(2 * n) * √R / (δ * (n / h) ^ (2 - alpha / 2))) ^ n =
      (2 * √2 * Real.exp 2 / δ) ^ n * √R ^ n * h ^ ((4 - alpha) * n / 2) *
        (n : ℝ) ^ (-((3 - alpha) * n / 2)) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have e1 : Real.exp (2 * (n / h) * h) = Real.exp 2 ^ n := by
    rw [← Real.exp_nat_mul]; congr 1; field_simp
  have e2 : h ^ ((4 - alpha) * n / 2) = (h ^ ((4 - alpha) / 2)) ^ n := by
    rw [← Real.rpow_mul_natCast hh.le]; congr 1; ring
  have e3 : (n : ℝ) ^ (-((3 - alpha) * n / 2)) = ((n : ℝ) ^ (-((3 - alpha) / 2))) ^ n := by
    rw [← Real.rpow_mul_natCast hn0.le]; congr 1; ring
  rw [e1, e2, e3, ← mul_pow, ← mul_pow, ← mul_pow, ← mul_pow]
  congr 1
  have hq : (n / h : ℝ) ^ (2 - alpha / 2) = (n : ℝ) ^ (2 - alpha / 2) / h ^ (2 - alpha / 2) :=
    Real.div_rpow hn0.le hh.le _
  have hs : √(2 * (n : ℝ)) = √2 * (n : ℝ) ^ (1 / 2 : ℝ) := by
    rw [Real.sqrt_mul (by norm_num), Real.sqrt_eq_rpow (n : ℝ)]
  have hm : (n : ℝ) ^ (-((3 - alpha) / 2)) * (n : ℝ) ^ (2 - alpha / 2) = (n : ℝ) ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_add hn0]; congr 1; ring
  have hh2 : h ^ ((4 - alpha) / 2) = h ^ (2 - alpha / 2) := by congr 1; ring
  have hp1 : 0 < (n : ℝ) ^ (2 - alpha / 2) := Real.rpow_pos_of_pos hn0 _
  have hp2 : 0 < h ^ (2 - alpha / 2) := Real.rpow_pos_of_pos hh _
  rw [hq, hs, hh2, ← hm]
  field_simp

/-- Step of `P:static-phase-all-orders` (main TeX line 2640): `100 n ≤ 200^n`
for `n ≥ 1`. -/
theorem hundred_mul_le {n : ℕ} (hn : 1 ≤ n) : (100 : ℝ) * n ≤ 200 ^ n := by
  have h1 : (n : ℝ) ≤ 2 ^ n := by exact_mod_cast (Nat.lt_two_pow_self).le
  have h2 : (100 : ℝ) ≤ 100 ^ n := le_self_pow₀ (by norm_num) (by omega)
  calc (100 : ℝ) * n ≤ 100 ^ n * 2 ^ n := by gcongr
    _ = 200 ^ n := by rw [← mul_pow]; norm_num

/-- Step of `P:static-phase-all-orders` (main TeX line 2640, `n! ≤ n^n`): for
`γ ≥ 0` and `n ≥ 1`, `n^{-γn} ≤ 1/(n!)^γ`. -/
theorem rpow_neg_le_factorial {n : ℕ} (hn : 1 ≤ n) {γ : ℝ} (hγ : 0 ≤ γ) :
    (n : ℝ) ^ (-(γ * n)) ≤ 1 / (n ! : ℝ) ^ γ := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hf : (0 : ℝ) < n ! := by exact_mod_cast Nat.factorial_pos n
  have hle : (n ! : ℝ) ≤ (n : ℝ) ^ n := by exact_mod_cast Nat.factorial_le_pow n
  rw [show -(γ * n) = (n : ℝ) * (-γ) by ring, Real.rpow_natCast_mul hn0.le, one_div,
    ← Real.rpow_neg hf.le]
  exact Real.rpow_le_rpow_of_nonpos hf hle (by linarith)

/-- Step of `P:static-phase-all-orders` (main TeX lines 2640-2641): the display
of lines 2636-2638, times `100 n`, is at most
`(A √R)^n h^{(4-α)n/2}/(n!)^{(3-α)/2}` with `A = orderConst δ = 400√2 e²/δ`,
for `α ≤ 3` (the TeX has `0 < α < 2`). -/
theorem order_final_le {n : ℕ} (hn : 1 ≤ n) {h R δ alpha : ℝ} (hh : 0 < h)
    (hδ : 0 < δ) (hα : alpha ≤ 3) :
    100 * n * ((2 * √2 * Real.exp 2 / δ) ^ n * √R ^ n * h ^ ((4 - alpha) * n / 2) *
        (n : ℝ) ^ (-((3 - alpha) * n / 2))) ≤
      (orderConst δ * √R) ^ n * h ^ ((4 - alpha) * n / 2) / (n ! : ℝ) ^ ((3 - alpha) / 2) := by
  have hγ : 0 ≤ (3 - alpha) / 2 := by linarith
  have h1 := hundred_mul_le hn
  have h2 := rpow_neg_le_factorial hn hγ
  rw [show -((3 - alpha) * n / 2) = -((3 - alpha) / 2 * n) by ring]
  have hB : 0 ≤ (2 * √2 * Real.exp 2 / δ) ^ n * √R ^ n * h ^ ((4 - alpha) * n / 2) := by
    positivity
  have hC : 0 ≤ (n : ℝ) ^ (-((3 - alpha) / 2 * n)) := by positivity
  have hA : orderConst δ = 200 * (2 * √2 * Real.exp 2 / δ) := by
    unfold orderConst; ring
  calc 100 * n * ((2 * √2 * Real.exp 2 / δ) ^ n * √R ^ n * h ^ ((4 - alpha) * n / 2) *
        (n : ℝ) ^ (-((3 - alpha) / 2 * n)))
      = (100 * n) * ((2 * √2 * Real.exp 2 / δ) ^ n * √R ^ n * h ^ ((4 - alpha) * n / 2)) *
        (n : ℝ) ^ (-((3 - alpha) / 2 * n)) := by ring
    _ ≤ 200 ^ n * ((2 * √2 * Real.exp 2 / δ) ^ n * √R ^ n * h ^ ((4 - alpha) * n / 2)) *
        (1 / (n ! : ℝ) ^ ((3 - alpha) / 2)) := by gcongr
    _ = _ := by rw [hA, mul_pow, mul_pow]; ring

/-- **Step of `P:static-phase-all-orders`, the scalar arithmetic at `λ = n/h`**
(main TeX lines 2631-2641): for `n ≥ 1`, `h, δ > 0`, `α ≤ 3` and
`0 ≤ d ≤ 2√(2n)√R`,
`n · 100 e^{2λh} (d/(δ λ^{2-α/2}))^n ≤ (A √R)^n h^{(4-α)n/2}/(n!)^{(3-α)/2}`
with `λ = n/h` and `A = 400√2 e²/δ`.  The factor `n` is the norm comparison
`‖z‖_{1/h} ≤ n ‖z‖_{n/h}` of line 2632. -/
theorem all_orders_arith {n : ℕ} (hn : 1 ≤ n) {h R δ alpha d : ℝ} (hh : 0 < h)
    (hδ : 0 < δ) (hα : alpha ≤ 3) (hd0 : 0 ≤ d) (hd : d ≤ 2 * √(2 * n) * √R) :
    n * (100 * Real.exp (2 * (n / h) * h) * (d / (δ * (n / h) ^ (2 - alpha / 2))) ^ n) ≤
      (orderConst δ * √R) ^ n * h ^ ((4 - alpha) * n / 2) / (n ! : ℝ) ^ ((3 - alpha) / 2) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hc : 0 < δ * (n / h) ^ (2 - alpha / 2) := by positivity
  calc (n : ℝ) * (100 * Real.exp (2 * (n / h) * h) * (d / (δ * (n / h) ^ (2 - alpha / 2))) ^ n)
      ≤ n * (100 * Real.exp (2 * (n / h) * h) *
          (2 * √(2 * n) * √R / (δ * (n / h) ^ (2 - alpha / 2))) ^ n) := by gcongr
    _ = 100 * n * (Real.exp (2 * (n / h) * h) *
          (2 * √(2 * n) * √R / (δ * (n / h) ^ (2 - alpha / 2))) ^ n) := by ring
    _ = 100 * n * ((2 * √2 * Real.exp 2 / δ) ^ n * √R ^ n * h ^ ((4 - alpha) * n / 2) *
        (n : ℝ) ^ (-((3 - alpha) * n / 2))) := by rw [order_display_eq hn hh hδ]
    _ ≤ _ := order_final_le hn hh hδ hα

/-! ## `E:all-static-phase-orders` -/

/-- **Step row of `P:static-phase-all-orders`, `E:all-static-phase-orders` at
fixed cutoffs** (main TeX lines 2609-2641).  `E` is a complex Banach space
standing for the cutoff space `L²(Ω; X_λ)` at `λ = n/h` (finite Gaussian
cutoff `m`, degree cutoff `N = n`, band `b`), `F z` the phase propagator
`𝓜_z(h)` at complex coupling `z`, `v` the initial phase `S_b(f,g)` times the
vacuum, `z1` the `L²(Ω; X_{1/h})` norm of the cutoff `n`th Duhamel phase and
`N1 = ‖(f,g)‖_{1/h}`.  Supplied inputs:
* `hentire`: the phase entries are entire in the coupling (lines 2616-2617);
* `hcircle`: the bound `100 e^{2λh}` on `|z| ≤ δ λ^{2-α/2}/d'` for every
  `d' > 0`, `d' ≥ d_n` (`L:complex-phase` with `a = α/2`, applied to the sandwich
  bound of `L:fock-form`, lines 2611-2614);
* `hz`: the identification of the coefficient with the cutoff Duhamel phase
  (lines 2625-2630, via `L:finite-word-cutoff`) together with the norm
  comparison `‖z‖_{1/h} ≤ n ‖z‖_{n/h}` (line 2632);
* `hv`: `‖S_b(f,g)‖_{n/h} ≤ ‖(f,g)‖_{n/h} ≤ ‖(f,g)‖_{1/h}` (line 2633; the first
  inequality, `S_b` a contraction in `X_λ`, is implicit in the TeX).
Conclusion: `z1 ≤ (A √R)^n h^{(4-α)n/2}/(n!)^{(3-α)/2} N1`, `A = 400√2 e²/δ`.
The Cauchy estimate and the arithmetic are proved; the step holds for every
real `R` and `α ≤ 3`. -/
theorem static_phase_order_cutoff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] (F : ℂ → E →L[ℂ] E) (v : E) {n : ℕ} (hn : 1 ≤ n)
    {alpha h R δ z1 N1 : ℝ} (hα : alpha ≤ 3) (hh : 0 < h) (hδ : 0 < δ)
    (hentire : Differentiable ℂ F)
    (hcircle : ∀ d' : ℝ, 0 < d' → fockD n R ≤ d' → ∀ z : ℂ,
      ‖z‖ ≤ δ * (n / h) ^ (2 - alpha / 2) / d' → ‖F z‖ ≤ 100 * Real.exp (2 * (n / h) * h))
    (hz : z1 ≤ n * ‖taylorCoeff F n v‖) (hv : ‖v‖ ≤ N1) :
    z1 ≤ (orderConst δ * √R) ^ n * h ^ ((4 - alpha) * n / 2) / (n ! : ℝ) ^ ((3 - alpha) / 2) *
      N1 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hc : 0 < δ * (n / h) ^ (2 - alpha / 2) := by positivity
  have hT := norm_taylorCoeff_le_of_disc hentire hc (fockD_nonneg n R) hcircle n
  have hN1 : 0 ≤ N1 := (norm_nonneg v).trans hv
  set M := 100 * Real.exp (2 * (n / h) * h) * (fockD n R / (δ * (n / h) ^ (2 - alpha / 2))) ^ n
    with hMdef
  have hM0 : 0 ≤ M := by have := fockD_nonneg n R; positivity
  have h1 : ‖taylorCoeff F n v‖ ≤ M * N1 :=
    ((taylorCoeff F n).le_opNorm v).trans (mul_le_mul hT hv (norm_nonneg v) hM0)
  have h2 := all_orders_arith hn hh hδ hα (fockD_nonneg n R) (fockD_le hn R)
  calc z1 ≤ n * ‖taylorCoeff F n v‖ := hz
    _ ≤ n * (M * N1) := by gcongr
    _ = n * M * N1 := by ring
    _ ≤ _ := by gcongr


/-- **Step row of `P:static-phase-all-orders`, `E:all-static-phase-orders`**
(main TeX lines 2588-2595, proof 2609-2667): the cutoff bound of
`static_phase_order_cutoff` at every Gaussian cutoff `m` and band `b`, with the
cutoff removals supplied as convergence of norms: `hband`, for each `m` the
cutoff norms converge as `b → ∞` (lines 2643-2652), and `hgauss`, the
resulting norms converge to `z = ‖Z_n^ε(h)‖_{L²(Ω; X_{1/h})}` as `m → ∞`
(lines 2654-2666).  Norm convergence is implied by the strong convergence the
TeX proves.  The estimate survives both limits (proved).  The other inputs are
those of `static_phase_order_cutoff`, at each cutoff. -/
theorem static_phase_all_orders_step (E : ℕ → ℕ → Type*) [∀ m b, NormedAddCommGroup (E m b)]
    [∀ m b, NormedSpace ℂ (E m b)] [∀ m b, CompleteSpace (E m b)]
    (F : ∀ m b, ℂ → E m b →L[ℂ] E m b) (v : ∀ m b, E m b)
    (zc : ℕ → ℕ → ℝ) (zm : ℕ → ℝ) {n : ℕ} (hn : 1 ≤ n)
    {alpha h R δ z N1 : ℝ} (hα : alpha ≤ 3) (hh : 0 < h) (hδ : 0 < δ)
    (hentire : ∀ m b, Differentiable ℂ (F m b))
    (hcircle : ∀ m b, ∀ d' : ℝ, 0 < d' → fockD n R ≤ d' → ∀ z : ℂ,
      ‖z‖ ≤ δ * (n / h) ^ (2 - alpha / 2) / d' → ‖F m b z‖ ≤ 100 * Real.exp (2 * (n / h) * h))
    (hz : ∀ m b, zc m b ≤ n * ‖taylorCoeff (F m b) n (v m b)‖) (hv : ∀ m b, ‖v m b‖ ≤ N1)
    (hband : ∀ m, Tendsto (zc m) atTop (𝓝 (zm m))) (hgauss : Tendsto zm atTop (𝓝 z)) :
    z ≤ (orderConst δ * √R) ^ n * h ^ ((4 - alpha) * n / 2) / (n ! : ℝ) ^ ((3 - alpha) / 2) *
      N1 := by
  have hcut : ∀ m b, zc m b ≤ (orderConst δ * √R) ^ n * h ^ ((4 - alpha) * n / 2) /
      (n ! : ℝ) ^ ((3 - alpha) / 2) * N1 := fun m b =>
    static_phase_order_cutoff (F m b) (v m b) hn hα hh hδ (hentire m b) (hcircle m b) (hz m b)
      (hv m b)
  exact le_of_tendsto' hgauss (fun m => le_of_tendsto' (hband m) (hcut m))

/-! ## `E:all-static-phase-sum` -/

/-- Step of `P:static-phase-all-orders` (main TeX lines 2669-2670 and
2600-2603): with `x = A|σ|√R h^{(4-α)/2}` and `β = (3-α)/2`,
`x^{1/β} = A^{2/(3-α)} (|σ|²R)^{1/(3-α)} h^{(4-α)/(3-α)}`. -/
theorem sum_exponent_eq {alpha A R h σ : ℝ} (hα : alpha < 3) (hA : 0 ≤ A) (hR : 0 ≤ R)
    (hh : 0 < h) :
    (A * |σ| * √R * h ^ ((4 - alpha) / 2)) ^ (1 / ((3 - alpha) / 2)) =
      A ^ (2 / (3 - alpha)) * (|σ| ^ 2 * R) ^ (1 / (3 - alpha)) * h ^ ((4 - alpha) / (3 - alpha)) := by
  have h3 : (0 : ℝ) < 3 - alpha := by linarith
  have hs : 0 ≤ |σ| := abs_nonneg σ
  rw [show (1 / ((3 - alpha) / 2)) = 2 / (3 - alpha) by field_simp]
  rw [Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow (by positivity) (by positivity),
    Real.mul_rpow hA hs, Real.mul_rpow (by positivity) hR]
  have e1 : (|σ| ^ 2) ^ (1 / (3 - alpha)) = |σ| ^ (2 / (3 - alpha)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hs]; congr 1; push_cast; ring
  have e2 : √R ^ (2 / (3 - alpha)) = R ^ (1 / (3 - alpha)) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hR]; congr 1; ring
  have e3 : (h ^ ((4 - alpha) / 2)) ^ (2 / (3 - alpha)) = h ^ ((4 - alpha) / (3 - alpha)) := by
    rw [← Real.rpow_mul hh.le]; congr 1; field_simp
  rw [e1, e2, e3]; ring

/-- **Step row of `P:static-phase-all-orders`, `E:all-static-phase-sum`** (main
TeX lines 2596-2604, proof 2669-2681).  In a real Banach space standing for
`L²(Ω; X_{1/h})`, with `N = ‖(f,g)‖_{1/h}`, the supplied inputs are
`hZ0`: `‖Z_0(h)‖_{1/h} ≤ √e N` (line 2679, free evolution) and `hZ`: the bounds
`E:all-static-phase-orders` for `n ≥ 1` (proved under their inputs by
`static_phase_all_orders_paper`).  Conclusion: `∑ σ^n Z_n` converges absolutely
and `‖∑ σ^n Z_n‖² ≤ (√e+2)² exp{6 A^{2/(3-α)} (|σ|²R)^{1/(3-α)} h^{(4-α)/(3-α)}} N²`.
The elementary series bound is `SeriesType.seriesNu_le_two_exp_three` at
`β = (3-α)/2`. -/
theorem all_static_phase_sum_step {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (Z : ℕ → E) {alpha A R h σ N : ℝ} (hα0 : 0 ≤ alpha) (hα2 : alpha ≤ 2)
    (hA : 0 ≤ A) (hR : 0 ≤ R) (hh : 0 < h)
    (hZ0 : ‖Z 0‖ ≤ √(Real.exp 1) * N)
    (hZ : ∀ n, 1 ≤ n → ‖Z n‖ ≤
      (A * √R) ^ n * h ^ ((4 - alpha) * n / 2) / (n ! : ℝ) ^ ((3 - alpha) / 2) * N) :
    Summable (fun n => ‖σ ^ n • Z n‖) ∧ Summable (fun n => σ ^ n • Z n) ∧
      ‖∑' n, σ ^ n • Z n‖ ^ 2 ≤ (√(Real.exp 1) + 2) ^ 2 *
        Real.exp (6 * A ^ (2 / (3 - alpha)) * (|σ| ^ 2 * R) ^ (1 / (3 - alpha)) *
          h ^ ((4 - alpha) / (3 - alpha))) * N ^ 2 := by
  have hN : 0 ≤ N := by
    have := (norm_nonneg (Z 0)).trans hZ0
    exact nonneg_of_mul_nonneg_right (by linarith) (Real.sqrt_pos.2 (Real.exp_pos 1))
  set β := (3 - alpha) / 2 with hβ
  set x := A * |σ| * √R * h ^ ((4 - alpha) / 2) with hx
  have hx0 : 0 ≤ x := by positivity
  obtain ⟨hs, hb⟩ := seriesNu_le_two_exp_three (β := β) (x := x)
    (by rw [hβ]; linarith) (by rw [hβ]; linarith) hx0
  have hterm : ∀ k : ℕ, ‖σ ^ (k + 1) • Z (k + 1)‖ ≤
      N * (x ^ (k + 1) / ((k + 1)! : ℝ) ^ β) := by
    intro k
    have h1 := hZ (k + 1) (by omega)
    rw [norm_smul, norm_pow, Real.norm_eq_abs]
    have hpow : h ^ ((4 - alpha) * ((k + 1 : ℕ) : ℝ) / 2) = (h ^ ((4 - alpha) / 2)) ^ (k + 1) := by
      rw [← Real.rpow_mul_natCast hh.le]; congr 1; ring
    rw [hpow] at h1
    have hf : 0 < ((k + 1)! : ℝ) ^ β := by positivity
    calc |σ| ^ (k + 1) * ‖Z (k + 1)‖
        ≤ |σ| ^ (k + 1) * ((A * √R) ^ (k + 1) * (h ^ ((4 - alpha) / 2)) ^ (k + 1) /
            ((k + 1)! : ℝ) ^ β * N) := by gcongr
      _ = N * (x ^ (k + 1) / ((k + 1)! : ℝ) ^ β) := by
          rw [hx, show A * |σ| * √R * h ^ ((4 - alpha) / 2) =
            |σ| * (A * √R) * h ^ ((4 - alpha) / 2) by ring, mul_pow, mul_pow]
          field_simp
          ring
  have hs1 : Summable (fun k : ℕ => x ^ (k + 1) / ((k + 1)! : ℝ) ^ β) :=
    (summable_nat_add_iff 1).2 hs
  have hu : Summable (fun k : ℕ => ‖σ ^ (k + 1) • Z (k + 1)‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm (hs1.mul_left N)
  have hnorm : Summable (fun n => ‖σ ^ n • Z n‖) := (summable_nat_add_iff 1).1 hu
  have hsum : Summable (fun n => σ ^ n • Z n) := hnorm.of_norm
  refine ⟨hnorm, hsum, ?_⟩
  have hS : ∑' n : ℕ, x ^ n / (n ! : ℝ) ^ β =
      1 + ∑' k : ℕ, x ^ (k + 1) / ((k + 1)! : ℝ) ^ β := by
    rw [hs.tsum_eq_zero_add]; simp
  have htot : ∑' n, ‖σ ^ n • Z n‖ ≤ √(Real.exp 1) * N + N * (2 * Real.exp (3 * x ^ (1 / β)) - 1) := by
    rw [hnorm.tsum_eq_zero_add]
    have h0 : ‖σ ^ 0 • Z 0‖ ≤ √(Real.exp 1) * N := by simpa using hZ0
    have h1 : ∑' k : ℕ, ‖σ ^ (k + 1) • Z (k + 1)‖ ≤ N * (2 * Real.exp (3 * x ^ (1 / β)) - 1) := by
      calc ∑' k : ℕ, ‖σ ^ (k + 1) • Z (k + 1)‖
          ≤ ∑' k : ℕ, N * (x ^ (k + 1) / ((k + 1)! : ℝ) ^ β) :=
            hu.tsum_le_tsum hterm (hs1.mul_left N)
        _ = N * ∑' k : ℕ, x ^ (k + 1) / ((k + 1)! : ℝ) ^ β := tsum_mul_left
        _ ≤ N * (2 * Real.exp (3 * x ^ (1 / β)) - 1) := by
            gcongr; linarith
    linarith
  have hy : 1 ≤ Real.exp (3 * x ^ (1 / β)) := by
    have : 0 ≤ 3 * x ^ (1 / β) := by positivity
    exact Real.one_le_exp this
  have hfin : ‖∑' n, σ ^ n • Z n‖ ≤ (√(Real.exp 1) + 2) * Real.exp (3 * x ^ (1 / β)) * N := by
    refine (norm_tsum_le_tsum_norm hnorm).trans (htot.trans ?_)
    have hse : 0 ≤ √(Real.exp 1) := Real.sqrt_nonneg _
    nlinarith [mul_le_mul_of_nonneg_left hy (mul_nonneg hse hN)]
  have hexp : x ^ (1 / β) = A ^ (2 / (3 - alpha)) * (|σ| ^ 2 * R) ^ (1 / (3 - alpha)) *
      h ^ ((4 - alpha) / (3 - alpha)) := by
    rw [hβ, hx]; exact sum_exponent_eq (by linarith) hA hR hh
  calc ‖∑' n, σ ^ n • Z n‖ ^ 2 ≤ ((√(Real.exp 1) + 2) * Real.exp (3 * x ^ (1 / β)) * N) ^ 2 := by
        gcongr
    _ = (√(Real.exp 1) + 2) ^ 2 * Real.exp (6 * x ^ (1 / β)) * N ^ 2 := by
        rw [mul_pow, mul_pow, ← Real.exp_nat_mul]; push_cast; ring_nf
    _ = _ := by rw [hexp]; ring_nf

/-- **Step row of `P:static-phase-all-orders`, `E:all-static-phase-orders`, with
the section's constants** (main TeX lines 2577-2595, proof 2607-2667): for
locally finite (Radon) `μ, Γ` on `ℝ³`, `0 < α < 2` (line 2054),
`R = R_α = απ μ(B_1)/(2 sin(πα/2))` (line 2061), `δ = δ_{α/2}` in the circle
bound and `A_α = 400√2 e²/δ_{α/2}`, for `n ≥ 1` and `h > 0`:
`‖Z_n^ε(h)‖_{L²(Ω; X_{1/h})} ≤ (A_α √R_α)^n h^{(4-α)n/2}/(n!)^{(3-α)/2} ‖(f,g)‖_{1/h}`.
Supplied inputs as in `static_phase_all_orders_step` (`L:fock-form`,
`L:complex-phase`, entireness, `L:finite-word-cutoff`, the norm comparisons,
the cutoff removals); evenness, positive definiteness and scaling of `Γ` enter
only through them.  Weaker than the TeX statement: only the displayed bound for
the quantities named by the inputs is proved.  `_hμ`, `_hΓ`, `_hα0` and `_hRdef`
are carried and not used: the step holds for every real `R` and `α < 2`. -/
theorem static_phase_all_orders_paper (E : ℕ → ℕ → Type*) [∀ m b, NormedAddCommGroup (E m b)]
    [∀ m b, NormedSpace ℂ (E m b)] [∀ m b, CompleteSpace (E m b)]
    (F : ∀ m b, ℂ → E m b →L[ℂ] E m b) (v : ∀ m b, E m b)
    (zc : ℕ → ℕ → ℝ) (zm : ℕ → ℝ) {n : ℕ} (hn : 1 ≤ n) {alpha h R z N1 : ℝ}
    (μ Γ : Measure (HomogHypothesis.Rd 3))
    (_hμ : IsLocallyFiniteMeasure μ) (_hΓ : IsLocallyFiniteMeasure Γ)
    (_hα0 : 0 < alpha) (hα2 : alpha < 2)
    (_hRdef : R = alpha * π * (μ (Metric.ball 0 1)).toReal / (2 * Real.sin (π * alpha / 2)))
    (hh : 0 < h)
    (hentire : ∀ m b, Differentiable ℂ (F m b))
    (hcircle : ∀ m b, ∀ d' : ℝ, 0 < d' → fockD n R ≤ d' → ∀ z : ℂ,
      ‖z‖ ≤ deltaA (alpha / 2) * (n / h) ^ (2 - alpha / 2) / d' →
        ‖F m b z‖ ≤ 100 * Real.exp (2 * (n / h) * h))
    (hz : ∀ m b, zc m b ≤ n * ‖taylorCoeff (F m b) n (v m b)‖) (hv : ∀ m b, ‖v m b‖ ≤ N1)
    (hband : ∀ m, Tendsto (zc m) atTop (𝓝 (zm m))) (hgauss : Tendsto zm atTop (𝓝 z)) :
    z ≤ (allOrdersA alpha * √R) ^ n * h ^ ((4 - alpha) * n / 2) /
      (n ! : ℝ) ^ ((3 - alpha) / 2) * N1 :=
  static_phase_all_orders_step E F v zc zm hn (by linarith) hh
    (deltaA_pos (a := alpha / 2) (by linarith)) hentire hcircle hz hv hband hgauss

/-- **Step row of `P:static-phase-all-orders`, `E:all-static-phase-sum`, with the
section's constants** (main TeX lines 2596-2604, proof 2669-2681): for locally
finite `μ, Γ` on `ℝ³`, `0 < α < 2`, `R = R_α = απ μ(B_1)/(2 sin(πα/2))` and
`A = A_α = 400√2 e²/δ_{α/2}`, from the supplied `hZ0` (free bound, line 2679)
and `hZ` (`E:all-static-phase-orders`, the conclusion of
`static_phase_all_orders_paper` for each `n ≥ 1`), the series `∑ σ^n Z_n`
converges absolutely and
`‖∑ σ^n Z_n‖² ≤ (√e+2)² exp{6 A_α^{2/(3-α)} (|σ|²R_α)^{1/(3-α)} h^{(4-α)/(3-α)}} N²`.
Weaker than the TeX statement as explained at `all_static_phase_sum_step`.
`_hμ`, `_hΓ` only make `μ(B_1)`, `Γ(B_1)` finite and are not used. -/
theorem all_static_phase_sum_paper {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (Z : ℕ → E) {alpha R h σ N : ℝ}
    (μ Γ : Measure (HomogHypothesis.Rd 3))
    (_hμ : IsLocallyFiniteMeasure μ) (_hΓ : IsLocallyFiniteMeasure Γ)
    (hα0 : 0 < alpha) (hα2 : alpha < 2)
    (hRdef : R = alpha * π * (μ (Metric.ball 0 1)).toReal / (2 * Real.sin (π * alpha / 2)))
    (hh : 0 < h)
    (hZ0 : ‖Z 0‖ ≤ √(Real.exp 1) * N)
    (hZ : ∀ n, 1 ≤ n → ‖Z n‖ ≤ (allOrdersA alpha * √R) ^ n * h ^ ((4 - alpha) * n / 2) /
      (n ! : ℝ) ^ ((3 - alpha) / 2) * N) :
    Summable (fun n => ‖σ ^ n • Z n‖) ∧ Summable (fun n => σ ^ n • Z n) ∧
      ‖∑' n, σ ^ n • Z n‖ ^ 2 ≤ (√(Real.exp 1) + 2) ^ 2 *
        Real.exp (6 * allOrdersA alpha ^ (2 / (3 - alpha)) * (|σ| ^ 2 * R) ^ (1 / (3 - alpha)) *
          h ^ ((4 - alpha) / (3 - alpha))) * N ^ 2 :=
  all_static_phase_sum_step Z hα0.le hα2.le (allOrdersA_pos (by linarith)).le
    (hRdef ▸ IntervalScalar.ralpha_nonneg μ hα0 hα2) hh hZ0 hZ

end StratonovichHAMSecondMoment.StaticPhaseCauchy
