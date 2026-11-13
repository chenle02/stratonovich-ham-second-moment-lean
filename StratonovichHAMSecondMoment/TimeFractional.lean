module

/-
Copyright 2026 Le Chen. SPDX-License-Identifier: Apache-2.0

Time-fractional ingredients of the main TeX file
`notes/notes_stratonovich_ham_second_moment.tex` (revision a284420) used by
`P:clock-copy-obstruction` (lines 7754-7905) and by the finiteness part of
`L:damped-homogeneous-norms` (lines 803-919).

Formalized here (all proved, no supplied input):
* the Gamma-integral (subordination) representation of the power kernel,
  `r^{-a} = Γ(a)⁻¹ ∫_0^∞ λ^{a-1} e^{-λ r} dλ` for `r > 0`
  (`rpow_neg_eq_subordination`; it is the "Laplace formula for the power
  covariance" invoked in the proof of `P:clock-copy-obstruction`);
* the averaged clock kernel `Ψ_a` of `E:averaged-clock-kernel` (line 7704)
  with the three properties stated after it: nonnegativity (in fact
  positivity), monotone decrease in `v`, and `Ψ_a(r,v) ≤ r^{-a}`;
* the two-time Laplace lemma, for complex `a, b` with positive real part
  and `λ ≥ 0`,
  `∫∫_{(0,∞)²} e^{-as-bt-λ|s-t|} ds dt = (a+b+2λ)/((a+b)(a+λ)(b+λ))`
  (`twoTimeC_integral`), and its real case `1/(c(c+λ))`.  The manuscript
  does this integration "over the two cones `s = t+v`, `t = s+v`" in the
  proof of `P:clock-copy-obstruction`; here it is one lemma used for both the
  `K` side (with `a, b = θ ∓ i r`) and the `J` side (real `a = b`).

Auxiliary to the Lean proof route (no direct manuscript label):
`integral_pos_of_ae_pos`, `integrable_of_rpow_bounds`, the half-cone
integrals, `iterated_integral_swap` (a Fubini rearrangement of a triple
integral) and `lintegral_triple_twoTime` (the corresponding Tonelli
computation).  The Bochner integral of a non-integrable function is `0` in
Lean, so integrability is stated or proved separately where it matters
(`subKernel_integrable`, `psiKernel_integrable`, `twoTimeC_integral`,
`twoTimeR_integral`); identities such as `rpow_neg_eq_subordination` and
`integral_cexp_neg_Ioi` do not carry it.
-/

public import Mathlib

@[expose] public section

noncomputable section

set_option autoImplicit false

open MeasureTheory Set Real Filter
open scoped ENNReal

namespace StratonovichHAMSecondMoment.TimeFractional

/-- Lebesgue measure on `(0,∞)`. -/
abbrev L0 : Measure ℝ := volume.restrict (Ioi (0 : ℝ))

/-- Lebesgue measure on `(0,∞)²`, as a product measure. -/
abbrev P2 : Measure (ℝ × ℝ) := L0.prod L0

/-! ### Two general helpers (auxiliary to the Lean proof route) -/

/-- Auxiliary to the Lean proof route. An integrable function that is a.e. positive for a nonzero
measure has a
positive integral. -/
theorem integral_pos_of_ae_pos {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℝ} (hf : Integrable f μ) (hμ : μ ≠ 0) (hpos : ∀ᵐ x ∂μ, 0 < f x) :
    0 < ∫ x, f x ∂μ := by
  rw [integral_pos_iff_support_of_nonneg_ae (hpos.mono fun _ h => h.le) hf]
  refine pos_iff_ne_zero.2 fun h0 => hμ ?_
  have h1 : ∀ᵐ x ∂μ, x ∉ Function.support f := measure_eq_zero_iff_ae_notMem.1 h0
  have h2 : ∀ᵐ _x ∂μ, False := (h1.and hpos).mono fun x hx => hx.1 hx.2.ne'
  exact ae_eq_bot.1 (eventually_false_iff_eq_bot.1 h2)

/-- Auxiliary to the Lean proof route. Integrability on `(0,∞)` from the bounds `C λ^p` on
`(0,1]` (`p > -1`) and
`C λ^q` on `(1,∞)` (`q < -1`). -/
theorem integrable_of_rpow_bounds (p q C : ℝ) (hp : -1 < p) (hq : q < -1) {f : ℝ → ℝ}
    (hf : AEStronglyMeasurable f L0)
    (hb1 : ∀ l : ℝ, 0 < l → l ≤ 1 → ‖f l‖ ≤ C * l ^ p)
    (hb2 : ∀ l : ℝ, 1 < l → ‖f l‖ ≤ C * l ^ q) :
    Integrable f L0 := by
  show IntegrableOn f (Ioi 0)
  rw [← Ioc_union_Ioi_eq_Ioi (zero_le_one : (0 : ℝ) ≤ 1)]
  refine IntegrableOn.union ?_ ?_
  · have hI : IntegrableOn (fun l : ℝ => l ^ p) (Ioc 0 1) := by
      rw [integrableOn_Ioc_iff_integrableOn_Ioo]
      exact (intervalIntegral.integrableOn_Ioo_rpow_iff zero_lt_one).2 hp
    refine Integrable.mono' (hI.const_mul C) (hf.mono_set Ioc_subset_Ioi_self) ?_
    exact (ae_restrict_iff' measurableSet_Ioc).2
      (Eventually.of_forall fun l hl => hb1 l hl.1 hl.2)
  · have hI : IntegrableOn (fun l : ℝ => l ^ q) (Ioi 1) :=
      (integrableOn_Ioi_rpow_iff zero_lt_one).2 hq
    refine Integrable.mono' (hI.const_mul C)
      (hf.mono_set (Ioi_subset_Ioi zero_le_one)) ?_
    exact (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun l hl => hb2 l hl)

/-! ### Subordination: the Laplace formula for the power kernel -/

/-- Auxiliary to the Lean proof route. The subordination integrand `λ^{a-1} e^{-rλ}`. -/
def subKernel (a r l : ℝ) : ℝ := l ^ (a - 1) * Real.exp (-(r * l))

/-- Auxiliary to the Lean proof route. -/
theorem subKernel_integrable (a r : ℝ) (ha : 0 < a) (hr : 0 < r) :
    Integrable (subKernel a r) L0 := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := a - 1) (b := r)
    (by linarith) one_pos hr
  simp only [Real.rpow_one] at h
  refine h.congr (Eventually.of_forall fun l => ?_)
  simp [subKernel, neg_mul]

/-- Auxiliary to the Lean proof route. -/
theorem subKernel_nonneg (a r l : ℝ) (hl : 0 ≤ l) : 0 ≤ subKernel a r l :=
  mul_nonneg (Real.rpow_nonneg hl _) (Real.exp_pos _).le

/-- Subordination: for `a, r > 0`,
`r^{-a} = Γ(a)⁻¹ ∫_0^∞ λ^{a-1} e^{-rλ} dλ` (the integrand is integrable by
`subKernel_integrable`). -/
theorem rpow_neg_eq_subordination (a r : ℝ) (ha : 0 < a) (hr : 0 < r) :
    r ^ (-a) = (Real.Gamma a)⁻¹ * ∫ l in Ioi (0 : ℝ), subKernel a r l := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi ha hr
  have hG : Real.Gamma a ≠ 0 := (Real.Gamma_pos_of_pos ha).ne'
  simp only [subKernel]
  rw [h, one_div, Real.inv_rpow hr.le, Real.rpow_neg hr.le]
  field_simp

/-! ### The averaged clock kernel `Ψ_a` (`E:averaged-clock-kernel`) -/

/-- Auxiliary to the Lean proof route. The integrand of `Ψ_a`. -/
def psiKernel (a r v l : ℝ) : ℝ := l ^ (a - 1) * Real.exp (-(r * l) - v * l ^ 2 / 2)

/-- `E:averaged-clock-kernel` (line 7704):
`Ψ_a(r,v) = Γ(a)⁻¹ ∫_0^∞ λ^{a-1} e^{-rλ - vλ²/2} dλ`. -/
def Psi (a r v : ℝ) : ℝ := (Real.Gamma a)⁻¹ * ∫ l in Ioi (0 : ℝ), psiKernel a r v l

/-- Auxiliary to the Lean proof route. -/
theorem psiKernel_measurable (a r v : ℝ) : Measurable (psiKernel a r v) := by
  unfold psiKernel; fun_prop

/-- Auxiliary to the Lean proof route. -/
theorem psiKernel_le (a r v l : ℝ) (hv : 0 ≤ v) (hl : 0 ≤ l) :
    psiKernel a r v l ≤ subKernel a r l := by
  unfold psiKernel subKernel
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (Real.rpow_nonneg hl _)
  have : 0 ≤ v * l ^ 2 / 2 := by positivity
  linarith

/-- Auxiliary to the Lean proof route. -/
theorem psiKernel_pos (a r v l : ℝ) (hl : 0 < l) : 0 < psiKernel a r v l :=
  mul_pos (Real.rpow_pos_of_pos hl _) (Real.exp_pos _)

/-- Auxiliary to the Lean proof route. -/
theorem psiKernel_integrable (a r v : ℝ) (ha : 0 < a) (hr : 0 < r) (hv : 0 ≤ v) :
    Integrable (psiKernel a r v) L0 := by
  refine Integrable.mono' (subKernel_integrable a r ha hr)
    (psiKernel_measurable a r v).aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun l hl => ?_)
  rw [Real.norm_of_nonneg (psiKernel_pos a r v l hl).le]
  exact psiKernel_le a r v l hv (le_of_lt hl)

/-- `Ψ_a(r,0) = r^{-a}` for `r > 0`. -/
theorem Psi_zero (a r : ℝ) (ha : 0 < a) (hr : 0 < r) : Psi a r 0 = r ^ (-a) := by
  rw [rpow_neg_eq_subordination a r ha hr, Psi]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun l => ?_)
  simp [psiKernel, subKernel]

/-- `Ψ_a(r,v) > 0` for `r > 0`, `v ≥ 0` (the manuscript states `Ψ_a ≥ 0`). -/
theorem Psi_pos (a r v : ℝ) (ha : 0 < a) (hr : 0 < r) (hv : 0 ≤ v) : 0 < Psi a r v := by
  refine mul_pos (inv_pos.2 (Real.Gamma_pos_of_pos ha)) ?_
  refine integral_pos_of_ae_pos (psiKernel_integrable a r v ha hr hv) ?_ ?_
  · simp
  · exact (ae_restrict_iff' measurableSet_Ioi).2
      (Eventually.of_forall fun l hl => psiKernel_pos a r v l hl)

/-- `Ψ_a(r,·)` decreases: `0 ≤ v ≤ v'` gives `Ψ_a(r,v') ≤ Ψ_a(r,v)`. -/
theorem Psi_antitone (a r v v' : ℝ) (ha : 0 < a) (hr : 0 < r) (hv : 0 ≤ v) (hvv : v ≤ v') :
    Psi a r v' ≤ Psi a r v := by
  refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 (Real.Gamma_pos_of_pos ha).le)
  refine integral_mono_ae (psiKernel_integrable a r v' ha hr (hv.trans hvv))
    (psiKernel_integrable a r v ha hr hv) ?_
  refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun l hl => ?_)
  unfold psiKernel
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (Real.rpow_nonneg hl.le _)
  have : v * l ^ 2 / 2 ≤ v' * l ^ 2 / 2 := by
    have := sq_nonneg l
    nlinarith
  linarith

/-- `Ψ_a(r,v) ≤ r^{-a}` for `r > 0`, `v ≥ 0`. -/
theorem Psi_le_rpow (a r v : ℝ) (ha : 0 < a) (hr : 0 < r) (hv : 0 ≤ v) :
    Psi a r v ≤ r ^ (-a) := by
  rw [← Psi_zero a r ha hr]
  exact Psi_antitone a r 0 v ha hr le_rfl hv

/-- The three properties of `Ψ_a` stated after `E:averaged-clock-kernel`
(lines 7708-7713), for `0 < a`, `r > 0`, `0 ≤ v ≤ v'`. -/
theorem Psi_properties_paper (a r v v' : ℝ) (ha : 0 < a) (hr : 0 < r) (hv : 0 ≤ v)
    (hvv : v ≤ v') :
    Integrable (psiKernel a r v) L0 ∧ 0 ≤ Psi a r v ∧ Psi a r v' ≤ Psi a r v ∧
      Psi a r v ≤ r ^ (-a) :=
  ⟨psiKernel_integrable a r v ha hr hv, (Psi_pos a r v ha hr hv).le,
    Psi_antitone a r v v' ha hr hv hvv, Psi_le_rpow a r v ha hr hv⟩

/-! ### The two-time Laplace lemma -/

/-- The two-time kernel `e^{-as-bt-λ|s-t|}` with complex `a, b`. -/
def twoTimeC (a b : ℂ) (lam : ℝ) (p : ℝ × ℝ) : ℂ :=
  Complex.exp (-(a * (p.1 : ℂ)) - b * (p.2 : ℂ) - (lam : ℂ) * ((|p.1 - p.2| : ℝ) : ℂ))

/-- Auxiliary to the Lean proof route. -/
theorem twoTimeC_continuous (a b : ℂ) (lam : ℝ) : Continuous (twoTimeC a b lam) := by
  unfold twoTimeC; fun_prop

/-- Auxiliary to the Lean proof route. -/
theorem integrable_exp_neg (c : ℝ) (hc : 0 < c) :
    Integrable (fun x : ℝ => Real.exp (-c * x)) L0 :=
  exp_neg_integrableOn_Ioi 0 hc

/-- Auxiliary to the Lean proof route. -/
theorem twoTimeC_integrable (a b : ℂ) (lam : ℝ) (ha : 0 < a.re) (hb : 0 < b.re)
    (hl : 0 ≤ lam) : Integrable (twoTimeC a b lam) P2 := by
  refine Integrable.mono' ((integrable_exp_neg a.re ha).mul_prod (integrable_exp_neg b.re hb))
    (twoTimeC_continuous a b lam).aestronglyMeasurable (Eventually.of_forall fun p => ?_)
  simp only [twoTimeC, Complex.norm_exp]
  rw [← Real.exp_add, Real.exp_le_exp]
  simp only [Complex.sub_re, Complex.neg_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero]
  have : 0 ≤ lam * |p.1 - p.2| := mul_nonneg hl (abs_nonneg _)
  nlinarith

/-- Auxiliary to the Lean proof route. The cone integral
`∫_{t > s} e^{-as-bt-λ(t-s)} dt = e^{-(a+b)s}/(b+λ)`. -/
theorem twoTimeC_cone (a b : ℂ) (lam : ℝ) (hb : 0 < b.re) (hl : 0 ≤ lam) (s : ℝ) :
    ∫ t in Ioi s, twoTimeC a b lam (s, t) = Complex.exp (-(a + b) * s) / (b + lam) := by
  have hre : (-(b + (lam : ℂ))).re < 0 := by simp; linarith
  have hne : b + (lam : ℂ) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  rw [setIntegral_congr_fun measurableSet_Ioi (g := fun t : ℝ =>
    Complex.exp (((lam : ℂ) - a) * s) * Complex.exp (-(b + (lam : ℂ)) * t)) ?_]
  · rw [integral_const_mul, integral_exp_mul_complex_Ioi hre s, neg_div_neg_eq,
      ← mul_div_assoc, ← Complex.exp_add]
    congr 2
    ring
  · intro t ht
    have hts : |s - t| = t - s := by
      rw [abs_sub_comm]; exact abs_of_pos (sub_pos.2 ht)
    simp only [twoTimeC, hts, ← Complex.exp_add]
    congr 1
    push_cast
    ring

/-- Auxiliary to the Lean proof route. -/
theorem twoTimeC_half_lt (a b : ℂ) (lam : ℝ) (hb : 0 < b.re) (hl : 0 ≤ lam) (s : ℝ)
    (hs : 0 < s) :
    ∫ t in Ioi (0 : ℝ), (Ioi s).indicator (fun t => twoTimeC a b lam (s, t)) t =
      Complex.exp (-(a + b) * s) / (b + lam) := by
  rw [setIntegral_indicator measurableSet_Ioi,
    inter_eq_right.2 (Ioi_subset_Ioi hs.le), twoTimeC_cone a b lam hb hl s]

/-- Auxiliary to the Lean proof route. -/
theorem twoTimeC_half_le (a b : ℂ) (lam : ℝ) (hb : 0 < b.re) (hl : 0 ≤ lam) (s : ℝ)
    (hs : 0 < s) :
    ∫ t in Ioi (0 : ℝ), (Ici s).indicator (fun t => twoTimeC a b lam (s, t)) t =
      Complex.exp (-(a + b) * s) / (b + lam) := by
  rw [setIntegral_indicator measurableSet_Ici,
    inter_eq_right.2 (Ici_subset_Ioi.2 hs), integral_Ici_eq_integral_Ioi,
    twoTimeC_cone a b lam hb hl s]

/-- Auxiliary to the Lean proof route. -/
theorem integral_cexp_neg_Ioi (z : ℂ) (hz : 0 < z.re) :
    ∫ s in Ioi (0 : ℝ), Complex.exp (-z * s) = 1 / z := by
  have hre : (-z).re < 0 := by simp; linarith
  rw [integral_exp_mul_complex_Ioi hre 0]
  simp

/-- Auxiliary to the Lean proof route. One half of the two-time integral: the cone `s < t`. -/
theorem twoTimeC_integral_lt (a b : ℂ) (lam : ℝ) (ha : 0 < a.re) (hb : 0 < b.re)
    (hl : 0 ≤ lam) :
    ∫ p, {p : ℝ × ℝ | p.1 < p.2}.indicator (twoTimeC a b lam) p ∂P2 =
      1 / (a + b) / (b + lam) := by
  have hS : MeasurableSet {p : ℝ × ℝ | p.1 < p.2} :=
    measurableSet_lt measurable_fst measurable_snd
  rw [integral_prod _ ((twoTimeC_integrable a b lam ha hb hl).indicator hS)]
  have hab : 0 < (a + b).re := by simp; linarith
  rw [setIntegral_congr_fun measurableSet_Ioi (g := fun s : ℝ =>
    Complex.exp (-(a + b) * s) / (b + lam)) ?_]
  · rw [integral_div, integral_cexp_neg_Ioi _ hab]
  · intro s hs
    dsimp only
    rw [← twoTimeC_half_lt a b lam hb hl s hs]
    congr 1

/-- Auxiliary to the Lean proof route. -/
theorem twoTimeC_swap (a b : ℂ) (lam : ℝ) (p : ℝ × ℝ) :
    twoTimeC a b lam p.swap = twoTimeC b a lam p := by
  simp only [twoTimeC, Prod.fst_swap, Prod.snd_swap, abs_sub_comm p.2 p.1]
  congr 1
  ring

/-- The two-time Laplace lemma: for `Re a, Re b > 0` and `λ ≥ 0`,
`∫∫_{(0,∞)²} e^{-as-bt-λ|s-t|} ds dt = (a+b+2λ)/((a+b)(a+λ)(b+λ))`. -/
theorem twoTimeC_integral (a b : ℂ) (lam : ℝ) (ha : 0 < a.re) (hb : 0 < b.re)
    (hl : 0 ≤ lam) :
    Integrable (twoTimeC a b lam) P2 ∧
      ∫ p, twoTimeC a b lam p ∂P2 =
        (a + b + 2 * lam) / ((a + b) * (a + lam) * (b + lam)) := by
  have hI := twoTimeC_integrable a b lam ha hb hl
  refine ⟨hI, ?_⟩
  have hS : MeasurableSet {p : ℝ × ℝ | p.1 < p.2} :=
    measurableSet_lt measurable_fst measurable_snd
  have hsplit := integral_add (hI.indicator hS) (hI.indicator hS.compl)
  simp only [indicator_self_add_compl_apply] at hsplit
  rw [hsplit, twoTimeC_integral_lt a b lam ha hb hl]
  -- the cone `t ≤ s`, by the swap `(s,t) ↦ (t,s)`
  have hS' : MeasurableSet {p : ℝ × ℝ | p.1 ≤ p.2} :=
    measurableSet_le measurable_fst measurable_snd
  have hcompl : ∫ p, ({p : ℝ × ℝ | p.1 < p.2}ᶜ).indicator (twoTimeC a b lam) p ∂P2 =
      ∫ p, {p : ℝ × ℝ | p.1 ≤ p.2}.indicator (twoTimeC b a lam) p ∂P2 := by
    rw [← integral_prod_swap]
    congr 1
    funext p
    simp only [indicator_apply, mem_compl_iff, mem_ofPred_eq, not_lt, Prod.fst_swap,
      Prod.snd_swap]
    rw [← twoTimeC_swap b a lam p.swap, Prod.swap_swap]
  rw [hcompl, integral_prod _ ((twoTimeC_integrable b a lam hb ha hl).indicator hS')]
  have hab : 0 < (b + a).re := by simp; linarith
  rw [setIntegral_congr_fun measurableSet_Ioi (g := fun s : ℝ =>
    Complex.exp (-(b + a) * s) / (a + lam)) ?_]
  · rw [integral_div, integral_cexp_neg_Ioi _ hab]
    have h1 : a + b ≠ 0 := by
      intro h; have := congrArg Complex.re h; simp at this; linarith
    have h2 : a + (lam : ℂ) ≠ 0 := by
      intro h; have := congrArg Complex.re h; simp at this; linarith
    have h3 : b + (lam : ℂ) ≠ 0 := by
      intro h; have := congrArg Complex.re h; simp at this; linarith
    have h4 : b + a ≠ 0 := by rw [add_comm]; exact h1
    field_simp
    ring
  · intro s hs
    dsimp only
    rw [← twoTimeC_half_le b a lam ha hl s hs]
    congr 1

/-- The real two-time kernel `e^{-c(s+t)-λ|s-t|}`. -/
def twoTimeR (c lam : ℝ) (p : ℝ × ℝ) : ℝ :=
  Real.exp (-(c * (p.1 + p.2)) - lam * |p.1 - p.2|)

/-- Auxiliary to the Lean proof route. -/
theorem twoTimeR_ofReal (c lam : ℝ) (p : ℝ × ℝ) :
    ((twoTimeR c lam p : ℝ) : ℂ) = twoTimeC c c lam p := by
  simp only [twoTimeR, twoTimeC, Complex.ofReal_exp]
  congr 1
  push_cast
  ring

/-- Auxiliary to the Lean proof route. -/
theorem twoTimeR_pos (c lam : ℝ) (p : ℝ × ℝ) : 0 < twoTimeR c lam p := Real.exp_pos _

/-- The real two-time lemma: `∫∫ e^{-c(s+t)-λ|s-t|} = 1/(c(c+λ))`. -/
theorem twoTimeR_integral (c lam : ℝ) (hc : 0 < c) (hl : 0 ≤ lam) :
    Integrable (twoTimeR c lam) P2 ∧ ∫ p, twoTimeR c lam p ∂P2 = 1 / (c * (c + lam)) := by
  obtain ⟨hI, hV⟩ := twoTimeC_integral (c : ℂ) (c : ℂ) lam (by simpa using hc)
    (by simpa using hc) hl
  refine ⟨?_, ?_⟩
  · refine hI.re.congr (Eventually.of_forall fun p => ?_)
    simp only [← twoTimeR_ofReal, RCLike.re_to_complex, Complex.ofReal_re]
  · apply Complex.ofReal_injective
    rw [← integral_complex_ofReal]
    simp_rw [twoTimeR_ofReal]
    rw [hV]
    have h1 : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
    have h2 : (c : ℂ) + lam ≠ 0 := by exact_mod_cast (by linarith : c + lam ≠ 0)
    push_cast
    field_simp
    ring

/-- Auxiliary to the Lean proof route. -/
theorem twoTimeR_lintegral (c lam : ℝ) (hc : 0 < c) (hl : 0 ≤ lam) :
    ∫⁻ p, ENNReal.ofReal (twoTimeR c lam p) ∂P2 = ENNReal.ofReal (1 / (c * (c + lam))) := by
  obtain ⟨hI, hV⟩ := twoTimeR_integral c lam hc hl
  rw [← hV, ofReal_integral_eq_lintegral_ofReal hI
    (Eventually.of_forall fun p => (twoTimeR_pos c lam p).le)]

/-! ### Fubini and Tonelli rearrangements (auxiliary to the Lean proof route) -/

/-- Auxiliary to the Lean proof route. For `F` integrable on `X × (Y × Z)`, the iterated
integrals in the orders
`z, y, x` and `x, y, z` agree. -/
theorem iterated_integral_swap {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace Z] {μX : Measure X} {μY : Measure Y} {μZ : Measure Z} [SFinite μX]
    [SFinite μY] [SFinite μZ] (F : X × (Y × Z) → ℝ)
    (hF : Integrable F (μX.prod (μY.prod μZ))) :
    ∫ z, ∫ y, ∫ x, F (x, (y, z)) ∂μX ∂μY ∂μZ =
      ∫ x, ∫ y, ∫ z, F (x, (y, z)) ∂μZ ∂μY ∂μX := by
  have h1 := integral_prod F hF
  have h2 := integral_prod_symm F hF
  have hG : Integrable (fun yz : Y × Z => ∫ x, F (x, yz) ∂μX) (μY.prod μZ) :=
    hF.integral_prod_right
  have h3 := integral_prod_symm _ hG
  have h4 : (fun x => ∫ yz, F (x, yz) ∂(μY.prod μZ)) =ᵐ[μX]
      fun x => ∫ y, ∫ z, F (x, (y, z)) ∂μZ ∂μY :=
    hF.prod_right_ae.mono fun x hx => integral_prod _ hx
  rw [← h3, ← h2, h1]
  exact integral_congr_ae h4

/-- Auxiliary to the Lean proof route. Tonelli for a nonnegative amplitude times the real
two-time kernel, with
the time variables innermost. -/
theorem lintegral_triple_twoTime {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (ν : Measure X) (μ : Measure Y) [SFinite ν] [SFinite μ] (f c A : X → Y → ℝ)
    (hf : Measurable (Function.uncurry f)) (hc : Measurable (Function.uncurry c))
    (hA : Measurable (Function.uncurry A)) (hf0 : ∀ x y, 0 ≤ f x y)
    (hc0 : ∀ x y, 0 < c x y) (hA0 : ∀ x y, 0 ≤ A x y) :
    ∫⁻ z, ENNReal.ofReal (f z.1 z.2.1 * twoTimeR (c z.1 z.2.1) (A z.1 z.2.1) z.2.2)
        ∂(ν.prod (μ.prod P2)) =
      ∫⁻ x, ∫⁻ y, ENNReal.ofReal (f x y / (c x y * (c x y + A x y))) ∂μ ∂ν := by
  have hmeas : Measurable fun z : X × (Y × (ℝ × ℝ)) =>
      ENNReal.ofReal (f z.1 z.2.1 * twoTimeR (c z.1 z.2.1) (A z.1 z.2.1) z.2.2) := by
    have e1 : Measurable fun z : X × (Y × (ℝ × ℝ)) => f z.1 z.2.1 :=
      hf.comp (measurable_fst.prodMk measurable_snd.fst)
    have e2 : Measurable fun z : X × (Y × (ℝ × ℝ)) => c z.1 z.2.1 :=
      hc.comp (measurable_fst.prodMk measurable_snd.fst)
    have e3 : Measurable fun z : X × (Y × (ℝ × ℝ)) => A z.1 z.2.1 :=
      hA.comp (measurable_fst.prodMk measurable_snd.fst)
    unfold twoTimeR
    fun_prop
  rw [lintegral_prod _ hmeas.aemeasurable]
  refine lintegral_congr fun x => ?_
  have hm2 : Measurable fun yp : Y × (ℝ × ℝ) =>
      ENNReal.ofReal (f x yp.1 * twoTimeR (c x yp.1) (A x yp.1) yp.2) :=
    hmeas.comp measurable_prodMk_left
  dsimp only
  rw [lintegral_prod _ hm2.aemeasurable]
  refine lintegral_congr fun y => ?_
  simp_rw [ENNReal.ofReal_mul (hf0 x y)]
  rw [lintegral_const_mul _ ?_, twoTimeR_lintegral _ _ (hc0 x y) (hA0 x y),
    ← ENNReal.ofReal_mul (hf0 x y)]
  · congr 1
    ring
  · unfold twoTimeR
    fun_prop

end StratonovichHAMSecondMoment.TimeFractional
