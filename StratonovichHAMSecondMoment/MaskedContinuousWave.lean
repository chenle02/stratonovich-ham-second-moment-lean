module

/-
Copyright 2026 Le Chen. SPDX-License-Identifier: Apache-2.0

Lemma `L:masked-continuous-wave` (Continuous sine factors) of
`notes/integrated_covariance_foundation.tex` at revision a284420 (statement TeX
lines 378-390, display `E:masked-continuous-wave` 385-389, proof 392-423), with
the standing assumptions of its subsection (TeX lines 296-298) and of
`L:masked-time-completion` (TeX lines 141-181).

Statement formalized (`masked_continuous_wave_paper`).  Standing assumptions:
`0 < a < 1`, `T > 0`, `I = [s, s+h] ⊆ [0, T]` (`0 ≤ s`, `s + h ≤ T`),
`0 < h ≤ 1`.  Lemma data: `r, ρ ≥ 0`, `c_r(t) = cos(rt)`,
`b_r(t) = ⟨r⟩ sin(rt)/r` for `r > 0`, `b_0(t) = t` (`cFn`, `bFn`),
`F_r ∈ {c_r, b_r}`, `G_ρ ∈ {c_ρ, b_ρ}` (`Wave`, `Wave.eval`).  Conclusion:
`1_I F_r G_ρ` (`waveFn`) lies in the accepted class `V`, and
`‖1_I F_r G_ρ‖_a² ≤ C₁(a) (1+T)⁴ h^{2-a} 𝒬_h(r,ρ)` with
`C₁(a) = 4·3^{1-a}·C₀(a)` (`C₁`), `C₀(a) = 16/(1-a)`, the manuscript's constant.
No `Γ ≠ 0` (the TeX states none).

The norm `‖·‖_a` (abstract, as in `MaskedTrigProducts` and `MaskedModulation`).
The manuscript's norm is that of the complexified completion `H_a^ℂ` of
`L:masked-time-completion`.  The theorem is stated generically over the same
abstract data as `MaskedModulation.masked_trig_products_bridged_paper` (B24):
a complex inner product space `E`, a submodule `V` of `ℝ → ℂ` (the functions
accepted into the completion) and a linear inclusion `emb : V →ₗ[ℂ] E`; the
manuscript's `‖f‖_a` is `‖emb f‖`.  It takes exactly B24's two supplied inputs,
under B24's names:
* `hmem` — B24's `hmem` for every amplitude B24 accepts: for every
  `A ∈ C¹(I; ℂ)` and every real `ω`, `1_I A e^{iω·} ∈ V`.  Source:
  `L:masked-time-completion`, TeX lines 154-155 ("bounded measurable
  amplitudes on a subinterval, extended by zero, belong to this completion"),
  which covers every such `A` (continuous on the compact `I`, hence bounded and
  measurable after extension by zero); so the input is no stronger than its
  source.
* `hnorm` — verbatim B24's `hnorm`: for `f ∈ V` with `f ∈ L²(0,T)`,
  `‖emb f‖² = Re ∬_{[0,T]²} f(t) conj f(u) |t-u|^{-a}`.  Source: the
  complexification clause of `L:masked-time-completion` (TeX lines 153-154,
  with 148-149 and 177-179).
Once a concrete `H_a` is built (wave item L5-a) with its `V`, `emb` and proofs
of these two facts, one application of `masked_continuous_wave_paper`
discharges both inputs.

Proof route (differs from the TeX proof; same statement, same constant).  The
TeX (lines 392-423) writes `b_r = t⟨r⟩∫_0^1 cos(vrt) dv` for `r ≤ 1`, takes
`H_a`-valued Bochner averages over `[0,1]^k`, applies Hilbert Jensen and
`L:masked-trig-products` with `A(t) = t^j` to each integrand at frequencies
`r', ρ'` with `|r'-r|, |ρ'-ρ| ≤ 1`, and compares brackets.  Here no averaging
and no continuity of a parameter family in `H_a` is used.  Instead:
* each factor is written as an amplitude times a trigonometric factor
  (`amp`, `trig`, `fr`; `eval_eq`): `c_r = 1·cos(r·)`; for `r ≥ 1`,
  `b_r = (⟨r⟩/r)·sin(r·)`, the coefficient `⟨r⟩/r ≤ √2` going into the
  amplitude; for `r < 1` (including `r = 0`), `b_r = b_r·cos(0·)`, the whole
  factor going into the amplitude at frequency `0`;
* the amplitude `A` of `F_r G_ρ` is the product of the two factor amplitudes, a
  `C¹` function, and B24 (`masked_trig_products_bridged_paper`) is applied
  once, at the frequencies `r' ∈ {r, 0}`, `ρ' ∈ {ρ, 0}` (`|r'-r|, |ρ'-ρ| ≤ 1`);
* `M = sup_I |A|` and `D = sup_I |A'|` are bounded with `csSup_le`
  (`amp_prod_sup`): each factor has `M_i + h D_i ≤ √2(1+T)` (`amp_bound`), so
  `M + hD ≤ (M_1 + hD_1)(M_2 + hD_2) ≤ 2(1+T)²` and `(M+hD)² ≤ 4(1+T)⁴`;
* the bracket comparison is the TeX's (lines 411-419):
  `⟨x+e⟩ ≤ (1+|e|)⟨x⟩` (`bracket_add_le`), the arguments `h(r'±ρ')` differ from
  `h(r±ρ)` by at most `2` since `h ≤ 1`, so `𝒬_h(r',ρ') ≤ 3^{1-a} 𝒬_h(r,ρ)`
  (`frequencyPair_shift_le`).
Hence the bound `C₀ h^{2-a}·4(1+T)⁴·3^{1-a} 𝒬_h(r,ρ)`, i.e. `C₁(a)` exactly.
The case split `r < 1` / `r ≥ 1` differs from the TeX's `r ≤ 1` / `r ≥ 1`
only at `r = 1`, where both apply.

Implicit side conditions made explicit: `b_r` is the manuscript's for `r ≥ 0`
(the definition `bFn` also assigns a value at `r < 0`, never used since
`r, ρ ≥ 0` are hypotheses); functions are real-valued and enter `V ⊆ (ℝ → ℂ)`
through the coercion `ℝ → ℂ` (the complexified completion).  No `sSup`
appears in the statement; in the proof `M` and `D` are suprema of nonempty
bounded sets (`I` nonempty since `h > 0`), so no junk value enters.  `T > 0`
is carried in the wrapper but not used (it follows from `0 ≤ s`, `h > 0`,
`s + h ≤ T`).

Auxiliary to the Lean proof route (no direct manuscript label): `amp`, `trig`,
`fr` and every lemma whose doc string says "Auxiliary".
-/
public import Mathlib
public import StratonovichHAMSecondMoment.MaskedModulation

@[expose] public section

noncomputable section

set_option autoImplicit false

open MeasureTheory Set

namespace StratonovichHAMSecondMoment.MaskedContinuousWave

open StratonovichHAMSecondMoment.TimeSchur StratonovichHAMSecondMoment.MaskedTrigProducts
  StratonovichHAMSecondMoment.MaskedModulation

/-! ### The wave factors (TeX lines 379-384) -/

/-- `c_r(t) = cos(rt)` (TeX line 379). -/
def cFn (r t : ℝ) : ℝ := Real.cos (r * t)

/-- `b_r(t) = ⟨r⟩ sin(rt)/r` for `r ≠ 0` and `b_0(t) = t` (TeX lines 380-383;
the manuscript defines it for `r > 0` and `r = 0`, and only `r ≥ 0` is used). -/
def bFn (r t : ℝ) : ℝ := if r = 0 then t else bracket r * Real.sin (r * t) / r

/-- The two factor shapes `c` and `b` (TeX line 384). -/
inductive Wave
  | c
  | b

/-- `Wave.eval W r t` is `c_r(t)` or `b_r(t)`. -/
def Wave.eval : Wave → ℝ → ℝ → ℝ
  | .c, r, t => cFn r t
  | .b, r, t => bFn r t

/-- The masked product `t ↦ 1_I(t) F_r(t) G_ρ(t)`, viewed in `ℂ`. -/
def waveFn (I : Set ℝ) (F G : Wave) (r ρ : ℝ) : ℝ → ℂ :=
  I.indicator fun t => ((F.eval r t * G.eval ρ t : ℝ) : ℂ)

/-- `C₁(a) = 4·3^{1-a}·C₀(a)` (TeX line 388). -/
def C₁ (a : ℝ) : ℝ := 4 * 3 ^ (1 - a) * C₀ a

/-! ### Bracket comparison (TeX lines 411-419) -/

/-- `⟨x+e⟩ ≤ (1+|e|)⟨x⟩` (upper half of the display at TeX lines 413-416, on line 415). -/
theorem bracket_add_le (x e : ℝ) : bracket (x + e) ≤ (1 + |e|) * bracket x := by
  have h1 : (0 : ℝ) ≤ 1 + |e| := by positivity
  have hx : 2 * |x| ≤ 1 + x ^ 2 := by nlinarith [sq_nonneg (|x| - 1), sq_abs x]
  have hxe : x * e ≤ |x| * |e| := (le_abs_self _).trans_eq (abs_mul x e)
  have key : 1 + (x + e) ^ 2 ≤ ((1 + |e|) * bracket x) ^ 2 := by
    rw [mul_pow, bracket, Real.sq_sqrt (by positivity)]
    nlinarith [abs_nonneg e, sq_abs e, mul_nonneg (abs_nonneg e) (sq_nonneg (|x| - 1)),
      mul_le_mul_of_nonneg_right hx (abs_nonneg e), mul_nonneg (abs_nonneg e) (sq_nonneg x),
      sq_nonneg (e * x)]
  rw [bracket, Real.sqrt_le_iff]
  exact ⟨mul_nonneg h1 (Real.sqrt_nonneg _), key⟩

/-- `⟨x⟩ > 0`. -/
theorem bracket_pos (x : ℝ) : 0 < bracket x := lt_of_lt_of_le one_pos (one_le_bracket x)

/-- If `|x - x'| ≤ 2` and `a < 1`, then `⟨x'⟩^{a-1} ≤ 3^{1-a} ⟨x⟩^{a-1}` (TeX
lines 418-419: "each altered bracket to the power `a-1` is at most `3^{1-a}`
times the original one"). -/
theorem bracket_rpow_shift_le {a : ℝ} (ha1 : a < 1) {x x' : ℝ} (hxx : |x - x'| ≤ 2) :
    bracket x' ^ (a - 1) ≤ 3 ^ (1 - a) * bracket x ^ (a - 1) := by
  have hb : bracket x ≤ 3 * bracket x' := by
    have := bracket_add_le x' (x - x')
    rw [add_sub_cancel] at this
    refine this.trans (mul_le_mul_of_nonneg_right ?_ (bracket_pos x').le)
    linarith
  have hr : (3 * bracket x') ^ (a - 1) ≤ bracket x ^ (a - 1) :=
    Real.rpow_le_rpow_of_nonpos (bracket_pos x) hb (by linarith)
  rw [Real.mul_rpow (by norm_num) (bracket_pos x').le] at hr
  have h3 : (3 : ℝ) ^ (1 - a) * 3 ^ (a - 1) = 1 := by
    rw [← Real.rpow_add (by norm_num)]; simp
  have h3p : (0 : ℝ) ≤ 3 ^ (1 - a) := by positivity
  calc bracket x' ^ (a - 1) = 3 ^ (1 - a) * (3 ^ (a - 1) * bracket x' ^ (a - 1)) := by
        rw [← mul_assoc, h3, one_mul]
    _ ≤ 3 ^ (1 - a) * bracket x ^ (a - 1) := mul_le_mul_of_nonneg_left hr h3p

/-- Frequency shifts by at most one in each variable cost at most `3^{1-a}`:
for `0 ≤ h ≤ 1`, `|r'-r| ≤ 1`, `|ρ'-ρ| ≤ 1`, `𝒬_h(r',ρ') ≤ 3^{1-a} 𝒬_h(r,ρ)`
(TeX lines 417-419, "the changes in `h(r±ρ)` have magnitude at most two"). -/
theorem frequencyPair_shift_le {a h r ρ r' ρ' : ℝ} (ha1 : a < 1) (hh0 : 0 ≤ h) (hh1 : h ≤ 1)
    (hr : |r - r'| ≤ 1) (hρ : |ρ - ρ'| ≤ 1) :
    frequencyPair a h r' ρ' ≤ 3 ^ (1 - a) * frequencyPair a h r ρ := by
  obtain ⟨hr1, hr2⟩ := abs_le.mp hr
  obtain ⟨hρ1, hρ2⟩ := abs_le.mp hρ
  have d1 : |h * (r - ρ) - h * (r' - ρ')| ≤ 2 := by
    rw [abs_le]; constructor <;> nlinarith
  have d2 : |h * (r + ρ) - h * (r' + ρ')| ≤ 2 := by
    rw [abs_le]; constructor <;> nlinarith
  unfold frequencyPair
  rw [mul_add (3 ^ (1 - a) : ℝ)]
  exact add_le_add (bracket_rpow_shift_le ha1 d1) (bracket_rpow_shift_le ha1 d2)

/-! ### Amplitude decomposition of a factor (auxiliary to the Lean proof route) -/

/-- Auxiliary: the amplitude of a factor.  `c_r ↦ 1`; `b_r ↦ b_r` for `r < 1`;
`b_r ↦ ⟨r⟩/r` for `r ≥ 1`. -/
def amp : Wave → ℝ → ℝ → ℝ
  | .c, _, _ => 1
  | .b, r, t => if r < 1 then bFn r t else bracket r / r

/-- Auxiliary: the trigonometric shape of a factor (`cos`, except `sin` for
`b_r` with `r ≥ 1`). -/
def trig : Wave → ℝ → Trig
  | .c, _ => .cos
  | .b, r => if r < 1 then .cos else .sin

/-- Auxiliary: the frequency of a factor (`r`, except `0` for `b_r` with
`r < 1`). -/
def fr : Wave → ℝ → ℝ
  | .c, r => r
  | .b, r => if r < 1 then 0 else r

/-- Auxiliary: `F_r(t) = amp(t) · P(fr · t)`. -/
theorem eval_eq (W : Wave) (r t : ℝ) :
    ((W.eval r t : ℝ) : ℂ) = (amp W r t : ℂ) * (trig W r).eval (fr W r * t) := by
  cases W with
  | c => simp [Wave.eval, amp, trig, fr, Trig.eval, cFn]
  | b =>
    by_cases hr : r < 1
    · simp [Wave.eval, amp, trig, fr, Trig.eval, hr]
    · have hr0 : r ≠ 0 := by intro h; rw [h] at hr; norm_num at hr
      simp only [Wave.eval, amp, trig, fr, hr, ite_false, Trig.eval, bFn, hr0]
      push_cast
      ring

/-- Auxiliary: for `r ≥ 0`, the factor frequency is nonnegative and within one
of `r`. -/
theorem fr_spec (W : Wave) {r : ℝ} (hr : 0 ≤ r) : 0 ≤ fr W r ∧ |r - fr W r| ≤ 1 := by
  cases W with
  | c => simp [fr, hr]
  | b =>
    by_cases h1 : r < 1
    · simp only [fr, h1, ite_true, le_refl, sub_zero, true_and]
      rw [abs_of_nonneg hr]; exact h1.le
    · simp [fr, h1, hr]

/-- Auxiliary: `b_r` is `C¹` (smooth) for every `r`. -/
theorem bFn_contDiff (r : ℝ) : ContDiff ℝ 1 (bFn r) := by
  by_cases hr : r = 0
  · have : bFn r = fun t => t := by funext t; simp [bFn, hr]
    rw [this]; exact contDiff_id
  · have : bFn r = fun t => bracket r * Real.sin (r * t) / r := by funext t; simp [bFn, hr]
    rw [this]; fun_prop

/-- Auxiliary: every factor amplitude is `C¹`. -/
theorem amp_contDiff (W : Wave) (r : ℝ) : ContDiff ℝ 1 (amp W r) := by
  cases W with
  | c => exact contDiff_const
  | b =>
    by_cases h1 : r < 1
    · have : amp .b r = bFn r := by funext t; simp [amp, h1]
      rw [this]; exact bFn_contDiff r
    · have : amp .b r = fun _ => bracket r / r := by funext t; simp [amp, h1]
      rw [this]; exact contDiff_const

/-- Auxiliary: `|b_r(t)| ≤ ⟨r⟩|t|` and `|b_r'(t)| ≤ ⟨r⟩` for `r ≥ 0`. -/
theorem bFn_bounds {r : ℝ} (hr : 0 ≤ r) (t : ℝ) :
    |bFn r t| ≤ bracket r * |t| ∧ |deriv (bFn r) t| ≤ bracket r := by
  by_cases hr0 : r = 0
  · have : bFn r = fun t => t := by funext t; simp [bFn, hr0]
    rw [this, deriv_id'']
    subst hr0
    simp [bracket]
  · have hrp : 0 < r := lt_of_le_of_ne hr (Ne.symm hr0)
    have : bFn r = fun t => bracket r * Real.sin (r * t) / r := by funext t; simp [bFn, hr0]
    rw [this]
    have hd : HasDerivAt (fun t => bracket r * Real.sin (r * t) / r)
        (bracket r * (Real.cos (r * t) * (r * 1)) / r) t := by
      have := ((hasDerivAt_id t).const_mul r).sin.const_mul (bracket r)
      simpa using this.div_const r
    rw [hd.deriv]
    have hb := (bracket_pos r).le
    constructor
    · rw [abs_div, abs_mul, abs_of_nonneg hb, abs_of_pos hrp, div_le_iff₀ hrp]
      have := Real.abs_sin_le_abs (x := r * t)
      rw [abs_mul, abs_of_pos hrp] at this
      nlinarith
    · rw [show bracket r * (Real.cos (r * t) * (r * 1)) / r = bracket r * Real.cos (r * t) by
        field_simp]
      rw [abs_mul, abs_of_nonneg hb]
      exact mul_le_of_le_one_right hb (Real.abs_cos_le_one _)

/-- Auxiliary: `⟨r⟩ ≤ √2` for `0 ≤ r ≤ 1`. -/
theorem bracket_le_sqrt_two {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1) : bracket r ≤ √2 :=
  Real.sqrt_le_sqrt (by nlinarith)

/-- Auxiliary: `⟨r⟩/r ≤ √2` for `r ≥ 1` (TeX line 393: "a coefficient at most
`√2`"). -/
theorem bracket_div_le_sqrt_two {r : ℝ} (hr1 : 1 ≤ r) : bracket r / r ≤ √2 := by
  have hrp : 0 < r := by linarith
  rw [div_le_iff₀ hrp, bracket, Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  rw [mul_pow, Real.sq_sqrt (by norm_num)]
  nlinarith

/-- Auxiliary: per-factor envelope.  For `r ≥ 0`, `T ≥ 0`, `h ≤ 1` there are
`M_i, D_i ≥ 0` with `|amp| ≤ M_i`, `|amp'| ≤ D_i` on `[0, T]` and
`M_i + h D_i ≤ √2 (1+T)`. -/
theorem amp_bound (W : Wave) {r T h : ℝ} (hr : 0 ≤ r) (hT : 0 ≤ T) (hh1 : h ≤ 1) :
    ∃ Mi Di : ℝ, 0 ≤ Mi ∧ 0 ≤ Di ∧ Mi + h * Di ≤ √2 * (1 + T) ∧
      ∀ t ∈ Icc 0 T, |amp W r t| ≤ Mi ∧ |deriv (amp W r) t| ≤ Di := by
  have hs1 : (1 : ℝ) ≤ √2 := Real.one_le_sqrt.mpr (by norm_num)
  cases W with
  | c =>
    refine ⟨1, 0, zero_le_one, le_rfl, by nlinarith, fun t _ => ?_⟩
    have : amp .c r = fun _ => 1 := rfl
    simp [this]
  | b =>
    by_cases h1 : r < 1
    · have e : amp .b r = bFn r := by funext t; simp [amp, h1]
      have hb := bracket_le_sqrt_two hr h1.le
      refine ⟨√2 * T, √2, by positivity, by positivity, by nlinarith, fun t ht => ?_⟩
      rw [e]
      obtain ⟨b1, b2⟩ := bFn_bounds hr t
      refine ⟨b1.trans ?_, b2.trans hb⟩
      rw [abs_of_nonneg ht.1]
      exact mul_le_mul hb ht.2 ht.1 (by positivity)
    · have e : amp .b r = fun _ => bracket r / r := by funext t; simp [amp, h1]
      have hr1 : 1 ≤ r := not_lt.mp h1
      have hb := bracket_div_le_sqrt_two hr1
      refine ⟨bracket r / r, 0, by have := bracket_pos r; positivity, le_rfl, by nlinarith,
        fun t _ => ?_⟩
      rw [e]
      simp only [deriv_const', abs_zero, le_refl, and_true]
      rw [abs_of_nonneg (by have := bracket_pos r; positivity)]

/-! ### Envelope of a product amplitude (auxiliary to the Lean proof route) -/

/-- Auxiliary: for `C¹` real `f, g` with `|f| ≤ M_f`, `|f'| ≤ D_f`, `|g| ≤ M_g`,
`|g'| ≤ D_g` on `I = [s, s+h]`, `h > 0`, the amplitude `A = f g` (in `ℂ`) is
`C¹` on `I`, `sup_I |A| ≤ M_f M_g` and `sup_I |A'| ≤ M_f D_g + D_f M_g`, with
`A'` the derivative within `I` (the suprema are over the nonempty set `I`). -/
theorem amp_prod_sup {s h : ℝ} (hh : 0 < h) {f g : ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    (hg : ContDiff ℝ 1 g) {Mf Df Mg Dg : ℝ}
    (hfb : ∀ t ∈ Icc s (s + h), |f t| ≤ Mf ∧ |deriv f t| ≤ Df)
    (hgb : ∀ t ∈ Icc s (s + h), |g t| ≤ Mg ∧ |deriv g t| ≤ Dg) :
    ContDiffOn ℝ 1 (fun t => ((f t * g t : ℝ) : ℂ)) (Icc s (s + h)) ∧
      sSup ((fun t => ‖((f t * g t : ℝ) : ℂ)‖) '' Icc s (s + h)) ≤ Mf * Mg ∧
      sSup ((fun t => ‖derivWithin (fun t => ((f t * g t : ℝ) : ℂ)) (Icc s (s + h)) t‖) ''
        Icc s (s + h)) ≤ Mf * Dg + Df * Mg := by
  have hne : (Icc s (s + h)).Nonempty := nonempty_Icc.mpr (by linarith)
  have hMf : ∀ t ∈ Icc s (s + h), 0 ≤ Mf := fun t ht => (abs_nonneg _).trans (hfb t ht).1
  have hMg : ∀ t ∈ Icc s (s + h), 0 ≤ Mg := fun t ht => (abs_nonneg _).trans (hgb t ht).1
  refine ⟨?_, ?_, ?_⟩
  · have := (Complex.ofRealCLM.contDiff.comp (hf.mul hg)).contDiffOn (s := Icc s (s + h))
    simpa [Function.comp_def] using this
  · refine csSup_le (hne.image _) ?_
    rintro _ ⟨t, ht, rfl⟩
    dsimp only
    rw [Complex.norm_real, Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (hfb t ht).1 (hgb t ht).1 (abs_nonneg _) (hMf t ht)
  · refine csSup_le (hne.image _) ?_
    rintro _ ⟨t, ht, rfl⟩
    have hd : HasDerivAt (fun t => ((f t * g t : ℝ) : ℂ))
        (((deriv f t * g t + f t * deriv g t : ℝ)) : ℂ) t :=
      (((hf.differentiable one_ne_zero t).hasDerivAt).mul
        ((hg.differentiable one_ne_zero t).hasDerivAt)).ofReal_comp
    dsimp only
    rw [hd.hasDerivWithinAt.derivWithin (uniqueDiffOn_Icc (by linarith) t ht),
      Complex.norm_real, Real.norm_eq_abs]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul]
    have e1 := mul_le_mul (hfb t ht).2 (hgb t ht).1 (abs_nonneg _)
      ((abs_nonneg _).trans (hfb t ht).2)
    have e2 := mul_le_mul (hfb t ht).1 (hgb t ht).2 (abs_nonneg _) (hMf t ht)
    linarith

/-- Auxiliary: the masked product is a masked trigonometric product in the sense
of `MaskedTrigProducts.prodFn`, with amplitude `amp F r · amp G ρ` and
frequencies `fr F r`, `fr G ρ`. -/
theorem waveFn_eq_prodFn (I : Set ℝ) (F G : Wave) (r ρ : ℝ) :
    waveFn I F G r ρ = prodFn I (fun t => ((amp F r t * amp G ρ t : ℝ) : ℂ)) (trig F r)
      (trig G ρ) (fr F r) (fr G ρ) := by
  funext t
  simp only [waveFn, prodFn]
  by_cases ht : t ∈ I
  · rw [indicator_of_mem ht, indicator_of_mem ht]
    push_cast
    rw [eval_eq F r t, eval_eq G ρ t]
    ring
  · rw [indicator_of_notMem ht, indicator_of_notMem ht]

/-! ### The lemma -/

/-- `L:masked-continuous-wave` (TeX lines 378-423, display
`E:masked-continuous-wave` 385-389), exact hypotheses, inputs-supplied with
exactly the two inputs of `MaskedModulation.masked_trig_products_bridged_paper`
(B24), under its names.

Standing assumptions (TeX lines 296-298 and `L:masked-time-completion`):
`0 < a < 1`, `T > 0`, `I = [s, s+h] ⊆ [0, T]`, `0 < h ≤ 1`; lemma data:
`r, ρ ≥ 0`, `F, G ∈ {c, b}`.  The norm `‖f‖_a` is `‖emb f‖` for the linear
inclusion `emb : V →ₗ[ℂ] E` of the accepted class `V` into the complex inner
product space `E` (the manuscript's `H_a^ℂ`).  Supplied inputs:
* `hmem` — for every `A ∈ C¹(I; ℂ)` and real `ω`, `1_I A e^{iω·} ∈ V`
  (`L:masked-time-completion`, TeX lines 154-155; B24's `hmem` for every
  amplitude B24 accepts);
* `hnorm` — for `f ∈ V ∩ L²(0,T)`, `‖emb f‖² = Re ⟨f, f⟩_a`
  (`L:masked-time-completion`, TeX lines 153-154; B24's `hnorm` verbatim).

Conclusion: `1_I F_r G_ρ ∈ V`, and for it
`‖1_I F_r G_ρ‖_a² ≤ C₁(a) (1+T)⁴ h^{2-a} 𝒬_h(r,ρ)`, `C₁(a) = 4·3^{1-a}·C₀(a)`.

Proof route (differs from the TeX's `H_a`-valued Bochner averaging, lines
393-407): the `b`-factors with `r < 1` and the coefficients `⟨r⟩/r` with
`r ≥ 1` are moved into the `C¹` amplitude, B24 is applied once at frequencies
`r' ∈ {r, 0}`, `ρ' ∈ {ρ, 0}`, `M` and `D` are bounded with `csSup_le`, and the
brackets are compared as in the TeX (lines 411-419).  `T > 0` is carried but
not used. -/
theorem masked_continuous_wave_paper {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E]
    (a T s h : ℝ) (ha0 : 0 < a) (ha1 : a < 1) (hT : 0 < T)
    (hh0 : 0 < h) (hh1 : h ≤ 1) (hs : 0 ≤ s) (hsT : s + h ≤ T)
    (r ρ : ℝ) (hr : 0 ≤ r) (hρ : 0 ≤ ρ) (F G : Wave)
    (V : Submodule ℂ (ℝ → ℂ)) (emb : V →ₗ[ℂ] E)
    (hmem : ∀ A : ℝ → ℂ, ContDiffOn ℝ 1 A (Icc s (s + h)) →
      ∀ ω : ℝ, modeFn (Icc s (s + h)) A ω ∈ V)
    (hnorm : ∀ f : V, MemLp (f : ℝ → ℂ) 2 (volume.restrict (Icc 0 T)) →
      ‖emb f‖ ^ 2 = (timeForm a T f f).re) :
    waveFn (Icc s (s + h)) F G r ρ ∈ V ∧
      ∀ hp : waveFn (Icc s (s + h)) F G r ρ ∈ V,
        ‖emb ⟨waveFn (Icc s (s + h)) F G r ρ, hp⟩‖ ^ 2 ≤
          C₁ a * (1 + T) ^ 4 * h ^ (2 - a) * frequencyPair a h r ρ := by
  set I := Icc s (s + h) with hI
  set A : ℝ → ℂ := fun t => ((amp F r t * amp G ρ t : ℝ) : ℂ) with hA
  have hT0 : 0 ≤ T := by linarith
  have hIsub : ∀ t ∈ I, t ∈ Icc (0 : ℝ) T := fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩
  obtain ⟨Mf, Df, hMf, hDf, hsumf, hbf⟩ := amp_bound F hr hT0 hh1
  obtain ⟨Mg, Dg, hMg, hDg, hsumg, hbg⟩ := amp_bound G hρ hT0 hh1
  obtain ⟨hAc, hMle, hDle⟩ := amp_prod_sup hh0 (amp_contDiff F r) (amp_contDiff G ρ)
    (fun t ht => hbf t (hIsub t ht)) (fun t ht => hbg t (hIsub t ht))
  obtain ⟨hfr0, hfr1⟩ := fr_spec F hr
  obtain ⟨hfρ0, hfρ1⟩ := fr_spec G hρ
  set M := sSup ((fun t => ‖A t‖) '' I) with hM
  set D := sSup ((fun t => ‖derivWithin A I t‖) '' I) with hD
  obtain ⟨hmemP, hbound⟩ := masked_trig_products_bridged_paper a T s h ha0 ha1 hT hh0 hh1 hs hsT
    A hAc M D hM hD (fr F r) (fr G ρ) hfr0 hfρ0 (trig F r) (trig G ρ) V emb (hmem A hAc) hnorm
  have heq := waveFn_eq_prodFn I F G r ρ
  refine ⟨heq ▸ hmemP, fun hp => ?_⟩
  have hsub : (⟨waveFn I F G r ρ, hp⟩ : V) =
      ⟨prodFn I A (trig F r) (trig G ρ) (fr F r) (fr G ρ), heq ▸ hp⟩ := Subtype.ext heq
  rw [hsub]
  refine (hbound _).trans ?_
  -- the envelope `(M + hD)² ≤ 4(1+T)⁴`
  have hM0 : 0 ≤ M := Real.sSup_nonneg (by rintro _ ⟨t, _, rfl⟩; exact norm_nonneg _)
  have hD0 : 0 ≤ D := Real.sSup_nonneg (by rintro _ ⟨t, _, rfl⟩; exact norm_nonneg _)
  have hMD : M + h * D ≤ 2 * (1 + T) ^ 2 := by
    have h2 : (√2 * (1 + T)) * (√2 * (1 + T)) = 2 * (1 + T) ^ 2 := by
      rw [show (√2 * (1 + T)) * (√2 * (1 + T)) = (√2 * √2) * (1 + T) ^ 2 by ring,
        Real.mul_self_sqrt (by norm_num)]
    have hprod : (Mf + h * Df) * (Mg + h * Dg) ≤ (√2 * (1 + T)) * (√2 * (1 + T)) :=
      mul_le_mul hsumf hsumg (by positivity) (by positivity)
    have hh2 : 0 ≤ h * h * Df * Dg := by positivity
    have : M + h * D ≤ Mf * Mg + h * (Mf * Dg + Df * Mg) :=
      add_le_add hMle (mul_le_mul_of_nonneg_left hDle hh0.le)
    nlinarith
  have hMD2 : (M + h * D) ^ 2 ≤ 4 * (1 + T) ^ 4 := by
    have h0 : 0 ≤ M + h * D := by positivity
    calc (M + h * D) ^ 2 ≤ (2 * (1 + T) ^ 2) ^ 2 := pow_le_pow_left₀ h0 hMD 2
      _ = 4 * (1 + T) ^ 4 := by ring
  -- the frequency comparison `𝒬_h(r', ρ') ≤ 3^{1-a} 𝒬_h(r, ρ)`
  have hQ := frequencyPair_shift_le (a := a) ha1 hh0.le hh1 hfr1 hfρ1
  have hQ0 : 0 ≤ frequencyPair a h (fr F r) (fr G ρ) := by
    unfold frequencyPair
    have := bracket_pos (h * (fr F r - fr G ρ))
    have := bracket_pos (h * (fr F r + fr G ρ))
    positivity
  have hC0 : 0 ≤ C₀ a := div_nonneg (by norm_num) (by linarith)
  have hhp : 0 ≤ h ^ (2 - a) := Real.rpow_nonneg hh0.le _
  calc C₀ a * h ^ (2 - a) * (M + h * D) ^ 2 * frequencyPair a h (fr F r) (fr G ρ)
      ≤ C₀ a * h ^ (2 - a) * (4 * (1 + T) ^ 4) *
          (3 ^ (1 - a) * frequencyPair a h r ρ) := by
        gcongr
    _ = C₁ a * (1 + T) ^ 4 * h ^ (2 - a) * frequencyPair a h r ρ := by
        unfold C₁; ring

end StratonovichHAMSecondMoment.MaskedContinuousWave
