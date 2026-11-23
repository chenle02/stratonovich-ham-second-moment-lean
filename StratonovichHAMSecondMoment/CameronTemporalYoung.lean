module

/-
Copyright 2026 Le Chen. SPDX-License-Identifier: Apache-2.0

Wave L16, item L16-C (part 1): the two shared lemmas of `P:cameron-temporal-map` that item D
uses, `YoungTarget` and `KformAbsTarget` (frozen in `CameronInterface`).

TeX anchors: `integrated_cameron_mean.tex` lines 280-293 at revision edf7085f (book
1.1.3), Step 3 of the proof of `P:cameron-temporal-map`.

* `young : YoungTarget`: the three-exponent Young inequality `‖f * h‖_r ≤ ‖f‖_u ‖h‖_v`
  (`1/u + 1/v = 1 + 1/r`), proved as in the TeX (lines 288-292) by splitting the integrand into
  `(f^u h^v)^{1/r}`, `f^{u(1/u-1/r)}` and `h^{v(1/v-1/r)}` and applying Hölder with three
  exponents (`ENNReal.lintegral_prod_norm_pow_le`) and Tonelli.  Mathlib has no Young
  convolution inequality.
* `kform_abs (p) : KformAbsTarget p`: `∫∫_{I²} |s-t|^{-a} |F(s)| |F(t)| ≤ ‖K_a‖_{r/2} ‖F‖²_{r'}`
  (lines 283-287), by Hölder (`r'`, `r`) and Young (`u = r'`, `v = r/2`) applied to the zero
  extension of `|F|` and `K_a(v) = |v|^{-a} 1_{|v| ≤ 1}`.
-/
public import Mathlib
public import StratonovichHAMSecondMoment.CameronInterface

@[expose] public section

noncomputable section

set_option autoImplicit false

open MeasureTheory Set Filter
open scoped ENNReal

namespace StratonovichHAMSecondMoment.CameronTemporal

open SpaceTimePositivity (timeMeasure)
open TimeSchur (kern kern_nonneg measurable_kern)
open OccupationCompletion (TParams)
open CameronInterface (YoungTarget KformAbsTarget KaNorm)

/-! ### Young's convolution inequality (three exponents) -/

/-- Auxiliary: the pointwise splitting of the Young integrand (TeX lines 290-291):
`a b = (a^u b^v)^{1/r} (a^u)^{θ₁} (b^v)^{θ₂}` when `u/r + u θ₁ = 1` and `v/r + v θ₂ = 1`. -/
theorem young_split {u v r θ₁ θ₂ : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (hr : 0 ≤ 1 / r)
    (h₁ : 0 ≤ θ₁) (h₂ : 0 ≤ θ₂) (e₁ : u * (1 / r) + u * θ₁ = 1)
    (e₂ : v * (1 / r) + v * θ₂ = 1) (a b : ℝ≥0∞) :
    (a ^ u * b ^ v) ^ (1 / r) * (a ^ u) ^ θ₁ * (b ^ v) ^ θ₂ = a * b := by
  rw [ENNReal.mul_rpow_of_nonneg _ _ hr, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul,
    ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
  calc a ^ (u * (1 / r)) * b ^ (v * (1 / r)) * a ^ (u * θ₁) * b ^ (v * θ₂)
      = (a ^ (u * (1 / r)) * a ^ (u * θ₁)) * (b ^ (v * (1 / r)) * b ^ (v * θ₂)) := by ring
    _ = a ^ (u * (1 / r) + u * θ₁) * b ^ (v * (1 / r) + v * θ₂) := by
        rw [ENNReal.rpow_add_of_nonneg _ _ (mul_nonneg hu hr) (mul_nonneg hu h₁),
          ENNReal.rpow_add_of_nonneg _ _ (mul_nonneg hv hr) (mul_nonneg hv h₂)]
    _ = a * b := by rw [e₁, e₂, ENNReal.rpow_one, ENNReal.rpow_one]

/-- **The three-exponent Young inequality** (`integrated_cameron_mean.tex` lines 288-292 at
revision edf7085f (book 1.1.3)), in `ℝ≥0∞` form on `ℝ`: for `u, v, r ≥ 1` with
`1/u + 1/v = 1 + 1/r` and measurable `f, h ≥ 0`,
`(∫ (∫ f(y) h(x-y) dy)^r dx)^{1/r} ≤ (∫ f^u)^{1/u} (∫ h^v)^{1/v}`.
Route (as in the TeX): Hölder with the three exponents `r`, `(1/u-1/r)^{-1}`, `(1/v-1/r)^{-1}`
(`ENNReal.lintegral_prod_norm_pow_le`, which allows the degenerate exponent `0`), then Tonelli
and translation invariance. -/
theorem young : YoungTarget := by
  intro u v r hu hv hr huvr f h hf hh
  have hu0 : 0 < u := by linarith
  have hv0 : 0 < v := by linarith
  have hr0 : 0 < r := by linarith
  set θ₁ := 1 / u - 1 / r with hθ₁
  set θ₂ := 1 / v - 1 / r with hθ₂
  have hiv : 1 / v ≤ 1 := by rw [div_le_one hv0]; exact hv
  have hiu : 1 / u ≤ 1 := by rw [div_le_one hu0]; exact hu
  have h₁ : 0 ≤ θ₁ := by rw [hθ₁]; linarith
  have h₂ : 0 ≤ θ₂ := by rw [hθ₂]; linarith
  have hrr : 0 ≤ 1 / r := by positivity
  have e₁ : u * (1 / r) + u * θ₁ = 1 := by rw [hθ₁]; field_simp; ring
  have e₂ : v * (1 / r) + v * θ₂ = 1 := by rw [hθ₂]; field_simp; ring
  set A := ∫⁻ x, f x ^ u
  set B := ∫⁻ x, h x ^ v
  -- the pointwise Hölder step
  have hpt : ∀ x : ℝ, ∫⁻ y, f y * h (x - y) ≤
      (∫⁻ y, f y ^ u * h (x - y) ^ v) ^ (1 / r) * A ^ θ₁ * B ^ θ₂ := by
    intro x
    have hhx : Measurable fun y : ℝ => h (x - y) := hh.comp (measurable_const.sub measurable_id)
    let F : Fin 3 → ℝ → ℝ≥0∞ := ![fun y => f y ^ u * h (x - y) ^ v, fun y => f y ^ u,
      fun y => h (x - y) ^ v]
    let P : Fin 3 → ℝ := ![1 / r, θ₁, θ₂]
    have hF : ∀ i ∈ (Finset.univ : Finset (Fin 3)), AEMeasurable (F i) volume := by
      intro i _
      fin_cases i
      · exact ((hf.pow_const u).mul (hhx.pow_const v)).aemeasurable
      · exact (hf.pow_const u).aemeasurable
      · exact (hhx.pow_const v).aemeasurable
    have hP : ∑ i ∈ (Finset.univ : Finset (Fin 3)), P i = 1 := by
      simp only [Fin.sum_univ_three, P, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, hθ₁, hθ₂]
      linarith
    have hP0 : ∀ i ∈ (Finset.univ : Finset (Fin 3)), 0 ≤ P i := by
      intro i _
      fin_cases i
      · exact hrr
      · exact h₁
      · exact h₂
    have hH := ENNReal.lintegral_prod_norm_pow_le (μ := volume) Finset.univ hF hP hP0
    simp only [Fin.prod_univ_three, F, P, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at hH
    have hB : ∫⁻ y, h (x - y) ^ v = B := lintegral_sub_left_eq_self (fun y => h y ^ v) x
    rw [hB] at hH
    refine le_of_eq_of_le (lintegral_congr fun y => ?_) hH
    exact (young_split hu0.le hv0.le hrr h₁ h₂ e₁ e₂ (f y) (h (x - y))).symm
  -- integrate the `r`-th power
  have hmeas : Measurable (Function.uncurry fun x y : ℝ => f y ^ u * h (x - y) ^ v) :=
    (hf.comp measurable_snd).pow_const u |>.mul
      ((hh.comp (measurable_fst.sub measurable_snd)).pow_const v)
  have hTon : ∫⁻ x, ∫⁻ y, f y ^ u * h (x - y) ^ v = A * B := by
    rw [lintegral_lintegral_swap hmeas.aemeasurable]
    calc ∫⁻ y, ∫⁻ x, f y ^ u * h (x - y) ^ v = ∫⁻ y, f y ^ u * B := by
          refine lintegral_congr fun y => ?_
          rw [lintegral_const_mul _ (show Measurable fun x => h (x - y) ^ v from
            (hh.comp (measurable_sub_const y)).pow_const v)]
          rw [lintegral_sub_right_eq_self (fun x => h x ^ v) y]
      _ = A * B := lintegral_mul_const _ (hf.pow_const u)
  have hpow : ∫⁻ x, (∫⁻ y, f y * h (x - y)) ^ r ≤ A * B * (A ^ θ₁ * B ^ θ₂) ^ r := by
    calc ∫⁻ x, (∫⁻ y, f y * h (x - y)) ^ r
        ≤ ∫⁻ x, (∫⁻ y, f y ^ u * h (x - y) ^ v) * (A ^ θ₁ * B ^ θ₂) ^ r := by
          refine lintegral_mono fun x => ?_
          calc (∫⁻ y, f y * h (x - y)) ^ r
              ≤ ((∫⁻ y, f y ^ u * h (x - y) ^ v) ^ (1 / r) * A ^ θ₁ * B ^ θ₂) ^ r :=
                ENNReal.rpow_le_rpow (hpt x) hr0.le
            _ = (∫⁻ y, f y ^ u * h (x - y) ^ v) * (A ^ θ₁ * B ^ θ₂) ^ r := by
                rw [mul_assoc, ENNReal.mul_rpow_of_nonneg _ _ hr0.le, ← ENNReal.rpow_mul,
                  one_div_mul_cancel hr0.ne', ENNReal.rpow_one]
      _ = A * B * (A ^ θ₁ * B ^ θ₂) ^ r := by
          rw [lintegral_mul_const _ (show Measurable fun x => ∫⁻ y, f y ^ u * h (x - y) ^ v from
            hmeas.lintegral_prod_right'), hTon]
  calc (∫⁻ x, (∫⁻ y, f y * h (x - y)) ^ r) ^ (1 / r)
      ≤ (A * B * (A ^ θ₁ * B ^ θ₂) ^ r) ^ (1 / r) := ENNReal.rpow_le_rpow hpow hrr
    _ = A ^ (1 / r) * B ^ (1 / r) * (A ^ θ₁ * B ^ θ₂) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ hrr, ENNReal.mul_rpow_of_nonneg _ _ hrr,
          ← ENNReal.rpow_mul, mul_one_div_cancel hr0.ne', ENNReal.rpow_one]
    _ = A ^ (1 / r + θ₁) * B ^ (1 / r + θ₂) := by
        rw [ENNReal.rpow_add_of_nonneg _ _ hrr h₁, ENNReal.rpow_add_of_nonneg _ _ hrr h₂]
        ring
    _ = A ^ (1 / u) * B ^ (1 / v) := by
        congr 2
        · rw [hθ₁]; ring
        · rw [hθ₂]; ring

/-! ### The absolute kernel form bound -/

/-- The truncated kernel `K_a(v) = |v|^{-a} 1_{|v| ≤ 1}` (`integrated_cameron_mean.tex`
line 282 at revision edf7085f (book 1.1.3)), in `ℝ≥0∞`. -/
def kaE (a : ℝ) (v : ℝ) : ℝ≥0∞ := (Icc (-1 : ℝ) 1).indicator (fun v => ENNReal.ofReal (kern a v)) v

/-- Auxiliary: `K_a` is measurable. -/
theorem measurable_kaE (a : ℝ) : Measurable (kaE a) :=
  (ENNReal.measurable_ofReal.comp (measurable_kern a)).indicator measurableSet_Icc

/-- Auxiliary: `‖K_a‖_{L^{r/2}(ℝ)} = KaNorm a r` for `0 < r`, `a r / 2 < 1`. -/
theorem lintegral_kaE_rpow {a r : ℝ} (hr : 0 < r) (har : a * r / 2 < 1) :
    (∫⁻ v, kaE a v ^ (r / 2)) ^ (1 / (r / 2)) = ENNReal.ofReal (KaNorm a r) := by
  have hr2 : 0 < r / 2 := by positivity
  have hint : IntegrableOn (fun v : ℝ => |v| ^ (-(a * r / 2))) (Icc (-1 : ℝ) 1) := by
    have := TimeSchur.intervalIntegrable_abs_rpow (r := -(a * r / 2)) (by linarith) (-1) 1
    exact (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num)).mp this
  have hpt : ∀ v, kaE a v ^ (r / 2) =
      (Icc (-1 : ℝ) 1).indicator (fun v => ENNReal.ofReal (|v| ^ (-(a * r / 2)))) v := by
    intro v
    by_cases hv : v ∈ Icc (-1 : ℝ) 1
    · simp only [kaE, indicator_of_mem hv, kern]
      rw [ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _) hr2.le,
        ← Real.rpow_mul (abs_nonneg _)]
      congr 2
      ring
    · simp only [kaE, indicator_of_notMem hv]
      exact ENNReal.zero_rpow_of_pos hr2
  simp_rw [hpt]
  rw [lintegral_indicator measurableSet_Icc,
    ← ofReal_integral_eq_lintegral_ofReal hint
      (ae_of_all _ fun v => Real.rpow_nonneg (abs_nonneg _) _),
    ENNReal.ofReal_rpow_of_nonneg (setIntegral_nonneg measurableSet_Icc fun v _ =>
      Real.rpow_nonneg (abs_nonneg _) _) (by positivity)]
  unfold KaNorm
  congr 2
  field_simp

/-- **`‖g‖²_{H_t} ≤ ‖K_a‖_{r/2} ‖g‖²_{r'}` with absolute values** (`integrated_cameron_mean.tex`
lines 283-287 at revision edf7085f (book 1.1.3)): for `2 < r < 2/a` and
`F` a.e.-strongly measurable on `I`,
`∫∫_{I²} |s-t|^{-a} |F(s)| |F(t)| ≤ ‖K_a‖_{L^{r/2}} ‖F‖²_{L^{r'}(I)}`, `r' = r/(r-1)`.
Route: zero extension `g = 1_I |F|`; on `I²`, `|s-t|^{-a} = K_a(s-t)`; Hölder (`r'`, `r`) and
`young` (`u = r'`, `v = r/2`, `1/r' + 2/r = 1 + 1/r`). -/
theorem kform_abs (p : TParams) : KformAbsTarget p := by
  intro r hr2 hra F hF
  set a := p.a
  have ha0 : 0 ≤ a := p.ha0.le
  have hr0 : 0 < r := by linarith
  have hr1 : 0 < r - 1 := by linarith
  set r' := r / (r - 1) with hr'
  have hr'0 : 0 < r' := div_pos hr0 hr1
  have har : a * r / 2 < 1 := by
    have := (lt_div_iff₀ p.ha0).mp hra
    linarith
  set F₀ := hF.mk F
  have hF₀ : StronglyMeasurable F₀ := hF.stronglyMeasurable_mk
  have hFF : F =ᵐ[timeMeasure] F₀ := hF.ae_eq_mk
  set I : Set ℝ := Ioo (0 : ℝ) 1
  set g : ℝ → ℝ≥0∞ := I.indicator fun t => ‖F₀ t‖ₑ with hg
  have hgm : Measurable g := hF₀.measurable.enorm.indicator measurableSet_Ioo
  set C : ℝ → ℝ≥0∞ := fun s => ∫⁻ t, g t * kaE a (s - t) with hC
  have hCm : Measurable C := by
    have : Measurable (Function.uncurry fun s t : ℝ => g t * kaE a (s - t)) :=
      (hgm.comp measurable_snd).mul ((measurable_kaE a).comp (measurable_fst.sub measurable_snd))
    exact this.lintegral_prod_right'
  -- Step 1: the form is bounded by `∫ g C`
  have hstep1 : ∫⁻ s, ∫⁻ t, ENNReal.ofReal (kern a (s - t)) * ‖F s‖ₑ * ‖F t‖ₑ ∂timeMeasure
      ∂timeMeasure ≤ ∫⁻ s, g s * C s := by
    have hinner : ∀ s ∈ I, ∫⁻ t, ENNReal.ofReal (kern a (s - t)) * ‖F s‖ₑ * ‖F t‖ₑ ∂timeMeasure =
        ‖F s‖ₑ * C s := by
      intro s hs
      calc ∫⁻ t, ENNReal.ofReal (kern a (s - t)) * ‖F s‖ₑ * ‖F t‖ₑ ∂timeMeasure
          = ∫⁻ t in I, ‖F s‖ₑ * (‖F₀ t‖ₑ * kaE a (s - t)) := by
            refine lintegral_congr_ae ?_
            filter_upwards [hFF, ae_restrict_mem measurableSet_Ioo] with t ht htI
            have hst : s - t ∈ Icc (-1 : ℝ) 1 := by
              constructor <;> linarith [hs.1, hs.2, htI.1, htI.2]
            rw [ht, kaE, indicator_of_mem hst]
            ring
        _ = ‖F s‖ₑ * ∫⁻ t in I, ‖F₀ t‖ₑ * kaE a (s - t) := by
            rw [lintegral_const_mul]
            exact hF₀.measurable.enorm.mul ((measurable_kaE a).comp
              (measurable_const.sub measurable_id))
        _ = ‖F s‖ₑ * C s := by
            congr 1
            rw [hC, ← lintegral_indicator measurableSet_Ioo]
            refine lintegral_congr fun t => ?_
            simp only [hg]
            by_cases ht : t ∈ I
            · rw [indicator_of_mem ht, indicator_of_mem ht]
            · rw [indicator_of_notMem ht, indicator_of_notMem ht, zero_mul]
    calc ∫⁻ s, ∫⁻ t, ENNReal.ofReal (kern a (s - t)) * ‖F s‖ₑ * ‖F t‖ₑ ∂timeMeasure ∂timeMeasure
        = ∫⁻ s in I, g s * C s := by
          refine lintegral_congr_ae ?_
          filter_upwards [hFF, ae_restrict_mem measurableSet_Ioo] with s hs hsI
          rw [hinner s hsI, hs, hg, indicator_of_mem hsI]
      _ ≤ ∫⁻ s, g s * C s := setLIntegral_le_lintegral _ _
  -- Step 2: Hölder with `r'` and `r`
  have hHC : r'.HolderConjugate r := by
    rw [Real.holderConjugate_iff]
    refine ⟨?_, ?_⟩
    · rw [hr', lt_div_iff₀ hr1]; linarith
    · rw [hr']; field_simp; ring
  have hstep2 := ENNReal.lintegral_mul_le_Lp_mul_Lq volume hHC hgm.aemeasurable hCm.aemeasurable
  -- Step 3: Young
  have hY := young r' (r / 2) r (by rw [hr', le_div_iff₀ hr1]; linarith) (by linarith) (by linarith)
    (by rw [hr']; field_simp; ring) g (kaE a) hgm (measurable_kaE a)
  rw [lintegral_kaE_rpow hr0 har] at hY
  -- Step 4: the `L^{r'}` norm of `F`
  have hnorm : eLpNorm F (ENNReal.ofReal r') timeMeasure = (∫⁻ x, g x ^ r') ^ (1 / r') := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simpa using hr'0) ENNReal.ofReal_ne_top hF,
      ENNReal.toReal_ofReal hr'0.le]
    congr 1
    rw [lintegral_congr_ae (hFF.mono fun t ht => by rw [ht]),
      ← lintegral_indicator measurableSet_Ioo]
    refine lintegral_congr fun t => ?_
    by_cases ht : t ∈ Ioo (0 : ℝ) 1
    · rw [indicator_of_mem ht, hg, indicator_of_mem ht]
    · rw [indicator_of_notMem ht, hg, indicator_of_notMem ht, ENNReal.zero_rpow_of_pos hr'0]
  have hC' : ∫⁻ s, g s * C s = ∫⁻ s, (g * C) s := rfl
  calc _ ≤ ∫⁻ s, g s * C s := hstep1
    _ ≤ (∫⁻ x, g x ^ r') ^ (1 / r') * (∫⁻ x, C x ^ r) ^ (1 / r) := hC' ▸ hstep2
    _ ≤ (∫⁻ x, g x ^ r') ^ (1 / r') *
          ((∫⁻ x, g x ^ r') ^ (1 / r') * ENNReal.ofReal (KaNorm a r)) := by
        gcongr
    _ = ENNReal.ofReal (KaNorm a r) * eLpNorm F (ENNReal.ofReal (r / (r - 1))) timeMeasure ^ 2 := by
        rw [← hr', hnorm]; ring

end StratonovichHAMSecondMoment.CameronTemporal
