module

/-
Copyright 2026 Le Chen. SPDX-License-Identifier: Apache-2.0

Wave L17, item L17-A: `L:translated-covariance-CS` (the translated covariance Cauchy-Schwarz
inequality), whole, against the frozen interface `PairingInterface` (L17-0).

TeX anchors: main file `notes/notes_stratonovich_ham_second_moment.tex` at revision edf7085f
(book 1.1.3): the setup "Covariance pairings of translated kernels" (`E:translated-covariance-form`)
lines 1156-1185; `L:translated-covariance-CS` statement lines 1186-1197
(`E:translated-covariance-CS` 1191-1193); proof lines 1199-1297 (Step 1 1207-1237, Step 2
1239-1255, Step 3 1257-1268, Step 4 1272-1296).

Results (the frozen targets of item A):
* `translated_covariance_cs_capped : TranslatedCSCappedTarget d` (the capped form, "This proves
  the capped form", TeX 1266-1268);
* `translated_covariance_cs : TranslatedCSTarget d` (the lemma, TeX 1186-1197).

**Route (decision 4 of wave L17, approved by Le on 2026-11-20).**  The TeX (Steps 1-2) forms the
Bochner integral `F_L(f) = ∫ f(t,x) Φ_L(t,x)` of the norm-continuous feature map
`Φ_L(t,x)(λ,ξ,r) = h_λ(t,r) e^{iξ·x}` in `L²((0,L] × ℝ^d × ℝ, ν μ dr)` and applies Cauchy-Schwarz
there.  This module proves the same feature-space inequality with scalar integrals only, with no
vector-valued integral and no norm-continuity argument:
1. the feature identity `∫ h_λ(t,r) h_λ(s,r) dr = e^{-λ|t-s|}` (TeX 1214-1220), `lintegral_feat_mul`,
   so `κ_L(t-s) = ∫_{(0,L]} ∫ h_λ(t,r) h_λ(s,r) dr ν(dλ)` (`kappaCap_eq`);
2. Tonelli in `[0,∞]` moves the temporal feature variables `(λ, r)` outside:
   `Q_L(f,h) = ∫_{(0,L]} ∫ B(f h_λ(·,r), h h_λ(·,r)) dr ν(dλ)` with the spatial pairing
   `B(Φ,Ψ) = ∫∫ Φ(t,x) Ψ(s,y) γ(x-y)` (`QLF_eq_lintegral_Bsp`);
3. the spatial factor by scalar Fubini: for `Φ, Ψ ∈ L¹`, with
   `Φ̂(ξ) = ∫ Φ(t,x) e^{iξ·x}` (a scalar Bochner integral), `B(Φ,Ψ) = Re ∫ Φ̂ conj Ψ̂ dμ`
   (`integral_fhat_mul_conj`, using that the transform of `μ` is `γ`, real and nonnegative),
   hence `B(Φ,Ψ) ≤ ∫ |Φ̂| |Ψ̂| dμ ≤ B(Φ,Φ)^{1/2} B(Ψ,Ψ)^{1/2}` (`Bsp_le`);
4. Hölder (`p = q = 2`) in `[0,∞]` in `r` and then in `λ` (`lintegral_sqrt_mul_le`).
Steps 2-4 together are Cauchy-Schwarz in `L²(ν|_(0,L] ⊗ μ ⊗ dr)` for the feature transforms
`F_L f(λ,ξ,r) = ∫ f(t,x) h_λ(t,r) e^{iξ·x}`, written as iterated scalar integrals.
5. Common-translation invariance of `Q_L` (TeX 1257-1265) is the translation invariance of
   Lebesgue measure on `ℝ × ℝ^d` (`QL_transl`); it needs no integrability.
6. Cap limit (TeX 1286-1296): `Q` is the supremum over integer caps (interface reading), and
   the capped inequality is bounded by the uncapped self pairings termwise.

Differences from the TeX's proof, all in the direction of fewer steps: the truncations `G_{i,M}`
and the monotone limit in `M` of Step 4 (TeX 1274-1284) are not needed, since the Tonelli
argument in `[0,∞]` applies directly to unbounded nonnegative `L¹` kernels; the absolute bound
`m_L ‖f‖₁ ‖h‖₁` is not needed, since no step divides by or subtracts a pairing.  The hypothesis
`ν((0,L]) < ∞` is used only to make `ν|_(0,L]` s-finite for Tonelli; `0 < L` and `N_C(G_i) < ∞`
are not used (a cap `L ≤ 0` gives `Q_L = 0`).  Zero norms and zero measures are included: no
division by a norm occurs (TeX 1293-1295).  Every statement is in `ℝ≥0∞` with the TeX's
finiteness hypotheses `N_0(G_i) < ∞` explicit.
-/
public import Mathlib
public import StratonovichHAMSecondMoment.PairingInterface

@[expose] public section

noncomputable section

set_option autoImplicit false

open MeasureTheory Set Function
open scoped ENNReal Real ComplexConjugate

namespace StratonovichHAMSecondMoment.PairingTranslatedCS

open HomogHypothesis (Rd)
open PairingInterface

variable {d : ℕ}

/-! ### Step 1: the temporal feature `h_λ(t,r) = √(2λ) e^{-λ(t-r)} 1_{r ≤ t}` (TeX 1211-1220) -/

/-- The temporal feature `h_λ(t,r) = √(2λ) e^{-λ(t-r)} 1_{r ≤ t}` at `w = (λ, t, r)`
(TeX 1211-1213), in `ℝ≥0∞`. -/
def feat (w : ℝ × ℝ × ℝ) : ℝ≥0∞ :=
  if w.2.2 ≤ w.2.1 then
    ENNReal.ofReal (Real.sqrt (2 * w.1) * Real.exp (-(w.1 * (w.2.1 - w.2.2))))
  else 0

@[fun_prop]
theorem measurable_feat : Measurable feat := by
  unfold feat
  refine Measurable.ite (measurableSet_le (by fun_prop) (by fun_prop)) ?_ measurable_const
  fun_prop

/-- `h_λ(t,r) ≤ √(2λ)` for `λ ≥ 0`. -/
theorem feat_le {l : ℝ} (hl : 0 ≤ l) (t r : ℝ) :
    feat (l, t, r) ≤ ENNReal.ofReal (Real.sqrt (2 * l)) := by
  unfold feat
  split_ifs with h
  · apply ENNReal.ofReal_le_ofReal
    have h1 : Real.exp (-(l * (t - r))) ≤ 1 :=
      Real.exp_le_one_iff.2 (by have : 0 ≤ t - r := sub_nonneg.2 h; nlinarith)
    calc Real.sqrt (2 * l) * Real.exp (-(l * (t - r))) ≤ Real.sqrt (2 * l) * 1 :=
          mul_le_mul_of_nonneg_left h1 (Real.sqrt_nonneg _)
      _ = Real.sqrt (2 * l) := mul_one _
  · exact zero_le

/-- The product of two features at the same `(λ, r)`. -/
theorem feat_mul_feat {l : ℝ} (hl : 0 < l) (t s r : ℝ) :
    feat (l, t, r) * feat (l, s, r) =
      (Iic (min t s)).indicator
        (fun r => ENNReal.ofReal (2 * l * Real.exp (-(l * (t + s))) * Real.exp (2 * l * r))) r := by
  unfold feat
  simp only [indicator, mem_Iic, le_min_iff]
  by_cases h1 : r ≤ t <;> by_cases h2 : r ≤ s <;> simp only [h1, h2, ↓reduceIte,
    and_true, and_false, mul_zero, zero_mul]
  rw [← ENNReal.ofReal_mul (by positivity)]
  congr 1
  have hsq : Real.sqrt (2 * l) * Real.sqrt (2 * l) = 2 * l := Real.mul_self_sqrt (by positivity)
  calc Real.sqrt (2 * l) * Real.exp (-(l * (t - r))) * (Real.sqrt (2 * l) * Real.exp (-(l * (s - r))))
      = (Real.sqrt (2 * l) * Real.sqrt (2 * l)) *
          (Real.exp (-(l * (t - r))) * Real.exp (-(l * (s - r)))) := by ring
    _ = 2 * l * Real.exp (-(l * (t + s))) * Real.exp (2 * l * r) := by
      rw [hsq, ← Real.exp_add, mul_assoc (2 * l) (Real.exp _) (Real.exp _), ← Real.exp_add]
      congr 2
      ring

/-- **Feature identity** (TeX 1214-1220): `∫ h_λ(t,r) h_λ(s,r) dr = e^{-λ|t-s|}` for `λ > 0`. -/
theorem lintegral_feat_mul {l : ℝ} (hl : 0 < l) (t s : ℝ) :
    ∫⁻ r, feat (l, t, r) * feat (l, s, r) = ENNReal.ofReal (Real.exp (-(l * |t - s|))) := by
  simp_rw [feat_mul_feat hl t s]
  rw [lintegral_indicator measurableSet_Iic]
  have hint : IntegrableOn
      (fun r => 2 * l * Real.exp (-(l * (t + s))) * Real.exp (2 * l * r)) (Iic (min t s)) :=
    (integrableOn_exp_mul_Iic (by positivity) _).const_mul _
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall fun r => by positivity)]
  congr 1
  rw [integral_const_mul, integral_exp_mul_Iic (by positivity)]
  have h2l : (2 * l) ≠ 0 := by positivity
  have e : 2 * l * Real.exp (-(l * (t + s))) * (Real.exp (2 * l * min t s) / (2 * l)) =
      Real.exp (-(l * (t + s))) * Real.exp (2 * l * min t s) := by
    field_simp
  rw [e, ← Real.exp_add]
  congr 1
  rcases le_total t s with h | h
  · rw [min_eq_left h, abs_of_nonpos (by linarith)]; ring
  · rw [min_eq_right h, abs_of_nonneg (by linarith)]; ring

/-- `κ_L(t-s) = ∫_{(0,L]} ∫ h_λ(t,r) h_λ(s,r) dr ν(dλ)` (TeX 1162-1163 with 1214-1220). -/
theorem kappaCap_eq (ν : Measure ℝ) (L t s : ℝ) :
    kappaCap ν L (t - s) = ∫⁻ l in Ioc 0 L, (∫⁻ r, feat (l, t, r) * feat (l, s, r)) ∂ν := by
  unfold kappaCap
  refine lintegral_congr_ae ?_
  filter_upwards [ae_restrict_mem (μ := ν) (measurableSet_Ioc (a := (0 : ℝ)) (b := L))] with l hl
  rw [lintegral_feat_mul hl.1]

/-! ### Hölder with `p = q = 2` in `[0,∞]` -/

/-- `∫ f^{1/2} g^{1/2} ≤ (∫ f)^{1/2} (∫ g)^{1/2}` in `[0,∞]` (no integrability needed). -/
theorem lintegral_sqrt_mul_le {β : Type*} [MeasurableSpace β] (m : Measure β) {f g : β → ℝ≥0∞}
    (hf : AEMeasurable f m) (hg : AEMeasurable g m) :
    ∫⁻ b, f b ^ (2⁻¹ : ℝ) * g b ^ (2⁻¹ : ℝ) ∂m ≤
      (∫⁻ b, f b ∂m) ^ (2⁻¹ : ℝ) * (∫⁻ b, g b ∂m) ^ (2⁻¹ : ℝ) := by
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq m Real.HolderConjugate.two_two
    (hf.pow_const (2⁻¹ : ℝ)) (hg.pow_const (2⁻¹ : ℝ))
  have e : ∀ x : ℝ≥0∞, (x ^ (2⁻¹ : ℝ)) ^ (2 : ℝ) = x := fun x =>
    ENNReal.rpow_inv_rpow two_ne_zero x
  simp only [Pi.mul_apply, e, one_div] at h
  exact h

/-! ### The spatial covariance -/

@[fun_prop]
theorem measurable_gammaOf (μ : Measure (Rd d)) [SFinite μ] : Measurable (gammaOf μ) := by
  have hc : StronglyMeasurable fun z : Rd d × Rd d => Real.cos (inner ℝ z.2 z.1) :=
    (by fun_prop : Continuous fun z : Rd d × Rd d => Real.cos (inner ℝ z.2 z.1)).stronglyMeasurable
  exact ENNReal.measurable_ofReal.comp (hc.integral_prod_right' (ν := μ)).measurable

theorem gammaOf_ne_top (μ : Measure (Rd d)) (x : Rd d) : gammaOf μ x ≠ ∞ :=
  ENNReal.ofReal_ne_top

/-- `0 ≤ γ(x) ≤ μ(ℝ^d)` (TeX 1159-1160), the upper half. -/
theorem toReal_gammaOf_le (μ : Measure (Rd d)) [IsFiniteMeasure μ] (x : Rd d) :
    (gammaOf μ x).toReal ≤ μ.real univ := by
  unfold gammaOf
  rw [ENNReal.toReal_ofReal']
  refine max_le ?_ measureReal_nonneg
  have h := norm_integral_le_of_norm_le_const (μ := μ)
    (f := fun ξ => Real.cos (inner ℝ ξ x)) (C := 1)
    (Filter.Eventually.of_forall fun ξ => by
      simpa [Real.norm_eq_abs] using Real.abs_cos_le_one (inner ℝ ξ x))
  rw [one_mul, Real.norm_eq_abs] at h
  exact (le_abs_self _).trans h

/-! ### Step 3 of the route: the spatial Cauchy-Schwarz by scalar Fubini -/

/-- The spatial pairing `B(Φ,Ψ) = ∫∫ Φ(t,x) Ψ(s,y) γ(x - y)` on `ℝ × ℝ^d`. -/
def Bsp (μ : Measure (Rd d)) (Φ Ψ : ℝ × Rd d → ℝ≥0∞) : ℝ≥0∞ :=
  ∫⁻ p, ∫⁻ q, Φ p * Ψ q * gammaOf μ (p.2 - q.2)

/-- The spatial Fourier transform `Φ̂(ξ) = ∫ φ(t,x) e^{iξ·x} dt dx` (a scalar Bochner
integral). -/
def fhat (φ : ℝ × Rd d → ℝ) (ξ : Rd d) : ℂ :=
  ∫ p, (φ p : ℂ) * Complex.exp (Complex.I * (inner ℝ ξ p.2 : ℝ))

theorem measurable_fhat {φ : ℝ × Rd d → ℝ} (hφ : Measurable φ) : Measurable (fhat φ) := by
  have h : StronglyMeasurable fun w : Rd d × (ℝ × Rd d) =>
      (φ w.2 : ℂ) * Complex.exp (Complex.I * (inner ℝ w.1 w.2.2 : ℝ)) :=
    (by fun_prop : Measurable fun w : Rd d × (ℝ × Rd d) =>
      (φ w.2 : ℂ) * Complex.exp (Complex.I * (inner ℝ w.1 w.2.2 : ℝ))).stronglyMeasurable
  exact (h.integral_prod_right' (ν := (volume : Measure (ℝ × Rd d)))).measurable

theorem norm_fhat_le {φ : ℝ × Rd d → ℝ} (ξ : Rd d) : ‖fhat φ ξ‖ ≤ ∫ p, ‖φ p‖ := by
  unfold fhat
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  congr 1
  funext p
  rw [norm_mul, mul_comm Complex.I, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real]

/-- Changing `Φ, Ψ` on null sets does not change `B`. -/
theorem Bsp_congr (μ : Measure (Rd d)) {Φ Φ' Ψ Ψ' : ℝ × Rd d → ℝ≥0∞}
    (hΦ : Φ =ᵐ[volume] Φ') (hΨ : Ψ =ᵐ[volume] Ψ') : Bsp μ Φ Ψ = Bsp μ Φ' Ψ' := by
  unfold Bsp
  refine lintegral_congr_ae (hΦ.mono fun p hp => ?_)
  refine lintegral_congr_ae (hΨ.mono fun q hq => ?_)
  simp only [hp, hq]

/-- **Scalar Fubini** (decision 4): `∫ Φ̂ conj Ψ̂ dμ = ∫∫ φ(p) ψ(q) γ(x_p - x_q)`, using that the
transform of `μ` is `γ` (`SpecNonneg`, `gammaOf_spec`). -/
theorem integral_fhat_mul_conj {μ : Measure (Rd d)} [IsFiniteMeasure μ] (hμ : SpecNonneg μ)
    {φ ψ : ℝ × Rd d → ℝ} (hφm : Measurable φ) (hψm : Measurable ψ) (hφ : Integrable φ)
    (hψ : Integrable ψ) :
    ∫ ξ, fhat φ ξ * conj (fhat ψ ξ) ∂μ =
      ((∫ z : (ℝ × Rd d) × (ℝ × Rd d),
        φ z.1 * ψ z.2 * (gammaOf μ (z.1.2 - z.2.2)).toReal ∂(volume.prod volume) : ℝ) : ℂ) := by
  set k : Rd d → (ℝ × Rd d) × (ℝ × Rd d) → ℂ := fun ξ z =>
    (φ z.1 : ℂ) * Complex.exp (Complex.I * (inner ℝ ξ z.1.2 : ℝ)) *
      conj ((ψ z.2 : ℂ) * Complex.exp (Complex.I * (inner ℝ ξ z.2.2 : ℝ))) with hk
  have h1 : ∀ ξ, fhat φ ξ * conj (fhat ψ ξ) = ∫ z, k ξ z ∂(volume.prod volume) := by
    intro ξ
    rw [fhat, fhat, ← integral_conj, ← integral_prod_mul]
  have hk' : ∀ ξ z, k ξ z = ((φ z.1 * ψ z.2 : ℝ) : ℂ) *
      Complex.exp (Complex.I * (inner ℝ ξ (z.1.2 - z.2.2) : ℝ)) := by
    intro ξ z
    simp only [hk, map_mul, Complex.conj_ofReal, ← Complex.exp_conj, Complex.conj_I,
      inner_sub_right, Complex.ofReal_sub, Complex.ofReal_mul]
    calc (φ z.1 : ℂ) * Complex.exp (Complex.I * (inner ℝ ξ z.1.2 : ℝ)) *
          ((ψ z.2 : ℂ) * Complex.exp (-Complex.I * (inner ℝ ξ z.2.2 : ℝ)))
        = (φ z.1 : ℂ) * (ψ z.2 : ℂ) * (Complex.exp (Complex.I * (inner ℝ ξ z.1.2 : ℝ)) *
            Complex.exp (-Complex.I * (inner ℝ ξ z.2.2 : ℝ))) := by ring
      _ = _ := by
        rw [← Complex.exp_add]
        congr 2
        ring
  have hku : uncurry k = fun w : Rd d × ((ℝ × Rd d) × (ℝ × Rd d)) =>
      ((φ w.2.1 * ψ w.2.2 : ℝ) : ℂ) *
        Complex.exp (Complex.I * (inner ℝ w.1 (w.2.1.2 - w.2.2.2) : ℝ)) := by
    funext w
    exact hk' w.1 w.2
  have hint : Integrable (uncurry k) (μ.prod (volume.prod volume)) := by
    have hb : Integrable (fun w : Rd d × ((ℝ × Rd d) × (ℝ × Rd d)) =>
        (1 : ℝ) * (‖φ w.2.1‖ * ‖ψ w.2.2‖)) (μ.prod (volume.prod volume)) :=
      (integrable_const (1 : ℝ)).mul_prod (hφ.norm.mul_prod hψ.norm)
    refine hb.mono' ?_ (Filter.Eventually.of_forall fun w => ?_)
    · rw [hku]
      exact (by fun_prop : Measurable fun w : Rd d × ((ℝ × Rd d) × (ℝ × Rd d)) =>
        ((φ w.2.1 * ψ w.2.2 : ℝ) : ℂ) *
          Complex.exp (Complex.I * (inner ℝ w.1 (w.2.1.2 - w.2.2.2) : ℝ))).aestronglyMeasurable
    · rw [hku]
      simp only
      rw [norm_mul, mul_comm Complex.I, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
        norm_mul, one_mul]
  simp_rw [h1]
  rw [integral_integral_swap hint]
  have h2 : ∀ z : (ℝ × Rd d) × (ℝ × Rd d), ∫ ξ, k ξ z ∂μ =
      ((φ z.1 * ψ z.2 * (gammaOf μ (z.1.2 - z.2.2)).toReal : ℝ) : ℂ) := by
    intro z
    simp_rw [hk']
    rw [integral_const_mul, ← gammaOf_spec hμ]
    push_cast
    ring
  simp_rw [h2]
  exact integral_ofReal

/-- For nonnegative integrable `φ, ψ`, `B(φ,ψ)` is the real double integral. -/
theorem Bsp_ofReal {μ : Measure (Rd d)} [IsFiniteMeasure μ] {φ ψ : ℝ × Rd d → ℝ}
    (hφm : Measurable φ) (hψm : Measurable ψ) (hφ : Integrable φ) (hψ : Integrable ψ)
    (hφ0 : ∀ p, 0 ≤ φ p) (hψ0 : ∀ p, 0 ≤ ψ p) :
    Bsp μ (fun p => ENNReal.ofReal (φ p)) (fun q => ENNReal.ofReal (ψ q)) =
      ENNReal.ofReal (∫ z : (ℝ × Rd d) × (ℝ × Rd d),
        φ z.1 * ψ z.2 * (gammaOf μ (z.1.2 - z.2.2)).toReal ∂(volume.prod volume)) := by
  have hint : Integrable (fun z : (ℝ × Rd d) × (ℝ × Rd d) =>
      φ z.1 * ψ z.2 * (gammaOf μ (z.1.2 - z.2.2)).toReal) (volume.prod volume) := by
    refine ((hφ.mul_prod hψ).mul_const (μ.real univ)).mono'
      (by fun_prop : Measurable fun z : (ℝ × Rd d) × (ℝ × Rd d) =>
        φ z.1 * ψ z.2 * (gammaOf μ (z.1.2 - z.2.2)).toReal).aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => ?_)
    have h0 : 0 ≤ φ z.1 * ψ z.2 := mul_nonneg (hφ0 _) (hψ0 _)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg h0 ENNReal.toReal_nonneg)]
    exact mul_le_mul_of_nonneg_left (toReal_gammaOf_le μ _) h0
  rw [ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall fun z => mul_nonneg (mul_nonneg (hφ0 _) (hψ0 _))
        ENNReal.toReal_nonneg),
    lintegral_prod _ (by fun_prop : Measurable fun z : (ℝ × Rd d) × (ℝ × Rd d) =>
      ENNReal.ofReal (φ z.1 * ψ z.2 * (gammaOf μ (z.1.2 - z.2.2)).toReal)).aemeasurable]
  unfold Bsp
  refine lintegral_congr fun p => lintegral_congr fun q => ?_
  rw [ENNReal.ofReal_mul (mul_nonneg (hφ0 _) (hψ0 _)), ENNReal.ofReal_mul (hφ0 _),
    ENNReal.ofReal_toReal (gammaOf_ne_top μ _)]

/-- `B(φ,φ) = ∫ |φ̂|² dμ`. -/
theorem Bsp_self {μ : Measure (Rd d)} [IsFiniteMeasure μ] (hμ : SpecNonneg μ)
    {φ : ℝ × Rd d → ℝ} (hφm : Measurable φ) (hφ : Integrable φ) (hφ0 : ∀ p, 0 ≤ φ p) :
    Bsp μ (fun p => ENNReal.ofReal (φ p)) (fun q => ENNReal.ofReal (φ q)) =
      ∫⁻ ξ, ‖fhat φ ξ‖ₑ ^ (2 : ℝ) ∂μ := by
  rw [Bsp_ofReal hφm hφm hφ hφ hφ0 hφ0]
  have hc := integral_fhat_mul_conj hμ hφm hφm hφ hφ
  have hpt : ∀ ξ, fhat φ ξ * conj (fhat φ ξ) = ((‖fhat φ ξ‖ ^ 2 : ℝ) : ℂ) := fun ξ => by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_pow]
  have hc2 : ∫ ξ, fhat φ ξ * conj (fhat φ ξ) ∂μ = ∫ ξ, ((‖fhat φ ξ‖ ^ 2 : ℝ) : ℂ) ∂μ :=
    integral_congr_ae (Filter.Eventually.of_forall hpt)
  rw [hc2] at hc
  have hc' : ∫ ξ, ‖fhat φ ξ‖ ^ 2 ∂μ = ∫ z : (ℝ × Rd d) × (ℝ × Rd d),
      φ z.1 * φ z.2 * (gammaOf μ (z.1.2 - z.2.2)).toReal ∂(volume.prod volume) := by
    have h3 : ((∫ ξ, ‖fhat φ ξ‖ ^ 2 ∂μ : ℝ) : ℂ) = ((∫ z : (ℝ × Rd d) × (ℝ × Rd d),
        φ z.1 * φ z.2 * (gammaOf μ (z.1.2 - z.2.2)).toReal ∂(volume.prod volume) : ℝ) : ℂ) := by
      rw [← hc]
      exact integral_ofReal.symm
    exact_mod_cast h3
  rw [← hc']
  have hb : Integrable (fun ξ => ‖fhat φ ξ‖ ^ 2) μ := by
    refine Integrable.of_bound (C := (∫ p, ‖φ p‖) ^ 2)
      ((measurable_fhat hφm).norm.pow_const 2).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ξ => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_fhat_le ξ) 2
  rw [ofReal_integral_eq_lintegral_ofReal hb (Filter.Eventually.of_forall fun ξ => by positivity)]
  refine lintegral_congr fun ξ => ?_
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm, ENNReal.rpow_two]

/-- **Spatial Cauchy-Schwarz** for nonnegative integrable real functions. -/
theorem Bsp_le_real {μ : Measure (Rd d)} [IsFiniteMeasure μ] (hμ : SpecNonneg μ)
    {φ ψ : ℝ × Rd d → ℝ} (hφm : Measurable φ) (hψm : Measurable ψ) (hφ : Integrable φ)
    (hψ : Integrable ψ) (hφ0 : ∀ p, 0 ≤ φ p) (hψ0 : ∀ p, 0 ≤ ψ p) :
    Bsp μ (fun p => ENNReal.ofReal (φ p)) (fun q => ENNReal.ofReal (ψ q)) ≤
      Bsp μ (fun p => ENNReal.ofReal (φ p)) (fun q => ENNReal.ofReal (φ q)) ^ (2⁻¹ : ℝ) *
        Bsp μ (fun p => ENNReal.ofReal (ψ p)) (fun q => ENNReal.ofReal (ψ q)) ^ (2⁻¹ : ℝ) := by
  rw [Bsp_self hμ hφm hφ hφ0, Bsp_self hμ hψm hψ hψ0, Bsp_ofReal hφm hψm hφ hψ hφ0 hψ0]
  have hc := integral_fhat_mul_conj hμ hφm hψm hφ hψ
  calc ENNReal.ofReal (∫ z : (ℝ × Rd d) × (ℝ × Rd d),
        φ z.1 * ψ z.2 * (gammaOf μ (z.1.2 - z.2.2)).toReal ∂(volume.prod volume))
      ≤ ‖∫ ξ, fhat φ ξ * conj (fhat ψ ξ) ∂μ‖ₑ := by
        rw [hc, ← ofReal_norm, Complex.norm_real, Real.norm_eq_abs]
        exact ENNReal.ofReal_le_ofReal (le_abs_self _)
    _ ≤ ∫⁻ ξ, ‖fhat φ ξ * conj (fhat ψ ξ)‖ₑ ∂μ := enorm_integral_le_lintegral_enorm _
    _ = ∫⁻ ξ, ‖fhat φ ξ‖ₑ * ‖fhat ψ ξ‖ₑ ∂μ := by
        refine lintegral_congr fun ξ => ?_
        rw [enorm_mul, RCLike.enorm_conj]
    _ ≤ (∫⁻ ξ, ‖fhat φ ξ‖ₑ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) *
          (∫⁻ ξ, ‖fhat ψ ξ‖ₑ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) :=
        ENNReal.lintegral_mul_le_Lp_mul_Lq μ Real.HolderConjugate.two_two
          (measurable_fhat hφm).enorm.aemeasurable (measurable_fhat hψm).enorm.aemeasurable
    _ = _ := by rw [one_div]

/-- **Spatial Cauchy-Schwarz** (route step 3): for measurable `Φ, Ψ ≥ 0` with finite integrals,
`B(Φ,Ψ) ≤ B(Φ,Φ)^{1/2} B(Ψ,Ψ)^{1/2}`. -/
theorem Bsp_le {μ : Measure (Rd d)} [IsFiniteMeasure μ] (hμ : SpecNonneg μ)
    {Φ Ψ : ℝ × Rd d → ℝ≥0∞} (hΦ : Measurable Φ) (hΨ : Measurable Ψ) (hΦ1 : ∫⁻ p, Φ p ≠ ∞)
    (hΨ1 : ∫⁻ p, Ψ p ≠ ∞) :
    Bsp μ Φ Ψ ≤ Bsp μ Φ Φ ^ (2⁻¹ : ℝ) * Bsp μ Ψ Ψ ^ (2⁻¹ : ℝ) := by
  have hΦe : (fun p => ENNReal.ofReal (Φ p).toReal) =ᵐ[volume] Φ :=
    ofReal_toReal_ae_eq (ae_lt_top hΦ hΦ1)
  have hΨe : (fun p => ENNReal.ofReal (Ψ p).toReal) =ᵐ[volume] Ψ :=
    ofReal_toReal_ae_eq (ae_lt_top hΨ hΨ1)
  rw [← Bsp_congr μ hΦe hΨe, ← Bsp_congr μ hΦe hΦe, ← Bsp_congr μ hΨe hΨe]
  exact Bsp_le_real hμ hΦ.ennreal_toReal hΨ.ennreal_toReal
    (integrable_toReal_of_lintegral_ne_top hΦ.aemeasurable hΦ1)
    (integrable_toReal_of_lintegral_ne_top hΨ.aemeasurable hΨ1)
    (fun _ => ENNReal.toReal_nonneg) (fun _ => ENNReal.toReal_nonneg)

/-! ### Route step 2: Tonelli moves the temporal features `(λ, r)` outside -/

/-- `Q_L` for functions on `ℝ × ℝ^d`: `QL ν μ L f h = QLF ν μ L (uncurry f) (uncurry h)`. -/
def QLF (ν : Measure ℝ) (μ : Measure (Rd d)) (L : ℝ) (F G : ℝ × Rd d → ℝ≥0∞) : ℝ≥0∞ :=
  ∫⁻ p, ∫⁻ q, F p * G q * kappaCap ν L (p.1 - q.1) * gammaOf μ (p.2 - q.2)

theorem QL_eq_QLF (ν : Measure ℝ) (μ : Measure (Rd d)) (L : ℝ) (f h : Kernel d) :
    QL ν μ L f h = QLF ν μ L (uncurry f) (uncurry h) := rfl

/-- `Φ_{λ,r}(t,x) = F(t,x) h_λ(t,r)`. -/
def featMul (F : ℝ × Rd d → ℝ≥0∞) (l r : ℝ) (p : ℝ × Rd d) : ℝ≥0∞ := F p * feat (l, p.1, r)

/-- The integrand `F(p) h_λ(t_p,r) G(q) h_λ(t_q,r) γ(x_p - x_q)`. -/
def Xint (μ : Measure (Rd d)) (F G : ℝ × Rd d → ℝ≥0∞) (p q : ℝ × Rd d) (l r : ℝ) : ℝ≥0∞ :=
  F p * feat (l, p.1, r) * (G q * feat (l, q.1, r)) * gammaOf μ (p.2 - q.2)

theorem measurable_Xint (μ : Measure (Rd d)) [SFinite μ] {F G : ℝ × Rd d → ℝ≥0∞}
    (hF : Measurable F) (hG : Measurable G) :
    Measurable fun w : ((ℝ × Rd d) × (ℝ × Rd d)) × (ℝ × ℝ) =>
      Xint μ F G w.1.1 w.1.2 w.2.1 w.2.2 := by
  unfold Xint
  fun_prop

/-- `(λ, r) ↦ B(Φ_{λ,r}, Ψ_{λ,r})` is measurable. -/
theorem measurable_Bsp_featMul (μ : Measure (Rd d)) [SFinite μ] {F G : ℝ × Rd d → ℝ≥0∞}
    (hF : Measurable F) (hG : Measurable G) :
    Measurable fun w : ℝ × ℝ => Bsp μ (featMul F w.1 w.2) (featMul G w.1 w.2) := by
  have hX := measurable_Xint μ hF hG
  exact Measurable.lintegral_prod_right'
    (f := fun z : (ℝ × ℝ) × (ℝ × Rd d) => ∫⁻ q, Xint μ F G z.2 q z.1.1 z.1.2)
    (Measurable.lintegral_prod_right'
      (f := fun z : ((ℝ × ℝ) × (ℝ × Rd d)) × (ℝ × Rd d) => Xint μ F G z.1.2 z.2 z.1.1.1 z.1.1.2)
      (hX.comp (f := fun z : ((ℝ × ℝ) × (ℝ × Rd d)) × (ℝ × Rd d) =>
        ((z.1.2, z.2), (z.1.1.1, z.1.1.2))) (by fun_prop)))

/-- **Route step 2** (Tonelli in `[0,∞]`): `Q_L(F,G) = ∫_{(0,L]} ∫ B(F h_λ(·,r), G h_λ(·,r)) dr
ν(dλ)`. -/
theorem QLF_eq_lintegral_Bsp (ν : Measure ℝ) (μ : Measure (Rd d)) [SFinite μ] (L : ℝ)
    [SFinite (ν.restrict (Ioc 0 L))] {F G : ℝ × Rd d → ℝ≥0∞} (hF : Measurable F)
    (hG : Measurable G) :
    QLF ν μ L F G = ∫⁻ l in Ioc 0 L, (∫⁻ r, Bsp μ (featMul F l r) (featMul G l r)) ∂ν := by
  have hX := measurable_Xint μ hF hG
  have step1 : ∀ p q : ℝ × Rd d,
      F p * G q * kappaCap ν L (p.1 - q.1) * gammaOf μ (p.2 - q.2) =
        ∫⁻ l in Ioc 0 L, (∫⁻ r, Xint μ F G p q l r) ∂ν := by
    intro p q
    have hm1 : Measurable fun l => ∫⁻ r, feat (l, p.1, r) * feat (l, q.1, r) :=
      Measurable.lintegral_prod_right'
        (f := fun z : ℝ × ℝ => feat (z.1, p.1, z.2) * feat (z.1, q.1, z.2)) (by fun_prop)
    calc F p * G q * kappaCap ν L (p.1 - q.1) * gammaOf μ (p.2 - q.2)
        = (F p * G q * gammaOf μ (p.2 - q.2)) *
            ∫⁻ l in Ioc 0 L, (∫⁻ r, feat (l, p.1, r) * feat (l, q.1, r)) ∂ν := by
          rw [kappaCap_eq]; ring
      _ = ∫⁻ l in Ioc 0 L, (F p * G q * gammaOf μ (p.2 - q.2)) *
            (∫⁻ r, feat (l, p.1, r) * feat (l, q.1, r)) ∂ν :=
          (lintegral_const_mul _ hm1).symm
      _ = _ := by
          refine lintegral_congr fun l => ?_
          rw [← lintegral_const_mul _ (by fun_prop)]
          refine lintegral_congr fun r => ?_
          unfold Xint
          ring
  unfold QLF
  have e1 : ∀ p : ℝ × Rd d,
      ∫⁻ q, F p * G q * kappaCap ν L (p.1 - q.1) * gammaOf μ (p.2 - q.2) =
        ∫⁻ l in Ioc 0 L, (∫⁻ r, ∫⁻ q, Xint μ F G p q l r) ∂ν := by
    intro p
    rw [lintegral_congr (step1 p)]
    rw [lintegral_lintegral_swap (Measurable.lintegral_prod_right'
      (f := fun z : ((ℝ × Rd d) × ℝ) × ℝ => Xint μ F G p z.1.1 z.1.2 z.2)
      (hX.comp (f := fun z : ((ℝ × Rd d) × ℝ) × ℝ => ((p, z.1.1), (z.1.2, z.2)))
        (by fun_prop))).aemeasurable]
    refine lintegral_congr fun l => ?_
    exact lintegral_lintegral_swap
      (hX.comp (f := fun z : (ℝ × Rd d) × ℝ => ((p, z.1), (l, z.2))) (by fun_prop)).aemeasurable
  rw [lintegral_congr e1]
  rw [lintegral_lintegral_swap (Measurable.lintegral_prod_right'
    (f := fun z : ((ℝ × Rd d) × ℝ) × ℝ => ∫⁻ q, Xint μ F G z.1.1 q z.1.2 z.2)
    (Measurable.lintegral_prod_right'
      (f := fun z : (((ℝ × Rd d) × ℝ) × ℝ) × (ℝ × Rd d) => Xint μ F G z.1.1.1 z.2 z.1.1.2 z.1.2)
      (hX.comp (f := fun z : (((ℝ × Rd d) × ℝ) × ℝ) × (ℝ × Rd d) =>
        ((z.1.1.1, z.2), (z.1.1.2, z.1.2))) (by fun_prop)))).aemeasurable]
  refine lintegral_congr fun l => ?_
  rw [lintegral_lintegral_swap (Measurable.lintegral_prod_right'
    (f := fun z : ((ℝ × Rd d) × ℝ) × (ℝ × Rd d) => Xint μ F G z.1.1 z.2 l z.1.2)
    (hX.comp (f := fun z : ((ℝ × Rd d) × ℝ) × (ℝ × Rd d) => ((z.1.1, z.2), (l, z.1.2)))
      (by fun_prop))).aemeasurable]
  rfl

/-! ### Route step 4: the capped Cauchy-Schwarz inequality -/

theorem lintegral_featMul_ne_top {F : ℝ × Rd d → ℝ≥0∞} (hF1 : ∫⁻ p, F p ≠ ∞) {l : ℝ}
    (hl : 0 ≤ l) (r : ℝ) : ∫⁻ p, featMul F l r p ≠ ∞ := by
  refine ne_top_of_le_ne_top (b := ∫⁻ p, F p * ENNReal.ofReal (Real.sqrt (2 * l))) ?_ ?_
  · rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
    exact ENNReal.mul_ne_top hF1 ENNReal.ofReal_ne_top
  · exact lintegral_mono fun p => mul_le_mul' le_rfl (feat_le hl p.1 r)

/-- **Capped Cauchy-Schwarz** (TeX Steps 1-2, 1207-1255, by the scalar route):
`Q_L(F,G) ≤ Q_L(F,F)^{1/2} Q_L(G,G)^{1/2}` for measurable `F, G ≥ 0` in `L¹`. -/
theorem QLF_cs (ν : Measure ℝ) {μ : Measure (Rd d)} [IsFiniteMeasure μ] (hμ : SpecNonneg μ)
    (L : ℝ) [SFinite (ν.restrict (Ioc 0 L))] {F G : ℝ × Rd d → ℝ≥0∞} (hF : Measurable F)
    (hG : Measurable G) (hF1 : ∫⁻ p, F p ≠ ∞) (hG1 : ∫⁻ p, G p ≠ ∞) :
    QLF ν μ L F G ≤ QLF ν μ L F F ^ (2⁻¹ : ℝ) * QLF ν μ L G G ^ (2⁻¹ : ℝ) := by
  rw [QLF_eq_lintegral_Bsp ν μ L hF hG, QLF_eq_lintegral_Bsp ν μ L hF hF,
    QLF_eq_lintegral_Bsp ν μ L hG hG]
  have hmF := measurable_Bsp_featMul μ hF hF
  have hmG := measurable_Bsp_featMul μ hG hG
  have hmF' : ∀ l, Measurable fun r => Bsp μ (featMul F l r) (featMul F l r) := fun l =>
    hmF.comp (f := fun r : ℝ => (l, r)) (by fun_prop)
  have hmG' : ∀ l, Measurable fun r => Bsp μ (featMul G l r) (featMul G l r) := fun l =>
    hmG.comp (f := fun r : ℝ => (l, r)) (by fun_prop)
  have hfm : ∀ {H : ℝ × Rd d → ℝ≥0∞}, Measurable H → ∀ l r, Measurable (featMul H l r) :=
    fun {H} hH l r => by unfold featMul; fun_prop
  calc ∫⁻ l in Ioc 0 L, (∫⁻ r, Bsp μ (featMul F l r) (featMul G l r)) ∂ν
      ≤ ∫⁻ l in Ioc 0 L, (∫⁻ r, Bsp μ (featMul F l r) (featMul F l r) ^ (2⁻¹ : ℝ) *
            Bsp μ (featMul G l r) (featMul G l r) ^ (2⁻¹ : ℝ)) ∂ν := by
        refine setLIntegral_mono' measurableSet_Ioc fun l hl => lintegral_mono fun r => ?_
        exact Bsp_le hμ (hfm hF l r) (hfm hG l r) (lintegral_featMul_ne_top hF1 hl.1.le r)
          (lintegral_featMul_ne_top hG1 hl.1.le r)
    _ ≤ ∫⁻ l in Ioc 0 L, (∫⁻ r, Bsp μ (featMul F l r) (featMul F l r)) ^ (2⁻¹ : ℝ) *
            (∫⁻ r, Bsp μ (featMul G l r) (featMul G l r)) ^ (2⁻¹ : ℝ) ∂ν :=
        lintegral_mono fun l =>
          lintegral_sqrt_mul_le volume (hmF' l).aemeasurable (hmG' l).aemeasurable
    _ ≤ _ :=
        lintegral_sqrt_mul_le _ hmF.lintegral_prod_right'.aemeasurable
          hmG.lintegral_prod_right'.aemeasurable

/-! ### Route step 5: common-translation invariance (TeX 1257-1265) -/

/-- Lebesgue measure on `ℝ × ℝ^d` is translation invariant. -/
instance instIsAddRightInvariantVolumeProd : (volume : Measure (ℝ × Rd d)).IsAddRightInvariant := by
  rw [Measure.volume_eq_prod]
  infer_instance

/-- `Q_L(T_{A,a} f, T_{A,a} h) = Q_L(f,h)` (TeX 1260-1263): both differences are unchanged and
Lebesgue measure on `ℝ × ℝ^d` is translation invariant.  No integrability is needed. -/
theorem QL_transl (ν : Measure ℝ) (μ : Measure (Rd d)) (L A : ℝ) (a : Rd d) (f h : Kernel d) :
    QL ν μ L (transl A a f) (transl A a h) = QL ν μ L f h := by
  unfold QL transl
  set c : ℝ × Rd d := (A, a)
  set Φ : ℝ × Rd d → ℝ × Rd d → ℝ≥0∞ := fun p q =>
    f p.1 p.2 * h q.1 q.2 * kappaCap ν L (p.1 - q.1) * gammaOf μ (p.2 - q.2) with hΦ
  have key : ∀ p q : ℝ × Rd d,
      f (p.1 - A) (p.2 - a) * h (q.1 - A) (q.2 - a) * kappaCap ν L (p.1 - q.1) *
        gammaOf μ (p.2 - q.2) = Φ (p - c) (q - c) := by
    intro p q
    simp only [hΦ, c, Prod.fst_sub, Prod.snd_sub, sub_sub_sub_cancel_right]
  simp_rw [key]
  have h1 : ∀ p, ∫⁻ q, Φ (p - c) (q - c) = ∫⁻ q, Φ (p - c) q := fun p =>
    lintegral_sub_right_eq_self (fun q => Φ (p - c) q) c
  rw [lintegral_congr h1]
  exact lintegral_sub_right_eq_self (fun p => ∫⁻ q, Φ p q) c

theorem measurable_zeroExt {G : Kernel d} (hG : Measurable (uncurry G)) :
    Measurable (uncurry (zeroExt G)) := by
  have e : uncurry (zeroExt G) = fun p : ℝ × Rd d => if 0 < p.1 then uncurry G p else 0 := by
    funext p
    simp only [uncurry, zeroExt, indicator, mem_Ioi]
  rw [e]
  exact Measurable.ite (measurableSet_lt measurable_const measurable_fst) hG measurable_const

theorem measurable_transl {f : Kernel d} (hf : Measurable (uncurry f)) (A : ℝ) (a : Rd d) :
    Measurable (uncurry (transl A a f)) :=
  hf.comp (f := fun p : ℝ × Rd d => p - (A, a)) (by fun_prop)

/-- `∫ T_{A,a} G⁰ = N_0(G)`. -/
theorem lintegral_transl_zeroExt {G : Kernel d} (hG : Measurable (uncurry G)) (A : ℝ)
    (a : Rd d) : ∫⁻ p : ℝ × Rd d, uncurry (transl A a (zeroExt G)) p = N0 G := by
  have h1 : ∫⁻ p : ℝ × Rd d, uncurry (transl A a (zeroExt G)) p =
      ∫⁻ p : ℝ × Rd d, uncurry (zeroExt G) p :=
    lintegral_sub_right_eq_self (fun p : ℝ × Rd d => uncurry (zeroExt G) p) (A, a)
  rw [h1, N0, ← lintegral_indicator measurableSet_Ioi, Measure.volume_eq_prod,
    lintegral_prod _ (measurable_zeroExt hG).aemeasurable]
  refine lintegral_congr fun t => ?_
  simp only [uncurry, zeroExt, indicator, mem_Ioi]
  split_ifs <;> simp

/-! ### The targets -/

/-- **`L:translated-covariance-CS`, capped form** (TeX 1186-1197 at the finite cap; proof Steps
1-3, TeX 1207-1268, "This proves the capped form" 1266-1268), by the scalar route of the module
docstring.  `0 < L` is not used. -/
theorem translated_covariance_cs_capped (d : ℕ) : TranslatedCSCappedTarget d := by
  intro ν μ L _hL hνL hμ hspec G₁ G₂ hG₁ hG₂ hN₁ hN₂ A B x y
  have := hμ
  have : IsFiniteMeasure (ν.restrict (Ioc 0 L)) := isFiniteMeasure_restrict.2 hνL.ne
  refine ⟨?_, QL_transl ν μ L A x _ _⟩
  have h := QLF_cs ν hspec L (measurable_transl (measurable_zeroExt hG₁) A x)
    (measurable_transl (measurable_zeroExt hG₂) B y)
    (by rw [lintegral_transl_zeroExt hG₁]; exact hN₁.ne)
    (by rw [lintegral_transl_zeroExt hG₂]; exact hN₂.ne)
  rw [← QL_eq_QLF, ← QL_eq_QLF, ← QL_eq_QLF, QL_transl, QL_transl] at h
  exact h

/-- **`L:translated-covariance-CS`** (TeX 1186-1197; proof 1199-1297, by the scalar route of the
module docstring): for `ν` finite on bounded caps, `μ` finite with real nonnegative transform,
and measurable `G₁, G₂ ≥ 0` with `N_0(G_i) < ∞`,
`Q(T_{A,x} G₁⁰, T_{B,y} G₂⁰) ≤ N_C(G₁) N_C(G₂)` and `Q(T_{A,x} G_i⁰, T_{A,x} G_i⁰) = N_C(G_i)²`.
The hypotheses `N_C(G_i) < ∞` are not used. -/
theorem translated_covariance_cs (d : ℕ) : TranslatedCSTarget d := by
  intro ν μ hν hμ hspec G₁ G₂ hG₁ hG₂ hN₁ hN₂ _ _ A B x y
  have := hμ
  have hfin : ∀ L : ℕ, IsFiniteMeasure (ν.restrict (Ioc 0 (L : ℝ))) := by
    intro L
    rcases Nat.eq_zero_or_pos L with rfl | hL
    · simp only [Nat.cast_zero, Ioc_self, Measure.restrict_empty]
      infer_instance
    · exact isFiniteMeasure_restrict.2 (hν L (by exact_mod_cast hL)).ne
  have hQT : ∀ (C : ℝ) (c : Rd d) (G : Kernel d),
      Q ν μ (transl C c (zeroExt G)) (transl C c (zeroExt G)) = Q ν μ (zeroExt G) (zeroExt G) := by
    intro C c G
    unfold Q
    simp_rw [QL_transl]
  refine ⟨?_, by rw [hQT, NC_sq], by rw [hQT, NC_sq]⟩
  unfold NC
  refine iSup_le fun L => ?_
  have := hfin L
  have h := QLF_cs ν hspec (L : ℝ) (measurable_transl (measurable_zeroExt hG₁) A x)
    (measurable_transl (measurable_zeroExt hG₂) B y)
    (by rw [lintegral_transl_zeroExt hG₁]; exact hN₁.ne)
    (by rw [lintegral_transl_zeroExt hG₂]; exact hN₂.ne)
  rw [← QL_eq_QLF, ← QL_eq_QLF, ← QL_eq_QLF, QL_transl, QL_transl] at h
  refine h.trans (mul_le_mul' ?_ ?_)
  · exact ENNReal.rpow_le_rpow (le_iSup (fun L : ℕ => QL ν μ (L : ℝ) (zeroExt G₁) (zeroExt G₁)) L)
      (by norm_num)
  · exact ENNReal.rpow_le_rpow (le_iSup (fun L : ℕ => QL ν μ (L : ℝ) (zeroExt G₂) (zeroExt G₂)) L)
      (by norm_num)

end StratonovichHAMSecondMoment.PairingTranslatedCS
