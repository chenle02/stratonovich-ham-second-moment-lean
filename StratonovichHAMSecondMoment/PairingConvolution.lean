module

/-
Copyright 2026 Le Chen. SPDX-License-Identifier: Apache-2.0

Wave L17, item L17-B, part 1: Step 1 of `L:pairing-product-envelope`, the convolution bounds
`E:pairing-convolution-norms` (claim and proof TeX lines 1522-1535, display 1524-1530, in
Step 1 1510-1537 at revision edf7085f (book 1.1.3)).

For nonnegative measurable kernels `G, H` and their one-sided space-time convolution
`F = G * H` (`PairingInterface.conv`):
* `N0_conv`: `N_0(F) = N_0(G) N_0(H)` ("positivity", Tonelli on the group `ℝ × ℝ^d`; no
  finiteness is needed);
* `N1_conv_le`: `N_{1,e}(F) ≤ N_0(G) N_{1,e}(H)`, from the Laplace-Fourier product
  `𝓛F = 𝓛G · 𝓛H` (`lapFour_conv`, a Bochner Fubini on `(ℝ × ℝ^d)²`) and
  `|𝓛G(λ,ξ)| ≤ N_0(G)` for `λ ≥ 0` (`enorm_lapFour_le`);
* `NC_conv_le`, hence `N2_conv_le`: `N_{2,e}(F) ≤ N_0(G) N_{2,e}(H)`.

Route for the second norm (differs in form from the TeX, same mathematics).  The TeX
zero-extends `H`, writes `G * H` as the Bochner integral of the translates
`T_{s,y} H^0` against `G(s,y)` in the covariance Hilbert space, and applies Minkowski.  Here
the same estimate is proved at every finite cap `L` without a Hilbert space: the pairing
`Q_L(F^0, F^0)` is expanded by Tonelli (all integrands are nonnegative) into
`∫∫ G^0(q) G^0(q') Q_L(T_q H^0, T_{q'} H^0) dq dq'`, each translated pairing is bounded by
`Q_L(H^0,H^0)` with the coefficient-one Cauchy-Schwarz inequality and the common-translation
invariance of `L:translated-covariance-CS` at the cap (item A's capped form, taken as the
HYPOTHESIS `TranslatedCSCappedTarget d`), and the cap limit is the supremum over integer caps.
This is Minkowski for the square of the norm, written as the bilinear expansion.

`convolution_norms` takes `TranslatedCSCappedTarget d` (the capped form) instead of
`TranslatedCSTarget d`, as the interface allows (INTERFACE.md §2, item B).  It uses neither
`a < 1` nor the finite cap `∃ L, E.A ⊆ Ioc 0 L` of the target (both are hypotheses of the frozen
`ConvolutionNormsTarget`, kept unchanged); `0 < a` is used for `ν_e((0,L]) < ∞`.
-/
public import Mathlib
public import StratonovichHAMSecondMoment.PairingInterface

@[expose] public section

noncomputable section

set_option autoImplicit false

open MeasureTheory Set Function
open scoped ENNReal Real

namespace StratonovichHAMSecondMoment.PairingConvolution

open HomogHypothesis (Rd)
open PairingInterface

variable {d : ℕ}

/-! ### The space-time group `ℝ × ℝ^d` -/

/-- Lebesgue measure on `ℝ × ℝ^d` is invariant under negation (each factor is). -/
instance instIsNegInvariantVolumeProdRd :
    ((volume : Measure ℝ).prod (volume : Measure (Rd d))).IsNegInvariant := by
  constructor
  show Measure.map Neg.neg _ = _
  have h : (Neg.neg : ℝ × Rd d → ℝ × Rd d) = Prod.map Neg.neg Neg.neg := rfl
  rw [h, ← Measure.map_prod_map _ _ measurable_neg measurable_neg, Measure.map_neg_eq_self,
    Measure.map_neg_eq_self]

/-- The parameter measure `ν_e` is s-finite. -/
instance instSFiniteNuE (a : ℝ) (A : Set ℝ) : SFinite (nuE a A) := by
  unfold nuE; infer_instance

theorem volume_prodRd :
    (volume : Measure (ℝ × Rd d)) = (volume : Measure ℝ).prod (volume : Measure (Rd d)) :=
  Measure.volume_eq_prod ℝ (Rd d)

theorem lintegral_zeroExt_sub_right (H : Kernel d) (q : ℝ × Rd d) :
    ∫⁻ p : ℝ × Rd d, zeroExt H (p - q).1 (p - q).2 = ∫⁻ p : ℝ × Rd d, zeroExt H p.1 p.2 := by
  rw [volume_prodRd]
  exact lintegral_sub_right_eq_self (fun r : ℝ × Rd d => zeroExt H r.1 r.2) q

theorem lintegral_zeroExt_sub_left (H : Kernel d) (p : ℝ × Rd d) :
    ∫⁻ q : ℝ × Rd d, zeroExt H (p - q).1 (p - q).2 = ∫⁻ q : ℝ × Rd d, zeroExt H q.1 q.2 := by
  rw [volume_prodRd]
  exact lintegral_sub_left_eq_self (fun r : ℝ × Rd d => zeroExt H r.1 r.2) p

theorem integral_sub_right_prodRd (f : ℝ × Rd d → ℂ) (q : ℝ × Rd d) :
    ∫ p : ℝ × Rd d, f (p - q) = ∫ p : ℝ × Rd d, f p := by
  rw [volume_prodRd]
  exact integral_sub_right_eq_self f q

/-! ### Zero extension and the one-sided convolution -/

theorem zeroExt_of_pos (G : Kernel d) {t : ℝ} (ht : 0 < t) (x : Rd d) : zeroExt G t x = G t x := by
  simp [zeroExt, ht]

theorem zeroExt_of_nonpos (G : Kernel d) {t : ℝ} (ht : t ≤ 0) (x : Rd d) : zeroExt G t x = 0 := by
  simp [zeroExt, not_lt.2 ht]

theorem uncurry_zeroExt (G : Kernel d) :
    uncurry (zeroExt G) = {p : ℝ × Rd d | 0 < p.1}.indicator (uncurry G) := by
  ext ⟨t, x⟩
  by_cases ht : 0 < t
  · simp [zeroExt_of_pos G ht, ht]
  · simp [zeroExt_of_nonpos G (not_lt.1 ht), ht]

theorem measurable_zeroExt {G : Kernel d} (hG : Measurable (uncurry G)) :
    Measurable (uncurry (zeroExt G)) := by
  rw [uncurry_zeroExt]
  exact hG.indicator (measurableSet_lt measurable_const measurable_fst)

/-- `N_0(F) = ∫ F^0` over `ℝ × ℝ^d`. -/
theorem N0_eq_lintegral {F : Kernel d} (hF : Measurable (uncurry F)) :
    N0 F = ∫⁻ p : ℝ × Rd d, zeroExt F p.1 p.2 := by
  rw [volume_prodRd, lintegral_prod (fun p : ℝ × Rd d => zeroExt F p.1 p.2)
    (measurable_zeroExt hF).aemeasurable, N0, ← lintegral_indicator measurableSet_Ioi]
  refine lintegral_congr fun t => ?_
  by_cases ht : 0 < t
  · simp only [Set.indicator_of_mem (show t ∈ Ioi (0 : ℝ) from ht), zeroExt_of_pos F ht]
  · simp only [Set.indicator_of_notMem (show t ∉ Ioi (0 : ℝ) from ht),
      zeroExt_of_nonpos F (not_lt.1 ht), lintegral_zero]

theorem conv_of_nonpos (G H : Kernel d) {t : ℝ} (ht : t ≤ 0) (x : Rd d) : conv G H t x = 0 := by
  simp [conv, Ioo_eq_empty (not_lt.2 ht)]

/-- The convolution vanishes at nonpositive times: it is its own zero extension. -/
theorem zeroExt_conv (G H : Kernel d) : zeroExt (conv G H) = conv G H := by
  funext t x
  by_cases ht : 0 < t
  · exact zeroExt_of_pos _ ht x
  · rw [zeroExt_of_nonpos _ (not_lt.1 ht), conv_of_nonpos _ _ (not_lt.1 ht)]

/-- The one-sided convolution is the group convolution of the zero extensions. -/
theorem conv_eq_lintegral {G H : Kernel d} (hG : Measurable (uncurry G))
    (hH : Measurable (uncurry H)) (p : ℝ × Rd d) :
    conv G H p.1 p.2 =
      ∫⁻ q : ℝ × Rd d, zeroExt G q.1 q.2 * zeroExt H (p - q).1 (p - q).2 := by
  have hm : Measurable fun q : ℝ × Rd d => zeroExt G q.1 q.2 * zeroExt H (p - q).1 (p - q).2 :=
    (measurable_zeroExt hG).mul ((measurable_zeroExt hH).comp (measurable_const.sub measurable_id))
  rw [volume_prodRd, lintegral_prod _ hm.aemeasurable, conv,
    ← lintegral_indicator measurableSet_Ioo]
  refine lintegral_congr fun s => ?_
  by_cases hs : s ∈ Ioo 0 p.1
  · rw [Set.indicator_of_mem hs]
    refine lintegral_congr fun y => ?_
    simp only [Prod.fst_sub, Prod.snd_sub]
    rw [zeroExt_of_pos G hs.1, zeroExt_of_pos H (sub_pos.2 hs.2)]
  · rw [Set.indicator_of_notMem hs]
    simp only [mem_Ioo, not_and_or, not_lt] at hs
    symm
    refine lintegral_eq_zero_iff' ?_ |>.2 ?_
    · exact (hm.comp (measurable_const.prodMk measurable_id)).aemeasurable
    · refine Filter.Eventually.of_forall fun y => ?_
      simp only [Prod.fst_sub, Prod.snd_sub, Pi.zero_apply]
      rcases hs with h | h
      · rw [zeroExt_of_nonpos G h, zero_mul]
      · rw [zeroExt_of_nonpos H (by linarith), mul_zero]

/-- `∫∫ G^0(q) H^0(p - q) dq dp = N_0(G) N_0(H)`. -/
theorem lintegral_conv_kernel {G H : Kernel d} (hG : Measurable (uncurry G))
    (hH : Measurable (uncurry H)) :
    ∫⁻ p : ℝ × Rd d, ∫⁻ q : ℝ × Rd d, zeroExt G q.1 q.2 * zeroExt H (p - q).1 (p - q).2 =
      N0 G * N0 H := by
  have hm : Measurable (uncurry fun p q : ℝ × Rd d =>
      zeroExt G q.1 q.2 * zeroExt H (p - q).1 (p - q).2) :=
    ((measurable_zeroExt hG).comp measurable_snd).mul
      ((measurable_zeroExt hH).comp (measurable_fst.sub measurable_snd))
  rw [lintegral_lintegral_swap hm.aemeasurable]
  have hG' : Measurable fun q : ℝ × Rd d => zeroExt G q.1 q.2 := measurable_zeroExt hG
  have inner : ∀ q : ℝ × Rd d,
      ∫⁻ p : ℝ × Rd d, zeroExt G q.1 q.2 * zeroExt H (p - q).1 (p - q).2 =
        zeroExt G q.1 q.2 * N0 H := fun q => by
    have hq : Measurable fun p : ℝ × Rd d => zeroExt H (p - q).1 (p - q).2 :=
      (measurable_zeroExt hH).comp (measurable_id.sub measurable_const)
    rw [lintegral_const_mul _ hq, lintegral_zeroExt_sub_right H q, ← N0_eq_lintegral hH]
  rw [lintegral_congr inner, lintegral_mul_const _ hG', ← N0_eq_lintegral hG]

/-- **`N_0(G * H) = N_0(G) N_0(H)`** (TeX 1526, "positivity"). -/
theorem N0_conv {G H : Kernel d} (hG : Measurable (uncurry G)) (hH : Measurable (uncurry H)) :
    N0 (conv G H) = N0 G * N0 H := by
  rw [N0_eq_lintegral (measurable_conv hG hH), zeroExt_conv]
  rw [lintegral_congr fun p => conv_eq_lintegral hG hH p]
  exact lintegral_conv_kernel hG hH

/-! ### The Laplace-Fourier transform -/

/-- The character `e^{-λt + iξ·x}`. -/
def ch (l : ℝ) (ξ : Rd d) (p : ℝ × Rd d) : ℂ :=
  Complex.exp ((-(l * p.1) : ℝ) + Complex.I * (inner ℝ ξ p.2 : ℝ))

/-- The real values of the zero extension. -/
def re0 (F : Kernel d) (p : ℝ × Rd d) : ℝ := (zeroExt F p.1 p.2).toReal

/-- The integrand of the Laplace-Fourier transform on `ℝ × ℝ^d`. -/
def chRe (l : ℝ) (ξ : Rd d) (F : Kernel d) (p : ℝ × Rd d) : ℂ := ch l ξ p * (re0 F p : ℂ)

theorem ch_add (l : ℝ) (ξ : Rd d) (p q : ℝ × Rd d) : ch l ξ (p + q) = ch l ξ p * ch l ξ q := by
  simp only [ch, ← Complex.exp_add, Prod.fst_add, Prod.snd_add, inner_add_right]
  congr 1
  push_cast
  ring

theorem continuous_ch (l : ℝ) (ξ : Rd d) : Continuous (ch l ξ) := by
  unfold ch
  fun_prop

theorem norm_ch (l : ℝ) (ξ : Rd d) (p : ℝ × Rd d) : ‖ch l ξ p‖ = Real.exp (-(l * p.1)) := by
  simp [ch, Complex.norm_exp]

theorem measurable_re0 {F : Kernel d} (hF : Measurable (uncurry F)) : Measurable (re0 F) :=
  ENNReal.measurable_toReal.comp (measurable_zeroExt hF)

theorem measurable_chRe (l : ℝ) (ξ : Rd d) {F : Kernel d} (hF : Measurable (uncurry F)) :
    Measurable (chRe l ξ F) :=
  (continuous_ch l ξ).measurable.mul (Complex.measurable_ofReal.comp (measurable_re0 hF))

/-- For `λ ≥ 0`, `|e^{-λt+iξ·x} F^0(t,x)| ≤ F^0(t,x)`. -/
theorem enorm_chRe_le {l : ℝ} (hl : 0 ≤ l) (ξ : Rd d) (F : Kernel d) (p : ℝ × Rd d) :
    ‖chRe l ξ F p‖ₑ ≤ zeroExt F p.1 p.2 := by
  by_cases hp : 0 < p.1
  · rw [chRe, enorm_mul]
    have h1 : ‖ch l ξ p‖ₑ ≤ 1 := by
      rw [← ofReal_norm, norm_ch]
      exact ENNReal.ofReal_le_one.2
        (Real.exp_le_one_iff.2 (neg_nonpos.2 (mul_nonneg hl hp.le)))
    have h2 : ‖(re0 F p : ℂ)‖ₑ ≤ zeroExt F p.1 p.2 := by
      rw [← ofReal_norm, Complex.norm_real, Real.norm_eq_abs, re0,
        abs_of_nonneg ENNReal.toReal_nonneg]
      exact ENNReal.ofReal_toReal_le
    calc ‖ch l ξ p‖ₑ * ‖(re0 F p : ℂ)‖ₑ ≤ 1 * zeroExt F p.1 p.2 := mul_le_mul' h1 h2
      _ = zeroExt F p.1 p.2 := one_mul _
  · simp [chRe, re0, zeroExt_of_nonpos F (not_lt.1 hp)]

/-- `𝓛F(λ,ξ) = ∫ e^{-λt+iξ·x} F^0(t,x)` over `ℝ × ℝ^d`. -/
theorem lapFour_eq (F : Kernel d) (l : ℝ) (ξ : Rd d) :
    lapFour F l ξ = ∫ p : ℝ × Rd d, chRe l ξ F p := by
  rw [lapFour, ← integral_indicator (measurableSet_Ioi.prod MeasurableSet.univ)]
  refine integral_congr_ae (ae_of_all _ fun p => ?_)
  by_cases hp : 0 < p.1
  · rw [Set.indicator_of_mem (show p ∈ Ioi (0 : ℝ) ×ˢ (univ : Set (Rd d)) by simp [hp])]
    simp only [chRe, ch, re0, zeroExt_of_pos F hp]
  · rw [Set.indicator_of_notMem (show p ∉ Ioi (0 : ℝ) ×ˢ (univ : Set (Rd d)) by simp [hp])]
    simp [chRe, re0, zeroExt_of_nonpos F (not_lt.1 hp)]

/-- **`|𝓛G(λ,ξ)| ≤ N_0(G)` for `λ ≥ 0`** (TeX 1531-1532). -/
theorem enorm_lapFour_le {F : Kernel d} (hF : Measurable (uncurry F)) {l : ℝ} (hl : 0 ≤ l)
    (ξ : Rd d) : ‖lapFour F l ξ‖ₑ ≤ N0 F := by
  rw [lapFour_eq, N0_eq_lintegral hF]
  exact (enorm_integral_le_lintegral_enorm _).trans
    (lintegral_mono fun p => enorm_chRe_le hl ξ F p)

/-- The real values of the convolution are the real convolution of the real values. -/
theorem re0_conv {G H : Kernel d} (hG : Measurable (uncurry G)) (hH : Measurable (uncurry H))
    (hG0 : N0 G < ∞) (hH0 : N0 H < ∞) (p : ℝ × Rd d) :
    re0 (conv G H) p = ∫ q : ℝ × Rd d, re0 G q * re0 H (p - q) := by
  have hmG := measurable_zeroExt hG
  have hmH : Measurable fun q : ℝ × Rd d => zeroExt H (p - q).1 (p - q).2 :=
    (measurable_zeroExt hH).comp (measurable_const.sub measurable_id)
  have hm : Measurable fun q : ℝ × Rd d => re0 G q * re0 H (p - q) :=
    (measurable_re0 hG).mul (ENNReal.measurable_toReal.comp hmH)
  have h0 : 0 ≤ᵐ[volume] fun q : ℝ × Rd d => re0 G q * re0 H (p - q) :=
    Filter.Eventually.of_forall fun q => mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
  rw [integral_eq_lintegral_of_nonneg_ae (f := fun q : ℝ × Rd d => re0 G q * re0 H (p - q)) h0
    hm.aestronglyMeasurable]
  show (zeroExt (conv G H) p.1 p.2).toReal = _
  rw [zeroExt_conv, conv_eq_lintegral hG hH p]
  congr 1
  have h1 : ∀ᵐ q : ℝ × Rd d, zeroExt G q.1 q.2 < ∞ :=
    ae_lt_top hmG (by have := hG0.ne; rwa [N0_eq_lintegral hG] at this)
  have h2 : ∀ᵐ q : ℝ × Rd d, zeroExt H (p - q).1 (p - q).2 < ∞ :=
    ae_lt_top hmH (by
      have := hH0.ne
      rwa [N0_eq_lintegral hH, ← lintegral_zeroExt_sub_left H p] at this)
  refine lintegral_congr_ae ?_
  filter_upwards [h1, h2] with q hq1 hq2
  simp only [re0]
  rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hq1.ne,
    ENNReal.ofReal_toReal hq2.ne]

/-- **The Laplace-Fourier product** `𝓛(G * H) = 𝓛G · 𝓛H` for `λ ≥ 0` (TeX 1522-1523: "positivity and
the Laplace-Fourier product"). -/
theorem lapFour_conv {G H : Kernel d} (hG : Measurable (uncurry G))
    (hH : Measurable (uncurry H)) (hG0 : N0 G < ∞) (hH0 : N0 H < ∞) {l : ℝ} (hl : 0 ≤ l)
    (ξ : Rd d) : lapFour (conv G H) l ξ = lapFour G l ξ * lapFour H l ξ := by
  have key : ∀ p : ℝ × Rd d,
      chRe l ξ (conv G H) p = ∫ q : ℝ × Rd d, chRe l ξ G q * chRe l ξ H (p - q) := by
    intro p
    show ch l ξ p * (re0 (conv G H) p : ℂ) = _
    rw [re0_conv hG hH hG0 hH0 p, ← integral_complex_ofReal, ← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun q => ?_)
    have hch : ch l ξ p = ch l ξ q * ch l ξ (p - q) := by
      rw [← ch_add]; congr 1; abel
    simp only [chRe]
    rw [hch]
    push_cast
    ring
  have hm : Measurable (uncurry fun p q : ℝ × Rd d =>
      zeroExt G q.1 q.2 * zeroExt H (p - q).1 (p - q).2) :=
    ((measurable_zeroExt hG).comp measurable_snd).mul
      ((measurable_zeroExt hH).comp (measurable_fst.sub measurable_snd))
  have hΦ : Measurable (uncurry fun p q : ℝ × Rd d => chRe l ξ G q * chRe l ξ H (p - q)) :=
    ((measurable_chRe l ξ hG).comp measurable_snd).mul
      ((measurable_chRe l ξ hH).comp (measurable_fst.sub measurable_snd))
  have hint : Integrable (uncurry fun p q : ℝ × Rd d => chRe l ξ G q * chRe l ξ H (p - q))
      ((volume : Measure (ℝ × Rd d)).prod volume) := by
    refine ⟨hΦ.aestronglyMeasurable, ?_⟩
    have hle : ∀ x : (ℝ × Rd d) × (ℝ × Rd d),
        ‖uncurry (fun p q : ℝ × Rd d => chRe l ξ G q * chRe l ξ H (p - q)) x‖ₑ ≤
          uncurry (fun p q : ℝ × Rd d => zeroExt G q.1 q.2 * zeroExt H (p - q).1 (p - q).2) x :=
      fun x => by
        show ‖chRe l ξ G x.2 * chRe l ξ H (x.1 - x.2)‖ₑ ≤ _
        rw [enorm_mul]
        exact mul_le_mul' (enorm_chRe_le hl ξ G _) (enorm_chRe_le hl ξ H _)
    refine lt_of_le_of_lt (lintegral_mono hle) ?_
    rw [lintegral_prod _ hm.aemeasurable]
    exact (lintegral_conv_kernel hG hH).trans_lt (ENNReal.mul_lt_top hG0 hH0)
  rw [lapFour_eq, lapFour_eq, lapFour_eq, integral_congr_ae (ae_of_all _ key),
    integral_integral_swap hint]
  have inner : ∀ q : ℝ × Rd d,
      ∫ p : ℝ × Rd d, chRe l ξ G q * chRe l ξ H (p - q) =
        chRe l ξ G q * ∫ r : ℝ × Rd d, chRe l ξ H r := fun q => by
    rw [integral_const_mul, integral_sub_right_prodRd (chRe l ξ H) q]
  rw [integral_congr_ae (ae_of_all _ inner), integral_mul_const]

/-- `ν_e`-almost every parameter lies in `A_e`. -/
theorem ae_nuE_mem (a : ℝ) {A : Set ℝ} (hA : MeasurableSet A) : ∀ᵐ l ∂nuE a A, l ∈ A :=
  (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem hA)

/-- **`N_{1,e}(G * H) ≤ N_0(G) N_{1,e}(H)`** (TeX 1527, proof 1531-1532). -/
theorem N1_conv_le {G H : Kernel d} (hG : Measurable (uncurry G)) (hH : Measurable (uncurry H))
    (hG0 : N0 G < ∞) (hH0 : N0 H < ∞) (a : ℝ) (E : EdgeData d) :
    N1 a E (conv G H) ≤ N0 G * N1 a E H := by
  unfold N1
  calc ∫⁻ l, ∫⁻ ξ, ‖lapFour (conv G H) l ξ‖ₑ ∂E.μ ∂nuE a E.A
      ≤ ∫⁻ l, ∫⁻ ξ, N0 G * ‖lapFour H l ξ‖ₑ ∂E.μ ∂nuE a E.A := by
        refine lintegral_mono_ae ?_
        filter_upwards [ae_nuE_mem a E.measurableSet_A] with l hl
        have hl0 : 0 ≤ l := le_of_lt (Set.mem_Ioi.1 (E.A_subset hl))
        refine lintegral_mono fun ξ => ?_
        rw [lapFour_conv hG hH hG0 hH0 hl0, enorm_mul]
        exact mul_le_mul' (enorm_lapFour_le hG hl0 ξ) le_rfl
    _ = N0 G * ∫⁻ l, ∫⁻ ξ, ‖lapFour H l ξ‖ₑ ∂E.μ ∂nuE a E.A := by
        simp_rw [lintegral_const_mul' (N0 G) _ hG0.ne]

/-! ### The covariance norm of a convolution -/

theorem measurable_kappaCap (ν : Measure ℝ) [SFinite ν] (L : ℝ) : Measurable (kappaCap ν L) := by
  unfold kappaCap
  have : Measurable fun x : ℝ × ℝ => ENNReal.ofReal (Real.exp (-(x.2 * |x.1|))) :=
    (Real.continuous_exp.comp (by fun_prop : Continuous fun x : ℝ × ℝ => -(x.2 * |x.1|)))
      |>.measurable.ennreal_ofReal
  exact this.lintegral_prod_right'

theorem measurable_gammaOf (μ : Measure (Rd d)) [SFinite μ] : Measurable (gammaOf μ) := by
  unfold gammaOf
  refine ENNReal.measurable_ofReal.comp ?_
  have hc : StronglyMeasurable (uncurry fun (x ξ : Rd d) => Real.cos (inner ℝ ξ x)) :=
    (Real.continuous_cos.comp (continuous_snd.inner continuous_fst)).stronglyMeasurable
  exact (hc.integral_prod_right (ν := μ)).measurable

theorem kappaCap_of_nonpos (ν : Measure ℝ) {L : ℝ} (hL : L ≤ 0) (t : ℝ) : kappaCap ν L t = 0 := by
  simp [kappaCap, Ioc_eq_empty (not_lt.2 hL)]

theorem QL_of_nonpos (ν : Measure ℝ) (μ : Measure (Rd d)) {L : ℝ} (hL : L ≤ 0) (f h : Kernel d) :
    QL ν μ L f h = 0 := by
  simp [QL, kappaCap_of_nonpos ν hL]

/-- `ν_e((0,L]) < ∞` for `a > 0` (TeX 1512: "its measure is finite since `a > 0`"). -/
theorem nuE_Ioc_lt_top {a : ℝ} (ha : 0 < a) (A : Set ℝ) (L : ℝ) : nuE a A (Ioc 0 L) < ∞ := by
  rw [nuE, withDensity_apply _ measurableSet_Ioc]
  rcases le_or_gt L 0 with hL | hL
  · simp [Ioc_eq_empty (not_lt.2 hL)]
  have hint : IntegrableOn (fun l : ℝ => (Real.Gamma a)⁻¹ * l ^ (a - 1)) (Ioc 0 L) :=
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hL.le).1
      (intervalIntegral.intervalIntegrable_rpow' (by linarith))).const_mul _
  calc ∫⁻ l in Ioc 0 L, ENNReal.ofReal ((Real.Gamma a)⁻¹ * l ^ (a - 1)) ∂volume.restrict A
      ≤ ∫⁻ l in Ioc 0 L, ENNReal.ofReal ((Real.Gamma a)⁻¹ * l ^ (a - 1)) :=
        lintegral_mono' (Measure.restrict_mono subset_rfl Measure.restrict_le_self) le_rfl
    _ < ∞ := hint.lintegral_lt_top

/-- Three nonnegative integrals in one variable each: `(∫a)(∫b) k₁ k₂ = ∫∫ a b k₁ k₂`. -/
theorem lintegral_mul_lintegral_mul (a b : ℝ × Rd d → ℝ≥0∞) (ha : Measurable a)
    (hb : Measurable b) (k₁ k₂ : ℝ≥0∞) :
    (∫⁻ q, a q) * (∫⁻ q', b q') * k₁ * k₂ = ∫⁻ q, ∫⁻ q', a q * b q' * k₁ * k₂ := by
  rw [mul_assoc, mul_assoc, ← lintegral_mul_const _ hb, ← lintegral_mul_const _ ha]
  refine lintegral_congr fun q => ?_
  rw [← lintegral_const_mul _ (hb.mul_const _)]
  refine lintegral_congr fun q' => ?_
  ring

/-- Moving one variable outward past two (Tonelli). -/
theorem lintegral_swap3 {Ψ : ℝ × Rd d → ℝ × Rd d → ℝ × Rd d → ℝ≥0∞}
    (hΨ : Measurable fun x : (ℝ × Rd d) × (ℝ × Rd d) × (ℝ × Rd d) => Ψ x.1 x.2.1 x.2.2) :
    ∫⁻ p, ∫⁻ p', ∫⁻ q, Ψ p p' q = ∫⁻ q, ∫⁻ p, ∫⁻ p', Ψ p p' q := by
  have h1 : ∀ p, ∫⁻ p', ∫⁻ q, Ψ p p' q = ∫⁻ q, ∫⁻ p', Ψ p p' q := fun p =>
    lintegral_lintegral_swap (hΨ.comp (measurable_const.prodMk measurable_id)).aemeasurable
  rw [lintegral_congr h1]
  have h2 : Measurable (uncurry fun p q : ℝ × Rd d => ∫⁻ p', Ψ p p' q) :=
    (hΨ.comp (measurable_fst.fst.prodMk (measurable_snd.prodMk measurable_fst.snd))
      ).lintegral_prod_right'
  exact lintegral_lintegral_swap h2.aemeasurable

/-- Moving two variables outward past two (Tonelli). -/
theorem lintegral_swap4 {Φ : ℝ × Rd d → ℝ × Rd d → ℝ × Rd d → ℝ × Rd d → ℝ≥0∞}
    (hΦ : Measurable fun x : (ℝ × Rd d) × (ℝ × Rd d) × (ℝ × Rd d) × (ℝ × Rd d) =>
      Φ x.1 x.2.1 x.2.2.1 x.2.2.2) :
    ∫⁻ p, ∫⁻ p', ∫⁻ q, ∫⁻ q', Φ p p' q q' = ∫⁻ q, ∫⁻ q', ∫⁻ p, ∫⁻ p', Φ p p' q q' := by
  have hΨ : Measurable fun x : (ℝ × Rd d) × (ℝ × Rd d) × (ℝ × Rd d) =>
      ∫⁻ q', Φ x.1 x.2.1 x.2.2 q' :=
    (hΦ.comp (measurable_fst.fst.prodMk (measurable_fst.snd.fst.prodMk
      (measurable_fst.snd.snd.prodMk measurable_snd)))).lintegral_prod_right'
  refine (lintegral_swap3 (Ψ := fun p p' q => ∫⁻ q', Φ p p' q q') hΨ).trans ?_
  refine lintegral_congr fun q => ?_
  exact lintegral_swap3 (Ψ := fun p p' q' => Φ p p' q q')
    (hΦ.comp (measurable_fst.prodMk (measurable_snd.fst.prodMk
      (measurable_const.prodMk measurable_snd.snd))))

/-- The four-variable integrand of the expanded pairing `Q_L((G*H)^0,(G*H)^0)`. -/
def phiConv (ν : Measure ℝ) (μ : Measure (Rd d)) (L : ℝ) (G H : Kernel d)
    (p p' q q' : ℝ × Rd d) : ℝ≥0∞ :=
  zeroExt G q.1 q.2 * transl q.1 q.2 (zeroExt H) p.1 p.2 *
    (zeroExt G q'.1 q'.2 * transl q'.1 q'.2 (zeroExt H) p'.1 p'.2) *
    kappaCap ν L (p.1 - p'.1) * gammaOf μ (p.2 - p'.2)

theorem measurable_transl_zeroExt {H : Kernel d} (hH : Measurable (uncurry H)) :
    Measurable fun y : (ℝ × Rd d) × (ℝ × Rd d) => transl y.1.1 y.1.2 (zeroExt H) y.2.1 y.2.2 :=
  (measurable_zeroExt hH).comp (measurable_snd.sub measurable_fst)

theorem measurable_kappaCap_sub (ν : Measure ℝ) [SFinite ν] (L : ℝ) :
    Measurable fun y : (ℝ × Rd d) × (ℝ × Rd d) => kappaCap ν L (y.1.1 - y.2.1) :=
  (measurable_kappaCap ν L).comp (measurable_fst.fst.sub measurable_snd.fst)

theorem measurable_gammaOf_sub (μ : Measure (Rd d)) [SFinite μ] :
    Measurable fun y : (ℝ × Rd d) × (ℝ × Rd d) => gammaOf μ (y.1.2 - y.2.2) :=
  (measurable_gammaOf μ).comp (measurable_fst.snd.sub measurable_snd.snd)

theorem measurable_phiConv {ν : Measure ℝ} [SFinite ν] {μ : Measure (Rd d)} [SFinite μ]
    (L : ℝ) {G H : Kernel d} (hG : Measurable (uncurry G)) (hH : Measurable (uncurry H)) :
    Measurable fun x : (ℝ × Rd d) × (ℝ × Rd d) × (ℝ × Rd d) × (ℝ × Rd d) =>
      phiConv ν μ L G H x.1 x.2.1 x.2.2.1 x.2.2.2 := by
  have hG' : Measurable fun q : ℝ × Rd d => zeroExt G q.1 q.2 := measurable_zeroExt hG
  have hT := measurable_transl_zeroExt hH
  have h1 : Measurable fun x : (ℝ × Rd d) × (ℝ × Rd d) × (ℝ × Rd d) × (ℝ × Rd d) =>
      zeroExt G x.2.2.1.1 x.2.2.1.2 * transl x.2.2.1.1 x.2.2.1.2 (zeroExt H) x.1.1 x.1.2 :=
    (hG'.comp measurable_snd.snd.fst).mul
      (hT.comp (f := fun x : (ℝ × Rd d) × (ℝ × Rd d) × (ℝ × Rd d) × (ℝ × Rd d) => (x.2.2.1, x.1))
        (by fun_prop))
  have h2 : Measurable fun x : (ℝ × Rd d) × (ℝ × Rd d) × (ℝ × Rd d) × (ℝ × Rd d) =>
      zeroExt G x.2.2.2.1 x.2.2.2.2 * transl x.2.2.2.1 x.2.2.2.2 (zeroExt H) x.2.1.1 x.2.1.2 :=
    (hG'.comp measurable_snd.snd.snd).mul
      (hT.comp (f := fun x : (ℝ × Rd d) × (ℝ × Rd d) × (ℝ × Rd d) × (ℝ × Rd d) => (x.2.2.2, x.2.1))
        (by fun_prop))
  have h3 : Measurable fun x : (ℝ × Rd d) × (ℝ × Rd d) × (ℝ × Rd d) × (ℝ × Rd d) =>
      kappaCap ν L (x.1.1 - x.2.1.1) :=
    (measurable_kappaCap ν L).comp (measurable_fst.fst.sub measurable_snd.fst.fst)
  have h4 : Measurable fun x : (ℝ × Rd d) × (ℝ × Rd d) × (ℝ × Rd d) × (ℝ × Rd d) =>
      gammaOf μ (x.1.2 - x.2.1.2) :=
    (measurable_gammaOf μ).comp (measurable_fst.snd.sub measurable_snd.fst.snd)
  exact ((h1.mul h2).mul h3).mul h4

/-- The inner two integrals of the expanded pairing: `G^0(q) G^0(q') Q_L(T_q H^0, T_{q'} H^0)`. -/
theorem lintegral_phiConv_inner {ν : Measure ℝ} [SFinite ν] {μ : Measure (Rd d)} [SFinite μ]
    (L : ℝ) {G H : Kernel d} (hH : Measurable (uncurry H)) (q q' : ℝ × Rd d) :
    ∫⁻ p : ℝ × Rd d, ∫⁻ p' : ℝ × Rd d, phiConv ν μ L G H p p' q q' =
      zeroExt G q.1 q.2 * zeroExt G q'.1 q'.2 *
        QL ν μ L (transl q.1 q.2 (zeroExt H)) (transl q'.1 q'.2 (zeroExt H)) := by
  have hT := measurable_transl_zeroExt hH
  set c := zeroExt G q.1 q.2 * zeroExt G q'.1 q'.2
  have hin : Measurable fun y : (ℝ × Rd d) × (ℝ × Rd d) =>
      transl q.1 q.2 (zeroExt H) y.1.1 y.1.2 * transl q'.1 q'.2 (zeroExt H) y.2.1 y.2.2 *
        kappaCap ν L (y.1.1 - y.2.1) * gammaOf μ (y.1.2 - y.2.2) :=
    (((hT.comp (f := fun y : (ℝ × Rd d) × (ℝ × Rd d) => (q, y.1)) (by fun_prop)).mul
      (hT.comp (f := fun y : (ℝ × Rd d) × (ℝ × Rd d) => (q', y.2)) (by fun_prop))).mul
        (measurable_kappaCap_sub ν L)).mul (measurable_gammaOf_sub μ)
  have hin' : ∀ p : ℝ × Rd d, Measurable fun p' : ℝ × Rd d =>
      transl q.1 q.2 (zeroExt H) p.1 p.2 * transl q'.1 q'.2 (zeroExt H) p'.1 p'.2 *
        kappaCap ν L (p.1 - p'.1) * gammaOf μ (p.2 - p'.2) := fun p =>
    hin.comp (f := fun p' : ℝ × Rd d => (p, p')) (by fun_prop)
  have hout : Measurable fun p : ℝ × Rd d => ∫⁻ p' : ℝ × Rd d,
      transl q.1 q.2 (zeroExt H) p.1 p.2 * transl q'.1 q'.2 (zeroExt H) p'.1 p'.2 *
        kappaCap ν L (p.1 - p'.1) * gammaOf μ (p.2 - p'.2) :=
    hin.lintegral_prod_right'
  have e : ∀ p p' : ℝ × Rd d, phiConv ν μ L G H p p' q q' =
      c * (transl q.1 q.2 (zeroExt H) p.1 p.2 * transl q'.1 q'.2 (zeroExt H) p'.1 p'.2 *
        kappaCap ν L (p.1 - p'.1) * gammaOf μ (p.2 - p'.2)) := fun p p' => by
    simp only [phiConv, c]; ring
  simp only [e]
  rw [QL]
  simp only [lintegral_const_mul _ (hin' _), lintegral_const_mul _ hout]

/-- The pairing of the convolution is the double integral of the translated pairings. -/
theorem QL_conv_eq {ν : Measure ℝ} [SFinite ν] {μ : Measure (Rd d)} [SFinite μ] (L : ℝ)
    {G H : Kernel d} (hG : Measurable (uncurry G)) (hH : Measurable (uncurry H)) :
    QL ν μ L (zeroExt (conv G H)) (zeroExt (conv G H)) =
      ∫⁻ q : ℝ × Rd d, ∫⁻ q' : ℝ × Rd d, zeroExt G q.1 q.2 * zeroExt G q'.1 q'.2 *
        QL ν μ L (transl q.1 q.2 (zeroExt H)) (transl q'.1 q'.2 (zeroExt H)) := by
  have hG' : Measurable fun q : ℝ × Rd d => zeroExt G q.1 q.2 := measurable_zeroExt hG
  have hT := measurable_transl_zeroExt hH
  have hF : ∀ p : ℝ × Rd d, zeroExt (conv G H) p.1 p.2 =
      ∫⁻ q : ℝ × Rd d, zeroExt G q.1 q.2 * transl q.1 q.2 (zeroExt H) p.1 p.2 := fun p => by
    rw [zeroExt_conv, conv_eq_lintegral hG hH p]
    rfl
  have ha : ∀ p : ℝ × Rd d, Measurable fun q : ℝ × Rd d =>
      zeroExt G q.1 q.2 * transl q.1 q.2 (zeroExt H) p.1 p.2 := fun p =>
    hG'.mul (hT.comp (f := fun q : ℝ × Rd d => (q, p)) (by fun_prop))
  have step1 : QL ν μ L (zeroExt (conv G H)) (zeroExt (conv G H)) =
      ∫⁻ p : ℝ × Rd d, ∫⁻ p' : ℝ × Rd d, ∫⁻ q : ℝ × Rd d, ∫⁻ q' : ℝ × Rd d,
        phiConv ν μ L G H p p' q q' := by
    rw [QL]
    refine lintegral_congr fun p => lintegral_congr fun p' => ?_
    rw [hF p, hF p', lintegral_mul_lintegral_mul _ _ (ha p) (ha p')]
    rfl
  rw [step1, lintegral_swap4 (measurable_phiConv L hG hH)]
  exact lintegral_congr fun q => lintegral_congr fun q' => lintegral_phiConv_inner L hH q q'

/-- **At every cap, `Q_L((G*H)^0,(G*H)^0) ≤ N_0(G)² Q_L(H^0,H^0)`** (Minkowski, TeX 1532-1534),
from the capped Cauchy-Schwarz of `L:translated-covariance-CS` (item A, a hypothesis). -/
theorem QL_conv_le (hA : TranslatedCSCappedTarget d) {ν : Measure ℝ} [SFinite ν]
    (hν : ∀ L : ℝ, 0 < L → ν (Ioc 0 L) < ∞) {μ : Measure (Rd d)} [IsFiniteMeasure μ]
    (hμ : SpecNonneg μ) {G H : Kernel d} (hG : Measurable (uncurry G))
    (hH : Measurable (uncurry H)) (hH0 : N0 H < ∞) (L : ℝ) :
    QL ν μ L (zeroExt (conv G H)) (zeroExt (conv G H)) ≤
      N0 G ^ 2 * QL ν μ L (zeroExt H) (zeroExt H) := by
  rcases le_or_gt L 0 with hL | hL
  · rw [QL_of_nonpos ν μ hL]; exact zero_le
  have h2 : ∀ x : ℝ≥0∞, x ^ (2⁻¹ : ℝ) * x ^ (2⁻¹ : ℝ) = x := fun x => by
    rw [← pow_two]; simpa using ENNReal.rpow_inv_natCast_pow (n := 2) two_ne_zero x
  have hT : ∀ q q' : ℝ × Rd d,
      QL ν μ L (transl q.1 q.2 (zeroExt H)) (transl q'.1 q'.2 (zeroExt H)) ≤
        QL ν μ L (zeroExt H) (zeroExt H) := fun q q' => by
    have := (hA ν μ L hL (hν L hL) inferInstance hμ H H hH hH hH0 hH0 q.1 q'.1 q.2 q'.2).1
    rwa [h2] at this
  have hG' : Measurable fun q : ℝ × Rd d => zeroExt G q.1 q.2 := measurable_zeroExt hG
  set c := QL ν μ L (zeroExt H) (zeroExt H)
  rw [QL_conv_eq L hG hH]
  calc ∫⁻ q : ℝ × Rd d, ∫⁻ q' : ℝ × Rd d, zeroExt G q.1 q.2 * zeroExt G q'.1 q'.2 *
        QL ν μ L (transl q.1 q.2 (zeroExt H)) (transl q'.1 q'.2 (zeroExt H))
      ≤ ∫⁻ q : ℝ × Rd d, ∫⁻ q' : ℝ × Rd d, zeroExt G q.1 q.2 * zeroExt G q'.1 q'.2 * c :=
        lintegral_mono fun q => lintegral_mono fun q' => mul_le_mul' le_rfl (hT q q')
    _ = N0 G ^ 2 * c := by
        have e1 : ∀ q : ℝ × Rd d,
            ∫⁻ q' : ℝ × Rd d, zeroExt G q.1 q.2 * zeroExt G q'.1 q'.2 * c =
              zeroExt G q.1 q.2 * N0 G * c := fun q => by
          have hq : Measurable fun q' : ℝ × Rd d => zeroExt G q.1 q.2 * zeroExt G q'.1 q'.2 :=
            measurable_const.mul hG'
          rw [lintegral_mul_const _ hq, lintegral_const_mul _ hG', ← N0_eq_lintegral hG]
        have hq : Measurable fun q : ℝ × Rd d => zeroExt G q.1 q.2 * N0 G := hG'.mul_const _
        rw [lintegral_congr e1, lintegral_mul_const _ hq, lintegral_mul_const _ hG',
          ← N0_eq_lintegral hG, pow_two]

/-- **`N_C(G * H) ≤ N_0(G) N_C(H)`** (the cap limit of `QL_conv_le`). -/
theorem NC_conv_le (hA : TranslatedCSCappedTarget d) {ν : Measure ℝ} [SFinite ν]
    (hν : ∀ L : ℝ, 0 < L → ν (Ioc 0 L) < ∞) {μ : Measure (Rd d)} [IsFiniteMeasure μ]
    (hμ : SpecNonneg μ) {G H : Kernel d} (hG : Measurable (uncurry G))
    (hH : Measurable (uncurry H)) (hH0 : N0 H < ∞) :
    NC ν μ (conv G H) ≤ N0 G * NC ν μ H := by
  have hQ : Q ν μ (zeroExt (conv G H)) (zeroExt (conv G H)) ≤
      N0 G ^ 2 * Q ν μ (zeroExt H) (zeroExt H) := by
    unfold Q
    rw [ENNReal.mul_iSup]
    exact iSup_mono fun L => QL_conv_le hA hν hμ hG hH hH0 L
  unfold NC
  calc Q ν μ (zeroExt (conv G H)) (zeroExt (conv G H)) ^ (2⁻¹ : ℝ)
      ≤ (N0 G ^ 2 * Q ν μ (zeroExt H) (zeroExt H)) ^ (2⁻¹ : ℝ) :=
        ENNReal.rpow_le_rpow hQ (by norm_num)
    _ = N0 G * Q ν μ (zeroExt H) (zeroExt H) ^ (2⁻¹ : ℝ) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
        congr 1
        simpa using ENNReal.pow_rpow_inv_natCast (n := 2) two_ne_zero (N0 G)

/-- **`N_{2,e}(G * H) ≤ N_0(G) N_{2,e}(H)`** (TeX 1528, proof 1532-1534). -/
theorem N2_conv_le (hA : TranslatedCSCappedTarget d) {a : ℝ} (ha : 0 < a) (E : EdgeData d)
    {G H : Kernel d} (hG : Measurable (uncurry G)) (hH : Measurable (uncurry H))
    (hH0 : N0 H < ∞) : N2 a E (conv G H) ≤ N0 G * N2 a E H :=
  NC_conv_le hA (fun L _ => nuE_Ioc_lt_top ha E.A L) E.spec_nonneg hG hH hH0

/-! ### Step 1 -/

/-- **`E:pairing-convolution-norms`** (Step 1 of `L:pairing-product-envelope`; claim and proof
TeX lines 1522-1535, display 1524-1530, at revision edf7085f (book 1.1.3)), with item A's capped
Cauchy-Schwarz `TranslatedCSCappedTarget d` as the hypothesis. -/
theorem convolution_norms (hA : TranslatedCSCappedTarget d) : ConvolutionNormsTarget d := by
  intro a ha0 _ G H hG hH hG0 hH0
  exact ⟨N0_conv hG hH, fun E _ =>
    ⟨N1_conv_le hG hH hG0 hH0 a E, N2_conv_le hA ha0 E hG hH hH0⟩⟩

end StratonovichHAMSecondMoment.PairingConvolution
