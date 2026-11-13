module

/-
Copyright 2026 Le Chen. SPDX-License-Identifier: Apache-2.0

The damped norms `N₁, N₂` of `E:damped-norm-definitions` (line 782) and the
finiteness part of `L:damped-homogeneous-norms` (lines 803-919) of the main
TeX file `notes/notes_stratonovich_ham_second_moment.tex` (revision a284420).

Definitions:
* `N2sq a θ μ` is `N₂(θ)²` with temporal exponent `a`:
  `∫∫_{(0,∞)²} e^{-θ(s+t)} |s-t|^{-a} ∫ Ĝ_s(ξ) Ĝ_t(ξ) μ(dξ) ds dt`, the outer
  integral taken on `(0,∞)²` with Lebesgue product measure; `Ĝ` is real, so
  the conjugate is dropped.  Its integrand at `s = t` (a null set) is
  irrelevant.
* `N1 a θ μ` is `Γ(a)⁻¹ ∫_0^∞ λ^{a-1} R_Γ(θ+λ) dλ` with
  `R_Γ(q) = ∫ μ(dξ)/(q²+|ξ|²)`, which is the manuscript's `N₁(θ)`.
* `N₀` involves the physical Green measure `G_s(ℝ^d)`, which this module
  does not define; `N₀` is formalized in `DampedNormsHomog` and `WaveGreen`.

Formalized (finiteness part of `L:damped-homogeneous-norms`): under
`H:homog` and the supplied input `SpectralHomog.SpectralHomogeneous μ α`,
for every `θ > 0`
* the displayed spectral formula for `N₂(θ)²` is absolutely integrable on
  `(0,∞)² × ℝ^d` (`N2integrand_integrable`), and so is its outer integrand
  (`N2_outer_integrable`);
* the integrand of `N₁(θ)` is integrable on `(0,∞)` (`N1_integrable`).
The wrapper is `damped_norms_finite_paper`.  The scaling identities, the
temporal tails `E:damped-tail-norms` and the multiplier comparison
`E:damped-multiplier-comparison` of the lemma are not formalized here (they
are in `DampedNormsHomog`); `N₂(θ)² ≥ 0` is proved in `ClockCopy`
(`damped_N2_nonneg_paper`) from the exact formula of
`P:clock-copy-obstruction`.

Proof route (differs from the TeX, same conclusion): instead of splitting
`|ξ| ≤ 1` and `|ξ| > 1` and the time cones, the power kernel is expanded by
subordination, `|s-t|^{-a} = Γ(a)⁻¹ ∫ λ^{a-1} e^{-λ|s-t|} dλ`, and the
expanded integrand on `(0,∞) × ℝ^d × (0,∞)²` (`FK`, auxiliary) is dominated
using `|Ĝ_sĜ_t| ≤ 2(1+s)(1+t)(1+|ξ|²)⁻¹`; its Tonelli integral is computed
with the two-time Laplace lemma.  The absolute integrability of `N₂` is then
the `λ`-marginal of that of `FK`.  `FK` is also the integrand used for the
exact formula in `ClockCopy`.
-/

public import Mathlib
public import StratonovichHAMSecondMoment.HomogHypothesis
public import StratonovichHAMSecondMoment.TimeFractional
public import StratonovichHAMSecondMoment.SpectralHomog
public import StratonovichHAMSecondMoment.WaveKernel

@[expose] public section

noncomputable section

set_option autoImplicit false

open MeasureTheory Set Real Filter
open scoped ENNReal

namespace StratonovichHAMSecondMoment.DampedNorms

open HomogHypothesis TimeFractional SpectralHomog WaveKernel

variable {d : ℕ}

/-! ### Definitions -/

/-- The integrand of the displayed spectral formula for `N₂(θ)²`, as a
function of `((s,t), ξ)`. -/
def N2integrand (a θ : ℝ) (z : (ℝ × ℝ) × Rd d) : ℝ :=
  Real.exp (-(θ * (z.1.1 + z.1.2))) * |z.1.1 - z.1.2| ^ (-a) *
    (waveHat z.1.1 z.2 * waveHat z.1.2 z.2)

/-- `N₂(θ)²` of `E:damped-norm-definitions` (lines 788-791), temporal exponent `a`. -/
def N2sq (a θ : ℝ) (μ : Measure (Rd d)) : ℝ :=
  ∫ p, Real.exp (-(θ * (p.1 + p.2))) * |p.1 - p.2| ^ (-a) *
    ∫ ξ, waveHat p.1 ξ * waveHat p.2 ξ ∂μ ∂P2

/-- `N₁(θ)` of `E:damped-norm-definitions` (lines 785-787), temporal exponent `a`. -/
def N1 (a θ : ℝ) (μ : Measure (Rd d)) : ℝ :=
  (Real.Gamma a)⁻¹ * ∫ l in Ioi (0 : ℝ), l ^ (a - 1) * resolvent μ (θ + l)

/-- The subordinated integrand of `N₂(θ)²` on `(0,∞) × ℝ^d × (0,∞)²`
(auxiliary to the Lean proof route). -/
def FK (a θ : ℝ) (z : ℝ × (Rd d × (ℝ × ℝ))) : ℝ :=
  (Real.Gamma a)⁻¹ * |z.1| ^ (a - 1) * twoTimeR θ |z.1| z.2.2 *
    (waveHat z.2.2.1 z.2.1 * waveHat z.2.2.2 z.2.1)

/-! ### Almost-everywhere facts (auxiliary) -/

/-- Auxiliary to the Lean proof route. -/
theorem ae_L0_pos : ∀ᵐ l ∂L0, 0 < l := ae_restrict_mem measurableSet_Ioi

/-- Auxiliary to the Lean proof route. `P2`-a.e. `s, t > 0` and `s ≠ t`. -/
theorem ae_P2 : ∀ᵐ p ∂P2, 0 < p.1 ∧ 0 < p.2 ∧ p.1 ≠ p.2 := by
  have hpos : ∀ᵐ p ∂P2, p ∈ Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ) := by
    show ∀ᵐ p ∂((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))), _
    rw [Measure.prod_restrict]
    exact ae_restrict_mem (measurableSet_Ioi.prod measurableSet_Ioi)
  have hdiag : P2 {p : ℝ × ℝ | p.1 = p.2} = 0 := by
    rw [Measure.measure_prod_null (measurableSet_eq_fun measurable_fst measurable_snd)]
    refine Eventually.of_forall fun x => ?_
    have : Prod.mk x ⁻¹' {p : ℝ × ℝ | p.1 = p.2} = {x} := by
      ext y; simp [eq_comm]
    simp only [Pi.zero_apply, this]
    exact Measure.restrict_le_self.absolutelyContinuous (Real.volume_singleton)
  filter_upwards [hpos, measure_eq_zero_iff_ae_notMem.1 hdiag] with p hp hd
  exact ⟨hp.1, hp.2, hd⟩

/-- Auxiliary to the Lean proof route. On the triple product, a.e. `λ, s, t > 0` and `s ≠ t`. -/
theorem ae_triple (μ : Measure (Rd d)) [SFinite μ] :
    ∀ᵐ z ∂(L0.prod (μ.prod P2)), 0 < z.1 ∧ 0 < z.2.2.1 ∧ 0 < z.2.2.2 ∧
      z.2.2.1 ≠ z.2.2.2 := by
  have h1 : ∀ᵐ z ∂(L0.prod (μ.prod P2)), 0 < z.1 :=
    Measure.quasiMeasurePreserving_fst.ae ae_L0_pos
  have h2 : ∀ᵐ z ∂(L0.prod (μ.prod P2)),
      0 < z.2.2.1 ∧ 0 < z.2.2.2 ∧ z.2.2.1 ≠ z.2.2.2 :=
    Measure.quasiMeasurePreserving_snd.ae (Measure.quasiMeasurePreserving_snd.ae ae_P2)
  filter_upwards [h1, h2] with z hz1 hz2
  exact ⟨hz1, hz2⟩

/-! ### Domination of the subordinated integrand -/

/-- Auxiliary to the Lean proof route. -/
theorem one_add_le_exp (θ s : ℝ) (hθ : 0 < θ) (hs : 0 ≤ s) :
    1 + s ≤ (1 + 2 / θ) * Real.exp (θ * s / 2) := by
  have he := Real.add_one_le_exp (θ * s / 2)
  have h2 : 0 < 2 / θ := by positivity
  have h3 : 2 / θ * (θ * s / 2) = s := by field_simp
  nlinarith [Real.exp_pos (θ * s / 2)]

/-- Auxiliary to the Lean proof route. `λ ↦ K|λ|^{a-1}/(c(c+|λ|))` is integrable on
`(0,∞)`. -/
theorem integrable_rpow_div (a c K : ℝ) (ha0 : 0 < a) (ha1 : a < 1) (hc : 0 < c)
    (hK : 0 ≤ K) :
    Integrable (fun l : ℝ => K * |l| ^ (a - 1) / (c * (c + |l|))) L0 := by
  refine integrable_of_rpow_bounds (a - 1) (a - 2) (K / c ^ 2 + K / c) (by linarith)
    (by linarith) (by fun_prop : Measurable fun l : ℝ =>
      K * |l| ^ (a - 1) / (c * (c + |l|))).aestronglyMeasurable ?_ ?_
  · intro l hl _
    rw [abs_of_pos hl, Real.norm_of_nonneg (by positivity)]
    have hp : 0 ≤ l ^ (a - 1) := Real.rpow_nonneg hl.le _
    calc K * l ^ (a - 1) / (c * (c + l)) ≤ K * l ^ (a - 1) / (c * c) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity)
            (mul_le_mul_of_nonneg_left (by linarith) hc.le)
      _ = K / c ^ 2 * l ^ (a - 1) := by ring
      _ ≤ (K / c ^ 2 + K / c) * l ^ (a - 1) :=
          mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (by positivity)) hp
  · intro l hl
    have hl0 : 0 < l := lt_trans zero_lt_one hl
    rw [abs_of_pos hl0, Real.norm_of_nonneg (by positivity)]
    have hpq : l ^ (a - 2) = l ^ (a - 1) / l := by
      rw [show a - 2 = (a - 1) - 1 by ring, Real.rpow_sub_one hl0.ne']
    have hp0 : 0 ≤ l ^ (a - 1) := Real.rpow_nonneg hl0.le _
    rw [hpq]
    calc K * l ^ (a - 1) / (c * (c + l)) ≤ K * l ^ (a - 1) / (c * l) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity)
            (mul_le_mul_of_nonneg_left (by linarith) hc.le)
      _ = K / c * (l ^ (a - 1) / l) := by ring
      _ ≤ (K / c ^ 2 + K / c) * (l ^ (a - 1) / l) :=
          mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (by positivity))
            (by positivity)

/-- Auxiliary to the Lean proof route. -/
theorem waveHat_measurable :
    Measurable fun z : ℝ × Rd d => waveHat z.1 z.2 := waveHat_continuous.measurable

/-- Auxiliary to the Lean proof route. -/
theorem FK_measurable (a θ : ℝ) : Measurable (FK (d := d) a θ) := by
  have h1 : Measurable fun z : ℝ × (Rd d × (ℝ × ℝ)) => waveHat z.2.2.1 z.2.1 :=
    waveHat_measurable.comp (measurable_snd.snd.fst.prodMk measurable_snd.fst)
  have h2 : Measurable fun z : ℝ × (Rd d × (ℝ × ℝ)) => waveHat z.2.2.2 z.2.1 :=
    waveHat_measurable.comp (measurable_snd.snd.snd.prodMk measurable_snd.fst)
  unfold FK twoTimeR
  fun_prop

/-- The dominating function (auxiliary). -/
def MK (a θ : ℝ) (z : ℝ × (Rd d × (ℝ × ℝ))) : ℝ :=
  ((Real.Gamma a)⁻¹ * (2 * (1 + 2 / θ) ^ 2) * |z.1| ^ (a - 1) * (1 / (1 + ‖z.2.1‖ ^ 2))) *
    twoTimeR (θ / 2) |z.1| z.2.2

/-- Auxiliary to the Lean proof route. -/
theorem FK_le_MK (a θ : ℝ) (ha : 0 < a) (hθ : 0 < θ) (z : ℝ × (Rd d × (ℝ × ℝ)))
    (hs : 0 < z.2.2.1) (ht : 0 < z.2.2.2) : ‖FK a θ z‖ ≤ MK a θ z := by
  obtain ⟨l, ξ, s, t⟩ := z
  simp only at hs ht
  simp only [FK, MK, twoTimeR]
  have hG : 0 < (Real.Gamma a)⁻¹ := inv_pos.2 (Real.Gamma_pos_of_pos ha)
  have hl : 0 ≤ |l| ^ (a - 1) := Real.rpow_nonneg (abs_nonneg _) _
  have hW := abs_waveHat_mul_le s t ξ
  rw [abs_of_pos hs, abs_of_pos ht] at hW
  have hm : 0 < 1 / (1 + ‖ξ‖ ^ 2) := by positivity
  have hes := one_add_le_exp θ s hθ hs.le
  have het := one_add_le_exp θ t hθ ht.le
  set E := Real.exp (-(θ * (s + t)) - |l| * |s - t|)
  have hE : E * (Real.exp (θ * s / 2) * Real.exp (θ * t / 2)) =
      Real.exp (-(θ / 2 * (s + t)) - |l| * |s - t|) := by
    simp only [E, ← Real.exp_add]; congr 1; ring
  have hEpos : 0 < E := Real.exp_pos _
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity :
    0 ≤ (Real.Gamma a)⁻¹ * |l| ^ (a - 1) * E)]
  have key : E * |waveHat s ξ * waveHat t ξ| ≤
      2 * (1 + 2 / θ) ^ 2 * (1 / (1 + ‖ξ‖ ^ 2)) *
        Real.exp (-(θ / 2 * (s + t)) - |l| * |s - t|) := by
    rw [← hE]
    have hst : (1 + s) * (1 + t) ≤
        (1 + 2 / θ) ^ 2 * (Real.exp (θ * s / 2) * Real.exp (θ * t / 2)) := by
      have := mul_le_mul hes het (by linarith) (by positivity)
      nlinarith
    calc E * |waveHat s ξ * waveHat t ξ|
        ≤ E * (2 * (1 + s) * (1 + t) * (1 / (1 + ‖ξ‖ ^ 2))) :=
          mul_le_mul_of_nonneg_left hW hEpos.le
      _ = 2 * (1 / (1 + ‖ξ‖ ^ 2)) * E * ((1 + s) * (1 + t)) := by ring
      _ ≤ 2 * (1 / (1 + ‖ξ‖ ^ 2)) * E *
          ((1 + 2 / θ) ^ 2 * (Real.exp (θ * s / 2) * Real.exp (θ * t / 2))) :=
          mul_le_mul_of_nonneg_left hst (by positivity)
      _ = _ := by ring
  calc (Real.Gamma a)⁻¹ * |l| ^ (a - 1) * E * |waveHat s ξ * waveHat t ξ|
      = (Real.Gamma a)⁻¹ * |l| ^ (a - 1) * (E * |waveHat s ξ * waveHat t ξ|) := by ring
    _ ≤ (Real.Gamma a)⁻¹ * |l| ^ (a - 1) * (2 * (1 + 2 / θ) ^ 2 * (1 / (1 + ‖ξ‖ ^ 2)) *
        Real.exp (-(θ / 2 * (s + t)) - |l| * |s - t|)) :=
        mul_le_mul_of_nonneg_left key (by positivity)
    _ = _ := by ring

/-- Auxiliary to the Lean proof route. -/
theorem MK_integrable (μ : Measure (Rd d)) [SFinite μ]
    (hR : Integrable (fun ξ : Rd d => 1 / (1 + ‖ξ‖ ^ 2)) μ)
    (a θ : ℝ) (ha0 : 0 < a) (ha1 : a < 1) (hθ : 0 < θ) :
    Integrable (MK (d := d) a θ) (L0.prod (μ.prod P2)) := by
  set K := (Real.Gamma a)⁻¹ * (2 * (1 + 2 / θ) ^ 2) with hK_def
  have hK : 0 ≤ K := by
    have := Real.Gamma_pos_of_pos ha0; positivity
  have hmeas : Measurable (MK (d := d) a θ) := by
    unfold MK twoTimeR; fun_prop
  have hnn : ∀ z, 0 ≤ MK (d := d) a θ z := fun z => by
    unfold MK twoTimeR; positivity
  refine ⟨hmeas.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal
    (Eventually.of_forall hnn)).2 ?_⟩
  have hT := lintegral_triple_twoTime L0 μ
    (fun l ξ => K * |l| ^ (a - 1) * (1 / (1 + ‖ξ‖ ^ 2))) (fun _ _ => θ / 2)
    (fun l _ => |l|) (by fun_prop) (by fun_prop) (by fun_prop)
    (fun l ξ => by positivity) (fun _ _ => by positivity) (fun _ _ => abs_nonneg _)
  have hfun : (fun z : ℝ × (Rd d × (ℝ × ℝ)) => ENNReal.ofReal (MK a θ z)) =
      fun z => ENNReal.ofReal (K * |z.1| ^ (a - 1) * (1 / (1 + ‖z.2.1‖ ^ 2)) *
        twoTimeR (θ / 2) |z.1| z.2.2) := by
    funext z; simp only [MK, hK_def]
  rw [hfun, hT]
  have hsplit : ∀ l : ℝ, ∀ ξ : Rd d,
      ENNReal.ofReal (K * |l| ^ (a - 1) * (1 / (1 + ‖ξ‖ ^ 2)) /
        (θ / 2 * (θ / 2 + |l|))) =
      ENNReal.ofReal (K * |l| ^ (a - 1) / (θ / 2 * (θ / 2 + |l|))) *
        ENNReal.ofReal (1 / (1 + ‖ξ‖ ^ 2)) := by
    intro l ξ
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    ring
  simp_rw [hsplit]
  have hm : Measurable fun ξ : Rd d => ENNReal.ofReal (1 / (1 + ‖ξ‖ ^ 2)) := by fun_prop
  simp_rw [lintegral_const_mul _ hm]
  rw [lintegral_mul_const _ (by fun_prop)]
  exact ENNReal.mul_lt_top
    (integrable_rpow_div a (θ / 2) K ha0 ha1 (by positivity) hK).lintegral_lt_top
    hR.lintegral_lt_top

/-- Auxiliary to the Lean proof route. The subordinated integrand is integrable on
`(0,∞) × ℝ^d × (0,∞)²`. -/
theorem FK_integrable (μ : Measure (Rd d)) [SFinite μ]
    (hR : Integrable (fun ξ : Rd d => 1 / (1 + ‖ξ‖ ^ 2)) μ)
    (a θ : ℝ) (ha0 : 0 < a) (ha1 : a < 1) (hθ : 0 < θ) :
    Integrable (FK (d := d) a θ) (L0.prod (μ.prod P2)) := by
  refine Integrable.mono' (MK_integrable μ hR a θ ha0 ha1 hθ)
    (FK_measurable a θ).aestronglyMeasurable ?_
  filter_upwards [ae_triple μ] with z hz
  exact FK_le_MK a θ ha0 hθ z hz.2.1 hz.2.2.1

/-- Auxiliary to the Lean proof route. The `λ`-integral of the subordinated integrand is the `N₂`
integrand, for
`s, t > 0`, `s ≠ t`. -/
theorem integral_FK_eq (a θ : ℝ) (ha0 : 0 < a) (ξ : Rd d) (p : ℝ × ℝ) (hst : p.1 ≠ p.2) :
    ∫ l in Ioi (0 : ℝ), FK a θ (l, (ξ, p)) = N2integrand a θ (p, ξ) := by
  have hr : 0 < |p.1 - p.2| := abs_pos.2 (sub_ne_zero.2 hst)
  rw [setIntegral_congr_fun measurableSet_Ioi (g := fun l =>
    (Real.exp (-(θ * (p.1 + p.2))) * (waveHat p.1 ξ * waveHat p.2 ξ) * (Real.Gamma a)⁻¹) *
      subKernel a |p.1 - p.2| l) ?_]
  · rw [integral_const_mul, N2integrand, rpow_neg_eq_subordination a _ ha0 hr]
    ring
  · intro l hl
    simp only [FK, twoTimeR, subKernel, abs_of_pos (show (0 : ℝ) < l from hl)]
    rw [show -(θ * (p.1 + p.2)) - l * |p.1 - p.2| = -(θ * (p.1 + p.2)) + -(|p.1 - p.2| * l)
      by ring, Real.exp_add]
    ring

/-! ### Finiteness -/

/-- Absolute integrability of the displayed spectral formula for `N₂(θ)²`
on `(0,∞)² × ℝ^d`. -/
theorem N2integrand_integrable (μ : Measure (Rd d)) [SFinite μ]
    (hR : Integrable (fun ξ : Rd d => 1 / (1 + ‖ξ‖ ^ 2)) μ)
    (a θ : ℝ) (ha0 : 0 < a) (ha1 : a < 1) (hθ : 0 < θ) :
    Integrable (N2integrand (d := d) a θ) (P2.prod μ) := by
  have hG := (FK_integrable μ hR a θ ha0 ha1 hθ).integral_prod_right
  have hae : (fun yz : Rd d × (ℝ × ℝ) => ∫ l, FK a θ (l, yz) ∂L0) =ᵐ[μ.prod P2]
      fun yz => N2integrand a θ (yz.2, yz.1) := by
    filter_upwards [Measure.quasiMeasurePreserving_snd.ae ae_P2] with yz hyz
    exact integral_FK_eq a θ ha0 yz.1 yz.2 hyz.2.2
  exact (hG.congr hae).swap

/-- The outer integrand of `N₂(θ)²` is integrable on `(0,∞)²`, so `N2sq` is a
genuine (finite) integral. -/
theorem N2_outer_integrable (μ : Measure (Rd d)) [SFinite μ]
    (hR : Integrable (fun ξ : Rd d => 1 / (1 + ‖ξ‖ ^ 2)) μ)
    (a θ : ℝ) (ha0 : 0 < a) (ha1 : a < 1) (hθ : 0 < θ) :
    Integrable (fun p : ℝ × ℝ => Real.exp (-(θ * (p.1 + p.2))) * |p.1 - p.2| ^ (-a) *
      ∫ ξ, waveHat p.1 ξ * waveHat p.2 ξ ∂μ) P2 := by
  refine (N2integrand_integrable μ hR a θ ha0 ha1 hθ).integral_prod_left.congr
    (Eventually.of_forall fun p => ?_)
  simp only [N2integrand]
  rw [integral_const_mul]

/-- The integrand of `N₁(θ)` is integrable on `(0,∞)`, given the homogeneity. -/
theorem N1_integrable {alpha : ℝ} (μ : Measure (Rd d)) (hI : SpectralHomogeneous μ alpha)
    (a θ : ℝ) (ha0 : 0 < a) (hθ : 0 < θ) (hthr : a + alpha < 2) :
    Integrable (fun l : ℝ => l ^ (a - 1) * resolvent μ (θ + l)) L0 := by
  have hR1 : 0 ≤ resolvent μ 1 := integral_nonneg fun ξ => by positivity
  have heq : (fun l : ℝ => l ^ (a - 1) * resolvent μ (θ + l)) =ᵐ[L0]
      fun l => l ^ (a - 1) * ((θ + l) ^ (alpha - 2) * resolvent μ 1) := by
    filter_upwards [ae_L0_pos] with l hl
    rw [resolvent_homog hI (θ + l) (by linarith)]
  refine Integrable.congr ?_ heq.symm
  refine integrable_of_rpow_bounds (a - 1) (a + alpha - 3)
    (resolvent μ 1 * (θ ^ (alpha - 2) + 1)) (by linarith) (by linarith)
    (by fun_prop : Measurable fun l : ℝ =>
      l ^ (a - 1) * ((θ + l) ^ (alpha - 2) * resolvent μ 1)).aestronglyMeasurable ?_ ?_
  · intro l hl _
    have hp := Real.rpow_nonneg hl.le (a - 1)
    have hq : (θ + l) ^ (alpha - 2) ≤ θ ^ (alpha - 2) :=
      Real.rpow_le_rpow_of_nonpos hθ (by linarith) (by linarith)
    rw [Real.norm_of_nonneg (by positivity)]
    have hθp := Real.rpow_nonneg hθ.le (alpha - 2)
    nlinarith [mul_le_mul_of_nonneg_left hq (mul_nonneg hp hR1)]
  · intro l hl
    have hl0 : 0 < l := lt_trans zero_lt_one hl
    have hq : (θ + l) ^ (alpha - 2) ≤ l ^ (alpha - 2) :=
      Real.rpow_le_rpow_of_nonpos hl0 (by linarith) (by linarith)
    have hp := Real.rpow_nonneg hl0.le (a - 1)
    have he : l ^ (a + alpha - 3) = l ^ (a - 1) * l ^ (alpha - 2) := by
      rw [← Real.rpow_add hl0]; ring_nf
    rw [Real.norm_of_nonneg (by positivity), he]
    have hθp := Real.rpow_nonneg hθ.le (alpha - 2)
    have hlp := Real.rpow_nonneg hl0.le (alpha - 2)
    nlinarith [mul_le_mul_of_nonneg_left hq (mul_nonneg hp hR1),
      mul_nonneg (mul_nonneg hR1 hθp) (mul_nonneg hp hlp)]

/-- Finiteness part of `L:damped-homogeneous-norms` (lines 803-919) with the
manuscript's hypothesis `H:homog` (temporal exponent `a = α₀`) and the supplied
spectral homogeneity: for every `θ > 0` the spectral formula for `N₂(θ)²` is
absolutely integrable on `(0,∞)² × ℝ^d`, its outer integrand is integrable on
`(0,∞)²`, and the integrand of `N₁(θ)` is integrable on `(0,∞)`. -/
theorem damped_norms_finite_paper {alpha alpha0 : ℝ} {Γ μ : Measure (Rd d)}
    (h : HomogCovariance d alpha alpha0 Γ μ) (hI : SpectralHomogeneous μ alpha)
    (θ : ℝ) (hθ : 0 < θ) :
    Integrable (N2integrand (d := d) alpha0 θ) (P2.prod μ) ∧
      Integrable (fun p : ℝ × ℝ => Real.exp (-(θ * (p.1 + p.2))) * |p.1 - p.2| ^ (-alpha0) *
        ∫ ξ, waveHat p.1 ξ * waveHat p.2 ξ ∂μ) P2 ∧
      Integrable (fun l : ℝ => l ^ (alpha0 - 1) * resolvent μ (θ + l)) L0 := by
  have := h.μ_radon
  have ha2 : alpha < 2 := by linarith [h.threshold, h.alpha0_pos]
  have hR := integrable_inv_one_add_sq hI ha2
  exact ⟨N2integrand_integrable μ hR alpha0 θ h.alpha0_pos h.alpha0_lt_one hθ,
    N2_outer_integrable μ hR alpha0 θ h.alpha0_pos h.alpha0_lt_one hθ,
    N1_integrable μ hI alpha0 θ h.alpha0_pos hθ (by linarith [h.threshold])⟩

end StratonovichHAMSecondMoment.DampedNorms
