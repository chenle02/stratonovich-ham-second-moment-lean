module

/-
Copyright 2026 Le Chen. SPDX-License-Identifier: Apache-2.0

Lemma `L:white-clock-laplace` (White-space low-order Laplace transforms) of
`notes/notes_stratonovich_ham_second_moment.tex` at revision `a284420`
(section `S:two-clock-screen`): statement lines 7645--7671, with the displays
`E:white-cross-clock-transform` (lines 7648--7659), the diagonal value (lines
7660--7661) and `E:white-self-clock-transform` (lines 7663--7670); proof lines
7673--7696.  The section's standing case (lines 7640--7643) is `d = α = 1`,
`Γ = δ_0`, `0 < a < 1` and `G_s(y) = (1/2) 1_{|y|<s}`.

What is formalized, in full:
* `E:white-cross-clock-transform`: for `0 < a < 1` and `θ₁, θ₂ > 0` the
  integrand `e^{-θ₁ s - θ₂ t} |s-t|^{-a} min(s,t)/2` is integrable on the open
  quadrant `(0,∞)²`, its integral over the quadrant and its iterated integral
  `∫_0^∞ (∫_0^∞ · ds) dt` (the TeX order) both equal
  `Γ_E(1-a)/(2(θ₁+θ₂)²) (θ₁^{a-1} + θ₂^{a-1})`;
* the diagonal value `K_×(θ,θ) = Γ_E(1-a)/(4 θ^{3-a})`;
* `E:white-self-clock-transform`: the integrand
  `e^{-η₁ r₁ - η₂ r₂} r₂^{-a} r₁/2` is integrable on the quadrant and its
  quadrant and iterated (`∫_0^∞ (∫_0^∞ · dr₁) dr₂`) integrals equal
  `Γ_E(1-a)/(2 η₁² η₂^{1-a})`;
* the two Green-factor steps of the proof: `∫ G_s G_t = min(s,t)/2`
  (lines 7674--7679) and `G_{r₂}(0) = 1/2`, `∫ G_{r₁} = r₁` (lines 7691--7693).

Conventions and side conditions made explicit here:
* `Γ_E` is Mathlib's `Real.Gamma`; powers are `Real.rpow`.
* The self transform's damping parameters `η₁, η₂` are not given a sign in the
  TeX (line 7662, "independent gap damping"); the integral converges only for
  `η₁, η₂ > 0`, which is made an explicit hypothesis.
* Every integral conclusion carries integrability on the quadrant (the Bochner
  integral of a non-integrable function is `0` in Lean); the iterated integral
  then equals the quadrant integral by Fubini.
* At `s = t` Lean's `|s-t|^{-a} = 0^{-a}` is `0`; the diagonal is a null set, so
  the value is irrelevant to the integral.  The Lean proof uses this value only
  to split the quadrant pointwise (no statement depends on it).
* In the Green-factor step the `δ_0`-pairing `∫∫ G_s(y)G_t(z)δ_0(y-z) dy dz` is
  read, as in the TeX, as the diagonal integral `∫ G_s(y)G_t(y) dy`; Lean proves
  the remaining equality with `min(s,t)/2`.
* The standing `Γ = δ_0` and `d = α = 1` enter only through the Green-factor
  steps; the displayed transforms are explicit real integrals, so no covariance
  hypothesis (`H:homog`) is carried.

Proof route: the TeX splits the time integral into `s = t + v` and `t = s + v`
and separates by Tonelli.  Lean does the same on the quadrant: the half
`{0 < t < s}` is the image of `(0,∞)²` under the measure-preserving shear
`(v,t) ↦ (v+t, t)` (`measurePreserving_add_prod`), the half `{0 < s < t}` is
reduced to the first by the coordinate swap (exchanging `θ₁` and `θ₂`), and each
product integral is computed by `integral_prod_mul` and the Gamma integral
`integral_rpow_mul_exp_neg_mul_rpow`.  In the section "Auxiliary",
`laplace_id` and `laplace_rpow` are the two elementary integrals of the TeX
proof (lines 7683--7687); the other helpers there serve only this Lean route
and are not TeX steps.
-/
public import Mathlib

@[expose] public section

noncomputable section

set_option autoImplicit false

open MeasureTheory Set Real

namespace StratonovichHAMSecondMoment.WhiteClockLaplace

/-! ### Auxiliary: one-dimensional Laplace integrals and the quadrant product -/

/-- Step of the TeX proof of `L:white-clock-laplace` (the first elementary integral of TeX lines
7683--7685): for `c > 0`, `t e^{-ct}` is integrable on `(0,∞)` and
`∫_0^∞ t e^{-ct} dt = c^{-2}`. -/
theorem laplace_id {c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun t : ℝ => t * exp (-(c * t))) (Ioi 0) ∧
      ∫ t in Ioi (0:ℝ), t * exp (-(c * t)) = (c ^ 2)⁻¹ := by
  have hcongr : ∀ t ∈ Ioi (0:ℝ),
      t ^ (1:ℝ) * exp (-c * t ^ (1:ℝ)) = t * exp (-(c * t)) := by
    intro t _; simp [rpow_one, neg_mul]
  refine ⟨(integrableOn_rpow_mul_exp_neg_mul_rpow (by norm_num) one_pos hc).congr_fun hcongr
    measurableSet_Ioi, ?_⟩
  rw [← setIntegral_congr_fun measurableSet_Ioi hcongr,
    integral_rpow_mul_exp_neg_mul_rpow one_pos (by norm_num) hc]
  rw [show (-((1:ℝ) + 1) / 1) = -((2:ℕ):ℝ) by norm_num, show ((1:ℝ) + 1) / 1 = 2 by norm_num,
    rpow_neg hc.le, rpow_natCast, Gamma_two]
  ring

/-- Step of the TeX proof of `L:white-clock-laplace` (the second elementary integral of TeX lines
7686--7687): for `a < 1` and `θ > 0`, `v^{-a} e^{-θ v}` is integrable on
`(0,∞)` and `∫_0^∞ v^{-a} e^{-θ v} dv = Γ_E(1-a) θ^{a-1}`. -/
theorem laplace_rpow {a θ : ℝ} (ha : a < 1) (hθ : 0 < θ) :
    IntegrableOn (fun v : ℝ => v ^ (-a) * exp (-(θ * v))) (Ioi 0) ∧
      ∫ v in Ioi (0:ℝ), v ^ (-a) * exp (-(θ * v)) = Gamma (1 - a) * θ ^ (a - 1) := by
  have hcongr : ∀ v ∈ Ioi (0:ℝ),
      v ^ (-a) * exp (-θ * v ^ (1:ℝ)) = v ^ (-a) * exp (-(θ * v)) := by
    intro v _; simp [rpow_one, neg_mul]
  refine ⟨(integrableOn_rpow_mul_exp_neg_mul_rpow (by linarith) one_pos hθ).congr_fun hcongr
    measurableSet_Ioi, ?_⟩
  rw [← setIntegral_congr_fun measurableSet_Ioi hcongr,
    integral_rpow_mul_exp_neg_mul_rpow one_pos (by linarith) hθ]
  rw [show (-(-a + 1) / 1) = a - 1 by ring, show (-a + 1) / 1 = 1 - a by ring]
  ring

/-- Auxiliary (Lean route): Lebesgue measure on the open quadrant is the product
of the restricted Lebesgue measures on `(0,∞)`. -/
theorem volume_restrict_quadrant :
    (volume : Measure (ℝ × ℝ)).restrict (Ioi 0 ×ˢ Ioi 0) =
      (volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ))) := by
  rw [Measure.prod_restrict, Measure.volume_eq_prod]

/-- Auxiliary (Lean route; the Tonelli separation of TeX line 7688): for `f, g`
integrable on `(0,∞)`, `f(x) g(y)` is integrable on the quadrant and its integral
is `(∫_0^∞ f)(∫_0^∞ g)`. -/
theorem quadrant_mul {f g : ℝ → ℝ} (hf : IntegrableOn f (Ioi 0)) (hg : IntegrableOn g (Ioi 0)) :
    IntegrableOn (fun z : ℝ × ℝ => f z.1 * g z.2) (Ioi 0 ×ˢ Ioi 0) ∧
      ∫ z in Ioi (0:ℝ) ×ˢ Ioi (0:ℝ), f z.1 * g z.2 =
        (∫ x in Ioi (0:ℝ), f x) * ∫ y in Ioi (0:ℝ), g y := by
  refine ⟨?_, ?_⟩
  · change Integrable _ ((volume : Measure (ℝ × ℝ)).restrict (Ioi 0 ×ˢ Ioi 0))
    rw [volume_restrict_quadrant]
    exact hf.mul_prod hg
  · rw [volume_restrict_quadrant]
    exact integral_prod_mul f g

/-- Auxiliary (Lean route): an integral over the open quadrant is the iterated
integral `∫_0^∞ (∫_0^∞ F(x,y) dx) dy` (inner integral in the first variable),
for `F` integrable on the quadrant. -/
theorem quadrant_iterated {F : ℝ × ℝ → ℝ} (hF : IntegrableOn F (Ioi 0 ×ˢ Ioi 0)) :
    ∫ z in Ioi (0:ℝ) ×ˢ Ioi (0:ℝ), F z = ∫ y in Ioi (0:ℝ), ∫ x in Ioi (0:ℝ), F (x, y) := by
  have hF' : Integrable F ((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ)))) := by
    rw [← volume_restrict_quadrant]; exact hF
  rw [volume_restrict_quadrant]
  exact integral_prod_symm F hF'

/-! ### The cross-pair transform `E:white-cross-clock-transform` -/

/-- The integrand of `E:white-cross-clock-transform` (TeX line 7652) at
`p = (s, t)`: `e^{-θ₁ s - θ₂ t} |s-t|^{-a} min(s,t)/2`. -/
def crossIntegrand (a θ₁ θ₂ : ℝ) (p : ℝ × ℝ) : ℝ :=
  exp (-θ₁ * p.1 - θ₂ * p.2) * |p.1 - p.2| ^ (-a) * (min p.1 p.2 / 2)

/-- The right side of `E:white-cross-clock-transform` (TeX lines 7654--7656):
`Γ_E(1-a)/(2(θ₁+θ₂)²) (θ₁^{a-1} + θ₂^{a-1})`. -/
def crossValue (a θ₁ θ₂ : ℝ) : ℝ :=
  Gamma (1 - a) / (2 * (θ₁ + θ₂) ^ 2) * (θ₁ ^ (a - 1) + θ₂ ^ (a - 1))

/-- Auxiliary (Lean route): the half `{0 < t < s}` of the quadrant (the TeX part
`s = t + v`, `v > 0`, line 7680). -/
def upperHalf : Set (ℝ × ℝ) := {p | 0 < p.2 ∧ p.2 < p.1}

/-- Auxiliary (Lean route): the half `{0 < s < t}` of the quadrant (the TeX part
`t = s + v`, `v > 0`, line 7680). -/
def lowerHalf : Set (ℝ × ℝ) := {p | 0 < p.1 ∧ p.1 < p.2}

/-- Auxiliary (Lean route): `upperHalf` is measurable. -/
theorem measurableSet_upperHalf : MeasurableSet upperHalf :=
  (measurableSet_lt measurable_const measurable_snd).inter
    (measurableSet_lt measurable_snd measurable_fst)

/-- Auxiliary (Lean route): `lowerHalf` is measurable. -/
theorem measurableSet_lowerHalf : MeasurableSet lowerHalf :=
  (measurableSet_lt measurable_const measurable_fst).inter
    (measurableSet_lt measurable_fst measurable_snd)

/-- Auxiliary (Lean route): the coordinate swap exchanges `θ₁` and `θ₂`. -/
theorem crossIntegrand_swap (a θ₁ θ₂ : ℝ) (p : ℝ × ℝ) :
    crossIntegrand a θ₂ θ₁ p.swap = crossIntegrand a θ₁ θ₂ p := by
  simp only [crossIntegrand, Prod.fst_swap, Prod.snd_swap]
  rw [abs_sub_comm, min_comm]
  congr 3
  ring

/-- Auxiliary (Lean route): the shear `(v, t) ↦ (v + t, t)` preserves Lebesgue
measure on `ℝ²`. -/
theorem shear_measurePreserving :
    MeasurePreserving (fun z : ℝ × ℝ => (z.1 + z.2, z.2)) volume volume := by
  rw [Measure.volume_eq_prod]
  exact measurePreserving_add_prod volume volume

/-- Auxiliary (Lean route): the shear `(v, t) ↦ (v + t, t)` is a measurable
embedding. -/
theorem shear_measurableEmbedding :
    MeasurableEmbedding (fun z : ℝ × ℝ => (z.1 + z.2, z.2)) := by
  refine MeasurableEmbedding.of_measurable_inverse (g := fun z : ℝ × ℝ => (z.1 - z.2, z.2))
    (by fun_prop) ?_ (by fun_prop) (fun z => by simp)
  have : range (fun z : ℝ × ℝ => (z.1 + z.2, z.2)) = univ :=
    range_eq_univ.2 fun z => ⟨(z.1 - z.2, z.2), by simp⟩
  rw [this]; exact MeasurableSet.univ

/-- Auxiliary (Lean route): the coordinate swap is a measurable embedding. -/
theorem swap_measurableEmbedding : MeasurableEmbedding (Prod.swap : ℝ × ℝ → ℝ × ℝ) :=
  MeasurableEmbedding.of_measurable_inverse (g := Prod.swap) measurable_swap
    (by rw [range_eq_univ.2 Prod.swap_surjective]; exact MeasurableSet.univ)
    measurable_swap (fun z => by simp)

/-- Auxiliary (Lean route): the preimage of `upperHalf` under the shear is the
open quadrant. -/
theorem shear_preimage_upperHalf :
    (fun z : ℝ × ℝ => (z.1 + z.2, z.2)) ⁻¹' upperHalf = Ioi 0 ×ˢ Ioi 0 := by
  ext ⟨v, t⟩
  simp only [upperHalf, mem_preimage, mem_prod, mem_Ioi]
  change 0 < t ∧ t < v + t ↔ 0 < v ∧ 0 < t
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨by linarith, h1⟩
  · rintro ⟨h1, h2⟩; exact ⟨h2, by linarith⟩

/-- Auxiliary (Lean route): on the quadrant, the sheared cross integrand is the
product `[v^{-a} e^{-θ₁ v}] · [t e^{-(θ₁+θ₂) t}/2]`. -/
theorem crossIntegrand_shear (a θ₁ θ₂ : ℝ) {z : ℝ × ℝ} (hz : z ∈ Ioi (0:ℝ) ×ˢ Ioi (0:ℝ)) :
    crossIntegrand a θ₁ θ₂ (z.1 + z.2, z.2) =
      z.1 ^ (-a) * exp (-(θ₁ * z.1)) * (z.2 * exp (-((θ₁ + θ₂) * z.2)) / 2) := by
  obtain ⟨hv, ht⟩ := hz
  simp only [mem_Ioi] at hv ht
  simp only [crossIntegrand]
  rw [show z.1 + z.2 - z.2 = z.1 by ring, abs_of_pos hv, min_eq_right (by linarith),
    show -θ₁ * (z.1 + z.2) - θ₂ * z.2 = -(θ₁ * z.1) + -((θ₁ + θ₂) * z.2) by ring, exp_add]
  ring

/-- Auxiliary (Lean route; one half of the TeX split, lines 7680--7687): on
`{0 < t < s}` the cross integrand is integrable with integral
`Γ_E(1-a) θ₁^{a-1} / (2(θ₁+θ₂)²)`. -/
theorem cross_upperHalf {a θ₁ θ₂ : ℝ} (ha1 : a < 1) (hθ₁ : 0 < θ₁) (hθ₂ : 0 < θ₂) :
    IntegrableOn (crossIntegrand a θ₁ θ₂) upperHalf ∧
      ∫ p in upperHalf, crossIntegrand a θ₁ θ₂ p =
        Gamma (1 - a) * θ₁ ^ (a - 1) / (2 * (θ₁ + θ₂) ^ 2) := by
  have hc : 0 < θ₁ + θ₂ := by linarith
  obtain ⟨hgI, hgV⟩ := laplace_rpow ha1 hθ₁
  obtain ⟨hhI, hhV⟩ := laplace_id hc
  obtain ⟨hPI, hPV⟩ := quadrant_mul hgI (hhI.div_const 2)
  have hcongr : ∀ z ∈ Ioi (0:ℝ) ×ˢ Ioi (0:ℝ),
      (crossIntegrand a θ₁ θ₂ ∘ fun z : ℝ × ℝ => (z.1 + z.2, z.2)) z =
        z.1 ^ (-a) * exp (-(θ₁ * z.1)) * (z.2 * exp (-((θ₁ + θ₂) * z.2)) / 2) :=
    fun z hz => crossIntegrand_shear a θ₁ θ₂ hz
  have hS : MeasurableSet (Ioi (0:ℝ) ×ˢ Ioi (0:ℝ)) := measurableSet_Ioi.prod measurableSet_Ioi
  refine ⟨?_, ?_⟩
  · rw [← shear_measurePreserving.integrableOn_comp_preimage shear_measurableEmbedding,
      shear_preimage_upperHalf]
    exact hPI.congr_fun (fun z hz => (hcongr z hz).symm) hS
  · rw [← shear_measurePreserving.setIntegral_preimage_emb shear_measurableEmbedding,
      shear_preimage_upperHalf]
    rw [setIntegral_congr_fun hS (fun z hz => crossIntegrand_shear a θ₁ θ₂ hz), hPV,
      integral_div, hgV, hhV]
    field_simp

/-- Auxiliary (Lean route; the other half of the TeX split): on `{0 < s < t}` the
cross integrand is integrable with integral `Γ_E(1-a) θ₂^{a-1} / (2(θ₁+θ₂)²)`. -/
theorem cross_lowerHalf {a θ₁ θ₂ : ℝ} (ha1 : a < 1) (hθ₁ : 0 < θ₁) (hθ₂ : 0 < θ₂) :
    IntegrableOn (crossIntegrand a θ₁ θ₂) lowerHalf ∧
      ∫ p in lowerHalf, crossIntegrand a θ₁ θ₂ p =
        Gamma (1 - a) * θ₂ ^ (a - 1) / (2 * (θ₁ + θ₂) ^ 2) := by
  obtain ⟨hI, hV⟩ := cross_upperHalf (θ₁ := θ₂) (θ₂ := θ₁) ha1 hθ₂ hθ₁
  have hmp : MeasurePreserving (Prod.swap : ℝ × ℝ → ℝ × ℝ) volume volume := by
    rw [Measure.volume_eq_prod]; exact Measure.measurePreserving_swap
  have hpre : (Prod.swap : ℝ × ℝ → ℝ × ℝ) ⁻¹' upperHalf = lowerHalf := by
    ext p; simp [upperHalf, lowerHalf]
  have hfun : (crossIntegrand a θ₂ θ₁ ∘ Prod.swap) = crossIntegrand a θ₁ θ₂ :=
    funext fun p => crossIntegrand_swap a θ₁ θ₂ p
  refine ⟨?_, ?_⟩
  · rw [← hmp.integrableOn_comp_preimage swap_measurableEmbedding, hpre, hfun] at hI
    exact hI
  · rw [← hmp.setIntegral_preimage_emb swap_measurableEmbedding, hpre] at hV
    simp_rw [crossIntegrand_swap] at hV
    rw [hV, add_comm θ₂ θ₁]

/-- Auxiliary (Lean route): on the quadrant the cross integrand is the sum of its
restrictions to the two halves (on the diagonal it is `0`, since `0^{-a} = 0`
for `a ≠ 0`). -/
theorem crossIntegrand_split {a : ℝ} (ha0 : 0 < a) (θ₁ θ₂ : ℝ) :
    ∀ p ∈ Ioi (0:ℝ) ×ˢ Ioi (0:ℝ), crossIntegrand a θ₁ θ₂ p =
      upperHalf.indicator (crossIntegrand a θ₁ θ₂) p +
        lowerHalf.indicator (crossIntegrand a θ₁ θ₂) p := by
  rintro ⟨s, t⟩ ⟨hs, ht⟩
  simp only [mem_Ioi] at hs ht
  rcases lt_trichotomy s t with h | h | h
  · have h1 : (s, t) ∉ upperHalf := fun hp => by simp [upperHalf] at hp; linarith [hp.2]
    have h2 : (s, t) ∈ lowerHalf := ⟨hs, h⟩
    simp [indicator_of_notMem h1, indicator_of_mem h2]
  · subst h
    have h1 : (s, s) ∉ upperHalf := fun hp => lt_irrefl _ hp.2
    have h2 : (s, s) ∉ lowerHalf := fun hp => lt_irrefl _ hp.2
    simp [indicator_of_notMem h1, indicator_of_notMem h2, crossIntegrand,
      zero_rpow (neg_ne_zero.2 ha0.ne')]
  · have h1 : (s, t) ∈ upperHalf := ⟨ht, h⟩
    have h2 : (s, t) ∉ lowerHalf := fun hp => by simp [lowerHalf] at hp; linarith [hp.2]
    simp [indicator_of_mem h1, indicator_of_notMem h2]

/-- `E:white-cross-clock-transform` (TeX lines 7648--7659), quadrant form: for
`0 < a < 1` and `θ₁, θ₂ > 0` the cross integrand is integrable on the open
quadrant and its integral there is `Γ_E(1-a)/(2(θ₁+θ₂)²)(θ₁^{a-1}+θ₂^{a-1})`. -/
theorem cross_transform {a θ₁ θ₂ : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hθ₁ : 0 < θ₁)
    (hθ₂ : 0 < θ₂) :
    IntegrableOn (crossIntegrand a θ₁ θ₂) (Ioi 0 ×ˢ Ioi 0) ∧
      ∫ p in Ioi (0:ℝ) ×ˢ Ioi (0:ℝ), crossIntegrand a θ₁ θ₂ p = crossValue a θ₁ θ₂ := by
  obtain ⟨hUI, hUV⟩ := cross_upperHalf ha1 hθ₁ hθ₂
  obtain ⟨hLI, hLV⟩ := cross_lowerHalf ha1 hθ₁ hθ₂
  have hS : MeasurableSet (Ioi (0:ℝ) ×ˢ Ioi (0:ℝ)) := measurableSet_Ioi.prod measurableSet_Ioi
  have hU : IntegrableOn (upperHalf.indicator (crossIntegrand a θ₁ θ₂)) (Ioi 0 ×ˢ Ioi 0) :=
    ((integrable_indicator_iff measurableSet_upperHalf).2 hUI).integrableOn
  have hL : IntegrableOn (lowerHalf.indicator (crossIntegrand a θ₁ θ₂)) (Ioi 0 ×ˢ Ioi 0) :=
    ((integrable_indicator_iff measurableSet_lowerHalf).2 hLI).integrableOn
  have hsplit := crossIntegrand_split ha0 θ₁ θ₂
  have hUsub : Ioi (0:ℝ) ×ˢ Ioi (0:ℝ) ∩ upperHalf = upperHalf :=
    inter_eq_right.2 fun p hp => ⟨lt_trans hp.1 hp.2, hp.1⟩
  have hLsub : Ioi (0:ℝ) ×ˢ Ioi (0:ℝ) ∩ lowerHalf = lowerHalf :=
    inter_eq_right.2 fun p hp => ⟨hp.1, lt_trans hp.1 hp.2⟩
  refine ⟨(hU.add hL).congr_fun (fun p hp => (hsplit p hp).symm) hS, ?_⟩
  rw [setIntegral_congr_fun hS hsplit, integral_add hU hL,
    setIntegral_indicator measurableSet_upperHalf, setIntegral_indicator measurableSet_lowerHalf,
    hUsub, hLsub, hUV, hLV, crossValue]
  ring

/-- `E:white-cross-clock-transform` (TeX lines 7648--7659), iterated form in the
TeX order `∫_0^∞ (∫_0^∞ · ds) dt`, together with integrability on the quadrant. -/
theorem cross_transform_iterated {a θ₁ θ₂ : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hθ₁ : 0 < θ₁)
    (hθ₂ : 0 < θ₂) :
    IntegrableOn (crossIntegrand a θ₁ θ₂) (Ioi 0 ×ˢ Ioi 0) ∧
      ∫ t in Ioi (0:ℝ), ∫ s in Ioi (0:ℝ), crossIntegrand a θ₁ θ₂ (s, t) =
        crossValue a θ₁ θ₂ := by
  obtain ⟨hI, hV⟩ := cross_transform ha0 ha1 hθ₁ hθ₂
  exact ⟨hI, (quadrant_iterated hI).symm.trans hV⟩

/-- The diagonal value (TeX lines 7660--7661):
`K_×(θ,θ) = Γ_E(1-a)/(4 θ^{3-a})` for `θ > 0`. -/
theorem crossValue_diag (a : ℝ) {θ : ℝ} (hθ : 0 < θ) :
    crossValue a θ θ = Gamma (1 - a) / (4 * θ ^ (3 - a)) := by
  have h : θ ^ (a - 1) * θ ^ (3 - a) = θ ^ 2 := by
    rw [← rpow_add hθ, show a - 1 + (3 - a) = ((2:ℕ):ℝ) by norm_num, rpow_natCast]
  have h3 : 0 < θ ^ (3 - a) := rpow_pos_of_pos hθ _
  unfold crossValue
  field_simp
  linear_combination (4 * Gamma (1 - a)) * h

/-! ### The self-pair transform `E:white-self-clock-transform` -/

/-- The integrand of `E:white-self-clock-transform` (TeX line 7666) at
`p = (r₁, r₂)`: `e^{-η₁ r₁ - η₂ r₂} r₂^{-a} r₁/2`. -/
def selfIntegrand (a η₁ η₂ : ℝ) (p : ℝ × ℝ) : ℝ :=
  exp (-η₁ * p.1 - η₂ * p.2) * p.2 ^ (-a) * (p.1 / 2)

/-- The right side of `E:white-self-clock-transform` (TeX lines 7668--7669):
`Γ_E(1-a)/(2 η₁² η₂^{1-a})`. -/
def selfValue (a η₁ η₂ : ℝ) : ℝ := Gamma (1 - a) / (2 * η₁ ^ 2 * η₂ ^ (1 - a))

/-- `E:white-self-clock-transform` (TeX lines 7663--7670), quadrant and iterated
(`∫_0^∞ (∫_0^∞ · dr₁) dr₂`, the TeX order) forms: for `a < 1` and `η₁, η₂ > 0`
the self integrand is integrable on the quadrant and both integrals equal
`Γ_E(1-a)/(2 η₁² η₂^{1-a})`.  (`a > 0` is not needed here.) -/
theorem self_transform {a η₁ η₂ : ℝ} (ha1 : a < 1) (hη₁ : 0 < η₁) (hη₂ : 0 < η₂) :
    IntegrableOn (selfIntegrand a η₁ η₂) (Ioi 0 ×ˢ Ioi 0) ∧
      ∫ p in Ioi (0:ℝ) ×ˢ Ioi (0:ℝ), selfIntegrand a η₁ η₂ p = selfValue a η₁ η₂ ∧
      ∫ r₂ in Ioi (0:ℝ), ∫ r₁ in Ioi (0:ℝ), selfIntegrand a η₁ η₂ (r₁, r₂) =
        selfValue a η₁ η₂ := by
  obtain ⟨hfI, hfV⟩ := laplace_id hη₁
  obtain ⟨hgI, hgV⟩ := laplace_rpow ha1 hη₂
  obtain ⟨hPI, hPV⟩ := quadrant_mul (hfI.div_const 2) hgI
  have hS : MeasurableSet (Ioi (0:ℝ) ×ˢ Ioi (0:ℝ)) := measurableSet_Ioi.prod measurableSet_Ioi
  have hfun : ∀ p : ℝ × ℝ, selfIntegrand a η₁ η₂ p =
      p.1 * exp (-(η₁ * p.1)) / 2 * (p.2 ^ (-a) * exp (-(η₂ * p.2))) := by
    intro p
    simp only [selfIntegrand]
    rw [show -η₁ * p.1 - η₂ * p.2 = -(η₁ * p.1) + -(η₂ * p.2) by ring, exp_add]
    ring
  have hI : IntegrableOn (selfIntegrand a η₁ η₂) (Ioi 0 ×ˢ Ioi 0) :=
    hPI.congr_fun (fun p _ => (hfun p).symm) hS
  have hV : ∫ p in Ioi (0:ℝ) ×ˢ Ioi (0:ℝ), selfIntegrand a η₁ η₂ p = selfValue a η₁ η₂ := by
    simp_rw [hfun]
    rw [hPV, integral_div, hfV, hgV, selfValue]
    have h : η₂ ^ (a - 1) * η₂ ^ (1 - a) = 1 := by
      rw [← rpow_add hη₂, show a - 1 + (1 - a) = 0 by ring, rpow_zero]
    have h3 : 0 < η₂ ^ (1 - a) := rpow_pos_of_pos hη₂ _
    field_simp
    linear_combination h
  exact ⟨hI, hV, (quadrant_iterated hI).symm.trans hV⟩

/-! ### The Green-factor steps of the proof (TeX lines 7674--7679, 7691--7693) -/

/-- The one-dimensional wave Green function of the section (TeX line 7642):
`G_s(y) = (1/2) 1_{|y| < s}`. -/
def green (s y : ℝ) : ℝ := if |y| < s then 1 / 2 else 0

/-- Proof step (TeX lines 7674--7679): for `s, t ≥ 0`, `G_s G_t` is integrable on
`ℝ` and `∫ G_s(y) G_t(y) dy = min(s,t)/2` (the `δ_0`-pairing read as the
diagonal integral, as in the TeX). -/
theorem green_cross_factor {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    Integrable (fun y => green s y * green t y) ∧
      ∫ y, green s y * green t y = min s t / 2 := by
  have hm : 0 ≤ min s t := le_min hs ht
  have hfun : (fun y => green s y * green t y) =
      (Ioo (-min s t) (min s t)).indicator (fun _ => (1:ℝ) / 4) := by
    funext y
    have hmem : y ∈ Ioo (-min s t) (min s t) ↔ |y| < s ∧ |y| < t := by
      rw [mem_Ioo, ← abs_lt, lt_min_iff]
    by_cases h1 : |y| < s <;> by_cases h2 : |y| < t <;>
      simp [green, h1, h2, indicator, hmem]
    norm_num
  rw [hfun]
  refine ⟨(integrable_indicator_iff measurableSet_Ioo).2 (integrableOn_const
    (by simp [Real.volume_Ioo])), ?_⟩
  rw [integral_indicator measurableSet_Ioo, setIntegral_const, smul_eq_mul,
    measureReal_def, Real.volume_Ioo, ENNReal.toReal_ofReal (by linarith)]
  ring

/-- Proof step (TeX lines 7691--7693): `G_{r₂}(0) = 1/2` for `r₂ > 0`, and for
`r₁ ≥ 0` the first Green factor is integrable with mass `∫ G_{r₁} = r₁`. -/
theorem green_self_factor {r₁ r₂ : ℝ} (hr₁ : 0 ≤ r₁) (hr₂ : 0 < r₂) :
    green r₂ 0 = 1 / 2 ∧ Integrable (green r₁) ∧ ∫ y, green r₁ y = r₁ := by
  have h := green_cross_factor hr₁ hr₁
  have hfun : (fun y => green r₁ y * green r₁ y) = fun y => green r₁ y / 2 := by
    funext y; by_cases h1 : |y| < r₁ <;> simp [green, h1]
    norm_num
  rw [hfun, min_self] at h
  refine ⟨by simp [green, hr₂], ?_, ?_⟩
  · have := h.1.const_mul 2
    refine this.congr (Filter.Eventually.of_forall fun y => ?_)
    simp only; ring
  · have h2 := h.2
    rw [integral_div] at h2
    linarith

/-! ### Lemma `L:white-clock-laplace` under its exact hypotheses -/

/-- Lemma `L:white-clock-laplace` (TeX lines 7645--7671) under the section's
hypothesis `0 < a < 1` (line 7641), `θ₁, θ₂ > 0` (line 7657) and the implicit
`η₁, η₂ > 0` (made explicit):
1. `E:white-cross-clock-transform`: the cross integrand is integrable on the
   quadrant and its iterated integral `∫_0^∞ ∫_0^∞ · ds dt` equals
   `Γ_E(1-a)/(2(θ₁+θ₂)²)(θ₁^{a-1}+θ₂^{a-1})`;
2. the diagonal value: for every `θ > 0`, the same integrability and
   `K_×(θ,θ) = Γ_E(1-a)/(4θ^{3-a})`;
3. `E:white-self-clock-transform`: the self integrand is integrable on the
   quadrant and its iterated integral `∫_0^∞ ∫_0^∞ · dr₁ dr₂` equals
   `Γ_E(1-a)/(2η₁²η₂^{1-a})`. -/
theorem white_clock_laplace_paper {a θ₁ θ₂ η₁ η₂ : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    (hθ₁ : 0 < θ₁) (hθ₂ : 0 < θ₂) (hη₁ : 0 < η₁) (hη₂ : 0 < η₂) :
    (IntegrableOn (crossIntegrand a θ₁ θ₂) (Ioi 0 ×ˢ Ioi 0) ∧
      ∫ t in Ioi (0:ℝ), ∫ s in Ioi (0:ℝ),
          exp (-θ₁ * s - θ₂ * t) * |s - t| ^ (-a) * (min s t / 2) =
        Gamma (1 - a) / (2 * (θ₁ + θ₂) ^ 2) * (θ₁ ^ (a - 1) + θ₂ ^ (a - 1))) ∧
    (∀ θ : ℝ, 0 < θ →
      IntegrableOn (crossIntegrand a θ θ) (Ioi 0 ×ˢ Ioi 0) ∧
        ∫ t in Ioi (0:ℝ), ∫ s in Ioi (0:ℝ),
            exp (-θ * s - θ * t) * |s - t| ^ (-a) * (min s t / 2) =
          Gamma (1 - a) / (4 * θ ^ (3 - a))) ∧
    (IntegrableOn (selfIntegrand a η₁ η₂) (Ioi 0 ×ˢ Ioi 0) ∧
      ∫ r₂ in Ioi (0:ℝ), ∫ r₁ in Ioi (0:ℝ),
          exp (-η₁ * r₁ - η₂ * r₂) * r₂ ^ (-a) * (r₁ / 2) =
        Gamma (1 - a) / (2 * η₁ ^ 2 * η₂ ^ (1 - a))) := by
  refine ⟨cross_transform_iterated ha0 ha1 hθ₁ hθ₂, fun θ hθ => ?_, ?_⟩
  · obtain ⟨hI, hV⟩ := cross_transform_iterated ha0 ha1 hθ hθ
    exact ⟨hI, hV.trans (crossValue_diag a hθ)⟩
  · obtain ⟨hI, -, hV⟩ := self_transform ha1 hη₁ hη₂
    exact ⟨hI, hV⟩

end StratonovichHAMSecondMoment.WhiteClockLaplace
