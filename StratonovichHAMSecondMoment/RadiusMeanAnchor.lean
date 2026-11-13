module

/-
Copyright 2026 Le Chen. SPDX-License-Identifier: Apache-2.0

Proposition `P:radius-mean-anchor` (Averaged block mean tends to zero) of
`notes/integrated_radius_anchor.tex`, with the condition
`E:radius-anchor-Q` and the conclusions `E:radius-mean-anchor`,
`E:radius-mean-anchor-decay`.

Manuscript input supplied as a hypothesis (not proved here):
* The moment bound of `C:radius-covariance-residuals` (with `C = 1`, `v = p`),
  i.e. `P:radius-actual-moments` transferred to the residual noise `Y_m`:
  `(𝔼‖M_R(Y_m)‖_{C^θ}^p)^{1/p} ≤ C_{Q,B} √p R^{d/Q}` for every block `m`,
  together with the facts that `M_R(Y_m)` is almost surely a `C^θ` path and
  that its `p`-th norm power is integrable (part of the `L^p(C^θ)` statement).
  The stochastic objects `M_R`, `Y_m`, `W` are abstracted to an arbitrary
  family of random paths `M m : Ω → ℝ → E`; so the bound is automatically
  uniform in the deterministic residual projection.

Representation of `C^θ([0,B];E)`.  The manuscript
(`integrated_actual_operator_driver.tex`, line 23) defines the `C^θ` norm as the
supremum norm plus the `θ`-Hölder seminorm.  We define both explicitly as real
suprema over `[0,B]`:
`supNorm B f = sup_{t∈[0,B]} ‖f t‖`,
`holderSemi θ B f = sup_{s≠t ∈ [0,B]} ‖f t - f s‖ / |t - s|^θ`,
and `IsCHolder θ B f` (membership in `C^θ`) says both sets are bounded above.
Mathlib's `HolderWith` is a predicate on a constant on the whole domain, not a
norm on `[0,B]`, so it is not the closest representation.

Implicit side conditions made explicit:
* `μ` is a probability measure (the manuscript's `𝔼`).
* Measurability of `ω ↦ ‖X_m(ω)‖_{C^θ}` (the manuscript treats `X_m` as a
  `C^θ`-valued random variable) is a hypothesis.
* Integrability of `Z_δ` is part of the expectation conclusion.
* Paths are functions `ℝ → E`; only their values on `[0,B]` enter.
-/
public import Mathlib

@[expose] public section

noncomputable section

set_option autoImplicit false

open MeasureTheory Filter Set Topology

namespace StratonovichHAMSecondMoment.RadiusMeanAnchor

/-! ### The margin `e_anchor > 0` (general dimension) -/

/-- `Q > 2d/(1-a)` is equivalent to `Q(1-a) > 2d` (TeX line 324). -/
theorem anchor_Q_iff (a Q d : ℝ) (ha : a < 1) :
    2 * d / (1 - a) < Q ↔ 2 * d < Q * (1 - a) :=
  div_lt_iff₀ (by linarith)

/-- `e_anchor = (1-a)/2 - d/Q > 0` from `Q > 2d/(1-a)`, any real `d`
(TeX lines 323-325). -/
theorem anchor_margin_pos (a Q d : ℝ) (ha : a < 1) (hQ : 0 < Q)
    (hcut : 2 * d / (1 - a) < Q) : 0 < (1 - a) / 2 - d / Q := by
  have h : 2 * d < Q * (1 - a) := (anchor_Q_iff a Q d ha).1 hcut
  have : d / Q < (1 - a) / 2 := by
    rw [div_lt_iff₀ hQ]; nlinarith
  linarith

/-! ### The `C^θ` norm on `[0,B]` and stopped paths -/

variable {E : Type*} [NormedAddCommGroup E]

/-- The values `‖f t‖`, `t ∈ [0,B]`. -/
def supSet (B : ℝ) (f : ℝ → E) : Set ℝ := (fun t => ‖f t‖) '' Icc 0 B

/-- The Hölder quotients `‖f t - f s‖ / |t - s|^θ`, `s ≠ t` in `[0,B]`. -/
def quotSet (θ B : ℝ) (f : ℝ → E) : Set ℝ :=
  {x | ∃ s ∈ Icc 0 B, ∃ t ∈ Icc 0 B, s ≠ t ∧ x = ‖f t - f s‖ / |t - s| ^ θ}

/-- Supremum norm on `[0,B]`. -/
def supNorm (B : ℝ) (f : ℝ → E) : ℝ := sSup (supSet B f)

/-- `θ`-Hölder seminorm on `[0,B]`. -/
def holderSemi (θ B : ℝ) (f : ℝ → E) : ℝ := sSup (quotSet θ B f)

/-- The `C^θ([0,B];E)` norm: supremum norm plus Hölder seminorm. -/
def holderNorm (θ B : ℝ) (f : ℝ → E) : ℝ := supNorm B f + holderSemi θ B f

/-- Membership in `C^θ([0,B];E)`: both suprema are finite. -/
def IsCHolder (θ B : ℝ) (f : ℝ → E) : Prop :=
  BddAbove (supSet B f) ∧ BddAbove (quotSet θ B f)

/-- The path stopped at `ℓ` and extended constantly: `u ↦ f (min u ℓ)`. -/
def stop (ℓ : ℝ) (f : ℝ → E) : ℝ → E := fun u => f (min u ℓ)

theorem supNorm_nonneg (B : ℝ) (f : ℝ → E) : 0 ≤ supNorm B f :=
  Real.sSup_nonneg (by rintro x ⟨t, -, rfl⟩; exact norm_nonneg _)

theorem holderSemi_nonneg (θ B : ℝ) (f : ℝ → E) : 0 ≤ holderSemi θ B f :=
  Real.sSup_nonneg (by rintro x ⟨s, -, t, -, -, rfl⟩; positivity)

theorem holderNorm_nonneg (θ B : ℝ) (f : ℝ → E) : 0 ≤ holderNorm θ B f :=
  add_nonneg (supNorm_nonneg B f) (holderSemi_nonneg θ B f)

theorem min_mem_Icc {B ℓ u : ℝ} (hℓ0 : 0 ≤ ℓ) (hu : u ∈ Icc 0 B) :
    min u ℓ ∈ Icc 0 B :=
  ⟨le_min hu.1 hℓ0, (min_le_left _ _).trans hu.2⟩

theorem stop_supSet_le {B ℓ : ℝ} {f : ℝ → E} (hℓ0 : 0 ≤ ℓ)
    (hf : BddAbove (supSet B f)) :
    ∀ x ∈ supSet B (stop ℓ f), x ≤ supNorm B f := by
  rintro x ⟨t, ht, rfl⟩
  exact le_csSup hf ⟨min t ℓ, min_mem_Icc hℓ0 ht, rfl⟩

theorem stop_quotSet_le {θ B ℓ : ℝ} {f : ℝ → E} (hθ : 0 ≤ θ) (hℓ0 : 0 ≤ ℓ)
    (hf : BddAbove (quotSet θ B f)) :
    ∀ x ∈ quotSet θ B (stop ℓ f), x ≤ holderSemi θ B f := by
  rintro x ⟨s, hs, t, ht, -, rfl⟩
  simp only [stop]
  by_cases heq : min s ℓ = min t ℓ
  · rw [heq, sub_self, norm_zero, zero_div]
    exact holderSemi_nonneg θ B f
  · have hlip : |min t ℓ - min s ℓ| ≤ |t - s| := by
      have := abs_min_sub_min_le_max t ℓ s ℓ
      simpa using this
    have hpos : 0 < |min t ℓ - min s ℓ| :=
      abs_pos.2 (sub_ne_zero.2 (Ne.symm heq))
    calc ‖f (min t ℓ) - f (min s ℓ)‖ / |t - s| ^ θ
        ≤ ‖f (min t ℓ) - f (min s ℓ)‖ / |min t ℓ - min s ℓ| ^ θ :=
          div_le_div_of_nonneg_left (norm_nonneg _) (Real.rpow_pos_of_pos hpos θ)
            (Real.rpow_le_rpow hpos.le hlip hθ)
      _ ≤ holderSemi θ B f :=
          le_csSup hf ⟨min s ℓ, min_mem_Icc hℓ0 hs, min t ℓ, min_mem_Icc hℓ0 ht,
            heq, rfl⟩

/-- Stopping at `ℓ ∈ [0,B]` keeps a path in `C^θ([0,B];E)`. -/
theorem stopped_isCHolder {θ B ℓ : ℝ} {f : ℝ → E} (hθ : 0 ≤ θ) (hℓ0 : 0 ≤ ℓ)
    (hf : IsCHolder θ B f) : IsCHolder θ B (stop ℓ f) :=
  ⟨⟨supNorm B f, stop_supSet_le hℓ0 hf.1⟩,
    ⟨holderSemi θ B f, stop_quotSet_le hθ hℓ0 hf.2⟩⟩

/-- Stopping does not increase the supremum (TeX lines 308-309). -/
theorem stopped_path_sup_le {B ℓ : ℝ} {f : ℝ → E} (hℓ0 : 0 ≤ ℓ)
    (hf : BddAbove (supSet B f)) : supNorm B (stop ℓ f) ≤ supNorm B f :=
  Real.sSup_le (stop_supSet_le hℓ0 hf) (supNorm_nonneg B f)

/-- Stopping does not increase the `θ`-Hölder seminorm, `θ ≥ 0`
(TeX lines 308-309). -/
theorem stopped_path_holder_le {θ B ℓ : ℝ} {f : ℝ → E} (hθ : 0 ≤ θ) (hℓ0 : 0 ≤ ℓ)
    (hf : BddAbove (quotSet θ B f)) :
    holderSemi θ B (stop ℓ f) ≤ holderSemi θ B f :=
  Real.sSup_le (stop_quotSet_le hθ hℓ0 hf) (holderSemi_nonneg θ B f)

theorem stopped_holderNorm_le {θ B ℓ : ℝ} {f : ℝ → E} (hθ : 0 ≤ θ) (hℓ0 : 0 ≤ ℓ)
    (hf : IsCHolder θ B f) : holderNorm θ B (stop ℓ f) ≤ holderNorm θ B f :=
  add_le_add (stopped_path_sup_le hℓ0 hf.1) (stopped_path_holder_le hθ hℓ0 hf.2)

/-- An empty last interval (`ℓ = 0`) gives the zero path on `[0,B]` for a path
starting at zero (TeX lines 309-310). -/
theorem stop_zero_path {B : ℝ} {f : ℝ → E} (hf0 : f 0 = 0) :
    ∀ u ∈ Icc 0 B, stop 0 f u = 0 := by
  intro u hu
  simp only [stop, min_eq_right hu.1, hf0]

section Scale

variable [NormedSpace ℝ E]

theorem smul_isCHolder_and_le {θ B : ℝ} (g : ℝ) {f : ℝ → E} (hf : IsCHolder θ B f) :
    IsCHolder θ B (fun u => g • f u) ∧
      holderNorm θ B (fun u => g • f u) ≤ |g| * holderNorm θ B f := by
  have h1 : ∀ x ∈ supSet B (fun u => g • f u), x ≤ |g| * supNorm B f := by
    rintro x ⟨t, ht, rfl⟩
    simp only [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (le_csSup hf.1 ⟨t, ht, rfl⟩) (abs_nonneg g)
  have h2 : ∀ x ∈ quotSet θ B (fun u => g • f u), x ≤ |g| * holderSemi θ B f := by
    rintro x ⟨s, hs, t, ht, hst, rfl⟩
    rw [← smul_sub, norm_smul, Real.norm_eq_abs, mul_div_assoc]
    exact mul_le_mul_of_nonneg_left (le_csSup hf.2 ⟨s, hs, t, ht, hst, rfl⟩)
      (abs_nonneg g)
  refine ⟨⟨⟨_, h1⟩, ⟨_, h2⟩⟩, ?_⟩
  have a1 := Real.sSup_le h1 (mul_nonneg (abs_nonneg g) (supNorm_nonneg B f))
  have a2 := Real.sSup_le h2 (mul_nonneg (abs_nonneg g) (holderSemi_nonneg θ B f))
  unfold holderNorm supNorm holderSemi at *
  rw [mul_add]
  exact add_le_add a1 a2

/-- The block path `X_m(u) = g · P(min(u, ℓ))`. -/
def blockPath (g ℓ : ℝ) (P : ℝ → E) : ℝ → E := fun u => g • P (min u ℓ)

/-- `‖g P(min(·,ℓ))‖_{C^θ} ≤ |g| ‖P‖_{C^θ}` (stopping at
`ℓ ≥ 0`, then scaling by `g`; TeX lines 287, 308-309). -/
theorem blockPath_norm_le {θ B ℓ : ℝ} (g : ℝ) {P : ℝ → E} (hθ : 0 ≤ θ) (hℓ0 : 0 ≤ ℓ)
    (hP : IsCHolder θ B P) :
    holderNorm θ B (blockPath g ℓ P) ≤ |g| * holderNorm θ B P := by
  have hs := stopped_isCHolder hθ hℓ0 hP
  have h := (smul_isCHolder_and_le g hs).2
  exact h.trans (mul_le_mul_of_nonneg_left (stopped_holderNorm_le hθ hℓ0 hP)
    (abs_nonneg g))

end Scale

/-! ### The block partition -/

/-- `N + 1 ≤ 2/(δB)` and `N ≥ 1` for `N = ⌊1/(δB)⌋`, `δB < 1`
(TeX lines 320-321). -/
theorem block_count_le (δ B : ℝ) (hδ : 0 < δ) (hB : 0 < B) (hδB : δ * B < 1) :
    1 ≤ ⌊1 / (δ * B)⌋₊ ∧ ((⌊1 / (δ * B)⌋₊ : ℝ) + 1 ≤ 2 / (δ * B)) := by
  have hpos : 0 < δ * B := mul_pos hδ hB
  have h1 : 1 ≤ 1 / (δ * B) := by rw [le_div_iff₀ hpos]; linarith
  refine ⟨Nat.le_floor (by exact_mod_cast h1), ?_⟩
  have := Nat.floor_le (le_trans zero_le_one h1)
  have h2 : 2 / (δ * B) = 1 / (δ * B) + 1 / (δ * B) := by ring
  linarith

/-- `δ (N+1) ≤ 2/B`. -/
theorem block_mass_le (δ B : ℝ) (hδ : 0 < δ) (hB : 0 < B) (hδB : δ * B < 1) :
    δ * ((⌊1 / (δ * B)⌋₊ : ℝ) + 1) ≤ 2 / B := by
  have h := (block_count_le δ B hδ hB hδB).2
  calc δ * ((⌊1 / (δ * B)⌋₊ : ℝ) + 1) ≤ δ * (2 / (δ * B)) :=
        mul_le_mul_of_nonneg_left h hδ.le
    _ = 2 / B := by field_simp

/-- The true block lengths of `S:actual-cameron-mean`: `ℓ_m = B` for `m < N`,
`ℓ_N = δ⁻¹ - N B`. -/
def ell (δ B : ℝ) (m : ℕ) : ℝ :=
  if m < ⌊1 / (δ * B)⌋₊ then B else δ⁻¹ - (⌊1 / (δ * B)⌋₊ : ℝ) * B

/-- `ℓ_m ∈ [0,B]` (indeed `ℓ_N ∈ [0,B)`). -/
theorem ell_mem (δ B : ℝ) (hδ : 0 < δ) (hB : 0 < B) (m : ℕ) :
    0 ≤ ell δ B m ∧ ell δ B m ≤ B := by
  unfold ell
  split_ifs
  · exact ⟨hB.le, le_rfl⟩
  · have hpos : 0 < δ * B := mul_pos hδ hB
    have hfl := Nat.floor_le (show 0 ≤ 1 / (δ * B) by positivity)
    have hlt := Nat.lt_floor_add_one (1 / (δ * B))
    have e : 1 / (δ * B) * B = δ⁻¹ := by field_simp
    have a1 := mul_le_mul_of_nonneg_right hfl hB.le
    have a2 := mul_lt_mul_of_pos_right hlt hB
    rw [e] at a1 a2
    constructor <;> nlinarith

/-! ### Lyapunov and the finite block sum -/

/-- Lyapunov: for a probability measure, `p ≥ 1`, nonnegative `Z` with `Z^p`
integrable, `Z` is integrable and `𝔼 Z ≤ (𝔼 Z^p)^{1/p}`. -/
theorem lyapunov_mean_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (Z : Ω → ℝ) (p : ℝ) (hp : 1 ≤ p) (hZ0 : ∀ ω, 0 ≤ Z ω)
    (hZm : AEStronglyMeasurable Z μ) (hZp : Integrable (fun ω => Z ω ^ p) μ) :
    Integrable Z μ ∧ ∫ ω, Z ω ∂μ ≤ (∫ ω, Z ω ^ p ∂μ) ^ (1 / p) := by
  have hint : Integrable Z μ := by
    refine Integrable.mono' (hZp.add (integrable_const (1 : ℝ))) hZm
      (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hZ0 ω)]
    show Z ω ≤ Z ω ^ p + 1
    rcases le_total (Z ω) 1 with h | h
    · have := Real.rpow_nonneg (hZ0 ω) p
      linarith
    · have := Real.rpow_le_rpow_of_exponent_le h hp
      rw [Real.rpow_one] at this
      linarith
  refine ⟨hint, ?_⟩
  have hJ : (∫ ω, Z ω ∂μ) ^ p ≤ ∫ ω, Z ω ^ p ∂μ :=
    (convexOn_rpow hp).map_integral_le
      (fun x _ => (Real.continuousAt_rpow_const x p (Or.inr (by linarith))).continuousWithinAt)
      isClosed_Ici (ae_of_all _ fun ω => hZ0 ω) hint hZp
  have hE0 : 0 ≤ ∫ ω, Z ω ∂μ := integral_nonneg hZ0
  have hp0 : p ≠ 0 := by linarith
  calc ∫ ω, Z ω ∂μ = ((∫ ω, Z ω ∂μ) ^ p) ^ (1 / p) := by
        rw [one_div, Real.rpow_rpow_inv hE0 hp0]
    _ ≤ (∫ ω, Z ω ^ p ∂μ) ^ (1 / p) :=
        Real.rpow_le_rpow (Real.rpow_nonneg hE0 p) hJ (by positivity)

/-- The averaged block mean from per-block `p`-th moment bounds
`𝔼 Y_m^p ≤ A^p` (TeX lines 311-319): `Z = (δ ∑_{m ≤ N} Y_m^p)^{1/p}` is
integrable and `𝔼 Z ≤ (δ(N+1))^{1/p} A`.  Only linearity of the finite sum is
used. -/
theorem mean_anchor_bound_general {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (N : ℕ) (Y : ℕ → Ω → ℝ) (δ p A : ℝ) (hδ : 0 ≤ δ)
    (hp : 1 ≤ p) (hA : 0 ≤ A) (hY0 : ∀ m ω, 0 ≤ Y m ω)
    (hYp : ∀ m ∈ Finset.range (N + 1), Integrable (fun ω => Y m ω ^ p) μ)
    (hmom : ∀ m ∈ Finset.range (N + 1), ∫ ω, Y m ω ^ p ∂μ ≤ A ^ p) :
    Integrable (fun ω => (δ * ∑ m ∈ Finset.range (N + 1), Y m ω ^ p) ^ (1 / p)) μ ∧
      ∫ ω, (δ * ∑ m ∈ Finset.range (N + 1), Y m ω ^ p) ^ (1 / p) ∂μ ≤
        (δ * ((N : ℝ) + 1)) ^ (1 / p) * A := by
  set S : Ω → ℝ := fun ω => δ * ∑ m ∈ Finset.range (N + 1), Y m ω ^ p with hS
  have hS0 : ∀ ω, 0 ≤ S ω := fun ω =>
    mul_nonneg hδ (Finset.sum_nonneg fun m _ => Real.rpow_nonneg (hY0 m ω) p)
  have hSint : Integrable S μ := (integrable_finsetSum _ hYp).const_mul δ
  have hp0 : p ≠ 0 := by linarith
  have hZp : (fun ω => (S ω ^ (1 / p)) ^ p) = S := by
    funext ω; rw [one_div, Real.rpow_inv_rpow (hS0 ω) hp0]
  have hZm : AEStronglyMeasurable (fun ω => S ω ^ (1 / p)) μ :=
    (hSint.aemeasurable.pow_const (1 / p)).aestronglyMeasurable
  have hL := lyapunov_mean_le μ (fun ω => S ω ^ (1 / p)) p hp
    (fun ω => Real.rpow_nonneg (hS0 ω) _) hZm (by rw [hZp]; exact hSint)
  refine ⟨hL.1, ?_⟩
  have hIS : ∫ ω, S ω ∂μ ≤ δ * ((N : ℝ) + 1) * A ^ p := by
    rw [hS, integral_const_mul, integral_finsetSum _ hYp]
    have : ∑ m ∈ Finset.range (N + 1), ∫ ω, Y m ω ^ p ∂μ ≤
        ∑ _m ∈ Finset.range (N + 1), A ^ p := Finset.sum_le_sum hmom
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at this
    push_cast at this
    calc δ * ∑ m ∈ Finset.range (N + 1), ∫ ω, Y m ω ^ p ∂μ
        ≤ δ * (((N : ℝ) + 1) * A ^ p) := mul_le_mul_of_nonneg_left this hδ
      _ = δ * ((N : ℝ) + 1) * A ^ p := by ring
  have hIS' : ∫ ω, (S ω ^ (1 / p)) ^ p ∂μ ≤ δ * ((N : ℝ) + 1) * A ^ p := by
    rw [hZp]; exact hIS
  have hδN : 0 ≤ δ * ((N : ℝ) + 1) := by positivity
  calc ∫ ω, S ω ^ (1 / p) ∂μ ≤ (∫ ω, (S ω ^ (1 / p)) ^ p ∂μ) ^ (1 / p) := hL.2
    _ ≤ (δ * ((N : ℝ) + 1) * A ^ p) ^ (1 / p) :=
        Real.rpow_le_rpow (integral_nonneg fun ω => Real.rpow_nonneg
          (Real.rpow_nonneg (hS0 ω) _) _) hIS' (by positivity)
    _ = (δ * ((N : ℝ) + 1)) ^ (1 / p) * A := by
        rw [Real.mul_rpow hδN (Real.rpow_nonneg hA p), one_div,
          Real.rpow_rpow_inv hA hp0]

/-! ### `E:radius-mean-anchor` for the stopped block paths -/

section Paths

variable [NormedSpace ℝ E]

/-- `E:radius-mean-anchor` (TeX lines 293-296, proof 307-321) for a general
block count `N` and stopping times `ℓ_m ≥ 0`, from the supplied moment input.
Conclusion: `Z_δ` is integrable and
`𝔼 Z_δ ≤ (δ(N+1))^{1/p} g C √p R^{d/Q}`. -/
theorem mean_anchor_bound_blocks {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (θ B δ g p C R e : ℝ) (N : ℕ) (ℓ : ℕ → ℝ)
    (M : ℕ → Ω → ℝ → E) (hθ : 0 ≤ θ) (hδ : 0 ≤ δ) (hg : 0 ≤ g) (hp : 1 ≤ p)
    (hℓ : ∀ m ∈ Finset.range (N + 1), 0 ≤ ℓ m)
    -- supplied input (`C:radius-covariance-residuals` with `C = 1`, `v = p`):
    (hMC : ∀ m ∈ Finset.range (N + 1), ∀ᵐ ω ∂μ, IsCHolder θ B (M m ω))
    (hMint : ∀ m ∈ Finset.range (N + 1),
      Integrable (fun ω => holderNorm θ B (M m ω) ^ p) μ)
    (hMmom : ∀ m ∈ Finset.range (N + 1),
      (∫ ω, holderNorm θ B (M m ω) ^ p ∂μ) ^ (1 / p) ≤ C * Real.sqrt p * R ^ e)
    -- implicit side condition: `‖X_m‖_{C^θ}` is a random variable
    (hXmeas : ∀ m ∈ Finset.range (N + 1),
      AEStronglyMeasurable (fun ω => holderNorm θ B (blockPath g (ℓ m) (M m ω))) μ) :
    Integrable (fun ω => (δ * ∑ m ∈ Finset.range (N + 1),
        holderNorm θ B (blockPath g (ℓ m) (M m ω)) ^ p) ^ (1 / p)) μ ∧
      ∫ ω, (δ * ∑ m ∈ Finset.range (N + 1),
        holderNorm θ B (blockPath g (ℓ m) (M m ω)) ^ p) ^ (1 / p) ∂μ ≤
        (δ * ((N : ℝ) + 1)) ^ (1 / p) * (g * (C * Real.sqrt p * R ^ e)) := by
  have hp0 : p ≠ 0 := by linarith
  have hK : 0 ≤ C * Real.sqrt p * R ^ e :=
    (Real.rpow_nonneg (integral_nonneg fun ω =>
      Real.rpow_nonneg (holderNorm_nonneg θ B (M 0 ω)) p) _).trans
      (hMmom 0 (by simp))
  -- pointwise stopping/scaling bound, almost surely
  have hpt : ∀ m ∈ Finset.range (N + 1), ∀ᵐ ω ∂μ,
      holderNorm θ B (blockPath g (ℓ m) (M m ω)) ^ p ≤
        g ^ p * holderNorm θ B (M m ω) ^ p := by
    intro m hm
    filter_upwards [hMC m hm] with ω hω
    have h := blockPath_norm_le g hθ (hℓ m hm) hω
    rw [abs_of_nonneg hg] at h
    rw [← Real.mul_rpow hg (holderNorm_nonneg θ B _)]
    exact Real.rpow_le_rpow (holderNorm_nonneg θ B _) h (by linarith)
  have hXint : ∀ m ∈ Finset.range (N + 1), Integrable
      (fun ω => holderNorm θ B (blockPath g (ℓ m) (M m ω)) ^ p) μ := by
    intro m hm
    refine Integrable.mono' ((hMint m hm).const_mul (g ^ p))
      ((hXmeas m hm).aemeasurable.pow_const p).aestronglyMeasurable ?_
    filter_upwards [hpt m hm] with ω hω
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (holderNorm_nonneg θ B _) p)]
    exact hω
  have hXmom : ∀ m ∈ Finset.range (N + 1),
      ∫ ω, holderNorm θ B (blockPath g (ℓ m) (M m ω)) ^ p ∂μ ≤
        (g * (C * Real.sqrt p * R ^ e)) ^ p := by
    intro m hm
    have hI0 : 0 ≤ ∫ ω, holderNorm θ B (M m ω) ^ p ∂μ :=
      integral_nonneg fun ω => Real.rpow_nonneg (holderNorm_nonneg θ B _) p
    have hIM : ∫ ω, holderNorm θ B (M m ω) ^ p ∂μ ≤ (C * Real.sqrt p * R ^ e) ^ p := by
      have := Real.rpow_le_rpow (Real.rpow_nonneg hI0 _) (hMmom m hm)
        (show (0 : ℝ) ≤ p by linarith)
      rwa [one_div, Real.rpow_inv_rpow hI0 hp0] at this
    calc ∫ ω, holderNorm θ B (blockPath g (ℓ m) (M m ω)) ^ p ∂μ
        ≤ ∫ ω, g ^ p * holderNorm θ B (M m ω) ^ p ∂μ :=
          integral_mono_ae (hXint m hm) ((hMint m hm).const_mul _) (hpt m hm)
      _ = g ^ p * ∫ ω, holderNorm θ B (M m ω) ^ p ∂μ := integral_const_mul _ _
      _ ≤ g ^ p * (C * Real.sqrt p * R ^ e) ^ p :=
          mul_le_mul_of_nonneg_left hIM (Real.rpow_nonneg hg p)
      _ = (g * (C * Real.sqrt p * R ^ e)) ^ p := (Real.mul_rpow hg hK).symm
  exact mean_anchor_bound_general μ N
    (fun m ω => holderNorm θ B (blockPath g (ℓ m) (M m ω))) δ p _ hδ hp
    (mul_nonneg hg hK) (fun m ω => holderNorm_nonneg θ B _) hXint hXmom

end Paths

/-! ### Decay with `R_δ = δ⁻¹ + 2` -/

/-- `R_δ = 1/δ + 2 ≤ 3/δ` for `0 < δ ≤ 1` (TeX line 323). -/
theorem radius_le (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) : 1 / δ + 2 ≤ 3 / δ := by
  rw [div_add' _ _ _ hδ.ne', div_le_div_iff_of_pos_right hδ]
  linarith

/-- The substitution: `g_δ R_δ^{d/Q} ≤ 3^{d/Q} δ^{(1-a)/2 - d/Q}`. -/
theorem radius_substitution (δ a x : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hx : 0 ≤ x) :
    δ ^ ((1 - a) / 2) * (1 / δ + 2) ^ x ≤ 3 ^ x * δ ^ ((1 - a) / 2 - x) := by
  have h1 : (1 / δ + 2) ^ x ≤ (3 / δ) ^ x :=
    Real.rpow_le_rpow (by positivity) (radius_le δ hδ hδ1) hx
  rw [Real.div_rpow (by norm_num) hδ.le, Real.rpow_sub hδ] at *
  calc δ ^ ((1 - a) / 2) * (1 / δ + 2) ^ x ≤ δ ^ ((1 - a) / 2) * (3 ^ x / δ ^ x) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = 3 ^ x * (δ ^ ((1 - a) / 2) / δ ^ x) := by ring

/-- `E:radius-mean-anchor-decay`: from `𝔼 Z ≤ K g_δ R_δ^{d/Q}` with `K ≥ 0`,
`2 𝔼 Z ≤ 2 K 3^{d/Q} δ^{e_anchor}`. -/
theorem mean_anchor_decay (δ a x K EZ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hx : 0 ≤ x)
    (hK : 0 ≤ K) (hEZ : EZ ≤ K * (δ ^ ((1 - a) / 2) * (1 / δ + 2) ^ x)) :
    2 * EZ ≤ 2 * K * 3 ^ x * δ ^ ((1 - a) / 2 - x) := by
  have := mul_le_mul_of_nonneg_left (radius_substitution δ a x hδ hδ1 hx) hK
  nlinarith

/-- The deterministic bound tends to zero as `δ → 0⁺` when `e > 0`. -/
theorem decay_tendsto (K e : ℝ) (he : 0 < e) :
    Tendsto (fun δ : ℝ => K * δ ^ e) (𝓝[>] 0) (𝓝 0) := by
  have h : Tendsto (fun δ : ℝ => δ ^ e) (𝓝 0) (𝓝 0) := by
    have := (Real.continuousAt_rpow_const 0 e (Or.inr he.le)).tendsto
    rwa [Real.zero_rpow he.ne'] at this
  simpa using (h.mono_left nhdsWithin_le_nhds).const_mul K

/-! ### The proposition under exactly its manuscript hypotheses -/

section Paper

variable [NormedSpace ℝ E]

/-- Proposition `P:radius-mean-anchor` under the hypotheses of the manuscript:
`H:homog` (`d ∈ {1,2,3}`, `0 < a = α₀ < 1`, `0 < α < d` or `α = d = 1`,
`a + α < 2`), `E:radius-anchor-parameters`, `E:radius-anchor-Q` (`Q` even,
`Q ≥ 2`), integer `B ≥ 1`, `0 < δ < min(1, 1/B)`, `N = ⌊1/(δB)⌋`, the true block
lengths `ℓ_m = ell δ B m`, `g_δ = δ^{(1-a)/2}`, `p ≥ 1`, `R ≥ 1`, and the
supplied input of `C:radius-covariance-residuals` for the paths
`M m = M_R(Y_m)`.  Conclusions:
1. `Z_δ` is integrable and `𝔼 Z_δ ≤ (2/B)^{1/p} C √p g_δ R^{d/Q}`
   (`E:radius-mean-anchor`);
2. `e_anchor = (1-a)/2 - d/Q > 0`;
3. if `R = δ⁻¹ + 2`, then `2𝔼 Z_δ ≤ 2(2/B)^{1/p} C √p 3^{d/Q} δ^{e_anchor}`
   (`E:radius-mean-anchor-decay`);
4. that bound tends to `0` as `δ → 0⁺`. -/
theorem radius_mean_anchor_paper {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    -- `H:homog`
    (d : ℕ) (_hd : d = 1 ∨ d = 2 ∨ d = 3) (a α : ℝ) (_ha0 : 0 < a) (ha1 : a < 1)
    (_hα : (0 < α ∧ α < d) ∨ (α = d ∧ d = 1)) (_hthr : a + α < 2)
    -- `E:radius-anchor-parameters`
    (γ θ ηt βt : ℝ) (_hγ0 : 0 < γ) (_hγ : γ < min (1 / 2) ((2 - α) / 2))
    (hθ : 1 / 2 < θ) (_hθη : θ < ηt) (_hηβ : ηt < βt)
    (_hβ : βt < min (1 - a / 2) ((3 - a - α) / 2))
    -- `E:radius-anchor-Q`
    (Q : ℕ) (_hQeven : Even Q) (hQ2 : 2 ≤ Q) (_hQγ : (d : ℝ) < Q * γ)
    (_hQβ : 0 < βt - ηt - 1 / Q) (hQa : 2 * (d : ℝ) / (1 - a) < Q)
    -- block partition
    (B : ℕ) (hB : 1 ≤ B) (δ : ℝ) (hδ0 : 0 < δ) (hδ : δ < min 1 (1 / (B : ℝ)))
    (p : ℝ) (hp : 1 ≤ p) (R : ℝ) (hR : 1 ≤ R) (C : ℝ)
    -- the transferred residual paths `M_R(Y_m)`, `m = 0, …, N`
    (M : ℕ → Ω → ℝ → E)
    -- supplied input (`C:radius-covariance-residuals`, `C = 1`, `v = p`)
    (hMC : ∀ m ∈ Finset.range (⌊1 / (δ * B)⌋₊ + 1), ∀ᵐ ω ∂μ, IsCHolder θ B (M m ω))
    (hMint : ∀ m ∈ Finset.range (⌊1 / (δ * B)⌋₊ + 1),
      Integrable (fun ω => holderNorm θ B (M m ω) ^ p) μ)
    (hMmom : ∀ m ∈ Finset.range (⌊1 / (δ * B)⌋₊ + 1),
      (∫ ω, holderNorm θ B (M m ω) ^ p ∂μ) ^ (1 / p) ≤
        C * Real.sqrt p * R ^ ((d : ℝ) / Q))
    -- implicit side condition: `‖X_m‖_{C^θ}` is a random variable
    (hXmeas : ∀ m ∈ Finset.range (⌊1 / (δ * B)⌋₊ + 1),
      AEStronglyMeasurable (fun ω =>
        holderNorm θ B (blockPath (δ ^ ((1 - a) / 2)) (ell δ B m) (M m ω))) μ) :
    (Integrable (fun ω => (δ * ∑ m ∈ Finset.range (⌊1 / (δ * B)⌋₊ + 1),
        holderNorm θ B (blockPath (δ ^ ((1 - a) / 2)) (ell δ B m) (M m ω)) ^ p)
          ^ (1 / p)) μ ∧
      ∫ ω, (δ * ∑ m ∈ Finset.range (⌊1 / (δ * B)⌋₊ + 1),
        holderNorm θ B (blockPath (δ ^ ((1 - a) / 2)) (ell δ B m) (M m ω)) ^ p)
          ^ (1 / p) ∂μ ≤
        (2 / (B : ℝ)) ^ (1 / p) * C * Real.sqrt p * δ ^ ((1 - a) / 2) *
          R ^ ((d : ℝ) / Q)) ∧
    0 < (1 - a) / 2 - (d : ℝ) / Q ∧
    (R = δ⁻¹ + 2 →
      2 * ∫ ω, (δ * ∑ m ∈ Finset.range (⌊1 / (δ * B)⌋₊ + 1),
        holderNorm θ B (blockPath (δ ^ ((1 - a) / 2)) (ell δ B m) (M m ω)) ^ p)
          ^ (1 / p) ∂μ ≤
        2 * (2 / (B : ℝ)) ^ (1 / p) * C * Real.sqrt p * 3 ^ ((d : ℝ) / Q) *
          δ ^ ((1 - a) / 2 - (d : ℝ) / Q)) ∧
    Tendsto (fun δ' : ℝ => 2 * (2 / (B : ℝ)) ^ (1 / p) * C * Real.sqrt p *
        3 ^ ((d : ℝ) / Q) * δ' ^ ((1 - a) / 2 - (d : ℝ) / Q)) (𝓝[>] 0) (𝓝 0) := by
  have hBpos : (0 : ℝ) < B := by exact_mod_cast hB
  have hQpos : (0 : ℝ) < Q := by exact_mod_cast (lt_of_lt_of_le two_pos hQ2)
  have hδ1 : δ < 1 := lt_of_lt_of_le hδ (min_le_left _ _)
  have hδB : δ * B < 1 := by
    have h := lt_of_lt_of_le hδ (min_le_right _ _)
    rwa [lt_div_iff₀ hBpos] at h
  have hx : 0 ≤ (d : ℝ) / Q := by positivity
  set N := ⌊1 / (δ * B)⌋₊ with hN
  have hg : 0 ≤ δ ^ ((1 - a) / 2) := Real.rpow_nonneg hδ0.le _
  have hmain := mean_anchor_bound_blocks μ θ B δ (δ ^ ((1 - a) / 2)) p C R ((d : ℝ) / Q)
    N (ell δ B) M (by linarith) hδ0.le hg hp
    (fun m _ => (ell_mem δ B hδ0 hBpos m).1) hMC hMint hMmom hXmeas
  have hK : 0 ≤ C * Real.sqrt p * R ^ ((d : ℝ) / Q) :=
    (Real.rpow_nonneg (integral_nonneg fun ω =>
      Real.rpow_nonneg (holderNorm_nonneg θ B (M 0 ω)) p) _).trans
      (hMmom 0 (by simp))
  have hC : 0 ≤ C := by
    have h1 : 0 < Real.sqrt p * R ^ ((d : ℝ) / Q) :=
      mul_pos (Real.sqrt_pos.2 (by linarith)) (Real.rpow_pos_of_pos (by linarith) _)
    have : 0 ≤ C * (Real.sqrt p * R ^ ((d : ℝ) / Q)) := by rw [← mul_assoc]; exact hK
    exact nonneg_of_mul_nonneg_left this h1
  have hmass : (δ * ((N : ℝ) + 1)) ^ (1 / p) ≤ (2 / (B : ℝ)) ^ (1 / p) :=
    Real.rpow_le_rpow (by positivity) (block_mass_le δ B hδ0 hBpos hδB)
      (by have : 0 < p := by linarith
          positivity)
  have hbound : ∫ ω, (δ * ∑ m ∈ Finset.range (N + 1),
        holderNorm θ B (blockPath (δ ^ ((1 - a) / 2)) (ell δ B m) (M m ω)) ^ p)
          ^ (1 / p) ∂μ ≤
        (2 / (B : ℝ)) ^ (1 / p) * C * Real.sqrt p * δ ^ ((1 - a) / 2) *
          R ^ ((d : ℝ) / Q) := by
    refine hmain.2.trans ?_
    have := mul_le_mul_of_nonneg_right hmass (mul_nonneg hg hK)
    calc (δ * ((N : ℝ) + 1)) ^ (1 / p) *
          (δ ^ ((1 - a) / 2) * (C * Real.sqrt p * R ^ ((d : ℝ) / Q)))
        ≤ (2 / (B : ℝ)) ^ (1 / p) *
          (δ ^ ((1 - a) / 2) * (C * Real.sqrt p * R ^ ((d : ℝ) / Q))) := this
      _ = _ := by ring
  have he := anchor_margin_pos a Q d ha1 hQpos hQa
  have hK2 : 0 ≤ (2 / (B : ℝ)) ^ (1 / p) * C * Real.sqrt p := by positivity
  refine ⟨⟨hmain.1, hbound⟩, he, ?_, ?_⟩
  · intro hRδ
    have e1 : (2 / (B : ℝ)) ^ (1 / p) * C * Real.sqrt p * δ ^ ((1 - a) / 2) *
        R ^ ((d : ℝ) / Q) = ((2 / (B : ℝ)) ^ (1 / p) * C * Real.sqrt p) *
        (δ ^ ((1 - a) / 2) * (1 / δ + 2) ^ ((d : ℝ) / Q)) := by
      rw [hRδ, ← one_div]; ring
    have h := mean_anchor_decay δ a ((d : ℝ) / Q)
      ((2 / (B : ℝ)) ^ (1 / p) * C * Real.sqrt p) _ hδ0 hδ1.le hx hK2
      (hbound.trans e1.le)
    have e2 : 2 * ((2 / (B : ℝ)) ^ (1 / p) * C * Real.sqrt p) * 3 ^ ((d : ℝ) / Q) *
        δ ^ ((1 - a) / 2 - (d : ℝ) / Q) = 2 * (2 / (B : ℝ)) ^ (1 / p) * C *
        Real.sqrt p * 3 ^ ((d : ℝ) / Q) * δ ^ ((1 - a) / 2 - (d : ℝ) / Q) := by ring
    rw [e2] at h
    exact h
  · have := decay_tendsto (2 * (2 / (B : ℝ)) ^ (1 / p) * C * Real.sqrt p *
      3 ^ ((d : ℝ) / Q)) _ he
    exact this

end Paper

end StratonovichHAMSecondMoment.RadiusMeanAnchor
