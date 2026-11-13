module

/-
Copyright 2026 Le Chen. SPDX-License-Identifier: Apache-2.0

The damped occupation kernel and its exact row maximum, from
`notes/integrated_spatial_occupation.tex` (revision a284420):
the kernel `K_⋆` of `E:occupation-damped-kernel` (lines 352-359) and
Lemma `L:occupation-kernel-row` (lines 361-379, display
`E:occupation-kernel-row`, lines 365-368).

Standing assumptions of the section (lines 4-10): a nonzero original
covariance from `H:homog`, `a = α₀`, `q = 4 - α`, `D = q - 2a > 0`.

Formalized here (all proved, no supplied input):
* `Kstar a D u`: the manuscript's formula
  `K_⋆(u) = Γ_E(a)⁻¹ ∫_0^∞ e^{-(λ + λ²/(2D))|u|} λ^{a-1} dλ` for `u ≠ 0`,
  and `K_⋆(0) = 0` (line 359); `Γ_E` is Mathlib's `Real.Gamma`.
  `Kstar_eq_Psi` identifies it, for `u ≠ 0`, with the averaged clock kernel
  `TimeFractional.Psi a |u| (|u|/D)` of the main file, and
  `kstarIntegrand_integrable` proves that the defining integral is a
  convergent Lebesgue integral for `u ≠ 0`, `a > 0`, `D > 0` (so `Kstar` is
  not a junk value of a non-integrable Bochner integral there).
* `occupation_kernel_row`: the kernel is even, positive off zero, locally
  integrable (`a < 1`), strictly decreasing on `(0,∞)`, `K_⋆(u) ≤ |u|^{-a}`
  off zero; for every `s ∈ [0,1]` the row `t ↦ K_⋆(s-t)` is integrable on
  `[0,1]`; and `R_⋆ = 2 ∫_0^{1/2} K_⋆` is the greatest element of the set of
  row values `{∫_0^1 K_⋆(s-t) dt : s ∈ [0,1]}` (so the maximum exists and
  equals `R_⋆`, attained at `s = 1/2`), with `K_⋆` integrable on `[0,1/2]`
  and `0 < R_⋆` (a real number, hence finite).
* `occupation_kernel_row_paper`: the same under the section's standing
  hypotheses, `HomogHypothesis.HomogCovariance d α a Γ μ`, `Γ ≠ 0` and
  `D = (4 - α) - 2a`; `D > 0` is derived there from `H:homog`
  (`a + α < 2`).  `Γ ≠ 0` is carried as stated by the TeX and is not used
  by the proof.

Also formalized (all proved, no supplied input), Lemma `L:spatial-physical-pair`
(lines 12-33, display `E:spatial-physical-pair`, lines 15-17):
* `pairMeasure Γ = volume.prod Γ` (`ν(dx,dy) = dx Γ(dy)`) and
  `pairing Γ f h = ∫⁻ f(x) h(x-y) dν` for `[0,∞]`-valued `f, h` (the TeX's
  "extended nonnegative integral"; arbitrary `[0,∞]`-valued functions are
  allowed, which contains the TeX's finite Borel representatives);
* `spatial_physical_pair` (for any locally finite `Γ` on `ℝ^d`): `ν` is
  sigma-finite; `pairing` is unchanged when `f` and `h` are replaced by
  Lebesgue-a.e. equal functions; for Lebesgue-a.e. measurable `f, h` the
  integrand is `ν`-a.e. measurable; Lebesgue-a.e. convergence of a sequence of
  real functions transfers to `ν`-a.e. convergence at `x` and at `x - y`.
  `ae_pair_of_ae` is the null-set transfer of the TeX proof (lines 26-29);
* `spatial_physical_pair_paper`: the same under `HomogCovariance d α a Γ μ`
  and `Γ ≠ 0`; only local finiteness of `Γ` is used.

The manuscript says "decreasing"; the Lean statement proves strict decrease
(`StrictAntiOn`), which implies the weak form.  Interval integrals are
Mathlib's `∫ t in (0:ℝ)..1`, and each comes with its integrability.

Proof route.  The bound `K_⋆ ≤ |u|^{-a}` and positivity are reused from
`TimeFractional.Psi_le_rpow` and `TimeFractional.Psi_pos`.  The row identity
`∫_0^1 K_⋆(s-t) dt = Φ(s) + Φ(1-s)` with `Φ(t) = ∫_0^t K_⋆` is the TeX's.
The TeX then invokes concavity of `Φ`; here the inequality
`Φ(s) + Φ(1-s) ≤ 2Φ(1/2)` (for `s ≤ 1/2`, the other case by `s ↦ 1-s`) is
proved directly by a shift comparison,
`Φ(1-s) - Φ(1/2) = ∫_s^{1/2} K_⋆(x + (1/2 - s)) dx ≤ ∫_s^{1/2} K_⋆ =
Φ(1/2) - Φ(s)`, using that `K_⋆` decreases on `(0,∞)` (the same fact that
the TeX uses for concavity).  Lemmas marked "auxiliary to the Lean proof
route" have no manuscript label.
-/

public import Mathlib
public import StratonovichHAMSecondMoment.TimeFractional
public import StratonovichHAMSecondMoment.HomogHypothesis

@[expose] public section

noncomputable section

set_option autoImplicit false

open MeasureTheory Set Real Filter
open scoped ENNReal
open StratonovichHAMSecondMoment.TimeFractional

namespace StratonovichHAMSecondMoment.OccupationKernelRow

/-! ### The kernel `K_⋆` (`E:occupation-damped-kernel`, lines 352-359) -/

/-- The integrand of `E:occupation-damped-kernel`:
`e^{-(λ + λ²/(2D))|u|} λ^{a-1}` (lines 354-357). -/
def kstarIntegrand (a D u l : ℝ) : ℝ :=
  Real.exp (-(l + l ^ 2 / (2 * D)) * |u|) * l ^ (a - 1)

/-- The kernel `K_⋆` of `E:occupation-damped-kernel` (lines 352-359):
`Γ_E(a)⁻¹ ∫_0^∞ e^{-(λ + λ²/(2D))|u|} λ^{a-1} dλ` for `u ≠ 0`, and
`K_⋆(0) = 0`. -/
def Kstar (a D u : ℝ) : ℝ :=
  if u = 0 then 0 else (Real.Gamma a)⁻¹ * ∫ l in Ioi (0 : ℝ), kstarIntegrand a D u l

/-- The row integral `∫_0^1 K_⋆(s-t) dt` of `E:occupation-kernel-row`. -/
def row (a D s : ℝ) : ℝ := ∫ t in (0 : ℝ)..1, Kstar a D (s - t)

/-- `R_⋆ = 2 ∫_0^{1/2} K_⋆(u) du` of `E:occupation-kernel-row`. -/
def Rstar (a D : ℝ) : ℝ := 2 * ∫ u in (0 : ℝ)..(1 / 2), Kstar a D u

/-- Auxiliary to the Lean proof route. The integrand equals the integrand of
`TimeFractional.Psi a |u| (|u|/D)` (an identity of real numbers, valid for every `D`). -/
theorem kstarIntegrand_eq_psiKernel (a D u l : ℝ) :
    kstarIntegrand a D u l = psiKernel a |u| (|u| / D) l := by
  unfold kstarIntegrand psiKernel
  rw [mul_comm]
  congr 2
  ring

/-- For `u ≠ 0`, `K_⋆(u) = Ψ_a(|u|, |u|/D)`, the averaged clock kernel
`TimeFractional.Psi` of `E:averaged-clock-kernel` (main file, line 7704). -/
theorem Kstar_eq_Psi (a D u : ℝ) (hu : u ≠ 0) : Kstar a D u = Psi a |u| (|u| / D) := by
  simp only [Kstar, hu, ite_false, Psi, kstarIntegrand_eq_psiKernel]

/-- For `a > 0`, `D > 0`, `u ≠ 0`, the integrand of `E:occupation-damped-kernel` is
integrable on `(0,∞)`. -/
theorem kstarIntegrand_integrable (a D u : ℝ) (ha : 0 < a) (hD : 0 < D) (hu : u ≠ 0) :
    Integrable (kstarIntegrand a D u) L0 := by
  have h := psiKernel_integrable a |u| (|u| / D) ha (abs_pos.2 hu) (by positivity)
  have he : kstarIntegrand a D u = psiKernel a |u| (|u| / D) :=
    funext (kstarIntegrand_eq_psiKernel a D u)
  rw [he]
  exact h

/-- `K_⋆` is even. -/
theorem Kstar_neg (a D u : ℝ) : Kstar a D (-u) = Kstar a D u := by
  simp only [Kstar, neg_eq_zero, kstarIntegrand, abs_neg]

/-- `K_⋆(u) > 0` for `u ≠ 0` (`a > 0`, `D > 0`). -/
theorem Kstar_pos (a D u : ℝ) (ha : 0 < a) (hD : 0 < D) (hu : u ≠ 0) : 0 < Kstar a D u := by
  rw [Kstar_eq_Psi a D u hu]
  exact Psi_pos a |u| (|u| / D) ha (abs_pos.2 hu) (by positivity)

/-- Auxiliary to the Lean proof route. `K_⋆(u) ≥ 0` for every `u` (`a > 0`, `D > 0`). -/
theorem Kstar_nonneg (a D u : ℝ) (ha : 0 < a) (hD : 0 < D) : 0 ≤ Kstar a D u := by
  by_cases hu : u = 0
  · simp [Kstar, hu]
  · exact (Kstar_pos a D u ha hD hu).le

/-- `K_⋆(u) ≤ |u|^{-a}` for `u ≠ 0` (`a > 0`, `D > 0`). -/
theorem Kstar_le_rpow (a D u : ℝ) (ha : 0 < a) (hD : 0 < D) (hu : u ≠ 0) :
    Kstar a D u ≤ |u| ^ (-a) := by
  rw [Kstar_eq_Psi a D u hu]
  exact Psi_le_rpow a |u| (|u| / D) ha (abs_pos.2 hu) (by positivity)

/-- Auxiliary to the Lean proof route. Strict decrease of `Ψ_a(r, r/D)` along the
diagonal `r ↦ (r, r/D)`, for `0 < r < r'`. -/
theorem Psi_diag_strictAnti (a D r r' : ℝ) (ha : 0 < a) (hD : 0 < D) (hr : 0 < r)
    (hrr : r < r') : Psi a r' (r' / D) < Psi a r (r / D) := by
  have hr' : 0 < r' := hr.trans hrr
  have hv : 0 ≤ r / D := by positivity
  have hv' : 0 ≤ r' / D := by positivity
  have hvv : r / D ≤ r' / D := div_le_div_of_nonneg_right hrr.le hD.le
  have i1 := psiKernel_integrable a r (r / D) ha hr hv
  have i2 := psiKernel_integrable a r' (r' / D) ha hr' hv'
  have hpos : ∀ᵐ l ∂L0, 0 < psiKernel a r (r / D) l - psiKernel a r' (r' / D) l := by
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun l hl => ?_)
    have hl : 0 < l := hl
    rw [sub_pos]
    unfold psiKernel
    refine mul_lt_mul_of_pos_left (Real.exp_lt_exp.2 ?_) (Real.rpow_pos_of_pos hl _)
    have h1 : r * l < r' * l := mul_lt_mul_of_pos_right hrr hl
    have h2 : r / D * l ^ 2 / 2 ≤ r' / D * l ^ 2 / 2 := by
      have := sq_nonneg l
      have : r / D * l ^ 2 ≤ r' / D * l ^ 2 := mul_le_mul_of_nonneg_right hvv this
      linarith
    linarith
  have h := integral_pos_of_ae_pos
    (f := fun l => psiKernel a r (r / D) l - psiKernel a r' (r' / D) l) (i1.sub i2) (by simp) hpos
  rw [integral_sub i1 i2, sub_pos] at h
  unfold Psi
  exact mul_lt_mul_of_pos_left h (inv_pos.2 (Real.Gamma_pos_of_pos ha))

/-- `K_⋆` is strictly decreasing on `(0,∞)` (`a > 0`, `D > 0`); the manuscript says
"decreasing". -/
theorem Kstar_strictAntiOn (a D : ℝ) (ha : 0 < a) (hD : 0 < D) :
    StrictAntiOn (Kstar a D) (Ioi 0) := by
  intro u hu u' hu' huu
  have hu : (0 : ℝ) < u := hu
  have hu' : (0 : ℝ) < u' := hu'
  rw [Kstar_eq_Psi a D u hu.ne', Kstar_eq_Psi a D u' hu'.ne', abs_of_pos hu, abs_of_pos hu']
  exact Psi_diag_strictAnti a D u u' ha hD hu huu

/-- Auxiliary to the Lean proof route. `K_⋆` is measurable. -/
theorem Kstar_measurable (a D : ℝ) : Measurable (Kstar a D) := by
  have hF : StronglyMeasurable (fun p : ℝ × ℝ => kstarIntegrand a D p.1 p.2) := by
    refine Measurable.stronglyMeasurable ?_
    unfold kstarIntegrand
    fun_prop
  have hI : Measurable fun u : ℝ => ∫ l in Ioi (0 : ℝ), kstarIntegrand a D u l :=
    (hF.integral_prod_right' (ν := L0)).measurable
  unfold Kstar
  exact Measurable.ite (measurableSet_singleton 0) measurable_const
    (measurable_const.mul hI)

/-- Auxiliary to the Lean proof route. Interval integrability of `K_⋆` on `[0,c]`, `c ≥ 0`
(`0 < a < 1`, `D > 0`). -/
theorem Kstar_intervalIntegrable_zero_of_nonneg (a D c : ℝ) (ha : 0 < a) (ha1 : a < 1)
    (hD : 0 < D) (hc : 0 ≤ c) : IntervalIntegrable (Kstar a D) volume 0 c := by
  have hR : IntervalIntegrable (fun x : ℝ => x ^ (-a)) volume 0 c :=
    intervalIntegral.intervalIntegrable_rpow' (by linarith)
  refine hR.mono_fun' (Kstar_measurable a D).aestronglyMeasurable ?_
  rw [uIoc_of_le hc]
  refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun u hu => ?_)
  have hu0 : 0 < u := hu.1
  dsimp only
  rw [Real.norm_of_nonneg (Kstar_nonneg a D u ha hD)]
  have := Kstar_le_rpow a D u ha hD hu0.ne'
  rwa [abs_of_pos hu0] at this

/-- Auxiliary to the Lean proof route. Interval integrability of `K_⋆` on every interval
(`0 < a < 1`, `D > 0`). -/
theorem Kstar_intervalIntegrable (a D b c : ℝ) (ha : 0 < a) (ha1 : a < 1) (hD : 0 < D) :
    IntervalIntegrable (Kstar a D) volume b c := by
  have h0 : ∀ c : ℝ, IntervalIntegrable (Kstar a D) volume 0 c := by
    intro c
    rcases le_total 0 c with hc | hc
    · exact Kstar_intervalIntegrable_zero_of_nonneg a D c ha ha1 hD hc
    · have h := Kstar_intervalIntegrable_zero_of_nonneg a D (-c) ha ha1 hD (by linarith)
      rw [IntervalIntegrable.iff_comp_neg] at h
      simpa only [Kstar_neg, neg_zero, neg_neg] using h
  exact (h0 b).symm.trans (h0 c)

/-- `K_⋆` is locally integrable on `ℝ` (`0 < a < 1`, `D > 0`). -/
theorem Kstar_locallyIntegrable (a D : ℝ) (ha : 0 < a) (ha1 : a < 1) (hD : 0 < D) :
    LocallyIntegrable (Kstar a D) := by
  rw [locallyIntegrable_iff]
  intro k hk
  obtain ⟨R, hR⟩ := hk.isBounded.subset_closedBall 0
  have hsub : k ⊆ Icc (-|R|) |R| := by
    intro x hx
    have := hR hx
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at this
    have hRR : R ≤ |R| := le_abs_self R
    constructor <;> [linarith [neg_abs_le x]; linarith [le_abs_self x]]
  have hI := Kstar_intervalIntegrable a D (-|R|) |R| ha ha1 hD
  have hle : -|R| ≤ |R| := by linarith [abs_nonneg R]
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hle] at hI
  exact hI.mono_set hsub

/-! ### The row and its maximum (`E:occupation-kernel-row`) -/

/-- `Φ(t) = ∫_0^t K_⋆(u) du` of the proof of `L:occupation-kernel-row` (lines 374-375). -/
def Phi (a D t : ℝ) : ℝ := ∫ u in (0 : ℝ)..t, Kstar a D u

/-- The row is `Φ(s) + Φ(1-s)` (TeX line 376), for every real `s`
(`0 < a < 1`, `D > 0`). -/
theorem row_eq_Phi (a D s : ℝ) (ha : 0 < a) (ha1 : a < 1) (hD : 0 < D) :
    row a D s = Phi a D s + Phi a D (1 - s) := by
  have hI : ∀ b c : ℝ, IntervalIntegrable (Kstar a D) volume b c :=
    fun b c => Kstar_intervalIntegrable a D b c ha ha1 hD
  unfold row Phi
  rw [intervalIntegral.integral_comp_sub_left (fun x => Kstar a D x) s, sub_zero,
    ← intervalIntegral.integral_add_adjacent_intervals (hI (s - 1) 0) (hI 0 s), add_comm]
  congr 1
  have h := intervalIntegral.integral_comp_neg (a := s - 1) (b := 0) (fun x => Kstar a D x)
  simp only [Kstar_neg, neg_zero, neg_sub] at h
  exact h

/-- Auxiliary to the Lean proof route. `Φ(s) + Φ(1-s) ≤ 2Φ(1/2)` for `0 ≤ s ≤ 1/2`, by a
shift comparison. -/
theorem Phi_sum_le_of_le_half (a D s : ℝ) (ha : 0 < a) (ha1 : a < 1) (hD : 0 < D)
    (hs0 : 0 ≤ s) (hs : s ≤ 1 / 2) :
    Phi a D s + Phi a D (1 - s) ≤ 2 * Phi a D (1 / 2) := by
  have hI : ∀ b c : ℝ, IntervalIntegrable (Kstar a D) volume b c :=
    fun b c => Kstar_intervalIntegrable a D b c ha ha1 hD
  set c := 1 / 2 - s with hc
  have hc0 : 0 ≤ c := by rw [hc]; linarith
  have e1 : Phi a D (1 / 2) = Phi a D s + ∫ u in s..(1 / 2), Kstar a D u :=
    (intervalIntegral.integral_add_adjacent_intervals (hI 0 s) (hI s (1 / 2))).symm
  have e2 : Phi a D (1 - s) = Phi a D (1 / 2) + ∫ u in (1 / 2)..(1 - s), Kstar a D u :=
    (intervalIntegral.integral_add_adjacent_intervals (hI 0 (1 / 2)) (hI (1 / 2) (1 - s))).symm
  have e3 : ∫ u in (1 / 2)..(1 - s), Kstar a D u = ∫ x in s..(1 / 2), Kstar a D (x + c) := by
    rw [intervalIntegral.integral_comp_add_right (fun x => Kstar a D x) c]
    congr 1 <;> rw [hc] <;> ring
  have hshift : IntervalIntegrable (fun x => Kstar a D (x + c)) volume s (1 / 2) := by
    have h := hI (s + c) (1 / 2 + c)
    exact (IntervalIntegrable.comp_add_right h c (by finiteness)).congr_ae
      (by simp) |>.mono_set (by simp)
  have hmono : ∫ x in s..(1 / 2), Kstar a D (x + c) ≤ ∫ x in s..(1 / 2), Kstar a D x := by
    refine intervalIntegral.integral_mono_on_of_le_Ioo hs hshift (hI s (1 / 2)) ?_
    intro x hx
    have hx0 : 0 < x := lt_of_le_of_lt hs0 hx.1
    exact (Kstar_strictAntiOn a D ha hD).antitoneOn hx0 (show (0 : ℝ) < x + c by linarith)
      (by linarith)
  rw [e2, e3]
  linarith

/-- `Φ(s) + Φ(1-s) ≤ 2Φ(1/2)` for `s ∈ [0,1]` (TeX line 376). -/
theorem Phi_sum_le (a D s : ℝ) (ha : 0 < a) (ha1 : a < 1) (hD : 0 < D)
    (hs : s ∈ Icc (0 : ℝ) 1) :
    Phi a D s + Phi a D (1 - s) ≤ 2 * Phi a D (1 / 2) := by
  rcases le_total s (1 / 2) with h | h
  · exact Phi_sum_le_of_le_half a D s ha ha1 hD hs.1 h
  · have := Phi_sum_le_of_le_half a D (1 - s) ha ha1 hD (by linarith [hs.2]) (by linarith)
    rw [sub_sub_cancel] at this
    linarith

/-- Lemma `L:occupation-kernel-row` (lines 361-379), for `0 < a < 1` and `D > 0`:
`K_⋆` is even, positive off zero, locally integrable, strictly decreasing on `(0,∞)`,
`K_⋆(u) ≤ |u|^{-a}` off zero; every row `t ↦ K_⋆(s-t)`, `s ∈ [0,1]`, is integrable
on `[0,1]`; `R_⋆ = 2∫_0^{1/2} K_⋆` is the greatest row value over `s ∈ [0,1]`
(`E:occupation-kernel-row`); `K_⋆` is integrable on `[0,1/2]` and `0 < R_⋆`. -/
theorem occupation_kernel_row (a D : ℝ) (ha : 0 < a) (ha1 : a < 1) (hD : 0 < D) :
    (∀ u, Kstar a D (-u) = Kstar a D u) ∧
    (∀ u, u ≠ 0 → 0 < Kstar a D u) ∧
    LocallyIntegrable (Kstar a D) ∧
    StrictAntiOn (Kstar a D) (Ioi 0) ∧
    (∀ u, u ≠ 0 → Kstar a D u ≤ |u| ^ (-a)) ∧
    (∀ s ∈ Icc (0 : ℝ) 1, IntervalIntegrable (fun t => Kstar a D (s - t)) volume 0 1) ∧
    IsGreatest (row a D '' Icc (0 : ℝ) 1) (Rstar a D) ∧
    IntervalIntegrable (Kstar a D) volume 0 (1 / 2) ∧
    0 < Rstar a D := by
  have hI : ∀ b c : ℝ, IntervalIntegrable (Kstar a D) volume b c :=
    fun b c => Kstar_intervalIntegrable a D b c ha ha1 hD
  have hR : Rstar a D = 2 * Phi a D (1 / 2) := rfl
  refine ⟨Kstar_neg a D, fun u hu => Kstar_pos a D u ha hD hu,
    Kstar_locallyIntegrable a D ha ha1 hD, Kstar_strictAntiOn a D ha hD,
    fun u hu => Kstar_le_rpow a D u ha hD hu, fun s _ => ?_, ⟨?_, ?_⟩, hI 0 (1 / 2), ?_⟩
  · have h := (hI s (s - 1)).comp_sub_left s (by finiteness)
    simpa only [sub_self, sub_sub_cancel] using h
  · refine ⟨1 / 2, ⟨by norm_num, by norm_num⟩, ?_⟩
    rw [row_eq_Phi a D _ ha ha1 hD, hR]
    norm_num
    ring
  · rintro _ ⟨s, hs, rfl⟩
    rw [row_eq_Phi a D s ha ha1 hD, hR]
    exact Phi_sum_le a D s ha ha1 hD hs
  · rw [hR]
    refine mul_pos two_pos ?_
    refine intervalIntegral.intervalIntegral_pos_of_pos_on (hI 0 (1 / 2)) ?_ (by norm_num)
    intro x hx
    exact Kstar_pos a D x ha hD hx.1.ne'

open HomogHypothesis in
/-- Lemma `L:occupation-kernel-row` (lines 361-379) under the standing assumptions of
Section `S:spatial-occupation-foundation` (lines 4-10): `H:homog` with `α₀ = a`, a nonzero
covariance `Γ`, and `D = q - 2a` with `q = 4 - α`.  `D > 0` and `a < 1` follow from
`H:homog`; `Γ ≠ 0` is carried as stated and not used. -/
theorem occupation_kernel_row_paper {d : ℕ} {alpha a : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogCovariance d alpha a Γ μ) (_hΓ : Γ ≠ 0) (D : ℝ)
    (hD : D = (4 - alpha) - 2 * a) :
    (∀ u, Kstar a D (-u) = Kstar a D u) ∧
    (∀ u, u ≠ 0 → 0 < Kstar a D u) ∧
    LocallyIntegrable (Kstar a D) ∧
    StrictAntiOn (Kstar a D) (Ioi 0) ∧
    (∀ u, u ≠ 0 → Kstar a D u ≤ |u| ^ (-a)) ∧
    (∀ s ∈ Icc (0 : ℝ) 1, IntervalIntegrable (fun t => Kstar a D (s - t)) volume 0 1) ∧
    IsGreatest (row a D '' Icc (0 : ℝ) 1) (Rstar a D) ∧
    IntervalIntegrable (Kstar a D) volume 0 (1 / 2) ∧
    0 < Rstar a D := by
  have hD0 : 0 < D := by
    have := hH.threshold
    have := hH.alpha0_lt_one
    rw [hD]
    linarith
  exact occupation_kernel_row a D hH.alpha0_pos hH.alpha0_lt_one hD0

/-! ### The physical two-point integral (`L:spatial-physical-pair`, lines 12-33) -/

open HomogHypothesis

/-- The physical pair measure `ν(dx, dy) = dx Γ(dy)` on `ℝ^d × ℝ^d` (line 13). -/
abbrev pairMeasure {d : ℕ} (Γ : Measure (Rd d)) : Measure (Rd d × Rd d) := volume.prod Γ

/-- `B_Γ(f,h) = ∫ f(x) h(x-y) ν(dx,dy)` of `E:spatial-physical-pair` (lines 15-17), as an
extended nonnegative (lower Lebesgue) integral of `[0,∞]`-valued functions. -/
def pairing {d : ℕ} (Γ : Measure (Rd d)) (f h : Rd d → ℝ≥0∞) : ℝ≥0∞ :=
  ∫⁻ p, f p.1 * h (p.1 - p.2) ∂(pairMeasure Γ)

/-- Null-set transfer (TeX lines 26-29): for a locally finite `Γ`, a property that holds
for Lebesgue-a.e. `x` holds `ν`-a.e. at both positions `x` and `x - y`.  No measurability
of the property is assumed (an arbitrary Lebesgue null set has a Borel null superset). -/
theorem ae_pair_of_ae {d : ℕ} (Γ : Measure (Rd d)) [IsLocallyFiniteMeasure Γ]
    {P : Rd d → Prop} (hP : ∀ᵐ x ∂(volume : Measure (Rd d)), P x) :
    ∀ᵐ p ∂(pairMeasure Γ), P p.1 ∧ P (p.1 - p.2) := by
  obtain ⟨N, hsub, hN, hN0⟩ := exists_measurable_superset_of_null (ae_iff.1 hP)
  have h1 : pairMeasure Γ {p | p.1 ∈ N} = 0 := by
    have : {p : Rd d × Rd d | p.1 ∈ N} = N ×ˢ univ := by ext p; simp
    rw [this, Measure.prod_prod, hN0, zero_mul]
  have h2 : pairMeasure Γ {p | p.1 - p.2 ∈ N} = 0 := by
    have hm : MeasurableSet {p : Rd d × Rd d | p.1 - p.2 ∈ N} :=
      (measurable_fst.sub measurable_snd) hN
    rw [pairMeasure, Measure.prod_apply_symm hm]
    have hy : ∀ y : Rd d,
        volume ((fun x : Rd d => (x, y)) ⁻¹' {p : Rd d × Rd d | p.1 - p.2 ∈ N}) = 0 := by
      intro y
      have : (fun x : Rd d => (x, y)) ⁻¹' {p : Rd d × Rd d | p.1 - p.2 ∈ N} =
          (fun x => x + -y) ⁻¹' N := by
        ext x; simp [sub_eq_add_neg]
      rw [this, measure_preimage_add_right, hN0]
    simp only [hy, lintegral_zero]
  have h3 : pairMeasure Γ ({p | p.1 ∈ N} ∪ {p | p.1 - p.2 ∈ N}) = 0 :=
    measure_union_null h1 h2
  refine measure_mono_null (fun p hp => ?_) h3
  have hp' : ¬ (P p.1 ∧ P (p.1 - p.2)) := hp
  rcases not_and_or.1 hp' with hq | hq
  · exact Or.inl (hsub (show p.1 ∈ {x | ¬ P x} from hq))
  · exact Or.inr (hsub (show p.1 - p.2 ∈ {x | ¬ P x} from hq))

/-- Lemma `L:spatial-physical-pair` (lines 12-33) for a locally finite `Γ` on `ℝ^d`:
(1) `ν` is sigma-finite; (2) `B_Γ(f,h)` is representative independent: Lebesgue-a.e.
equal `[0,∞]`-valued functions give the same value (no measurability needed);
(3) for Lebesgue-a.e. measurable `f, h` the integrand `f(x) h(x-y)` is `ν`-a.e.
measurable (measurable in the `ν` completion); (4) Lebesgue-a.e. convergence of real
functions transfers to `ν`-a.e. convergence at both positions `x` and `x - y`. -/
theorem spatial_physical_pair {d : ℕ} (Γ : Measure (Rd d)) [IsLocallyFiniteMeasure Γ] :
    SigmaFinite (pairMeasure Γ) ∧
    (∀ f f' h h' : Rd d → ℝ≥0∞, f =ᵐ[volume] f' → h =ᵐ[volume] h' →
      pairing Γ f h = pairing Γ f' h') ∧
    (∀ f h : Rd d → ℝ≥0∞, AEMeasurable f volume → AEMeasurable h volume →
      AEMeasurable (fun p : Rd d × Rd d => f p.1 * h (p.1 - p.2)) (pairMeasure Γ)) ∧
    (∀ (F : ℕ → Rd d → ℝ) (G : Rd d → ℝ),
      (∀ᵐ x ∂(volume : Measure (Rd d)), Tendsto (fun n => F n x) atTop (nhds (G x))) →
      ∀ᵐ p ∂(pairMeasure Γ), Tendsto (fun n => F n p.1) atTop (nhds (G p.1)) ∧
        Tendsto (fun n => F n (p.1 - p.2)) atTop (nhds (G (p.1 - p.2)))) := by
  refine ⟨inferInstance, fun f f' h h' hf hh => ?_, fun f h hf hh => ?_,
    fun F G hFG => ae_pair_of_ae Γ hFG⟩
  · refine lintegral_congr_ae ?_
    filter_upwards [ae_pair_of_ae Γ (hf.and hh)] with p hp
    rw [hp.1.1, hp.2.2]
  · refine ⟨fun p => hf.mk f p.1 * hh.mk h (p.1 - p.2), ?_, ?_⟩
    · exact (hf.measurable_mk.comp measurable_fst).mul
        (hh.measurable_mk.comp (measurable_fst.sub measurable_snd))
    · filter_upwards [ae_pair_of_ae Γ (hf.ae_eq_mk.and hh.ae_eq_mk)] with p hp
      rw [hp.1.1, hp.2.2]

/-- Lemma `L:spatial-physical-pair` (lines 12-33) under the standing assumptions of
Section `S:spatial-occupation-foundation` (lines 4-10): `H:homog` with `α₀ = a` and a
nonzero covariance `Γ`.  Only local finiteness of `Γ` (part of `H:homog`) is used;
`Γ ≠ 0` and the rest of `H:homog` are carried as stated and not used. -/
theorem spatial_physical_pair_paper {d : ℕ} {alpha a : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogCovariance d alpha a Γ μ) (_hΓ : Γ ≠ 0) :
    SigmaFinite (pairMeasure Γ) ∧
    (∀ f f' h h' : Rd d → ℝ≥0∞, f =ᵐ[volume] f' → h =ᵐ[volume] h' →
      pairing Γ f h = pairing Γ f' h') ∧
    (∀ f h : Rd d → ℝ≥0∞, AEMeasurable f volume → AEMeasurable h volume →
      AEMeasurable (fun p : Rd d × Rd d => f p.1 * h (p.1 - p.2)) (pairMeasure Γ)) ∧
    (∀ (F : ℕ → Rd d → ℝ) (G : Rd d → ℝ),
      (∀ᵐ x ∂(volume : Measure (Rd d)), Tendsto (fun n => F n x) atTop (nhds (G x))) →
      ∀ᵐ p ∂(pairMeasure Γ), Tendsto (fun n => F n p.1) atTop (nhds (G p.1)) ∧
        Tendsto (fun n => F n (p.1 - p.2)) atTop (nhds (G (p.1 - p.2)))) := by
  have := hH.Γ_radon
  exact spatial_physical_pair Γ

end StratonovichHAMSecondMoment.OccupationKernelRow
