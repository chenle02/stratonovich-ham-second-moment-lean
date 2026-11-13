module

/-
Copyright 2026 Le Chen. SPDX-License-Identifier: Apache-2.0

Gaussian Schwartz test functions, built by hand (Mathlib has no Gaussian
`SchwartzMap`).  This module has no manuscript label of its own: it is the
foundation for `P:masked-spectral-growth`
(`notes/integrated_covariance_foundation.tex`, revision a284420, lines 34-77),
whose proof (lines 56-66) applies the spectral convention
`E:masked-spectral-convention` (lines 15-19) "to the single Schwartz test
`e^{-r²|x|²/4} e^{-iy·x}`" and uses the Gaussian Fourier integral of
lines 61-64.  Everything here is auxiliary to the Lean proof route.

Contents:
* `poly_mul_exp_neg_sq_le`: `(1+s)^m e^{-cs²} ≤ e^{m²/(4c)}` for `s ≥ 0`,
  `c > 0`;
* `gauss c x = e^{-c‖x‖²}` on a real inner product space, its smoothness and
  the decay of all its derivatives (`gauss_decay`, from the Faà di Bruno bound
  `norm_iteratedFDeriv_comp_le` and the temperate growth of `‖x‖²`), and the
  Schwartz map `gaussSchwartz c hc` (`c > 0`);
* `gaussTest s hs w y`, the complex Schwartz map
  `x ↦ e^{-s‖x-w‖²} e^{-i⟨y,x⟩}` (`s > 0`): the real Gaussian, translated by
  `w` and modulated by the phase `e^{-i⟨y,x⟩}`;
* `gaussTest_fourier`: on `ℝ^d`, `∫ gaussTest(x) e^{i⟨ξ,x⟩} dx =
  (π/s)^{d/2} e^{i⟨ξ-y,w⟩} e^{-‖ξ-y‖²/(4s)}` (the identity of lines 61-64 for
  `w = 0`, `s = r²/4`), from Mathlib's
  `GaussianFourier.integral_cexp_neg_mul_sq_norm_add`.
-/

public import Mathlib
public import StratonovichHAMSecondMoment.HomogHypothesis

@[expose] public section

noncomputable section

set_option autoImplicit false

open MeasureTheory Real
open scoped Nat ContDiff

namespace StratonovichHAMSecondMoment.GaussianTest

/-- Auxiliary to the Lean proof route. `(1+s)^m e^{-cs²} ≤ e^{m²/(4c)}` for
`s ≥ 0` and `c > 0`, from `1 + s ≤ e^s` and `ms - cs² ≤ m²/(4c)`. -/
theorem poly_mul_exp_neg_sq_le (m : ℕ) {c : ℝ} (hc : 0 < c) {s : ℝ} (hs : 0 ≤ s) :
    (1 + s) ^ m * Real.exp (-(c * s ^ 2)) ≤ Real.exp ((m : ℝ) ^ 2 / (4 * c)) := by
  have h1 : (1 + s) ^ m ≤ Real.exp (m * s) := by
    calc (1 + s) ^ m ≤ (Real.exp s) ^ m := by
          gcongr
          linarith [Real.add_one_le_exp s]
      _ = Real.exp (m * s) := by rw [← Real.exp_nat_mul]
  have h2 : (m : ℝ) * s - c * s ^ 2 ≤ (m : ℝ) ^ 2 / (4 * c) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg (2 * c * s - m)]
  calc (1 + s) ^ m * Real.exp (-(c * s ^ 2))
      ≤ Real.exp (m * s) * Real.exp (-(c * s ^ 2)) :=
        mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    _ = Real.exp (m * s - c * s ^ 2) := by rw [← Real.exp_add]; ring_nf
    _ ≤ Real.exp ((m : ℝ) ^ 2 / (4 * c)) := Real.exp_le_exp.2 h2

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The real Gaussian `x ↦ e^{-c‖x‖²}`. -/
def gauss (c : ℝ) : E → ℝ := fun x => Real.exp (-(c * ‖x‖ ^ 2))

/-- Auxiliary to the Lean proof route. -/
theorem contDiff_gauss (c : ℝ) : ContDiff ℝ ∞ (gauss (E := E) c) :=
  ((contDiff_const.mul (contDiff_norm_sq ℝ)).neg).exp

/-- Auxiliary to the Lean proof route. All derivatives of `exp` at `y` have
norm at most `e^y`. -/
theorem norm_iteratedFDeriv_exp_le (i : ℕ) (y : ℝ) :
    ‖iteratedFDeriv ℝ i Real.exp y‖ ≤ Real.exp y := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_eq_iterate,
    Real.iter_deriv_exp, Real.norm_eq_abs, abs_of_pos (Real.exp_pos y)]

/-- Auxiliary to the Lean proof route. Decay of every derivative of the
Gaussian (`c > 0`): `‖x‖^k ‖D^n e^{-c‖x‖²}‖` is bounded. -/
theorem gauss_decay {c : ℝ} (hc : 0 < c) (k n : ℕ) :
    ∃ C : ℝ, ∀ x : E, ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (gauss (E := E) c) x‖ ≤ C := by
  have hq : (fun x : E => -(c * ‖x‖ ^ 2)).HasTemperateGrowth := by
    have := (Function.HasTemperateGrowth.const c).mul (Function.hasTemperateGrowth_norm_sq (H := E))
    exact this.neg
  obtain ⟨l, C₁, hC₁, hq'⟩ := hq.norm_iteratedFDeriv_le_uniform n
  refine ⟨n ! * (C₁ + 1) ^ n * Real.exp (((k + l * n : ℕ) : ℝ) ^ 2 / (4 * c)), fun x => ?_⟩
  set s := ‖x‖ with hs_def
  have hs : 0 ≤ s := norm_nonneg x
  set D := (C₁ + 1) * (1 + s) ^ l with hD_def
  have hD1 : 1 ≤ D := by
    have : 1 ≤ (1 + s) ^ l := one_le_pow₀ (by linarith)
    nlinarith
  have hcomp : gauss (E := E) c = Real.exp ∘ (fun x : E => -(c * ‖x‖ ^ 2)) := rfl
  have hbound := norm_iteratedFDeriv_comp_le (n := n) (N := ∞) contDiff_exp hq.1
    (mod_cast le_top) x (C := Real.exp (-(c * ‖x‖ ^ 2))) (D := D)
    (fun i _ => norm_iteratedFDeriv_exp_le i _)
    (fun i hi1 hin => by
      refine (hq' i hin x).trans ?_
      calc C₁ * (1 + ‖x‖) ^ l ≤ D := by
            rw [hD_def]
            have : 0 ≤ (1 + s) ^ l := by positivity
            nlinarith
        _ ≤ D ^ i := le_self_pow₀ hD1 (by omega))
  rw [← hcomp] at hbound
  have hxk : s ^ k ≤ (1 + s) ^ k := pow_le_pow_left₀ hs (by linarith) k
  have hkey := poly_mul_exp_neg_sq_le (k + l * n) hc hs
  calc s ^ k * ‖iteratedFDeriv ℝ n (gauss c) x‖
      ≤ (1 + s) ^ k * (n ! * Real.exp (-(c * s ^ 2)) * D ^ n) := by
        gcongr
    _ = n ! * (C₁ + 1) ^ n * ((1 + s) ^ (k + l * n) * Real.exp (-(c * s ^ 2))) := by
        rw [hD_def, mul_pow, ← pow_mul, pow_add]
        ring
    _ ≤ n ! * (C₁ + 1) ^ n * Real.exp (((k + l * n : ℕ) : ℝ) ^ 2 / (4 * c)) := by
        gcongr

/-- The Gaussian `x ↦ e^{-c‖x‖²}` as a real Schwartz map (`c > 0`). -/
def gaussSchwartz (c : ℝ) (hc : 0 < c) : SchwartzMap E ℝ where
  toFun := gauss c
  smooth' := contDiff_gauss c
  decay' := gauss_decay hc

/-- Auxiliary to the Lean proof route. -/
@[simp] theorem gaussSchwartz_apply (c : ℝ) (hc : 0 < c) (x : E) :
    gaussSchwartz c hc x = Real.exp (-(c * ‖x‖ ^ 2)) := rfl

/-- Auxiliary to the Lean proof route. The phase `x ↦ e^{-i⟨y,x⟩}` has
temperate growth. -/
theorem phase_hasTemperateGrowth (y : E) :
    (fun x : E => Complex.exp (((-inner ℝ y x : ℝ) : ℂ) * Complex.I)).HasTemperateGrowth :=
  Complex.hasTemperateGrowth_exp_mul_I.comp
    (Function.hasTemperateGrowth_inner_right (H := E) y).neg

/-- Auxiliary to the Lean proof route. The translation `x ↦ x - w` has
temperate growth. -/
theorem sub_hasTemperateGrowth (w : E) : (fun x : E => x - w).HasTemperateGrowth :=
  (ContinuousLinearMap.id ℝ E).hasTemperateGrowth.sub (Function.HasTemperateGrowth.const w)

omit [InnerProductSpace ℝ E] in
/-- Auxiliary to the Lean proof route. The translation `x ↦ x - w` has the
polynomial lower bound required by `SchwartzMap.compCLM`. -/
theorem sub_upper (w : E) : ∃ (k : ℕ) (C : ℝ), ∀ x : E, ‖x‖ ≤ C * (1 + ‖x - w‖) ^ k :=
  ⟨1, 1 + ‖w‖, fun x => by
    have h1 : ‖x‖ ≤ ‖x - w‖ + ‖w‖ := by
      calc ‖x‖ = ‖(x - w) + w‖ := by rw [sub_add_cancel]
        _ ≤ ‖x - w‖ + ‖w‖ := norm_add_le _ _
    have h2 := norm_nonneg (x - w)
    have h3 := norm_nonneg w
    rw [pow_one]
    nlinarith⟩

/-- The complex Schwartz test `x ↦ e^{-i⟨y,x⟩} e^{-s‖x-w‖²}` (`s > 0`). -/
def gaussTest (s : ℝ) (hs : 0 < s) (w y : E) : SchwartzMap E ℂ :=
  SchwartzMap.smulLeftCLM ℂ (fun x : E => Complex.exp (((-inner ℝ y x : ℝ) : ℂ) * Complex.I))
    (SchwartzMap.compCLM ℝ (sub_hasTemperateGrowth w) (sub_upper w)
      (SchwartzMap.postcompCLM (𝕜 := ℝ) Complex.ofRealCLM (gaussSchwartz s hs)))

/-- The values of the test: `e^{-i⟨y,x⟩} e^{-s‖x-w‖²}`. -/
theorem gaussTest_apply (s : ℝ) (hs : 0 < s) (w y x : E) :
    gaussTest s hs w y x =
      Complex.exp (-(Complex.I * (inner ℝ y x : ℝ))) * (Real.exp (-(s * ‖x - w‖ ^ 2)) : ℂ) := by
  rw [gaussTest, SchwartzMap.smulLeftCLM_apply_apply (phase_hasTemperateGrowth y)]
  simp only [SchwartzMap.compCLM_apply, Function.comp_apply, SchwartzMap.postcompCLM_apply,
    gaussSchwartz_apply, Complex.ofRealCLM_apply, smul_eq_mul]
  congr 2
  push_cast
  ring

open HomogHypothesis in
/-- The Gaussian Fourier integral of the test (lines 61-64 of
`integrated_covariance_foundation.tex` when `w = 0`, `s = r²/4`):
`∫ e^{-i⟨y,x⟩} e^{-s‖x-w‖²} e^{i⟨ξ,x⟩} dx =
(π/s)^{d/2} e^{i⟨ξ-y,w⟩} e^{-‖ξ-y‖²/(4s)}` on `ℝ^d`, `s > 0`. -/
theorem gaussTest_fourier {d : ℕ} (s : ℝ) (hs : 0 < s) (w y ξ : Rd d) :
    ∫ x, gaussTest s hs w y x * Complex.exp (Complex.I * (inner ℝ ξ x : ℝ)) =
      ((Real.pi / s) ^ ((d : ℝ) / 2) : ℝ) * Complex.exp (Complex.I * (inner ℝ (ξ - y) w : ℝ)) *
        (Real.exp (-(‖ξ - y‖ ^ 2 / (4 * s))) : ℂ) := by
  have hpt : ∀ x : Rd d, gaussTest s hs w y x * Complex.exp (Complex.I * (inner ℝ ξ x : ℝ)) =
      Complex.exp (Complex.I * (inner ℝ (ξ - y) w : ℝ)) *
        Complex.exp (-(s : ℂ) * ‖x - w‖ ^ 2 + Complex.I * (inner ℝ (ξ - y) (x - w) : ℝ)) := by
    intro x
    rw [gaussTest_apply, Complex.ofReal_exp, ← Complex.exp_add, ← Complex.exp_add,
      ← Complex.exp_add]
    congr 1
    simp only [inner_sub_left, inner_sub_right, Complex.ofReal_sub, Complex.ofReal_neg,
      Complex.ofReal_mul, Complex.ofReal_pow]
    ring
  simp_rw [hpt]
  rw [integral_const_mul]
  rw [integral_sub_right_eq_self
    (fun v : Rd d => Complex.exp (-(s : ℂ) * ‖v‖ ^ 2 + Complex.I * (inner ℝ (ξ - y) v : ℝ))) w]
  rw [GaussianFourier.integral_cexp_neg_mul_sq_norm_add (by simpa using hs) Complex.I (ξ - y)]
  rw [finrank_euclideanSpace_fin]
  have hπ : ((Real.pi / s) ^ ((d : ℝ) / 2) : ℝ) = ((Real.pi : ℂ) / s) ^ ((d : ℂ) / 2) := by
    rw [Complex.ofReal_cpow (by positivity)]
    push_cast
    rfl
  rw [hπ]
  have he : Complex.I ^ 2 * (‖ξ - y‖ : ℂ) ^ 2 / (4 * (s : ℂ)) =
      ((-(‖ξ - y‖ ^ 2 / (4 * s)) : ℝ) : ℂ) := by
    push_cast
    rw [Complex.I_sq]
    ring
  rw [he, ← Complex.ofReal_exp]
  ring

end StratonovichHAMSecondMoment.GaussianTest
