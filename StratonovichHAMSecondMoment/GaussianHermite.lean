module

/-
Copyright 2026 Le Chen. SPDX-License-Identifier: Apache-2.0

Gaussian Hermite polynomials (a reusable foundation; no manuscript label of its
own).

Source: `notes/notes_stratonovich_ham_second_moment.tex` (main TeX) at commit
`a284420`.  The proof of `L:fock-form` (lines 2515-2517) and the proof of
`E:occupied-multiplication` inside `P:mild-construction` (lines 1805-1810) use
"normalized Hermite polynomials", for which multiplication by the coordinate
`g_i` acts by `g_i h_k = √(k_i+1) h_{k+e_i} + √(k_i) h_{k-e_i}`, and the
orthonormality of the products `h_k` under independent standard Gaussians.
The TeX takes these facts from Janson (cited at lines 2467-2468).  This module
proves them.

Contents (everything proved, nothing supplied):
* `hermR n`: Mathlib's probabilists' Hermite polynomial `He_n`
  (`Polynomial.hermite`) with real coefficients; `He n x` its value.
  The Appell property `He_{n+1}' = (n+1) He_n` (`derivative_hermR_succ`; absent
  from Mathlib) and the three-term recurrence
  `He_{n+2} = x He_{n+1} - (n+1) He_n` (`hermR_succ_succ`).
* `gE p = ∫ p dN(0,1)` for a real polynomial `p`; every polynomial is
  integrable (`integrable_eval`).
* The integration-by-parts shift `E[He_{n+1} f] = E[He_n f']` for polynomial
  `f` (`gE_hermR_succ_mul`, function form `integral_He_succ_mul`), from
  `GaussianIBP.integral_mul_eq_integral_deriv`, and its iterate
  `E[He_n f] = E[f^{(n)}]` (`gE_hermR_mul`).
* Orthogonality `E[He_n He_m] = n! δ_{nm}` (`integral_He_mul_He`).
* The normalized `hn n = He_n/√(n!)`: orthonormal (`integral_hn_mul_hn`) with
  `x hn_n = √(n+1) hn_{n+1} + √n hn_{n-1}` (`mul_hn`; at `n = 0` the second
  term has coefficient `0`).
* Multi-index products `hk k x = ∏_i hn_{k_i}(x_i)` on `Fin m → ℝ`,
  orthonormal under `GaussianIBP.stdPi m` (`integral_hk_mul_hk`, with
  integrability `integrable_hk_mul_hk`), with the coordinate recurrence
  `x_i hk_k = √(k_i+1) hk_{k+e_i} + √(k_i) hk_{k-e_i}` (`coord_mul_hk`, where
  `e_i = Pi.single i 1` and `k - e_i` is truncated subtraction; at `k_i = 0`
  the second coefficient is `0`), `hk 0 = 1` and `hk e_i = x_i`.
* The spanning step used for `E:occupied-multiplication`: every monomial
  `x^k` with `|k| ≤ n` is a real combination of the `hk l` with `|l| ≤ n`
  (`monomial_mem_hermiteSpan`), hence so is every real polynomial of total
  degree at most `n` (`mvPolynomial_mem_hermiteSpan`).

Junk values: none of the statements depends on one.  `√(n!) > 0`, every
integral comes with its integrability, and the truncated subtraction
`k - e_i` only appears multiplied by `√(k_i)`, which is `0` exactly when the
subtraction truncates.
-/
public import Mathlib
public import StratonovichHAMSecondMoment.GaussianIBP

@[expose] public section

noncomputable section

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Polynomial Finset
open scoped Nat

namespace StratonovichHAMSecondMoment.GaussianHermite

/-! ### One variable: the polynomials -/

/-- The probabilists' Hermite polynomial `He_n` (Mathlib's `Polynomial.hermite`)
with real coefficients. -/
def hermR (n : ℕ) : ℝ[X] := (hermite n).map (Int.castRingHom ℝ)

/-- The value `He_n(x)`. -/
def He (n : ℕ) (x : ℝ) : ℝ := (hermR n).eval x

/-- Auxiliary (absent from Mathlib): the Appell property over `ℤ`,
`He_{n+1}' = (n+1) He_n`. -/
theorem derivative_hermite_succ : ∀ n : ℕ,
    derivative (hermite (n + 1)) = ((n + 1 : ℕ) : ℤ[X]) * hermite n
  | 0 => by simp [hermite_zero]
  | n + 1 => by
    have ih := derivative_hermite_succ n
    rw [hermite_succ (n + 1), derivative_sub, derivative_mul, derivative_X, ih,
      derivative_mul, derivative_natCast, zero_mul, zero_add]
    rw [hermite_succ n]; push_cast; ring

/-- `He_0 = 1`. -/
theorem hermR_zero : hermR 0 = 1 := by simp [hermR]

/-- `He_{n+1} = x He_n - He_n'`. -/
theorem hermR_succ (n : ℕ) : hermR (n + 1) = X * hermR n - derivative (hermR n) := by
  simp only [hermR, hermite_succ, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_X,
    derivative_map]

/-- The Appell property `He_{n+1}' = (n+1) He_n`. -/
theorem derivative_hermR_succ (n : ℕ) :
    derivative (hermR (n + 1)) = ((n : ℝ[X]) + 1) * hermR n := by
  simp only [hermR, derivative_map, derivative_hermite_succ, Polynomial.map_mul,
    Polynomial.map_natCast]
  push_cast; ring

/-- The three-term recurrence `He_{n+2} = x He_{n+1} - (n+1) He_n`. -/
theorem hermR_succ_succ (n : ℕ) :
    hermR (n + 2) = X * hermR (n + 1) - ((n : ℝ[X]) + 1) * hermR n := by
  rw [hermR_succ (n + 1), derivative_hermR_succ]

/-- `He_n` is monic. -/
theorem hermR_monic (n : ℕ) : (hermR n).Monic := (hermite_monic n).map _

/-- `He_n` has degree `n`. -/
theorem natDegree_hermR (n : ℕ) : (hermR n).natDegree = n := by
  rw [hermR, (hermite_monic n).natDegree_map, natDegree_hermite]

/-- Auxiliary: `He_n^{(n)} = n!` as a constant polynomial. -/
theorem iterate_derivative_hermR_self (n : ℕ) :
    derivative^[n] (hermR n) = C (n ! : ℝ) := by
  have hdeg : (derivative^[n] (hermR n)).natDegree ≤ 0 := by
    have := natDegree_iterate_derivative (hermR n) n
    rw [natDegree_hermR] at this; omega
  have hc : (hermR n).coeff n = 1 := by
    have := (hermR_monic n).coeff_natDegree; rwa [natDegree_hermR] at this
  rw [eq_C_of_natDegree_le_zero hdeg, coeff_iterate_derivative, zero_add,
    Nat.descFactorial_self, hc]
  simp

/-- `He_n' = n He_{n-1}` (for `n = 0` both sides are `0`). -/
theorem derivative_hermR (n : ℕ) :
    derivative (hermR n) = (n : ℝ[X]) * hermR (n - 1) := by
  cases n with
  | zero => simp [hermR_zero]
  | succ n => rw [derivative_hermR_succ]; simp

/-- `x He_n = He_{n+1} + n He_{n-1}`. -/
theorem X_mul_hermR (n : ℕ) :
    X * hermR n = hermR (n + 1) + (n : ℝ[X]) * hermR (n - 1) := by
  rw [hermR_succ, derivative_hermR]; ring

/-! ### One variable: Gaussian integrals -/

/-- Every real polynomial is integrable against `N(0,1)`. -/
theorem integrable_eval (p : ℝ[X]) :
    Integrable (fun x => p.eval x) (gaussianReal 0 1) := by
  have h : (fun x => p.eval x) =
      fun x => ∑ i ∈ range (p.natDegree + 1), p.coeff i * x ^ i := by
    funext x; exact eval_eq_sum_range x
  rw [h]
  exact integrable_finsetSum _ fun i _ =>
    (GaussianIBP.integrable_pow_gaussian i).const_mul _

/-- The Gaussian expectation of a real polynomial. -/
def gE (p : ℝ[X]) : ℝ := ∫ x, p.eval x ∂gaussianReal 0 1

/-- Auxiliary: additivity of `gE`. -/
theorem gE_add (p q : ℝ[X]) : gE (p + q) = gE p + gE q := by
  simp only [gE, eval_add]; exact integral_add (integrable_eval p) (integrable_eval q)

/-- Auxiliary: `gE` of a difference. -/
theorem gE_sub (p q : ℝ[X]) : gE (p - q) = gE p - gE q := by
  simp only [gE, eval_sub]; exact integral_sub (integrable_eval p) (integrable_eval q)

/-- Auxiliary: `gE` of a constant (`N(0,1)` is a probability measure). -/
theorem gE_C (c : ℝ) : gE (C c) = c := by simp [gE]

/-- Gaussian integration by parts on polynomials: `E[x p] = E[p']`. -/
theorem gE_X_mul (p : ℝ[X]) : gE (X * p) = gE (derivative p) := by
  have h := GaussianIBP.integral_mul_eq_integral_deriv (fun x => p.eval x)
    (fun x => (derivative p).eval x) (fun x => p.hasDerivAt x) (integrable_eval p)
    ((integrable_eval (X * p)).congr (ae_of_all _ fun x => by simp)) (integrable_eval _)
  simpa [gE] using h

/-- The shift `E[He_{n+1} f] = E[He_n f']` for a polynomial `f`. -/
theorem gE_hermR_succ_mul (n : ℕ) (q : ℝ[X]) :
    gE (hermR (n + 1) * q) = gE (hermR n * derivative q) := by
  have h1 : hermR (n + 1) * q = X * (hermR n * q) - derivative (hermR n) * q := by
    rw [hermR_succ]; ring
  have h2 : derivative (hermR n * q) = derivative (hermR n) * q + hermR n * derivative q :=
    derivative_mul
  rw [h1, gE_sub, gE_X_mul, h2, gE_add]; ring

/-- The iterated shift `E[He_n f] = E[f^{(n)}]`. -/
theorem gE_hermR_mul (n : ℕ) (q : ℝ[X]) :
    gE (hermR n * q) = gE (derivative^[n] q) := by
  induction n generalizing q with
  | zero => simp [hermR_zero]
  | succ n ih => rw [gE_hermR_succ_mul, ih, Function.iterate_succ_apply]

/-- Polynomial form of the orthogonality: `E[He_n He_m] = n! δ_{nm}`. -/
theorem gE_hermR_mul_hermR (n m : ℕ) :
    gE (hermR n * hermR m) = if n = m then (n ! : ℝ) else 0 := by
  rcases lt_trichotomy n m with h | h | h
  · rw [mul_comm, gE_hermR_mul, iterate_derivative_eq_zero (by rw [natDegree_hermR]; exact h)]
    simpa [h.ne] using gE_C 0
  · subst h; rw [gE_hermR_mul, iterate_derivative_hermR_self, gE_C]; simp
  · rw [gE_hermR_mul, iterate_derivative_eq_zero (by rw [natDegree_hermR]; exact h)]
    simpa [h.ne'] using gE_C 0

/-- **Orthogonality** `E[He_n(g) He_m(g)] = n! δ_{nm}` for `g ~ N(0,1)`, with
integrability. -/
theorem integral_He_mul_He (n m : ℕ) :
    Integrable (fun x => He n x * He m x) (gaussianReal 0 1) ∧
      ∫ x, He n x * He m x ∂gaussianReal 0 1 = if n = m then (n ! : ℝ) else 0 := by
  refine ⟨by simpa [He] using integrable_eval (hermR n * hermR m), ?_⟩
  rw [← gE_hermR_mul_hermR]; simp [gE, He]

/-- **The shift** `E[He_{n+1}(g) f(g)] = E[He_n(g) f'(g)]` for a real polynomial
`f`, with integrability of both integrands. -/
theorem integral_He_succ_mul (n : ℕ) (q : ℝ[X]) :
    Integrable (fun x => He (n + 1) x * q.eval x) (gaussianReal 0 1) ∧
      Integrable (fun x => He n x * (derivative q).eval x) (gaussianReal 0 1) ∧
      ∫ x, He (n + 1) x * q.eval x ∂gaussianReal 0 1 =
        ∫ x, He n x * (derivative q).eval x ∂gaussianReal 0 1 := by
  refine ⟨by simpa [He] using integrable_eval (hermR (n + 1) * q),
    by simpa [He] using integrable_eval (hermR n * derivative q), ?_⟩
  have := gE_hermR_succ_mul n q
  simpa [gE, He] using this

/-! ### One variable: normalized Hermite polynomials -/

/-- The normalized Hermite polynomial `He_n/√(n!)`. -/
def hnPoly (n : ℕ) : ℝ[X] := C (√(n ! : ℝ))⁻¹ * hermR n

/-- The normalized Hermite function `hn n x = He_n(x)/√(n!)`. -/
def hn (n : ℕ) (x : ℝ) : ℝ := (hnPoly n).eval x

/-- `hn n x = He_n(x)/√(n!)`. -/
theorem hn_eq (n : ℕ) (x : ℝ) : hn n x = He n x / √(n ! : ℝ) := by
  simp [hn, hnPoly, He, div_eq_inv_mul]

/-- Auxiliary: `√(n!) > 0`. -/
theorem sqrt_factorial_pos (n : ℕ) : 0 < √(n ! : ℝ) :=
  Real.sqrt_pos.2 (by exact_mod_cast Nat.factorial_pos n)

/-- `hn_0 = 1`. -/
theorem hn_zero (x : ℝ) : hn 0 x = 1 := by simp [hn_eq, He, hermR_zero]

/-- `hn_1(x) = x`. -/
theorem hn_one (x : ℝ) : hn 1 x = x := by
  simp [hn_eq, He, hermR_succ, hermR_zero]

/-- Every product `hn n * hn m` is integrable against `N(0,1)`. -/
theorem integrable_hn_mul_hn (n m : ℕ) :
    Integrable (fun x => hn n x * hn m x) (gaussianReal 0 1) := by
  simpa [hn] using integrable_eval (hnPoly n * hnPoly m)

/-- **Orthonormality** of the normalized Hermite polynomials under `N(0,1)`. -/
theorem integral_hn_mul_hn (n m : ℕ) :
    ∫ x, hn n x * hn m x ∂gaussianReal 0 1 = if n = m then 1 else 0 := by
  have h : (fun x => hn n x * hn m x) =
      fun x => ((√(n ! : ℝ))⁻¹ * (√(m ! : ℝ))⁻¹) * (He n x * He m x) := by
    funext x; rw [hn_eq, hn_eq]; ring
  rw [h, integral_const_mul, (integral_He_mul_He n m).2]
  split_ifs with hnm
  · subst hnm
    have := sqrt_factorial_pos n
    rw [← mul_inv, Real.mul_self_sqrt (by positivity)]
    exact inv_mul_cancel₀ (by exact_mod_cast (Nat.factorial_pos n).ne')
  · simp

/-- **Recurrence** `x hn_n = √(n+1) hn_{n+1} + √n hn_{n-1}` (at `n = 0` the
second coefficient is `0`). -/
theorem mul_hn (n : ℕ) (x : ℝ) :
    x * hn n x = √((n : ℝ) + 1) * hn (n + 1) x + √(n : ℝ) * hn (n - 1) x := by
  have hrec : x * He n x = He (n + 1) x + n * He (n - 1) x := by
    have := congrArg (eval x) (X_mul_hermR n)
    simpa [He] using this
  have hs : √((n + 1)! : ℝ) = √((n : ℝ) + 1) * √(n ! : ℝ) := by
    rw [Nat.factorial_succ, Nat.cast_mul, Real.sqrt_mul (by positivity)]; push_cast; ring
  have hpos := sqrt_factorial_pos n
  have h1 : 0 < √((n : ℝ) + 1) := Real.sqrt_pos.2 (by positivity)
  rw [hn_eq, hn_eq, hn_eq, hs]
  cases n with
  | zero => simp at hrec ⊢; rw [hrec]
  | succ k =>
    simp only [Nat.add_sub_cancel] at hrec ⊢
    have hs' : √((k + 1)! : ℝ) = √((k : ℝ) + 1) * √(k ! : ℝ) := by
      rw [Nat.factorial_succ, Nat.cast_mul, Real.sqrt_mul (by positivity)]; push_cast; ring
    rw [hs'] at hpos ⊢
    have hk := sqrt_factorial_pos k
    have h2 : 0 < √((k : ℝ) + 1) := Real.sqrt_pos.2 (by positivity)
    have hsq : √((k : ℝ) + 1) * √((k : ℝ) + 1) = (k : ℝ) + 1 :=
      Real.mul_self_sqrt (by positivity)
    push_cast at hrec ⊢
    field_simp
    rw [Real.sq_sqrt (by positivity)]
    linarith [hrec]

/-! ### Several variables -/

variable {m : ℕ}

/-- The multi-index Hermite function `hk k x = ∏_i hn_{k_i}(x_i)`. -/
def hk (k : Fin m → ℕ) (x : Fin m → ℝ) : ℝ := ∏ i, hn (k i) (x i)

/-- The unit multi-index `e_i`. -/
abbrev unitIdx (i : Fin m) : Fin m → ℕ := Pi.single i 1

/-- `hk_0 = 1`. -/
theorem hk_zero (x : Fin m → ℝ) : hk 0 x = 1 := by simp [hk, hn_zero]

/-- `hk_{e_i}(x) = x_i`. -/
theorem hk_unitIdx (i : Fin m) (x : Fin m → ℝ) : hk (unitIdx i) x = x i := by
  rw [hk, ← Finset.mul_prod_erase univ _ (mem_univ i)]
  rw [Finset.prod_eq_one fun j hj => by
    simp [unitIdx, Finset.ne_of_mem_erase hj, hn_zero]]
  simp [hn_one]

/-- Every product `hk k * hk l` is integrable under `stdPi m`. -/
theorem integrable_hk_mul_hk (k l : Fin m → ℕ) :
    Integrable (fun x => hk k x * hk l x) (GaussianIBP.stdPi m) := by
  have h : (fun x => hk k x * hk l x) = fun x => ∏ i, (hn (k i) (x i) * hn (l i) (x i)) := by
    funext x; simp [hk, Finset.prod_mul_distrib]
  rw [h, GaussianIBP.stdPi]
  exact Integrable.fintype_prod (f := fun i y => hn (k i) y * hn (l i) y)
    fun i => integrable_hn_mul_hn _ _

/-- **Orthonormality** of the multi-index Hermite functions under the product
Gaussian `stdPi m`. -/
theorem integral_hk_mul_hk (k l : Fin m → ℕ) :
    ∫ x, hk k x * hk l x ∂GaussianIBP.stdPi m = if k = l then 1 else 0 := by
  have h : (fun x => hk k x * hk l x) = fun x => ∏ i, (hn (k i) (x i) * hn (l i) (x i)) := by
    funext x; simp [hk, Finset.prod_mul_distrib]
  rw [h, GaussianIBP.stdPi,
    integral_fintype_prod_eq_prod (f := fun i y => hn (k i) y * hn (l i) y)]
  simp only [integral_hn_mul_hn]
  rw [Finset.prod_boole]
  simp [funext_iff]

/-- Auxiliary: `hk` splits off coordinate `i`. -/
theorem hk_eq_mul_erase (k : Fin m → ℕ) (i : Fin m) (x : Fin m → ℝ) :
    hk k x = hn (k i) (x i) * ∏ j ∈ univ.erase i, hn (k j) (x j) :=
  (Finset.mul_prod_erase univ (fun j => hn (k j) (x j)) (mem_univ i)).symm

/-- Auxiliary: changing the multi-index only at `i` changes only the `i`-th
factor. -/
theorem hk_eq_of_eq_off (k l : Fin m → ℕ) (i : Fin m) (hkl : ∀ j, j ≠ i → l j = k j)
    (x : Fin m → ℝ) :
    hk l x = hn (l i) (x i) * ∏ j ∈ univ.erase i, hn (k j) (x j) := by
  rw [hk_eq_mul_erase l i]
  congr 1
  exact Finset.prod_congr rfl fun j hj => by rw [hkl j (Finset.ne_of_mem_erase hj)]

/-- **Coordinate recurrence** `x_i hk_k = √(k_i+1) hk_{k+e_i} + √(k_i) hk_{k-e_i}`
(truncated subtraction; at `k_i = 0` the second coefficient is `0`). -/
theorem coord_mul_hk (k : Fin m → ℕ) (i : Fin m) (x : Fin m → ℝ) :
    x i * hk k x = √((k i : ℝ) + 1) * hk (k + unitIdx i) x +
      √(k i : ℝ) * hk (k - unitIdx i) x := by
  rw [hk_eq_mul_erase k i, hk_eq_of_eq_off k (k + unitIdx i) i
      (fun j hj => by simp [hj]),
    hk_eq_of_eq_off k (k - unitIdx i) i (fun j hj => by simp [hj])]
  have h1 : (k + unitIdx i) i = k i + 1 := by simp
  have h2 : (k - unitIdx i) i = k i - 1 := by simp
  rw [h1, h2, ← mul_assoc, mul_hn]; ring

/-! ### The spanning step -/

/-- Functions on `Fin m → ℝ` that are real combinations of the `hk l` with
`|l| = ∑_i l_i ≤ n`. -/
def HermiteSpan (m n : ℕ) (F : (Fin m → ℝ) → ℝ) : Prop :=
  ∃ c : (Fin m → ℕ) → ℝ, ∀ x, F x =
    ∑ l ∈ (Fintype.piFinset fun _ => range (n + 1)).filter (fun l => ∑ i, l i ≤ n),
      c l * hk l x

/-- Auxiliary: one-variable span of `hn_0, …, hn_j`. -/
def Span1 (j : ℕ) (f : ℝ → ℝ) : Prop :=
  ∃ b : ℕ → ℝ, ∀ x, f x = ∑ l ∈ range (j + 1), b l * hn l x

/-- Auxiliary: `Span1 j` is closed under addition. -/
theorem Span1.add {j : ℕ} {f g : ℝ → ℝ} (hf : Span1 j f) (hg : Span1 j g) :
    Span1 j (f + g) := by
  obtain ⟨b, hb⟩ := hf; obtain ⟨b', hb'⟩ := hg
  exact ⟨b + b', fun x => by simp [hb, hb', add_mul, Finset.sum_add_distrib]⟩

/-- Auxiliary: `Span1 j` is closed under scalar multiples. -/
theorem Span1.smul {j : ℕ} {f : ℝ → ℝ} (r : ℝ) (hf : Span1 j f) :
    Span1 j (fun x => r * f x) := by
  obtain ⟨b, hb⟩ := hf
  exact ⟨fun l => r * b l, fun x => by simp [hb, Finset.mul_sum, mul_assoc]⟩

/-- Auxiliary: `Span1 j ⊆ Span1 j'` for `j ≤ j'`. -/
theorem Span1.mono {j j' : ℕ} (hjj : j ≤ j') {f : ℝ → ℝ} (hf : Span1 j f) : Span1 j' f := by
  obtain ⟨b, hb⟩ := hf
  refine ⟨fun l => if l ≤ j then b l else 0, fun x => ?_⟩
  rw [hb, ← Finset.sum_subset (range_subset_range.2 (by omega : j + 1 ≤ j' + 1))]
  · exact Finset.sum_congr rfl fun l hl => by
      simp at hl; simp [show l ≤ j by omega]
  · intro l _ hl; simp at hl; simp [show ¬ l ≤ j by omega]

/-- Auxiliary: `0 ∈ Span1 j`. -/
theorem Span1.zero (j : ℕ) : Span1 j (fun _ => 0) := ⟨0, fun x => by simp⟩

/-- Auxiliary: `hn l ∈ Span1 j` for `l ≤ j`. -/
theorem Span1.of_hn {j l : ℕ} (hl : l ≤ j) : Span1 j (hn l) :=
  ⟨fun l' => if l' = l then 1 else 0, fun x => by
    rw [Finset.sum_eq_single l (fun b _ hb => by simp [hb]) (fun h => by simp at h; omega)]
    simp⟩

/-- Auxiliary: `Span1 j` is closed under finite sums. -/
theorem Span1.sum {j : ℕ} {ι : Type*} (s : Finset ι) (f : ι → ℝ → ℝ)
    (hf : ∀ a ∈ s, Span1 j (f a)) : Span1 j (fun x => ∑ a ∈ s, f a x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Span1.zero j
  | insert a s ha ih =>
    have := (hf a (mem_insert_self a s)).add (ih fun b hb => hf b (mem_insert_of_mem hb))
    convert this using 1
    funext x; simp [Finset.sum_insert ha]

/-- Auxiliary (triangularity): `x^j` lies in the span of `hn_0, …, hn_j`. -/
theorem pow_mem_span1 (j : ℕ) : Span1 j (fun x => x ^ j) := by
  induction j with
  | zero => exact ⟨fun l => if l = 0 then 1 else 0, fun x => by simp [hn_zero]⟩
  | succ j ih =>
    obtain ⟨b, hb⟩ := ih
    have hb' : ∀ x : ℝ, x ^ j = ∑ l ∈ range (j + 1), b l * hn l x := hb
    have h : (fun x : ℝ => x ^ (j + 1)) = fun x => ∑ l ∈ range (j + 1),
        (b l * √((l : ℝ) + 1) * hn (l + 1) x + b l * √(l : ℝ) * hn (l - 1) x) := by
      funext x
      rw [pow_succ, hb', Finset.sum_mul]
      exact Finset.sum_congr rfl fun l _ => by
        rw [mul_assoc, mul_comm (hn l x) x, mul_hn]; ring
    rw [h]
    refine Span1.sum _ _ fun l hl => ?_
    have hl' : l ≤ j := by simp at hl; omega
    have := ((Span1.of_hn (j := j + 1) (l := l + 1) (by omega)).smul (b l * √((l : ℝ) + 1))).add
      ((Span1.of_hn (j := j + 1) (l := l - 1) (by omega)).smul (b l * √(l : ℝ)))
    convert this using 1

/-- The spanning step: each monomial `x^k = ∏_i x_i^{k_i}` with `|k| ≤ n` lies
in `HermiteSpan m n`. -/
theorem monomial_mem_hermiteSpan (n : ℕ) (k : Fin m → ℕ) (hdk : ∑ i, k i ≤ n) :
    HermiteSpan m n (fun x => ∏ i, x i ^ k i) := by
  classical
  choose b hb using fun i => pow_mem_span1 (k i)
  simp only at hb
  set S := Fintype.piFinset fun i => range (k i + 1) with hS
  set D := (Fintype.piFinset fun _ : Fin m => range (n + 1)).filter (fun l => ∑ i, l i ≤ n)
  have hSD : S ⊆ D := by
    intro l hl
    simp only [hS, Fintype.mem_piFinset, mem_range] at hl
    have hle : ∑ i, l i ≤ n := (Finset.sum_le_sum fun i _ => by have := hl i; omega).trans hdk
    simp only [D, mem_filter, Fintype.mem_piFinset, mem_range]
    exact ⟨fun i => by
      have := Finset.single_le_sum (fun j _ => Nat.zero_le (l j)) (mem_univ i)
      omega, hle⟩
  refine ⟨fun l => if l ∈ S then ∏ i, b i (l i) else 0, fun x => ?_⟩
  have h1 : ∏ i, x i ^ k i = ∑ l ∈ S, (∏ i, b i (l i)) * hk l x := by
    rw [Finset.prod_congr rfl fun i _ => hb i (x i), Finset.prod_univ_sum]
    exact Finset.sum_congr rfl fun l _ => by simp [hk, Finset.prod_mul_distrib]
  show ∏ i, x i ^ k i = _
  rw [h1, ← Finset.sum_subset hSD]
  · exact Finset.sum_congr rfl fun l hl => by simp only [hl, ite_true]
  · intro l _ hl; simp only [hl, ite_false, zero_mul]

/-- `HermiteSpan m n` is closed under addition. -/
theorem HermiteSpan.add {n : ℕ} {F G : (Fin m → ℝ) → ℝ} (hF : HermiteSpan m n F)
    (hG : HermiteSpan m n G) : HermiteSpan m n (fun x => F x + G x) := by
  obtain ⟨c, hc⟩ := hF; obtain ⟨c', hc'⟩ := hG
  exact ⟨c + c', fun x => by simp [hc, hc', add_mul, Finset.sum_add_distrib]⟩

/-- `HermiteSpan m n` is closed under scalar multiples. -/
theorem HermiteSpan.smul {n : ℕ} {F : (Fin m → ℝ) → ℝ} (r : ℝ) (hF : HermiteSpan m n F) :
    HermiteSpan m n (fun x => r * F x) := by
  obtain ⟨c, hc⟩ := hF
  exact ⟨fun l => r * c l, fun x => by simp [hc, Finset.mul_sum, mul_assoc]⟩

/-- `0 ∈ HermiteSpan m n`. -/
theorem HermiteSpan.zero (n : ℕ) : HermiteSpan m n (fun _ => 0) := ⟨0, fun x => by simp⟩

/-- `HermiteSpan m n` is closed under finite sums. -/
theorem HermiteSpan.sum {n : ℕ} {ι : Type*} (s : Finset ι) (F : ι → (Fin m → ℝ) → ℝ)
    (hF : ∀ a ∈ s, HermiteSpan m n (F a)) : HermiteSpan m n (fun x => ∑ a ∈ s, F a x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using HermiteSpan.zero (m := m) n
  | insert a s ha ih =>
    have := (hF a (mem_insert_self a s)).add (ih fun b hb => hF b (mem_insert_of_mem hb))
    convert this using 1
    funext x; simp [Finset.sum_insert ha]

/-- The spanning step for polynomials: every real polynomial in `x_1, …, x_m` of
total degree at most `n` is, as a function, a real combination of the `hk l`
with `|l| ≤ n`. -/
theorem mvPolynomial_mem_hermiteSpan (n : ℕ) (p : MvPolynomial (Fin m) ℝ)
    (hp : p.totalDegree ≤ n) : HermiteSpan m n (fun x => MvPolynomial.eval x p) := by
  classical
  have key : ∀ s ∈ p.support, HermiteSpan m n
      (fun x => MvPolynomial.eval x (MvPolynomial.monomial s (p.coeff s))) := by
    intro s hs
    have hdeg : ∑ i, s i ≤ n := by
      have := MvPolynomial.le_totalDegree hs
      rw [Finsupp.sum_fintype _ _ (fun _ => rfl)] at this
      exact this.trans hp
    have := (monomial_mem_hermiteSpan n (fun i => s i) hdeg).smul (p.coeff s)
    convert this using 2 with x
    rw [MvPolynomial.eval_monomial, Finsupp.prod_fintype _ _ (fun _ => by simp)]
  have hsum : (fun x => MvPolynomial.eval x p) = fun x => ∑ s ∈ p.support,
      MvPolynomial.eval x (MvPolynomial.monomial s (p.coeff s)) := by
    funext x
    conv_lhs => rw [p.as_sum]
    rw [map_sum]
  rw [hsum]
  exact HermiteSpan.sum _ _ key

end StratonovichHAMSecondMoment.GaussianHermite
