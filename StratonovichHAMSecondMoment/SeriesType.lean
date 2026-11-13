module

/-
Copyright 2026 Le Chen. SPDX-License-Identifier: Apache-2.0

Scalar series and factorial foundation used by the coefficient-type arguments
of `notes/notes_stratonovich_ham_second_moment.tex` (main TeX file; line
numbers at revision a284420). The manuscript uses each of these elementary
facts inline, inside the proofs of labelled results, except `gamma_mid_sq_le`,
a standalone tool for which no manuscript line is claimed; none is a labelled
result itself. Formalized here, each in full and with nothing supplied:

* `sum_rpow_le_rpow_sum`: the finite `ℓ^ν` versus `ℓ^1` inequality
  `∑ a_k^ν ≤ (∑ a_k)^ν` for `ν ≥ 1` and `a_k ≥ 0` (used at lines 2001-2002,
  2676, 4678-4682, 5155-5159, 6054-6058, 6740-6743, 7258-7259).
* `seriesNu_summable_le`: for `ν ≥ 1` and `x ≥ 0`, the series
  `S_ν(x) = ∑_{k ≥ 0} x^k/(k!)^ν` converges and `S_ν(x) ≤ exp(ν x^{1/ν})`
  (lines 2001, 2768-2769, 3571-3572, 4678-4682, 5155-5159, 5617, 6054-6058,
  6740-6743, 7255-7256).
  Summability is part of the conclusion, since a Lean `tsum` of a
  non-summable family is `0`.
* `seriesNu_holder_le` and `seriesNu_le_two_exp_three`: the `β < 1` Hölder
  variant of lines 2670-2679 (inside the proof of
  `P:static-phase-all-orders`): for `1/2 ≤ β < 1`,
  `∑ x^n/(n!)^β ≤ 2^{1-β} exp(2β x^{1/β})`, by Hölder's inequality applied to
  `((2x^{1/β})^n/n!)^β · (2^{-βn/(1-β)})^{1-β}` exactly as in the TeX; and the
  displayed consequence `∑ x^n/(n!)^β ≤ 2 exp(3 x^{1/β})`, here for every
  `1/2 ≤ β ≤ 3` (the TeX uses `β = (3-α)/2 ∈ (1/2, 3/2)`).
* `factorial_sq_le_mul_factorial`: `r! s! ≥ (k!)^2` when `r + s = 2k`
  (lines 2754, 5119). Proof route (auxiliary to Lean, the TeX gives no proof):
  the central binomial coefficient is the largest, `Nat.choose_le_middle`.
* `factorial_ge_exp`, `factorial_le_exp`, `log_factorial_bounds`: the
  two-sided bounds `k log k - k + 1 ≤ log k! ≤ k log k - k + 1 + log k` for
  `k ≥ 1` (lines 7246-7247, inside the proof of `L:positive-series-type`).
  Proof route differs from the TeX (which integrates `log x` on `[1,k]`): an
  induction on `k` using `1 + x ≤ e^x`.
* `gamma_mid_sq_le`: `Γ((x+y)/2)^2 ≤ Γ(x)Γ(y)` for `x, y > 0`
  (log-convexity of Euler's Gamma function, `Real.convexOn_log_Gamma`),
  a general tool recorded for later coefficient comparisons.

All powers `(k!)^ν` with real `ν` are `Real.rpow` of the positive real `k!`,
so no junk value of `rpow` at a nonpositive base enters.
-/
public import Mathlib

@[expose] public section

noncomputable section

set_option autoImplicit false

open Real Finset Filter
open scoped Nat

namespace StratonovichHAMSecondMoment.SeriesType

/-! ### The finite `ℓ^ν` inequality -/

/-- The finite `ℓ^ν` versus `ℓ^1` inequality: for `ν ≥ 1` and nonnegative
`a_k`, `∑_{k<n} a_k^ν ≤ (∑_{k<n} a_k)^ν` (used inline at main TeX lines
2001-2002, 2676, 4678-4682, 5155-5159, 6054-6058, 6740-6743, 7258-7259). -/
theorem sum_rpow_le_rpow_sum {ν : ℝ} (hν : 1 ≤ ν) (a : ℕ → ℝ) (ha : ∀ k, 0 ≤ a k)
    (n : ℕ) : ∑ k ∈ range n, a k ^ ν ≤ (∑ k ∈ range n, a k) ^ ν := by
  induction n with
  | zero => simp [Real.zero_rpow (by linarith : ν ≠ 0)]
  | succ n ih =>
    rw [sum_range_succ, sum_range_succ]
    calc _ ≤ (∑ k ∈ range n, a k) ^ ν + a n ^ ν := by gcongr
      _ ≤ _ := Real.add_rpow_le_rpow_add (sum_nonneg fun k _ => ha k) (ha n) hν

/-- Auxiliary (Lean route): for `x ≥ 0` and `ν ≠ 0`,
`x^k/(k!)^ν = ((x^{1/ν})^k/k!)^ν`. -/
theorem term_eq_rpow {ν x : ℝ} (hν : ν ≠ 0) (hx : 0 ≤ x) (k : ℕ) :
    x ^ k / (k ! : ℝ) ^ ν = ((x ^ (1 / ν)) ^ k / (k ! : ℝ)) ^ ν := by
  have hk : (0 : ℝ) ≤ (k ! : ℝ) := by positivity
  rw [Real.div_rpow (pow_nonneg (Real.rpow_nonneg hx _) _) hk]
  congr 1
  rw [← Real.rpow_natCast (x ^ (1 / ν)) k, ← Real.rpow_mul hx, ← Real.rpow_mul hx,
    show 1 / ν * (k : ℝ) * ν = (k : ℝ) by field_simp, Real.rpow_natCast]

/-! ### The series `S_ν(x) = ∑ x^k/(k!)^ν` -/

/-- **The series bound `S_ν(x) ≤ exp(ν x^{1/ν})`** (main TeX lines 4678-4682,
5155-5159, 6054-6058, 6740-6743, 7255-7256, and inline at 2001, 2768-2769,
3571-3572, 5617): for `ν ≥ 1` and `x ≥ 0` the series
`∑_{k ≥ 0} x^k/(k!)^ν` converges and its sum is at most `exp(ν x^{1/ν})`.
Proof as in the TeX: write each term as `a_k^ν` with `a_k = (x^{1/ν})^k/k!`
and apply the `ℓ^ν` inequality to the exponential series. -/
theorem seriesNu_summable_le {ν x : ℝ} (hν : 1 ≤ ν) (hx : 0 ≤ x) :
    Summable (fun k : ℕ => x ^ k / (k ! : ℝ) ^ ν) ∧
      ∑' k : ℕ, x ^ k / (k ! : ℝ) ^ ν ≤ Real.exp (ν * x ^ (1 / ν)) := by
  have hν0 : ν ≠ 0 := by positivity
  set y := x ^ (1 / ν) with hydef
  have hy : 0 ≤ y := Real.rpow_nonneg hx _
  have hnn : ∀ k : ℕ, 0 ≤ x ^ k / (k ! : ℝ) ^ ν := fun k => by positivity
  have hpart : ∀ n, ∑ k ∈ range n, x ^ k / (k ! : ℝ) ^ ν ≤ Real.exp (ν * y) := by
    intro n
    simp_rw [term_eq_rpow hν0 hx]
    calc _ ≤ (∑ k ∈ range n, y ^ k / (k ! : ℝ)) ^ ν :=
          sum_rpow_le_rpow_sum hν _ (fun k => by positivity) n
      _ ≤ (Real.exp y) ^ ν := by
          gcongr
          exact Real.sum_le_exp_of_nonneg hy n
      _ = Real.exp (ν * y) := by rw [← Real.exp_mul]; ring_nf
  exact ⟨summable_of_sum_range_le hnn hpart, Real.tsum_le_of_sum_range_le hnn hpart⟩

/-- **The `β < 1` Hölder variant** (main TeX lines 2670-2679, inside the proof
of `P:static-phase-all-orders`): for `1/2 ≤ β < 1` and `x ≥ 0`, the series
`∑ x^n/(n!)^β` converges and is at most `2^{1-β} exp(2β x^{1/β})`.
Proof as in the TeX: Hölder's inequality with exponents `1/β`, `1/(1-β)`
applied to `((2x^{1/β})^n/n!)^β · (2^{-βn/(1-β)})^{1-β}`; the geometric sum
`∑ 2^{-βn/(1-β)}` is at most `2` because `β ≥ 1/2`. -/
theorem seriesNu_holder_le {β x : ℝ} (hβ1 : 1 / 2 ≤ β) (hβ2 : β < 1) (hx : 0 ≤ x) :
    Summable (fun k : ℕ => x ^ k / (k ! : ℝ) ^ β) ∧
      ∑' k : ℕ, x ^ k / (k ! : ℝ) ^ β ≤
        (2 : ℝ) ^ (1 - β) * Real.exp (2 * β * x ^ (1 / β)) := by
  have hβ0 : 0 < β := by linarith
  have hβ' : 0 < 1 - β := by linarith
  set y := x ^ (1 / β) with hydef
  have hy : 0 ≤ y := Real.rpow_nonneg hx _
  set r0 : ℝ := (2 : ℝ) ^ (-β) with hr0
  have hr0nn : 0 ≤ r0 := by positivity
  have hnn : ∀ k : ℕ, 0 ≤ x ^ k / (k ! : ℝ) ^ β := fun k => by positivity
  -- the Hölder factorization of each term
  have hfac : ∀ k : ℕ, x ^ k / (k ! : ℝ) ^ β =
      ((2 * y) ^ k / (k ! : ℝ)) ^ β * r0 ^ k := by
    intro k
    have h2 : ((2 : ℝ) ^ k) ^ β * r0 ^ k = 1 := by
      rw [hr0, ← Real.rpow_natCast ((2 : ℝ) ^ (-β)) k,
        ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2), ← Real.rpow_natCast (2 : ℝ) k,
        ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2), ← Real.rpow_add (by norm_num : (0:ℝ) < 2),
        show (k : ℝ) * β + -β * k = 0 by ring, Real.rpow_zero]
    rw [term_eq_rpow hβ0.ne' hx k, mul_pow, mul_div_assoc,
      Real.mul_rpow (by positivity) (by positivity)]
    calc ((y ^ k / (k ! : ℝ))) ^ β = (y ^ k / (k ! : ℝ)) ^ β * (((2 : ℝ) ^ k) ^ β * r0 ^ k) := by
          rw [h2, mul_one]
      _ = _ := by ring
  have hpq : (1 / β).HolderConjugate (1 / (1 - β)) :=
    Real.holderConjugate_one_div hβ0 hβ' (by ring)
  have hgeo : ∀ n, ∑ k ∈ range n, (r0 ^ k) ^ (1 / (1 - β)) ≤ 2 := by
    intro n
    have hq : r0 ^ (1 / (1 - β)) ≤ 1 / 2 := by
      rw [hr0, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
      have hle : -β * (1 / (1 - β)) ≤ -1 := by
        rw [neg_mul, neg_le_neg_iff, mul_one_div, le_div_iff₀ hβ']; linarith
      calc (2 : ℝ) ^ (-β * (1 / (1 - β))) ≤ (2 : ℝ) ^ (-1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) hle
        _ = 1 / 2 := by rw [Real.rpow_neg_one]; norm_num
    calc ∑ k ∈ range n, (r0 ^ k) ^ (1 / (1 - β))
        = ∑ k ∈ range n, (r0 ^ (1 / (1 - β))) ^ k := by
          refine sum_congr rfl fun k _ => ?_
          rw [← Real.rpow_natCast r0 k, ← Real.rpow_natCast _ k, ← Real.rpow_mul hr0nn,
            ← Real.rpow_mul hr0nn, mul_comm]
      _ ≤ ∑ k ∈ range n, (1 / 2 : ℝ) ^ k := by
          gcongr with k _
      _ ≤ 2 := sum_geometric_two_le n
  have hexp : ∀ n, ∑ k ∈ range n, (((2 * y) ^ k / (k ! : ℝ)) ^ β) ^ (1 / β) ≤
      Real.exp (2 * y) := by
    intro n
    calc _ = ∑ k ∈ range n, (2 * y) ^ k / (k ! : ℝ) := by
          refine sum_congr rfl fun k _ => ?_
          rw [← Real.rpow_mul (by positivity), mul_one_div_cancel hβ0.ne', Real.rpow_one]
      _ ≤ Real.exp (2 * y) := Real.sum_le_exp_of_nonneg (by positivity) n
  have hpart : ∀ n, ∑ k ∈ range n, x ^ k / (k ! : ℝ) ^ β ≤
      (2 : ℝ) ^ (1 - β) * Real.exp (2 * β * y) := by
    intro n
    simp_rw [hfac]
    have hH := Real.inner_le_Lp_mul_Lq_of_nonneg (range n) hpq
      (f := fun k => ((2 * y) ^ k / (k ! : ℝ)) ^ β) (g := fun k => r0 ^ k)
      (fun k _ => by positivity) (fun k _ => by positivity)
    refine hH.trans ?_
    rw [one_div_one_div, one_div_one_div, mul_comm ((2 : ℝ) ^ (1 - β))]
    have hA : (∑ k ∈ range n, (((2 * y) ^ k / (k ! : ℝ)) ^ β) ^ (1 / β)) ^ β ≤
        Real.exp (2 * β * y) := by
      calc _ ≤ (Real.exp (2 * y)) ^ β :=
            Real.rpow_le_rpow (sum_nonneg fun k _ => Real.rpow_nonneg (by positivity) _)
              (hexp n) hβ0.le
        _ = Real.exp (2 * β * y) := by rw [← Real.exp_mul]; ring_nf
    have hB : (∑ k ∈ range n, (r0 ^ k) ^ (1 / (1 - β))) ^ (1 - β) ≤ (2 : ℝ) ^ (1 - β) :=
      Real.rpow_le_rpow (sum_nonneg fun k _ => Real.rpow_nonneg (by positivity) _)
        (hgeo n) hβ'.le
    exact mul_le_mul hA hB (Real.rpow_nonneg (sum_nonneg fun k _ =>
      Real.rpow_nonneg (by positivity) _) _) (Real.exp_pos _).le
  exact ⟨summable_of_sum_range_le hnn hpart, Real.tsum_le_of_sum_range_le hnn hpart⟩

/-- **The displayed elementary series bound of the proof of
`P:static-phase-all-orders`** (main TeX lines 2670-2679):
`∑_{n ≥ 0} x^n/(n!)^β ≤ 2 e^{3 x^{1/β}}`, with summability, for every
`1/2 ≤ β ≤ 3` and `x ≥ 0` (the TeX applies it at `β = (3-α)/2 ∈ (1/2,3/2)`).
For `β ≥ 1` it follows from `seriesNu_summable_le`, for `β < 1` from the
Hölder variant `seriesNu_holder_le`, as in the TeX. -/
theorem seriesNu_le_two_exp_three {β x : ℝ} (hβ1 : 1 / 2 ≤ β) (hβ3 : β ≤ 3)
    (hx : 0 ≤ x) :
    Summable (fun k : ℕ => x ^ k / (k ! : ℝ) ^ β) ∧
      ∑' k : ℕ, x ^ k / (k ! : ℝ) ^ β ≤ 2 * Real.exp (3 * x ^ (1 / β)) := by
  have hy : 0 ≤ x ^ (1 / β) := Real.rpow_nonneg hx _
  rcases lt_or_ge β 1 with hlt | hge
  · obtain ⟨hs, hb⟩ := seriesNu_holder_le hβ1 hlt hx
    refine ⟨hs, hb.trans ?_⟩
    have h2 : (2 : ℝ) ^ (1 - β) ≤ 2 := by
      calc (2 : ℝ) ^ (1 - β) ≤ (2 : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
        _ = 2 := Real.rpow_one 2
    have h3 : Real.exp (2 * β * x ^ (1 / β)) ≤ Real.exp (3 * x ^ (1 / β)) := by
      gcongr; linarith
    gcongr
  · obtain ⟨hs, hb⟩ := seriesNu_summable_le hge hx
    refine ⟨hs, hb.trans ?_⟩
    have h3 : Real.exp (β * x ^ (1 / β)) ≤ Real.exp (3 * x ^ (1 / β)) := by
      gcongr
    linarith [Real.exp_pos (3 * x ^ (1 / β))]

/-! ### Factorial inequalities -/

/-- **`r! s! ≥ (k!)^2` when `r + s = 2k`** (main TeX lines 2754 and 5119,
"the elementary factorial inequality"). Proof route (auxiliary, the TeX gives
none): `r! s! · C(2k,r) = (2k)! = (k!)^2 · C(2k,k)` and the central binomial
coefficient is the largest. -/
theorem factorial_sq_le_mul_factorial {r s k : ℕ} (h : r + s = 2 * k) :
    (k !) ^ 2 ≤ r ! * s ! := by
  have hr : r ≤ 2 * k := by omega
  have h1 := Nat.choose_mul_factorial_mul_factorial hr
  have h2 := Nat.choose_mul_factorial_mul_factorial (show k ≤ 2 * k by omega)
  have h3 := Nat.choose_le_middle r (2 * k)
  rw [show 2 * k / 2 = k by omega] at h3
  rw [show 2 * k - r = s by omega] at h1
  rw [show 2 * k - k = k by omega] at h2
  have hpos : 0 < (2 * k).choose k := Nat.choose_pos (by omega)
  refine Nat.le_of_mul_le_mul_left ?_ hpos
  calc (2 * k).choose k * k ! ^ 2 = (2 * k).choose k * k ! * k ! := by ring
    _ = (2 * k).choose r * r ! * s ! := by rw [h1, h2]
    _ ≤ (2 * k).choose k * r ! * s ! := by gcongr
    _ = (2 * k).choose k * (r ! * s !) := by ring

/-- Lower factorial bound `k^k e^{1-k} ≤ k!` for `k ≥ 1` (the exponential
form of the left inequality at main TeX line 7246). Proof route (auxiliary,
differs from the TeX's integral comparison): induction using
`(1 + 1/k)^k ≤ e`. -/
theorem factorial_ge_exp (k : ℕ) (hk : 1 ≤ k) :
    (k : ℝ) ^ k * Real.exp (1 - k) ≤ (k ! : ℝ) := by
  induction k, hk using Nat.le_induction with
  | base => simp
  | succ k hk ih =>
    have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
    have hkey : ((k : ℝ) + 1) ^ k ≤ (k : ℝ) ^ k * Real.exp 1 := by
      have h1 : (k : ℝ) + 1 ≤ k * Real.exp (1 / k) := by
        have := Real.add_one_le_exp (1 / (k : ℝ))
        calc (k : ℝ) + 1 = k * (1 / k + 1) := by field_simp; ring
          _ ≤ k * Real.exp (1 / k) := by gcongr
      calc ((k : ℝ) + 1) ^ k ≤ (k * Real.exp (1 / k)) ^ k := by gcongr
        _ = (k : ℝ) ^ k * Real.exp 1 := by
          rw [mul_pow, ← Real.exp_nat_mul, mul_one_div_cancel hk0.ne']
    rw [Nat.factorial_succ]
    push_cast
    have he : Real.exp (1 - ((k : ℝ) + 1)) * Real.exp 1 = Real.exp (1 - k) := by
      rw [← Real.exp_add]; ring_nf
    calc ((k : ℝ) + 1) ^ (k + 1) * Real.exp (1 - ((k : ℝ) + 1))
        = ((k : ℝ) + 1) * (((k : ℝ) + 1) ^ k * Real.exp (1 - ((k : ℝ) + 1))) := by ring
      _ ≤ ((k : ℝ) + 1) * ((k : ℝ) ^ k * Real.exp 1 * Real.exp (1 - ((k : ℝ) + 1))) := by
          gcongr
      _ = ((k : ℝ) + 1) * ((k : ℝ) ^ k * Real.exp (1 - k)) := by rw [← he]; ring
      _ ≤ ((k : ℝ) + 1) * (k ! : ℝ) := by gcongr

/-- Upper factorial bound `k! ≤ k^{k+1} e^{1-k}` for `k ≥ 1` (the exponential
form of the right inequality at main TeX line 7247). Proof route (auxiliary,
differs from the TeX's integral comparison): induction using
`k e^{1/(k+1)} ≤ k + 1`. -/
theorem factorial_le_exp (k : ℕ) (hk : 1 ≤ k) :
    (k ! : ℝ) ≤ (k : ℝ) ^ (k + 1) * Real.exp (1 - k) := by
  induction k, hk using Nat.le_induction with
  | base => simp
  | succ k hk ih =>
    have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
    have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by linarith
    have hkey : (k : ℝ) ^ (k + 1) * Real.exp 1 ≤ ((k : ℝ) + 1) ^ (k + 1) := by
      have h1 : (k : ℝ) * Real.exp (1 / ((k : ℝ) + 1)) ≤ (k : ℝ) + 1 := by
        have := Real.add_one_le_exp (-(1 / ((k : ℝ) + 1)))
        have h2 : (k : ℝ) ≤ ((k : ℝ) + 1) * Real.exp (-(1 / ((k : ℝ) + 1))) := by
          calc (k : ℝ) = ((k : ℝ) + 1) * (-(1 / ((k : ℝ) + 1)) + 1) := by field_simp; ring
            _ ≤ _ := by gcongr
        calc (k : ℝ) * Real.exp (1 / ((k : ℝ) + 1))
            ≤ ((k : ℝ) + 1) * Real.exp (-(1 / ((k : ℝ) + 1))) *
                Real.exp (1 / ((k : ℝ) + 1)) := by gcongr
          _ = (k : ℝ) + 1 := by
              rw [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]
      calc (k : ℝ) ^ (k + 1) * Real.exp 1
          = ((k : ℝ) * Real.exp (1 / ((k : ℝ) + 1))) ^ (k + 1) := by
            rw [mul_pow, ← Real.exp_nat_mul]; push_cast
            rw [mul_one_div_cancel hk1.ne']
        _ ≤ ((k : ℝ) + 1) ^ (k + 1) := by gcongr
    rw [Nat.factorial_succ]
    push_cast
    have he : Real.exp (1 - (k : ℝ)) = Real.exp 1 * Real.exp (1 - ((k : ℝ) + 1)) := by
      rw [← Real.exp_add]; ring_nf
    calc ((k : ℝ) + 1) * (k ! : ℝ)
        ≤ ((k : ℝ) + 1) * ((k : ℝ) ^ (k + 1) * Real.exp (1 - k)) := by gcongr
      _ = ((k : ℝ) + 1) * ((k : ℝ) ^ (k + 1) * Real.exp 1) *
            Real.exp (1 - ((k : ℝ) + 1)) := by rw [he]; ring
      _ ≤ ((k : ℝ) + 1) * ((k : ℝ) + 1) ^ (k + 1) * Real.exp (1 - ((k : ℝ) + 1)) := by
          gcongr
      _ = ((k : ℝ) + 1) ^ (k + 1 + 1) * Real.exp (1 - ((k : ℝ) + 1)) := by ring

/-- **The two-sided logarithmic factorial bounds** (main TeX lines 7246-7247,
inside the proof of `L:positive-series-type`): for `k ≥ 1`,
`k log k - k + 1 ≤ log(k!) ≤ k log k - k + 1 + log k`. -/
theorem log_factorial_bounds (k : ℕ) (hk : 1 ≤ k) :
    (k : ℝ) * Real.log k - k + 1 ≤ Real.log (k ! : ℝ) ∧
      Real.log (k ! : ℝ) ≤ (k : ℝ) * Real.log k - k + 1 + Real.log k := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hpos1 : (0 : ℝ) < (k : ℝ) ^ k * Real.exp (1 - k) := by positivity
  have hpos2 : (0 : ℝ) < (k : ℝ) ^ (k + 1) * Real.exp (1 - k) := by positivity
  constructor
  · have := Real.log_le_log hpos1 (factorial_ge_exp k hk)
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_exp] at this
    linarith
  · have := Real.log_le_log (by positivity) (factorial_le_exp k hk)
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_exp] at this
    push_cast at this
    linarith

/-! ### Euler's Gamma function -/

/-- Midpoint log-convexity of Euler's Gamma function:
`Γ((x+y)/2)^2 ≤ Γ(x) Γ(y)` for `x, y > 0` (from `Real.convexOn_log_Gamma`). -/
theorem gamma_mid_sq_le {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    Real.Gamma ((x + y) / 2) ^ 2 ≤ Real.Gamma x * Real.Gamma y := by
  have h := Real.convexOn_log_Gamma.2 (Set.mem_Ioi.2 hx) (Set.mem_Ioi.2 hy)
    (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num)
  simp only [Function.comp, smul_eq_mul] at h
  have hm : (1/2:ℝ) * x + 1/2 * y = (x + y) / 2 := by ring
  rw [hm] at h
  have hg := Real.Gamma_pos_of_pos (by linarith : 0 < (x+y)/2)
  have := Real.exp_le_exp.2 (by linarith : 2 * Real.log (Real.Gamma ((x+y)/2)) ≤
      Real.log (Real.Gamma x) + Real.log (Real.Gamma y))
  rw [Real.exp_add, Real.exp_log (Real.Gamma_pos_of_pos hx),
    Real.exp_log (Real.Gamma_pos_of_pos hy), ← Real.log_rpow hg, Real.exp_log (by positivity)] at this
  simpa using this

end StratonovichHAMSecondMoment.SeriesType
