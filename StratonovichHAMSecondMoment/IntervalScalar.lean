module

/-
Copyright 2026 Le Chen. SPDX-License-Identifier: Apache-2.0

Deterministic scalar steps of `C:static-interaction` (Summable static
interaction bounds) and `P:interval-coefficients` (Uniform interval
coefficients) of `notes/notes_stratonovich_ham_second_moment.tex` (main TeX
file; line numbers at revision a284420).  Both results are operator and
stochastic statements; this module formalizes the scalar, combinatorial and
Hilbert-space deductions inside their proofs.  Every theorem here is a STEP of
those results (class: inputs supplied, conclusion weaker than the labelled
statement): the operator and stochastic inputs enter as named hypotheses whose
doc comments name their labels and lines.

`C:static-interaction` (statement lines 2685-2731, proof 2733-2796):
* `static_interaction_paper` (`E:static-interaction`, line 2707; proof lines
  2733-2770): in a real Hilbert space standing for `L²(Ω; X_λ)`, if
  `Y_0 = (f,g)`, the order bounds of the displayed estimate at lines 2745-2751
  hold, odd pairings vanish (line 2752) and the two first-variance inputs of
  lines 2740-2742 hold, then `∑ σ^n Y_n` converges and
  `‖∑ σ^n Y_n‖² ≤ (1 + 𝓔(h,σ,λ)) N²` with the TeX's `L_α`,
  `B_α = 3e A_α²`, `γ = 3-α`, `x = B_α σ² R_α h^{4-α}` (`staticL`, `staticB`,
  `staticX`, `staticE`, lines 2693-2703).  The derivation of the order bounds
  from `P:static-phase-all-orders`, of the parity from Gaussian symmetry, and
  of the two first-variance inputs from `P:static-phase-variance` is not
  formalized (supplied inputs).  The identity `I = S_0(-h) ∑ σ^n Z_n =
  ∑ σ^n Y_n` is linear algebra that the inputs already encode (`Y_n` are the
  transported phases).
* `static_block_series_paper` (`E:static-block-series`, line 2713; proof lines
  2772-2786): in full (pure scalar statement; nothing supplied).
* `independent_static_blocks_paper` (`E:independent-static-blocks`, line
  2720; proof lines 2787-2794): the scalar iteration and `1 + y ≤ e^y`; the
  per-block bound (from `E:static-interaction`, `‖S_0(h_j)‖² ≤ e^{λh_j}`,
  density and tensoring with the past, lines 2787-2792) is supplied.

`P:interval-coefficients` (statement lines 3402-3414, proof 3416-3581):
* `interval_coefficient_assembly_paper` (`E:interval-coefficient-bound`, line
  3405; proof lines 3417-3420 and 3499-3547): the bound
  `|[s^{2k}] energy| ≤ C^k R_α^k T^{βk}/(k!)^ν ‖v‖²` with the explicit
  `C = 12 max(c,0) max(1,L)^β C_split C_inv`, assembled from the split
  identity (`E:interval-energy-splits` with the reflection parity, lines
  3478-3488), `L:fixed-split` (lines 3053-3094; `E:fixed-split-bound`, lines 3080-3091) and
  `L:inventory-product` (`E:inventory-product`, lines 2986-2997), all three
  supplied.  The local weight substitution (`h_i ≤ LT/i`, `λ = k/T`,
  `σ_i² ≤ c h_i^{-α₀}`, lines 3499-3538), the split counting `2l+1 ≤ 3^l`,
  the coefficient-of-a-product identity (lines 3539-3544) and the reduction
  `L ↦ max(1,L)` (lines 3417-3420) are formalized.  The reduction to
  `σ_i > 0` (lines 3420-3423) changes the Gaussian fields and is not
  formalized; the wrapper assumes `σ_i > 0` and `R_α > 0`, as `L:fixed-split`
  does (narrower: the TeX's zero-noise case and sign reduction are not covered).
* `interval_phase_bound_paper` (`E:interval-phase-bound`, line 3410; proof
  lines 3568-3579): from the coefficient bound, the zero-order bound
  `≤ e‖v‖²`, vanishing odd coefficients and the power-series identity at
  `s = 1` (supplied), the energy is at most
  `e exp{ν C^{1/ν} R_α^{1/ν} T^{β/ν}} ‖v‖²`; summability is proved.

`L:inventory-product` is formalized by wave item L7-a in parallel; here it is
the hypothesis `InventoryProduct α α₀ C`, the TeX statement
`E:inventory-product` for all `M` and `k ≥ 1` with the product over
`i = 1, …, M` written as `∏ j : Fin M` at `i = j + 1`.

Junk values: every real power `x^q` here has `x > 0` or is `(k!)^ν`,
`(i:ℝ)^q` with `i ≥ 1`; `R_α` and `D_Γ` are written with `ENNReal.toReal`
of ball masses, which are finite under the stated local finiteness
(`IsLocallyFiniteMeasure`, Radon in the TeX); summability is proved, never
assumed through `tsum`.
-/
public import Mathlib
public import StratonovichHAMSecondMoment.SeriesType
public import StratonovichHAMSecondMoment.HomogHypothesis

@[expose] public section

noncomputable section

set_option autoImplicit false

open Real Finset Filter Topology MeasureTheory
open scoped Nat

namespace StratonovichHAMSecondMoment.IntervalScalar

open StratonovichHAMSecondMoment.SeriesType

/-! ## `C:static-interaction` (main TeX lines 2685-2796) -/

/-- Step of `C:static-interaction` (main TeX line 2762): `e(2k+1) ≤ (3e)^k` for
`k ≥ 1`. -/
theorem exp_mul_two_k_add_one_le (k : ℕ) (hk : 1 ≤ k) :
    Real.exp 1 * (2 * k + 1) ≤ (3 * Real.exp 1) ^ k := by
  have h3 : ((2 * k + 1 : ℕ) : ℝ) ≤ ((3 ^ k : ℕ) : ℝ) := by
    exact_mod_cast (by
      induction k with
      | zero => omega
      | succ n ih =>
        rcases Nat.eq_zero_or_pos n with h | h
        · subst h; norm_num
        · have := ih h
          rw [pow_succ]; omega)
  have he : Real.exp 1 ≤ Real.exp 1 ^ k :=
    le_self_pow₀ (by linarith [Real.add_one_le_exp (1 : ℝ)]) (by omega)
  push_cast at h3
  rw [mul_pow]
  calc Real.exp 1 * (2 * k + 1) ≤ Real.exp 1 ^ k * 3 ^ k :=
        mul_le_mul he h3 (by positivity) (by positivity)
    _ = 3 ^ k * Real.exp 1 ^ k := mul_comm _ _

/-- Auxiliary (Lean route; partial-sum form of `tail_series_le`): for `γ ≥ 1`,
`x ≥ 0` and every `m`, `∑_{j<m} x^{j+2}/((j+2)!)^γ ≤ x² exp(γ x^{1/γ})`. -/
theorem tail_sum_le {γ x : ℝ} (hγ : 1 ≤ γ) (hx : 0 ≤ x) (m : ℕ) :
    ∑ j ∈ range m, x ^ (j + 2) / ((j + 2)! : ℝ) ^ γ ≤
      x ^ 2 * Real.exp (γ * x ^ (1 / γ)) := by
  obtain ⟨hs, hle⟩ := seriesNu_summable_le hγ hx
  have hterm : ∀ j, x ^ (j + 2) / ((j + 2)! : ℝ) ^ γ ≤ x ^ 2 * (x ^ j / (j ! : ℝ) ^ γ) := by
    intro j
    have h1 : (j ! : ℝ) ^ γ ≤ ((j + 2)! : ℝ) ^ γ := by
      apply Real.rpow_le_rpow (by positivity) _ (by linarith)
      exact_mod_cast Nat.factorial_le (by omega)
    have h0 : 0 < (j ! : ℝ) ^ γ := by positivity
    calc x ^ (j + 2) / ((j + 2)! : ℝ) ^ γ = x ^ 2 * (x ^ j / ((j + 2)! : ℝ) ^ γ) := by ring
      _ ≤ _ := by gcongr
  calc ∑ j ∈ range m, x ^ (j + 2) / ((j + 2)! : ℝ) ^ γ
      ≤ ∑ j ∈ range m, x ^ 2 * (x ^ j / (j ! : ℝ) ^ γ) := sum_le_sum fun j _ => hterm j
    _ = x ^ 2 * ∑ j ∈ range m, x ^ j / (j ! : ℝ) ^ γ := by rw [mul_sum]
    _ ≤ x ^ 2 * Real.exp (γ * x ^ (1 / γ)) := by
        gcongr
        exact (hs.sum_le_tsum _ (fun i _ => by positivity)).trans hle

/-- Step of `C:static-interaction` (main TeX lines 2762-2769): for `γ ≥ 1` and
`x ≥ 0`, the series `∑_{k ≥ 2} x^k/(k!)^γ` (indexed here as `k = j + 2`)
converges and is at most `x² e^{γ x^{1/γ}}`; it uses
`∑_{j ≥ 0} x^j/(j!)^γ ≤ e^{γ x^{1/γ}}` (`SeriesType.seriesNu_summable_le`). -/
theorem tail_series_le {γ x : ℝ} (hγ : 1 ≤ γ) (hx : 0 ≤ x) :
    Summable (fun j : ℕ => x ^ (j + 2) / ((j + 2)! : ℝ) ^ γ) ∧
      ∑' j : ℕ, x ^ (j + 2) / ((j + 2)! : ℝ) ^ γ ≤ x ^ 2 * Real.exp (γ * x ^ (1 / γ)) :=
  ⟨summable_of_sum_range_le (fun _ => by positivity) (tail_sum_le hγ hx),
    Real.tsum_le_of_sum_range_le (fun _ => by positivity) (tail_sum_le hγ hx)⟩

/-- Step of `C:static-interaction` (main TeX lines 2753-2761): if
`‖Y_n‖ ≤ M a^n/(n!)^{γ/2} N` for every `n ≥ 0` (with `M, a, N ≥ 0`,
`γ ≥ 0`), then for `r + s = 2k`,
`‖Y_r‖ ‖Y_s‖ ≤ M² (a²)^k/(k!)^γ N²`, by `r! s! ≥ (k!)²`
(`SeriesType.factorial_sq_le_mul_factorial`). `Y` takes values in any normed
group. -/
theorem pair_norm_le {E : Type*} [NormedAddCommGroup E] (Y : ℕ → E) {M a γ N : ℝ}
    (hM : 0 ≤ M) (ha : 0 ≤ a) (hγ : 0 ≤ γ) (hN : 0 ≤ N)
    (hY : ∀ n, ‖Y n‖ ≤ M * (a ^ n / (n ! : ℝ) ^ (γ / 2)) * N)
    {r s k : ℕ} (hrs : r + s = 2 * k) :
    ‖Y r‖ * ‖Y s‖ ≤ M ^ 2 * ((a ^ 2) ^ k / (k ! : ℝ) ^ γ) * N ^ 2 := by
  have hfac : ((k ! : ℝ)) ^ γ ≤ ((r ! : ℝ)) ^ (γ / 2) * ((s ! : ℝ)) ^ (γ / 2) := by
    rw [← Real.mul_rpow (by positivity) (by positivity)]
    have h1 : ((k ! : ℝ) ^ 2) ≤ (r ! : ℝ) * (s ! : ℝ) := by
      exact_mod_cast factorial_sq_le_mul_factorial hrs
    calc ((k ! : ℝ)) ^ γ = ((k ! : ℝ) ^ 2) ^ (γ / 2) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; congr 1; push_cast; ring
      _ ≤ _ := Real.rpow_le_rpow (by positivity) h1 (by linarith)
  have hk0 : 0 < (k ! : ℝ) ^ γ := by positivity
  calc ‖Y r‖ * ‖Y s‖ ≤ (M * (a ^ r / (r ! : ℝ) ^ (γ / 2)) * N) *
        (M * (a ^ s / (s ! : ℝ) ^ (γ / 2)) * N) :=
        mul_le_mul (hY r) (hY s) (norm_nonneg _) (by positivity)
    _ = M ^ 2 * (a ^ (r + s) / ((r ! : ℝ) ^ (γ / 2) * (s ! : ℝ) ^ (γ / 2))) * N ^ 2 := by
        rw [pow_add]; field_simp
    _ ≤ M ^ 2 * (a ^ (r + s) / (k ! : ℝ) ^ γ) * N ^ 2 := by
        gcongr
    _ = M ^ 2 * ((a ^ 2) ^ k / (k ! : ℝ) ^ γ) * N ^ 2 := by
        rw [hrs, pow_mul]

/-- Auxiliary (Lean route): if `c r s = 0` whenever `r + s` is odd, the square
sum `∑_{r,s<n} c r s` regroups as `∑_{k<n} ∑_{r+s=2k, r,s<n} c r s`. -/
theorem square_sum_eq (n : ℕ) (c : ℕ → ℕ → ℝ) (hodd : ∀ r s, Odd (r + s) → c r s = 0) :
    ∑ r ∈ range n, ∑ s ∈ range n, c r s =
      ∑ k ∈ range n, ∑ p ∈ (antidiagonal (2 * k)).filter (fun p => p.1 < n ∧ p.2 < n),
        c p.1 p.2 := by
  rw [← Finset.sum_product' (range n) (range n) c]
  rw [← Finset.sum_filter_of_ne (p := fun p : ℕ × ℕ => Even (p.1 + p.2))
    (fun p _ hp => by
      by_contra h
      exact hp (hodd _ _ (Nat.not_even_iff_odd.mp h)))]
  rw [← Finset.sum_fiberwise_of_maps_to (t := range n) (g := fun p : ℕ × ℕ => (p.1 + p.2) / 2)
    (fun p hp => by
      simp only [mem_filter, mem_product, mem_range] at hp
      simp only [mem_range]; omega)]
  refine sum_congr rfl fun k _ => ?_
  apply sum_congr _ (fun _ _ => rfl)
  ext p
  simp only [mem_filter, mem_product, mem_range, Finset.HasAntidiagonal.mem_antidiagonal, Nat.even_iff]
  omega

/-- Step of `C:static-interaction` (main TeX lines 2733-2770), general form: in
a complete real inner product space (standing for `L²(Ω; X_λ)`), let
`‖Y_0‖ = N`, `‖Y_n‖ ≤ √e K a^n/(n!)^{γ/2} N` for `n ≥ 1` with `K ≥ 1`,
`⟪Y_r, Y_s⟫ = 0` when `r + s` is odd, and
`|⟪Y_1, Y_1⟫ + 2⟪Y_0, Y_2⟫| ≤ L N²` (the complete `σ²` coefficient; real inner
product, so `⟪Y_2, Y_0⟫ = ⟪Y_0, Y_2⟫`), with `γ ≥ 1`.  Then
`∑ σ^n Y_n` converges and
`‖∑ σ^n Y_n‖² ≤ (1 + σ² L + K² x² e^{γ x^{1/γ}}) N²`, `x = 3e σ² a²`.
Proof route: bound the partial sums (regrouped by `r + s = 2k`, keeping the
first coefficient signed and bounding orders `k ≥ 2` in absolute value by
`pair_norm_le`, `exp_mul_two_k_add_one_le`, `tail_sum_le`) and pass to the
limit; the TeX argues directly with the absolutely convergent double series. -/
theorem static_interaction_assembly {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (Y : ℕ → E) {σ N K a γ Lc : ℝ} (hN : 0 ≤ N) (hK : 1 ≤ K) (ha : 0 ≤ a)
    (hγ : 1 ≤ γ) (hY0 : ‖Y 0‖ = N)
    (hY : ∀ n, 1 ≤ n → ‖Y n‖ ≤ √(Real.exp 1) * K * (a ^ n / (n ! : ℝ) ^ (γ / 2)) * N)
    (hodd : ∀ r s, Odd (r + s) → inner ℝ (Y r) (Y s) = 0)
    (hfirst : |inner ℝ (Y 1) (Y 1) + 2 * inner ℝ (Y 0) (Y 2)| ≤ Lc * N ^ 2) :
    Summable (fun n => σ ^ n • Y n) ∧
      ‖∑' n, σ ^ n • Y n‖ ^ 2 ≤
        (1 + σ ^ 2 * Lc + K ^ 2 * ((3 * Real.exp 1 * σ ^ 2 * a ^ 2) ^ 2 *
          Real.exp (γ * (3 * Real.exp 1 * σ ^ 2 * a ^ 2) ^ (1 / γ)))) * N ^ 2 := by
  set M := √(Real.exp 1) * K with hMdef
  have he1 : 1 ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hsqe : 1 ≤ √(Real.exp 1) := by rw [Real.one_le_sqrt]; exact he1
  have hM1 : 1 ≤ M := by nlinarith
  have hM0 : 0 ≤ M := by linarith
  have hYall : ∀ n, ‖Y n‖ ≤ M * (a ^ n / (n ! : ℝ) ^ (γ / 2)) * N := by
    intro n
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; simp [hY0]; nlinarith
    · exact hY n h
  -- summability
  set x := 3 * Real.exp 1 * σ ^ 2 * a ^ 2 with hxdef
  have hx0 : 0 ≤ x := by positivity
  have hsum : Summable (fun n => σ ^ n • Y n) := by
    obtain ⟨hs, -⟩ := seriesNu_le_two_exp_three (β := 1 / 2) (x := |σ| * a) (by norm_num)
      (by norm_num) (by positivity)
    refine Summable.of_norm_bounded ((hs.mul_left (M * N))) (fun n => ?_)
    rw [norm_smul, norm_pow, Real.norm_eq_abs]
    have hn1 : (1 : ℝ) ≤ (n ! : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero n)
    have hf : ((n ! : ℝ)) ^ ((1 : ℝ) / 2) ≤ ((n ! : ℝ)) ^ (γ / 2) :=
      Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
    have hf0 : 0 < ((n ! : ℝ)) ^ ((1 : ℝ) / 2) := by positivity
    calc |σ| ^ n * ‖Y n‖ ≤ |σ| ^ n * (M * (a ^ n / (n ! : ℝ) ^ (γ / 2)) * N) :=
          mul_le_mul_of_nonneg_left (hYall n) (by positivity)
      _ = M * N * ((|σ| * a) ^ n / (n ! : ℝ) ^ (γ / 2)) := by ring
      _ ≤ M * N * ((|σ| * a) ^ n / (n ! : ℝ) ^ ((1 : ℝ) / 2)) := by gcongr
  refine ⟨hsum, ?_⟩
  -- partial sums
  set c : ℕ → ℕ → ℝ := fun r s => σ ^ (r + s) * inner ℝ (Y r) (Y s) with hcdef
  have hcodd : ∀ r s, Odd (r + s) → c r s = 0 := fun r s h => by simp [hcdef, hodd r s h]
  have hnormS : ∀ n, ‖∑ r ∈ range n, σ ^ r • Y r‖ ^ 2 =
      ∑ r ∈ range n, ∑ s ∈ range n, c r s := by
    intro n
    rw [← real_inner_self_eq_norm_sq, sum_inner]
    refine sum_congr rfl fun r _ => ?_
    rw [inner_sum]
    refine sum_congr rfl fun s _ => ?_
    rw [real_inner_smul_left, real_inner_smul_right, hcdef]
    simp only; rw [pow_add]; ring
  -- bound on each shell k ≥ 1
  have hshell : ∀ k, 1 ≤ k → ∀ n, ∑ p ∈ (antidiagonal (2 * k)).filter
      (fun p => p.1 < n ∧ p.2 < n), c p.1 p.2 ≤ K ^ 2 * (x ^ k / (k ! : ℝ) ^ γ) * N ^ 2 := by
    intro k hk n
    have hpair : ∀ p ∈ antidiagonal (2 * k), |c p.1 p.2| ≤
        (σ ^ 2) ^ k * (M ^ 2 * ((a ^ 2) ^ k / (k ! : ℝ) ^ γ) * N ^ 2) := by
      intro p hp
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
      simp only [hcdef, abs_mul, abs_pow, hp]
      rw [pow_mul, sq_abs]
      exact mul_le_mul_of_nonneg_left ((abs_real_inner_le_norm _ _).trans
        (pair_norm_le Y hM0 ha (by linarith) hN hYall hp)) (by positivity)
    have hcard : ((antidiagonal (2 * k)).card : ℝ) = 2 * k + 1 := by
      rw [Finset.Nat.card_antidiagonal]; push_cast; ring
    have hk3 := exp_mul_two_k_add_one_le k hk
    calc ∑ p ∈ (antidiagonal (2 * k)).filter (fun p => p.1 < n ∧ p.2 < n), c p.1 p.2
        ≤ ∑ p ∈ (antidiagonal (2 * k)).filter (fun p => p.1 < n ∧ p.2 < n), |c p.1 p.2| :=
          sum_le_sum fun p _ => le_abs_self _
      _ ≤ ∑ p ∈ antidiagonal (2 * k), |c p.1 p.2| :=
          sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => abs_nonneg _)
      _ ≤ ∑ p ∈ antidiagonal (2 * k),
            (σ ^ 2) ^ k * (M ^ 2 * ((a ^ 2) ^ k / (k ! : ℝ) ^ γ) * N ^ 2) := sum_le_sum hpair
      _ = (Real.exp 1 * (2 * k + 1)) * K ^ 2 * ((σ ^ 2) ^ k * (a ^ 2) ^ k / (k ! : ℝ) ^ γ)
            * N ^ 2 := by
          rw [sum_const, nsmul_eq_mul, hcard, hMdef, mul_pow,
            Real.sq_sqrt (by positivity)]; ring
      _ ≤ (3 * Real.exp 1) ^ k * K ^ 2 * ((σ ^ 2) ^ k * (a ^ 2) ^ k / (k ! : ℝ) ^ γ)
            * N ^ 2 := by gcongr
      _ = K ^ 2 * (x ^ k / (k ! : ℝ) ^ γ) * N ^ 2 := by
          rw [hxdef]; ring
  have hpartial : ∀ n, 3 ≤ n → ‖∑ r ∈ range n, σ ^ r • Y r‖ ^ 2 ≤
      (1 + σ ^ 2 * Lc + K ^ 2 * (x ^ 2 * Real.exp (γ * x ^ (1 / γ)))) * N ^ 2 := by
    intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
    rw [hnormS, square_sum_eq _ c hcodd, sum_range_succ', sum_range_succ']
    have h0 : (antidiagonal (2 * 0)).filter (fun p : ℕ × ℕ => p.1 < m + 2 ∧ p.2 < m + 2) =
        {(0, 0)} := by
      ext p; simp only [mem_filter, Finset.HasAntidiagonal.mem_antidiagonal, mem_singleton, Prod.ext_iff]; omega
    have h1 : (antidiagonal (2 * (0 + 1))).filter
        (fun p : ℕ × ℕ => p.1 < m + 2 ∧ p.2 < m + 2) = {(0, 2), (1, 1), (2, 0)} := by
      ext p
      simp only [mem_filter, Finset.HasAntidiagonal.mem_antidiagonal, mem_insert, mem_singleton, Prod.ext_iff]
      omega
    rw [h0, h1, sum_singleton]
    rw [sum_insert (by decide), sum_insert (by decide), sum_singleton]
    have hc00 : c 0 0 = N ^ 2 := by
      simp [hcdef, hY0]
    have hc1 : c (0, 2).1 (0, 2).2 + (c (1, 1).1 (1, 1).2 + c (2, 0).1 (2, 0).2) ≤
        σ ^ 2 * Lc * N ^ 2 := by
      simp only [hcdef]
      have hcomm : inner ℝ (Y 2) (Y 0) = inner ℝ (Y 0) (Y 2) := real_inner_comm _ _
      have := le_abs_self (inner ℝ (Y 1) (Y 1) + 2 * inner ℝ (Y 0) (Y 2))
      have hs2 : 0 ≤ σ ^ 2 := sq_nonneg σ
      have hb := mul_le_mul_of_nonneg_left (this.trans hfirst) hs2
      rw [hcomm]
      norm_num
      rw [real_inner_self_eq_norm_sq] at hb
      nlinarith [hb]
    have htail : ∑ j ∈ range m, ∑ p ∈ (antidiagonal (2 * (j + 1 + 1))).filter
        (fun p : ℕ × ℕ => p.1 < m + 2 ∧ p.2 < m + 2), c p.1 p.2 ≤
        K ^ 2 * (x ^ 2 * Real.exp (γ * x ^ (1 / γ))) * N ^ 2 := by
      calc _ ≤ ∑ j ∈ range m, K ^ 2 * (x ^ (j + 2) / ((j + 2)! : ℝ) ^ γ) * N ^ 2 :=
            sum_le_sum fun j _ => hshell (j + 1 + 1) (by omega) _
        _ = K ^ 2 * (∑ j ∈ range m, x ^ (j + 2) / ((j + 2)! : ℝ) ^ γ) * N ^ 2 := by
            rw [mul_sum, sum_mul]
        _ ≤ _ := by gcongr; exact tail_sum_le hγ hx0 m
    nlinarith [htail, hc1, hc00]
  have hlim := (hsum.hasSum.tendsto_sum_nat.norm).pow 2
  exact le_of_tendsto hlim (eventually_atTop.2 ⟨3, hpartial⟩)

/-- `L_α(h, λ) = 4e R_α h² λ^{α-2} + 4√e D_Γ/((2-α)(3-α)) · h^{3-α}/λ`
(`C:static-interaction`, main TeX lines 2696-2699). -/
def staticL (alpha R D h lam : ℝ) : ℝ :=
  4 * Real.exp 1 * R * h ^ 2 * lam ^ (alpha - 2) +
    4 * √(Real.exp 1) * D / ((2 - alpha) * (3 - alpha)) * (h ^ (3 - alpha) / lam)

/-- `B_α = 3e A_α²` (`C:static-interaction`, main TeX line 2693). -/
def staticB (A : ℝ) : ℝ := 3 * Real.exp 1 * A ^ 2

/-- `x = B_α σ² R_α h^{4-α}` (`C:static-interaction`, main TeX line 2700). -/
def staticX (alpha A R h σ : ℝ) : ℝ := staticB A * σ ^ 2 * R * h ^ (4 - alpha)

/-- `𝓔(h, σ, λ) = σ² L_α(h, λ) + (λh)^{-2} x² e^{γ x^{1/γ}}` with
`γ = 3 - α` (`C:static-interaction`, main TeX lines 2693, 2701-2703). -/
def staticE (alpha A R D h σ lam : ℝ) : ℝ :=
  σ ^ 2 * staticL alpha R D h lam +
    (lam * h)⁻¹ ^ 2 * (staticX alpha A R h σ ^ 2 *
      Real.exp ((3 - alpha) * staticX alpha A R h σ ^ (1 / (3 - alpha))))

/-- Step of `C:static-interaction` (main TeX lines 2737-2742): for `α < 2`,
`R, D ≥ 0`, `λ, h > 0`, `λh ≤ 1`, if `0 ≤ b ≤ e · (E:phase-born)` and
`|m| ≤ N · √e · (E:phase-mean)` (the right sides of `P:static-phase-variance`,
lines 2168-2174), then `|b + 2m| ≤ L_α(h, λ) N²`.  Here `b` stands for the first
random squared norm `‖Y_1‖²` and `m` for the mean cross term `⟪Y_0, Y_2⟫`;
`λh ≤ 1` gives `(1+λ²h²) ≤ 2`. -/
theorem first_coefficient_le {alpha R D h lam N b m : ℝ} (hα2 : alpha < 2)
    (hR : 0 ≤ R) (hD : 0 ≤ D) (hlam : 0 < lam) (hh : 0 < h) (hlh : lam * h ≤ 1)
    (hb0 : 0 ≤ b)
    (hborn : b ≤ Real.exp 1 * (R * h ^ 2 * lam ^ (alpha - 2) * (1 + lam ^ 2 * h ^ 2) ^ 2 * N ^ 2))
    (hmean : |m| ≤ N * (√(Real.exp 1) * (D * (1 + lam ^ 2 * h ^ 2) * h ^ (3 - alpha) /
      (lam * (2 - alpha) * (3 - alpha)) * N))) :
    |b + 2 * m| ≤ staticL alpha R D h lam * N ^ 2 := by
  have hq : lam ^ 2 * h ^ 2 ≤ 1 := by
    have : lam ^ 2 * h ^ 2 = (lam * h) ^ 2 := by ring
    rw [this]; nlinarith [mul_pos hlam hh]
  have hq0 : 0 ≤ lam ^ 2 * h ^ 2 := by positivity
  have hP1 : 0 ≤ R * h ^ 2 * lam ^ (alpha - 2) * N ^ 2 := by positivity
  have hP2 : 0 ≤ D * h ^ (3 - alpha) / (lam * (2 - alpha) * (3 - alpha)) * N ^ 2 := by
    have : 0 < (2 - alpha) := by linarith
    have : 0 < (3 - alpha) := by linarith
    positivity
  have hb' : b ≤ 4 * Real.exp 1 * (R * h ^ 2 * lam ^ (alpha - 2) * N ^ 2) := by
    have h4 : (1 + lam ^ 2 * h ^ 2) ^ 2 ≤ 4 := by nlinarith
    calc b ≤ _ := hborn
      _ = Real.exp 1 * ((1 + lam ^ 2 * h ^ 2) ^ 2 * (R * h ^ 2 * lam ^ (alpha - 2) * N ^ 2)) := by
          ring
      _ ≤ Real.exp 1 * (4 * (R * h ^ 2 * lam ^ (alpha - 2) * N ^ 2)) := by
          gcongr
      _ = _ := by ring
  have hm' : |m| ≤ 2 * √(Real.exp 1) *
      (D * h ^ (3 - alpha) / (lam * (2 - alpha) * (3 - alpha)) * N ^ 2) := by
    calc |m| ≤ _ := hmean
      _ = √(Real.exp 1) * ((1 + lam ^ 2 * h ^ 2) *
            (D * h ^ (3 - alpha) / (lam * (2 - alpha) * (3 - alpha)) * N ^ 2)) := by ring
      _ ≤ √(Real.exp 1) * (2 * (D * h ^ (3 - alpha) / (lam * (2 - alpha) * (3 - alpha)) * N ^ 2)) := by
          gcongr; linarith
      _ = _ := by ring
  have hL : staticL alpha R D h lam * N ^ 2 = 4 * Real.exp 1 * (R * h ^ 2 * lam ^ (alpha - 2) * N ^ 2)
      + 2 * (2 * √(Real.exp 1) * (D * h ^ (3 - alpha) / (lam * (2 - alpha) * (3 - alpha)) * N ^ 2)) := by
    unfold staticL
    have : (2 - alpha) ≠ 0 := by linarith
    have : (3 - alpha) ≠ 0 := by linarith
    field_simp
    ring
  rw [hL]
  calc |b + 2 * m| ≤ |b| + |2 * m| := abs_add_le _ _
    _ = b + 2 * |m| := by rw [abs_of_nonneg hb0, abs_mul]; norm_num
    _ ≤ _ := by linarith

/-- Auxiliary (Lean route; the TeX uses `y = 𝓔 ≥ 0` at line 2794): for
`α < 2`, `R, D ≥ 0` and `λ, h > 0`, `𝓔(h, σ, λ) ≥ 0`. -/
theorem staticE_nonneg {alpha A R D h σ lam : ℝ} (hα2 : alpha < 2) (hR : 0 ≤ R) (hD : 0 ≤ D)
    (hlam : 0 < lam) (hh : 0 < h) : 0 ≤ staticE alpha A R D h σ lam := by
  have h2 : 0 < 2 - alpha := by linarith
  have h3 : 0 < 3 - alpha := by linarith
  have hL : 0 ≤ staticL alpha R D h lam := by unfold staticL; positivity
  unfold staticE
  positivity

/-- **Step row of `C:static-interaction`, `E:static-interaction`** (main TeX
lines 2707-2709, proof 2733-2770), with `R_α ≥ 0` and `D_Γ ≥ 0` as hypotheses
(`static_interaction_paper` derives them from the TeX's formulas).  In a
complete real inner product space standing for `L²(Ω; X_λ)` with
`Y_n = S_0(-h) Z_n^ε(h)`, `N = ‖(f,g)‖_λ` and `λh ≤ 1`, the supplied inputs are:
* `hY0`: `Y_0 = (f,g)`, so `‖Y_0‖ = N` (line 2737);
* `hY`: the displayed order bound at lines 2746-2751, which the TeX derives
  from `P:static-phase-all-orders` (`E:all-static-phase-orders`, lines
  2589-2594), `‖S_0(-h)‖_λ ≤ √e` and the norm comparisons for `λh ≤ 1`;
* `hodd`: Gaussian symmetry, `E⟨Y_r, Y_s⟩_λ = 0` for odd `r + s` (line 2752);
* `hborn`: `E‖Y_1‖² ≤ e · (E:phase-born)` (lines 2740-2741, from
  `P:static-phase-variance`);
* `hmean`: `|E⟨Y_0, Y_2⟩| ≤ N · √e · (E:phase-mean)` (lines 2741-2742: `Y_0`
  is deterministic, so this is Cauchy-Schwarz against `S_0(-h) E Z_2`).
Conclusion: `∑ σ^n Y_n` converges and its squared norm is at most
`(1 + 𝓔(h,σ,λ)) N²`.  `A` is any constant `≥ 0` (the TeX's
`A_α = 400√2 e²/δ_{α/2}`); the uniformity in `ε` is that of the inputs.
Weaker than the TeX statement: the identification of `I_σ^ε(h)(f,g)` with
`∑ σ^n Y_n` and every input above are not proved here.  `_hα0` (`0 < α`, the
section's standing assumption) is carried but not used. -/
theorem static_interaction_step {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (Y : ℕ → E) {alpha A R D h lam σ N : ℝ}
    (_hα0 : 0 < alpha) (hα2 : alpha < 2) (hA : 0 ≤ A) (hR : 0 ≤ R) (hD : 0 ≤ D)
    (hlam : 0 < lam) (hh : 0 < h) (hlh : lam * h ≤ 1) (hN : 0 ≤ N)
    (hY0 : ‖Y 0‖ = N)
    (hY : ∀ n, 1 ≤ n → ‖Y n‖ ≤ √(Real.exp 1) / (lam * h) *
      ((A * √R) ^ n * h ^ ((4 - alpha) * n / 2) / (n ! : ℝ) ^ ((3 - alpha) / 2)) * N)
    (hodd : ∀ r s, Odd (r + s) → inner ℝ (Y r) (Y s) = 0)
    (hborn : ‖Y 1‖ ^ 2 ≤
      Real.exp 1 * (R * h ^ 2 * lam ^ (alpha - 2) * (1 + lam ^ 2 * h ^ 2) ^ 2 * N ^ 2))
    (hmean : |inner ℝ (Y 0) (Y 2)| ≤ N * (√(Real.exp 1) * (D * (1 + lam ^ 2 * h ^ 2) *
      h ^ (3 - alpha) / (lam * (2 - alpha) * (3 - alpha)) * N))) :
    Summable (fun n => σ ^ n • Y n) ∧
      ‖∑' n, σ ^ n • Y n‖ ^ 2 ≤ (1 + staticE alpha A R D h σ lam) * N ^ 2 := by
  have hlh0 : 0 < lam * h := mul_pos hlam hh
  set a := A * √R * h ^ ((4 - alpha) / 2) with hadef
  have ha : 0 ≤ a := by positivity
  have hK : 1 ≤ (lam * h)⁻¹ := by rw [le_inv_comm₀ (by norm_num) hlh0]; simpa using hlh
  have han : ∀ n : ℕ, a ^ n = (A * √R) ^ n * h ^ ((4 - alpha) * n / 2) := by
    intro n
    rw [hadef, mul_pow, ← Real.rpow_mul_natCast hh.le]
    congr 2; ring
  have ha2 : a ^ 2 = A ^ 2 * R * h ^ (4 - alpha) := by
    rw [han 2, mul_pow, Real.sq_sqrt hR]; norm_num
  have hfirst : |inner ℝ (Y 1) (Y 1) + 2 * inner ℝ (Y 0) (Y 2)| ≤ staticL alpha R D h lam * N ^ 2 := by
    rw [real_inner_self_eq_norm_sq]
    exact first_coefficient_le hα2 hR hD hlam hh hlh (sq_nonneg _) hborn hmean
  have hY' : ∀ n, 1 ≤ n → ‖Y n‖ ≤ √(Real.exp 1) * (lam * h)⁻¹ *
      (a ^ n / (n ! : ℝ) ^ ((3 - alpha) / 2)) * N := by
    intro n hn
    rw [han n]
    calc ‖Y n‖ ≤ _ := hY n hn
      _ = _ := by rw [div_eq_mul_inv]
  obtain ⟨hs, hb⟩ := static_interaction_assembly Y (σ := σ) hN hK ha (by linarith) hY0 hY' hodd hfirst
  refine ⟨hs, hb.trans (le_of_eq ?_)⟩
  have hx : 3 * Real.exp 1 * σ ^ 2 * a ^ 2 = staticX alpha A R h σ := by
    rw [ha2]; unfold staticX staticB; ring
  rw [hx]
  unfold staticE
  ring

/-- Auxiliary (Lean route): for `λ > 0` and `q > 0`, `j ↦ (2^{-j}/λ)^q` is
summable (a geometric series). -/
theorem summable_dyadic_rpow {lam q : ℝ} (hlam : 0 < lam) (hq : 0 < q) :
    Summable (fun j : ℕ => ((2 : ℝ)⁻¹ ^ j / lam) ^ q) := by
  have heq : ∀ j : ℕ, ((2 : ℝ)⁻¹ ^ j / lam) ^ q = (lam ^ q)⁻¹ * ((2 : ℝ)⁻¹ ^ q) ^ j := by
    intro j
    rw [Real.div_rpow (by positivity) hlam.le, ← Real.rpow_natCast, ← Real.rpow_natCast,
      ← Real.rpow_mul (by norm_num), ← Real.rpow_mul (by norm_num), mul_comm (j : ℝ) q]
    ring
  simp_rw [heq]
  refine Summable.mul_left _ (summable_geometric_of_lt_one (by positivity) ?_)
  exact Real.rpow_lt_one (by norm_num) (by norm_num) hq

/-- Step of `C:static-interaction` (main TeX lines 2772-2786): at `h = q` with
`0 < q ≤ 1/λ` and `σ² = q^{-α₀}`, the block term `(T/q) 𝓔(q, σ, λ)` is at most
`C₁ q^{1-α₀} + C₂ q^{2-α-α₀} + C₃ q^{2β-3}`, `β = 4-α-α₀`, with the TeX's
three constants; the exponential factor is bounded by its value at
`q = 1/λ` (`h_0`). Requires `α < 2`, `R ≥ 0`, `β > 0`; `D` and `A` are
arbitrary here. -/
theorem block_term_le {alpha alpha0 A R D lam T q s : ℝ} (hα2 : alpha < 2)
    (hR : 0 ≤ R) (hlam : 0 < lam) (hT : 0 < T) (hq : 0 < q) (hql : q ≤ lam⁻¹)
    (hβ : 0 < 4 - alpha - alpha0) (hs : s ^ 2 = q ^ (-alpha0)) :
    T / q * staticE alpha A R D q s lam ≤
      T * (4 * Real.exp 1 * R * lam ^ (alpha - 2)) * q ^ (1 - alpha0) +
      T * (4 * √(Real.exp 1) * D / ((2 - alpha) * (3 - alpha)) / lam) * q ^ (2 - alpha - alpha0) +
      T * (lam ^ 2)⁻¹ * (staticB A * R) ^ 2 *
        Real.exp ((3 - alpha) * (staticB A * R * lam⁻¹ ^ (4 - alpha - alpha0)) ^ (1 / (3 - alpha))) *
        q ^ (2 * (4 - alpha - alpha0) - 3) := by
  have hγ0 : 0 < 3 - alpha := by linarith
  have hBR0 : 0 ≤ staticB A * R := by unfold staticB; positivity
  have hX : staticX alpha A R q s = staticB A * R * q ^ (4 - alpha - alpha0) := by
    unfold staticX
    rw [hs, show 4 - alpha - alpha0 = -alpha0 + (4 - alpha) by ring, Real.rpow_add hq]
    ring
  have f1 : q ^ (-alpha0) * q ^ 2 / q = q ^ (1 - alpha0) := by
    rw [show (1 - alpha0) = (-alpha0 + 2) - 1 by ring, Real.rpow_sub hq (-alpha0 + 2) 1,
      Real.rpow_add hq (-alpha0) 2, Real.rpow_one, Real.rpow_two]
  have f2 : q ^ (-alpha0) * q ^ (3 - alpha) / q = q ^ (2 - alpha - alpha0) := by
    rw [show (2 - alpha - alpha0) = (-alpha0 + (3 - alpha)) - 1 by ring,
      Real.rpow_sub hq (-alpha0 + (3 - alpha)) 1, Real.rpow_add hq (-alpha0) (3 - alpha), Real.rpow_one]
  have f3 : q ^ (2 * (4 - alpha - alpha0) - 3) =
      q ^ (4 - alpha - alpha0) * q ^ (4 - alpha - alpha0) / q ^ 3 := by
    rw [show 2 * (4 - alpha - alpha0) - 3 = ((4 - alpha - alpha0) + (4 - alpha - alpha0)) - 3 by ring,
      Real.rpow_sub hq ((4 - alpha - alpha0) + (4 - alpha - alpha0)) 3,
      Real.rpow_add hq (4 - alpha - alpha0) (4 - alpha - alpha0)]
    congr 1
    exact_mod_cast Real.rpow_natCast q 3
  have hfirst : T / q * (s ^ 2 * staticL alpha R D q lam) =
      T * (4 * Real.exp 1 * R * lam ^ (alpha - 2)) * q ^ (1 - alpha0) +
      T * (4 * √(Real.exp 1) * D / ((2 - alpha) * (3 - alpha)) / lam) * q ^ (2 - alpha - alpha0) := by
    unfold staticL
    rw [hs, ← f1, ← f2]
    ring
  have hexp : Real.exp ((3 - alpha) * staticX alpha A R q s ^ (1 / (3 - alpha))) ≤
      Real.exp ((3 - alpha) * (staticB A * R * lam⁻¹ ^ (4 - alpha - alpha0)) ^ (1 / (3 - alpha))) := by
    have hX0 : 0 ≤ staticX alpha A R q s := by rw [hX]; positivity
    gcongr
    rw [hX]; gcongr
  have hsecond : T / q * ((lam * q)⁻¹ ^ 2 * (staticX alpha A R q s ^ 2 *
      Real.exp ((3 - alpha) * staticX alpha A R q s ^ (1 / (3 - alpha))))) ≤
      T * (lam ^ 2)⁻¹ * (staticB A * R) ^ 2 *
        Real.exp ((3 - alpha) * (staticB A * R * lam⁻¹ ^ (4 - alpha - alpha0)) ^ (1 / (3 - alpha))) *
        q ^ (2 * (4 - alpha - alpha0) - 3) := by
    have e3 : T / q * ((lam * q)⁻¹ ^ 2 * staticX alpha A R q s ^ 2) =
        T * (lam ^ 2)⁻¹ * (staticB A * R) ^ 2 * q ^ (2 * (4 - alpha - alpha0) - 3) := by
      rw [hX, f3]
      field_simp
    have hP : 0 ≤ T * (lam ^ 2)⁻¹ * (staticB A * R) ^ 2 * q ^ (2 * (4 - alpha - alpha0) - 3) := by
      positivity
    calc _ = (T / q * ((lam * q)⁻¹ ^ 2 * staticX alpha A R q s ^ 2)) *
          Real.exp ((3 - alpha) * staticX alpha A R q s ^ (1 / (3 - alpha))) := by ring
      _ ≤ _ := by rw [e3]; nlinarith [mul_le_mul_of_nonneg_left hexp hP]
  unfold staticE
  rw [mul_add, hfirst]
  linarith [hsecond]

/-- **`E:static-block-series`** (main TeX lines 2713-2716, proof 2772-2786), in
full, with `R_α ≥ 0` and `D_Γ ≥ 0` as hypotheses (`static_block_series_paper`
derives them): for `0 < α₀ < 1`, `α + α₀ < 2`, `λ, T > 0`,
`h_j = 2^{-j}/λ` and `σ_j² = h_j^{-α₀}`, the series
`∑_j (T/h_j) 𝓔(h_j, σ_j, λ)` converges. `_hα0` is carried, not used; `_ha0`
(`0 < α₀`) is used despite its name (`linarith` takes `α < 2` from it and `α + α₀ < 2`). -/
theorem static_block_series {alpha alpha0 A R D lam T : ℝ} (σ : ℕ → ℝ)
    (_hα0 : 0 < alpha) (_ha0 : 0 < alpha0) (ha01 : alpha0 < 1) (hsum : alpha + alpha0 < 2)
    (hR : 0 ≤ R) (hD : 0 ≤ D) (hlam : 0 < lam) (hT : 0 < T)
    (hσ : ∀ j, σ j ^ 2 = ((2 : ℝ)⁻¹ ^ j / lam) ^ (-alpha0)) :
    Summable (fun j : ℕ => T / ((2 : ℝ)⁻¹ ^ j / lam) *
      staticE alpha A R D ((2 : ℝ)⁻¹ ^ j / lam) (σ j) lam) := by
  have hpos : ∀ j : ℕ, 0 < (2 : ℝ)⁻¹ ^ j / lam := fun j => by positivity
  have hle : ∀ j : ℕ, (2 : ℝ)⁻¹ ^ j / lam ≤ lam⁻¹ := by
    intro j
    rw [div_eq_mul_inv]
    exact mul_le_of_le_one_left (by positivity) (pow_le_one₀ (by norm_num) (by norm_num))
  have hnonneg : ∀ j : ℕ, 0 ≤ T / ((2 : ℝ)⁻¹ ^ j / lam) *
      staticE alpha A R D ((2 : ℝ)⁻¹ ^ j / lam) (σ j) lam := fun j =>
    mul_nonneg (div_nonneg hT.le (hpos j).le) (staticE_nonneg (by linarith) hR hD hlam (hpos j))
  refine Summable.of_nonneg_of_le hnonneg
    (fun j => block_term_le (by linarith) hR hlam hT (hpos j) (hle j) (by linarith) (hσ j)) ?_
  exact (((summable_dyadic_rpow hlam (by linarith)).mul_left _).add
    ((summable_dyadic_rpow hlam (by linarith)).mul_left _)).add
    ((summable_dyadic_rpow hlam (by linarith)).mul_left _)

/-- Step of `C:static-interaction` (main TeX lines 2792-2794), scalar
iteration: if `m_{j+1} ≤ e^{ℓ_j}(1 + E_j) m_j` for `j < K`, `E_j ≥ 0` and
`m_0 ≥ 0`, then `m_K ≤ exp(∑_{j<K} ℓ_j + ∑_{j<K} E_j) m_0`, by `1 + y ≤ e^y`. -/
theorem independent_blocks_scalar (K : ℕ) (m lh E : ℕ → ℝ) (hE : ∀ j, 0 ≤ E j) (hm0 : 0 ≤ m 0)
    (hstep : ∀ j, j < K → m (j + 1) ≤ Real.exp (lh j) * (1 + E j) * m j) :
    m K ≤ Real.exp (∑ j ∈ range K, lh j + ∑ j ∈ range K, E j) * m 0 := by
  induction K with
  | zero => simp
  | succ n ih =>
    have ih' := ih (fun j hj => hstep j (by omega))
    have h1 : 1 + E n ≤ Real.exp (E n) := by linarith [Real.add_one_le_exp (E n)]
    have hS : 0 ≤ Real.exp (∑ j ∈ range n, lh j + ∑ j ∈ range n, E j) * m 0 := by positivity
    calc m (n + 1) ≤ Real.exp (lh n) * (1 + E n) * m n := hstep n (by omega)
      _ ≤ Real.exp (lh n) * (1 + E n) *
            (Real.exp (∑ j ∈ range n, lh j + ∑ j ∈ range n, E j) * m 0) := by
          gcongr
          exact mul_nonneg (Real.exp_pos _).le (by linarith [hE n])
      _ ≤ Real.exp (lh n) * Real.exp (E n) *
            (Real.exp (∑ j ∈ range n, lh j + ∑ j ∈ range n, E j) * m 0) := by gcongr
      _ = _ := by
          rw [sum_range_succ, sum_range_succ, ← mul_assoc, ← Real.exp_add, ← Real.exp_add]
          ring_nf

/-- Auxiliary (Lean route): for `0 < α < 2`,
`R_α = απ μ(B_1)/(2 sin(πα/2)) ≥ 0` (main TeX lines 2061 and 2820). -/
theorem ralpha_nonneg {d : ℕ} {alpha : ℝ} (μ : Measure (HomogHypothesis.Rd d)) (h0 : 0 < alpha)
    (h2 : alpha < 2) :
    0 ≤ alpha * π * (μ (Metric.ball 0 1)).toReal / (2 * Real.sin (π * alpha / 2)) := by
  have : 0 < Real.sin (π * alpha / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith [Real.pi_pos])
  positivity

/-- Auxiliary (Lean route): for `α < 2`,
`D_Γ = c_Γ b_α ≥ 0` with `c_Γ = (3-α)Γ(B_1)/(4π)` and
`b_α = 2^α + 3^{2-α}/(2-α)` (`E:phase-constants`, main TeX lines 2058-2065). -/
theorem dgamma_nonneg {d : ℕ} {alpha : ℝ} (Γ : Measure (HomogHypothesis.Rd d)) (h2 : alpha < 2) :
    0 ≤ (3 - alpha) * (Γ (Metric.ball 0 1)).toReal / (4 * π) *
      (2 ^ alpha + 3 ^ (2 - alpha) / (2 - alpha)) := by
  have : 0 < 2 - alpha := by linarith
  have : 0 < 3 - alpha := by linarith
  positivity

/-- **Step row of `C:static-interaction`, `E:static-interaction`** (main TeX
lines 2707-2709, proof 2733-2770), with the section's constants:
`R_α = απ μ(B_1)/(2 sin(πα/2))` and `D_Γ = c_Γ b_α` from `E:phase-constants`
(lines 2058-2065) for locally finite (Radon) `μ, Γ` on `ℝ³` and `0 < α < 2`
(line 2054).  The rest of the covariance class (evenness, positive
definiteness, scaling) enters only through the supplied inputs `hY`, `hodd`,
`hborn`, `hmean`, documented at `static_interaction_step`.  Conclusion
weaker than the TeX statement as explained there.  `_hμ`, `_hΓ` only make
`μ(B_1)`, `Γ(B_1)` finite (no junk `toReal`); they are not used in the proof. -/
theorem static_interaction_paper {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (Y : ℕ → E) {alpha A R D h lam σ N : ℝ}
    (μ Γ : Measure (HomogHypothesis.Rd 3))
    (_hμ : IsLocallyFiniteMeasure μ) (_hΓ : IsLocallyFiniteMeasure Γ)
    (hα0 : 0 < alpha) (hα2 : alpha < 2)
    (hRdef : R = alpha * π * (μ (Metric.ball 0 1)).toReal / (2 * Real.sin (π * alpha / 2)))
    (hDdef : D = (3 - alpha) * (Γ (Metric.ball 0 1)).toReal / (4 * π) *
      (2 ^ alpha + 3 ^ (2 - alpha) / (2 - alpha)))
    (hA : 0 ≤ A) (hlam : 0 < lam) (hh : 0 < h) (hlh : lam * h ≤ 1) (hN : 0 ≤ N)
    (hY0 : ‖Y 0‖ = N)
    (hY : ∀ n, 1 ≤ n → ‖Y n‖ ≤ √(Real.exp 1) / (lam * h) *
      ((A * √R) ^ n * h ^ ((4 - alpha) * n / 2) / (n ! : ℝ) ^ ((3 - alpha) / 2)) * N)
    (hodd : ∀ r s, Odd (r + s) → inner ℝ (Y r) (Y s) = 0)
    (hborn : ‖Y 1‖ ^ 2 ≤
      Real.exp 1 * (R * h ^ 2 * lam ^ (alpha - 2) * (1 + lam ^ 2 * h ^ 2) ^ 2 * N ^ 2))
    (hmean : |inner ℝ (Y 0) (Y 2)| ≤ N * (√(Real.exp 1) * (D * (1 + lam ^ 2 * h ^ 2) *
      h ^ (3 - alpha) / (lam * (2 - alpha) * (3 - alpha)) * N))) :
    Summable (fun n => σ ^ n • Y n) ∧
      ‖∑' n, σ ^ n • Y n‖ ^ 2 ≤ (1 + staticE alpha A R D h σ lam) * N ^ 2 :=
  static_interaction_step Y hα0 hα2 hA (hRdef ▸ ralpha_nonneg μ hα0 hα2)
    (hDdef ▸ dgamma_nonneg Γ hα2) hlam hh hlh hN hY0 hY hodd hborn hmean

/-- **`E:static-block-series`** (main TeX lines 2711-2716, proof 2772-2786),
in full, with the section's constants `R_α`, `D_Γ` (`E:phase-constants`,
lines 2058-2065) for locally finite `μ, Γ` on `ℝ³`: for `0 < α`,
`0 < α₀ < 1`, `α + α₀ < 2`, `λ, T > 0`, `h_j = 2^{-j}/λ` and
`σ_j² = h_j^{-α₀}`, `∑_j (T/h_j) 𝓔(h_j, σ_j, λ) < ∞` (as `Summable`; every term
is nonnegative). Nothing supplied. -/
theorem static_block_series_paper {alpha alpha0 A R D lam T : ℝ} (σ : ℕ → ℝ)
    (μ Γ : Measure (HomogHypothesis.Rd 3))
    (_hμ : IsLocallyFiniteMeasure μ) (_hΓ : IsLocallyFiniteMeasure Γ)
    (hα0 : 0 < alpha) (ha0 : 0 < alpha0) (ha01 : alpha0 < 1) (hsum : alpha + alpha0 < 2)
    (hRdef : R = alpha * π * (μ (Metric.ball 0 1)).toReal / (2 * Real.sin (π * alpha / 2)))
    (hDdef : D = (3 - alpha) * (Γ (Metric.ball 0 1)).toReal / (4 * π) *
      (2 ^ alpha + 3 ^ (2 - alpha) / (2 - alpha)))
    (hlam : 0 < lam) (hT : 0 < T)
    (hσ : ∀ j, σ j ^ 2 = ((2 : ℝ)⁻¹ ^ j / lam) ^ (-alpha0)) :
    Summable (fun j : ℕ => T / ((2 : ℝ)⁻¹ ^ j / lam) *
      staticE alpha A R D ((2 : ℝ)⁻¹ ^ j / lam) (σ j) lam) :=
  static_block_series σ hα0 ha0 ha01 hsum (hRdef ▸ ralpha_nonneg μ hα0 (by linarith))
    (hDdef ▸ dgamma_nonneg Γ (by linarith)) hlam hT hσ

/-- **Step row of `C:static-interaction`, `E:independent-static-blocks`** (main
TeX lines 2720-2725, proof 2787-2794): with `m_j` standing for
`E‖M_j(h_j) ⋯ M_1(h_1)(f,g)‖_λ²` (indices shifted to start at `0`), the
supplied input `hstep` is the per-block bound
`m_{j+1} ≤ e^{λh_j}(1 + 𝓔(h_j, σ_j, λ)) m_j`, which the TeX obtains from
`E:static-interaction`, `‖S_0(h_j)‖² ≤ e^{λh_j}`, density and tensoring with
the independent past (lines 2788-2793).  Conclusion:
`m_K ≤ exp{λ ∑ h_j + ∑ 𝓔(h_j, σ_j, λ)} m_0`.  `_hlh` (`λh_j ≤ 1`), `_hμ`,
`_hΓ` are carried, not used. -/
theorem independent_static_blocks_paper {alpha A R D lam : ℝ} (K : ℕ) (h σ m : ℕ → ℝ)
    (μ Γ : Measure (HomogHypothesis.Rd 3))
    (_hμ : IsLocallyFiniteMeasure μ) (_hΓ : IsLocallyFiniteMeasure Γ)
    (hα0 : 0 < alpha) (hα2 : alpha < 2)
    (hRdef : R = alpha * π * (μ (Metric.ball 0 1)).toReal / (2 * Real.sin (π * alpha / 2)))
    (hDdef : D = (3 - alpha) * (Γ (Metric.ball 0 1)).toReal / (4 * π) *
      (2 ^ alpha + 3 ^ (2 - alpha) / (2 - alpha)))
    (hlam : 0 < lam) (hh : ∀ j, 0 < h j) (_hlh : ∀ j, lam * h j ≤ 1) (hm0 : 0 ≤ m 0)
    (hstep : ∀ j, j < K → m (j + 1) ≤
      Real.exp (lam * h j) * (1 + staticE alpha A R D (h j) (σ j) lam) * m j) :
    m K ≤ Real.exp (lam * ∑ j ∈ range K, h j +
      ∑ j ∈ range K, staticE alpha A R D (h j) (σ j) lam) * m 0 := by
  have hR := hRdef ▸ ralpha_nonneg μ hα0 hα2
  have hD := hDdef ▸ dgamma_nonneg Γ hα2
  have := independent_blocks_scalar K m (fun j => lam * h j)
    (fun j => staticE alpha A R D (h j) (σ j) lam)
    (fun j => staticE_nonneg hα2 hR hD hlam (hh j)) hm0 hstep
  simpa [mul_sum] using this

/-! ## `P:interval-coefficients` (main TeX lines 3402-3581) -/

/-- `v_i = i^{-β} + k^{-1} i^{-(β-1)} + k^{α-2} i^{-p}` with `β = 4-α-α₀`,
`p = 2-α₀` (`L:inventory-product`, main TeX lines 2989-2990). -/
def invV (alpha alpha0 : ℝ) (k i : ℕ) : ℝ :=
  (i : ℝ) ^ (-(4 - alpha - alpha0)) + (k : ℝ)⁻¹ * (i : ℝ) ^ (-(4 - alpha - alpha0 - 1)) +
    (k : ℝ) ^ (alpha - 2) * (i : ℝ) ^ (-(2 - alpha0))

/-- `b_{i,l} = i^{-βl}(1 + l i/k)²/(l!)^ν`, `ν = 3-α` (`L:inventory-product`,
main TeX line 2991). -/
def invB (alpha alpha0 : ℝ) (k i l : ℕ) : ℝ :=
  (i : ℝ) ^ (-((4 - alpha - alpha0) * l)) * (1 + l * i / k) ^ 2 / (l ! : ℝ) ^ (3 - alpha)

/-- The coefficients of `1 + v_i z + ∑_{l ≥ 2} b_{i,l} z^l`
(`E:inventory-product`, main TeX lines 2994-2997). -/
def invCoeff (alpha alpha0 : ℝ) (k i l : ℕ) : ℝ :=
  if l = 0 then 1 else if l = 1 then invV alpha alpha0 k i else invB alpha alpha0 k i l

/-- The statement `E:inventory-product` of `L:inventory-product` (main TeX
lines 2986-2997) with constant `C`: for every `M` and `k ≥ 1`,
`[z^k] ∏_{i=1}^M (1 + v_i z + ∑_{l≥2} b_{i,l} z^l) ≤ C^k/(k!)^ν`, the product
written over `j : Fin M` with `i = j + 1`.  Formalized by wave item L7-a; used
here only as a hypothesis. -/
def InventoryProduct (alpha alpha0 C : ℝ) : Prop :=
  ∀ M k : ℕ, 1 ≤ k →
    PowerSeries.coeff k (∏ j : Fin M, PowerSeries.mk (invCoeff alpha alpha0 k ((j : ℕ) + 1))) ≤
      C ^ k / (k ! : ℝ) ^ (3 - alpha)

/-- `ℓ_i = 1_{r_i > 0} + 1_{q_i > 0}` (`L:fixed-split`, main TeX line 3075)
for a split `p = (r_i, q_i)`. -/
def splitEll (p : ℕ × ℕ) : ℕ := (if 0 < p.1 then 1 else 0) + (if 0 < p.2 then 1 else 0)

/-- The per-color factor of `E:fixed-split-bound` (main TeX lines 3080-3091)
at `λ`: `1` if `k_i = 0` (inactive color); `σ_i² h_i² λ^{α-2}` for a cross
singleton `k_i = 1`, `(r_i, q_i) = (1,1)` (the set `𝒞`); otherwise
`(σ_i² h_i^{4-α})^{k_i}/(k_i!)^ν (1 + k_i/(λh_i))^{ℓ_i}` (the set `ℬ`).  The
product over all colors is the product in `E:fixed-split-bound`. -/
def splitFactor (alpha σ h lam : ℝ) (κ : ℕ) (p : ℕ × ℕ) : ℝ :=
  if κ = 0 then 1
  else if κ = 1 ∧ p = (1, 1) then σ ^ 2 * h ^ 2 * lam ^ (alpha - 2)
  else (σ ^ 2 * h ^ (4 - alpha)) ^ κ / (κ ! : ℝ) ^ (3 - alpha) * (1 + κ / (lam * h)) ^ splitEll p

/-- Auxiliary (Lean route): `ℓ_i ≤ 2`. -/
theorem splitEll_le (p : ℕ × ℕ) : splitEll p ≤ 2 := by
  unfold splitEll; split_ifs <;> omega

/-- Auxiliary (Lean route): the split factors are nonnegative for `h, λ > 0`. -/
theorem splitFactor_nonneg {alpha σ h lam : ℝ} (hh : 0 < h) (hlam : 0 < lam) (κ : ℕ)
    (p : ℕ × ℕ) : 0 ≤ splitFactor alpha σ h lam κ p := by
  unfold splitFactor
  split_ifs <;> positivity

/-- Auxiliary (Lean route): the inventory coefficients are nonnegative. -/
theorem invCoeff_nonneg (alpha alpha0 : ℝ) (k i l : ℕ) : 0 ≤ invCoeff alpha alpha0 k i l := by
  unfold invCoeff invV invB
  split_ifs <;> positivity

/-- Auxiliary (Lean route): `(LT/i)^q = L^q T^q i^{-q}` for `L, T ≥ 0`, `i > 0`. -/
theorem H_rpow {L T q : ℝ} {i : ℝ} (hL : 0 ≤ L) (hT : 0 ≤ T) (hi : 0 < i) :
    (L * T / i) ^ q = L ^ q * T ^ q * i ^ (-q) := by
  rw [Real.div_rpow (by positivity) hi.le, Real.mul_rpow hL hT, Real.rpow_neg hi.le, div_eq_mul_inv]

/-- Step of `P:interval-coefficients` (main TeX lines 3506-3538, singleton
mean row): for `β = 4-α-α₀ ≥ 1`, `L ≥ 1`, `k, i ≥ 1`, `T, h > 0` and
`h ≤ LT/i`, `h^β (1 + 1/(λh)) ≤ L^β T^β (i^{-β} + k^{-1} i^{-(β-1)})` at
`λ = k/T`.  The TeX's monotonicity in `h` is used in the form
`h^β(1 + 1/(λh)) = h^β + h^{β-1}/λ`. -/
theorem singleton_weight_le {alpha alpha0 h T L : ℝ} {k i : ℕ} (hβ1 : 1 ≤ 4 - alpha - alpha0)
    (hh : 0 < h) (hT : 0 < T) (hL : 1 ≤ L) (hk : 1 ≤ k) (hi : 1 ≤ i)
    (hlen : h ≤ L * T / i) :
    h ^ (4 - alpha - alpha0) * (1 + 1 / (k / T * h)) ≤
      L ^ (4 - alpha - alpha0) * T ^ (4 - alpha - alpha0) *
        ((i : ℝ) ^ (-(4 - alpha - alpha0)) + (k : ℝ)⁻¹ * (i : ℝ) ^ (-(4 - alpha - alpha0 - 1))) := by
  set β := 4 - alpha - alpha0
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hi0 : (0 : ℝ) < i := by exact_mod_cast hi
  have hL0 : 0 ≤ L := by linarith
  have e1 : h ^ β * (1 + 1 / (k / T * h)) = h ^ β + h ^ (β - 1) * (T / k) := by
    rw [Real.rpow_sub_one hh.ne']
    field_simp
  have m1 : h ^ β ≤ (L * T / i) ^ β := Real.rpow_le_rpow hh.le hlen (by linarith)
  have m2 : h ^ (β - 1) ≤ (L * T / i) ^ (β - 1) := Real.rpow_le_rpow hh.le hlen (by linarith)
  rw [e1]
  rw [H_rpow hL0 hT.le hi0] at m1 m2
  have hLle : L ^ (β - 1) ≤ L ^ β := Real.rpow_le_rpow_of_exponent_le hL (by linarith)
  have hTT : T ^ (β - 1) * (T / k) = T ^ β * (k : ℝ)⁻¹ := by
    rw [Real.rpow_sub_one hT.ne']; field_simp
  calc h ^ β + h ^ (β - 1) * (T / k)
      ≤ L ^ β * T ^ β * (i : ℝ) ^ (-β) + L ^ (β - 1) * T ^ (β - 1) * (i : ℝ) ^ (-(β - 1)) * (T / k) := by
        gcongr
    _ = L ^ β * T ^ β * (i : ℝ) ^ (-β) + L ^ (β - 1) * (T ^ (β - 1) * (T / k)) * (i : ℝ) ^ (-(β - 1)) := by
        ring
    _ ≤ L ^ β * T ^ β * (i : ℝ) ^ (-β) + L ^ β * (T ^ (β - 1) * (T / k)) * (i : ℝ) ^ (-(β - 1)) := by
        gcongr
    _ = _ := by rw [hTT]; ring

/-- Step of `P:interval-coefficients` (main TeX lines 3506-3538, cross
singleton row): for `α ≤ 2`, `α₀ ≤ 2`, `L ≥ 1`, `k, i ≥ 1`, `T, h > 0` and
`h ≤ LT/i`, `h^{2-α₀} λ^{α-2} ≤ L^β T^β k^{α-2} i^{-(2-α₀)}` at `λ = k/T`. -/
theorem cross_weight_le {alpha alpha0 h T L : ℝ} {k i : ℕ} (hα2 : alpha ≤ 2) (ha0 : alpha0 ≤ 2)
    (hh : 0 < h) (hT : 0 < T) (hL : 1 ≤ L) (hk : 1 ≤ k) (hi : 1 ≤ i) (hlen : h ≤ L * T / i) :
    h ^ (2 - alpha0) * (k / T) ^ (alpha - 2) ≤
      L ^ (4 - alpha - alpha0) * T ^ (4 - alpha - alpha0) *
        ((k : ℝ) ^ (alpha - 2) * (i : ℝ) ^ (-(2 - alpha0))) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hi0 : (0 : ℝ) < i := by exact_mod_cast hi
  have hL0 : 0 ≤ L := by linarith
  have m1 : h ^ (2 - alpha0) ≤ (L * T / i) ^ (2 - alpha0) :=
    Real.rpow_le_rpow hh.le hlen (by linarith)
  rw [H_rpow hL0 hT.le hi0] at m1
  have hLle : L ^ (2 - alpha0) ≤ L ^ (4 - alpha - alpha0) :=
    Real.rpow_le_rpow_of_exponent_le hL (by linarith)
  have hTT : T ^ (2 - alpha0) * (T ^ (alpha - 2))⁻¹ = T ^ (4 - alpha - alpha0) := by
    rw [← Real.rpow_neg hT.le, ← Real.rpow_add hT]; congr 1; ring
  rw [Real.div_rpow hk0.le hT.le]
  calc h ^ (2 - alpha0) * ((k : ℝ) ^ (alpha - 2) / T ^ (alpha - 2))
      ≤ L ^ (2 - alpha0) * T ^ (2 - alpha0) * (i : ℝ) ^ (-(2 - alpha0)) *
          ((k : ℝ) ^ (alpha - 2) / T ^ (alpha - 2)) := by gcongr
    _ = L ^ (2 - alpha0) * (T ^ (2 - alpha0) * (T ^ (alpha - 2))⁻¹) *
          ((k : ℝ) ^ (alpha - 2) * (i : ℝ) ^ (-(2 - alpha0))) := by ring
    _ ≤ L ^ (4 - alpha - alpha0) * (T ^ (2 - alpha0) * (T ^ (alpha - 2))⁻¹) *
          ((k : ℝ) ^ (alpha - 2) * (i : ℝ) ^ (-(2 - alpha0))) := by gcongr
    _ = _ := by rw [hTT]

/-- Step of `P:interval-coefficients` (main TeX lines 3518-3533, higher-degree
row): for `β ≥ 1`, `l ≥ 2`, `L ≥ 1`, `k, i ≥ 1`, `T, h > 0` and `h ≤ LT/i`,
`(h^β)^l (1 + l/(λh))² ≤ (L^β T^β)^l i^{-βl}(1 + l i/k)²` at `λ = k/T`.
Proof as in the TeX: the whole weight `h^{βl-2}(h + l/λ)²` increases with `h`,
and `1 + l/(λ LT/i) ≤ 1 + l i/k` since `L ≥ 1`. -/
theorem higher_weight_le {alpha alpha0 h T L : ℝ} {k i l : ℕ} (hβ1 : 1 ≤ 4 - alpha - alpha0)
    (hh : 0 < h) (hT : 0 < T) (hL : 1 ≤ L) (hk : 1 ≤ k) (hi : 1 ≤ i) (hl : 2 ≤ l)
    (hlen : h ≤ L * T / i) :
    (h ^ (4 - alpha - alpha0)) ^ l * (1 + l / (k / T * h)) ^ 2 ≤
      (L ^ (4 - alpha - alpha0) * T ^ (4 - alpha - alpha0)) ^ l *
        ((i : ℝ) ^ (-((4 - alpha - alpha0) * l)) * (1 + l * i / k) ^ 2) := by
  set β := 4 - alpha - alpha0
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hi0 : (0 : ℝ) < i := by exact_mod_cast hi
  have hL0 : 0 ≤ L := by linarith
  set H := L * T / i with hHdef
  have hH : 0 < H := by positivity
  have hl2 : (2 : ℝ) ≤ l := by exact_mod_cast hl
  have hexp : 0 ≤ β * l - 2 := by nlinarith
  -- rewrite LHS as h^(βl-2) (h + lT/k)^2
  have key : ∀ x : ℝ, 0 < x → (x ^ β) ^ l * (1 + l / (k / T * x)) ^ 2 =
      x ^ (β * l - 2) * (x + l * T / k) ^ 2 := by
    intro x hx
    rw [← Real.rpow_mul_natCast hx.le, Real.rpow_sub hx, Real.rpow_two]
    field_simp
  rw [key h hh]
  have m1 : h ^ (β * l - 2) ≤ H ^ (β * l - 2) := Real.rpow_le_rpow hh.le hlen hexp
  have m2 : h + l * T / k ≤ H * (1 + l * i / k) := by
    have : l * T / k ≤ H * (l * i / k) := by
      rw [hHdef]
      have : L * T / i * (l * i / k) = L * (l * T / k) := by field_simp
      rw [this]
      have : 0 ≤ l * T / k := by positivity
      nlinarith
    nlinarith
  have hH2 : H ^ (β * l - 2) * (H * (1 + l * i / k)) ^ 2 =
      (H ^ β) ^ l * (1 + l * i / k) ^ 2 := by
    rw [← Real.rpow_mul_natCast hH.le, Real.rpow_sub hH, Real.rpow_two]
    field_simp
  calc h ^ (β * l - 2) * (h + l * T / k) ^ 2 ≤ H ^ (β * l - 2) * (H * (1 + l * i / k)) ^ 2 := by
        gcongr
    _ = (H ^ β) ^ l * (1 + l * i / k) ^ 2 := hH2
    _ = _ := by
        rw [hHdef, H_rpow hL0 hT.le hi0, mul_pow, show -(β * l) = (-β) * l by ring,
          Real.rpow_mul_natCast hi0.le]
        ring

/-- Step of `P:interval-coefficients` (main TeX line 3488): `2k+1 ≤ 3^k`
(also the split count `∏_i (2k_i + 1) ≤ 3^k` per color). -/
theorem two_mul_add_one_le_three_pow (k : ℕ) : 2 * k + 1 ≤ 3 ^ k := by
  induction k with
  | zero => norm_num
  | succ n ih => rw [pow_succ]; omega

/-- Step of `P:interval-coefficients` (main TeX lines 3499-3538), one color:
for `α < 2`, `0 < α₀ < 1`, `α + α₀ < 2`, `h, T > 0`, `L ≥ 1`, `c ≥ 0`,
`k, i ≥ 1`, `h ≤ LT/i` and `σ² ≤ c h^{-α₀}`, the sum of the split factors over
all splits `r + q = 2l` of a color of degree `l` is at most
`(3c L^β T^β)^l` times the inventory coefficient (`1`, `v_i`, `b_{i,l}`).
This combines the length substitution and the split count
(`2l + 1 ≤ 3^l`; for `l = 1` the two singleton alternatives `m_i + c_i`). -/
theorem color_split_sum_le {alpha alpha0 σ h T L c : ℝ} {k i l : ℕ}
    (hα2 : alpha < 2) (ha0 : 0 < alpha0) (ha01 : alpha0 < 1) (hsum : alpha + alpha0 < 2)
    (hh : 0 < h) (hT : 0 < T) (hL : 1 ≤ L) (hc : 0 ≤ c) (hk : 1 ≤ k) (hi : 1 ≤ i)
    (hlen : h ≤ L * T / i) (hσ : σ ^ 2 ≤ c * h ^ (-alpha0)) :
    ∑ p ∈ antidiagonal (2 * l), splitFactor alpha σ h (k / T) l p ≤
      (3 * c * (L ^ (4 - alpha - alpha0) * T ^ (4 - alpha - alpha0))) ^ l *
        invCoeff alpha alpha0 k i l := by
  set β := 4 - alpha - alpha0 with hβdef
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hlam : 0 < (k : ℝ) / T := by positivity
  have hP : 0 ≤ L ^ β * T ^ β := by positivity
  -- σ² h^{4-α} ≤ c h^β and σ² h² ≤ c h^{2-α0}
  have hs1 : σ ^ 2 * h ^ (4 - alpha) ≤ c * h ^ β := by
    calc σ ^ 2 * h ^ (4 - alpha) ≤ c * h ^ (-alpha0) * h ^ (4 - alpha) := by gcongr
      _ = c * h ^ β := by
          rw [mul_assoc, ← Real.rpow_add hh, hβdef]; ring_nf
  have hs2 : σ ^ 2 * h ^ 2 ≤ c * h ^ (2 - alpha0) := by
    calc σ ^ 2 * h ^ 2 ≤ c * h ^ (-alpha0) * h ^ 2 := by gcongr
      _ = c * h ^ (2 - alpha0) := by
          rw [mul_assoc, ← Real.rpow_two h, ← Real.rpow_add hh]; ring_nf
  rcases Nat.lt_or_ge l 2 with hl | hl
  · interval_cases l
    · simp [splitFactor, invCoeff]
    · -- l = 1
      have hA : antidiagonal (2 * 1) = {(0, 2), (1, 1), (2, 0)} := by rfl
      rw [hA, sum_insert (by decide), sum_insert (by decide), sum_singleton]
      have hS := singleton_weight_le (alpha := alpha) (alpha0 := alpha0) (by linarith) hh hT hL hk hi hlen
      have hX := cross_weight_le (alpha := alpha) (alpha0 := alpha0) hα2.le (by linarith) hh hT hL hk hi hlen
      have hsing : σ ^ 2 * h ^ (4 - alpha) * (1 + 1 / (k / T * h)) ≤ c * (L ^ β * T ^ β *
          ((i : ℝ) ^ (-β) + (k : ℝ)⁻¹ * (i : ℝ) ^ (-(β - 1)))) := by
        calc _ ≤ c * h ^ β * (1 + 1 / (k / T * h)) := by gcongr
          _ = c * (h ^ β * (1 + 1 / (k / T * h))) := by ring
          _ ≤ _ := by gcongr
      have hcross : σ ^ 2 * h ^ 2 * (k / T) ^ (alpha - 2) ≤ c * (L ^ β * T ^ β *
          ((k : ℝ) ^ (alpha - 2) * (i : ℝ) ^ (-(2 - alpha0)))) := by
        calc _ ≤ c * h ^ (2 - alpha0) * (k / T) ^ (alpha - 2) := by gcongr
          _ = c * (h ^ (2 - alpha0) * (k / T) ^ (alpha - 2)) := by ring
          _ ≤ _ := by gcongr
      have t1 : (0 : ℝ) ≤ (i : ℝ) ^ (-β) := by positivity
      have t2 : (0 : ℝ) ≤ (k : ℝ)⁻¹ * (i : ℝ) ^ (-(β - 1)) := by positivity
      have t3 : (0 : ℝ) ≤ (k : ℝ) ^ (alpha - 2) * (i : ℝ) ^ (-(2 - alpha0)) := by positivity
      have hcP : 0 ≤ c * (L ^ β * T ^ β) := by positivity
      have hs02 : splitFactor alpha σ h (k / T) 1 (0, 2) =
          σ ^ 2 * h ^ (4 - alpha) * (1 + 1 / (k / T * h)) := by
        simp [splitFactor, splitEll]
      have hs20 : splitFactor alpha σ h (k / T) 1 (2, 0) =
          σ ^ 2 * h ^ (4 - alpha) * (1 + 1 / (k / T * h)) := by
        simp [splitFactor, splitEll]
      have hs11 : splitFactor alpha σ h (k / T) 1 (1, 1) = σ ^ 2 * h ^ 2 * (k / T) ^ (alpha - 2) := by
        simp [splitFactor]
      have hinv1 : invCoeff alpha alpha0 k i 1 = invV alpha alpha0 k i := by simp [invCoeff]
      rw [hs02, hs11, hs20, hinv1, pow_one]
      change _ ≤ _ * ((i : ℝ) ^ (-β) + (k : ℝ)⁻¹ * (i : ℝ) ^ (-(β - 1)) +
        (k : ℝ) ^ (alpha - 2) * (i : ℝ) ^ (-(2 - alpha0)))
      nlinarith [mul_le_mul_of_nonneg_left t3 hcP, mul_le_mul_of_nonneg_left t1 hcP,
        mul_le_mul_of_nonneg_left t2 hcP]
  · -- l ≥ 2
    have hl0 : l ≠ 0 := by omega
    have hl1 : l ≠ 1 := by omega
    have hH := higher_weight_le (alpha := alpha) (alpha0 := alpha0) (l := l) (by linarith) hh hT hL hk hi hl hlen
    have hbase : 1 ≤ 1 + (l : ℝ) / (k / T * h) := by
      have : 0 ≤ (l : ℝ) / (k / T * h) := by positivity
      linarith
    have hterm : ∀ p ∈ antidiagonal (2 * l), splitFactor alpha σ h (k / T) l p ≤
        (c * (L ^ β * T ^ β)) ^ l * invB alpha alpha0 k i l := by
      intro p _
      simp only [splitFactor, hl0, hl1, false_and, ite_false]
      have hpow : (1 + (l : ℝ) / (k / T * h)) ^ splitEll p ≤ (1 + (l : ℝ) / (k / T * h)) ^ 2 :=
        pow_le_pow_right₀ hbase (splitEll_le p)
      have hfac : 0 < (l ! : ℝ) ^ (3 - alpha) := by positivity
      unfold invB
      calc (σ ^ 2 * h ^ (4 - alpha)) ^ l / (l ! : ℝ) ^ (3 - alpha) *
            (1 + (l : ℝ) / (k / T * h)) ^ splitEll p
          ≤ (c * h ^ β) ^ l / (l ! : ℝ) ^ (3 - alpha) * (1 + (l : ℝ) / (k / T * h)) ^ 2 := by
            gcongr
        _ = c ^ l * ((h ^ β) ^ l * (1 + (l : ℝ) / (k / T * h)) ^ 2) / (l ! : ℝ) ^ (3 - alpha) := by
            ring
        _ ≤ c ^ l * ((L ^ β * T ^ β) ^ l *
              ((i : ℝ) ^ (-(β * l)) * (1 + l * i / k) ^ 2)) / (l ! : ℝ) ^ (3 - alpha) := by
            gcongr
        _ = _ := by ring
    have hcard : ((antidiagonal (2 * l)).card : ℝ) ≤ 3 ^ l := by
      rw [Finset.Nat.card_antidiagonal]
      exact_mod_cast two_mul_add_one_le_three_pow l
    have hb0 : 0 ≤ (c * (L ^ β * T ^ β)) ^ l * invB alpha alpha0 k i l := by
      unfold invB; positivity
    calc ∑ p ∈ antidiagonal (2 * l), splitFactor alpha σ h (k / T) l p
        ≤ ∑ p ∈ antidiagonal (2 * l), (c * (L ^ β * T ^ β)) ^ l * invB alpha alpha0 k i l :=
          sum_le_sum hterm
      _ = ((antidiagonal (2 * l)).card : ℝ) * ((c * (L ^ β * T ^ β)) ^ l * invB alpha alpha0 k i l) := by
          rw [sum_const, nsmul_eq_mul]
      _ ≤ 3 ^ l * ((c * (L ^ β * T ^ β)) ^ l * invB alpha alpha0 k i l) := by gcongr
      _ = _ := by simp only [invCoeff, hl0, hl1, ite_false]; ring

/-- Step of `P:interval-coefficients` (main TeX lines 3539-3544): the sum over
degree vectors `κ` with `∑ κ_i = k` of `∏_i w_{i,κ_i}` is the `k`th coefficient
of `∏_i ∑_l w_{i,l} z^l` (`PowerSeries.coeff_prod`), here for the inventory
weights. -/
theorem kvector_sum_eq_coeff (alpha alpha0 : ℝ) (M k : ℕ) :
    ∑ κ ∈ (univ : Finset (Fin M)).finsuppAntidiag k,
        ∏ i : Fin M, invCoeff alpha alpha0 k ((i : ℕ) + 1) (κ i) =
      PowerSeries.coeff k (∏ j : Fin M, PowerSeries.mk (invCoeff alpha alpha0 k ((j : ℕ) + 1))) := by
  rw [PowerSeries.coeff_prod]
  simp [PowerSeries.coeff_mk]

/-- **Step row of `P:interval-coefficients`, `E:interval-coefficient-bound`**
(main TeX lines 3405-3408, proof 3478-3547) at `L ≥ 1`, general form.  For
`α < 2`, `0 < α₀ < 1`, `α + α₀ < 2`, `k ≥ 1`, `T > 0`, `c, R, V, C_split ≥ 0`,
positive lengths with `h_i ≤ LT/i` and `σ_i² ≤ c h_i^{-α₀}` (`E:interval-inventory`,
line 3045, colors `i = j + 1` for `j : Fin M`), supplied inputs:
* `hinv`: `L:inventory-product` with constant `C_inv` (L7-a);
* `hsplits`: `E:interval-energy-splits` (lines 3478-3482) combined with the
  reflection parity (lines 3483-3485): the coefficient is the sum over degree
  vectors `κ` (`∑ κ_i = k`) and splits `p_i = (r_i, q_i)`, `r_i + q_i = 2κ_i`,
  of `Q_{r,q}`;
* `hfixed`: `L:fixed-split` (`E:fixed-split-bound`, lines 3080-3091) at
  `λ = k/T` with constant `C_split`, for every such split.
Conclusion: `|coef| ≤ (12 c L^β C_split C_inv)^k R^k T^{βk}/(k!)^ν V`.  Proved
here: per-color length substitution and split counting (`color_split_sum_le`),
`k² ≤ 4^k`, and the product-coefficient identity (`kvector_sum_eq_coeff`).
The identification of the coefficients with the finite-interval model
(lines 3490-3497, 3549-3565) is not formalized. -/
theorem interval_coefficient_assembly {alpha alpha0 R T L c Cs Cinv V coef : ℝ} {M k : ℕ}
    (h σ : Fin M → ℝ) (Q : (Fin M → ℕ × ℕ) → ℝ)
    (hα2 : alpha < 2) (ha0 : 0 < alpha0) (ha01 : alpha0 < 1) (hsum : alpha + alpha0 < 2)
    (hk : 1 ≤ k) (hT : 0 < T) (hL : 1 ≤ L) (hc : 0 ≤ c) (hR : 0 ≤ R) (hV : 0 ≤ V) (hCs : 0 ≤ Cs)
    (hh : ∀ i, 0 < h i) (hlen : ∀ i : Fin M, h i ≤ L * T / ((i : ℕ) + 1 : ℕ))
    (hσ : ∀ i, σ i ^ 2 ≤ c * h i ^ (-alpha0))
    (hinv : InventoryProduct alpha alpha0 Cinv)
    (hsplits : coef = ∑ κ ∈ (univ : Finset (Fin M)).finsuppAntidiag k,
      ∑ p ∈ Fintype.piFinset (fun i => antidiagonal (2 * κ i)), Q p)
    (hfixed : ∀ κ ∈ (univ : Finset (Fin M)).finsuppAntidiag k,
      ∀ p ∈ Fintype.piFinset (fun i => antidiagonal (2 * κ i)),
        |Q p| ≤ (k : ℝ) ^ 2 * Cs ^ k * R ^ k * V *
          ∏ i, splitFactor alpha (σ i) (h i) (k / T) (κ i) (p i)) :
    |coef| ≤ (12 * c * L ^ (4 - alpha - alpha0) * Cs * Cinv) ^ k * R ^ k *
      T ^ ((4 - alpha - alpha0) * k) / (k ! : ℝ) ^ (3 - alpha) * V := by
  set β := 4 - alpha - alpha0 with hβdef
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hlam : 0 < (k : ℝ) / T := by positivity
  set W := 3 * c * (L ^ β * T ^ β) with hW
  have hW0 : 0 ≤ W := by positivity
  set A := (k : ℝ) ^ 2 * Cs ^ k * R ^ k * V with hA
  have hA0 : 0 ≤ A := by positivity
  set u : Fin M → ℕ → ℝ := fun i l => invCoeff alpha alpha0 k ((i : ℕ) + 1) l with hu
  -- step 1: triangle inequality and fixed-split
  have step1 : |coef| ≤ ∑ κ ∈ (univ : Finset (Fin M)).finsuppAntidiag k,
      A * ∏ i, ∑ q ∈ antidiagonal (2 * κ i), splitFactor alpha (σ i) (h i) (k / T) (κ i) q := by
    rw [hsplits]
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun κ hκ => ?_)
    refine (abs_sum_le_sum_abs _ _).trans ?_
    rw [Finset.prod_univ_sum, mul_sum]
    exact sum_le_sum fun p hp => hfixed κ hκ p hp
  -- step 2: per-color bound
  have step2 : ∀ κ ∈ (univ : Finset (Fin M)).finsuppAntidiag k,
      A * ∏ i, ∑ q ∈ antidiagonal (2 * κ i), splitFactor alpha (σ i) (h i) (k / T) (κ i) q ≤
        A * (W ^ k * ∏ i, u i (κ i)) := by
    intro κ hκ
    have hsumκ : ∑ i, κ i = k := ((mem_finsuppAntidiag).1 hκ).1
    apply mul_le_mul_of_nonneg_left _ hA0
    calc ∏ i, ∑ q ∈ antidiagonal (2 * κ i), splitFactor alpha (σ i) (h i) (k / T) (κ i) q
        ≤ ∏ i, W ^ (κ i) * u i (κ i) := by
          apply Finset.prod_le_prod₀
          · intro i _; exact sum_nonneg fun q _ => splitFactor_nonneg (hh i) hlam _ _
          · intro i _
            have hi1 : 1 ≤ (i : ℕ) + 1 := by omega
            have hlen' : h i ≤ L * T / (((i : ℕ) + 1 : ℕ) : ℝ) := hlen i
            exact color_split_sum_le hα2 ha0 ha01 hsum (hh i) hT hL hc hk hi1 hlen' (hσ i)
      _ = W ^ k * ∏ i, u i (κ i) := by
          rw [prod_mul_distrib, prod_pow_eq_pow_sum, hsumκ]
  have hS0 : 0 ≤ ∑ κ ∈ (univ : Finset (Fin M)).finsuppAntidiag k, ∏ i, u i (κ i) :=
    sum_nonneg fun κ _ => prod_nonneg fun i _ => invCoeff_nonneg _ _ _ _ _
  have hS : ∑ κ ∈ (univ : Finset (Fin M)).finsuppAntidiag k, ∏ i, u i (κ i) ≤
      Cinv ^ k / (k ! : ℝ) ^ (3 - alpha) := by
    rw [hu, kvector_sum_eq_coeff]; exact hinv M k hk
  have hk4 : (k : ℝ) ^ 2 ≤ 4 ^ k := by
    have : k ^ 2 ≤ 4 ^ k := by
      have h1 := two_mul_add_one_le_three_pow k
      calc k ^ 2 ≤ (2 ^ k) ^ 2 := Nat.pow_le_pow_left (Nat.lt_two_pow_self).le 2
        _ = 4 ^ k := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
    exact_mod_cast this
  have hTk : T ^ (β * k) = (T ^ β) ^ k := Real.rpow_mul_natCast hT.le β k
  have hfin : 0 ≤ Cinv ^ k / (k ! : ℝ) ^ (3 - alpha) := hS0.trans hS
  calc |coef| ≤ ∑ κ ∈ (univ : Finset (Fin M)).finsuppAntidiag k, A * (W ^ k * ∏ i, u i (κ i)) :=
        step1.trans (sum_le_sum step2)
    _ = A * W ^ k * ∑ κ ∈ (univ : Finset (Fin M)).finsuppAntidiag k, ∏ i, u i (κ i) := by
        rw [← mul_sum, ← mul_sum]; ring
    _ ≤ A * W ^ k * (Cinv ^ k / (k ! : ℝ) ^ (3 - alpha)) := by gcongr
    _ = (k : ℝ) ^ 2 * (Cs ^ k * R ^ k * V * W ^ k * (Cinv ^ k / (k ! : ℝ) ^ (3 - alpha))) := by
        rw [hA]; ring
    _ ≤ 4 ^ k * (Cs ^ k * R ^ k * V * W ^ k * (Cinv ^ k / (k ! : ℝ) ^ (3 - alpha))) := by
        gcongr
    _ = _ := by
        rw [hTk, hW, show (12 : ℝ) = 3 * 4 by norm_num]
        rw [div_eq_mul_inv, div_eq_mul_inv]
        simp only [mul_pow]
        ring

/-- Step of `P:interval-coefficients`, `E:interval-coefficient-bound` ⟹
`E:interval-phase-bound` (main TeX lines 3570-3579), general form: for `ν ≥ 1`,
`C, R, V ≥ 0`, `T > 0`, if the energy is the sum of its coefficient series
(`henergy`, the power-series identity at `s = 1` from the entire majorant,
lines 3430-3471 and 3559-3563), odd coefficients vanish (`hodd`, Gaussian
reflection of every color, lines 3483-3485), the zero-order coefficient is at
most `e V` (lines 3570-3571) and `|c_{2k}| ≤ C^k R^k T^{βk}/(k!)^ν V` for `k ≥ 1`,
then the coefficient series converges and the energy is at most
`e · exp(ν C^{1/ν} R^{1/ν} T^{β/ν}) · V`, via `(e + Y - 1) V ≤ e Y V`,
`Y = e^{ν x^{1/ν}} ≥ 1`, `x = C R T^β`. -/
theorem interval_phase_bound_of_coefficients {ν β C R T V energy : ℝ} (c : ℕ → ℝ)
    (hν : 1 ≤ ν) (hC : 0 ≤ C) (hR : 0 ≤ R) (hT : 0 < T) (hV : 0 ≤ V)
    (hodd : ∀ k, c (2 * k + 1) = 0) (h0 : c 0 ≤ Real.exp 1 * V)
    (hcoef : ∀ k, 1 ≤ k → |c (2 * k)| ≤ C ^ k * R ^ k * T ^ (β * k) / (k ! : ℝ) ^ ν * V)
    (henergy : energy = ∑' m, c m) :
    Summable c ∧
      energy ≤ Real.exp 1 * Real.exp (ν * C ^ (1 / ν) * R ^ (1 / ν) * T ^ (β / ν)) * V := by
  set x := C * R * T ^ β with hx
  have hx0 : 0 ≤ x := by positivity
  obtain ⟨hs, hle⟩ := seriesNu_summable_le hν hx0
  have hck : ∀ k, 1 ≤ k → |c (2 * k)| ≤ V * (x ^ k / (k ! : ℝ) ^ ν) := by
    intro k hk
    calc |c (2 * k)| ≤ _ := hcoef k hk
      _ = V * (x ^ k / (k ! : ℝ) ^ ν) := by
          rw [hx, Real.rpow_mul_natCast hT.le, mul_pow, mul_pow]; ring
  have hsE1 : Summable (fun k => c (2 * (k + 1))) := by
    refine Summable.of_norm_bounded ((hs.comp_injective (add_left_injective 1)).mul_left V) ?_
    intro k
    rw [Real.norm_eq_abs]
    exact hck (k + 1) (by omega)
  have hsE : Summable (fun k => c (2 * k)) := (summable_nat_add_iff 1).1 hsE1
  have hsO : Summable (fun k => c (2 * k + 1)) := by simp [hodd]
  have hsum : Summable c := hsE.even_add_odd hsO
  refine ⟨hsum, ?_⟩
  set Y := Real.exp (ν * x ^ (1 / ν)) with hY
  have hY1 : 1 ≤ Y := Real.one_le_exp (by positivity)
  have htail : ∑' k, c (2 * (k + 1)) ≤ V * (Y - 1) := by
    have hs1 : Summable (fun k : ℕ => x ^ (k + 1) / ((k + 1)! : ℝ) ^ ν) :=
      hs.comp_injective (add_left_injective 1)
    have htt : ∑' k : ℕ, x ^ k / (k ! : ℝ) ^ ν = 1 + ∑' k : ℕ, x ^ (k + 1) / ((k + 1)! : ℝ) ^ ν := by
      rw [hs.tsum_eq_zero_add]; simp
    calc ∑' k, c (2 * (k + 1)) ≤ ∑' k : ℕ, V * (x ^ (k + 1) / ((k + 1)! : ℝ) ^ ν) :=
          hsE1.tsum_le_tsum (fun k => (le_abs_self _).trans (hck (k + 1) (by omega)))
            (hs1.mul_left V)
      _ = V * ∑' k : ℕ, x ^ (k + 1) / ((k + 1)! : ℝ) ^ ν := tsum_mul_left
      _ ≤ V * (Y - 1) := by gcongr; linarith
  have hE : energy ≤ Real.exp 1 * V + V * (Y - 1) := by
    rw [henergy, ← tsum_even_add_odd hsE hsO]
    simp only [hodd, tsum_zero, add_zero]
    rw [hsE.tsum_eq_zero_add]
    simp only [mul_zero]
    linarith
  have hxr : x ^ (1 / ν) = C ^ (1 / ν) * R ^ (1 / ν) * T ^ (β / ν) := by
    rw [hx, Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow hC hR,
      ← Real.rpow_mul hT.le]
    congr 2; ring
  have he1 : 1 ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
  calc energy ≤ Real.exp 1 * V + V * (Y - 1) := hE
    _ ≤ Real.exp 1 * Y * V := by nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.2 he1) (sub_nonneg.2 hY1)) hV]
    _ = _ := by rw [hY, hxr]; ring_nf

/-- Auxiliary (Lean route): under `H:homog`, `0 < α < 2`, `0 < α₀ < 1` and
`α + α₀ < 2`. -/
theorem homog_alpha_range {d : ℕ} {alpha alpha0 : ℝ} {Γ μ : Measure (HomogHypothesis.Rd d)}
    (hH : HomogHypothesis.HomogCovariance d alpha alpha0 Γ μ) :
    0 < alpha ∧ alpha < 2 ∧ 0 < alpha0 ∧ alpha0 < 1 ∧ alpha + alpha0 < 2 := by
  have h1 := hH.alpha0_pos
  have h2 := hH.alpha0_lt_one
  have h3 := hH.threshold
  have hpos : 0 < alpha := by
    rcases hH.alpha_range with ⟨h, _⟩ | ⟨h, hd⟩
    · exact h
    · rw [h, hd]; norm_num
  exact ⟨hpos, by linarith, h1, h2, by linarith⟩

/-- **Step row of `P:interval-coefficients`, `E:interval-coefficient-bound`**
(main TeX lines 3405-3408; proof 3416-3420 and 3478-3547) under `H:homog`
(the section's standing class, main TeX lines 2814-2819, is that of `H:homog`,
line 225) with `R_α = απ μ(B_1)/(2 sin(πα/2))` (line 2820).  Arbitrary real `L` and `c` are
reduced to `max(1, L)` and `max(c, 0)` (the TeX's `L ↦ max{1, L}`, lines
3417-3420), giving the explicit constant
`C = 12 max(c,0) max(1,L)^β C_split C_inv`, which depends only on
`α, α₀, L, c` and the constants of the two lemmas.  Supplied inputs as in
`interval_coefficient_assembly`.  Narrower than the TeX: the wrapper assumes
`R_α > 0` and `σ_i > 0`, the hypotheses of `L:fixed-split`; the TeX's
zero-noise case and the sign reduction `(σ_i, W_i) ↦ (|σ_i|, sgn σ_i W_i)`
(lines 3417, 3420-3423, a change of Gaussian fields) are not formalized.
`_hRpos` and `_hσpos` are carried so that `hfixed` is literally
`L:fixed-split`; the proof does not use them.  Positive lengths `h_i > 0` are
made explicit (the TeX's `h_i^{-α₀}`). -/
theorem interval_coefficient_assembly_paper {d : ℕ} {alpha alpha0 : ℝ}
    {Γ μ : Measure (HomogHypothesis.Rd d)}
    (hH : HomogHypothesis.HomogCovariance d alpha alpha0 Γ μ)
    {R T L c Cs Cinv V coef : ℝ} {M k : ℕ}
    (h σ : Fin M → ℝ) (Q : (Fin M → ℕ × ℕ) → ℝ)
    (hRdef : R = alpha * π * (μ (Metric.ball 0 1)).toReal / (2 * Real.sin (π * alpha / 2)))
    (_hRpos : 0 < R) (hk : 1 ≤ k) (hT : 0 < T) (hV : 0 ≤ V) (hCs : 0 ≤ Cs)
    (hh : ∀ i, 0 < h i) (_hσpos : ∀ i, 0 < σ i)
    (hlen : ∀ i : Fin M, h i ≤ L * T / ((i : ℕ) + 1 : ℕ))
    (hσ : ∀ i, σ i ^ 2 ≤ c * h i ^ (-alpha0))
    (hinv : InventoryProduct alpha alpha0 Cinv)
    (hsplits : coef = ∑ κ ∈ (univ : Finset (Fin M)).finsuppAntidiag k,
      ∑ p ∈ Fintype.piFinset (fun i => antidiagonal (2 * κ i)), Q p)
    (hfixed : ∀ κ ∈ (univ : Finset (Fin M)).finsuppAntidiag k,
      ∀ p ∈ Fintype.piFinset (fun i => antidiagonal (2 * κ i)),
        |Q p| ≤ (k : ℝ) ^ 2 * Cs ^ k * R ^ k * V *
          ∏ i, splitFactor alpha (σ i) (h i) (k / T) (κ i) (p i)) :
    |coef| ≤ (12 * max c 0 * max 1 L ^ (4 - alpha - alpha0) * Cs * Cinv) ^ k * R ^ k *
      T ^ ((4 - alpha - alpha0) * k) / (k ! : ℝ) ^ (3 - alpha) * V := by
  obtain ⟨hα0, hα2, ha0, ha01, hsum⟩ := homog_alpha_range hH
  have hR := hRdef ▸ ralpha_nonneg μ hα0 hα2
  have hlen' : ∀ i : Fin M, h i ≤ max 1 L * T / ((i : ℕ) + 1 : ℕ) := by
    intro i
    refine (hlen i).trans ?_
    gcongr
    exact le_max_right _ _
  have hσ' : ∀ i, σ i ^ 2 ≤ max c 0 * h i ^ (-alpha0) := by
    intro i
    refine (hσ i).trans ?_
    gcongr
    · exact (Real.rpow_pos_of_pos (hh i) _).le
    · exact le_max_left _ _
  exact interval_coefficient_assembly h σ Q hα2 ha0 ha01 hsum hk hT (le_max_left _ _)
    (le_max_right _ _) hR hV hCs hh hlen' hσ' hinv hsplits hfixed

/-- **Step row of `P:interval-coefficients`, `E:interval-phase-bound`** (main
TeX lines 3410-3413; proof 3570-3579) under `H:homog` with `ν = 3-α`,
`β = 4-α-α₀` and `R_α = απ μ(B_1)/(2 sin(πα/2))`: from the coefficient bound
`E:interval-coefficient-bound` with constant `C`, together with the supplied
inputs of `interval_phase_bound_of_coefficients` (power-series identity at
`s = 1`, vanishing odd coefficients, zero-order bound), the energy at `s = 1`
is at most `e exp{C' R_α^{1/ν} T^{β/ν}} ‖v‖²` with `C' = ν C^{1/ν}`, the
TeX's absorbed constant. -/
theorem interval_phase_bound_paper {d : ℕ} {alpha alpha0 : ℝ}
    {Γ μ : Measure (HomogHypothesis.Rd d)}
    (hH : HomogHypothesis.HomogCovariance d alpha alpha0 Γ μ)
    {R C T V energy : ℝ} (c : ℕ → ℝ)
    (hRdef : R = alpha * π * (μ (Metric.ball 0 1)).toReal / (2 * Real.sin (π * alpha / 2)))
    (hC : 0 ≤ C) (hT : 0 < T) (hV : 0 ≤ V)
    (hodd : ∀ k, c (2 * k + 1) = 0) (h0 : c 0 ≤ Real.exp 1 * V)
    (hcoef : ∀ k, 1 ≤ k → |c (2 * k)| ≤
      C ^ k * R ^ k * T ^ ((4 - alpha - alpha0) * k) / (k ! : ℝ) ^ (3 - alpha) * V)
    (henergy : energy = ∑' m, c m) :
    Summable c ∧
      energy ≤ Real.exp 1 * Real.exp ((3 - alpha) * C ^ (1 / (3 - alpha)) *
        R ^ (1 / (3 - alpha)) * T ^ ((4 - alpha - alpha0) / (3 - alpha))) * V := by
  obtain ⟨hα0, hα2, -, -, -⟩ := homog_alpha_range hH
  exact interval_phase_bound_of_coefficients c (by linarith) hC
    (hRdef ▸ ralpha_nonneg μ hα0 hα2) hT hV hodd h0 hcoef henergy

end StratonovichHAMSecondMoment.IntervalScalar
