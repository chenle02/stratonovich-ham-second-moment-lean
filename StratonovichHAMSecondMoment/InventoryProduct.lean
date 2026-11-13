module

/-
Copyright 2026 Le Chen. SPDX-License-Identifier: Apache-2.0

Lemma `L:inventory-product` (A coefficient bound for a product with
nonnegative coefficients) of `notes/notes_stratonovich_ham_second_moment.tex`
(main TeX file; line numbers at revision a284420): statement lines 2986-2998,
equation `E:inventory-product` at 2994-2997, proof lines 3000-3040. The
section `S:interval-upper` (line 2803) fixes at lines 2809-2812
`ν = 3 - α > 1`, `β = 4 - α - α₀ > 2`, `p = 2 - α₀ > 1`, under the standing
hypothesis `H:homog` (lines 225-242, here `HomogHypothesis.HomogCovariance`).

Formalized IN FULL, nothing supplied:

* The object is the actual coefficient: each factor
  `1 + v_i z + ∑_{l ≥ 2} b_{i,l} z^l` is the Mathlib formal power series
  `factorSeries` (`PowerSeries.mk`), the product over `i = 1, …, M` is
  `inventoryProduct`, and `[z^k]` is `PowerSeries.coeff k`.
* `inventory_product` (general form, hypotheses `0 < α₀ < 1`, `α₀ + α < 2`)
  and `inventory_product_paper` (exact-hypothesis wrapper under `H:homog`):
  for every `M` and every `k ≥ 1`,
  `[z^k] ∏_{i=1}^M (…) ≤ C^k/(k!)^ν` with the explicit constant
  `C = inventoryConst α α₀ = 4 e^{K(α,α₀)}`, a function of `(α, α₀)` only,
  hence independent of `M` and `k` (and of `d`, `Γ`, `μ`).
* `inventory_product_eval_le`: at `z = θ k^ν`, `θ = 1/4`, each factor series
  converges and the product of their sums is at most `e^{K k}` (the TeX's
  "the entire product is consequently at most `e^{Ck}`").
* `coeff_prod_le_prod_tsum`: the evaluation bound `[z^k]F ≤ F(z)/z^k` for a
  finite product of power series with nonnegative coefficients, convergent at
  `z > 0`.

Differences from the TeX proof route (the statement is unchanged):
* The factor `1 + Q_i`, `Q_i = θ k i^{-p}`, is bounded by `e^{Q_i}` and
  `∑_i Q_i ≤ θ k p/(p-1)` directly, instead of the TeX's comparison with the
  improper integral `∫_0^∞ log(1 + A x^{-p}) dx` giving `C k^{1/p}`. Both give
  the `C k` that the proof needs; no improper integral is used.
* The uniform bound `∑_{l≥2} P^l(1+ly)^2/(l!)^ν ≤ C P^2(1+y^2)` for
  `0 ≤ P ≤ 1/4`, `y ≥ 0` is proved with `C = 128`, via
  `(1+ly)^2 ≤ 2l^2(1+y^2)`, `l^2 ≤ 2^{l+1}` and `(l!)^ν ≥ 1` (the TeX gives no
  argument for it).
* The tail sums `∑_{i>k} i^{-s} ≤ k^{1-s}/(s-1)` are proved by Mathlib's
  sum-integral comparison for antitone functions (`AntitoneOn.sum_le_integral`)
  and `integral_rpow`; the TeX uses them without proof.
* All factor bounds are first proved for every partial sum of a factor and
  then passed to the series sum.
* `S_ν(x) ≤ e^{ν x^{1/ν}}` is `SeriesType.seriesNu_summable_le` (wave L6).

Of the hypotheses, the general theorem uses only `0 < α₀ < 1` and
`α₀ + α < 2` (through `ν ≥ 1`, `ν ≤ β`, `β > 2`, `p > 1` and
`ν + α - 2 = 1`); the wrapper takes the full `H:homog`, whose remaining fields
are carried but unused. In every evaluation and coefficient bound all real powers have
positive bases (`i ≥ 1`, `k ≥ 1`, `l! ≥ 1`), `k⁻¹` has `k ≥ 1`, and every `tsum` is
accompanied by its summability, so no junk value enters a bound.  The definitions and
`factorCoeff_nonneg` are unrestricted and also cover `k = 0` or `i = 0` with Lean's
conventions (`0⁻¹ = 0`, `0 ^ x = 0` for `x ≠ 0`); no bound uses those values.
-/
public import Mathlib
public import StratonovichHAMSecondMoment.TypeContinuity

@[expose] public section

noncomputable section

set_option autoImplicit false

open Real Finset PowerSeries
open scoped Nat

namespace StratonovichHAMSecondMoment.InventoryProduct

open StratonovichHAMSecondMoment.TypeContinuity

/-! ### The objects of `L:inventory-product` -/

/-- `p = 2 - α₀` (main TeX line 2812). `ν = 3 - α` and `β = 4 - α - α₀`
(lines 2811-2812) are `TypeContinuity.nuOf` and `TypeContinuity.betaOf`. -/
def pOf (alpha0 : ℝ) : ℝ := 2 - alpha0

/-- `v_i = i^{-β} + k^{-1} i^{-(β-1)} + k^{α-2} i^{-p}` (main TeX lines 2989-2990). -/
def vCoef (alpha alpha0 : ℝ) (k i : ℕ) : ℝ :=
  (i : ℝ) ^ (-betaOf alpha alpha0) + (k : ℝ)⁻¹ * (i : ℝ) ^ (-(betaOf alpha alpha0 - 1)) +
    (k : ℝ) ^ (alpha - 2) * (i : ℝ) ^ (-pOf alpha0)

/-- `b_{i,l} = i^{-βl}(1 + li/k)^2/(l!)^ν` (main TeX line 2991). -/
def bCoef (alpha alpha0 : ℝ) (k i l : ℕ) : ℝ :=
  (i : ℝ) ^ (-betaOf alpha alpha0 * l) * (1 + l * i / k) ^ 2 / ((l ! : ℕ) : ℝ) ^ nuOf alpha

/-- The coefficients of the `i`th factor `1 + v_i z + ∑_{l ≥ 2} b_{i,l} z^l`. -/
def factorCoeff (alpha alpha0 : ℝ) (k i l : ℕ) : ℝ :=
  if l = 0 then 1 else if l = 1 then vCoef alpha alpha0 k i else bCoef alpha alpha0 k i l

/-- The `i`th factor as a formal power series. -/
def factorSeries (alpha alpha0 : ℝ) (k i : ℕ) : PowerSeries ℝ :=
  PowerSeries.mk (factorCoeff alpha alpha0 k i)

/-- The product `∏_{i=1}^M (1 + v_i z + ∑_{l≥2} b_{i,l} z^l)` of
`E:inventory-product` (main TeX lines 2994-2998), as a formal power series. -/
def inventoryProduct (alpha alpha0 : ℝ) (M k : ℕ) : PowerSeries ℝ :=
  ∏ i ∈ Icc 1 M, factorSeries alpha alpha0 k i

/-- The sum `F_i(z) = ∑_l c_{i,l} z^l` of the `i`th factor at a real point. -/
def factorEval (alpha alpha0 : ℝ) (k i : ℕ) (z : ℝ) : ℝ :=
  ∑' l : ℕ, factorCoeff alpha alpha0 k i l * z ^ l

/-- The exponent `K(α, α₀)` collected in the proof (auxiliary to the Lean
route: the TeX writes a generic `C`). -/
def expConst (alpha alpha0 : ℝ) : ℝ :=
  1 / 4 * (pOf alpha0 / (pOf alpha0 - 1)) +
    nuOf alpha * ((betaOf alpha alpha0 / nuOf alpha) / (betaOf alpha alpha0 / nuOf alpha - 1)) +
    1 / 4 / (betaOf alpha alpha0 - 1) + 1 / 4 / (betaOf alpha alpha0 - 1 - 1) +
    8 / (2 * betaOf alpha alpha0 - 1) + 8 / (2 * betaOf alpha alpha0 - 2 - 1)

/-- The constant `C = C(α, α₀) = 4 e^{K(α,α₀)}` of `E:inventory-product`. -/
def inventoryConst (alpha alpha0 : ℝ) : ℝ := 4 * Real.exp (expConst alpha alpha0)

theorem inventoryConst_pos (alpha alpha0 : ℝ) : 0 < inventoryConst alpha alpha0 := by
  unfold inventoryConst; positivity

/-! ### Coefficients of a product of power series with nonnegative coefficients -/

/-- Auxiliary (Lean route): the partial sum `∑_{n ≤ N} [z^n]F z^n`. -/
def partialEval (F : PowerSeries ℝ) (N : ℕ) (z : ℝ) : ℝ :=
  ∑ n ∈ range (N + 1), coeff n F * z ^ n

/-- Auxiliary: a product of two power series with nonnegative coefficients has
nonnegative coefficients. -/
theorem coeff_mul_nonneg (F G : PowerSeries ℝ) (hF : ∀ n, 0 ≤ coeff n F)
    (hG : ∀ n, 0 ≤ coeff n G) (n : ℕ) : 0 ≤ coeff n (F * G) := by
  rw [coeff_mul]
  exact sum_nonneg fun p _ => mul_nonneg (hF _) (hG _)

/-- Auxiliary: a finite product of power series with nonnegative coefficients
has nonnegative coefficients. -/
theorem coeff_prod_nonneg {ι : Type*} (s : Finset ι) (F : ι → PowerSeries ℝ)
    (hF : ∀ i ∈ s, ∀ n, 0 ≤ coeff n (F i)) (n : ℕ) : 0 ≤ coeff n (∏ i ∈ s, F i) := by
  classical
  induction s using Finset.induction_on generalizing n with
  | empty => rw [prod_empty, coeff_one]; split_ifs <;> norm_num
  | insert j s hj ih =>
    rw [prod_insert hj]
    exact coeff_mul_nonneg _ _ (hF j (mem_insert_self j s))
      (fun m => ih (fun i hi => hF i (mem_insert_of_mem hi)) m) n

/-- Auxiliary: for nonnegative coefficients and `z ≥ 0`, the partial sum of a
product is at most the product of the partial sums. -/
theorem partialEval_mul_le (F G : PowerSeries ℝ) (hF : ∀ n, 0 ≤ coeff n F)
    (hG : ∀ n, 0 ≤ coeff n G) {z : ℝ} (hz : 0 ≤ z) (N : ℕ) :
    partialEval (F * G) N z ≤ partialEval F N z * partialEval G N z := by
  set h : ℕ × ℕ → ℝ := fun p => coeff p.1 F * z ^ p.1 * (coeff p.2 G * z ^ p.2) with hh
  have hnn : ∀ p, 0 ≤ h p := fun p => by
    simp only [hh]; exact mul_nonneg (mul_nonneg (hF _) (pow_nonneg hz _))
      (mul_nonneg (hG _) (pow_nonneg hz _))
  have h1 : partialEval (F * G) N z =
      ∑ x ∈ (range (N + 1)).sigma (fun n => Finset.HasAntidiagonal.antidiagonal n), h x.2 := by
    rw [partialEval, sum_sigma]
    refine sum_congr rfl fun n _ => ?_
    rw [coeff_mul, sum_mul]
    refine sum_congr rfl fun p hp => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    simp only [hh]; rw [← hp, pow_add]; ring
  have hinj : ∀ x ∈ (range (N + 1)).sigma (fun n => Finset.HasAntidiagonal.antidiagonal n),
      ∀ y ∈ (range (N + 1)).sigma (fun n => Finset.HasAntidiagonal.antidiagonal n),
        x.2 = y.2 → x = y := by
    rintro ⟨a, p⟩ hx ⟨b, q⟩ hy hxy
    simp only [mem_sigma, Finset.HasAntidiagonal.mem_antidiagonal] at hx hy
    simp only at hxy
    subst hxy
    have : a = b := by omega
    subst this; rfl
  have h2 : ∑ x ∈ (range (N + 1)).sigma (fun n => Finset.HasAntidiagonal.antidiagonal n), h x.2 =
      ∑ p ∈ ((range (N + 1)).sigma
        (fun n => Finset.HasAntidiagonal.antidiagonal n)).image (fun x => x.2), h p :=
    (sum_image hinj).symm
  have hsub : ((range (N + 1)).sigma
      (fun n => Finset.HasAntidiagonal.antidiagonal n)).image (fun x => x.2)
      ⊆ range (N + 1) ×ˢ range (N + 1) := by
    intro p hp
    simp only [mem_image, mem_sigma, mem_range, Finset.HasAntidiagonal.mem_antidiagonal] at hp
    obtain ⟨⟨a, q⟩, ⟨ha, hq⟩, rfl⟩ := hp
    simp only [mem_product, mem_range] at ha hq ⊢; omega
  rw [h1, h2]
  refine (sum_le_sum_of_subset_of_nonneg hsub fun p _ _ => hnn p).trans_eq ?_
  rw [sum_product, partialEval, partialEval, sum_mul_sum]

/-- Auxiliary: the partial-sum inequality for a finite product. -/
theorem partialEval_prod_le {ι : Type*} (s : Finset ι) (F : ι → PowerSeries ℝ)
    (hF : ∀ i ∈ s, ∀ n, 0 ≤ coeff n (F i)) {z : ℝ} (hz : 0 ≤ z) (N : ℕ) :
    partialEval (∏ i ∈ s, F i) N z ≤ ∏ i ∈ s, partialEval (F i) N z := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [prod_empty, partialEval]
    rw [sum_eq_single 0]
    · simp
    · intro b _ hb; simp [coeff_one, hb]
    · intro h; simp at h
  | insert j s hj ih =>
    have hs : ∀ i ∈ s, ∀ n, 0 ≤ coeff n (F i) := fun i hi => hF i (mem_insert_of_mem hi)
    rw [prod_insert hj, prod_insert hj]
    refine (partialEval_mul_le _ _ (hF j (mem_insert_self j s))
      (coeff_prod_nonneg s F hs) hz N).trans ?_
    have h0 : 0 ≤ partialEval (F j) N z :=
      sum_nonneg fun n _ => mul_nonneg (hF j (mem_insert_self j s) n) (pow_nonneg hz _)
    exact mul_le_mul_of_nonneg_left (ih hs) h0

/-- Auxiliary: one coefficient term is at most the partial sum. -/
theorem coeff_mul_pow_le_partialEval (F : PowerSeries ℝ) (hF : ∀ n, 0 ≤ coeff n F)
    {z : ℝ} (hz : 0 ≤ z) (N : ℕ) : coeff N F * z ^ N ≤ partialEval F N z := by
  unfold partialEval
  exact single_le_sum (f := fun n => coeff n F * z ^ n)
    (fun n _ => mul_nonneg (hF n) (pow_nonneg hz _)) (self_mem_range_succ N)

/-- **The evaluation bound `[z^k]F ≤ F(z)/z^k`** (main TeX lines 3037-3038,
"positivity of its coefficients bounds the `k`th coefficient"): for a finite
product `F = ∏_{i ∈ s} F_i` of power series with nonnegative coefficients,
each convergent at `z > 0` (the summability is a hypothesis), the `k`th
coefficient is at most `∏_i F_i(z)/z^k`. -/
theorem coeff_prod_le_prod_tsum {ι : Type*} (s : Finset ι) (F : ι → PowerSeries ℝ)
    (hF : ∀ i ∈ s, ∀ n, 0 ≤ coeff n (F i)) {z : ℝ} (hz : 0 < z)
    (hsum : ∀ i ∈ s, Summable (fun n => coeff n (F i) * z ^ n)) (k : ℕ) :
    coeff k (∏ i ∈ s, F i) ≤ (∏ i ∈ s, ∑' n, coeff n (F i) * z ^ n) / z ^ k := by
  rw [le_div_iff₀ (pow_pos hz k)]
  refine (coeff_mul_pow_le_partialEval _ (coeff_prod_nonneg s F hF) hz.le k).trans ?_
  refine (partialEval_prod_le s F hF hz.le k).trans ?_
  refine Finset.prod_le_prod₀ (fun i hi => sum_nonneg fun n _ =>
    mul_nonneg (hF i hi n) (pow_nonneg hz.le _)) fun i hi => ?_
  exact (hsum i hi).sum_le_tsum _ fun n _ => mul_nonneg (hF i hi n) (pow_nonneg hz.le _)

/-! ### Tail sums of `i^{-s}` -/

/-- Auxiliary: `∑_{j<n} (a + j + 1)^{-s} ≤ a^{1-s}/(s-1)` for `s > 1`, `a ≥ 1`,
by the sum-integral comparison for the antitone `x ↦ x^{-s}`. -/
theorem sum_range_rpow_tail_le {s : ℝ} (hs : 1 < s) {a : ℕ} (ha : 1 ≤ a) (n : ℕ) :
    ∑ j ∈ range n, ((a : ℝ) + ((j + 1 : ℕ) : ℝ)) ^ (-s) ≤ (a : ℝ) ^ (1 - s) / (s - 1) := by
  have ha0 : (0 : ℝ) < a := by exact_mod_cast ha
  have hanti : AntitoneOn (fun x : ℝ => x ^ (-s)) (Set.Icc (a : ℝ) (a + n)) :=
    (antitoneOn_rpow_Ioi_of_exponent_nonpos (by linarith)).mono
      fun x hx => lt_of_lt_of_le ha0 hx.1
  refine (hanti.sum_le_integral).trans ?_
  have hnot : (0 : ℝ) ∉ Set.uIcc (a : ℝ) (a + n) := by
    rw [Set.uIcc_of_le (by linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)])]
    exact fun h => absurd h.1 (not_le.mpr ha0)
  rw [integral_rpow (Or.inr ⟨by linarith, hnot⟩)]
  have h1 : (0 : ℝ) ≤ ((a : ℝ) + n) ^ (-(s - 1)) := Real.rpow_nonneg (by positivity) _
  have hs1 : (0 : ℝ) < s - 1 := by linarith
  rw [show -s + 1 = 1 - s by ring, show (1 - s : ℝ) = -(s - 1) by ring, div_neg,
    ← neg_div, neg_sub, div_le_div_iff_of_pos_right hs1]
  linarith

/-- The tail bound `∑_{i ∈ t} i^{-s} ≤ a^{1-s}/(s-1)` for a finite set `t` of
indices `i > a ≥ 1` and `s > 1` (used without proof at main TeX lines
3024-3035). -/
theorem sum_rpow_tail_le {s : ℝ} (hs : 1 < s) {a : ℕ} (ha : 1 ≤ a) (t : Finset ℕ)
    (ht : ∀ i ∈ t, a < i) :
    ∑ i ∈ t, (i : ℝ) ^ (-s) ≤ (a : ℝ) ^ (1 - s) / (s - 1) := by
  set N := t.sup id
  have hsub : t ⊆ (range N).image (fun j => a + (j + 1)) := by
    intro i hi
    have hiN : i ≤ N := le_sup (f := id) hi
    have hai := ht i hi
    rw [mem_image]
    exact ⟨i - a - 1, by rw [mem_range]; omega, by omega⟩
  have hinj : ∀ x ∈ range N, ∀ y ∈ range N, a + (x + 1) = a + (y + 1) → x = y := by
    intro x _ y _ h; omega
  calc ∑ i ∈ t, (i : ℝ) ^ (-s)
      ≤ ∑ i ∈ (range N).image (fun j => a + (j + 1)), (i : ℝ) ^ (-s) :=
        sum_le_sum_of_subset_of_nonneg hsub fun i _ _ => Real.rpow_nonneg (by positivity) _
    _ = ∑ j ∈ range N, ((a + (j + 1) : ℕ) : ℝ) ^ (-s) := sum_image hinj
    _ = ∑ j ∈ range N, ((a : ℝ) + ((j + 1 : ℕ) : ℝ)) ^ (-s) := by
        refine sum_congr rfl fun j _ => ?_; push_cast; ring_nf
    _ ≤ _ := sum_range_rpow_tail_le hs ha N

/-- The whole-sum bound `∑_{i ∈ t} i^{-s} ≤ s/(s-1)` for a finite set of
positive indices and `s > 1` (the convergence of `∑ i^{-s}` used at main TeX
lines 3004-3011 and 3017-3022). -/
theorem sum_rpow_pos_le {s : ℝ} (hs : 1 < s) (t : Finset ℕ) (ht : ∀ i ∈ t, 1 ≤ i) :
    ∑ i ∈ t, (i : ℝ) ^ (-s) ≤ s / (s - 1) := by
  classical
  rw [← sum_filter_add_sum_filter_not t (fun i => i = 1)]
  have h1 : ∑ i ∈ t.filter (fun i => i = 1), (i : ℝ) ^ (-s) ≤ 1 := by
    calc _ ≤ ∑ i ∈ ({1} : Finset ℕ), (i : ℝ) ^ (-s) := by
          refine sum_le_sum_of_subset_of_nonneg ?_ fun i _ _ =>
            Real.rpow_nonneg (by positivity) _
          intro i hi; rw [mem_filter] at hi; rw [mem_singleton]; exact hi.2
      _ = 1 := by simp
  have h2 := sum_rpow_tail_le hs le_rfl (t.filter (fun i => ¬ i = 1)) (by
    intro i hi; rw [mem_filter] at hi; have := ht i hi.1; omega)
  rw [Nat.cast_one, Real.one_rpow] at h2
  have hs1 : (0 : ℝ) < s - 1 := by linarith
  have : s / (s - 1) = 1 + 1 / (s - 1) := by field_simp; ring
  linarith

/-- Auxiliary: the scaled tail bound
`∑_{i ∈ t} c k^e i^{-s} ≤ c k/(s-1)` for `i > k ≥ 1`, `s > 1`, `c ≥ 0` and
`e ≤ s` (so `k^{e+1-s} ≤ k`). -/
theorem tail_scaled_le {s e c : ℝ} (hs : 1 < s) (hes : e ≤ s) (hc : 0 ≤ c) {k : ℕ}
    (hk : 1 ≤ k) (t : Finset ℕ) (ht : ∀ i ∈ t, k < i) :
    ∑ i ∈ t, c * (k : ℝ) ^ e * (i : ℝ) ^ (-s) ≤ c * k / (s - 1) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hs1 : (0 : ℝ) < s - 1 := by linarith
  rw [← mul_sum]
  calc c * (k : ℝ) ^ e * ∑ i ∈ t, (i : ℝ) ^ (-s)
      ≤ c * (k : ℝ) ^ e * ((k : ℝ) ^ (1 - s) / (s - 1)) := by
        gcongr; exact sum_rpow_tail_le hs hk t ht
    _ = c * (k : ℝ) ^ (e + (1 - s)) / (s - 1) := by
        rw [Real.rpow_add hk0]; ring
    _ ≤ c * (k : ℝ) ^ (1 : ℝ) / (s - 1) := by
        have hke : (k : ℝ) ^ (e + (1 - s)) ≤ (k : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hk1 (by linarith)
        gcongr
    _ = c * k / (s - 1) := by rw [Real.rpow_one]

/-! ### The factors at `z = θ k^ν` -/

/-- Auxiliary: `(1 + l)^2 ≤ 4^l`. -/
theorem one_add_sq_le_four_pow (l : ℕ) : ((1 : ℝ) + l) ^ 2 ≤ 4 ^ l := by
  have h : (l : ℝ) + 1 ≤ 2 ^ l := by exact_mod_cast Nat.lt_two_pow_self
  calc ((1 : ℝ) + l) ^ 2 ≤ ((2 : ℝ) ^ l) ^ 2 := by gcongr; linarith
    _ = 4 ^ l := by rw [← pow_mul, mul_comm, pow_mul]; norm_num

/-- Auxiliary: `l^2 ≤ 2^{l+1}`. -/
theorem sq_le_two_pow_succ (l : ℕ) : ((l : ℝ)) ^ 2 ≤ 2 ^ (l + 1) := by
  have key : ∀ l : ℕ, l ^ 2 ≤ 2 ^ (l + 1) := by
    intro l
    induction l with
    | zero => norm_num
    | succ n ih =>
      rcases lt_or_ge n 3 with h | h
      · interval_cases n <;> norm_num
      · have : (n + 1) ^ 2 ≤ 2 * n ^ 2 := by nlinarith
        calc (n + 1) ^ 2 ≤ 2 * n ^ 2 := this
          _ ≤ 2 * 2 ^ (n + 1) := by omega
          _ = 2 ^ (n + 1 + 1) := by ring
  exact_mod_cast key l

/-- Auxiliary: `(l!)^ν ≥ 1` for `ν ≥ 0`. -/
theorem factorial_rpow_ge_one {ν : ℝ} (hν : 0 ≤ ν) (l : ℕ) : 1 ≤ ((l ! : ℕ) : ℝ) ^ ν :=
  Real.one_le_rpow (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero l)) hν

/-- The factors with `i ≤ k` (main TeX lines 3013-3022), for every partial sum:
if the terms of a factor are `1`, `A + Q` and `P^l(1+ly)^2/(l!)^ν` (`l ≥ 2`)
with `A ≤ 4P` and `0 ≤ y ≤ 1`, then each partial sum is at most
`S_ν(4P) + Q ≤ exp(ν(4P)^{1/ν} + Q)`. -/
theorem factor_small {ν P A Q y z : ℝ} (hν : 1 ≤ ν) (c : ℕ → ℝ) (hP : 0 ≤ P)
    (hA4 : A ≤ 4 * P) (hQ : 0 ≤ Q) (hy : 0 ≤ y) (hy1 : y ≤ 1)
    (h0 : c 0 = 1) (h1 : c 1 * z = A + Q)
    (h2 : ∀ l, 2 ≤ l → c l * z ^ l = P ^ l * (1 + l * y) ^ 2 / ((l ! : ℕ) : ℝ) ^ ν)
    (N : ℕ) :
    ∑ l ∈ range N, c l * z ^ l ≤ Real.exp (ν * (4 * P) ^ (1 / ν) + Q) := by
  have hterm : ∀ l ∈ range N, c l * z ^ l ≤
      (4 * P) ^ l / ((l ! : ℕ) : ℝ) ^ ν + (if l = 1 then Q else 0) := by
    intro l _
    rcases Nat.lt_or_ge l 2 with hl | hl
    · interval_cases l
      · simp [h0]
      · simp [h1]; linarith
    · have hl1 : ¬ l = 1 := by omega
      rw [h2 l hl]
      simp only [hl1, ↓reduceIte, add_zero]
      have hfac : 0 < ((l ! : ℕ) : ℝ) ^ ν := Real.rpow_pos_of_pos (by positivity) _
      gcongr
      calc P ^ l * (1 + l * y) ^ 2 ≤ P ^ l * 4 ^ l := by
            gcongr
            calc (1 + l * y) ^ 2 ≤ ((1 : ℝ) + l) ^ 2 := by
                  gcongr; nlinarith [(Nat.cast_nonneg l : (0:ℝ) ≤ l)]
              _ ≤ 4 ^ l := one_add_sq_le_four_pow l
        _ = (4 * P) ^ l := by rw [mul_pow]; ring
  refine (sum_le_sum hterm).trans ?_
  rw [sum_add_distrib]
  have hS : ∑ l ∈ range N, (4 * P) ^ l / ((l ! : ℕ) : ℝ) ^ ν ≤
      Real.exp (ν * (4 * P) ^ (1 / ν)) := by
    obtain ⟨hs, hb⟩ := SeriesType.seriesNu_summable_le hν (by positivity : 0 ≤ 4 * P)
    exact (hs.sum_le_tsum _ fun l _ => by positivity).trans hb
  have hQs : ∑ l ∈ range N, (if l = 1 then Q else 0) ≤ Q := by
    rw [sum_ite_eq']; split_ifs <;> linarith
  have he : 1 ≤ Real.exp (ν * (4 * P) ^ (1 / ν)) := Real.one_le_exp (by positivity)
  calc _ ≤ Real.exp (ν * (4 * P) ^ (1 / ν)) + Q := add_le_add hS hQs
    _ ≤ Real.exp (ν * (4 * P) ^ (1 / ν)) * (1 + Q) := by nlinarith
    _ ≤ Real.exp (ν * (4 * P) ^ (1 / ν)) * Real.exp Q := by
        gcongr; linarith [Real.add_one_le_exp Q]
    _ = _ := (Real.exp_add _ _).symm

/-- The factors with `i > k` (main TeX lines 3024-3036), for every partial sum:
if the terms are `1`, `A + Q` and `P^l(1+ly)^2/(l!)^ν` (`l ≥ 2`) with
`0 ≤ P ≤ 1/4` and `y ≥ 0`, then each partial sum is at most
`exp(A + Q + 128 P^2(1+y^2))`. This contains the TeX's uniform bound
`∑_{l≥2} P^l(1+ly)^2/(l!)^ν ≤ C P^2(1+y^2)`, here with `C = 128`. -/
theorem factor_large {ν P A Q y z : ℝ} (hν : 0 ≤ ν) (c : ℕ → ℝ) (hP : 0 ≤ P)
    (hP4 : P ≤ 1 / 4) (hA : 0 ≤ A) (hQ : 0 ≤ Q) (hy : 0 ≤ y)
    (h0 : c 0 = 1) (h1 : c 1 * z = A + Q)
    (h2 : ∀ l, 2 ≤ l → c l * z ^ l = P ^ l * (1 + l * y) ^ 2 / ((l ! : ℕ) : ℝ) ^ ν)
    (N : ℕ) :
    ∑ l ∈ range N, c l * z ^ l ≤ Real.exp (A + Q + 128 * (P ^ 2 * (1 + y ^ 2))) := by
  set W := P ^ 2 * (1 + y ^ 2) with hW
  have hW0 : 0 ≤ W := by positivity
  have hterm : ∀ l ∈ range N, c l * z ^ l ≤
      ((if l = 0 then 1 else 0) + (if l = 1 then A + Q else 0)) + 64 * W * (1 / 2) ^ l := by
    intro l _
    rcases Nat.lt_or_ge l 2 with hl | hl
    · interval_cases l
      · simp [h0]; positivity
      · simp [h1]; positivity
    · have hl0 : ¬ l = 0 := by omega
      have hl1 : ¬ l = 1 := by omega
      rw [h2 l hl]
      simp only [hl0, hl1, ↓reduceIte, add_zero, zero_add]
      have hfac := factorial_rpow_ge_one hν l
      have hl1' : (1 : ℝ) ≤ l := by exact_mod_cast (by omega : 1 ≤ l)
      have hsq : (1 + l * y) ^ 2 ≤ 2 * (l : ℝ) ^ 2 * (1 + y ^ 2) := by
        nlinarith [sq_nonneg (1 - l * y), sq_nonneg (l : ℝ), mul_nonneg hy hy]
      have h2P : (2 * P) ^ l ≤ 16 * P ^ 2 * (1 / 2) ^ l := by
        obtain ⟨m, rfl⟩ : ∃ m, l = m + 2 := ⟨l - 2, by omega⟩
        rw [pow_add, pow_add]
        have : (2 * P) ^ m ≤ (1 / 2) ^ m := by gcongr; linarith
        calc (2 * P) ^ m * (2 * P) ^ 2 ≤ (1 / 2) ^ m * (2 * P) ^ 2 := by gcongr
          _ = 16 * P ^ 2 * ((1 / 2) ^ m * (1 / 2) ^ 2) := by ring
      have hpow := sq_le_two_pow_succ l
      have hnum : P ^ l * (1 + l * y) ^ 2 ≤ 64 * W * (1 / 2) ^ l := by
        calc P ^ l * (1 + l * y) ^ 2 ≤ P ^ l * (2 * (l : ℝ) ^ 2 * (1 + y ^ 2)) := by gcongr
          _ ≤ P ^ l * (2 * 2 ^ (l + 1) * (1 + y ^ 2)) := by gcongr
          _ = 4 * (1 + y ^ 2) * (2 * P) ^ l := by rw [mul_pow, pow_succ]; ring
          _ ≤ 4 * (1 + y ^ 2) * (16 * P ^ 2 * (1 / 2) ^ l) := by gcongr
          _ = 64 * W * (1 / 2) ^ l := by rw [hW]; ring
      calc P ^ l * (1 + l * y) ^ 2 / ((l ! : ℕ) : ℝ) ^ ν ≤ P ^ l * (1 + l * y) ^ 2 :=
            div_le_self (by positivity) hfac
        _ ≤ _ := hnum
  refine (sum_le_sum hterm).trans ?_
  rw [sum_add_distrib, sum_add_distrib, ← mul_sum]
  have h0s : ∑ l ∈ range N, (if l = 0 then (1 : ℝ) else 0) ≤ 1 := by
    rw [sum_ite_eq']; split_ifs <;> norm_num
  have h1s : ∑ l ∈ range N, (if l = 1 then A + Q else 0) ≤ A + Q := by
    rw [sum_ite_eq']; split_ifs <;> linarith
  have hgs : ∑ l ∈ range N, (1 / 2 : ℝ) ^ l ≤ 2 := sum_geometric_two_le _
  have := Real.add_one_le_exp (A + Q + 128 * W)
  nlinarith

/-! ### The parameters -/

/-- The parameter facts used in the proof (main TeX lines 2809-2814 and
3003): under `0 < α₀ < 1` and `α₀ + α < 2`, `ν = 3 - α ≥ 1`, `ν ≤ β`,
`β > 2`, `p > 1` and `ν + (α - 2) = 1`. -/
theorem params {alpha alpha0 : ℝ} (h0 : 0 < alpha0) (h1 : alpha0 < 1)
    (hth : alpha0 + alpha < 2) :
    1 ≤ nuOf alpha ∧ nuOf alpha ≤ betaOf alpha alpha0 ∧ 2 < betaOf alpha alpha0 ∧
      1 < pOf alpha0 ∧ nuOf alpha + (alpha - 2) = 1 := by
  unfold nuOf betaOf pOf
  refine ⟨by linarith, by linarith, by linarith, by linarith, by ring⟩

/-! ### The proof of `L:inventory-product` -/

section Proof

variable {alpha alpha0 : ℝ}

/-- Auxiliary: the exponent `g_i` of the bound `F_i(θ k^ν) ≤ e^{g_i}`; for
`i ≤ k` it is `ν k i^{-β/ν} + Q_i`, for `i > k` it is
`θ k^ν i^{-β} + θ k^{ν-1} i^{-(β-1)} + 8 k^{2ν} i^{-2β} + 8 k^{2ν-2} i^{-(2β-2)} + Q_i`,
with `Q_i = θ k i^{-p}`, `θ = 1/4`. -/
def gExp (alpha alpha0 : ℝ) (k i : ℕ) : ℝ :=
  1 / 4 * (k : ℝ) * (i : ℝ) ^ (-pOf alpha0) +
    if i ≤ k then nuOf alpha * k * (i : ℝ) ^ (-(betaOf alpha alpha0 / nuOf alpha))
    else 1 / 4 * (k : ℝ) ^ nuOf alpha * (i : ℝ) ^ (-betaOf alpha alpha0) +
      1 / 4 * (k : ℝ) ^ (nuOf alpha - 1) * (i : ℝ) ^ (-(betaOf alpha alpha0 - 1)) +
      8 * (k : ℝ) ^ (2 * nuOf alpha) * (i : ℝ) ^ (-(2 * betaOf alpha alpha0)) +
      8 * (k : ℝ) ^ (2 * nuOf alpha - 2) * (i : ℝ) ^ (-(2 * betaOf alpha alpha0 - 2))

/-- The coefficients `1`, `v_i`, `b_{i,l}` of every factor are nonnegative
("positive product", main TeX line 3001). -/
theorem factorCoeff_nonneg (k i l : ℕ) : 0 ≤ factorCoeff alpha alpha0 k i l := by
  unfold factorCoeff vCoef bCoef
  split_ifs <;> positivity

/-- Auxiliary: every partial sum of the `i`th factor at `z = θ k^ν` is at most
`e^{g_i}` (main TeX lines 3001-3036). -/
theorem factor_partial_le (h0 : 0 < alpha0) (h1 : alpha0 < 1) (hth : alpha0 + alpha < 2)
    {k i : ℕ} (hk : 1 ≤ k) (hi : 1 ≤ i) (N : ℕ) :
    ∑ l ∈ range N, factorCoeff alpha alpha0 k i l * (1 / 4 * (k : ℝ) ^ nuOf alpha) ^ l ≤
      Real.exp (gExp alpha alpha0 k i) := by
  obtain ⟨hν, hνβ, hβ, _hp, hνα⟩ := params h0 h1 hth
  set ν := nuOf alpha with hνdef
  set β := betaOf alpha alpha0 with hβdef
  set p := pOf alpha0 with hpdef
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hi0 : (0 : ℝ) < i := by exact_mod_cast hi
  set z : ℝ := 1 / 4 * (k : ℝ) ^ ν with hz
  set P : ℝ := z * (i : ℝ) ^ (-β) with hPdef
  set A : ℝ := P + z * ((k : ℝ)⁻¹ * (i : ℝ) ^ (-(β - 1))) with hAdef
  set Q : ℝ := 1 / 4 * (k : ℝ) * (i : ℝ) ^ (-p) with hQdef
  set y : ℝ := (i : ℝ) / k with hydef
  have hP : 0 ≤ P := by positivity
  have hQ : 0 ≤ Q := by positivity
  have hy : 0 ≤ y := by positivity
  have hc0 : factorCoeff alpha alpha0 k i 0 = 1 := by simp [factorCoeff]
  have hc1 : factorCoeff alpha alpha0 k i 1 * z = A + Q := by
    have hzk : z * (k : ℝ) ^ (alpha - 2) = 1 / 4 * k := by
      rw [hz, mul_assoc, ← Real.rpow_add hk0, hνα, Real.rpow_one]
    simp only [factorCoeff, one_ne_zero, ↓reduceIte, vCoef]
    rw [hAdef, hQdef, hPdef, ← hβdef, ← hpdef, ← hzk]; ring
  have hc2 : ∀ l, 2 ≤ l → factorCoeff alpha alpha0 k i l * z ^ l =
      P ^ l * (1 + l * y) ^ 2 / ((l ! : ℕ) : ℝ) ^ ν := by
    intro l hl
    have hl0 : ¬ l = 0 := by omega
    have hl1 : ¬ l = 1 := by omega
    simp only [factorCoeff, hl0, hl1, ↓reduceIte, bCoef]
    rw [← hβdef, ← hνdef, Real.rpow_mul_natCast hi0.le, hPdef, hydef, mul_pow]
    field_simp
    rw [hz]; ring
  -- the shape of the second singleton term: `z k^{-1} i^{-(β-1)} = P (i/k)`
  have hsec : z * ((k : ℝ)⁻¹ * (i : ℝ) ^ (-(β - 1))) = P * y := by
    rw [show -(β - 1) = -β + 1 by ring, Real.rpow_add hi0, Real.rpow_one, hPdef, hydef]
    field_simp
  unfold gExp
  rw [← hνdef, ← hβdef, ← hpdef]
  split_ifs with hik
  · -- `i ≤ k`
    have hy1 : y ≤ 1 := by
      rw [hydef, div_le_one hk0]; exact_mod_cast hik
    have hA4 : A ≤ 4 * P := by
      rw [hAdef, hsec]; nlinarith
    refine (factor_small hν _ hP hA4 hQ hy hy1 hc0 hc1 hc2 N).trans_eq ?_
    congr 1
    have h4P : 4 * P = (k : ℝ) ^ ν * (i : ℝ) ^ (-β) := by rw [hPdef, hz]; ring
    have hν0 : ν ≠ 0 := by linarith
    rw [h4P, Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hk0.le,
      ← Real.rpow_mul hi0.le, mul_one_div_cancel hν0, Real.rpow_one,
      show -β * (1 / ν) = -(β / ν) by ring]
    ring
  · -- `i > k`
    have hki : k < i := by omega
    have hP4 : P ≤ 1 / 4 := by
      have hib : (i : ℝ) ^ (-β) ≤ (k : ℝ) ^ (-β) :=
        Real.rpow_le_rpow_of_nonpos hk0 (by exact_mod_cast hki.le) (by linarith)
      have hkk : (k : ℝ) ^ ν * (k : ℝ) ^ (-β) ≤ 1 := by
        rw [← Real.rpow_add hk0]
        exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hk) (by linarith)
      calc P = 1 / 4 * ((k : ℝ) ^ ν * (i : ℝ) ^ (-β)) := by rw [hPdef, hz]; ring
        _ ≤ 1 / 4 * ((k : ℝ) ^ ν * (k : ℝ) ^ (-β)) := by gcongr
        _ ≤ 1 / 4 * 1 := by gcongr
        _ = 1 / 4 := by ring
    have hA : 0 ≤ A := by positivity
    refine (factor_large (by linarith) _ hP hP4 hA hQ hy hc0 hc1 hc2 N).trans_eq ?_
    congr 1
    -- identify `A + 128 P^2 (1 + y^2)` with the four tail terms
    have e1 : z * ((k : ℝ)⁻¹ * (i : ℝ) ^ (-(β - 1))) =
        1 / 4 * (k : ℝ) ^ (ν - 1) * (i : ℝ) ^ (-(β - 1)) := by
      rw [hz, Real.rpow_sub_one hk0.ne']; ring
    have hiβ2 : ((i : ℝ) ^ (-β)) ^ 2 = (i : ℝ) ^ (-(2 * β)) := by
      rw [← Real.rpow_mul_natCast hi0.le]; ring_nf
    have hkν2 : ((k : ℝ) ^ ν) ^ 2 = (k : ℝ) ^ (2 * ν) := by
      rw [← Real.rpow_mul_natCast hk0.le]; ring_nf
    have e2 : 128 * (P ^ 2 * (1 + y ^ 2)) =
        8 * (k : ℝ) ^ (2 * ν) * (i : ℝ) ^ (-(2 * β)) +
          8 * (k : ℝ) ^ (2 * ν - 2) * (i : ℝ) ^ (-(2 * β - 2)) := by
      have hk2 : (k : ℝ) ^ (2 * ν - 2) = (k : ℝ) ^ (2 * ν) / (k : ℝ) ^ 2 := by
        rw [Real.rpow_sub hk0, Real.rpow_two]
      have hi2 : (i : ℝ) ^ (-(2 * β - 2)) = (i : ℝ) ^ (-(2 * β)) * (i : ℝ) ^ 2 := by
        rw [show -(2 * β - 2) = -(2 * β) + 2 by ring, Real.rpow_add hi0, Real.rpow_two]
      rw [hk2, hi2, hPdef, hz, hydef, mul_pow, mul_pow, hiβ2, hkν2]
      field_simp
      ring
    rw [hAdef, e1, hPdef, hz]
    rw [hPdef, hz] at e2
    linear_combination e2

/-- **The evaluated product** (main TeX lines 3001-3037): at `z = θ k^ν`,
`θ = 1/4`, every factor series converges, each factor sum is nonnegative, and
the product of the factor sums is at most `e^{K k}`, `K = expConst α α₀`
("the entire product is consequently at most `e^{Ck}`"). Hypotheses: those
of the general theorem, `0 < α₀ < 1`, `α₀ + α < 2`, `k ≥ 1`. -/
theorem inventory_product_eval_le (h0 : 0 < alpha0) (h1 : alpha0 < 1)
    (hth : alpha0 + alpha < 2) (M k : ℕ) (hk : 1 ≤ k) :
    (∀ i ∈ Icc 1 M, Summable (fun l => factorCoeff alpha alpha0 k i l *
        (1 / 4 * (k : ℝ) ^ nuOf alpha) ^ l)) ∧
      ∏ i ∈ Icc 1 M, factorEval alpha alpha0 k i (1 / 4 * (k : ℝ) ^ nuOf alpha) ≤
        Real.exp (expConst alpha alpha0 * k) := by
  obtain ⟨hν, hνβ, hβ, hp, _⟩ := params h0 h1 hth
  set ν := nuOf alpha with hνdef
  set β := betaOf alpha alpha0 with hβdef
  set p := pOf alpha0 with hpdef
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  set z : ℝ := 1 / 4 * (k : ℝ) ^ ν with hz
  have hz0 : 0 ≤ z := by positivity
  have hnn : ∀ i l, 0 ≤ factorCoeff alpha alpha0 k i l * z ^ l := fun i l =>
    mul_nonneg (factorCoeff_nonneg k i l) (pow_nonneg hz0 _)
  have hfac : ∀ i ∈ Icc 1 M, Summable (fun l => factorCoeff alpha alpha0 k i l * z ^ l) ∧
      factorEval alpha alpha0 k i z ≤ Real.exp (gExp alpha alpha0 k i) := by
    intro i hi
    have hi1 : 1 ≤ i := (mem_Icc.mp hi).1
    exact ⟨summable_of_sum_range_le (hnn i) (factor_partial_le h0 h1 hth hk hi1),
      Real.tsum_le_of_sum_range_le (hnn i) (factor_partial_le h0 h1 hth hk hi1)⟩
  refine ⟨fun i hi => (hfac i hi).1, ?_⟩
  -- the sum of the exponents
  have hsum : ∑ i ∈ Icc 1 M, gExp alpha alpha0 k i ≤ expConst alpha alpha0 * k := by
    unfold gExp
    rw [← hνdef, ← hβdef, ← hpdef, sum_add_distrib, sum_ite]
    have hpos : ∀ i ∈ Icc 1 M, 1 ≤ i := fun i hi => (mem_Icc.mp hi).1
    have hQ : ∑ i ∈ Icc 1 M, 1 / 4 * (k : ℝ) * (i : ℝ) ^ (-p) ≤ 1 / 4 * k * (p / (p - 1)) := by
      rw [← mul_sum]; gcongr; exact sum_rpow_pos_le hp _ hpos
    have hr : 1 < β / ν := by
      rw [one_lt_div (by linarith)]
      have : nuOf alpha < betaOf alpha alpha0 := by unfold nuOf betaOf; linarith
      exact this
    have hX : ∑ i ∈ (Icc 1 M).filter (fun i => i ≤ k), ν * k * (i : ℝ) ^ (-(β / ν)) ≤
        ν * k * ((β / ν) / (β / ν - 1)) := by
      rw [← mul_sum]
      exact mul_le_mul_of_nonneg_left
        (sum_rpow_pos_le hr _ fun i hi => hpos i (mem_filter.mp hi).1) (by positivity)
    have htail : ∀ i ∈ (Icc 1 M).filter (fun i => ¬ i ≤ k), k < i := fun i hi => by
      have := (mem_filter.mp hi).2; omega
    have hY := tail_scaled_le (s := β) (e := ν) (c := 1 / 4) (by linarith) hνβ (by norm_num)
      hk _ htail
    have hY2 := tail_scaled_le (s := β - 1) (e := ν - 1) (c := 1 / 4) (by linarith)
      (by linarith) (by norm_num) hk _ htail
    have hY3 := tail_scaled_le (s := 2 * β) (e := 2 * ν) (c := 8) (by linarith)
      (by linarith) (by norm_num) hk _ htail
    have hY4 := tail_scaled_le (s := 2 * β - 2) (e := 2 * ν - 2) (c := 8) (by linarith)
      (by linarith) (by norm_num) hk _ htail
    rw [sum_add_distrib, sum_add_distrib, sum_add_distrib]
    have hE : expConst alpha alpha0 * k =
        1 / 4 * k * (p / (p - 1)) + ν * k * ((β / ν) / (β / ν - 1)) +
          1 / 4 * k / (β - 1) + 1 / 4 * k / (β - 1 - 1) + 8 * k / (2 * β - 1) +
          8 * k / (2 * β - 2 - 1) := by
      unfold expConst; rw [← hνdef, ← hβdef, ← hpdef]; ring
    rw [hE]
    linarith
  calc ∏ i ∈ Icc 1 M, factorEval alpha alpha0 k i z
      ≤ ∏ i ∈ Icc 1 M, Real.exp (gExp alpha alpha0 k i) :=
        Finset.prod_le_prod₀ (fun i _ => tsum_nonneg (hnn i)) fun i hi => (hfac i hi).2
    _ = Real.exp (∑ i ∈ Icc 1 M, gExp alpha alpha0 k i) := (Real.exp_sum _ _).symm
    _ ≤ Real.exp (expConst alpha alpha0 * k) := Real.exp_le_exp.mpr hsum

/-- **`L:inventory-product`, general form** (main TeX lines 2986-2998, proof
3000-3040): for `0 < α₀ < 1`, `α₀ + α < 2`, every `M` and every `k ≥ 1`,
`[z^k] ∏_{i=1}^M (1 + v_i z + ∑_{l≥2} b_{i,l} z^l) ≤ C^k/(k!)^ν` with
`C = inventoryConst α α₀ = 4 e^{K(α,α₀)}`, which depends on `(α, α₀)` only.
Proof as in the TeX (evaluation at `z = k^ν/4`, `k^{-νk} ≤ (k!)^{-ν}`), with
the route differences listed in the module doc comment. -/
theorem inventory_product (h0 : 0 < alpha0) (h1 : alpha0 < 1) (hth : alpha0 + alpha < 2)
    (M k : ℕ) (hk : 1 ≤ k) :
    coeff k (inventoryProduct alpha alpha0 M k) ≤
      inventoryConst alpha alpha0 ^ k / ((k ! : ℕ) : ℝ) ^ nuOf alpha := by
  obtain ⟨hν, -, -, -, -⟩ := params h0 h1 hth
  obtain ⟨hs, hprod⟩ := inventory_product_eval_le h0 h1 hth M k hk
  set ν := nuOf alpha with hνdef
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  set z : ℝ := 1 / 4 * (k : ℝ) ^ ν with hz
  have hzpos : 0 < z := by positivity
  have hcoef : ∀ i ∈ Icc 1 M, ∀ n, 0 ≤ coeff n (factorSeries alpha alpha0 k i) := by
    intro i _ n; rw [factorSeries, coeff_mk]; exact factorCoeff_nonneg k i n
  have hs' : ∀ i ∈ Icc 1 M, Summable
      (fun n => coeff n (factorSeries alpha alpha0 k i) * z ^ n) := by
    intro i hi; simpa only [factorSeries, coeff_mk] using hs i hi
  have hbound := coeff_prod_le_prod_tsum (Icc 1 M) (factorSeries alpha alpha0 k) hcoef hzpos
    hs' k
  have hev : ∏ i ∈ Icc 1 M, ∑' n, coeff n (factorSeries alpha alpha0 k i) * z ^ n =
      ∏ i ∈ Icc 1 M, factorEval alpha alpha0 k i z := by
    refine prod_congr rfl fun i _ => ?_
    simp [factorEval, factorSeries, coeff_mk]
  rw [hev] at hbound
  unfold inventoryProduct
  refine hbound.trans ?_
  have hfk : ((k ! : ℕ) : ℝ) ^ ν ≤ ((k : ℝ) ^ ν) ^ k := by
    rw [← Real.rpow_mul_natCast hk0.le, mul_comm, Real.rpow_natCast_mul hk0.le]
    have : ((k ! : ℕ) : ℝ) ≤ (k : ℝ) ^ k := by exact_mod_cast Nat.factorial_le_pow k
    exact Real.rpow_le_rpow (by positivity) this (by linarith)
  have hfpos : 0 < ((k ! : ℕ) : ℝ) ^ ν := Real.rpow_pos_of_pos (by positivity) _
  rw [div_le_div_iff₀ (pow_pos hzpos k) hfpos]
  have hC : inventoryConst alpha alpha0 ^ k * z ^ k = Real.exp (expConst alpha alpha0 * k) *
      ((k : ℝ) ^ ν) ^ k := by
    rw [inventoryConst, hz, ← mul_pow,
      show 4 * Real.exp (expConst alpha alpha0) * (1 / 4 * (k : ℝ) ^ ν) =
        Real.exp (expConst alpha alpha0) * (k : ℝ) ^ ν by ring,
      mul_pow, ← Real.exp_nat_mul, mul_comm (k : ℝ)]
  rw [hC]
  calc (∏ i ∈ Icc 1 M, factorEval alpha alpha0 k i z) * ((k ! : ℕ) : ℝ) ^ ν
      ≤ Real.exp (expConst alpha alpha0 * k) * ((k : ℝ) ^ ν) ^ k :=
        mul_le_mul hprod hfk hfpos.le (Real.exp_pos _).le

/-- **`L:inventory-product` with the manuscript's hypotheses** (main TeX lines
2986-2998, proof 3000-3040): under `H:homog` (lines 225-242, the standing
hypothesis of section `S:interval-upper`, with `ν = 3 - α`,
`β = 4 - α - α₀`, `p = 2 - α₀` as at lines 2809-2812), the finite constant
`C = inventoryConst α α₀ > 0`, a function of `(α, α₀)` alone, satisfies
`[z^k] ∏_{i=1}^M (1 + v_i z + ∑_{l≥2} b_{i,l} z^l) ≤ C^k/(k!)^ν` for every
`M` and every `k ≥ 1`. Of `H:homog` only `0 < α₀ < 1` and `α₀ + α < 2` are
used. -/
theorem inventory_product_paper {d : ℕ} {Γ μ : MeasureTheory.Measure (HomogHypothesis.Rd d)}
    (h : HomogHypothesis.HomogCovariance d alpha alpha0 Γ μ) :
    0 < inventoryConst alpha alpha0 ∧
      ∀ M k : ℕ, 1 ≤ k →
        coeff k (inventoryProduct alpha alpha0 M k) ≤
          inventoryConst alpha alpha0 ^ k / ((k ! : ℕ) : ℝ) ^ nuOf alpha :=
  ⟨inventoryConst_pos alpha alpha0, fun M k hk =>
    inventory_product h.alpha0_pos h.alpha0_lt_one h.threshold M k hk⟩

end Proof

end StratonovichHAMSecondMoment.InventoryProduct
