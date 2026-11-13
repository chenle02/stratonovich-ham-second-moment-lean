module

/-
Copyright 2026 Le Chen. SPDX-License-Identifier: Apache-2.0

Integration of wave items L7-a (`InventoryProduct`) and L7-f (`IntervalScalar`)
for `notes/notes_stratonovich_ham_second_moment.tex` (main TeX file; line
numbers at revision a284420).  This module discharges the
`L:inventory-product` input of the `IntervalScalar` step rows of
`P:interval-coefficients` (statement lines 3402-3414, proof 3416-3581).

`IntervalScalar` takes `L:inventory-product` (`E:inventory-product`, lines
2986-2997) as the hypothesis `IntervalScalar.InventoryProduct α α₀ C`, with the
product written over `j : Fin M` at `i = j + 1` and the exponent `3 - α`.
`InventoryProduct` proves the same statement IN FULL with the product over
`i ∈ Finset.Icc 1 M`, the exponent `TypeContinuity.nuOf α = 3 - α` and the
explicit constant `InventoryProduct.inventoryConst α α₀`.

* `invV_eq`, `invB_eq`, `invCoeff_eq` (auxiliary bridge): the coefficient
  functions of the two modules are equal (`invV = vCoef`, `invB = bCoef`,
  `invCoeff = factorCoeff`); they differ only in writing `β`, `ν`, `p`
  through `TypeContinuity.betaOf`, `nuOf` and `InventoryProduct.pOf`.
  `prod_fin_eq_inventoryProduct` (auxiliary bridge): the `Fin M` product
  equals `InventoryProduct.inventoryProduct`.
* `inventoryProduct_holds`: under `0 < α₀ < 1` and `α₀ + α < 2` (the
  hypotheses of `InventoryProduct.inventory_product`),
  `IntervalScalar.InventoryProduct α α₀ (inventoryConst α α₀)`;
  `inventoryProduct_holds_paper`: the same under `H:homog`
  (`HomogHypothesis.HomogCovariance`, lines 225-242).
* `interval_coefficient_assembly_completed` and
  `interval_coefficient_assembly_paper_completed`: the two `IntervalScalar`
  theorems that take the input (`interval_coefficient_assembly`,
  `interval_coefficient_assembly_paper`) re-issued without `hinv`, with
  `C_inv = inventoryConst α α₀`; every other hypothesis is kept exactly.  The
  other two inputs of these step rows (`hsplits`: `E:interval-energy-splits`
  with the reflection parity; `hfixed`: `L:fixed-split`) remain supplied, and
  every narrowing recorded in `IntervalScalar` (`R_α > 0`, `σ_i > 0`, the
  zero-noise case and sign reduction not covered) is unchanged.

No other `IntervalScalar` theorem takes the `InventoryProduct` input.  The
existing modules are not modified.
-/
public import Mathlib
public import StratonovichHAMSecondMoment.IntervalScalar
public import StratonovichHAMSecondMoment.InventoryProduct

@[expose] public section

noncomputable section

set_option autoImplicit false

open Real Finset MeasureTheory
open scoped Nat

namespace StratonovichHAMSecondMoment.IntervalScalarCompleted

open StratonovichHAMSecondMoment.IntervalScalar StratonovichHAMSecondMoment.TypeContinuity

/-- Auxiliary bridge: `IntervalScalar.invV = InventoryProduct.vCoef` (both are
`v_i` of `L:inventory-product`, main TeX lines 2989-2990). -/
theorem invV_eq (alpha alpha0 : ℝ) (k i : ℕ) :
    invV alpha alpha0 k i = InventoryProduct.vCoef alpha alpha0 k i := by
  simp only [invV, InventoryProduct.vCoef, betaOf, InventoryProduct.pOf]

/-- Auxiliary bridge: `IntervalScalar.invB = InventoryProduct.bCoef` (both are
`b_{i,l}` of `L:inventory-product`, main TeX line 2991). -/
theorem invB_eq (alpha alpha0 : ℝ) (k i l : ℕ) :
    invB alpha alpha0 k i l = InventoryProduct.bCoef alpha alpha0 k i l := by
  simp only [invB, InventoryProduct.bCoef, betaOf, nuOf, neg_mul]

/-- Auxiliary bridge: `IntervalScalar.invCoeff = InventoryProduct.factorCoeff`
(the coefficients of `1 + v_i z + ∑_{l≥2} b_{i,l} z^l`, main TeX lines
2994-2997). -/
theorem invCoeff_eq (alpha alpha0 : ℝ) (k i l : ℕ) :
    invCoeff alpha alpha0 k i l = InventoryProduct.factorCoeff alpha alpha0 k i l := by
  simp only [invCoeff, InventoryProduct.factorCoeff, invV_eq, invB_eq]

/-- Auxiliary bridge: the product over `j : Fin M` at `i = j + 1` used in
`IntervalScalar.InventoryProduct` is `InventoryProduct.inventoryProduct`, the
product over `i ∈ Icc 1 M` (main TeX lines 2994-2997). -/
theorem prod_fin_eq_inventoryProduct (alpha alpha0 : ℝ) (M k : ℕ) :
    ∏ j : Fin M, PowerSeries.mk (invCoeff alpha alpha0 k ((j : ℕ) + 1)) =
      InventoryProduct.inventoryProduct alpha alpha0 M k := by
  have hfun : ∀ i : ℕ, PowerSeries.mk (invCoeff alpha alpha0 k i) =
      InventoryProduct.factorSeries alpha alpha0 k i := by
    intro i
    simp only [InventoryProduct.factorSeries]
    congr 1
    funext l
    exact invCoeff_eq alpha alpha0 k i l
  rw [InventoryProduct.inventoryProduct, Fin.prod_univ_eq_prod_range
    (fun j => PowerSeries.mk (invCoeff alpha alpha0 k (j + 1))) M,
    ← Finset.Ico_add_one_right_eq_Icc, Finset.prod_Ico_eq_prod_range, Nat.add_sub_cancel]
  refine prod_congr rfl fun j _ => ?_
  rw [hfun, add_comm]

/-- **`L:inventory-product` discharges the `IntervalScalar` input** (main TeX
lines 2986-2997): under `0 < α₀ < 1` and `α₀ + α < 2`, the hypotheses of
`InventoryProduct.inventory_product`, the statement
`IntervalScalar.InventoryProduct α α₀ C` holds with
`C = InventoryProduct.inventoryConst α α₀ = 4 e^{K(α,α₀)}`, a function of
`(α, α₀)` only. -/
theorem inventoryProduct_holds {alpha alpha0 : ℝ} (h0 : 0 < alpha0) (h1 : alpha0 < 1)
    (hth : alpha0 + alpha < 2) :
    IntervalScalar.InventoryProduct alpha alpha0
      (InventoryProduct.inventoryConst alpha alpha0) := by
  intro M k hk
  rw [prod_fin_eq_inventoryProduct]
  have := InventoryProduct.inventory_product h0 h1 hth M k hk
  simpa only [nuOf, Nat.cast_id] using this

/-- **`L:inventory-product` under `H:homog` discharges the `IntervalScalar`
input** (main TeX lines 2986-2997; `H:homog`, lines 225-242, is the standing
hypothesis of section `S:interval-upper`): from
`InventoryProduct.inventory_product_paper`, the constant
`InventoryProduct.inventoryConst α α₀` is positive and satisfies
`IntervalScalar.InventoryProduct α α₀`.  Of `H:homog` only `0 < α₀ < 1` and
`α₀ + α < 2` are used. -/
theorem inventoryProduct_holds_paper {d : ℕ} {alpha alpha0 : ℝ}
    {Γ μ : Measure (HomogHypothesis.Rd d)}
    (hH : HomogHypothesis.HomogCovariance d alpha alpha0 Γ μ) :
    0 < InventoryProduct.inventoryConst alpha alpha0 ∧
      IntervalScalar.InventoryProduct alpha alpha0
        (InventoryProduct.inventoryConst alpha alpha0) :=
  ⟨(InventoryProduct.inventory_product_paper hH).1,
    inventoryProduct_holds hH.alpha0_pos hH.alpha0_lt_one hH.threshold⟩

/-- **Step row of `P:interval-coefficients`, `E:interval-coefficient-bound`**
(main TeX lines 3405-3408, proof 3478-3547) at `L ≥ 1`, general form, with the
`L:inventory-product` input (main TeX lines 2986-2997) discharged:
`IntervalScalar.interval_coefficient_assembly` without `hinv`, with
`C_inv = InventoryProduct.inventoryConst α α₀` (by `inventoryProduct_holds`).
Every other hypothesis is exactly that of
`IntervalScalar.interval_coefficient_assembly`; the inputs `hsplits`
(`E:interval-energy-splits` with the reflection parity, lines 3478-3485) and
`hfixed` (`L:fixed-split`, lines 3080-3091, at `λ = k/T` with constant
`C_split`) remain supplied.  Conclusion:
`|coef| ≤ (12 c L^β C_split C_inv)^k R^k T^{βk}/(k!)^ν V`. -/
theorem interval_coefficient_assembly_completed {alpha alpha0 R T L c Cs V coef : ℝ}
    {M k : ℕ} (h σ : Fin M → ℝ) (Q : (Fin M → ℕ × ℕ) → ℝ)
    (hα2 : alpha < 2) (ha0 : 0 < alpha0) (ha01 : alpha0 < 1) (hsum : alpha + alpha0 < 2)
    (hk : 1 ≤ k) (hT : 0 < T) (hL : 1 ≤ L) (hc : 0 ≤ c) (hR : 0 ≤ R) (hV : 0 ≤ V) (hCs : 0 ≤ Cs)
    (hh : ∀ i, 0 < h i) (hlen : ∀ i : Fin M, h i ≤ L * T / ((i : ℕ) + 1 : ℕ))
    (hσ : ∀ i, σ i ^ 2 ≤ c * h i ^ (-alpha0))
    (hsplits : coef = ∑ κ ∈ (univ : Finset (Fin M)).finsuppAntidiag k,
      ∑ p ∈ Fintype.piFinset (fun i => antidiagonal (2 * κ i)), Q p)
    (hfixed : ∀ κ ∈ (univ : Finset (Fin M)).finsuppAntidiag k,
      ∀ p ∈ Fintype.piFinset (fun i => antidiagonal (2 * κ i)),
        |Q p| ≤ (k : ℝ) ^ 2 * Cs ^ k * R ^ k * V *
          ∏ i, splitFactor alpha (σ i) (h i) (k / T) (κ i) (p i)) :
    |coef| ≤ (12 * c * L ^ (4 - alpha - alpha0) * Cs *
        InventoryProduct.inventoryConst alpha alpha0) ^ k * R ^ k *
      T ^ ((4 - alpha - alpha0) * k) / (k ! : ℝ) ^ (3 - alpha) * V :=
  interval_coefficient_assembly h σ Q hα2 ha0 ha01 hsum hk hT hL hc hR hV hCs hh hlen hσ
    (inventoryProduct_holds ha0 ha01 (by linarith)) hsplits hfixed

/-- **Step row of `P:interval-coefficients`, `E:interval-coefficient-bound`**
(main TeX lines 3405-3408; proof 3416-3420 and 3478-3547) under `H:homog`,
with the `L:inventory-product` input (main TeX lines 2986-2997) discharged:
`IntervalScalar.interval_coefficient_assembly_paper` without `hinv`, with
`C_inv = InventoryProduct.inventoryConst α α₀` (by
`inventoryProduct_holds_paper`).  Every other hypothesis is exactly that of
`IntervalScalar.interval_coefficient_assembly_paper`, including the carried
`_hRpos`, `_hσpos` (unused by the proof); the inputs `hsplits` and `hfixed`
remain supplied.  The constant
`C = 12 max(c,0) max(1,L)^β C_split C_inv` depends only on `α, α₀, L, c` and
`C_split`.  Narrower than the TeX exactly as the original wrapper: `R_α > 0`
and `σ_i > 0` are assumed; the zero-noise case and the sign reduction (lines
3417, 3420-3423) are not formalized. -/
theorem interval_coefficient_assembly_paper_completed {d : ℕ} {alpha alpha0 : ℝ}
    {Γ μ : Measure (HomogHypothesis.Rd d)}
    (hH : HomogHypothesis.HomogCovariance d alpha alpha0 Γ μ)
    {R T L c Cs V coef : ℝ} {M k : ℕ}
    (h σ : Fin M → ℝ) (Q : (Fin M → ℕ × ℕ) → ℝ)
    (hRdef : R = alpha * π * (μ (Metric.ball 0 1)).toReal / (2 * Real.sin (π * alpha / 2)))
    (_hRpos : 0 < R) (hk : 1 ≤ k) (hT : 0 < T) (hV : 0 ≤ V) (hCs : 0 ≤ Cs)
    (hh : ∀ i, 0 < h i) (_hσpos : ∀ i, 0 < σ i)
    (hlen : ∀ i : Fin M, h i ≤ L * T / ((i : ℕ) + 1 : ℕ))
    (hσ : ∀ i, σ i ^ 2 ≤ c * h i ^ (-alpha0))
    (hsplits : coef = ∑ κ ∈ (univ : Finset (Fin M)).finsuppAntidiag k,
      ∑ p ∈ Fintype.piFinset (fun i => antidiagonal (2 * κ i)), Q p)
    (hfixed : ∀ κ ∈ (univ : Finset (Fin M)).finsuppAntidiag k,
      ∀ p ∈ Fintype.piFinset (fun i => antidiagonal (2 * κ i)),
        |Q p| ≤ (k : ℝ) ^ 2 * Cs ^ k * R ^ k * V *
          ∏ i, splitFactor alpha (σ i) (h i) (k / T) (κ i) (p i)) :
    |coef| ≤ (12 * max c 0 * max 1 L ^ (4 - alpha - alpha0) * Cs *
        InventoryProduct.inventoryConst alpha alpha0) ^ k * R ^ k *
      T ^ ((4 - alpha - alpha0) * k) / (k ! : ℝ) ^ (3 - alpha) * V :=
  interval_coefficient_assembly_paper hH h σ Q hRdef _hRpos hk hT hV hCs hh _hσpos hlen hσ
    (inventoryProduct_holds_paper hH).2 hsplits hfixed

end StratonovichHAMSecondMoment.IntervalScalarCompleted
