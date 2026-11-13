/-
Copyright 2026 Le Chen. SPDX-License-Identifier: Apache-2.0

Lemma `L:gram-scalar-algebra` of `notes/integrated_positive_gram.tex`
(manuscript revision ba01d98): the scalar square-root duality, the Hilbert
completed-square identity and inequality, and the finite Gram identity with
`C_ij = ⟪k_i, k_j⟫` (the section's defining line).

The manuscript works in a real Hilbert space. Completeness is not used, so the
statements are made for any real inner product space; this is a weakening of
the hypotheses, not a strengthening. The section's standing assumptions
`C_ij ≥ 0`, `ℓ_i > 0`, `b_i ≥ 0` are not used by the lemma and are omitted.
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false

open scoped BigOperators

universe u v

namespace StratonovichHAMSecondMoment.GramScalarAlgebra

/-- `E:gram-sqrt-dual`: for real `ℓ`, `w > 0` and `t ≥ 0`,
`2 ℓ √t ≤ ℓ² / w + w t`. -/
theorem sqrt_dual (ell w t : ℝ) (hw : 0 < w) (ht : 0 ≤ t) :
    2 * ell * Real.sqrt t ≤ ell ^ 2 / w + w * t := by
  have hs : w * t * w = (w * Real.sqrt t) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt ht]; ring
  rw [div_add' _ _ _ hw.ne', le_div_iff₀ hw, hs]
  nlinarith [sq_nonneg (ell - w * Real.sqrt t)]

/-- The identity half of `E:gram-hilbert-square`:
`⟪Φ, z⟫ - ‖Φ‖²/2 = ‖z‖²/2 - ‖Φ - z‖²/2`. -/
theorem hilbert_square_eq {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (Φ z : H) :
    inner ℝ Φ z - ‖Φ‖ ^ 2 / 2 = ‖z‖ ^ 2 / 2 - ‖Φ - z‖ ^ 2 / 2 := by
  rw [norm_sub_sq_real]
  ring

/-- The inequality half of `E:gram-hilbert-square`:
`⟪Φ, z⟫ - ‖Φ‖²/2 ≤ ‖z‖²/2`. -/
theorem hilbert_square_le {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (Φ z : H) :
    inner ℝ Φ z - ‖Φ‖ ^ 2 / 2 ≤ ‖z‖ ^ 2 / 2 := by
  rw [hilbert_square_eq]
  nlinarith [sq_nonneg ‖Φ - z‖]

/-- `E:gram-hilbert-square` in full: the identity and the inequality. -/
theorem hilbert_square {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (Φ z : H) :
    inner ℝ Φ z - ‖Φ‖ ^ 2 / 2 = ‖z‖ ^ 2 / 2 - ‖Φ - z‖ ^ 2 / 2 ∧
      ‖z‖ ^ 2 / 2 - ‖Φ - z‖ ^ 2 / 2 ≤ ‖z‖ ^ 2 / 2 := by
  refine ⟨hilbert_square_eq Φ z, ?_⟩
  nlinarith [sq_nonneg ‖Φ - z‖]

/-- The finite Gram identity: with `C i j = ⟪k i, k j⟫` (the section's
definition `C_{ij} = \langle k_i,k_j\rangle`), for a finite index set and real
weights, `‖∑ w_i k_i‖² = ∑_{i,j} w_i C_ij w_j`. -/
theorem gram_identity {ι : Type u} {H : Type v} [Fintype ι]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (k : ι → H) (C : ι → ι → ℝ) (hC : ∀ i j, C i j = inner ℝ (k i) (k j))
    (w : ι → ℝ) :
    ‖∑ i, w i • k i‖ ^ 2 = ∑ i, ∑ j, w i * C i j * w j := by
  rw [← real_inner_self_eq_norm_sq]
  simp only [sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right, hC]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [real_inner_comm (k i) (k j)]
  ring

/-- `L:gram-scalar-algebra` with the section's own standing hypotheses: a real
Hilbert space (`CompleteSpace H`) and a Gram matrix `C_ij = ⟪k_i, k_j⟫` with
`C_ij ≥ 0` for every pair. These hypotheses are not needed by the proof (see
`sqrt_dual`, `hilbert_square`, `gram_identity`, which hold more generally);
this wrapper states the lemma exactly as the manuscript does. -/
theorem gram_scalar_algebra_paper {ι : Type u} {H : Type v} [Fintype ι]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (k : ι → H) (C : ι → ι → ℝ) (hC : ∀ i j, C i j = inner ℝ (k i) (k j))
    (_hCnn : ∀ i j, 0 ≤ C i j) :
    (∀ ell w t : ℝ, 0 < w → 0 ≤ t → 2 * ell * Real.sqrt t ≤ ell ^ 2 / w + w * t) ∧
      (∀ Φ z : H, inner ℝ Φ z - ‖Φ‖ ^ 2 / 2 = ‖z‖ ^ 2 / 2 - ‖Φ - z‖ ^ 2 / 2 ∧
        ‖z‖ ^ 2 / 2 - ‖Φ - z‖ ^ 2 / 2 ≤ ‖z‖ ^ 2 / 2) ∧
      (∀ w : ι → ℝ, ‖∑ i, w i • k i‖ ^ 2 = ∑ i, ∑ j, w i * C i j * w j) :=
  ⟨fun ell w t hw ht => sqrt_dual ell w t hw ht, fun Φ z => hilbert_square Φ z,
    fun w => gram_identity k C hC w⟩

end StratonovichHAMSecondMoment.GramScalarAlgebra
