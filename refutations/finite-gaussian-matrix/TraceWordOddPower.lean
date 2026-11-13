import StratonovichHAMSecondMoment.FiniteGaussianMatrix

/-!
Refutation for `StratonovichHAMSecondMoment.FiniteGaussianMatrix.trace_word_le`
(manuscript `L:gaussian-trace-bounds`, display `E:gaussian-trace-word`): the
trace-word bound with `Y^L` in place of `|Y|^L` needs `L` even (the manuscript
has `L = 2m-2`); `|Y|` cannot be replaced by `Y` for odd `L`.

The wrong variant is the core bound with the hypothesis `Even L` removed.
Counterexample: `B = [[0,1],[1,0]]`, `Y = diag(-2, 1)`, `L = 3`, `q = 1`:
`Tr(B Y B Y^2) = 2` but `Tr(B^2 Y^3) = -8 + 1 = -7`.
The contrast theorem applies the package theorem at the same `B`, `Y` with the
even exponent `L = 2` and records that `L = 3` violates only evenness.
No junk value is involved.

Expected outcome: compiles (refuted).
-/

set_option autoImplicit false

namespace Refutations.FiniteGaussianMatrix

open Matrix

/-- The counterexample `B`. -/
def Bc : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

/-- The counterexample `Y`. -/
def Yc : Matrix (Fin 2) (Fin 2) ℂ := !![-2, 0; 0, 1]

theorem Bc_isHermitian : Bc.IsHermitian := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Bc]

theorem Yc_isHermitian : Yc.IsHermitian := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Yc]

/-- The trace-word bound with `Y^L` and odd `L` is false. -/
theorem trace_word_le_drop_even :
    ¬ (∀ (B Y : Matrix (Fin 2) (Fin 2) ℂ), B.IsHermitian → Y.IsHermitian →
      ∀ L q : ℕ, q ≤ L →
        (trace (B * Y ^ q * B * Y ^ (L - q))).re ≤ (trace (B ^ 2 * Y ^ L)).re) := by
  intro h
  have := h Bc Yc Bc_isHermitian Yc_isHermitian 3 1 (by norm_num)
  simp [Bc, Yc, pow_succ, Matrix.trace_fin_two] at this
  norm_num at this

/-- Contrast: `L = 3` violates only evenness; at the same `B`, `Y` the package
theorem holds for the even exponent `L = 2`. -/
theorem trace_word_le_drop_even_contrast :
    ¬ Even 3 ∧ ∀ q : ℕ, q ≤ 2 →
      (trace (Bc * Yc ^ q * Bc * Yc ^ (2 - q))).re ≤ (trace (Bc ^ 2 * Yc ^ 2)).re :=
  ⟨by decide, fun _ hq =>
    StratonovichHAMSecondMoment.FiniteGaussianMatrix.trace_word_le Bc_isHermitian
      Yc_isHermitian ⟨1, rfl⟩ hq⟩

end Refutations.FiniteGaussianMatrix
