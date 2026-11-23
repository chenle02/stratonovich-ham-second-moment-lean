/-
Refutation for the time density of the terminal-chain measure
(`E:terminal-chain-measure`, main TeX lines 4276-4282 at edf7085f: the product
`∏_{j=1}^n G_{s_{j+1}-s_j}` has `n` factors, with `s_{n+1} = T` and no factor
for the first time), package theorem
`StratonovichHAMSecondMoment.TerminalWickInputs.chainWeightReal_eq_ite`.

Wrong variant: an extra Green factor `G_{s_1 - 0}` from a chain started at time
`0`, i.e. the density `1_{0<s_1<⋯<s_n<T} s_1 ∏_j (s_{j+1} - s_j)` (this would give
mass `T^{2n+1}/(2n+1)!` instead of `T^{2n}/(2n)!`).  Counterexample: `n = 1`,
`T = 1`, `s_1 = 1/2`: the package density is `1 - 1/2 = 1/2`, the variant gives
`1/4`.  `extra_first_gap_contrast` is the package theorem at the same point.  No
junk-value reliance.

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.TerminalWickInputs

set_option autoImplicit false

open StratonovichHAMSecondMoment TerminalWick TerminalWickInputs

namespace Refutations.TerminalWickInputs

/-- Auxiliary: `0 < 1/2 < 1` is in the open simplex, with gap `1/2`. -/
theorem half_openSimplex : OpenSimplex 1 (fun _ : Fin 1 => (1 / 2 : ℝ)) := by
  refine ⟨fun _ => by norm_num, fun j => ?_⟩
  have hj : j = Fin.last 0 := Subsingleton.elim _ _
  subst hj
  rw [Fin.succ_last, Fin.snoc_last]
  norm_num

/-- Auxiliary: the gap at `s_1 = 1/2`, `T = 1`. -/
theorem half_gap (j : Fin 1) : gap 1 (fun _ : Fin 1 => (1 / 2 : ℝ)) j = 1 / 2 := by
  have hj : j = Fin.last 0 := Subsingleton.elim _ _
  subst hj
  rw [gap_last]
  norm_num

open scoped Classical in
/-- The package value: the time density at `s_1 = 1/2`, `T = 1`, is `1/2`. -/
theorem extra_first_gap_contrast :
    chainWeightReal 1 1 (fun _ => 1 / 2) =
      if OpenSimplex 1 (fun _ : Fin 1 => (1 / 2 : ℝ)) then ENNReal.ofReal (1 / 2) else 0 := by
  rw [chainWeightReal_eq_ite]
  simp only [half_gap, Finset.univ_unique, Finset.prod_singleton]

open scoped Classical in
/-- The density with the extra first factor `s_1` is false. -/
theorem extra_first_gap_refuted :
    ¬ (∀ (T : ℝ) (s : Fin 1 → ℝ), chainWeightReal 1 T s =
      if OpenSimplex T s then ENNReal.ofReal (s 0) * ∏ j, ENNReal.ofReal (gap T s j) else 0) := by
  intro h
  have h1 := h 1 (fun _ => 1 / 2)
  rw [extra_first_gap_contrast, ite_eq_left half_openSimplex, ite_eq_left half_openSimplex]
    at h1
  simp only [half_gap, Finset.univ_unique, Finset.prod_singleton] at h1
  rw [← ENNReal.ofReal_mul (by norm_num),
    ENNReal.ofReal_eq_ofReal_iff (by norm_num) (by norm_num)] at h1
  norm_num at h1

end Refutations.TerminalWickInputs
