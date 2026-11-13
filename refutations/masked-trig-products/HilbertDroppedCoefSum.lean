/-
Refutation for `StratonovichHAMSecondMoment.MaskedTrigProducts.norm_sq_sum_le`
(`L:masked-trig-products`, TeX l. 365-368).

Wrong variant: the package statement with the factor `Σ|c_j|` dropped,
`‖Σ c_j v_j‖² ≤ Σ|c_j| ‖v_j‖²`, in the exact binder shape of `norm_sq_sum_le`
(index type `ι`, complex seminormed space `E`, `s : Finset ι`, `c`, `v`; both
types quantified in universe `0`). Witness `ι = Fin 2`, `E = ℂ`,
`s = univ`, `c = (1, 1)`, `v = (1, 1)`: `4 ≤ 2` fails. The contrast theorem
applies `norm_sq_sum_le` itself at the same point, where its right side is
`2 * 2 = 4` and the bound holds.

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.MaskedTrigProducts

set_option autoImplicit false

namespace Refutations.MaskedTrigProducts

/-- `norm_sq_sum_le` without the factor `Σ|c_j|` is false. -/
theorem hilbert_dropped_coef_sum :
    ¬ ∀ (ι E : Type) [SeminormedAddCommGroup E] [NormedSpace ℂ E]
        (s : Finset ι) (c : ι → ℂ) (v : ι → E),
      ‖∑ j ∈ s, c j • v j‖ ^ 2 ≤ ∑ j ∈ s, ‖c j‖ * ‖v j‖ ^ 2 := by
  intro h
  have := h (Fin 2) ℂ Finset.univ (fun _ => 1) (fun _ => 1)
  simp at this
  norm_num at this

/-- Contrast: the package theorem `norm_sq_sum_le` at the counterexample point
(`ι = Fin 2`, `E = ℂ`, `c = v = 1`). -/
theorem hilbert_dropped_coef_sum_contrast :
    ‖∑ j : Fin 2, (fun _ => (1 : ℂ)) j • (fun _ => (1 : ℂ)) j‖ ^ 2 ≤
      (∑ j : Fin 2, ‖(fun _ => (1 : ℂ)) j‖) *
        ∑ j : Fin 2, ‖(fun _ => (1 : ℂ)) j‖ * ‖(fun _ => (1 : ℂ)) j‖ ^ 2 :=
  StratonovichHAMSecondMoment.MaskedTrigProducts.norm_sq_sum_le Finset.univ
    (fun _ => (1 : ℂ)) (fun _ => (1 : ℂ))

end Refutations.MaskedTrigProducts
