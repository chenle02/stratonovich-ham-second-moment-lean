/-
Refutation for `StratonovichHAMSecondMoment.MaskedTrigProducts.norm_sq_sum_le`
(`L:masked-trig-products`).

Wrong variant: the orthogonal-modes form, with `Σ|c_j|²` in place of the
package factor `Σ|c_j|`, stated in the exact binder shape of `norm_sq_sum_le`
(index type `ι`, complex seminormed space `E`, `s : Finset ι`, `c`, `v`; both
types quantified in universe `0`). It is false when modes coincide (TeX
l. 373-375: "Repeated or zero frequencies are permitted; no orthogonality ...
is used"). Witness `ι = Fin 4`, `E = ℂ`, `s = univ`, four equal modes
`v_j = 1`, `c_j = 1/4`: `1 ≤ 1/4` fails. The contrast theorem applies
`norm_sq_sum_le` itself at the same point, where its right side is `1 * 1`.

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.MaskedTrigProducts

set_option autoImplicit false

namespace Refutations.MaskedTrigProducts

/-- `norm_sq_sum_le` with `Σ|c_j|²` in place of `Σ|c_j|` is false. -/
theorem hilbert_orthogonal_weights :
    ¬ ∀ (ι E : Type) [SeminormedAddCommGroup E] [NormedSpace ℂ E]
        (s : Finset ι) (c : ι → ℂ) (v : ι → E),
      ‖∑ j ∈ s, c j • v j‖ ^ 2 ≤
        (∑ j ∈ s, ‖c j‖ ^ 2) * ∑ j ∈ s, ‖c j‖ * ‖v j‖ ^ 2 := by
  intro h
  have := h (Fin 4) ℂ Finset.univ (fun _ => 1 / 4) (fun _ => 1)
  simp at this
  norm_num at this

/-- Contrast: the package theorem `norm_sq_sum_le` at the counterexample point
(`ι = Fin 4`, `E = ℂ`, `c = 1/4`, `v = 1`). -/
theorem hilbert_orthogonal_weights_contrast :
    ‖∑ j : Fin 4, (fun _ => (1 / 4 : ℂ)) j • (fun _ => (1 : ℂ)) j‖ ^ 2 ≤
      (∑ j : Fin 4, ‖(fun _ => (1 / 4 : ℂ)) j‖) *
        ∑ j : Fin 4, ‖(fun _ => (1 / 4 : ℂ)) j‖ * ‖(fun _ => (1 : ℂ)) j‖ ^ 2 :=
  StratonovichHAMSecondMoment.MaskedTrigProducts.norm_sq_sum_le Finset.univ
    (fun _ => (1 / 4 : ℂ)) (fun _ => (1 : ℂ))

end Refutations.MaskedTrigProducts
