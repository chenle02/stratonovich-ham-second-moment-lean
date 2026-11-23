/-
Refutation for the torus extraction `E:split-vector-cauchy` (main TeX lines
3973-3984 at edf7085f), package theorem
`StratonovichHAMSecondMoment.FixedSplitCore.torus_coefficient`.

Wrong variant: the unnormalized angular measure (`dθ` instead of
`dθ/(2π)`), i.e. `∫_{[0,2π]^n} e^{-ir·θ} Φ(ϱe^{iθ}) dθ = ϱ^r c_r`.
Counterexample: `n = 1`, the constant series `Φ ≡ 1` (`c_0 = 1`, all other
coefficients `0`), `ϱ = 1`, `r = 0`; the integral is `2π ≠ 1`.  The value
`2π` is obtained from the package theorem itself, which is also the contrast
`torus_normalization_contrast`.  No junk-value reliance (the integrand is
continuous, and integrability is part of the package conclusion).

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.FixedSplitCore

set_option autoImplicit false

namespace Refutations.FixedSplitCore

open StratonovichHAMSecondMoment.FixedSplitCore MeasureTheory Real

/-- The coefficients of the constant series `1`. -/
noncomputable def oneCoeff : (Fin 1 → ℕ) → ℂ := fun s => if s = 0 then 1 else 0

theorem oneCoeff_summable :
    Summable fun s : Fin 1 → ℕ => ‖oneCoeff s‖ * ∏ i, (fun _ : Fin 1 => (1 : ℝ)) i ^ s i := by
  have : (fun s : Fin 1 → ℕ => ‖oneCoeff s‖ * ∏ i, (fun _ : Fin 1 => (1 : ℝ)) i ^ s i) =
      fun s => if s = 0 then 1 else 0 := by
    funext s; unfold oneCoeff; split_ifs <;> simp
  rw [this]
  exact (hasSum_ite_eq 0 1).summable

theorem oneCoeff_hasSum (θ : Fin 1 → ℝ) :
    HasSum (fun s => monom (torusPoint (fun _ => 1) θ) s • oneCoeff s)
      ((fun _ : Fin 1 → ℂ => (1 : ℂ)) (torusPoint (fun _ => 1) θ)) := by
  have : (fun s => monom (torusPoint (fun _ => 1) θ) s • oneCoeff s) =
      fun s => if s = 0 then (1 : ℂ) else 0 := by
    funext s; unfold oneCoeff monom; split_ifs with h
    · subst h; simp
    · simp
  rw [this]
  exact hasSum_ite_eq 0 1

/-- The package normalization at the counterexample. -/
theorem torus_normalization_contrast :
    ((2 * π) ^ Fintype.card (Fin 1))⁻¹ •
        ∫ θ in angularBox (Fin 1), phase 0 θ • (fun _ : Fin 1 → ℂ => (1 : ℂ))
          (torusPoint (fun _ => 1) θ) =
      ((∏ i, (fun _ : Fin 1 => (1 : ℝ)) i ^ (0 : Fin 1 → ℕ) i : ℝ) : ℂ) • oneCoeff 0 :=
  (torus_coefficient oneCoeff (fun _ => 1) (fun _ => 1) 0 (fun _ => zero_le_one)
    oneCoeff_summable oneCoeff_hasSum).2

/-- Without the factor `(2π)^{-n}` the extraction formula is false. -/
theorem torus_normalization_refuted :
    ¬ (∀ (c : (Fin 1 → ℕ) → ℂ) (Φ : (Fin 1 → ℂ) → ℂ) (ρ : Fin 1 → ℝ) (r : Fin 1 → ℕ),
        (∀ i, 0 ≤ ρ i) → (Summable fun s : Fin 1 → ℕ => ‖c s‖ * ∏ i, ρ i ^ s i) →
        (∀ θ : Fin 1 → ℝ, HasSum (fun s => monom (torusPoint ρ θ) s • c s)
          (Φ (torusPoint ρ θ))) →
        ∫ θ in angularBox (Fin 1), phase r θ • Φ (torusPoint ρ θ) =
          ((∏ i, ρ i ^ r i : ℝ) : ℂ) • c r) := by
  intro h
  have h1 := h oneCoeff (fun _ => 1) (fun _ => 1) 0 (fun _ => zero_le_one) oneCoeff_summable
    oneCoeff_hasSum
  have h2 := torus_normalization_contrast
  rw [h1] at h2
  simp [oneCoeff] at h2
  have hpi : π⁻¹ * 2⁻¹ ≠ (1 : ℝ) := by
    have := Real.pi_gt_three
    intro h; field_simp at h; linarith
  apply hpi
  have h3 : ((π⁻¹ * 2⁻¹ : ℝ) : ℂ) = 1 := by push_cast; exact h2
  exact_mod_cast h3
end Refutations.FixedSplitCore
