/-
Refutation for the time exponent of `E:riesz-four` (main TeX lines 5158-5160 and
5206-5208 at edf7085f: "scaling time and space by `t` contributes `t^8` ... and
`t^{-2α-2α₀}` ..., giving `t^{2β}`"), package theorem
`StratonovichHAMSecondMoment.RieszFourDiagrams.riesz_four`.

Wrong variant: the order-four terms scale like the order-two terms,
`J_{m,n,D}(t) = c^2 t^β I_{m,D}` (one factor `t^β` per order two instead of per
pair).  Counterexample: `c = 1`, `α = α₀ = 1/2` (`β = 3`), `t = 2`, the split
`(4,0)`: the package gives `2^6 I_{4,D}`, the variant `2^3 I_{4,D}`, and `I_{4,D}` is
positive and finite.  `timeExponentHalved_contrast` is the package representation
at `t = 2`.
Class (a): manuscript-claim perturbation in the manuscript domain.
No junk-value reliance.

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.RieszFourDiagrams

set_option autoImplicit false

open MeasureTheory StratonovichHAMSecondMoment DiagramModel RieszFourDiagrams

namespace Refutations.RieszFourDiagrams

/-- The package at `c = 1`, `α = α₀ = 1/2`, `t = 2`, `(m, n) = (4, 0)`:
`J = 2^6 I`. -/
theorem timeExponentHalved_contrast :
    ∀ D ∈ Pi2 4 0, diagram (WaveGreen.waveGreen 1) (HigherRieszTwo.riesz 1 (1 / 2)) (1 / 2)
      4 0 D 2 = ENNReal.ofReal 64 * rieszUnit (1 / 2) (1 / 2) 4 0 D := by
  intro D hD
  rw [((riesz_four zero_le_one (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (m := 4) (n := 0) rfl two_pos).2 D hD).1]
  congr 2
  rw [show (2 : ℝ) * (4 - 1 / 2 - 1 / 2) = ((6 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  norm_num

/-- The order-four terms scale like `t^{2β}`, not `t^β`. -/
theorem timeExponentHalved_refuted :
    ¬ ∀ t : ℝ, 0 < t → ∀ D ∈ Pi2 4 0, diagram (WaveGreen.waveGreen 1)
      (HigherRieszTwo.riesz 1 (1 / 2)) (1 / 2) 4 0 D t =
        ENNReal.ofReal ((1 : ℝ) ^ 2 * t ^ (4 - 1 / 2 - 1 / 2 : ℝ)) *
          rieszUnit (1 / 2) (1 / 2) 4 0 D := by
  intro h
  obtain ⟨D, hD⟩ : (Pi2 4 0).Nonempty :=
    Finset.card_pos.1 (by rw [card_Pi2 (m := 4) (n := 0) (k := 2) rfl]; decide)
  have h1 := h 2 two_pos D hD
  have h2 := timeExponentHalved_contrast D hD
  have hpos := diagram_riesz_pos (c := 1) (α := 1 / 2) (α₀ := 1 / 2) one_pos (by norm_num) D
    two_pos
  have htop := rieszUnit_ne_top (α := 1 / 2) (α₀ := 1 / 2) (m := 4) (n := 0) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (k := 2) rfl hD
  rw [show (4 - 1 / 2 - 1 / 2 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at h1
  rw [h2] at hpos h1
  have hI : rieszUnit (1 / 2) (1 / 2) 4 0 D ≠ 0 := by
    intro h0; rw [h0, mul_zero] at hpos; exact lt_irrefl _ hpos
  have hr := congrArg ENNReal.toReal h1
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by norm_num),
    ENNReal.toReal_ofReal (by norm_num)] at hr
  have hp : 0 < (rieszUnit (1 / 2) (1 / 2) 4 0 D).toReal := ENNReal.toReal_pos hI htop
  norm_num at hr
  linarith

end Refutations.RieszFourDiagrams
