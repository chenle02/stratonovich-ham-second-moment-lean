/-
Refutation for the total-order-four coefficient (main TeX lines 5163, 5169-5171
and 5446-5451 at edf7085f: `A_2(t) = Σ_{m=0}^{4} E[X_m X_{4-m}]`, all five splits),
package theorem `StratonovichHAMSecondMoment.RieszFourDiagrams.riesz_coeffA_two`.

Wrong variant: only the diagonal split counts, `A_2(t) = Σ_D J_{2,2,D}(t)`
(`A_2 = E X_2²`, the Skorohod orthogonality of the chaoses, which fails for the
Stratonovich expansion).  Counterexample: `c = 1`, `α = α₀ = 1/2`, `t = 1`: the
split `(0,4)` contributes a positive amount (`diagram_riesz_pos`) and every term is
finite (`riesz_coeffA_two`).  `secondChaosOnly_contrast` is the package
representation at the same point.
Class (a): manuscript-claim perturbation in the manuscript domain.
No junk-value reliance.

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.RieszFourDiagrams

set_option autoImplicit false

open MeasureTheory StratonovichHAMSecondMoment DiagramModel RieszFourDiagrams

namespace Refutations.RieszFourDiagrams

/-- The package at `c = 1`, `α = α₀ = 1/2`, `t = 1`: `A_2` is the sum over all five
splits and is finite. -/
theorem secondChaosOnly_contrast :
    coeffA (WaveGreen.waveGreen 1) (HigherRieszTwo.riesz 1 (1 / 2)) (1 / 2) 2 1 =
        ENNReal.ofReal ((1 : ℝ) ^ 2 * (1 : ℝ) ^ (2 * (4 - 1 / 2 - 1 / 2 : ℝ))) *
          ∑ m ∈ Finset.range (2 * 2 + 1), ∑ D ∈ Pi2 m (2 * 2 - m),
            rieszUnit (1 / 2) (1 / 2) m (2 * 2 - m) D ∧
      coeffA (WaveGreen.waveGreen 1) (HigherRieszTwo.riesz 1 (1 / 2)) (1 / 2) 2 1 ≠ ⊤ :=
  riesz_coeffA_two zero_le_one (by norm_num) (by norm_num) (by norm_num) (by norm_num) one_pos

/-- `A_2(t)` is not the diagonal term `E X_2²` alone. -/
theorem secondChaosOnly_refuted :
    ¬ coeffA (WaveGreen.waveGreen 1) (HigherRieszTwo.riesz 1 (1 / 2)) (1 / 2) 2 1 =
      ∑ D ∈ Pi2 2 (2 * 2 - 2),
        diagram (WaveGreen.waveGreen 1) (HigherRieszTwo.riesz 1 (1 / 2)) (1 / 2) 2 (2 * 2 - 2)
          D 1 := by
  intro h
  have hfin := secondChaosOnly_contrast.2
  unfold coeffA at h hfin
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add] at h hfin
  set T0 := ∑ D ∈ Pi2 0 (2 * 2 - 0),
    diagram (WaveGreen.waveGreen 1) (HigherRieszTwo.riesz 1 (1 / 2)) (1 / 2) 0 (2 * 2 - 0) D 1
  set T2 := ∑ D ∈ Pi2 2 (2 * 2 - 2),
    diagram (WaveGreen.waveGreen 1) (HigherRieszTwo.riesz 1 (1 / 2)) (1 / 2) 2 (2 * 2 - 2) D 1
  set X1 := ∑ D ∈ Pi2 1 (2 * 2 - 1),
    diagram (WaveGreen.waveGreen 1) (HigherRieszTwo.riesz 1 (1 / 2)) (1 / 2) 1 (2 * 2 - 1) D 1
  set X3 := ∑ D ∈ Pi2 3 (2 * 2 - 3),
    diagram (WaveGreen.waveGreen 1) (HigherRieszTwo.riesz 1 (1 / 2)) (1 / 2) 3 (2 * 2 - 3) D 1
  set X4 := ∑ D ∈ Pi2 (2 * 2) (2 * 2 - 2 * 2), diagram (WaveGreen.waveGreen 1)
    (HigherRieszTwo.riesz 1 (1 / 2)) (1 / 2) (2 * 2) (2 * 2 - 2 * 2) D 1
  have hT2 : T2 ≠ ⊤ := by rw [← h]; exact hfin
  have hT0 : 0 < T0 := by
    obtain ⟨D, hD⟩ : (Pi2 0 (2 * 2 - 0)).Nonempty :=
      Finset.card_pos.1 (by rw [card_Pi2 (m := 0) (n := 2 * 2 - 0) (k := 2) rfl]; decide)
    exact lt_of_lt_of_le (diagram_riesz_pos one_pos (by norm_num) D one_pos)
      (Finset.single_le_sum (f := fun D => diagram (WaveGreen.waveGreen 1)
        (HigherRieszTwo.riesz 1 (1 / 2)) (1 / 2) 0 (2 * 2 - 0) D 1) (fun _ _ => bot_le) hD)
  have hle : T0 + T2 ≤ 0 + T2 := by
    rw [zero_add]
    calc T0 + T2 ≤ T0 + X1 + T2 := by gcongr; exact le_self_add
      _ ≤ T0 + X1 + T2 + X3 := le_self_add
      _ ≤ T0 + X1 + T2 + X3 + X4 := le_self_add
      _ = T2 := h
  have h0 := ENNReal.le_of_add_le_add_right hT2 hle
  exact absurd hT0 (not_lt.2 h0)

end Refutations.RieszFourDiagrams
