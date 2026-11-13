module
import StratonovichHAMSecondMoment.RayleighTail
set_option autoImplicit false
set_option pp.all true
#check @StratonovichHAMSecondMoment.RayleighTail.cutoff_split
#print axioms StratonovichHAMSecondMoment.RayleighTail.cutoff_split
#check @StratonovichHAMSecondMoment.RayleighTail.gaussian_weight_tail
#print axioms StratonovichHAMSecondMoment.RayleighTail.gaussian_weight_tail
#check @StratonovichHAMSecondMoment.RayleighTail.rayleigh_tail
#print axioms StratonovichHAMSecondMoment.RayleighTail.rayleigh_tail
#check @StratonovichHAMSecondMoment.RayleighTail.rayleigh_head_integrable
#print axioms StratonovichHAMSecondMoment.RayleighTail.rayleigh_head_integrable
#check @StratonovichHAMSecondMoment.RayleighTail.rayleigh_tail_paper
#print axioms StratonovichHAMSecondMoment.RayleighTail.rayleigh_tail_paper
open MeasureTheory Set in
/-- Consumer: head and tail combined, the Rayleigh integrand is integrable on
the whole half-line `[0, ∞)`, with the tail bound kept. -/
private theorem rayleigh_consumer (G : ℝ → ℝ) (hG : Measurable G) (A₀ C ν M δ : ℝ)
    (hgrowth : ∀ r, 0 ≤ r → G r ≤ A₀ + C * r ^ ν)
    (hC : 0 ≤ C) (hν1 : 1 < ν) (hν2 : ν < 2) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hM : 0 < M) (hcut : 4 * C ≤ M ^ (2 - ν)) :
    IntegrableOn (fun r : ℝ => r / δ * Real.exp ((G r - r ^ 2 / 2) / δ)) (Ici 0) ∧
      ∫ r in Ioi M, r / δ * Real.exp ((G r - r ^ 2 / 2) / δ) ≤
        4 * Real.exp ((A₀ - M ^ 2 / 4) / δ) := by
  obtain ⟨ht, hb, hh⟩ := StratonovichHAMSecondMoment.RayleighTail.rayleigh_tail_paper
    G hG A₀ C ν M δ hgrowth hC hν1 hν2 hδ hδ1 hM hcut
  refine ⟨?_, hb⟩
  rw [← Icc_union_Ioi_eq_Ici hM.le]
  exact hh.union ht
#check @rayleigh_consumer
#print axioms rayleigh_consumer
open MeasureTheory Set in
example :
    IntegrableOn (fun r : ℝ => r / (1 / 2) * Real.exp ((0 - r ^ 2 / 2) / (1 / 2))) (Ici 0) ∧
      ∫ r in Ioi (1 : ℝ), r / (1 / 2) * Real.exp ((0 - r ^ 2 / 2) / (1 / 2)) ≤
        4 * Real.exp ((0 - 1 ^ 2 / 4) / (1 / 2)) :=
  rayleigh_consumer (fun _ => 0) measurable_const 0 0 (3 / 2) 1 (1 / 2)
    (by intro r _; simp) le_rfl (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by simp)
