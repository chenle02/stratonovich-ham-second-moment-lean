/-
Refutation for the common-amplitude requirement of the comparison in
`StratonovichHAMSecondMoment.EndpointLemmas.product_comparison` (manuscript
`L:product-endpoints`, main TeX lines 7267-7279 at 39f2597a: "The amplitude remains
`c^θ c^{1-θ} = c`").

Wrong variant: the Gaussian comparison with endpoints of a different amplitude, here the
constant covariances `Γ = L = dx` and `S = (1/2) dx` at `θ = 1/2`.  Every Gaussian
convolution of `c dx` equals `c`, so the claim reads `1 ≤ 1^{1/2} (1/2)^{1/2}`, false.
Control of the broader Lean generalization (the geometric-mean comparison for any
exponents), outside the manuscript's endpoint class: all exponents are zero here, whereas the
manuscript requires `α = Σ a_j ∈ (1,2)` and `Σ b_j = 1` (main TeX lines 7171, 7183). 
`amplitude_mismatch_contrast` is the package
comparison with the common amplitude `1`.  No junk-value reliance.

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.EndpointLemmas

set_option autoImplicit false

namespace Refutations.EndpointLemmas

open MeasureTheory
open StratonovichHAMSecondMoment.EndpointLemmas
open StratonovichHAMSecondMoment.HomogHypothesis (Rd)

/-- The Gaussian convolution of `c dx` (zero exponents) is `c`. -/
theorem hconv_const {c : ℝ} (ε : ℝ) (hε : 0 < ε) (z : Rd 3) :
    hconv (prodRieszMeasure c (0 : Fin 3 → ℝ)) ε z = ENNReal.ofReal c := by
  have h : prodRiesz c (0 : Fin 3 → ℝ) = fun _ => ENNReal.ofReal c := by
    funext y; simp [prodRiesz, prodRieszReal]
  rw [hconv, prodRieszMeasure, h, withDensity_const, lintegral_smul_measure,
    lintegral_sub_left_eq_self (fun y => ENNReal.ofReal
      (StratonovichHAMSecondMoment.VariationalMean.heatK ε y)) z,
    StratonovichHAMSecondMoment.HigherRieszTwo.lintegral_heatK hε, smul_eq_mul, mul_one]

/-- The comparison with the common amplitude `1` (the package factorization at `θ = 1/2`). -/
theorem amplitude_mismatch_contrast :
    GaussComparison (1 / 2) (prodRieszMeasure 1 (0 : Fin 3 → ℝ))
      (prodRieszMeasure 1 (0 : Fin 3 → ℝ)) (prodRieszMeasure 1 (0 : Fin 3 → ℝ)) := by
  intro ε hε z
  rw [hconv_const ε hε, rpow_mul_rpow_one_sub _ (by norm_num) (by norm_num)]

/-- With mismatched amplitudes the comparison fails. -/
theorem amplitude_mismatch_refuted :
    ¬ GaussComparison (1 / 2) (prodRieszMeasure 1 (0 : Fin 3 → ℝ))
      (prodRieszMeasure 1 (0 : Fin 3 → ℝ)) (prodRieszMeasure (1 / 2) (0 : Fin 3 → ℝ)) := by
  intro h
  have h1 := h 1 one_pos 0
  rw [hconv_const 1 one_pos, hconv_const 1 one_pos, ENNReal.ofReal_one,
    ENNReal.one_rpow, one_mul] at h1
  have hlt : ENNReal.ofReal (1 / 2) ^ (1 - 1 / 2 : ℝ) < 1 :=
    ENNReal.rpow_lt_one (by rw [ENNReal.ofReal_lt_one]; norm_num) (by norm_num)
  exact absurd h1 (not_le.2 hlt)

end Refutations.EndpointLemmas
