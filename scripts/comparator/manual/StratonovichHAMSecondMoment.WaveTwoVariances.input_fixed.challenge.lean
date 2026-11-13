namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.WaveTwoVariances
open MeasureTheory Set Filter Topology
open scoped ComplexConjugate ENNReal
open StratonovichHAMSecondMoment
open StratonovichHAMSecondMoment.MaskedTrigProducts (bracket frequencyPair)
open StratonovichHAMSecondMoment.MaskedContinuousWave (Wave cFn bFn waveFn C₁)
open StratonovichHAMSecondMoment.TimeCompletion
open StratonovichHAMSecondMoment.HomogHypothesis (Rd)
open StratonovichHAMSecondMoment.FrequencyRow (rowKernel)
-- Statement copied from the source (the printed type names the instance `WithLp.measurableSpace (2 : ENNReal) ..` explicitly, and its `2 : ENNReal` does not elaborate to the project's instance term).
/-- If 0<h<=1, 0<=s, s+h<=T, U_k (k<n) L^2-orthonormal, V_i in L^2, l fixed: each eta-integrand is integrable and sum_k ||coef U_k V l||^2 <= int^- 4 A_T h^(2-a) Phi_h(xi, xi-l) sum_i |V_i(xi)|^2 d xi. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.WaveTwoVariances.input_fixed (p : TimeParams) {d : ℕ} {s h : ℝ} (hh0 : 0 < h) (hh1 : h ≤ 1)
    (hs : 0 ≤ s) (hsT : s + h ≤ p.T) {n : ℕ} (U : Fin n → Fin 2 → Rd d → ℂ)
    (hU : PhaseBessel.IsOrthonormalL2 volume U) (V : Fin 2 → Rd d → ℂ)
    (hV : ∀ i, MemLp (V i) 2 volume) (l : Rd d) :
    (∀ k, Integrable (fun η => ∑ i, ∑ j, (U k j η * conj (V i (η + l))) •
        kerH p s h i j (η + l) η)) ∧
      ENNReal.ofReal (∑ k, ‖coef p s h (U k) V l‖ ^ 2) ≤
        ∫⁻ ξ, ENNReal.ofReal (4 * AT p * h ^ (2 - p.a) * rowKernel p.a h ξ (ξ - l) *
          ∑ i, ‖V i ξ‖ ^ 2) := by
  sorry
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.WaveTwoVariances
