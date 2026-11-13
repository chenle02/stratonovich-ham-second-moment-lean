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
/-- If 0<h<=1, 0<=s, s+h<=T, U_j in L^2, V_k (k<n) L^2-orthonormal, l fixed: each eta-integrand is integrable and sum_k ||coef U V_k l||^2 <= int^- 4 A_T h^(2-a) Phi_h(eta+l, eta) sum_j |U_j(eta)|^2 d eta. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.WaveTwoVariances.output_fixed (p : TimeParams) {d : ℕ} {s h : ℝ} (hh0 : 0 < h) (hh1 : h ≤ 1)
    (hs : 0 ≤ s) (hsT : s + h ≤ p.T) (U : Fin 2 → Rd d → ℂ) (hU : ∀ j, MemLp (U j) 2 volume)
    {n : ℕ} (V : Fin n → Fin 2 → Rd d → ℂ) (hV : PhaseBessel.IsOrthonormalL2 volume V)
    (l : Rd d) :
    (∀ k, Integrable (fun η => ∑ i, ∑ j, (U j η * conj (V k i (η + l))) •
        kerH p s h i j (η + l) η)) ∧
      ENNReal.ofReal (∑ k, ‖coef p s h U (V k) l‖ ^ 2) ≤
        ∫⁻ η, ENNReal.ofReal (4 * AT p * h ^ (2 - p.a) * rowKernel p.a h (η + l) η *
          ∑ j, ‖U j η‖ ^ 2) := by
  bridge_revert_all
  bridge_auto _root_.StratonovichHAMSecondMoment.WaveTwoVariances.output_fixed
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.WaveTwoVariances
