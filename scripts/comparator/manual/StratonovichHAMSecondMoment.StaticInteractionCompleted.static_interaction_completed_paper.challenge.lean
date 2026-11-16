namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.StaticInteractionCompleted
-- Statement copied from the source (the printed type fails lean-pkg's round-trip check).
open Real Finset Filter Topology MeasureTheory Set
open scoped Nat
open StratonovichHAMSecondMoment.StaticPhaseCauchy StratonovichHAMSecondMoment.ComplexPhaseScalar
open StratonovichHAMSecondMoment.IntervalScalar (staticE)
open StratonovichHAMSecondMoment.PhaseContractions (PhaseCovariance dGam)
open StratonovichHAMSecondMoment.SpectralMassIdentity (ralpha)
open StratonovichHAMSecondMoment.HomogHypothesis (Rd)
/-- PhaseCovariance alpha Gamma mu, lambda, h > 0, lambda h <= 1, R_alpha, D_Gamma: the hypotheses of static_interaction_orders with the order bounds replaced by the inputs of static_phase_all_orders_cp at every n >= 1 give its three conclusions. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.StaticInteractionCompleted.static_interaction_completed_paper {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E]
    (Ec : ℕ → ℕ → ℕ → Type*) [∀ n m b, NormedAddCommGroup (Ec n m b)]
    [∀ n m b, NormedSpace ℂ (Ec n m b)] [∀ n m b, CompleteSpace (Ec n m b)]
    (Hs : ℕ → ℕ → ℕ → Type*) [∀ n m b, NormedAddCommGroup (Hs n m b)]
    [∀ n m b, InnerProductSpace ℂ (Hs n m b)] [∀ n m b, CompleteSpace (Hs n m b)]
    {alpha h lam σ N1 : ℝ} {Γ μ : Measure (Rd 3)} (hcov : PhaseCovariance alpha Γ μ)
    (hlam : 0 < lam) (hh : 0 < h) (hlh : lam * h ≤ 1)
    (T S : E →L[ℝ] E) (f0 : E) (Z : ℕ → E) (zn : ℕ → ℝ)
    (hT : ‖T‖ ≤ √(Real.exp 1)) (hS : ‖S‖ ≤ √(Real.exp 1)) (hTS : ∀ x, T (S x) = x)
    (hZ0 : Z 0 = S f0) (hcmp : ∀ n, 1 ≤ n → ‖Z n‖ ≤ (lam * h)⁻¹ * zn n) (hN1 : N1 ≤ ‖f0‖)
    (F : ∀ n m b, ℂ → Ec n m b →L[ℂ] Ec n m b) (v : ∀ n m b, Ec n m b)
    (zc : ℕ → ℕ → ℕ → ℝ) (zm : ℕ → ℕ → ℝ)
    (A0 B : ∀ n m b, Hs n m b →L[ℂ] Hs n m b) (hA0 : ∀ n m b, (A0 n m b).IsPositive)
    (hB : ∀ n m b, IsSelfAdjoint (B n m b))
    (hsand : ∀ n, 1 ≤ n → ∀ m b,
      FockSandwich (A0 n m b) (B n m b) (fockD n (ralpha μ alpha)) (alpha / 2))
    (Cop Fop Hop Q' : ∀ n m b, ℂ → Hs n m b →L[ℂ] Hs n m b)
    (J : ∀ n m b, ℂ → ℝ → Hs n m b →L[ℂ] Hs n m b)
    (hcp : ∀ n, 1 ≤ n → ∀ m b, CPInputs (A0 n m b) (B n m b) n alpha h (ralpha μ alpha)
      (Cop n m b) (Fop n m b) (Hop n m b) (Q' n m b) (J n m b))
    (hprop : ∀ n, 1 ≤ n → ∀ m b z, InDisc n alpha h (ralpha μ alpha) z →
      PropagatorBlock (F n m b z) (Cop n m b z) (Fop n m b z) (Hop n m b z) (Q' n m b z))
    (hentire : ∀ n, 1 ≤ n → ∀ m b, Differentiable ℂ (F n m b))
    (hz : ∀ n, 1 ≤ n → ∀ m b, zc n m b ≤ n * ‖taylorCoeff (F n m b) n (v n m b)‖)
    (hv : ∀ n, 1 ≤ n → ∀ m b, ‖v n m b‖ ≤ N1)
    (hband : ∀ n, 1 ≤ n → ∀ m, Tendsto (zc n m) atTop (𝓝 (zm n m)))
    (hgauss : ∀ n, 1 ≤ n → Tendsto (zm n) atTop (𝓝 (zn n)))
    (hodd : ∀ r s, Odd (r + s) → inner ℝ (T (Z r)) (T (Z s)) = 0)
    (hborn : ‖T (Z 1)‖ ^ 2 ≤ Real.exp 1 * (ralpha μ alpha * h ^ 2 * lam ^ (alpha - 2) *
      (1 + lam ^ 2 * h ^ 2) ^ 2 * ‖f0‖ ^ 2))
    (hmean : |inner ℝ f0 (T (Z 2))| ≤ ‖f0‖ * (√(Real.exp 1) * (dGam Γ alpha *
      (1 + lam ^ 2 * h ^ 2) * h ^ (3 - alpha) / (lam * (2 - alpha) * (3 - alpha)) * ‖f0‖))) :
    Summable (fun n => σ ^ n • Z n) ∧
      T (∑' n, σ ^ n • Z n) = ∑' n, σ ^ n • T (Z n) ∧
      ‖T (∑' n, σ ^ n • Z n)‖ ^ 2 ≤
        (1 + staticE alpha (allOrdersA alpha) (ralpha μ alpha) (dGam Γ alpha) h σ lam) *
          ‖f0‖ ^ 2 := by
  sorry
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.StaticInteractionCompleted
