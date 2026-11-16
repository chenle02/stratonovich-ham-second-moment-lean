namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.FockSandwichModel
-- Statement copied from the source (the printed type fails lean-pkg's round-trip check).
open MeasureTheory Real Finset Filter Topology Set
open scoped ComplexConjugate Nat
open HomogHypothesis (Rd)
open HermiteFock (Supp degLE fieldOp mem_degLE deg gmul cre ann)
open GaussianHermite (unitIdx)
open FockColumnBound (mulOp mulOp_ae op_ext band measurable_band abs_band_le bandProj wt measurable_wt sqrtResolvent nuEps nuEps_finite modes)
open ComplexPhaseScalar (invSqrtShift shiftOp)
open StaticInteractionCompleted (FockSandwich CPInputs PropagatorBlock InDisc)
open StaticPhaseCauchy (fockD taylorCoeff allOrdersA)
open SpectralMassIdentity (ralpha)
open PhaseContractions (PhaseCovariance dGam)
open IntervalScalar (staticE)
/-- PhaseCovariance, eps > 0, real orthonormal modes, lambda, h > 0, lambda h <= 1 and the other inputs (CPInputs, PropagatorBlock, hentire, hz, hv, hband, hgauss, hT, hS, hTS, hZ0, hcmp, hN1, hodd, hborn, hmean): sum sigma^n Z n converges, T commutes with it, E:static-interaction. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.FockSandwichModel.static_interaction_model_paper {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E]
    (Ec : ℕ → ℕ → ℕ → Type*) [∀ n m b, NormedAddCommGroup (Ec n m b)]
    [∀ n m b, NormedSpace ℂ (Ec n m b)] [∀ n m b, CompleteSpace (Ec n m b)]
    {alpha ε h lam σ N1 : ℝ} {Γ μ : Measure (Rd 3)} (hcov : PhaseCovariance alpha Γ μ)
    (hε : 0 < ε) (ψ : ∀ m, Fin m → Lp ℂ 2 (nuEps μ ε)) (hψ : ∀ m, Orthonormal ℂ (ψ m))
    (hreal : ∀ m i, ∀ᵐ ξ ∂(nuEps μ ε), ψ m i (-ξ) = conj (ψ m i ξ))
    (hlam : 0 < lam) (hh : 0 < h) (hlh : lam * h ≤ 1)
    (T S : E →L[ℝ] E) (f0 : E) (Z : ℕ → E) (zn : ℕ → ℝ)
    (hT : ‖T‖ ≤ √(Real.exp 1)) (hS : ‖S‖ ≤ √(Real.exp 1)) (hTS : ∀ x, T (S x) = x)
    (hZ0 : Z 0 = S f0) (hcmp : ∀ n, 1 ≤ n → ‖Z n‖ ≤ (lam * h)⁻¹ * zn n) (hN1 : N1 ≤ ‖f0‖)
    (F : ∀ n m b, ℂ → Ec n m b →L[ℂ] Ec n m b) (v : ∀ n m b, Ec n m b)
    (zc : ℕ → ℕ → ℕ → ℝ) (zm : ℕ → ℕ → ℝ)
    (Cop Fop Hop Q' : ∀ n m (_ : ℕ), ℂ → FockH (L2 3) m n →L[ℂ] FockH (L2 3) m n)
    (J : ∀ n m (_ : ℕ), ℂ → ℝ → FockH (L2 3) m n →L[ℂ] FockH (L2 3) m n)
    (hcp : ∀ n, 1 ≤ n → ∀ m (b : ℕ), CPInputs (opA0 (b : ℝ))
      (fieldB (b : ℝ) (nuEps_finite hcov.μ_tempered hε) (ψ m) (hψ m)) n alpha h
      (ralpha μ alpha) (Cop n m b) (Fop n m b) (Hop n m b) (Q' n m b) (J n m b))
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
  exact _root_.StratonovichHAMSecondMoment.FockSandwichModel.static_interaction_model_paper Ec (StratonovichHamSecondMomentLeanAuditBridge.PhaseContractions.pcToP hcov) hε ψ hψ hreal hlam hh hlh
    T S f0 Z zn hT hS hTS hZ0 hcmp hN1 F v zc zm Cop Fop Hop Q' J (fun n hn m b => StratonovichHamSecondMomentLeanAuditBridge.StaticInteractionCompleted.cpiToP (hcp n hn m b))
    hprop hentire hz hv hband hgauss hodd hborn hmean
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.FockSandwichModel
