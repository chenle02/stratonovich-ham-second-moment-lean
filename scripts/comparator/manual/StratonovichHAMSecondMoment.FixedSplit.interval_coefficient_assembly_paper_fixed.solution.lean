namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.FixedSplit
open Finset Real MeasureTheory
open scoped Nat
open StratonovichHAMSecondMoment.IntervalScalar StratonovichHAMSecondMoment.FixedSplitCore
-- Statement copied from the source (the printed type elides a term as `_`, which the round trip cannot elaborate).
/-- Under H:homog and the hypotheses of interval_coefficient_assembly_paper_completed but hfixed, with endpoints in [0,T], b - a <= h, delta > 0, the Fock-model operator hypotheses, the V bound, SplitInputs for every split and the added hQ: its conclusion, C_split = splitConst delta. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.FixedSplit.interval_coefficient_assembly_paper_fixed {d : ℕ} {alpha alpha0 : ℝ}
    {Γ μ : Measure (HomogHypothesis.Rd d)}
    (hH : HomogHypothesis.HomogCovariance d alpha alpha0 Γ μ)
    {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]
    {R T L c δ V coef : ℝ} {M k m : ℕ}
    (h σ a b : Fin M → ℝ) (Q : (Fin M → ℕ × ℕ) → ℝ)
    (hRdef : R = alpha * π * (μ (Metric.ball 0 1)).toReal / (2 * Real.sin (π * alpha / 2)))
    (hRpos : 0 < R) (hk : 1 ≤ k) (hT : 0 < T) (hδ : 0 < δ)
    (hh : ∀ i, 0 < h i) (hσpos : ∀ i, 0 < σ i)
    (hlen : ∀ i : Fin M, h i ≤ L * T / ((i : ℕ) + 1 : ℕ))
    (hσ : ∀ i, σ i ^ 2 ≤ c * h i ^ (-alpha0))
    (hsplits : coef = ∑ κ ∈ (univ : Finset (Fin M)).finsuppAntidiag k,
      ∑ p ∈ Fintype.piFinset (fun i => antidiagonal (2 * κ i)), Q p)
    (hIlen : ∀ i, b i - a i ≤ h i) (hab : ∀ i, 0 ≤ a i ∧ b i ≤ T)
    (col : Fin m → Fin M) (S : ℝ → X →L[ℂ] X) (Mlt : Fin m → X →L[ℂ] X) (Pb : X →L[ℂ] X)
    (u w : X)
    (hSs : ∀ ρ u w, inner ℂ (S ρ u) w = inner ℂ u (S ρ w))
    (hSn : ∀ ρ : ℝ, 0 < ρ → ∀ f, ‖S ρ f‖ ≤ ρ⁻¹ * ‖f‖)
    (hScmp : ∀ ρ ρ' : ℝ, 0 < ρ → 0 < ρ' → ∀ g, ‖S ρ' g‖ ≤ max 1 (ρ / ρ') * ‖S ρ g‖)
    (hM : ∀ j u w, inner ℂ (Mlt j u) w = inner ℂ u (Mlt j w))
    (hPs : ∀ u w, inner ℂ (Pb u) w = inner ℂ u (Pb w)) (hPP : ∀ u, Pb (Pb u) = Pb u)
    (hPS : ∀ ρ u, Pb (S ρ u) = S ρ (Pb u))
    (hcol : ∀ i (ρ : ℝ), 0 < ρ →
      FockForm.FockColumn (fun j => S ρ ∘L colorMask col i Mlt j) (R * ρ ^ (alpha - 2)))
    (hV : ‖u‖ ^ 2 + ‖S (1 / T) w‖ ^ 2 ≤ V)
    (P : ∀ κ : Fin M → ℕ, (Fin M → ℂ) → ℝ → ℝ → PhaseSp X col (fun i => 2 * κ i) →
      PhaseSp X col (fun i => 2 * κ i))
    (cf : ∀ κ : Fin M → ℕ, (Fin M → ℕ) → PhaseSp X col (fun i => 2 * κ i))
    (hQ : ∀ κ ∈ (univ : Finset (Fin M)).finsuppAntidiag k,
      ∀ p ∈ Fintype.piFinset (fun i => antidiagonal (2 * κ i)),
        |Q p| ≤ ‖inner ℂ (fockEmb S (1 / T) (cf κ fun i => (p i).1))
          (fockEmb S (1 / T) (cf κ fun i => (p i).2))‖)
    (hin : ∀ κ ∈ (univ : Finset (Fin M)).finsuppAntidiag k,
      ∀ p ∈ Fintype.piFinset (fun i => antidiagonal (2 * κ i)),
        SplitInputs col κ p S Mlt Pb (P κ) (cf κ) u w a b h σ alpha δ R T k) :
    |coef| ≤ (12 * max c 0 * max 1 L ^ (4 - alpha - alpha0) * splitConst δ *
        InventoryProduct.inventoryConst alpha alpha0) ^ k * R ^ k *
      T ^ ((4 - alpha - alpha0) * k) / (k ! : ℝ) ^ (3 - alpha) * V := by
  bridge_revert_all
  bridge_auto _root_.StratonovichHAMSecondMoment.FixedSplit.interval_coefficient_assembly_paper_fixed
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.FixedSplit
