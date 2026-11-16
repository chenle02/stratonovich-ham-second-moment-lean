namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.FiniteWordCutoff
-- Statement copied from the source (the printed type fails lean-pkg's round-trip check).
open Finset Real MeasureTheory
open scoped Nat
open StratonovichHAMSecondMoment.HermiteFock
open StratonovichHAMSecondMoment.GaussianHermite (unitIdx)
open StratonovichHAMSecondMoment.FixedSplit StratonovichHAMSecondMoment.FixedSplitCore
/-- FixedSplit.interval_coefficient_assembly_paper_fixed without hQ: Q_(r,q) = Re fullInner S (1/T) (U r) (U q) for uncut coefficients U, hsplits stated for it, and DuhamelWords for (U r, cf kappa r), (U q, cf kappa q) for every split; same bound on |coef|. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.FiniteWordCutoff.interval_coefficient_assembly_paper_words {d : ℕ} {alpha alpha0 : ℝ}
    {Γ μ : Measure (HomogHypothesis.Rd d)}
    (hH : HomogHypothesis.HomogCovariance d alpha alpha0 Γ μ)
    {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]
    {β α Ω : Type*} [MeasurableSpace Ω]
    {R T L c δ V coef : ℝ} {M k m : ℕ}
    (h σ a b : Fin M → ℝ)
    (hRdef : R = alpha * π * (μ (Metric.ball 0 1)).toReal / (2 * Real.sin (π * alpha / 2)))
    (hRpos : 0 < R) (hk : 1 ≤ k) (hT : 0 < T) (hδ : 0 < δ)
    (hh : ∀ i, 0 < h i) (hσpos : ∀ i, 0 < σ i)
    (hlen : ∀ i : Fin M, h i ≤ L * T / ((i : ℕ) + 1 : ℕ))
    (hσ : ∀ i, σ i ^ 2 ≤ c * h i ^ (-alpha0))
    (col : Fin m → Fin M) (S : ℝ → X →L[ℂ] X) (Mlt : Fin m → X →L[ℂ] X) (Pb : X →L[ℂ] X)
    (u w : X) (U : (Fin M → ℕ) → FullPhase X m)
    (hsplits : coef = ∑ κ ∈ (univ : Finset (Fin M)).finsuppAntidiag k,
      ∑ p ∈ Fintype.piFinset (fun i => antidiagonal (2 * κ i)),
        (fullInner S (1 / T) (U fun i => (p i).1) (U fun i => (p i).2)).re)
    (hIlen : ∀ i, b i - a i ≤ h i) (hab : ∀ i, 0 ≤ a i ∧ b i ≤ T)
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
    (Fr : β → X × X →L[ℂ] X × X) (A : (Fin M → ℕ) → Finset α)
    (ν : (Fin M → ℕ) → α → Measure Ω)
    (ω : (Fin M → ℕ) → α → Ω → β × List (Fin M × β))
    (hword : ∀ κ ∈ (univ : Finset (Fin M)).finsuppAntidiag k,
      ∀ p ∈ Fintype.piFinset (fun i => antidiagonal (2 * κ i)),
        (DuhamelWords col (fun i => 2 * κ i) σ (fun j => Pb ∘L Mlt j ∘L Pb) Fr u w
          (A fun i => (p i).1) (ν fun i => (p i).1) (ω fun i => (p i).1) (fun i => (p i).1)
          (U fun i => (p i).1) (cf κ fun i => (p i).1)) ∧
        DuhamelWords col (fun i => 2 * κ i) σ (fun j => Pb ∘L Mlt j ∘L Pb) Fr u w
          (A fun i => (p i).2) (ν fun i => (p i).2) (ω fun i => (p i).2) (fun i => (p i).2)
          (U fun i => (p i).2) (cf κ fun i => (p i).2))
    (hin : ∀ κ ∈ (univ : Finset (Fin M)).finsuppAntidiag k,
      ∀ p ∈ Fintype.piFinset (fun i => antidiagonal (2 * κ i)),
        SplitInputs col κ p S Mlt Pb (P κ) (cf κ) u w a b h σ alpha δ R T k) :
    |coef| ≤ (12 * max c 0 * max 1 L ^ (4 - alpha - alpha0) * splitConst δ *
        InventoryProduct.inventoryConst alpha alpha0) ^ k * R ^ k *
      T ^ ((4 - alpha - alpha0) * k) / (k ! : ℝ) ^ (3 - alpha) * V := by
  bridge_revert_all
  bridge_auto _root_.StratonovichHAMSecondMoment.FiniteWordCutoff.interval_coefficient_assembly_paper_words
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.FiniteWordCutoff
