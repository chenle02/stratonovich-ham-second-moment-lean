namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.FixedSplit
open Finset Real MeasureTheory
open scoped Nat
open StratonovichHAMSecondMoment.IntervalScalar StratonovichHAMSecondMoment.FixedSplitCore
-- Statement copied from the source (the printed type elides a term as `_`, which the round trip cannot elaborate).
-- The section variables of the source, as there:
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
/-- For kappa with sum k >= 1, r_i + q_i = 2 kappa_i, delta, R, T, sigma, h > 0, alpha <= 3, b - a <= h, cross intervals in [0,T], ||emb_(1/T) v||^2 <= V, the per-copy hypotheses and inputs: |<emb_(1/T) c_r, emb_(1/T) c_q>| <= k^2 splitConst delta^k R^k V prod splitFactor. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.FixedSplit.fixed_split_abstract (Z₁ Z₂ : Finset ι → Set E) (emb : ℝ → E →L[ℂ] F)
    (J : ι → E → E) (P : (ι → ℂ) → ℝ → ℝ → E → E) (v : E) (c : (ι → ℕ) → E)
    (κ : ι → ℕ) (p : ι → ℕ × ℕ) (a b h σ : ι → ℝ) (alpha δ R T V : ℝ) (k : ℕ)
    (hT : 0 < T) (hk : 1 ≤ k) (hsum : ∑ i, κ i = k) (hp : ∀ i, (p i).1 + (p i).2 = 2 * κ i)
    (hδ : 0 < δ) (hR : 0 < R) (hα : alpha ≤ 3) (hσ : ∀ i, 0 < σ i) (hh : ∀ i, 0 < h i)
    (hlen : ∀ i, b i - a i ≤ h i) (habC : ∀ i ∈ crossSet κ p, 0 ≤ a i ∧ b i ≤ T)
    (hcmp : ∀ ρ ρ' : ℝ, 0 < ρ → 0 < ρ' → ∀ x, ‖emb ρ' x‖ ≤ max 1 (ρ / ρ') * ‖emb ρ x‖)
    (hV : ‖emb (1 / T) v‖ ^ 2 ≤ V) (hv₁ : v ∈ Z₁ ∅) (hv₂ : v ∈ Z₂ ∅)
    (hJ₁ : ∀ i ∈ crossSet κ p, ∀ S ⊆ crossSet κ p, i ∉ S → ∀ x ∈ Z₁ S,
      J i x ∈ Z₁ (insert i S) ∧ ∀ ρ, (k : ℝ) / T ≤ ρ →
        ‖emb ρ (J i x)‖ ≤ insertConst alpha R ((k : ℝ) / T) (σ i) * ‖emb ρ x‖)
    (hJ₂ : ∀ i ∈ crossSet κ p, ∀ S ⊆ crossSet κ p, i ∉ S → ∀ x ∈ Z₂ S,
      J i x ∈ Z₂ (insert i S) ∧ ∀ ρ, (k : ℝ) / T ≤ ρ →
        ‖emb ρ (J i x)‖ ≤ insertConst alpha R ((k : ℝ) / T) (σ i) * ‖emb ρ x‖)
    (hPZ₁ : BackgroundPreserves (copyFirst κ p) (crossSet κ p) Z₁ P)
    (hPZ₂ : BackgroundPreserves (copySecond κ p) (crossSet κ p) Z₂ P)
    (hseg₁ : SegmentBound (copyFirst κ p) emb P
      (fun i => splitRadius alpha δ (σ i) R (h i) (κ i)) a b h κ k T)
    (hseg₂ : SegmentBound (copySecond κ p) emb P
      (fun i => splitRadius alpha δ (σ i) R (h i) (κ i)) a b h κ k T)
    (hent : EntireCoefficients c)
    (hdys₁ : DysonCrossCube (copyFirst κ p) (crossSet κ p) c
      (fun i => splitRadius alpha δ (σ i) R (h i) (κ i)) a b
      (word (copyFirst κ p) (crossSet κ p) a b T J P v))
    (hdys₂ : DysonCrossCube (copySecond κ p) (crossSet κ p) c
      (fun i => splitRadius alpha δ (σ i) R (h i) (κ i)) a b
      (word (copySecond κ p) (crossSet κ p) a b T J P v)) :
    ‖inner ℂ (emb (1 / T) (c fun i => (p i).1)) (emb (1 / T) (c fun i => (p i).2))‖ ≤
      (k : ℝ) ^ 2 * splitConst δ ^ k * R ^ k * V *
        ∏ i, splitFactor alpha (σ i) (h i) ((k : ℝ) / T) (κ i) (p i) := by
  bridge_revert_all
  bridge_auto _root_.StratonovichHAMSecondMoment.FixedSplit.fixed_split_abstract
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.FixedSplit
