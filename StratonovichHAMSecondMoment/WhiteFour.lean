module

/-
Copyright 2026 Le Chen. SPDX-License-Identifier: Apache-2.0

The nine order-four white-noise diagram integrals (wave L13 item D6, part 2:
`P:white-four`).  Main TeX file `notes/notes_stratonovich_ham_second_moment.tex`
at revision 39f2597a:
* the pairings `A = {(1,2),(3,4)}`, `B = {(1,3),(2,4)}`, `C = {(1,4),(2,3)}`
  and the Green normalization `G(s,y) = ½ 1_{|y|<s}` (lines 4911-4919);
* `E:interval-area`: `F(a,b,c) = 4ab - (a+b-c)_+² + (|a-b|-c)_+²`, the area of
  `{|x| < a, |y| < b, |x-y| < c}` (lines 4923-4935);
* the domains `(0,4)`, `(1,3)`, `(2,2)` of the increment variables (lines
  4937-4943);
* `P:white-four` (statement lines 4946-4983, proof 4985-5015): the table
  `E:white-four-table`, the total `E:total-four`, and the scaling
  `t^{6-2α₀}`.

Labels are 0-based (`i : Fin 4` is the TeX label `i+1`), so `pA = ![1,0,3,2]`
is `A`, `pB = ![2,3,0,1]` is `B`, `pC = ![3,2,1,0]` is `C`.  A table row
`(m,n), D, V, q₁, q₂` is the statement
`diagramLim 1 δ₀ α₀ m n D t = ∫_{dom} q₁^{-α₀} q₂^{-α₀} V`, with the
increment vector `v = (a,b,c,d)` for `(0,4)` and `(2,2)` and `v = (r,a,b,c)`
for `(1,3)` (the letters of lines 4937-4943), Lebesgue measure on `ℝ^4`, and
`q^{-α₀}` the `ℝ≥0∞` power `ENNReal.ofReal q ^ (-α₀)`.

Formalized (all proved, nothing supplied; the analytic limit is
`WhiteCollapse.diagramLim_white`):
* `Pi2_four`: `Π_2` on four labels is `{A, B, C}` ("no unlisted pairing or
  multiplicity", line 5001);
* `volume_tri`: `E:interval-area` (the area is `F`), with `volume_strip`,
  `volume_box` for the other two area shapes;
* `whiteSpatial_*`: the nine collapsed spatial factors `V` (and the three
  `(3,1)` ones), e.g. `whiteSpatial 1 pB h = F(r, a, min(b,c))/16`;
* `J_04A` … `J_22C`: the nine rows of `E:white-four-table`;
* `J_40_eq`, `J_31A_eq`, `J_31B_eq`, `J_31C_eq`: "or by exchanging the two
  chains" (`J_{4,0,D} = J_{0,4,D}`; `J_{3,1}` for `A, B, C` equals `J_{1,3}`
  for `C, B, A`);
* `total_four`: `E:total-four`, `A_2(t) = 2 Σ_D J_{0,4,D} + 2 Σ_D J_{1,3,D} +
  Σ_D J_{2,2,D}` (`A_2` = `coeffALim 1 δ₀ α₀ 2 t`);
* `diagramLim_four_scale`: every order-four entry is `t^{6-2α₀}` times its
  unit-time value (`t > 0`), from the general `whiteDiagram_smul`;
* wrapper `white_four_paper`.

Hypotheses: `α₀ < 1` (the manuscript's `0 < α₀ < 1`; positivity is carried by
the wrapper and unused), `d = α = 1`, `γ = δ₀`.  Class: whole on the model
(registered model choice `DiagramModel`): every conclusion of `P:white-four`
is a Lean conclusion about `diagramLim 1 δ₀`, the TeX's `J_{m,n,D}(t)` for
white noise.  Statements about `E u²` are not part of `P:white-four`.

Lemmas marked "Auxiliary" serve only the Lean route.
-/
public import Mathlib
public import StratonovichHAMSecondMoment.WhiteCollapse

@[expose] public section

noncomputable section

set_option autoImplicit false

open MeasureTheory Filter Topology Real
open scoped ENNReal

namespace StratonovichHAMSecondMoment.WhiteFour

open HomogHypothesis (Rd)
open DiagramModel WhiteCollapse

/-! ### The three pairings of four labels -/

/-- The pairing `A = {(1,2),(3,4)}` (main TeX line 4913), 0-based. -/
def pA : Fin 4 → Fin 4 := ![1, 0, 3, 2]

/-- The pairing `B = {(1,3),(2,4)}` (main TeX line 4913), 0-based. -/
def pB : Fin 4 → Fin 4 := ![2, 3, 0, 1]

/-- The pairing `C = {(1,4),(2,3)}` (main TeX line 4914), 0-based. -/
def pC : Fin 4 → Fin 4 := ![3, 2, 1, 0]

theorem isPairing_pA : IsPairing pA := by unfold IsPairing pA; decide
theorem isPairing_pB : IsPairing pB := by unfold IsPairing pB; decide
theorem isPairing_pC : IsPairing pC := by unfold IsPairing pC; decide

/-- The pairings of four labels are exactly `A, B, C` ("these are the three
pairings of four vertices", main TeX line 4916). -/
theorem pairings_four :
    FiniteWick.pairings (Finset.univ : Finset (Fin 4)) = {pA, pB, pC} := by
  symm
  refine Finset.eq_of_subset_of_card_le ?_ ?_
  · intro D hD
    simp only [Finset.mem_insert, Finset.mem_singleton] at hD
    rw [FiniteWick.mem_pairings]
    rcases hD with rfl | rfl | rfl <;> decide
  · rw [FiniteWick.card_pairings_even 2 _ (by simp)]
    decide

/-- `Π_2` for the chains `(0,4)`. -/
theorem Pi2_04 : Pi2 0 4 = {pA, pB, pC} := pairings_four
/-- `Π_2` for the chains `(1,3)`. -/
theorem Pi2_13 : Pi2 1 3 = {pA, pB, pC} := pairings_four
/-- `Π_2` for the chains `(2,2)`. -/
theorem Pi2_22 : Pi2 2 2 = {pA, pB, pC} := pairings_four
/-- `Π_2` for the chains `(3,1)`. -/
theorem Pi2_31 : Pi2 3 1 = {pA, pB, pC} := pairings_four
/-- `Π_2` for the chains `(4,0)`. -/
theorem Pi2_40 : Pi2 4 0 = {pA, pB, pC} := pairings_four

/-- Auxiliary: the openers of `A`. -/
theorem openers_pA : openers pA = {0, 2} := by decide
/-- Auxiliary: the openers of `B`. -/
theorem openers_pB : openers pB = {0, 1} := by decide
/-- Auxiliary: the openers of `C`. -/
theorem openers_pC : openers pC = {0, 1} := by decide

/-- Auxiliary: positions under `A` are `(x, x, y, y)`. -/
theorem opener_pA (v : Fin 4 → ℝ) : (fun i => v (opener pA i)) = ![v 0, v 0, v 2, v 2] := by
  funext i; fin_cases i <;> rfl
/-- Auxiliary: positions under `B` are `(x, y, x, y)`. -/
theorem opener_pB (v : Fin 4 → ℝ) : (fun i => v (opener pB i)) = ![v 0, v 1, v 0, v 1] := by
  funext i; fin_cases i <;> rfl
/-- Auxiliary: positions under `C` are `(x, y, y, x)`. -/
theorem opener_pC (v : Fin 4 → ℝ) : (fun i => v (opener pC i)) = ![v 0, v 1, v 1, v 0] := by
  funext i; fin_cases i <;> rfl

/-- Auxiliary: the Gaussian closer weight under `A`. -/
theorem gaussW_pA (v : Fin 4 → ℝ) :
    gaussW pA v = ENNReal.ofReal (phi 1 (v 1)) * ENNReal.ofReal (phi 1 (v 3)) := by
  rw [gaussW, openers_pA, Finset.prod_insert (by decide), Finset.prod_singleton]; rfl
/-- Auxiliary: the Gaussian closer weight under `B`. -/
theorem gaussW_pB (v : Fin 4 → ℝ) :
    gaussW pB v = ENNReal.ofReal (phi 1 (v 2)) * ENNReal.ofReal (phi 1 (v 3)) := by
  rw [gaussW, openers_pB, Finset.prod_insert (by decide), Finset.prod_singleton]; rfl
/-- Auxiliary: the Gaussian closer weight under `C`. -/
theorem gaussW_pC (v : Fin 4 → ℝ) :
    gaussW pC v = ENNReal.ofReal (phi 1 (v 2)) * ENNReal.ofReal (phi 1 (v 3)) := by
  rw [gaussW, openers_pC, Finset.prod_insert (by decide), Finset.prod_singleton, mul_comm]; rfl

/-! ### Fubini on `ℝ^4` -/

/-- Auxiliary: `Fin.cons x` is measurable. -/
theorem measurable_cons (x : ℝ) (n : ℕ) :
    Measurable fun w : Fin n → ℝ => (Fin.cons x w : Fin (n + 1) → ℝ) := by
  refine measurable_pi_iff.2 fun i => ?_
  cases i using Fin.cases with
  | zero => simp
  | succ j => simpa using measurable_pi_apply j

/-- Auxiliary: splitting off the first coordinate. -/
theorem lintegral_fin_cons (n : ℕ) (F : (Fin (n + 1) → ℝ) → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ v, F v = ∫⁻ x : ℝ, ∫⁻ w : Fin n → ℝ, F (Fin.cons x w) := by
  have hmp := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => (volume : Measure ℝ)) 0
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0
  have he : ∀ p : ℝ × (Fin n → ℝ), e.symm p = Fin.cons p.1 p.2 := by
    intro p; simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply]; rfl
  rw [show (volume : Measure (Fin (n + 1) → ℝ)) = Measure.pi fun _ => volume from rfl,
    ← (hmp.symm _).lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _) F,
    lintegral_prod (fun p => F (e.symm p)) (hF.comp e.symm.measurable).aemeasurable]
  simp_rw [he]
  rfl

/-- Auxiliary: Tonelli on `ℝ^4` as four iterated integrals. -/
theorem lintegral_fin4 (F : (Fin 4 → ℝ) → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ v, F v = ∫⁻ a, ∫⁻ b, ∫⁻ c, ∫⁻ d, F ![a, b, c, d] := by
  have h0 : ∀ G : (Fin 0 → ℝ) → ℝ≥0∞, ∫⁻ w, G w = G ![] := by
    intro G
    rw [show (volume : Measure (Fin 0 → ℝ)) = Measure.pi fun _ => volume from rfl,
      Measure.pi_of_empty (x := ![]), lintegral_dirac]
  rw [lintegral_fin_cons 3 F hF]
  refine lintegral_congr fun a => ?_
  rw [lintegral_fin_cons 2 (fun w => F (Fin.cons a w)) (hF.comp (measurable_cons a 3))]
  refine lintegral_congr fun b => ?_
  rw [lintegral_fin_cons 1 (fun w => F (Fin.cons a (Fin.cons b w)))
    ((hF.comp (measurable_cons a 3)).comp (measurable_cons b 2))]
  refine lintegral_congr fun c => ?_
  rw [lintegral_fin_cons 0 (fun w => F (Fin.cons a (Fin.cons b (Fin.cons c w))))
    (((hF.comp (measurable_cons a 3)).comp (measurable_cons b 2)).comp (measurable_cons c 1))]
  refine lintegral_congr fun d => ?_
  rw [h0]
  rfl

/-- Auxiliary: `p_1` is measurable. -/
theorem measurable_phi1 : Measurable fun r => ENNReal.ofReal (phi 1 r) :=
  ENNReal.measurable_ofReal.comp (continuous_phi 1).measurable

/-- Auxiliary: integrating out the closers `1, 3` of `A`. -/
theorem lintegral_A (Φ : ℝ → ℝ → ℝ≥0∞) (hΦ : Measurable fun p : ℝ × ℝ => Φ p.1 p.2) :
    ∫⁻ v : Fin 4 → ℝ, Φ (v 0) (v 2) *
        (ENNReal.ofReal (phi 1 (v 1)) * ENNReal.ofReal (phi 1 (v 3))) =
      ∫⁻ p : ℝ × ℝ, Φ p.1 p.2 := by
  have hΦa : ∀ a, Measurable (Φ a) := fun a => hΦ.comp (measurable_const.prodMk measurable_id)
  have hm : Measurable fun v : Fin 4 → ℝ => Φ (v 0) (v 2) *
      (ENNReal.ofReal (phi 1 (v 1)) * ENNReal.ofReal (phi 1 (v 3))) := by
    have m0 : Measurable fun v : Fin 4 → ℝ => Φ (v 0) (v 2) :=
      hΦ.comp (f := fun v : Fin 4 → ℝ => (v 0, v 2))
        ((measurable_pi_apply 0).prodMk (measurable_pi_apply 2))
    have m1 : Measurable fun v : Fin 4 → ℝ => ENNReal.ofReal (phi 1 (v 1)) :=
      measurable_phi1.comp (measurable_pi_apply 1)
    have m2 : Measurable fun v : Fin 4 → ℝ => ENNReal.ofReal (phi 1 (v 3)) :=
      measurable_phi1.comp (measurable_pi_apply 3)
    exact m0.mul (m1.mul m2)
  calc ∫⁻ v : Fin 4 → ℝ, Φ (v 0) (v 2) *
        (ENNReal.ofReal (phi 1 (v 1)) * ENNReal.ofReal (phi 1 (v 3)))
      = ∫⁻ a, ∫⁻ b, ∫⁻ c, ∫⁻ d, Φ a c *
          (ENNReal.ofReal (phi 1 b) * ENNReal.ofReal (phi 1 d)) := lintegral_fin4 _ hm
    _ = ∫⁻ a, ∫⁻ b, ∫⁻ c, Φ a c * ENNReal.ofReal (phi 1 b) := by
        refine lintegral_congr fun a => lintegral_congr fun b => lintegral_congr fun c => ?_
        simp_rw [← mul_assoc]
        rw [lintegral_const_mul _ measurable_phi1, lintegral_phi_one, mul_one]
    _ = ∫⁻ a, ∫⁻ c, Φ a c := by
        refine lintegral_congr fun a => ?_
        simp_rw [lintegral_mul_const _ (hΦa a)]
        rw [lintegral_const_mul _ measurable_phi1, lintegral_phi_one, mul_one]
    _ = ∫⁻ p : ℝ × ℝ, Φ p.1 p.2 := by
        rw [Measure.volume_eq_prod, lintegral_prod _ hΦ.aemeasurable]

/-- Auxiliary: integrating out the closers `2, 3` of `B` and `C`. -/
theorem lintegral_BC (Φ : ℝ → ℝ → ℝ≥0∞) (hΦ : Measurable fun p : ℝ × ℝ => Φ p.1 p.2) :
    ∫⁻ v : Fin 4 → ℝ, Φ (v 0) (v 1) *
        (ENNReal.ofReal (phi 1 (v 2)) * ENNReal.ofReal (phi 1 (v 3))) =
      ∫⁻ p : ℝ × ℝ, Φ p.1 p.2 := by
  have hm : Measurable fun v : Fin 4 → ℝ => Φ (v 0) (v 1) *
      (ENNReal.ofReal (phi 1 (v 2)) * ENNReal.ofReal (phi 1 (v 3))) := by
    have m0 : Measurable fun v : Fin 4 → ℝ => Φ (v 0) (v 1) :=
      hΦ.comp (f := fun v : Fin 4 → ℝ => (v 0, v 1))
        ((measurable_pi_apply 0).prodMk (measurable_pi_apply 1))
    have m1 : Measurable fun v : Fin 4 → ℝ => ENNReal.ofReal (phi 1 (v 2)) :=
      measurable_phi1.comp (measurable_pi_apply 2)
    have m2 : Measurable fun v : Fin 4 → ℝ => ENNReal.ofReal (phi 1 (v 3)) :=
      measurable_phi1.comp (measurable_pi_apply 3)
    exact m0.mul (m1.mul m2)
  calc ∫⁻ v : Fin 4 → ℝ, Φ (v 0) (v 1) *
        (ENNReal.ofReal (phi 1 (v 2)) * ENNReal.ofReal (phi 1 (v 3)))
      = ∫⁻ a, ∫⁻ b, ∫⁻ c, ∫⁻ d, Φ a b *
          (ENNReal.ofReal (phi 1 c) * ENNReal.ofReal (phi 1 d)) := lintegral_fin4 _ hm
    _ = ∫⁻ a, ∫⁻ b, Φ a b := by
        refine lintegral_congr fun a => lintegral_congr fun b => ?_
        have : ∀ c, ∫⁻ d, Φ a b * (ENNReal.ofReal (phi 1 c) * ENNReal.ofReal (phi 1 d)) =
            Φ a b * ENNReal.ofReal (phi 1 c) := by
          intro c
          simp_rw [← mul_assoc]
          rw [lintegral_const_mul _ measurable_phi1, lintegral_phi_one, mul_one]
        simp_rw [this]
        rw [lintegral_const_mul _ measurable_phi1, lintegral_phi_one, mul_one]
    _ = ∫⁻ p : ℝ × ℝ, Φ p.1 p.2 := by
        rw [Measure.volume_eq_prod, lintegral_prod _ hΦ.aemeasurable]

/-! ### The Green products of four labels -/

/-- Auxiliary: the Green product for the chains `(0,4)` (and `(4,0)`). -/
theorem greenProd_m0 (h y : Fin 4 → ℝ) : greenProd 0 h y =
    g1 (h 0) (y 0) * g1 (h 1) (y 1 - y 0) * g1 (h 2) (y 2 - y 1) * g1 (h 3) (y 3 - y 2) := by
  simp [greenProd, Fin.prod_univ_four, predVal, pred]

/-- Auxiliary: the Green product for the chains `(1,3)`. -/
theorem greenProd_m1 (h y : Fin 4 → ℝ) : greenProd 1 h y =
    g1 (h 0) (y 0) * g1 (h 1) (y 1) * g1 (h 2) (y 2 - y 1) * g1 (h 3) (y 3 - y 2) := by
  simp [greenProd, Fin.prod_univ_four, predVal, pred]

/-- Auxiliary: the Green product for the chains `(2,2)`. -/
theorem greenProd_m2 (h y : Fin 4 → ℝ) : greenProd 2 h y =
    g1 (h 0) (y 0) * g1 (h 1) (y 1 - y 0) * g1 (h 2) (y 2) * g1 (h 3) (y 3 - y 2) := by
  simp [greenProd, Fin.prod_univ_four, predVal, pred]

/-- Auxiliary: the Green product for the chains `(3,1)`. -/
theorem greenProd_m3 (h y : Fin 4 → ℝ) : greenProd 3 h y =
    g1 (h 0) (y 0) * g1 (h 1) (y 1 - y 0) * g1 (h 2) (y 2 - y 1) * g1 (h 3) (y 3) := by
  simp [greenProd, Fin.prod_univ_four, predVal, pred]

/-- Auxiliary: `g = ½ · 1{|r| < s}`. -/
theorem g1_eq (s r : ℝ) : g1 s r = ENNReal.ofReal (1 / 2) * (if |r| < s then 1 else 0) := by
  unfold g1; split_ifs <;> simp

/-- Auxiliary: a product of four indicator values. -/
theorem prod4 (c1 c2 c3 c4 : Prop) [Decidable c1] [Decidable c2] [Decidable c3] [Decidable c4] :
    (if c1 then (1 : ℝ≥0∞) else 0) * (if c2 then 1 else 0) * (if c3 then 1 else 0) *
      (if c4 then 1 else 0) = if c1 ∧ c2 ∧ c3 ∧ c4 then 1 else 0 := by
  by_cases h1 : c1 <;> by_cases h2 : c2 <;> by_cases h3 : c3 <;> by_cases h4 : c4 <;>
    simp [h1, h2, h3, h4]

/-- Auxiliary: four Green factors give `1/16` times an indicator ("spatial
integration leaves `1/16` times the area", main TeX lines 4995-4996). -/
theorem g1prod4 (a b c d r1 r2 r3 r4 : ℝ) :
    g1 a r1 * g1 b r2 * g1 c r3 * g1 d r4 = ENNReal.ofReal (1 / 16) *
      (if |r1| < a ∧ |r2| < b ∧ |r3| < c ∧ |r4| < d then 1 else 0) := by
  simp only [g1_eq]
  rw [← prod4, show ENNReal.ofReal (1 / 16) = ENNReal.ofReal (1 / 2) ^ 4 by
    rw [← ENNReal.ofReal_pow (by norm_num)]; norm_num]
  ring

/-! ### The three area shapes and `E:interval-area` -/

/-- The strip `{|x| < p, |y - x| < q}` (area `4pq`). -/
def strip (p q : ℝ) : Set (ℝ × ℝ) := {z | |z.1| < p ∧ |z.2 - z.1| < q}

/-- The rectangle `{|x| < p, |y| < q}` (area `4pq`). -/
def box (p q : ℝ) : Set (ℝ × ℝ) := {z | |z.1| < p ∧ |z.2| < q}

/-- The region `{|x| < p, |y| < q, |x - y| < w}` of `E:interval-area`. -/
def tri (p q w : ℝ) : Set (ℝ × ℝ) := {z | |z.1| < p ∧ |z.2| < q ∧ |z.1 - z.2| < w}

theorem measurableSet_strip (p q : ℝ) : MeasurableSet (strip p q) :=
  (measurableSet_lt measurable_fst.abs measurable_const).inter
    (measurableSet_lt (measurable_snd.sub measurable_fst).abs measurable_const)

theorem measurableSet_box (p q : ℝ) : MeasurableSet (box p q) :=
  (measurableSet_lt measurable_fst.abs measurable_const).inter
    (measurableSet_lt measurable_snd.abs measurable_const)

theorem measurableSet_tri (p q w : ℝ) : MeasurableSet (tri p q w) :=
  (measurableSet_lt measurable_fst.abs measurable_const).inter
    ((measurableSet_lt measurable_snd.abs measurable_const).inter
      (measurableSet_lt (measurable_fst.sub measurable_snd).abs measurable_const))

/-- The area of the strip. -/
theorem volume_strip (p q : ℝ) :
    volume (strip p q) = ENNReal.ofReal (2 * p) * ENNReal.ofReal (2 * q) := by
  rw [Measure.volume_eq_prod, Measure.prod_apply (measurableSet_strip p q)]
  have hsl : ∀ x : ℝ, volume (Prod.mk x ⁻¹' strip p q) =
      (Metric.ball (0 : ℝ) p).indicator (fun _ => ENNReal.ofReal (2 * q)) x := by
    intro x
    by_cases hx : |x| < p
    · rw [Set.indicator_of_mem (by simpa [Real.dist_eq] using hx)]
      have : Prod.mk x ⁻¹' strip p q = Metric.ball x q := by
        ext y; simp [strip, hx, Real.dist_eq]
      rw [this, Real.volume_ball]
    · rw [Set.indicator_of_notMem (by simpa [Real.dist_eq] using hx)]
      have : Prod.mk x ⁻¹' strip p q = ∅ := by ext y; simp [strip, hx]
      rw [this, measure_empty]
  simp_rw [hsl]
  rw [lintegral_indicator_const Metric.isOpen_ball.measurableSet, Real.volume_ball, mul_comm]

/-- The area of the rectangle. -/
theorem volume_box (p q : ℝ) :
    volume (box p q) = ENNReal.ofReal (2 * p) * ENNReal.ofReal (2 * q) := by
  rw [Measure.volume_eq_prod, Measure.prod_apply (measurableSet_box p q)]
  have hsl : ∀ x : ℝ, volume (Prod.mk x ⁻¹' box p q) =
      (Metric.ball (0 : ℝ) p).indicator (fun _ => ENNReal.ofReal (2 * q)) x := by
    intro x
    by_cases hx : |x| < p
    · rw [Set.indicator_of_mem (by simpa [Real.dist_eq] using hx)]
      have : Prod.mk x ⁻¹' box p q = Metric.ball 0 q := by
        ext y; simp [box, hx]
      rw [this, Real.volume_ball]
    · rw [Set.indicator_of_notMem (by simpa [Real.dist_eq] using hx)]
      have : Prod.mk x ⁻¹' box p q = ∅ := by ext y; simp [box, hx]
      rw [this, measure_empty]
  simp_rw [hsl]
  rw [lintegral_indicator_const Metric.isOpen_ball.measurableSet, Real.volume_ball, mul_comm]

/-- `E:interval-area` (main TeX line 4925):
`F(a,b,c) = 4ab - (a+b-c)_+² + (|a-b|-c)_+²`. -/
def F (a b c : ℝ) : ℝ := 4 * a * b - max (a + b - c) 0 ^ 2 + max (|a - b| - c) 0 ^ 2

/-- `F` is symmetric in its first two arguments (main TeX line 4928). -/
theorem F_comm (a b c : ℝ) : F a b c = F b a c := by
  unfold F; rw [abs_sub_comm, add_comm a b]; ring

/-- Auxiliary: `(u)_+² = (u² + u|u|)/2`. -/
theorem sq_max (u : ℝ) : max u 0 ^ 2 = (u ^ 2 + u * |u|) / 2 := by
  rcases le_total 0 u with h | h
  · rw [max_eq_left h, abs_of_nonneg h]; ring
  · rw [max_eq_right h, abs_of_nonpos h]; ring

/-- Auxiliary: the interval-overlap length as a sum of four ramps. -/
theorem ramp_pointwise {q w : ℝ} (hq : 0 < q) (hw : 0 < w) (x : ℝ) :
    max (min q (x + w) - max (-q) (x - w)) 0 =
      max (x + (q + w)) 0 - max (x + (q - w)) 0 - max (x + (w - q)) 0 +
        max (x + (-q - w)) 0 := by
  simp only [max_def, min_def]
  split_ifs <;> linarith

/-- Auxiliary: `∫_{-p}^{p} (x + c)_+ dx = ((p+c)_+² - (c-p)_+²)/2`. -/
theorem integral_ramp {p : ℝ} (hp : 0 ≤ p) (c : ℝ) :
    ∫ x in -p..p, max (x + c) 0 = (max (p + c) 0 ^ 2 - max (c - p) 0 ^ 2) / 2 := by
  have hlin : ∀ a b : ℝ, ∫ x in a..b, (x + c) = ((b + c) ^ 2 - (a + c) ^ 2) / 2 := by
    intro a b
    rw [intervalIntegral.integral_comp_add_right (fun x => x), integral_id]
  rcases le_total p c with h1 | h1
  · rw [intervalIntegral.integral_congr (g := fun x => x + c) (fun x hx => by
      rw [Set.uIcc_of_le (by linarith)] at hx; exact max_eq_left (by linarith [hx.1])),
      hlin, max_eq_left (by linarith), max_eq_left (by linarith)]
    ring
  rcases le_total c (-p) with h2 | h2
  · rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) (fun x hx => by
      rw [Set.uIcc_of_le (by linarith)] at hx; exact max_eq_right (by linarith [hx.2])),
      intervalIntegral.integral_zero, max_eq_right (by linarith), max_eq_right (by linarith)]
    ring
  · have hc1 : IntervalIntegrable (fun x => max (x + c) 0) volume (-p) (-c) :=
      (by fun_prop : Continuous fun x : ℝ => max (x + c) 0).intervalIntegrable _ _
    have hc2 : IntervalIntegrable (fun x => max (x + c) 0) volume (-c) p :=
      (by fun_prop : Continuous fun x : ℝ => max (x + c) 0).intervalIntegrable _ _
    rw [← intervalIntegral.integral_add_adjacent_intervals hc1 hc2,
      intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) (a := -p) (b := -c) (fun x hx => by
        rw [Set.uIcc_of_le (by linarith)] at hx; exact max_eq_right (by linarith [hx.2])),
      intervalIntegral.integral_congr (g := fun x => x + c) (a := -c) (b := p) (fun x hx => by
        rw [Set.uIcc_of_le (by linarith)] at hx; exact max_eq_left (by linarith [hx.1])),
      intervalIntegral.integral_zero, hlin, max_eq_left (by linarith), max_eq_right (by linarith)]
    ring

/-- Auxiliary: the four ramp integrals add up to `F`. -/
theorem F_formula {p q w : ℝ} (hp : 0 < p) (hq : 0 < q) (hw : 0 < w) :
    (max (p + (q + w)) 0 ^ 2 - max ((q + w) - p) 0 ^ 2) / 2
      - (max (p + (q - w)) 0 ^ 2 - max ((q - w) - p) 0 ^ 2) / 2
      - (max (p + (w - q)) 0 ^ 2 - max ((w - q) - p) 0 ^ 2) / 2
      + (max (p + (-q - w)) 0 ^ 2 - max ((-q - w) - p) 0 ^ 2) / 2 = F p q w := by
  unfold F
  simp only [sq_max]
  rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ p + (q + w)),
    abs_of_nonpos (by linarith : (-q - w) - p ≤ 0)]
  rcases le_total p q with hpq | hpq
  · rw [abs_of_nonpos (by linarith : p - q ≤ 0),
      abs_of_nonneg (by linarith : (0:ℝ) ≤ (q + w) - p),
      abs_of_nonpos (by linarith : p + (-q - w) ≤ 0)]
    rcases le_total 0 (p + q - w) with h2 | h2 <;> rcases le_total 0 (p + w - q) with h3 | h3
    · rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ p + (q - w)),
        abs_of_nonpos (by linarith : (w - q) - p ≤ 0), abs_of_nonneg h2,
        abs_of_nonneg (by linarith : (0:ℝ) ≤ p + (w - q)),
        abs_of_nonpos (by linarith : (q - w) - p ≤ 0),
        abs_of_nonpos (by linarith : -(p - q) - w ≤ 0)]
      ring
    · rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ p + (q - w)),
        abs_of_nonpos (by linarith : (w - q) - p ≤ 0), abs_of_nonneg h2,
        abs_of_nonpos (by linarith : p + (w - q) ≤ 0),
        abs_of_nonneg (by linarith : (0:ℝ) ≤ (q - w) - p),
        abs_of_nonneg (by linarith : (0:ℝ) ≤ -(p - q) - w)]
      ring
    · rw [abs_of_nonpos (by linarith : p + (q - w) ≤ 0),
        abs_of_nonneg (by linarith : (0:ℝ) ≤ (w - q) - p), abs_of_nonpos h2,
        abs_of_nonneg (by linarith : (0:ℝ) ≤ p + (w - q)),
        abs_of_nonpos (by linarith : (q - w) - p ≤ 0),
        abs_of_nonpos (by linarith : -(p - q) - w ≤ 0)]
      ring
    · exfalso; linarith
  · rw [abs_of_nonneg (by linarith : 0 ≤ p - q),
      abs_of_nonneg (by linarith : (0:ℝ) ≤ p + (w - q)),
      abs_of_nonpos (by linarith : (q - w) - p ≤ 0)]
    rcases le_total 0 (p + q - w) with h2 | h2 <;> rcases le_total 0 (q + w - p) with h1 | h1
    · rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ p + (q - w)),
        abs_of_nonpos (by linarith : (w - q) - p ≤ 0), abs_of_nonneg h2,
        abs_of_nonneg (by linarith : (0:ℝ) ≤ (q + w) - p),
        abs_of_nonpos (by linarith : p + (-q - w) ≤ 0),
        abs_of_nonpos (by linarith : p - q - w ≤ 0)]
      ring
    · rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ p + (q - w)),
        abs_of_nonpos (by linarith : (w - q) - p ≤ 0), abs_of_nonneg h2,
        abs_of_nonpos (by linarith : (q + w) - p ≤ 0),
        abs_of_nonneg (by linarith : (0:ℝ) ≤ p + (-q - w)),
        abs_of_nonneg (by linarith : (0:ℝ) ≤ p - q - w)]
      ring
    · rw [abs_of_nonpos (by linarith : p + (q - w) ≤ 0),
        abs_of_nonneg (by linarith : (0:ℝ) ≤ (w - q) - p), abs_of_nonpos h2,
        abs_of_nonneg (by linarith : (0:ℝ) ≤ (q + w) - p),
        abs_of_nonpos (by linarith : p + (-q - w) ≤ 0),
        abs_of_nonpos (by linarith : p - q - w ≤ 0)]
      ring
    · exfalso; linarith

/-- Auxiliary: `ofReal r = ofReal r_+`. -/
theorem ofReal_eq_ofReal_max (r : ℝ) : ENNReal.ofReal r = ENNReal.ofReal (max r 0) := by
  rcases le_total r 0 with h | h
  · rw [max_eq_right h, ENNReal.ofReal_of_nonpos h, ENNReal.ofReal_zero]
  · rw [max_eq_left h]

/-- **`E:interval-area`** (main TeX lines 4923-4935): for `a, b, c > 0` the area
of `{(x,y) : |x| < a, |y| < b, |x - y| < c}` is `F(a,b,c)`. -/
theorem volume_tri {p q w : ℝ} (hp : 0 < p) (hq : 0 < q) (hw : 0 < w) :
    volume (tri p q w) = ENNReal.ofReal (F p q w) := by
  rw [Measure.volume_eq_prod, Measure.prod_apply (measurableSet_tri p q w)]
  set L : ℝ → ℝ := fun x => min q (x + w) - max (-q) (x - w) with hL
  have hsl : ∀ x : ℝ, volume (Prod.mk x ⁻¹' tri p q w) =
      (Metric.ball (0 : ℝ) p).indicator (fun x => ENNReal.ofReal (L x)) x := by
    intro x
    by_cases hx : |x| < p
    · rw [Set.indicator_of_mem (by simpa [Real.dist_eq] using hx)]
      have : Prod.mk x ⁻¹' tri p q w = Set.Ioo (max (-q) (x - w)) (min q (x + w)) := by
        ext y
        simp only [Set.mem_preimage, tri, Set.mem_ofPred_eq, hx, true_and, Set.mem_Ioo,
          max_lt_iff, lt_min_iff]
        simp only [abs_lt]
        constructor <;> intro h <;> refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;>
          linarith [h.1.1, h.1.2, h.2.1, h.2.2]
      rw [this, Real.volume_Ioo]
    · rw [Set.indicator_of_notMem (by simpa [Real.dist_eq] using hx)]
      have : Prod.mk x ⁻¹' tri p q w = ∅ := by ext y; simp [tri, hx]
      rw [this, measure_empty]
  simp_rw [hsl]
  have hball : Metric.ball (0 : ℝ) p = Set.Ioo (-p) p := by
    rw [Real.ball_eq_Ioo]; simp
  have hcont : Continuous fun x => max (L x) 0 := by simp only [hL]; fun_prop
  rw [lintegral_indicator Metric.isOpen_ball.measurableSet, hball]
  simp_rw [ofReal_eq_ofReal_max (L _)]
  rw [← ofReal_integral_eq_lintegral_ofReal
      ((hcont.integrableOn_Icc).mono_set Set.Ioo_subset_Icc_self)
      (ae_of_all _ fun x => le_max_right _ _),
    ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by linarith)]
  congr 1
  rw [intervalIntegral.integral_congr (g := fun x => max (x + (q + w)) 0 - max (x + (q - w)) 0 -
      max (x + (w - q)) 0 + max (x + (-q - w)) 0) (fun x _ => ramp_pointwise hq hw x)]
  have hi : ∀ c : ℝ, IntervalIntegrable (fun x => max (x + c) 0) volume (-p) p :=
    fun c => (by fun_prop : Continuous fun x : ℝ => max (x + c) 0).intervalIntegrable _ _
  rw [intervalIntegral.integral_add (((hi _).sub (hi _)).sub (hi _)) (hi _),
    intervalIntegral.integral_sub ((hi _).sub (hi _)) (hi _),
    intervalIntegral.integral_sub (hi _) (hi _), integral_ramp hp.le, integral_ramp hp.le,
    integral_ramp hp.le, integral_ramp hp.le, F_formula hp hq hw]

/-! ### The collapsed spatial factors -/

/-- Auxiliary: the collapsed spatial factor under `A` as `1/16` times an area. -/
theorem whiteSpatial_eq_A (m : ℕ) (h : Fin 4 → ℝ) (S : Set (ℝ × ℝ)) (hS : MeasurableSet S)
    (hG : ∀ v : Fin 4 → ℝ, greenProd m h (fun i => v (opener pA i)) =
      ENNReal.ofReal (1 / 16) * S.indicator 1 (v 0, v 2)) :
    whiteSpatial m pA h = ENNReal.ofReal (1 / 16) * volume S := by
  unfold whiteSpatial
  simp_rw [hG, gaussW_pA]
  rw [lintegral_A (fun x y => ENNReal.ofReal (1 / 16) * S.indicator 1 (x, y))
    (measurable_const.mul (measurable_one.indicator hS))]
  simp only [Prod.mk.eta]
  rw [lintegral_const_mul _ (measurable_one.indicator hS), lintegral_indicator_one hS]

/-- Auxiliary: the collapsed spatial factor under `B` as `1/16` times an area. -/
theorem whiteSpatial_eq_B (m : ℕ) (h : Fin 4 → ℝ) (S : Set (ℝ × ℝ)) (hS : MeasurableSet S)
    (hG : ∀ v : Fin 4 → ℝ, greenProd m h (fun i => v (opener pB i)) =
      ENNReal.ofReal (1 / 16) * S.indicator 1 (v 0, v 1)) :
    whiteSpatial m pB h = ENNReal.ofReal (1 / 16) * volume S := by
  unfold whiteSpatial
  simp_rw [hG, gaussW_pB]
  rw [lintegral_BC (fun x y => ENNReal.ofReal (1 / 16) * S.indicator 1 (x, y))
    (measurable_const.mul (measurable_one.indicator hS))]
  simp only [Prod.mk.eta]
  rw [lintegral_const_mul _ (measurable_one.indicator hS), lintegral_indicator_one hS]

/-- Auxiliary: the collapsed spatial factor under `C` as `1/16` times an area. -/
theorem whiteSpatial_eq_C (m : ℕ) (h : Fin 4 → ℝ) (S : Set (ℝ × ℝ)) (hS : MeasurableSet S)
    (hG : ∀ v : Fin 4 → ℝ, greenProd m h (fun i => v (opener pC i)) =
      ENNReal.ofReal (1 / 16) * S.indicator 1 (v 0, v 1)) :
    whiteSpatial m pC h = ENNReal.ofReal (1 / 16) * volume S := by
  unfold whiteSpatial
  simp_rw [hG, gaussW_pC]
  rw [lintegral_BC (fun x y => ENNReal.ofReal (1 / 16) * S.indicator 1 (x, y))
    (measurable_const.mul (measurable_one.indicator hS))]
  simp only [Prod.mk.eta]
  rw [lintegral_const_mul _ (measurable_one.indicator hS), lintegral_indicator_one hS]

/-- Auxiliary: `(1/16) · 2p · 2q = pq/4`. -/
theorem area_quarter {p : ℝ} (hp : 0 ≤ p) (q : ℝ) :
    ENNReal.ofReal (1 / 16) * (ENNReal.ofReal (2 * p) * ENNReal.ofReal (2 * q)) =
      ENNReal.ofReal (p * q / 4) := by
  rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by norm_num)]
  congr 1; ring

/-- Auxiliary: `(1/16) F = F/16`. -/
theorem area_F {p q w : ℝ} (hp : 0 < p) (hq : 0 < q) (hw : 0 < w) :
    ENNReal.ofReal (1 / 16) * volume (tri p q w) = ENNReal.ofReal (F p q w / 16) := by
  rw [volume_tri hp hq hw, ← ENNReal.ofReal_mul (by norm_num)]
  congr 1; ring

section rows

variable {h : Fin 4 → ℝ}

/-- Row `(0,4), A`: `V = ac/4` (positions `(x,x,y,y)`, area `4ac`). -/
theorem whiteSpatial_04A (hh : ∀ i, 0 < h i) :
    whiteSpatial 0 pA h = ENNReal.ofReal (h 0 * h 2 / 4) := by
  classical
  rw [whiteSpatial_eq_A 0 h (strip (h 0) (h 2)) (measurableSet_strip _ _) (fun v => ?_),
    volume_strip, area_quarter (hh 0).le _]
  rw [opener_pA, greenProd_m0, g1prod4, Set.indicator_apply]
  congr 1
  refine if_congr ?_ rfl rfl
  simp [strip, hh 1, hh 3]

/-- Row `(0,4), B`: `V = a min(b,c,d)/4` (positions `(x,y,x,y)`). -/
theorem whiteSpatial_04B (hh : ∀ i, 0 < h i) :
    whiteSpatial 0 pB h = ENNReal.ofReal (h 0 * min (h 1) (min (h 2) (h 3)) / 4) := by
  classical
  rw [whiteSpatial_eq_B 0 h (strip (h 0) (min (h 1) (min (h 2) (h 3)))) (measurableSet_strip _ _)
    (fun v => ?_), volume_strip, area_quarter (hh 0).le _]
  rw [opener_pB, greenProd_m0, g1prod4, Set.indicator_apply]
  congr 1
  refine if_congr ?_ rfl rfl
  simp only [strip, Set.mem_ofPred_eq, lt_min_iff]
  simp [abs_sub_comm (v 0) (v 1)]

/-- Row `(0,4), C`: `V = a min(b,d)/4` (positions `(x,y,y,x)`). -/
theorem whiteSpatial_04C (hh : ∀ i, 0 < h i) :
    whiteSpatial 0 pC h = ENNReal.ofReal (h 0 * min (h 1) (h 3) / 4) := by
  classical
  rw [whiteSpatial_eq_C 0 h (strip (h 0) (min (h 1) (h 3))) (measurableSet_strip _ _)
    (fun v => ?_), volume_strip, area_quarter (hh 0).le _]
  rw [opener_pC, greenProd_m0, g1prod4, Set.indicator_apply]
  congr 1
  refine if_congr ?_ rfl rfl
  simp only [strip, Set.mem_ofPred_eq, lt_min_iff]
  simp [abs_sub_comm (v 0) (v 1), hh 2]

/-- Row `(1,3), A`: `V = min(r,a) b/4`. -/
theorem whiteSpatial_13A (hh : ∀ i, 0 < h i) :
    whiteSpatial 1 pA h = ENNReal.ofReal (min (h 0) (h 1) * h 2 / 4) := by
  classical
  rw [whiteSpatial_eq_A 1 h (strip (min (h 0) (h 1)) (h 2)) (measurableSet_strip _ _)
    (fun v => ?_), volume_strip, area_quarter (le_min (hh 0).le (hh 1).le) _]
  rw [opener_pA, greenProd_m1, g1prod4, Set.indicator_apply]
  congr 1
  refine if_congr ?_ rfl rfl
  simp only [strip, Set.mem_ofPred_eq, lt_min_iff]
  simp [hh 3, and_assoc]

/-- Row `(1,3), B`: `V = F(r, a, min(b,c))/16`. -/
theorem whiteSpatial_13B (hh : ∀ i, 0 < h i) :
    whiteSpatial 1 pB h = ENNReal.ofReal (F (h 0) (h 1) (min (h 2) (h 3)) / 16) := by
  classical
  rw [whiteSpatial_eq_B 1 h (tri (h 0) (h 1) (min (h 2) (h 3))) (measurableSet_tri _ _ _)
    (fun v => ?_), area_F (hh 0) (hh 1) (lt_min (hh 2) (hh 3))]
  rw [opener_pB, greenProd_m1, g1prod4, Set.indicator_apply]
  congr 1
  refine if_congr ?_ rfl rfl
  simp only [tri, Set.mem_ofPred_eq, lt_min_iff]
  simp [abs_sub_comm (v 0) (v 1)]

/-- Row `(1,3), C`: `V = F(r, a, c)/16`. -/
theorem whiteSpatial_13C (hh : ∀ i, 0 < h i) :
    whiteSpatial 1 pC h = ENNReal.ofReal (F (h 0) (h 1) (h 3) / 16) := by
  classical
  rw [whiteSpatial_eq_C 1 h (tri (h 0) (h 1) (h 3)) (measurableSet_tri _ _ _)
    (fun v => ?_), area_F (hh 0) (hh 1) (hh 3)]
  rw [opener_pC, greenProd_m1, g1prod4, Set.indicator_apply]
  congr 1
  refine if_congr ?_ rfl rfl
  simp [tri, hh 2]

/-- Row `(2,2), A`: `V = ac/4` (positions `(x,x),(y,y)`). -/
theorem whiteSpatial_22A (hh : ∀ i, 0 < h i) :
    whiteSpatial 2 pA h = ENNReal.ofReal (h 0 * h 2 / 4) := by
  classical
  rw [whiteSpatial_eq_A 2 h (box (h 0) (h 2)) (measurableSet_box _ _) (fun v => ?_),
    volume_box, area_quarter (hh 0).le _]
  rw [opener_pA, greenProd_m2, g1prod4, Set.indicator_apply]
  congr 1
  refine if_congr ?_ rfl rfl
  simp [box, hh 1, hh 3]

/-- Row `(2,2), B`: `V = min(a,c) min(b,d)/4` (positions `(x,y),(x,y)`). -/
theorem whiteSpatial_22B (hh : ∀ i, 0 < h i) :
    whiteSpatial 2 pB h = ENNReal.ofReal (min (h 0) (h 2) * min (h 1) (h 3) / 4) := by
  classical
  rw [whiteSpatial_eq_B 2 h (strip (min (h 0) (h 2)) (min (h 1) (h 3))) (measurableSet_strip _ _)
    (fun v => ?_), volume_strip, area_quarter (le_min (hh 0).le (hh 2).le) _]
  rw [opener_pB, greenProd_m2, g1prod4, Set.indicator_apply]
  congr 1
  refine if_congr ?_ rfl rfl
  simp only [strip, Set.mem_ofPred_eq, lt_min_iff]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  tauto

/-- Row `(2,2), C`: `V = F(a, c, min(b,d))/16` (positions `(x,y),(y,x)`). -/
theorem whiteSpatial_22C (hh : ∀ i, 0 < h i) :
    whiteSpatial 2 pC h = ENNReal.ofReal (F (h 0) (h 2) (min (h 1) (h 3)) / 16) := by
  classical
  rw [whiteSpatial_eq_C 2 h (tri (h 0) (h 2) (min (h 1) (h 3))) (measurableSet_tri _ _ _)
    (fun v => ?_), area_F (hh 0) (hh 2) (lt_min (hh 1) (hh 3))]
  rw [opener_pC, greenProd_m2, g1prod4, Set.indicator_apply]
  congr 1
  refine if_congr ?_ rfl rfl
  simp only [tri, Set.mem_ofPred_eq, lt_min_iff]
  simp [abs_sub_comm (v 0) (v 1)]
  tauto

/-- Row `(3,1), A` (the exchange of `(1,3), C`): `V = F(a, r, c)/16` with
`h = (a, b, c, r)`. -/
theorem whiteSpatial_31A (hh : ∀ i, 0 < h i) :
    whiteSpatial 3 pA h = ENNReal.ofReal (F (h 0) (h 3) (h 2) / 16) := by
  classical
  rw [whiteSpatial_eq_A 3 h (tri (h 0) (h 3) (h 2)) (measurableSet_tri _ _ _)
    (fun v => ?_), area_F (hh 0) (hh 3) (hh 2)]
  rw [opener_pA, greenProd_m3, g1prod4, Set.indicator_apply]
  congr 1
  refine if_congr ?_ rfl rfl
  simp [tri, hh 1, abs_sub_comm (v 0) (v 2)]
  tauto

/-- Row `(3,1), B` (the exchange of `(1,3), B`): `V = F(a, r, min(b,c))/16`. -/
theorem whiteSpatial_31B (hh : ∀ i, 0 < h i) :
    whiteSpatial 3 pB h = ENNReal.ofReal (F (h 0) (h 3) (min (h 1) (h 2)) / 16) := by
  classical
  rw [whiteSpatial_eq_B 3 h (tri (h 0) (h 3) (min (h 1) (h 2))) (measurableSet_tri _ _ _)
    (fun v => ?_), area_F (hh 0) (hh 3) (lt_min (hh 1) (hh 2))]
  rw [opener_pB, greenProd_m3, g1prod4, Set.indicator_apply]
  congr 1
  refine if_congr ?_ rfl rfl
  simp only [tri, Set.mem_ofPred_eq, lt_min_iff]
  simp [abs_sub_comm (v 0) (v 1)]
  tauto

/-- Row `(3,1), C` (the exchange of `(1,3), A`): `V = min(a, r) b/4`. -/
theorem whiteSpatial_31C (hh : ∀ i, 0 < h i) :
    whiteSpatial 3 pC h = ENNReal.ofReal (min (h 0) (h 3) * h 1 / 4) := by
  classical
  rw [whiteSpatial_eq_C 3 h (strip (min (h 0) (h 3)) (h 1)) (measurableSet_strip _ _)
    (fun v => ?_), volume_strip, area_quarter (le_min (hh 0).le (hh 3).le) _]
  rw [opener_pC, greenProd_m3, g1prod4, Set.indicator_apply]
  congr 1
  refine if_congr ?_ rfl rfl
  simp only [strip, Set.mem_ofPred_eq, lt_min_iff]
  simp [hh 2]
  tauto

end rows

/-! ### From the time simplices to the increment variables -/

/-- Auxiliary: the increment map preserves Lebesgue measure (determinant one,
`DiagramBridge.measurePreserving_incrMatrix`). -/
theorem measurePreserving_incr (m N : ℕ) : MeasurePreserving (incr m (N := N)) volume volume := by
  have h1 := DiagramBridge.measurePreserving_incrMatrix m N
  have h2 : (Matrix.toLin' (DiagramBridge.incrMatrix m N) : (Fin N → ℝ) → Fin N → ℝ) =
      incr m := by
    funext v
    rw [Matrix.toLin'_apply]
    exact DiagramBridge.incrMatrix_mulVec m N v
  rwa [h2] at h1

/-- Auxiliary: a white-noise diagram as an integral in the increment
variables, given the image of the simplices, the time weight and the spatial
factor in those variables. -/
theorem whiteDiagram_eq_table {α₀ : ℝ} (m n : ℕ) (D : Fin (m + n) → Fin (m + n)) (t : ℝ)
    (Dom : Set (Fin (m + n) → ℝ)) (hDom : MeasurableSet Dom)
    (Q W : (Fin (m + n) → ℝ) → ℝ≥0∞) (hQ : Measurable Q) (hW : Measurable W)
    (hiff : ∀ s, s ∈ twoSimplex m n t ↔ incr m s ∈ Dom)
    (htw : ∀ s ∈ twoSimplex m n t, timeWeight α₀ D s = Q (incr m s))
    (hsp : ∀ v ∈ Dom, whiteSpatial m D v = W v) :
    whiteDiagram α₀ m n D t = ∫⁻ v in Dom, Q v * W v := by
  unfold whiteDiagram
  rw [← lintegral_indicator (measurableSet_twoSimplex m n t), ← lintegral_indicator hDom,
    ← (measurePreserving_incr m (m + n)).lintegral_comp
      (f := Dom.indicator fun v => Q v * W v) ((hQ.mul hW).indicator hDom)]
  refine lintegral_congr fun s => ?_
  by_cases hs : s ∈ twoSimplex m n t
  · rw [Set.indicator_of_mem hs, Set.indicator_of_mem ((hiff s).1 hs), htw s hs,
      hsp _ ((hiff s).1 hs)]
  · rw [Set.indicator_of_notMem hs, Set.indicator_of_notMem fun h => hs ((hiff s).2 h)]

/-- Auxiliary: a statement over `Fin 4` is four statements. -/
theorem forall_fin4 {P : Fin 4 → Prop} : (∀ i, P i) ↔ P 0 ∧ P 1 ∧ P 2 ∧ P 3 :=
  ⟨fun h => ⟨h 0, h 1, h 2, h 3⟩, fun ⟨h0, h1, h2, h3⟩ i => by fin_cases i <;> assumption⟩

/-- The domain `(0,4)`: `a,b,c,d > 0`, `a+b+c+d < t` (main TeX line 4940). -/
def dom04 (t : ℝ) : Set (Fin 4 → ℝ) :=
  {v | 0 < v 0 ∧ 0 < v 1 ∧ 0 < v 2 ∧ 0 < v 3 ∧ v 0 + v 1 + v 2 + v 3 < t}

/-- The domain `(1,3)`: `0 < r < t`, `a,b,c > 0`, `a+b+c < t`, with
`v = (r,a,b,c)` (main TeX line 4941). -/
def dom13 (t : ℝ) : Set (Fin 4 → ℝ) :=
  {v | 0 < v 0 ∧ v 0 < t ∧ 0 < v 1 ∧ 0 < v 2 ∧ 0 < v 3 ∧ v 1 + v 2 + v 3 < t}

/-- The domain `(2,2)`: `a,b,c,d > 0`, `a+b < t`, `c+d < t` (main TeX line
4942). -/
def dom22 (t : ℝ) : Set (Fin 4 → ℝ) :=
  {v | 0 < v 0 ∧ 0 < v 1 ∧ 0 < v 2 ∧ 0 < v 3 ∧ v 0 + v 1 < t ∧ v 2 + v 3 < t}

/-- The domain `(3,1)` (the exchange of `(1,3)`): `v = (a,b,c,r)`. -/
def dom31 (t : ℝ) : Set (Fin 4 → ℝ) :=
  {v | 0 < v 0 ∧ 0 < v 1 ∧ 0 < v 2 ∧ v 0 + v 1 + v 2 < t ∧ 0 < v 3 ∧ v 3 < t}

theorem measurableSet_dom04 (t : ℝ) : MeasurableSet (dom04 t) :=
  (measurableSet_lt measurable_const (measurable_pi_apply 0)).inter <|
  (measurableSet_lt measurable_const (measurable_pi_apply 1)).inter <|
  (measurableSet_lt measurable_const (measurable_pi_apply 2)).inter <|
  (measurableSet_lt measurable_const (measurable_pi_apply 3)).inter <|
  measurableSet_lt (by fun_prop : Measurable fun v : Fin 4 → ℝ => v 0 + v 1 + v 2 + v 3)
    measurable_const

theorem measurableSet_dom13 (t : ℝ) : MeasurableSet (dom13 t) :=
  (measurableSet_lt measurable_const (measurable_pi_apply 0)).inter <|
  (measurableSet_lt (measurable_pi_apply 0) measurable_const).inter <|
  (measurableSet_lt measurable_const (measurable_pi_apply 1)).inter <|
  (measurableSet_lt measurable_const (measurable_pi_apply 2)).inter <|
  (measurableSet_lt measurable_const (measurable_pi_apply 3)).inter <|
  measurableSet_lt (by fun_prop : Measurable fun v : Fin 4 → ℝ => v 1 + v 2 + v 3)
    measurable_const

theorem measurableSet_dom22 (t : ℝ) : MeasurableSet (dom22 t) :=
  (measurableSet_lt measurable_const (measurable_pi_apply 0)).inter <|
  (measurableSet_lt measurable_const (measurable_pi_apply 1)).inter <|
  (measurableSet_lt measurable_const (measurable_pi_apply 2)).inter <|
  (measurableSet_lt measurable_const (measurable_pi_apply 3)).inter <|
  (measurableSet_lt (by fun_prop : Measurable fun v : Fin 4 → ℝ => v 0 + v 1)
    measurable_const).inter <|
  measurableSet_lt (by fun_prop : Measurable fun v : Fin 4 → ℝ => v 2 + v 3) measurable_const

theorem measurableSet_dom31 (t : ℝ) : MeasurableSet (dom31 t) :=
  (measurableSet_lt measurable_const (measurable_pi_apply 0)).inter <|
  (measurableSet_lt measurable_const (measurable_pi_apply 1)).inter <|
  (measurableSet_lt measurable_const (measurable_pi_apply 2)).inter <|
  (measurableSet_lt (by fun_prop : Measurable fun v : Fin 4 → ℝ => v 0 + v 1 + v 2)
    measurable_const).inter <|
  (measurableSet_lt measurable_const (measurable_pi_apply 3)).inter <|
  measurableSet_lt (measurable_pi_apply 3) measurable_const

/-- Auxiliary: the increments for the chains `(0,4)`. -/
theorem incr_m0 (s : Fin 4 → ℝ) : incr 0 s = ![s 0, s 1 - s 0, s 2 - s 1, s 3 - s 2] := by
  funext i; fin_cases i <;> simp [incr, predVal, pred]
/-- Auxiliary: the increments for the chains `(1,3)`. -/
theorem incr_m1 (s : Fin 4 → ℝ) : incr 1 s = ![s 0, s 1, s 2 - s 1, s 3 - s 2] := by
  funext i; fin_cases i <;> simp [incr, predVal, pred]
/-- Auxiliary: the increments for the chains `(2,2)`. -/
theorem incr_m2 (s : Fin 4 → ℝ) : incr 2 s = ![s 0, s 1 - s 0, s 2, s 3 - s 2] := by
  funext i; fin_cases i <;> simp [incr, predVal, pred]
/-- Auxiliary: the increments for the chains `(3,1)`. -/
theorem incr_m3 (s : Fin 4 → ℝ) : incr 3 s = ![s 0, s 1 - s 0, s 2 - s 1, s 3] := by
  funext i; fin_cases i <;> simp [incr, predVal, pred]

/-- Auxiliary: the simplices `(0,4)` in increments. -/
theorem mem_twoSimplex_04 (t : ℝ) (s : Fin 4 → ℝ) : s ∈ twoSimplex 0 4 t ↔ incr 0 s ∈ dom04 t := by
  rw [incr_m0, show s ∈ twoSimplex 0 4 t ↔ ∀ i : Fin 4, predVal 0 s i < s i ∧ s i < t from Iff.rfl,
    forall_fin4]
  simp [predVal, pred, dom04]
  constructor <;> intro h <;> casesm* _ ∧ _ <;> split_ands <;> linarith

/-- Auxiliary: the simplices `(1,3)` in increments. -/
theorem mem_twoSimplex_13 (t : ℝ) (s : Fin 4 → ℝ) : s ∈ twoSimplex 1 3 t ↔ incr 1 s ∈ dom13 t := by
  rw [incr_m1, show s ∈ twoSimplex 1 3 t ↔ ∀ i : Fin 4, predVal 1 s i < s i ∧ s i < t from Iff.rfl,
    forall_fin4]
  simp [predVal, pred, dom13]
  constructor <;> intro h <;> casesm* _ ∧ _ <;> split_ands <;> linarith

/-- Auxiliary: the simplices `(2,2)` in increments. -/
theorem mem_twoSimplex_22 (t : ℝ) (s : Fin 4 → ℝ) : s ∈ twoSimplex 2 2 t ↔ incr 2 s ∈ dom22 t := by
  rw [incr_m2, show s ∈ twoSimplex 2 2 t ↔ ∀ i : Fin 4, predVal 2 s i < s i ∧ s i < t from Iff.rfl,
    forall_fin4]
  simp [predVal, pred, dom22]
  constructor <;> intro h <;> casesm* _ ∧ _ <;> split_ands <;> linarith

/-- Auxiliary: the simplices `(3,1)` in increments. -/
theorem mem_twoSimplex_31 (t : ℝ) (s : Fin 4 → ℝ) : s ∈ twoSimplex 3 1 t ↔ incr 3 s ∈ dom31 t := by
  rw [incr_m3, show s ∈ twoSimplex 3 1 t ↔ ∀ i : Fin 4, predVal 3 s i < s i ∧ s i < t from Iff.rfl,
    forall_fin4]
  simp [predVal, pred, dom31]
  constructor <;> intro h <;> casesm* _ ∧ _ <;> split_ands <;> linarith

/-- Auxiliary: the time weight of `A`. -/
theorem timeWeight_pA (α₀ : ℝ) (s : Fin 4 → ℝ) :
    timeWeight α₀ pA s = timeCov α₀ (s 0) (s 1) * timeCov α₀ (s 2) (s 3) := by
  rw [timeWeight, openers_pA, Finset.prod_insert (by decide), Finset.prod_singleton]; rfl
/-- Auxiliary: the time weight of `B`. -/
theorem timeWeight_pB (α₀ : ℝ) (s : Fin 4 → ℝ) :
    timeWeight α₀ pB s = timeCov α₀ (s 0) (s 2) * timeCov α₀ (s 1) (s 3) := by
  rw [timeWeight, openers_pB, Finset.prod_insert (by decide), Finset.prod_singleton]; rfl
/-- Auxiliary: the time weight of `C`. -/
theorem timeWeight_pC (α₀ : ℝ) (s : Fin 4 → ℝ) :
    timeWeight α₀ pC s = timeCov α₀ (s 0) (s 3) * timeCov α₀ (s 1) (s 2) := by
  rw [timeWeight, openers_pC, Finset.prod_insert (by decide), Finset.prod_singleton]; rfl

/-- Auxiliary: the time weights `q₁^{-α₀} q₂^{-α₀}` are measurable. -/
theorem measurable_Q (α₀ : ℝ) {q1 q2 : (Fin 4 → ℝ) → ℝ} (h1 : Continuous q1) (h2 : Continuous q2) :
    Measurable fun v => ENNReal.ofReal (q1 v) ^ (-α₀) * ENNReal.ofReal (q2 v) ^ (-α₀) := by
  have m1 : Measurable fun v => ENNReal.ofReal (q1 v) ^ (-α₀) :=
    (ENNReal.measurable_ofReal.comp h1.measurable).pow_const _
  have m2 : Measurable fun v => ENNReal.ofReal (q2 v) ^ (-α₀) :=
    (ENNReal.measurable_ofReal.comp h2.measurable).pow_const _
  exact m1.mul m2

/-- Auxiliary: the spatial factor `V` is measurable. -/
theorem measurable_W {V : (Fin 4 → ℝ) → ℝ} (hV : Continuous V) :
    Measurable fun v => ENNReal.ofReal (V v) :=
  ENNReal.measurable_ofReal.comp hV.measurable

/-- Auxiliary: `F` composed with continuous maps is continuous. -/
theorem continuous_F_comp {X : Type*} [TopologicalSpace X] {f g k : X → ℝ} (hf : Continuous f)
    (hg : Continuous g) (hk : Continuous k) : Continuous fun x => F (f x) (g x) (k x) := by
  unfold F; fun_prop

/-- Auxiliary: positivity of all increments on a domain. -/
theorem pos_of_dom04 {t : ℝ} {v : Fin 4 → ℝ} (hv : v ∈ dom04 t) : ∀ i, 0 < v i :=
  forall_fin4.2 ⟨hv.1, hv.2.1, hv.2.2.1, hv.2.2.2.1⟩
theorem pos_of_dom13 {t : ℝ} {v : Fin 4 → ℝ} (hv : v ∈ dom13 t) : ∀ i, 0 < v i :=
  forall_fin4.2 ⟨hv.1, hv.2.2.1, hv.2.2.2.1, hv.2.2.2.2.1⟩
theorem pos_of_dom22 {t : ℝ} {v : Fin 4 → ℝ} (hv : v ∈ dom22 t) : ∀ i, 0 < v i :=
  forall_fin4.2 ⟨hv.1, hv.2.1, hv.2.2.1, hv.2.2.2.1⟩
theorem pos_of_dom31 {t : ℝ} {v : Fin 4 → ℝ} (hv : v ∈ dom31 t) : ∀ i, 0 < v i :=
  forall_fin4.2 ⟨hv.1, hv.2.1, hv.2.2.1, hv.2.2.2.2.1⟩

/-! ### The nine rows of `E:white-four-table` -/

section table

variable {α₀ : ℝ}

/-- Auxiliary: closing the time-weight identities on a domain. -/
macro "tw_close" : tactic =>
  `(tactic| (unfold timeCov; congr 3 <;>
    first
    | (rw [abs_of_nonpos (by linarith)]; ring)
    | (rw [abs_of_nonneg (by linarith)]; ring)
    | (congr 1; ring)
    | ring))

/-- **Row `(0,4), A`**: `V = ac/4`, `q₁ = b`, `q₂ = d`. -/
theorem J_04A (hα1 : α₀ < 1) (t : ℝ) :
    diagramLim 1 (Measure.dirac 0) α₀ 0 4 pA t = ∫⁻ v in dom04 t,
      ENNReal.ofReal (v 1) ^ (-α₀) * ENNReal.ofReal (v 3) ^ (-α₀) *
        ENNReal.ofReal (v 0 * v 2 / 4) := by
  rw [diagramLim_white hα1 0 4 isPairing_pA t]
  refine whiteDiagram_eq_table 0 4 pA t (dom04 t) (measurableSet_dom04 t) _ _
    (measurable_Q α₀ (by fun_prop) (by fun_prop)) (measurable_W (by fun_prop))
    (mem_twoSimplex_04 t) (fun s hs => ?_) (fun v hv => whiteSpatial_04A (pos_of_dom04 hv))
  have h := (mem_twoSimplex_04 t s).1 hs
  rw [incr_m0] at h ⊢
  simp only [dom04, Set.mem_ofPred_eq, Matrix.cons_val] at h
  simp only [timeWeight_pA, Matrix.cons_val]
  obtain ⟨h0, h1, h2, h3, h4⟩ := h
  tw_close

/-- **Row `(0,4), B`**: `V = a min(b,c,d)/4`, `q₁ = b+c`, `q₂ = c+d`. -/
theorem J_04B (hα1 : α₀ < 1) (t : ℝ) :
    diagramLim 1 (Measure.dirac 0) α₀ 0 4 pB t = ∫⁻ v in dom04 t,
      ENNReal.ofReal (v 1 + v 2) ^ (-α₀) * ENNReal.ofReal (v 2 + v 3) ^ (-α₀) *
        ENNReal.ofReal (v 0 * min (v 1) (min (v 2) (v 3)) / 4) := by
  have hq1 : Continuous fun v : Fin 4 → ℝ => v 1 + v 2 := by fun_prop
  have hq2 : Continuous fun v : Fin 4 → ℝ => v 2 + v 3 := by fun_prop
  have hV : Continuous fun v : Fin 4 → ℝ => v 0 * min (v 1) (min (v 2) (v 3)) / 4 := by
    fun_prop
  rw [diagramLim_white hα1 0 4 isPairing_pB t]
  refine whiteDiagram_eq_table 0 4 pB t (dom04 t) (measurableSet_dom04 t)
    (fun v => ENNReal.ofReal (v 1 + v 2) ^ (-α₀) * ENNReal.ofReal (v 2 + v 3) ^ (-α₀))
    (fun v => ENNReal.ofReal (v 0 * min (v 1) (min (v 2) (v 3)) / 4))
    (measurable_Q α₀ hq1 hq2) (measurable_W hV)
    (mem_twoSimplex_04 t) (fun s hs => ?_) (fun v hv => whiteSpatial_04B (pos_of_dom04 hv))
  have h := (mem_twoSimplex_04 t s).1 hs
  rw [incr_m0] at h ⊢
  simp only [dom04, Set.mem_ofPred_eq, Matrix.cons_val] at h
  simp only [timeWeight_pB, Matrix.cons_val]
  casesm* _ ∧ _
  tw_close

/-- **Row `(0,4), C`**: `V = a min(b,d)/4`, `q₁ = b+c+d`, `q₂ = c`. -/
theorem J_04C (hα1 : α₀ < 1) (t : ℝ) :
    diagramLim 1 (Measure.dirac 0) α₀ 0 4 pC t = ∫⁻ v in dom04 t,
      ENNReal.ofReal (v 1 + v 2 + v 3) ^ (-α₀) * ENNReal.ofReal (v 2) ^ (-α₀) *
        ENNReal.ofReal (v 0 * min (v 1) (v 3) / 4) := by
  have hq1 : Continuous fun v : Fin 4 → ℝ => v 1 + v 2 + v 3 := by fun_prop
  have hq2 : Continuous fun v : Fin 4 → ℝ => v 2 := by fun_prop
  have hV : Continuous fun v : Fin 4 → ℝ => v 0 * min (v 1) (v 3) / 4 := by
    fun_prop
  rw [diagramLim_white hα1 0 4 isPairing_pC t]
  refine whiteDiagram_eq_table 0 4 pC t (dom04 t) (measurableSet_dom04 t)
    (fun v => ENNReal.ofReal (v 1 + v 2 + v 3) ^ (-α₀) * ENNReal.ofReal (v 2) ^ (-α₀))
    (fun v => ENNReal.ofReal (v 0 * min (v 1) (v 3) / 4))
    (measurable_Q α₀ hq1 hq2) (measurable_W hV)
    (mem_twoSimplex_04 t) (fun s hs => ?_) (fun v hv => whiteSpatial_04C (pos_of_dom04 hv))
  have h := (mem_twoSimplex_04 t s).1 hs
  rw [incr_m0] at h ⊢
  simp only [dom04, Set.mem_ofPred_eq, Matrix.cons_val] at h
  simp only [timeWeight_pC, Matrix.cons_val]
  casesm* _ ∧ _
  tw_close

/-- **Row `(1,3), A`**: `V = min(r,a) b/4`, `q₁ = |r-a|`, `q₂ = c`. -/
theorem J_13A (hα1 : α₀ < 1) (t : ℝ) :
    diagramLim 1 (Measure.dirac 0) α₀ 1 3 pA t = ∫⁻ v in dom13 t,
      ENNReal.ofReal (|v 0 - v 1|) ^ (-α₀) * ENNReal.ofReal (v 3) ^ (-α₀) *
        ENNReal.ofReal (min (v 0) (v 1) * v 2 / 4) := by
  have hq1 : Continuous fun v : Fin 4 → ℝ => |v 0 - v 1| := by fun_prop
  have hq2 : Continuous fun v : Fin 4 → ℝ => v 3 := by fun_prop
  have hV : Continuous fun v : Fin 4 → ℝ => min (v 0) (v 1) * v 2 / 4 := by
    fun_prop
  rw [diagramLim_white hα1 1 3 isPairing_pA t]
  refine whiteDiagram_eq_table 1 3 pA t (dom13 t) (measurableSet_dom13 t)
    (fun v => ENNReal.ofReal (|v 0 - v 1|) ^ (-α₀) * ENNReal.ofReal (v 3) ^ (-α₀))
    (fun v => ENNReal.ofReal (min (v 0) (v 1) * v 2 / 4))
    (measurable_Q α₀ hq1 hq2) (measurable_W hV)
    (mem_twoSimplex_13 t) (fun s hs => ?_) (fun v hv => whiteSpatial_13A (pos_of_dom13 hv))
  have h := (mem_twoSimplex_13 t s).1 hs
  rw [incr_m1] at h ⊢
  simp only [dom13, Set.mem_ofPred_eq, Matrix.cons_val] at h
  simp only [timeWeight_pA, Matrix.cons_val]
  casesm* _ ∧ _
  tw_close

/-- **Row `(1,3), B`**: `V = F(r,a,min(b,c))/16`, `q₁ = |r-a-b|`, `q₂ = b+c`. -/
theorem J_13B (hα1 : α₀ < 1) (t : ℝ) :
    diagramLim 1 (Measure.dirac 0) α₀ 1 3 pB t = ∫⁻ v in dom13 t,
      ENNReal.ofReal (|v 0 - v 1 - v 2|) ^ (-α₀) * ENNReal.ofReal (v 2 + v 3) ^ (-α₀) *
        ENNReal.ofReal (F (v 0) (v 1) (min (v 2) (v 3)) / 16) := by
  have hq1 : Continuous fun v : Fin 4 → ℝ => |v 0 - v 1 - v 2| := by fun_prop
  have hq2 : Continuous fun v : Fin 4 → ℝ => v 2 + v 3 := by fun_prop
  have hV : Continuous fun v : Fin 4 → ℝ => F (v 0) (v 1) (min (v 2) (v 3)) / 16 := by
    exact (continuous_F_comp (by fun_prop) (by fun_prop) (by fun_prop)).div_const _
  rw [diagramLim_white hα1 1 3 isPairing_pB t]
  refine whiteDiagram_eq_table 1 3 pB t (dom13 t) (measurableSet_dom13 t)
    (fun v => ENNReal.ofReal (|v 0 - v 1 - v 2|) ^ (-α₀) * ENNReal.ofReal (v 2 + v 3) ^ (-α₀))
    (fun v => ENNReal.ofReal (F (v 0) (v 1) (min (v 2) (v 3)) / 16))
    (measurable_Q α₀ hq1 hq2) (measurable_W hV)
    (mem_twoSimplex_13 t) (fun s hs => ?_) (fun v hv => whiteSpatial_13B (pos_of_dom13 hv))
  have h := (mem_twoSimplex_13 t s).1 hs
  rw [incr_m1] at h ⊢
  simp only [dom13, Set.mem_ofPred_eq, Matrix.cons_val] at h
  simp only [timeWeight_pB, Matrix.cons_val]
  casesm* _ ∧ _
  tw_close

/-- **Row `(1,3), C`**: `V = F(r,a,c)/16`, `q₁ = |r-a-b-c|`, `q₂ = b`. -/
theorem J_13C (hα1 : α₀ < 1) (t : ℝ) :
    diagramLim 1 (Measure.dirac 0) α₀ 1 3 pC t = ∫⁻ v in dom13 t,
      ENNReal.ofReal (|v 0 - v 1 - v 2 - v 3|) ^ (-α₀) * ENNReal.ofReal (v 2) ^ (-α₀) *
        ENNReal.ofReal (F (v 0) (v 1) (v 3) / 16) := by
  have hq1 : Continuous fun v : Fin 4 → ℝ => |v 0 - v 1 - v 2 - v 3| := by fun_prop
  have hq2 : Continuous fun v : Fin 4 → ℝ => v 2 := by fun_prop
  have hV : Continuous fun v : Fin 4 → ℝ => F (v 0) (v 1) (v 3) / 16 := by
    exact (continuous_F_comp (by fun_prop) (by fun_prop) (by fun_prop)).div_const _
  rw [diagramLim_white hα1 1 3 isPairing_pC t]
  refine whiteDiagram_eq_table 1 3 pC t (dom13 t) (measurableSet_dom13 t)
    (fun v => ENNReal.ofReal (|v 0 - v 1 - v 2 - v 3|) ^ (-α₀) * ENNReal.ofReal (v 2) ^ (-α₀))
    (fun v => ENNReal.ofReal (F (v 0) (v 1) (v 3) / 16))
    (measurable_Q α₀ hq1 hq2) (measurable_W hV)
    (mem_twoSimplex_13 t) (fun s hs => ?_) (fun v hv => whiteSpatial_13C (pos_of_dom13 hv))
  have h := (mem_twoSimplex_13 t s).1 hs
  rw [incr_m1] at h ⊢
  simp only [dom13, Set.mem_ofPred_eq, Matrix.cons_val] at h
  simp only [timeWeight_pC, Matrix.cons_val]
  casesm* _ ∧ _
  tw_close

/-- **Row `(2,2), A`**: `V = ac/4`, `q₁ = b`, `q₂ = d`. -/
theorem J_22A (hα1 : α₀ < 1) (t : ℝ) :
    diagramLim 1 (Measure.dirac 0) α₀ 2 2 pA t = ∫⁻ v in dom22 t,
      ENNReal.ofReal (v 1) ^ (-α₀) * ENNReal.ofReal (v 3) ^ (-α₀) *
        ENNReal.ofReal (v 0 * v 2 / 4) := by
  have hq1 : Continuous fun v : Fin 4 → ℝ => v 1 := by fun_prop
  have hq2 : Continuous fun v : Fin 4 → ℝ => v 3 := by fun_prop
  have hV : Continuous fun v : Fin 4 → ℝ => v 0 * v 2 / 4 := by
    fun_prop
  rw [diagramLim_white hα1 2 2 isPairing_pA t]
  refine whiteDiagram_eq_table 2 2 pA t (dom22 t) (measurableSet_dom22 t)
    (fun v => ENNReal.ofReal (v 1) ^ (-α₀) * ENNReal.ofReal (v 3) ^ (-α₀))
    (fun v => ENNReal.ofReal (v 0 * v 2 / 4))
    (measurable_Q α₀ hq1 hq2) (measurable_W hV)
    (mem_twoSimplex_22 t) (fun s hs => ?_) (fun v hv => whiteSpatial_22A (pos_of_dom22 hv))
  have h := (mem_twoSimplex_22 t s).1 hs
  rw [incr_m2] at h ⊢
  simp only [dom22, Set.mem_ofPred_eq, Matrix.cons_val] at h
  simp only [timeWeight_pA, Matrix.cons_val]
  casesm* _ ∧ _
  tw_close

/-- **Row `(2,2), B`**: `V = min(a,c) min(b,d)/4`, `q₁ = |a-c|`, `q₂ = |a+b-c-d|`. -/
theorem J_22B (hα1 : α₀ < 1) (t : ℝ) :
    diagramLim 1 (Measure.dirac 0) α₀ 2 2 pB t = ∫⁻ v in dom22 t,
      ENNReal.ofReal (|v 0 - v 2|) ^ (-α₀) * ENNReal.ofReal (|v 0 + v 1 - v 2 - v 3|) ^ (-α₀) *
        ENNReal.ofReal (min (v 0) (v 2) * min (v 1) (v 3) / 4) := by
  have hq1 : Continuous fun v : Fin 4 → ℝ => |v 0 - v 2| := by fun_prop
  have hq2 : Continuous fun v : Fin 4 → ℝ => |v 0 + v 1 - v 2 - v 3| := by fun_prop
  have hV : Continuous fun v : Fin 4 → ℝ => min (v 0) (v 2) * min (v 1) (v 3) / 4 := by
    fun_prop
  rw [diagramLim_white hα1 2 2 isPairing_pB t]
  refine whiteDiagram_eq_table 2 2 pB t (dom22 t) (measurableSet_dom22 t)
    (fun v => ENNReal.ofReal (|v 0 - v 2|) ^ (-α₀) *
      ENNReal.ofReal (|v 0 + v 1 - v 2 - v 3|) ^ (-α₀))
    (fun v => ENNReal.ofReal (min (v 0) (v 2) * min (v 1) (v 3) / 4))
    (measurable_Q α₀ hq1 hq2) (measurable_W hV)
    (mem_twoSimplex_22 t) (fun s hs => ?_) (fun v hv => whiteSpatial_22B (pos_of_dom22 hv))
  have h := (mem_twoSimplex_22 t s).1 hs
  rw [incr_m2] at h ⊢
  simp only [dom22, Set.mem_ofPred_eq, Matrix.cons_val] at h
  simp only [timeWeight_pB, Matrix.cons_val]
  casesm* _ ∧ _
  tw_close

/-- **Row `(2,2), C`**: `V = F(a,c,min(b,d))/16`, `q₁ = |a-c-d|`, `q₂ = |a+b-c|`. -/
theorem J_22C (hα1 : α₀ < 1) (t : ℝ) :
    diagramLim 1 (Measure.dirac 0) α₀ 2 2 pC t = ∫⁻ v in dom22 t,
      ENNReal.ofReal (|v 0 - v 2 - v 3|) ^ (-α₀) * ENNReal.ofReal (|v 0 + v 1 - v 2|) ^ (-α₀) *
        ENNReal.ofReal (F (v 0) (v 2) (min (v 1) (v 3)) / 16) := by
  have hq1 : Continuous fun v : Fin 4 → ℝ => |v 0 - v 2 - v 3| := by fun_prop
  have hq2 : Continuous fun v : Fin 4 → ℝ => |v 0 + v 1 - v 2| := by fun_prop
  have hV : Continuous fun v : Fin 4 → ℝ => F (v 0) (v 2) (min (v 1) (v 3)) / 16 := by
    exact (continuous_F_comp (by fun_prop) (by fun_prop) (by fun_prop)).div_const _
  rw [diagramLim_white hα1 2 2 isPairing_pC t]
  refine whiteDiagram_eq_table 2 2 pC t (dom22 t) (measurableSet_dom22 t)
    (fun v => ENNReal.ofReal (|v 0 - v 2 - v 3|) ^ (-α₀) *
      ENNReal.ofReal (|v 0 + v 1 - v 2|) ^ (-α₀))
    (fun v => ENNReal.ofReal (F (v 0) (v 2) (min (v 1) (v 3)) / 16))
    (measurable_Q α₀ hq1 hq2) (measurable_W hV)
    (mem_twoSimplex_22 t) (fun s hs => ?_) (fun v hv => whiteSpatial_22C (pos_of_dom22 hv))
  have h := (mem_twoSimplex_22 t s).1 hs
  rw [incr_m2] at h ⊢
  simp only [dom22, Set.mem_ofPred_eq, Matrix.cons_val] at h
  simp only [timeWeight_pC, Matrix.cons_val]
  casesm* _ ∧ _
  tw_close

/-- Auxiliary: row `(3,1), A` in `v = (a,b,c,r)`. -/
theorem J_31A_tab (hα1 : α₀ < 1) (t : ℝ) :
    diagramLim 1 (Measure.dirac 0) α₀ 3 1 pA t = ∫⁻ v in dom31 t,
      ENNReal.ofReal (v 1) ^ (-α₀) * ENNReal.ofReal (|v 0 + v 1 + v 2 - v 3|) ^ (-α₀) *
        ENNReal.ofReal (F (v 0) (v 3) (v 2) / 16) := by
  have hq1 : Continuous fun v : Fin 4 → ℝ => v 1 := by fun_prop
  have hq2 : Continuous fun v : Fin 4 → ℝ => |v 0 + v 1 + v 2 - v 3| := by fun_prop
  have hV : Continuous fun v : Fin 4 → ℝ => F (v 0) (v 3) (v 2) / 16 := by
    exact (continuous_F_comp (by fun_prop) (by fun_prop) (by fun_prop)).div_const _
  rw [diagramLim_white hα1 3 1 isPairing_pA t]
  refine whiteDiagram_eq_table 3 1 pA t (dom31 t) (measurableSet_dom31 t)
    (fun v => ENNReal.ofReal (v 1) ^ (-α₀) * ENNReal.ofReal (|v 0 + v 1 + v 2 - v 3|) ^ (-α₀))
    (fun v => ENNReal.ofReal (F (v 0) (v 3) (v 2) / 16))
    (measurable_Q α₀ hq1 hq2) (measurable_W hV)
    (mem_twoSimplex_31 t) (fun s hs => ?_) (fun v hv => whiteSpatial_31A (pos_of_dom31 hv))
  have h := (mem_twoSimplex_31 t s).1 hs
  rw [incr_m3] at h ⊢
  simp only [dom31, Set.mem_ofPred_eq, Matrix.cons_val] at h
  simp only [timeWeight_pA, Matrix.cons_val]
  casesm* _ ∧ _
  tw_close

/-- Auxiliary: row `(3,1), B` in `v = (a,b,c,r)`. -/
theorem J_31B_tab (hα1 : α₀ < 1) (t : ℝ) :
    diagramLim 1 (Measure.dirac 0) α₀ 3 1 pB t = ∫⁻ v in dom31 t,
      ENNReal.ofReal (v 1 + v 2) ^ (-α₀) * ENNReal.ofReal (|v 0 + v 1 - v 3|) ^ (-α₀) *
        ENNReal.ofReal (F (v 0) (v 3) (min (v 1) (v 2)) / 16) := by
  have hq1 : Continuous fun v : Fin 4 → ℝ => v 1 + v 2 := by fun_prop
  have hq2 : Continuous fun v : Fin 4 → ℝ => |v 0 + v 1 - v 3| := by fun_prop
  have hV : Continuous fun v : Fin 4 → ℝ => F (v 0) (v 3) (min (v 1) (v 2)) / 16 := by
    exact (continuous_F_comp (by fun_prop) (by fun_prop) (by fun_prop)).div_const _
  rw [diagramLim_white hα1 3 1 isPairing_pB t]
  refine whiteDiagram_eq_table 3 1 pB t (dom31 t) (measurableSet_dom31 t)
    (fun v => ENNReal.ofReal (v 1 + v 2) ^ (-α₀) * ENNReal.ofReal (|v 0 + v 1 - v 3|) ^ (-α₀))
    (fun v => ENNReal.ofReal (F (v 0) (v 3) (min (v 1) (v 2)) / 16))
    (measurable_Q α₀ hq1 hq2) (measurable_W hV)
    (mem_twoSimplex_31 t) (fun s hs => ?_) (fun v hv => whiteSpatial_31B (pos_of_dom31 hv))
  have h := (mem_twoSimplex_31 t s).1 hs
  rw [incr_m3] at h ⊢
  simp only [dom31, Set.mem_ofPred_eq, Matrix.cons_val] at h
  simp only [timeWeight_pB, Matrix.cons_val]
  casesm* _ ∧ _
  tw_close

/-- Auxiliary: row `(3,1), C` in `v = (a,b,c,r)`. -/
theorem J_31C_tab (hα1 : α₀ < 1) (t : ℝ) :
    diagramLim 1 (Measure.dirac 0) α₀ 3 1 pC t = ∫⁻ v in dom31 t,
      ENNReal.ofReal (|v 0 - v 3|) ^ (-α₀) * ENNReal.ofReal (v 2) ^ (-α₀) *
        ENNReal.ofReal (min (v 0) (v 3) * v 1 / 4) := by
  have hq1 : Continuous fun v : Fin 4 → ℝ => |v 0 - v 3| := by fun_prop
  have hq2 : Continuous fun v : Fin 4 → ℝ => v 2 := by fun_prop
  have hV : Continuous fun v : Fin 4 → ℝ => min (v 0) (v 3) * v 1 / 4 := by
    fun_prop
  rw [diagramLim_white hα1 3 1 isPairing_pC t]
  refine whiteDiagram_eq_table 3 1 pC t (dom31 t) (measurableSet_dom31 t)
    (fun v => ENNReal.ofReal (|v 0 - v 3|) ^ (-α₀) * ENNReal.ofReal (v 2) ^ (-α₀))
    (fun v => ENNReal.ofReal (min (v 0) (v 3) * v 1 / 4))
    (measurable_Q α₀ hq1 hq2) (measurable_W hV)
    (mem_twoSimplex_31 t) (fun s hs => ?_) (fun v hv => whiteSpatial_31C (pos_of_dom31 hv))
  have h := (mem_twoSimplex_31 t s).1 hs
  rw [incr_m3] at h ⊢
  simp only [dom31, Set.mem_ofPred_eq, Matrix.cons_val] at h
  simp only [timeWeight_pC, Matrix.cons_val]
  casesm* _ ∧ _
  tw_close

end table

/-! ### Exchanging the two chains and the total -/

/-- Auxiliary: on four labels the chains `(4,0)` and `(0,4)` have the same
predecessors (one chain of four). -/
theorem pred_four_zero : ∀ i : Fin 4, pred 4 i = pred 0 i := by decide

/-- **`(4,0)` by exchanging the chains**: `J_{4,0,D}(t) = J_{0,4,D}(t)`. -/
theorem J_40_eq {α₀ : ℝ} (hα1 : α₀ < 1) {D : Fin 4 → Fin 4} (hD : IsPairing D) (t : ℝ) :
    diagramLim 1 (Measure.dirac 0) α₀ 4 0 D t = diagramLim 1 (Measure.dirac 0) α₀ 0 4 D t := by
  rw [diagramLim_white hα1 4 0 hD t, diagramLim_white hα1 0 4 hD t]
  unfold whiteDiagram whiteSpatial greenProd twoSimplex incr predVal
  simp only [pred_four_zero]

/-- Auxiliary: the relabelling of the chains, `(1,3)`-label `↦` `(3,1)`-label
read backwards: `w = (v_3, v_0, v_1, v_2)`. -/
def σ : Fin 4 ≃ Fin 4 := ⟨![3, 0, 1, 2], ![1, 2, 3, 0], by decide, by decide⟩

/-- Auxiliary: permuting the coordinates of `ℝ^4` preserves Lebesgue measure. -/
theorem lintegral_perm (G : (Fin 4 → ℝ) → ℝ≥0∞) :
    ∫⁻ v : Fin 4 → ℝ, G (fun i => v (σ i)) = ∫⁻ v, G v := by
  have hmp := volume_measurePreserving_piCongrLeft (fun _ : Fin 4 => ℝ) σ.symm
  have he : ∀ v : Fin 4 → ℝ,
      MeasurableEquiv.piCongrLeft (fun _ => ℝ) σ.symm v = fun i => v (σ i) := by
    intro v; funext i; simp [MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft]
  simp_rw [← he]
  exact hmp.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _) G

/-- Auxiliary: the exchange of two set integrals by the relabelling `σ`. -/
theorem setLIntegral_perm {S T : Set (Fin 4 → ℝ)} (hS : MeasurableSet S) (hT : MeasurableSet T)
    {f g : (Fin 4 → ℝ) → ℝ≥0∞} (hmem : ∀ v, v ∈ S ↔ (fun i => v (σ i)) ∈ T)
    (hfg : ∀ v ∈ S, f v = g fun i => v (σ i)) :
    ∫⁻ v in S, f v = ∫⁻ v in T, g v := by
  rw [← lintegral_indicator hS, ← lintegral_indicator hT]
  conv_rhs => rw [← lintegral_perm]
  refine lintegral_congr fun v => ?_
  by_cases hv : v ∈ S
  · rw [Set.indicator_of_mem hv, Set.indicator_of_mem ((hmem v).1 hv), hfg v hv]
  · rw [Set.indicator_of_notMem hv, Set.indicator_of_notMem fun h => hv ((hmem v).2 h)]

/-- Auxiliary: domain correspondence under `σ`. -/
theorem mem_dom31_iff (t : ℝ) (v : Fin 4 → ℝ) : v ∈ dom31 t ↔ (fun i => v (σ i)) ∈ dom13 t := by
  simp only [dom31, dom13, Set.mem_ofPred_eq, σ, Equiv.coe_fn_mk, Matrix.cons_val]
  constructor <;> intro h <;> casesm* _ ∧ _ <;> split_ands <;> linarith

/-- **`(3,1), A` by exchanging the chains**: `J_{3,1,A}(t) = J_{1,3,C}(t)`. -/
theorem J_31A_eq {α₀ : ℝ} (hα1 : α₀ < 1) (t : ℝ) :
    diagramLim 1 (Measure.dirac 0) α₀ 3 1 pA t = diagramLim 1 (Measure.dirac 0) α₀ 1 3 pC t := by
  rw [J_31A_tab hα1, J_13C hα1]
  refine setLIntegral_perm (measurableSet_dom31 t) (measurableSet_dom13 t) (mem_dom31_iff t)
    fun v _ => ?_
  simp only [σ, Equiv.coe_fn_mk, Matrix.cons_val]
  have e : |v 3 - v 0 - v 1 - v 2| = |v 0 + v 1 + v 2 - v 3| := by
    rw [← abs_neg]; congr 1; ring
  rw [e, F_comm (v 3)]
  ring

/-- **`(3,1), B` by exchanging the chains**: `J_{3,1,B}(t) = J_{1,3,B}(t)`. -/
theorem J_31B_eq {α₀ : ℝ} (hα1 : α₀ < 1) (t : ℝ) :
    diagramLim 1 (Measure.dirac 0) α₀ 3 1 pB t = diagramLim 1 (Measure.dirac 0) α₀ 1 3 pB t := by
  rw [J_31B_tab hα1, J_13B hα1]
  refine setLIntegral_perm (measurableSet_dom31 t) (measurableSet_dom13 t) (mem_dom31_iff t)
    fun v _ => ?_
  simp only [σ, Equiv.coe_fn_mk, Matrix.cons_val]
  have e : |v 3 - v 0 - v 1| = |v 0 + v 1 - v 3| := by
    rw [← abs_neg]; congr 1; ring
  rw [e, F_comm (v 3)]
  ring

/-- **`(3,1), C` by exchanging the chains**: `J_{3,1,C}(t) = J_{1,3,A}(t)`. -/
theorem J_31C_eq {α₀ : ℝ} (hα1 : α₀ < 1) (t : ℝ) :
    diagramLim 1 (Measure.dirac 0) α₀ 3 1 pC t = diagramLim 1 (Measure.dirac 0) α₀ 1 3 pA t := by
  rw [J_31C_tab hα1, J_13A hα1]
  refine setLIntegral_perm (measurableSet_dom31 t) (measurableSet_dom13 t) (mem_dom31_iff t)
    fun v _ => ?_
  simp only [σ, Equiv.coe_fn_mk, Matrix.cons_val]
  rw [abs_sub_comm (v 3), min_comm (v 3)]

/-- Auxiliary: a pairing in `Π_2` on four labels is a fixed-point-free
involution. -/
theorem isPairing_of_mem_four {D : Fin 4 → Fin 4} (hD : D ∈ ({pA, pB, pC} : Finset _)) :
    IsPairing D := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at hD
  rcases hD with rfl | rfl | rfl
  exacts [isPairing_pA, isPairing_pB, isPairing_pC]

/-- **`E:total-four`** (main TeX lines 4968-4972): the total-order-four
coefficient `A_2(t) = Σ_{m=0}^{4} Σ_{D ∈ Π_2} J_{m,4-m,D}(t)` equals
`2 Σ_D J_{0,4,D} + 2 Σ_D J_{1,3,D} + Σ_D J_{2,2,D}`. -/
theorem total_four {α₀ : ℝ} (hα1 : α₀ < 1) (t : ℝ) :
    coeffALim 1 (Measure.dirac 0) α₀ 2 t =
      2 * ∑ D ∈ Pi2 0 4, diagramLim 1 (Measure.dirac 0) α₀ 0 4 D t +
        2 * ∑ D ∈ Pi2 1 3, diagramLim 1 (Measure.dirac 0) α₀ 1 3 D t +
          ∑ D ∈ Pi2 2 2, diagramLim 1 (Measure.dirac 0) α₀ 2 2 D t := by
  unfold coeffALim
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  change ∑ D ∈ Pi2 0 4, diagramLim 1 (Measure.dirac 0) α₀ 0 4 D t +
      ∑ D ∈ Pi2 1 3, diagramLim 1 (Measure.dirac 0) α₀ 1 3 D t +
      ∑ D ∈ Pi2 2 2, diagramLim 1 (Measure.dirac 0) α₀ 2 2 D t +
      ∑ D ∈ Pi2 3 1, diagramLim 1 (Measure.dirac 0) α₀ 3 1 D t +
      ∑ D ∈ Pi2 4 0, diagramLim 1 (Measure.dirac 0) α₀ 4 0 D t = _
  have h40 : ∑ D ∈ Pi2 4 0, diagramLim 1 (Measure.dirac 0) α₀ 4 0 D t =
      ∑ D ∈ Pi2 0 4, diagramLim 1 (Measure.dirac 0) α₀ 0 4 D t := by
    rw [Pi2_40, Pi2_04]
    exact Finset.sum_congr rfl fun D hD => J_40_eq hα1 (isPairing_of_mem_four hD) t
  have h31 : ∑ D ∈ Pi2 3 1, diagramLim 1 (Measure.dirac 0) α₀ 3 1 D t =
      ∑ D ∈ Pi2 1 3, diagramLim 1 (Measure.dirac 0) α₀ 1 3 D t := by
    rw [Pi2_31, Pi2_13, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_singleton, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_singleton, J_31A_eq hα1, J_31B_eq hα1, J_31C_eq hα1]
    ring
  rw [h40, h31]
  ring

/-! ### Scaling in `t` -/

/-- Auxiliary: change of variables for a positive diagonal map of `ℝ^N`. -/
theorem lintegral_diag {N : ℕ} (d : Fin N → ℝ) (hd : ∀ i, 0 < d i)
    {f : (Fin N → ℝ) → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ v, f v = ENNReal.ofReal (∏ i, d i) * ∫⁻ w : Fin N → ℝ, f fun i => d i * w i := by
  set M : Matrix (Fin N) (Fin N) ℝ := Matrix.diagonal d
  have hpos : 0 < ∏ i, d i := Finset.prod_pos fun i _ => hd i
  have hdet : M.det = ∏ i, d i := Matrix.det_diagonal
  have hmeas : Measurable (Matrix.toLin' M : (Fin N → ℝ) → Fin N → ℝ) :=
    (Matrix.toLin' M).continuous_of_finiteDimensional.measurable
  have hfun : (Matrix.toLin' M : (Fin N → ℝ) → Fin N → ℝ) = fun w i => d i * w i := by
    funext w i; simp [M, Matrix.mulVec_diagonal]
  have hmap := Real.map_matrix_volume_pi_eq_smul_volume_pi (M := M) (by rw [hdet]; exact hpos.ne')
  have h1 : ∫⁻ w : Fin N → ℝ, f (fun i => d i * w i) = ENNReal.ofReal |M.det⁻¹| * ∫⁻ v, f v := by
    rw [show (∫⁻ w : Fin N → ℝ, f (fun i => d i * w i)) = ∫⁻ w, f (Matrix.toLin' M w) from
      lintegral_congr fun w => by rw [hfun], ← lintegral_map hf hmeas, hmap,
      lintegral_smul_measure, smul_eq_mul]
  rw [h1, hdet, abs_inv, abs_of_pos hpos, ← mul_assoc, ← ENNReal.ofReal_mul hpos.le,
    mul_inv_cancel₀ hpos.ne', ENNReal.ofReal_one, one_mul]

/-- Auxiliary: the predecessor value of a scaled vector. -/
theorem predVal_smul (m : ℕ) {N : ℕ} (t : ℝ) (y : Fin N → ℝ) (i : Fin N) :
    predVal m (fun j => t * y j) i = t * predVal m y i := by
  rcases hp : pred m i with _ | j
  · rw [predVal_of_none m _ i hp, predVal_of_none m _ i hp, mul_zero]
  · rw [predVal_of_some m _ i j hp, predVal_of_some m _ i j hp]

/-- Auxiliary: the Green product is invariant under `(h, y) ↦ (t h, t y)`, `t > 0`. -/
theorem greenProd_smul (m : ℕ) {N : ℕ} {t : ℝ} (ht : 0 < t) (h y : Fin N → ℝ) :
    greenProd m (fun i => t * h i) (fun i => t * y i) = greenProd m h y := by
  unfold greenProd
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [predVal_smul, ← mul_sub]
  have key : ∀ r a : ℝ, t * |r| < t * a ↔ |r| < a := fun r a =>
    ⟨fun h => lt_of_mul_lt_mul_left h ht.le, fun h => mul_lt_mul_of_pos_left h ht⟩
  simp only [g1, abs_mul, abs_of_pos ht, key]

/-- Auxiliary: an opener's partner. -/
theorem opener_lt {N : ℕ} {D : Fin N → Fin N} (hD : IsPairing D) (i : Fin N) :
    opener D i < D (opener D i) := by
  unfold opener
  split_ifs with h
  · exact h
  · exact lt_of_not_lt hD h

/-- Auxiliary: the collapsed spatial factor is measurable in the increments. -/
theorem measurable_whiteSpatial (m : ℕ) {N : ℕ} (D : Fin N → Fin N) :
    Measurable (whiteSpatial m D) := by
  have hj : Measurable fun p : (Fin N → ℝ) × (Fin N → ℝ) =>
      (p.1, fun i => p.2 (opener D i)) :=
    measurable_fst.prodMk (measurable_pi_iff.2 fun i => (measurable_pi_apply _).comp measurable_snd)
  have hg : Measurable fun p : (Fin N → ℝ) × (Fin N → ℝ) =>
      greenProd m p.1 (fun i => p.2 (opener D i)) := (measurable_greenProd_uncurry m).comp hj
  exact Measurable.lintegral_prod_right'
    (f := fun p : (Fin N → ℝ) × (Fin N → ℝ) =>
      greenProd m p.1 (fun i => p.2 (opener D i)) * gaussW D p.2)
    (hg.mul ((measurable_gaussW D).comp measurable_snd))

/-- Auxiliary: `S(t h) = t^k S(h)` for the collapsed spatial factor (`k` pairs). -/
theorem whiteSpatial_smul (m : ℕ) {N : ℕ} {D : Fin N → Fin N} (hD : IsPairing D) {t : ℝ}
    (ht : 0 < t) (h : Fin N → ℝ) :
    whiteSpatial m D (fun i => t * h i) = ENNReal.ofReal t ^ (openers D).card *
      whiteSpatial m D h := by
  unfold whiteSpatial
  set d : Fin N → ℝ := fun i => if i < D i then t else 1 with hd_def
  have hd : ∀ i, 0 < d i := fun i => by simp only [hd_def]; split_ifs <;> linarith
  have hmeas : Measurable fun v : Fin N → ℝ =>
      greenProd m (fun i => t * h i) (fun i => v (opener D i)) * gaussW D v := by
    have h1 : Measurable fun v : Fin N → ℝ => fun i => v (opener D i) :=
      measurable_pi_iff.2 fun i => measurable_pi_apply _
    exact ((measurable_greenProd m _).comp h1).mul (measurable_gaussW D)
  rw [lintegral_diag d hd hmeas]
  have hprod : ∏ i, d i = t ^ (openers D).card := by
    rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one]; rfl
  rw [hprod, ENNReal.ofReal_pow ht.le]
  congr 1
  refine lintegral_congr fun w => ?_
  have hop : (fun i => d (opener D i) * w (opener D i)) = fun i => t * w (opener D i) := by
    funext i; simp [hd_def, opener_lt hD i]
  have hg : gaussW D (fun i => d i * w i) = gaussW D w := by
    unfold gaussW
    refine Finset.prod_congr rfl fun j hj => ?_
    have hj' : j < D j := by simpa [openers] using hj
    simp [hd_def, not_lt_of_lt hD hj']
  rw [hop, hg, greenProd_smul m ht]

/-- Auxiliary: `∏ |t s_j - t s_h|^{-α₀} = (t^{-α₀})^k ∏ |s_j - s_h|^{-α₀}`. -/
theorem timeWeight_smul {N : ℕ} (α₀ : ℝ) (D : Fin N → Fin N) {t : ℝ} (ht : 0 < t)
    (s : Fin N → ℝ) :
    timeWeight α₀ D (fun i => t * s i) =
      (ENNReal.ofReal t ^ (-α₀)) ^ (openers D).card * timeWeight α₀ D s := by
  unfold timeWeight
  rw [← Finset.prod_const, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j _ => ?_
  unfold timeCov
  rw [← mul_sub, abs_mul, abs_of_pos ht, ENNReal.ofReal_mul ht.le,
    ENNReal.mul_rpow_of_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top]

/-- Auxiliary: `t u ∈ [0,t]^m_< × [0,t]^n_<` iff `u ∈ [0,1]^m_< × [0,1]^n_<`. -/
theorem smul_mem_twoSimplex (m n : ℕ) {t : ℝ} (ht : 0 < t) (u : Fin (m + n) → ℝ) :
    (fun i => t * u i) ∈ twoSimplex m n t ↔ u ∈ twoSimplex m n 1 := by
  have key : ∀ a b : ℝ, t * a < t * b ↔ a < b := fun a b =>
    ⟨fun h => lt_of_mul_lt_mul_left h ht.le, fun h => mul_lt_mul_of_pos_left h ht⟩
  show (∀ i, predVal m (fun j => t * u j) i < t * u i ∧ t * u i < t) ↔
    ∀ i, predVal m u i < u i ∧ u i < 1
  simp only [predVal_smul, key]
  refine forall_congr' fun i => and_congr_right' ?_
  rw [show t * u i < t ↔ t * u i < t * 1 by rw [mul_one], key]

/-- Auxiliary: the increments of a scaled vector. -/
theorem incr_smul (m : ℕ) {N : ℕ} (t : ℝ) (u : Fin N → ℝ) :
    incr m (fun i => t * u i) = fun i => t * incr m u i := by
  funext i; unfold incr; rw [predVal_smul]; ring

/-- **Scaling of every white-noise diagram** (`t > 0`, `N = m + n` labels, `k`
pairs): `J(t) = t^N · t^k · (t^{-α₀})^k · J(1)`; for `N = 4`, `k = 2` this is
`t^{6-2α₀}` (main TeX lines 4982-4983 and 5012-5015: "`t^4` from their measure,
`t^2` from the area and `t^{-2α₀}` from the covariance factors"). -/
theorem whiteDiagram_smul (α₀ : ℝ) (m n : ℕ) {D : Fin (m + n) → Fin (m + n)} (hD : IsPairing D)
    {t : ℝ} (ht : 0 < t) :
    whiteDiagram α₀ m n D t = ENNReal.ofReal t ^ (m + n) *
      (ENNReal.ofReal t ^ (openers D).card * (ENNReal.ofReal t ^ (-α₀)) ^ (openers D).card) *
        whiteDiagram α₀ m n D 1 := by
  have h0 : ENNReal.ofReal t ≠ 0 := by simpa using ht
  have hc : ENNReal.ofReal t ^ (openers D).card * (ENNReal.ofReal t ^ (-α₀)) ^ (openers D).card
      ≠ ⊤ := by
    refine ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) (ENNReal.pow_ne_top ?_)
    rw [Ne, ENNReal.rpow_eq_top_iff]
    simp [h0]
  have hG : Measurable fun s => timeWeight α₀ D s * whiteSpatial m D (incr m s) :=
    (measurable_timeWeight α₀ D).mul ((measurable_whiteSpatial m D).comp (measurable_incr m))
  unfold whiteDiagram
  rw [← lintegral_indicator (measurableSet_twoSimplex m n t),
    lintegral_diag (fun _ => t) (fun _ => ht) (hG.indicator (measurableSet_twoSimplex m n t)),
    ← lintegral_indicator (measurableSet_twoSimplex m n 1), Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, ENNReal.ofReal_pow ht.le, mul_assoc, ← lintegral_const_mul' _ _ hc]
  refine congrArg _ (lintegral_congr fun u => ?_)
  by_cases hu : u ∈ twoSimplex m n 1
  · rw [Set.indicator_of_mem ((smul_mem_twoSimplex m n ht u).2 hu), Set.indicator_of_mem hu,
      timeWeight_smul α₀ D ht, incr_smul, whiteSpatial_smul m hD ht]
    ring
  · rw [Set.indicator_of_notMem (fun h => hu ((smul_mem_twoSimplex m n ht u).1 h)),
      Set.indicator_of_notMem hu, mul_zero]

/-- **Scaling of the order-four entries** (`P:white-four`, last sentence, main TeX
lines 4982-4983): for `t > 0` every `J_{m,n,D}(t)` with `m + n = 4` is
`t^{6-2α₀}` times its unit-time value. -/
theorem diagramLim_four_scale {α₀ : ℝ} (hα1 : α₀ < 1) {m n : ℕ} (hk : m + n = 2 * 2)
    {D : Fin (m + n) → Fin (m + n)} (hD : D ∈ Pi2 m n) {t : ℝ} (ht : 0 < t) :
    diagramLim 1 (Measure.dirac 0) α₀ m n D t =
      ENNReal.ofReal (t ^ (6 - 2 * α₀)) * diagramLim 1 (Measure.dirac 0) α₀ m n D 1 := by
  have hP := isPairing_of_mem hD
  rw [diagramLim_white hα1 m n hP, diagramLim_white hα1 m n hP, whiteDiagram_smul α₀ m n hP ht,
    card_openers hD hk, show ENNReal.ofReal t ^ (m + n) = ENNReal.ofReal t ^ 4 by rw [hk]]
  congr 1
  have hx0 : ENNReal.ofReal t ≠ 0 := by simpa using ht
  have hxt : ENNReal.ofReal t ≠ ⊤ := ENNReal.ofReal_ne_top
  rw [← ENNReal.ofReal_rpow_of_pos ht, pow_two (ENNReal.ofReal t ^ (-α₀)),
    ← ENNReal.rpow_natCast (ENNReal.ofReal t) 4, ← ENNReal.rpow_natCast (ENNReal.ofReal t) 2,
    ← ENNReal.rpow_add _ _ hx0 hxt, ← ENNReal.rpow_add _ _ hx0 hxt,
    ← ENNReal.rpow_add _ _ hx0 hxt]
  congr 1
  push_cast
  ring

/-- **`P:white-four` under the manuscript's hypotheses** (main TeX lines
4946-4983: `d = α = 1`, `γ = δ₀`, `0 < α₀ < 1` from `E:cov`): the nine rows of
`E:white-four-table`, the exchanged chains `(4,0)` and `(3,1)`, `E:total-four`
and the `t^{6-2α₀}` scaling.  The hypothesis `0 < α₀` is carried and unused
(every conclusion holds for `α₀ < 1`). -/
theorem white_four_paper {α₀ : ℝ} (hα : 0 < α₀ ∧ α₀ < 1) (t : ℝ) :
    (diagramLim 1 (Measure.dirac 0) α₀ 0 4 pA t = ∫⁻ v in dom04 t,
          ENNReal.ofReal (v 1) ^ (-α₀) * ENNReal.ofReal (v 3) ^ (-α₀) *
            ENNReal.ofReal (v 0 * v 2 / 4)) ∧
    (diagramLim 1 (Measure.dirac 0) α₀ 0 4 pB t = ∫⁻ v in dom04 t,
          ENNReal.ofReal (v 1 + v 2) ^ (-α₀) * ENNReal.ofReal (v 2 + v 3) ^ (-α₀) *
            ENNReal.ofReal (v 0 * min (v 1) (min (v 2) (v 3)) / 4)) ∧
    (diagramLim 1 (Measure.dirac 0) α₀ 0 4 pC t = ∫⁻ v in dom04 t,
          ENNReal.ofReal (v 1 + v 2 + v 3) ^ (-α₀) * ENNReal.ofReal (v 2) ^ (-α₀) *
            ENNReal.ofReal (v 0 * min (v 1) (v 3) / 4)) ∧
    (diagramLim 1 (Measure.dirac 0) α₀ 1 3 pA t = ∫⁻ v in dom13 t,
          ENNReal.ofReal (|v 0 - v 1|) ^ (-α₀) * ENNReal.ofReal (v 3) ^ (-α₀) *
            ENNReal.ofReal (min (v 0) (v 1) * v 2 / 4)) ∧
    (diagramLim 1 (Measure.dirac 0) α₀ 1 3 pB t = ∫⁻ v in dom13 t,
          ENNReal.ofReal (|v 0 - v 1 - v 2|) ^ (-α₀) * ENNReal.ofReal (v 2 + v 3) ^ (-α₀) *
            ENNReal.ofReal (F (v 0) (v 1) (min (v 2) (v 3)) / 16)) ∧
    (diagramLim 1 (Measure.dirac 0) α₀ 1 3 pC t = ∫⁻ v in dom13 t,
          ENNReal.ofReal (|v 0 - v 1 - v 2 - v 3|) ^ (-α₀) * ENNReal.ofReal (v 2) ^ (-α₀) *
            ENNReal.ofReal (F (v 0) (v 1) (v 3) / 16)) ∧
    (diagramLim 1 (Measure.dirac 0) α₀ 2 2 pA t = ∫⁻ v in dom22 t,
          ENNReal.ofReal (v 1) ^ (-α₀) * ENNReal.ofReal (v 3) ^ (-α₀) *
            ENNReal.ofReal (v 0 * v 2 / 4)) ∧
    (diagramLim 1 (Measure.dirac 0) α₀ 2 2 pB t = ∫⁻ v in dom22 t,
          ENNReal.ofReal (|v 0 - v 2|) ^ (-α₀) * ENNReal.ofReal (|v 0 + v 1 - v 2 - v 3|) ^ (-α₀) *
            ENNReal.ofReal (min (v 0) (v 2) * min (v 1) (v 3) / 4)) ∧
    (diagramLim 1 (Measure.dirac 0) α₀ 2 2 pC t = ∫⁻ v in dom22 t,
          ENNReal.ofReal (|v 0 - v 2 - v 3|) ^ (-α₀) * ENNReal.ofReal (|v 0 + v 1 - v 2|) ^ (-α₀) *
            ENNReal.ofReal (F (v 0) (v 2) (min (v 1) (v 3)) / 16)) ∧
    (∀ D ∈ Pi2 4 0, diagramLim 1 (Measure.dirac 0) α₀ 4 0 D t =
      diagramLim 1 (Measure.dirac 0) α₀ 0 4 D t) ∧
    diagramLim 1 (Measure.dirac 0) α₀ 3 1 pA t = diagramLim 1 (Measure.dirac 0) α₀ 1 3 pC t ∧
    diagramLim 1 (Measure.dirac 0) α₀ 3 1 pB t = diagramLim 1 (Measure.dirac 0) α₀ 1 3 pB t ∧
    diagramLim 1 (Measure.dirac 0) α₀ 3 1 pC t = diagramLim 1 (Measure.dirac 0) α₀ 1 3 pA t ∧
    coeffALim 1 (Measure.dirac 0) α₀ 2 t =
      2 * ∑ D ∈ Pi2 0 4, diagramLim 1 (Measure.dirac 0) α₀ 0 4 D t +
        2 * ∑ D ∈ Pi2 1 3, diagramLim 1 (Measure.dirac 0) α₀ 1 3 D t +
          ∑ D ∈ Pi2 2 2, diagramLim 1 (Measure.dirac 0) α₀ 2 2 D t ∧
    (∀ (m n : ℕ), m + n = 2 * 2 → ∀ D ∈ Pi2 m n, 0 < t →
      diagramLim 1 (Measure.dirac 0) α₀ m n D t =
        ENNReal.ofReal (t ^ (6 - 2 * α₀)) * diagramLim 1 (Measure.dirac 0) α₀ m n D 1) := by
  have h := hα.2
  refine ⟨J_04A h t, J_04B h t, J_04C h t, J_13A h t, J_13B h t, J_13C h t, J_22A h t,
    J_22B h t, J_22C h t, fun D hD => J_40_eq h (isPairing_of_mem_four (by rwa [Pi2_40] at hD)) t,
    J_31A_eq h t,
    J_31B_eq h t, J_31C_eq h t, total_four h t,
    fun m n hk D hD ht => diagramLim_four_scale h hk hD ht⟩

end StratonovichHAMSecondMoment.WhiteFour
