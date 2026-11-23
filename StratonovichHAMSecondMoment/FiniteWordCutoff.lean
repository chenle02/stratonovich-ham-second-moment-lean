module

/-
Copyright 2026 Le Chen. SPDX-License-Identifier: Apache-2.0

`L:finite-word-cutoff` (Exact cutoffs for finite Gaussian words) of
`notes/notes_stratonovich_ham_second_moment.tex` (main TeX file; all line
numbers below are at revision edf7085f): statement lines 3036-3058 (display
`E:finite-word-cutoff`, lines 3048-3055), proof lines 3060-3076, in its
multi-mode form (several Gaussian modes per color, the cutoff on the TOTAL
Hermite degree of each color), and its use in `P:interval-coefficients`
(lines 4054-4228): the coefficient `Q_{r,q} = ⟨U_r v, U_q v⟩_{𝓗_{1/T}}`
(lines 4142-4144) and the exact preservation of the selected coefficients by
the cutoff `N_i = 2k_i` (lines 4163-4170).  Wave item L11-K10.

Why a new module.  `StratonovichHAMAudit.HermiteWord.cut_eq_raw` (the
abstract finite-word induction) lives in a non-module file, which a `module`
cannot import; `HermiteWordFock` applies it to one mode per color with
per-coordinate cutoffs.  This module re-proves the abstract induction natively
(`bump`, `counts`, `raw`, `cut`, `raw_support`, `cut_eq_raw`: the same
definitions and proof, in this namespace) so that `FixedSplit`-side modules can
use it, and redoes the degree bookkeeping for the cutoff `cutIdx col N` of
`FixedSplit` (color total degree `≤ N_i`, modes `Fin m` with colors `col`).

Formalized (proved):
* `finite_word_cutoff` / `finite_word_cutoff_paper`: `E:finite-word-cutoff`
  on coefficient vectors `(Fin m → ℕ) → 𝒳` in the normalized Hermite basis,
  `J_i = ∑_{col j = i} M_{g_j} ⊗ K_j` (`field`, multiplication by `g_j` being
  `HermiteFock.gmul`, creation plus annihilation), frames acting on `𝒳` only,
  start `(I ⊗ F_0)(1 ⊗ v) = 1 ⊗ F_0 v` (`vac`), `P` the projection onto color total degrees
  `≤ N_i` (`truncN`), any finite word with `r_i ≤ N_i`.  The degree
  bookkeeping is `colorGood_vac`, `colorGood_field` (an insertion of color
  `i` raises the color-`i` total degree by at most one and keeps the others),
  `colorGood_frame`, `truncN_eq`.
* `finite_word_cutoff_integral`: the last sentence of the lemma (lines
  3056-3057) for finite sums of integrals of words, coordinatewise in the
  Hermite basis (`wordCoef`); the integrands agree everywhere, so no
  integrability is needed.
* the phase form used in `S:interval-upper` (`𝒳` the phase pairs, insertion
  `(u, w) ↦ (0, σ_i B_i u)`, line 3861): `phase_word_cutoff`, and the bridge
  `extP_cutWordC` to `FixedSplit`'s cutoff model (`fockJ` on `PhaseSp`,
  start `startC = (I ⊗ F_0) vacPhase`, frames acting pointwise): the cutoff
  word on `PhaseSp`, extended by zero, is the word with `P` before and after
  every insertion; hence `cutWordC_eq_raw`.
* `coef_cutoff_eq`: under the Duhamel word expansion (`DuhamelWords`) the
  ordinary coefficient `c_r` of the cutoff evolution at cutoff `N ≥ r`,
  extended by zero, IS the uncut coefficient `U_r v` (lines 4166-4170).
* `fullInner_extP`, `Q_identification`: the inner product `⟨U_r v, U_q v⟩`
  of `𝓗_{1/T}` on the uncut space (`fullInner`, a sum over all multi-indices)
  equals the cutoff inner product `⟨fockEmb (c_r), fockEmb (c_q)⟩` of
  `FixedSplit`.
* `interval_coefficient_assembly_paper_words`: the step row
  `FixedSplit.interval_coefficient_assembly_paper_fixed` re-issued WITHOUT
  its hypothesis `hQ`: `Q_{r,q}` is no longer a free function but
  `Re ⟨U_r v, U_q v⟩_{𝓗_{1/T}}` of the uncut coefficients `U`, and the bound
  `|Q| ≤ |⟨c_r, c_q⟩|` that `hQ` assumed is proved (`Q_identification`).

Supplied input (named `Prop`): `DuhamelWords` (the Duhamel expansion of the
ordinary coefficients, lines 4092-4097 and 4166-4170: `U_r v` and the cutoff
coefficient `c_r` are the same finite sum of integrals of words with exactly
`r_i` insertions of color `i`, raw for `U_r`, cut for `c_r`).  The
evolutions are not constructed in the package (as in `FixedSplit`, where the
cutoff coefficients `c` are already parameters), so this expansion is
supplied; it replaces `hQ`, which assumed the conclusion.

Differences from the TeX.  The Gaussian `L²` space is represented by its
Hermite coefficients (as in `HermiteFock`, `FockForm` and `FixedSplit`); the
uncut space is all functions `(Fin m → ℕ) → 𝒳` and its inner product
`fullInner` is a `tsum` (used only for finitely supported vectors, where it
is a finite sum).  `𝒳` is an inner product space; completeness is carried in
the `_paper` form and unused.  Integrals of words are coordinatewise (the
Hermite coefficients of a Bochner integral in `L²(Ω; 𝒳)` are the integrals of
the coefficients).  `Q_{r,q}` is the real part of the TeX's complex inner
product: `FixedSplit`'s step row has a real `Q` and `E:interval-energy-splits`
is a real identity (its sum is the real part of the sum of the complex
`Q_{r,q}`), and `|Re z| ≤ |z|`.  `hsplits` (`E:interval-energy-splits` with
the reflection parity) remains supplied, now about the uncut coefficients.

Junk values: none.  The `tsum` of `fullInner` is evaluated in the theorems
only on extensions of cutoff vectors, which are finitely supported
(`tsum_eq_sum`); Bochner integrals are compared only for everywhere-equal
integrands, so they agree whether or not they are integrable.
-/
public import Mathlib
public import StratonovichHAMSecondMoment.FixedSplit

@[expose] public section

noncomputable section

set_option autoImplicit false

open Finset Real MeasureTheory
open scoped Nat

namespace StratonovichHAMSecondMoment.FiniteWordCutoff

open StratonovichHAMSecondMoment.HermiteFock
open StratonovichHAMSecondMoment.GaussianHermite (unitIdx)
open StratonovichHAMSecondMoment.FixedSplit StratonovichHAMSecondMoment.FixedSplitCore

/-! ### The abstract finite-word induction (native copy of `HermiteWord`) -/

section Words

variable {C B V : Type*} [DecidableEq C]

/-- Raising the degree of color `i` by one. -/
def bump (i : C) (d : C → ℕ) : C → ℕ :=
  fun c => d c + if c = i then 1 else 0

/-- The color counts `r_i` of a word (main TeX line 3045). -/
def counts : List (C × B) → C → ℕ
  | [] => fun _ => 0
  | (i, _) :: w => bump i (counts w)

/-- The uncompressed word `F_n J_{i_n} ⋯ F_1 J_{i_1} v₀` (right side of
`E:finite-word-cutoff`); the list is read latest letter first. -/
def raw (J : C → V → V) (F : B → V → V) (v₀ : V) : List (C × B) → V
  | [] => v₀
  | (i, b) :: w => F b (J i (raw J F v₀ w))

/-- The compressed word `F_n (P J_{i_n} P) ⋯ F_1 (P J_{i_1} P) v₀` (left side
of `E:finite-word-cutoff`). -/
def cut (P : V → V) (J : C → V → V) (F : B → V → V)
    (v₀ : V) : List (C × B) → V
  | [] => v₀
  | (i, b) :: w => F b (P (J i (P (cut P J F v₀ w))))

/-- The degree induction of the proof (main TeX lines 3065-3069): after the
first `l` insertions the uncompressed word has color degrees at most the
counts. -/
theorem raw_support
    (Good : (C → ℕ) → V → Prop)
    (J : C → V → V) (F : B → V → V) (v₀ : V)
    (hv₀ : Good (fun _ => 0) v₀)
    (hJ : ∀ d i v, Good d v → Good (bump i d) (J i v))
    (hF : ∀ d b v, Good d v → Good d (F b v))
    (w : List (C × B)) : Good (counts w) (raw J F v₀ w) := by
  induction w with
  | nil => exact hv₀
  | cons a w ih =>
    exact hF _ a.2 _ (hJ _ a.1 _ ih)

/-- **The abstract `E:finite-word-cutoff`** (main TeX lines 3060-3076): if
`P` fixes every vector whose degrees are at most `N`, insertions raise one
color degree by at most one and frames keep degrees, then on a word with
counts at most `N` the compressed and uncompressed words agree. -/
theorem cut_eq_raw
    (Good : (C → ℕ) → V → Prop)
    (J : C → V → V) (F : B → V → V) (P : V → V)
    (v₀ : V) (N : C → ℕ)
    (hv₀ : Good (fun _ => 0) v₀)
    (hJ : ∀ d i v, Good d v → Good (bump i d) (J i v))
    (hF : ∀ d b v, Good d v → Good d (F b v))
    (hP : ∀ d v, (∀ c, d c ≤ N c) → Good d v → P v = v)
    (w : List (C × B)) (hN : ∀ c, counts w c ≤ N c) :
    cut P J F v₀ w = raw J F v₀ w := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    have hs : ∀ c, counts w c ≤ N c := by
      intro c
      have hc := hN c
      simp only [counts, bump] at hc
      omega
    have hw := raw_support Good J F v₀ hv₀ hJ hF w
    have hp₀ := hP (counts w) (raw J F v₀ w) hs hw
    have hp₁ := hP (bump a.1 (counts w)) (J a.1 (raw J F v₀ w))
      hN (hJ _ _ _ hw)
    change F a.2 (P (J a.1 (P (cut P J F v₀ w)))) =
      F a.2 (J a.1 (raw J F v₀ w))
    rw [ih hs, hp₀, hp₁]

end Words

/-! ### Color total degrees on Hermite coefficients -/

section Field

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ}
variable {Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℂ Y]

/-- Support in color total degrees at most `d`: the coefficient vanishes at
every multi-index whose degree in some color `i` (summed over the modes of
color `i`) exceeds `d i`. -/
def ColorGood (col : Fin m → ι) (d : ι → ℕ) (v : (Fin m → ℕ) → Y) : Prop :=
  ∀ k, ¬ (∀ i, colorDeg col k i ≤ d i) → v k = 0

/-- **The color-`i` insertion `J_i = ∑_{col j = i} M_{g_j} ⊗ K_j`** on Hermite
coefficients (main TeX lines 3040-3043), `M_{g_j}` acting by
`HermiteFock.gmul` (creation plus annihilation). -/
def field (col : Fin m → ι) (K : Fin m → Y →L[ℂ] Y) (i : ι) (v : (Fin m → ℕ) → Y) :
    (Fin m → ℕ) → Y :=
  fun k => ∑ j ∈ univ.filter (fun j => col j = i), gmul j (fun l => K j (v l)) k

/-- **The cutoff `P`** (main TeX lines 3046-3047): projection onto color total
degrees at most `N_i` in every color, i.e. onto the multi-indices of
`FixedSplit.cutIdx col N`. -/
def truncN (col : Fin m → ι) (N : ι → ℕ) (v : (Fin m → ℕ) → Y) : (Fin m → ℕ) → Y :=
  fun k => if k ∈ cutIdx col N then v k else 0

omit [Fintype ι] [InnerProductSpace ℂ Y] in
/-- The vacuum `1 ⊗ u` has degree zero in every color. -/
theorem colorGood_vac (col : Fin m → ι) (u : Y) : ColorGood col (fun _ => 0) (vac u) := by
  intro k hk
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact hk fun i => by simp [colorDeg]
  simp [vac, hk0]

omit [Fintype ι] in
/-- **Degree raising for a color with several modes** (main TeX lines
3062-3066): multiplication by `g_j` changes the total degree of the color
`col j` by one and leaves every other color degree unchanged; so the color-`i`
insertion maps support in degrees `≤ d` into support in degrees
`≤ d + e_i`.  The lowering terms are retained. -/
theorem colorGood_field (col : Fin m → ι) (K : Fin m → Y →L[ℂ] Y) (d : ι → ℕ) (i : ι)
    (v : (Fin m → ℕ) → Y) (hv : ColorGood col d v) :
    ColorGood col (bump i d) (field col K i v) := by
  intro k hk
  refine Finset.sum_eq_zero fun j hj => ?_
  have hj' : col j = i := (mem_filter.1 hj).2
  simp only [not_forall, not_le] at hk
  obtain ⟨c, hc⟩ := hk
  have hiff : (col j = c) ↔ (c = i) := by rw [hj']; exact eq_comm
  simp only [bump] at hc
  have hann : v (k + unitIdx j) = 0 := hv _ fun h => by
    have h' := h c
    rw [colorDeg_add_unitIdx] at h'
    simp only [hiff] at h'
    split_ifs at hc h' <;> omega
  have hcre : cre j (fun l => K j (v l)) k = 0 := by
    by_cases hkj : k j = 0
    · exact cre_of_eq_zero j _ hkj
    · have h0 : v (k - unitIdx j) = 0 := hv _ fun h => by
        have h' := h c
        have e := colorDeg_sub_unitIdx col hkj c
        simp only [hiff] at e
        split_ifs at hc e <;> omega
      simp [cre, h0]
  simp [gmul, hcre, ann, hann]

omit [Fintype ι] in
/-- Frames acting on `𝒳` only keep every color degree. -/
theorem colorGood_frame (col : Fin m → ι) (F : Y →L[ℂ] Y) (d : ι → ℕ) (v : (Fin m → ℕ) → Y)
    (hv : ColorGood col d v) : ColorGood col d (fun l => F (v l)) := fun k hk => by
  simp [hv k hk]

omit [InnerProductSpace ℂ Y] in
/-- The cutoff fixes every vector supported in color degrees `≤ d ≤ N`. -/
theorem truncN_eq (col : Fin m → ι) (N d : ι → ℕ) (v : (Fin m → ℕ) → Y)
    (hd : ∀ i, d i ≤ N i) (hv : ColorGood col d v) : truncN col N v = v := by
  funext k
  unfold truncN
  split_ifs with h
  · rfl
  · refine (hv k fun hk => h ((mem_cutIdx col N k).2 fun i => (hk i).trans (hd i))).symm

/-- **`L:finite-word-cutoff`** (main TeX lines 3036-3058, display
`E:finite-word-cutoff`, proof 3060-3076), multi-mode form: modes `Fin m`
grouped by colors `col`, insertions `J_i = ∑_{col j = i} M_{g_j} ⊗ K_j`,
frames `F_b` acting on `𝒳` only, start `1 ⊗ u` (`u = F_0 v`), and `P` the
projection onto color total degrees `≤ N_i`.  For a finite word whose color
counts satisfy `r_i ≤ N_i`, the word with `P` before and after every insertion
equals the uncompressed word; creation followed by annihilation (all
self-contractions) is retained. -/
theorem finite_word_cutoff {β : Type*} (col : Fin m → ι) (K : Fin m → Y →L[ℂ] Y)
    (F : β → Y →L[ℂ] Y) (u : Y) (N : ι → ℕ) (w : List (ι × β))
    (hN : ∀ i, counts w i ≤ N i) :
    cut (truncN col N) (field col K) (fun b v l => F b (v l)) (vac u) w =
      raw (field col K) (fun b v l => F b (v l)) (vac u) w :=
  cut_eq_raw (fun d v => ColorGood col d v) _ _ _ _ N (colorGood_vac col u)
    (fun d i v hv => colorGood_field col K d i v hv)
    (fun d b v hv => colorGood_frame col (F b) d v hv)
    (fun d v hd hv => truncN_eq col N d v hd hv) w hN

/-- **`L:finite-word-cutoff` under the lemma's hypotheses** (main TeX lines
3036-3058): `finite_word_cutoff` with `𝒳` a complex Hilbert space (the
completeness instance is carried and unused) and bounded `K_{ij}`, `F_l`
(continuous linear maps). -/
theorem finite_word_cutoff_paper [CompleteSpace Y] {β : Type*} (col : Fin m → ι)
    (K : Fin m → Y →L[ℂ] Y) (F : β → Y →L[ℂ] Y) (u : Y) (N : ι → ℕ) (w : List (ι × β))
    (hN : ∀ i, counts w i ≤ N i) :
    cut (truncN col N) (field col K) (fun b v l => F b (v l)) (vac u) w =
      raw (field col K) (fun b v l => F b (v l)) (vac u) w :=
  finite_word_cutoff col K F u N w hN

/-- Finite sums of integrals of words, coordinatewise in the Hermite basis:
`(∑_{a∈A} ∫ f(ω_a(t)) dμ_a(t))_k` (the words `ω_a(t)` of any type `W`). -/
def wordCoef {W α Ω : Type*} [MeasurableSpace Ω] (A : Finset α) (μ : α → Measure Ω)
    (ω : α → Ω → W) (f : W → (Fin m → ℕ) → Y) : (Fin m → ℕ) → Y :=
  fun k => ∑ a ∈ A, ∫ t, f (ω a t) k ∂μ a

/-- **The last assertion of `L:finite-word-cutoff`** (main TeX lines
3056-3057, proof line 3072): the equality holds for finite sums of integrals
of words whose counts are at most the cutoffs.  Each word `ω_a(t) = (b₀, l)`
carries its own first frame `F_0 = F_{b₀}` (in a Duhamel expansion the first
free factor depends on the first insertion time), so its start is
`(I ⊗ F_0)(1 ⊗ v) = 1 ⊗ F_0 v`.  The integrands agree everywhere, so the
equality needs no integrability. -/
theorem finite_word_cutoff_integral {β α Ω : Type*} [MeasurableSpace Ω] (col : Fin m → ι)
    (K : Fin m → Y →L[ℂ] Y) (F : β → Y →L[ℂ] Y) (v : Y) (N : ι → ℕ) (A : Finset α)
    (μ : α → Measure Ω) (ω : α → Ω → β × List (ι × β))
    (hN : ∀ a ∈ A, ∀ t i, counts (ω a t).2 i ≤ N i) :
    wordCoef A μ ω (fun x => cut (truncN col N) (field col K) (fun b v l => F b (v l))
        (vac (F x.1 v)) x.2) =
      wordCoef A μ ω (fun x => raw (field col K) (fun b v l => F b (v l))
        (vac (F x.1 v)) x.2) := by
  funext k
  refine Finset.sum_congr rfl fun a ha => ?_
  have h : (fun t => cut (truncN col N) (field col K) (fun b v l => F b (v l))
      (vac (F (ω a t).1 v)) (ω a t).2 k) = fun t => raw (field col K)
        (fun b v l => F b (v l)) (vac (F (ω a t).1 v)) (ω a t).2 k :=
    funext fun t => by rw [finite_word_cutoff col K F _ N _ (hN a ha t)]
  simp only [h]

end Field

/-! ### The phase form and `FixedSplit`'s cutoff model -/

section Phase

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ}
variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X]

/-- Phase vectors `(f, g)` of the uncut Gaussian space (finitely many modes,
no degree cutoff) by their Hermite coefficients. -/
abbrev FullPhase (X : Type*) (m : ℕ) := ((Fin m → ℕ) → X) × ((Fin m → ℕ) → X)

/-- **The phase insertion `J_i(u, w) = (0, σ_i B_i u)`** (main TeX line 3861)
on the uncut space, `B_i = ∑_{col j = i} M_{g_j} ⊗ B_j`. -/
def insP (col : Fin m → ι) (σ : ι → ℝ) (B : Fin m → X →L[ℂ] X) (i : ι) (x : FullPhase X m) :
    FullPhase X m :=
  (0, fun k => ((σ i : ℝ) : ℂ) • field col B i x.1 k)

/-- A frame (free phase factor) acting on the phase pair only, pointwise in
the Hermite index. -/
def frameP (Fb : X × X →L[ℂ] X × X) (x : FullPhase X m) : FullPhase X m :=
  (fun k => (Fb (x.1 k, x.2 k)).1, fun k => (Fb (x.1 k, x.2 k)).2)

/-- The cutoff `P` on phases: `truncN` on both components. -/
def truncP (col : Fin m → ι) (N : ι → ℕ) (x : FullPhase X m) : FullPhase X m :=
  (truncN col N x.1, truncN col N x.2)

/-- The deterministic phase `(u, w)` in the Gaussian vacuum. -/
def vacP (u w : X) : FullPhase X m := (vac u, vac w)

/-- Both components supported in color degrees `≤ d`. -/
def ColorGoodP (col : Fin m → ι) (d : ι → ℕ) (x : FullPhase X m) : Prop :=
  ColorGood col d x.1 ∧ ColorGood col d x.2

omit [Fintype ι] in
/-- Degree raising for the phase insertion. -/
theorem colorGoodP_ins (col : Fin m → ι) (σ : ι → ℝ) (B : Fin m → X →L[ℂ] X) (d : ι → ℕ)
    (i : ι) (x : FullPhase X m) (hx : ColorGoodP col d x) :
    ColorGoodP col (bump i d) (insP col σ B i x) := by
  refine ⟨fun k _ => rfl, fun k hk => ?_⟩
  simp [insP, colorGood_field col B d i x.1 hx.1 k hk]

omit [Fintype ι] in
/-- Frames keep the color degrees of phases. -/
theorem colorGoodP_frame (col : Fin m → ι) (Fb : X × X →L[ℂ] X × X) (d : ι → ℕ)
    (x : FullPhase X m) (hx : ColorGoodP col d x) : ColorGoodP col d (frameP Fb x) := by
  refine ⟨fun k hk => ?_, fun k hk => ?_⟩ <;>
    simp [frameP, hx.1 k hk, hx.2 k hk, Prod.mk_zero_zero]

/-- **`E:finite-word-cutoff` in the phase form of `P:interval-coefficients`**
(main TeX lines 4163-4170: "with the spatial phase space as `𝒳` and free phase
factors between insertions"): for a word with counts `≤ N`, the cutoff word
equals the uncut word, for every start of Gaussian degree zero (for
instance `(I ⊗ F_0)` applied to the vacuum phase, `colorGoodP_start`). -/
theorem phase_word_cutoff {β : Type*} (col : Fin m → ι) (σ : ι → ℝ) (B : Fin m → X →L[ℂ] X)
    (Fr : β → X × X →L[ℂ] X × X) (x₀ : FullPhase X m) (hx₀ : ColorGoodP col (fun _ => 0) x₀)
    (N : ι → ℕ) (l : List (ι × β)) (hN : ∀ i, counts l i ≤ N i) :
    cut (truncP col N) (insP col σ B) (fun b => frameP (Fr b)) x₀ l =
      raw (insP col σ B) (fun b => frameP (Fr b)) x₀ l :=
  cut_eq_raw (fun d x => ColorGoodP col d x) _ _ _ _ N hx₀
    (fun d i x hx => colorGoodP_ins col σ B d i x hx)
    (fun d b x hx => colorGoodP_frame col (Fr b) d x hx)
    (fun d x hd hx => Prod.ext (truncN_eq col N d x.1 hd hx.1) (truncN_eq col N d x.2 hd hx.2))
    l hN

omit [Fintype ι] in
/-- The start `(I ⊗ F_0)(1 ⊗ (u, w))` of a word has Gaussian degree zero. -/
theorem colorGoodP_start (col : Fin m → ι) (Fb : X × X →L[ℂ] X × X) (u w : X) :
    ColorGoodP col (fun _ => 0) (frameP Fb (vacP u w)) :=
  colorGoodP_frame col Fb _ _ ⟨colorGood_vac col u, colorGood_vac col w⟩

/-- Extension by zero of a cutoff phase (`PhaseSp`) to the uncut space. -/
def extP {col : Fin m → ι} {N : ι → ℕ} (y : PhaseSp X col N) : FullPhase X m :=
  (extC y.1, extC y.2)

/-- A frame acting pointwise on cutoff phases. -/
def frameC {col : Fin m → ι} {N : ι → ℕ} (Fb : X × X →L[ℂ] X × X) (y : PhaseSp X col N) :
    PhaseSp X col N :=
  (fun k => (Fb (y.1 k, y.2 k)).1, fun k => (Fb (y.1 k, y.2 k)).2)

/-- **The word of the cutoff evolution on `FixedSplit`'s model**: insertions
`FixedSplit.fockJ σ B` (the field followed by the cutoff), frames acting
pointwise, start `y₀` (in the Duhamel expansion `(I ⊗ F_0)` applied to
`FixedSplit.vacPhase u w`, `startC`). -/
def cutWordC {β : Type*} (col : Fin m → ι) (N : ι → ℕ) (σ : ι → ℝ) (B : Fin m → X →L[ℂ] X)
    (Fr : β → X × X →L[ℂ] X × X) (y₀ : PhaseSp X col N) : List (ι × β) → PhaseSp X col N :=
  raw (fun i y => fockJ σ B i y) (fun b y => frameC (Fr b) y) y₀

/-- The start `(I ⊗ F_0)(1 ⊗ (u, w))` on the cutoff space. -/
def startC {col : Fin m → ι} {N : ι → ℕ} (Fb : X × X →L[ℂ] X × X) (u w : X) :
    PhaseSp X col N :=
  frameC Fb (vacPhase u w)

omit [InnerProductSpace ℂ X] in
/-- Auxiliary (Lean route): `extC f` at a retained index. -/
theorem extC_mem {col : Fin m → ι} {N : ι → ℕ} (f : CoefSp X col N) {k : Fin m → ℕ}
    (hk : k ∈ cutIdx col N) : extC f k = f ⟨k, hk⟩ := by
  simp [extC, hk]

omit [InnerProductSpace ℂ X] in
/-- Auxiliary (Lean route): `extC f` vanishes off the cutoff. -/
theorem extC_not_mem {col : Fin m → ι} {N : ι → ℕ} (f : CoefSp X col N) {k : Fin m → ℕ}
    (hk : k ∉ cutIdx col N) : extC f k = 0 := by
  simp [extC, hk]

omit [InnerProductSpace ℂ X] in
/-- Auxiliary (Lean route): `0` is a retained multi-index. -/
theorem zero_mem_cutIdx (col : Fin m → ι) (N : ι → ℕ) : (0 : Fin m → ℕ) ∈ cutIdx col N :=
  (mem_cutIdx col N 0).2 fun i => by simp [colorDeg]

omit [InnerProductSpace ℂ X] in
/-- The vacuum phase extends to the uncut vacuum. -/
theorem extP_vacPhase (col : Fin m → ι) (N : ι → ℕ) (u w : X) :
    extP (vacPhase u w : PhaseSp X col N) = vacP u w := by
  have h : ∀ y : X, extC (vacC y : CoefSp X col N) = vac y := by
    intro y
    funext k
    by_cases hk : k ∈ cutIdx col N
    · simp [extC, hk, vacC, vac]
    · have hk0 : k ≠ 0 := fun h => hk (h ▸ zero_mem_cutIdx col N)
      simp [extC, hk, vac, hk0]
  simp [extP, vacPhase, vacP, h]

/-- Extension commutes with pointwise frames. -/
theorem extP_frameC {col : Fin m → ι} {N : ι → ℕ} (Fb : X × X →L[ℂ] X × X)
    (y : PhaseSp X col N) : extP (frameC Fb y) = frameP Fb (extP y) := by
  refine Prod.ext (funext fun k => ?_) (funext fun k => ?_) <;>
  by_cases hk : k ∈ cutIdx col N <;> simp [extP, frameC, frameP, extC, hk, Prod.mk_zero_zero]

/-- The cutoff insertion `fockJ` is `P J_i P` on the uncut space. -/
theorem extP_fockJ (col : Fin m → ι) (N : ι → ℕ) (σ : ι → ℝ) (B : Fin m → X →L[ℂ] X) (i : ι)
    (y : PhaseSp X col N) :
    extP (fockJ σ B i y) = truncP col N (insP col σ B i (extP y)) := by
  refine Prod.ext (funext fun k => ?_) (funext fun k => ?_) <;>
  by_cases hk : k ∈ cutIdx col N <;>
    simp [extP, fockJ, insField, truncP, truncN, insP, field, extC, hk]

omit [InnerProductSpace ℂ X] in
/-- The extension of a cutoff phase is fixed by the cutoff. -/
theorem truncP_extP (col : Fin m → ι) (N : ι → ℕ) (y : PhaseSp X col N) :
    truncP col N (extP y) = extP y := by
  refine Prod.ext (funext fun k => ?_) (funext fun k => ?_) <;>
  by_cases hk : k ∈ cutIdx col N <;> simp [extP, truncP, truncN, extC, hk]

/-- **The bridge**: the cutoff word of `FixedSplit`'s model, extended by zero,
is the word with `P` before and after every insertion on the uncut space (the
left side of `E:finite-word-cutoff`), for every word. -/
theorem extP_cutWordC {β : Type*} (col : Fin m → ι) (N : ι → ℕ) (σ : ι → ℝ)
    (B : Fin m → X →L[ℂ] X) (Fr : β → X × X →L[ℂ] X × X) (y₀ : PhaseSp X col N)
    (l : List (ι × β)) :
    extP (cutWordC col N σ B Fr y₀ l) =
      cut (truncP col N) (insP col σ B) (fun b => frameP (Fr b)) (extP y₀) l := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    obtain ⟨i, b⟩ := a
    change extP (frameC (Fr b) (fockJ σ B i (cutWordC col N σ B Fr y₀ l))) =
      frameP (Fr b) (truncP col N (insP col σ B i (truncP col N
        (cut (truncP col N) (insP col σ B) (fun b => frameP (Fr b)) (extP y₀) l))))
    rw [← ih, truncP_extP, extP_frameC, extP_fockJ]

/-- **`L:finite-word-cutoff` on `FixedSplit`'s cutoff model** (main TeX lines
3036-3058 as applied at lines 4163-4170): for a word with counts `≤ N`, the
cutoff word (insertions `fockJ`, start `startC`), extended by zero, is the
uncut word (started at `(I ⊗ F_0)(1 ⊗ (u, w))`). -/
theorem cutWordC_eq_raw {β : Type*} (col : Fin m → ι) (N : ι → ℕ) (σ : ι → ℝ)
    (B : Fin m → X →L[ℂ] X) (Fr : β → X × X →L[ℂ] X × X) (b₀ : β) (u w : X)
    (l : List (ι × β)) (hN : ∀ i, counts l i ≤ N i) :
    extP (cutWordC col N σ B Fr (startC (Fr b₀) u w) l) =
      raw (insP col σ B) (fun b => frameP (Fr b)) (frameP (Fr b₀) (vacP u w)) l := by
  have h0 : extP (startC (Fr b₀) u w : PhaseSp X col N) = frameP (Fr b₀) (vacP u w) := by
    rw [startC, extP_frameC, extP_vacPhase]
  rw [extP_cutWordC, h0, phase_word_cutoff col σ B Fr _ (colorGoodP_start col _ u w) N l hN]

/-- Finite sums of integrals of phase words, coordinatewise. -/
def wordCoefP {W α Ω : Type*} [MeasurableSpace Ω] (A : Finset α) (μ : α → Measure Ω)
    (ω : α → Ω → W) (f : W → FullPhase X m) : FullPhase X m :=
  (fun k => ∑ a ∈ A, ∫ t, (f (ω a t)).1 k ∂μ a, fun k => ∑ a ∈ A, ∫ t, (f (ω a t)).2 k ∂μ a)

/-- **Supplied input `DuhamelWords`** (the Duhamel expansion of the ordinary
coefficients, main TeX lines 4092-4097 and 4166-4170: "Their Duhamel time
integrals and finite word sums preserve the equality").  The uncut ordinary
coefficient `U_r v` and the ordinary coefficient `c_r` of the evolution at
cutoff `N` are the same finite sum `∑_{a∈A} ∫ · dμ_a` of words
`ω_a(t) = (b₀, l)`, each with exactly `r_i` insertions of color `i` (the
coefficient of `z^r`) and first free factor `F_0 = Fr b₀`: of the uncut words
(`raw` with `insP`, start `(I ⊗ F_0)(1 ⊗ (u, w))`) for `U_r`, of the cutoff
words (`cutWordC` with `fockJ`, start `startC`, extended by zero) for `c_r`.
The frames `Fr` are the free phase factors between insertions, and the
vacuum phase `(u, w)` is the initial datum.  The evolutions are not
constructed in the package, so this expansion is supplied. -/
def DuhamelWords {β α Ω : Type*} [MeasurableSpace Ω] (col : Fin m → ι) (N : ι → ℕ)
    (σ : ι → ℝ) (B : Fin m → X →L[ℂ] X) (Fr : β → X × X →L[ℂ] X × X) (u w : X)
    (A : Finset α) (μ : α → Measure Ω) (ω : α → Ω → β × List (ι × β)) (r : ι → ℕ)
    (U : FullPhase X m) (c : PhaseSp X col N) : Prop :=
  (∀ a ∈ A, ∀ t, counts (ω a t).2 = r) ∧
    U = wordCoefP A μ ω (fun x => raw (insP col σ B) (fun b => frameP (Fr b))
      (frameP (Fr x.1) (vacP u w)) x.2) ∧
    extP c = wordCoefP A μ ω (fun x => extP (cutWordC col N σ B Fr (startC (Fr x.1) u w) x.2))

/-- **The cutoff preserves the selected coefficient exactly** (main TeX lines
4163-4170): under the Duhamel word expansion, for `r_i ≤ N_i` the ordinary
coefficient of the cutoff evolution, extended by zero, is the uncut
coefficient `U_r v`. -/
theorem coef_cutoff_eq {β α Ω : Type*} [MeasurableSpace Ω] (col : Fin m → ι) (N : ι → ℕ)
    (σ : ι → ℝ) (B : Fin m → X →L[ℂ] X) (Fr : β → X × X →L[ℂ] X × X) (u w : X)
    (A : Finset α) (μ : α → Measure Ω) (ω : α → Ω → β × List (ι × β)) (r : ι → ℕ)
    (U : FullPhase X m) (c : PhaseSp X col N)
    (hD : DuhamelWords col N σ B Fr u w A μ ω r U c) (hr : ∀ i, r i ≤ N i) :
    extP c = U := by
  obtain ⟨hcount, hU, hc⟩ := hD
  have h : ∀ a ∈ A, ∀ t, extP (cutWordC col N σ B Fr (startC (Fr (ω a t).1) u w) (ω a t).2) =
      raw (insP col σ B) (fun b => frameP (Fr b)) (frameP (Fr (ω a t).1) (vacP u w))
        (ω a t).2 := fun a ha t =>
    cutWordC_eq_raw col N σ B Fr _ u w _ fun i => (hcount a ha t ▸ hr i)
  rw [hc, hU]
  refine Prod.ext (funext fun k => Finset.sum_congr rfl fun a ha => ?_)
    (funext fun k => Finset.sum_congr rfl fun a ha => ?_) <;>
  · simp only [h a ha]

/-- **The inner product of `𝓗_ρ = L²(Ω; X_ρ)` on the uncut space**
(main TeX line 4142, phase norm lines 3370-3372): `∑_k ⟨f_k, f'_k⟩ +
⟨S_ρ g_k, S_ρ g'_k⟩` over all multi-indices, `S_ρ` standing for
`A_ρ^{-1/2}` as in `FixedSplit.fockEmb`. -/
def fullInner (S : ℝ → X →L[ℂ] X) (ρ : ℝ) (x y : FullPhase X m) : ℂ :=
  ∑' k, (inner ℂ (x.1 k) (y.1 k) + inner ℂ (S ρ (x.2 k)) (S ρ (y.2 k)))

/-- On extensions of cutoff phases the uncut inner product is the cutoff inner
product of `FixedSplit` (through `fockEmb`). -/
theorem fullInner_extP {col : Fin m → ι} {N : ι → ℕ} (S : ℝ → X →L[ℂ] X) (ρ : ℝ)
    (y y' : PhaseSp X col N) :
    fullInner S ρ (extP y) (extP y') = inner ℂ (fockEmb S ρ y) (fockEmb S ρ y') := by
  unfold fullInner
  rw [tsum_eq_sum (s := cutIdx col N) fun k hk => by simp [extP, extC, hk]]
  rw [← Finset.sum_coe_sort (cutIdx col N), PiLp.inner_apply, Fintype.sum_sum_type,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [extP, extC_mem _ k.2, fockEmb]

/-- **Identification of `Q_{r,q}`** (main TeX lines 4142-4144 with lines
4163-4170): under the Duhamel word expansion of `U_r`, `U_q` and the cutoff
coefficients `c_r`, `c_q` (`r, q ≤ N`), the inner product
`⟨U_r v, U_q v⟩_{𝓗_ρ}` equals the cutoff inner product
`⟨fockEmb (c_r), fockEmb (c_q)⟩`. -/
theorem Q_identification {β α Ω : Type*} [MeasurableSpace Ω] (col : Fin m → ι) (N : ι → ℕ)
    (σ : ι → ℝ) (B : Fin m → X →L[ℂ] X) (Fr : β → X × X →L[ℂ] X × X) (u w : X)
    (S : ℝ → X →L[ℂ] X) (ρ : ℝ) (A₁ A₂ : Finset α) (μ₁ μ₂ : α → Measure Ω)
    (ω₁ ω₂ : α → Ω → β × List (ι × β)) (r q : ι → ℕ) (U : (ι → ℕ) → FullPhase X m)
    (c : (ι → ℕ) → PhaseSp X col N)
    (hDr : DuhamelWords col N σ B Fr u w A₁ μ₁ ω₁ r (U r) (c r))
    (hDq : DuhamelWords col N σ B Fr u w A₂ μ₂ ω₂ q (U q) (c q))
    (hr : ∀ i, r i ≤ N i) (hq : ∀ i, q i ≤ N i) :
    fullInner S ρ (U r) (U q) = inner ℂ (fockEmb S ρ (c r)) (fockEmb S ρ (c q)) := by
  rw [← coef_cutoff_eq col N σ B Fr u w A₁ μ₁ ω₁ r (U r) (c r) hDr hr,
    ← coef_cutoff_eq col N σ B Fr u w A₂ μ₂ ω₂ q (U q) (c q) hDq hq, fullInner_extP]

end Phase

/-- **Step row of `P:interval-coefficients` with `L:fixed-split` and
`L:finite-word-cutoff` supplied by their proofs** (main TeX lines 4054-4066,
proof 4068-4228): `FixedSplit.interval_coefficient_assembly_paper_fixed`
WITHOUT its hypothesis `hQ`.  `Q_{r,q}` is now the real part of
`⟨U_r v, U_q v⟩_{𝓗_{1/T}}` (line 4142) for the uncut ordinary coefficients
`U`, and `hsplits` (`E:interval-energy-splits` with the reflection parity,
lines 4145-4157) is stated for it.  For every degree split `κ` and split
`p = (r, q)` the uncut coefficients `U_r`, `U_q` and the coefficients
`cf κ r`, `cf κ q` of the evolution at cutoff `N_i = 2κ_i` satisfy the
Duhamel word expansion `DuhamelWords` with insertions `B_j = S_b M_{e_j} S_b`
(the `B` of `SplitInputs`) and the same word data `(A, ν, ω)` for `U_r` and
`cf κ r`; then `|Q| ≤ |⟨cf κ r, cf κ q⟩|` (what `hQ` assumed) is proved by
`Q_identification`.  Every other hypothesis is exactly that of
`interval_coefficient_assembly_paper_fixed`. -/
theorem interval_coefficient_assembly_paper_words {d : ℕ} {alpha alpha0 : ℝ}
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
  refine interval_coefficient_assembly_paper_fixed hH h σ a b
    (fun p => (fullInner S (1 / T) (U fun i => (p i).1) (U fun i => (p i).2)).re) hRdef hRpos
    hk hT hδ hh hσpos hlen hσ hsplits hIlen hab col S Mlt Pb u w hSs hSn hScmp hM hPs hPP hPS
    hcol hV P cf (fun κ hκ p hp => ?_) hin
  have hpp : ∀ i, (p i).1 + (p i).2 = 2 * κ i := fun i =>
    mem_antidiagonal.1 (Fintype.mem_piFinset.1 hp i)
  obtain ⟨hD1, hD2⟩ := hword κ hκ p hp
  rw [Q_identification col (fun i => 2 * κ i) σ (fun j => Pb ∘L Mlt j ∘L Pb) Fr u w S (1 / T)
    (A fun i => (p i).1) (A fun i => (p i).2) (ν fun i => (p i).1) (ν fun i => (p i).2)
    (ω fun i => (p i).1) (ω fun i => (p i).2) (fun i => (p i).1) (fun i => (p i).2) U (cf κ)
    hD1 hD2 (fun i => by have := hpp i; omega) (fun i => by have := hpp i; omega)]
  exact Complex.abs_re_le_norm _

end StratonovichHAMSecondMoment.FiniteWordCutoff
