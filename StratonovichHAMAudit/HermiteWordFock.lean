/-
Copyright 2026 Le Chen. SPDX-License-Identifier: Apache-2.0

Application of `StratonovichHAMAudit.HermiteWord.cut_eq_raw` (the finite-word induction of
`L:finite-word-cutoff`, main TeX `notes/notes_stratonovich_ham_second_moment.tex`, statement
lines 2531-2553 and proof 2555-2571 at revision a284420; display `E:finite-word-cutoff`,
lines 2543-2550) to the concrete Gaussian Fock model of `StratonovichHAMSecondMoment.FockForm`
(wave item L9-H).

`HermiteWord` predates the module system and is not a `module`, so a `module` file cannot
import it; this file is not a `module` and imports both.

Model (that of `FockForm`): coefficient vectors `(Fin m → ℕ) → X` over `m` colors with ONE
standard Gaussian mode per color (the TeX allows `m_i` modes in color `i`); the insertion of
color `i` is `J_i v = gmul i (K_i v)`, multiplication by `g_i` tensored with a bounded
operator `K_i` on `X`; the frames `F_b` act on `X` only; the cutoff `P = truncC Nc` projects
each color onto Hermite degree at most `N_c`; the start vector is `vac u = 1 ⊗ u` (the TeX's
`(I ⊗ F_0)(1 ⊗ v)` with `u = F_0 v`).  The four hypotheses of `cut_eq_raw` are
`FockForm.goodDeg_vac`, `goodDeg_insert`, `goodDeg_frame` and `truncC_eq`.

Narrower than the TeX: one mode per color, finite words only (the sentence on finite sums and
Bochner integrals of words, lines 2551-2552, is not formalized), and `X` an inner product space
in `Type` (the universe of `HermiteWord`), with no completeness used.
-/
import StratonovichHAMAudit.HermiteWord
import StratonovichHAMSecondMoment.FockForm

namespace StratonovichHAMAudit.HermiteWordFock

open StratonovichHAMAudit.HermiteWord
open StratonovichHAMSecondMoment.HermiteFock (gmul vac)
open StratonovichHAMSecondMoment.FockForm (GoodDeg truncC goodDeg_vac goodDeg_insert
  goodDeg_frame truncC_eq)

/-- **`E:finite-word-cutoff` for the Fock model of `FockForm`** (`L:finite-word-cutoff`, main
TeX lines 2531-2553, proof 2555-2571 at a284420), one Gaussian mode per color: for colors
`Fin m`, insertions `J_i v = g_i ⊗ K_i` (`gmul i (K_i v)`), frames `T_b` acting on `X`, a start
vector `u`, per-color cutoffs `N_c` and a finite word `w` whose color counts are at most the
cutoffs, the cut word (with `P = truncC Nc` before and after every insertion) equals the raw
word.  The lowering terms of `g_i` are retained.  This is `HermiteWord.cut_eq_raw` with the
hypotheses supplied by `FockForm.goodDeg_vac`, `goodDeg_insert`, `goodDeg_frame` and
`truncC_eq`. -/
theorem cut_eq_raw_fock {X : Type} [NormedAddCommGroup X] [InnerProductSpace ℂ X] {m : ℕ}
    {B : Type} (K : Fin m → X →L[ℂ] X) (T : B → X →L[ℂ] X) (u : X) (Nc : Fin m → ℕ)
    (w : List (Fin m × B)) (hN : ∀ c, counts w c ≤ Nc c) :
    cut (truncC Nc) (fun i v => gmul i (fun l => K i (v l))) (fun b v => fun l => T b (v l))
        (vac u) w =
      raw (fun i v => gmul i (fun l => K i (v l))) (fun b v => fun l => T b (v l)) (vac u) w :=
  cut_eq_raw GoodDeg _ _ (truncC Nc) (vac u) Nc (goodDeg_vac u)
    (fun d i v hv => goodDeg_insert K d i v hv) (fun d b v hv => goodDeg_frame (T b) d v hv)
    (fun d v hd hv => truncC_eq Nc d v hd hv) w hN

end StratonovichHAMAudit.HermiteWordFock
