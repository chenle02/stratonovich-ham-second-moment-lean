/-
Refutation for the hypothesis `TimeAtomless` of the strong-measurability theorem
`StratonovichHAMSecondMoment.TerminalWickInputs.aestronglyMeasurable_prodL2_of_cell`
(`L:terminal-wick`, main TeX lines 4357-4359 at edf7085f: "the product is strongly
measurable in `L²` on the stated pieces", which needs the cut times to be null for
the chain measure).

Wrong variant: every finite measure on tuples of points has no time atoms (so the
hypothesis would be vacuous).  Counterexample: `d = 1`, `T = 1`, the unit mass at
the one-point tuple `(0, 0)`: the set `{z : time of z_1 = 0}` has mass `1`.
`time_atoms_contrast` is the package theorem: the constructed `g_n^{T,x}` has no
time atoms.  No junk-value reliance.

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.TerminalWickInputs

set_option autoImplicit false

open MeasureTheory StratonovichHAMSecondMoment TerminalWick TerminalWickInputs

namespace Refutations.TerminalWickInputs

/-- The package fact: `g_n^{1,0}` (`d = 1`) has no time atoms. -/
theorem time_atoms_contrast :
    TimeAtomless (fun n => chainMeasure 1 n 1 zero_le_one 0) :=
  timeAtomless_chainMeasure 1 1 zero_le_one 0

/-- Auxiliary: the point `(0, 0)` of `[0,1] × ℝ`. -/
def origin : Pt 1 1 := (⟨0, le_rfl, zero_le_one⟩, 0)

/-- "Every finite chain measure has no time atoms" is false. -/
theorem time_atoms_refuted :
    ¬ (∀ ν : ∀ n : ℕ, Measure (Fin n → Pt 1 1), (∀ n, IsFiniteMeasure (ν n)) →
      TimeAtomless ν) := by
  intro h
  have h1 := h (fun _ => Measure.dirac fun _ => origin) (fun _ => inferInstance) 1 0 0
  have hm : (fun _ : Fin 1 => origin) ∈ {z : Fin 1 → Pt 1 1 | ((z 0).1 : ℝ) = 0} := rfl
  rw [Measure.dirac_apply_of_mem hm] at h1
  exact one_ne_zero h1

end Refutations.TerminalWickInputs
