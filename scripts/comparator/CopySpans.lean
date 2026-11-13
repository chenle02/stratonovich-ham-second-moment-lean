/-
Copyright 2026 Le Chen. SPDX-License-Identifier: Apache-2.0

Input of `gen_defs.py` (read-only; writes nothing):

  lake env lean --run scripts/comparator/CopySpans.lean > <spans.tsv>

For every theorem of `comparator.json` (`StratonovichHamSecondMomentLeanAudit.D`, `D` the
claimed declaration), it walks the project constants reachable from the type of `D`
(through the types and values of project definitions, theorems and inductives) and prints
`REACH<TAB>name<TAB>module<TAB>first line<TAB>last line` (`-` when the constant has no
source range, e.g. a generated `_proof_N`), then `ALL<TAB>name<TAB>module<TAB>first<TAB>last`
for every ranged declaration of every project module.
-/
import Lean
import StratonovichHAMSecondMoment
open Lean

def projMod? (env : Environment) (c : Name) : Option Name := do
  let i ← env.getModuleIdxFor? c
  let m := env.header.moduleNames[i.toNat]!
  if (`StratonovichHAMAudit).isPrefixOf m || (`StratonovichHAMSecondMoment).isPrefixOf m then
    some m else none

def main : IO UInt32 := do
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := `StratonovichHAMSecondMoment }] {}
  let cfg ← IO.ofExcept <| Json.parse (← IO.FS.readFile "comparator.json")
  let names ← IO.ofExcept <| cfg.getObjValAs? (Array String) "theorem_names"
  let pfx := "StratonovichHamSecondMomentLeanAudit."
  let mut work : Array Name := #[]
  for s in names do
    unless s.startsWith pfx do throw <| IO.userError s!"{s}: not under {pfx}"
    let d := (s.drop pfx.length).toString.toName
    let some ci := env.find? d | throw <| IO.userError s!"unknown declaration {d}"
    work := work ++ ci.type.getUsedConstants
  let mut seen : NameSet := {}
  let mut reach : Array (Name × Name) := #[]
  while h : work.size > 0 do
    let c := work.back
    work := work.pop
    if seen.contains c then continue
    seen := seen.insert c
    let some m := projMod? env c | continue
    let some cc := env.find? c | continue
    reach := reach.push (c, m)
    work := work ++ cc.type.getUsedConstants
    match cc with
    | .defnInfo v => work := work ++ v.value.getUsedConstants
    | .thmInfo v => work := work ++ v.value.getUsedConstants
    | .inductInfo v => work := work ++ v.ctors.toArray
    | _ => pure ()
  let ctx : Core.Context := { fileName := "<CopySpans>", fileMap := default }
  let st : Core.State := { env }
  let span (n : Name) : IO String := do
    let (r, _) ← (findDeclarationRanges? n : CoreM _).toIO ctx st
    return match r with
      | some r => s!"{r.range.pos.line}\t{r.range.endPos.line}"
      | none => "-\t-"
  for (c, m) in reach.qsort (fun a b => a.1.toString < b.1.toString) do
    IO.println s!"REACH\t{c}\t{m}\t{← span c}"
  for mi in [0:env.header.moduleNames.size] do
    let m := env.header.moduleNames[mi]!
    unless (`StratonovichHAMAudit).isPrefixOf m || (`StratonovichHAMSecondMoment).isPrefixOf m do continue
    for n in env.header.moduleData[mi]!.constNames do
      let s ← span n
      unless s.startsWith "-" do IO.println s!"ALL\t{n}\t{m}\t{s}"
  return 0
