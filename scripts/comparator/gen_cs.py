"""Write Challenge.lean and Solution.lean (run from the repository root:
python3 scripts/comparator/gen_cs.py) from scripts/comparator/scaffold.json, the
scaffold block `lean-pkg comparator config --from-claims NAME --from-output TYPES.json`
wrote into lean-pkg-signoff.json (moved here once Challenge and Solution existed): the pre-filled statement of
each entry, with every project constant name N written as StratonovichHamSecondMomentLeanAudit.N
(the verbatim copy in ChallengeDefs). An entry with
scripts/comparator/manual/<decl>.{challenge,solution}.lean is taken from those files
(a printed type that failed lean-pkg's round-trip check); one with <decl>.proof.lean
keeps the generated statement and replaces its proof (a bridge, see manual/Bridge.lean,
which is inserted at the top of Solution)."""
# SPDX-FileCopyrightText: 2026 Le Chen
# SPDX-License-Identifier: Apache-2.0
import json, re, sys, os, glob
W = "."
PFX = "StratonovichHamSecondMomentLeanAudit"
DPFX = "StratonovichHamSecondMomentLeanDefs"
t = json.load(open(f"{W}/scripts/comparator/scaffold.json"))["todo"]
names = json.load(open(f"{W}/comparator.json"))["theorem_names"]
order = {n: i for i, n in enumerate(names)}
t.sort(key=lambda e: order[e["theorem_name"]])
proj = re.compile(r"(?<![\w.'@])(StratonovichHAMAudit|StratonovichHAMSecondMoment)\.")
defs = sorted(p[:-5].replace("/", ".") for p in glob.glob("ChallengeDefs/**/*.lean", recursive=True))
def head(imports):
    return ["module", ""] + [f"public import {i}" for i in imports] + [""]
ch = head(["Mathlib"] + defs) + [
    "/-!",
    "# Challenge (trusted): the statements the comparator checks",
    "",
    "One theorem per theorem claim of `claims.yaml`, named",
    f"`{PFX}.<decl>`, each proved by `sorry`. Each statement is the claimed",
    "declaration's elaborated type as Lean prints it (lean-pkg comparator config",
    "--challenge-from-type, round-trip checked), with the project definitions it mentions",
    "replaced by their verbatim copies in `ChallengeDefs` (same name under the prefix",
    f"`{DPFX}`). `scripts/comparator/CheckFidelity.lean` checks with `Expr`",
    "equality that every statement equals the claimed declaration's type and every copy",
    "the project definition, up to that renaming. Imports: Mathlib and `ChallengeDefs` only.",
    "-/", "", "public section", "", "set_option autoImplicit false", ""]
so = [f"import {i}" for i in ["Mathlib"] + defs + ["StratonovichHAMSecondMoment"]] + ["",
    "/-!",
    "# Solution (untrusted): each Challenge theorem, proved from the project",
    "",
    "Same names and statements as `Challenge`; each proof applies the claimed project",
    "declaration (`exact @_root_.<decl>`, accepted because the `ChallengeDefs` copies unfold",
    "to the same terms), or a bridge proof where the statement mentions a copied",
    "inductive type or structure. Not a `module`: the project umbrella is not one (its",
    "seam `StratonovichHAMAudit.HermiteWord` predates the module system), and a module",
    "cannot import it. `lake comparator` compares the exported constants either way.",
    "-/", "", "set_option autoImplicit false",
    "-- the printed statements name instance binders they never mention (`inst_1`, ...)",
    "set_option linter.unusedVariables false", ""]
manual_dir = f"{W}/scripts/comparator/manual"
import yaml
SUMMARY = {c["decl"]: c.get("summary", "") for c in yaml.safe_load(open(f"{W}/claims.yaml"))["claims"]}
nman = 0
so += [open(f"{manual_dir}/Bridge.lean").read().rstrip("\n"), ""]
for e in t:
    d = e["decl"]
    mc = f"{manual_dir}/{d}.challenge.lean"
    if os.path.exists(mc):
        c = open(mc).read().rstrip("\n"); s = open(f"{manual_dir}/{d}.solution.lean").read().rstrip("\n"); nman += 1
    elif os.path.exists(f"{manual_dir}/{d}.open"):
        # a printed type that elaborates only under the module's scoped instances or
        # notation: the printed text, under `open scoped ... in` (CheckFidelity decides)
        op = open(f"{manual_dir}/{d}.open").read().strip()
        ty = e.get("printed_type") or e["type"]
        lv = []
        for u in re.findall(r"\bu_\d+\b", ty):
            if u not in lv: lv.append(u)
        lvs = (".{" + ", ".join(lv) + "}") if lv else ""
        body = "\n".join("    " + l for l in ty.split("\n"))
        summ = re.search(r"/--.*?-/", e["challenge"], re.S)
        doc = summ.group(0) + "\n" if summ else f"/-- {SUMMARY[d]} -/\n"
        hdr = f"{op}\n{doc}theorem {e['theorem_name']}{lvs} :\n{body} := by\n"
        c = proj.sub(DPFX + r".\1.", hdr + "  sorry")
        s = proj.sub(DPFX + r".\1.", hdr + f"  exact @_root_.{d}")
        if os.path.exists(f"{manual_dir}/{d}.proof.lean"):
            s = proj.sub(DPFX + r".\1.", hdr) + open(f"{manual_dir}/{d}.proof.lean").read().rstrip("\n")
        nman += 1
    else:
        assert "type" in e, d
        c = "\n".join(l for l in e["challenge"].split("\n") if not l.startswith("-- TODO"))
        s = e["solution"]
        c = proj.sub(DPFX + r".\1.", c)
        s = proj.sub(DPFX + r".\1.", s)
        mp = f"{manual_dir}/{d}.proof.lean"
        if os.path.exists(mp):
            last = f"  exact @_root_.{d}"
            assert s.endswith(last), d
            s = s[: -len(last)] + open(mp).read().rstrip("\n"); nman += 1
    assert "TODO" not in c and "TODO" not in s, d
    ch += [c, ""]; so += [s, ""]
ch += ["end", ""]
open(f"{W}/Challenge.lean", "w").write("\n".join(ch))
open(f"{W}/Solution.lean", "w").write("\n".join(so))
print(len(t), "entries,", nman, "manual")
