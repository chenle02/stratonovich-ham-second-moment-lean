"""Generate ChallengeDefs/<project module path>.lean: verbatim copies of the project
definitions reachable from the claimed theorem types, under the namespace prefix
StratonovichHamSecondMomentLeanDefs (Challenge theorems use StratonovichHamSecondMomentLeanAudit,
so a claimed theorem that a definition needs can be copied too). Every other declaration of the module is dropped.

  lake env lean --run scripts/comparator/CopySpans.lean > /tmp/spans.tsv
  python3 scripts/comparator/gen_defs.py /tmp/spans.tsv

Run from the repository root. Then `lake build Challenge` and
`lake env lean --run scripts/comparator/CheckFidelity.lean` (which checks every copy)."""
# SPDX-FileCopyrightText: 2026 Le Chen
# SPDX-License-Identifier: Apache-2.0
import re, sys, os, collections
SPANS, W = sys.argv[1], "."
PFX = "StratonovichHamSecondMomentLeanDefs"
reach, allspans = {}, collections.defaultdict(list)
for line in open(SPANS):
    p = line.rstrip("\n").split("\t")
    if p[0] == "ALL":
        _, n, m, a, b = p; allspans[m].append((n, int(a), int(b)))
    elif p[0] == "REACH":
        _, n, m, a, b = p
        # a private proof auxiliary of a copied theorem is regenerated with the copy
        if n.startswith("_private."): continue
        reach[n] = (m, None if a == "-" else (int(a), int(b)))
mods = sorted({m for m, _ in reach.values()})
keep = collections.defaultdict(set)
for n, (m, r) in reach.items():
    if r: keep[m].add((r[0], r[1]))
# every reachable constant without a range must have a kept ancestor declaration
for n, (m, r) in reach.items():
    if r: continue
    parts = n.split(".")
    ok = False
    for k in range(len(parts) - 1, 0, -1):
        anc = ".".join(parts[:k])
        hit = [(a, b) for (x, a, b) in allspans[m] if x == anc]
        if hit:
            keep[m].add(hit[0]); ok = True
            break
        # an equation lemma (`f.eq_1`) is stored in the module that first asked for it,
        # which need not be the module declaring `f`: keep `f` in its own module
        hit = [(mm, a, b) for mm in allspans for (x, a, b) in allspans[mm] if x == anc]
        if hit:
            mm, a, b = hit[0]
            keep[mm].add((a, b)); ok = True
            if mm not in mods: mods.append(mm); mods.sort()
            break
    assert ok, n
def defs_mod(m): return "ChallengeDefs." + m
def resolve(imp, seen=None):
    """A project import becomes its ChallengeDefs copy when one is generated, else the
    imports of that module (recursively), so no Mathlib import is lost."""
    if not imp.startswith("StratonovichHAM"): return [imp]
    if imp in mods: return [defs_mod(imp)]
    seen = seen or set()
    if imp in seen: return []
    seen.add(imp)
    out = []
    for l in open(f"{W}/{imp.replace('.', '/')}.lean", encoding="utf-8"):
        if re.match(r"^(public )?import ", l):
            for x in resolve(l.split()[-1], seen):
                if x not in out: out.append(x)
    return out
for m in mods:
    src = f"{W}/{m.replace('.', '/')}.lean"
    lines = open(src, encoding="utf-8").read().split("\n")
    drop = set()
    kept = sorted(keep[m])
    for n, a, b in allspans[m]:
        if any(ka <= a and b <= kb for ka, kb in kept): continue
        # notation commands are kept (the copied definitions may be written with them)
        if any(re.match(r"^\s*(local |scoped )?(notation|infixl?|infixr|prefix|postfix|macro|syntax)\b", x)
               for x in lines[a - 1:b]): continue
        for i in range(a, b + 1): drop.add(i)
        # a `set_option/omit/include/open ... in` line directly above belongs to the dropped command
        j = a - 1
        while j >= 1 and re.match(r"^\s*(set_option|omit|include|open|attribute) .* in\s*$", lines[j - 1]): drop.add(j); j -= 1
    out = []
    mod_header = lines[0].strip() == "module"
    imports = []
    body_start = 0
    for i, l in enumerate(lines, 1):
        if re.match(r"^(public )?import ", l):
            imports += resolve(l.split()[-1])
            body_start = i
    body = []
    in_comment = False
    for i, l in enumerate(lines, 1):
        if i <= body_start or i in drop: continue
        s = l.strip()
        if s in ("@[expose] public section", "noncomputable section", "public section", "module"): continue
        body.append(l)
    # section headings (`/-! ### ... -/`) left with nothing under them
    def heading(x): return re.match(r"^/-!.*-/\s*$", x.strip()) is not None
    nxt = lambda k: next((x for x in body[k + 1:] if x.strip()), "")
    body = [x for k, x in enumerate(body)
            if not (heading(x) and (heading(nxt(k)) or nxt(k).strip().startswith("end ") or nxt(k) == ""))]
    # trailing bare `end` that closed the noncomputable section in the original
    while body and body[-1].strip() == "": body.pop()
    if body and body[-1].strip() == "end": body.pop()
    # collapse blank runs left by dropped declarations
    txt = re.sub(r"\n{3,}", "\n\n", "\n".join(body)).strip("\n")
    # `open NS (x y ...)`: keep only the names that are copied (a dropped one is unknown
    # in the copy); drop the command when none is left
    def open_sel(mt):
        ns, items = mt.group(2), mt.group(3).split()
        root = m.split(".")[0]
        kept_items = [x for x in items
                      if any(c in reach for c in (f"{ns}.{x}", f"{root}.{ns}.{x}"))]
        if not kept_items: return ""
        return f"{mt.group(1)}open {ns} ({' '.join(kept_items)})"
    txt = re.sub(r"^([ \t]*)open ([\w.]+) \(([^)]*)\)[ \t]*$", open_sel, txt, flags=re.M)
    # `open NS ...` of a project namespace none of whose constants is copied: the namespace
    # does not exist in the copies (drop that name; drop the command when none is left)
    root = m.split(".")[0]
    allnames = [x for mm in allspans for (x, _, _) in allspans[mm]]
    def proj_ns(x):
        full = x if x.startswith("StratonovichHAM") else f"{root}.{x}"
        if not any(n.startswith(full + ".") for n in allnames): return None
        return full
    def open_plain(mt):
        items = mt.group(2).split()
        kept_items = [x for x in items
                      if proj_ns(x) is None or any(c.startswith(proj_ns(x) + ".") for c in reach)]
        if kept_items == items: return mt.group(0)
        if not kept_items: return ""
        return f"{mt.group(1)}open {' '.join(kept_items)}"
    txt = re.sub(r"^([ \t]*)open ((?!scoped\b)[\w.]+(?: [\w.]+)*)[ \t]*$", open_plain, txt, flags=re.M)
    txt = re.sub(r"\n{3,}", "\n\n", txt)
    hdr = ["module", ""] + [f"public import {i}" for i in dict.fromkeys(imports)] + [
        "", "/-!",
        f"Verbatim copy of the definitions of `{m}` that the claimed theorem types use,",
        f"under the namespace prefix `{PFX}` (generated by scripts/comparator/gen_defs.py;",
        "every other declaration of the module is omitted). Mathlib-only: part of the",
        "trusted Challenge statement. `scripts/comparator/CheckFidelity.lean` checks that",
        "each copied constant equals the project's after removing the prefix.",
        "-/", "", "@[expose] public section", ""]
    if not mod_header: hdr = hdr  # the original is not a module; its copy is
    nc = ["noncomputable section", ""] if any(re.match(r"^noncomputable section", x.strip()) for x in lines) else []
    out = hdr + nc + [f"namespace {PFX}", "", txt, "", f"end {PFX}", ""]
    if nc: out += ["end", ""]
    dst = f"{W}/ChallengeDefs/{m.replace('.', '/')}.lean"
    os.makedirs(os.path.dirname(dst), exist_ok=True)
    open(dst, "w", encoding="utf-8").write("\n".join(out))
    print(dst, len(kept), "declaration(s)")
