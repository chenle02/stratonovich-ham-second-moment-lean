#!/usr/bin/env python3
"""Coverage check for the modules not replayed --fresh in the wave-L6 job.

usage: replay-coverage.py REPO NEW_COMMIT TARGETS

REPO is a checkout of the companion repository; it is read with `git show`
only, plus the `summary.tsv` files of the earlier replay folders under
REPO/verification/. TARGETS is the list of modules replayed --fresh at
NEW_COMMIT (harness/modules-wavel6.txt).

For every module M at NEW_COMMIT that is not in TARGETS it takes the most
recent earlier Easley --fresh replay whose summary.tsv lists M with exit 0,
and checks that M and every project module in M's transitive import closure
at NEW_COMMIT have, with comments stripped, the same source at that replay
commit as at NEW_COMMIT. Comment stripping and import parsing are those of
closure-check.py (imported from the same directory).
"""
import importlib.util
import os
import sys
from collections import Counter

here = os.path.dirname(os.path.abspath(__file__))
spec = importlib.util.spec_from_file_location("cc", os.path.join(here, "closure-check.py"))
cc = importlib.util.module_from_spec(spec)
spec.loader.exec_module(cc)

REPLAYS = [  # most recent first
    ("712c307", "leanchecker-easley-wave-l5"),
    ("2f5ee14", "leanchecker-easley-wave-l4"),
    ("687e631", "leanchecker-easley-wave-l3"),
    ("837778a", "leanchecker-easley-2026-11-10"),
]


def main():
    repo, new, tfile = sys.argv[1:4]
    new_c = cc.git(repo, "rev-parse", new + "^{commit}").decode().strip()
    here_t = set(open(tfile).read().split())
    passed = {}
    for c, d in REPLAYS:
        with open(os.path.join(repo, "verification", d, "summary.tsv")) as f:
            passed[c] = {r.split("\t")[0] for r in f if r.split("\t")[1] == "0"}
    nm = cc.modules(repo, new_c)
    sn = {m: cc.strip_comments(cc.git(repo, "show", f"{new_c}:{p}").decode())
          for m, p in nm.items()}
    direct = {m: cc.project_imports(s) for m, s in sn.items()}

    def closure(m):
        acc, st = set(), [m]
        while st:
            for i in direct[st.pop()]:
                if i not in acc:
                    acc.add(i)
                    st.append(i)
        return acc

    old = {c: cc.modules(repo, c) for c, _ in REPLAYS}
    print(f"new {new_c}")
    print(f"modules at new: {len(nm)}; replayed --fresh here: {len(here_t & set(nm))}")
    tally, bad = Counter(), 0
    for m in sorted(nm):
        if m in here_t:
            continue
        hit = next(((c, d) for c, d in REPLAYS if m in passed[c]), None)
        if hit is None:
            print(f"  {m}: NO EARLIER --fresh REPLAY")
            bad += 1
            continue
        c, d = hit
        om = old[c]
        clo = closure(m)
        same = all(x in om and cc.strip_comments(
            cc.git(repo, "show", f"{c}:{om[x]}").decode()) == sn[x] for x in {m} | clo)
        raw = cc.git(repo, "show", f"{c}:{om[m]}") == cc.git(repo, "show", f"{new_c}:{nm[m]}")
        kind = "identical" if raw else "comment-only"
        print(f"  {m}: {c} ({d}) own source {kind}; "
              f"{len(clo)} project imports; stripped sources incl. imports equal: {'yes' if same else 'NO'}")
        tally[(c, kind)] += 1
        bad += not same
    print("\nsummary (replay commit, own source vs that commit): count")
    for (c, k), v in sorted(tally.items()):
        print(f"  {c} {k}: {v}")
    print(f"modules failing the check: {bad}")


if __name__ == "__main__":
    main()
