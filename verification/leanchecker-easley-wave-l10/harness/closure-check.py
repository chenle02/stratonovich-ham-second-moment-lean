#!/usr/bin/env python3
"""Target-selection check for the wave-L5 leanchecker replay.

usage: closure-check.py REPO OLD_COMMIT NEW_COMMIT

Reads the companion repository with `git show` only (no checkout, no writes).
For every Lean module of the two libraries (StratonovichHAMSecondMoment,
StratonovichHAMAudit, and the umbrella StratonovichHAMSecondMoment.lean) it
classifies the module at NEW_COMMIT relative to OLD_COMMIT as

  new           absent at OLD_COMMIT
  content       the comment-stripped source differs
  comment-only  the raw source differs, the comment-stripped source is identical
  identical     the raw source is byte-identical

For a comment-only module it also reports whether the line count is
unchanged (if so, no declaration moves to a different line).

Comment stripping removes Lean block comments `/- ... -/` (nested, which
covers doc comments `/-- -/` and module docs `/-! -/`) and line comments
`-- ...` up to the end of the line, and leaves string and character literals
intact. Nothing else is normalized: whitespace outside comments is compared
as is.

It then computes, for every module, its transitive project imports at
NEW_COMMIT and reports any module that is identical or comment-only but
imports (directly or indirectly) a module that is new or changed in content.
Such a module would need a --fresh replay even though its own source did not
change in content.
"""
import re
import subprocess
import sys

LIBS = ("StratonovichHAMSecondMoment", "StratonovichHAMAudit")
UMBRELLA = "StratonovichHAMSecondMoment"
CHAR_RE = re.compile(r"'(\\(x[0-9a-fA-F]{2}|u\{[0-9a-fA-F]+\}|.)|[^'\\\n])'")


def git(repo, *args):
    return subprocess.run(["git", "-C", repo, *args], check=True,
                          capture_output=True).stdout


def modules(repo, commit):
    out = git(repo, "ls-tree", "-r", "--name-only", commit, "--", *LIBS,
              UMBRELLA + ".lean").decode()
    mods = {}
    for path in out.split("\n"):
        if path.endswith(".lean"):
            mods[path[:-5].replace("/", ".")] = path
    return mods


def strip_comments(src):
    out = []
    i, n = 0, len(src)
    while i < n:
        c = src[i]
        if src.startswith("/-", i):
            depth, i = 1, i + 2
            while i < n and depth:
                if src.startswith("/-", i):
                    depth, i = depth + 1, i + 2
                elif src.startswith("-/", i):
                    depth, i = depth - 1, i + 2
                else:
                    i += 1
            if depth:
                raise ValueError("unterminated block comment")
        elif src.startswith("--", i):
            j = src.find("\n", i)
            i = n if j < 0 else j  # keep the newline itself
        elif c == '"':
            j = i + 1
            while j < n and src[j] != '"':
                j += 2 if src[j] == "\\" else 1
            out.append(src[i:j + 1])
            i = j + 1
        elif c == "'" and not (i and (src[i - 1].isalnum() or src[i - 1] in "_'!?.")) \
                and CHAR_RE.match(src, i):
            # character literal such as 'a' or '\n' (a prime ending an
            # identifier, as in x', is excluded by the preceding character)
            j = CHAR_RE.match(src, i).end()
            out.append(src[i:j])
            i = j
        else:
            out.append(c)
            i += 1
    return "".join(out)


IMPORT_RE = re.compile(r"^import\s+(\S+)", re.M)


def project_imports(stripped):
    return {m for m in IMPORT_RE.findall(stripped)
            if m == UMBRELLA or m.split(".")[0] in LIBS}


def main():
    repo, old, new = sys.argv[1:4]
    old_c = git(repo, "rev-parse", old + "^{commit}").decode().strip()
    new_c = git(repo, "rev-parse", new + "^{commit}").decode().strip()
    old_m, new_m = modules(repo, old_c), modules(repo, new_c)
    print(f"old {old_c}\nnew {new_c}")
    print(f"modules: {len(old_m)} at old, {len(new_m)} at new")
    removed = sorted(set(old_m) - set(new_m))
    print(f"removed: {len(removed)} {' '.join(removed)}")
    cls, stripped_new, same_lines = {}, {}, {}
    for mod, path in sorted(new_m.items()):
        nsrc = git(repo, "show", f"{new_c}:{path}").decode()
        stripped_new[mod] = strip_comments(nsrc)
        if mod not in old_m:
            cls[mod] = "new"
            continue
        osrc = git(repo, "show", f"{old_c}:{old_m[mod]}").decode()
        if osrc == nsrc:
            cls[mod] = "identical"
        elif strip_comments(osrc) == stripped_new[mod]:
            cls[mod] = "comment-only"
            same_lines[mod] = osrc.count("\n") == nsrc.count("\n")
        else:
            cls[mod] = "content"
    for kind in ("new", "content", "comment-only", "identical"):
        ms = [m for m in sorted(cls) if cls[m] == kind]
        print(f"\n{kind}: {len(ms)}")
        for m in ms:
            note = ""
            if kind == "comment-only":
                note = "  (line count unchanged)" if same_lines[m] else "  (LINE COUNT CHANGED)"
            print(f"  {m}{note}")
    # transitive project imports at the new commit
    direct = {m: project_imports(s) for m, s in stripped_new.items()}
    unknown = sorted({i for s in direct.values() for i in s} - set(new_m))
    print(f"\nproject imports that are not modules of the two libraries: {len(unknown)} {' '.join(unknown)}")
    closure = {}

    def close(m, seen=()):
        if m in closure:
            return closure[m]
        acc = set()
        for i in direct.get(m, ()):
            if i in seen:
                raise ValueError(f"import cycle at {i}")
            acc |= {i} | close(i, seen + (m,))
        closure[m] = acc
        return acc

    for m in new_m:
        close(m)
    changed = {m for m, k in cls.items() if k in ("new", "content")}
    print("\nimport-closure gaps (identical or comment-only module importing a new or content-changed module):")
    gaps = 0
    for m in sorted(cls):
        if cls[m] in ("identical", "comment-only"):
            hit = sorted(closure[m] & changed)
            if hit:
                gaps += 1
                print(f"  {m} -> {' '.join(hit)}")
    print(f"  total {gaps}")
    print("\ndirect importers of each new or content-changed module:")
    for m in sorted(changed):
        users = sorted(u for u in new_m if m in direct[u])
        print(f"  {m}: {' '.join(users) if users else '-'}")


if __name__ == "__main__":
    main()
