#!/usr/bin/env python3
"""EASLEY LOGIN NODE. Collect an L11 array campaign into an evidence folder (format of waves L6/L7).

usage: python3 -I collect.py RUN_DIR OUT_DIR

Coverage is decided by the frozen manifest, never by a count of successes:
  * every index 1..N of targets-fresh.txt has exactly one counted PASS attempt (rc 0, empty checker
    output, task.result target == manifest line), and index 0 (default mode) passed every manifest target;
  * every counted attempt is bound to the same commit, tree, inputs hash, workspace tarball hash and
    leanchecker hash as shared/BUILD_OK;
  * sacct shows the build job and every counted task COMPLETED 0:0 (terminal accounting).
Writes OUT_DIR/summary.tsv (module, exit, wall, peak RSS KiB, output bytes, job id; manifest order),
OUT_DIR/default/summary-<job>.tsv, OUT_DIR/fresh-time/<Module>.time, OUT_DIR/jobs/<job>/ (logs),
OUT_DIR/sacct.tsv and OUT_DIR/COLLECT.txt. Prints the indices to resubmit (submit.sh redo LIST) and the
failure signature (sacct State/ExitCode + hash of the first error line) of each failed attempt; two failed
attempts with one signature write RUN_DIR/STOP, which blocks submit.sh until diagnosed.
Exit 0 iff the campaign is complete and accepted. Writes nothing into RUN_DIR except STOP.
"""
import hashlib, os, re, shutil, subprocess, sys
from collections import defaultdict

run, out = sys.argv[1], sys.argv[2]
inp, sh, tdir = os.path.join(run, "inputs"), os.path.join(run, "shared"), os.path.join(run, "tasks")


def kv(path):
    d = {}
    with open(path) as fh:
        for line in fh:
            if "=" in line:
                k, v = line.rstrip("\n").split("=", 1)
                d[k] = v
    return d


def lines(path):
    return [l.strip() for l in open(path) if l.strip()]


def sha(path):
    h = hashlib.sha256()
    with open(path, "rb") as fh:
        for b in iter(lambda: fh.read(1 << 20), b""):
            h.update(b)
    return h.hexdigest()


problems = []
build = kv(os.path.join(sh, "BUILD_OK"))
targets = lines(os.path.join(inp, "targets-fresh.txt"))
manifest = lines(os.path.join(inp, "modules-all.txt"))
if build.get("inputs_sha256") != sha(os.path.join(inp, "INPUT-SHA256SUMS")):
    problems.append("BUILD_OK inputs hash differs from the frozen inputs")
bind_keys = ("commit", "tree", "inputs_sha256", "ws_tar_sha256")

# All attempts per index: tasks/NNN-<jobid>/task.result
attempts = defaultdict(list)
for name in sorted(os.listdir(tdir)):
    m = re.fullmatch(r"(\d{3})-(\d+)", name)
    res = os.path.join(tdir, name, "task.result")
    if not m:
        problems.append(f"unexpected entry tasks/{name}")
        continue
    if not os.path.exists(res):
        attempts[int(m.group(1))].append({"dir": name, "job": m.group(2), "rc": "NO_RESULT"})
        continue
    r = kv(res)
    r["dir"], r["job"] = name, m.group(2)
    attempts[int(m.group(1))].append(r)

# Terminal accounting for every job id seen
jobids = [build["build_job"]] + [a["job"] for v in attempts.values() for a in v]
sacct_txt = subprocess.run(
    ["sacct", "-P", "-j", ",".join(jobids), "--format=JobIDRaw,JobID,JobName,State,ExitCode,Start,End,Elapsed,"
     "AllocCPUS,TotalCPU,ReqMem,MaxRSS,NodeList"],
    capture_output=True, text=True, env=dict(os.environ, SLURM_TIME_FORMAT="%Y-%m-%dT%H:%M:%S%z")).stdout
acct = {}
for row in sacct_txt.splitlines()[1:]:
    f = row.split("|")
    if "." not in f[0]:
        acct.setdefault(f[0], f)  # keyed by JobIDRaw = the task's own SLURM_JOB_ID; steps skipped
def terminal(job):
    f = acct.get(job)
    return (f[3], f[4]) if f else ("NO_SACCT", "")
if terminal(build["build_job"]) != ("COMPLETED", "0:0"):
    problems.append(f"build job {build['build_job']} not COMPLETED 0:0: {terminal(build['build_job'])}")


def passed(idx, a):
    if a.get("rc") != "0" or any(a.get(k) != build.get(k) for k in bind_keys):
        return False
    if a.get("leanchecker_sha256") != build.get("leanchecker_sha256"):
        return False
    want = "ALL" if idx == 0 else targets[idx - 1]
    if a.get("target") != want or terminal(a["job"]) != ("COMPLETED", "0:0"):
        return False
    mode = "default" if idx == 0 else "fresh"
    summ = os.path.join(tdir, a["dir"], mode, "summary.tsv")
    if not os.path.exists(summ):
        return False
    rows = [l.split("\t") for l in lines(summ)]
    mods = [r[0] for r in rows]
    expect = manifest if idx == 0 else [want]
    return sorted(mods) == sorted(expect) and len(mods) == len(set(mods)) and all(r[1] == "0" and r[4] == "0" for r in rows)


def signature(a):
    st = terminal(a["job"])
    first = ""
    for cand in ("task.log",):
        p = os.path.join(tdir, a["dir"], cand)
        if os.path.exists(p):
            for l in open(p, errors="replace"):
                if re.search(r"FAIL|MISMATCH|MISSING|BUSY|TOO SMALL|error|Error|DIFFERS", l):
                    first = re.sub(r"\d{2}:\d{2}:\d{2}|node\d+|\d{6,}", "#", l.strip())
                    break
    return f"{st[0]}/{st[1]}/{hashlib.sha256(first.encode()).hexdigest()[:12]}", first


counted, redo, sigs = {}, [], defaultdict(list)
for idx in range(0, len(targets) + 1):
    good = [a for a in attempts.get(idx, []) if passed(idx, a)]
    for a in attempts.get(idx, []):
        if not passed(idx, a):
            s, line = signature(a)
            sigs[s].append((idx, a["job"], line))
    if len(good) >= 1:
        counted[idx] = good[-1]   # all PASS attempts share the bindings; keep the latest
    else:
        redo.append(idx)
extra = sorted(set(attempts) - set(range(0, len(targets) + 1)))
if extra:
    problems.append(f"attempts for indices outside the manifest: {extra}")

os.makedirs(out)
for sub in ("default", "fresh-time", "jobs"):
    os.makedirs(os.path.join(out, sub))
with open(os.path.join(out, "sacct.tsv"), "w") as fh:
    fh.write(sacct_txt)
bj = os.path.join(out, "jobs", build["build_job"])
os.makedirs(bj)
for f in ("build-job.log", "cache-get-1.log", "runtime-preflight.log", "runtime-binaries.sha256", "build-monitor.log", "BUILD_OK"):
    if os.path.exists(os.path.join(sh, f)):
        shutil.copy2(os.path.join(sh, f), bj)
with open(os.path.join(sh, "build.log"), errors="replace") as fh, open(os.path.join(bj, "build.tail.log"), "w") as o:
    o.writelines(fh.readlines()[-60:])
rows = []
for idx, a in sorted(counted.items()):
    d = os.path.join(tdir, a["dir"])
    jd = os.path.join(out, "jobs", a["job"])
    os.makedirs(jd)
    for f in ("task.log", "monitor.log", "task.result"):
        if os.path.exists(os.path.join(d, f)):
            shutil.copy2(os.path.join(d, f), jd)
    if idx == 0:
        shutil.copy2(os.path.join(d, "default", "summary.tsv"), os.path.join(out, "default", f"summary-{a['job']}.tsv"))
    else:
        t = targets[idx - 1]
        r = lines(os.path.join(d, "fresh", "summary.tsv"))[0].split("\t")
        rows.append((idx, "\t".join(r[:5] + [a["job"]])))
        shutil.copy2(os.path.join(d, "fresh", t + ".time"), os.path.join(out, "fresh-time", t + ".time"))
with open(os.path.join(out, "summary.tsv"), "w") as fh:
    for _, r in sorted(rows):
        fh.write(r + "\n")

stop = [(s, v) for s, v in sigs.items() if len(v) >= 2]
complete = not redo and not problems
with open(os.path.join(out, "COLLECT.txt"), "w") as fh:
    fh.write(f"commit={build['commit']}\ntree={build['tree']}\nbuild_job={build['build_job']}\n")
    fh.write(f"fresh_targets={len(targets)} counted_fresh={len([i for i in counted if i > 0])} default_ok={0 in counted}\n")
    fh.write(f"redo={','.join(map(str, redo)) or '-'}\nproblems={problems or '-'}\n")
    for s, v in sigs.items():
        fh.write(f"failure_signature {s} x{len(v)}: {v}\n")
    fh.write(f"VERDICT={'COMPLETE' if complete else 'INCOMPLETE'}\n")
print(open(os.path.join(out, "COLLECT.txt")).read(), end="")
if stop and not complete:
    with open(os.path.join(run, "STOP"), "w") as fh:
        fh.write("; ".join(f"{s} x{len(v)}" for s, v in stop) + "\n")
    print("STOP: a failure signature repeated; diagnose before any resubmission (RUN_DIR/STOP written)")
if redo and not (stop and not complete):
    print(f"resubmit with: submit.sh {run} redo {','.join(map(str, redo))}")
sys.exit(0 if complete else 1)
