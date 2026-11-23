#!/usr/bin/env python3
"""Per-module leanchecker replay driver (one module per invocation).

usage: replay.py MODE MODULES_FILE OUTDIR PARALLEL TIMEOUT_S
  MODE = default | fresh
Runs `timeout -k 30s T lake env leanchecker [--fresh] <Module>` once per module,
in the current directory, PARALLEL at a time. Per module it writes
OUTDIR/<Module>.log (combined stdout+stderr) and OUTDIR/<Module>.time
(command, exit status, wall seconds, user/sys CPU seconds, peak RSS KiB from
os.wait4 of that child), and appends a row to OUTDIR/summary.tsv:
module, exit code, wall time (h:mm:ss.ss), peak RSS (KiB), output bytes.
Exit 0 iff every module exits 0 with empty output (the pass signature).
"""
import os, subprocess, sys, time, threading
from concurrent.futures import ThreadPoolExecutor

mode, modfile, outdir, par, tmo = sys.argv[1], sys.argv[2], sys.argv[3], int(sys.argv[4]), int(sys.argv[5])
assert mode in ("default", "fresh")
mods = [l.strip() for l in open(modfile) if l.strip()]
os.makedirs(outdir, exist_ok=True)
lock = threading.Lock()


def fmt(s):
    s = round(s, 2)
    h, r = divmod(s, 3600)
    m, sec = divmod(r, 60)
    return f"{int(h)}:{int(m):02d}:{sec:05.2f}"


def one(mod):
    cmd = ["timeout", "-k", "30s", f"{tmo}s", "lake", "env", "leanchecker"]
    if mode == "fresh":
        cmd.append("--fresh")
    cmd.append(mod)
    log = os.path.join(outdir, mod + ".log")
    with lock:
        print(f"BEGIN {mode} {mod} {time.strftime('%H:%M:%S')}", flush=True)
    t0 = time.time()
    with open(log, "wb") as fh:
        p = subprocess.Popen(cmd, stdout=fh, stderr=subprocess.STDOUT, stdin=subprocess.DEVNULL)
        _, status, ru = os.wait4(p.pid, 0)
    wall = time.time() - t0
    rc = os.waitstatus_to_exitcode(status)
    nbytes = os.path.getsize(log)
    with open(os.path.join(outdir, mod + ".time"), "w") as fh:
        fh.write(f"Command: {' '.join(cmd)}\n")
        fh.write(f"Exit status: {rc}\n")
        fh.write(f"Elapsed wall (s): {wall:.2f}\n")
        fh.write(f"Elapsed wall (h:mm:ss): {fmt(wall)}\n")
        fh.write(f"User CPU (s): {ru.ru_utime:.2f}\n")
        fh.write(f"System CPU (s): {ru.ru_stime:.2f}\n")
        fh.write(f"Peak RSS of largest waited descendant (KiB): {ru.ru_maxrss}\n")
        fh.write(f"Output bytes: {nbytes}\n")
        fh.write(f"Host: {os.uname().nodename}  Job: {os.environ.get('SLURM_JOB_ID', 'NA')}\n")
    row = f"{mod}\t{rc}\t{fmt(wall)}\t{ru.ru_maxrss}\t{nbytes}\n"
    with lock:
        with open(os.path.join(outdir, "summary.tsv"), "a") as fh:
            fh.write(row)
        print(f"END {mode} {row}", end="", flush=True)
    return rc == 0 and nbytes == 0


with ThreadPoolExecutor(max_workers=par) as ex:
    ok = list(ex.map(one, mods))
print(f"REPLAY_{mode.upper()} pass={sum(ok)} fail={len(ok) - sum(ok)} total={len(ok)}", flush=True)
sys.exit(0 if all(ok) else 1)
