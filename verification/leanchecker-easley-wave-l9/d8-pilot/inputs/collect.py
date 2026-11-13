#!/usr/bin/env python3
"""Summarize the D8 pilot: compare Easley numbers with the <MACHINE> numbers in expect.tsv.

usage: collect.py RUN_DIR   (login node, after the job ends)
Prints a table and the decision line. Exit 0 only if sacct says COMPLETED 0:0 and PILOT_DONE has mismatch=0.
"""
import csv
import pathlib
import subprocess
import sys

def main() -> int:
    r = pathlib.Path(sys.argv[1]).resolve()
    jobs = (r / "jobs.txt").read_text().split()
    job = jobs[1]
    st = subprocess.run(["sacct", "-n", "-X", "-P", "-j", job, "-o", "State,ExitCode,Elapsed,MaxRSS,TotalCPU"],
                        capture_output=True, text=True, check=True).stdout.strip().splitlines()
    print("sacct:", st)
    done = (r / "pilot" / "PILOT_DONE")
    if not done.exists():
        print("NO PILOT_DONE"); return 2
    exp = {}
    for row in csv.reader((r / "inputs" / "expect.tsv").open(), delimiter="\t"):
        if row and not row[0].startswith("#"):
            exp[row[0]] = row
    print(f"{'label':34} {'rc':>3} {'wall_s':>9} {'rss_GB':>7} | office wall/rss")
    worst = 0.0
    for row in csv.reader((r / "pilot" / "results.tsv").open(), delimiter="\t"):
        label, rc, wall, rss = row[0], row[1], float(row[2]), int(row[3]) / 1e6
        base = label.rsplit(".", 1)[0] if "." in label else label
        base = base.split(".", 1)[1] if base.startswith(("olean.", "check.", "fresh.")) else base
        e = exp.get(base)
        ref = f"{e[2]} s / {int(e[3]) / 1e6:.1f} GB" if e and not label.startswith(("olean", "check", "fresh")) else ""
        worst = max(worst, rss)
        print(f"{label:34} {rc:>3} {wall:9.1f} {rss:7.2f} | {ref}")
    ok = "mismatch=0" in done.read_text() and st and st[0].startswith("COMPLETED|0:0")
    print(f"peak RSS over all runs: {worst:.2f} GB")
    print("DECISION:", "PASS (K5/K6 may start on <MACHINE>; Easley replays them in the normal array gate)" if ok
          else "STOP (read pilot-job.log; do not resubmit before diagnosing)")
    return 0 if ok else 1

if __name__ == "__main__":
    sys.exit(main())
