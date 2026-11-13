#!/usr/bin/env python3
"""Run one command, report wall time, peak RSS of the child tree and the exit code.

Used inside the lab image, which has no /usr/bin/time (CLAUDE.md HPC rule 2).
usage: measure.py LABEL OUTFILE -- CMD ARGS...
Appends one tab-separated line to OUTFILE: label, rc, wall_s, maxrss_kb, cmd.
"""
import resource
import subprocess
import sys
import time

def main() -> int:
    if len(sys.argv) < 5 or sys.argv[3] != "--":
        print(__doc__, file=sys.stderr)
        return 64
    label, out, cmd = sys.argv[1], sys.argv[2], sys.argv[4:]
    t0 = time.monotonic()
    rc = subprocess.run(cmd).returncode
    wall = time.monotonic() - t0
    rss = resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss  # kB on Linux
    with open(out, "a", encoding="utf-8") as fh:
        fh.write(f"{label}\t{rc}\t{wall:.2f}\t{rss}\t{' '.join(cmd)}\n")
    print(f"MEASURE {label} rc={rc} wall_s={wall:.2f} maxrss_kb={rss}", flush=True)
    return 0  # the caller judges rc against the expectation table

if __name__ == "__main__":
    sys.exit(main())
