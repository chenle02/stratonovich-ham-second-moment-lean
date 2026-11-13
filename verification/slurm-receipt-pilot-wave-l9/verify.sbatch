#!/bin/bash
# Companion adaptation (stratonovich-ham-second-moment-lean, Easley, wave L9 receipt pilot): this file is
# `lean-pkg receipt slurm --template` with only these changes: Slurm lines for nova_20 / resourcecap_plus,
# 4 CPUs / 12G (local systemd receipt at f3be834: MemoryPeak 9.97 GB under a 12G cap, 4 CPU quota);
# the Lean 4.35.0 runtime tarball and the lab image are staged node-local and every tool runs in the image
# (RUN below, --cleanenv); the companion's verify.sh commands are the defaults (VERIFY_CMD fetches the pinned
# Mathlib cache, then builds the umbrella and the Axioms module, whose #print axioms lines are the axioms;
# AXIOMS_CMD is `true`); the EXIT trap removes the whole node-local work directory.
# verify.sbatch: a Lean verification job whose files `lean-pkg receipt slurm` accepts
# (printed by `lean-pkg receipt slurm --template`). Submit it from the package checkout:
#
#   sbatch verify.sbatch
#   lean-pkg receipt slurm --check --log verify-J.log --stdout verify-J.out --stderr verify-J.err --commit SHA
#   lean-pkg receipt slurm --job J --log verify-J.log --stdout verify-J.out --stderr verify-J.err --commit SHA
#
# Run --check on the files of a short trial job before the long one: it names every line still missing.
# What the receipt reads; keep these lines as they are:
#   stdout (.out): exactly one line each of pre-manifest-sha256, post-manifest-sha256, verify-log-sha256
#                  (and container-image-sha256 or container-oci-digest when the tools run in a container)
#   stderr (.err): empty, so every tool writes into the log, never to the job's stderr
#   the log: one line each of checker:, sorry-count:, axioms: (and lean-toolchain:, commit:, job-id:,
#            generated-at:, which must agree with the commit and the job), the claim-axioms lines of
#            every claim in claims.yaml (read from the built environment after the build), the hyp-probe/1
#            section after them (the Challenge is built into $WORK/hyp-challenge-build.log, not this
#            log), the build between the lean-pkg-build: begin / end lines, and no root-package module Lake restored instead of
#            compiling (`Reused`, `Replayed`, `Unpacked`): its sorry warning need not be in the log
#   the job: sacct State COMPLETED, ExitCode 0:0 (any failed step fails the job: set -e)
#SBATCH --job-name=stratham-l9-receipt
#SBATCH --partition=nova_20
#SBATCH --qos=resourcecap_plus
#SBATCH --no-requeue
#SBATCH --output=verify-%j.out
#SBATCH --error=verify-%j.err
#SBATCH --nodes=1
#SBATCH --ntasks=1
#SBATCH --cpus-per-task=4
#SBATCH --mem=12G
#SBATCH --time=1-00:00:00
# An inherited locale the node does not have (C.UTF-8, say) makes bash and other tools print a warning on
# stderr, which the receipt refuses (stderr must be empty; it is never filtered). The C locale is set for the
# job's own shell here and again below for every tool it starts; drop neither line.
#SBATCH --export=ALL,LC_ALL=C,LANG=C,PYTHONUTF8=1
# Add the partition, account or QOS lines your site requires.

set -euo pipefail
# Exact runtime: the C locale before any tool runs (an sbatch --export on the command line replaces the line above).
export LC_ALL=C LANG=C PYTHONUTF8=1
unset LANGUAGE

# The package's own commands (placeholders; edit them here or set them when submitting).
VERIFY_CMD=${VERIFY_CMD:-"lake exe cache get && lake build StratonovichHAMSecondMoment StratonovichHAMSecondMoment.Axioms"}
# a file of `#print axioms Name` lines for the theorems the receipt covers. `lake lean FILE`, not
# `lake env lean FILE`: under `lake env` a dependency's build directory holding the package's own namespace
# comes first on LEAN_PATH and would be loaded instead (the check below refuses that too).
AXIOMS_CMD=${AXIOMS_CMD:-"true"}
# prints the LEAN_PATH the audit runs under, for the shadowing check
LEAN_PATH_CMD=${LEAN_PATH_CMD:-"lake env printenv LEAN_PATH"}
CHECKER=${CHECKER:-"verify.sbatch (lake build StratonovichHAMSecondMoment StratonovichHAMSecondMoment.Axioms; #print axioms)"}
# Run the tools inside the job container when the node needs one, e.g. RUN="apptainer exec lean.sif".
RUN=${RUN:-}
# The container image the tools run in, recorded in the log and on stdout (the receipt's `container` key).
# CONTAINER_IMAGE: the Apptainer or Singularity .sif file (default: the first word of RUN ending in .sif), or an
# OCI image name for podman or docker. CONTAINER_ENGINE: apptainer, singularity, podman or docker (default: the
# first word of RUN). Before the build the job takes the SIF file's sha256, or the OCI image's digest
# (`podman image inspect`, `docker image inspect`); the log names the image with a home directory shown as ~.
CONTAINER_IMAGE=${CONTAINER_IMAGE:-}
CONTAINER_ENGINE=${CONTAINER_ENGINE:-}
# How the tree committed at COMMIT reaches the work directory. archive (the default): `git archive`, so the
# job's tree has no .git. clone: a new repository there holding only COMMIT and its history (fetched over the
# file transport from the submitting checkout, never the network; its own object store, so nothing is shared
# with the checkout and no untracked or ignored file comes along), checked out at COMMIT; the job fails unless
# HEAD is COMMIT and `git status` is empty. Use clone for a VERIFY_CMD that reads `git rev-parse HEAD`.
SRC_MODE=${SRC_MODE:-archive}
# Optional: a tarball (any compression tar reads) holding .lake/packages, the dependencies' checkouts and
# builds, restored before the build so the job need not fetch and build Mathlib again. Only .lake/packages is
# taken from it (anything else in it is ignored); the job fails when the restore changed anything else in the
# tree, or when a dependency's build directory holds one of the package's root namespaces. The package itself
# is still compiled fresh: the checks below are unchanged. The log records the tarball's sha256, never its path.
# The tarball must hold what the audit imports, not only the build target's cone (`import Mathlib` needs every
# Mathlib module built); check it before submitting, on the login node (reads, builds and writes nothing):
#   lean-pkg receipt slurm --preflight-deps --deps-tar T --commit SHA [--entries 'Verify/**/*.lean' ...]
DEPS_TAR=${DEPS_TAR:-}
# Optional artifact seal: ARTIFACTS_DIR, a directory relative to the job's package tree ($SRC; relative to $WORK
# with ARTIFACTS_BASE=work) that the build or the audit fills. After the audit every regular file under it is
# copied to ARTIFACTS_OUT (default $OUT_DIR/artifacts-<J>; must not exist yet) with a manifest artifacts.sha256
# there: one line per file, sorted by path, `<relative path> <size> <sha256>`. The manifest's sha256 goes on
# stdout beside the seal lines (artifacts-manifest-sha256), so `lean-pkg receipt slurm --artifacts DIR`
# rehashes a collected copy against the job's own manifest. A symlink or special file under the directory, a
# file name holding a newline, or a copy that does not rehash to the manifest fails the job.
ARTIFACTS_DIR=${ARTIFACTS_DIR:-}
ARTIFACTS_BASE=${ARTIFACTS_BASE:-src}

JOB=${SLURM_JOB_ID:?run this under sbatch}
PKG_DIR=${PKG_DIR:-${SLURM_SUBMIT_DIR:-$PWD}}
COMMIT=${COMMIT:-$(git -C "$PKG_DIR" rev-parse HEAD)}
OUT_DIR=${OUT_DIR:-${SLURM_SUBMIT_DIR:-$PWD}}
LOG="$OUT_DIR/verify-$JOB.log"
ARTIFACTS_OUT=${ARTIFACTS_OUT:-$OUT_DIR/artifacts-$JOB}
ARTIFACTS_MANIFEST=artifacts.sha256

# Node-local work directory. The receipt redacts /tmp/<user>-job<J> and /scratch/<user>/ by itself; a
# path elsewhere that appears in the log needs `--redact REGEX` at receipt time.
WORK=${SLURM_TMPDIR:-/tmp/${USER:-user}-job-$JOB}
STAGE="$WORK/src"
DEPS_STAGE="$WORK/deps"
# Lake's local artifact cache restores a module built earlier (`Reused`) without its sorry warning, so the job
# gets an empty cache of its own and the cache switched off. LAKE_CACHE_DIR="" would NOT disable it (Lake then
# uses .lake/cache), and a lakefile's `enableArtifactCache = true` wins over LAKE_ARTIFACT_CACHE=false: the
# empty directory leaves it nothing to restore. (--no-cache / LAKE_NO_CACHE only govern downloads.)
export LAKE_CACHE_DIR="$WORK/lake-cache"
export LAKE_ARTIFACT_CACHE=false
rm -rf "$STAGE" "$DEPS_STAGE" "$LAKE_CACHE_DIR"
mkdir -p "$STAGE" "$LAKE_CACHE_DIR"
trap 'chmod -R u+w "$WORK" 2>/dev/null; rm -rf "$WORK" 2>/dev/null' EXIT
# Stage the Lean runtime (the elan toolchain) and the Mathlib cache node-local before the build, e.g.
# copy the toolchain under "$WORK/elan" and export ELAN_HOME="$WORK/elan" PATH="$WORK/elan/bin:$PATH";
# a shared filesystem under many parallel readers is slow and can fail the build.
export MATHLIB_CACHE_DIR=${MATHLIB_CACHE_DIR:-$WORK/mathlib-cache}
# Mathlib-heavy packages can exhaust the node's file table (fs.file-max) at higher thread counts;
# /proc/sys/fs/file-nr goes into the log before and after the build.
export LEAN_NUM_THREADS=${LEAN_NUM_THREADS:-3}

# Companion adaptation: the Lean runtime and the lab image, node-local; every tool runs in the image.
SIF_SRC=${SIF_SRC:?the lab Apptainer image}
TB=${TB:?the Lean 4.35.0 runtime tarball}
RUNTIME_SHA=${RUNTIME_SHA:?its sha256}
SINGULARITY=${SINGULARITY:-/tools/singularity-3.8.4/bin/singularity}
TOOLDIR=leanprover--lean4---v4.35.0
mkdir -p "$WORK/tc" "$WORK/xdg" "$MATHLIB_CACHE_DIR"
printf '%s  %s\n' "$RUNTIME_SHA" "$TB" | sha256sum -c --quiet -
cp -- "$SIF_SRC" "$WORK/image.sif"
tar -xzf "$TB" -C "$WORK/tc"
TOOLBIN=$WORK/tc/$TOOLDIR/bin
RUN="$SINGULARITY exec --cleanenv --bind /tmp:/tmp --env PATH=$TOOLBIN:/usr/bin:/bin,XDG_CACHE_HOME=$WORK/xdg,MATHLIB_CACHE_DIR=$MATHLIB_CACHE_DIR,LAKE_CACHE_DIR=$LAKE_CACHE_DIR,LAKE_ARTIFACT_CACHE=false,LEAN_NUM_THREADS=$LEAN_NUM_THREADS,LC_ALL=C,LANG=C,PYTHONUTF8=1,GIT_TERMINAL_PROMPT=0,GIT_CONFIG_NOSYSTEM=1,GIT_CONFIG_GLOBAL=/dev/null $WORK/image.sif"
cd "$WORK"

# Required-executable probe, before the work: every host tool this script runs, and the first word of each
# command it runs under $RUN (with `lean` beside a `lake` one), must resolve with `type -P` (not `command -v`:
# a shell keyword or function is not an executable). A missing one fails the job here, with nothing built.
# Add more with EXTRA_TOOLS (host) or RUN_TOOLS (under $RUN), e.g. RUN_TOOLS=python3.
HOST_TOOLS="git tar sha256sum find sort xargs awk sed grep cut tr cp mkdir rm ls cat ${EXTRA_TOOLS:-}"
run_tools="${RUN_TOOLS:-}"
for c in "$VERIFY_CMD" "$AXIOMS_CMD" "$LEAN_PATH_CMD"; do
  for w in $c; do
    case "$w" in *=*) continue ;; esac
    run_tools="$run_tools $w"
    if [ "$w" = lake ]; then run_tools="$run_tools lean"; fi
    break
  done
done
missing=""
for t in $HOST_TOOLS; do
  type -P "$t" >/dev/null || missing="$missing $t"
done
for t in $($RUN bash -c 'for c in "$@"; do type -P "$c" >/dev/null || echo "$c"; done' _ $run_tools); do
  missing="$missing $t${RUN:+ (under RUN)}"
done
if [ -n "$missing" ]; then
  echo "error: runtime preflight: executable(s) not found:$missing" >&2
  exit 1
fi

# The container image identity, before anything runs in it (CONTAINER_IMAGE above).
if [ -z "$CONTAINER_IMAGE" ]; then
  for w in $RUN; do
    case "$w" in *.sif) CONTAINER_IMAGE=$w; break ;; esac
  done
fi
container_key=""
if [ -n "$CONTAINER_IMAGE" ]; then
  if [ -z "$CONTAINER_ENGINE" ]; then
    for w in $RUN; do CONTAINER_ENGINE=${w##*/}; break; done
  fi
  case "$CONTAINER_ENGINE" in
    apptainer|singularity)
      if [ ! -f "$CONTAINER_IMAGE" ]; then
        echo "error: CONTAINER_IMAGE: no SIF file $CONTAINER_IMAGE" >&2
        exit 1
      fi
      container_key=container-image-sha256
      container_digest=$(sha256sum "$CONTAINER_IMAGE" | cut -d' ' -f1)
      ;;
    podman)
      container_key=container-oci-digest
      container_digest=$(podman image inspect --format '{{.Digest}}' "$CONTAINER_IMAGE")
      ;;
    docker)
      container_key=container-oci-digest
      container_digest=$(docker image inspect --format '{{index .RepoDigests 0}}' "$CONTAINER_IMAGE")
      container_digest=${container_digest##*@}
      ;;
    *)
      echo "error: CONTAINER_ENGINE is apptainer, singularity, podman or docker, not '$CONTAINER_ENGINE'" >&2
      exit 1
      ;;
  esac
  case "$container_key $container_digest" in
    "container-image-sha256 "[0-9a-f]*|"container-oci-digest sha256:"[0-9a-f]*) ;;
    *)
      echo "error: no digest for the container image $CONTAINER_IMAGE" >&2
      exit 1
      ;;
  esac
  container_ref=$CONTAINER_IMAGE
  case "$container_ref" in
    "${HOME:-/nonexistent}"/*) container_ref="~/${container_ref#"$HOME"/}" ;;
  esac
  echo "$container_key $container_digest"
fi

# The committed tree at COMMIT, never the working tree.
case "$SRC_MODE" in
  archive)
    git -C "$PKG_DIR" archive --format=tar "$COMMIT:./" | tar -xf - -C "$STAGE"
    SRC="$STAGE"
    ;;
  clone)
    COMMIT=$(git -C "$PKG_DIR" rev-parse --verify --quiet "$COMMIT^{commit}")
    prefix=$(git -C "$PKG_DIR" rev-parse --show-prefix)
    # No template hooks, no hooks at checkout, only the file transport.
    git init -q --template= "$STAGE"
    GIT_ALLOW_PROTOCOL=file git -C "$STAGE" -c protocol.version=2 fetch -q --no-tags --no-recurse-submodules \
      "$(git -C "$PKG_DIR" rev-parse --show-toplevel)" "$COMMIT"
    git -C "$STAGE" -c core.hooksPath=/dev/null -c advice.detachedHead=false checkout -q --detach FETCH_HEAD
    SRC="$STAGE${prefix:+/${prefix%/}}"
    ;;
  *)
    echo "error: SRC_MODE is archive or clone, not '$SRC_MODE'" >&2
    exit 1
    ;;
esac
cd "$SRC"
echo "pre-manifest-sha256 $(sha256sum lake-manifest.json | cut -d' ' -f1)"
deps_restore=none
if [ -n "$DEPS_TAR" ]; then
  deps_restore="tar $(sha256sum "$DEPS_TAR" | cut -d' ' -f1)"
fi

{
  echo "commit: $COMMIT"
  echo "job-id: $JOB"
  echo "lean-toolchain: $(cat lean-toolchain)"
  echo "checker: $CHECKER"
  echo "lean-num-threads: $LEAN_NUM_THREADS"
  echo "runtime-preflight: ok (LC_ALL=$LC_ALL LANG=$LANG PYTHONUTF8=$PYTHONUTF8; tools:$(echo $run_tools | tr ' ' '\n' | sort -u | tr '\n' ' ' | sed 's/ $//;s/^/ /'))"
  echo "fs-file-nr-before: $(cat /proc/sys/fs/file-nr 2>/dev/null || echo unavailable)"
  echo "lake-cache-dir: fresh (empty, job-local)"
  echo "lake-artifact-cache: $LAKE_ARTIFACT_CACHE"
  echo "src-mode: $SRC_MODE"
  if [ "$SRC_MODE" = clone ]; then
    echo "src-head: $(git rev-parse HEAD)"
  fi
  echo "deps-restore: $deps_restore"
  if [ -n "$container_key" ]; then
    echo "container-engine: $CONTAINER_ENGINE"
    echo "container-image: $container_ref"
    echo "$container_key: $container_digest"
  fi
} >"$LOG"
if [ "$SRC_MODE" = clone ]; then
  if [ "$(git rev-parse HEAD)" != "$COMMIT" ]; then
    echo "error: the clone's HEAD is not COMMIT $COMMIT" >>"$LOG"
    exit 1
  fi
  if [ -n "$(git -C "$STAGE" status --porcelain --untracked-files=all --ignored)" ]; then
    echo "error: the clone at COMMIT is not clean (git status --porcelain is not empty)" >>"$LOG"
    exit 1
  fi
fi
# >>> lean-pkg lake_shadow_check (keep identical in every copy; see lean_pkg/lake_hygiene.py)
lake_root_namespaces() {
  local found
  found=$(
    {
      if [ -f lakefile.toml ]; then
        awk '/^[[:space:]]*\[/ { lib = ($0 ~ /^[[:space:]]*\[\[[[:space:]]*lean_lib[[:space:]]*\]\]/) }
             lib && /^[[:space:]]*(name|roots|globs)[[:space:]]*=/' lakefile.toml | grep -oE '"[^"]+"' | tr -d '"'
      fi
      if [ -f lakefile.lean ]; then
        grep -oE 'lean_lib[[:space:]]+(«[^»]+»|[A-Za-z_][A-Za-z0-9_.]*)' lakefile.lean | awk '{print $2}'
        tr '\n' ' ' < lakefile.lean | grep -oE '(roots|globs)[[:space:]]*:=[[:space:]]*#\[[^]]*\]' \
          | grep -oE '`[^]`[:space:],)]+' | tr -d '`'
      fi
    } 2>/dev/null | sed -e 's/^«\([^»]*\)».*$/\1/' -e 's/[.].*$//' | grep -E '^[A-Za-z_]' | sort -u || true
  )
  if [ -z "$found" ]; then
    found=$(find . -path ./.lake -prune -o -name '*.lean' ! -path ./lakefile.lean -print 2>/dev/null \
      | sed -e 's|^\./||' -e 's|/.*$||' -e 's|\.lean$||' | grep -E '^[A-Za-z_]' | sort -u || true)
  fi
  printf '%s\n' "$found"
}
lake_shadow_check() {
  local own entry r n=0 hits=0 roots
  local -a entries
  own="$(pwd -P)/.lake/build/lib/lean"
  roots=$(lake_root_namespaces)
  IFS=: read -r -a entries <<<"${1:-}"
  for entry in "${entries[@]}"; do
    [ -n "$entry" ] || continue
    n=$((n + 1))
    if [ "$(cd "$entry" 2>/dev/null && pwd -P)" = "$own" ]; then continue; fi
    for r in $roots; do
      if [ -d "$entry/$r" ] || [ -e "$entry/$r.olean" ] || [ -e "$entry/$r.ilean" ]; then
        echo "lean-path-shadow: $entry/$r"
        hits=$((hits + 1))
      fi
    done
  done
  if [ "$hits" -gt 0 ]; then return 1; fi
  echo "lean-path-shadow: none ($n entries, roots $(printf '%s' "$roots" | paste -sd, -))"
}
# <<< lean-pkg lake_shadow_check
# Per-claim axioms read from the built environment (lean-pkg's ClaimAxioms.lean, core Lean only):
# `claim-axioms: NAME AXIOMS` / `claim-missing: NAME` for every claim of claims.yaml, then
# `claim-axioms-done: N`. The receipt refuses a missing or unchecked claim and sorryAx.
claims_decls() {
  awk 'function val(s) {
  sub(/^[A-Za-z_]+:[ \t]*/, "", s); sub(/[ \t]+#.*$/, "", s); sub(/[ \t\r]+$/, "", s)
  if (s ~ /^".*"$/ || s ~ /^'\''.*'\''$/) s = substr(s, 2, length(s) - 2)
  return s
}
function flush() { if (decl != "") print decl "\t" file; decl = ""; file = "" }
BEGIN { item = -1; key = -1 }
/^[ \t]*#/ || /^[ \t\r]*$/ { next }
/^claims:/ { inl = 1; next }
inl && /^[^ \t-]/ { flush(); inl = 0 }
!inl { next }
{
  match($0, /^ */); ind = RLENGTH; rest = substr($0, ind + 1)
  if (rest ~ /^- /) {
    if (item < 0) item = ind
    if (ind == item) { flush(); match(rest, /^- +/); ind = ind + RLENGTH; rest = substr(rest, RLENGTH + 1); key = ind }
  }
  if (ind == key) {
    if (rest ~ /^decl:/) decl = val(rest)
    else if (rest ~ /^file:/) file = val(rest)
  }
}
END { flush() }' "$1"
}
claim_axioms_run() {
  [ -f claims.yaml ] || return 0
  local pairs names mods
  pairs=$(claims_decls claims.yaml)
  if [ -z "$pairs" ]; then echo "claim-axioms-done: 0" >>"$1"; return 0; fi
  names=$(printf '%s\n' "$pairs" | cut -f1)
  mods=$(printf '%s\n' "$pairs" | cut -f2 | grep '\.lean$' | sed -e 's/\.lean$//' -e 's|/|.|g' | sort -u || true)
  mkdir -p "$2"
  cat >"$2/ClaimAxioms.lean" <<'LEAN_PKG_CLAIM_AXIOMS'
/-
Copyright 2026 Le Chen. SPDX-License-Identifier: Apache-2.0
-/
-- lean_pkg.claim_axioms: the Lean half. Read-only probe of a compiled environment.
--
-- Usage: LEAN_PATH=<the package's> lean --run ClaimAxioms.lean MOD [MOD ...] -- NAME [NAME ...]
--
-- Imports MOD... exactly as `import MOD` would (data only: no extension state is loaded and no
-- initializer runs, so Lean walks every constant body itself instead of reading axiom lists cached in
-- the .olean files), then runs core Lean's `collectAxioms` on every NAME and prints one line per name:
--   claim-axioms: NAME AX1,AX2,...   (sorted; `none` when it depends on no axiom)
--   claim-missing: NAME              (no constant of that name in the environment)
-- and a final `claim-axioms-done: N` line (N = the number of names). A run without that line is
-- incomplete; lean_pkg/claim_axioms.py refuses it. Nothing is judged here. Core Lean only.
import Lean

open Lean

/-- The monad `collectAxioms` needs: an environment that can be read. -/
abbrev ClaimAxiomsM := StateM Environment

instance : MonadEnv ClaimAxiomsM where
  getEnv := get
  modifyEnv f := modify f

def main (args : List String) : IO UInt32 := do
  let mods := args.takeWhile (· != "--")
  let names := (args.dropWhile (· != "--")).drop 1
  if mods.isEmpty || names.isEmpty then
    IO.eprintln "usage: lean --run ClaimAxioms.lean MOD [MOD ...] -- NAME [NAME ...]"
    return 2
  initSearchPath (← findSysroot)
  let imports := mods.toArray.map fun m => ({ module := m.toName } : Import)
  let env ← importModules imports {} (loadExts := false)
  let mut n := 0
  for s in names do
    n := n + 1
    let name := s.toName
    if (env.find? name).isNone then
      IO.println s!"claim-missing: {s}"
    else
      let (axs, _) := (collectAxioms name : ClaimAxiomsM (Array Name)).run env
      let sorted := (axs.map toString).qsort (· < ·)
      let shown := if sorted.isEmpty then "none" else ",".intercalate sorted.toList
      IO.println s!"claim-axioms: {s} {shown}"
  IO.println s!"claim-axioms-done: {n}"
  return 0
LEAN_PKG_CLAIM_AXIOMS
  # shellcheck disable=SC2086 # one word per module and per name
  ${RUN:-} env LEAN_PATH="$3" lean --run "$2/ClaimAxioms.lean" $mods -- $names >>"$1" 2>&1
}
# Conditional-claim facts read from the built environment (lean-pkg's HypProbe.lean, core Lean only;
# proposal 0003): the `== lean-pkg hypotheses (hyp-probe/1) ==` section, one `hyp-*: {json}` line
# per fact, then `hyp-done`. The Challenge is built into a side log, never into this log.
hyp_json_str() {
  printf '"%s"' "$(printf '%s' "$1" | tr -d '\000-\037' | sed -e 's/\\/\\\\/g' -e 's/"/\\"/g')"
}
hyp_error() {   # OUT PHASE EXIT FILE...: one hyp-error line, the first error line without paths
  local out=$1 phase=$2 rc=$3 msg
  shift 3
  msg=$(cat "$@" 2>/dev/null | grep -m1 -i 'error' | sed -e 's#[^ ]*/##g' | cut -c1-200 || true)
  echo "hyp-error: {\"phase\":\"$phase\",\"message\":$(hyp_json_str "exit $rc${msg:+: $msg}")}" >>"$out"
}
hypotheses_run() {
  [ -f claims.yaml ] || return 0
  local dir=$2 side=${4:-$2/hyp-challenge-build.log} pairs names mods rc cfgs="" cfg m ok built=1 decls chal list=""
  mkdir -p "$dir"
  local out="$dir/hyp.out" part="$dir/hyp.part" err="$dir/hyp.err"
  : >"$out"
  cat >"$dir/HypProbe.lean" <<'LEAN_PKG_HYP_PROBE'
/-
Copyright 2026 Le Chen. SPDX-License-Identifier: Apache-2.0
-/
-- lean_pkg.hypotheses: the Lean half (proposal 0003, the `hyp-probe/1` section of the verify log).
-- Read-only probe of a compiled environment. Lean prints facts; lean_pkg/hypotheses.py judges them.
--
-- Usage (LEAN_PATH=<the package's>):
--   lean --run HypProbe.lean decl MOD [MOD ...] -- NAME [NAME ...]
--       imports MOD... and prints, for every NAME, one line
--         hyp-decl: {"v":1,"theorem":N,"binders":[{"i","head","kind","module","explicit"}...],"data_binders":k}
--         hyp-missing: {"v":1,"theorem":N}            (no constant of that name)
--   lean --run HypProbe.lean modules CFG [CFG ...]
--       reads each comparator configuration (JSON) and prints `challenge-module: M` for its `challenge_module`,
--       each module once (for the job, which builds them outside the sealed log; never part of the log).
--   lean --run HypProbe.lean challenge CFG [CFG ...]
--       imports every configuration's Challenge module into one environment and prints
--         hyp-challenge: {... as hyp-decl ..., "config":C}  (once per name of each configuration's theorem_names)
--       then positive facts only, over the distinct Challenge theorems:
--         hyp-corollary: {"corollary":T',"of":T,"drops":[H...],"binders":[i...]}
--         hyp-proof: {"proof":P,"proves":H}
--         hyp-witness: {"witness":W,"of":T}
--         hyp-skip: {"theorem":T,"reason":R}           (more than MAX_HYPS distinct hypothesis constants)
--         hyp-error: {"phase":"challenge","message":M}  (a configured name that is not in the environment)
-- The header line and the final `hyp-done` line are written by the job (hypotheses.job_sh), which counts
-- these lines. A run that fails (exit code not 0) is replaced by one `hyp-error` line there.
--
-- Comparison (proposal 0003, open question 4): `Expr.eqv` (`==`: binder names and annotations ignored), plus
-- equal binder annotations on the outer binders, plus the other theorem's universe parameters renamed
-- positionally. No unfolding, no `whnf`, no `isDefEq`. Only non-dependent binders are dropped. Core Lean only.
import Lean

open Lean Meta

namespace HypProbe

/-- Above this many distinct hypothesis constants the 2^m subset search is not run (`hyp-skip`). -/
def MAX_HYPS : Nat := 12

def kindOf : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "def"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quot"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

/-- A JSON string. -/
def js (s : String) : String := (Json.str s).compress

def str (n : Name) : String := js n.toString

/-- A JSON object of already rendered values, its keys in the given order, compact. -/
def obj (pairs : List (String × String)) : String :=
  "{" ++ ",".intercalate (pairs.map fun (k, v) => js k ++ ":" ++ v) ++ "}"

def arr (xs : Array String) : String := "[" ++ ",".intercalate xs.toList ++ "]"

def line (tag : String) (pairs : List (String × String)) : IO Unit :=
  IO.println s!"{tag}: {obj pairs}"

/-- One `Prop` binder headed by a constant: its position, head, the head's kind and module, explicitness. -/
structure Hyp where
  i : Nat
  head : Name
  explicit : Bool

/-- The binders of a type's telescope (not unfolded): the `Prop` binders headed by a constant, and the number
of binders that are not `Prop`s. -/
def binders (ty : Expr) : MetaM (Array Hyp × Nat) :=
  forallTelescope ty fun xs _ => do
    let mut out := #[]
    let mut data := 0
    for h : i in [0:xs.size] do
      let d ← xs[i].fvarId!.getDecl
      let t := d.type
      if ← isProp t then
        let f := t.getAppFn
        if f.isConst then
          out := out.push { i, head := f.constName!, explicit := d.binderInfo.isExplicit }
      else
        data := data + 1
    return (out, data)

def moduleOf (env : Environment) (c : Name) : String :=
  match env.getModuleIdxFor? c with
  | some idx => (env.allImportedModuleNames[idx.toNat]?.map toString).getD ""
  | none => ""

def binderJson (env : Environment) (h : Hyp) : String :=
  let k := (env.find? h.head).map kindOf |>.getD "missing"
  obj [("i", toString h.i), ("head", str h.head), ("kind", js k), ("module", js (moduleOf env h.head)),
    ("explicit", toString h.explicit)]

/-- The `hyp-decl` / `hyp-challenge` keys of a constant. -/
def declPairs (env : Environment) (thm : Name) (ty : Expr) : MetaM (List (String × String)) := do
  let (hs, data) ← binders ty
  return [("v", "1"), ("theorem", str thm), ("binders", arr (hs.map (binderJson env))),
    ("data_binders", toString data)]

/-- `ty` without the outer binders at the positions `drop` selects, or none when a kept binder or the body
mentions a dropped one. -/
partial def dropAt (drop : Nat → Bool) : Nat → Expr → Option Expr
  | i, .forallE n t b bi =>
    if drop i then
      if b.hasLooseBVar 0 then none else dropAt drop (i + 1) (b.lowerLooseBVars 1 1)
    else (dropAt drop (i + 1) b).map fun b' => .forallE n t b' bi
  | _, e => some e

/-- The binder annotations of the outer binders. -/
def infos : Expr → List BinderInfo
  | .forallE _ _ b bi => bi :: infos b
  | _ => []

/-- `Expr.eqv` plus equal outer binder annotations. -/
def same (a b : Expr) : Bool := a == b && infos a == infos b

/-- `ci`'s type with its universe parameters renamed positionally to `us` (same count), else unchanged. -/
def typeAt (ci : ConstantInfo) (us : List Name) : Expr :=
  if ci.levelParams.length == us.length then ci.instantiateTypeLevelParams (us.map mkLevelParam) else ci.type

/-- The expected witness type of `ty`: `∃` over its non-`Prop` binders in order, of the right-nested `∧` of all
its `Prop` binders in order; none when there is no `Prop` binder or the result would mention a proof. -/
def witnessType (ty : Expr) : MetaM (Option Expr) :=
  forallTelescope ty fun xs _ => do
    let mut data := #[]
    let mut props := #[]
    for x in xs do
      let t ← inferType x
      if ← isProp t then props := props.push t else data := data.push x
    if props.isEmpty then return none
    let conj := props.pop.foldr (fun p acc => mkAnd p acc) props.back!
    let mut body := conj
    for x in data.reverse do
      body ← mkAppM ``Exists #[← mkLambdaFVars #[x] body]
    body ← instantiateMVars body
    if body.hasAnyFVar (fun f => xs.any (·.fvarId! == f)) then return none
    return some body

/-- The subsets of `xs` (as lists, in `xs` order), the empty one first. -/
def subsets : List Name → List (List Name)
  | [] => [[]]
  | x :: rest => let r := subsets rest; r ++ r.map (x :: ·)

def runDecl (names : List String) : MetaM Unit := do
  let env ← getEnv
  for s in names do
    let n := s.toName
    match env.find? n with
    | none => line "hyp-missing" [("v", "1"), ("theorem", js s)]
    | some ci => line "hyp-decl" (← declPairs env n ci.type)

structure Config where
  path : String
  challenge : Name
  names : Array Name

def readConfig (path : String) : IO Config := do
  let text ← IO.FS.readFile path
  let j ← IO.ofExcept (Json.parse text |>.mapError fun e => s!"{path}: not JSON: {e}")
  let m ← IO.ofExcept (j.getObjValAs? String "challenge_module"
    |>.mapError fun _ => s!"{path}: no string challenge_module")
  let ns ← IO.ofExcept (j.getObjValAs? (Array String) "theorem_names"
    |>.mapError fun _ => s!"{path}: theorem_names is not a list of strings")
  return { path, challenge := m.toName, names := ns.map String.toName }

def runChallenge (cfgs : Array Config) : MetaM Unit := do
  let env ← getEnv
  let mut thms : Array Name := #[]
  for c in cfgs do
    for n in c.names do
      match env.find? n with
      | none =>
        line "hyp-error" [("phase", js "challenge"),
          ("message", js s!"{n} (theorem_names of {c.path}) is not in the Challenge environment")]
      | some ci =>
        line "hyp-challenge" ((← declPairs env n ci.type) ++ [("config", js c.path)])
        unless thms.contains n do thms := thms.push n
  -- the binders of every distinct Challenge theorem, and every hypothesis constant
  let mut info : Array (Name × ConstantInfo × Array Hyp) := #[]
  let mut heads : Array Name := #[]
  for n in thms do
    let ci := (env.find? n).get!
    let (hs, _) ← binders ci.type
    info := info.push (n, ci, hs)
    for h in hs do
      unless heads.contains h.head do heads := heads.push h.head
  -- hyp-corollary: T' is T with every binder headed by a constant of S removed (S non-empty)
  for (t, tci, hs) in info do
    let consts := hs.foldl (fun acc h => if acc.contains h.head then acc else acc.push h.head) #[]
    if consts.size > MAX_HYPS then
      line "hyp-skip" [("theorem", str t), ("reason", js
        s!"{consts.size} distinct hypothesis constants, more than {MAX_HYPS}: the corollary search is not run")]
      continue
    for s in subsets consts.toList do
      if s.isEmpty then continue
      let pos := hs.filter (s.contains ·.head) |>.map (·.i)
      let some dropped := dropAt (pos.contains ·) 0 tci.type | continue
      for (c, cci, _) in info do
        if c == t then continue
        if same dropped (typeAt cci tci.levelParams) then
          line "hyp-corollary" [("corollary", str c), ("of", str t),
            ("drops", arr (s.toArray.map str)), ("binders", arr (pos.map toString))]
  -- hyp-proof: a theorem whose type is exactly a hypothesis constant
  for (p, pci, _) in info do
    match pci.type with
    | .const h _ => if heads.contains h then line "hyp-proof" [("proof", str p), ("proves", str h)]
    | _ => pure ()
  -- hyp-witness: a theorem whose type is the expected witness type of a conditional theorem
  for (t, tci, hs) in info do
    if hs.isEmpty then continue
    let some w ← (try witnessType tci.type catch _ => pure none) | continue
    for (c, cci, _) in info do
      if c == t then continue
      if typeAt cci tci.levelParams == w then
        line "hyp-witness" [("witness", str c), ("of", str t)]

def runMeta (env : Environment) (x : MetaM Unit) : IO Unit := do
  let ctx : Core.Context := { fileName := "<hypprobe>", fileMap := default }
  let _ ← (x.run' {}).toIO ctx { env := env }

def importAll (mods : Array Name) : IO Environment := do
  initSearchPath (← findSysroot)
  importModules (mods.map fun m => ({ module := m } : Import)) {} (loadExts := false)

end HypProbe

open HypProbe in
def main (args : List String) : IO UInt32 := do
  match args with
  | "decl" :: rest =>
    let mods := rest.takeWhile (· != "--")
    let names := (rest.dropWhile (· != "--")).drop 1
    if mods.isEmpty || names.isEmpty then
      IO.eprintln "usage: lean --run HypProbe.lean decl MOD [MOD ...] -- NAME [NAME ...]"
      return 2
    let env ← importAll (mods.toArray.map String.toName)
    runMeta env (runDecl names)
    return 0
  | "modules" :: cfgs@(_ :: _) =>
    let mut seen : Array Name := #[]
    for p in cfgs do
      let c ← readConfig p
      unless seen.contains c.challenge do
        seen := seen.push c.challenge
        IO.println s!"challenge-module: {c.challenge}"
    return 0
  | "challenge" :: cfgs@(_ :: _) =>
    let cs ← cfgs.toArray.mapM readConfig
    let mods := cs.foldl (fun acc c => if acc.contains c.challenge then acc else acc.push c.challenge) #[]
    let env ← importAll mods
    runMeta env (runChallenge cs)
    return 0
  | _ =>
    IO.eprintln "usage: lean --run HypProbe.lean (decl MOD... -- NAME... | modules CFG... | challenge CFG...)"
    return 2
LEAN_PKG_HYP_PROBE
  pairs=$(claims_decls claims.yaml)
  if [ -n "$pairs" ]; then
    names=$(printf '%s\n' "$pairs" | cut -f1)
    mods=$(printf '%s\n' "$pairs" | cut -f2 | grep '\.lean$' | sed -e 's/\.lean$//' -e 's|/|.|g' | sort -u || true)
    rc=0
    # shellcheck disable=SC2086 # one word per module and per name
    ${RUN:-} env LEAN_PATH="$3" lean --run "$dir/HypProbe.lean" decl $mods -- $names >"$part" 2>"$err" || rc=$?
    if [ "$rc" = 0 ]; then grep -E '^hyp-[a-z-]+: ' "$part" >>"$out" || true
    else hyp_error "$out" decl "$rc" "$part" "$err"; fi
  fi
  if grep -Eq '^[[:blank:]-]+(hypotheses|discharges|witness):' claims.yaml; then
    for cfg in comparator*.json comparator/config*.json; do
      if [ -f "$cfg" ]; then cfgs="$cfgs $cfg"; list="$list${list:+,}$(hyp_json_str "$cfg")"; fi
    done
    if [ -n "$cfgs" ]; then
      rc=0
      # shellcheck disable=SC2086 # one word per configuration
      ${RUN:-} env LEAN_PATH="$3" lean --run "$dir/HypProbe.lean" modules $cfgs >"$part" 2>"$err" || rc=$?
      if [ "$rc" != 0 ]; then hyp_error "$out" challenge "$rc" "$part" "$err"
      else
        sed -n 's/^challenge-module: //p' "$part" >"$dir/modules"
        : >"$side"
        while IFS= read -r m; do
          ok=true
          ${RUN:-} lake build "$m" </dev/null >>"$side" 2>&1 || { ok=false; built=0; }
          echo "hyp-challenge-build: {\"module\":$(hyp_json_str "$m"),\"ok\":$ok}" >>"$out"
        done <"$dir/modules"
        if [ "$built" = 1 ]; then
          rc=0
          # shellcheck disable=SC2086 # one word per configuration
          ${RUN:-} env LEAN_PATH="$3" lean --run "$dir/HypProbe.lean" challenge $cfgs >"$part" 2>"$err" || rc=$?
          if [ "$rc" = 0 ]; then grep -E '^hyp-[a-z-]+: ' "$part" >>"$out" || true
          else hyp_error "$out" challenge "$rc" "$part" "$err"; fi
        else
          echo "hyp-error: {\"phase\":\"challenge\",\"message\":\"a Challenge module did not build (its output: the side log hyp-challenge-build.log)\"}" >>"$out"
        fi
      fi
    fi
  fi
  decls=$(grep -c -E '^hyp-(decl|missing): ' "$out" || true)
  chal=$(grep -c '^hyp-challenge: ' "$out" || true)
  {
    echo "== lean-pkg hypotheses (hyp-probe/1) =="
    cat "$out"
    echo "hyp-done: {\"v\":1,\"decls\":$decls,\"challenge\":$chal,\"configs\":[$list]}"
  } >>"$1"
}
# The dependency restore may change .lake/packages and nothing else: a listing and the content hashes of the
# rest of the tree (.lake itself aside, which it may create) are compared before and after. (No directory
# sizes or times: creating .lake changes those of the package directory on some filesystems.)
deps_snapshot() {
  find . -path ./.lake/packages -prune -o -path ./.lake -o -printf '%y %m %p -> %l\n' | LC_ALL=C sort
  find . -path ./.lake/packages -prune -o -type f -print0 | LC_ALL=C sort -z | xargs -0 -r sha256sum
}
if [ -n "$DEPS_TAR" ]; then
  if [ -L .lake ] || [ -e .lake/packages ] || [ -L .lake/packages ]; then
    echo "error: DEPS_TAR: the committed tree already holds .lake/packages (or .lake is a symlink)" >>"$LOG"
    exit 1
  fi
  before=$(deps_snapshot | sha256sum)
  mkdir -p "$DEPS_STAGE"
  tar -xf "$DEPS_TAR" -C "$DEPS_STAGE" --no-same-owner
  if [ -L "$DEPS_STAGE/.lake" ] || [ -L "$DEPS_STAGE/.lake/packages" ] || [ ! -d "$DEPS_STAGE/.lake/packages" ]; then
    echo "error: DEPS_TAR holds no .lake/packages directory (a symlink is not one)" >>"$LOG"
    exit 1
  fi
  mkdir -p .lake
  mv "$DEPS_STAGE/.lake/packages" .lake/packages
  rm -rf "$DEPS_STAGE"
  if [ "$(deps_snapshot | sha256sum)" != "$before" ]; then
    echo "error: DEPS_TAR: the restore changed the tree outside .lake/packages" >>"$LOG"
    exit 1
  fi
  # A dependency's build directory holding a root namespace would shadow the package (see LEAN_PATH below).
  shadowed=""
  for r in $(lake_root_namespaces); do
    hit=$(find .lake/packages \( -path "*/build/lib/lean/$r" -o -path "*/build/lib/lean/$r.olean" \
      -o -path "*/build/lib/lean/$r.ilean" \) -print -quit)
    if [ -n "$hit" ]; then
      echo "deps-restore-shadow: $hit" >>"$LOG"
      shadowed="$shadowed $r"
    fi
  done
  if [ -n "$shadowed" ]; then
    echo "error: DEPS_TAR: a dependency's build directory holds the package's root namespace(s):$shadowed" >>"$LOG"
    exit 1
  fi
  echo "deps-restore-check: ok (only .lake/packages changed; no root namespace in it)" >>"$LOG"
fi
if [ -e .lake/build ] || [ -n "$(ls -A "$LAKE_CACHE_DIR")" ]; then
  echo "error: not a fresh build: the committed tree holds .lake/build, or the Lake cache is not empty" >>"$LOG"
  exit 1
fi
echo "lean-pkg-build: begin" >>"$LOG"
$RUN bash -c "$VERIFY_CMD" >>"$LOG" 2>&1
echo "lean-pkg-build: end" >>"$LOG"
# A root-package module Lake restored instead of compiling fails the job: its sorry warning need not be in the
# log. (Lake prints such a job only when it has output, or with -v; the empty cache is the real defence.) A
# cache line after the module's own Built is Lake re-printing its stored warnings, not a restore.
restored=""
for m in $(sed -n '/^lean-pkg-build: begin$/,/^lean-pkg-build: end$/p' "$LOG" \
    | grep -oE '\[[0-9]+/[0-9]+\]( \(Optional\))? (Built|Reused|Replayed|Unpacked) [^ ]+' \
    | awk '{m = $NF; sub(/:.*$/, "", m); if ($(NF - 1) == "Built") b[m] = 1; else if (!(m in b)) print m}' \
    | sort -u || true); do
  if [ -n "$(find . -path ./.lake -prune -o -path "*/${m//.//}.lean" -print -quit 2>/dev/null)" ] \
      || lake_root_namespaces | grep -qxF "${m%%.*}"; then
    restored="$restored $m"
  fi
done
if [ -n "$restored" ]; then
  echo "error: Lake restored root-package module(s) instead of compiling them:$restored" >>"$LOG"
  exit 1
fi
# LEAN_PATH: Lake lists the package's own lib directory last and Lean loads <R>/ from the first entry holding
# it, so a dependency's build directory holding the package's namespace is refused before the audit. The
# check runs here, outside $RUN: with a container, bind the work directory at the same path.
lean_path=$($RUN bash -c "$LEAN_PATH_CMD")
if ! lake_shadow_check "$lean_path" >>"$LOG"; then
  echo "error: a LEAN_PATH entry shadows the package's own modules (lean-path-shadow lines above)" >>"$LOG"
  exit 1
fi
$RUN bash -c "$AXIOMS_CMD" >>"$LOG" 2>&1
# Every claim's axioms, read from the built environment (claim_axioms_run above; not only the printed ones).
claim_axioms_run "$LOG" "$WORK/claim-axioms" "$lean_path"
# The hyp-probe/1 section (proposal 0003): every claim's Prop hypotheses, and with conditional claims the
# Challenge facts. The Challenge is built into the side log $WORK/hyp-challenge-build.log, never into $LOG.
hypotheses_run "$LOG" "$WORK/hyp-probe" "$lean_path" "$WORK/hyp-challenge-build.log"
echo "fs-file-nr-after: $(cat /proc/sys/fs/file-nr 2>/dev/null || echo unavailable)" >>"$LOG"

# The artifact seal (ARTIFACTS_DIR above). artifacts_list DIR: the manifest lines of the regular files under DIR,
# sorted by path (C locale), the manifest itself left out.
artifacts_list() {
  (cd "$1" && find . -path "./$ARTIFACTS_MANIFEST" -prune -o -type f -print0 | LC_ALL=C sort -z \
    | while IFS= read -r -d '' f; do
        printf '%s %s %s\n' "${f#./}" "$(stat -c %s "$f")" "$(sha256sum <"$f" | cut -d' ' -f1)"
      done)
}
artifacts_sha=""
if [ -n "$ARTIFACTS_DIR" ]; then
  case "$ARTIFACTS_BASE" in
    src) abase="$SRC" ;;
    work) abase="$WORK" ;;
    *) echo "error: ARTIFACTS_BASE is src or work, not '$ARTIFACTS_BASE'" >>"$LOG"; exit 1 ;;
  esac
  case "/$ARTIFACTS_DIR/" in
    //*|*/../*) echo "error: ARTIFACTS_DIR must be a relative path without '..'" >>"$LOG"; exit 1 ;;
  esac
  adir="$abase/$ARTIFACTS_DIR"
  if [ ! -d "$adir" ] || [ "$(realpath -e "$adir")" != "$(realpath -m -s "$(realpath -e "$abase")/$ARTIFACTS_DIR")" ]; then
    echo "error: ARTIFACTS_DIR is not a directory under $ARTIFACTS_BASE (or a path component is a symlink)" >>"$LOG"
    exit 1
  fi
  bad=$(find "$adir" ! -type f ! -type d -print -quit)
  if [ -n "$bad" ]; then
    echo "error: ARTIFACTS_DIR holds a symlink or special file: ${bad#"$adir"/}" >>"$LOG"
    exit 1
  fi
  if [ -n "$(find "$adir" -name $'*[\n\r]*' -print -quit)" ]; then
    echo "error: ARTIFACTS_DIR holds a file name with a newline" >>"$LOG"
    exit 1
  fi
  if [ -e "$adir/$ARTIFACTS_MANIFEST" ]; then
    echo "error: ARTIFACTS_DIR already holds $ARTIFACTS_MANIFEST, the manifest's own name" >>"$LOG"
    exit 1
  fi
  if [ -e "$ARTIFACTS_OUT" ] || [ -L "$ARTIFACTS_OUT" ]; then
    echo "error: ARTIFACTS_OUT already exists; the job never overwrites artifacts" >>"$LOG"
    exit 1
  fi
  mkdir -p "$(dirname "$ARTIFACTS_OUT")"
  mkdir "$ARTIFACTS_OUT"
  artifacts_list "$adir" >"$ARTIFACTS_OUT/$ARTIFACTS_MANIFEST"
  cp -R "$adir/." "$ARTIFACTS_OUT/"
  # the copy is what is collected: it must rehash to the manifest taken from the job's own tree
  if ! artifacts_list "$ARTIFACTS_OUT" | cmp -s - "$ARTIFACTS_OUT/$ARTIFACTS_MANIFEST"; then
    echo "error: the copy in ARTIFACTS_OUT does not rehash to the manifest of ARTIFACTS_DIR" >>"$LOG"
    exit 1
  fi
  artifacts_sha=$(sha256sum "$ARTIFACTS_OUT/$ARTIFACTS_MANIFEST" | cut -d' ' -f1)
  echo "artifacts-manifest: $(wc -l <"$ARTIFACTS_OUT/$ARTIFACTS_MANIFEST") file(s) from $ARTIFACTS_BASE/$ARTIFACTS_DIR, sha256 $artifacts_sha" >>"$LOG"
fi

# The key lines, from Lean's own output in the log: sorry-count may not be lower than the
# `declaration uses `sorry`` warnings (either quote style), and axioms may not leave out a `#print axioms` result.
sorry=$(grep -c -E "declaration uses ['\`]sorry['\`]" "$LOG" || true)
# (newlines joined first: Lean wraps a long axiom list over several lines)
axioms=$(tr '\n' ' ' <"$LOG" | grep -o 'depends on axioms: \[[^]]*\]' | sed -e 's/^[^[]*\[//' -e 's/\]$//' \
  | tr ',' '\n' | tr -d ' ' | grep -v '^$' | sort -u | paste -sd, - || true)
{
  echo "sorry-count: $sorry"
  if [ -n "$axioms" ]; then
    echo "axioms: $axioms"
  elif grep -q 'does not depend on any axioms' "$LOG"; then
    echo "axioms: none"
  fi
  echo "generated-at: $(date -u +%Y-%m-%dT%H:%M:%SZ)"
} >>"$LOG"

# The seal: nothing may write to the log after this line.
if [ -n "$artifacts_sha" ]; then
  echo "artifacts-manifest-sha256 $artifacts_sha"
fi
echo "post-manifest-sha256 $(sha256sum lake-manifest.json | cut -d' ' -f1)"
echo "verify-log-sha256 $(sha256sum "$LOG" | cut -d' ' -f1)"
