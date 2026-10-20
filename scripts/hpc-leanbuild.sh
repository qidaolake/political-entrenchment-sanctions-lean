#!/bin/bash
#SBATCH --job-name=spcl-lean-build
#SBATCH --output=build_%j.out
#SBATCH --error=build_%j.err
#SBATCH --time=06:00:00
#SBATCH --nodes=1
#SBATCH --ntasks=1
#SBATCH --cpus-per-task=8
#SBATCH --mem=64G
# SanctionPublicChoiceLean HPC Lean gate (CLAUDE.md Rule 26). Ported on 2026-10-01 from
# HigherOrderBelief's analysis/hpc-leanbuild.sh and adapted: its own persistent work tree
# (this project pins a different toolchain), the seven-gate audit run in the same job against
# the tree it just built, pwsh/node/elan from pinned archives, and a round axiom scan.
# Packaged by scripts/hpc-package.py; the return is checked by scripts/hpc-verify-return.py.
set -uo pipefail
umask 077
START=$(date +%s)
RUNDIR="${SLURM_SUBMIT_DIR:?SLURM_SUBMIT_DIR is required}"
PKGDIR="${RUNDIR}/leanbuild"
WORK="${HOME}/spcl-lean-work"
JOB="${SLURM_JOB_ID:?SLURM_JOB_ID is required}"
mkdir -p "${WORK}" || exit 90

# Verify every persistent cleanup boundary before removing any source or project artifact.
EXPECTED_WORK="$(readlink -f "${HOME}")/spcl-lean-work"
[ "$(readlink -f "${WORK}")" = "${EXPECTED_WORK}" ] || exit 91
[ "$(readlink -f "${PKGDIR}")" = "$(readlink -f "${RUNDIR}")/leanbuild" ] || exit 92
exec 9>"${WORK}/.gate.lock"
flock -n 9 || { echo "FATAL another build owns the persistent work tree"; exit 93; }

# Run-private managed temporary storage. The runtime, tools and dependency cache persist.
export TMPDIR="${WORK}/run-temp/${JOB}"
export TEMP="${TMPDIR}"
export TMP="${TMPDIR}"
mkdir -p "${TMPDIR}" || exit 94
[ "$(readlink -f "${TMPDIR}")" = "${EXPECTED_WORK}/run-temp/${JOB}" ] || exit 95
export ELAN_HOME="${WORK}/.elan"
TOOLS="${WORK}/.tools"
SHIM="${WORK}/.shim"
export LEAN_NUM_THREADS="${SLURM_CPUS_PER_TASK:-8}"
export POWERSHELL_TELEMETRY_OPTOUT=1
export POWERSHELL_UPDATECHECK=Off
export DOTNET_CLI_TELEMETRY_OPTOUT=1
# No __pycache__ inside the package: the receipt helper checks the package inventory exactly.
export PYTHONDONTWRITEBYTECODE=1
HELPER="${PKGDIR}/hpc_gate_receipt.py"
LOG="${RUNDIR}/runtime.log"

{
  echo "RECEIPT_SCHEMA=spcl-lean-build/v1"
  echo "job_id=${JOB} node=$(hostname) start_utc=$(date -u +%FT%TZ)"
  echo "WORK=${WORK} TMPDIR=${TMPDIR} LEAN_NUM_THREADS=${LEAN_NUM_THREADS}"
  echo "runtime=persistent tools=persistent cache=persistent project_build=from-empty"
  echo "declared_incremental_disk_ceiling_bytes=34359738368 declared_incremental_inode_ceiling=100000"
  head -n 2 /etc/os-release 2>&1 || true
  ldd --version 2>&1 | head -n 1 || true
  df -PB1 "${WORK}"
  df -Pi "${WORK}"
  quota -s 2>&1 || true
  ulimit -a
} >"${LOG}" 2>&1
FREE_BYTES=$(df -PB1 "${WORK}" | awk 'NR==2 {print $4}')
FREE_INODES=$(df -Pi "${WORK}" | awk 'NR==2 {print $4}')
[ "${FREE_BYTES}" -ge 34359738368 ] && [ "${FREE_INODES}" -ge 100000 ] \
  || { echo "FATAL managed storage admission"; exit 96; }

# --- Environment, fail fast: everything the build and the audit need, before any long step ---
# Python 3.12 from the cluster module catalog; the audit calls `python`, so shim it.
set +u
if ! type module >/dev/null 2>&1; then
  for init in /etc/profile.d/lmod.sh /etc/profile.d/modules.sh /usr/share/lmod/lmod/init/bash; do
    if [ -r "${init}" ]; then . "${init}"; break; fi
  done
fi
if type module >/dev/null 2>&1; then module load python/3.12.14 >>"${LOG}" 2>&1; fi
set -u
PY="$(command -v python3 || true)"
[ -n "${PY}" ] || { echo "FATAL python3 absent"; exit 97; }
"${PY}" -c 'import sys; assert sys.version_info >= (3, 9), sys.version' >>"${LOG}" 2>&1 \
  || { echo "FATAL python3 older than 3.9"; exit 97; }
mkdir -p "${SHIM}" && ln -sfn "${PY}" "${SHIM}/python" || exit 97

# Pinned tool archives: digest-checked against the package, unpacked once into the work tree.
( cd "${PKGDIR}/vendor" && sha256sum -c VENDOR.sha256 ) >>"${LOG}" 2>&1 \
  || { echo "FATAL vendored archive digest"; exit 97; }
install_archive() {  # name archive strip-components
  local name="$1" archive="$2" strip="$3"
  local dest="${TOOLS}/${name}" want
  want="$(sha256sum "${archive}" | awk '{print $1}')"
  [ "$(readlink -m "${dest}")" = "${EXPECTED_WORK}/.tools/${name}" ] || return 1
  if [ -f "${dest}/.installed-sha256" ] && [ "$(cat "${dest}/.installed-sha256")" = "${want}" ]; then
    echo "${name}: persistent install reused (${want})"
    return 0
  fi
  rm -rf -- "${dest}" && mkdir -p "${dest}" \
    && tar -xzf "${archive}" -C "${dest}" --strip-components="${strip}" \
    && echo "${want}" >"${dest}/.installed-sha256" \
    && echo "${name}: installed (${want})"
}
mkdir -p "${TOOLS}" || exit 97
install_archive pwsh "${PKGDIR}/vendor/powershell-7.6.6-linux-x64.tar.gz" 0 >>"${LOG}" 2>&1 \
  || { echo "FATAL pwsh install"; exit 97; }
chmod +x "${TOOLS}/pwsh/pwsh" || exit 97
install_archive node "${PKGDIR}/vendor/node-v24.21.0-linux-x64.tar.gz" 1 >>"${LOG}" 2>&1 \
  || { echo "FATAL node install"; exit 97; }
if [ ! -x "${ELAN_HOME}/bin/elan" ]; then
  tar -xzf "${PKGDIR}/vendor/elan-x86_64-unknown-linux-gnu.tar.gz" -C "${TMPDIR}" || exit 97
  "${TMPDIR}/elan-init" -y --no-modify-path --default-toolchain none >>"${LOG}" 2>&1 \
    || { echo "FATAL elan bootstrap"; exit 97; }
  echo "elan: bootstrapped from the pinned archive" >>"${LOG}"
else
  echo "elan: persistent install reused" >>"${LOG}"
fi
export PATH="${SHIM}:${TOOLS}/node/bin:${TOOLS}/pwsh:${ELAN_HOME}/bin:${PATH}"

PWSH_PROBE='$PSVersionTable.PSVersion.ToString()'
if ! pwsh -NoProfile -NonInteractive -Command "${PWSH_PROBE}" >>"${LOG}" 2>&1; then
  export DOTNET_SYSTEM_GLOBALIZATION_INVARIANT=1
  echo "pwsh: retrying with DOTNET_SYSTEM_GLOBALIZATION_INVARIANT=1" >>"${LOG}"
  pwsh -NoProfile -NonInteractive -Command "${PWSH_PROBE}" >>"${LOG}" 2>&1 || { echo "FATAL pwsh"; exit 98; }
fi
{ node --version && python --version && git --version && elan --version; } >>"${LOG}" 2>&1 \
  || { echo "FATAL node/python/git/elan probe"; exit 98; }
echo "ENVIRONMENT_OK utc=$(date -u +%FT%TZ)" | tee -a "${LOG}"

# --- Replace exactly the project sources; keep the pinned dependency checkout and cache ---
for leaf in Sanctions Sanctions.lean RoundScan.lean scripts docs HEADLINE-SNAPSHOT.md \
            README.md BUILD-STATUS.md lakefile.toml lean-toolchain lake-manifest.json; do
  target="${WORK}/${leaf}"
  [ "$(readlink -m "${target}")" = "${EXPECTED_WORK}/${leaf}" ] || exit 99
  rm -rf -- "${target}" || exit 99
done
cp -r "${PKGDIR}/project/." "${WORK}/" || exit 100
cd "${WORK}" || exit 101
PIN="$(tr -d ' \r\n' < lean-toolchain)"
echo "toolchain_pin=${PIN}" >>"${LOG}"
elan toolchain install "${PIN}" >"${RUNDIR}/toolchain_install.log" 2>&1 \
  || { echo "FATAL toolchain install"; exit 102; }

# Explicit trust-store selection, retained from HigherOrderBelief's diagnosed cache-download repair.
for bundle in /etc/pki/tls/certs/ca-bundle.crt /etc/ssl/certs/ca-certificates.crt; do
  if [ -r "${bundle}" ]; then
    export SSL_CERT_FILE="${bundle}"
    export CURL_CA_BUNDLE="${bundle}"
    export SSL_CERT_DIR="$(dirname "${bundle}")"
    break
  fi
done
lake exe cache get >"${RUNDIR}/cache_get.log" 2>&1
CACHE_RC=$?
[ "${CACHE_RC}" -eq 0 ] || { echo "FATAL cache acquisition; no from-source fallback"; exit 104; }
lake env lean --version >"${RUNDIR}/lean_version.log" 2>&1 || exit 102
lake --version >>"${LOG}" 2>&1 || exit 103

# Rule 17: clear the complete project build tree after cache acquisition and before the build.
PROJECT_BUILD="${WORK}/.lake/build"
[ "$(readlink -m "${PROJECT_BUILD}")" = "${EXPECTED_WORK}/.lake/build" ] || exit 105
rm -rf -- "${PROJECT_BUILD}" || exit 106
mkdir -p "${PROJECT_BUILD}" || exit 107
CLEAN_BEFORE=$(find "${PROJECT_BUILD}" -name '*.olean' -type f | wc -l)
[ "${CLEAN_BEFORE}" -eq 0 ] || exit 108
echo "project_oleans_before=${CLEAN_BEFORE}" >>"${LOG}"
"${PY}" "${HELPER}" snapshot --pkg "${PKGDIR}" --work "${WORK}" --out "${RUNDIR}" \
  --label before >"${RUNDIR}/snapshot_before.log" 2>&1 || exit 109

echo "BUILD_STARTED job_id=${JOB} utc=$(date -u +%FT%TZ)" | tee -a "${LOG}"
( while sleep 120; do cp -f "${RUNDIR}/build_full.log" "${RUNDIR}/build_progress.log" 2>/dev/null || true; done ) &
PROGRESS_PID=$!
lake build >"${RUNDIR}/build_full.log" 2>&1
BUILD_RC=$?
kill "${PROGRESS_PID}" 2>/dev/null || true
wait "${PROGRESS_PID}" 2>/dev/null || true
echo "BUILD_DONE build_rc=${BUILD_RC} utc=$(date -u +%FT%TZ) elapsed_seconds=$(( $(date +%s) - START ))" | tee -a "${LOG}"

# The seven audit gates, against the tree this job just built (Rule 26), then the round scan.
AUDIT_RC=125
SCAN_RC=125
CENSUS_RC=125
MAP_RC=125
REPLAY_RC=125
REPLAY_SECONDS=0
FRESH_RC=125
FRESH_SECONDS=0
if [ "${BUILD_RC}" -eq 0 ]; then
  pwsh -NoProfile -NonInteractive -File scripts/Audit-Round.ps1 -SkipBuild >"${RUNDIR}/audit.log" 2>&1
  AUDIT_RC=$?
  cp -f HEADLINE-SNAPSHOT.md "${RUNDIR}/HEADLINE-SNAPSHOT.regenerated.md"
  echo "AUDIT_DONE audit_rc=${AUDIT_RC} utc=$(date -u +%FT%TZ)" | tee -a "${LOG}"
  lake env lean RoundScan.lean >"${RUNDIR}/round_axiom_scan.log" 2>&1
  SCAN_RC=$?
  # Hypothesis census and unused-binder instrument (docs/README.md), against the same tree.
  # Their raw outputs go to the run directory, never into the packaged sources.
  CENSUS_RC=0
  python scripts/census_run.py docs/census/roots-headlines.txt "${RUNDIR}/raw-headlines.txt" \
    >"${RUNDIR}/census.log" 2>&1 || CENSUS_RC=1
  python scripts/census_run.py docs/census/roots-manuscript-names.txt "${RUNDIR}/raw-manuscript.txt" \
    >>"${RUNDIR}/census.log" 2>&1 || CENSUS_RC=1
  python scripts/census_run.py docs/census/roots-preds.txt "${RUNDIR}/raw-preds.txt" censusPreds \
    >>"${RUNDIR}/census.log" 2>&1 || CENSUS_RC=1
  python scripts/unused_run.py "${RUNDIR}/unused-binders.md" docs/census/roots-headlines.txt \
    docs/census/roots-manuscript-names.txt >>"${RUNDIR}/census.log" 2>&1 || CENSUS_RC=1
  echo "CENSUS_DONE census_rc=${CENSUS_RC} utc=$(date -u +%FT%TZ)" | tee -a "${LOG}"
  # Map-identifier scan (LEANREPO M4): every identifier of the formal supplement's primary table
  # names a declaration of the environment just built (scripts/map_identifiers.py generates it).
  lake env lean scripts/map_scan.lean >"${RUNDIR}/map_scan.log" 2>&1
  MAP_RC=$?
  echo "MAP_DONE map_rc=${MAP_RC} utc=$(date -u +%FT%TZ)" | tee -a "${LOG}"
  # Kernel replay (LEANREPO M5), after the from-empty build: the toolchain's leanchecker re-checks
  # every declaration of every compiled Sanctions module against that module's imports. Gating.
  LEANCHECKER="$(dirname "$(elan which lean)")/leanchecker"
  REPLAY_START=$(date +%s)
  lake env "${LEANCHECKER}" -v Sanctions >"${RUNDIR}/leanchecker.log" 2>&1
  REPLAY_RC=$?
  REPLAY_SECONDS=$(( $(date +%s) - REPLAY_START ))
  echo "REPLAY_DONE replay_rc=${REPLAY_RC} seconds=${REPLAY_SECONDS} utc=$(date -u +%FT%TZ)" | tee -a "${LOG}"
  # Fresh replay of the headline closure, Mathlib included, into an empty environment: a timed
  # pilot (90 minutes), recorded in the receipt and never counted as a pass unless it completes.
  FRESH_START=$(date +%s)
  timeout 5400 lake env "${LEANCHECKER}" -v --fresh Sanctions.Headlines \
    >"${RUNDIR}/leanchecker_fresh.log" 2>&1
  FRESH_RC=$?
  FRESH_SECONDS=$(( $(date +%s) - FRESH_START ))
  echo "FRESH_DONE fresh_rc=${FRESH_RC} seconds=${FRESH_SECONDS} utc=$(date -u +%FT%TZ)" | tee -a "${LOG}"
fi
"${PY}" "${HELPER}" snapshot --pkg "${PKGDIR}" --work "${WORK}" --out "${RUNDIR}" \
  --label after >"${RUNDIR}/snapshot_after.log" 2>&1
SNAPSHOT_RC=$?

# Remove only this job's verified run-private temporary directory. Runtime, tools, cache persist.
TEMP_REMOVED=false
if [ "$(readlink -f "${TMPDIR}")" = "${EXPECTED_WORK}/run-temp/${JOB}" ]; then
  rm -rf -- "${TMPDIR}"
  [ ! -e "${TMPDIR}" ] && TEMP_REMOVED=true
fi
echo "end_utc=$(date -u +%FT%TZ) total_seconds=$(( $(date +%s) - START )) temp_removed=${TEMP_REMOVED}" >>"${LOG}"
"${PY}" "${HELPER}" finalize --pkg "${PKGDIR}" --work "${WORK}" --out "${RUNDIR}" \
  --build-rc "${BUILD_RC}" --audit-rc "${AUDIT_RC}" --scan-rc "${SCAN_RC}" --census-rc "${CENSUS_RC}" \
  --snapshot-rc "${SNAPSHOT_RC}" --clean-before "${CLEAN_BEFORE}" --temp-removed "${TEMP_REMOVED}" \
  --map-rc "${MAP_RC}" --replay-rc "${REPLAY_RC}" --replay-seconds "${REPLAY_SECONDS}" \
  --fresh-rc "${FRESH_RC}" --fresh-seconds "${FRESH_SECONDS}" \
  --job-id "${JOB}"
OVERALL_RC=$?
echo "OVERALL_RC=${OVERALL_RC} BUILD_RC=${BUILD_RC} AUDIT_RC=${AUDIT_RC} SCAN_RC=${SCAN_RC} CENSUS_RC=${CENSUS_RC} SNAPSHOT_RC=${SNAPSHOT_RC} MAP_RC=${MAP_RC} REPLAY_RC=${REPLAY_RC} FRESH_RC=${FRESH_RC}"
echo "BUILD_DONE job_id=${JOB}"
exit "${OVERALL_RC}"
