#!/usr/bin/env bash
# Reproducible 3-step verification replay for the frozen polymer decay challenge
# (Targets 1-6c, verification/Challenge.v) and the frozen 4D Z_2 lattice gauge
# theory challenge (Targets 7a-7d, verification/ChallengeZ2Gauge.v).
# Usage (from Windows):
#   wsl -e bash -lc 'bash /mnt/c/GitHub/reimannhypothesis/yang-mills-final-proof/coq/verification/replay.sh'
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
COQ_DIR="$(cd "$SCRIPT_DIR/.." && pwd)"
RECEIPTS="$SCRIPT_DIR/receipts"
mkdir -p "$RECEIPTS"

COQC="${COQC:-/usr/bin/coqc}"
COQCHK="${COQCHK:-/usr/bin/coqchk}"

cd "$COQ_DIR"

echo "=== 1. Toolchain & Source Provenance ==="
{
  echo "Date (UTC): $(date -u +%Y-%m-%dT%H:%M:%SZ)"
  echo "Host: $(uname -a)"
  echo "COQC: $COQC"
  "$COQC" --version
  echo "COQCHK: $COQCHK"
  "$COQCHK" --version || true
  if git -C "$COQ_DIR/.." rev-parse HEAD >/dev/null 2>&1; then
    echo "Git HEAD: $(git -C "$COQ_DIR/.." rev-parse HEAD)"
  fi
} | tee "$RECEIPTS/toolchain.txt"

# The first 16 entries are the byte-identical Targets 1-6c cone pinned by
# Zenodo 10.5281/zenodo.24507324; the last 11 entries are the Target 7 cone.
# The order is a valid compilation order (replay.py compiles in this order).
CONE_SOURCES=(
  "verification/Challenge.v"
  "rg/polymer_types.v"
  "rg/cluster_expansion.v"
  "rg/penrose_tree_bound.v"
  "rg/poly_exp_bound.v"
  "rg/tree_cut_bijection.v"
  "rg/kotecky_preiss.v"
  "rg/exp_series_limit.v"
  "rg/cluster_log_partition.v"
  "ym/geometry_frontier.v"
  "ym/lattice.v"
  "ym/lattice_4d_coordination.v"
  "ym/lattice_4d_kp.v"
  "verification/Verify.v"
  "verification/CheckTypes.v"
  "verification/CheckAxioms.v"
  "verification/ChallengeZ2Gauge.v"
  "rg/dup_clustering.v"
  "rg/polymer_representation.v"
  "rg/connected_subset_bound.v"
  "ym/z2_gauge_expansion.v"
  "ym/z2_gauge_clustering.v"
  "ym/z2_polymer_gas.v"
  "ym/z2_free_energy.v"
  "verification/VerifyZ2Gauge.v"
  "verification/CheckTypesZ2Gauge.v"
  "verification/CheckAxiomsZ2Gauge.v"
)

sha256sum "${CONE_SOURCES[@]}" | tee "$RECEIPTS/sources.sha256"

echo ""
echo "=== 2. Static Guard on Frozen Challenge Files, Zero-Axiom Proofs & Verify Files ==="
GUARD_FILES=(
  "verification/Challenge.v"
  "rg/penrose_tree_bound.v"
  "rg/poly_exp_bound.v"
  "rg/tree_cut_bijection.v"
  "rg/kotecky_preiss.v"
  "rg/exp_series_limit.v"
  "rg/cluster_log_partition.v"
  "ym/lattice_4d_coordination.v"
  "ym/lattice_4d_kp.v"
  "verification/Verify.v"
  "verification/ChallengeZ2Gauge.v"
  "rg/dup_clustering.v"
  "rg/polymer_representation.v"
  "rg/connected_subset_bound.v"
  "ym/z2_gauge_expansion.v"
  "ym/z2_gauge_clustering.v"
  "ym/z2_polymer_gas.v"
  "ym/z2_free_energy.v"
  "verification/VerifyZ2Gauge.v"
)
if grep -En '^\s*(Axiom|Axioms|Parameter|Parameters|Conjecture|Admitted|admit)\b' "${GUARD_FILES[@]}"; then
  echo "FAIL: Forbidden declaration found in guarded verification files" >&2
  exit 1
fi
echo "PASS: Zero Axiom/Parameter/Conjecture/Admitted declarations across all ${#GUARD_FILES[@]} guarded files."

# The frozen Target 7 statement file may import ONLY the Coq standard library
# and the frozen verification/Challenge.v, and may contain no proof scripts.
if grep -En '^\s*(Require|From)\b' verification/ChallengeZ2Gauge.v \
     | grep -Ev '(From Coq Require Import|Require Import verification\.Challenge\.)'; then
  echo "FAIL: verification/ChallengeZ2Gauge.v imports a non-stdlib, non-Challenge module" >&2
  exit 1
fi
if grep -En '^\s*(Proof|Qed|Defined|Theorem|Lemma|Corollary|Hypothesis|Hypotheses|Variable|Variables|Context)\b' verification/ChallengeZ2Gauge.v; then
  echo "FAIL: verification/ChallengeZ2Gauge.v contains a proof script or a section assumption" >&2
  exit 1
fi
echo "PASS: verification/ChallengeZ2Gauge.v imports only the Coq stdlib + frozen Challenge.v and contains definitions only."

echo ""
echo "=== 3. Clean Wipe of Verification Cone Build Artifacts ==="
for src in "${CONE_SOURCES[@]}"; do
  base="${src%.v}"
  rm -f "${base}.vo" "${base}.vos" "${base}.vok" "${base}.glob" "$(dirname "$src")/.$(basename "$base").aux"
done
echo "Removed all prebuilt .vo/.glob/.aux files for the ${#CONE_SOURCES[@]}-file verification cone."

echo ""
echo "=== 4. Step 1: Compile Frozen Challenge Files FIRST (Stdlib-only Isolation) ==="
"$COQC" -R . '' -q verification/Challenge.v
echo "PASS: verification/Challenge.v compiled cleanly before any project module existed."
"$COQC" -R . '' -q verification/ChallengeZ2Gauge.v
echo "PASS: verification/ChallengeZ2Gauge.v compiled cleanly with only Challenge.vo present (no proof module existed)."

echo ""
echo "=== 5. Step 2: Compile Submitted Proof Cone & Verify Files ==="
for src in "rg/polymer_types.v" "rg/cluster_expansion.v" "rg/penrose_tree_bound.v" "rg/poly_exp_bound.v" "rg/tree_cut_bijection.v" "rg/kotecky_preiss.v" "rg/exp_series_limit.v" "rg/cluster_log_partition.v" "ym/geometry_frontier.v" "ym/lattice.v" "ym/lattice_4d_coordination.v" "ym/lattice_4d_kp.v" "verification/Verify.v" "rg/dup_clustering.v" "rg/polymer_representation.v" "rg/connected_subset_bound.v" "ym/z2_gauge_expansion.v" "ym/z2_gauge_clustering.v" "ym/z2_polymer_gas.v" "ym/z2_free_energy.v" "verification/VerifyZ2Gauge.v"; do
  echo "  coqc $src"
  "$COQC" -R . '' -q "$src"
done
echo "PASS: All submitted proof modules, verification/Verify.v and verification/VerifyZ2Gauge.v compiled cleanly."

echo ""
echo "=== 6. Step 2b: Check Target Types, Print Assumptions & Enforce Stdlib-Only Allowlist ==="
{
  "$COQC" -R . '' -q verification/CheckTypes.v 2>&1
  "$COQC" -R . '' -q verification/CheckTypesZ2Gauge.v 2>&1
} | tee "$RECEIPTS/types.log"
{
  "$COQC" -R . '' -q verification/CheckAxioms.v 2>&1
  "$COQC" -R . '' -q verification/CheckAxiomsZ2Gauge.v 2>&1
} | tee "$RECEIPTS/axioms.log"
python3 verification/check_allowlist.py "$RECEIPTS/axioms.log" | tee "$RECEIPTS/allowlist.log"

echo ""
echo "=== 7. Step 3: Independent Kernel Replay (coqchk) ==="
"$COQCHK" -R . '' verification.Challenge verification.Verify \
  verification.ChallengeZ2Gauge verification.VerifyZ2Gauge 2>&1 | tee "$RECEIPTS/coqchk.log"
if ! grep -q "Modules were successfully checked" "$RECEIPTS/coqchk.log"; then
  echo "FAIL: coqchk did not report 'Modules were successfully checked'" >&2
  exit 1
fi

echo ""
echo "=== ALL 3 VERIFICATION STEPS PASSED ==="
sha256sum verification/Challenge.vo verification/Verify.vo \
  verification/ChallengeZ2Gauge.vo verification/VerifyZ2Gauge.vo | tee "$RECEIPTS/artifacts.sha256"
