#!/usr/bin/env bash
# Reproducible 3-step verification replay for the frozen polymer decay challenge.
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
)

sha256sum "${CONE_SOURCES[@]}" | tee "$RECEIPTS/sources.sha256"

echo ""
echo "=== 2. Static Guard on Frozen Challenge.v, New Zero-Axiom Proofs & Verify.v ==="
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
)
if grep -En '^\s*(Axiom|Axioms|Parameter|Parameters|Conjecture|Admitted|admit)\b' "${GUARD_FILES[@]}"; then
  echo "FAIL: Forbidden declaration found in guarded verification files" >&2
  exit 1
fi
echo "PASS: Zero Axiom/Parameter/Conjecture/Admitted declarations across all ${#GUARD_FILES[@]} guarded files."

echo ""
echo "=== 3. Clean Wipe of Verification Cone Build Artifacts ==="
for src in "${CONE_SOURCES[@]}"; do
  base="${src%.v}"
  rm -f "${base}.vo" "${base}.vos" "${base}.vok" "${base}.glob" "$(dirname "$src")/.$(basename "$base").aux"
done
echo "Removed all prebuilt .vo/.glob/.aux files for the ${#CONE_SOURCES[@]}-file verification cone."

echo ""
echo "=== 4. Step 1: Compile Frozen Challenge.v FIRST (Stdlib-only Isolation) ==="
"$COQC" -R . '' -q verification/Challenge.v
echo "PASS: verification/Challenge.v compiled cleanly before any project module existed."

echo ""
echo "=== 5. Step 2: Compile Submitted Proof Cone & Verify.v ==="
for src in "rg/polymer_types.v" "rg/cluster_expansion.v" "rg/penrose_tree_bound.v" "rg/poly_exp_bound.v" "rg/tree_cut_bijection.v" "rg/kotecky_preiss.v" "rg/exp_series_limit.v" "rg/cluster_log_partition.v" "ym/geometry_frontier.v" "ym/lattice.v" "ym/lattice_4d_coordination.v" "ym/lattice_4d_kp.v" "verification/Verify.v"; do
  echo "  coqc $src"
  "$COQC" -R . '' -q "$src"
done
echo "PASS: All submitted proof modules and verification/Verify.v compiled cleanly."

echo ""
echo "=== 6. Step 2b: Check Target Types, Print Assumptions & Enforce Stdlib-Only Allowlist ==="
"$COQC" -R . '' -q verification/CheckTypes.v 2>&1 | tee "$RECEIPTS/types.log"
"$COQC" -R . '' -q verification/CheckAxioms.v 2>&1 | tee "$RECEIPTS/axioms.log"
python3 verification/check_allowlist.py "$RECEIPTS/axioms.log" | tee "$RECEIPTS/allowlist.log"

echo ""
echo "=== 7. Step 3: Independent Kernel Replay (coqchk) ==="
"$COQCHK" -R . '' verification.Challenge verification.Verify 2>&1 | tee "$RECEIPTS/coqchk.log"
if ! grep -q "Modules were successfully checked" "$RECEIPTS/coqchk.log"; then
  echo "FAIL: coqchk did not report 'Modules were successfully checked'" >&2
  exit 1
fi

echo ""
echo "=== ALL 3 VERIFICATION STEPS PASSED ==="
sha256sum verification/Challenge.vo verification/Verify.vo | tee "$RECEIPTS/artifacts.sha256"
