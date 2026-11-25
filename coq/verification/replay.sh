#!/usr/bin/env bash
# Reproducible 3-step verification replay for the frozen polymer decay challenge
# (Targets 1-6c, verification/Challenge.v), the frozen 4D Z_2 lattice gauge
# theory challenge (Targets 7a-7d, verification/ChallengeZ2Gauge.v) and the
# frozen Wilson-loop area-law challenge (Target 7e,
# verification/ChallengeZ2AreaLaw.v).
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

# Entries 1-16 are the byte-identical Targets 1-6c cone pinned by
# Zenodo 10.5281/zenodo.24507324; entries 1-27 (adding the Targets 7a-7d cone)
# are the byte-identical cone pinned by Zenodo 10.5281/zenodo.24512861; the
# last 8 entries are the Target 7e cone.
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
  "verification/ChallengeZ2AreaLaw.v"
  "rg/rooted_polymer_bound.v"
  "ym/z2_even_holonomy.v"
  "ym/z2_min_area.v"
  "ym/z2_area_law.v"
  "verification/VerifyZ2AreaLaw.v"
  "verification/CheckTypesZ2AreaLaw.v"
  "verification/CheckAxiomsZ2AreaLaw.v"
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
  "verification/ChallengeZ2AreaLaw.v"
  "rg/rooted_polymer_bound.v"
  "ym/z2_even_holonomy.v"
  "ym/z2_min_area.v"
  "ym/z2_area_law.v"
  "verification/VerifyZ2AreaLaw.v"
)
if grep -En '^\s*(Axiom|Axioms|Parameter|Parameters|Conjecture|Admitted|admit)\b' "${GUARD_FILES[@]}"; then
  echo "FAIL: Forbidden declaration found in guarded verification files" >&2
  exit 1
fi
echo "PASS: Zero Axiom/Parameter/Conjecture/Admitted declarations across all ${#GUARD_FILES[@]} guarded files."

# The frozen Target 7 statement files may import ONLY the Coq standard library
# and the frozen statement files that precede them (Challenge.v for
# ChallengeZ2Gauge.v; Challenge.v and ChallengeZ2Gauge.v for
# ChallengeZ2AreaLaw.v), and may contain no proof scripts.
if grep -En '^\s*(Require|From)\b' verification/ChallengeZ2Gauge.v \
     | grep -Ev '(From Coq Require Import|Require Import verification\.Challenge\.)'; then
  echo "FAIL: verification/ChallengeZ2Gauge.v imports a non-stdlib, non-Challenge module" >&2
  exit 1
fi
if grep -En '^\s*(Require|From)\b' verification/ChallengeZ2AreaLaw.v \
     | grep -Ev '(From Coq Require Import|Require Import verification\.Challenge\.|Require Import verification\.ChallengeZ2Gauge\.)'; then
  echo "FAIL: verification/ChallengeZ2AreaLaw.v imports a module other than the stdlib and the frozen challenge files" >&2
  exit 1
fi
for frozen in verification/ChallengeZ2Gauge.v verification/ChallengeZ2AreaLaw.v; do
  if grep -En '^\s*(Proof|Qed|Defined|Theorem|Lemma|Corollary|Hypothesis|Hypotheses|Variable|Variables|Context)\b' "$frozen"; then
    echo "FAIL: $frozen contains a proof script or a section assumption" >&2
    exit 1
  fi
done
echo "PASS: verification/ChallengeZ2Gauge.v imports only the Coq stdlib + frozen Challenge.v and contains definitions only."
echo "PASS: verification/ChallengeZ2AreaLaw.v imports only the Coq stdlib + frozen Challenge.v/ChallengeZ2Gauge.v and contains definitions only."

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
"$COQC" -R . '' -q verification/ChallengeZ2AreaLaw.v
echo "PASS: verification/ChallengeZ2AreaLaw.v compiled cleanly with only Challenge.vo and ChallengeZ2Gauge.vo present (no proof module existed)."

echo ""
echo "=== 5. Step 2: Compile Submitted Proof Cone & Verify Files ==="
for src in "rg/polymer_types.v" "rg/cluster_expansion.v" "rg/penrose_tree_bound.v" "rg/poly_exp_bound.v" "rg/tree_cut_bijection.v" "rg/kotecky_preiss.v" "rg/exp_series_limit.v" "rg/cluster_log_partition.v" "ym/geometry_frontier.v" "ym/lattice.v" "ym/lattice_4d_coordination.v" "ym/lattice_4d_kp.v" "verification/Verify.v" "rg/dup_clustering.v" "rg/polymer_representation.v" "rg/connected_subset_bound.v" "ym/z2_gauge_expansion.v" "ym/z2_gauge_clustering.v" "ym/z2_polymer_gas.v" "ym/z2_free_energy.v" "verification/VerifyZ2Gauge.v" "rg/rooted_polymer_bound.v" "ym/z2_even_holonomy.v" "ym/z2_min_area.v" "ym/z2_area_law.v" "verification/VerifyZ2AreaLaw.v"; do
  echo "  coqc $src"
  "$COQC" -R . '' -q "$src"
done
echo "PASS: All submitted proof modules, verification/Verify.v, verification/VerifyZ2Gauge.v and verification/VerifyZ2AreaLaw.v compiled cleanly."

echo ""
echo "=== 6. Step 2b: Check Target Types, Print Assumptions & Enforce Stdlib-Only Allowlist ==="
{
  "$COQC" -R . '' -q verification/CheckTypes.v 2>&1
  "$COQC" -R . '' -q verification/CheckTypesZ2Gauge.v 2>&1
  "$COQC" -R . '' -q verification/CheckTypesZ2AreaLaw.v 2>&1
} | tee "$RECEIPTS/types.log"
{
  "$COQC" -R . '' -q verification/CheckAxioms.v 2>&1
  "$COQC" -R . '' -q verification/CheckAxiomsZ2Gauge.v 2>&1
  "$COQC" -R . '' -q verification/CheckAxiomsZ2AreaLaw.v 2>&1
} | tee "$RECEIPTS/axioms.log"
python3 verification/check_allowlist.py "$RECEIPTS/axioms.log" | tee "$RECEIPTS/allowlist.log"

echo ""
echo "=== 7. Step 3: Independent Kernel Replay (coqchk) ==="
"$COQCHK" -R . '' verification.Challenge verification.Verify \
  verification.ChallengeZ2Gauge verification.VerifyZ2Gauge \
  verification.ChallengeZ2AreaLaw verification.VerifyZ2AreaLaw 2>&1 | tee "$RECEIPTS/coqchk.log"
if ! grep -q "Modules were successfully checked" "$RECEIPTS/coqchk.log"; then
  echo "FAIL: coqchk did not report 'Modules were successfully checked'" >&2
  exit 1
fi

echo ""
echo "=== ALL 3 VERIFICATION STEPS PASSED ==="
sha256sum verification/Challenge.vo verification/Verify.vo \
  verification/ChallengeZ2Gauge.vo verification/VerifyZ2Gauge.vo \
  verification/ChallengeZ2AreaLaw.vo verification/VerifyZ2AreaLaw.vo | tee "$RECEIPTS/artifacts.sha256"
