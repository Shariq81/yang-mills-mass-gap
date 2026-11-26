#!/usr/bin/env bash
# Reproducible 3-step verification replay for the frozen polymer decay challenge
# (Targets 1-6c, verification/Challenge.v), the frozen 4D Z_2 lattice gauge
# theory challenge (Targets 7a-7d, verification/ChallengeZ2Gauge.v), the
# frozen Wilson-loop area-law challenge (Target 7e,
# verification/ChallengeZ2AreaLaw.v), the frozen 4D SU(2) lattice gauge
# theory challenge (Targets 8a-8e, verification/ChallengeSU2Gauge.v), the
# frozen infinite-volume challenge for that theory (Targets 9a-9d,
# verification/ChallengeSU2InfiniteVolume.v), the frozen reflection
# positivity / mass gap challenge for it (Targets 10a-10f,
# verification/ChallengeSU2MassGap.v), the frozen Haar bi-invariance /
# gauge invariance challenge (Targets 11a-11c,
# verification/ChallengeSU2GaugeInvariance.v), the frozen transfer
# operator positivity challenge (Targets 12a-12d,
# verification/ChallengeSU2TransferPositivity.v) and the frozen
# Osterwalder-Schrader Hilbert space challenge (Target 13,
# verification/ChallengeSU2HilbertSpace.v).
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
# are the byte-identical cone pinned by Zenodo 10.5281/zenodo.24512861;
# entries 1-35 (adding the Target 7e cone) are the byte-identical cone of the
# 16-target release; entries 36-46 are the Target 8 cone, entries 47-54 are
# the Target 9 cone, entries 55-68 are the Target 10 cone, entries 69-79 are
# the Target 11 cone, entries 80-88 are the Target 12 cone and the last 6
# entries are the Target 13 cone.
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
  "verification/ChallengeSU2Gauge.v"
  "rg/product_measure.v"
  "ym/su2_algebra.v"
  "ym/su2_clustering.v"
  "ym/su2_area_law.v"
  "ym/su2_continuity.v"
  "ym/su2_haar_grid.v"
  "ym/su2_haar_limit.v"
  "verification/VerifySU2Gauge.v"
  "verification/CheckTypesSU2Gauge.v"
  "verification/CheckAxiomsSU2Gauge.v"
  "verification/ChallengeSU2InfiniteVolume.v"
  "rg/product_measure_perm.v"
  "ym/su2_volume.v"
  "ym/lattice_boxes.v"
  "ym/su2_infinite_volume.v"
  "verification/VerifySU2InfiniteVolume.v"
  "verification/CheckTypesSU2InfiniteVolume.v"
  "verification/CheckAxiomsSU2InfiniteVolume.v"
  "verification/ChallengeSU2MassGap.v"
  "rg/product_measure_relabel.v"
  "rg/cauchy_schwarz_gap.v"
  "ym/lattice_boxes_tail.v"
  "ym/su2_haar_grid_conj.v"
  "ym/lattice_symmetry.v"
  "ym/su2_covariance.v"
  "ym/su2_multi_clustering.v"
  "ym/su2_uniqueness.v"
  "ym/su2_reflection_positivity.v"
  "ym/su2_mass_gap.v"
  "verification/VerifySU2MassGap.v"
  "verification/CheckTypesSU2MassGap.v"
  "verification/CheckAxiomsSU2MassGap.v"
  "verification/ChallengeSU2GaugeInvariance.v"
  "ym/su2_haar_mean.v"
  "ym/su2_haar_moments.v"
  "ym/su2_haar_torus.v"
  "ym/su2_haar_orbit.v"
  "ym/su2_haar_poly.v"
  "ym/su2_haar_invariance.v"
  "ym/su2_gauge_invariance.v"
  "verification/VerifySU2GaugeInvariance.v"
  "verification/CheckTypesSU2GaugeInvariance.v"
  "verification/CheckAxiomsSU2GaugeInvariance.v"
  "verification/ChallengeSU2TransferPositivity.v"
  "rg/positive_kernel.v"
  "rg/product_measure_two_copy.v"
  "ym/su2_link_translate.v"
  "ym/lattice_link_reflection.v"
  "ym/su2_transfer_positivity.v"
  "verification/VerifySU2TransferPositivity.v"
  "verification/CheckTypesSU2TransferPositivity.v"
  "verification/CheckAxiomsSU2TransferPositivity.v"
  "verification/ChallengeSU2HilbertSpace.v"
  "rg/hilbert_completion.v"
  "ym/su2_os_hilbert_space.v"
  "verification/VerifySU2HilbertSpace.v"
  "verification/CheckTypesSU2HilbertSpace.v"
  "verification/CheckAxiomsSU2HilbertSpace.v"
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
  "verification/ChallengeSU2Gauge.v"
  "rg/product_measure.v"
  "ym/su2_algebra.v"
  "ym/su2_clustering.v"
  "ym/su2_area_law.v"
  "ym/su2_continuity.v"
  "ym/su2_haar_grid.v"
  "ym/su2_haar_limit.v"
  "verification/VerifySU2Gauge.v"
  "verification/ChallengeSU2InfiniteVolume.v"
  "rg/product_measure_perm.v"
  "ym/su2_volume.v"
  "ym/lattice_boxes.v"
  "ym/su2_infinite_volume.v"
  "verification/VerifySU2InfiniteVolume.v"
  "verification/ChallengeSU2MassGap.v"
  "rg/product_measure_relabel.v"
  "rg/cauchy_schwarz_gap.v"
  "ym/lattice_boxes_tail.v"
  "ym/su2_haar_grid_conj.v"
  "ym/lattice_symmetry.v"
  "ym/su2_covariance.v"
  "ym/su2_multi_clustering.v"
  "ym/su2_uniqueness.v"
  "ym/su2_reflection_positivity.v"
  "ym/su2_mass_gap.v"
  "verification/VerifySU2MassGap.v"
  "verification/ChallengeSU2GaugeInvariance.v"
  "ym/su2_haar_mean.v"
  "ym/su2_haar_moments.v"
  "ym/su2_haar_torus.v"
  "ym/su2_haar_orbit.v"
  "ym/su2_haar_poly.v"
  "ym/su2_haar_invariance.v"
  "ym/su2_gauge_invariance.v"
  "verification/VerifySU2GaugeInvariance.v"
  "verification/ChallengeSU2TransferPositivity.v"
  "rg/positive_kernel.v"
  "rg/product_measure_two_copy.v"
  "ym/su2_link_translate.v"
  "ym/lattice_link_reflection.v"
  "ym/su2_transfer_positivity.v"
  "verification/VerifySU2TransferPositivity.v"
  "verification/ChallengeSU2HilbertSpace.v"
  "rg/hilbert_completion.v"
  "ym/su2_os_hilbert_space.v"
  "verification/VerifySU2HilbertSpace.v"
)
if grep -En '^\s*(Axiom|Axioms|Parameter|Parameters|Conjecture|Admitted|admit)\b' "${GUARD_FILES[@]}"; then
  echo "FAIL: Forbidden declaration found in guarded verification files" >&2
  exit 1
fi
echo "PASS: Zero Axiom/Parameter/Conjecture/Admitted declarations across all ${#GUARD_FILES[@]} guarded files."

# The frozen Target 7, Target 8, Target 9 and Target 10 statement files may
# import ONLY the Coq standard library and the frozen statement files that
# precede them (Challenge.v for ChallengeZ2Gauge.v; Challenge.v and
# ChallengeZ2Gauge.v for ChallengeZ2AreaLaw.v; those three for
# ChallengeSU2Gauge.v; those four for ChallengeSU2InfiniteVolume.v; those
# five for ChallengeSU2MassGap.v and for ChallengeSU2GaugeInvariance.v; the
# first six for ChallengeSU2TransferPositivity.v and for
# ChallengeSU2HilbertSpace.v), and may contain no proof scripts.
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
if grep -En '^\s*(Require|From)\b' verification/ChallengeSU2Gauge.v \
     | grep -Ev '(From Coq Require Import|Require Import verification\.Challenge\.|Require Import verification\.ChallengeZ2Gauge\.|Require Import verification\.ChallengeZ2AreaLaw\.)'; then
  echo "FAIL: verification/ChallengeSU2Gauge.v imports a module other than the stdlib and the frozen challenge files" >&2
  exit 1
fi
if grep -En '^\s*(Require|From)\b' verification/ChallengeSU2InfiniteVolume.v \
     | grep -Ev '(From Coq Require Import|Require Import verification\.Challenge\.|Require Import verification\.ChallengeZ2Gauge\.|Require Import verification\.ChallengeZ2AreaLaw\.|Require Import verification\.ChallengeSU2Gauge\.)'; then
  echo "FAIL: verification/ChallengeSU2InfiniteVolume.v imports a module other than the stdlib and the frozen challenge files" >&2
  exit 1
fi
if grep -En '^\s*(Require|From)\b' verification/ChallengeSU2MassGap.v \
     | grep -Ev '(From Coq Require Import|Require Import verification\.Challenge\.|Require Import verification\.ChallengeZ2Gauge\.|Require Import verification\.ChallengeZ2AreaLaw\.|Require Import verification\.ChallengeSU2Gauge\.|Require Import verification\.ChallengeSU2InfiniteVolume\.)'; then
  echo "FAIL: verification/ChallengeSU2MassGap.v imports a module other than the stdlib and the frozen challenge files" >&2
  exit 1
fi
if grep -En '^\s*(Require|From)\b' verification/ChallengeSU2GaugeInvariance.v \
     | grep -Ev '(From Coq Require Import|Require Import verification\.Challenge\.|Require Import verification\.ChallengeZ2Gauge\.|Require Import verification\.ChallengeZ2AreaLaw\.|Require Import verification\.ChallengeSU2Gauge\.|Require Import verification\.ChallengeSU2InfiniteVolume\.)'; then
  echo "FAIL: verification/ChallengeSU2GaugeInvariance.v imports a module other than the stdlib and the frozen challenge files" >&2
  exit 1
fi
if grep -En '^\s*(Require|From)\b' verification/ChallengeSU2TransferPositivity.v \
     | grep -Ev '(From Coq Require Import|Require Import verification\.Challenge\.|Require Import verification\.ChallengeZ2Gauge\.|Require Import verification\.ChallengeZ2AreaLaw\.|Require Import verification\.ChallengeSU2Gauge\.|Require Import verification\.ChallengeSU2InfiniteVolume\.|Require Import verification\.ChallengeSU2MassGap\.)'; then
  echo "FAIL: verification/ChallengeSU2TransferPositivity.v imports a module other than the stdlib and the frozen challenge files" >&2
  exit 1
fi
if grep -En '^\s*(Require|From)\b' verification/ChallengeSU2HilbertSpace.v \
     | grep -Ev '(From Coq Require Import|Require Import verification\.Challenge\.|Require Import verification\.ChallengeZ2Gauge\.|Require Import verification\.ChallengeZ2AreaLaw\.|Require Import verification\.ChallengeSU2Gauge\.|Require Import verification\.ChallengeSU2InfiniteVolume\.|Require Import verification\.ChallengeSU2MassGap\.)'; then
  echo "FAIL: verification/ChallengeSU2HilbertSpace.v imports a module other than the stdlib and the frozen challenge files" >&2
  exit 1
fi
for frozen in verification/ChallengeZ2Gauge.v verification/ChallengeZ2AreaLaw.v verification/ChallengeSU2Gauge.v verification/ChallengeSU2InfiniteVolume.v verification/ChallengeSU2MassGap.v verification/ChallengeSU2GaugeInvariance.v verification/ChallengeSU2TransferPositivity.v verification/ChallengeSU2HilbertSpace.v; do
  if grep -En '^\s*(Proof|Qed|Defined|Theorem|Lemma|Corollary|Hypothesis|Hypotheses|Variable|Variables|Context)\b' "$frozen"; then
    echo "FAIL: $frozen contains a proof script or a section assumption" >&2
    exit 1
  fi
done
echo "PASS: verification/ChallengeZ2Gauge.v imports only the Coq stdlib + frozen Challenge.v and contains definitions only."
echo "PASS: verification/ChallengeZ2AreaLaw.v imports only the Coq stdlib + frozen Challenge.v/ChallengeZ2Gauge.v and contains definitions only."
echo "PASS: verification/ChallengeSU2Gauge.v imports only the Coq stdlib + frozen Challenge.v/ChallengeZ2Gauge.v/ChallengeZ2AreaLaw.v and contains definitions only."
echo "PASS: verification/ChallengeSU2InfiniteVolume.v imports only the Coq stdlib + the four frozen files above and contains definitions only."
echo "PASS: verification/ChallengeSU2MassGap.v imports only the Coq stdlib + the five frozen files above and contains definitions only."
echo "PASS: verification/ChallengeSU2GaugeInvariance.v imports only the Coq stdlib + the first five frozen files and contains definitions only."
echo "PASS: verification/ChallengeSU2TransferPositivity.v imports only the Coq stdlib + the first six frozen files and contains definitions only."
echo "PASS: verification/ChallengeSU2HilbertSpace.v imports only the Coq stdlib + the first six frozen files and contains definitions only."

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
"$COQC" -R . '' -q verification/ChallengeSU2Gauge.v
echo "PASS: verification/ChallengeSU2Gauge.v compiled cleanly with only Challenge.vo, ChallengeZ2Gauge.vo and ChallengeZ2AreaLaw.vo present (no proof module existed)."
"$COQC" -R . '' -q verification/ChallengeSU2InfiniteVolume.v
echo "PASS: verification/ChallengeSU2InfiniteVolume.v compiled cleanly with only the four earlier frozen .vo files present (no proof module existed)."
"$COQC" -R . '' -q verification/ChallengeSU2MassGap.v
echo "PASS: verification/ChallengeSU2MassGap.v compiled cleanly with only the five earlier frozen .vo files present (no proof module existed)."
"$COQC" -R . '' -q verification/ChallengeSU2GaugeInvariance.v
echo "PASS: verification/ChallengeSU2GaugeInvariance.v compiled cleanly with only the six earlier frozen .vo files present (no proof module existed)."
"$COQC" -R . '' -q verification/ChallengeSU2TransferPositivity.v
echo "PASS: verification/ChallengeSU2TransferPositivity.v compiled cleanly with only the seven earlier frozen .vo files present (no proof module existed)."
"$COQC" -R . '' -q verification/ChallengeSU2HilbertSpace.v
echo "PASS: verification/ChallengeSU2HilbertSpace.v compiled cleanly with only the eight earlier frozen .vo files present (no proof module existed)."

echo ""
echo "=== 5. Step 2: Compile Submitted Proof Cone & Verify Files ==="
for src in "rg/polymer_types.v" "rg/cluster_expansion.v" "rg/penrose_tree_bound.v" "rg/poly_exp_bound.v" "rg/tree_cut_bijection.v" "rg/kotecky_preiss.v" "rg/exp_series_limit.v" "rg/cluster_log_partition.v" "ym/geometry_frontier.v" "ym/lattice.v" "ym/lattice_4d_coordination.v" "ym/lattice_4d_kp.v" "verification/Verify.v" "rg/dup_clustering.v" "rg/polymer_representation.v" "rg/connected_subset_bound.v" "ym/z2_gauge_expansion.v" "ym/z2_gauge_clustering.v" "ym/z2_polymer_gas.v" "ym/z2_free_energy.v" "verification/VerifyZ2Gauge.v" "rg/rooted_polymer_bound.v" "ym/z2_even_holonomy.v" "ym/z2_min_area.v" "ym/z2_area_law.v" "verification/VerifyZ2AreaLaw.v" "rg/product_measure.v" "ym/su2_algebra.v" "ym/su2_clustering.v" "ym/su2_area_law.v" "ym/su2_continuity.v" "ym/su2_haar_grid.v" "ym/su2_haar_limit.v" "verification/VerifySU2Gauge.v" "rg/product_measure_perm.v" "ym/su2_volume.v" "ym/lattice_boxes.v" "ym/su2_infinite_volume.v" "verification/VerifySU2InfiniteVolume.v" "rg/product_measure_relabel.v" "rg/cauchy_schwarz_gap.v" "ym/lattice_boxes_tail.v" "ym/su2_haar_grid_conj.v" "ym/lattice_symmetry.v" "ym/su2_covariance.v" "ym/su2_multi_clustering.v" "ym/su2_uniqueness.v" "ym/su2_reflection_positivity.v" "ym/su2_mass_gap.v" "verification/VerifySU2MassGap.v" "ym/su2_haar_mean.v" "ym/su2_haar_moments.v" "ym/su2_haar_torus.v" "ym/su2_haar_orbit.v" "ym/su2_haar_poly.v" "ym/su2_haar_invariance.v" "ym/su2_gauge_invariance.v" "verification/VerifySU2GaugeInvariance.v" "rg/positive_kernel.v" "rg/product_measure_two_copy.v" "ym/su2_link_translate.v" "ym/lattice_link_reflection.v" "ym/su2_transfer_positivity.v" "verification/VerifySU2TransferPositivity.v" "rg/hilbert_completion.v" "ym/su2_os_hilbert_space.v" "verification/VerifySU2HilbertSpace.v"; do
  echo "  coqc $src"
  "$COQC" -R . '' -q "$src"
done
echo "PASS: All submitted proof modules, verification/Verify.v, verification/VerifyZ2Gauge.v, verification/VerifyZ2AreaLaw.v, verification/VerifySU2Gauge.v, verification/VerifySU2InfiniteVolume.v, verification/VerifySU2MassGap.v, verification/VerifySU2GaugeInvariance.v, verification/VerifySU2TransferPositivity.v and verification/VerifySU2HilbertSpace.v compiled cleanly."

echo ""
echo "=== 6. Step 2b: Check Target Types, Print Assumptions & Enforce Stdlib-Only Allowlist ==="
{
  "$COQC" -R . '' -q verification/CheckTypes.v 2>&1
  "$COQC" -R . '' -q verification/CheckTypesZ2Gauge.v 2>&1
  "$COQC" -R . '' -q verification/CheckTypesZ2AreaLaw.v 2>&1
  "$COQC" -R . '' -q verification/CheckTypesSU2Gauge.v 2>&1
  "$COQC" -R . '' -q verification/CheckTypesSU2InfiniteVolume.v 2>&1
  "$COQC" -R . '' -q verification/CheckTypesSU2MassGap.v 2>&1
  "$COQC" -R . '' -q verification/CheckTypesSU2GaugeInvariance.v 2>&1
  "$COQC" -R . '' -q verification/CheckTypesSU2TransferPositivity.v 2>&1
  "$COQC" -R . '' -q verification/CheckTypesSU2HilbertSpace.v 2>&1
} | tee "$RECEIPTS/types.log"
{
  "$COQC" -R . '' -q verification/CheckAxioms.v 2>&1
  "$COQC" -R . '' -q verification/CheckAxiomsZ2Gauge.v 2>&1
  "$COQC" -R . '' -q verification/CheckAxiomsZ2AreaLaw.v 2>&1
  "$COQC" -R . '' -q verification/CheckAxiomsSU2Gauge.v 2>&1
  "$COQC" -R . '' -q verification/CheckAxiomsSU2InfiniteVolume.v 2>&1
  "$COQC" -R . '' -q verification/CheckAxiomsSU2MassGap.v 2>&1
  "$COQC" -R . '' -q verification/CheckAxiomsSU2GaugeInvariance.v 2>&1
  "$COQC" -R . '' -q verification/CheckAxiomsSU2TransferPositivity.v 2>&1
  "$COQC" -R . '' -q verification/CheckAxiomsSU2HilbertSpace.v 2>&1
} | tee "$RECEIPTS/axioms.log"
python3 verification/check_allowlist.py "$RECEIPTS/axioms.log" | tee "$RECEIPTS/allowlist.log"

echo ""
echo "=== 7. Step 3: Independent Kernel Replay (coqchk) ==="
"$COQCHK" -R . '' verification.Challenge verification.Verify \
  verification.ChallengeZ2Gauge verification.VerifyZ2Gauge \
  verification.ChallengeZ2AreaLaw verification.VerifyZ2AreaLaw \
  verification.ChallengeSU2Gauge verification.VerifySU2Gauge \
  verification.ChallengeSU2InfiniteVolume verification.VerifySU2InfiniteVolume \
  verification.ChallengeSU2MassGap verification.VerifySU2MassGap \
  verification.ChallengeSU2GaugeInvariance verification.VerifySU2GaugeInvariance \
  verification.ChallengeSU2TransferPositivity verification.VerifySU2TransferPositivity \
  verification.ChallengeSU2HilbertSpace verification.VerifySU2HilbertSpace 2>&1 | tee "$RECEIPTS/coqchk.log"
if ! grep -q "Modules were successfully checked" "$RECEIPTS/coqchk.log"; then
  echo "FAIL: coqchk did not report 'Modules were successfully checked'" >&2
  exit 1
fi

echo ""
echo "=== ALL 3 VERIFICATION STEPS PASSED ==="
sha256sum verification/Challenge.vo verification/Verify.vo \
  verification/ChallengeZ2Gauge.vo verification/VerifyZ2Gauge.vo \
  verification/ChallengeZ2AreaLaw.vo verification/VerifyZ2AreaLaw.vo \
  verification/ChallengeSU2Gauge.vo verification/VerifySU2Gauge.vo \
  verification/ChallengeSU2InfiniteVolume.vo verification/VerifySU2InfiniteVolume.vo \
  verification/ChallengeSU2MassGap.vo verification/VerifySU2MassGap.vo \
  verification/ChallengeSU2GaugeInvariance.vo verification/VerifySU2GaugeInvariance.vo \
  verification/ChallengeSU2TransferPositivity.vo verification/VerifySU2TransferPositivity.vo \
  verification/ChallengeSU2HilbertSpace.vo verification/VerifySU2HilbertSpace.vo | tee "$RECEIPTS/artifacts.sha256"
