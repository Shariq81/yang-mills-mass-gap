#!/usr/bin/env python3
"""Replay the pinned verification cone on a local Coq 8.18 installation."""

import argparse
from hashlib import sha256
from pathlib import Path
import re
import runpy
import subprocess
from tempfile import TemporaryDirectory


ROOT = Path(__file__).resolve().parent
COQ = ROOT / "coq"
VERIFICATION = COQ / "verification"
RECEIPTS = VERIFICATION / "receipts"

# Frozen statement files, compiled first and in this order, before any proof
# module exists: Challenge.v imports only the Coq standard library, and
# ChallengeZ2Gauge.v imports only the Coq standard library and Challenge.v.
FROZEN = [Path("verification/Challenge.v"), Path("verification/ChallengeZ2Gauge.v")]
# 16 files of Targets 1-6c (Zenodo 10.5281/zenodo.24507324) + 11 files of Target 7.
EXPECTED_SOURCES = 27
CHECKED_MODULES = [
    "verification.Challenge",
    "verification.Verify",
    "verification.ChallengeZ2Gauge",
    "verification.VerifyZ2Gauge",
]


def run(args, cwd):
    result = subprocess.run(
        args, cwd=cwd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT
    )
    output = result.stdout.decode("utf-8", errors="replace")
    if result.returncode:
        raise SystemExit(f"{args!r} exited {result.returncode}\n{output}")
    return output.replace("\r\n", "\n")


def main():
    options = argparse.ArgumentParser(description=__doc__)
    options.add_argument("--coqc", default="coqc")
    options.add_argument("--coqchk", default="coqchk")
    args = options.parse_args()
    version = run([args.coqc, "--version"], ROOT)
    check_version = run([args.coqchk, "--version"], ROOT)
    for report in (version, check_version):
        if not re.search(r"\b8\.18\.0\b", report):
            raise SystemExit(f"Expected Coq 8.18.0. Reported: {report.strip()}")
        print(report.strip(), flush=True)

    parser = runpy.run_path(str(VERIFICATION / "check_allowlist.py"))
    parser["self_test"]()
    expected = parser["EXPECTED_THEOREMS"]
    manifest = (RECEIPTS / "sources.sha256").read_text(encoding="utf-8")
    sources = []
    for entry in manifest.splitlines():
        digest, name = entry.split(maxsplit=1)
        path = Path(name)
        if path.is_absolute() or ".." in path.parts or path.suffix != ".v":
            raise SystemExit(f"Invalid manifest path: {name}")
        data = (COQ / path).read_bytes()
        if sha256(data).hexdigest() != digest:
            raise SystemExit(f"Source hash mismatch: {name}")
        sources.append((path, data))
    listed = [path for path, _ in sources]
    if len(sources) != EXPECTED_SOURCES or listed[0] != FROZEN[0]:
        raise SystemExit(
            f"Expected the {EXPECTED_SOURCES}-file cone with Challenge.v first."
        )
    if any(frozen not in listed for frozen in FROZEN):
        raise SystemExit("A frozen challenge file is missing from the manifest.")

    with TemporaryDirectory(prefix="coq-plaquette-replay-") as temporary:
        work = Path(temporary).resolve()
        for path, data in sources:
            target = work / path
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(data)
        # The frozen statement files first (isolation), then the manifest order.
        order = FROZEN + [path for path in listed if path not in FROZEN]
        types_output = ""
        axioms_output = ""
        for path in order:
            print(f"Compiling {path.as_posix()}", flush=True)
            output = run([args.coqc, "-R", ".", "", "-q", str(path)], work)
            if path.name.startswith("CheckTypes"):
                types_output += output
            if path.name.startswith("CheckAxioms"):
                axioms_output += output
        if not all(name in types_output for name in expected):
            raise SystemExit("Missing frozen target in the CheckTypes output.")
        ok, error, details = parser["evaluate_log"](axioms_output)
        if not ok:
            raise SystemExit(f"Axiom gate failed: {error or details}")
        archived = (RECEIPTS / "axioms.log").read_text(encoding="utf-8")
        blocks = parser["parse_assumptions_blocks"]
        if blocks(axioms_output) != blocks(archived):
            raise SystemExit("Axiom sets differ from the archived WSL receipt.")
        for theorem, axioms, _ in details:
            print(f"{theorem}: {len(axioms)} standard-library axioms", flush=True)
        print("Running coqchk on the frozen challenges and verified proofs", flush=True)
        checked = run([args.coqchk, "-R", ".", ""] + CHECKED_MODULES, work)
        if "Modules were successfully checked" not in checked:
            raise SystemExit("The usual coqchk success message is missing.")
        print(
            f"All {len(expected)} targets matched the archived receipts. "
            "Modules were successfully checked."
        )


if __name__ == "__main__":
    main()
