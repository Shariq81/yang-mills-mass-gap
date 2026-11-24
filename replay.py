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
    if len(sources) != 16 or sources[0][0] != Path("verification/Challenge.v"):
        raise SystemExit("Expected the sixteen-file cone with Challenge.v first.")

    with TemporaryDirectory(prefix="coq-plaquette-replay-") as temporary:
        work = Path(temporary).resolve()
        for path, data in sources:
            target = work / path
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(data)
        for path, _ in sources:
            print(f"Compiling {path.as_posix()}", flush=True)
            output = run([args.coqc, "-R", ".", "", "-q", str(path)], work)
            if path.name == "CheckTypes.v":
                if not all(name in output for name in parser["EXPECTED_THEOREMS"]):
                    raise SystemExit("Missing frozen target in CheckTypes output.")
        if sources[-1][0].name != "CheckAxioms.v":
            raise SystemExit("Expected CheckAxioms.v last in the source manifest.")
        ok, error, details = parser["evaluate_log"](output)
        if not ok:
            raise SystemExit(f"Axiom gate failed: {error or details}")
        archived = (RECEIPTS / "axioms.log").read_text(encoding="utf-8")
        if parser["parse_assumptions_blocks"](output) != parser["parse_assumptions_blocks"](archived):
            raise SystemExit("Axiom sets differ from the archived WSL receipt.")
        for theorem, axioms, _ in details:
            print(f"{theorem}: {len(axioms)} standard-library axioms", flush=True)
        print("Running coqchk on the frozen challenge and verified proofs", flush=True)
        checked = run([args.coqchk, "-R", ".", "", "verification.Challenge", "verification.Verify"], work)
        if "Modules were successfully checked" not in checked:
            raise SystemExit("The usual coqchk success message is missing.")
        print("All 11 targets matched the archived receipts. Modules were successfully checked.")


if __name__ == "__main__":
    main()
