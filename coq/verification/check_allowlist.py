#!/usr/bin/env python3
"""
Strict Coq stdlib-only axiom allowlist gate for `verification/CheckAxioms.v`.

Because `CheckAxioms.v` emits ONLY `Print Assumptions` output (type checks live
in `CheckTypes.v`), this parser NEVER ignores `Verify.*` or `Challenge.*`
identifiers inside an `Axioms:` block. Any unindented line inside an `Axioms:`
block that is not a new block header (`Axioms:` / `Closed under the global context`)
is parsed as an axiom name and MUST belong to `ALLOWLIST`.
"""
import re
import sys

ALLOWLIST = {
    "Classical_Prop.classic",
    "ClassicalEpsilon.constructive_indefinite_description",
    "ClassicalDedekindReals.sig_not_dec",
    "ClassicalDedekindReals.sig_forall_dec",
    "FunctionalExtensionality.functional_extensionality_dep",
}

EXPECTED_THEOREMS = [
    "Verify.verified_connects_implies_dist_bound",
    "Verify.verified_conditional_exponential_decay",
    "Verify.verified_master_conditional_statement",
    "Verify.verified_lattice4D_exact21",
    "Verify.verified_lattice4D_coordination24",
    "Verify.verified_kotecky_preiss_pinned_bound",
    "Verify.verified_kotecky_preiss_exponential_decay",
    "Verify.verified_lattice4D_kp_exponential_decay",
    "Verify.verified_kotecky_preiss_log_partition_fn",
    "Verify.verified_kotecky_preiss_log_ratio_decay",
    "Verify.verified_lattice4D_partition_fn_decay",
]


def parse_assumptions_blocks(text: str):
    """Return list of axiom-name sets, one per Print Assumptions output block."""
    blocks = []
    lines = text.splitlines()
    i = 0
    while i < len(lines):
        line = lines[i].strip()
        if line == "Closed under the global context":
            blocks.append(set())
            i += 1
        elif line == "Axioms:":
            axioms = set()
            i += 1
            while i < len(lines):
                raw = lines[i]
                stripped = raw.strip()
                if not stripped:
                    i += 1
                    continue
                if stripped == "Axioms:" or stripped == "Closed under the global context":
                    break
                # Every unindented line inside an Axioms block is an axiom declaration:
                # `<Qualified.Name> : <Type>` or `<Qualified.Name>` (with type on next indented line).
                if not raw.startswith(" ") and not raw.startswith("\t"):
                    m = re.match(r"^([A-Za-z0-9_'.]+)\b", stripped)
                    if not m:
                        raise ValueError(f"Unparseable axiom line: {raw!r}")
                    axioms.add(m.group(1))
                i += 1
            blocks.append(axioms)
        elif not line:
            i += 1
        else:
            raise ValueError(f"Unexpected non-axiom output line in axioms.log: {lines[i]!r}")
    return blocks


def evaluate_log(text: str):
    blocks = parse_assumptions_blocks(text)
    if len(blocks) != len(EXPECTED_THEOREMS):
        return False, f"expected {len(EXPECTED_THEOREMS)} Print Assumptions blocks, found {len(blocks)}", []
    details = []
    ok = True
    for thm, axs in zip(EXPECTED_THEOREMS, blocks):
        illegal = sorted(axs - ALLOWLIST)
        if illegal:
            ok = False
        details.append((thm, sorted(axs), illegal))
    return ok, "", details


def self_test():
    """Negative tests ensuring Verify.* / Challenge.* / project axioms are NEVER missed."""
    clean_block = "Axioms:\nClassical_Prop.classic : forall P : Prop, P \\/ ~ P\n"
    closed_block = "Closed under the global context\n"
    for bad_name in ["Verify.bogus", "Challenge.hidden_axiom", "small_field.beta", "plaq_wellformed"]:
        fake = (
            clean_block
            + f"Axioms:\n{bad_name} : False\nClassical_Prop.classic : forall P : Prop, P \\/ ~ P\n"
            + clean_block
            + closed_block
            + clean_block * (len(EXPECTED_THEOREMS) - 4)
        )
        ok, _, details = evaluate_log(fake)
        assert not ok, f"Self-test FAILED: parser accepted {bad_name}!"
        assert bad_name in details[1][2], f"Self-test FAILED: {bad_name} not flagged as illegal!"

    # Also test multiline axiom where `:` is on the next indented line
    fake_multi = (
        clean_block
        + "Axioms:\nVerify.multiline_axiom\n  : forall P : Prop, P\n"
        + clean_block
        + closed_block
        + clean_block * (len(EXPECTED_THEOREMS) - 4)
    )
    ok, _, details = evaluate_log(fake_multi)
    assert not ok and "Verify.multiline_axiom" in details[1][2], (
        "Self-test FAILED: multiline Verify.* axiom not caught!"
    )
    print("PASS: allowlist parser self-test caught Verify.*, Challenge.*, project, and multiline axioms.")


def main():
    if len(sys.argv) == 2 and sys.argv[1] == "--self-test":
        self_test()
        return

    if len(sys.argv) != 2:
        print(f"Usage: {sys.argv[0]} <axioms.log | --self-test>", file=sys.stderr)
        sys.exit(2)

    self_test()
    text = open(sys.argv[1], encoding="utf-8", errors="replace").read()
    try:
        ok, err, details = evaluate_log(text)
    except ValueError as e:
        print(f"FAIL: {e}", file=sys.stderr)
        sys.exit(1)

    if err:
        print(f"FAIL: {err}", file=sys.stderr)
        sys.exit(1)

    print("=== Axiom Allowlist Gate ===")
    print(f"Permitted Coq stdlib axioms ({len(ALLOWLIST)}): {sorted(ALLOWLIST)}")
    for thm, axs, illegal in details:
        if illegal:
            print(f"FAIL {thm}: DISALLOWED axioms detected: {illegal}", file=sys.stderr)
        else:
            print(f"PASS {thm}: {len(axs)} stdlib axioms ({axs}), 0 project axioms")

    if not ok:
        sys.exit(1)
    print("ALL TARGETS PASSED ALLOWLIST GATE (0 project axioms, 0 admitted lemmas).")


if __name__ == "__main__":
    main()
