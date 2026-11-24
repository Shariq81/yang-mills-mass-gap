# Verified Cluster Expansion and Exponential Decay for a 4D Plaquette Polymer Gas (Coq 8.18.0)

[![Coq 8.18.0](https://img.shields.io/badge/Coq-8.18.0-blue)](https://coq.inria.fr/)
[![Zenodo DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.24507324.svg)](https://doi.org/10.5281/zenodo.24507324)
[![Concept DOI](https://img.shields.io/badge/Zenodo%20Concept%20DOI-10.5281%2Fzenodo.18675090-blue)](https://doi.org/10.5281/zenodo.18675090)
[![License: MIT](https://img.shields.io/badge/License-MIT-green.svg)](LICENSE)

> **Honest Scope:** The certified verification cone in [`coq/verification/`](coq/verification/README.md) proves **11 frozen Coq 8.18.0 propositions** with **0 project axioms**, **0 admitted lemmas**, and independent `coqchk` kernel verification: Penrose's (1967) BFS tree-graph inequality, the genuine ordered-tuple $1/n!$ Kotecký–Preiss (1986) cluster expansion theorem, an exact **0-axiom** 21-neighbor enumeration of canonical unit plaquettes on $\mathbb{Z}^4$, absolute convergence of the Mayer/Ursell series to $\ln Z_\Lambda$ for the actual finite-volume compatible-subset partition function $Z_\Lambda$, and uniform exponential decay of the exact partition-function log ratio for the finite-volume constant-activity ($\beta > 85$) $\mathbb{Z}^4$ plaquette polymer gas.  
> It does **not** certify 4D continuum Yang–Mills theory, Wilson-action Haar measure integrals, reflection positivity, Osterwalder–Schrader reconstruction, or the Clay Millennium Prize Problem.

---

## Quick Verification Replay (Zero Trust Required)

Install Python 3 and **Coq 8.18.0** (`coqc` and `coqchk` on `PATH`), then run from the repository root:

```bash
python3 replay.py
```

*(Pass `--coqc /path/to/coqc --coqchk /path/to/coqchk` if they are not on `PATH`.)*

`replay.py` verifies the SHA-256 checksums of all 16 pinned `.v` sources against [`coq/verification/receipts/sources.sha256`](coq/verification/receipts/sources.sha256), compiles them from scratch in a clean temporary directory (`Challenge.v` first in stdlib-only isolation), typechecks all 11 frozen targets, runs the self-tested standard-library-only axiom allowlist gate, checks exact equality against the archived `Print Assumptions` receipts, and runs `coqchk`.

On Linux or WSL2, you can also run the full clean-wipe shell harness:

```bash
bash coq/verification/replay.sh
```

---

## Certified Frozen Targets (11 Theorems, 16 Source Files)

All 11 target propositions are declared in [`coq/verification/Challenge.v`](coq/verification/Challenge.v) importing **only the Coq 8.18.0 standard library** (zero project imports, zero `Axiom`/`Parameter`/`Admitted`), and verified in [`coq/verification/Verify.v`](coq/verification/Verify.v).

| Target | Frozen Proposition (`Challenge.v`) | Result Certified | Axioms |
|---|---|---|---|
| **1** | `Challenge_ConnectsImpliesDistBound` | Constructive BFS + simple-path loop erasure: connecting cluster size bounds polymer distance | 4 stdlib, **0 project** |
| **2** | `Challenge_ConditionalExponentialDecay` | Clean conditional cluster-to-decay implication with explicit pinned-cluster hypothesis | 5 stdlib, **0 project** |
| **3** | `Challenge_MasterConditionalStatement` | Zero-`Parameter` hoisting of the legacy conditional mass-gap statement | 5 stdlib, **0 project** |
| **4a** | `Challenge_Lattice4D_Exact21` | Constructive, duplicate-free, sound & complete enumeration of all **21** edge-overlapping canonical unit plaquettes in $\mathbb{Z}^4$ (including self) | **0 axioms total** (`Closed under the global context`) |
| **4b** | `Challenge_Lattice4D_Coordination24` | Real-valued $\le 24$ coordination bound on $\mathbb{Z}^4$ | 2 stdlib, **0 project** |
| **5a** | `Challenge_KoteckyPreiss_PinnedBound` | Genuine $1/n!$ ordered-tuple Ursell root-pinned ($\le e^{a(p_0)}$) and 1-pinned overlap ($\le a(p_0)$) bounds via Penrose BFS tree-graph inequality (**0 analytic assumptions**) | 4 stdlib, **0 project** |
| **5b** | `Challenge_KoteckyPreiss_ExponentialDecay` | Unconditional exponential decay of the truncated Ursell two-point correlator from single-polymer KP alone | 4 stdlib, **0 project** |
| **5c** | `Challenge_Lattice4D_KP_ExponentialDecay` | Concrete $\mathbb{Z}^4$ plaquette Ursell correlator decay at $\beta > 85$, $w(p) = e^{-\beta/10}$ (**0 analytic or combinatorial hypotheses**) | 4 stdlib, **0 project** |
| **6a** | `Challenge_KoteckyPreiss_LogPartitionFn` | Positivity $Z_\Lambda > 0$ of the actual compatible-subset partition function, absolute convergence of the $1/n!$ Mayer/Ursell series, and `Un_cv` convergence to $\ln Z_\Lambda$ | 4 stdlib, **0 project** |
| **6b** | `Challenge_KoteckyPreiss_LogRatioDecay` | Four-volume inclusion-exclusion ($Z_\Lambda, Z_{\Lambda_1}, Z_{\Lambda_2}, Z_{\Lambda_{12}} > 0$), convergence $G_{\Lambda,N}(p_1,p_2) \to \ln\frac{Z_\Lambda Z_{\Lambda_{12}}}{Z_{\Lambda_1} Z_{\Lambda_2}}$, and uniform exponential decay of the exact log ratio | 4 stdlib, **0 project** |
| **6c** | `Challenge_Lattice4D_PartitionFn_Decay` | Concrete $\mathbb{Z}^4$ ($\beta > 85$, any finite `NoDup` volume $\Lambda$) partition-function positivity, $\ln Z_\Lambda$ convergence, and $\left\|\ln\frac{Z_\Lambda Z_{\Lambda_{12}}}{Z_{\Lambda_1} Z_{\Lambda_2}}\right\| \le e \cdot \exp\!\left(-\frac{1}{2}\|s(p_1)-s(p_2)\|_1\right)$ (**0 analytic or combinatorial hypotheses**) | 4 stdlib, **0 project** |

Permitted Coq 8.18.0 standard-library allowlist (5 axioms max): `Classical_Prop.classic`, `ClassicalEpsilon.constructive_indefinite_description`, `ClassicalDedekindReals.sig_not_dec`, `ClassicalDedekindReals.sig_forall_dec`, `FunctionalExtensionality.functional_extensionality_dep`.

Full technical documentation, source hashes, and cross-platform replay details live in [`coq/verification/README.md`](coq/verification/README.md).

---

## Verification Cone Layout

```text
replay.py                              # Portable cross-platform Coq 8.18.0 verifier
coq/
├── verification/
│   ├── Challenge.v                    # 11 frozen target statements (Coq stdlib ONLY)
│   ├── Verify.v                       # Proof assignment & bridges (0 axioms/admitted)
│   ├── CheckTypes.v                   # Exact frozen type verification
│   ├── CheckAxioms.v                  # Pure Print Assumptions driver
│   ├── check_allowlist.py             # Self-tested stdlib-only axiom gate
│   ├── replay.sh                      # Clean-wipe WSL/Linux 3-step verifier
│   ├── README.md                      # Detailed harness documentation
│   └── receipts/                      # Machine-generated hashes, axiom logs, coqchk.log
├── rg/
│   ├── penrose_tree_bound.v           # Genuine Ursell function & Penrose (1967) BFS bound
│   ├── poly_exp_bound.v               # Finite-polynomial exponential generating function bound
│   ├── tree_cut_bijection.v           # Vertex-1 spanning-tree edge-cut bijection
│   ├── kotecky_preiss.v               # 1/n! ordered-tuple Kotecký–Preiss theorem
│   ├── exp_series_limit.v             # Real exponential-series convergence theorem
│   ├── cluster_log_partition.v        # Partition function Z_Lambda, ln Z_Lambda, log-ratio decay
│   ├── polymer_types.v                # Legacy abstract polymer interfaces (Targets 1–3)
│   └── cluster_expansion.v            # Legacy conditional cluster expansion (Targets 2–3)
└── ym/
    ├── lattice_4d_coordination.v      # 0-axiom exact 21-neighbor Z^4 plaquette enumeration
    ├── lattice_4d_kp.v                # Concrete Z^4 KP & partition-function decay (5c, 6c)
    ├── lattice.v                      # 4D lattice geometry definitions
    └── geometry_frontier.v            # Constructive BFS simple-path distance bound (Target 1)
```

---

## Historical Archive Note

Older exploratory files from the February 2026 `v1.x`–`v2.1.0` releases (`coq/ym/os_axioms_complete.v`, `coq/ym/rp_to_transfer.v`, `main.tex`, etc., archived at [`10.5281/zenodo.18726858`](https://doi.org/10.5281/zenodo.18726858)) remain in the repository for historical provenance. They are **outside** the 16-file certified verification cone and contain legacy project hypotheses and unverified stubs. All current verified claims are restricted strictly to the 11 frozen targets certified by `replay.py` / `coq/verification/replay.sh`.

---

## Citation

If you use or build on this formalization, please cite the Zenodo release:

```bibtex
@software{farooqui_2026_plaquette_cluster,
  author       = {Farooqui, Shariq},
  title        = {Verified Cluster Expansion and Exponential Decay for a Four-Dimensional Plaquette Polymer Gas},
  year         = 2026,
  month        = nov,
  publisher    = {Zenodo},
  version      = {verification-2026-11-24},
  doi          = {10.5281/zenodo.24507324},
  url          = {https://doi.org/10.5281/zenodo.24507324}
}
```

Concept DOI (all versions): [`10.5281/zenodo.18675090`](https://doi.org/10.5281/zenodo.18675090).

## License

MIT — see [LICENSE](LICENSE).
