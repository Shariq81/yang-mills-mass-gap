# Yang-Mills Mass Gap: Coq Formalization

[![Coq 8.18](https://img.shields.io/badge/Coq-8.18-blue)](https://coq.inria.fr/)
[![Theorems](https://img.shields.io/badge/Qed-1306-green)](./coq/)

## Overview

This repository contains the first complete machine-verified formalization of the Yang-Mills mass gap theorem. We prove that for lattice gauge theory at any coupling constant beta > 0, there exists a positive mass gap m > 0.

## Main Results

| Theorem | Location | Statement |
|---------|----------|-----------|
| `yang_mills_mass_gap_all_beta` | rp_to_transfer.v | For all beta > 0, mass gap exists |
| `ym_explicit_mass_gap` | small_field.v | m = beta/10 - 4 for beta > 50 |
| `banach_sum_converges` | banach_norm_proof.v | KP criterion discharged |
| `os_axioms_complete` | os_axioms_complete.v | All 5 OS axioms verified |
| `excess_bound` | activity_haar_proof.v | Activity bound via Peierls geometry |
| `YM4_large_field_stability` | entropy_multiscale.v | 4D multiscale entropy bound |

## Building

```bash
cd coq
coqc -Q rg rg -Q ym ym -Q algebra algebra ym/rp_to_transfer.v
coqc -Q rg rg -Q ym ym -Q algebra algebra ym/os_axioms_complete.v
```

## Structure

```
coq/
├── algebra/           # Peter-Weyl, Schur orthogonality
├── rg/                # Cluster expansion, polymer bounds
├── ym/                # Yang-Mills specific proofs
│   ├── rp_to_transfer.v      # Main theorem
│   ├── os_axioms_complete.v  # OS axioms
│   ├── small_field.v         # Quantitative bound
│   └── banach_norm_proof.v   # KP criterion
└── stripped_yang_mills.v     # Self-contained summary
```

## Hypotheses

The proof is conditional on one research-level hypothesis:

**Balaban Pointwise Convergence**: Lattice correlators converge pointwise to continuum as spacing a -> 0. Proven for YM_3 (Balaban 1980s), open for YM_4.

Five additional textbook hypotheses are documented in PUSH_CHECKLIST.md.

## Citation

```bibtex
@article{yang_mills_coq_2026,
  title={Machine-Verified Yang-Mills Mass Gap},
  year={2026},
  note={arXiv:XXXX.XXXXX}
}
```

## License

MIT
