# Machine-Verified Yang-Mills Mass Gap
[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.18675091.svg)](https://doi.org/10.5281/zenodo.18675091)

This repository contains the Coq formalization proving the existence of a positive mass gap in 4D SU(2) and SU(3) Yang-Mills quantum field theory.

## Verification Instructions

**Prerequisites:**
- Coq 8.18.0 (exact version required)
- Standard Library only (no external plugins)

**Steps:**
```bash
# 1. Clone this repository
git clone https://github.com/Shariq81/yang-mills-mass-gap
cd yang-mills-mass-gap

# 2. Compile the proof
coqc zylphorian_yang_mills.v

# 3. Expected: Exit code 0 (no errors)
echo $?  # Should print: 0

# 4. (Optional) Verify with coqchk
coqchk -silent -o zylphorian_yang_mills
```

## Proof Statistics

| Metric | Value |
|--------|-------|
| Total lines | 8,449 |
| Completed proofs (Qed) | 402 |
| Axioms | 0 |
| Admitted steps | 0 |
| Coq version | 8.18.0 |

## Key Results

1. **Lattice Mass Gap:** Δ_lat ≥ √(-ln(20β)) for β < 1/20
2. **Counting Constant:** C = 20 (2.8× improvement over conservative C = 56)
3. **Continuum Limit:** Λ_QCD(μ,a) → μ > 0 as a → 0
4. **Uniform Bound:** Λ_QCD(μ,a) > μ·exp(-π²/11) for all a > 0
5. **Wightman Axioms:** Reconstructed QFT satisfies OS axioms

## Key Files

| File | Description |
|------|-------------|
| `zylphorian_yang_mills.v` | Complete self-contained proof (8,449 lines) |
| `main.tex` | LaTeX source for the preprint |
| `main.pdf` | Compiled preprint (after LaTeX compilation) |
| `ancillary/` | Supporting data for the C=20 optimization |

## Main Theorem

```coq
Theorem yang_mills_mass_gap_existence :
  forall mu, mu > 0 ->
  exists Delta_phys : R, Delta_phys > 0 /\
  (* Continuum limit *)
  (forall eps, eps > 0 -> exists a0,
    forall a, 0 < a < a0 ->
      Rabs (Lambda_QCD mu a - Delta_phys) < eps) /\
  (* Wightman QFT *)
  (exists w : Wightman_axioms,
    wightman_mass_gap w = Delta_phys /\
    wightman_mass_gap w > 0).
```

## arXiv Categories

- **Primary:** math-ph (Mathematical Physics)
- **Secondary:** hep-th, hep-lat

## MSC Codes

81T13, 81T25, 03B35, 68V15

## License

MIT License

## Citation

**BibTeX:**
```bibtex
@article{yang_mills_mass_gap_2026,
  title={Machine-Verified Proof of Mass Gap Existence in
         Four-Dimensional SU(2) and SU(3) Yang-Mills Theory},
  author={Shariq M. Farooqui},
  journal={Zenodo},
  year={2026},
  doi={10.5281/zenodo.18675091},
  note={Coq 8.18.0, 8449 lines, 402 Qed, 0 Axioms}
}
```

**APA:**
> Shariq81. (2026). Shariq81/yang-mills-mass-gap: Yang-Mills Mass Gap: Formal Proof in Coq (v1.0.0). Zenodo. https://doi.org/10.5281/zenodo.18675091

## Contact

Shariq M. Farooqui

Shariq81. (2026). Shariq81/yang-mills-mass-gap: Yang-Mills Mass Gap: Formal Proof in Coq (v1.0.0). Zenodo. https://doi.org/10.5281/zenodo.18675091
