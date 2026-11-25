# Verified Cluster Expansion, Exponential Decay, and 4D $\mathbb{Z}_2$ and $SU(2)$ Wilson Lattice Gauge Theory at Strong Coupling (Coq 8.18.0)

[![Coq 8.18.0](https://img.shields.io/badge/Coq-8.18.0-blue)](https://coq.inria.fr/)
[![Zenodo DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.24512861.svg)](https://doi.org/10.5281/zenodo.24512861)
[![Concept DOI](https://img.shields.io/badge/Zenodo%20Concept%20DOI-10.5281%2Fzenodo.18675090-blue)](https://doi.org/10.5281/zenodo.18675090)
[![License: MIT](https://img.shields.io/badge/License-MIT-green.svg)](LICENSE)

> **Honest Scope:** The certified verification cone in [`coq/verification/`](coq/verification/README.md) proves **25 frozen Coq 8.18.0 propositions** with **0 project axioms**, **0 admitted lemmas**, and independent `coqchk` kernel verification. **Targets 1–6c** (11 propositions, unchanged since the Zenodo release `10.5281/zenodo.24507324`): Penrose's (1967) BFS tree-graph inequality, the genuine ordered-tuple $1/n!$ Kotecký–Preiss (1986) cluster expansion theorem, an exact **0-axiom** 21-neighbor enumeration of canonical unit plaquettes on $\mathbb{Z}^4$, absolute convergence of the Mayer/Ursell series to $\ln Z_\Lambda$ for the actual finite-volume compatible-subset partition function $Z_\Lambda$, and uniform exponential decay of the exact partition-function log ratio for the finite-volume constant-activity ($\beta > 85$) $\mathbb{Z}^4$ plaquette polymer gas. **Targets 7a–7d** (4 propositions, pinned together with Targets 1–6c by the Zenodo release `10.5281/zenodo.24512861`): for the 4D $\mathbb{Z}_2$ Wilson lattice gauge theory in finite volume (Wilson action, exact Haar sum over all link configurations) — the exact strong-coupling expansion into closed mod-2 surfaces, exponential clustering of the gauge-invariant connected plaquette correlator at strong coupling uniformly in the volume, the exact identification of $Z_\Lambda$ with a hard-core gas of surface polymers, and the Kotecký–Preiss criterion with a convergent cluster expansion of the free energy. **Target 7e** (1 proposition, added after `10.5281/zenodo.24512861`): a uniform area–perimeter upper bound on rectangular Wilson-loop expectations for $63|\tanh\beta| \le 1$ whenever all boundary links of the loop lie in the dynamical volume (interior holes allowed), yielding exponential area suppression as both side lengths grow whenever $63|\tanh\beta| < 1$. **Targets 8a–8e** (5 propositions, added after the 16-target release): for the 4D $SU(2)$ Wilson lattice gauge theory — lattice Yang–Mills theory with the non-abelian gauge group $SU(2)$ (unit quaternions, Wilson action) — in finite volume at strong coupling: exponential clustering of the truncated correlation of any two plaquette-local observables and a uniform area–perimeter upper bound on rectangular Wilson loops, first for every finite a-priori link distribution on $SU(2)$, uniformly in the distribution (8a, 8b), then for the Haar measure, realized as the limit of the uniform distributions on dyadic Hopf-coordinate grids, for which the Gibbs expectation of every bounded uniformly continuous observable is proved to exist (8c, 8d, 8e). **Targets 9a–9d** (4 propositions): the infinite-volume limit of that theory at strong coupling — the expectation of a local observable changes by an exponentially small amount when distant plaquettes are added to the volume (9a), the infinite-volume Haar-measure Gibbs expectation of every bounded uniformly continuous observable localized on finitely many plaquettes exists as the limit along the cubes $[-n,n]^4$ (9b), and it satisfies the exponential clustering bound (9c) and the Wilson-loop area–perimeter bound (9d).  
> It does **not** certify 4D continuum Yang–Mills theory, a continuum limit, weak coupling, uniqueness of the infinite-volume limit (independence of boundary conditions and of the exhausting sequence) or its translation invariance, reflection positivity, a transfer-matrix spectral gap, a string tension defined as a limit or any lower bound on Wilson loops, Osterwalder–Schrader reconstruction, or the Clay Millennium Prize Problem. The $SU(2)$ results are strong-coupling lattice statements, i.e. in the regime opposite to the one where a continuum limit would be taken; and the identification of the Hopf-coordinate measure with the Haar measure of $SU(2)$ (its bi-invariance) is the classical volume formula of $S^3$, not a formalized statement.

---

## Quick Verification Replay (Zero Trust Required)

Install Python 3 and **Coq 8.18.0** (`coqc` and `coqchk` on `PATH`), then run from the repository root:

```bash
python3 replay.py
```

*(Pass `--coqc /path/to/coqc --coqchk /path/to/coqchk` if they are not on `PATH`.)*

`replay.py` verifies the SHA-256 checksums of all 54 pinned `.v` sources against [`coq/verification/receipts/sources.sha256`](coq/verification/receipts/sources.sha256), compiles them from scratch in a clean temporary directory (the frozen statement files `Challenge.v`, `ChallengeZ2Gauge.v`, `ChallengeZ2AreaLaw.v`, `ChallengeSU2Gauge.v` and `ChallengeSU2InfiniteVolume.v` first, before any proof module exists), typechecks all 25 frozen targets, runs the self-tested standard-library-only axiom allowlist gate, checks exact equality against the archived `Print Assumptions` receipts, and runs `coqchk`.

On Linux or WSL2, you can also run the full clean-wipe shell harness:

```bash
bash coq/verification/replay.sh
```

---

## Certified Frozen Targets (25 Theorems, 54 Source Files)

Targets 1–6c are declared in [`coq/verification/Challenge.v`](coq/verification/Challenge.v) importing **only the Coq 8.18.0 standard library** (zero project imports, zero `Axiom`/`Parameter`/`Admitted`), and verified in [`coq/verification/Verify.v`](coq/verification/Verify.v). Targets 7a–7d are declared in [`coq/verification/ChallengeZ2Gauge.v`](coq/verification/ChallengeZ2Gauge.v), which imports **only the Coq standard library and the frozen `Challenge.v`** and contains definitions only, and are verified in [`coq/verification/VerifyZ2Gauge.v`](coq/verification/VerifyZ2Gauge.v). Target 7e is declared in [`coq/verification/ChallengeZ2AreaLaw.v`](coq/verification/ChallengeZ2AreaLaw.v), which imports **only the Coq standard library and the two frozen files above** and contains definitions only, and is verified in [`coq/verification/VerifyZ2AreaLaw.v`](coq/verification/VerifyZ2AreaLaw.v). Targets 8a–8e are declared in [`coq/verification/ChallengeSU2Gauge.v`](coq/verification/ChallengeSU2Gauge.v), which imports **only the Coq standard library and the three frozen files above** and contains definitions only, and are verified in [`coq/verification/VerifySU2Gauge.v`](coq/verification/VerifySU2Gauge.v). Targets 9a–9d are declared in [`coq/verification/ChallengeSU2InfiniteVolume.v`](coq/verification/ChallengeSU2InfiniteVolume.v), which imports **only the Coq standard library and the four frozen files above** and contains definitions only, and are verified in [`coq/verification/VerifySU2InfiniteVolume.v`](coq/verification/VerifySU2InfiniteVolume.v). The 16 source files of Targets 1–6c are byte-identical to the Zenodo release `10.5281/zenodo.24507324`, and the 27 source files of Targets 1–7d are byte-identical to the Zenodo release `10.5281/zenodo.24512861`; the 8 source files added for Target 7e, the 11 source files added for Targets 8a–8e and the 8 source files added for Targets 9a–9d are **not** part of either record.

| Target | Frozen Proposition (`Challenge.v`; 7a–7d: `ChallengeZ2Gauge.v`; 7e: `ChallengeZ2AreaLaw.v`; 8a–8e: `ChallengeSU2Gauge.v`; 9a–9d: `ChallengeSU2InfiniteVolume.v`) | Result Certified | Axioms |
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
| **6c** | `Challenge_Lattice4D_PartitionFn_Decay` | Concrete $\mathbb{Z}^4$ ($\beta > 85$, any finite `NoDup` volume $\Lambda$) partition-function positivity, $\ln Z_\Lambda$ convergence, and $\left\lvert\ln\frac{Z_\Lambda Z_{\Lambda_{12}}}{Z_{\Lambda_1} Z_{\Lambda_2}}\right\rvert \le e \cdot \exp\!\left(-\frac{1}{2}\|s(p_1)-s(p_2)\|_1\right)$ (**0 analytic or combinatorial hypotheses**) | 4 stdlib, **0 project** |
| **7a** | `Challenge_Z2Gauge4D_StrongCouplingExpansion` | Exact strong-coupling expansion of the 4D $\mathbb{Z}_2$ Wilson lattice gauge theory (Wilson action, exact Haar sum): $Z_\Lambda = \cosh(\beta)^{\lvert\Lambda\rvert} \sum_{\partial S = 0} \tanh(\beta)^{\lvert S\rvert}$ over closed mod-2 surfaces, and $\langle \prod_{l \in C} U_l \rangle = \sum_{\partial S = C} \tanh(\beta)^{\lvert S\rvert} / \sum_{\partial S = 0} \tanh(\beta)^{\lvert S\rvert}$, for every $\beta$ and every finite plaquette list (**0 hypotheses**) | 3 stdlib, **0 project** |
| **7b** | `Challenge_Z2Gauge4D_StrongCouplingClustering` | Exponential clustering of the gauge-invariant connected plaquette correlator, uniformly in the finite volume: $\left\lvert\langle U_{p_1} U_{p_2}\rangle_\Lambda - \langle U_{p_1}\rangle_\Lambda \langle U_{p_2}\rangle_\Lambda\right\rvert \le 4\,e^{-\mu(\mathrm{dist}(p_1,p_2)-1)}$ whenever $168\,\lvert\beta\rvert \le e^{-\mu}$ (**0 analytic or combinatorial hypotheses**) | 4 stdlib, **0 project** |
| **7c** | `Challenge_Z2Gauge4D_SurfacePolymerGas` | $Z_\Lambda(\beta) = \cosh(\beta)^{\lvert\Lambda\rvert}$ times the hard-core polymer partition function (the object of Targets 6a–6c) of connected closed mod-2 surfaces with activity $\tanh(\beta)^{\lvert\gamma\rvert}$ — exactly, for every $\beta$ | 3 stdlib, **0 project** |
| **7d** | `Challenge_Z2Gauge4D_FreeEnergyClusterExpansion` | For $189\,\lvert\tanh\beta\rvert \le 1$: the Kotecký–Preiss inequality for the surface polymers, convergence of the Mayer/Ursell series to $\ln Z_\Lambda - \lvert\Lambda\rvert \ln\cosh\beta$, and $\left\lvert\ln Z_\Lambda - \lvert\Lambda\rvert\ln\cosh\beta\right\rvert \le 189\,\lvert\tanh\beta\rvert\,\lvert\Lambda\rvert$ (**0 analytic or combinatorial hypotheses**) | 4 stdlib, **0 project** |
| **7e** | `Challenge_Z2Gauge4D_WilsonLoopAreaLaw` | Uniform strong-coupling Wilson-loop area–perimeter upper bound: for $63\,\lvert\tanh\beta\rvert \le 1$ and every $a \times b$ rectangular loop $C$ all of whose boundary links belong to `z2_links Lambda` (interior holes allowed), $\left\lvert\langle \prod_{l \in C} U_l \rangle_\Lambda\right\rvert \le (63\,\lvert\tanh\beta\rvert)^{ab}\, e^{2(a+b)}$; gives exponential area suppression as $a, b \to \infty$ whenever $63\,\lvert\tanh\beta\rvert < 1$ (**0 analytic or combinatorial hypotheses**) | 4 stdlib, **0 project** |
| **8a** | `Challenge_SU2Gauge4D_StrongCouplingClustering` | 4D $SU(2)$ Wilson lattice gauge theory with any non-empty finite list $G \subset SU(2)$ as a-priori link distribution: for observables $f, g$ with $\lvert f\rvert, \lvert g\rvert \le 1$ depending only on the link variables of the plaquettes $p_1$, $p_2$ (e.g. $\tfrac12\mathrm{tr}\,U_{p_1}$, $\tfrac12\mathrm{tr}\,U_{p_2}$), $\left\lvert\langle f g\rangle_\Lambda - \langle f\rangle_\Lambda \langle g\rangle_\Lambda\right\rvert \le 4\,e^{-\mu(\mathrm{dist}(p_1,p_2)-1)}$ whenever $168\,\lvert\beta\rvert \le e^{-\mu}$, uniformly in the finite volume and in $G$ (**0 analytic or combinatorial hypotheses**) | 4 stdlib, **0 project** |
| **8b** | `Challenge_SU2Gauge4D_WilsonLoopAreaLaw` | Same theory with $G$ invariant under $U \mapsto -U$: for $63\,(e^{2\lvert\beta\rvert}-1) \le 1$ and every $a \times b$ rectangular loop $C$ all of whose links belong to `z2_links Lambda`, $\left\lvert\langle \tfrac12\mathrm{tr}\,U(C) \rangle_\Lambda\right\rvert \le (63\,(e^{2\lvert\beta\rvert}-1))^{ab}\, e^{2(a+b)}$, uniformly in the finite volume and in $G$; gives exponential area suppression as $a, b \to \infty$ whenever $63\,(e^{2\lvert\beta\rvert}-1) < 1$ (**0 analytic or combinatorial hypotheses**) | 4 stdlib, **0 project** |
| **8c** | `Challenge_SU2Gauge4D_HaarStateExists` | Haar-measure Gibbs state of the 4D $SU(2)$ Wilson lattice gauge theory: for every $\beta$, every finite plaquette list and every bounded uniformly continuous observable $F$, the Gibbs expectations for the uniform distributions on the dyadic Hopf-coordinate grids of $SU(2) = S^3$ (Riemann sums of the Haar integrals) converge | 4 stdlib, **0 project** |
| **8d** | `Challenge_SU2Gauge4D_HaarClustering` | For the Haar-measure Gibbs state and bounded uniformly continuous plaquette-local $f, g$: the expectations $\langle fg\rangle$, $\langle f\rangle$, $\langle g\rangle$ exist and satisfy the bound of 8a, uniformly in the finite volume | 4 stdlib, **0 project** |
| **8e** | `Challenge_SU2Gauge4D_HaarWilsonLoopAreaLaw` | For the Haar-measure Gibbs state: the Wilson-loop expectation exists and satisfies the bound of 8b, uniformly in the finite volume | 4 stdlib, **0 project** |
| **9a** | `Challenge_SU2Gauge4D_VolumeDependence` | 4D $SU(2)$ Wilson lattice gauge theory with any finite a-priori link distribution: for an observable $f$, $\lvert f\rvert \le 1$, localized on the plaquettes $P \subseteq \Lambda$, $\left\lvert\langle f\rangle_{Q \cup \Lambda} - \langle f\rangle_\Lambda\right\rvert \le 2\,e^{2\lvert\beta\rvert} \sum_{q \in Q} \sum_{p \in P} e^{-\mu(\mathrm{dist}(p,q)-1)}$ whenever $168\,\lvert\beta\rvert \le e^{-\mu}$ (**0 analytic or combinatorial hypotheses**) | 4 stdlib, **0 project** |
| **9b** | `Challenge_SU2Gauge4D_ThermodynamicLimit` | Thermodynamic limit: for $43008\,\lvert\beta\rvert \le 1$ and every bounded uniformly continuous observable localized on finitely many canonical plaquettes, the Haar-measure Gibbs expectations in the volumes $\Lambda_n$ (all canonical plaquettes anchored in the cube $[-n,n]^4$) converge as $n \to \infty$ | 4 stdlib, **0 project** |
| **9c** | `Challenge_SU2Gauge4D_InfiniteVolumeClustering` | Infinite-volume Gibbs state: for bounded uniformly continuous plaquette-local $f, g$ with $\lvert f\rvert, \lvert g\rvert \le 1$, the expectations exist and $\left\lvert\langle f g\rangle - \langle f\rangle\langle g\rangle\right\rvert \le 4\,e^{-\mu(\mathrm{dist}(p_1,p_2)-1)}$ whenever $168\,\lvert\beta\rvert \le e^{-\mu}$ and $43008\,\lvert\beta\rvert \le 1$ | 4 stdlib, **0 project** |
| **9d** | `Challenge_SU2Gauge4D_InfiniteVolumeAreaLaw` | Infinite-volume Gibbs state: for $43008\,\lvert\beta\rvert \le 1$ and every $a \times b$ rectangular loop $C$ (anywhere on the lattice), the Wilson-loop expectation exists and $\left\lvert\langle \tfrac12\mathrm{tr}\,U(C)\rangle\right\rvert \le (63\,(e^{2\lvert\beta\rvert}-1))^{ab}\, e^{2(a+b)}$ | 4 stdlib, **0 project** |

Permitted Coq 8.18.0 standard-library allowlist (5 axioms max): `Classical_Prop.classic`, `ClassicalEpsilon.constructive_indefinite_description`, `ClassicalDedekindReals.sig_not_dec`, `ClassicalDedekindReals.sig_forall_dec`, `FunctionalExtensionality.functional_extensionality_dep`.

**Scope of Targets 7a–7e.** They concern the lattice gauge theory with the *finite abelian* gauge group $\mathbb{Z}_2$, in *finite volume* with free boundary conditions, at *strong coupling* only ($|\beta| \le 1/168$ for 7b, $|\tanh\beta| \le 1/189$ for 7d, $|\tanh\beta| \le 1/63$ for 7e); 7b is clustering of a truncated correlation function, not a spectral gap. 7e is a uniform *area–perimeter upper bound* for *rectangular* loops whose boundary links all lie inside the dynamical volume (interior holes in $\Lambda$ are allowed, while links outside `z2_links Lambda` are frozen to $+1$, so a loop outside it has expectation $1$ and the boundary-link hypothesis cannot be dropped); because of the perimeter factor $e^{2(a+b)}$, it is non-trivial when $ab \ln\frac{1}{63|\tanh\beta|} > 2(a+b)$ (hence gives exponential area suppression as both side lengths grow whenever $63|\tanh\beta| < 1$), and no lower bound on Wilson loops and no string tension as a limit is formalized. The mathematics is classical (Wegner 1971; Wilson 1974; Osterwalder–Seiler 1978); what is new is the machine-checked formalization with zero project axioms. Target 7b is proved by a duplicate-system expansion and does not use the Kotecký–Preiss engine; the engine is used in 7d and 7e.

**Scope of Targets 8a–8e.** They concern the *lattice* gauge theory with the non-abelian compact simple gauge group $SU(2)$ and the Wilson action, in *finite volume* with free boundary conditions, at *strong coupling* only ($|\beta| \le 1/168$ for 8a/8d, $e^{2|\beta|} - 1 \le 1/63$ for 8b/8e), with bounds that are uniform in the volume. Strong coupling is the regime opposite to $\beta \to \infty$, where a continuum limit would have to be taken: these results do not approach the continuum theory, and no transfer matrix, reflection positivity or spectral gap is formalized (the infinite-volume limit is the subject of Targets 9a–9d). 8a/8d bound truncated correlations of plaquette-local observables; 8b/8e are *upper* bounds for *rectangular* Wilson loops inside the dynamical volume, non-trivial only when $ab \ln\frac{1}{63(e^{2|\beta|}-1)} > 2(a+b)$. In 8c–8e the Haar measure is realized as the limit of uniform distributions on dyadic grids of the Hopf coordinates of $S^3$; that this limit is the Haar measure (bi-invariance) is the classical volume formula and is not formalized, whereas 8a/8b hold for *every* finite a-priori distribution of the stated kind and hence for every weak limit of such distributions. The mathematics is classical (Wilson 1974; Osterwalder–Seiler 1978); what is new is the machine-checked formalization with zero project axioms. 8a reuses the duplicate-system theorem of 7b, and 8b reuses the rooted expansion, minimal-area lemma and entropy bound of 7e together with the $\mathbb{Z}_2$ center symmetry of $SU(2)$.

**Scope of Targets 9a–9d.** They concern the same strong-coupling $SU(2)$ *lattice* theory ($|\beta| \le 1/43008$ for 9b–9d). The infinite-volume Gibbs expectation is the limit of the Haar-measure expectations along the cubes $[-n,n]^4$ with free boundary conditions, for observables localized on finitely many plaquettes; its independence of the boundary conditions and of the exhausting sequence, and its translation invariance, are **not** formalized. 9c is exponential decay of truncated correlations in infinite volume — a finite correlation length for plaquette-local observables; identifying the decay rate with a spectral (mass) gap of a transfer matrix requires reflection positivity and a Hilbert-space construction, which are not formalized. 9d is an *upper* bound for *rectangular* Wilson loops. Nothing here concerns the continuum limit or the Clay Millennium Prize Problem. The mathematics is classical (Osterwalder–Seiler 1978); the proof of 9a reuses the duplicate-system theorem of 7b, and 9b sums the resulting bounds over the shells of the cubes.

Full technical documentation, source hashes, and cross-platform replay details live in [`coq/verification/README.md`](coq/verification/README.md).

---

## Verification Cone Layout

```text
replay.py                              # Portable cross-platform Coq 8.18.0 verifier
coq/
├── verification/
│   ├── Challenge.v                    # 11 frozen target statements, Targets 1–6c (Coq stdlib ONLY)
│   ├── ChallengeZ2Gauge.v             # 4 frozen target statements, Targets 7a–7d (stdlib + Challenge.v ONLY)
│   ├── ChallengeZ2AreaLaw.v           # 1 frozen target statement, Target 7e (stdlib + the two files above ONLY)
│   ├── ChallengeSU2Gauge.v            # 5 frozen target statements, Targets 8a–8e (stdlib + the three files above ONLY)
│   ├── ChallengeSU2InfiniteVolume.v   # 4 frozen target statements, Targets 9a–9d (stdlib + the four files above ONLY)
│   ├── Verify.v                       # Proof assignment & bridges (0 axioms/admitted)
│   ├── VerifyZ2Gauge.v                # Proof assignment for Targets 7a–7d (0 axioms/admitted)
│   ├── VerifyZ2AreaLaw.v              # Proof assignment for Target 7e (0 axioms/admitted)
│   ├── VerifySU2Gauge.v               # Proof assignment for Targets 8a–8e (0 axioms/admitted)
│   ├── VerifySU2InfiniteVolume.v      # Proof assignment for Targets 9a–9d (0 axioms/admitted)
│   ├── CheckTypes.v                   # Exact frozen type verification (Targets 1–6c)
│   ├── CheckTypesZ2Gauge.v            # Exact frozen type verification (Targets 7a–7d)
│   ├── CheckTypesZ2AreaLaw.v          # Exact frozen type verification (Target 7e)
│   ├── CheckTypesSU2Gauge.v           # Exact frozen type verification (Targets 8a–8e)
│   ├── CheckTypesSU2InfiniteVolume.v  # Exact frozen type verification (Targets 9a–9d)
│   ├── CheckAxioms.v                  # Pure Print Assumptions driver (Targets 1–6c)
│   ├── CheckAxiomsZ2Gauge.v           # Pure Print Assumptions driver (Targets 7a–7d)
│   ├── CheckAxiomsZ2AreaLaw.v         # Pure Print Assumptions driver (Target 7e)
│   ├── CheckAxiomsSU2Gauge.v          # Pure Print Assumptions driver (Targets 8a–8e)
│   ├── CheckAxiomsSU2InfiniteVolume.v # Pure Print Assumptions driver (Targets 9a–9d)
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
│   ├── cluster_expansion.v            # Legacy conditional cluster expansion (Targets 2–3)
│   ├── dup_clustering.v               # Abstract duplicate-system clustering theorem (Target 7b)
│   ├── polymer_representation.v       # Factorizing subset sums = polymer partition functions (7c)
│   ├── connected_subset_bound.v       # KP pinned bound for connected subsets / lattice animals (7d)
│   ├── rooted_polymer_bound.v         # Rooted KP entropy bound & rooted subset expansion (Target 7e)
│   ├── product_measure.v              # Product a-priori measure: independence & one-variable symmetry (Target 8)
│   └── product_measure_perm.v         # Product a-priori measure: order of variables, extra variables (Target 9)
└── ym/
    ├── lattice_4d_coordination.v      # 0-axiom exact 21-neighbor Z^4 plaquette enumeration
    ├── lattice_4d_kp.v                # Concrete Z^4 KP & partition-function decay (5c, 6c)
    ├── lattice.v                      # 4D lattice geometry definitions
    ├── geometry_frontier.v            # Constructive BFS simple-path distance bound (Target 1)
    ├── z2_gauge_expansion.v           # Exact Z_2 strong-coupling expansion (Target 7a)
    ├── z2_gauge_clustering.v          # Z_2 strong-coupling exponential clustering (Target 7b)
    ├── z2_polymer_gas.v               # Z_2 surface-polymer-gas representation (Target 7c)
    ├── z2_free_energy.v               # Z_2 KP criterion & free-energy cluster expansion (Target 7d)
    ├── z2_even_holonomy.v             # Even link multiplicities force holonomy +1 (Target 7e)
    ├── z2_min_area.v                  # Minimal area of plaquette sets bounded by a rectangle (7e)
    ├── z2_area_law.v                  # Z_2 strong-coupling Wilson-loop area law (Target 7e)
    ├── su2_algebra.v                  # Unit quaternions, SU(2) holonomies, center flips (Target 8)
    ├── su2_clustering.v               # SU(2) strong-coupling exponential clustering (Target 8a)
    ├── su2_area_law.v                 # SU(2) strong-coupling Wilson-loop area law (Target 8b)
    ├── su2_continuity.v               # Bounded uniformly continuous SU(2) observables (Target 8c)
    ├── su2_haar_grid.v                # Hopf grids: center symmetry & convergence of grid sums (8c)
    ├── su2_haar_limit.v               # Haar-measure Gibbs state: existence, clustering, area law (8c–8e)
    ├── su2_volume.v                   # Exponentially small dependence on the volume (Target 9a)
    ├── lattice_boxes.v                # The cubes [-n,n]^4: counting and distances of the shells (9b)
    └── su2_infinite_volume.v          # Thermodynamic limit, clustering and area law in infinite volume (9b–9d)
```

---

## Historical Archive Note

Older exploratory files from the February 2026 `v1.x`–`v2.1.0` releases (`coq/ym/os_axioms_complete.v`, `coq/ym/rp_to_transfer.v`, `main.tex`, etc., archived at [`10.5281/zenodo.18726858`](https://doi.org/10.5281/zenodo.18726858)) remain in the repository for historical provenance. They are **outside** the 54-file certified verification cone and contain legacy project hypotheses and unverified stubs. All current verified claims are restricted strictly to the 25 frozen targets certified by `replay.py` / `coq/verification/replay.sh`.

---

## Citation

If you use or build on this formalization, please cite the Zenodo release:

```bibtex
@software{farooqui_2026_z2_gauge_cluster,
  author       = {Farooqui, Shariq},
  title        = {Verified Cluster Expansion, Exponential Decay, and 4D Z_2 Wilson Lattice Gauge Theory at Strong Coupling},
  year         = 2026,
  month        = nov,
  publisher    = {Zenodo},
  doi          = {10.5281/zenodo.18675090},
  url          = {https://doi.org/10.5281/zenodo.18675090}
}
```

Concept DOI (always resolves to the latest version): [`10.5281/zenodo.18675090`](https://doi.org/10.5281/zenodo.18675090) · Version `z2-gauge-2026-11-24` (Targets 1–7d): [`10.5281/zenodo.24512861`](https://doi.org/10.5281/zenodo.24512861) · Version `verification-2026-11-24` (Targets 1–6c): [`10.5281/zenodo.24507324`](https://doi.org/10.5281/zenodo.24507324).

## License

MIT — see [LICENSE](LICENSE).
