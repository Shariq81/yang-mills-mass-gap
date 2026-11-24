# Frozen Challenge Verification Harness (RH-Style 3-Step Workflow)

This directory provides a self-contained, reproducible verification harness for the finite-lattice polymer cluster-expansion proofs (including the genuine ordered-tuple $1/n!$ Ursell Kotecký–Preiss tree-graph theorem) and concrete 4D hypercubic lattice ($\mathbb{Z}^4$) plaquette combinatorics and exponential decay in `yang-mills-final-proof/coq/`, modeled after the `Challenge` / `Comparator` / independent-checker workflow used to verify the 2026 Lean 4 Riemann Hypothesis proof.

> **Honest Scope:** This harness certifies finite-volume abstract polymer graph/metric bounds, conditional cluster-expansion exponential decay, the genuine ordered-tuple $1/n!$ Ursell Kotecký–Preiss (1986) / Penrose (1967) tree-graph theorem (pinned exponential-moment bounds and truncated correlator exponential decay with **zero** analytic assumptions), convergence of the $1/n!$ Mayer/Ursell series to $\ln Z_\Lambda$ for the actual finite-volume compatible-subset partition function $Z_\Lambda$ plus convergence and exponential decay of the exact partition-function log ratio $\ln\frac{Z_\Lambda Z_{\Lambda \setminus (\bar{p}_1 \cup \bar{p}_2)}}{Z_{\Lambda \setminus \bar{p}_1} Z_{\Lambda \setminus \bar{p}_2}}$, and concrete $\mathbb{Z}^4$ plaquette overlap combinatorics (exact 21-neighbor enumeration) plus unconditional finite-volume $\ln Z_\Lambda$ convergence and log-ratio decay for the constant-activity ($\beta > 85$) $\mathbb{Z}^4$ plaquette polymer model. It does **not** certify 4D continuum Yang–Mills theory, Wilson action / Haar measure, Osterwalder–Schrader reconstruction, or the Clay Millennium Prize Problem.

---

## Architecture

| File | Role | Imports |
|---|---|---|
| [Challenge.v](Challenge.v) | **11 frozen target statements** (Targets 1–3, 4a–4b, 5a–5c, 6a–6c) | **Coq 8.18.0 stdlib only** (`Reals`, `ZArith`, `Bool`, `Arith`, `List`, `Classes.RelationClasses`) — zero project imports, zero `Axiom`/`Parameter`/`Admitted` |
| [../rg/penrose_tree_bound.v](../rg/penrose_tree_bound.v) | Genuine Ursell function $\varphi^T(X) = \sum_{H \text{ conn.}} (-1)^{|E(H)|}$, Penrose (1967) BFS partition scheme, tree-graph inequality $|\varphi^T(X)| \le \#\mathcal{T}(X)$, and graph-isomorphism invariance | Coq stdlib only |
| [../rg/poly_exp_bound.v](../rg/poly_exp_bound.v) | Exact finite-polynomial exponential generating function lemma (`exp_recurrence_sum_bound`) and Taylor partial-sum bound (`exp_partial_sum_le`) | Coq stdlib only |
| [../rg/tree_cut_bijection.v](../rg/tree_cut_bijection.v) | Exact Vertex-1 spanning-tree edge-cut bijection (`tree_count_decomp`) | Coq stdlib + `rg.penrose_tree_bound` |
| [../rg/kotecky_preiss.v](../rg/kotecky_preiss.v) | Genuine ordered-tuple $1/n!$ Kotecký–Preiss theorem: tree-sum induction, root-pinned bound ($\le e^{a(p_0)}$), 1-pinned overlap bound ($\le a(p_0)$), and Ursell two-point correlator exponential decay (0 analytic assumptions) | Coq stdlib + `rg.penrose_tree_bound`, `rg.poly_exp_bound`, `rg.tree_cut_bijection` |
| [../rg/exp_series_limit.v](../rg/exp_series_limit.v) | Real-analysis exponential generating function convergence theorem (`exp_of_abs_conv_recurrence`): finite-support recurrence + absolute convergence implies $Z = \sum_{k=0}^D A_k > 0$ and $\sum_{n=0}^N c_n \to \ln Z$ | Coq stdlib + `rg.poly_exp_bound` |
| [../rg/cluster_log_partition.v](../rg/cluster_log_partition.v) | Finite-volume compatible-subset partition function $Z_\Lambda$, ordered-tuple equivalence, exact 0-component graph bijection, $\ln Z_\Lambda$ convergence (`kp_log_partition_fn`), four-volume inclusion-exclusion, and exact log-ratio decay (`kp_log_ratio_decay`) | Coq stdlib + `rg.penrose_tree_bound`, `rg.poly_exp_bound`, `rg.tree_cut_bijection`, `rg.kotecky_preiss`, `rg.exp_series_limit` |
| [../ym/lattice_4d_coordination.v](../ym/lattice_4d_coordination.v) | Zero-axiom constructive proof of exact 21-neighbor enumeration (`Closed under the global context`) and $\le 24$ coordination bound on $\mathbb{Z}^4$, replacing legacy `Axiom plaq_wellformed` with explicit `wf_plaq` | Coq stdlib + `ym.lattice` |
| [../ym/lattice_4d_kp.v](../ym/lattice_4d_kp.v) | Discharges the single-polymer KP inequality on $\mathbb{Z}^4$ from the exact 21-neighbor count ($21 e^{-\beta/10 + 2} \le 1$ for $\beta > 85$) and proves concrete $\mathbb{Z}^4$ plaquette Ursell correlator decay (5c) and partition-function $\ln Z_\Lambda$ convergence & exact log-ratio decay (6c) | Coq stdlib + `ym.lattice`, `ym.lattice_4d_coordination`, `rg.kotecky_preiss`, `rg.cluster_log_partition` |
| [Verify.v](Verify.v) | Bridges `Challenge.v` definitions to the repo's submitted proofs and assigns them to all 11 frozen propositions | `verification.Challenge` + submitted proof cone |
| [CheckTypes.v](CheckTypes.v) | Typechecks that each verified theorem matches its exact frozen `Challenge` proposition | `verification.Challenge`, `verification.Verify` |
| [CheckAxioms.v](CheckAxioms.v) | Emits **only** `Print Assumptions` blocks (no interleaved `Check` output) | `verification.Verify` |
| [check_allowlist.py](check_allowlist.py) | Automated gate + built-in negative self-test: fails with exit 1 if any axiom outside the 5 Coq stdlib axioms appears (including `Verify.*` or `Challenge.*` axioms) | — |
| [replay.sh](replay.sh) | Clean-wipe rebuild of all 16 files in the verification cone (`Challenge.v` compiled first in isolation), static guard on all 10 new/frozen files, typecheck, self-tested allowlist check, and `coqchk` kernel replay | — |

---

## Critical Mathematical Note on Target 3 (`n!` Ordered-Cluster Caveat)

Independent audit (2026-11-24) identified a crucial mathematical limitation in the legacy `rg/cluster_expansion.v` + `ym/small_field.v` formulation captured by Target 3 (`Challenge_MasterConditionalStatement`):
- `clusters_Λ_N` enumerates **ordered** NoDup lists of length $\le N_{\max}$ without a $\frac{1}{|X|!}$ symmetry factor, and Target 3 sets `ursell := 1`.
- On an $n$-vertex path with $\beta = 86, a = 1$, each vertex has $\le 3$ overlapping neighbors, so both KP conditions hold ($3 e^{-7.6} \le 1$, $3 e^{-6.6} \le 1$), yet all $n!$ permutations of the path connect its endpoints and contribute $n! e^{-7.6 n} \to \infty$ as $n \to \infty$, violating the pinned bound $\le e^2$ for large $n$.
- **Resolution in Targets 5a–5c:** Targets 5a–5c implement the standard ordered-tuple Mayer / Kotecký–Preiss expansion (Fernández–Procacci 2007 §2; Kotecký–Preiss 1986 §2): ordered tuples $X \in \Lambda^n$ (repetitions allowed), genuine $1/n!$ symmetry factor, and the genuine Ursell coefficient $\varphi^T(X) = \sum_{H \subseteq \mathcal{G}(X)\text{ conn.}} (-1)^{|E(H)|}$. In this formulation, the pinned exponential-moment bounds and correlator exponential decay are **proved unconditionally from the elementary single-polymer KP inequality** via Penrose's (1967) BFS tree-graph inequality and rooted-tree induction — with zero analytic assumptions.

---

## Frozen Targets & Explicit Hypotheses

1. **`Challenge.Challenge_ConnectsImpliesDistBound`** *(unconditional graph/metric theorem — 0 analytic hypotheses)*  
   For any polymer type `P` with decidable equality, symmetric decidable adjacency `adj`, real distance `dist` (`dist p p = 0`, triangle inequality, `adj p q -> dist p q <= 1`), and `size p >= 1`, any cluster `X` connecting `p1` to `p2` satisfies $\mathrm{dist}(p_1, p_2) \le \mathrm{cluster\_size}(X)$.  
   *Submitted proof:* constructive BFS + simple-path loop erasure in `ym/geometry_frontier.v` (`connects_to_simple_path`, `ym_connects_implies_dist_bound_from_frontier`).

2. **`Challenge.Challenge_ConditionalExponentialDecay`** *(clean conditional cluster-to-decay implication)*  
   Under the same polymer/metric/adjacency structure, finite-volume cluster enumeration `(polymers_Λ, N_max)`, uniform size bound `S_max >= 1`, decay rate `a > 0`, and the **explicitly visible pinned-cluster exponential-moment hypothesis**:
   $$\forall p_1, p_2,\quad \sum_{X \in \mathcal{C}(\Lambda, N_{\max}),\, X \text{ connects } p_1, p_2} |w(X)|\, e^{a |X|} \le e^{a\,\mathrm{size}(p_1)} e^{a\,\mathrm{size}(p_2)},$$
   the connected correlator decays exponentially with explicit prefactor $e^{2 a S_{\max}}$ and decay rate $a$.  
   *Submitted proof:* `ym/geometry_frontier.v` + `rg/cluster_expansion.v`.

3. **`Challenge.Challenge_MasterConditionalStatement`** *(exact zero-`Parameter` hoisting of `ym/wightman_mass_gap_master.v`)*  
   Hoists all 8 former global parameters of `ym/small_field.v` into explicit `forall` quantifiers alongside `beta > 85`, `a <= beta / 20`, KP at `a`, KP at `2a`, and the Brydges pinned-cluster implication, proving `exists m > 0, has_mass_gap dist correlator m`.  
   *Submitted proof:* `ym/geometry_frontier.v` + `rg/cluster_expansion.v` (`exponential_decay_from_cluster`).

4a. **`Challenge.Challenge_Lattice4D_Exact21`** *(pure constructive $\mathbb{Z}^4$ plaquette combinatorics — **0 axioms total**, `Closed under the global context`)*  
   Defines concrete 4D lattice sites `Site4D` ($\mathbb{Z}^4$), directions `Dir4D`, plaquettes `Plaq4D`, explicit canonical-plane well-formedness `wf_plaq_4D` (eliminating legacy `Axiom plaq_wellformed`), unordered boundary-edge sharing `plaq4D_shares_edge`, and reflexive overlap `plaq4D_overlap`. Certifies an explicit neighbor enumerator satisfying `NoDup`, well-formedness closure, sound+complete overlap specification (`In q (neighbors p) <-> plaq4D_overlap p q`), and exact cardinality `length (neighbors p) = 21` (1 self + 4 boundary edges $\times$ 5 other canonical plaquettes per edge).  
   *Submitted proof:* `ym/lattice.v` + `ym/lattice_4d_coordination.v` (coordinate-sum anchor invariant + translation equivariance + decidable `vm_compute` on the 6 origin planes).

4b. **`Challenge.Challenge_Lattice4D_Coordination24`** *(real-valued 24-coordination bound — 0 analytic hypotheses, 0 project axioms)*  
   Extends Target 4a with `INR (length (neighbors p)) <= 24`, discharging the concrete 4D instance of `YMNeighborEnumerationFrontier`.  
   *Submitted proof:* `ym/lattice.v` + `ym/lattice_4d_coordination.v`.

5a. **`Challenge.Challenge_KoteckyPreiss_PinnedBound`** *(genuine Kotecký–Preiss pinned exponential-moment bounds — **0 analytic assumptions**, 0 project axioms)*  
   In the standard ordered-tuple $1/n!$ Ursell formulation (repetitions allowed, $\varphi^T(X) = \sum_{H \subseteq \mathcal{G}(X)\text{ conn.}} (-1)^{|E(H)|}$), under ONLY the elementary single-polymer KP condition $\sum_{q \in \Lambda,\, q \nsim p} |w(q)| e^{a(q)+d(q)} \le a(p)$ (at $p_0$ and on $\Lambda$), proves BOTH:
   - **Root-pinned bound:** $\sum_{k=0}^{N} \frac{1}{k!} \sum_{Y \in \Lambda^k} |\varphi^T(p_0 :: Y)| \prod_{q \in Y} (|w(q)| e^{d(q)}) \le e^{a(p_0)}$;
   - **1-pinned overlap bound (Kotecký–Preiss Theorem 1):** $\sum_{n=1}^{N_{\max}} \frac{1}{n!} \sum_{X \in \Lambda^n,\, X \nsim p_0} |\varphi^T(X)| \prod_{q \in X} (|w(q)| e^{d(q)}) \le a(p_0)$.  
   *Submitted proof:* `rg/penrose_tree_bound.v` + `rg/poly_exp_bound.v` + `rg/tree_cut_bijection.v` + `rg/kotecky_preiss.v`.

5b. **`Challenge.Challenge_KoteckyPreiss_ExponentialDecay`** *(unconditional Ursell correlator exponential decay from KP alone — **0 analytic assumptions**, 0 project axioms)*  
   Under ONLY the single-polymer KP condition (with $d(q) = c \cdot \mathrm{size}(q)$, $c > 0$, $\mathrm{size}(q) \ge 1$) and a unit-step metric (`ob p q = true -> dist p q <= 1`), proves uniform exponential decay of the genuine truncated two-point Ursell correlator (clusters overlapping both $p_1$ and $p_2$, which converges as $N_{\max} \to \infty$ to $\ln\frac{Z_\Lambda Z_{\Lambda \setminus (\bar{p}_1 \cup \bar{p}_2)}}{Z_{\Lambda \setminus \bar{p}_1} Z_{\Lambda \setminus \bar{p}_2}}$, proved in Targets 6a–6c):
   $$\left|G_{\Lambda, N_{\max}}(p_1, p_2)\right| \le a(p_1)\, e^c\, e^{-c\,\mathrm{dist}(p_1, p_2)}.$$  
   *Submitted proof:* `rg/kotecky_preiss.v`.

5c. **`Challenge.Challenge_Lattice4D_KP_ExponentialDecay`** *(concrete $\mathbb{Z}^4$ plaquette Ursell correlator exponential decay — **0 analytic hypotheses, 0 combinatorial hypotheses**, 0 project axioms)*  
   Quantifies over ANY boolean decision procedure `ob` for `plaq4D_overlap`, ANY $\beta > 85$, ANY finite `NoDup` volume $\Lambda$ of canonical $\mathbb{Z}^4$ plaquettes, ANY truncation $N_{\max}$, and ANY canonical $p_1, p_2 \in \mathcal{P}(\mathbb{Z}^4)$, discharging KP automatically from the exact 21-neighbor bound ($21 e^{-\beta/10 + 2} \le 1$) and proving:
   $$\left|G_{\Lambda, N_{\max}}^{\mathbb{Z}^4}(p_1, p_2)\right| \le e \cdot \exp\!\left(-\frac{1}{2}\|s(p_1) - s(p_2)\|_1\right).$$  
   *Submitted proof:* `ym/lattice_4d_coordination.v` + `rg/kotecky_preiss.v` + `ym/lattice_4d_kp.v`.

6a. **`Challenge.Challenge_KoteckyPreiss_LogPartitionFn`** *(exact finite-volume partition function $Z_\Lambda > 0$ and $\ln Z_\Lambda$ convergence — **0 analytic assumptions**, 0 project axioms)*  
   Defines the genuine compatible-subset finite-volume partition function $Z_\Lambda = \sum_{S \subseteq \Lambda\text{ pairwise compat.}} \prod_{p \in S} w(p)$. Under ONLY reflexive+symmetric `ob` and the single-polymer KP condition on $\Lambda$ (with $d \equiv 0$), proves:
   - $Z_\Lambda > 0$;
   - absolute convergence of the $1/n!$ Mayer/Ursell series: $\forall N,\, \sum_{n=0}^N |c_n| \le \sum_{p \in \Lambda} a(p)$;
   - `Un_cv (fun N => kp_series Lambda N (ursell * w)) (ln Z_Lambda)`.  
   *Submitted proof:* `rg/exp_series_limit.v` + `rg/cluster_log_partition.v`.

6b. **`Challenge.Challenge_KoteckyPreiss_LogRatioDecay`** *(convergence of truncated correlator to the partition-function log ratio and exact log-ratio exponential decay — **0 analytic assumptions**, 0 project axioms)*  
   For $\Lambda_1 = \Lambda \setminus N(p_1)$, $\Lambda_2 = \Lambda \setminus N(p_2)$, $\Lambda_{12} = \Lambda \setminus (N(p_1) \cup N(p_2))$, proves $Z_\Lambda, Z_{\Lambda_1}, Z_{\Lambda_2}, Z_{\Lambda_{12}} > 0$, exact convergence of the truncated Ursell correlator $G_{\Lambda, N}(p_1, p_2) \xrightarrow{N \to \infty} \ln\frac{Z_\Lambda Z_{\Lambda_{12}}}{Z_{\Lambda_1} Z_{\Lambda_2}}$ via four-volume inclusion-exclusion, and unconditional exponential decay of the exact partition-function log ratio:
   $$\left|\ln\frac{Z_\Lambda Z_{\Lambda_{12}}}{Z_{\Lambda_1} Z_{\Lambda_2}}\right| \le a(p_1)\, e^c\, e^{-c\,\mathrm{dist}(p_1, p_2)}.$$  
   *Submitted proof:* `rg/cluster_log_partition.v`.

6c. **`Challenge.Challenge_Lattice4D_PartitionFn_Decay`** *(concrete $\mathbb{Z}^4$ plaquette partition function $\ln Z_\Lambda$ convergence and exact log-ratio decay — **0 analytic hypotheses, 0 combinatorial hypotheses**, 0 project axioms)*  
   For any $\beta > 85$, $w(p) = e^{-\beta/10}$, any finite `NoDup` volume $\Lambda$ of canonical $\mathbb{Z}^4$ plaquettes, and any canonical $p_1$ and $p_2$, proves $Z_\Lambda, Z_{\Lambda_1}, Z_{\Lambda_2}, Z_{\Lambda_{12}} > 0$, $\lim_{N \to \infty} \mathrm{kp\_series}(\Lambda, N) = \ln Z_\Lambda$, $\lim_{N \to \infty} G_{\Lambda, N}(p_1, p_2) = \ln\frac{Z_\Lambda Z_{\Lambda_{12}}}{Z_{\Lambda_1} Z_{\Lambda_2}}$, and:
   $$\left|\ln\frac{Z_\Lambda Z_{\Lambda_{12}}}{Z_{\Lambda_1} Z_{\Lambda_2}}\right| \le e \cdot \exp\!\left(-\frac{1}{2}\|s(p_1) - s(p_2)\|_1\right).$$  
   *Submitted proof:* `ym/lattice_4d_coordination.v` + `rg/exp_series_limit.v` + `rg/cluster_log_partition.v` + `ym/lattice_4d_kp.v`.

---

## Latest Verified Run (`2026-11-24T15:44:00Z`)

- **Toolchain:** Coq `8.18.0` (OCaml `4.14.1`), `/usr/bin/coqc` & `/usr/bin/coqchk` (WSL2 Linux x86_64) — see [receipts/toolchain.txt](receipts/toolchain.txt).
- **Static guard:** `0` occurrences of `Axiom`, `Parameter`, `Conjecture`, `Admitted`, or `admit` across all 10 guarded files (`Challenge.v`, `penrose_tree_bound.v`, `poly_exp_bound.v`, `tree_cut_bijection.v`, `kotecky_preiss.v`, `exp_series_limit.v`, `cluster_log_partition.v`, `lattice_4d_coordination.v`, `lattice_4d_kp.v`, `Verify.v`).
- **Isolation check:** `verification/Challenge.v` compiled cleanly after wiping all 16 cone `.vo` files and **before** any project `.v` file was compiled.
- **Axiom Allowlist Gate ([receipts/allowlist.log](receipts/allowlist.log), [receipts/axioms.log](receipts/axioms.log)):**
  - Allowlist parser built-in negative self-test: **PASS** (rejected injected `Verify.*`, `Challenge.*`, project, and multiline axioms).
  - `Verify.verified_connects_implies_dist_bound`: **4 Coq stdlib axioms**, **0 project axioms**, **0 admitted lemmas**.
  - `Verify.verified_conditional_exponential_decay`: **5 Coq stdlib axioms**, **0 project axioms**, **0 admitted lemmas**.
  - `Verify.verified_master_conditional_statement`: **5 Coq stdlib axioms**, **0 project axioms**, **0 admitted lemmas**.
  - `Verify.verified_lattice4D_exact21`: **0 axioms total (`Closed under the global context`)**, **0 project axioms**, **0 admitted lemmas**.
  - `Verify.verified_lattice4D_coordination24`: **2 Coq stdlib axioms** (`sig_forall_dec`, `functional_extensionality_dep`), **0 project axioms**, **0 admitted lemmas**.
  - `Verify.verified_kotecky_preiss_pinned_bound`: **4 Coq stdlib axioms** (`sig_forall_dec`, `sig_not_dec`, `classic`, `functional_extensionality_dep`), **0 project axioms**, **0 admitted lemmas**.
  - `Verify.verified_kotecky_preiss_exponential_decay`: **4 Coq stdlib axioms**, **0 project axioms**, **0 admitted lemmas**.
  - `Verify.verified_lattice4D_kp_exponential_decay`: **4 Coq stdlib axioms**, **0 project axioms**, **0 admitted lemmas**.
  - `Verify.verified_kotecky_preiss_log_partition_fn`: **4 Coq stdlib axioms**, **0 project axioms**, **0 admitted lemmas**.
  - `Verify.verified_kotecky_preiss_log_ratio_decay`: **4 Coq stdlib axioms**, **0 project axioms**, **0 admitted lemmas**.
  - `Verify.verified_lattice4D_partition_fn_decay`: **4 Coq stdlib axioms**, **0 project axioms**, **0 admitted lemmas**.
  - Permitted stdlib allowlist: `Classical_Prop.classic`, `ClassicalEpsilon.constructive_indefinite_description`, `ClassicalDedekindReals.sig_not_dec`, `ClassicalDedekindReals.sig_forall_dec`, `FunctionalExtensionality.functional_extensionality_dep`.
- **Kernel Replay ([receipts/coqchk.log](receipts/coqchk.log)):** `coqchk -R . '' verification.Challenge verification.Verify` → **`Modules were successfully checked`** (exit `0`).
- **Checksums:** Recorded in [receipts/sources.sha256](receipts/sources.sha256) (16 source files) and [receipts/artifacts.sha256](receipts/artifacts.sha256) (`Challenge.vo`, `Verify.vo`).

---

## Reproducing the Check From Scratch

From Windows (via WSL2 with Coq 8.18.0):

```bash
wsl -e bash -lc 'bash /mnt/c/GitHub/reimannhypothesis/yang-mills-final-proof/coq/verification/replay.sh'
```
