# Cumulative Search with a Fixed Engine: Explicit Phase Invariants, Historical Event Replay, and Bounded Representation Escalation

*A verifiable separation of macro acquisition, law acquisition, and their computational utility*

**Aleksandr Strand · 22 November 2026**

## Abstract

We study a deterministic search engine that stores acquired program components and laws in a library and uses them to solve subsequent tasks. The paper provides two reproducible computational witnesses. The first is a three-event history: NAND law acquisition, XOR acquisition, and XOR law acquisition, with the permitted events executed anew for all eight coalitions. Numerical Shapley attribution uses an explicit model with several categories of computational work, accounting for component acquisition, law checks, circuit re-verification, and normalization. On a fixed suite of three tasks, the complete event set yields a capped logarithmic gain of 2.912749 nats over the empty acquisition library; on AND3, macro availability has a negative contribution. The second witness moves from a finite certificate that the target language cannot be recognized by a DFA with at most five states to a previously available class of one-counter automata. The transition table is synthesized from 12 initially empty cells; coefficients of a phase-linear invariant are extracted from its transitions and checked against local obligations. Applying the inferred slopes to the next task reduces the number of backtracking nodes from 57 to 28; an incorrect transfer triggers a fresh unrestricted search. The study distinguishes verified program semantics, finite access to an unknown teacher, acquisition cost, application cost, and the completeness of invariant inference. It makes no claim to provide a universal learner for arbitrary languages, absolute invariance under changes of code, a general 1-DCA equivalence solver, or unbounded cumulative discovery.

## 1. Problem Setting and Witness Criterion

A fixed algorithm updates memory and the search meta-state:

$$
(K_{t+1},M_{t+1})=F(K_t,M_t,D_t).
$$

In our programs, `F` is the fixed Python implementation of the general search procedure and verification gates. The experimenter specifies the admissible hypotheses, input encoding, task format, permitted acquisition events, and availability policy. The output has the form

$$
\mathrm{Output}=(P,I,\mathcal D,\pi,\mathcal E),
$$

where $P$ is a synthesized program, $I$ is an invariant in a specified formula class, $\mathcal D$ is its domain of applicability, $\pi$ contains checkable conditions, and $\mathcal E$ records observed costs and interventions. The absence of a certificate is assigned the status `UNKNOWN`, rather than being treated as truth by default. Physical cost measurements and independent proof-assistant verification are not claimed.

We distinguish two notions of contribution: the current value of an **already acquired** library and the counterfactual outcome of permitting **acquisition events** when replaying a predetermined sequence. Version 1.0 computed only the former. Version 1.1 separately recomputes the latter within a precisely bounded three-event model.

## 2. Finite witnesses for state lower bounds and escalation

Let $L\subseteq\{0,1,\$\}^*$, and let $p_1,\ldots,p_m$ be prefixes. A collection of suffixes $s_{ij}$ satisfying

$$
\mathbf1_L(p_i s_{ij})\ne\mathbf1_L(p_j s_{ij}),\qquad i\ne j,
$$

proves that any DFA recognizing $L$ must have at least $m$ distinguishable states, by the Myhill-Nerode criterion. The executed code produces all 15 pairwise distinguishing suffixes for six distinct rows: at horizon $K=2$ for $0^n1^n\$$, and at $K=5$ for $0^n1^{n+1}\$$. This is an exact certificate that **DFA≤5 is insufficient, assuming trusted answers**. It does not prove that an arbitrary unknown teacher is nonregular, nor does it rule out DFAs with six or more states.

The engine is configured in advance to select `1-DCA` as the next class: the certificate triggers a transition to the next available level, but does not constitute an independent invention of a counter. The absence of a trigger does not certify global equivalence between a finite observation table and an arbitrary teacher. For the regular negative control $0^+1^+\$$, we additionally construct a formal five-state reference automaton and exhaustively check equivalence between two **explicitly specified DFAs** by traversing their finite product graph.

A control guards against a stronger interpretation: the finite language consisting of every positive query made during the experiment is indistinguishable from the original target language on that transcript, yet differs on another word. Accordingly, the `oracle_global_equivalence` field is deliberately set to `UNKNOWN` for an arbitrary external function.

## 3. 1-DCA Synthesis and the Phase-Linear Consequence

The machine has active states $q_0,q_1$, terminal states `ACC` and `REJ`, a nonnegative integer counter $c$, symbols `0`, `1`, and `$`, and the test $c>0$. The interpreter is fixed; the program is a table of 12 cells. Backtracking starts with a completely empty table and fills cells in response to training examples. A strict end-of-input marker is required: accepting while ignoring symbols after `ACC` is forbidden.

**Lemma 3.1 (`DERIVED`, within the declared template).** Suppose that reading `0` in $q_0$ increments the counter by $a>0$; the bridge on the first `1` changes it by $d_b$ and enters $q_1$; and every subsequent `1` while $c>0$ changes the counter by $b<0$. When the local order, zero-test, and acceptance conditions hold, every non-rejected prefix satisfies

$$
q_0:\ c=am,\qquad
q_1:\ c=am+bk+d,\qquad d=d_b-b.
$$

Proof. Initially, $c=0$. Every `0` increases $c$ by $a$ and $m$ by one. After the first `1`, $c=am+d_b=am+b+d$. Each subsequent permitted transition on `1` increases $k$ by one and changes $c$ by $b$. Transitions that violate the required order, and attempts to make the counter negative, cause rejection. Acceptance at the unique `$` is permitted exactly from $q_1$ with $c=0$. Thus, within the stated domain, the accepted subset is exactly the subset satisfying $am+bk+d=0$. $\square$

For the selected machines, coefficients are obtained from the transitions **without an external `offset_for_inv`**, but the two-phase form and the local conditions to be checked are built into the analyzer. Specifically:

$$
T_1:\quad q_0:c=m,\quad q_1:c=m-k,\quad \mathrm{accept}\iff m=k;
$$

$$
T_2:\quad q_0:c=m,\quad q_1:c=m-k+1,\quad \mathrm{accept}\iff k=m+1.
$$

Acceptance over the same alphabet also requires the order $0^+1^+\$$. Neither $m=k$ nor $k=m+1$ is asserted to hold at intermediate prefixes.

**Experiment (`PRESENT`).** The synthesizer explored 26 backtracking nodes on T1 and 57 on T2 without a stored constraint. With a constraint based on the slopes inferred from T1, T2 required 28 nodes, a reduction by a factor of 2.035714. The constraint is admitted **provisionally**: if it does not lead to a certifiable program, the engine returns to the original unrestricted search. A control with the incorrect slope `(1,1)` explored 205 nodes without finding a solution in the constrained branch, then found the correct result in 57 nodes of the baseline search: 262 nodes in total.

The invariant is inferred within a prescribed class of phase-linear equations; discovery of an arbitrary mathematical explanation structure is not claimed. Local conditions are checked by executable code, while the induction above is a written proof, not a Lean certificate.

## 4. Acquisition of Boolean Operators and Laws

The Boolean engine starts with a single primitive, NAND. When event $e_1$ is permitted, the algorithm exhaustively discovers and checks NAND commutativity. When $e_2$ is permitted, it synthesizes XOR from NAND using the exact truth table over four input pairs and stores the program. Event $e_3$ can then discover the XOR laws: commutativity, associativity, $x\oplus x=0$, and zero as the identity element. The specified discovery tasks are part of a fixed curriculum. Candidate laws are checked over the entire finite Boolean domain; the operators' names are not used by the equality-checking algorithm.

For every $S\subseteq\{e_1,e_2,e_3\}$, a new history starts **with an empty acquisition library**. Events are executed in the order $e_1\to e_2\to e_3$, only when permitted by the coalition; $e_3$ has no effect without $e_2$. The macro is acquired anew: acquisition requires 341 candidate evaluations when the NAND law is available, and 1535 otherwise. Three-input parity, four-input parity, and AND3 are then solved under identical conditions. This is a local counterfactual **replay of three events**, rather than a history of arbitrary autonomous development.

### 4.1. Cost Accounting and the Failure Penalty

Instead of a single quantity called "time," we record the vector

$$
\mathbf C=(N_{\text{candidate}},N_{\text{normalize}},N_{\text{law}},
N_{\text{law-proof}},N_{\text{gate-proof}},T_{\text{wall}}).
$$

The primary proxy, $C_{\text{proxy}}$, assigns unit weight to each of the first five operation categories. Law discovery and verification over its finite truth table are charged separately; for a sequence of three tasks, acquisition is charged **once**. Actual elapsed time is reported only as a diagnostic. Python operations do not have equal durations: the proxy is neither energy, physical time, nor an absolute cost of thought.

Search for each individual task is bounded by a gate limit and a budget of 200,000 candidate evaluations. If no program is found within those bounds, the task's base candidate/proof component is assigned a **failure penalty** of 200,000. Recorded normalization costs are added separately, as are acquisition costs. Thus, the total proxy cost for a failed task can exceed 200,000. The penalty does not assert that a solution would be found at step 200,000, nor does it measure an observed completion time or a universal certification cost.

For a selected task collection $\mathcal T$, the logarithmic game applies a separate aggregate ceiling

$$
B_{\mathrm{aggregate}}=|\mathcal T|\cdot200\,000+1\,000\,000:
$$

1,200,000 for a single task and 1,600,000 for the three-task suite. These are explicit scoring conventions. The numerical attribution uses the penalized proxy cost defined here; the probabilistic identity below also holds independently for genuine random completion costs.

## 5. Budget Functional and Coalition Attribution

For a fixed task set, cost convention, and shared source of randomness $U$, let $C_S\in[1,\infty]$ denote the cost of obtaining the specified result under coalition $S$. With a finite ceiling $B$, define

$$
v(S)=\mathbb E_{\tau,U}\,[\ln\min(C_\varnothing,B)-\ln\min(C_S,B)].
$$

Here $v(\varnothing)=0$. The Shapley value for three players is given by the standard sum

$$
W_i=\sum_{S\subseteq N\setminus\{i\}}
\frac{|S|!(|N|-|S|-1)!}{|N|!}[v(S\cup\{i\})-v(S)].
$$

In the computed finite instance, $U$ is fixed, and no integration over $\mu$ is needed for an individual task. The three-task suite uses a shared sequence in which acquisition is charged once. For every coalition, the record includes the event order, available library, separate cost categories, synthesis results, and a history hash. Shapley attribution allocates the selected capped gain over the specified player set; its values may change when players are split or the cost convention changes.

**Lemma 5.1 (`DERIVED`, a standard identity).** For any $C_0,C_1\in[1,\infty]$ and finite $B\ge1$:

$$
\int_1^B [P(C_1\le b)-P(C_0\le b)]\,\frac{db}{b}=
\mathbb E[\ln\min(C_0,B)-\ln\min(C_1,B)].
$$

Proof. Use $\ln\min(C,B)=\int_1^B\mathbf1\{C>b\}\,db/b$, followed by linearity of expectation. A finite $B$ prevents the indeterminate expression $\infty-\infty$. $\square$

The uncapped expression may be used only when the difference of expectations is well defined and finite. The probability-of-success contribution curve need not have a single maximum; when usefulness differs across tasks, it can have multiple peaks or negative regions.

### 5.1. Computed Coalition Values
The table uses the primary proxy with a unit cost for normalization. Values are rounded to six decimal places. Internal calculations use unrounded values, and the identity $\sum_i W_i=v(N)$ is then checked.

| Condition | NAND_law, nats | XOR_macro, nats | XOR_laws, nats | Total gain, nats |
|---|---:|---:|---:|---:|
| Three-input parity | +0.728308 | +4.494372 | +0.025662 | 5.248342 |
| Four-input parity | +0.515465 | +1.668690 | +0.407383 | 2.591538 |
| AND3 | +1.229634 | **−0.867907** | +0.460386 | 0.822114 |
| Three-task history; acquisition charged once | **+0.546115** | **+1.925060** | **+0.441573** | **2.912749** |

On AND3, the XOR macro makes a negative contribution under the same engine that successfully uses it for parity. This is a concrete instance of the *utility problem*. It does not establish that XOR is harmful in general: the effect depends on the task distribution, grammar, budget, and cost model.

Accounting for normalization substantially changes the numerical results. For the three-task history, the XOR macro's share changes from approximately +2.869 nats when normalizer calls are free to +1.925 nats at unit cost and +0.957 nats at a cost of five. The gain reported in v1.0 is not carried over as a new measurement.

### 5.2. Implications for Attribution
Individual ablation and Shapley attribution answer different questions. In the OR game, removing either of two interchangeable components from the full coalition has zero effect, whereas Shapley assigns each a value of $1/2$. In the AND game, each component is necessary (leave-one-out = 1), whereas Shapley again assigns each a value of $1/2$. A zero removal effect and a positive attribution share do not contradict each other.

Historical contribution is not determined by a component's invocation frequency. A compiled program may cease to reference the original macro even though its acquisition affected earlier search. However, a single current snapshot does not establish a particular historical value; that value must be measured through replay under explicitly defined intervention semantics.

### 5.3. Historical Evidence and Search Priority

Retrospective $W^{\text{hist}}$ and future priority $U^{\text{future}}$ are different functions. Low future utility may justify removing a component from the active search queue, **not** deleting its history, certificate, or independent proofs. Losing one source of support does not automatically falsify a claim that has another valid proof.

## 6. What Has Been Established and What Remains Unknown

**Established within the stated classes:** reproducible acquisition of a macro and laws; replay of permitted acquisition events; signed Shapley attribution for a bounded game; positive and negative effects of library components; finite Myhill-Nerode lower-bound witnesses; 1-DCA synthesis from an empty table; inference of coefficients in a phase-affine form; exact characterization of the program's language within known families; a reduction in nodes from 57 to 28; and recovery after incorrect transfer.

**Not established:** the correctness of an arbitrary unknown teacher from finite observations; a globally optimal program or universal "bit of insight"; an invariant discovered outside the phase-linear template; invention of a new memory class; physical speedup; unbounded cumulative discovery; consciousness; or verification by a proof assistant. No historical model of an unbounded curriculum has been constructed. Preservation of meaning under arbitrary encoding changes requires a separate admissible mapping between representations and a proof of its correctness.

The exact finite negative result is that six pairwise distinguishable rows over a finite suffix set rule out DFA≤5. Nonregularity of the known languages can be proved separately by classical methods, but this finite signal does not establish it for an arbitrary teacher.

## 7. Discussion

This work does not claim to introduce Shapley attribution, Myhill-Nerode theory, inductive invariants, or library learning itself. Related approaches appear in Angluin [1], DreamCoder [3], babble [4], and causal Shapley [5]. Its potential independent value is a **compact, open, reproducible testbed in which acquisition events, the availability of executable macros, the availability of laws, and the measurement of their effects are kept distinct by definition**.

## 8. Reproducibility

The program version and exact files are recorded in `MANIFEST.json` and `SHA256SUMS.txt`. The original v1.0 is retained unchanged in `legacy/`. The new results preserve all eight event histories, programs, metric vectors, inductive conditions, finite Myhill-Nerode pairs, and negative counterexamples. Run the audit with:

```bash
python3 tests/audit_release.py
```

Timings and OS metadata may differ across runs. Consequently, hashes of raw JSON files do not test equality of semantic results: the audit compares deterministic fields separately. 

## References

1. D. Angluin. *Learning Regular Sets from Queries and Counterexamples*, Information and Computation 75(2), 1987. https://doi.org/10.1016/0890-5401(87)90052-6
2. S. Böhm, S. Göller, P. Jančar. *Equivalence of Deterministic One-Counter Automata is NL-complete*, STOC 2013. https://arxiv.org/abs/1301.2181
3. K. Ellis et al. *DreamCoder: Growing Generalizable, Interpretable Knowledge with Wake-Sleep Bayesian Program Learning*, 2023. https://doi.org/10.1098/rsta.2022.0050
4. D. Cao et al. *babble: Learning Better Abstractions with E-Graphs and Anti-Unification*, POPL 2023. https://doi.org/10.1145/3571207
5. T. Heskes et al. *Causal Shapley Values: Exploiting Causal Knowledge to Explain Individual Predictions of Complex Models*, NeurIPS 2020. https://proceedings.neurips.cc/paper_files/paper/2020/hash/32e54441e6382a7fbacbbbaf3c450059-Abstract.html
6. L. S. Shapley. *A Value for n-Person Games*, 1953. https://www.rand.org/pubs/papers/P295.html
7. J. Pearl. *Direct and Indirect Effects*, 2001. https://ftp.cs.ucla.edu/pub/stat_ser/R273.pdf
