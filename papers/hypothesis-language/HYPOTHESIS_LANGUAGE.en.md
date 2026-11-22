# Hypothesis Languages and Evidence-Scoped Identification

**Agreement queries, bounded algebraic criteria, and a finite cellular-automaton case study**

**Aleksandr Strand · 23 November 2026**

## Abstract

An observation can identify a unique semantic hypothesis relative to a selected hypothesis language without establishing either language-independent truth or the integrity of the observation channel. We develop a scoped account of this distinction: a claim has a formulation, an applicability domain, admissible transformations, and an evidence status. For nested hypothesis languages, the semantic version space shrinks under additional consistent observations but expands under language enlargement; consequently, finite identification certificates are representation-relative. For finite-dimensional linear function classes over the Boolean field, we give a two-sided identification window described by consistency and the kernel of the evaluation map. For general hypothesis families we use the agreement set to distinguish queries that split surviving hypotheses from queries that can falsify all of them by returning a forbidden answer. As a finite construction illustrating these distinctions, the Gate 4B–5 sequence implements conditional measurement, version-space filtering, model-consistency checks, a four-word parity code and a re-evaluated evidence predicate in an **augmented** radius-one cellular automaton whose base layer follows Rule 110 before an internal write-back. A supplied Lean 4.36.0 log reports ten successful checks of standalone Boolean, coding, and evidence-predicate statements. **Neither the complete 64-site transition system nor global origin-membership is proved by those Lean declarations.** The contribution is an inspectable integration and scoping of existing ideas, not a universal epistemic theorem or the invention of active learning, error-detecting codes, or runtime verification.

## 1. Claims, semantic identity, and evidence

A proposed invariant is recorded as $I=\langle\Phi,D,\mathcal T,E\rangle$: a precise claim $\Phi$, assumptions and scope $D$, a class of transformations $\mathcal T$, and evidence status $E$. The status must cite an actual proof, certificate, executable trace or explicit counterexample; it is not a property conferred merely by assigning a label. A code location or document page is an address to the evidence, not the identity of the mathematical claim.

Let $Q$ be a set of possible queries, $A$ the answer set, and $L_i$ nested symbolic hypothesis languages with embeddings $L_i\hookrightarrow L_j$ for $i\le j$. Assume the semantic map $\llbracket\cdot\rrbracket_i:L_i\to A^Q$ respects the embeddings. It need not be injective: different programs can express the same total behavior.

For a finite observation set $D\subseteq Q\times A$, define the **semantic** version space

$$
\widetilde V(L_i,D)=
\left\{\llbracket h\rrbracket_i:
h\in L_i,\ \forall(q,a)\in D,\ \llbracket h\rrbracket_i(q)=a\right\}.
$$

Identification means **exactly one semantic function**, not exactly one program syntax. In particular, any certificate must specify $L_i$, the query domain $Q$, semantic equality, observations, and the trusted observation assumptions.

For $D\subseteq D'$ with a fixed language and coherent interpretation,

$$
\widetilde V(L_i,D')\subseteq\widetilde V(L_i,D).
$$

For a semantics-preserving inclusion $L_i\hookrightarrow L_j$, with fixed observations,

$$
\widetilde V(L_i,D)\subseteq\widetilde V(L_j,D).
$$

Thus **more evidence contracts the hypothesis class; more expressive languages can reopen identification**. Refuting one semantic hypothesis is invariant under exact re-encoding; uniqueness among all admissible hypotheses is not.

The quantifier distinction is essential: establishing an identifying finite dataset *separately for each bounded language* is weaker than exhibiting a *single finite dataset that identifies the target uniformly across an unbounded hierarchy*. No such uniform conclusion follows from finite experiments here.

## 2. A finite-dimensional linear identification window

Here we present the algebraic claim in the precise domain where it holds.

Identify Boolean functions $Q=\mathbb F_2^n\to\mathbb F_2$ with the multilinear quotient algebra

$$
R=\mathbb F_2[x_1,\ldots,x_n]/(x_1^2-x_1,\ldots,x_n^2-x_n).
$$

Let $U_0\subseteq U_1\subseteq\cdots\subseteq U_k\subseteq R$ be a filtration of finite-dimensional $\mathbb F_2$-linear subspaces, $Z\subseteq Q$ the support of observed queries, and $y\in\mathbb F_2^Z$ their **consistent** answers. Write

$$
\rho_Z:U_i\to\mathbb F_2^Z,\qquad
K_i=\ker(\rho_Z|_{U_i})=U_i\cap I(Z),
$$

where $I(Z)=\{f:f|_Z=0\}$. If $\rho_Z(f)=y$ has no solution in $U_i$, the version space is empty. Otherwise it is an affine coset $f+K_i$ with

$$
|\widetilde V(U_i,D)|=2^{\dim U_i-\operatorname{rank}(\rho_Z|_{U_i})}.
$$

Define $i_*(D)$ as the first index at which a solution exists and $k_{\mathrm{break}}(Z)$ as the first index at which $K_i\ne\{0\}$, taking either index to be $+\infty$ when no such index exists. Under the stated nesting and consistency assumptions,

$$
|\widetilde V(U_i,D)|=1
\quad\Longleftrightarrow\quad
i_*(D)\le i<k_{\mathrm{break}}(Z).
$$

The window can be empty. The condition is not a theorem for arbitrary nonlinear grammars, nonnested classes, noisy observations, or language changes that alter the meaning of existing programs.

For an $i$ with a nonempty affine version space and $q\notin Z$, the evaluation map on $K_i$ is a linear functional. If it is nonzero at $q$, exactly half of the remaining semantic functions predict 0 and half predict 1. Equivalently, outside the common zero set $B(K_i)$, a binary oracle query bisects that finite affine version space. This **exact halving property is special to the linear case**.

A small language illustration: on $Q=\mathbb F_2^2$, the observations $f(0,0)=0$ and $f(1,0)=1$ identify $f(x_1,x_2)=x_1$ among functions dependent only on $x_1$. Allowing all Boolean functions leaves four semantic functions agreeing on the same data. The original bounded certificate was correct; its extrapolation to the enlarged language was not.

## 3. Agreement queries: discrimination versus potential falsification

For a **nonempty** semantic version space $V\subseteq A^Q$, define

$$
\operatorname{Agree}(V)=
\{q\in Q:\forall f,g\in V,\ f(q)=g(q)\}.
$$

Two different experimental purposes follow.

* If $q\notin\operatorname{Agree}(V)$, surviving models disagree at $q$. An admissible answer can remove at least one existing semantic prediction class. An answer not predicted by any survivor would instead refute them all.
* If $q\in\operatorname{Agree}(V)$, survivors have one common predicted answer. A **different** observed answer empties the version space and falsifies the present language-and-observation model. A **matching** answer shows compatibility for that query, **not** global truth, origin membership or unique identity.

When $V=\varnothing$, the universal formula above is vacuous: the system must mark the model already inconsistent, not infer a meaningful agreement test.

For the linear setting, $\operatorname{Agree}(f+K_i)=B(K_i)$. For a general nonlinear grammar, equal-split conclusions do not follow from nonagreement. Operationally, the distinction between *finding which candidate* and *testing whether the candidate family applies* is a useful research-controller contract, even though counterexample-guided learning and falsification are established prior practices.

## 4. Finite cellular-automaton witness, not pure binary Rule 110

The Gate 4B–5 experiments instantiate a small, deliberately finite observation protocol. The main layer is a 64-site periodic Rule 110 ring, while each site in the **augmented** automaton also has structured role, phase, communication and memory fields. Its single radius-one transition rule is spatially homogeneous but is **not** the two-symbol Wolfram Rule 110 transition on the complete alphabet.

Within the supplied finite fixture, the base Rule 110 layers of paired histories coincide on every site for times 10 through 27. The observer's auxiliary fields retain distinctions and later write an output into the base layer at the transition 27→28. This does not reverse a merger of the **complete augmented state**. The protocol uses preassigned sensor roles and a four-hypothesis response table, not autonomous creation of an open-ended hypothesis language.

The sequence of constructions addresses separate defects:

| Stage | Added behavior | Boundary exposed |
|---|---|---|
| Gate 4B | Conditional sensor routing and historical-bit recovery | Selection initially depends on a supplied context; proof checking is external |
| Gate 5 v1 | Internal four-hypothesis register and adaptive query choice | Early finite-scope construction; unrestricted origin validity not shown |
| Gate 5 v2 | Model-consistency query, finite time phase, full base-layer merger | The three-bit observation code has minimum distance 1 |
| Gate 5 v3 | Independent checksum lane and parity agreement | Static flags can disagree with a damaged version-space register |
| Gate 5 v3.1 | Direct version-register and codeword consistency check | A latched certificate can become stale after memory modification |
| Gate 5 v3.2 | Re-evaluation of a stored evidence tuple before use | Two-bit correlated faults and unknown origin remain outside the guarantee |

In the reported finite fixture, checksum and data reach the observer at states $t=13$ and $t=19$, and the output is published at $t=28$. These are simulation-level statements, not theorems of the attached Lean module. Full end-to-end verification of the 64-site transition system is not established here.

## 5. Local error-detecting code and live evidence predicate

The allowed observation triples are

$$
C_3=\{000,010,110,111\}.
$$

With an extra parity coordinate $p=z_1\oplus z_A\oplus z_B$, the resulting code is

$$
C_4=\{0000,0101,1100,1111\},\quad d_{\min}(C_4)=2.
$$

The supplied Lean source proves that every one of the 16 possible single-coordinate flips of the four valid codewords leaves the code. It also counts 10 of 24 two-bit flips that map a codeword to another codeword; protection is **not** guaranteed for correlated multi-bit errors, damage to the code-generation mechanism, or arbitrary faults in the augmented automaton. Syndrome disagreement is not uniquely diagnostic of a channel fault: out-of-model initial states can also violate the relation without wire corruption.

The **formal** live predicate in the Lean file is a Boolean function of a current version-space mask, a proposed answer and an observation word:

$$
\mathrm{LiveCert}(V,a,w)=
[V=2^a]\land[\operatorname{decode}(w_{0:3})=a]
\land[w_0\oplus w_1\oplus w_2\oplus w_3=0].
$$

Its ten declared theorems establish: Rule 110 truth-table equivalence with its algebraic normal form; $d_{\min}=2$; all 16 single-bit flips rejected; exactly 10/24 undetected two-bit flips; four nominal live predicates accepted; incorrect version-space masks, answer IDs and single receipt-bit flips rejected; and the impossibility of a length-two, four-word binary code with distance at least two.

**These are properties of the declared finite functions and the live predicate.** The Lean source does *not* prove that all reachable CA states compute this predicate correctly, that it is re-evaluated at every reachable step, or that no fault alters state fields outside the receipt. The supplied Lean 4.36.0 verification log records exit code 0 and standard axioms only; it was not independently recompiled in this editorial review.

There is an important separation between two code-length claims: four abstract messages with binary distance at least two need **at least three** code bits, whereas *extending this specific three-bit code $C_3$* to detect every single-bit corruption requires at least one additional parity bit. Neither proves that the entire physical CA needs only three or four bits of memory.

The original manuscript reports 23,014,938,240 formal product states per site (35 bits with dense fixed-width encoding), compared with 207,134,444,160 for v3.1, and an observed set of 505 local states across four nominal trajectories. These figures should remain explicitly labeled **reported state-accounting and finite trajectory observations**, not a global minimum or a proof of reachable-state closure.

## 6. Soundness and trust boundary

A valid *observation-relative* identification requires at least:

1. A fixed, declared hypothesis space and semantic equivalence relation.
2. Correctly associated query identities, answers and initial contexts.
3. A trusted or explicitly modeled observation channel.
4. Verified consistency between retained evidence, surviving hypotheses and released answer.
5. Adequate protection of the evidence fields **under the declared fault class**.

Even all five do not imply that the complete unknown 64-bit initial state belongs to the four hard-coded fixtures. **Origin membership remains UNKNOWN.** A finite sensor transcript determines an observation equivalence class, not an arbitrary complete configuration.

Likewise, a checksum that detects a single changed symbol cannot authenticate maliciously coordinated rewrites of several symbols or guarantee truth of a mislabeled world model.

The live-certification contract concerns consistency *of the current stored evidence*. It is not a theorem of consciousness, first-person experience, self-discovery, or language-independent truth.

## 7. Relation to prior research and contribution

The mathematical ingredients draw on established areas: machine identification and distinguishing experiments (Moore; Gold; Lee–Yannakakis), oracle-guided inductive program synthesis (Jha–Seshia), error-detecting coding (Hamming), and runtime verification of an executing system (Leucker–Schallhart). The presence of these ingredients is **not**, by itself, evidence that a new general theorem has been discovered.

The defensible contribution of this research line is: (a) an explicit joint contract for language-scoped semantic uniqueness, model consistency, syndrome evidence and origin uncertainty; (b) an exact finite-dimensional algebraic explanation of where identification fails under language growth; (c) a constructive finite augmented-CA development in which failures of overly strong certificate claims lead to successively narrower operational claims; and (d) a small, inspectable Lean proof artifact verifying selected finite subclaims.

The resulting case study is limited to an explicitly specified hypothesis family and a finite augmented-automaton fixture. Its Lean artifact formalizes selected finite Boolean and coding properties, not a general theorem about adaptive scientific discovery.

## References

1. E. F. Moore, *Gedanken-experiments on Sequential Machines*, 1956.
2. E. M. Gold, *Complexity of Automaton Identification from Given Data*, 1978.
3. D. Lee and M. Yannakakis, *Testing Finite-State Machines: State Identification and Verification*, 1994.
4. S. Jha and S. A. Seshia, *A Theory of Formal Synthesis via Inductive Learning*, *Acta Informatica* 54 (2017), 693–726. https://arxiv.org/abs/1505.03953
5. R. W. Hamming, *Error Detecting and Error Correcting Codes*, *Bell System Technical Journal* 29 (1950), 147–160. https://doi.org/10.1002/j.1538-7305.1950.tb00463.x
6. M. Leucker and C. Schallhart, *A Brief Account of Runtime Verification*, *J. Logic and Algebraic Programming* 78 (2009), 293–303. https://doi.org/10.1016/j.jlap.2008.08.004
7. Dnarts, *Rule 110 dependency fronts* (domain-specific companion): https://github.com/Dnarts/rule110-dependency-fronts
8. Dnarts, *Proof-Carrying Discovery*, v1.1 (cumulative search and bounded representation escalation): https://github.com/Dnarts/proof-carrying-discovery
