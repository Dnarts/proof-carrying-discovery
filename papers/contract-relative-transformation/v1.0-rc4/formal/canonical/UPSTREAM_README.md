# CRTT-T23-v0.1.1-preflight — Certified Pruning

Status: **VERIFIED on Lean 4.36.0.** All six modules compile with exit 0 and
zero diagnostics; 166 upstream + 24 new = 190 axiom reports are audited by
exact name, with only `propext` and `Quot.sound` permitted; no `sorryAx`, no
`Classical.choice`, no warning, no error. Toolchain
`Lean (version 4.36.0, arm64-apple-darwin24.6.0, commit 611c117)`. See
`KERNEL_CHECK.log`.
Parent: `CRTT-T23-v0.1-draft.zip`. This preflight does not overwrite the parent.
All five upstream Lean files, their SHA-256 manifest and the upstream kernel log are byte-identical to `CRTT-T22.9-v0.2.3-verified.zip`. The 166 upstream axiom reports were re-audited successfully; they are not a new compilation.

## Changes and obligations

- Fixed eight reversed applications of `allB` / `allB_iff` using their actual T22 predicate-first signatures.
- Replaced recursive proof elaboration in the two prefix lemmas with explicit induction and list membership APIs. Rewrote the profitability proof using a supplied additive equality and `Nat.sub_add_cancel`, avoiding dependence on `Nat.sub_mul`.
- Added `rejected_region_empty`, `injectiveRule`, `depthRule`. The latter two are early T20 constraints, not additional semantic assumptions.
- Added a constructive full-leaf decoder (`assignmentWitness`, `assignmentCover`, `selectedPair`, `decodePortMap`). No dummy inhabitant is required when a port carrier is empty.
- Added executable `prunedDiscover` and a bridge to the exact canonical certificates of T22: `prunedDiscover_sound`, `prunedDiscover_complete`, `prunedDiscover_iff`, `prunedDiscover_pair_complete`, `prunedDiscover_empty_iff`. The target is equality of membership, not list order or multiplicity. Final certification still uses the unchanged T22 checks. This is an eager DFS with early pruning, not yet a paid/resumable frontier.
- Added `composeRule_same_keep` and `ordered_rule_cost_iff`, separating commutative semantic conjunction from short-circuit costs on a fixed region collection. `composeRule.cost` is a sum / upper bound; it is not a measurement of short-circuited execution.
- Replaced the finite check with literal total-map enumeration compared against eight prefix-search policies (seven filtered plus the no-rule control). The stand checks exact canonical certificates, scoped rejection, empty/asymmetric domains, and actual counts in its own model. It does not execute Lean.
- `searchTotalCost` and `pruning_profitable_iff` are still conditional arithmetic, not a theorem that supplies counts from actual Lean execution. T23.5 (paid pruning cursor), action-prefix pruning, actual trace accounting, selection of a rule from a library, and amortization of discovery-rule synthesis remain OPEN. See `NEXT_GATES.md`.

## Observed finite checks

`FINITE_CHECK.log` records 8,529 task pairs, 59,703 filtered policy comparisons, 82,005 rejected regions, 3,108 canonical pair results, 2,048 row-monotonicity checks, 3,000 uniform-cost arithmetic checks, and 9,625 ordering arithmetic checks. The seven filtered policies are compared with the same unfiltered prefix-tree control with unchanged final T22 guards. It also contains positive/negative economic witnesses, including a no-op rule and two filter orders. These are fixed abstract charges, not CPU time, empirical generalization, or a Lean proof.

## Kernel verification

Lean 4.36.0 is required. The strict auditor and its ten fixtures are copied from the input archive. Expected: 166 upstream + 24 new-module reports = 190 reports. The new-module compilation was run in a verification environment with Lean 4.36.0 and passed; see the outcome section below. The script fails closed on compiler errors, warnings, missing/extra/duplicate axiom reports, and axioms beyond `propext` / `Quot.sound`.

```bash
unzip CRTT-T23-v0.1.1-preflight.zip
cd CRTT-T23-v0.1.1-preflight
set -o pipefail
bash run_verify.sh 2>&1 | tee ../T23-PREFLIGHT-KERNEL.log
```

**Outcome of that run.** `run_verify.sh` exits 0 on a fresh extraction. Per-module
audits are `22 + 22 + 51 + 37 + 34 + 24 = 190` reports, and
`CertifiedPruning.lean` reports `24/24 axiom reports; Lean exit=0;
dependencies={'Quot.sound': 18, 'propext': 23}`. All ten auditor fixtures pass,
and the finite checks pass: `monotonicity=2048; arithmetic=3000; order=9625;
independent literal h,p,a enumeration`, plus exact canonical certificates,
scoped rejections, empty/asymmetric domains and short-circuit accounting.

Three defects had to be repaired to reach this status, and they are recorded so
that the same patterns can be recognised again:

- `morphism_mem_partialPortWorlds` applied `M.read_eq pair.1 x`. That field takes
  four explicit arguments — port, its membership in `S.ports`, world, and its
  membership in `T.worlds` — so the world was being passed where the membership
  proof was expected. Supplying `port_mem_all`/`world_mem_all` fixed the
  elaboration and, with it, the three `sorryAx` dependencies that descended from
  it (`morphism_mem_partialPortWorlds`, `empty_partialReadRow_prunes`,
  `readCompatRule`).
- `pruning_profitable_iff` and `ordered_rule_cost_iff` proved a biconditional
  with a single bare `omega`. On `↔` over truncated `Nat` subtraction and
  multiplication, `omega` falls back on a classical decision and imports
  `Classical.choice`; splitting with `constructor` and closing each direction
  separately is constructive.

`KERNEL_CHECK.log` is included in this archive and records the run. The claims
about open work are unchanged: `searchTotalCost` and `pruning_profitable_iff`
remain conditional arithmetic, and T23.5 (paid pruning cursor), action-prefix
pruning, actual trace accounting, rule selection from a library and amortisation
of rule synthesis stay open in `NEXT_GATES.md`. A recorded PASS is not a substitute
for kernel acceptance on the consumer's machine: rerun the script and read the
`#print axioms` output yourself.
