# Section 8–9 evidence and bibliographic locators

Canonical evidence lives in the separately distributed RECONCILED archive, identified by the SHA-256 in Section 8.3. The source and audit counts below refer to that immutable payload, not to a new Lean invocation.

| Claim | Exact source |
|---|---|
| 21 Lean files, 542 targets (520 theorems, 22 definitions) | `catalog/AUDITED_DECLARATIONS.csv`; `catalog/VERIFICATION.json`; `VERIFICATION_RU.md` |
| Pinned toolchain and complete runner | `canonical/lean-toolchain`; `canonical/run_verify.sh`; supplied `evidence/local_verification/RUNNER_FULL.log` line 176 |
| Parser controls | supplied runner lines 164–175; `canonical/test_audit.py`; `canonical/test_release_projection.py` |
| Canonical release proof targets | `canonical/Release.lean` lines 22–81 and 273–285; supplied runner lines 778–800 |
| 515 learning cases | supplied runner, finite learning output (`vs_read_costlier: 515`); `canonical/check_learning.py` |
| T28 cost witness | `canonical/check_replacement.py`; runner line 904; net gain and reserve discussion lines 919–922 |
| T29c mixed costs | `canonical/check_trace.py`; runner lines 945–946 |
| T31 closure and 8→7→6, 4→10 | `canonical/check_closure.py`; runner lines 978–1000 |
| T32 nine cases | `canonical/FINITE_RELEASE.json`; `canonical/Release.lean` `Witnesses` and `reports`; `canonical/check_release.py` lines 67–91, 102–148; runner lines 1542–1554 |
| Five-unit prior work | `canonical/Release.lean` line 254 (`partialLive`); runner `T32PRIOR` and `T32CERT` predecessor rows |
| Log replay vs fresh run | `catalog/VERIFICATION.json`; `evidence/reconciliation/replay/log_review.json`; the original English publication ZIP (RC4 replay receipt) |
| Historical numbering and axiom limitations | `GAPS_AND_STATUS_RU.md` |

The bibliography uses published metadata and DOI links (or the original arXiv identifier in the RAT-verification entry); the artifact entry refers to the supplied supplementary archive rather than an invented DOI. Related-work paragraphs are a scoped comparison, not an exhaustive novelty review.

## Companion-study references (rc2)

The original English publication ZIP contains `ZENODO_LINK_AUDIT.md` and `ZENODO_LINK_AUDIT.json` with exact repository locators, blob SHA values, and the distinction between repository verification and unresolved external record availability. These citations are contextual, not proof dependencies.

## RC4 additions (worked example and evidence supply)

- Depth obstruction and unit-charge baseline: `canonical/ControllerReplacement.lean`, `namespace Witnesses`, `src`, `dst`, `oldController`, `newController`, `oldContinuation`, `offer`, `profitable_switch`, `paid_end_to_end`, `baseline_bill`; `canonical/FINITE_RELEASE.json` baseline and single records. The direct root replacement and single meta-upgrade are separate runs on the same task pair.
- Selected meta-policy and its actual cost: `canonical/MetaPolicy.lean`, `Witnesses.decisionModel`, `selected`, `terminal_bills`, `selected_bills`, `makeUpgrade`, `changed_bill`; `canonical/Release.lean`, `Witnesses.single`, `costs`, `low_liquidity`, `nonempty_result`, `predecessor_result`.
- Constructive reserve and cost-evidence boundaries: `BudgetedPruning.lean:405` (`potential`), `ControllerReplacement.lean:106` (`remainingBill`), `:113` (`completion_bill_le`), `MetaInvestigation.lean:280` (`actualBill_le_reservation`), `MetaEvidenceAcquisition.lean:441` (`initialBounds`), `:446` (`exactRequest`), `:450` (`exactRequest_charge_covers`), `:455` (`exactRequest_point`), `RelativeEvidence.lean:103` (`fromAbsolute`), `MetaPolicy.lean:264` (`selected`), `:286` (`makeUpgrade`). These locate definitions and proofs, not a claim that all witness synthesis costs are cheap or accounted for physically.
- `supplement/replay_rc4/log_review.json` and command receipts: repeated current-source log replay; `supplement/local_attempt/STATUS.json` and the accompanying raw logs in the original English publication ZIP: historical attempt stopped before compilation (exit 127). The separate [fresh Linux run](supplement/FRESH_VERIFICATION.md) passed.
- `supplement/COMPANION_REFERENCES.tex` and PDF preserve all eight previously linked works. Three remain in the main text. The RC2 record-resolution limitations documented in the original English publication ZIP are unchanged.
- Reference [8] checked against the official arXiv abstract page `https://arxiv.org/abs/1612.02353` (title, authors, 2016, identifier).
