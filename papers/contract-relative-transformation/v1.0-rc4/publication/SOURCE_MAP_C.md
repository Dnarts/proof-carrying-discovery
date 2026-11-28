# Source map for preprint Sections 6–7

The paper theorem statements combine named verified declarations with explicit definitions; they are not new Lean declarations. The line locators below refer to the immutable accepted source bytes identified by SOURCE_SHA256_C.txt. The last column refers to the supplied successful T32 log, not a newly executed kernel check.

## 6.1: frontier correctness and rebase

| Lean declaration | Source line | Supplied audit line |
|---|---:|---:|
| `CRTT.BudgetedPruning.Correct` | BudgetedPruning.lean:220 | definition / not individually reported |
| `CRTT.BudgetedPruning.execute_funded_exhausts` | BudgetedPruning.lean:455 | 420 |
| `CRTT.BudgetedPruning.execute_full` | BudgetedPruning.lean:477 | 421 |

## 6.1: continuation

| Lean declaration | Source line | Supplied audit line |
|---|---:|---:|
| `CRTT.ControllerReplacement.Controller` | ControllerReplacement.lean:19 | definition / not individually reported |
| `CRTT.ControllerReplacement.rebaseJob` | ControllerReplacement.lean:25 | definition / not individually reported |
| `CRTT.ControllerReplacement.SameContinuation` | ControllerReplacement.lean:51 | definition / not individually reported |
| `CRTT.ControllerReplacement.rebase_same` | ControllerReplacement.lean:62 | 586 |
| `CRTT.ControllerReplacement.same_correct` | ControllerReplacement.lean:66 | 587 |
| `CRTT.ControllerReplacement.Continuation` | ControllerReplacement.lean:85 | definition / not individually reported |
| `CRTT.ControllerReplacement.Live` | ControllerReplacement.lean:185 | definition / not individually reported |
| `CRTT.ControllerReplacement.remainingBill` | ControllerReplacement.lean:106 | definition / not individually reported |
| `CRTT.ControllerReplacement.completion_full` | ControllerReplacement.lean:108 | 589 |
| `CRTT.ControllerReplacement.completion_bill_le` | ControllerReplacement.lean:113 | 590 |

## 6.2: absolute admission

| Lean declaration | Source line | Supplied audit line |
|---|---:|---:|
| `CRTT.ControllerReplacement.Offer` | ControllerReplacement.lean:126 | definition / not individually reported |
| `CRTT.ControllerReplacement.check` | ControllerReplacement.lean:215 | definition / not individually reported |
| `CRTT.ControllerReplacement.checked_accept_iff` | ControllerReplacement.lean:261 | 595 |
| `CRTT.ControllerReplacement.economic_sound` | ControllerReplacement.lean:151 | 594 |
| `CRTT.ControllerReplacement.chargedFee` | ControllerReplacement.lean:335 | definition / not individually reported |

## 6.2: relative admission

| Lean declaration | Source line | Supplied audit line |
|---|---:|---:|
| `CRTT.RelativeEvidence.RelativeOffer` | RelativeEvidence.lean:66 | definition / not individually reported |
| `CRTT.RelativeEvidence.relativeOK_iff` | RelativeEvidence.lean:21 | 629 |
| `CRTT.RelativeEvidence.coverage_nonempty` | RelativeEvidence.lean:45 | 632 |
| `CRTT.RelativeEvidence.relative_sound` | RelativeEvidence.lean:97 | 638 |
| `CRTT.RelativeEvidence.absolute_gate` | RelativeEvidence.lean:113 | 641 |

## 6.2: verdict and payment

| Lean declaration | Source line | Supplied audit line |
|---|---:|---:|
| `CRTT.AdmissionAccounting.gate` | AdmissionAccounting.lean:24 | definition / not individually reported |
| `CRTT.AdmissionAccounting.gate_accepted_iff` | AdmissionAccounting.lean:32 | 654 |
| `CRTT.AdmissionAccounting.tryRelative` | AdmissionAccounting.lean:160 | definition / not individually reported |
| `CRTT.AdmissionAccounting.applyVerdict` | AdmissionAccounting.lean:146 | definition / not individually reported |
| `CRTT.AdmissionAccounting.apply_same` | AdmissionAccounting.lean:202 | 666 |
| `CRTT.AdmissionAccounting.apply_fees` | AdmissionAccounting.lean:212 | 667 |
| `CRTT.AdmissionAccounting.apply_liquid` | AdmissionAccounting.lean:258 | 673 |
| `CRTT.AdmissionAccounting.apply_charge` | AdmissionAccounting.lean:241 | 671 |
| `CRTT.AdmissionAccounting.apply_funds` | AdmissionAccounting.lean:250 | 672 |
| `CRTT.AdmissionAccounting.apply_accepted_gain` | AdmissionAccounting.lean:263 | 674 |
| `CRTT.AdmissionAccounting.recordEvidence` | AdmissionAccounting.lean:282 | definition / not individually reported |

## 6.3: mixed root histories

| Lean declaration | Source line | Supplied audit line |
|---|---:|---:|
| `CRTT.RecursiveTrace.Preserves` | RecursiveTrace.lean:109 | definition / not individually reported |
| `CRTT.RecursiveTrace.Delta` | RecursiveTrace.lean:155 | definition / not individually reported |
| `CRTT.RecursiveTrace.attemptDelta` | RecursiveTrace.lean:165 | definition / not individually reported |
| `CRTT.RecursiveTrace.Laws` | RecursiveTrace.lean:171 | definition / not individually reported |
| `CRTT.RecursiveTrace.remainingBill_prefix` | RecursiveTrace.lean:74 | 695 |
| `CRTT.RecursiveTrace.advance_objective` | RecursiveTrace.lean:100 | 698 |
| `CRTT.RecursiveTrace.action_laws` | RecursiveTrace.lean:285 | 709 |
| `CRTT.RecursiveTrace.laws_compose` | RecursiveTrace.lean:181 | 705 |
| `CRTT.RecursiveTrace.ValidTrace` | RecursiveTrace.lean:302 | definition / not individually reported |
| `CRTT.RecursiveTrace.trace_laws` | RecursiveTrace.lean:323 | 712 |
| `CRTT.RecursiveTrace.trace_objective` | RecursiveTrace.lean:336 | 713 |
| `CRTT.RecursiveTrace.trace_funds` | RecursiveTrace.lean:340 | 714 |
| `CRTT.RecursiveTrace.trace_preserves` | RecursiveTrace.lean:343 | 715 |
| `CRTT.RecursiveTrace.trace_paid_bound` | RecursiveTrace.lean:346 | 716 |
| `CRTT.RecursiveTrace.finish_bill` | RecursiveTrace.lean:361 | 718 |
| `CRTT.RecursiveTrace.trace_final_gain_iff` | RecursiveTrace.lean:372 | 721 |

## 7.1: policy and upgrade

| Lean declaration | Source line | Supplied audit line |
|---|---:|---:|
| `CRTT.MetaPolicy.Frame` | MetaPolicy.lean:26 | definition / not individually reported |
| `CRTT.MetaPolicy.Provider` | MetaPolicy.lean:53 | definition / not individually reported |
| `CRTT.MetaPolicy.interpret` | MetaPolicy.lean:112 | definition / not individually reported |
| `CRTT.MetaPolicy.interpret_funds` | MetaPolicy.lean:123 | 733 |
| `CRTT.MetaPolicy.interpret_preserves` | MetaPolicy.lean:127 | 734 |
| `CRTT.MetaPolicy.policyBill` | MetaPolicy.lean:136 | definition / not individually reported |
| `CRTT.MetaPolicy.policyBill_complete` | MetaPolicy.lean:139 | 736 |
| `CRTT.MetaPolicy.Machine` | MetaPolicy.lean:159 | definition / not individually reported |
| `CRTT.MetaPolicy.Proposal` | MetaPolicy.lean:166 | definition / not individually reported |
| `CRTT.MetaPolicy.upgrade` | MetaPolicy.lean:186 | definition / not individually reported |
| `CRTT.MetaPolicy.upgrade_funds` | MetaPolicy.lean:205 | 737 |
| `CRTT.MetaPolicy.upgrade_preserves` | MetaPolicy.lean:210 | 738 |
| `CRTT.MetaPolicy.upgrade_history` | MetaPolicy.lean:220 | 740 |
| `CRTT.MetaPolicy.upgrade_gain` | MetaPolicy.lean:214 | 739 |

## 7.2: meta-history

| Lean declaration | Source line | Supplied audit line |
|---|---:|---:|
| `CRTT.MetaClosure.Plan` | MetaClosure.lean:57 | definition / not individually reported |
| `CRTT.MetaClosure.Transition` | MetaClosure.lean:61 | definition / not individually reported |
| `CRTT.MetaClosure.ValidTrace` | MetaClosure.lean:84 | definition / not individually reported |
| `CRTT.MetaClosure.upgrade_facts` | MetaClosure.lean:41 | 753 |
| `CRTT.MetaClosure.trace_laws` | MetaClosure.lean:111 | 755 |
| `CRTT.MetaClosure.trace_paid_balance` | MetaClosure.lean:156 | 756 |
| `CRTT.MetaClosure.trace_liquid` | MetaClosure.lean:165 | 757 |
| `CRTT.MetaClosure.trace_no_rejection_gain` | MetaClosure.lean:191 | 759 |
| `CRTT.MetaClosure.runPlans` | MetaClosure.lean:216 | definition / not individually reported |
| `CRTT.MetaClosure.run_steps` | MetaClosure.lean:227 | 761 |
| `CRTT.MetaClosure.Closed` | MetaClosure.lean:233 | definition / not individually reported |
| `CRTT.MetaClosure.closeRun` | MetaClosure.lean:240 | definition / not individually reported |
| `CRTT.MetaClosure.closed_history` | MetaClosure.lean:280 | 767 |
| `CRTT.MetaClosure.closed_gain` | MetaClosure.lean:274 | 766 |

## 7.3: final release

| Lean declaration | Source line | Supplied audit line |
|---|---:|---:|
| `CRTT.Release.run` | Release.lean:22 | definition / not individually reported |
| `CRTT.Release.runList` | Release.lean:26 | definition / not individually reported |
| `CRTT.Release.result_steps` | Release.lean:70 | 787 |
| `CRTT.Release.result_exhausted` | Release.lean:36 | 780 |
| `CRTT.Release.result_complete` | Release.lean:32 | 779 |
| `CRTT.Release.result_impossible_iff` | Release.lean:56 | 783 |
| `CRTT.Release.result_funds` | Release.lean:60 | 784 |
| `CRTT.Release.result_history` | Release.lean:63 | 785 |
| `CRTT.Release.result_bill` | Release.lean:66 | 786 |
| `CRTT.Release.Witnesses.low_liquidity` | Release.lean:276 | 792 |

## 7.3: canonical representative

| Lean declaration | Source line | Supplied audit line |
|---|---:|---:|
| `CRTT.MorphismDiscovery.discover_complete` | MorphismDiscovery.lean:421 | 309 |

