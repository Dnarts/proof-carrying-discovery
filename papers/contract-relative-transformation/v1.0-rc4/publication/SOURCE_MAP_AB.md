# Source map — Sections 1–5

These locators refer to exact available source bytes. Earlier standalone sources have separate historical proof status and are not imports of the T19–T32 stack. A supporting declaration need not have an individual axiom report. Audit line numbers refer to the supplied successful T32 log, not a new run.

## CRTTCore

`CRTT-T17-T18-v0.1.2-verified.zip / CRTT-v0.2/CRTTCore.lean`. SHA-256: `722aa191c2efcbe114dd3a5d381e3aada2566d519d6d6d10654facc9fa2604ac`.

| Declaration | Source line | Evidence |
|---|---:|---|
| `CRTT.selector_iff` | 27 | Historical source |
| `CRTT.refine_policy` | 52 | Historical source |
| `CRTT.empty_action_barrier` | 129 | Historical source |

## SufficientPartitions

`CRTT-T03-T19-v0.1.2-verified.zip / CRTT-T03-T19-v0.1.1/SufficientPartitions.lean`. SHA-256: `8d6cd092a75d1feff080a8120de40981934d266c261322b85b0aa16170259add`.

| Declaration | Source line | Evidence |
|---|---:|---|
| `CRTT.SufficientPartitions.coarsest_exists_iff` | 106 | Historical source |
| `CRTT.SufficientPartitions.coarsest_contains_compatible` | 93 | Historical source |
| `CRTT.SufficientPartitions.pairMerge_sufficient` | 68 | Historical source |
| `CRTT.SufficientPartitions.triangle_compat_all` | 173 | Historical source |
| `CRTT.SufficientPartitions.triangle_compat_equiv` | 185 | Historical source |
| `CRTT.SufficientPartitions.triangle_no_common_action` | 192 | Historical source |
| `CRTT.SufficientPartitions.triangle_no_coarsest` | 197 | Historical source |
| `CRTT.SufficientPartitions.exact_target_coarsest` | 133 | Historical source |

## CumulativeDiscovery

`CRTT-T17-T18-v0.1.2-verified.zip / CRTT-v0.2/CumulativeDiscovery.lean`. SHA-256: `f80c3e5d0ba96d77ed5e88ad2e4b07afc4f34f00e28c8db58f055a66d5d18915`.

| Declaration | Source line | Evidence |
|---|---:|---|
| `CRTT.Cumulative.budgetReach_monotone` | 131 | Historical source |
| `CRTT.Cumulative.plan_accounting` | 190 | Historical source |
| `CRTT.Cumulative.strict_gain_iff` | 211 | Historical source |
| `CRTT.Cumulative.Witnesses.repeat_not_sufficient` | 267 | Historical source |
| `CRTT.Cumulative.Witnesses.library_bloat_witness` | 287 | Historical source |

## OnlineDiscovery

`CRTT-T17-T18-v0.1.2-verified.zip / CRTT-T17-v0.1/OnlineDiscovery.lean`. SHA-256: `e50748e61533bfe2c1b83298e7021989572fac981a2babf3f33cafa11fc26ae4`.

| Declaration | Source line | Evidence |
|---|---:|---|
| `CRTT.OnlineDiscovery.adversarial_regret` | 36 | Historical source |
| `CRTT.OnlineDiscovery.buyAt_two_competitive` | 188 | Historical source |

## ObservationValue

`CRTT-T17-T18-v0.1.2-verified.zip / CRTT-T18-v0.1/ObservationValue.lean`. SHA-256: `4a0b507aebaff388dfbf9b3fb32db6b416c2c676e0c692029c2294e528ca4ffe`.

| Declaration | Source line | Evidence |
|---|---:|---|
| `CRTT.ObservationValue.portValue` | 95 | Historical source |
| `CRTT.ObservationValue.epsilon_sufficient_iff` | 139 | Historical source |
| `CRTT.ObservationValue.paid_strict_iff` | 183 | Historical source |
| `CRTT.ObservationValue.xor_synergy` | 199 | Historical source |
| `CRTT.ObservationValue.refinement_monotone` | 170 | Historical source |

## AdaptiveObservation

`Accepted T32 / AdaptiveObservation.lean`. SHA-256: `4935dc618d899f294ad60fd6f9599b1e760022cf61a6fc5d0051089db7f8c133`.

| Declaration | Source line | Evidence |
|---|---:|---|
| `CRTT.AdaptiveObservation.Problem` | 96 | Supporting source |
| `CRTT.AdaptiveObservation.Investigation` | 105 | Supporting source |
| `CRTT.AdaptiveObservation.Legal` | 139 | Supporting source |
| `CRTT.AdaptiveObservation.runCost` | 111 | Supporting source |
| `CRTT.AdaptiveObservation.worst_observe` | 147 | T32 log line 184 |
| `CRTT.AdaptiveObservation.solve_legal` | 250 | T32 log line 183 |
| `CRTT.AdaptiveObservation.solve_optimal` | 265 | T32 log line 185 |
| `CRTT.AdaptiveObservation.bellman` | 292 | T32 log line 186 |
| `CRTT.AdaptiveObservation.epsilon_budget_iff` | 417 | T32 log line 189 |
| `CRTT.AdaptiveObservation.adaptive_le_static` | 560 | T32 log line 194 |
| `CRTT.AdaptiveObservation.Witnesses.mux_adaptive_beats_static` | 630 | T32 log line 195 |
| `CRTT.AdaptiveObservation.Witnesses.xor_greedy_failure` | 663 | T32 log line 199 |

## InvestigationTransfer

`Accepted T32 / InvestigationTransfer.lean`. SHA-256: `0fd34692b5f2cbf48b4f9e8b87853804dd1bcd3f52e3021a40215a8fd9037ef6`.

| Declaration | Source line | Evidence |
|---|---:|---|
| `CRTT.InvestigationTransfer.TransferMorphism` | 24 | Supporting source |
| `CRTT.InvestigationTransfer.transfer_legal` | 135 | T32 log line 205 |
| `CRTT.InvestigationTransfer.transfer_runCost_le` | 194 | T32 log line 207 |
| `CRTT.InvestigationTransfer.transfer_hard_contract` | 214 | T32 log line 209 |
| `CRTT.InvestigationTransfer.transfer_semantics` | 154 | T32 log line 206 |
| `CRTT.InvestigationTransfer.optimum_le` | 228 | T32 log line 210 |
| `CRTT.InvestigationTransfer.mutual_optimum_eq` | 237 | T32 log line 211 |
| `CRTT.InvestigationTransfer.transfer_compose` | 300 | T32 log line 216 |
| `CRTT.InvestigationTransfer.Witnesses.equal_optimum_no_global_morphism` | 385 | T32 log line 222 |
| `CRTT.InvestigationTransfer.Witnesses.equal_optimum_no_loss_morphism` | 406 | T32 log line 223 |

## InvestigationLibrary

`Accepted T32 / InvestigationLibrary.lean`. SHA-256: `1b3f30c633fb14240dc5a6304bb7e9900df05b0147becb0fea8a2db5b509967d`.

| Declaration | Source line | Evidence |
|---|---:|---|
| `CRTT.InvestigationLibrary.paid_candidate_iff` | 236 | T32 log line 251 |
| `CRTT.InvestigationLibrary.search_profitable_iff` | 357 | T32 log line 263 |
| `CRTT.InvestigationLibrary.best_le_fresh` | 301 | T32 log line 256 |
| `CRTT.InvestigationLibrary.best_le_candidate` | 305 | T32 log line 257 |
| `CRTT.InvestigationLibrary.complete_search_matches_oracle` | 407 | T32 log line 265 |
| `CRTT.InvestigationLibrary.amortization_iff` | 502 | T32 log line 270 |

## MorphismDiscovery

`Accepted T32 / MorphismDiscovery.lean`. SHA-256: `c3f5305f049c38e4809ce19d243b5133755fc3cefdbd3868c43db1570a41127a`.

| Declaration | Source line | Evidence |
|---|---:|---|
| `CRTT.MorphismDiscovery.IndexedTask` | 147 | Supporting source |
| `CRTT.MorphismDiscovery.fixed_pair_iff` | 370 | T32 log line 306 |
| `CRTT.MorphismDiscovery.portOK_iff` | 196 | T32 log line 294 |
| `CRTT.MorphismDiscovery.worldWitness_sound` | 284 | T32 log line 298 |
| `CRTT.MorphismDiscovery.worldWitness_complete` | 292 | T32 log line 299 |
| `CRTT.MorphismDiscovery.discover_complete` | 421 | T32 log line 309 |
| `CRTT.MorphismDiscovery.empty_iff_no_morphism` | 439 | T32 log line 310 |
| `CRTT.MorphismDiscovery.transfer_eq_of_maps` | 484 | T32 log line 315 |

## BudgetedDiscovery

`Accepted T32 / BudgetedDiscovery.lean`. SHA-256: `5198b6cb269696318633300777233e063cb03d7ef2a69588041bb262b9a22817`.

| Declaration | Source line | Evidence |
|---|---:|---|
| `CRTT.BudgetedDiscovery.QuotedStep` | 7 | Supporting source |
| `CRTT.BudgetedDiscovery.Account` | 12 | Supporting source |
| `CRTT.BudgetedDiscovery.run` | 21 | Supporting source |
| `CRTT.BudgetedDiscovery.execute` | 564 | Supporting source |
| `CRTT.BudgetedDiscovery.accounting` | 31 | T32 log line 326 |
| `CRTT.BudgetedDiscovery.invariant` | 93 | T32 log line 329 |
| `CRTT.BudgetedDiscovery.budget_bound` | 87 | T32 log line 328 |
| `CRTT.BudgetedDiscovery.run_stuck_of_ge_budget` | 513 | T32 log line 347 |

## ResumeLaws

`Accepted T32 / ResumeLaws.lean`. SHA-256: `a0e87b5e8d0c3c7c03cf5480dea11e51322d9d91c8395bf0dbd911c1fa5c6e9e`.

| Declaration | Source line | Evidence |
|---|---:|---|
| `CRTT.ResumeLaws.execute_topUp_add` | 77 | T32 log line 395 |
| `CRTT.ResumeLaws.execute_topUp_prefix` | 44 | T32 log line 394 |

## CertifiedPruning

`Accepted T32 / CertifiedPruning.lean`. SHA-256: `f6bbb4250a12237a9d4af6fe13d1b896855279b5acdf9b849c92494c251fd82e`.

| Declaration | Source line | Evidence |
|---|---:|---|
| `CRTT.CertifiedPruning.CertifiedRule` | 72 | Supporting source |
| `CRTT.CertifiedPruning.prunedDiscover_iff` | 367 | T32 log line 374 |
| `CRTT.CertifiedPruning.pruning_profitable_iff` | 400 | T32 log line 386 |
| `CRTT.CertifiedPruning.composeRule` | 147 | T32 log line 382 |
| `CRTT.CertifiedPruning.ordered_rule_cost_iff` | 426 | T32 log line 365 |

## BudgetedPruning

`Accepted T32 / BudgetedPruning.lean`. SHA-256: `ef49185bcd784a3dd475941f8cb4d8525b2a1b515f0769ec2035865c094e245b`.

| Declaration | Source line | Evidence |
|---|---:|---|
| `CRTT.BudgetedPruning.Correct` | 220 | Supporting source |
| `CRTT.BudgetedPruning.quote_potential` | 408 | T32 log line 417 |
| `CRTT.BudgetedPruning.execute_funded_exhausts` | 455 | T32 log line 420 |
| `CRTT.BudgetedPruning.execute_full` | 477 | T32 log line 421 |
| `CRTT.BudgetedPruning.execute_certificate_prefix` | 522 | T32 log line 425 |
| `CRTT.BudgetedPruning.exhausted_impossible` | 279 | T32 log line 410 |
| `CRTT.BudgetedPruning.classify` | 546 | T32 log line 427 |

## ImpasseCompilation

`Accepted T32 / ImpasseCompilation.lean`. SHA-256: `6b832a624d0f5ac8815a3057b1528aff22422101b174b8aa38dd78668fd103a5`.

| Declaration | Source line | Evidence |
|---|---:|---|
| `CRTT.ImpasseCompilation.shrink_spec` | 32 | T32 log line 432 |
| `CRTT.ImpasseCompilation.extract` | 142 | T32 log line 436 |
| `CRTT.ImpasseCompilation.core_excludes` | 186 | T32 log line 438 |
| `CRTT.ImpasseCompilation.compileCore_rejects` | 202 | T32 log line 440 |
| `CRTT.ImpasseCompilation.containsCore_iff` | 174 | T32 log line 437 |
| `CRTT.ImpasseCompilation.transportCore` | 269 | T32 log line 444 |

## LearningDiscovery

`Accepted T32 / LearningDiscovery.lean`. SHA-256: `0af0630db289932e11e5e23271c777be9617e77ce4e7a9c260a8a9dcc1bc1dc6`.

| Declaration | Source line | Evidence |
|---|---:|---|
| `CRTT.LearningDiscovery.LearnedEvent` | 90 | Supporting source |
| `CRTT.LearningDiscovery.State` | 98 | Supporting source |
| `CRTT.LearningDiscovery.insertCore_rejects` | 31 | T32 log line 452 |
| `CRTT.LearningDiscovery.execute_correct` | 307 | T32 log line 462 |
| `CRTT.LearningDiscovery.execute_trace` | 301 | T32 log line 461 |
| `CRTT.LearningDiscovery.execute_split` | 313 | T32 log line 463 |
| `CRTT.LearningDiscovery.execute_exhausted_iff` | 318 | T32 log line 464 |

## MetaInvestigation

`Accepted T32 / MetaInvestigation.lean`. SHA-256: `dea72dcb1b7294a65617f0e078c79cf7e8f30a4d75e97304d795b9bf11f49a59`.

| Declaration | Source line | Evidence |
|---|---:|---|
| `CRTT.MetaInvestigation.Plan` | 39 | Supporting source |
| `CRTT.MetaInvestigation.Funded` | 69 | Supporting source |
| `CRTT.MetaInvestigation.runPlan` | 76 | Supporting source |
| `CRTT.MetaInvestigation.perform_complete` | 216 | T32 log line 478 |
| `CRTT.MetaInvestigation.perform_accounting` | 242 | T32 log line 481 |
| `CRTT.MetaInvestigation.perform_static` | 222 | T32 log line 479 |
| `CRTT.MetaInvestigation.actualBill_le_reservation` | 280 | T32 log line 483 |
| `CRTT.MetaInvestigation.runMeta_bill` | 398 | T32 log line 488 |
| `CRTT.MetaInvestigation.optimizer_bound_optimal` | 444 | T32 log line 494 |
| `CRTT.MetaInvestigation.optimizer_actual_optimal` | 449 | T32 log line 495 |
| `CRTT.MetaInvestigation.acquisition_gain_iff` | 478 | T32 log line 498 |

## MetaEvidenceAcquisition

`Accepted T32 / MetaEvidenceAcquisition.lean`. SHA-256: `fd4177f489f241782b160b4b5a31c6439e3d3f617e7f69982ca5a4f534e64ef2`.

| Declaration | Source line | Evidence |
|---|---:|---|
| `CRTT.MetaEvidenceAcquisition.Bounds` | 18 | Supporting source |
| `CRTT.MetaEvidenceAcquisition.certified_gap` | 185 | T32 log line 517 |
| `CRTT.MetaEvidenceAcquisition.gap_monotone` | 196 | T32 log line 518 |
| `CRTT.MetaEvidenceAcquisition.lower_le_true` | 158 | T32 log line 513 |
| `CRTT.MetaEvidenceAcquisition.true_le_upper` | 165 | T32 log line 514 |
| `CRTT.MetaEvidenceAcquisition.assess_complete` | 248 | T32 log line 521 |
| `CRTT.MetaEvidenceAcquisition.quote_meter` | 321 | T32 log line 523 |
| `CRTT.MetaEvidenceAcquisition.quote_info` | 333 | T32 log line 524 |
| `CRTT.MetaEvidenceAcquisition.execute_funded_quiescent` | 385 | T32 log line 526 |

## DecisionEvidence

`Accepted T32 / DecisionEvidence.lean`. SHA-256: `06fe11cbfacae3b7ea5e3a2cbd8455963f374412ef169af26d953a7d79840d87`.

| Declaration | Source line | Evidence |
|---|---:|---|
| `CRTT.DecisionEvidence.Model` | 15 | Supporting source |
| `CRTT.DecisionEvidence.residual_iff` | 63 | T32 log line 545 |
| `CRTT.DecisionEvidence.catalogue_robust_iff` | 102 | T32 log line 549 |
| `CRTT.DecisionEvidence.residual_subset` | 80 | T32 log line 547 |
| `CRTT.DecisionEvidence.refine_truth` | 258 | T32 log line 559 |
| `CRTT.DecisionEvidence.acquisition_optimal` | 279 | T32 log line 562 |
| `CRTT.DecisionEvidence.acquisition_bellman` | 288 | T32 log line 564 |
| `CRTT.DecisionEvidence.total_bill_identity` | 340 | T32 log line 568 |
| `CRTT.DecisionEvidence.hard_assess_complete` | 381 | T32 log line 571 |
| `CRTT.DecisionEvidence.hard_minimal_observation` | 438 | T32 log line 574 |
| `CRTT.DecisionEvidence.hard_execution` | 397 | T32 log line 572 |

