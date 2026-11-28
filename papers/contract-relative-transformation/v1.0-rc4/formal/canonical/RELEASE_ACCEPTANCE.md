# T32 — final acceptance and freeze

The mathematical closure gate T31 has passed in the supplied parent log. The
following is the finite release contract; its scope cannot grow silently.

| Condition | RC1 state | Final witness |
|---|---|---|
| Inherited source identity | PASS 19/19 | UPSTREAM_SHA256.txt + actual compile |
| Parent audit | PASS 524/524 replay | T31_KERNEL_CHECK.log |
| Entire package integrity | PASS locally, repeat required | verify_integrity.py |
| Exact compiler and full strict audit | PENDING | run_verify.sh exit 0; 542 reports |
| Unified execution | Source candidate | Release.run / runList and actual CLI |
| Canonical completeness and exhaustion | Verified in T31/T28; wrapper pending | result_complete/result_exhausted |
| Impossibility vs completion | Wrapper pending; 9 finite cases pass | result_impossible_iff and actual CLI |
| Resource conservation and provenance | Verified in T31; wrapper pending | result_funds/result_history/summary_conserved |
| Nontrivial positive & negative cases | Python PASS, new Lean pending | FINITE_RELEASE.json + actual output |
| Independent runtime projection comparison | Parser controls PASS, actual Lean pending | check_release.py --lean-log |

Only after all mandatory checks pass, freeze the exact accepted package and
archive the actual compiler/runtime log as a separately hashed witness. Do
not overwrite manifest-covered logs or edit verified source to change the
meaning of an earlier theorem. Correct integration bugs by a new T32 revision
with an explicit repair record. No new architecture phase. A new scope or
external application is a separate research question, not a release blocker.
