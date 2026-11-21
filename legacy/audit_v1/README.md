# InvariantNet v1.0 — verification addendum

Start with `REVIEW.ru.md`. Original v1.0 uploads are preserved unchanged in `original/`.

`audit_release_v1.py` re-executes the uploaded sources, compares deterministic output, independently tests emitted Boolean gate circuits, reconstructs pairwise distinguishing suffixes, checks four recognizers over all strings of length 0–8 in `{0,1,$}`, and runs two adversarial checks: finite-teacher indistinguishability and wrong transferred law. It also calculates conditional Shapley scores under a different (still partial) acquisition-cost convention for sensitivity analysis.

## Run

```bash
python3 audit_release_v1.py
```

The script reads four immutable sources from `original/` next to itself. It also supports the original four uploads in `/mnt/data`. No external dependencies are used.

`audit_checks.json`, `gate_witnesses.json`, `mn_pair_witnesses.json` are the already executed audit outputs. The `SHA256SUMS.txt` and `MANIFEST.json` are integrity indices. File names and predicates in the review are scoped to this specific upload; this is not an external laboratory replication.
