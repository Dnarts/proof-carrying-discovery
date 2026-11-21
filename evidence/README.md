# Verification evidence

- `verification_receipt.json`: local release-audit outcome for the publication files. Reproduce it with `python3 tests/audit_release.py`.
- `unittest_stdout.txt`: the regression-test log for this publication.
- `publication_patch.json`: the certificate-checker defect observed before v1.1.1, its regression coverage, and a comparison of experimental values before and after the patch.

All checks use the stated Python models. The checks are distinct from a proof-assistant formalization and from an independent laboratory replication. Timing and platform metadata are excluded when comparing deterministic experimental results.

Earlier evidence is retained with its corresponding source files in `legacy/` and the exact predecessor archive in `history/`.
