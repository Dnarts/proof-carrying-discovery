# Independent reproduction checklist

The canonical formal artifact is unchanged. This manuscript supplement provides a clean-extraction wrapper, not a new theorem or replacement verifier. Its input is the exact `CRTT-v1.0-FULL-ARCHITECTURE-RECONCILED.zip` whose SHA-256 is printed in Section 8.3.

1. Obtain the exact archive and the pinned Lean toolchain (`leanprover/lean4:v4.36.0`, compiler commit `611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9`). Make `lean` available on PATH and use Python 3 and Bash. The canonical runner enforces the exact version and commit.
2. From the extracted manuscript package, run:

   ```bash
   bash supplement/verify_fresh.sh /absolute/path/CRTT-v1.0-FULL-ARCHITECTURE-RECONCILED.zip ../fresh-lean-evidence
   ```

   The output directory must not exist. The script verifies the archive hash, extracts into a private temporary directory, checks the full archive manifest and calls the unchanged canonical `run_verify.sh`. Logs are kept outside the canonical directory. The exit status of the actual runner is preserved; success requires both zero exit status and the final full-run marker. The temporary extraction is removed on exit. No supplied log is substituted for compiler output.
3. Retain the complete output directory, including `ENVIRONMENT.log`, `EXTRACTION.log`, `ARCHIVE_CHECK.log`, `FRESH_KERNEL_CHECK.log`, `RUNNER_EXIT.txt`, and `STATUS.json`. Check `fresh_kernel_verification_passed` and `exit_code` in `STATUS.json`. Do not edit the successful transcript. Have an independent reviewer or CI runner perform this same procedure and publish the evidence with its environment and artifact identity.
4. Deposit the unchanged formal archive, its SHA-256, and independently generated verification evidence as supplementary research software on a persistent repository. Record the actual version-specific DOI after it is issued and update the manuscript artifact reference accordingly; a draft or a guessed identifier is not publication evidence.

## RC4 local check

The wrapper is syntax-checked and actually exercised in the current assembly environment. See `local_attempt/` for the resulting evidence. No Lean executable is present here; the runner correctly stops before compilation. The supplied successful transcript and prior Python replay retain their previous evidence status. A fresh independent Lean run and DOI remain outstanding.
