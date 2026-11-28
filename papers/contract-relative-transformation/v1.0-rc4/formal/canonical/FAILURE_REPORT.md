# Historical failed T29-v0.1: report and repair boundary

Source of diagnosis: user-provided Hermes report immediately preceding this
revision. This is a record of that report, not an independently replayed raw
compiler log. The previous generated ZIP is not mounted in this environment.
The report states that the 14 inherited modules compiled cleanly; T28's
ControllerReplacement produced all 43 requested reports. RecursiveAdmission
had 78 compile errors and 18 reports of sorryAx attributed to elaboration
failures rather than explicit placeholders. The source before the first
reported failing theorem (around line 310) was reported to compile.

Three reported clusters:
1. check_accepted_iff: dependent match on the boolean check of correlated rows,
   causing proof-dependent reduction problems in the verdict equivalence.
2. apply_charge / apply_funds: insufficiently explicit equality connecting the
   proposed installed reserve and the candidate reserve, and relating journal
   charge to validation + migration in the accepted branch.
3. Step / Chain: dependent case elimination with a computed endpoint index
   (tryRelative ...).2. The attempted cases patterns no longer matched the
   eliminator-generated binders.

Assessment: failure of compilation is a blocker; it is not a mathematical
counterexample. The arithmetic implications and continuation semantics remain
research obligations until the new gate is checked. No change to T28.

T29a reconstructs only the relative-evidence layer, using the source shown in
the earlier conversation, not the original failed file bytes. It moves that
layer into namespace CRTT.RelativeEvidence, retains Candidate and RelativeOffer
with joint actual coverage, and makes the reserve and absolute embedding
boundary explicit. It adds the general empty-coverage lemma and finite positive
and negative witnesses. It omits (defers, rather than silently certifies) the
runtime and history layer. The generic prefix-accounting lemma from old T29
is deferred to T29c. The original failed T29 should remain immutable in its
original environment. No claim is made that its errors have been fixed in place.
