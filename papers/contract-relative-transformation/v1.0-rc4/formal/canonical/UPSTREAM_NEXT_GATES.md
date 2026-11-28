# T23 continuation — proof obligations, not claims of implementation

## 1. Incremental constraints

Given a partial port map rho with compatibility rows B_rho(x), extending it by q -> t changes the row by intersection:

B_(rho + (q,t))(x) = {y in B_rho(x) | target.read(t,x) = source.read(q,y)}.

An exact incremental update can avoid reevaluating prior constraints. Prove cached rows equal the denotation after every transition. A cached empty row proves the entire region empty; cache misses are not obstructions. Costs must include update, storage, and any reuse/lookup.

For an unassigned source port q, define D_rho(q) to contain only unused target ports satisfying price and the one-more-port read compatibility condition. Every full morphism extending rho must map q into D_rho(q). Thus if a subset J of unassigned source ports has |union_(q in J) D_rho(q)| < |J|, then no injective extension exists (Hall obstruction). A witness subset is sufficient to reject the whole region. Computing such witnesses is not yet implemented. Passing the matching test does not prove a morphism exists.

For partial action maps, refine the same rows by the terminal-loss constraints. Do not conflate independent per-action feasibility with joint feasibility. Example: candidate source worlds y0,y1 with source losses (1,0) and (0,1) over two source actions; target losses for the mapped actions are both 1. Each individual loss condition has a witness, but no common witness exists. No injectivity of actionMap is required by T20.

## 2. T23.5 — paid frontier, not an eager list of survivors

Reuse BudgetedDiscovery.Account, QuotedStep, run, execute and accounting. Define a new frontier cursor with an incremental child generator; no full list of port assignments, action assignments, or certificates may be computed by the quote stage. Charge the actual abstract elementary operation (including rule evaluation, node splitting, local witness checks, and finishing a candidate). If a single step generates an entire child list, either charge that generation or split it into elementary transitions. Positive fixed tariffs are sufficient for the generic budget-as-fuel theorem. Changing the order of rules between resumes changes the transition system and invalidates the existing exact split-budget theorem unless additional hypotheses are proved.

Proposed state:

- stack of disjoint regions represented by partial maps and next-child indices;
- per-region cached rows and rule cursor;
- canonical certificates already emitted;
- proof-carrying exclusion receipts (or erased proofs with a checkable replay log);
- resource account and a monotone incumbent.

Proof targets:

- frontier coverage: original certificate membership iff in emitted certificates or some remaining region;
- scoped rejection: a removed region has no valid extension;
- split: parent denotation = union of disjoint children; include the empty-carrier cases;
- no silent loss: an unaffordable quote leaves the state and budget unchanged;
- certificate prefix and exact composition for fixed deterministic policy;
- sufficient abstract budget implies exhaustive reference membership;
- negative verdict only on certified exhaustion;
- early optimum relative to every remaining region's certified lower bound.

An all-certificate denotation belongs to specification/proofs only, not to the executable budgeted runner.

## 3. T23.6–T23.9 — actual trace and policy economics

For a fully executed policy pi, measure the symbolic cost from its actual paid transition trace, including failed tests. The trace equation must connect the accountant's spent delta to the sum of fees. The current source contains only uniform-node arithmetic and a fixed-collection ordering criterion. The current Python stand counts the costs it actually models, but does not prove the Lean implementation's trace.

Two pure rules A,B on the same N regions pass nA,nB regions respectively. Under constant fees cA,cB, the short-circuit bills are N*cA+nA*cB and N*cB+nB*cA. Let rA=N-nA, rB=N-nB. A-first is strictly cheaper iff rB*cA < rA*cB. Positive fees allow a rejection-per-cost comparison. This does not assume free knowledge of future counts. With more rules, the relevant region collection is conditional on earlier passes; a fixed global rank need not be optimal. Rule availability, evaluation, scheduling, and estimation all require cost accounting.

Do not force every rule in a library to run. Empty policy and original reference policy must remain admissible. For free optional choice and fixed charges, more options cannot worsen the best policy value; with mandatory scans or discovery costs the T21 bloat counterexample reappears. Test per-instance regret and aggregate savings separately.

## 4. T24 — transfer of search policy (new hypothesis)

Separate a certified pruning schema (a proof-producing family applicable across task pairs) from a task-specific CertifiedRule. A schema has a parameter/interface contract, a rule constructor, a soundness theorem, and a charged application model. Only then can reuse of a *method of discovery* be distinguished from reusing a single task-specific Boolean predicate.

Treat policy selection as a higher-level investigation. T19 can optimize a finite, explicitly specified meta-task of deciding which rule to test or whether to split, but that requires a definition of meta-worlds, admissible observations, loss and paid transitions. The present T23 module does not provide that reduction. No computational speedup or novelty claim follows from the hierarchy alone.
