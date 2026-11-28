import DecisionEvidence

/-! T28: independently admitted replacement of a live, funded T23 controller.
The root indexed tasks are fixed by the types. A proposal can rebase the
pending rule queues, not change the underlying regions, certificates or trace.
Cost bounds are supplied proof-carrying data; the admission code never computes
full prospective runs. The interface models abstract charges, not CPU or RAM.
No arbitrary program rewrite or untrusted proof parser is claimed. -/
namespace CRTT.ControllerReplacement
open CRTT.MorphismDiscovery CRTT.BudgetedDiscovery
open CRTT.CertifiedPruning (RuleLibrary)
open CRTT.BudgetedPruning (Job Frontier Correct Covers Covered receiptCost)
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

variable {sw sp sa tw tp ta : Nat}
variable (S : IndexedTask sw sp sa) (T : IndexedTask tw tp ta)

structure Controller where
  rules : RuleLibrary S T
  fees : CRTT.BudgetedPruning.Fees

/-- Reset the rule cursor only, even on an already partially checked region.
All action jobs, including their unprocessed suffix, are unchanged. -/
def rebaseJob (rules : RuleLibrary S T) : Job S T → Job S T
  | .ports qs rho _ => .ports qs rho rules
  | .actions p acts => .actions p acts

def rebase (rules : RuleLibrary S T) (f : Frontier S T) : Frontier S T :=
  { f with jobs := f.jobs.map (rebaseJob S T rules) }

theorem covers_rebaseJob (rules : RuleLibrary S T) (m : Morphism S T) (j : Job S T) :
    Covers S T m (rebaseJob S T rules j) ↔ Covers S T m j := by
  cases j <;> exact Iff.rfl

theorem covered_rebase (rules : RuleLibrary S T) (f : Frontier S T) (m : Morphism S T) :
    Covered S T m (rebase S T rules f).jobs ↔ Covered S T m f.jobs := by
  constructor
  · rintro ⟨j, hj, hc⟩
    change j ∈ f.jobs.map (rebaseJob S T rules) at hj
    obtain ⟨k, hk, he⟩ := List.mem_map.mp hj
    subst j
    exact ⟨k, hk, (covers_rebaseJob S T rules m k).mp hc⟩
  · rintro ⟨j, hj, hc⟩
    refine ⟨rebaseJob S T rules j, ?_, (covers_rebaseJob S T rules m j).mpr hc⟩
    change rebaseJob S T rules j ∈ f.jobs.map (rebaseJob S T rules)
    exact List.mem_map.mpr ⟨j, hj, rfl⟩

/-- Stronger than final-answer equivalence: the unresolved denotation is
unchanged, and the old certificate and receipt lists survive exactly. -/
def SameContinuation (f g : Frontier S T) : Prop :=
  g.certificates = f.certificates ∧ g.receipts = f.receipts ∧
    ∀ m : Morphism S T, Covered S T m g.jobs ↔ Covered S T m f.jobs

theorem same_refl (f : Frontier S T) : SameContinuation S T f f :=
  ⟨rfl, rfl, fun _ => Iff.rfl⟩

theorem same_trans (f g h : Frontier S T) (a : SameContinuation S T f g)
    (b : SameContinuation S T g h) : SameContinuation S T f h :=
  ⟨b.1.trans a.1, b.2.1.trans a.2.1, fun m => (b.2.2 m).trans (a.2.2 m)⟩

theorem rebase_same (rules : RuleLibrary S T) (f : Frontier S T) :
    SameContinuation S T f (rebase S T rules f) :=
  ⟨rfl, rfl, covered_rebase S T rules f⟩

theorem same_correct (f g : Frontier S T) (hf : Correct S T f)
    (h : SameContinuation S T f g) : Correct S T g := by
  constructor
  · intro m hm
    rw [h.1] at hm
    exact hf.1 m hm
  · intro m hm
    rcases hf.2 m hm with hc | hp
    · left
      rw [h.1]
      exact hc
    · exact Or.inr ((h.2.2 m).mpr hp)

theorem rebase_correct (rules : RuleLibrary S T) (f : Frontier S T) (hf : Correct S T f) :
    Correct S T (rebase S T rules f) :=
  same_correct S T f _ hf (rebase_same S T rules f)

/-- A continuation includes a supplied sufficient reserve, not a paid bill.
The potential is a proposition-side bound and is not recomputed on admission. -/
structure Continuation where
  controller : Controller S T
  frontier : Frontier S T
  correct : Correct S T frontier
  reserve : Nat
  funded : CRTT.BudgetedPruning.potential S T controller.rules controller.fees frontier ≤ reserve

def rebased (old : Continuation S T) (new : Controller S T) (reserve : Nat)
    (h : CRTT.BudgetedPruning.potential S T new.rules new.fees
      (rebase S T new.rules old.frontier) ≤ reserve) : Continuation S T :=
  ⟨new, rebase S T new.rules old.frontier,
    rebase_correct S T new.rules old.frontier old.correct, reserve, h⟩

def input (c : Continuation S T) : Account (Frontier S T) := ⟨c.frontier, c.reserve, 0⟩

def prefixRun (c : Continuation S T) (n : Nat) : Account (Frontier S T) :=
  run (CRTT.BudgetedPruning.quote S T c.controller.rules c.controller.fees) n (input S T c)

def completion (c : Continuation S T) : Account (Frontier S T) :=
  prefixRun S T c c.reserve

def remainingBill (c : Continuation S T) : Nat := (completion S T c).spent

theorem completion_full (c : Continuation S T) (m : Morphism S T) :
    m ∈ (completion S T c).state.certificates ↔ m ∈ discoverAll S T :=
  CRTT.BudgetedPruning.execute_full S T c.controller.rules c.controller.fees
    (input S T c) c.correct c.funded m

theorem completion_bill_le (c : Continuation S T) : remainingBill S T c ≤ c.reserve := by
  have h := budget_bound (CRTT.BudgetedPruning.quote S T c.controller.rules c.controller.fees)
    c.reserve (input S T c)
  simpa [remainingBill, completion, prefixRun, input] using h

theorem completion_same_answers (c d : Continuation S T) (m : Morphism S T) :
    m ∈ (completion S T c).state.certificates ↔ m ∈ (completion S T d).state.certificates :=
  (completion_full S T c m).trans (completion_full S T d m).symm

/-- A proposal is indexed by the exact old continuation. A stale certificate
about a different frontier is not a certificate at this type. EvidenceLabel
is provenance metadata, not an authenticity claim. The bounds are relative
only to the two complete static continuations, not arbitrary algorithms. -/
structure Offer (old : Continuation S T) where
  newController : Controller S T
  sameBaseFees : newController.fees = old.controller.fees
  reserve : Nat
  reserveSound : CRTT.BudgetedPruning.potential S T newController.rules newController.fees
    (rebase S T newController.rules old.frontier) ≤ reserve
  migration : Nat
  oldLower : Nat
  newUpper : Nat
  oldLowerSound : oldLower ≤ remainingBill S T old
  newUpperSound : remainingBill S T (rebased S T old newController reserve reserveSound) ≤ newUpper
  evidenceLabel : String

def proposed (old : Continuation S T) (o : Offer S T old) : Continuation S T :=
  rebased S T old o.newController o.reserve o.reserveSound

theorem proposed_fees (old : Continuation S T) (o : Offer S T old) :
    (proposed S T old o).controller.fees = old.controller.fees := o.sameBaseFees

theorem proposed_same (old : Continuation S T) (o : Offer S T old) :
    SameContinuation S T old.frontier (proposed S T old o).frontier :=
  rebase_same S T o.newController.rules old.frontier

/-- Prospective charges include validation and migration. Old paid history is
sunk for this comparison but remains in the actual ledger. -/
theorem economic_sound (old : Continuation S T) (o : Offer S T old) (checkFee : Nat)
    (h : checkFee + o.migration + o.newUpper < o.oldLower) :
    checkFee + o.migration + remainingBill S T (proposed S T old o) < remainingBill S T old := by
  have hu : remainingBill S T (proposed S T old o) ≤ o.newUpper := o.newUpperSound
  have hl := o.oldLowerSound
  omega

inductive RejectReason where
  | liquidity | economics
  deriving Repr, DecidableEq

inductive ReceiptStatus where
  | rejected (reason : RejectReason)
  | committed
  deriving Repr, DecidableEq

structure AttemptReceipt where
  old : Continuation S T
  proposal : Offer S T old
  balanceBefore : Nat
  checkFee : Nat
  status : ReceiptStatus

def attemptCharge (r : AttemptReceipt S T) : Nat :=
  r.checkFee + (match r.status with
  | .rejected _ => 0
  | .committed => r.proposal.migration)

def historyCost : List (AttemptReceipt S T) → Nat
  | [] => 0
  | r :: rs => attemptCharge S T r + historyCost rs

/-- The old controller is always funded. A failed replacement cannot take
away the incumbent's ability to discharge the remaining root obligations. -/
structure Live where
  current : Continuation S T
  balance : Nat
  history : List (AttemptReceipt S T)
  liquid : current.reserve ≤ balance

def spent (s : Live S T) : Nat :=
  receiptCost s.current.frontier.receipts + historyCost S T s.history

def totalFunds (s : Live S T) : Nat := s.balance + spent S T s

def openLive (c : Continuation S T) (balance : Nat) (h : c.reserve ≤ balance) : Live S T :=
  ⟨c, balance, [], h⟩

/-- These are *separate* guards. A cheaper continuation can be illiquid; an
affordable continuation can be more expensive. Validation must be affordable
while retaining the old fallback reserve, even before considering acceptance. -/
inductive Admission (s : Live S T) (o : Offer S T s.current) (checkFee : Nat) where
  | deferred (h : ¬ checkFee + s.current.reserve ≤ s.balance)
  | rejectLiquidity (checked : checkFee + s.current.reserve ≤ s.balance)
      (h : ¬ checkFee + o.migration + o.reserve ≤ s.balance)
  | rejectGain (checked : checkFee + s.current.reserve ≤ s.balance)
      (funded : checkFee + o.migration + o.reserve ≤ s.balance)
      (h : ¬ checkFee + o.migration + o.newUpper < o.oldLower)
  | accepted (checked : checkFee + s.current.reserve ≤ s.balance)
      (funded : checkFee + o.migration + o.reserve ≤ s.balance)
      (gain : checkFee + o.migration + o.newUpper < o.oldLower)

/-- Numeric gate only; proof-bearing Offer is already kernel-typed. No calls
to completion, potential, or a candidate predicate occur in this checker. -/
def check (s : Live S T) (o : Offer S T s.current) (checkFee : Nat) :
    Admission S T s o checkFee :=
  if hc : checkFee + s.current.reserve ≤ s.balance then
    if hl : checkFee + o.migration + o.reserve ≤ s.balance then
      if hg : checkFee + o.migration + o.newUpper < o.oldLower then
        .accepted hc hl hg
      else .rejectGain hc hl hg
    else .rejectLiquidity hc hl
  else .deferred hc

inductive Verdict where
  | deferred | rejectLiquidity | rejectGain | accepted
  deriving DecidableEq, Repr

def verdict {s : Live S T} {o : Offer S T s.current} {fee : Nat} : Admission S T s o fee → Verdict
  | .deferred _ => .deferred
  | .rejectLiquidity _ _ => .rejectLiquidity
  | .rejectGain _ _ _ => .rejectGain
  | .accepted _ _ _ => .accepted

private def rejected (s : Live S T) (o : Offer S T s.current) (fee : Nat)
    (why : RejectReason) (hc : fee + s.current.reserve ≤ s.balance) : Live S T :=
  ⟨s.current, s.balance - fee, ⟨s.current, o, s.balance, fee, .rejected why⟩ :: s.history, by omega⟩

private def committed (s : Live S T) (o : Offer S T s.current) (fee : Nat)
    (hl : fee + o.migration + o.reserve ≤ s.balance) : Live S T :=
  ⟨proposed S T s.current o, s.balance - (fee + o.migration),
    ⟨s.current, o, s.balance, fee, .committed⟩ :: s.history, by
      change o.reserve ≤ s.balance - (fee + o.migration)
      omega⟩

def applyAdmission (s : Live S T) (o : Offer S T s.current) (fee : Nat) :
    Admission S T s o fee → Live S T
  | .deferred _ => s
  | .rejectLiquidity hc _ => rejected S T s o fee .liquidity hc
  | .rejectGain hc _ _ => rejected S T s o fee .economics hc
  | .accepted _ hl _ => committed S T s o fee hl

/-- The public attempt charges a positive validation price (baseCheck + 1).
The same decision object controls commitment; it cannot be recomputed from
an altered continuation. -/
def tryReplace (s : Live S T) (o : Offer S T s.current) (baseCheck : Nat) : Verdict × Live S T :=
  let fee := baseCheck + 1
  let d := check S T s o fee
  (verdict S T d, applyAdmission S T s o fee d)

theorem checked_accept_iff (s : Live S T) (o : Offer S T s.current) (fee : Nat) :
    verdict S T (check S T s o fee) = .accepted ↔
      fee + s.current.reserve ≤ s.balance ∧
      fee + o.migration + o.reserve ≤ s.balance ∧
      fee + o.migration + o.newUpper < o.oldLower := by
  by_cases hc : fee + s.current.reserve ≤ s.balance
  · by_cases hl : fee + o.migration + o.reserve ≤ s.balance
    · by_cases hg : fee + o.migration + o.newUpper < o.oldLower
      · simp [check, hc, hl, hg, verdict]
      · simp [check, hc, hl, hg, verdict]
    · simp [check, hc, hl, verdict]
  · simp [check, hc, verdict]

theorem apply_same (s : Live S T) (o : Offer S T s.current) (fee : Nat)
    (d : Admission S T s o fee) :
    SameContinuation S T s.current.frontier (applyAdmission S T s o fee d).current.frontier := by
  cases d with
  | deferred _ => exact same_refl S T _
  | rejectLiquidity _ _ => exact same_refl S T _
  | rejectGain _ _ _ => exact same_refl S T _
  | accepted _ _ _ => exact proposed_same S T s.current o

theorem apply_nonaccepted_current (s : Live S T) (o : Offer S T s.current) (fee : Nat)
    (d : Admission S T s o fee) (h : verdict S T d ≠ .accepted) :
    (applyAdmission S T s o fee d).current = s.current := by
  cases d with
  | deferred _ => rfl
  | rejectLiquidity _ _ => rfl
  | rejectGain _ _ _ => rfl
  | accepted _ _ _ => exact False.elim (h rfl)

theorem apply_history (s : Live S T) (o : Offer S T s.current) (fee : Nat)
    (d : Admission S T s o fee) :
    ∃ added, (applyAdmission S T s o fee d).history = added ++ s.history := by
  cases d with
  | deferred _ => exact ⟨[], rfl⟩
  | rejectLiquidity _ _ => exact ⟨[⟨s.current, o, s.balance, fee, .rejected .liquidity⟩], rfl⟩
  | rejectGain _ _ _ => exact ⟨[⟨s.current, o, s.balance, fee, .rejected .economics⟩], rfl⟩
  | accepted _ _ _ => exact ⟨[⟨s.current, o, s.balance, fee, .committed⟩], rfl⟩

private theorem rejected_conserves (s : Live S T) (o : Offer S T s.current) (fee : Nat)
    (why : RejectReason) (hc : fee + s.current.reserve ≤ s.balance) :
    totalFunds S T (rejected S T s o fee why hc) = totalFunds S T s := by
  change s.balance - fee + (receiptCost s.current.frontier.receipts +
    (fee + 0 + historyCost S T s.history)) =
      s.balance + (receiptCost s.current.frontier.receipts + historyCost S T s.history)
  omega

private theorem committed_conserves (s : Live S T) (o : Offer S T s.current) (fee : Nat)
    (hl : fee + o.migration + o.reserve ≤ s.balance) :
    totalFunds S T (committed S T s o fee hl) = totalFunds S T s := by
  change s.balance - (fee + o.migration) + (receiptCost s.current.frontier.receipts +
    (fee + o.migration + historyCost S T s.history)) =
      s.balance + (receiptCost s.current.frontier.receipts + historyCost S T s.history)
  omega

theorem apply_conserves (s : Live S T) (o : Offer S T s.current) (fee : Nat)
    (d : Admission S T s o fee) : totalFunds S T (applyAdmission S T s o fee d) = totalFunds S T s := by
  cases d with
  | deferred _ => rfl
  | rejectLiquidity hc _ => exact rejected_conserves S T s o fee .liquidity hc
  | rejectGain hc _ _ => exact rejected_conserves S T s o fee .economics hc
  | accepted _ hl _ => exact committed_conserves S T s o fee hl

theorem apply_accepted_gain (s : Live S T) (o : Offer S T s.current) (fee : Nat)
    (d : Admission S T s o fee) (h : verdict S T d = .accepted) :
    fee + o.migration + remainingBill S T (applyAdmission S T s o fee d).current <
      remainingBill S T s.current := by
  cases d with
  | deferred _ => cases h
  | rejectLiquidity _ _ => cases h
  | rejectGain _ _ _ => cases h
  | accepted _ _ hg => exact economic_sound S T s.current o fee hg

def chargedFee (fee migration : Nat) : Verdict → Nat
  | .deferred => 0
  | .rejectLiquidity => fee
  | .rejectGain => fee
  | .accepted => fee + migration

theorem apply_balance (s : Live S T) (o : Offer S T s.current) (fee : Nat)
    (d : Admission S T s o fee) :
    (applyAdmission S T s o fee d).balance = s.balance - chargedFee fee o.migration (verdict S T d) := by
  cases d with
  | deferred _ => exact (Nat.sub_zero _).symm
  | rejectLiquidity _ _ => rfl
  | rejectGain _ _ _ => rfl
  | accepted _ _ _ => rfl

theorem apply_exact_charge (s : Live S T) (o : Offer S T s.current) (fee : Nat)
    (d : Admission S T s o fee) :
    spent S T (applyAdmission S T s o fee d) = spent S T s + chargedFee fee o.migration (verdict S T d) := by
  cases d with
  | deferred _ => exact (Nat.add_zero _).symm
  | rejectLiquidity _ _ =>
    change receiptCost s.current.frontier.receipts + (fee + 0 + historyCost S T s.history) =
      receiptCost s.current.frontier.receipts + historyCost S T s.history + fee
    omega
  | rejectGain _ _ _ =>
    change receiptCost s.current.frontier.receipts + (fee + 0 + historyCost S T s.history) =
      receiptCost s.current.frontier.receipts + historyCost S T s.history + fee
    omega
  | accepted _ _ _ =>
    change receiptCost s.current.frontier.receipts + (fee + o.migration + historyCost S T s.history) =
      receiptCost s.current.frontier.receipts + historyCost S T s.history + (fee + o.migration)
    omega

theorem apply_liquid (s : Live S T) (o : Offer S T s.current) (fee : Nat)
    (d : Admission S T s o fee) :
    (applyAdmission S T s o fee d).current.reserve ≤ (applyAdmission S T s o fee d).balance :=
  (applyAdmission S T s o fee d).liquid

/-! Actual execution after a switch. Use precisely the certified reserve, not
all uncommitted funds. This makes the compared completion bill identical to
the executed remaining bill. Unused reserve remains available. -/
theorem prefix_funded (c : Continuation S T) (n : Nat) :
    CRTT.BudgetedPruning.potential S T c.controller.rules c.controller.fees
      (prefixRun S T c n).state ≤ (prefixRun S T c n).remaining :=
  CRTT.BudgetedPruning.run_funded
    (CRTT.BudgetedPruning.quote S T c.controller.rules c.controller.fees)
    (CRTT.BudgetedPruning.potential S T c.controller.rules c.controller.fees)
    (CRTT.BudgetedPruning.quote_potential S T c.controller.rules c.controller.fees)
    n (input S T c) c.funded

theorem prefix_correct (c : Continuation S T) (n : Nat) : Correct S T (prefixRun S T c n).state :=
  invariant (CRTT.BudgetedPruning.quote S T c.controller.rules c.controller.fees)
    (Correct S T) (CRTT.BudgetedPruning.quote_correct S T c.controller.rules c.controller.fees)
    n (input S T c) c.correct

def afterPrefix (c : Continuation S T) (n : Nat) : Continuation S T :=
  let out := prefixRun S T c n
  ⟨c.controller, out.state, prefix_correct S T c n, out.remaining, prefix_funded S T c n⟩

def advance (s : Live S T) (n : Nat) : Live S T :=
  let c := afterPrefix S T s.current n
  ⟨c, s.balance - s.current.reserve + c.reserve, s.history, by omega⟩

def finish (s : Live S T) : Live S T := advance S T s s.current.reserve

theorem advance_history (s : Live S T) (n : Nat) :
    (advance S T s n).history = s.history := rfl

theorem advance_certificates (s : Live S T) (n : Nat) :
    ∃ tail, (advance S T s n).current.frontier.certificates = s.current.frontier.certificates ++ tail := by
  let P : Frontier S T → Prop := fun f => ∃ tail, f.certificates = s.current.frontier.certificates ++ tail
  have hclosed : ∀ f q, P f →
      CRTT.BudgetedPruning.quote S T s.current.controller.rules s.current.controller.fees f = some q →
      P (q.next ()) := by
    intro f q hf hq
    obtain ⟨a, ha⟩ := hf
    obtain ⟨b, hb⟩ := CRTT.BudgetedPruning.quote_certificate_prefix S T
      s.current.controller.rules s.current.controller.fees f q hq
    exact ⟨a ++ b, by rw [hb, ha, List.append_assoc]⟩
  exact invariant (CRTT.BudgetedPruning.quote S T s.current.controller.rules s.current.controller.fees)
    P hclosed n (input S T s.current) ⟨[], (List.append_nil _).symm⟩

theorem quote_receipt_prefix (c : Continuation S T) (f : Frontier S T)
    (q : QuotedStep (Frontier S T))
    (h : CRTT.BudgetedPruning.quote S T c.controller.rules c.controller.fees f = some q) :
    ∃ r, (q.next ()).receipts = r :: f.receipts := by
  cases hj : f.jobs with
  | nil => simp [CRTT.BudgetedPruning.quote, hj] at h
  | cons j rest =>
    simp [CRTT.BudgetedPruning.quote, hj] at h
    rw [← h]
    exact ⟨CRTT.BudgetedPruning.bill S T c.controller.fees j, rfl⟩

theorem advance_receipts (s : Live S T) (n : Nat) :
    ∃ added, (advance S T s n).current.frontier.receipts = added ++ s.current.frontier.receipts := by
  let P : Frontier S T → Prop := fun f => ∃ added, f.receipts = added ++ s.current.frontier.receipts
  have hclosed : ∀ f q, P f →
      CRTT.BudgetedPruning.quote S T s.current.controller.rules s.current.controller.fees f = some q →
      P (q.next ()) := by
    intro f q hf hq
    obtain ⟨a, ha⟩ := hf
    obtain ⟨r, hr⟩ := quote_receipt_prefix S T s.current f q hq
    exact ⟨r :: a, hr.trans (congrArg (fun rs => r :: rs) ha)⟩
  exact invariant (CRTT.BudgetedPruning.quote S T s.current.controller.rules s.current.controller.fees)
    P hclosed n (input S T s.current) ⟨[], rfl⟩

theorem advance_meter (s : Live S T) (n : Nat) :
    spent S T (advance S T s n) = spent S T s + (prefixRun S T s.current n).spent := by
  have h := CRTT.BudgetedPruning.run_meter
    (CRTT.BudgetedPruning.quote S T s.current.controller.rules s.current.controller.fees)
    (fun f => receiptCost f.receipts)
    (CRTT.BudgetedPruning.quote_receipt_cost S T s.current.controller.rules s.current.controller.fees)
    n (input S T s.current)
  change (prefixRun S T s.current n).spent + receiptCost s.current.frontier.receipts =
    0 + receiptCost (prefixRun S T s.current n).state.receipts at h
  change receiptCost (prefixRun S T s.current n).state.receipts + historyCost S T s.history =
    receiptCost s.current.frontier.receipts + historyCost S T s.history + (prefixRun S T s.current n).spent
  omega

theorem advance_conserves (s : Live S T) (n : Nat) :
    totalFunds S T (advance S T s n) = totalFunds S T s := by
  have h := accounting (CRTT.BudgetedPruning.quote S T s.current.controller.rules s.current.controller.fees)
    n (input S T s.current)
  change (prefixRun S T s.current n).remaining + (prefixRun S T s.current n).spent = s.current.reserve + 0 at h
  have hl := s.liquid
  unfold totalFunds
  rw [advance_meter S T s n]
  change s.balance - s.current.reserve + (prefixRun S T s.current n).remaining +
    (spent S T s + (prefixRun S T s.current n).spent) = s.balance + spent S T s
  omega

theorem finish_full (s : Live S T) (m : Morphism S T) :
    m ∈ (finish S T s).current.frontier.certificates ↔ m ∈ discoverAll S T :=
  completion_full S T s.current m

theorem finish_exhausted (s : Live S T) : (finish S T s).current.frontier.jobs = [] :=
  CRTT.BudgetedPruning.execute_funded_exhausts S T s.current.controller.rules s.current.controller.fees
    (input S T s.current) s.current.funded

theorem finish_meter (s : Live S T) : spent S T (finish S T s) = spent S T s + remainingBill S T s.current :=
  advance_meter S T s s.current.reserve

theorem finish_after_attempt_full (s : Live S T) (o : Offer S T s.current) (baseCheck : Nat)
    (m : Morphism S T) :
    m ∈ (finish S T (tryReplace S T s o baseCheck).2).current.frontier.certificates ↔ m ∈ discoverAll S T :=
  finish_full S T (tryReplace S T s o baseCheck).2 m

/-- Full incremental comparison includes the current check fee. Not a claim
that all historical acquisition costs have been recovered. -/
theorem accepted_finish_gain (s : Live S T) (o : Offer S T s.current) (fee : Nat)
    (d : Admission S T s o fee) (h : verdict S T d = .accepted) :
    spent S T (finish S T (applyAdmission S T s o fee d)) < spent S T (finish S T s) := by
  have hg := apply_accepted_gain S T s o fee d h
  cases d with
  | deferred _ => cases h
  | rejectLiquidity _ _ => cases h
  | rejectGain _ _ _ => cases h
  | accepted hc hl hgain =>
    rw [finish_meter S T (applyAdmission S T s o fee (.accepted hc hl hgain)), finish_meter S T s]
    change spent S T (committed S T s o fee hl) + remainingBill S T (proposed S T s.current o) <
      spent S T s + remainingBill S T s.current
    change fee + o.migration + remainingBill S T (proposed S T s.current o) < remainingBill S T s.current at hg
    unfold spent
    change receiptCost s.current.frontier.receipts + (fee + o.migration + historyCost S T s.history) +
      remainingBill S T (proposed S T s.current o) <
        receiptCost s.current.frontier.receipts + historyCost S T s.history + remainingBill S T s.current
    omega

theorem tryReplace_conserves (s : Live S T) (o : Offer S T s.current) (baseCheck : Nat) :
    totalFunds S T (tryReplace S T s o baseCheck).2 = totalFunds S T s :=
  apply_conserves S T s o (baseCheck + 1) (check S T s o (baseCheck + 1))

theorem tryReplace_same (s : Live S T) (o : Offer S T s.current) (baseCheck : Nat) :
    SameContinuation S T s.current.frontier (tryReplace S T s o baseCheck).2.current.frontier :=
  apply_same S T s o (baseCheck + 1) (check S T s o (baseCheck + 1))

theorem tryReplace_accepted_gain (s : Live S T) (o : Offer S T s.current) (baseCheck : Nat)
    (h : (tryReplace S T s o baseCheck).1 = .accepted) :
    spent S T (finish S T (tryReplace S T s o baseCheck).2) < spent S T (finish S T s) :=
  accepted_finish_gain S T s o (baseCheck + 1) (check S T s o (baseCheck + 1)) h

namespace Witnesses

-- A depth obstruction: source horizon 1 exceeds target horizon 0.
-- A depth filter can finish at the root; baseline must visit its children.
def src : IndexedTask 1 2 0 where
  read := fun _ _ => false
  price := fun _ => 0
  loss := fun _ _ => 0
  depth := 1

def dst : IndexedTask 1 2 0 := { src with depth := 0 }

def oldController : Controller src dst := ⟨[], ⟨0,0,0⟩⟩
def newController : Controller src dst := ⟨[CRTT.CertifiedPruning.depthRule src dst 0], ⟨0,0,0⟩⟩

def oldContinuation : Continuation src dst :=
  ⟨oldController, CRTT.BudgetedPruning.initial src dst [],
    CRTT.BudgetedPruning.initial_correct src dst [], 100, by decide⟩

def offer : Offer src dst oldContinuation where
  newController := CRTT.ControllerReplacement.Witnesses.newController
  sameBaseFees := rfl
  reserve := 100
  reserveSound := by decide
  migration := 1
  oldLower := 7
  newUpper := 1
  oldLowerSound := by decide
  newUpperSound := by decide
  evidenceLabel := "closed depth-obstruction example"

def fundedLive : Live src dst := openLive src dst oldContinuation 110 (by decide)
def tightLive : Live src dst := openLive src dst oldContinuation 100 (by decide)
def illiquidLive : Live src dst := openLive src dst oldContinuation 101 (by decide)

theorem profitable_switch : (tryReplace src dst fundedLive offer 0).1 = .accepted := by decide

theorem fallback_reserve_protected : (tryReplace src dst tightLive offer 0).1 = .deferred := by decide

theorem cheaper_but_illiquid : (tryReplace src dst illiquidLive offer 0).1 = .rejectLiquidity := by decide

theorem paid_end_to_end : spent src dst (finish src dst (tryReplace src dst fundedLive offer 0).2) = 3 := by decide

theorem baseline_bill : spent src dst (finish src dst fundedLive) = 7 := by decide

end Witnesses

#print axioms covers_rebaseJob
#print axioms covered_rebase
#print axioms same_refl
#print axioms same_trans
#print axioms rebase_same
#print axioms same_correct
#print axioms rebase_correct
#print axioms completion_full
#print axioms completion_bill_le
#print axioms completion_same_answers
#print axioms proposed_fees
#print axioms proposed_same
#print axioms economic_sound
#print axioms checked_accept_iff
#print axioms apply_same
#print axioms apply_nonaccepted_current
#print axioms apply_history
#print axioms apply_conserves
#print axioms apply_accepted_gain
#print axioms apply_balance
#print axioms apply_exact_charge
#print axioms apply_liquid
#print axioms prefix_funded
#print axioms prefix_correct
#print axioms advance_history
#print axioms advance_certificates
#print axioms quote_receipt_prefix
#print axioms advance_receipts
#print axioms advance_meter
#print axioms advance_conserves
#print axioms finish_full
#print axioms finish_exhausted
#print axioms finish_meter
#print axioms finish_after_attempt_full
#print axioms accepted_finish_gain
#print axioms tryReplace_conserves
#print axioms tryReplace_same
#print axioms tryReplace_accepted_gain
#print axioms Witnesses.profitable_switch
#print axioms Witnesses.fallback_reserve_protected
#print axioms Witnesses.cheaper_but_illiquid
#print axioms Witnesses.paid_end_to_end
#print axioms Witnesses.baseline_bill
end CRTT.ControllerReplacement
