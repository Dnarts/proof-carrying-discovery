import RelativeEvidence

/-! T29b. Nondependent numeric verdict, followed by proof-indexed application.
No recursive trace, no new cost-evidence acquisition algorithm. The checker
reads supplied rows only after both reserve guards pass. Proofs relate those
rows to the actual old/new continuation bills in T29a. -/
namespace CRTT.AdmissionAccounting
open CRTT.MorphismDiscovery
open CRTT.ControllerReplacement (Continuation Live Verdict SameContinuation remainingBill chargedFee)
open CRTT.RelativeEvidence (Row RelativeOffer relativeOK proposed)
open CRTT.BudgetedPruning (receiptCost)
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

structure GateInput where
  fee : Nat
  migration : Nat
  oldReserve : Nat
  newReserve : Nat
  balance : Nat
  rows : List Row

/-- No dependent match and no Session or Offer in the numeric decision. -/
def gate (i : GateInput) : Verdict :=
  if i.fee + i.oldReserve ≤ i.balance then
    if i.fee + i.migration + i.newReserve ≤ i.balance then
      if relativeOK (i.fee + i.migration) i.rows = true then .accepted
      else .rejectGain
    else .rejectLiquidity
  else .deferred

theorem gate_accepted_iff (i : GateInput) : gate i = .accepted ↔
    i.fee + i.oldReserve ≤ i.balance ∧
    i.fee + i.migration + i.newReserve ≤ i.balance ∧
    relativeOK (i.fee + i.migration) i.rows = true := by
  by_cases hc : i.fee + i.oldReserve ≤ i.balance
  · by_cases hl : i.fee + i.migration + i.newReserve ≤ i.balance
    · by_cases hg : relativeOK (i.fee + i.migration) i.rows = true
      · simp [gate, hc, hl, hg]
      · simp [gate, hc, hl, hg]
    · simp [gate, hc, hl]
  · simp [gate, hc]

theorem gate_deferred_iff (i : GateInput) : gate i = .deferred ↔
    ¬ i.fee + i.oldReserve ≤ i.balance := by
  by_cases hc : i.fee + i.oldReserve ≤ i.balance
  · by_cases hl : i.fee + i.migration + i.newReserve ≤ i.balance
    · by_cases hg : relativeOK (i.fee + i.migration) i.rows = true
      · simp [gate, hc, hl, hg]
      · simp [gate, hc, hl, hg]
    · simp [gate, hc, hl]
  · simp [gate, hc]

theorem gate_rejectLiquidity_iff (i : GateInput) : gate i = .rejectLiquidity ↔
    i.fee + i.oldReserve ≤ i.balance ∧ ¬ i.fee + i.migration + i.newReserve ≤ i.balance := by
  by_cases hc : i.fee + i.oldReserve ≤ i.balance
  · by_cases hl : i.fee + i.migration + i.newReserve ≤ i.balance
    · by_cases hg : relativeOK (i.fee + i.migration) i.rows = true
      · simp [gate, hc, hl, hg]
      · simp [gate, hc, hl, hg]
    · simp [gate, hc, hl]
  · simp [gate, hc]

theorem gate_rejectGain_iff (i : GateInput) : gate i = .rejectGain ↔
    i.fee + i.oldReserve ≤ i.balance ∧
    i.fee + i.migration + i.newReserve ≤ i.balance ∧
    ¬ relativeOK (i.fee + i.migration) i.rows = true := by
  by_cases hc : i.fee + i.oldReserve ≤ i.balance
  · by_cases hl : i.fee + i.migration + i.newReserve ≤ i.balance
    · by_cases hg : relativeOK (i.fee + i.migration) i.rows = true
      · simp [gate, hc, hl, hg]
      · simp [gate, hc, hl, hg]
    · simp [gate, hc, hl]
  · simp [gate, hc]

theorem gate_debit_le (i : GateInput) (v : Verdict) (hv : gate i = v) :
    chargedFee i.fee i.migration v ≤ i.balance := by
  cases v with
  | deferred => exact Nat.zero_le _
  | rejectLiquidity =>
    have h := ((gate_rejectLiquidity_iff i).mp hv).1
    change i.fee ≤ i.balance
    omega
  | rejectGain =>
    have h := ((gate_rejectGain_iff i).mp hv).1
    change i.fee ≤ i.balance
    omega
  | accepted =>
    have h := ((gate_accepted_iff i).mp hv).2.1
    change i.fee + i.migration ≤ i.balance
    omega

variable {sw sp sa tw tp ta : Nat}
variable (S : IndexedTask sw sp sa) (T : IndexedTask tw tp ta)

/-- Distinct journal; no claim that a relative offer passed T28's absolute gate. -/
inductive Entry where
  | evidence (label : String) (fee : Nat)
  | attempt (old : Continuation S T) (offer : RelativeOffer S T old)
      (balanceBefore fee : Nat) (status : Verdict)

def entryFee : Entry S T → Nat
  | .evidence _ fee => fee
  | .attempt _ o _ fee v => chargedFee fee o.candidate.migration v

def journalCost : List (Entry S T) → Nat
  | [] => 0
  | e :: es => entryFee S T e + journalCost es

structure Session where
  live : Live S T
  journal : List (Entry S T)

def start (s : Live S T) : Session S T := ⟨s, []⟩
def spent (s : Session S T) : Nat := CRTT.ControllerReplacement.spent S T s.live + journalCost S T s.journal
def funds (s : Session S T) : Nat := s.live.balance + spent S T s
/-- Specification only: admission never calls this or remainingBill. -/
def objective (s : Session S T) : Nat := spent S T s + remainingBill S T s.live.current

def gateInput (s : Session S T) (o : RelativeOffer S T s.live.current) (fee : Nat) : GateInput :=
  ⟨fee, o.candidate.migration, s.live.current.reserve, o.candidate.reserve, s.live.balance, o.rows⟩

/-- Explicit reserve bridge; no rewriting inside a dependent verdict match. -/
theorem accepted_affordable (s : Session S T) (o : RelativeOffer S T s.live.current) (fee : Nat)
    (h : gate (gateInput S T s o fee) = .accepted) :
    fee + o.candidate.migration + (proposed S T s.live.current o).reserve ≤ s.live.balance := by
  have hl := ((gate_accepted_iff (gateInput S T s o fee)).mp h).2.1
  rw [CRTT.RelativeEvidence.proposed_reserve S T s.live.current o]
  exact hl

theorem rejected_liquidity_affordable (s : Session S T) (o : RelativeOffer S T s.live.current) (fee : Nat)
    (h : gate (gateInput S T s o fee) = .rejectLiquidity) : fee + s.live.current.reserve ≤ s.live.balance :=
  ((gate_rejectLiquidity_iff (gateInput S T s o fee)).mp h).1

theorem rejected_gain_affordable (s : Session S T) (o : RelativeOffer S T s.live.current) (fee : Nat)
    (h : gate (gateInput S T s o fee) = .rejectGain) : fee + s.live.current.reserve ≤ s.live.balance :=
  ((gate_rejectGain_iff (gateInput S T s o fee)).mp h).1

private def charge (s : Session S T) (c : Continuation S T) (e : Entry S T) (debit : Nat)
    (h : debit + c.reserve ≤ s.live.balance) : Session S T :=
  ⟨⟨c, s.live.balance - debit, s.live.history, by omega⟩, e :: s.journal⟩

/-- A plain verdict, and a proof that it is the verdict of the fixed gate on
this precise input. Pattern matching is only on the four ordinary constructors.
The proof does not contribute any runtime cost or authority. -/
def applyVerdict (s : Session S T) (o : RelativeOffer S T s.live.current) (fee : Nat) :
    (v : Verdict) → gate (gateInput S T s o fee) = v → Session S T
  | .deferred, _ => s
  | .rejectLiquidity, h => charge S T s s.live.current
      (.attempt s.live.current o s.live.balance fee .rejectLiquidity) fee
      (rejected_liquidity_affordable S T s o fee h)
  | .rejectGain, h => charge S T s s.live.current
      (.attempt s.live.current o s.live.balance fee .rejectGain) fee
      (rejected_gain_affordable S T s o fee h)
  | .accepted, h => charge S T s (proposed S T s.live.current o)
      (.attempt s.live.current o s.live.balance fee .accepted) (fee + o.candidate.migration)
      (accepted_affordable S T s o fee h)

/-- The gate is evaluated once. Public checks cost base+1 when not deferred. -/
def tryRelative (s : Session S T) (o : RelativeOffer S T s.live.current) (base : Nat) : Verdict × Session S T :=
  let fee := base + 1
  let v := gate (gateInput S T s o fee)
  (v, applyVerdict S T s o fee v rfl)

def installed (s : Session S T) (o : RelativeOffer S T s.live.current) : Verdict → Continuation S T
  | .accepted => proposed S T s.live.current o
  | _ => s.live.current

def addedEntries (s : Session S T) (o : RelativeOffer S T s.live.current) (fee : Nat) : Verdict → List (Entry S T)
  | .deferred => []
  | .rejectLiquidity => [.attempt s.live.current o s.live.balance fee .rejectLiquidity]
  | .rejectGain => [.attempt s.live.current o s.live.balance fee .rejectGain]
  | .accepted => [.attempt s.live.current o s.live.balance fee .accepted]

/-- Establish the receipt/debit identity before any accounting proof. -/
theorem addedEntries_cost (s : Session S T) (o : RelativeOffer S T s.live.current) (fee : Nat) (v : Verdict) :
    journalCost S T (addedEntries S T s o fee v ++ s.journal) =
      chargedFee fee o.candidate.migration v + journalCost S T s.journal := by
  cases v with
  | deferred => exact (Nat.zero_add _).symm
  | rejectLiquidity => rfl
  | rejectGain => rfl
  | accepted => rfl

theorem apply_deferred (s : Session S T) (o : RelativeOffer S T s.live.current) (fee : Nat)
    (hv : gate (gateInput S T s o fee) = .deferred) : applyVerdict S T s o fee .deferred hv = s := rfl

theorem apply_current (s : Session S T) (o : RelativeOffer S T s.live.current) (fee : Nat)
    (v : Verdict) (hv : gate (gateInput S T s o fee) = v) :
    (applyVerdict S T s o fee v hv).live.current = installed S T s o v := by
  cases v <;> rfl

theorem apply_nonaccepted (s : Session S T) (o : RelativeOffer S T s.live.current) (fee : Nat)
    (v : Verdict) (hv : gate (gateInput S T s o fee) = v) (hn : v ≠ .accepted) :
    (applyVerdict S T s o fee v hv).live.current = s.live.current := by
  cases v with
  | deferred => rfl
  | rejectLiquidity => rfl
  | rejectGain => rfl
  | accepted => exact False.elim (hn rfl)

theorem apply_same (s : Session S T) (o : RelativeOffer S T s.live.current) (fee : Nat)
    (v : Verdict) (hv : gate (gateInput S T s o fee) = v) :
    SameContinuation S T s.live.current.frontier (applyVerdict S T s o fee v hv).live.current.frontier := by
  rw [apply_current S T s o fee v hv]
  cases v with
  | deferred => exact CRTT.ControllerReplacement.same_refl S T _
  | rejectLiquidity => exact CRTT.ControllerReplacement.same_refl S T _
  | rejectGain => exact CRTT.ControllerReplacement.same_refl S T _
  | accepted => exact CRTT.RelativeEvidence.proposed_same S T s.live.current o

theorem apply_fees (s : Session S T) (o : RelativeOffer S T s.live.current) (fee : Nat)
    (v : Verdict) (hv : gate (gateInput S T s o fee) = v) :
    (applyVerdict S T s o fee v hv).live.current.controller.fees = s.live.current.controller.fees := by
  rw [apply_current S T s o fee v hv]
  cases v with
  | deferred => rfl
  | rejectLiquidity => rfl
  | rejectGain => rfl
  | accepted => exact CRTT.RelativeEvidence.proposed_fees S T s.live.current o

theorem apply_old_history (s : Session S T) (o : RelativeOffer S T s.live.current) (fee : Nat)
    (v : Verdict) (hv : gate (gateInput S T s o fee) = v) :
    (applyVerdict S T s o fee v hv).live.history = s.live.history := by
  cases v <;> rfl

theorem apply_journal (s : Session S T) (o : RelativeOffer S T s.live.current) (fee : Nat)
    (v : Verdict) (hv : gate (gateInput S T s o fee) = v) :
    (applyVerdict S T s o fee v hv).journal = addedEntries S T s o fee v ++ s.journal := by
  cases v <;> rfl

theorem apply_balance (s : Session S T) (o : RelativeOffer S T s.live.current) (fee : Nat)
    (v : Verdict) (hv : gate (gateInput S T s o fee) = v) :
    (applyVerdict S T s o fee v hv).live.balance = s.live.balance - chargedFee fee o.candidate.migration v := by
  cases v with
  | deferred => exact (Nat.sub_zero _).symm
  | rejectLiquidity => rfl
  | rejectGain => rfl
  | accepted => rfl

theorem apply_charge (s : Session S T) (o : RelativeOffer S T s.live.current) (fee : Nat)
    (v : Verdict) (hv : gate (gateInput S T s o fee) = v) :
    spent S T (applyVerdict S T s o fee v hv) = spent S T s + chargedFee fee o.candidate.migration v := by
  have hs := apply_same S T s o fee v hv
  unfold spent CRTT.ControllerReplacement.spent
  rw [hs.2.1, apply_old_history S T s o fee v hv, apply_journal S T s o fee v hv,
    addedEntries_cost S T s o fee v]
  omega

theorem apply_funds (s : Session S T) (o : RelativeOffer S T s.live.current) (fee : Nat)
    (v : Verdict) (hv : gate (gateInput S T s o fee) = v) :
    funds S T (applyVerdict S T s o fee v hv) = funds S T s := by
  have hd : chargedFee fee o.candidate.migration v ≤ s.live.balance := gate_debit_le (gateInput S T s o fee) v hv
  unfold funds
  rw [apply_balance S T s o fee v hv, apply_charge S T s o fee v hv]
  omega

theorem apply_liquid (s : Session S T) (o : RelativeOffer S T s.live.current) (fee : Nat)
    (v : Verdict) (hv : gate (gateInput S T s o fee) = v) :
    (applyVerdict S T s o fee v hv).live.current.reserve ≤ (applyVerdict S T s o fee v hv).live.balance :=
  (applyVerdict S T s o fee v hv).live.liquid

theorem apply_accepted_gain (s : Session S T) (o : RelativeOffer S T s.live.current) (fee : Nat)
    (hv : gate (gateInput S T s o fee) = .accepted) :
    objective S T (applyVerdict S T s o fee .accepted hv) < objective S T s := by
  have hg : relativeOK (fee + o.candidate.migration) o.rows = true := ((gate_accepted_iff (gateInput S T s o fee)).mp hv).2.2
  have h := CRTT.RelativeEvidence.relative_sound S T s.live.current o fee hg
  unfold objective
  rw [apply_charge S T s o fee .accepted hv, apply_current S T s o fee .accepted hv]
  change spent S T s + (fee + o.candidate.migration) + remainingBill S T (proposed S T s.live.current o) <
    spent S T s + remainingBill S T s.live.current
  omega

theorem apply_nonaccepted_objective (s : Session S T) (o : RelativeOffer S T s.live.current) (fee : Nat)
    (v : Verdict) (hv : gate (gateInput S T s o fee) = v) (hn : v ≠ .accepted) :
    objective S T (applyVerdict S T s o fee v hv) = objective S T s + chargedFee fee o.candidate.migration v := by
  unfold objective
  rw [apply_charge S T s o fee v hv, apply_nonaccepted S T s o fee v hv hn]
  omega

/-- External paid receipt only, not proof of acquisition or truth. -/
def recordEvidence (s : Session S T) (label : String) (base : Nat)
    (h : base + 1 + s.live.current.reserve ≤ s.live.balance) : Session S T :=
  charge S T s s.live.current (.evidence label (base + 1)) (base + 1) h

theorem evidence_current (s : Session S T) (label : String) (base : Nat)
    (h : base+1+s.live.current.reserve ≤ s.live.balance) :
    (recordEvidence S T s label base h).live.current = s.live.current := rfl

theorem evidence_journal (s : Session S T) (label : String) (base : Nat)
    (h : base+1+s.live.current.reserve ≤ s.live.balance) :
    (recordEvidence S T s label base h).journal = .evidence label (base+1) :: s.journal := rfl

theorem evidence_charge (s : Session S T) (label : String) (base : Nat)
    (h : base+1+s.live.current.reserve ≤ s.live.balance) :
    spent S T (recordEvidence S T s label base h) = spent S T s + (base+1) := by
  change CRTT.ControllerReplacement.spent S T s.live + (base+1+journalCost S T s.journal) =
    CRTT.ControllerReplacement.spent S T s.live + journalCost S T s.journal + (base+1)
  omega

theorem evidence_funds (s : Session S T) (label : String) (base : Nat)
    (h : base+1+s.live.current.reserve ≤ s.live.balance) :
    funds S T (recordEvidence S T s label base h) = funds S T s := by
  unfold funds
  rw [evidence_charge S T s label base h]
  change s.live.balance - (base+1) + (spent S T s + (base+1)) = s.live.balance + spent S T s
  omega

theorem evidence_objective (s : Session S T) (label : String) (base : Nat)
    (h : base+1+s.live.current.reserve ≤ s.live.balance) :
    objective S T (recordEvidence S T s label base h) = objective S T s + (base+1) := by
  unfold objective
  rw [evidence_charge S T s label base h, evidence_current S T s label base h]
  omega

theorem tryRelative_funds (s : Session S T) (o : RelativeOffer S T s.live.current) (base : Nat) :
    funds S T (tryRelative S T s o base).2 = funds S T s :=
  apply_funds S T s o (base+1) _ rfl

theorem tryRelative_same (s : Session S T) (o : RelativeOffer S T s.live.current) (base : Nat) :
    SameContinuation S T s.live.current.frontier (tryRelative S T s o base).2.live.current.frontier :=
  apply_same S T s o (base+1) _ rfl

theorem tryRelative_completion (s : Session S T) (o : RelativeOffer S T s.live.current) (base : Nat)
    (m : Morphism S T) :
    m ∈ (CRTT.ControllerReplacement.finish S T (tryRelative S T s o base).2.live).current.frontier.certificates ↔ m ∈ discoverAll S T :=
  CRTT.ControllerReplacement.finish_full S T (tryRelative S T s o base).2.live m

namespace Witnesses
open CRTT.ControllerReplacement.Witnesses (src dst oldContinuation fundedLive tightLive illiquidLive)
open CRTT.RelativeEvidence.Witnesses (liveOffer)

theorem relative_accepted : (tryRelative src dst (start src dst fundedLive) liveOffer 0).1 = .accepted := by decide

theorem relative_deferred : (tryRelative src dst (start src dst tightLive) liveOffer 0).1 = .deferred := by decide

theorem relative_illiquid : (tryRelative src dst (start src dst illiquidLive) liveOffer 0).1 = .rejectLiquidity := by decide

theorem accepted_exact_cost : objective src dst (tryRelative src dst (start src dst fundedLive) liveOffer 0).2 = 3 := by decide

theorem reject_exact_cost : objective src dst (tryRelative src dst (start src dst illiquidLive) liveOffer 0).2 = 8 := by decide

end Witnesses

#print axioms gate_accepted_iff
#print axioms gate_deferred_iff
#print axioms gate_rejectLiquidity_iff
#print axioms gate_rejectGain_iff
#print axioms gate_debit_le
#print axioms accepted_affordable
#print axioms rejected_liquidity_affordable
#print axioms rejected_gain_affordable
#print axioms addedEntries_cost
#print axioms apply_deferred
#print axioms apply_current
#print axioms apply_nonaccepted
#print axioms apply_same
#print axioms apply_fees
#print axioms apply_old_history
#print axioms apply_journal
#print axioms apply_balance
#print axioms apply_charge
#print axioms apply_funds
#print axioms apply_liquid
#print axioms apply_accepted_gain
#print axioms apply_nonaccepted_objective
#print axioms evidence_current
#print axioms evidence_journal
#print axioms evidence_charge
#print axioms evidence_funds
#print axioms evidence_objective
#print axioms tryRelative_funds
#print axioms tryRelative_same
#print axioms tryRelative_completion
#print axioms Witnesses.relative_accepted
#print axioms Witnesses.relative_deferred
#print axioms Witnesses.relative_illiquid
#print axioms Witnesses.accepted_exact_cost
#print axioms Witnesses.reject_exact_cost
end CRTT.AdmissionAccounting
