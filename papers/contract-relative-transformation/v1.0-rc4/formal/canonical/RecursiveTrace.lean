import AdmissionAccounting

/-! T29c: finite connected histories of actual T29b operations.
No dependent endpoint in an inductive constructor. Session equality is a
proposition, not an invented decision procedure for function-bearing states.
All economic metrics below are specifications, not free runtime estimates. -/
namespace CRTT.RecursiveTrace
open CRTT.MorphismDiscovery
open CRTT.BudgetedDiscovery
open CRTT.ControllerReplacement (Continuation Verdict remainingBill prefixRun afterPrefix chargedFee)
open CRTT.RelativeEvidence (RelativeOffer)
open CRTT.AdmissionAccounting (Session spent funds objective gate gateInput applyVerdict tryRelative recordEvidence)
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

/-! Independent prefix law, before any trace construction. -/
variable {U : Type}

def shiftSpent (s : Account U) (k : Nat) : Account U := { s with spent := s.spent + k }

theorem run_shift_spent (qf : U → Option (QuotedStep U)) (n : Nat)
    (s : Account U) (k : Nat) : run qf n (shiftSpent s k) = shiftSpent (run qf n s) k := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    cases hq : qf s.state with
    | none => simp [run, shiftSpent, hq]
    | some q =>
      by_cases hp : q.fee ≤ s.remaining
      · let paid : Account U := ⟨q.next (), s.remaining - q.fee, s.spent + q.fee⟩
        have hr : run qf (n+1) s = run qf n paid := by
          change run qf (n+1) s = run qf n ⟨q.next (), s.remaining-q.fee, s.spent+q.fee⟩
          simp [run, hq, hp]
        have hl : run qf (n+1) (shiftSpent s k) = run qf n (shiftSpent paid k) := by
          have he : s.spent + k + q.fee = s.spent + q.fee + k := by omega
          change run qf (n+1) ⟨s.state,s.remaining,s.spent+k⟩ =
            run qf n ⟨q.next (),s.remaining-q.fee,(s.spent+q.fee)+k⟩
          simp [run, hq, hp, he]
        rw [hl, hr]
        exact ih paid
      · simp [run, shiftSpent, hq, hp]

theorem execute_prefix_bill (qf : U → Option (QuotedStep U)) (n : Nat)
    (u : U) (b : Nat) :
    let start : Account U := ⟨u,b,0⟩
    let p := run qf n start
    (execute qf start).spent = p.spent + (execute qf ⟨p.state,p.remaining,0⟩).spent := by
  let start : Account U := ⟨u,b,0⟩
  let p := run qf n start
  let tail : Account U := ⟨p.state,p.remaining,0⟩
  change (execute qf start).spent = p.spent + (execute qf tail).spent
  have h := CRTT.ResumeLaws.execute_topUp_prefix qf n start 0
  have hrun : execute qf start = execute qf p := by
    change execute qf (topUp start 0) = execute qf (topUp p 0) at h
    simpa only [topUp, Nat.add_zero] using h
  have hp : shiftSpent tail p.spent = p := by
    change (⟨p.state,p.remaining,0+p.spent⟩ : Account U) = p
    calc
      _ = (⟨p.state,p.remaining,p.spent⟩ : Account U) :=
        congrArg (fun k : Nat => (⟨p.state,p.remaining,k⟩ : Account U)) (Nat.zero_add _)
      _ = p := rfl
  have hshift : execute qf p = shiftSpent (execute qf tail) p.spent := by
    calc
      execute qf p = execute qf (shiftSpent tail p.spent) := congrArg (execute qf) hp.symm
      _ = shiftSpent (execute qf tail) p.spent := run_shift_spent qf tail.remaining tail p.spent
  calc
    (execute qf start).spent = (execute qf p).spent := congrArg (fun a : Account U => a.spent) hrun
    _ = (shiftSpent (execute qf tail) p.spent).spent := congrArg (fun a : Account U => a.spent) hshift
    _ = p.spent + (execute qf tail).spent := Nat.add_comm _ _

variable {sw sp sa tw tp ta : Nat}
variable (S : IndexedTask sw sp sa) (T : IndexedTask tw tp ta)

theorem remainingBill_prefix (c : Continuation S T) (n : Nat) :
    remainingBill S T c = (prefixRun S T c n).spent + remainingBill S T (afterPrefix S T c n) :=
  execute_prefix_bill (CRTT.BudgetedPruning.quote S T c.controller.rules c.controller.fees)
    n c.frontier c.reserve

def advance (s : Session S T) (n : Nat) : Session S T :=
  ⟨CRTT.ControllerReplacement.advance S T s.live n, s.journal⟩

theorem advance_spent (s : Session S T) (n : Nat) : spent S T (advance S T s n) =
    spent S T s + (prefixRun S T s.live.current n).spent := by
  unfold CRTT.AdmissionAccounting.spent
  change CRTT.ControllerReplacement.spent S T (CRTT.ControllerReplacement.advance S T s.live n) +
    CRTT.AdmissionAccounting.journalCost S T s.journal = _
  rw [CRTT.ControllerReplacement.advance_meter S T s.live n]
  omega

theorem advance_funds (s : Session S T) (n : Nat) : funds S T (advance S T s n) = funds S T s := by
  have h := CRTT.ControllerReplacement.advance_conserves S T s.live n
  change (CRTT.ControllerReplacement.advance S T s.live n).balance +
    CRTT.ControllerReplacement.spent S T (CRTT.ControllerReplacement.advance S T s.live n) =
    s.live.balance + CRTT.ControllerReplacement.spent S T s.live at h
  change (CRTT.ControllerReplacement.advance S T s.live n).balance +
    (CRTT.ControllerReplacement.spent S T (CRTT.ControllerReplacement.advance S T s.live n) + CRTT.AdmissionAccounting.journalCost S T s.journal) =
    s.live.balance + (CRTT.ControllerReplacement.spent S T s.live + CRTT.AdmissionAccounting.journalCost S T s.journal)
  omega

theorem advance_objective (s : Session S T) (n : Nat) : objective S T (advance S T s n) = objective S T s := by
  have h := remainingBill_prefix S T s.live.current n
  unfold CRTT.AdmissionAccounting.objective
  rw [advance_spent S T s n]
  change spent S T s + (prefixRun S T s.live.current n).spent + remainingBill S T (afterPrefix S T s.live.current n) =
    spent S T s + remainingBill S T s.live.current
  omega

/-! Cumulative preservation is a relation on actual endpoints. -/
structure Preserves (s t : Session S T) : Prop where
  fees : t.live.current.controller.fees = s.live.current.controller.fees
  certificates : ∃ tail, t.live.current.frontier.certificates = s.live.current.frontier.certificates ++ tail
  receipts : ∃ added, t.live.current.frontier.receipts = added ++ s.live.current.frontier.receipts
  journal : ∃ added, t.journal = added ++ s.journal
  oldHistory : t.live.history = s.live.history

theorem preserves_refl (s : Session S T) : Preserves S T s s :=
  ⟨rfl, ⟨[], (List.append_nil _).symm⟩, ⟨[], rfl⟩, ⟨[], rfl⟩, rfl⟩

theorem preserves_trans (s t u : Session S T) (a : Preserves S T s t) (b : Preserves S T t u) :
    Preserves S T s u := by
  refine ⟨b.fees.trans a.fees, ?_, ?_, ?_, b.oldHistory.trans a.oldHistory⟩
  · obtain ⟨x,hx⟩ := a.certificates
    obtain ⟨y,hy⟩ := b.certificates
    exact ⟨x++y, by rw [hy,hx,List.append_assoc]⟩
  · obtain ⟨x,hx⟩ := a.receipts
    obtain ⟨y,hy⟩ := b.receipts
    exact ⟨y++x, by rw [hy,hx,List.append_assoc]⟩
  · obtain ⟨x,hx⟩ := a.journal
    obtain ⟨y,hy⟩ := b.journal
    exact ⟨y++x, by rw [hy,hx,List.append_assoc]⟩

theorem advance_preserves (s : Session S T) (n : Nat) : Preserves S T s (advance S T s n) :=
  ⟨rfl, CRTT.ControllerReplacement.advance_certificates S T s.live n,
    CRTT.ControllerReplacement.advance_receipts S T s.live n, ⟨[],rfl⟩,
    CRTT.ControllerReplacement.advance_history S T s.live n⟩

theorem apply_preserves (s : Session S T) (o : RelativeOffer S T s.live.current) (fee : Nat)
    (v : Verdict) (hv : gate (gateInput S T s o fee) = v) :
    Preserves S T s (applyVerdict S T s o fee v hv) := by
  have hs := CRTT.AdmissionAccounting.apply_same S T s o fee v hv
  exact ⟨CRTT.AdmissionAccounting.apply_fees S T s o fee v hv,
    ⟨[], hs.1.trans (List.append_nil _).symm⟩, ⟨[],hs.2.1⟩,
    ⟨CRTT.AdmissionAccounting.addedEntries S T s o fee v,
      CRTT.AdmissionAccounting.apply_journal S T s o fee v hv⟩,
    CRTT.AdmissionAccounting.apply_old_history S T s o fee v hv⟩

theorem evidence_preserves (s : Session S T) (label : String) (base : Nat)
    (h : base+1+s.live.current.reserve ≤ s.live.balance) :
    Preserves S T s (recordEvidence S T s label base h) :=
  ⟨rfl, ⟨[],(List.append_nil _).symm⟩, ⟨[],rfl⟩,
    ⟨[.evidence label (base+1)],rfl⟩,rfl⟩

/-! The four additive trace statistics. Gain is NET of the accepted check
and migration; only rejected checks and external evidence enter overhead. -/
structure Delta where
  gain : Nat
  overhead : Nat
  paidAttempts : Nat
  accepted : Nat

def zeroDelta : Delta := ⟨0,0,0,0⟩
def addDelta (a b : Delta) : Delta :=
  ⟨a.gain+b.gain,a.overhead+b.overhead,a.paidAttempts+b.paidAttempts,a.accepted+b.accepted⟩

def attemptDelta (s t : Session S T) (fee : Nat) : Verdict → Delta
  | .deferred => zeroDelta
  | .rejectLiquidity => ⟨0,fee,1,0⟩
  | .rejectGain => ⟨0,fee,1,0⟩
  | .accepted => ⟨objective S T s - objective S T t,0,1,1⟩

structure Laws (s t : Session S T) (d : Delta) : Prop where
  objLaw : objective S T t + d.gain = objective S T s + d.overhead
  fundLaw : funds S T t = funds S T s
  paidLaw : spent S T s + d.paidAttempts ≤ spent S T t
  acceptLaw : d.accepted ≤ d.gain
  provenance : Preserves S T s t

theorem laws_refl (s : Session S T) : Laws S T s s zeroDelta :=
  ⟨rfl,rfl,by simp [zeroDelta],Nat.le_refl 0,preserves_refl S T s⟩

theorem laws_compose (s t u : Session S T) (a b : Delta)
    (ha : Laws S T s t a) (hb : Laws S T t u b) : Laws S T s u (addDelta a b) := by
  refine ⟨?_,hb.fundLaw.trans ha.fundLaw,?_,?_,preserves_trans S T s t u ha.provenance hb.provenance⟩
  · have h1 := ha.objLaw
    have h2 := hb.objLaw
    change objective S T u + (a.gain+b.gain) = objective S T s + (a.overhead+b.overhead)
    omega
  · have h1 := ha.paidLaw
    have h2 := hb.paidLaw
    change spent S T s + (a.paidAttempts+b.paidAttempts) ≤ spent S T u
    omega
  · exact Nat.add_le_add ha.acceptLaw hb.acceptLaw

theorem advance_laws (s : Session S T) (n : Nat) : Laws S T s (advance S T s n) zeroDelta := by
  refine ⟨?_,advance_funds S T s n,?_,Nat.le_refl 0,advance_preserves S T s n⟩
  · change objective S T (advance S T s n) + 0 = objective S T s + 0
    simpa only [Nat.add_zero] using advance_objective S T s n
  · change spent S T s + 0 ≤ spent S T (advance S T s n)
    rw [advance_spent S T s n]
    omega

theorem evidence_laws (s : Session S T) (label : String) (base : Nat)
    (h : base+1+s.live.current.reserve ≤ s.live.balance) :
    Laws S T s (recordEvidence S T s label base h) ⟨0,base+1,0,0⟩ := by
  refine ⟨?_,CRTT.AdmissionAccounting.evidence_funds S T s label base h,?_,Nat.le_refl 0,
    evidence_preserves S T s label base h⟩
  · change objective S T (recordEvidence S T s label base h) + 0 = objective S T s + (base+1)
    rw [Nat.add_zero]
    exact CRTT.AdmissionAccounting.evidence_objective S T s label base h
  · change spent S T s + 0 ≤ spent S T (recordEvidence S T s label base h)
    rw [CRTT.AdmissionAccounting.evidence_charge S T s label base h]
    omega

/-- Case split only on the ordinary four-constructor Verdict, with its exact
verified gate equality. No dependent match on the computation of a verdict. -/
theorem apply_laws (s : Session S T) (o : RelativeOffer S T s.live.current) (base : Nat)
    (v : Verdict) (hv : gate (gateInput S T s o (base+1)) = v) :
    Laws S T s (applyVerdict S T s o (base+1) v hv)
      (attemptDelta S T s (applyVerdict S T s o (base+1) v hv) (base+1) v) := by
  refine ⟨?_, CRTT.AdmissionAccounting.apply_funds S T s o (base+1) v hv, ?_, ?_,
    apply_preserves S T s o (base+1) v hv⟩
  · cases v with
    | deferred =>
      rw [CRTT.AdmissionAccounting.apply_deferred S T s o (base+1) hv] <;> rfl
    | rejectLiquidity =>
      have h := CRTT.AdmissionAccounting.apply_nonaccepted_objective S T s o (base+1) .rejectLiquidity hv (by decide)
      change objective S T (applyVerdict S T s o (base+1) .rejectLiquidity hv) + 0 = objective S T s + (base+1)
      simpa only [Nat.add_zero,chargedFee] using h
    | rejectGain =>
      have h := CRTT.AdmissionAccounting.apply_nonaccepted_objective S T s o (base+1) .rejectGain hv (by decide)
      change objective S T (applyVerdict S T s o (base+1) .rejectGain hv) + 0 = objective S T s + (base+1)
      simpa only [Nat.add_zero,chargedFee] using h
    | accepted =>
      have h := CRTT.AdmissionAccounting.apply_accepted_gain S T s o (base+1) hv
      change objective S T (applyVerdict S T s o (base+1) .accepted hv) +
        (objective S T s - objective S T (applyVerdict S T s o (base+1) .accepted hv)) = objective S T s + 0
      omega
  · have h := CRTT.AdmissionAccounting.apply_charge S T s o (base+1) v hv
    cases v with
    | deferred =>
      change spent S T s + 0 ≤ spent S T (applyVerdict S T s o (base+1) .deferred hv)
      rw [h] <;> exact Nat.le_refl _
    | rejectLiquidity =>
      change spent S T s + 1 ≤ spent S T (applyVerdict S T s o (base+1) .rejectLiquidity hv)
      rw [h]
      change spent S T s + 1 ≤ spent S T s + (base+1)
      omega
    | rejectGain =>
      change spent S T s + 1 ≤ spent S T (applyVerdict S T s o (base+1) .rejectGain hv)
      rw [h]
      change spent S T s + 1 ≤ spent S T s + (base+1)
      omega
    | accepted =>
      change spent S T s + 1 ≤ spent S T (applyVerdict S T s o (base+1) .accepted hv)
      rw [h]
      change spent S T s + 1 ≤ spent S T s + (base+1+o.candidate.migration)
      omega
  · cases v with
    | deferred => exact Nat.le_refl 0
    | rejectLiquidity => exact Nat.le_refl 0
    | rejectGain => exact Nat.le_refl 0
    | accepted =>
      have h := CRTT.AdmissionAccounting.apply_accepted_gain S T s o (base+1) hv
      change 1 ≤ objective S T s - objective S T (applyVerdict S T s o (base+1) .accepted hv)
      omega

/-! One state PARAMETER, no endpoint index. Execution computes its endpoint.
No independent choice of endpoint is present in the Transition record. -/
inductive Action (s : Session S T) where
  | advance (fuel : Nat)
  | attempt (offer : RelativeOffer S T s.live.current) (base : Nat)
  | evidence (label : String) (base : Nat) (affordable : base+1+s.live.current.reserve ≤ s.live.balance)

def perform (s : Session S T) : Action S T s → Session S T
  | .advance n => advance S T s n
  | .attempt o b => (tryRelative S T s o b).2
  | .evidence label b h => recordEvidence S T s label b h

/-- Ghost/specification delta; never evaluated to select an action. -/
def actionDelta (s : Session S T) : Action S T s → Delta
  | .advance _ => zeroDelta
  | .attempt o b => let out := tryRelative S T s o b; attemptDelta S T s out.2 (b+1) out.1
  | .evidence _ b _ => ⟨0,b+1,0,0⟩

theorem action_laws (s : Session S T) (a : Action S T s) :
    Laws S T s (perform S T s a) (actionDelta S T s a) := by
  cases a with
  | advance n => exact advance_laws S T s n
  | attempt o b => exact apply_laws S T s o b (gate (gateInput S T s o (b+1))) rfl
  | evidence label b h => exact evidence_laws S T s label b h

structure Transition where
  before : Session S T
  action : Action S T before

def after (x : Transition S T) : Session S T := perform S T x.before x.action

def effect (x : Transition S T) : Delta := actionDelta S T x.before x.action

/-- Endpoints are verified against actual adjacent transitions, rather than
being chosen by a postcondition. There is no claim of decidable equality. -/
def ValidTrace : List (Transition S T) → Session S T → Session S T → Prop
  | [], s, t => s = t
  | x::xs, s, t => x.before = s ∧ ValidTrace xs (after S T x) t

def traceDelta : List (Transition S T) → Delta
  | [] => zeroDelta
  | x::xs => addDelta (effect S T x) (traceDelta xs)

theorem singleton_valid (x : Transition S T) : ValidTrace S T [x] x.before (after S T x) := ⟨rfl,rfl⟩

theorem valid_append (xs ys : List (Transition S T)) (s t u : Session S T)
    (hx : ValidTrace S T xs s t) (hy : ValidTrace S T ys t u) : ValidTrace S T (xs++ys) s u := by
  induction xs generalizing s with
  | nil =>
    change s = t at hx
    subst s
    exact hy
  | cons x xs ih =>
    change x.before = s ∧ ValidTrace S T xs (after S T x) t at hx
    exact ⟨hx.1, ih (after S T x) hx.2⟩

theorem trace_laws (xs : List (Transition S T)) (s t : Session S T)
    (h : ValidTrace S T xs s t) : Laws S T s t (traceDelta S T xs) := by
  induction xs generalizing s with
  | nil =>
    change s = t at h
    subst s
    exact laws_refl S T t
  | cons x xs ih =>
    change x.before = s ∧ ValidTrace S T xs (after S T x) t at h
    rw [← h.1]
    exact laws_compose S T x.before (after S T x) t (effect S T x) (traceDelta S T xs)
      (action_laws S T x.before x.action) (ih (after S T x) h.2)

theorem trace_objective (xs : List (Transition S T)) (s t : Session S T) (h : ValidTrace S T xs s t) :
    objective S T t + (traceDelta S T xs).gain = objective S T s + (traceDelta S T xs).overhead :=
  (trace_laws S T xs s t h).objLaw

theorem trace_funds (xs : List (Transition S T)) (s t : Session S T) (h : ValidTrace S T xs s t) : funds S T t = funds S T s :=
  (trace_laws S T xs s t h).fundLaw

theorem trace_preserves (xs : List (Transition S T)) (s t : Session S T) (h : ValidTrace S T xs s t) : Preserves S T s t :=
  (trace_laws S T xs s t h).provenance

theorem trace_paid_bound (xs : List (Transition S T)) (s t : Session S T) (h : ValidTrace S T xs s t) :
    (traceDelta S T xs).paidAttempts + t.live.balance ≤ s.live.balance := by
  have hw := (trace_laws S T xs s t h).paidLaw
  have hf := trace_funds S T xs s t h
  unfold CRTT.AdmissionAccounting.funds at hf
  omega

theorem trace_accepted_bound (xs : List (Transition S T)) (s t : Session S T) (h : ValidTrace S T xs s t) :
    (traceDelta S T xs).accepted ≤ objective S T s + (traceDelta S T xs).overhead := by
  have h1 := (trace_laws S T xs s t h).acceptLaw
  have h2 := trace_objective S T xs s t h
  omega

def finish (s : Session S T) : Session S T := advance S T s s.live.current.reserve

theorem finish_bill (s : Session S T) : spent S T (finish S T s) = objective S T s :=
  advance_spent S T s s.live.current.reserve

theorem finish_full (s : Session S T) (m : Morphism S T) :
    m ∈ (finish S T s).live.current.frontier.certificates ↔ m ∈ discoverAll S T :=
  CRTT.ControllerReplacement.finish_full S T s.live m

theorem trace_completion (xs : List (Transition S T)) (s t : Session S T) (_h : ValidTrace S T xs s t) (m : Morphism S T) :
    m ∈ (finish S T t).live.current.frontier.certificates ↔ m ∈ discoverAll S T :=
  finish_full S T t m

theorem trace_final_gain_iff (xs : List (Transition S T)) (s t : Session S T) (h : ValidTrace S T xs s t) :
    spent S T (finish S T t) < spent S T (finish S T s) ↔
      (traceDelta S T xs).overhead < (traceDelta S T xs).gain := by
  rw [finish_bill S T t, finish_bill S T s]
  have he := trace_objective S T xs s t h
  constructor
  · intro hh; omega
  · intro hh; omega

namespace Witnesses
open CRTT.ControllerReplacement.Witnesses (src dst fundedLive)
open CRTT.RelativeEvidence.Witnesses (liveOffer)

def initial : Session src dst := CRTT.AdmissionAccounting.start src dst fundedLive

def acquisition : Transition src dst := ⟨initial, .evidence "external model charge" 0 (by decide)⟩
def positiveSwitch : Transition src dst := ⟨after src dst acquisition, .attempt liveOffer 0⟩
def positiveFinish : Transition src dst := ⟨after src dst positiveSwitch, .advance 100⟩
def positiveTrace : List (Transition src dst) := [acquisition, positiveSwitch, positiveFinish]

theorem positive_valid : ValidTrace src dst positiveTrace initial (after src dst positiveFinish) :=
  ⟨rfl,rfl,rfl,rfl⟩

theorem positive_cost : spent src dst (after src dst positiveFinish) = 4 ∧
    objective src dst initial = 7 ∧ (traceDelta src dst positiveTrace).gain = 4 ∧
    (traceDelta src dst positiveTrace).overhead = 1 := by decide

-- A 5-unit check is affordable but cannot certify strictly positive gain.
-- The following 1-unit check succeeds against the unchanged old controller.
def expensiveReject : Transition src dst := ⟨initial, .attempt liveOffer 4⟩
def negativeSwitch : Transition src dst := ⟨after src dst expensiveReject, .attempt liveOffer 0⟩
def negativeTrace : List (Transition src dst) := [expensiveReject,negativeSwitch]

theorem negative_valid : ValidTrace src dst negativeTrace initial (after src dst negativeSwitch) :=
  ⟨rfl,rfl,rfl⟩

theorem negative_cost : spent src dst (finish src dst (after src dst negativeSwitch)) = 8 ∧
    (traceDelta src dst negativeTrace).gain = 4 ∧ (traceDelta src dst negativeTrace).overhead = 5 := by decide

end Witnesses

#print axioms run_shift_spent
#print axioms execute_prefix_bill
#print axioms remainingBill_prefix
#print axioms advance_spent
#print axioms advance_funds
#print axioms advance_objective
#print axioms preserves_refl
#print axioms preserves_trans
#print axioms advance_preserves
#print axioms apply_preserves
#print axioms evidence_preserves
#print axioms laws_refl
#print axioms laws_compose
#print axioms advance_laws
#print axioms evidence_laws
#print axioms apply_laws
#print axioms action_laws
#print axioms singleton_valid
#print axioms valid_append
#print axioms trace_laws
#print axioms trace_objective
#print axioms trace_funds
#print axioms trace_preserves
#print axioms trace_paid_bound
#print axioms trace_accepted_bound
#print axioms finish_bill
#print axioms finish_full
#print axioms trace_completion
#print axioms trace_final_gain_iff
#print axioms Witnesses.positive_valid
#print axioms Witnesses.positive_cost
#print axioms Witnesses.negative_valid
#print axioms Witnesses.negative_cost
end CRTT.RecursiveTrace
