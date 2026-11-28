import MetaPolicy

/-! T31: closure of finite histories under the SAME T30 provider and checker.
A plan may supply a new finite policy at the current machine, but it cannot
replace the provider or the root contract. Costs are the declared model.
The trace stores actual results, not freely chosen final states. -/
namespace CRTT.MetaClosure
open CRTT.MorphismDiscovery
open CRTT.ControllerReplacement (Continuation)
open CRTT.AdmissionAccounting (Session spent funds)
open CRTT.RecursiveTrace (Preserves)
open CRTT.MetaPolicy (Machine Provider Proposal UpgradeResult UpgradeStatus
  UpgradeEvent Event Outcome Frame Tree affordable pay pay_spent setupLabel upgrade policyBill)
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

variable {sw sp sa tw tp ta : Nat}
variable (S : IndexedTask sw sp sa) (T : IndexedTask tw tp ta)
variable {old : Continuation S T}

def debit (base : Nat) : UpgradeStatus → Nat
  | .deferred => 0
  | _ => base+1

def paidOne : UpgradeStatus → Nat
  | .deferred => 0
  | _ => 1

def acceptedOne : UpgradeStatus → Nat
  | .accepted => 1
  | _ => 0

structure Facts (p : Provider S T old) (m : Machine S T old) (base : Nat)
    (r : UpgradeResult S T p m) : Prop where
  meter : spent S T r.next.frame.session = spent S T m.frame.session + debit base r.status
  historyLength : r.next.history.length = m.history.length + paidOne r.status
  deferredSame : r.status = .deferred → r.next = m

/-- The two positive-price branches pay exactly the setup tariff, regardless
of acceptance. The third branch does not invoke the proposal factory. -/
theorem upgrade_facts (p : Provider S T old) (m : Machine S T old) (base : Nat)
    (make : (h : affordable S T m.frame base) → Unit → Proposal S T p m base h) :
    Facts S T p m base (upgrade S T p m base make) := by
  by_cases h : affordable S T m.frame base
  · simp only [upgrade, dite_eq_left h]
    by_cases hg : (make h ()).newUpper < (make h ()).oldLower
    · simp only [dite_eq_left hg]
      exact ⟨pay_spent S T m.frame setupLabel base h, rfl, fun hv => by cases hv⟩
    · simp only [dite_eq_right hg]
      exact ⟨pay_spent S T m.frame setupLabel base h, rfl, fun hv => by cases hv⟩
  · simp only [upgrade, dite_eq_right h]
    exact ⟨rfl,rfl,fun _ => rfl⟩

/-- Plan factories are externally supplied. Only the base tariff is needed
before the check; the proof-bearing proposal thunk is invoked by T30 after
funding. No scheduler synthesis or free cost oracle is claimed. -/
structure Plan (p : Provider S T old) where
  base : Nat
  make : (m : Machine S T old) → (h : affordable S T m.frame base) → Unit → Proposal S T p m base h

structure Transition (p : Provider S T old) where
  before : Machine S T old
  base : Nat
  make : (h : affordable S T before.frame base) → Unit → Proposal S T p before base h
  result : UpgradeResult S T p before
  executed : result = upgrade S T p before base make

def recordUpgrade (p : Provider S T old) (m : Machine S T old) (base : Nat)
    (make : (h : affordable S T m.frame base) → Unit → Proposal S T p m base h) : Transition S T p :=
  ⟨m,base,make,upgrade S T p m base make,rfl⟩

def executePlan (p : Provider S T old) (m : Machine S T old) (plan : Plan S T p) : Transition S T p :=
  recordUpgrade S T p m plan.base (plan.make m)

def after {p : Provider S T old} (x : Transition S T p) : Machine S T old := x.result.next

theorem transition_facts {p : Provider S T old} (x : Transition S T p) :
    Facts S T p x.before x.base x.result := by
  rw [x.executed]
  exact upgrade_facts S T p x.before x.base x.make

/-- An explicit connected history; no decidable equality is assumed for
function-bearing states. All endpoints are actual recorded transition results. -/
def ValidTrace (p : Provider S T old) : List (Transition S T p) → Machine S T old → Machine S T old → Prop
  | [], m, n => m = n
  | x::xs, m, n => x.before = m ∧ ValidTrace p xs (after S T x) n

def chargeTotal {p : Provider S T old} : List (Transition S T p) → Nat
  | [] => 0
  | x::xs => debit x.base x.result.status + chargeTotal xs

def paidCount {p : Provider S T old} : List (Transition S T p) → Nat
  | [] => 0
  | x::xs => paidOne x.result.status + paidCount xs

def acceptedCount {p : Provider S T old} : List (Transition S T p) → Nat
  | [] => 0
  | x::xs => acceptedOne x.result.status + acceptedCount xs

structure Laws (p : Provider S T old) (xs : List (Transition S T p)) (m n : Machine S T old) : Prop where
  preserved : Preserves S T m.frame.session n.frame.session
  conserved : funds S T n.frame.session = funds S T m.frame.session
  historyKept : ∃ added, n.history = added ++ m.history
  meter : spent S T n.frame.session = spent S T m.frame.session + chargeTotal S T xs
  historyLength : n.history.length = m.history.length + paidCount S T xs
  paidBound : paidCount S T xs ≤ chargeTotal S T xs
  acceptedBound : acceptedCount S T xs ≤ paidCount S T xs

/-- One inductive closure law for every finite connected history with fixed p.
The length and the policy-tree size may vary; no higher verifier is added. -/
theorem trace_laws (p : Provider S T old) (xs : List (Transition S T p)) (m n : Machine S T old)
    (h : ValidTrace S T p xs m n) : Laws S T p xs m n := by
  induction xs generalizing m with
  | nil =>
    change m = n at h
    subst m
    exact ⟨CRTT.RecursiveTrace.preserves_refl S T n.frame.session,rfl,⟨[],rfl⟩,rfl,rfl,Nat.le_refl _,Nat.le_refl _⟩
  | cons x xs ih =>
    change x.before = m ∧ ValidTrace S T p xs (after S T x) n at h
    have tail := ih (after S T x) h.2
    have hlaws := transition_facts S T x
    rw [← h.1]
    refine ⟨CRTT.RecursiveTrace.preserves_trans S T _ _ _ x.result.preserved tail.preserved,
      tail.conserved.trans x.result.conserved, ?_, ?_, ?_, ?_, ?_⟩
    · obtain ⟨a,ha⟩ := x.result.historyKept
      obtain ⟨b,hb⟩ := tail.historyKept
      refine ⟨b++a,?_⟩
      -- `after S T x` is definitionally `x.result.next`, and the goal has already
      -- been rewritten to `n.history` by the `rw [← h.1]` above, so `ha` is applied
      -- after unfolding the projection through `show`.
      rw [hb]
      rw [show after S T x = x.result.next from rfl, ha, List.append_assoc]
    · change spent S T n.frame.session = spent S T x.before.frame.session +
        (debit x.base x.result.status + chargeTotal S T xs)
      have ht := tail.meter
      change spent S T n.frame.session = spent S T x.result.next.frame.session + chargeTotal S T xs at ht
      have hl := hlaws.meter
      omega
    · change n.history.length = x.before.history.length + (paidOne x.result.status + paidCount S T xs)
      have ht := tail.historyLength
      change n.history.length = x.result.next.history.length + paidCount S T xs at ht
      have hl := hlaws.historyLength
      omega
    · change paidOne x.result.status + paidCount S T xs ≤ debit x.base x.result.status + chargeTotal S T xs
      have hp : paidOne x.result.status ≤ debit x.base x.result.status := by
        cases x.result.status with
        | deferred => exact Nat.le_refl 0
        | rejected => change 1 ≤ x.base+1; omega
        | accepted => change 1 ≤ x.base+1; omega
      exact Nat.add_le_add hp tail.paidBound
    · change acceptedOne x.result.status + acceptedCount S T xs ≤ paidOne x.result.status + paidCount S T xs
      have hp : acceptedOne x.result.status ≤ paidOne x.result.status := by
        cases x.result.status <;> decide
      exact Nat.add_le_add hp tail.acceptedBound

theorem trace_paid_balance (p : Provider S T old) (xs : List (Transition S T p)) (m n : Machine S T old)
    (h : ValidTrace S T p xs m n) : paidCount S T xs + n.frame.session.live.balance ≤ m.frame.session.live.balance := by
  have l := trace_laws S T p xs m n h
  have hc := l.conserved
  unfold CRTT.AdmissionAccounting.funds at hc
  have hm := l.meter
  have hp := l.paidBound
  omega

theorem trace_liquid (p : Provider S T old) (xs : List (Transition S T p)) (m n : Machine S T old)
    (_h : ValidTrace S T p xs m n) : n.frame.session.live.current.reserve ≤ n.frame.session.live.balance :=
  n.frame.session.live.liquid

/-- Rejection may change which operations a later tree can afford. Thus a
rejected meta-upgrade does NOT have an assumed +fee effect on policyBill.
Only accepted and deferred transitions have the following monotonic law. -/
theorem transition_gain {p : Provider S T old} (x : Transition S T p) :
    x.result.status ≠ .rejected →
    policyBill S T p (after S T x).active (after S T x).frame + acceptedOne x.result.status ≤
      policyBill S T p x.before.active x.before.frame := by
  cases hv : x.result.status with
  | deferred =>
    intro _
    have he := (transition_facts S T x).deferredSame hv
    change policyBill S T p x.result.next.active x.result.next.frame + 0 ≤ policyBill S T p x.before.active x.before.frame
    rw [he] <;> exact Nat.le_refl _
  | rejected =>
    intro h
    exact False.elim (h rfl)
  | accepted =>
    intro _
    have hg := x.result.acceptedGain hv
    change policyBill S T p x.result.next.active x.result.next.frame + 1 ≤ policyBill S T p x.before.active x.before.frame
    omega

theorem trace_no_rejection_gain (p : Provider S T old) (xs : List (Transition S T p)) (m n : Machine S T old)
    (h : ValidTrace S T p xs m n) (hn : ∀ x ∈ xs, x.result.status ≠ .rejected) :
    policyBill S T p n.active n.frame + acceptedCount S T xs ≤ policyBill S T p m.active m.frame := by
  induction xs generalizing m with
  | nil =>
    change m = n at h
    subst m
    exact Nat.le_refl _
  | cons x xs ih =>
    change x.before = m ∧ ValidTrace S T p xs (after S T x) n at h
    have h1 := transition_gain S T x (hn x (List.Mem.head _))
    have h2 := ih (after S T x) h.2 (fun y hy => hn y (List.mem_cons.mpr (Or.inr hy)))
    rw [← h.1]
    change policyBill S T p n.active n.frame + (acceptedOne x.result.status + acceptedCount S T xs) ≤
      policyBill S T p x.before.active x.before.frame
    omega

/-! A bounded executable schedule. Every supplied plan consumes one list cell,
even if its funding guard returns deferred. No unbounded free retry loop. -/
structure Run (p : Provider S T old) (m : Machine S T old) (length : Nat) where
  final : Machine S T old
  trace : List (Transition S T p)
  connected : ValidTrace S T p trace m final
  lengthEq : trace.length = length

def runPlans (p : Provider S T old) : (plans : List (Plan S T p)) → (m : Machine S T old) → Run S T p m plans.length
  | [], m => ⟨m,[],rfl,rfl⟩
  | plan::plans, m =>
    let x := executePlan S T p m plan
    let r := runPlans p plans (after S T x)
    ⟨r.final,x::r.trace,⟨rfl,r.connected⟩,congrArg Nat.succ r.lengthEq⟩

theorem run_laws (p : Provider S T old) (plans : List (Plan S T p)) (m : Machine S T old) :
    Laws S T p (runPlans S T p plans m).trace m (runPlans S T p plans m).final :=
  trace_laws S T p _ _ _ (runPlans S T p plans m).connected

theorem run_steps (p : Provider S T old) (plans : List (Plan S T p)) (m : Machine S T old) :
    (runPlans S T p plans m).trace.length = plans.length := (runPlans S T p plans m).lengthEq

/-! The closed execution uses the final installed policy exactly once. Its
Outcome retains observations and prepared offers (including deferred attempts).
The final funded root completion then discharges the original obligations. -/
structure Closed (p : Provider S T old) (m : Machine S T old) (length : Nat) where
  upgrades : Run S T p m length
  episode : Outcome S T upgrades.final.frame.session
  interpreted : episode = CRTT.MetaPolicy.interpret S T p upgrades.final.active upgrades.final.frame
  final : Session S T
  finished : final = CRTT.RecursiveTrace.finish S T episode.final

def closeRun (p : Provider S T old) (m : Machine S T old) (n : Nat) (r : Run S T p m n) : Closed S T p m n :=
  let ep := CRTT.MetaPolicy.interpret S T p r.final.active r.final.frame
  ⟨r,ep,rfl,CRTT.RecursiveTrace.finish S T ep.final,rfl⟩

def close (p : Provider S T old) (plans : List (Plan S T p)) (m : Machine S T old) : Closed S T p m plans.length :=
  closeRun S T p m plans.length (runPlans S T p plans m)

def history {p : Provider S T old} {m : Machine S T old} {n : Nat} (r : Closed S T p m n) : List (Sum UpgradeEvent (Event S T)) :=
  r.upgrades.final.history.reverse.map Sum.inl ++ r.episode.events.map Sum.inr

theorem closed_preserves (p : Provider S T old) (m : Machine S T old) (n : Nat) (r : Closed S T p m n) :
    Preserves S T m.frame.session r.final := by
  rw [r.finished]
  have h := (trace_laws S T p _ _ _ r.upgrades.connected).preserved
  exact CRTT.RecursiveTrace.preserves_trans S T _ _ _ h
    (CRTT.RecursiveTrace.preserves_trans S T _ _ _ r.episode.preserved
      (CRTT.RecursiveTrace.advance_preserves S T r.episode.final r.episode.final.live.current.reserve))

theorem closed_funds (p : Provider S T old) (m : Machine S T old) (n : Nat) (r : Closed S T p m n) :
    funds S T r.final = funds S T m.frame.session := by
  rw [r.finished]
  exact (CRTT.RecursiveTrace.advance_funds S T r.episode.final r.episode.final.live.current.reserve).trans
    (r.episode.conserved.trans (trace_laws S T p _ _ _ r.upgrades.connected).conserved)

theorem closed_complete (p : Provider S T old) (m : Machine S T old) (n : Nat) (r : Closed S T p m n) (x : Morphism S T) :
    x ∈ r.final.live.current.frontier.certificates ↔ x ∈ discoverAll S T := by
  rw [r.finished]
  exact CRTT.RecursiveTrace.finish_full S T r.episode.final x

theorem closed_bill (p : Provider S T old) (m : Machine S T old) (n : Nat) (r : Closed S T p m n) :
    spent S T r.final = policyBill S T p r.upgrades.final.active r.upgrades.final.frame := by
  rw [r.finished,r.interpreted]
  exact CRTT.MetaPolicy.policyBill_complete S T p r.upgrades.final.active r.upgrades.final.frame

theorem closed_gain (p : Provider S T old) (m : Machine S T old) (n : Nat) (r : Closed S T p m n)
    (h : ∀ x ∈ r.upgrades.trace, x.result.status ≠ .rejected) :
    spent S T r.final + acceptedCount S T r.upgrades.trace ≤ policyBill S T p m.active m.frame := by
  rw [closed_bill S T p m n r]
  exact trace_no_rejection_gain S T p _ _ _ r.upgrades.connected h

theorem closed_history (p : Provider S T old) (m : Machine S T old) (n : Nat) (r : Closed S T p m n) :
    (∃ added, r.upgrades.final.history = added ++ m.history) ∧
    (∃ prior, history S T r = prior ++ r.episode.events.map Sum.inr) :=
  ⟨(trace_laws S T p _ _ _ r.upgrades.connected).historyKept,⟨r.upgrades.final.history.reverse.map Sum.inl,rfl⟩⟩

/-- Universal conservative bound used by the deliberately non-improving
control plan. It uses conservation, not a prospective execution in the gate. -/
theorem policyBill_le_funds (p : Provider S T old) (t : Tree) (f : Frame S T old) :
    policyBill S T p t f ≤ funds S T f.session := by
  let ep := CRTT.MetaPolicy.interpret S T p t f
  let fin := CRTT.RecursiveTrace.finish S T ep.final
  have hf : funds S T fin = funds S T f.session :=
    (CRTT.RecursiveTrace.advance_funds S T ep.final ep.final.live.current.reserve).trans ep.conserved
  have hb : spent S T fin = policyBill S T p t f := CRTT.MetaPolicy.policyBill_complete S T p t f
  calc
    policyBill S T p t f = spent S T fin := hb.symm
    _ ≤ funds S T fin := by
      unfold CRTT.AdmissionAccounting.funds
      omega
    _ = funds S T f.session := hf

/-- A non-improving control factory for any current machine. The lower bound
zero deliberately prevents acceptance. This tests actual list execution. -/
def conservativeControl (p : Provider S T old) : Plan S T p where
  base := 0
  make := fun m h _ =>
    { tree := m.active
      oldLower := 0
      newUpper := funds S T m.frame.session
      oldSound := Nat.zero_le _
      newSound := Nat.le_trans
        (policyBill_le_funds S T p m.active (pay S T m.frame setupLabel 0 h))
        (Nat.le_of_eq (CRTT.MetaPolicy.pay_funds S T m.frame setupLabel 0 h)) }

namespace Witnesses
open CRTT.ControllerReplacement.Witnesses (src dst)
open CRTT.MetaPolicy.Witnesses (goodProvider goodFrame incumbent makeUpgrade tightFrame)

def first : Transition src dst goodProvider := recordUpgrade src dst goodProvider incumbent 0 makeUpgrade

def firstRun : Run src dst goodProvider incumbent 1 :=
  ⟨after src dst first,[first],⟨rfl,rfl⟩,rfl⟩

def firstClosed := closeRun src dst goodProvider incumbent 1 firstRun

theorem first_complete_bill : spent src dst firstClosed.final = 6 ∧
    paidCount src dst firstRun.trace = 1 ∧ acceptedCount src dst firstRun.trace = 1 := by decide

-- Retaining the very same policy after the paid check gives no certified
-- improvement. This is a CLOSED, pre-certified proposal, not a generic oracle.
def secondMake (h : affordable src dst (after src dst first).frame 0) (_ : Unit) :
    Proposal src dst goodProvider (after src dst first) 0 h where
  tree := (after src dst first).active
  oldLower := 6
  newUpper := 7
  oldSound := by decide
  newSound := by decide +revert

def second : Transition src dst goodProvider :=
  recordUpgrade src dst goodProvider (after src dst first) 0 secondMake

def secondRun : Run src dst goodProvider incumbent 2 :=
  ⟨after src dst second,[first,second],⟨rfl,rfl,rfl⟩,rfl⟩

def secondClosed := closeRun src dst goodProvider incumbent 2 secondRun

theorem paid_rejection_erases_saving : second.result.status = .rejected ∧
    spent src dst secondClosed.final = 7 ∧ paidCount src dst secondRun.trace = 2 := by decide

/-- A deliberately redundant, but finite, incumbent. Repeated reads are
allowed by T30's executable tree language, not by its one-query legal class. -/
def repeatProbe : Nat → Tree
  | 0 => .act true
  | n+1 => .observe () (.act false) (repeatProbe n)

def redundant : Machine src dst CRTT.ControllerReplacement.Witnesses.oldContinuation :=
  ⟨goodFrame,repeatProbe 4,[]⟩

def improveOne (h : affordable src dst redundant.frame 0) (_ : Unit) :
    Proposal src dst goodProvider redundant 0 h where
  tree := repeatProbe 2
  oldLower := 8
  newUpper := 7
  oldSound := by decide
  newSound := by decide +revert

def one : Transition src dst goodProvider := recordUpgrade src dst goodProvider redundant 0 improveOne

def improveTwo (h : affordable src dst (after src dst one).frame 0) (_ : Unit) :
    Proposal src dst goodProvider (after src dst one) 0 h where
  tree := .act true
  oldLower := 7
  newUpper := 6
  oldSound := by decide
  newSound := by decide +revert

def two : Transition src dst goodProvider := recordUpgrade src dst goodProvider (after src dst one) 0 improveTwo

def twoRun : Run src dst goodProvider redundant 2 :=
  ⟨after src dst two,[one,two],⟨rfl,rfl,rfl⟩,rfl⟩

def twoClosed := closeRun src dst goodProvider redundant 2 twoRun

theorem two_accepted_changes : acceptedCount src dst twoRun.trace = 2 ∧
    policyBill src dst goodProvider redundant.active redundant.frame = 8 ∧
    spent src dst twoClosed.final = 6 := by decide

def controls := close src dst goodProvider
  [conservativeControl src dst goodProvider,conservativeControl src dst goodProvider] incumbent

theorem actual_schedule_rejections : controls.upgrades.trace.length = 2 ∧
    paidCount src dst controls.upgrades.trace = 2 ∧ acceptedCount src dst controls.upgrades.trace = 0 ∧
    spent src dst controls.final = 9 := by decide

def tightMachine : Machine src dst CRTT.ControllerReplacement.Witnesses.oldContinuation :=
  ⟨tightFrame,.act false,[]⟩

def deferredControls := close src dst goodProvider
  [conservativeControl src dst goodProvider,conservativeControl src dst goodProvider] tightMachine

theorem actual_schedule_deferred : deferredControls.upgrades.trace.length = 2 ∧
    paidCount src dst deferredControls.upgrades.trace = 0 ∧ spent src dst deferredControls.final = 7 := by decide

end Witnesses

#print axioms upgrade_facts
#print axioms transition_facts
#print axioms trace_laws
#print axioms trace_paid_balance
#print axioms trace_liquid
#print axioms transition_gain
#print axioms trace_no_rejection_gain
#print axioms run_laws
#print axioms run_steps
#print axioms closed_preserves
#print axioms closed_funds
#print axioms closed_complete
#print axioms closed_bill
#print axioms closed_gain
#print axioms closed_history
#print axioms policyBill_le_funds
#print axioms Witnesses.first_complete_bill
#print axioms Witnesses.paid_rejection_erases_saving
#print axioms Witnesses.two_accepted_changes
#print axioms Witnesses.actual_schedule_rejections
#print axioms Witnesses.actual_schedule_deferred
end CRTT.MetaClosure
