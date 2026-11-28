import RecursiveTrace

/-! T30: one finite executable, replaceable proposal policy. The root
continuation is fixed during an acquisition episode. A T19 tree selects
keep or prepare-and-attempt. The fixed T29b gate is the only authority
for installing a pruning controller. Observation and preparation thunks
are invoked only in their funded branches. Fees are modeled Nat tariffs,
not measured machine time. The closed catalogue is pre-certified. -/
namespace CRTT.MetaPolicy
open CRTT.MorphismDiscovery
open CRTT.AdaptiveObservation (Investigation Problem Legal)
open CRTT.ControllerReplacement (Continuation Verdict)
open CRTT.RelativeEvidence (RelativeOffer)
open CRTT.AdmissionAccounting (Session funds spent objective recordEvidence tryRelative)
open CRTT.RecursiveTrace (Preserves)
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

abbrev Tree := Investigation Unit Bool

variable {sw sp sa tw tp ta : Nat}
variable (S : IndexedTask sw sp sa) (T : IndexedTask tw tp ta)

/-- Paid acquisition keeps the exact continuation. There is no equality
procedure on function-bearing states and no stale-offer guessing. -/
structure Frame (old : Continuation S T) where
  session : Session S T
  fixed : session.live.current = old

def affordable {old : Continuation S T} (f : Frame S T old) (base : Nat) : Prop :=
  base+1+f.session.live.current.reserve ≤ f.session.live.balance

instance {old : Continuation S T} (f : Frame S T old) (base : Nat) : Decidable (affordable S T f base) :=
  inferInstanceAs (Decidable (base+1+f.session.live.current.reserve ≤ f.session.live.balance))

def pay {old : Continuation S T} (f : Frame S T old) (label : String) (base : Nat)
    (h : affordable S T f base) : Frame S T old :=
  ⟨recordEvidence S T f.session label base h,
    (CRTT.AdmissionAccounting.evidence_current S T f.session label base h).trans f.fixed⟩

theorem pay_funds {old : Continuation S T} (f : Frame S T old) (label : String) (base : Nat)
    (h : affordable S T f base) : funds S T (pay S T f label base h).session = funds S T f.session :=
  CRTT.AdmissionAccounting.evidence_funds S T f.session label base h

theorem pay_spent {old : Continuation S T} (f : Frame S T old) (label : String) (base : Nat)
    (h : affordable S T f base) : spent S T (pay S T f label base h).session = spent S T f.session + (base+1) :=
  CRTT.AdmissionAccounting.evidence_charge S T f.session label base h

theorem pay_preserves {old : Continuation S T} (f : Frame S T old) (label : String) (base : Nat)
    (h : affordable S T f base) : Preserves S T f.session (pay S T f label base h).session :=
  CRTT.RecursiveTrace.evidence_preserves S T f.session label base h

structure Provider (old : Continuation S T) where
  probe : Unit → Bool
  prepare : Unit → RelativeOffer S T old
  queryBase : Nat
  prepBase : Nat
  checkBase : Nat

/-- Casting through the recorded equality preserves the precise old frontier. -/
def offerAt {old : Continuation S T} (f : Frame S T old) (o : RelativeOffer S T old) :
    RelativeOffer S T f.session.live.current :=
  cast (congrArg (RelativeOffer S T) f.fixed.symm) o

inductive Event where
  | observed (answer : Bool) (fee : Nat)
  | prepared (old : Continuation S T) (offer : RelativeOffer S T old) (fee : Nat)
  | attempted (v : Verdict)

inductive Status where
  | kept | blocked | attempted (v : Verdict)
  deriving DecidableEq, Repr

/-- Proofs are built by composition of the verified local laws. The actual
observations are returned separately from the authoritative charge journal. -/
structure Outcome (s : Session S T) where
  final : Session S T
  events : List (Event S T)
  status : Status
  preserved : Preserves S T s final
  conserved : funds S T final = funds S T s

def stop (s : Session S T) (status : Status) : Outcome S T s :=
  ⟨s, [], status, CRTT.RecursiveTrace.preserves_refl S T s, rfl⟩

def attach {old : Continuation S T} (f : Frame S T old) (label : String) (base : Nat)
    (h : affordable S T f base) (ev : Event S T)
    (r : Outcome S T (pay S T f label base h).session) : Outcome S T f.session :=
  ⟨r.final, ev :: r.events, r.status,
    CRTT.RecursiveTrace.preserves_trans S T _ _ _ (pay_preserves S T f label base h) r.preserved,
    r.conserved.trans (pay_funds S T f label base h)⟩

def attempt (s : Session S T) (o : RelativeOffer S T s.live.current) (base : Nat) : Outcome S T s :=
  let r := tryRelative S T s o base
  ⟨r.2, [.attempted r.1], .attempted r.1,
    CRTT.RecursiveTrace.apply_preserves S T s o (base+1) r.1 rfl,
    CRTT.AdmissionAccounting.tryRelative_funds S T s o base⟩

/-- Preparation is a paid invocation of the proof-bearing offer factory,
not a numeric receipt that pretends evidence has been acquired. -/
def prepareAndAttempt {old : Continuation S T} (p : Provider S T old) (f : Frame S T old) : Outcome S T f.session :=
  if h : affordable S T f p.prepBase then
    let g := pay S T f "T30: prepare offer" p.prepBase h
    let prepared := p.prepare ()
    let o := offerAt S T g prepared
    attach S T f "T30: prepare offer" p.prepBase h (.prepared old prepared (p.prepBase+1))
      (attempt S T g.session o p.checkBase)
  else stop S T f.session .blocked

/-- Structural recursion on a finite tree, irrespective of affordability.
A failed funding check returns without invoking the corresponding thunk. -/
def interpret {old : Continuation S T} (p : Provider S T old) :
    (t : Tree) → (f : Frame S T old) → Outcome S T f.session
  | .act a, f => if a then prepareAndAttempt S T p f else stop S T f.session .kept
  | .observe _ l r, f =>
    if h : affordable S T f p.queryBase then
      let g := pay S T f "T30: observe" p.queryBase h
      let b := p.probe ()
      let out := if b then interpret p r g else interpret p l g
      attach S T f "T30: observe" p.queryBase h (.observed b (p.queryBase+1)) out
    else stop S T f.session .blocked

theorem interpret_funds {old : Continuation S T} (p : Provider S T old) (t : Tree) (f : Frame S T old) :
    funds S T (interpret S T p t f).final = funds S T f.session :=
  (interpret S T p t f).conserved

theorem interpret_preserves {old : Continuation S T} (p : Provider S T old) (t : Tree) (f : Frame S T old) :
    Preserves S T f.session (interpret S T p t f).final := (interpret S T p t f).preserved

theorem interpret_complete {old : Continuation S T} (p : Provider S T old) (t : Tree) (f : Frame S T old) (m : Morphism S T) :
    m ∈ (CRTT.RecursiveTrace.finish S T (interpret S T p t f).final).live.current.frontier.certificates ↔ m ∈ discoverAll S T :=
  CRTT.RecursiveTrace.finish_full S T (interpret S T p t f).final m

/-- Specification of the all-in bill, including already recorded expenses.
Never called by the policy-upgrade checker. -/
def policyBill {old : Continuation S T} (p : Provider S T old) (t : Tree) (f : Frame S T old) : Nat :=
  objective S T (interpret S T p t f).final

theorem policyBill_complete {old : Continuation S T} (p : Provider S T old) (t : Tree) (f : Frame S T old) :
    spent S T (CRTT.RecursiveTrace.finish S T (interpret S T p t f).final) = policyBill S T p t f :=
  CRTT.RecursiveTrace.finish_bill S T (interpret S T p t f).final

/-! The proposal policy is now explicit mutable state. Upgrades run BEFORE
execution of the episode tree. Their checks use a proof-bearing pair of bounds
for the exact before and post-payment frames, not an uncharged future run. -/
inductive UpgradeStatus where
  | deferred | rejected | accepted
  deriving DecidableEq, Repr

structure UpgradeEvent where
  fee : Nat
  status : UpgradeStatus
  prior : Tree
  candidate : Tree
  balanceBefore : Nat
  oldLower : Nat
  newUpper : Nat

structure Machine (old : Continuation S T) where
  frame : Frame S T old
  active : Tree
  history : List UpgradeEvent

abbrev setupLabel : String := "T30: policy synthesis and admission"

structure Proposal {old : Continuation S T} (p : Provider S T old) (m : Machine S T old)
    (base : Nat) (h : affordable S T m.frame base) where
  tree : Tree
  oldLower : Nat
  newUpper : Nat
  oldSound : oldLower ≤ policyBill S T p m.active m.frame
  newSound : policyBill S T p tree (pay S T m.frame setupLabel base h) ≤ newUpper

structure UpgradeResult {old : Continuation S T} (p : Provider S T old) (m : Machine S T old) where
  next : Machine S T old
  status : UpgradeStatus
  preserved : Preserves S T m.frame.session next.frame.session
  conserved : funds S T next.frame.session = funds S T m.frame.session
  historyKept : ∃ added, next.history = added ++ m.history
  acceptedGain : status = .accepted → policyBill S T p next.active next.frame < policyBill S T p m.active m.frame

/-- The proof-bearing provider can synthesize a proposal after payment. The
fixed numeric comparison includes setup cost through the post-payment frame.
The prepayment covers the declared synthesis/check tariff; proof production
outside this runtime is not a physical timing measurement. -/
def upgrade {old : Continuation S T} (p : Provider S T old) (m : Machine S T old) (base : Nat)
    (make : (h : affordable S T m.frame base) → Unit → Proposal S T p m base h) : UpgradeResult S T p m :=
  if h : affordable S T m.frame base then
    let g := pay S T m.frame setupLabel base h
    let o := make h ()
    if hg : o.newUpper < o.oldLower then
      let ev : UpgradeEvent := ⟨base+1,.accepted,m.active,o.tree,m.frame.session.live.balance,o.oldLower,o.newUpper⟩
      ⟨⟨g,o.tree,ev :: m.history⟩,.accepted,
        pay_preserves S T m.frame setupLabel base h, pay_funds S T m.frame setupLabel base h,
        ⟨[ev],rfl⟩, fun _ => Nat.lt_of_le_of_lt o.newSound (Nat.lt_of_lt_of_le hg o.oldSound)⟩
    else
      let ev : UpgradeEvent := ⟨base+1,.rejected,m.active,o.tree,m.frame.session.live.balance,o.oldLower,o.newUpper⟩
      ⟨⟨g,m.active,ev :: m.history⟩,.rejected,
        pay_preserves S T m.frame setupLabel base h, pay_funds S T m.frame setupLabel base h,
        ⟨[ev],rfl⟩, fun he => by cases he⟩
  else
    ⟨m,.deferred,CRTT.RecursiveTrace.preserves_refl S T m.frame.session,rfl,
      ⟨[],rfl⟩,fun he => by cases he⟩

theorem upgrade_funds {old : Continuation S T} (p : Provider S T old) (m : Machine S T old) (base : Nat)
    (make : (h : affordable S T m.frame base) → Unit → Proposal S T p m base h) :
    funds S T (upgrade S T p m base make).next.frame.session = funds S T m.frame.session :=
  (upgrade S T p m base make).conserved

theorem upgrade_preserves {old : Continuation S T} (p : Provider S T old) (m : Machine S T old) (base : Nat)
    (make : (h : affordable S T m.frame base) → Unit → Proposal S T p m base h) :
    Preserves S T m.frame.session (upgrade S T p m base make).next.frame.session := (upgrade S T p m base make).preserved

theorem upgrade_gain {old : Continuation S T} (p : Provider S T old) (m : Machine S T old) (base : Nat)
    (make : (h : affordable S T m.frame base) → Unit → Proposal S T p m base h)
    (h : (upgrade S T p m base make).status = .accepted) :
    policyBill S T p (upgrade S T p m base make).next.active (upgrade S T p m base make).next.frame < policyBill S T p m.active m.frame :=
  (upgrade S T p m base make).acceptedGain h

theorem upgrade_history {old : Continuation S T} (p : Provider S T old) (m : Machine S T old) (base : Nat)
    (make : (h : affordable S T m.frame base) → Unit → Proposal S T p m base h) :
    ∃ added, (upgrade S T p m base make).next.history = added ++ m.history :=
  (upgrade S T p m base make).historyKept

/-! A tiny, concrete T19/T27 policy synthesis. The two declared scenarios
are the root depth-obstruction continuation and its already exhausted
counterpart. The portfolio uses exact action bills from this finite fixture.
The solver optimizes observation cost + regret, NOT absolute worst bill. -/
namespace Witnesses
open CRTT.ControllerReplacement.Witnesses (src dst oldContinuation fundedLive offer)

-- A real runtime observation on the continuation, not a cost-table lookup.
def probePending (c : Continuation src dst) : Unit → Bool := fun _ => !c.frontier.jobs.isEmpty

def goodFrame : Frame src dst oldContinuation := ⟨CRTT.AdmissionAccounting.start src dst fundedLive,rfl⟩
def goodProvider : Provider src dst oldContinuation :=
  ⟨probePending oldContinuation, fun _ => CRTT.RelativeEvidence.fromAbsolute src dst oldContinuation offer,0,0,0⟩

def emptyLive := CRTT.ControllerReplacement.finish src dst fundedLive
def emptyOld := emptyLive.current

def emptyFrame : Frame src dst emptyOld := ⟨CRTT.AdmissionAccounting.start src dst emptyLive,rfl⟩

def emptyCandidate : CRTT.RelativeEvidence.Candidate src dst emptyOld where
  controller := emptyOld.controller
  sameFees := rfl
  reserve := emptyOld.reserve
  funded := by decide
  migration := 1

def emptyOffer : RelativeOffer src dst emptyOld where
  candidate := emptyCandidate
  rows := [(0,0)]
  actual := ⟨(0,0),List.Mem.head _,by decide,by decide⟩
  evidenceLabel := "exhausted frontier: no remaining gain"

def emptyProvider : Provider src dst emptyOld := ⟨probePending emptyOld,fun _ => emptyOffer,0,0,0⟩

-- Relative to already spent costs. The empty context has spent 7 previously.
def directBill (a h : Bool) : Nat := if h then (if a then 4 else 7) else (if a then 2 else 0)

def decisionModel : CRTT.DecisionEvidence.Model Bool Bool := CRTT.DecisionEvidence.catalogueModel false [true] directBill

def selected (_ : Unit) : Tree := CRTT.DecisionEvidence.acquisitionTree decisionModel
  (fun (_ : Unit) h => h) (fun _ => 1) 1 [false,true] [()]

theorem terminal_bills :
    policyBill src dst goodProvider (.act false) goodFrame = directBill false true ∧
    policyBill src dst goodProvider (.act true) goodFrame = directBill true true ∧
    policyBill src dst emptyProvider (.act false) emptyFrame = 7+directBill false false ∧
    policyBill src dst emptyProvider (.act true) emptyFrame = 7+directBill true false := by decide

theorem selected_legal : Legal (CRTT.DecisionEvidence.evidenceProblem decisionModel (fun (_ : Unit) h => h) (fun _ => 1)) 1 [()] (selected ()) :=
  CRTT.DecisionEvidence.acquisition_legal decisionModel (fun (_ : Unit) h => h) (fun _ => 1) 1 [false,true] [()]

theorem selected_regret : CRTT.DecisionEvidence.acquisitionValue decisionModel
    (fun (_ : Unit) h => h) (fun _ => 1) 1 [false,true] [()] = 1 := by decide

theorem selected_bills : policyBill src dst goodProvider (selected ()) goodFrame = 5 ∧
    policyBill src dst emptyProvider (selected ()) emptyFrame = 8 := by decide

def incumbent : Machine src dst oldContinuation := ⟨goodFrame,.act false,[]⟩

-- Exact closed bounds checked by Lean; no prospective run in the numeric gate.
-- The solver is invoked in the paid proposal thunk, not in its tariff.
def makeUpgrade (h : affordable src dst incumbent.frame 0) (_ : Unit) : Proposal src dst goodProvider incumbent 0 h where
  tree := selected ()
  oldLower := 7
  newUpper := 6
  oldSound := by decide
  newSound := by
    -- The affordability proof is an argument of `pay`, so it occurs inside the
    -- goal type. `decide` refuses a goal carrying it as a local hypothesis
    -- ("Expected type must not contain free variables"); `decide +revert`
    -- generalises it first, which is what this computation needs.
    decide +revert

def upgraded := upgrade src dst goodProvider incumbent 0 makeUpgrade

theorem changed_policy : upgraded.status = .accepted := by decide

theorem changed_bill : policyBill src dst goodProvider upgraded.next.active upgraded.next.frame = 6 := by decide

theorem actual_saving : policyBill src dst goodProvider upgraded.next.active upgraded.next.frame < policyBill src dst goodProvider incumbent.active incumbent.frame :=
  upgrade_gain src dst goodProvider incumbent 0 makeUpgrade changed_policy

-- Protected fallback: no acquisition/attempt is affordable at exact reserve.
def tightFrame : Frame src dst oldContinuation :=
  ⟨CRTT.AdmissionAccounting.start src dst CRTT.ControllerReplacement.Witnesses.tightLive,rfl⟩

theorem blocked_is_free : spent src dst (interpret src dst goodProvider (selected ()) tightFrame).final = 0 ∧
    (interpret src dst goodProvider (selected ()) tightFrame).status = .blocked := by decide

end Witnesses

#print axioms pay_funds
#print axioms pay_spent
#print axioms pay_preserves
#print axioms interpret_funds
#print axioms interpret_preserves
#print axioms interpret_complete
#print axioms policyBill_complete
#print axioms upgrade_funds
#print axioms upgrade_preserves
#print axioms upgrade_gain
#print axioms upgrade_history
#print axioms Witnesses.terminal_bills
#print axioms Witnesses.selected_legal
#print axioms Witnesses.selected_regret
#print axioms Witnesses.selected_bills
#print axioms Witnesses.changed_policy
#print axioms Witnesses.changed_bill
#print axioms Witnesses.actual_saving
#print axioms Witnesses.blocked_is_free
end CRTT.MetaPolicy
