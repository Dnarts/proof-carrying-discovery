import MetaClosure

/-! T32: release boundary, not another solver or policy. Inputs remain typed
at a fixed root and provider; a funded initial continuation is required.
No unrestricted input parser or autonomous scheduler is assumed. -/
namespace CRTT.Release
open CRTT.MorphismDiscovery
open CRTT.ControllerReplacement (Continuation)
open CRTT.AdmissionAccounting (Session spent funds)
open CRTT.MetaPolicy (Machine Provider Tree)
open CRTT.MetaClosure (Run Plan Closed)
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

variable {sw sp sa tw tp ta : Nat}
variable (S : IndexedTask sw sp sa) (T : IndexedTask tw tp ta)
variable {old : Continuation S T}

/-- The certified schedule can be produced by runPlans or by a connected
sequence of actual, state-specific, already certified upgrade operations.
Its length is explicit. No free search for a schedule is implicit here. -/
def run (p : Provider S T old) (m : Machine S T old) (n : Nat)
    (schedule : Unit → Run S T p m n) : Closed S T p m n :=
  CRTT.MetaClosure.closeRun S T p m n (schedule ())

def runList (p : Provider S T old) (m : Machine S T old) (plans : List (Plan S T p)) : Closed S T p m plans.length :=
  run S T p m plans.length (fun _ => CRTT.MetaClosure.runPlans S T p plans m)

theorem runList_eq_close (p : Provider S T old) (m : Machine S T old) (plans : List (Plan S T p)) :
    runList S T p m plans = CRTT.MetaClosure.close S T p plans m := rfl

theorem result_complete (p : Provider S T old) (m : Machine S T old) (n : Nat) (r : Closed S T p m n)
    (x : Morphism S T) : x ∈ r.final.live.current.frontier.certificates ↔ x ∈ discoverAll S T :=
  CRTT.MetaClosure.closed_complete S T p m n r x

theorem result_exhausted (p : Provider S T old) (m : Machine S T old) (n : Nat) (r : Closed S T p m n) :
    r.final.live.current.frontier.jobs = [] := by
  rw [r.finished]
  exact CRTT.ControllerReplacement.finish_exhausted S T r.episode.final.live

theorem result_empty_impossible (p : Provider S T old) (m : Machine S T old) (n : Nat) (r : Closed S T p m n)
    (h : r.final.live.current.frontier.certificates = []) : ¬ Nonempty (Morphism S T) := by
  intro hn
  obtain ⟨x⟩ := hn
  obtain ⟨y,hy,_,_⟩ := discover_complete S T x
  have hm := (result_complete S T p m n r y).mpr hy
  rw [h] at hm
  cases hm

theorem result_impossible_empty (p : Provider S T old) (m : Machine S T old) (n : Nat) (r : Closed S T p m n)
    (h : ¬ Nonempty (Morphism S T)) : r.final.live.current.frontier.certificates = [] := by
  cases he : r.final.live.current.frontier.certificates with
  | nil => rfl
  | cons x xs => exact False.elim (h ⟨x⟩)

theorem result_impossible_iff (p : Provider S T old) (m : Machine S T old) (n : Nat) (r : Closed S T p m n) :
    r.final.live.current.frontier.certificates = [] ↔ ¬ Nonempty (Morphism S T) :=
  ⟨result_empty_impossible S T p m n r,result_impossible_empty S T p m n r⟩

theorem result_funds (p : Provider S T old) (m : Machine S T old) (n : Nat) (r : Closed S T p m n) :
    funds S T r.final = funds S T m.frame.session := CRTT.MetaClosure.closed_funds S T p m n r

theorem result_history (p : Provider S T old) (m : Machine S T old) (n : Nat) (r : Closed S T p m n) :
    CRTT.RecursiveTrace.Preserves S T m.frame.session r.final := CRTT.MetaClosure.closed_preserves S T p m n r

theorem result_bill (p : Provider S T old) (m : Machine S T old) (n : Nat) (r : Closed S T p m n) :
    spent S T r.final = CRTT.MetaPolicy.policyBill S T p r.upgrades.final.active r.upgrades.final.frame :=
  CRTT.MetaClosure.closed_bill S T p m n r

theorem result_steps (p : Provider S T old) (m : Machine S T old) (n : Nat) (r : Closed S T p m n) :
    r.upgrades.trace.length = n := r.upgrades.lengthEq

/-! Readable projection. No policyBill, discoverAll, or prospective execution
is evaluated by these renderers. The proof-bearing Closed value is authoritative.
Strings are a diagnostic display, not a parser or substitute proof. -/
structure MapView where
  worlds : List Nat
  ports : List Nat
  actions : List Nat
  deriving Repr

def mapView (x : Morphism S T) : MapView :=
  ⟨(indices tw).map (fun w => (x.worldMap w).val),
   (indices sp).map (fun q => (x.portMap q).val),
   (indices (sa+1)).map (fun a => (x.actionMap a).val)⟩

structure TaskView where
  worlds : Nat
  ports : Nat
  actions : Nat
  depth : Nat
  readTable : List (List Bool)
  prices : List Nat
  losses : List (List Nat)
  deriving Repr

def taskView {w q a : Nat} (d : IndexedTask w q a) : TaskView :=
  ⟨w,q,a+1,d.depth,(indices q).map (fun i => (indices w).map (d.read i)),
   (indices q).map d.price,(indices (a+1)).map (fun i => (indices w).map (d.loss i))⟩

def offerView (c : Continuation S T) (o : CRTT.RelativeEvidence.RelativeOffer S T c) : String :=
  "label=" ++ reprStr o.evidenceLabel ++ ";rows=" ++ reprStr o.rows ++ ";migration=" ++ toString o.candidate.migration ++
  ";oldReserve=" ++ toString c.reserve ++ ";newReserve=" ++ toString o.candidate.reserve ++
  ";oldRuleCosts=" ++ reprStr (c.controller.rules.map (fun r => r.cost)) ++
  ";newRuleCosts=" ++ reprStr (o.candidate.controller.rules.map (fun r => r.cost))

def eventView : CRTT.MetaPolicy.Event S T → String
  | .observed b fee => "observed;answer=" ++ toString b ++ ";fee=" ++ toString fee
  | .prepared c o fee => "prepared;fee=" ++ toString fee ++ ";" ++ offerView S T c o
  | .attempted v => "attempted;verdict=" ++ reprStr v

def entryView : CRTT.AdmissionAccounting.Entry S T → String
  | .evidence label fee => "evidence;fee=" ++ toString fee ++ ";label=" ++ reprStr label
  | .attempt c o balance fee v => "attempt;balanceBefore=" ++ toString balance ++ ";checkFee=" ++ toString fee ++
      ";verdict=" ++ reprStr v ++ ";debit=" ++ toString (CRTT.ControllerReplacement.chargedFee fee o.candidate.migration v) ++ ";" ++ offerView S T c o

def upgradeView (e : CRTT.MetaPolicy.UpgradeEvent) : String :=
  "fee=" ++ toString e.fee ++ ";status=" ++ reprStr e.status ++ ";balanceBefore=" ++ toString e.balanceBefore ++
  ";oldLower=" ++ toString e.oldLower ++ ";newUpper=" ++ toString e.newUpper ++
  ";prior=" ++ reprStr e.prior ++ ";candidate=" ++ reprStr e.candidate

def oldReceiptView (e : CRTT.ControllerReplacement.AttemptReceipt S T) : String :=
  "status=" ++ reprStr e.status ++ ";debit=" ++ toString (CRTT.ControllerReplacement.attemptCharge S T e) ++
  ";balanceBefore=" ++ toString e.balanceBefore ++ ";checkFee=" ++ toString e.checkFee ++
  ";oldLower=" ++ toString e.proposal.oldLower ++ ";newUpper=" ++ toString e.proposal.newUpper ++
  ";label=" ++ reprStr e.proposal.evidenceLabel

/-- One compact, structured projection of the actual result. Existing receipts
are ordered within each ledger. No global chronology is invented for
historical T28 receipts that predate this release's episode. -/
structure Summary where
  source : TaskView
  target : TaskView
  terminal : String
  episodeStatus : String
  initialBalance : Nat
  initialSpent : Nat
  initialReserve : Nat
  balance : Nat
  spent : Nat
  funds : Nat
  remainingReserve : Nat
  remainingJobs : Nat
  finishBill : Nat
  upgradeCount : Nat
  paidUpgrades : Nat
  acceptedUpgrades : Nat
  initialCertificates : List MapView
  certificates : List MapView
  upgradeStatuses : List String
  upgradeHistory : List String
  episodeEvents : List String
  relativeJournal : List String
  oldHistory : List String
  searchReceipts : List CRTT.BudgetedPruning.Receipt
  initialPolicy : String
  installedPolicy : String
  baseSearchFees : List Nat
  providerFees : List Nat
  deriving Repr

def summarize (p : Provider S T old) (m : Machine S T old) (n : Nat) (r : Closed S T p m n) : Summary :=
  let i := m.frame.session
  let f := r.final
  let fees := i.live.current.controller.fees
  { source := taskView S
    target := taskView T
    terminal := if f.live.current.frontier.certificates.isEmpty then "impossible" else "complete"
    episodeStatus := reprStr r.episode.status
    initialBalance := i.live.balance
    initialSpent := spent S T i
    initialReserve := i.live.current.reserve
    balance := f.live.balance
    spent := spent S T f
    funds := funds S T f
    remainingReserve := f.live.current.reserve
    remainingJobs := f.live.current.frontier.jobs.length
    finishBill := spent S T f - spent S T r.episode.final
    upgradeCount := r.upgrades.trace.length
    paidUpgrades := CRTT.MetaClosure.paidCount S T r.upgrades.trace
    acceptedUpgrades := CRTT.MetaClosure.acceptedCount S T r.upgrades.trace
    initialCertificates := i.live.current.frontier.certificates.map (mapView S T)
    certificates := f.live.current.frontier.certificates.map (mapView S T)
    upgradeStatuses := r.upgrades.trace.map (fun x => reprStr x.result.status)
    upgradeHistory := r.upgrades.final.history.reverse.map upgradeView
    episodeEvents := r.episode.events.map (eventView S T)
    relativeJournal := f.journal.reverse.map (entryView S T)
    oldHistory := f.live.history.reverse.map (oldReceiptView S T)
    searchReceipts := f.live.current.frontier.receipts.reverse
    initialPolicy := reprStr m.active
    installedPolicy := reprStr r.upgrades.final.active
    baseSearchFees := [fees.split+1,fees.prepare+1,fees.action+1]
    providerFees := [p.queryBase+1,p.prepBase+1,p.checkBase+1] }

theorem summary_exhausted (p : Provider S T old) (m : Machine S T old) (n : Nat) (r : Closed S T p m n) :
    (summarize S T p m n r).remainingJobs = 0 := by
  change r.final.live.current.frontier.jobs.length = 0
  rw [result_exhausted S T p m n r] <;> rfl

theorem summary_bill (p : Provider S T old) (m : Machine S T old) (n : Nat) (r : Closed S T p m n) :
    (summarize S T p m n r).spent = CRTT.MetaPolicy.policyBill S T p r.upgrades.final.active r.upgrades.final.frame :=
  result_bill S T p m n r

theorem summary_conserved (p : Provider S T old) (m : Machine S T old) (n : Nat) (r : Closed S T p m n) :
    (summarize S T p m n r).balance + (summarize S T p m n r).spent =
      (summarize S T p m n r).initialBalance + (summarize S T p m n r).initialSpent :=
  result_funds S T p m n r

namespace Witnesses
open CRTT.ControllerReplacement.Witnesses (src dst oldContinuation)
open CRTT.MetaPolicy.Witnesses (goodProvider incumbent goodFrame tightFrame)
open CRTT.MetaClosure.Witnesses (firstRun secondRun redundant twoRun)

def baseline := runList src dst goodProvider incumbent []
def single := run src dst goodProvider incumbent 1 (fun _ => firstRun)
def mixed := run src dst goodProvider incumbent 2 (fun _ => secondRun)
def double := run src dst goodProvider redundant 2 (fun _ => twoRun)

def tight : Machine src dst oldContinuation := ⟨tightFrame,.observe () (.act false) (.act true),[]⟩
def fallback := runList src dst goodProvider tight
  [CRTT.MetaClosure.conservativeControl src dst goodProvider, CRTT.MetaClosure.conservativeControl src dst goodProvider]

def lowFrame : CRTT.MetaPolicy.Frame src dst oldContinuation :=
  ⟨CRTT.AdmissionAccounting.start src dst (CRTT.ControllerReplacement.openLive src dst oldContinuation 103 (by decide)),rfl⟩
def low : Machine src dst oldContinuation := ⟨lowFrame,.act true,[]⟩
def lowBaseline := runList src dst goodProvider low []
def lowRejected := runList src dst goodProvider low [CRTT.MetaClosure.conservativeControl src dst goodProvider]

-- A separate positive semantic fixture: same source/target task, no depth
-- obstruction. Completeness is still reference membership, not a count alone.
def positiveController : CRTT.ControllerReplacement.Controller src src := ⟨[],⟨0,0,0⟩⟩
def positiveOld : Continuation src src :=
  ⟨positiveController,CRTT.BudgetedPruning.initial src src [],CRTT.BudgetedPruning.initial_correct src src [],100,by decide⟩
def positiveCandidate : CRTT.RelativeEvidence.Candidate src src positiveOld where
  controller := positiveController
  sameFees := rfl
  reserve := 100
  funded := by decide
  migration := 0

def positiveOffer : CRTT.RelativeEvidence.RelativeOffer src src positiveOld where
  candidate := positiveCandidate
  rows := [(0,100)]
  actual := ⟨(0,100),List.Mem.head _,Nat.zero_le _,by decide⟩
  evidenceLabel := "non-improving identity fixture"

def positiveProvider : Provider src src positiveOld := ⟨fun _ => true,fun _ => positiveOffer,0,0,0⟩
def positiveFrame : CRTT.MetaPolicy.Frame src src positiveOld :=
  ⟨CRTT.AdmissionAccounting.start src src (CRTT.ControllerReplacement.openLive src src positiveOld 100 (by decide)),rfl⟩
def positiveMachine : Machine src src positiveOld := ⟨positiveFrame,.act false,[]⟩
def positive := runList src src positiveProvider positiveMachine []

-- Actual paid prefix with a nonempty previously emitted certificate list.
def partialLive := CRTT.ControllerReplacement.advance src src positiveFrame.session.live 5
def partialOld := partialLive.current
def partialFrame : CRTT.MetaPolicy.Frame src src partialOld :=
  ⟨CRTT.AdmissionAccounting.start src src partialLive,rfl⟩
def partialCandidate : CRTT.RelativeEvidence.Candidate src src partialOld where
  controller := partialOld.controller
  sameFees := rfl
  reserve := partialOld.reserve
  funded := by decide
  migration := 0
def partialOffer : CRTT.RelativeEvidence.RelativeOffer src src partialOld where
  candidate := partialCandidate
  rows := [(0,100)]
  actual := ⟨(0,100),List.Mem.head _,Nat.zero_le _,by decide⟩
  evidenceLabel := "partial predecessor fixture"
def partialProvider : Provider src src partialOld := ⟨fun _ => true,fun _ => partialOffer,0,0,0⟩
def partialMachine : Machine src src partialOld := ⟨partialFrame,.act false,[]⟩
def partialResult := runList src src partialProvider partialMachine []

theorem costs : spent src dst baseline.final = 7 ∧ spent src dst single.final = 6 ∧
    spent src dst mixed.final = 7 ∧ spent src dst double.final = 6 := by decide

theorem low_liquidity : spent src dst lowBaseline.final = 4 ∧ spent src dst lowRejected.final = 10 ∧
    lowRejected.episode.status = .attempted .rejectLiquidity := by decide

theorem fallback_control : spent src dst fallback.final = 7 ∧ fallback.episode.status = .blocked ∧
    CRTT.MetaClosure.paidCount src dst fallback.upgrades.trace = 0 ∧ fallback.upgrades.trace.length = 2 := by decide

theorem nonempty_result : positive.final.live.current.frontier.certificates.length = 2 := by decide

theorem predecessor_result : partialOld.frontier.certificates.length = 1 ∧
    partialResult.final.live.current.frontier.certificates.length = 2 ∧ spent src src partialResult.final = 11 := by decide

def reports : List (String × Summary) :=
  [("baseline",summarize src dst goodProvider incumbent 0 baseline),
   ("single",summarize src dst goodProvider incumbent 1 single),
   ("mixed",summarize src dst goodProvider incumbent 2 mixed),
   ("double",summarize src dst goodProvider redundant 2 double),
   ("fallback",summarize src dst goodProvider tight 2 fallback),
   ("liquidity-baseline",summarize src dst goodProvider low 0 lowBaseline),
   ("liquidity-rejected",summarize src dst goodProvider low 1 lowRejected),
   ("nonempty",summarize src src positiveProvider positiveMachine 0 positive),
   ("predecessor",summarize src src partialProvider partialMachine 0 partialResult)]
end Witnesses

#print axioms runList_eq_close
#print axioms result_complete
#print axioms result_exhausted
#print axioms result_empty_impossible
#print axioms result_impossible_empty
#print axioms result_impossible_iff
#print axioms result_funds
#print axioms result_history
#print axioms result_bill
#print axioms result_steps
#print axioms summary_exhausted
#print axioms summary_bill
#print axioms summary_conserved
#print axioms Witnesses.costs
#print axioms Witnesses.low_liquidity
#print axioms Witnesses.fallback_control
#print axioms Witnesses.nonempty_result
#print axioms Witnesses.predecessor_result
end CRTT.Release
