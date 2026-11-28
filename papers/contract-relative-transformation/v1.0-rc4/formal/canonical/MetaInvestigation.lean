import LearningDiscovery

/-! T25: a finite, explicitly priced portfolio of complete research plans.
Rule schemas are instantiated at arbitrary indexed task pairs. A plan may
perform a bounded endogenous-learning prefix, then complete the SAME frontier
with the certified T23 runner. No termination theorem for unlimited learning
is assumed. A funded fallback is required separately from the realized bill.
The meta solver consumes a supplied cost table, not the actual hidden world.
This is a finite decision problem, not arbitrary recursive self-modification. -/
namespace CRTT.MetaInvestigation
open CRTT.MorphismDiscovery CRTT.AdaptiveObservation CRTT.BudgetedDiscovery
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

/-- Portable syntax; each constructor denotes a universally certified family.
The charge is an abstract tariff, not a measured bound on machine time. -/
inductive RuleSchema where
  | read (cost : Nat)
  | price (cost : Nat)
  | injective (cost : Nat)
  | depth (cost : Nat)
  deriving Repr, DecidableEq

variable {sw sp sa tw tp ta : Nat}
variable (S : IndexedTask sw sp sa) (T : IndexedTask tw tp ta)

def instantiate : RuleSchema → CRTT.CertifiedPruning.CertifiedRule S T
  | .read c => CRTT.CertifiedPruning.readCompatRule S T c
  | .price c => CRTT.CertifiedPruning.priceRule S T c
  | .injective c => CRTT.CertifiedPruning.injectiveRule S T c
  | .depth c => CRTT.CertifiedPruning.depthRule S T c

theorem schema_sound (r : RuleSchema) (m : Morphism S T)
    (rho : CRTT.CertifiedPruning.PartialAssign sp tp)
    (h : CRTT.CertifiedPruning.Extends S T m rho) :
    (instantiate S T r).keep rho = true :=
  (instantiate S T r).sound m rho h

structure Plan where
  rules : List RuleSchema
  learningBudget : Nat
  reserve : Nat
  setupFee : Nat
  deriving Repr

def staticPlan (rules : List RuleSchema) (reserve setupFee : Nat) : Plan :=
  ⟨rules, 0, reserve, setupFee⟩

def policy (p : Plan) : CRTT.CertifiedPruning.RuleLibrary S T :=
  p.rules.map (instantiate S T)

/-- Execute only the paid prefix; the learning allowance does not affect the
underlying quote. Zero allowance disables learning, including lookup. -/
def learningRun (fees : CRTT.LearningDiscovery.Fees) (p : Plan) :
    Account (CRTT.LearningDiscovery.State S T) :=
  execute (CRTT.LearningDiscovery.quote S T (policy S T p) fees)
    ⟨CRTT.LearningDiscovery.initial S T (policy S T p), p.learningBudget, 0⟩

/-- Handoff: retain emitted certificates and all unfinished jobs. Do not restart
or reconstruct the proof-only reference list. A pending learning event is not
an answer obligation. The unspent prefix balance is retained. -/
def finishInput (fees : CRTT.LearningDiscovery.Fees) (p : Plan) :
    Account (CRTT.BudgetedPruning.Frontier S T) :=
  let u := learningRun S T fees p
  ⟨u.state.frontier, u.remaining + p.reserve, u.spent⟩

/-- External funding proof. Neither the solver nor the runner calls `potential`
to obtain the reserve. Producing this proof/bound is not a free operation. -/
def Funded (fees : CRTT.LearningDiscovery.Fees) (p : Plan) : Prop :=
  CRTT.BudgetedPruning.potential S T (policy S T p) fees.base
    (finishInput S T fees p).state ≤ (finishInput S T fees p).remaining

/-- Return the learning-prefix account as evidence as well as the completed
frontier. The static fallback stops learning, but does not destroy the raw
obstructions, extracted cores, pending event, or trace of the prefix. -/
def runPlan (fees : CRTT.LearningDiscovery.Fees) (p : Plan) :
    Account (CRTT.LearningDiscovery.State S T) ×
      Account (CRTT.BudgetedPruning.Frontier S T) :=
  let u := learningRun S T fees p
  (u, execute (CRTT.BudgetedPruning.quote S T (policy S T p) fees.base)
    ⟨u.state.frontier, u.remaining + p.reserve, u.spent⟩)

/-- Semantic/cost projection of the complete evidence-bearing execution. -/
def perform (fees : CRTT.LearningDiscovery.Fees) (p : Plan) :
    Account (CRTT.BudgetedPruning.Frontier S T) :=
  (runPlan S T fees p).2

theorem runPlan_prefix (fees : CRTT.LearningDiscovery.Fees) (p : Plan) :
    (runPlan S T fees p).1 = learningRun S T fees p := rfl

/-- The optional learning prefix never changes reference coverage. -/
theorem finishInput_correct (fees : CRTT.LearningDiscovery.Fees) (p : Plan) :
    CRTT.BudgetedPruning.Correct S T (finishInput S T fees p).state := by
  change CRTT.BudgetedPruning.Correct S T (learningRun S T fees p).state.frontier
  exact CRTT.LearningDiscovery.execute_correct S T (policy S T p) fees
    ⟨CRTT.LearningDiscovery.initial S T (policy S T p), p.learningBudget, 0⟩
    (CRTT.BudgetedPruning.initial_correct S T (policy S T p))

/-- A learning step can drop work, but cannot add frontier liability beyond
what the same static policy would already require. -/
def frontierPotential (fees : CRTT.LearningDiscovery.Fees) (p : Plan)
    (f : CRTT.BudgetedPruning.Frontier S T) : Nat :=
  CRTT.BudgetedPruning.potential S T (policy S T p) fees.base f

theorem drop_potential_le (fees : CRTT.LearningDiscovery.Fees) (p : Plan)
    (f : CRTT.BudgetedPruning.Frontier S T) (j : CRTT.BudgetedPruning.Job S T)
    (rest : List (CRTT.BudgetedPruning.Job S T)) (hj : f.jobs = j :: rest) :
    frontierPotential S T fees p {f with jobs := rest} ≤ frontierPotential S T fees p f := by
  change CRTT.BudgetedPruning.jobsBudget S T (policy S T p) fees.base rest ≤
    CRTT.BudgetedPruning.jobsBudget S T (policy S T p) fees.base f.jobs
  rw [hj]
  change CRTT.BudgetedPruning.jobsBudget S T (policy S T p) fees.base rest ≤
    CRTT.BudgetedPruning.jobBudget S T (policy S T p) fees.base j +
      CRTT.BudgetedPruning.jobsBudget S T (policy S T p) fees.base rest
  omega

theorem base_potential_le (fees : CRTT.LearningDiscovery.Fees) (p : Plan)
    (s : CRTT.LearningDiscovery.State S T) (j : CRTT.BudgetedPruning.Job S T)
    (rest : List (CRTT.BudgetedPruning.Job S T)) (hj : s.frontier.jobs = j :: rest) :
    frontierPotential S T fees p
      (CRTT.LearningDiscovery.baseStep S T (policy S T p) fees s j rest).frontier ≤
      frontierPotential S T fees p s.frontier := by
  let q : QuotedStep (CRTT.BudgetedPruning.Frontier S T) :=
    ⟨(CRTT.BudgetedPruning.bill S T fees.base j).fee,
      CRTT.BudgetedPruning.bill_positive S T fees.base j,
      fun _ => CRTT.BudgetedPruning.advance S T (policy S T p) fees.base s.frontier j rest⟩
  have hq : CRTT.BudgetedPruning.quote S T (policy S T p) fees.base s.frontier = some q := by
    unfold CRTT.BudgetedPruning.quote
    rw [hj]
  have h := CRTT.BudgetedPruning.quote_potential S T (policy S T p) fees.base s.frontier q hq
  change frontierPotential S T fees p
    (CRTT.LearningDiscovery.baseStep S T (policy S T p) fees s j rest).frontier + q.fee ≤
      frontierPotential S T fees p s.frontier at h
  omega

theorem learning_quote_potential (fees : CRTT.LearningDiscovery.Fees) (p : Plan)
    (s : CRTT.LearningDiscovery.State S T) (q : QuotedStep (CRTT.LearningDiscovery.State S T))
    (hq : CRTT.LearningDiscovery.quote S T (policy S T p) fees s = some q) :
    frontierPotential S T fees p (q.next ()).frontier ≤ frontierPotential S T fees p s.frontier := by
  cases hp : s.pending with
  | some raw =>
    simp [CRTT.LearningDiscovery.quote, hp] at hq
    rw [← hq]
    exact Nat.le_refl _
  | none =>
    cases hj : s.frontier.jobs with
    | nil => simp [CRTT.LearningDiscovery.quote, hp, hj] at hq
    | cons j rest =>
      cases j with
      | actions pm acts =>
        simp [CRTT.LearningDiscovery.quote, hp, hj] at hq
        rw [← hq]
        exact base_potential_le S T fees p s (.actions pm acts) rest hj
      | ports qs rho rs =>
        cases rs with
        | cons r rs =>
          simp [CRTT.LearningDiscovery.quote, hp, hj] at hq
          rw [← hq]
          exact base_potential_le S T fees p s (.ports qs rho (r :: rs)) rest hj
        | nil =>
          cases hr : s.stage with
          | lookup =>
            simp [CRTT.LearningDiscovery.quote, hp, hj, hr] at hq
            rw [← hq]
            change frontierPotential S T fees p
              (CRTT.LearningDiscovery.lookupStep S T s rho rest).frontier ≤ _
            cases hk : first (fun k : CRTT.ImpasseCompilation.ObstructionCore S T =>
                CRTT.ImpasseCompilation.containsCore k.constraints rho) s.library with
            | none => simp [CRTT.LearningDiscovery.lookupStep, hk]
            | some k =>
              simpa [CRTT.LearningDiscovery.lookupStep, hk] using
                drop_potential_le S T fees p s.frontier (.ports qs rho []) rest hj
          | probe =>
            simp [CRTT.LearningDiscovery.quote, hp, hj, hr] at hq
            rw [← hq]
            change frontierPotential S T fees p
              (CRTT.LearningDiscovery.probeStep S T s rho rest).frontier ≤ _
            cases hk : CRTT.LearningDiscovery.findCore S T rho with
            | none => simp [CRTT.LearningDiscovery.probeStep, hk]
            | some k =>
              simpa [CRTT.LearningDiscovery.probeStep, hk] using
                drop_potential_le S T fees p s.frontier (.ports qs rho []) rest hj
          | advance =>
            simp [CRTT.LearningDiscovery.quote, hp, hj, hr] at hq
            rw [← hq]
            exact base_potential_le S T fees p s (.ports qs rho []) rest hj

theorem learning_potential_bound (fees : CRTT.LearningDiscovery.Fees) (p : Plan) :
    frontierPotential S T fees p (learningRun S T fees p).state.frontier ≤
      frontierPotential S T fees p (CRTT.BudgetedPruning.initial S T (policy S T p)) := by
  let cap := frontierPotential S T fees p (CRTT.BudgetedPruning.initial S T (policy S T p))
  let P : CRTT.LearningDiscovery.State S T → Prop :=
    fun u => frontierPotential S T fees p u.frontier ≤ cap
  have hc : ∀ u q, P u → CRTT.LearningDiscovery.quote S T (policy S T p) fees u = some q → P (q.next ()) := by
    intro u q hu hq
    exact Nat.le_trans (learning_quote_potential S T fees p u q hq) hu
  exact invariant (CRTT.LearningDiscovery.quote S T (policy S T p) fees) P hc
    p.learningBudget ⟨CRTT.LearningDiscovery.initial S T (policy S T p), p.learningBudget, 0⟩
    (Nat.le_refl _)

/-- An initial static reserve suffices for the fallback, regardless of how
much of the learning allowance is spent or which obligations are removed. -/
theorem funded_of_initial (fees : CRTT.LearningDiscovery.Fees) (p : Plan)
    (hb : frontierPotential S T fees p (CRTT.BudgetedPruning.initial S T (policy S T p)) ≤ p.reserve) :
    Funded S T fees p := by
  have h := learning_potential_bound S T fees p
  change frontierPotential S T fees p (learningRun S T fees p).state.frontier ≤
    (learningRun S T fees p).remaining + p.reserve
  omega

theorem perform_exhausted (fees : CRTT.LearningDiscovery.Fees) (p : Plan)
    (h : Funded S T fees p) : (perform S T fees p).state.jobs = [] :=
  CRTT.BudgetedPruning.execute_funded_exhausts S T (policy S T p) fees.base
    (finishInput S T fees p) h

theorem perform_complete (fees : CRTT.LearningDiscovery.Fees) (p : Plan)
    (h : Funded S T fees p) (N : Morphism S T) :
    N ∈ (perform S T fees p).state.certificates ↔ N ∈ discoverAll S T :=
  CRTT.BudgetedPruning.execute_full S T (policy S T p) fees.base
    (finishInput S T fees p) (finishInput_correct S T fees p) h N

theorem perform_static (fees : CRTT.LearningDiscovery.Fees)
    (rs : List RuleSchema) (reserve setup : Nat) :
    perform S T fees (staticPlan rs reserve setup) =
      execute (CRTT.BudgetedPruning.quote S T
        (policy S T (staticPlan rs reserve setup)) fees.base)
        ⟨CRTT.BudgetedPruning.initial S T (policy S T (staticPlan rs reserve setup)), reserve, 0⟩ := by
  change execute (CRTT.BudgetedPruning.quote S T
    (policy S T (staticPlan rs reserve setup)) fees.base)
    ⟨CRTT.BudgetedPruning.initial S T (policy S T (staticPlan rs reserve setup)),
      0 + reserve, 0⟩ = _
  rw [Nat.zero_add]

theorem learning_accounting (fees : CRTT.LearningDiscovery.Fees) (p : Plan) :
    (learningRun S T fees p).remaining + (learningRun S T fees p).spent = p.learningBudget := by
  have h := accounting (CRTT.LearningDiscovery.quote S T (policy S T p) fees)
    p.learningBudget (⟨CRTT.LearningDiscovery.initial S T (policy S T p),
      p.learningBudget, 0⟩ : Account (CRTT.LearningDiscovery.State S T))
  change (learningRun S T fees p).remaining + (learningRun S T fees p).spent = p.learningBudget + 0 at h
  exact h

theorem perform_accounting (fees : CRTT.LearningDiscovery.Fees) (p : Plan) :
    (perform S T fees p).remaining + (perform S T fees p).spent =
      p.learningBudget + p.reserve := by
  have h := accounting (CRTT.BudgetedPruning.quote S T (policy S T p) fees.base)
    (finishInput S T fees p).remaining (finishInput S T fees p)
  change (perform S T fees p).remaining + (perform S T fees p).spent =
    ((learningRun S T fees p).remaining + p.reserve) + (learningRun S T fees p).spent at h
  have hl := learning_accounting S T fees p
  omega

/-- The learning trace already includes the base transitions of its prefix.
Subtract their receipts (via this additive identity) when combining phases;
never count those fees twice. -/
theorem perform_trace (fees : CRTT.LearningDiscovery.Fees) (p : Plan) :
    (perform S T fees p).spent + CRTT.BudgetedPruning.receiptCost
      (learningRun S T fees p).state.frontier.receipts =
    CRTT.LearningDiscovery.feeSum (learningRun S T fees p).state.feesPaid +
      CRTT.BudgetedPruning.receiptCost (perform S T fees p).state.receipts := by
  have hp := CRTT.LearningDiscovery.execute_trace S T (policy S T p) fees
    (⟨CRTT.LearningDiscovery.initial S T (policy S T p), p.learningBudget, 0⟩ :
      Account (CRTT.LearningDiscovery.State S T))
  change (learningRun S T fees p).spent + 0 =
    0 + CRTT.LearningDiscovery.feeSum (learningRun S T fees p).state.feesPaid at hp
  rw [Nat.add_zero, Nat.zero_add] at hp
  have hf := CRTT.BudgetedPruning.execute_trace S T (policy S T p) fees.base
    (finishInput S T fees p)
  change (perform S T fees p).spent + CRTT.BudgetedPruning.receiptCost
      (learningRun S T fees p).state.frontier.receipts =
    (learningRun S T fees p).spent +
      CRTT.BudgetedPruning.receiptCost (perform S T fees p).state.receipts at hf
  rw [hp] at hf
  exact hf

/-- Setup/handoff/disposal charges are supplied explicitly. Unspent money is
not a cost. The reserved budget is distinct from the realized charge. -/
def actualBill (fees : CRTT.LearningDiscovery.Fees) (p : Plan) : Nat :=
  p.setupFee + (perform S T fees p).spent

theorem actualBill_le_reservation (fees : CRTT.LearningDiscovery.Fees) (p : Plan) :
    actualBill S T fees p ≤ p.setupFee + p.learningBudget + p.reserve := by
  have h := perform_accounting S T fees p
  unfold actualBill
  omega

/-- A meta world is a possible pair of tasks, not the world of an individual
T19 observation problem. This first implementation fixes carrier sizes across
meta worlds. -/
structure TaskPair (sw sp sa tw tp ta : Nat) where
  source : IndexedTask sw sp sa
  target : IndexedTask tw tp ta

/-- `costTable` is a supplied table/upper-bound function, with a proof relating
it to completed runs. A bound is NOT an exact realized cost. Constructing,
certifying, loading and optimizing the table must be priced externally;
controllerFee is the declared aggregate charge in this abstract model. -/
structure MetaTask (W Q A : Type) (sw sp sa tw tp ta : Nat) where
  pair : W → TaskPair sw sp sa tw tp ta
  worlds : List W
  ports : List Q
  defaultAction : A
  otherActions : List A
  observe : Q → W → Bool
  price : Q → Nat
  fees : CRTT.LearningDiscovery.Fees
  plan : A → Plan
  funded : ∀ a w, Funded (pair w).source (pair w).target fees (plan a)
  costTable : A → W → Nat
  tableBound : ∀ a w, actualBill (pair w).source (pair w).target fees (plan a) ≤ costTable a w
  controllerFee : Nat

variable {W Q A : Type}
variable (M : MetaTask W Q A sw sp sa tw tp ta)

def ExactTable : Prop :=
  ∀ a w, M.costTable a w = actualBill (M.pair w).source (M.pair w).target M.fees (M.plan a)

def problem : Problem W Q A where
  defaultAction := M.defaultAction
  otherActions := M.otherActions
  read := M.observe
  price := M.price
  loss := M.costTable

/-- The controller's runtime interface needs only paid sensor answers, not
access to the loss table of the hidden world. The tree is synthesized earlier. -/
structure Decision (A : Type) where
  action : A
  paid : Nat

def walk (sense : Q → Bool) (price : Q → Nat) : Investigation Q A → Decision A
  | .act a => ⟨a, 0⟩
  | .observe q l r =>
    let d := if sense q then walk sense price r else walk sense price l
    ⟨d.action, price q + d.paid⟩

theorem walk_cost (P : Problem W Q A) (w : W) (t : Investigation Q A) :
    (walk (fun q => P.read q w) P.price t).paid +
      P.loss (walk (fun q => P.read q w) P.price t).action w = runCost P w t := by
  induction t with
  | act a => simp [walk, runCost]
  | observe q l r ihl ihr =>
    cases h : P.read q w with
    | false =>
      simpa [walk, runCost, h, Nat.add_assoc] using congrArg (fun k => P.price q + k) ihl
    | true =>
      simpa [walk, runCost, h, Nat.add_assoc] using congrArg (fun k => P.price q + k) ihr

def decision (w : W) (t : Investigation Q A) : Decision A :=
  walk (fun q => M.observe q w) M.price t

def executionCost (w : W) (t : Investigation Q A) : Nat :=
  let d := decision M w t
  d.paid + actualBill (M.pair w).source (M.pair w).target M.fees (M.plan d.action)

theorem executionCost_le (w : W) (t : Investigation Q A) :
    executionCost M w t ≤ runCost (problem M) w t := by
  let d := decision M w t
  have hw := walk_cost (problem M) w t
  change d.paid + M.costTable d.action w = runCost (problem M) w t at hw
  change d.paid + actualBill (M.pair w).source (M.pair w).target M.fees (M.plan d.action) ≤ _
  rw [← hw]
  exact Nat.add_le_add_left (M.tableBound d.action w) d.paid

theorem executionCost_eq (h : ExactTable M) (w : W) (t : Investigation Q A) :
    executionCost M w t = runCost (problem M) w t := by
  let d := decision M w t
  have hw := walk_cost (problem M) w t
  change d.paid + M.costTable d.action w = runCost (problem M) w t at hw
  change d.paid + actualBill (M.pair w).source (M.pair w).target M.fees (M.plan d.action) = _
  rw [← hw, h d.action w]

/-- Only the selected plan is performed. The proof establishes the hard semantic
contract even if an arbitrary tree is supplied: all plan labels are funded. -/
def selectedRun (w : W) (t : Investigation Q A) :
    Account (CRTT.BudgetedPruning.Frontier (M.pair w).source (M.pair w).target) :=
  perform (M.pair w).source (M.pair w).target M.fees (M.plan (decision M w t).action)

theorem selectedRun_complete (w : W) (t : Investigation Q A)
    (N : Morphism (M.pair w).source (M.pair w).target) :
    N ∈ (selectedRun M w t).state.certificates ↔
      N ∈ discoverAll (M.pair w).source (M.pair w).target :=
  perform_complete (M.pair w).source (M.pair w).target M.fees
    (M.plan (decision M w t).action) (M.funded (decision M w t).action w) N

/-- A single execution returns the selected decision, completed frontier and
its total modeled charge. The specification `executionCost` is not a second
runtime pass. -/
def runMeta (w : W) (t : Investigation Q A) :
    Decision A × (Account (CRTT.LearningDiscovery.State
      (M.pair w).source (M.pair w).target) ×
      Account (CRTT.BudgetedPruning.Frontier
        (M.pair w).source (M.pair w).target)) × Nat :=
  let d := decision M w t
  let done := runPlan (M.pair w).source (M.pair w).target M.fees (M.plan d.action)
  (d, done, M.controllerFee + (d.paid + ((M.plan d.action).setupFee + done.2.spent)))

theorem runMeta_bill (w : W) (t : Investigation Q A) :
    (runMeta M w t).2.2 = M.controllerFee + executionCost M w t := rfl

theorem runMeta_complete (w : W) (t : Investigation Q A)
    (N : Morphism (M.pair w).source (M.pair w).target) :
    N ∈ (runMeta M w t).2.1.2.state.certificates ↔
      N ∈ discoverAll (M.pair w).source (M.pair w).target :=
  selectedRun_complete M w t N

theorem runMeta_history (w : W) (t : Investigation Q A) :
    (runMeta M w t).2.1.1 = learningRun (M.pair w).source (M.pair w).target
      M.fees (M.plan (decision M w t).action) := rfl

/-- The supplied controller fee is charged once, even in the empty-world
specification case. It is not silently treated as a free synthesis oracle. -/
def predictedWorst (t : Investigation Q A) : Nat :=
  M.controllerFee + worst (problem M) M.worlds t

def actualWorst (t : Investigation Q A) : Nat :=
  M.controllerFee + worstList (fun w => executionCost M w t) M.worlds

theorem actualWorst_le (t : Investigation Q A) :
    actualWorst M t ≤ predictedWorst M t := by
  unfold actualWorst predictedWorst
  apply Nat.add_le_add_left
  apply worstList_le
  intro w hw
  exact Nat.le_trans (executionCost_le M w t) (runCost_le_worst (problem M) M.worlds t w hw)

theorem actualWorst_eq (h : ExactTable M) (t : Investigation Q A) :
    actualWorst M t = predictedWorst M t := by
  have he : (fun w => executionCost M w t) = (fun w => runCost (problem M) w t) := by
    funext w
    exact executionCost_eq M h w t
  unfold actualWorst predictedWorst worst
  rw [he]

def optimizer [DecidableEq Q] (depth : Nat) : Investigation Q A :=
  solve (problem M) depth M.worlds M.ports

theorem optimizer_legal [DecidableEq Q] (depth : Nat) :
    Legal (problem M) depth M.ports (optimizer M depth) :=
  solve_legal (problem M) depth M.worlds M.ports

/-- Exact minimization of the DECLARED upper-bound objective, not necessarily
of realized expenses. The controller overhead is fixed across legal trees. -/
theorem optimizer_bound_optimal [DecidableEq Q] (depth : Nat) (t : Investigation Q A)
    (ht : Legal (problem M) depth M.ports t) :
    predictedWorst M (optimizer M depth) ≤ predictedWorst M t :=
  Nat.add_le_add_left (solve_optimal (problem M) depth M.worlds M.ports t ht) _

theorem optimizer_actual_optimal [DecidableEq Q] (h : ExactTable M) (depth : Nat)
    (t : Investigation Q A) (ht : Legal (problem M) depth M.ports t) :
    actualWorst M (optimizer M depth) ≤ actualWorst M t := by
  rw [actualWorst_eq M h (optimizer M depth), actualWorst_eq M h t]
  exact optimizer_bound_optimal M depth t ht

/-- Exact feasibility for the modeled guaranteed expenditure (with exact table,
also the actual worst bill). It is not a liquidity/reservation theorem. -/
theorem meta_budget_iff [DecidableEq Q] (depth budget : Nat) :
    predictedWorst M (optimizer M depth) ≤ budget ↔
      ∃ t, Legal (problem M) depth M.ports t ∧ predictedWorst M t ≤ budget := by
  constructor
  · intro h
    exact ⟨optimizer M depth, optimizer_legal M depth, h⟩
  · rintro ⟨t, ht, hb⟩
    exact Nat.le_trans (optimizer_bound_optimal M depth t ht) hb

/-- Guard against a free-oracle argument: adding a meta controller need not
improve over the direct default plan which does not pay that controller fee. -/
theorem default_upper [DecidableEq Q] (depth : Nat) :
    predictedWorst M (optimizer M depth) ≤
      M.controllerFee + worst (problem M) M.worlds (.act M.defaultAction) := by
  have hleg : Legal (problem M) depth M.ports (.act M.defaultAction) := by
    cases depth <;> exact List.Mem.head _
  exact optimizer_bound_optimal M depth (.act M.defaultAction) hleg

/-- Offline acquisition/verification is a one-time cost, not free information.
For a fixed stream of n uses at stated constant charges, this is the exact
strict amortization criterion. No unknown-future oracle is asserted. -/
theorem acquisition_gain_iff (setup n direct mediated : Nat) (h : mediated ≤ direct) :
    setup + n * mediated < n * direct ↔ setup < n * (direct - mediated) := by
  have he : n * (direct - mediated) + n * mediated = n * direct := by
    calc
      _ = n * ((direct - mediated) + mediated) := (Nat.mul_add _ _ _).symm
      _ = n * direct := congrArg (fun k : Nat => n * k) (Nat.sub_add_cancel h)
  -- A bare `omega` on a `↔` over truncated `Nat` multiplication falls back on a
  -- classical decision; splitting the directions keeps the proof constructive.
  constructor
  · intro hh; omega
  · intro hh; omega

#print axioms schema_sound
#print axioms runPlan_prefix
#print axioms finishInput_correct
#print axioms drop_potential_le
#print axioms base_potential_le
#print axioms learning_quote_potential
#print axioms learning_potential_bound
#print axioms funded_of_initial
#print axioms perform_exhausted
#print axioms perform_complete
#print axioms perform_static
#print axioms learning_accounting
#print axioms perform_accounting
#print axioms perform_trace
#print axioms actualBill_le_reservation
#print axioms walk_cost
#print axioms executionCost_le
#print axioms executionCost_eq
#print axioms selectedRun_complete
#print axioms runMeta_bill
#print axioms runMeta_complete
#print axioms runMeta_history
#print axioms actualWorst_le
#print axioms actualWorst_eq
#print axioms optimizer_legal
#print axioms optimizer_bound_optimal
#print axioms optimizer_actual_optimal
#print axioms meta_budget_iff
#print axioms default_upper
#print axioms acquisition_gain_iff
end CRTT.MetaInvestigation
