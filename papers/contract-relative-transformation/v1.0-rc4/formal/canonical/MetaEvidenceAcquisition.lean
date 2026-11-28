import MetaInvestigation

/-! T25.8--12: partial cost knowledge and paid acquisition.
All bounds are indexed by the actual cost FUNCTION, not by a predicted value.
A finite minimax gap concerns the worst bill of a legal tree, not its
pointwise regret against a world-aware oracle. Assessment is a paid step.
The catalogue and schedule are supplied, not synthesized by this module. -/
namespace CRTT.MetaEvidenceAcquisition
open CRTT.AdaptiveObservation CRTT.BudgetedDiscovery
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
-- The `DecidableEq` section variables below are needed by most declarations in
-- this module but not by the five theorems that only unfold definitions. Lean
-- 4.36 rejects a local `omit ... in` before a `theorem` inside this namespace, so
-- the unused-section-variable linter is disabled for the file instead.
set_option linter.unusedSectionVars false

structure Bounds (actual : Nat) where
  lower : Nat
  upper : Nat
  lower_ok : lower ≤ actual
  upper_ok : actual ≤ upper

def exactBounds (n : Nat) : Bounds n := ⟨n, n, Nat.le_refl _, Nat.le_refl _⟩

def meet (b e : Bounds n) : Bounds n :=
  ⟨max b.lower e.lower, min b.upper e.upper,
    Nat.max_le.mpr ⟨b.lower_ok, e.lower_ok⟩,
    by
      by_cases h : b.upper ≤ e.upper
      · rw [Nat.min_eq_left h]
        exact b.upper_ok
      · have he : e.upper ≤ b.upper := Nat.le_of_lt (Nat.lt_of_not_ge h)
        rw [Nat.min_eq_right he]
        exact e.upper_ok⟩

abbrev Table {K : Type} (C : K → Nat) := (k : K) → Bounds (C k)

variable {K : Type} {C : K → Nat}

def MoreInfo (old new : Table C) : Prop :=
  ∀ k, (old k).lower ≤ (new k).lower ∧ (new k).upper ≤ (old k).upper

theorem info_refl (t : Table C) : MoreInfo t t :=
  fun _ => ⟨Nat.le_refl _, Nat.le_refl _⟩

theorem info_trans (a b c : Table C) (hab : MoreInfo a b) (hbc : MoreInfo b c) :
    MoreInfo a c :=
  fun k => ⟨Nat.le_trans (hab k).1 (hbc k).1, Nat.le_trans (hbc k).2 (hab k).2⟩

def replaceCell [DecidableEq K] (t : Table C) (k : K) (v : Bounds (C k)) : Table C :=
  fun j => if h : j = k then cast (congrArg (fun x => Bounds (C x)) h.symm) v else t j

def refineCell [DecidableEq K] (t : Table C) (k : K) (v : Bounds (C k)) : Table C :=
  replaceCell t k (meet (t k) v)

theorem refine_at [DecidableEq K] (t : Table C) (k : K) (v : Bounds (C k)) :
    refineCell t k v k = meet (t k) v := by
  simp [refineCell, replaceCell]

theorem refine_elsewhere [DecidableEq K] (t : Table C) (k j : K) (v : Bounds (C k))
    (h : j ≠ k) : refineCell t k v j = t j := by
  simp [refineCell, replaceCell, h]

theorem refine_info [DecidableEq K] (t : Table C) (k : K) (v : Bounds (C k)) :
    MoreInfo t (refineCell t k v) := by
  intro j
  by_cases h : j = k
  · subst j
    rw [refine_at]
    exact ⟨Nat.le_max_left _ _, Nat.min_le_left _ _⟩
  · rw [refine_elsewhere t k j v h]
    exact ⟨Nat.le_refl _, Nat.le_refl _⟩

/-! Lift cell bounds to every legal adaptive investigation tree. -/
variable {W Q A : Type}

def withLoss (P : Problem W Q A) (loss : A → W → Nat) : Problem W Q A :=
  { P with loss := loss }

theorem legal_withLoss [DecidableEq Q] (P : Problem W Q A) (loss : A → W → Nat)
    (n : Nat) (ports : List Q) (t : Investigation Q A) :
    Legal (withLoss P loss) n ports t ↔ Legal P n ports t := by
  induction t generalizing n ports with
  | act a => cases n <;> rfl
  | observe q l r ihl ihr =>
    cases n with
    | zero => rfl
    | succ n =>
      change (q ∈ ports ∧ Legal (withLoss P loss) n (without ports q) l ∧
        Legal (withLoss P loss) n (without ports q) r) ↔
        (q ∈ ports ∧ Legal P n (without ports q) l ∧ Legal P n (without ports q) r)
      rw [ihl n (without ports q), ihr n (without ports q)]

theorem runCost_loss_le (P : Problem W Q A) (lo hi : A → W → Nat)
    (h : ∀ a w, lo a w ≤ hi a w) (w : W) (t : Investigation Q A) :
    runCost (withLoss P lo) w t ≤ runCost (withLoss P hi) w t := by
  induction t with
  | act a => exact h a w
  | observe q l r ihl ihr =>
    cases he : P.read q w with
    | false =>
      simpa [runCost, withLoss, he] using Nat.add_le_add_left ihl (P.price q)
    | true =>
      simpa [runCost, withLoss, he] using Nat.add_le_add_left ihr (P.price q)

theorem worst_loss_le (P : Problem W Q A) (lo hi : A → W → Nat)
    (h : ∀ a w, lo a w ≤ hi a w) (B : List W) (t : Investigation Q A) :
    worst (withLoss P lo) B t ≤ worst (withLoss P hi) B t := by
  unfold worst
  apply worstList_le
  intro w hw
  exact Nat.le_trans (runCost_loss_le P lo hi h w t)
    (runCost_le_worst (withLoss P hi) B t w hw)

theorem withLoss_self (P : Problem W Q A) : withLoss P P.loss = P := by
  cases P
  rfl

theorem value_loss_le [DecidableEq Q] (P : Problem W Q A) (lo hi : A → W → Nat)
    (h : ∀ a w, lo a w ≤ hi a w) (n : Nat) (B : List W) (ports : List Q) :
    value (withLoss P lo) n B ports ≤ value (withLoss P hi) n B ports := by
  let t := solve (withLoss P hi) n B ports
  have hlegal := (legal_withLoss P hi n ports t).mp
    (solve_legal (withLoss P hi) n B ports)
  have hlow := (legal_withLoss P lo n ports t).mpr hlegal
  exact Nat.le_trans (solve_optimal (withLoss P lo) n B ports t hlow)
    (worst_loss_le P lo hi h B t)

def cellCost (P : Problem W Q A) (k : A × W) : Nat := P.loss k.1 k.2

abbrev CostTable (P : Problem W Q A) := Table (cellCost P)

variable (P : Problem W Q A)

def lowerLoss (tab : CostTable P) (a : A) (w : W) : Nat := (tab (a,w)).lower

def upperLoss (tab : CostTable P) (a : A) (w : W) : Nat := (tab (a,w)).upper

def lowerModel (tab : CostTable P) : Problem W Q A := withLoss P (lowerLoss P tab)

def upperModel (tab : CostTable P) : Problem W Q A := withLoss P (upperLoss P tab)

variable [DecidableEq Q]

def lowerValue (tab : CostTable P) (n : Nat) (B : List W) (ports : List Q) : Nat :=
  value (lowerModel P tab) n B ports

def upperValue (tab : CostTable P) (n : Nat) (B : List W) (ports : List Q) : Nat :=
  value (upperModel P tab) n B ports

def upperTree (tab : CostTable P) (n : Nat) (B : List W) (ports : List Q) : Investigation Q A :=
  solve (upperModel P tab) n B ports

def gap (tab : CostTable P) (n : Nat) (B : List W) (ports : List Q) : Nat :=
  upperValue P tab n B ports - lowerValue P tab n B ports

theorem lower_le_true (tab : CostTable P) (n : Nat) (B : List W) (ports : List Q) :
    lowerValue P tab n B ports ≤ value P n B ports := by
  have h := value_loss_le P (lowerLoss P tab) P.loss
    (fun a w => (tab (a,w)).lower_ok) n B ports
  rw [withLoss_self P] at h
  exact h

theorem true_le_upper (tab : CostTable P) (n : Nat) (B : List W) (ports : List Q) :
    value P n B ports ≤ upperValue P tab n B ports := by
  have h := value_loss_le P P.loss (upperLoss P tab)
    (fun a w => (tab (a,w)).upper_ok) n B ports
  rw [withLoss_self P] at h
  exact h

theorem upperTree_legal (tab : CostTable P) (n : Nat) (B : List W) (ports : List Q) :
    Legal P n ports (upperTree P tab n B ports) :=
  (legal_withLoss P (upperLoss P tab) n ports _).mp
    (solve_legal (upperModel P tab) n B ports)

theorem upperTree_bill (tab : CostTable P) (n : Nat) (B : List W) (ports : List Q) :
    worst P B (upperTree P tab n B ports) ≤ upperValue P tab n B ports := by
  have h := worst_loss_le P P.loss (upperLoss P tab)
    (fun a w => (tab (a,w)).upper_ok) B (upperTree P tab n B ports)
  rw [withLoss_self P] at h
  exact h

/-- Certified additive approximation to the actual finite minimax optimum. -/
theorem certified_gap (tab : CostTable P) (n : Nat) (B : List W) (ports : List Q)
    (t : Investigation Q A) (ht : Legal P n ports t) :
    worst P B (upperTree P tab n B ports) ≤ worst P B t + gap P tab n B ports := by
  have hL := lower_le_true P tab n B ports
  have hU := true_le_upper P tab n B ports
  have hA := upperTree_bill P tab n B ports
  have hT := solve_optimal P n B ports t ht
  change value P n B ports ≤ worst P B t at hT
  unfold gap
  omega

theorem gap_monotone (old new : CostTable P) (h : MoreInfo old new)
    (n : Nat) (B : List W) (ports : List Q) :
    gap P new n B ports ≤ gap P old n B ports := by
  have hl : lowerValue P old n B ports ≤ lowerValue P new n B ports :=
    value_loss_le P (lowerLoss P old) (lowerLoss P new) (fun a w => (h (a,w)).1) n B ports
  have hu : upperValue P new n B ports ≤ upperValue P old n B ports :=
    value_loss_le P (upperLoss P new) (upperLoss P old) (fun a w => (h (a,w)).2) n B ports
  unfold gap
  omega

theorem pointTable_gap_zero (tab : CostTable P)
    (h : ∀ k, (tab k).lower = (tab k).upper)
    (n : Nat) (B : List W) (ports : List Q) : gap P tab n B ports = 0 := by
  have he : lowerLoss P tab = upperLoss P tab := by
    funext a w
    exact h (a,w)
  unfold gap upperValue lowerValue upperModel lowerModel
  rw [he, Nat.sub_self]

/-- Excludes acquisition/controller fees already spent or declared externally.
The actual WORST tree bill is bounded; no claim of per-world oracle regret. -/
structure NearOptimal (n : Nat) (B : List W) (ports : List Q) (eps : Nat) where
  tree : Investigation Q A
  legal : Legal P n ports tree
  lower : Nat
  upper : Nat
  lowerProof : lower ≤ value P n B ports
  upperProof : worst P B tree ≤ upper
  sufficient : upper ≤ lower + eps

theorem nearOptimal_guarantee {n : Nat} {B : List W} {ports : List Q} {eps : Nat}
    (r : NearOptimal P n B ports eps) (t : Investigation Q A)
    (ht : Legal P n ports t) : worst P B r.tree ≤ worst P B t + eps := by
  have h := solve_optimal P n B ports t ht
  change value P n B ports ≤ worst P B t at h
  have hl := r.lowerProof
  have hu := r.upperProof
  have hs := r.sufficient
  omega

/-- Evaluate each optimizer once in this executable assessment. The proofs are
not an additional pass over actual costs. -/
def assess (tab : CostTable P) (n : Nat) (B : List W) (ports : List Q) (eps : Nat) :
    Option (NearOptimal P n B ports eps) :=
  let lo := lowerValue P tab n B ports
  let t := upperTree P tab n B ports
  let hi := worst (upperModel P tab) B t
  if h : hi ≤ lo + eps then
    some ⟨t, upperTree_legal P tab n B ports, lo, hi,
      lower_le_true P tab n B ports, upperTree_bill P tab n B ports, h⟩
  else none

theorem assess_complete (tab : CostTable P) (n : Nat) (B : List W) (ports : List Q)
    (eps : Nat) (h : gap P tab n B ports ≤ eps) :
    (assess P tab n B ports eps).isSome = true := by
  have hle : upperValue P tab n B ports ≤ lowerValue P tab n B ports + eps := by
    unfold gap at h
    omega
  change (if h' : upperValue P tab n B ports ≤ lowerValue P tab n B ports + eps then
    some (⟨upperTree P tab n B ports, upperTree_legal P tab n B ports,
      lowerValue P tab n B ports, upperValue P tab n B ports,
      lower_le_true P tab n B ports, upperTree_bill P tab n B ports, h'⟩ :
      NearOptimal P n B ports eps) else none).isSome = true
  simp [hle]

/-- Sufficient end-to-end improvement against any specified reference bill.
All already paid and externally declared overhead must be included in H. -/
theorem paid_improvement {n : Nat} {B : List W} {ports : List Q} {eps : Nat}
    (r : NearOptimal P n B ports eps) (H reference : Nat)
    (h : H + r.upper < reference) : H + worst P B r.tree < reference :=
  Nat.lt_of_le_of_lt (Nat.add_le_add_left r.upperProof H) h

/-! Paid acquisition. Schedule is public, external and fixed at start.
The supplier must return evidence for the exact declared cost function. -/
structure Request {K : Type} (C : K → Nat) where
  key : K
  fee : Nat
  positive : 0 < fee
  acquire : Unit → Bounds (C key)

inductive Operation {K : Type} (C : K → Nat) where
  | acquire (request : Request C)
  | assess (tariff : Nat) -- charged tariff + 1

inductive Receipt (K : Type) where
  | acquired (key : K) (lower upper fee : Nat)
  | assessed (fee : Nat)
  deriving Repr

def receiptFee : Receipt K → Nat
  | .acquired _ _ _ f => f
  | .assessed f => f

def meter (rs : List (Receipt K)) : Nat := CRTT.LearningDiscovery.feeSum (rs.map receiptFee)

variable [DecidableEq A] [DecidableEq W]
variable (n : Nat) (B : List W) (ports : List Q) (eps : Nat)

structure Session where
  table : CostTable P
  pending : List (Operation (cellCost P))
  receipts : List (Receipt (A × W))
  result : Option (NearOptimal P n B ports eps)

def initial (tab : CostTable P) (ops : List (Operation (cellCost P))) :
    Session P n B ports eps := ⟨tab, ops, [], none⟩

def quote (s : Session P n B ports eps) : Option (QuotedStep (Session P n B ports eps)) :=
  match s.result with
  | some _ => none
  | none => match s.pending with
    | [] => none
    | .acquire r :: rest =>
      some ⟨r.fee, r.positive, fun _ =>
        let e := r.acquire ()
        let tbl := refineCell s.table r.key e
        { table := tbl, pending := rest,
          receipts := .acquired r.key e.lower e.upper r.fee :: s.receipts,
          result := s.result }⟩
    | .assess c :: rest =>
      some ⟨c+1, Nat.zero_lt_succ _, fun _ =>
        { table := s.table, pending := rest,
          receipts := .assessed (c+1) :: s.receipts,
          result := assess P s.table n B ports eps }⟩

theorem quote_meter (s : Session P n B ports eps) (q : QuotedStep (Session P n B ports eps))
    (hq : quote P n B ports eps s = some q) :
    meter (q.next ()).receipts = meter s.receipts + q.fee := by
  cases hr : s.result with
  | some r => simp [quote, hr] at hq
  | none =>
    cases hp : s.pending with
    | nil => simp [quote, hr, hp] at hq
    | cons op rest =>
      cases op <;> simp [quote, hr, hp] at hq <;> rw [← hq] <;>
        exact Nat.add_comm _ _

theorem quote_info (s : Session P n B ports eps) (q : QuotedStep (Session P n B ports eps))
    (hq : quote P n B ports eps s = some q) : MoreInfo s.table (q.next ()).table := by
  cases hr : s.result with
  | some r => simp [quote, hr] at hq
  | none =>
    cases hp : s.pending with
    | nil => simp [quote, hr, hp] at hq
    | cons op rest =>
      cases op with
      | acquire r =>
        simp [quote, hr, hp] at hq
        rw [← hq]
        exact refine_info s.table r.key (r.acquire ())
      | assess c =>
        simp [quote, hr, hp] at hq
        rw [← hq]
        exact info_refl s.table

def operationFee : Operation C → Nat
  | .acquire r => r.fee
  | .assess c => c+1

def potential (s : Session P n B ports eps) : Nat :=
  CRTT.LearningDiscovery.feeSum (s.pending.map operationFee)

theorem quote_potential (s : Session P n B ports eps) (q : QuotedStep (Session P n B ports eps))
    (hq : quote P n B ports eps s = some q) :
    potential P n B ports eps (q.next ()) + q.fee ≤ potential P n B ports eps s := by
  cases hr : s.result with
  | some r => simp [quote, hr] at hq
  | none =>
    cases hp : s.pending with
    | nil => simp [quote, hr, hp] at hq
    | cons op rest =>
      cases op with
      | acquire r =>
        -- `rw [← hq]` substitutes the structure literal but leaves `q.next ()`
        -- symbolic; rewriting with `q` itself lets the literal reduce.
        simp only [quote, hr, hp, Option.some.injEq] at hq
        subst hq
        unfold potential
        rw [hp]
        simp [operationFee, List.map_cons, CRTT.LearningDiscovery.feeSum, Nat.add_comm]
      | assess c =>
        simp only [quote, hr, hp, Option.some.injEq] at hq
        subst hq
        unfold potential
        rw [hp]
        simp [operationFee, List.map_cons, CRTT.LearningDiscovery.feeSum, Nat.add_comm]

/-- Funding the scheduled jobs guarantees quiescence, not a successful
certificate if the supplied evidence never becomes sufficiently precise. -/
theorem execute_funded_quiescent (s : Account (Session P n B ports eps))
    (hb : potential P n B ports eps s.state ≤ s.remaining) :
    quote P n B ports eps (execute (quote P n B ports eps) s).state = none := by
  let out := execute (quote P n B ports eps) s
  have hf : potential P n B ports eps out.state ≤ out.remaining :=
    CRTT.BudgetedPruning.run_funded (quote P n B ports eps) (potential P n B ports eps)
      (quote_potential P n B ports eps) s.remaining s hb
  have hk : Stuck (quote P n B ports eps) out :=
    run_stuck_of_ge_budget (quote P n B ports eps) s.remaining s (Nat.le_refl _)
  change quote P n B ports eps out.state = none
  cases hq : quote P n B ports eps out.state with
  | none => rfl
  | some q =>
    have hfee := quote_potential P n B ports eps out.state q hq
    have hno : ¬ q.fee ≤ out.remaining := by simpa [Stuck, hq] using hk
    exact False.elim (hno (by omega))

theorem execute_trace (s : Account (Session P n B ports eps)) :
    (execute (quote P n B ports eps) s).spent + meter s.state.receipts =
    s.spent + meter (execute (quote P n B ports eps) s).state.receipts :=
  CRTT.BudgetedPruning.run_meter (quote P n B ports eps) (fun u => meter u.receipts)
    (quote_meter P n B ports eps) s.remaining s

theorem execute_info (s : Account (Session P n B ports eps)) :
    MoreInfo s.state.table (execute (quote P n B ports eps) s).state.table :=
  invariant (quote P n B ports eps) (fun u => MoreInfo s.state.table u.table)
    (fun u q hu hq => info_trans _ _ _ hu (quote_info P n B ports eps u q hq))
    s.remaining s (info_refl s.state.table)

theorem execute_gap_le (s : Account (Session P n B ports eps)) :
    gap P (execute (quote P n B ports eps) s).state.table n B ports ≤
    gap P s.state.table n B ports :=
  gap_monotone P _ _ (execute_info P n B ports eps s) n B ports

theorem execute_split (s : Account (Session P n B ports eps)) (b1 b2 : Nat) :
    execute (quote P n B ports eps) (topUp s (b1+b2)) =
    execute (quote P n B ports eps) (topUp (execute (quote P n B ports eps) (topUp s b1)) b2) :=
  CRTT.ResumeLaws.execute_topUp_add (quote P n B ports eps) s b1 b2

def resume (s : Account (Session P n B ports eps)) (extra : Nat) :
    Account (Session P n B ports eps) := execute (quote P n B ports eps) (topUp s extra)

/-! Adapter to actual completed T25 plans, not to the provided prediction.
An exact acquisition runs the known catalogue entry under a prepaid charge
covering its reservation + a positive surcharge. No claim of refund or CPU
bound. Actual hidden-world identity is never supplied to the online tree. -/
section Adapter
open CRTT.MetaInvestigation
variable {sw sp sa tw tp ta : Nat}
variable (M : MetaTask W Q A sw sp sa tw tp ta)

def actualProblem : Problem W Q A :=
  withLoss (problem M) (fun a w => actualBill (M.pair w).source (M.pair w).target M.fees (M.plan a))

def reserved (a : A) : Nat := (M.plan a).setupFee + (M.plan a).learningBudget + (M.plan a).reserve

def initialBounds : CostTable (actualProblem M) := fun k =>
  ⟨(M.plan k.1).setupFee, reserved M k.1,
    Nat.le_add_right _ _,
    actualBill_le_reservation (M.pair k.2).source (M.pair k.2).target M.fees (M.plan k.1)⟩

def exactRequest (k : A × W) (surcharge : Nat) : Request (cellCost (actualProblem M)) :=
  ⟨k, reserved M k.1 + (surcharge + 1), Nat.zero_lt_succ _,
    fun _ => exactBounds (cellCost (actualProblem M) k)⟩

theorem exactRequest_charge_covers (k : A × W) (surcharge : Nat) :
    cellCost (actualProblem M) k ≤ (exactRequest M k surcharge).fee :=
  Nat.le_trans (initialBounds M k).upper_ok (Nat.le_add_right _ _)

/-- The exact acquisition produces a point interval, not a prediction. -/
theorem exactRequest_point (k : A × W) (surcharge : Nat) :
    ((exactRequest M k surcharge).acquire ()).lower = cellCost (actualProblem M) k ∧
    ((exactRequest M k surcharge).acquire ()).upper = cellCost (actualProblem M) k :=
  ⟨rfl, rfl⟩

/-- The actual-model semantics is exactly the T25 selected execution bill,
before adding the fixed controller and offline acquisition charges. -/
theorem actualModel_runCost (w : W) (t : Investigation Q A) :
    runCost (actualProblem M) w t = executionCost M w t :=
  (walk_cost (actualProblem M) w t).symm

theorem accepted_actual_bill (r : NearOptimal (actualProblem M) n M.worlds M.ports eps)
    (w : W) (hw : w ∈ M.worlds) :
    (runMeta M w r.tree).2.2 ≤ M.controllerFee + r.upper := by
  rw [runMeta_bill M w r.tree, ← actualModel_runCost M w r.tree]
  exact Nat.add_le_add_left (Nat.le_trans
    (runCost_le_worst (actualProblem M) M.worlds r.tree w hw) r.upperProof) _

theorem accepted_complete (r : NearOptimal (actualProblem M) n M.worlds M.ports eps)
    (w : W) (N : CRTT.MorphismDiscovery.Morphism (M.pair w).source (M.pair w).target) :
    N ∈ (runMeta M w r.tree).2.1.2.state.certificates ↔
      N ∈ CRTT.MorphismDiscovery.discoverAll (M.pair w).source (M.pair w).target :=
  runMeta_complete M w r.tree N

end Adapter

#print axioms info_refl
#print axioms info_trans
#print axioms refine_at
#print axioms refine_elsewhere
#print axioms refine_info
#print axioms legal_withLoss
#print axioms runCost_loss_le
#print axioms worst_loss_le
#print axioms withLoss_self
#print axioms value_loss_le
#print axioms lower_le_true
#print axioms true_le_upper
#print axioms upperTree_legal
#print axioms upperTree_bill
#print axioms certified_gap
#print axioms gap_monotone
#print axioms pointTable_gap_zero
#print axioms nearOptimal_guarantee
#print axioms assess_complete
#print axioms paid_improvement
#print axioms quote_meter
#print axioms quote_info
#print axioms quote_potential
#print axioms execute_funded_quiescent
#print axioms execute_trace
#print axioms execute_info
#print axioms execute_gap_le
#print axioms execute_split
#print axioms initialBounds
#print axioms exactRequest
#print axioms exactRequest_charge_covers
#print axioms exactRequest_point
#print axioms actualModel_runCost
#print axioms accepted_actual_bill
#print axioms accepted_complete
end CRTT.MetaEvidenceAcquisition
