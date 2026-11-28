import CertifiedPruning

/-! Budgeted prefix search. All prices are abstract operation charges, not
wall-clock bounds. One paid prepare step may enumerate a complete action-map
list. The proof-only reference list is never computed by quote or execute. -/
namespace CRTT.BudgetedPruning
open CRTT.MorphismDiscovery CRTT.CertifiedPruning CRTT.BudgetedDiscovery
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

variable {sw sp sa tw tp ta : Nat}
variable (S : IndexedTask sw sp sa) (T : IndexedTask tw tp ta)

inductive Job where
  | ports (remaining : List (Fin sp)) (assigned : PartialAssign sp tp)
      (rules : RuleLibrary S T)
  | actions (p : Fin sp → Fin tp) (remaining : List (Fin (sa+1) → Fin (ta+1)))

inductive Kind where
  | rule | split | prepare | action
  deriving Repr, DecidableEq

structure Receipt where
  kind : Kind
  fee : Nat
  deriving Repr, DecidableEq

/-- Stored base fees are incremented by one to guarantee positivity. A rule
uses its declared abstract cost plus one administrative unit. -/
structure Fees where
  split : Nat
  prepare : Nat
  action : Nat

structure Update where
  jobs : List (Job S T)
  emitted : List (Morphism S T)

structure Frontier where
  jobs : List (Job S T)
  certificates : List (Morphism S T)
  receipts : List Receipt -- reverse chronological, constant-time insertion

def initial (policy : RuleLibrary S T) : Frontier S T :=
  ⟨[.ports (indices sp) [] policy], [], []⟩

def bill (fees : Fees) : Job S T → Receipt
  | .ports _ _ (r :: _) => ⟨.rule, r.cost + 1⟩
  | .ports (_ :: _) _ [] => ⟨.split, fees.split + 1⟩
  | .ports [] _ [] => ⟨.prepare, fees.prepare + 1⟩
  | .actions _ _ => ⟨.action, fees.action + 1⟩

theorem bill_positive (fees : Fees) (j : Job S T) : 0 < (bill S T fees j).fee := by
  cases j with
  | ports qs rho rs =>
    cases rs with
    | nil => cases qs <;> simp [bill]
    | cons r rs => simp [bill]
  | actions p as => simp [bill]

/-- Each rule is tested separately. Children are generated only by a paid
split; action maps only by a paid prepare after the original T22 guard. -/
def jobStep (policy : RuleLibrary S T) : Job S T → Update S T
  | .ports qs rho (r :: rs) =>
    if r.keep rho then ⟨[.ports qs rho rs], []⟩ else ⟨[], []⟩
  | .ports (q :: qs) rho [] =>
    ⟨(indices tp).map (fun t => .ports qs ((q,t) :: rho) policy), []⟩
  | .ports [] rho [] =>
    match decodePortMap rho with
    | none => ⟨[], []⟩
    | some p =>
      if S.depth ≤ T.depth ∧ portOK S T p = true ∧ readCover S T p = true then
        ⟨[.actions p (maps (ta+1) (sa+1))], []⟩
      else ⟨[], []⟩
  | .actions _ [] => ⟨[], []⟩
  | .actions p (a :: rest) =>
    ⟨[.actions p rest], match certifyPair S T p a with
      | none => []
      | some m => [m]⟩

def advance (policy : RuleLibrary S T) (fees : Fees) (s : Frontier S T)
    (j : Job S T) (rest : List (Job S T)) : Frontier S T :=
  let u := jobStep S T policy j
  ⟨u.jobs ++ rest, s.certificates ++ u.emitted, bill S T fees j :: s.receipts⟩

def quote (policy : RuleLibrary S T) (fees : Fees) (s : Frontier S T) :
    Option (QuotedStep (Frontier S T)) :=
  match s.jobs with
  | [] => none
  | j :: rest => some ⟨(bill S T fees j).fee, bill_positive S T fees j,
      fun _ => advance S T policy fees s j rest⟩

/-- A canonical certificate is exactly the result of its own operational pair. -/
theorem canonical_pair (N : Morphism S T) (h : N ∈ discoverAll S T) :
    certifyPair S T N.portMap N.actionMap = some N := by
  have hd : S.depth ≤ T.depth := N.depth_le
  have hflat : N ∈ (portCandidates S T).flatMap (discoverForPort S T) := by
    simpa [discoverAll, hd] using h
  obtain ⟨p, _, hn⟩ := List.mem_flatMap.mp hflat
  have hm : some N ∈ (maps (ta+1) (sa+1)).map (certifyPair S T p) :=
    (mem_collectSome _ _).mp hn
  obtain ⟨a, _, ha⟩ := List.mem_map.mp hm
  have he := certified_pair_maps S T p a N ha
  rw [he.1, he.2]
  exact ha

theorem certified_mem_reference (p : Fin sp → Fin tp) (a : Fin (sa+1) → Fin (ta+1))
    (N : Morphism S T) (h : certifyPair S T p a = some N) : N ∈ discoverAll S T := by
  have he := certified_pair_maps S T p a N h
  have hp : p ∈ portCandidates S T := by
    rw [← he.1]
    exact morphism_portCandidate S T N
  have hm : some N ∈ (maps (ta+1) (sa+1)).map (certifyPair S T p) :=
    List.mem_map.mpr ⟨a, maps_complete (ta+1) (sa+1) a, h⟩
  have hf : N ∈ discoverForPort S T p := (mem_collectSome _ _).mpr hm
  have hd : S.depth ≤ T.depth := N.depth_le
  simpa [discoverAll, hd] using
    (List.mem_flatMap.mpr ⟨p, hp, hf⟩ : N ∈ (portCandidates S T).flatMap (discoverForPort S T))

/-- Declarative coverage, not a program enumerating the denotation. A port
job covers a canonical certificate if all its still-missing ports occur in qs. -/
def Covers (N : Morphism S T) : Job S T → Prop
  | .ports qs rho _ => Extends S T N rho ∧
      ∀ q, q ∈ qs ∨ (q, N.portMap q) ∈ rho
  | .actions p as => N.portMap = p ∧ N.actionMap ∈ as

def Covered (N : Morphism S T) (jobs : List (Job S T)) : Prop :=
  ∃ j ∈ jobs, Covers S T N j

theorem jobStep_sound (policy : RuleLibrary S T) (j : Job S T)
    (N : Morphism S T) (h : N ∈ (jobStep S T policy j).emitted) : N ∈ discoverAll S T := by
  cases j with
  | ports qs rho rs =>
    cases rs with
    | cons r rs =>
      by_cases hk : r.keep rho = true <;> simp [jobStep, hk] at h
    | nil =>
      cases qs with
      | cons q qs => simp [jobStep] at h
      | nil =>
        cases hd : decodePortMap rho with
        | none => simp [jobStep, hd] at h
        | some p =>
          by_cases hc : S.depth ≤ T.depth ∧ portOK S T p = true ∧ readCover S T p = true <;>
            simp [jobStep, hd, hc] at h
  | actions p as =>
    cases as with
    | nil => simp [jobStep] at h
    | cons a rest =>
      cases hc : certifyPair S T p a with
      | none => simp [jobStep, hc] at h
      | some m =>
        have he : N = m := by simpa [jobStep, hc] using h
        subst N
        exact certified_mem_reference S T p a m hc

theorem jobStep_covers (policy : RuleLibrary S T) (j : Job S T)
    (N : Morphism S T) (hn : N ∈ discoverAll S T) (h : Covers S T N j) :
    N ∈ (jobStep S T policy j).emitted ∨ Covered S T N (jobStep S T policy j).jobs := by
  cases j with
  | ports qs rho rs =>
    change Extends S T N rho ∧ (∀ q, q ∈ qs ∨ (q, N.portMap q) ∈ rho) at h
    cases rs with
    | cons r rs =>
      have hk := r.sound N rho h.1
      right
      refine ⟨.ports qs rho rs, ?_, h⟩
      simp [jobStep, hk]
    | nil =>
      cases qs with
      | nil =>
        have hf : ∀ q, (q, N.portMap q) ∈ rho := by
          intro q
          rcases h.2 q with he | hm
          · cases he
          · exact hm
        have hd := decodePortMap_of_extends S T N rho h.1 hf
        have hc : S.depth ≤ T.depth ∧ portOK S T N.portMap = true ∧ readCover S T N.portMap = true :=
          ⟨N.depth_le, morphism_portOK S T N, morphism_readCover S T N⟩
        right
        refine ⟨.actions N.portMap (maps (ta+1) (sa+1)), ?_, ?_⟩
        · simp [jobStep, hd, hc]
        · exact ⟨rfl, maps_complete (ta+1) (sa+1) N.actionMap⟩
      | cons q qs =>
        right
        refine ⟨.ports qs ((q, N.portMap q) :: rho) policy, ?_, ?_⟩
        · change Job.ports qs ((q, N.portMap q) :: rho) policy ∈
            (indices tp).map (fun t => Job.ports qs ((q,t) :: rho) policy)
          exact List.mem_map.mpr ⟨N.portMap q, mem_indices tp (N.portMap q), rfl⟩
        · constructor
          · intro e he
            rcases List.mem_cons.mp he with he' | ht
            · subst e
              rfl
            · exact h.1 e ht
          · intro r
            rcases h.2 r with hr | hr
            · rcases List.mem_cons.mp hr with he | ht
              · subst r
                exact Or.inr (List.Mem.head _)
              · exact Or.inl ht
            · exact Or.inr (List.Mem.tail _ hr)
  | actions p as =>
    change N.portMap = p ∧ N.actionMap ∈ as at h
    cases as with
    | nil => cases h.2
    | cons a rest =>
      rcases List.mem_cons.mp h.2 with he | ht
      · left
        have hc := canonical_pair S T N hn
        rw [h.1, he] at hc
        simp [jobStep, hc]
      · right
        refine ⟨.actions p rest, ?_, ⟨h.1, ht⟩⟩
        exact List.Mem.head _

/-- Two-sided global correctness: emitted certificates are canonical, and
no canonical certificate is lost. Overlap of abstract job denotations is
allowed; we do not assert a disjoint partition or list-order equality. -/
def Correct (s : Frontier S T) : Prop :=
  (∀ N ∈ s.certificates, N ∈ discoverAll S T) ∧
  (∀ N ∈ discoverAll S T, N ∈ s.certificates ∨ Covered S T N s.jobs)

theorem initial_correct (policy : RuleLibrary S T) : Correct S T (initial S T policy) := by
  constructor
  · intro N h
    cases h
  · intro N _
    right
    refine ⟨.ports (indices sp) [] policy, List.Mem.head _, ?_⟩
    constructor
    · intro e h
      cases h
    · intro q
      exact Or.inl (mem_indices sp q)

theorem quote_correct (policy : RuleLibrary S T) (fees : Fees) (s : Frontier S T)
    (q : QuotedStep (Frontier S T)) (hs : Correct S T s)
    (hq : quote S T policy fees s = some q) : Correct S T (q.next ()) := by
  cases hj : s.jobs with
  | nil => simp [quote, hj] at hq
  | cons j rest =>
    simp [quote, hj] at hq
    rw [← hq]
    change Correct S T (advance S T policy fees s j rest)
    constructor
    · intro N hm
      change N ∈ s.certificates ++ (jobStep S T policy j).emitted at hm
      rcases List.mem_append.mp hm with ha | hb
      · exact hs.1 N ha
      · exact jobStep_sound S T policy j N hb
    · intro N hn
      rcases hs.2 N hn with hm | ⟨k, hk, hc⟩
      · exact Or.inl (List.mem_append.mpr (Or.inl hm))
      · rw [hj] at hk
        rcases List.mem_cons.mp hk with he | ht
        · subst k
          rcases jobStep_covers S T policy j N hn hc with ha | ⟨k, hmem, hcov⟩
          · exact Or.inl (List.mem_append.mpr (Or.inr ha))
          · exact Or.inr ⟨k, List.mem_append.mpr (Or.inl hmem), hcov⟩
        · exact Or.inr ⟨k, List.mem_append.mpr (Or.inr ht), hc⟩

theorem execute_correct (policy : RuleLibrary S T) (fees : Fees)
    (s : Account (Frontier S T)) (hs : Correct S T s.state) :
    Correct S T (execute (quote S T policy fees) s).state :=
  invariant (quote S T policy fees) (Correct S T)
    (quote_correct S T policy fees) s.remaining s hs

theorem exhausted_iff (s : Frontier S T) (hs : Correct S T s) (he : s.jobs = [])
    (N : Morphism S T) : N ∈ s.certificates ↔ N ∈ discoverAll S T := by
  constructor
  · exact hs.1 N
  · intro hn
    rcases hs.2 N hn with hm | ⟨j, hj, _⟩
    · exact hm
    · rw [he] at hj
      cases hj

theorem exhausted_impossible (s : Frontier S T) (hs : Correct S T s)
    (he : s.jobs = []) (hc : s.certificates = []) : ¬ Nonempty (Morphism S T) := by
  rintro ⟨M⟩
  obtain ⟨N, hn, _, _⟩ := discover_complete S T M
  have hm := (exhausted_iff S T s hs he N).mpr hn
  rw [hc] at hm
  cases hm

/-! Exact trace accounting for the actual paid transition system. -/
def receiptCost : List Receipt → Nat
  | [] => 0
  | r :: rs => r.fee + receiptCost rs

theorem quote_receipt_cost (policy : RuleLibrary S T) (fees : Fees) (s : Frontier S T)
    (q : QuotedStep (Frontier S T)) (hq : quote S T policy fees s = some q) :
    receiptCost (q.next ()).receipts = receiptCost s.receipts + q.fee := by
  cases hj : s.jobs with
  | nil => simp [quote, hj] at hq
  | cons j rest =>
    simp [quote, hj] at hq
    rw [← hq]
    change (bill S T fees j).fee + receiptCost s.receipts = _
    exact Nat.add_comm _ _

/-- Generic meter lemma: executed fees, not estimated counts, account for spend. -/
theorem run_meter (qf : U → Option (QuotedStep U)) (meter : U → Nat)
    (hfee : ∀ s q, qf s = some q → meter (q.next ()) = meter s + q.fee)
    (n : Nat) (s : Account U) :
    (run qf n s).spent + meter s.state = s.spent + meter (run qf n s).state := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    cases hq : qf s.state with
    | none => simp [run, hq]
    | some q =>
      by_cases hp : q.fee ≤ s.remaining
      · let paid : Account U := ⟨q.next (), s.remaining - q.fee, s.spent + q.fee⟩
        have hstep : run qf (n+1) s = run qf n paid := by
          change run qf (n+1) s = run qf n ⟨q.next (), s.remaining - q.fee, s.spent + q.fee⟩
          simp [run, hq, hp]
        have hi := ih paid
        have hm : meter paid.state = meter s.state + q.fee := hfee s.state q hq
        have hs : paid.spent = s.spent + q.fee := rfl
        rw [hstep]
        omega
      · simp [run, hq, hp]

theorem execute_trace (policy : RuleLibrary S T) (fees : Fees) (s : Account (Frontier S T)) :
    (execute (quote S T policy fees) s).spent + receiptCost s.state.receipts =
      s.spent + receiptCost (execute (quote S T policy fees) s).state.receipts :=
  run_meter (quote S T policy fees) (fun u => receiptCost u.receipts)
    (quote_receipt_cost S T policy fees) s.remaining s

/-! A proof-only potential bounds remaining abstract charges (including the
paid empty action-list retirement). It is not evaluated by `resume`. -/
def rulesCost : RuleLibrary S T → Nat
  | [] => 0
  | r :: rs => (r.cost + 1) + rulesCost rs

def portsBudget (policy : RuleLibrary S T) (fees : Fees) : Nat → Nat
  | 0 => (fees.prepare + 1) + ((maps (ta+1) (sa+1)).length + 1) * (fees.action + 1)
  | n+1 => (fees.split + 1) + (indices tp).length * (rulesCost S T policy + portsBudget policy fees n)

def jobBudget (policy : RuleLibrary S T) (fees : Fees) : Job S T → Nat
  | .ports qs _ rs => rulesCost S T rs + portsBudget S T policy fees qs.length
  | .actions _ as => (as.length + 1) * (fees.action + 1)

def jobsBudget (policy : RuleLibrary S T) (fees : Fees) : List (Job S T) → Nat
  | [] => 0
  | j :: js => jobBudget S T policy fees j + jobsBudget policy fees js

theorem jobsBudget_append (policy : RuleLibrary S T) (fees : Fees) (xs ys : List (Job S T)) :
    jobsBudget S T policy fees (xs ++ ys) = jobsBudget S T policy fees xs + jobsBudget S T policy fees ys := by
  induction xs with
  | nil => simp [jobsBudget]
  | cons j js ih => simp [jobsBudget, ih, Nat.add_assoc]

theorem childrenBudget (policy : RuleLibrary S T) (fees : Fees) (q : Fin sp)
    (qs : List (Fin sp)) (rho : PartialAssign sp tp) (ts : List (Fin tp)) :
    jobsBudget S T policy fees (ts.map (fun t => Job.ports qs ((q,t) :: rho) policy)) =
      ts.length * (rulesCost S T policy + portsBudget S T policy fees qs.length) := by
  induction ts with
  | nil => simp [jobsBudget]
  | cons t ts ih =>
    change (rulesCost S T policy + portsBudget S T policy fees qs.length) +
      jobsBudget S T policy fees (ts.map (fun u => Job.ports qs ((q,u) :: rho) policy)) =
      (ts.length + 1) * (rulesCost S T policy + portsBudget S T policy fees qs.length)
    rw [ih, Nat.add_mul ts.length 1 (rulesCost S T policy + portsBudget S T policy fees qs.length), Nat.one_mul]
    exact Nat.add_comm _ _

theorem job_budget_step (policy : RuleLibrary S T) (fees : Fees) (j : Job S T) :
    jobsBudget S T policy fees (jobStep S T policy j).jobs + (bill S T fees j).fee ≤
      jobBudget S T policy fees j := by
  cases j with
  | ports qs rho rs =>
    cases rs with
    | cons r rs =>
      by_cases hk : r.keep rho = true <;>
        simp [jobStep, hk, bill, jobBudget, jobsBudget, rulesCost] <;> omega
    | nil =>
      cases qs with
      | cons q qs =>
        change jobsBudget S T policy fees ((indices tp).map
          (fun t => Job.ports qs ((q,t) :: rho) policy)) + (fees.split + 1) ≤
          0 + ((fees.split + 1) + (indices tp).length *
            (rulesCost S T policy + portsBudget S T policy fees qs.length))
        rw [childrenBudget S T policy fees q qs rho (indices tp)]
        omega
      | nil =>
        cases hd : decodePortMap rho with
        | none => simp [jobStep, hd, bill, jobBudget, jobsBudget, rulesCost, portsBudget] <;> omega
        | some p =>
          by_cases hc : S.depth ≤ T.depth ∧ portOK S T p = true ∧ readCover S T p = true <;>
            simp [jobStep, hd, hc, bill, jobBudget, jobsBudget, rulesCost, portsBudget] <;> omega
  | actions p as =>
    cases as with
    | nil => simp [jobStep, bill, jobBudget, jobsBudget]
    | cons a rest =>
      change (rest.length + 1) * (fees.action + 1) + 0 + (fees.action + 1) ≤
        (rest.length + 1 + 1) * (fees.action + 1)
      rw [Nat.add_zero]
      have he : (rest.length + 1 + 1) * (fees.action + 1) =
          (rest.length + 1) * (fees.action + 1) + (fees.action + 1) := by
        rw [Nat.add_mul (rest.length + 1) 1 (fees.action + 1), Nat.one_mul]
      exact Nat.le_of_eq he.symm

def potential (policy : RuleLibrary S T) (fees : Fees) (s : Frontier S T) : Nat :=
  jobsBudget S T policy fees s.jobs

theorem quote_potential (policy : RuleLibrary S T) (fees : Fees) (s : Frontier S T)
    (q : QuotedStep (Frontier S T)) (hq : quote S T policy fees s = some q) :
    potential S T policy fees (q.next ()) + q.fee ≤ potential S T policy fees s := by
  cases hj : s.jobs with
  | nil => simp [quote, hj] at hq
  | cons j rest =>
    simp [quote, hj] at hq
    rw [← hq]
    change jobsBudget S T policy fees ((jobStep S T policy j).jobs ++ rest) +
      (bill S T fees j).fee ≤ jobsBudget S T policy fees s.jobs
    rw [hj, jobsBudget_append S T policy fees]
    change jobsBudget S T policy fees (jobStep S T policy j).jobs + jobsBudget S T policy fees rest +
      (bill S T fees j).fee ≤ jobBudget S T policy fees j + jobsBudget S T policy fees rest
    have hb := job_budget_step S T policy fees j
    omega

theorem potential_decreases (policy : RuleLibrary S T) (fees : Fees) (s : Frontier S T)
    (q : QuotedStep (Frontier S T)) (hq : quote S T policy fees s = some q) :
    potential S T policy fees (q.next ()) < potential S T policy fees s := by
  have hb := quote_potential S T policy fees s q hq
  have hp := q.positive
  omega

/-- If every successor's remaining liability plus its charge fits the current
liability, sufficient money remains sufficient after any paid prefix. -/
theorem run_funded (qf : U → Option (QuotedStep U)) (pot : U → Nat)
    (hpot : ∀ s q, qf s = some q → pot (q.next ()) + q.fee ≤ pot s)
    (n : Nat) (s : Account U) (hs : pot s.state ≤ s.remaining) :
    pot (run qf n s).state ≤ (run qf n s).remaining := by
  induction n generalizing s with
  | zero => exact hs
  | succ n ih =>
    cases hq : qf s.state with
    | none => simpa [run, hq] using hs
    | some q =>
      have hb := hpot s.state q hq
      have hp : q.fee ≤ s.remaining := by omega
      let paid : Account U := ⟨q.next (), s.remaining - q.fee, s.spent + q.fee⟩
      have hstep : run qf (n+1) s = run qf n paid := by
        change run qf (n+1) s = run qf n ⟨q.next (), s.remaining - q.fee, s.spent + q.fee⟩
        simp [run, hq, hp]
      have hpaid : pot paid.state ≤ paid.remaining := by
        change pot (q.next ()) ≤ s.remaining - q.fee
        omega
      rw [hstep]
      exact ih paid hpaid

theorem execute_funded_exhausts (policy : RuleLibrary S T) (fees : Fees)
    (s : Account (Frontier S T)) (hb : potential S T policy fees s.state ≤ s.remaining) :
    (execute (quote S T policy fees) s).state.jobs = [] := by
  let out := execute (quote S T policy fees) s
  have hf : potential S T policy fees out.state ≤ out.remaining :=
    run_funded (quote S T policy fees) (potential S T policy fees)
      (quote_potential S T policy fees) s.remaining s hb
  have hk : Stuck (quote S T policy fees) out :=
    run_stuck_of_ge_budget (quote S T policy fees) s.remaining s (Nat.le_refl _)
  change out.state.jobs = []
  cases hj : out.state.jobs with
  | nil => rfl
  | cons j rest =>
    let q : QuotedStep (Frontier S T) := ⟨(bill S T fees j).fee, bill_positive S T fees j,
      fun _ => advance S T policy fees out.state j rest⟩
    have hq : quote S T policy fees out.state = some q := by
      unfold quote
      rw [hj]
    have hfee := quote_potential S T policy fees out.state q hq
    have hno : ¬ q.fee ≤ out.remaining := by simpa [Stuck, hq] using hk
    exact False.elim (hno (by omega))

theorem execute_full (policy : RuleLibrary S T) (fees : Fees)
    (s : Account (Frontier S T)) (hs : Correct S T s.state)
    (hb : potential S T policy fees s.state ≤ s.remaining) (N : Morphism S T) :
    N ∈ (execute (quote S T policy fees) s).state.certificates ↔ N ∈ discoverAll S T :=
  exhausted_iff S T _ (execute_correct S T policy fees s hs)
    (execute_funded_exhausts S T policy fees s hb) N

theorem execute_split (policy : RuleLibrary S T) (fees : Fees)
    (s : Account (Frontier S T)) (b1 b2 : Nat) :
    execute (quote S T policy fees) (topUp s (b1+b2)) =
      execute (quote S T policy fees) (topUp (execute (quote S T policy fees) (topUp s b1)) b2) := by
  simp only [execute_eq_saturate (quote S T policy fees) (potential S T policy fees)
    (potential_decreases S T policy fees)]
  exact saturate_topUp_add (quote S T policy fees) (potential S T policy fees)
    (potential_decreases S T policy fees) s b1 b2

structure CertifiedAccount where
  account : Account (Frontier S T)
  correct : Correct S T account.state

def start (policy : RuleLibrary S T) (budget : Nat) : CertifiedAccount S T :=
  ⟨⟨initial S T policy, budget, 0⟩, initial_correct S T policy⟩

def resume (policy : RuleLibrary S T) (fees : Fees) (s : CertifiedAccount S T)
    (extra : Nat) : CertifiedAccount S T :=
  ⟨execute (quote S T policy fees) (topUp s.account extra),
    execute_correct S T policy fees (topUp s.account extra) s.correct⟩

theorem start_full (policy : RuleLibrary S T) (fees : Fees) (budget : Nat)
    (hb : potential S T policy fees (initial S T policy) ≤ budget) (N : Morphism S T) :
    N ∈ (resume S T policy fees (start S T policy budget) 0).account.state.certificates ↔
      N ∈ discoverAll S T := by
  exact execute_full S T policy fees (topUp (start S T policy budget).account 0)
    (initial_correct S T policy) (by simpa [start, topUp] using hb) N

theorem quote_certificate_prefix (policy : RuleLibrary S T) (fees : Fees) (s : Frontier S T)
    (q : QuotedStep (Frontier S T)) (hq : quote S T policy fees s = some q) :
    ∃ tail, (q.next ()).certificates = s.certificates ++ tail := by
  cases hj : s.jobs with
  | nil => simp [quote, hj] at hq
  | cons j rest =>
    simp [quote, hj] at hq
    rw [← hq]
    exact ⟨(jobStep S T policy j).emitted, rfl⟩

theorem execute_certificate_prefix (policy : RuleLibrary S T) (fees : Fees)
    (s : Account (Frontier S T)) :
    ∃ tail, (execute (quote S T policy fees) s).state.certificates = s.state.certificates ++ tail := by
  let P : Frontier S T → Prop := fun u => ∃ tail, u.certificates = s.state.certificates ++ tail
  have hclosed : ∀ u q, P u → quote S T policy fees u = some q → P (q.next ()) := by
    intro u q hu hq
    obtain ⟨a, ha⟩ := hu
    obtain ⟨b, hb⟩ := quote_certificate_prefix S T policy fees u q hq
    exact ⟨a ++ b, by rw [hb, ha, List.append_assoc]⟩
  exact invariant (quote S T policy fees) P hclosed s.remaining s
    ⟨[], (List.append_nil _).symm⟩

inductive Outcome where
  | found (m : Morphism S T)
  | impossible (proof : ¬ Nonempty (Morphism S T))
  | inconclusive

def verdict (s : CertifiedAccount S T) : Outcome S T :=
  match hc : s.account.state.certificates with
  | m :: _ => .found m
  | [] => match he : s.account.state.jobs with
    | [] => .impossible (exhausted_impossible S T s.account.state s.correct he hc)
    | _ :: _ => .inconclusive

def classify (s : CertifiedAccount S T) : Outcome S T × CertifiedAccount S T :=
  (verdict S T s, s)

#print axioms bill_positive
#print axioms canonical_pair
#print axioms certified_mem_reference
#print axioms jobStep_sound
#print axioms jobStep_covers
#print axioms initial_correct
#print axioms quote_correct
#print axioms execute_correct
#print axioms exhausted_iff
#print axioms exhausted_impossible
#print axioms quote_receipt_cost
#print axioms run_meter
#print axioms execute_trace
#print axioms jobsBudget_append
#print axioms childrenBudget
#print axioms job_budget_step
#print axioms quote_potential
#print axioms potential_decreases
#print axioms run_funded
#print axioms execute_funded_exhausts
#print axioms execute_full
#print axioms execute_split
#print axioms start_full
#print axioms quote_certificate_prefix
#print axioms execute_certificate_prefix
#print axioms verdict
#print axioms classify
end CRTT.BudgetedPruning
