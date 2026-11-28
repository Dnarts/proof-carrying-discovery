import ImpasseCompilation
import ResumeLaws

/-! Endogenous compilation of read obstructions. The next quote depends on
research history, not on the balance. Core retention uses semantic inclusion;
this is not an economic-dominance claim. -/
namespace CRTT.LearningDiscovery
open CRTT.MorphismDiscovery CRTT.CertifiedPruning CRTT.ImpasseCompilation
open CRTT.BudgetedDiscovery
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

variable {sw sp sa tw tp ta : Nat}
variable (S : IndexedTask sw sp sa) (T : IndexedTask tw tp ta)

abbrev CoreLib := List (ObstructionCore S T)

def Rejects (lib : CoreLib S T) (rho : PartialAssign sp tp) : Prop :=
  ∃ k ∈ lib, Sub k.constraints rho

/-- Keep an already subsuming core; otherwise insert and remove supersets.
These are active rules, not the append-only evidence history. -/
def insertCore (k : ObstructionCore S T) (lib : CoreLib S T) : CoreLib S T :=
  match first (fun old => containsCore old.constraints k.constraints) lib with
  | some _ => lib
  | none => k :: lib.filter (fun old => !(containsCore k.constraints old.constraints))

theorem sub_trans {α : Type} {a b c : List α} (hab : Sub a b) (hbc : Sub b c) : Sub a c :=
  fun e he => hbc e (hab e he)

theorem insertCore_rejects (k : ObstructionCore S T) (lib : CoreLib S T)
    (rho : PartialAssign sp tp) :
    Rejects S T (insertCore S T k lib) rho ↔ Rejects S T lib rho ∨ Sub k.constraints rho := by
  cases h : first (fun old : ObstructionCore S T => containsCore old.constraints k.constraints) lib with
  | some old =>
    have hm := first_sound (fun old : ObstructionCore S T => containsCore old.constraints k.constraints) lib old h
    have hs := (containsCore_iff old.constraints k.constraints).mp hm.2
    have he : insertCore S T k lib = lib := by simp [insertCore, h]
    rw [he]
    constructor
    · exact Or.inl
    · intro hh
      rcases hh with hr | hk
      · exact hr
      · exact ⟨old, hm.1, sub_trans hs hk⟩
  | none =>
    have he : insertCore S T k lib = k :: lib.filter (fun old => !(containsCore k.constraints old.constraints)) := by
      simp [insertCore, h]
    rw [he]
    constructor
    · rintro ⟨old, hm, hs⟩
      rcases List.mem_cons.mp hm with hk | ht
      · subst old
        exact Or.inr hs
      · exact Or.inl ⟨old, (List.mem_filter.mp ht).1, hs⟩
    · intro hh
      rcases hh with ⟨old, hm, hs⟩ | hk
      · cases hc : containsCore k.constraints old.constraints with
        | true => exact ⟨k, List.Mem.head _, sub_trans ((containsCore_iff _ _).mp hc) hs⟩
        | false =>
          exact ⟨old, List.Mem.tail _ (List.mem_filter.mpr ⟨hm, by simp [hc]⟩), hs⟩
      · exact ⟨k, List.Mem.head _, hk⟩

theorem library_sound (lib : CoreLib S T) (rho : PartialAssign sp tp)
    (h : Rejects S T lib rho) : ¬ ∃ M : Morphism S T, Extends S T M rho := by
  obtain ⟨k, _, hk⟩ := h
  exact core_excludes S T k rho hk

/-- Recover a typed witness from a failed local read row. -/
def findCore (rho : PartialAssign sp tp) : Option (ObstructionCore S T) :=
  match h : first (fun x => rowBad S T x rho) (indices tw) with
  | none => none
  | some x => some ⟨x, rho, (first_sound _ _ x h).2⟩

theorem findCore_constraints (rho : PartialAssign sp tp) (k : ObstructionCore S T)
    (h : findCore S T rho = some k) : k.constraints = rho := by
  -- `findCore`'s dependent `match h :` motive blocks rewriting an equation into
  -- `h` (the motive mentions the scrutinee, so `rw`/`simp at h` are ill-typed).
  -- Unfolding the definition with `findCore.eq_def` exposes the plain `match`,
  -- which `split` then refines per branch with its own hypothesis.
  unfold findCore at h
  split at h
  · exact nomatch h
  · rename_i x _
    simp only [Option.some.injEq] at h
    rw [← h]

/-- Each learned event retains both the original obstruction and the certified
reduction, even if its compiled rule is later subsumed. -/
structure LearnedEvent where
  raw : ObstructionCore S T
  reduced : Extraction S T raw.world raw.constraints

inductive Stage where
  | lookup | probe | advance
  deriving DecidableEq

structure State where
  frontier : CRTT.BudgetedPruning.Frontier S T
  library : CoreLib S T
  history : List (LearnedEvent S T)
  pending : Option (ObstructionCore S T)
  stage : Stage
  feesPaid : List Nat

structure Fees where
  base : CRTT.BudgetedPruning.Fees
  lookup : Nat
  perCore : Nat
  probe : Nat
  compile : Nat

def initial (base : RuleLibrary S T) : State S T :=
  ⟨CRTT.BudgetedPruning.initial S T base, [], [], none, .lookup, []⟩

/-- Charge a conservative scan tariff. No rule is evaluated when quoting. -/
def lookupFee (fees : Fees) (s : State S T) : Nat :=
  fees.lookup + s.library.length * fees.perCore + 1

/-- Check the *current* library, not the snapshot at creation of a job. -/
def lookupStep (s : State S T) (rho : PartialAssign sp tp)
    (rest : List (CRTT.BudgetedPruning.Job S T)) : State S T :=
  match first (fun k => containsCore k.constraints rho) s.library with
  | none => {s with stage := .probe}
  | some _ => {s with frontier := {s.frontier with jobs := rest}, stage := .lookup}

/-- A failed probe discharges its obligation before compilation. The next
paid transition may minimize the raw core and add it to the active library. -/
def probeStep (s : State S T) (rho : PartialAssign sp tp)
    (rest : List (CRTT.BudgetedPruning.Job S T)) : State S T :=
  match findCore S T rho with
  | none => {s with stage := .advance}
  | some k => {s with frontier := {s.frontier with jobs := rest}, pending := some k, stage := .lookup}

def learnStep (s : State S T) (raw : ObstructionCore S T) : State S T :=
  let reduced := extract S T raw.world raw.constraints raw.emptyRow
  let k := toCore S T reduced
  {s with library := insertCore S T k s.library,
          history := ⟨raw, reduced⟩ :: s.history, pending := none, stage := .lookup}

def baseStep (base : RuleLibrary S T) (fees : Fees) (s : State S T)
    (j : CRTT.BudgetedPruning.Job S T) (rest : List (CRTT.BudgetedPruning.Job S T)) : State S T :=
  {s with frontier := CRTT.BudgetedPruning.advance S T base fees.base s.frontier j rest,
          stage := .lookup}

def charged (s : State S T) (fee : Nat) (pos : 0 < fee)
    (next : Unit → State S T) : QuotedStep (State S T) :=
  ⟨fee, pos, fun _ => {next () with feesPaid := fee :: s.feesPaid}⟩

def baseQuote (base : RuleLibrary S T) (fees : Fees) (s : State S T)
    (j : CRTT.BudgetedPruning.Job S T) (rest : List (CRTT.BudgetedPruning.Job S T)) : QuotedStep (State S T) :=
  charged S T s (CRTT.BudgetedPruning.bill S T fees.base j).fee
    (CRTT.BudgetedPruning.bill_positive S T fees.base j) (fun _ => baseStep S T base fees s j rest)

def quote (base : RuleLibrary S T) (fees : Fees) (s : State S T) : Option (QuotedStep (State S T)) :=
  match s.pending with
  | some raw => some (charged S T s (fees.compile+1) (by omega) (fun _ => learnStep S T s raw))
  | none => match s.frontier.jobs with
    | [] => none
    | j :: rest =>
      match j with
      | .ports _ rho [] =>
        match s.stage with
        | .lookup => some (charged S T s (lookupFee S T fees s) (by unfold lookupFee; omega)
            (fun _ => lookupStep S T s rho rest))
        | .probe => some (charged S T s (fees.probe+1) (by omega) (fun _ => probeStep S T s rho rest))
        | .advance => some (baseQuote S T base fees s j rest)
      | _ => some (baseQuote S T base fees s j rest)

/-- Dropping a failed region preserves reference coverage. -/
theorem drop_correct (s : State S T) (qs : List (Fin sp)) (rho : PartialAssign sp tp)
    (rest : List (CRTT.BudgetedPruning.Job S T))
    (hj : s.frontier.jobs = .ports qs rho [] :: rest)
    (hs : CRTT.BudgetedPruning.Correct S T s.frontier)
    (hk : ¬ ∃ M : Morphism S T, Extends S T M rho) :
    CRTT.BudgetedPruning.Correct S T {s.frontier with jobs := rest} := by
  refine ⟨hs.1, ?_⟩
  intro N hn
  rcases hs.2 N hn with hm | ⟨j, hmem, hcov⟩
  · exact Or.inl hm
  · rw [hj] at hmem
    rcases List.mem_cons.mp hmem with he | ht
    · subst j
      exact False.elim (hk ⟨N, hcov.1⟩)
    · exact Or.inr ⟨j, ht, hcov⟩

theorem probe_correct (s : State S T) (qs : List (Fin sp)) (rho : PartialAssign sp tp)
    (rest : List (CRTT.BudgetedPruning.Job S T))
    (hj : s.frontier.jobs = .ports qs rho [] :: rest)
    (hs : CRTT.BudgetedPruning.Correct S T s.frontier) :
    CRTT.BudgetedPruning.Correct S T (probeStep S T s rho rest).frontier := by
  cases hk : findCore S T rho with
  | none => simpa [probeStep, hk] using hs
  | some k =>
    have he := findCore_constraints S T rho k hk
    have hsub : Sub k.constraints rho := by
      intro e hm
      rw [he] at hm
      exact hm
    have hx := drop_correct S T s qs rho rest hj hs (core_excludes S T k rho hsub)
    simpa [probeStep, hk] using hx

theorem lookup_correct (s : State S T) (qs : List (Fin sp)) (rho : PartialAssign sp tp)
    (rest : List (CRTT.BudgetedPruning.Job S T))
    (hj : s.frontier.jobs = .ports qs rho [] :: rest)
    (hs : CRTT.BudgetedPruning.Correct S T s.frontier) :
    CRTT.BudgetedPruning.Correct S T (lookupStep S T s rho rest).frontier := by
  cases hk : first (fun k : ObstructionCore S T => containsCore k.constraints rho) s.library with
  | none => simpa [lookupStep, hk] using hs
  | some k =>
    have hm := first_sound (fun k : ObstructionCore S T => containsCore k.constraints rho) s.library k hk
    have hsub := (containsCore_iff k.constraints rho).mp hm.2
    have hx := drop_correct S T s qs rho rest hj hs (core_excludes S T k rho hsub)
    simpa [lookupStep, hk] using hx

theorem base_correct (base : RuleLibrary S T) (fees : Fees) (s : State S T)
    (j : CRTT.BudgetedPruning.Job S T) (rest : List (CRTT.BudgetedPruning.Job S T))
    (hj : s.frontier.jobs = j :: rest) (hs : CRTT.BudgetedPruning.Correct S T s.frontier) :
    CRTT.BudgetedPruning.Correct S T (baseStep S T base fees s j rest).frontier := by
  let q : QuotedStep (CRTT.BudgetedPruning.Frontier S T) :=
    ⟨(CRTT.BudgetedPruning.bill S T fees.base j).fee,
      CRTT.BudgetedPruning.bill_positive S T fees.base j,
      fun _ => CRTT.BudgetedPruning.advance S T base fees.base s.frontier j rest⟩
  have hq : CRTT.BudgetedPruning.quote S T base fees.base s.frontier = some q := by
    unfold CRTT.BudgetedPruning.quote
    rw [hj]
  exact CRTT.BudgetedPruning.quote_correct S T base fees.base s.frontier q hs hq

/-- Changing the library cannot invalidate the existing coverage proof. -/
theorem quote_correct (base : RuleLibrary S T) (fees : Fees) (s : State S T)
    (q : QuotedStep (State S T)) (hs : CRTT.BudgetedPruning.Correct S T s.frontier)
    (hq : quote S T base fees s = some q) :
    CRTT.BudgetedPruning.Correct S T (q.next ()).frontier := by
  cases hp : s.pending with
  | some raw =>
    simp [quote, hp] at hq
    rw [← hq]
    exact hs
  | none =>
    cases hj : s.frontier.jobs with
    | nil => simp [quote, hp, hj] at hq
    | cons j rest =>
      cases j with
      | actions p acts =>
        simp [quote, hp, hj] at hq
        rw [← hq]
        exact base_correct S T base fees s (.actions p acts) rest hj hs
      | ports qs rho rs =>
        cases rs with
        | cons r rs =>
          simp [quote, hp, hj] at hq
          rw [← hq]
          exact base_correct S T base fees s (.ports qs rho (r :: rs)) rest hj hs
        | nil =>
          cases hr : s.stage with
          | lookup =>
            simp [quote, hp, hj, hr] at hq
            rw [← hq]
            exact lookup_correct S T s qs rho rest hj hs
          | probe =>
            simp [quote, hp, hj, hr] at hq
            rw [← hq]
            exact probe_correct S T s qs rho rest hj hs
          | advance =>
            simp [quote, hp, hj, hr] at hq
            rw [← hq]
            exact base_correct S T base fees s (.ports qs rho []) rest hj hs

def feeSum : List Nat → Nat
  | [] => 0
  | c :: cs => c + feeSum cs

/-- Exact meter for the new operations, not a free diagnostic side channel. -/
theorem quote_meter (base : RuleLibrary S T) (fees : Fees) (s : State S T)
    (q : QuotedStep (State S T)) (hq : quote S T base fees s = some q) :
    feeSum (q.next ()).feesPaid = feeSum s.feesPaid + q.fee := by
  cases hp : s.pending with
  | some raw =>
    simp [quote, hp] at hq
    rw [← hq]
    exact Nat.add_comm _ _
  | none =>
    cases hj : s.frontier.jobs with
    | nil => simp [quote, hp, hj] at hq
    | cons j rest =>
      cases j with
      | actions p acts =>
        simp [quote, hp, hj] at hq
        rw [← hq]
        exact Nat.add_comm _ _
      | ports qs rho rs =>
        cases rs with
        | cons r rs =>
          simp [quote, hp, hj] at hq
          rw [← hq]
          exact Nat.add_comm _ _
        | nil =>
          cases hr : s.stage <;> simp [quote, hp, hj, hr] at hq <;>
            rw [← hq] <;> exact Nat.add_comm _ _

theorem execute_trace (base : RuleLibrary S T) (fees : Fees) (s : Account (State S T)) :
    (execute (quote S T base fees) s).spent + feeSum s.state.feesPaid =
      s.spent + feeSum (execute (quote S T base fees) s).state.feesPaid :=
  CRTT.BudgetedPruning.run_meter (quote S T base fees) (fun u => feeSum u.feesPaid)
    (quote_meter S T base fees) s.remaining s

theorem execute_correct (base : RuleLibrary S T) (fees : Fees) (s : Account (State S T))
    (hs : CRTT.BudgetedPruning.Correct S T s.state.frontier) :
    CRTT.BudgetedPruning.Correct S T (execute (quote S T base fees) s).state.frontier :=
  invariant (quote S T base fees) (fun u => CRTT.BudgetedPruning.Correct S T u.frontier)
    (quote_correct S T base fees) s.remaining s hs

theorem execute_split (base : RuleLibrary S T) (fees : Fees) (s : Account (State S T)) (b1 b2 : Nat) :
    execute (quote S T base fees) (topUp s (b1+b2)) =
      execute (quote S T base fees) (topUp (execute (quote S T base fees) (topUp s b1)) b2) :=
  CRTT.ResumeLaws.execute_topUp_add (quote S T base fees) s b1 b2

theorem execute_exhausted_iff (base : RuleLibrary S T) (fees : Fees) (s : Account (State S T))
    (hs : CRTT.BudgetedPruning.Correct S T s.state.frontier)
    (he : (execute (quote S T base fees) s).state.frontier.jobs = []) (N : Morphism S T) :
    N ∈ (execute (quote S T base fees) s).state.frontier.certificates ↔ N ∈ discoverAll S T :=
  CRTT.BudgetedPruning.exhausted_iff S T _ (execute_correct S T base fees s hs) he N

structure CertifiedAccount where
  account : Account (State S T)
  correct : CRTT.BudgetedPruning.Correct S T account.state.frontier

def start (base : RuleLibrary S T) (budget : Nat) : CertifiedAccount S T :=
  ⟨⟨initial S T base, budget, 0⟩, CRTT.BudgetedPruning.initial_correct S T base⟩

def resume (base : RuleLibrary S T) (fees : Fees) (s : CertifiedAccount S T) (extra : Nat) : CertifiedAccount S T :=
  ⟨execute (quote S T base fees) (topUp s.account extra), execute_correct S T base fees (topUp s.account extra) s.correct⟩

/-- Answer exhaustion is distinct from controller quiescence: compilation of a
last failed region may remain pending after the search itself is complete. -/
def verdict (s : CertifiedAccount S T) : CRTT.BudgetedPruning.Outcome S T :=
  match hc : s.account.state.frontier.certificates with
  | m :: _ => .found m
  | [] => match he : s.account.state.frontier.jobs with
    | [] => .impossible (CRTT.BudgetedPruning.exhausted_impossible S T
        s.account.state.frontier s.correct he hc)
    | _ :: _ => .inconclusive

def classify (s : CertifiedAccount S T) : CRTT.BudgetedPruning.Outcome S T × CertifiedAccount S T :=
  (verdict S T s, s)

#print axioms verdict
#print axioms classify
#print axioms sub_trans
#print axioms insertCore_rejects
#print axioms library_sound
#print axioms findCore_constraints
#print axioms drop_correct
#print axioms probe_correct
#print axioms lookup_correct
#print axioms base_correct
#print axioms quote_correct
#print axioms quote_meter
#print axioms execute_trace
#print axioms execute_correct
#print axioms execute_split
#print axioms execute_exhausted_iff
end CRTT.LearningDiscovery
