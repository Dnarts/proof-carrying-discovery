import InvestigationTransfer

/-!
CRTT T21: finite, explicitly supplied certified investigation offers.
The selection oracle over all transfers is NOT implemented: T22 is responsible
for discovering and pricing morphisms. All prices here are declared Nat costs,
not measurements of Lean computation. T19 and T20 are imported unchanged.
-/
namespace CRTT.InvestigationLibrary

open CRTT.AdaptiveObservation CRTT.InvestigationTransfer
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

/-- Package heterogeneous carrier types, retaining the actual port decision procedure. -/
structure ResearchTask where
  World : Type
  Port : Type
  Action : Type
  spec : TaskSpec World Port Action
  portEq : DecidableEq Port

abbrev Tree (S : ResearchTask) := Investigation S.Port S.Action

def taskLegal (S : ResearchTask) (t : Tree S) : Prop :=
  letI : DecidableEq S.Port := S.portEq
  legal S.spec t

def taskCost (S : ResearchTask) (t : Tree S) : Nat := cost S.spec t

def taskOptimum (S : ResearchTask) : Nat :=
  letI : DecidableEq S.Port := S.portEq
  optimum S.spec

def taskOptimizer (S : ResearchTask) : Tree S :=
  letI : DecidableEq S.Port := S.portEq
  optimalTree S.spec

theorem task_optimizer_legal (S : ResearchTask) : taskLegal S (taskOptimizer S) := by
  letI : DecidableEq S.Port := S.portEq
  exact solve_legal S.spec.problem S.spec.depth S.spec.worlds S.spec.ports

theorem task_optimizer_cost (S : ResearchTask) :
    taskCost S (taskOptimizer S) = taskOptimum S := rfl

theorem task_optimum_le (S : ResearchTask) (t : Tree S) (ht : taskLegal S t) :
    taskOptimum S ≤ taskCost S t := by
  letI : DecidableEq S.Port := S.portEq
  exact solve_optimal S.spec.problem S.spec.depth S.spec.worlds S.spec.ports t ht

/-- Separate hard limits from the soft total-cost objective. -/
def HardContract (S : ResearchTask) (t : Tree S) (budget eps : Nat) : Prop :=
  ∀ w ∈ S.spec.worlds, observationCost S.spec.problem w t ≤ budget ∧
    terminalLoss S.spec.problem w t ≤ eps

/-- Edge charges are incurred by this route. Shared enumeration, indexing and
ranking fees are accounted for separately, never charged only to the winner. -/
structure EdgeExpense where
  access : Nat
  verify : Nat
  translate : Nat

def EdgeExpense.total (e : EdgeExpense) : Nat := e.access + e.verify + e.translate

/-- A route through heterogeneous tasks, with an explicit cost on every edge.
A direct reuse can be represented by a single identity edge, with its actual fee. -/
inductive TransferPath (S : ResearchTask) : ResearchTask → Type 1 where
  | single {T : ResearchTask} (m : TransferMorphism S.spec T.spec) (e : EdgeExpense) :
      TransferPath S T
  | step {T U : ResearchTask} (prior : TransferPath S T)
      (m : TransferMorphism T.spec U.spec) (e : EdgeExpense) : TransferPath S U

variable {S T U : ResearchTask}

/-!
The endpoint is an INDEX of TransferPath, not a fixed recursion parameter.
Put it in the recursive telescope of each definition. The equation compiler
then generalizes the endpoint when recursing on the prior path. Require
structural recursion rather than a well-founded fallback: constructor
computation is tested by rfl below. Keep executable definitions (not
noncomputable eliminators or opaque theorems).
-/

def pathOverhead {S : ResearchTask} : {T : ResearchTask} →
    (p : TransferPath S T) → Nat
  | _, .single _ e => e.total
  | _, .step prior _ e => pathOverhead prior + e.total
termination_by structural _ p => p

def collapse {S : ResearchTask} : {T : ResearchTask} →
    (p : TransferPath S T) → TransferMorphism S.spec T.spec
  | _, .single m _ => m
  | _, .step prior m _ => compose (collapse prior) m
termination_by structural _ p => p

/-- Operational route semantics distinct from the collapsed certificate. -/
def executePath {S : ResearchTask} (t : Tree S) : {T : ResearchTask} →
    (p : TransferPath S T) → Tree T
  | _, .single m _ => transfer m t
  | _, .step prior m _ => transfer m (executePath t prior)
termination_by structural _ p => p

/-- Concatenate paths without pretending that collapse also accounts for fees.
The second path has its own varying destination index. -/
def appendPath {S T : ResearchTask} (p : TransferPath S T) : {U : ResearchTask} →
    (q : TransferPath T U) → TransferPath S U
  | _, .single m e => .step p m e
  | _, .step prior m e => .step (appendPath p prior) m e
termination_by structural _ q => q

/-! Constructor computation regressions. These are intentionally proved by rfl:
using only propositional rewrite rules would not certify kernel reduction. -/

theorem overhead_single (m : TransferMorphism S.spec T.spec) (e : EdgeExpense) :
    pathOverhead (TransferPath.single (S := S) (T := T) m e) = e.total := rfl

theorem overhead_step (p : TransferPath S T) (m : TransferMorphism T.spec U.spec)
    (e : EdgeExpense) : pathOverhead (TransferPath.step (U := U) p m e) = pathOverhead p + e.total := rfl

theorem collapse_single (m : TransferMorphism S.spec T.spec) (e : EdgeExpense) :
    collapse (TransferPath.single (S := S) (T := T) m e) = m := rfl

theorem collapse_step (p : TransferPath S T) (m : TransferMorphism T.spec U.spec)
    (e : EdgeExpense) : collapse (TransferPath.step (U := U) p m e) = compose (collapse p) m := rfl

theorem execute_single (t : Tree S) (m : TransferMorphism S.spec T.spec) (e : EdgeExpense) :
    executePath t (TransferPath.single (S := S) (T := T) m e) = transfer m t := rfl

theorem execute_step (t : Tree S) (p : TransferPath S T)
    (m : TransferMorphism T.spec U.spec) (e : EdgeExpense) :
    executePath t (TransferPath.step (U := U) p m e) = transfer m (executePath t p) := rfl

theorem append_single (p : TransferPath S T) (m : TransferMorphism T.spec U.spec)
    (e : EdgeExpense) : appendPath p (TransferPath.single (S := T) (T := U) m e) = .step p m e := rfl

theorem append_step {V : ResearchTask} (p : TransferPath S T) (q : TransferPath T U)
    (m : TransferMorphism U.spec V.spec) (e : EdgeExpense) :
    appendPath p (TransferPath.step (U := V) q m e) = .step (appendPath p q) m e := rfl

theorem collapse_exec (p : TransferPath S T) (t : Tree S) :
    transfer (collapse p) t = executePath t p := by
  induction p with
  | single m e => rfl
  | step prior m e ih =>
    change transfer (compose (collapse prior) m) t = transfer m (executePath t prior)
    rw [transfer_compose (collapse prior) m t, ih]

theorem append_overhead (p : TransferPath S T) (q : TransferPath T U) :
    pathOverhead (appendPath p q) = pathOverhead p + pathOverhead q := by
  induction q with
  | single m e => rfl
  | step prior m e ih =>
    change pathOverhead (appendPath p prior) + e.total =
      pathOverhead p + (pathOverhead prior + e.total)
    rw [ih, Nat.add_assoc]

theorem append_execution (p : TransferPath S T) (q : TransferPath T U) (t : Tree S) :
    executePath t (appendPath p q) = executePath (executePath t p) q := by
  induction q with
  | single m e => rfl
  | step prior m e ih =>
    change transfer m (executePath t (appendPath p prior)) =
      transfer m (executePath (executePath t p) prior)
    rw [ih]

theorem path_legal (p : TransferPath S T) (t : Tree S) (ht : taskLegal S t) :
    taskLegal T (executePath t p) := by
  letI : DecidableEq S.Port := S.portEq
  letI : DecidableEq T.Port := T.portEq
  rw [← collapse_exec p t]
  exact transfer_legal (collapse p) t ht

theorem path_cost_le (p : TransferPath S T) (t : Tree S) (ht : taskLegal S t) :
    taskCost T (executePath t p) ≤ taskCost S t := by
  letI : DecidableEq S.Port := S.portEq
  rw [← collapse_exec p t]
  exact transfer_worst_le (collapse p) t ht

theorem path_hard_contract (p : TransferPath S T) (t : Tree S) (ht : taskLegal S t)
    (budget eps : Nat) (hc : HardContract S t budget eps) :
    taskLegal T (executePath t p) ∧ HardContract T (executePath t p) budget eps := by
  letI : DecidableEq S.Port := S.portEq
  letI : DecidableEq T.Port := T.portEq
  rw [← collapse_exec p t]
  exact transfer_hard_contract (collapse p) t ht budget eps hc

/-- A library item need not be optimal, but it has an actual legal tree and
actual proofs of its declared source budget and tolerance. Provenance text
is an identifier, not a proof of authenticity. -/
structure LibraryEntry where
  provenance : String
  source : ResearchTask
  tree : Tree source
  legalTree : taskLegal source tree
  budget : Nat
  tolerance : Nat
  hardProof : HardContract source tree budget tolerance

abbrev Library := List LibraryEntry

/-- Only already discovered, certified paths can enter this list of offers. -/
structure TransferCandidate (target : ResearchTask) where
  entry : LibraryEntry
  route : TransferPath entry.source target

def TransferCandidate.tree (c : TransferCandidate T) : Tree T :=
  executePath c.entry.tree c.route

def TransferCandidate.overhead (c : TransferCandidate T) : Nat := pathOverhead c.route

def TransferCandidate.execution (c : TransferCandidate T) : Nat := taskCost T c.tree

def TransferCandidate.total (c : TransferCandidate T) : Nat := c.overhead + c.execution

theorem candidate_legal (c : TransferCandidate T) : taskLegal T c.tree :=
  path_legal c.route c.entry.tree c.entry.legalTree

theorem candidate_hard_contract (c : TransferCandidate T) :
    HardContract T c.tree c.entry.budget c.entry.tolerance :=
  (path_hard_contract c.route c.entry.tree c.entry.legalTree _ _ c.entry.hardProof).2

theorem candidate_optimum_le (c : TransferCandidate T) : taskOptimum T ≤ c.execution :=
  task_optimum_le T c.tree (candidate_legal c)

/-- T21.1: additive price comparison. The subtraction appears only in a
consequence and is legitimate because the transferred tree is legal. -/
theorem residual_comparison (H E D V : Nat) (hv : V ≤ E) :
    H + E < D + V ↔ H + (E - V) < D := by
  have haccount : E - V + V = E := Nat.sub_add_cancel hv
  constructor
  · intro h
    omega
  · intro h
    omega

theorem paid_candidate_iff (c : TransferCandidate T) (discovery : Nat) :
    c.total < discovery + taskOptimum T ↔
      c.overhead + (c.execution - taskOptimum T) < discovery :=
  residual_comparison c.overhead c.execution discovery (taskOptimum T) (candidate_optimum_le c)

/-- Mutual simulation forces a transported source optimizer to have target
optimal execution cost, so only route fees remain to compare. -/
theorem mutual_path_execution (p : TransferPath S T) (q : TransferPath T S)
    (t : Tree S) (ht : taskLegal S t) (hopt : taskCost S t = taskOptimum S) :
    taskCost T (executePath t p) = taskOptimum T := by
  letI : DecidableEq S.Port := S.portEq
  letI : DecidableEq T.Port := T.portEq
  apply Nat.le_antisymm
  · calc
      taskCost T (executePath t p) ≤ taskCost S t := path_cost_le p t ht
      _ = taskOptimum S := hopt
      _ = taskOptimum T := mutual_optimum_eq (collapse q) (collapse p)
  · exact task_optimum_le T _ (path_legal p t ht)

theorem mutual_paths_compare (p p' : TransferPath S T) (q : TransferPath T S)
    (t : Tree S) (ht : taskLegal S t) (hopt : taskCost S t = taskOptimum S) :
    pathOverhead p + taskCost T (executePath t p) ≤
      pathOverhead p' + taskCost T (executePath t p') ↔ pathOverhead p ≤ pathOverhead p' := by
  rw [mutual_path_execution p q t ht hopt, mutual_path_execution p' q t ht hopt]
  constructor
  · intro h
    omega
  · intro h
    exact Nat.add_le_add_right h _

/-! T21.4--6: explicit finite offers and optional paid search. -/

/-- `none` denotes the quoted fresh solution, not abstention. The quote must be
supplied by the caller; the selector does not solve the fresh task to get it. -/
def score (freshQuote : Nat) : Option (TransferCandidate T) → Nat
  | none => freshQuote
  | some c => c.total

def choose (freshQuote : Nat) (cs : List (TransferCandidate T)) : Option (TransferCandidate T) :=
  pick (score freshQuote) none (cs.map some)

def best (freshQuote : Nat) (cs : List (TransferCandidate T)) : Nat :=
  score freshQuote (choose freshQuote cs)

/-- Reference evaluator. Computing this comparator may itself require full
T19 synthesis; it is not a claim of a cheaper deployment algorithm. -/
def chooseAgainstOptimum (T : ResearchTask) (discovery : Nat)
    (cs : List (TransferCandidate T)) : Option (TransferCandidate T) :=
  choose (discovery + taskOptimum T) cs

theorem choose_mem (freshQuote : Nat) (cs : List (TransferCandidate T)) :
    choose freshQuote cs ∈ none :: cs.map some :=
  pick_mem (score (T := T) freshQuote) (none : Option (TransferCandidate T)) (cs.map some)

theorem chosen_from_list (freshQuote : Nat) (cs : List (TransferCandidate T))
    (c : TransferCandidate T) (hc : choose freshQuote cs = some c) : c ∈ cs := by
  have hm := choose_mem freshQuote cs
  rw [hc] at hm
  rcases List.mem_cons.mp hm with he | ht
  · cases he
  · obtain ⟨b, hb, he⟩ := List.mem_map.mp ht
    have hbc : b = c := Option.some.inj he
    rw [← hbc]
    exact hb

theorem best_le_fresh (freshQuote : Nat) (cs : List (TransferCandidate T)) :
    best freshQuote cs ≤ freshQuote :=
  pick_le (score freshQuote) none (cs.map some) none (List.Mem.head _)

theorem best_le_candidate (freshQuote : Nat) (cs : List (TransferCandidate T))
    (c : TransferCandidate T) (hc : c ∈ cs) : best freshQuote cs ≤ c.total := by
  have hm : some c ∈ none :: cs.map some :=
    List.mem_cons.mpr (Or.inr (List.mem_map.mpr ⟨c, hc, rfl⟩))
  exact pick_le (score freshQuote) none (cs.map some) (some c) hm

/-- The explicit optimum is attained by a returned option. -/
theorem best_attained (freshQuote : Nat) (cs : List (TransferCandidate T)) :
    best freshQuote cs = freshQuote ∨
    ∃ c ∈ cs, best freshQuote cs = c.total := by
  cases he : choose freshQuote cs with
  | none => exact Or.inl (by simp [best, he, score])
  | some c =>
    exact Or.inr ⟨c, chosen_from_list freshQuote cs c he, by simp [best, he, score]⟩

/-- Candidate membership in the library is a proof obligation; a route is not
assumed to be found merely because its source entry is available. -/
def Listed (L : Library) (cs : List (TransferCandidate T)) : Prop :=
  ∀ c ∈ cs, c.entry ∈ L

theorem chosen_from_library (L : Library) (freshQuote : Nat)
    (cs : List (TransferCandidate T)) (hl : Listed L cs)
    (c : TransferCandidate T) (hc : choose freshQuote cs = some c) : c.entry ∈ L :=
  hl c (chosen_from_list freshQuote cs c hc)

theorem listed_monotone (L L' : Library) (cs : List (TransferCandidate T))
    (hsub : ∀ e ∈ L, e ∈ L') (hl : Listed L cs) : Listed L' cs := by
  intro c hc
  exact hsub c.entry (hl c hc)

/-- A selector for a common hard contract must receive only eligible offers.
The fresh alternative must separately have a witness for that same contract. -/
theorem chosen_hard_contract (freshQuote : Nat) (cs : List (TransferCandidate T))
    (budget eps : Nat) (h : ∀ c ∈ cs, HardContract T c.tree budget eps)
    (c : TransferCandidate T) (hc : choose freshQuote cs = some c) :
    taskLegal T c.tree ∧ HardContract T c.tree budget eps :=
  ⟨candidate_legal c, h c (chosen_from_list freshQuote cs c hc)⟩

/-- Ideal library/list extension preserves every old offer and its costs. -/
theorem best_monotone (freshQuote : Nat) (old new : List (TransferCandidate T))
    (hsub : ∀ c ∈ old, c ∈ new) : best freshQuote new ≤ best freshQuote old := by
  rcases best_attained freshQuote old with hf | ⟨c, hc, he⟩
  · rw [hf]
    exact best_le_fresh freshQuote new
  · rw [he]
    exact best_le_candidate freshQuote new c (hsub c hc)

/-- Search and all rejected-candidate evaluation are charged separately.
The decision after search may be fresh even if search was globally wasteful. -/
def afterSearch (searchFee freshQuote : Nat) (cs : List (TransferCandidate T)) : Nat :=
  searchFee + best freshQuote cs

theorem search_profitable_iff (searchFee freshQuote : Nat) (cs : List (TransferCandidate T)) :
    afterSearch searchFee freshQuote cs < freshQuote ↔
      ∃ c ∈ cs, searchFee + c.total < freshQuote := by
  constructor
  · intro h
    rcases best_attained freshQuote cs with hf | ⟨c, hc, he⟩
    · have hh : searchFee + freshQuote < freshQuote := by
        simpa only [afterSearch, hf] using h
      have bad : False := by omega
      exact False.elim bad
    · exact ⟨c, hc, by simpa only [afterSearch, he] using h⟩
  · rintro ⟨c, hc, h⟩
    exact Nat.lt_of_le_of_lt (Nat.add_le_add_left (best_le_candidate freshQuote cs c hc) searchFee) h

/-! T21.8: the semantic oracle is a specification, not a search implementation. -/

/-- The issued-offer predicate fixes the admissible certificates AND their
quoted tariffs. In a hard-contract run it also restricts the service class.
Quantifying over arbitrary freely priced paths would give a meaningless oracle. -/
def Admitted (L : Library) (issued : TransferCandidate T → Prop)
    (c : TransferCandidate T) : Prop := c.entry ∈ L ∧ issued c

def AdmittedList (L : Library) (issued : TransferCandidate T → Prop)
    (cs : List (TransferCandidate T)) : Prop := ∀ c ∈ cs, Admitted L issued c

/-- An attaining oracle witness over authorized, priced offers from the library.
Fresh is always an alternative. This is a proposition, not a computable argmin
on an unenumerated space of functions, proofs and arbitrarily long paths. -/
structure OracleOptimal (L : Library) (issued : TransferCandidate T → Prop)
    (freshQuote : Nat) (o : Option (TransferCandidate T)) : Prop where
  admitted : ∀ c, o = some c → Admitted L issued c
  leFresh : score freshQuote o ≤ freshQuote
  leCandidate : ∀ c : TransferCandidate T, Admitted L issued c → score freshQuote o ≤ c.total

theorem oracle_le_realized (L : Library) (issued : TransferCandidate T → Prop)
    (freshQuote : Nat) (cs : List (TransferCandidate T)) (hl : AdmittedList L issued cs)
    (o : Option (TransferCandidate T)) (ho : OracleOptimal L issued freshQuote o) :
    score freshQuote o ≤ best freshQuote cs := by
  rcases best_attained freshQuote cs with hf | ⟨c, hc, he⟩
  · rw [hf]
    exact ho.leFresh
  · rw [he]
    exact ho.leCandidate c (hl c hc)

/-- A finite enumeration is cost-complete if it contains an offer no worse than
each admissible candidate. Enumeration of all proof terms is not necessary. -/
def CostComplete (L : Library) (issued : TransferCandidate T → Prop)
    (cs : List (TransferCandidate T)) : Prop :=
  ∀ c : TransferCandidate T, Admitted L issued c → ∃ b ∈ cs, b.total ≤ c.total

theorem complete_search_matches_oracle (L : Library) (issued : TransferCandidate T → Prop)
    (freshQuote : Nat) (cs : List (TransferCandidate T)) (hl : AdmittedList L issued cs)
    (hc : CostComplete L issued cs) (o : Option (TransferCandidate T))
    (ho : OracleOptimal L issued freshQuote o) :
    best freshQuote cs = score freshQuote o := by
  apply Nat.le_antisymm
  · cases o with
    | none => exact best_le_fresh freshQuote cs
    | some c =>
      obtain ⟨b, hb, hbc⟩ := hc c (ho.admitted c rfl)
      exact Nat.le_trans (best_le_candidate freshQuote cs b hb) hbc
  · exact oracle_le_realized L issued freshQuote cs hl o ho

/-- With an explicit exhaustive finite registry an attaining oracle can be
constructed, without any abstract choice or enumeration of functions. -/
theorem enumerated_oracle (L : Library) (freshQuote : Nat)
    (registry : List (TransferCandidate T)) (hl : Listed L registry) :
    OracleOptimal L (fun c => c ∈ registry) freshQuote (choose freshQuote registry) := by
  constructor
  · intro c he
    have hm := chosen_from_list freshQuote registry c he
    exact ⟨hl c hm, hm⟩
  · exact best_le_fresh freshQuote registry
  · intro c hc
    exact best_le_candidate freshQuote registry c hc.2

/-- Exact accounting for incompleteness of the candidate search; extra search
fees are not identified with the optimality gap. -/
theorem search_gap_accounting (L : Library) (issued : TransferCandidate T → Prop)
    (freshQuote : Nat) (cs : List (TransferCandidate T)) (hl : AdmittedList L issued cs)
    (o : Option (TransferCandidate T)) (ho : OracleOptimal L issued freshQuote o) :
    (best freshQuote cs - score freshQuote o) + score freshQuote o = best freshQuote cs :=
  Nat.sub_add_cancel (oracle_le_realized L issued freshQuote cs hl o ho)

/-! T21.7: one-time acquisition versus a fixed, feasible sequence of uses. -/

structure UseCost where
  discovery : Nat
  optimum : Nat
  overhead : Nat
  execution : Nat
  optimum_le : optimum ≤ execution

def UseCost.fresh (u : UseCost) : Nat := u.discovery + u.optimum

def UseCost.reuse (u : UseCost) : Nat := u.overhead + u.execution

def UseCost.excess (u : UseCost) : Nat := u.execution - u.optimum

def UseCost.burden (u : UseCost) : Nat := u.overhead + u.excess

/-- `sharedFee` includes all charged candidate-search/ranking work for this use.
A fresh quote is D+V. This is accounting for a fixed feasible plan, not an
algorithm for choosing which future methods to acquire. -/
def useFromCandidate (c : TransferCandidate T) (discovery sharedFee : Nat) : UseCost where
  discovery := discovery
  optimum := taskOptimum T
  overhead := sharedFee + c.overhead
  execution := c.execution
  optimum_le := candidate_optimum_le c

theorem use_accounting (u : UseCost) :
    u.reuse + u.discovery = u.fresh + u.burden := by
  have h := Nat.sub_add_cancel u.optimum_le
  unfold UseCost.reuse UseCost.fresh UseCost.burden UseCost.excess
  omega

def sumFresh : List UseCost → Nat
  | [] => 0
  | u :: us => u.fresh + sumFresh us

def sumReuse : List UseCost → Nat
  | [] => 0
  | u :: us => u.reuse + sumReuse us

def sumDiscovery : List UseCost → Nat
  | [] => 0
  | u :: us => u.discovery + sumDiscovery us

def sumBurden : List UseCost → Nat
  | [] => 0
  | u :: us => u.burden + sumBurden us

theorem stream_accounting (us : List UseCost) :
    sumReuse us + sumDiscovery us = sumFresh us + sumBurden us := by
  induction us with
  | nil => rfl
  | cons u us ih =>
    have hu := use_accounting u
    simp only [sumReuse, sumDiscovery, sumFresh, sumBurden]
    omega

/-- The optional one-time investment is paid once, not at each later use.
If already sunk, set it to zero. All tasks in the comparison must be served.
Any extra maintenance, verification or search is included in the declared fees. -/
theorem amortization_iff (setup : Nat) (us : List UseCost) :
    setup + sumReuse us < sumFresh us ↔ setup + sumBurden us < sumDiscovery us := by
  have h := stream_accounting us
  constructor
  · intro hlt
    omega
  · intro hlt
    omega

/-! Concrete certified witnesses. The numbers are derived by running the
actual imported T19/T20 semantics on the declared tasks and paths. -/
namespace Witnesses

def source : ResearchTask where
  World := Unit
  Port := Unit
  Action := Bool
  spec :=
    { problem := { defaultAction := false, otherActions := [true], read := fun _ _ => false,
                   price := fun _ => 0, loss := fun _ _ => 2 },
      worlds := [()], ports := [], depth := 0 }
  portEq := inferInstance

def targetLoss (a : Bool) : Nat := if a then 0 else 2

def target : ResearchTask where
  World := Unit
  Port := Unit
  Action := Bool
  spec :=
    { problem := { defaultAction := false, otherActions := [true], read := fun _ _ => false,
                   price := fun _ => 0, loss := fun a _ => targetLoss a },
      worlds := [()], ports := [], depth := 0 }
  portEq := inferInstance

def routeMorphism (f : Bool → Bool) (hf : ∀ a, targetLoss (f a) ≤ 2) :
    TransferMorphism source.spec target.spec where
  worldMap := id
  portMap := id
  actionMap := f
  world_mem := fun _ h => h
  port_mem := fun _ h => h
  action_mem := by
    intro a _ha
    change f a ∈ [false, true]
    cases f a <;> decide
  port_injective := fun _ _ _ _ h => h
  read_eq := fun _ _ _ _ => rfl
  price_le := fun _ _ => Nat.le_refl _
  loss_le := by
    intro a _ha _w _hw
    exact hf a
  depth_le := Nat.le_refl _

def cheapPath : TransferPath source target :=
  .single (routeMorphism id (by intro a; cases a <;> decide)) ⟨0, 0, 0⟩

def betterPath : TransferPath source target :=
  .single (routeMorphism (fun _ => true) (by intro _a; decide)) ⟨0, 0, 1⟩

def sourceTree : Tree source := .act false

theorem source_tree_legal : taskLegal source sourceTree := by
  change false ∈ [false, true]
  decide

def entry : LibraryEntry where
  provenance := "example/source/0"
  source := source
  tree := sourceTree
  legalTree := source_tree_legal
  budget := 0
  tolerance := 2
  hardProof := by
    intro _w _hw
    exact ⟨Nat.le_refl 0, Nat.le_refl 2⟩

def cheapCandidate : TransferCandidate target := ⟨entry, cheapPath⟩
def betterCandidate : TransferCandidate target := ⟨entry, betterPath⟩

/-- Both paths start from the SAME optimal source tree. A strictly smaller
route fee can nevertheless produce a larger total bill in the target. -/
theorem cheaper_path_not_cheaper_total :
    taskCost source sourceTree = taskOptimum source ∧
    pathOverhead cheapPath = 0 ∧ pathOverhead betterPath = 1 ∧
    cheapCandidate.execution = 2 ∧ betterCandidate.execution = 0 ∧
    betterCandidate.total < cheapCandidate.total := by decide

/-- Closed two-edge regression: the recursor must compute on step as well
as single. The identity edge has an actual nonzero fee. -/
def secondEdge : TransferPath target target :=
  .single (identity target.spec) ⟨2, 0, 0⟩

def twoEdgePath : TransferPath source target := appendPath betterPath secondEdge

theorem two_edge_computes :
    pathOverhead twoEdgePath = 3 ∧ taskCost target (executePath sourceTree twoEdgePath) = 0 := by
  decide

theorem selector_picks_better_total :
    best 10 [cheapCandidate, betterCandidate] = 1 ∧
    best 10 [betterCandidate] = 1 ∧ best 10 ([] : List (TransferCandidate target)) = 10 := by decide

/-- Additional historical entry, not needed for this workload. -/
def junk : LibraryEntry := { entry with provenance := "example/unused/1" }

def smallLibrary : Library := [entry]
def largeLibrary : Library := [entry, junk]

theorem same_offer_small : Listed smallLibrary [betterCandidate] := by
  intro c hc
  have he : c = betterCandidate := by simpa using hc
  subst c
  exact List.Mem.head _

theorem same_offer_large : Listed largeLibrary [betterCandidate] := by
  intro c hc
  have he : c = betterCandidate := by simpa using hc
  subst c
  exact List.Mem.head _

/-- T21.6: mandatory scan fee equals library size, even with the identical
useful offer. If unused entries are free to ignore, this model does not apply. -/
theorem library_bloat_witness :
    afterSearch smallLibrary.length 10 [betterCandidate] = 2 ∧
    afterSearch largeLibrary.length 10 [betterCandidate] = 3 := by decide

theorem small_in_large : ∀ e ∈ smallLibrary, e ∈ largeLibrary := by
  intro e he
  have he' : e = entry := by simpa [smallLibrary] using he
  subst e
  exact List.Mem.head _

theorem bloat_budget_barrier :
    afterSearch smallLibrary.length 10 [betterCandidate] ≤ 2 ∧
    ¬ (afterSearch largeLibrary.length 10 [betterCandidate] ≤ 2) := by decide

theorem empty_search_gap :
    best 10 ([] : List (TransferCandidate target)) = 10 ∧
    best 10 [betterCandidate] = 1 := by decide

end Witnesses

#print axioms task_optimizer_legal
#print axioms task_optimizer_cost
#print axioms task_optimum_le
#print axioms overhead_single
#print axioms overhead_step
#print axioms collapse_single
#print axioms collapse_step
#print axioms execute_single
#print axioms execute_step
#print axioms append_single
#print axioms append_step
#print axioms collapse_exec
#print axioms append_overhead
#print axioms append_execution
#print axioms path_legal
#print axioms path_cost_le
#print axioms path_hard_contract
#print axioms candidate_legal
#print axioms candidate_hard_contract
#print axioms candidate_optimum_le
#print axioms residual_comparison
#print axioms paid_candidate_iff
#print axioms mutual_path_execution
#print axioms mutual_paths_compare
#print axioms choose_mem
#print axioms chosen_from_list
#print axioms best_le_fresh
#print axioms best_le_candidate
#print axioms best_attained
#print axioms chosen_from_library
#print axioms listed_monotone
#print axioms chosen_hard_contract
#print axioms best_monotone
#print axioms search_profitable_iff
#print axioms oracle_le_realized
#print axioms complete_search_matches_oracle
#print axioms enumerated_oracle
#print axioms search_gap_accounting
#print axioms use_accounting
#print axioms stream_accounting
#print axioms amortization_iff
#print axioms Witnesses.source_tree_legal
#print axioms Witnesses.cheaper_path_not_cheaper_total
#print axioms Witnesses.two_edge_computes
#print axioms Witnesses.selector_picks_better_total
#print axioms Witnesses.same_offer_small
#print axioms Witnesses.same_offer_large
#print axioms Witnesses.library_bloat_witness
#print axioms Witnesses.small_in_large
#print axioms Witnesses.bloat_budget_barrier
#print axioms Witnesses.empty_search_gap

end CRTT.InvestigationLibrary
