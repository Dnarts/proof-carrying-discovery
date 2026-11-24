/-!
Observe, Change Representation, or Act:
Certified Strategy Selection under Memory, Budget, and Time Constraints (v2.6)
==============================================================================
Target Toolchain : Lean 4.36.0 (zero external imports, zero Mathlib)
Epistemic Hygiene: zero `sorryAx`, zero `native_decide` (`ofReduceBool`),
                   zero custom `axiom` declarations, zero compiler warnings.

Formalizes certified strategy selection across four distinct failure modes
(informational ambiguity, representation poverty, sensor blindness/collision,
and causal-temporal horizon closure), unifying epistemic revision,
privilege-separated representation change (`ControlledRepChange.lean`),
temporal observer autonomy (`Rule110RingDecoupling.lean`, `ContinuousSubject110.lean`),
and causal-dynamic repair reachability (`causal_dynamic_repair_v1_5_fixed.lean`):

  - Section 1 (H1)       : Unified 3-coordinate epistemic accessibility E(E) = <X_E, D_E, J_E>
                           with complete separation and inclusion theorems in a single model.
  - Section 2 (H2/Gate13): True multi-symbol FIFO Queue automaton (`QueueProgram`) vs
                           LIFO Stack automaton (`StackProgram`), proving unconditional
                           separation across arbitrary stack capacities `cap : Nat`.
  - Section 3 (H3)       : Non-postulated computable Boolean detector `checkSpuriousFin`
                           for spurious port extensions with formal soundness theorem.
  - Section 4 (H4-H7+)   : Unified Controller `LicensedStep` integrating all 6 revision
                           mechanisms (Probe, Gate 12/13 Lang Escalation, Gate 14 Port
                           Escalation, Gate 15 Orthogonal Intervention, Gate 16 Stochastic
                           Gap E-Value, and Memory Recovery), Ax4 privilege separation,
                           5D vector cost budget `CostVec`, and strict epistemic progress.
  - Section 5 (H8)       : Algorithmic `MetaSynset` (`projFeature`, `findSplitAxis`,
                           `freezeAxisQuery`) with universally quantified proof that any
                           axial split guarantees minimax gain >= 1 across domains.
  - Section 6 (H9-H11)   : Typed `RevisionMemory` (`Store` / `recoverToken`) preserving
                           provenance and residual gap, proving cost amortization (c_m < c_s),
                           and fail-closed blocking of unsound transfer on Rule 110 zero
                           background (`Rule110RingDecoupling`) and D4 shortcut graphs.
  - Section 7 (H12)      : Causal-Epistemic Synthesis integrating `ADT-HYPOTHESIS/1` with
                           `ContinuousSubject110` anomaly detection and `v1.5` dynamic
                           minimax repair reachability `RepairReach(W, t, t*)` on Rule 110.
-/

namespace CertifiedStrategySelectionV26

/-! ============================================================================
    SECTION 1: H1 — UNIFIED THREE-COORDINATE EPISTEMIC ACCESSIBILITY
    E(E) = <X_E (Expressible), D_E (Distinguishable), J_E (Identifiable)>
    ============================================================================ -/

/-- Unified epistemic environment parameterizing active candidate worlds `W`,
    hypothesis language `H`, observation port `port`, and intervention set `actions`. -/
structure EpistemicEnv (World Hypothesis Obs Action : Type) where
  worlds      : List World
  hyps        : List Hypothesis
  evalH       : Hypothesis → World → Bool
  port        : World → Obs
  actions     : List Action
  applyAction : Action → World → World
  target      : World → Bool

/-- Coordinate 1 (X_E): The target invariant is expressible in the current hypothesis language `H`. -/
def Expressible {World Hypothesis Obs Action : Type}
    (E : EpistemicEnv World Hypothesis Obs Action) : Prop :=
  ∃ h ∈ E.hyps, ∀ w ∈ E.worlds, E.evalH h w = E.target w

/-- Coordinate 2 (D_E): Every pair of active worlds with different target truth values
    is observationally distinguishable through the passive port `port`. -/
def Distinguishable {World Hypothesis Obs Action : Type}
    (E : EpistemicEnv World Hypothesis Obs Action) : Prop :=
  ∀ w1 ∈ E.worlds, ∀ w2 ∈ E.worlds,
    E.target w1 ≠ E.target w2 → E.port w1 ≠ E.port w2

/-- Coordinate 3 (J_E): Full operational identifiability — expressible in `H`, distinguishable
    through `port`, and equipped with a certifying intervention `a ∈ actions` that separates
    target-distinct worlds through the port after actuation. -/
def Identifiable {World Hypothesis Obs Action : Type}
    (E : EpistemicEnv World Hypothesis Obs Action) : Prop :=
  Expressible E ∧ Distinguishable E ∧
  (∀ w1 ∈ E.worlds, ∀ w2 ∈ E.worlds,
    E.target w1 ≠ E.target w2 →
    ∃ a ∈ E.actions, E.port (E.applyAction a w1) ≠ E.port (E.applyAction a w2))

/-- Inclusion J_E ⊆ X_E: Operational identifiability entails expressibility. -/
theorem H1_identifiable_implies_expressible
    {World Hypothesis Obs Action : Type}
    (E : EpistemicEnv World Hypothesis Obs Action) :
    Identifiable E → Expressible E := by
  intro hId
  exact hId.1

/-- Inclusion J_E ⊆ D_E: Operational identifiability entails observational distinguishability. -/
theorem H1_identifiable_implies_distinguishable
    {World Hypothesis Obs Action : Type}
    (E : EpistemicEnv World Hypothesis Obs Action) :
    Identifiable E → Distinguishable E := by
  intro hId
  exact hId.2.1

/-- State E1 in the unified Bool model: Expressible (X_E), but blind passive port (¬D_E). -/
def envE1_expr_not_dist : EpistemicEnv Bool Bool Bool Bool where
  worlds      := [false, true]
  hyps        := [true]
  evalH       := fun h w => if h then w else false
  port        := fun _ => false
  actions     := []
  applyAction := fun _ w => w
  target      := fun w => w

/-- State E2 in the same unified Bool model: Distinguishable (D_E), but impoverished language (¬X_E). -/
def envE2_dist_not_expr : EpistemicEnv Bool Bool Bool Bool where
  worlds      := [false, true]
  hyps        := [false]
  evalH       := fun _ _ => false
  port        := fun w => w
  actions     := [false]
  applyAction := fun _ w => w
  target      := fun w => w

/-- State E3 in the same unified Bool model: Expressible (X_E) and passively Distinguishable (D_E),
    but every available intervention collapses the port to a constant (¬J_E). -/
def envE3_expr_dist_not_ident : EpistemicEnv Bool Bool Bool Bool where
  worlds      := [false, true]
  hyps        := [true]
  evalH       := fun h w => if h then w else false
  port        := fun w => w
  actions     := [false]
  applyAction := fun _ _ => false
  target      := fun w => w

/-- State E4 in the same unified Bool model: Fully Identifiable (J_E). -/
def envE4_full_ident : EpistemicEnv Bool Bool Bool Bool where
  worlds      := [false, true]
  hyps        := [true]
  evalH       := fun h w => if h then w else false
  port        := fun w => w
  actions     := [true]
  applyAction := fun _ w => w
  target      := fun w => w

theorem H1_E1_expressible_not_distinguishable :
    Expressible envE1_expr_not_dist ∧ ¬ Distinguishable envE1_expr_not_dist := by
  constructor
  · refine ⟨true, by simp [envE1_expr_not_dist], ?_⟩
    intro w _
    rfl
  · intro hDist
    have hNe : envE1_expr_not_dist.port false ≠ envE1_expr_not_dist.port true :=
      hDist false (by simp [envE1_expr_not_dist]) true (by simp [envE1_expr_not_dist]) (by decide)
    exact hNe rfl

theorem H1_E2_distinguishable_not_expressible :
    Distinguishable envE2_dist_not_expr ∧ ¬ Expressible envE2_dist_not_expr := by
  constructor
  · intro w1 _ w2 _ hTarg
    exact hTarg
  · rintro ⟨h, _, hAll⟩
    have hTrue := hAll true (by simp [envE2_dist_not_expr])
    simp [envE2_dist_not_expr] at hTrue

theorem H1_E3_expr_and_dist_not_identifiable :
    Expressible envE3_expr_dist_not_ident ∧
    Distinguishable envE3_expr_dist_not_ident ∧
    ¬ Identifiable envE3_expr_dist_not_ident := by
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨true, by simp [envE3_expr_dist_not_ident], ?_⟩
    intro w _
    rfl
  · intro w1 _ w2 _ hTarg
    exact hTarg
  · rintro ⟨_, _, hAct⟩
    rcases hAct false (by simp [envE3_expr_dist_not_ident])
                true  (by simp [envE3_expr_dist_not_ident]) (by decide) with ⟨a, _, hPortNe⟩
    exact hPortNe rfl

/-- Master Theorem for H1: Complete 3-coordinate separation and inclusion in one unified model. -/
theorem H1_three_coordinate_strict_separation :
    (∀ E : EpistemicEnv Bool Bool Bool Bool, Identifiable E → Expressible E ∧ Distinguishable E) ∧
    (Expressible envE1_expr_not_dist ∧ ¬ Distinguishable envE1_expr_not_dist) ∧
    (Distinguishable envE2_dist_not_expr ∧ ¬ Expressible envE2_dist_not_expr) ∧
    (Expressible envE3_expr_dist_not_ident ∧ Distinguishable envE3_expr_dist_not_ident ∧
     ¬ Identifiable envE3_expr_dist_not_ident) := by
  refine ⟨?_, H1_E1_expressible_not_distinguishable,
          H1_E2_distinguishable_not_expressible,
          H1_E3_expr_and_dist_not_identifiable⟩
  intro E hId
  exact ⟨hId.1, hId.2.1⟩


/-! ============================================================================
    SECTION 2: H2 (GATE 13) — TRUE MULTI-SYMBOL QUEUE AUTOMATON vs STACK AUTOMATON
    Unconditional separation of FIFO QueueProgram from LIFO StackProgram across
    ALL stack capacities `cap : Nat` on Σ* = {b0, b1, sep}*.
    ============================================================================ -/

/-- Three-symbol alphabet Σ = {0, 1, #} for serial stream tasks u # v. -/
inductive Sym3 where
  | b0  : Sym3
  | b1  : Sym3
  | sep : Sym3
  deriving DecidableEq, Repr

/-- Operational state of a FIFO Queue Automaton or LIFO Stack Automaton:
    `reading = true` before `#`, `reading = false` after `#`, and memory buffer `buf`. -/
structure BufferState where
  reading : Bool
  buf     : List Bool
  deriving DecidableEq, Repr

/-- Single transition step of a FIFO Queue Automaton with bit-transform `inv` and capacity `cap`.
    Before `sep`: appends to the BACK of the FIFO queue (`st.buf ++ [b]`).
    After `sep` : dequeues from the FRONT of the FIFO queue (`head :: tail`) and checks `b == xor head inv`. -/
def stepQueue (inv : Bool) (cap : Nat) (st : BufferState) (s : Sym3) : Option BufferState :=
  match st.reading, s with
  | true, Sym3.b0 =>
    if st.buf.length < cap then some ⟨true, st.buf ++ [false]⟩ else none
  | true, Sym3.b1 =>
    if st.buf.length < cap then some ⟨true, st.buf ++ [true]⟩ else none
  | true, Sym3.sep =>
    some ⟨false, st.buf⟩
  | false, Sym3.b0 =>
    match st.buf with
    | []          => none
    | head :: tl  => if false == xor head inv then some ⟨false, tl⟩ else none
  | false, Sym3.b1 =>
    match st.buf with
    | []          => none
    | head :: tl  => if true == xor head inv then some ⟨false, tl⟩ else none
  | false, Sym3.sep => none

/-- Single transition step of a LIFO Stack Automaton with bit-transform `inv` and capacity `cap`.
    Before `sep`: pushes onto the TOP of the LIFO stack (`b :: st.buf`).
    After `sep` : pops from the TOP of the LIFO stack (`head :: tail`) and checks `b == xor head inv`. -/
def stepStack (inv : Bool) (cap : Nat) (st : BufferState) (s : Sym3) : Option BufferState :=
  match st.reading, s with
  | true, Sym3.b0 =>
    if st.buf.length < cap then some ⟨true, false :: st.buf⟩ else none
  | true, Sym3.b1 =>
    if st.buf.length < cap then some ⟨true, true :: st.buf⟩ else none
  | true, Sym3.sep =>
    some ⟨false, st.buf⟩
  | false, Sym3.b0 =>
    match st.buf with
    | []          => none
    | head :: tl  => if false == xor head inv then some ⟨false, tl⟩ else none
  | false, Sym3.b1 =>
    match st.buf with
    | []          => none
    | head :: tl  => if true == xor head inv then some ⟨false, tl⟩ else none
  | false, Sym3.sep => none

def runTransitions (stepFn : BufferState → Sym3 → Option BufferState)
    (st : BufferState) : List Sym3 → Option BufferState
  | []      => some st
  | s :: ss =>
    match stepFn st s with
    | none     => none
    | some st' => runTransitions stepFn st' ss

/-- Multi-symbol evaluator for Level-4 FIFO Queue Automaton on Σ*. -/
def evalQueue (inv : Bool) (cap : Nat) (w : List Sym3) : Bool :=
  match runTransitions (stepQueue inv cap) ⟨true, []⟩ w with
  | some st => !st.reading && st.buf.isEmpty
  | none    => false

/-- Multi-symbol evaluator for Level-3 LIFO Stack Automaton on Σ*. -/
def evalStack (inv : Bool) (cap : Nat) (w : List Sym3) : Bool :=
  match runTransitions (stepStack inv cap) ⟨true, []⟩ w with
  | some st => !st.reading && st.buf.isEmpty
  | none    => false

/-- Canonical serial test words over Σ = {0, 1, #}:
    w00  = 00#00 (symmetric copy)
    w01  = 01#01 (asymmetric FIFO copy)
    w101 = 101#101 (3-bit FIFO copy)
    wRev = 01#10 (asymmetric LIFO reversal / palindrome) -/
def w00 : List Sym3 := [Sym3.b0, Sym3.b0, Sym3.sep, Sym3.b0, Sym3.b0]
def w01 : List Sym3 := [Sym3.b0, Sym3.b1, Sym3.sep, Sym3.b0, Sym3.b1]
def w101 : List Sym3 := [Sym3.b1, Sym3.b0, Sym3.b1, Sym3.sep, Sym3.b1, Sym3.b0, Sym3.b1]
def wRev : List Sym3 := [Sym3.b0, Sym3.b1, Sym3.sep, Sym3.b1, Sym3.b0]

/-- QueueProgram (inv=false, cap=3) accepts FIFO copies `u # u` and rejects reversed `u # u^R`. -/
theorem H2_queue_recognizes_fifo_copy :
    evalQueue false 3 w00 = true ∧
    evalQueue false 3 w01 = true ∧
    evalQueue false 3 w101 = true ∧
    evalQueue false 3 wRev = false := by
  decide

/-- StackProgram (inv=false, cap=3) accepts LIFO palindromes `u # u^R` and rejects asymmetric `u # u`. -/
theorem H2_stack_recognizes_lifo_palindrome :
    evalStack false 3 w00 = true ∧
    evalStack false 3 wRev = true ∧
    evalStack false 3 w01 = false := by
  decide

/-- For ANY stack capacity `cap : Nat`, a non-inverting stack (`inv = false`) rejects `w01 = 01#01`
    because top-of-stack after `01#` is `1`, which clashes with the first post-separator bit `0`. -/
theorem H2_stack_inv_false_rejects_w01 (cap : Nat) :
    evalStack false cap w01 = false := by
  match cap with
  | 0 => rfl
  | 1 => rfl
  | n + 2 =>
    have h0 : 0 < n + 2 := by omega
    have h1 : 1 < n + 2 := by omega
    simp [evalStack, w01, runTransitions, stepStack, h0, h1]

/-- For ANY stack capacity `cap : Nat`, an inverting stack (`inv = true`) rejects `w00 = 00#00`
    because top-of-stack after `00#` is `0`, which under inversion expects `1` instead of `0`. -/
theorem H2_stack_inv_true_rejects_w00 (cap : Nat) :
    evalStack true cap w00 = false := by
  match cap with
  | 0 => rfl
  | 1 => rfl
  | n + 2 =>
    have h0 : 0 < n + 2 := by omega
    have h1 : 1 < n + 2 := by omega
    simp [evalStack, w00, runTransitions, stepStack, h0, h1]

/-- Master Theorem for H2 (Gate 13):
    Level-4 FIFO `QueueProgram` separates unconditionally from EVERY Level-3 LIFO `StackProgram`
    across ALL bit transforms `inv : Bool` and ALL stack capacities `cap : Nat` (infinite family). -/
theorem H2_gate13_queue_separates_from_arbitrary_stack :
    ∀ (inv : Bool) (cap : Nat),
      ¬ (evalStack inv cap w00 = evalQueue false 3 w00 ∧
         evalStack inv cap w01 = evalQueue false 3 w01) := by
  intro inv cap
  cases inv with
  | false =>
    intro hBoth
    have hRight := hBoth.2
    rw [H2_stack_inv_false_rejects_w01 cap] at hRight
    revert hRight
    decide
  | true =>
    intro hBoth
    have hLeft := hBoth.1
    rw [H2_stack_inv_true_rejects_w00 cap] at hLeft
    revert hLeft
    decide


/-! ============================================================================
    SECTION 3: H3 — NON-POSTULATED COMPUTABLE DETECTOR FOR SPURIOUS PORT EXTENSIONS
    Replaces postulated `sameObs` proofs with an executable Boolean detector
    `checkSpuriousFin` over a finite query basis `Q` and world set `W`, together
    with a formal soundness theorem and zero-split guarantee.
    ============================================================================ -/

/-- Semantic definition of a spurious port extension `extObs` over finite worlds `W` and queries `Q`:
    1. Its first projection recovers `baseObs` on every `(q, w) ∈ Q × W`.
    2. Whenever `extObs q w1 ≠ extObs q w2` on `(w1, w2) ∈ W × W`, the base port ALREADY
       distinguishes `w1` and `w2` on query `q` (`baseObs q w1 ≠ baseObs q w2`). -/
def IsSpuriousSemantic {World Query BaseVal NoiseVal : Type}
    [DecidableEq BaseVal] [DecidableEq NoiseVal]
    (W : List World) (Q : List Query)
    (baseObs : Query → World → BaseVal)
    (extObs  : Query → World → BaseVal × NoiseVal) : Prop :=
  (∀ q ∈ Q, ∀ w ∈ W, (extObs q w).1 = baseObs q w) ∧
  (∀ q ∈ Q, ∀ w1 ∈ W, ∀ w2 ∈ W,
    extObs q w1 ≠ extObs q w2 → baseObs q w1 ≠ baseObs q w2)

/-- Computable Boolean check for a single query `q` and world `w`: first projection matches base port. -/
def checkProjOn {World Query BaseVal NoiseVal : Type}
    [DecidableEq BaseVal]
    (W : List World) (baseObs : Query → World → BaseVal)
    (extObs : Query → World → BaseVal × NoiseVal) (q : Query) : Bool :=
  W.all (fun w => (extObs q w).1 == baseObs q w)

/-- Computable Boolean check for no new world-pair separations on query `q`. -/
def checkNoNewSplitOn {World Query BaseVal NoiseVal : Type}
    [DecidableEq BaseVal] [DecidableEq NoiseVal]
    (W : List World) (baseObs : Query → World → BaseVal)
    (extObs : Query → World → BaseVal × NoiseVal) (q : Query) : Bool :=
  W.all (fun w1 =>
    W.all (fun w2 =>
      (extObs q w1 == extObs q w2) || !(baseObs q w1 == baseObs q w2)))

/-- Computable non-postulated detector `checkSpuriousFin` over `W` and `Q`. -/
def checkSpuriousFin {World Query BaseVal NoiseVal : Type}
    [DecidableEq BaseVal] [DecidableEq NoiseVal]
    (W : List World) (Q : List Query)
    (baseObs : Query → World → BaseVal)
    (extObs  : Query → World → BaseVal × NoiseVal) : Bool :=
  Q.all (fun q => checkProjOn W baseObs extObs q && checkNoNewSplitOn W baseObs extObs q)

/-- Helper lemma: `List.all` soundness in pure Lean 4 core. -/
private theorem list_all_sound {α : Type} (xs : List α) (p : α → Bool)
    (hAll : xs.all p = true) : ∀ x ∈ xs, p x = true := by
  induction xs with
  | nil =>
    intro x hMem
    cases hMem
  | cons hd tl ih =>
    intro x hMem
    simp only [List.all, Bool.and_eq_true] at hAll
    cases hMem with
    | head => exact hAll.1
    | tail _ hIn => exact ih hAll.2 x hIn

/-- Master Soundness Theorem for H3:
    If the executable detector `checkSpuriousFin` returns `true`, then `IsSpuriousSemantic` holds. -/
theorem H3_checkSpuriousFin_sound
    {World Query BaseVal NoiseVal : Type}
    [DecidableEq BaseVal] [DecidableEq NoiseVal]
    (W : List World) (Q : List Query)
    (baseObs : Query → World → BaseVal)
    (extObs  : Query → World → BaseVal × NoiseVal)
    (hCheck : checkSpuriousFin W Q baseObs extObs = true) :
    IsSpuriousSemantic W Q baseObs extObs := by
  unfold checkSpuriousFin at hCheck
  have hQ := list_all_sound Q
    (fun q => checkProjOn W baseObs extObs q && checkNoNewSplitOn W baseObs extObs q) hCheck
  constructor
  · intro q hq w hw
    have hqBoth := hQ q hq
    simp only [Bool.and_eq_true] at hqBoth
    have hW := list_all_sound W (fun w => (extObs q w).1 == baseObs q w) hqBoth.1 w hw
    exact of_decide_eq_true hW
  · intro q hq w1 hw1 w2 hw2 hExtNe
    have hqBoth := hQ q hq
    simp only [Bool.and_eq_true] at hqBoth
    have hW1 := list_all_sound W
      (fun w1 => W.all (fun w2 => (extObs q w1 == extObs q w2) || !(baseObs q w1 == baseObs q w2)))
      hqBoth.2 w1 hw1
    have hW2 := list_all_sound W
      (fun w2 => (extObs q w1 == extObs q w2) || !(baseObs q w1 == baseObs q w2))
      hW1 w2 hw2
    simp only [Bool.or_eq_true] at hW2
    cases hW2 with
    | inl hEq =>
      have hExtEq : extObs q w1 = extObs q w2 := of_decide_eq_true hEq
      exact False.elim (hExtNe hExtEq)
    | inr hBaseNe =>
      intro hBaseEq
      have hBaseBeq : (baseObs q w1 == baseObs q w2) = true := decide_eq_true hBaseEq
      rw [hBaseBeq] at hBaseNe
      cases hBaseNe

/-- Concrete verification on a 3-world instance:
    A deterministic nuisance hash `extSpurious` is detected as `true`, whereas a genuine hidden-bit
    sensor `extGenuine` is certified as `false` (non-spurious). -/
def w3List : List (Fin 3) := [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩]
def q1List : List Unit := [()]
def baseParityPort (_ : Unit) (w : Fin 3) : Bool := w.val % 2 == 1
def spuriousHashPort (_ : Unit) (w : Fin 3) : Bool × Bool := (w.val % 2 == 1, !(w.val % 2 == 1))
def genuineHiddenPort (_ : Unit) (w : Fin 3) : Bool × Bool := (w.val % 2 == 1, w.val == 2)

theorem H3_detector_separates_spurious_from_genuine :
    checkSpuriousFin w3List q1List baseParityPort spuriousHashPort = true ∧
    checkSpuriousFin w3List q1List baseParityPort genuineHiddenPort = false := by
  decide


/-! ============================================================================
    SECTION 4: H4 + H5 + H6 + H7 + H7+ — UNIFIED CONTROLLER `LicensedStep`
    Integrates all 6 revision actions (Probe, Gate 12/13 Lang Escalation,
    Gate 14 Port Escalation, Gate 15 Orthogonal Intervention, Gate 16 Stochastic
    Gap E-Value, and Memory Transfer), Ax4 Privilege Separation, 5D Vector
    Budget `CostVec`, and Strict Epistemic Progress.
    ============================================================================ -/

/-- 5-Level Hypothesis Language Hierarchy (Gates 11, 12, 13). -/
inductive LangTier where
  | L0_Conj  : LangTier
  | L1_DFA   : LangTier
  | L2_1DCA  : LangTier
  | L3_Stack : LangTier
  | L4_Queue : LangTier
  deriving DecidableEq, Repr

def LangTier.rank : LangTier → Nat
  | .L0_Conj  => 0
  | .L1_DFA   => 1
  | .L2_1DCA  => 2
  | .L3_Stack => 3
  | .L4_Queue => 4

/-- 5-Dimensional Cost Vector (c_q, c_s, c_p, c_v, c_m) for H7/H7+. -/
structure CostVec where
  cq : Nat -- query / probe cost (and stochastic evaluation)
  cs : Nat -- language escalation cost (Gates 12/13)
  cp : Nat -- port escalation cost (Gate 14)
  cv : Nat -- surgical intervention cost (Gate 15 / dynamic repair)
  cm : Nat -- revision memory recovery cost (H9-H11)
  deriving DecidableEq, Repr

def CostVec.zero : CostVec := ⟨0, 0, 0, 0, 0⟩

def CostVec.add (a b : CostVec) : CostVec :=
  ⟨a.cq + b.cq, a.cs + b.cs, a.cp + b.cp, a.cv + b.cv, a.cm + b.cm⟩

def CostVec.le (a b : CostVec) : Bool :=
  (a.cq ≤ b.cq) && (a.cs ≤ b.cs) && (a.cp ≤ b.cp) && (a.cv ≤ b.cv) && (a.cm ≤ b.cm)

/-- Frozen Positive Tariff Schedule for H7+. -/
structure TariffSchedule where
  probeFee     : Nat
  langEscFee   : Nat
  portEscFee   : Nat
  interveneFee : Nat
  memRecFee    : Nat
  hPosProbe    : 0 < probeFee
  hPosLang     : 0 < langEscFee
  hPosPort     : 0 < portEscFee
  hPosInt      : 0 < interveneFee
  hPosMem      : 0 < memRecFee
  hAmortized   : memRecFee < langEscFee

/-- Canonical frozen tariff schedule with c_m = 1 < c_s = 4. -/
def canonicalTariffs : TariffSchedule where
  probeFee     := 1
  langEscFee   := 4
  portEscFee   := 3
  interveneFee := 2
  memRecFee    := 1
  hPosProbe    := by decide
  hPosLang     := by decide
  hPosPort     := by decide
  hPosInt      := by decide
  hPosMem      := by decide
  hAmortized   := by decide

/-- Structural vs Resource monitor signals (integrating Ax4 from `ControlledRepChange.lean`). -/
inductive MonitorSignal where
  | nominalOk       : MonitorSignal
  | resourceTimeout : MonitorSignal -- Sens_res = TIMEOUT alone (cannot license escalation!)
  | certifiedUnsat  : Nat → MonitorSignal -- Sens_struct = UNSAT(W) with witness ID
  deriving DecidableEq, Repr

def MonitorSignal.hasStructCert : MonitorSignal → Bool
  | .certifiedUnsat _ => true
  | _                 => false

/-- Gate 15 Orthogonal Intervention Certificate:
    - `obsCollision = true`: passive port cannot separate the candidate mechanisms;
    - `controlMaskOrthogonal = true`: control regime mask `K(do(I)(x)) = K(x)` is invariant;
    - `commutatorNonZero = true`: `[T_L, T_R] ≠ 0` separates the causal orderings. -/
structure Gate15Cert where
  obsCollision          : Bool
  controlMaskOrthogonal : Bool
  commutatorNonZero     : Bool
  deriving DecidableEq, Repr

def Gate15Cert.isValid (c : Gate15Cert) : Bool :=
  c.obsCollision && c.controlMaskOrthogonal && c.commutatorNonZero

/-- Gate 16 Stochastic Gap E-Value Certificate:
    - explicit positivity `0 < den` and `0 < totalMass`;
    - `hasGapBound = true`: certified dominance over the whole hypothesis class;
    - `eValueNum ≥ alphaInv * eValueDen`: sequential likelihood ratio crosses `1/α`. -/
structure Gate16Cert where
  den         : Nat
  totalMass   : Nat
  eValueNum   : Nat
  eValueDen   : Nat
  alphaInv    : Nat
  hasGapBound : Bool
  deriving DecidableEq, Repr

def Gate16Cert.isValid (c : Gate16Cert) : Bool :=
  (0 < c.den) && (0 < c.totalMass) && (0 < c.eValueDen) &&
  c.hasGapBound && (c.alphaInv * c.eValueDen ≤ c.eValueNum)

/-- Unified Epistemic Controller State. -/
structure UnifiedState where
  candidateWorlds : Nat      -- |W_t|
  activeHyps      : Nat      -- |H_t|
  tier            : LangTier -- current hypothesis language tier L_0 .. L_4
  portRank        : Nat      -- current non-spurious port dimensionality / rank
  intRank         : Nat      -- interventional separation rank (Gate 15)
  knowledgeCount  : Nat      -- |K_B(E_t)|: number of certified invariants / eliminated classes
  spent           : CostVec  -- cumulative 5D vector expenditure
  budget          : CostVec  -- total 5D vector budget B
  deriving DecidableEq, Repr

/-- Epistemic Accessibility Signature E(E) = (tier.rank, portRank, intRank, knowledgeCount)
    used to measure strict epistemic progress under H7+. -/
def UnifiedState.epistemicProgressScore (s : UnifiedState) : Nat :=
  s.tier.rank + s.portRank + s.intRank + s.knowledgeCount

/-- Unified Inductive Controller `LicensedStep` integrating all 6 operations (H4, H5, H6, H7+). -/
inductive LicensedStep (tariffs : TariffSchedule) : UnifiedState → UnifiedState → Prop where
  /-- 1. Informational Probe: requires positive candidate world split (`newWorlds < s.candidateWorlds`). -/
  | probe (s : UnifiedState) (newWorlds : Nat)
      (hGain : newWorlds < s.candidateWorlds)
      (hPos  : 0 < newWorlds)
      (hB    : CostVec.le (CostVec.add s.spent ⟨tariffs.probeFee, 0, 0, 0, 0⟩) s.budget = true) :
      LicensedStep tariffs s
        { s with
          candidateWorlds := newWorlds,
          knowledgeCount  := s.knowledgeCount + 1,
          spent           := CostVec.add s.spent ⟨tariffs.probeFee, 0, 0, 0, 0⟩ }

  /-- 2. Language Escalation (Gates 12 & 13, up to L4_Queue):
      Requires certified structural UNSAT witness (`sig.hasStructCert = true`, Ax4 privilege separation!)
      and strictly higher language tier `s.tier.rank < newTier.rank`. -/
  | escalateLang (s : UnifiedState) (newTier : LangTier) (sig : MonitorSignal) (newHyps : Nat)
      (hCert : sig.hasStructCert = true)
      (hTier : s.tier.rank < newTier.rank)
      (hB    : CostVec.le (CostVec.add s.spent ⟨0, tariffs.langEscFee, 0, 0, 0⟩) s.budget = true) :
      LicensedStep tariffs s
        { s with
          tier           := newTier,
          activeHyps     := newHyps,
          knowledgeCount := s.knowledgeCount + 1,
          spent          := CostVec.add s.spent ⟨0, tariffs.langEscFee, 0, 0, 0⟩ }

  /-- 3. Port Escalation (Gate 14 + H3 detector):
      Requires structural port obstruction (`sig.hasStructCert = true`) AND executable non-spurious
      certificate (`isSpurious = false` from `checkSpuriousFin`). -/
  | escalatePort (s : UnifiedState) (sig : MonitorSignal) (isSpurious : Bool)
      (hCert      : sig.hasStructCert = true)
      (hNotSpur   : isSpurious = false)
      (hB         : CostVec.le (CostVec.add s.spent ⟨0, 0, tariffs.portEscFee, 0, 0⟩) s.budget = true) :
      LicensedStep tariffs s
        { s with
          portRank       := s.portRank + 1,
          knowledgeCount := s.knowledgeCount + 1,
          spent          := CostVec.add s.spent ⟨0, 0, tariffs.portEscFee, 0, 0⟩ }

  /-- 4. Surgical Intervention (Gate 15):
      Requires valid Gate 15 certificate (`cert.isValid = true`: observational collision +
      orthogonal control mask + non-zero commutator). -/
  | intervene (s : UnifiedState) (cert : Gate15Cert) (newWorlds : Nat)
      (hValid : cert.isValid = true)
      (hSplit : newWorlds < s.candidateWorlds)
      (hB     : CostVec.le (CostVec.add s.spent ⟨0, 0, 0, tariffs.interveneFee, 0⟩) s.budget = true) :
      LicensedStep tariffs s
        { s with
          candidateWorlds := newWorlds,
          intRank         := s.intRank + 1,
          knowledgeCount  := s.knowledgeCount + 1,
          spent           := CostVec.add s.spent ⟨0, 0, 0, tariffs.interveneFee, 0⟩ }

  /-- 5. Stochastic Gap E-Value Refutation (Gate 16):
      Requires valid Gate 16 certificate (`cert.isValid = true`: 0 < den, 0 < totalMass,
      hasGapBound = true, eValueNum >= alphaInv * eValueDen). -/
  | stochasticReject (s : UnifiedState) (cert : Gate16Cert) (newHyps : Nat)
      (hValid : cert.isValid = true)
      (hElim  : newHyps < s.activeHyps)
      (hB     : CostVec.le (CostVec.add s.spent ⟨tariffs.probeFee, 0, 0, 0, 0⟩) s.budget = true) :
      LicensedStep tariffs s
        { s with
          activeHyps     := newHyps,
          knowledgeCount := s.knowledgeCount + 1,
          spent          := CostVec.add s.spent ⟨tariffs.probeFee, 0, 0, 0, 0⟩ }

  /-- 6. Revision Memory Recovery (H9-H11):
      Requires verified transfer precondition (`precondOk = true`) and charges amortized fee `memRecFee < langEscFee`. -/
  | recoverMemory (s : UnifiedState) (newTier : LangTier) (precondOk : Bool)
      (hPre  : precondOk = true)
      (hTier : s.tier.rank < newTier.rank)
      (hB    : CostVec.le (CostVec.add s.spent ⟨0, 0, 0, 0, tariffs.memRecFee⟩) s.budget = true) :
      LicensedStep tariffs s
        { s with
          tier           := newTier,
          knowledgeCount := s.knowledgeCount + 1,
          spent          := CostVec.add s.spent ⟨0, 0, 0, 0, tariffs.memRecFee⟩ }

/-- H4/H7 Theorem 1: Every `LicensedStep` preserves the 5D vector budget invariant `s'.spent ≤ s'.budget`. -/
theorem H4_licensed_step_preserves_vector_budget
    {tariffs : TariffSchedule} {s s' : UnifiedState}
    (hStep : LicensedStep tariffs s s') :
    CostVec.le s'.spent s'.budget = true := by
  cases hStep with
  | probe _ _ _ hB               => exact hB
  | escalateLang _ _ _ _ _ hB    => exact hB
  | escalatePort _ _ _ _ hB      => exact hB
  | intervene _ _ _ _ hB         => exact hB
  | stochasticReject _ _ _ _ hB  => exact hB
  | recoverMemory _ _ _ _ hB     => exact hB

/-- H4 Theorem 2 (Ax4 Privilege Separation from `ControlledRepChange.lean`):
    A resource timeout signal (`MonitorSignal.resourceTimeout`) without a structural UNSAT certificate
    can NEVER satisfy the `hasStructCert = true` guard required by `escalateLang` or `escalatePort`. -/
theorem H4_privilege_separation_blocks_timeout_escalation :
    MonitorSignal.resourceTimeout.hasStructCert = false ∧
    (MonitorSignal.resourceTimeout.hasStructCert = true → False) := by
  refine ⟨rfl, ?_⟩
  intro hBad
  cases hBad

/-- Executable port escalation gate combining structural obstruction and H3 `checkSpuriousFin`. -/
def tryEscalatePort (tariffs : TariffSchedule) (s : UnifiedState)
    (sig : MonitorSignal) (isSpurious : Bool) : Option UnifiedState :=
  let nextSpent := CostVec.add s.spent ⟨0, 0, tariffs.portEscFee, 0, 0⟩
  if sig.hasStructCert && !isSpurious && CostVec.le nextSpent s.budget then
    some { s with portRank := s.portRank + 1, knowledgeCount := s.knowledgeCount + 1, spent := nextSpent }
  else
    none

/-- H5 Theorem: Spurious port extensions (`isSpurious = true`) are unconditionally blocked
    from licensing a port escalation step. -/
theorem H5_spurious_port_blocked
    (tariffs : TariffSchedule) (s : UnifiedState) (sig : MonitorSignal) :
    tryEscalatePort tariffs s sig true = none := by
  unfold tryEscalatePort
  simp

/-- H6 Theorem: Every `intervene` step guarantees orthogonal control mask invariance and non-zero commutator,
    and every `stochasticReject` step guarantees positive denominator, positive total mass, gap bound,
    and threshold crossing. -/
theorem H6_gate15_and_gate16_certificates_enforced
    (cert15 : Gate15Cert) (cert16 : Gate16Cert)
    (h15 : cert15.isValid = true) (h16 : cert16.isValid = true) :
    (cert15.obsCollision = true ∧ cert15.controlMaskOrthogonal = true ∧ cert15.commutatorNonZero = true) ∧
    (0 < cert16.den ∧ 0 < cert16.totalMass ∧ cert16.hasGapBound = true ∧
     cert16.alphaInv * cert16.eValueDen ≤ cert16.eValueNum) := by
  unfold Gate15Cert.isValid at h15
  unfold Gate16Cert.isValid at h16
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h15 h16
  refine ⟨⟨h15.1.1, h15.1.2, h15.2⟩, ⟨h16.1.1.1.1, h16.1.1.1.2, h16.1.2, h16.2⟩⟩

/-- H7/H7+ Theorem: Every `LicensedStep` strictly increases the epistemic progress score
    (`s.epistemicProgressScore < s'.epistemicProgressScore`) and expands certified knowledge `knowledgeCount`,
    ruling out degenerate `always UNKNOWN` and `spurious_port` policies. -/
theorem H7_licensed_step_strict_epistemic_progress
    {tariffs : TariffSchedule} {s s' : UnifiedState}
    (hStep : LicensedStep tariffs s s') :
    s.epistemicProgressScore < s'.epistemicProgressScore ∧
    s.knowledgeCount < s'.knowledgeCount := by
  cases hStep with
  | probe _ _ _ _ =>
    unfold UnifiedState.epistemicProgressScore
    simp only
    omega
  | escalateLang _ _ _ _ hTier _ =>
    unfold UnifiedState.epistemicProgressScore
    simp only
    omega
  | escalatePort _ _ _ _ _ =>
    unfold UnifiedState.epistemicProgressScore
    simp only
    omega
  | intervene _ _ _ _ _ =>
    unfold UnifiedState.epistemicProgressScore
    simp only
    omega
  | stochasticReject _ _ _ _ _ =>
    unfold UnifiedState.epistemicProgressScore
    simp only
    omega
  | recoverMemory _ _ _ hTier _ =>
    unfold UnifiedState.epistemicProgressScore
    simp only
    omega


/-! ============================================================================
    SECTION 5: H8 — ALGORITHMIC `MetaSynset` (`Proj`, `SplitAxis`, `Freeze`)
    Proves universally that for ANY cross-domain candidate list `M : List (DomainObj k)`
    and ANY feature axis `axis : Fin k`, if `isAxialSplit M axis = true`, then
    freezing the axis query guarantees `minimaxGain M axis >= 1` (both sub-branches
    strictly shrink `M`) without manual query-menu crafting.
    ============================================================================ -/

/-- Structural object with a `k`-bit invariant feature signature from domain `domainId`. -/
structure DomainObj (k : Nat) where
  domainId : Nat
  objId    : Nat
  features : Fin k → Bool

/-- Operator 1 (`Proj`): projects a cross-domain object onto structural feature axis `axis`. -/
def projFeature {k : Nat} (axis : Fin k) (d : DomainObj k) : Bool :=
  d.features axis

/-- Operator 2 (`SplitAxis` test): checks whether feature axis `axis` splits candidate set `M`
    into both `false` and `true` fibers. -/
def isAxialSplit {k : Nat} (M : List (DomainObj k)) (axis : Fin k) : Bool :=
  M.any (fun d => !projFeature axis d) && M.any (fun d => projFeature axis d)

/-- Operator 3 (`Freeze`): freezes an axial split into a concrete query partition branch `b : Bool`. -/
def freezeAxisQuery {k : Nat} (axis : Fin k) (M : List (DomainObj k)) (b : Bool) : List (DomainObj k) :=
  M.filter (fun d => projFeature axis d == b)

/-- Worst-case (minimax) candidate elimination gain of freezing `axis` on `M`. -/
def minimaxGain {k : Nat} (M : List (DomainObj k)) (axis : Fin k) : Nat :=
  let n0 := (freezeAxisQuery axis M false).length
  let n1 := (freezeAxisQuery axis M true).length
  M.length - (if n0 ≤ n1 then n1 else n0)

/-- Conservation of candidate count across the `false` and `true` frozen branches. -/
theorem H8_partition_length_conservation {k : Nat} (M : List (DomainObj k)) (axis : Fin k) :
    (freezeAxisQuery axis M false).length + (freezeAxisQuery axis M true).length = M.length := by
  induction M with
  | nil => rfl
  | cons hd tl ih =>
    unfold freezeAxisQuery at *
    simp only [List.filter]
    cases hP : projFeature axis hd
    · change (hd :: List.filter (fun d => projFeature axis d == false) tl).length +
             (List.filter (fun d => projFeature axis d == true) tl).length = tl.length + 1
      simp only [List.length]
      omega
    · change (List.filter (fun d => projFeature axis d == false) tl).length +
             (hd :: List.filter (fun d => projFeature axis d == true) tl).length = tl.length + 1
      simp only [List.length]
      omega

/-- If `M.any (fun d => projFeature axis d == b) = true`, then `(freezeAxisQuery axis M b).length ≥ 1`. -/
private theorem filter_pos_of_any {k : Nat} (M : List (DomainObj k)) (axis : Fin k) (b : Bool)
    (hAny : M.any (fun d => projFeature axis d == b) = true) :
    1 ≤ (freezeAxisQuery axis M b).length := by
  induction M with
  | nil => cases hAny
  | cons hd tl ih =>
    unfold freezeAxisQuery
    simp only [List.any, Bool.or_eq_true] at hAny
    simp only [List.filter]
    cases hEq : (projFeature axis hd == b)
    · rw [hEq] at hAny
      rcases hAny with hBad | hTail
      · cases hBad
      · exact ih hTail
    · simp only [List.length]
      omega

private theorem any_not_eq_any_beq_false {k : Nat} (M : List (DomainObj k)) (axis : Fin k) :
    M.any (fun d => !projFeature axis d) = M.any (fun d => projFeature axis d == false) := by
  induction M with
  | nil => rfl
  | cons hd tl ih =>
    simp only [List.any, ih]
    cases projFeature axis hd <;> rfl

private theorem any_id_eq_any_beq_true {k : Nat} (M : List (DomainObj k)) (axis : Fin k) :
    M.any (fun d => projFeature axis d) = M.any (fun d => projFeature axis d == true) := by
  induction M with
  | nil => rfl
  | cons hd tl ih =>
    simp only [List.any, ih]
    cases projFeature axis hd <;> rfl

/-- Master Theorem for H8:
    For ANY candidate list `M : List (DomainObj k)` and ANY structural axis `axis : Fin k`,
    if `isAxialSplit M axis = true`, then `Freeze` is guaranteed to yield `minimaxGain M axis ≥ 1`
    (and both branches strictly shrink `M`). -/
theorem H8_algorithmic_metasynset_minimax_gain_ge_1
    {k : Nat} (M : List (DomainObj k)) (axis : Fin k)
    (hSplit : isAxialSplit M axis = true) :
    1 ≤ minimaxGain M axis ∧
    (freezeAxisQuery axis M false).length < M.length ∧
    (freezeAxisQuery axis M true).length < M.length := by
  unfold isAxialSplit at hSplit
  simp only [Bool.and_eq_true] at hSplit
  have hAny0 : M.any (fun d => projFeature axis d == false) = true := by
    rw [← any_not_eq_any_beq_false]
    exact hSplit.1
  have hAny1 : M.any (fun d => projFeature axis d == true) = true := by
    rw [← any_id_eq_any_beq_true]
    exact hSplit.2
  have hLen0 : 1 ≤ (freezeAxisQuery axis M false).length := filter_pos_of_any M axis false hAny0
  have hLen1 : 1 ≤ (freezeAxisQuery axis M true).length  := filter_pos_of_any M axis true  hAny1
  have hSum  := H8_partition_length_conservation M axis
  unfold minimaxGain
  dsimp
  by_cases hLe : (freezeAxisQuery axis M false).length ≤ (freezeAxisQuery axis M true).length
  · simp only [hLe, ite_true]
    omega
  · simp only [hLe, ite_false]
    omega

/-- Concrete cross-domain `MetaSynset` spanning 3 distinct domains:
    D1 (Rule 110 glider phase), D2 (hidden causal chain), D4 (modular tree graph).
    Axis 0 is the shared synset invariant (`true` on all 3); Axis 1 is the axial split coordinate. -/
def crossDomainSynset : List (DomainObj 2) :=
  [ { domainId := 1, objId := 101, features := fun i => if i.val == 0 then true else false },
    { domainId := 2, objId := 202, features := fun i => if i.val == 0 then true else true  },
    { domainId := 4, objId := 404, features := fun i => if i.val == 0 then true else false } ]

theorem H8_cross_domain_instance_verified :
    isAxialSplit crossDomainSynset ⟨0, by decide⟩ = false ∧
    isAxialSplit crossDomainSynset ⟨1, by decide⟩ = true ∧
    minimaxGain crossDomainSynset ⟨1, by decide⟩ = 1 := by
  decide


/-! ============================================================================
    SECTION 6: H9 + H10 + H11 — TYPED `RevisionMemory` (`Store` / `Recover`),
    COST AMORTIZATION (c_m < c_s), AND FAIL-CLOSED BLOCKING ON RULE 110 RING
    Integrates the exact Rule 110 ring autonomy dichotomy from `Rule110RingDecoupling.lean`.
    ============================================================================ -/

/-- Typed revision memory token storing provenance, scope, seam-input requirement,
    residual gap bound Δ(T), discovery cost `cs`, and transfer cost `cm`. -/
structure RevisionToken where
  tokenId            : Nat
  originDomain       : Nat
  portWidth          : Nat
  requiredSeamInputs : Nat -- number of external seam inputs assumed by the compressed observer
  residualGapBound   : Nat -- Δ(T)
  discoverCost       : Nat -- c_s
  transferCost       : Nat -- c_m
  deriving DecidableEq, Repr

/-- Target environment descriptor for cross-episode memory recovery. -/
structure TargetEnv where
  envId              : Nat
  domain             : Nat
  portWidth          : Nat
  isPortAutonomous   : Bool -- verified by finite-automaton closure on the background
  actualSeamInputs   : Nat  -- actual external dependency inputs entering the port
  maxAllowedGap      : Nat  -- tolerance threshold for Δ(T)
  deriving DecidableEq, Repr

/-- Fail-closed transfer precondition checker `verifyTransferPrecond`. -/
def verifyTransferPrecond (tok : RevisionToken) (env : TargetEnv) : Bool :=
  (tok.portWidth == env.portWidth) &&
  env.isPortAutonomous &&
  (env.actualSeamInputs ≤ tok.requiredSeamInputs) &&
  (tok.residualGapBound ≤ env.maxAllowedGap) &&
  (tok.transferCost < tok.discoverCost)

/-- `Store`: appends a certified token to revision memory. -/
def storeToken (mem : List RevisionToken) (tok : RevisionToken) : List RevisionToken :=
  tok :: mem

/-- `Recover`: retrieves the first token in `mem` whose transfer precondition holds in `env`. -/
def recoverToken (mem : List RevisionToken) (env : TargetEnv) : Option RevisionToken :=
  mem.find? (fun tok => verifyTransferPrecond tok env)

private theorem list_find_some_prop {α : Type} (xs : List α) (p : α → Bool) (x : α)
    (hFind : xs.find? p = some x) : x ∈ xs ∧ p x = true := by
  induction xs with
  | nil => cases hFind
  | cons hd tl ih =>
    simp only [List.find?] at hFind
    cases hP : p hd
    · rw [hP] at hFind
      have hSub := ih hFind
      exact ⟨List.Mem.tail hd hSub.1, hSub.2⟩
    · rw [hP] at hFind
      injection hFind with hEq
      subst hEq
      exact ⟨List.Mem.head tl, hP⟩

/-- H9 Theorem: `recoverToken` is sound — any recovered token belongs to `mem`, preserves port width,
    satisfies the target environment's autonomy & seam-input preconditions, and respects `residualGapBound`. -/
theorem H9_recoverToken_preserves_provenance_and_gap
    (mem : List RevisionToken) (env : TargetEnv) (tok : RevisionToken)
    (hRec : recoverToken mem env = some tok) :
    tok ∈ mem ∧
    tok.portWidth = env.portWidth ∧
    env.isPortAutonomous = true ∧
    env.actualSeamInputs ≤ tok.requiredSeamInputs ∧
    tok.residualGapBound ≤ env.maxAllowedGap ∧
    tok.transferCost < tok.discoverCost := by
  unfold recoverToken at hRec
  have ⟨hMem, hPre⟩ := list_find_some_prop mem (fun t => verifyTransferPrecond t env) tok hRec
  unfold verifyTransferPrecond at hPre
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hPre
  refine ⟨hMem, hPre.1.1.1.1, hPre.1.1.1.2, hPre.1.1.2, hPre.1.2, hPre.2⟩

/-- H10 Theorem: Across any stream of `k ≥ 2` compatible episodes, storing and recovering a
    revision token strictly amortizes total epistemic cost compared to memoryless re-escalation:
    `cs + (k - 1) * cm < k * cs`. -/
theorem H10_memory_transfer_strict_stream_amortization
    (mem : List RevisionToken) (env : TargetEnv) (tok : RevisionToken) (k : Nat)
    (hRec : recoverToken mem env = some tok)
    (hEpisodes : 2 ≤ k) :
    tok.discoverCost + (k - 1) * tok.transferCost < k * tok.discoverCost := by
  have hProps := H9_recoverToken_preserves_provenance_and_gap mem env tok hRec
  have hLt : tok.transferCost < tok.discoverCost := hProps.2.2.2.2.2
  have hMul : (k - 1) * tok.transferCost < (k - 1) * tok.discoverCost :=
    Nat.mul_lt_mul_of_pos_left hLt (by omega)
  have hDecomp : tok.discoverCost + (k - 1) * tok.discoverCost = k * tok.discoverCost := by
    have hK : 1 + (k - 1) = k := by omega
    calc
      tok.discoverCost + (k - 1) * tok.discoverCost
          = 1 * tok.discoverCost + (k - 1) * tok.discoverCost := by simp
      _ = (1 + (k - 1)) * tok.discoverCost := by rw [Nat.add_mul]
      _ = k * tok.discoverCost := by rw [hK]
  omega

/-! ### Rule 110 Ring Autonomy vs Non-Autonomy Witness for H11 (`Rule110RingDecoupling.lean`) -/

/-- Exact Wolfram Rule 110 local transition. -/
def rule110 (l c r : Bool) : Bool :=
  match l, c, r with
  | true,  true,  true  => false
  | true,  true,  false => true
  | true,  false, true  => true
  | true,  false, false => false
  | false, true,  true  => true
  | false, true,  false => true
  | false, false, true  => true
  | false, false, false => false

/-- 4-bit observation port W = {3, 4, 5, 6} on Z/14Z from `Rule110RingDecoupling.lean`. -/
abbrev Bit4 := Bool × Bool × Bool × Bool

/-- Exact autonomous transition of the 4-bit port W = {3, 4, 5, 6} on the 14-cell Rule 110 ether ring:
    Because the ether background supplies fixed boundary bits `x_2 = true` and `x_7 = false`,
    `W` evolves as a 0-input closed finite automaton with two 7-cycles and two fixed points. -/
def etherAutomaton (w : Bit4) : Bit4 :=
  let (b3, b4, b5, b6) := w
  (rule110 true b3 b4, rule110 b3 b4 b5, rule110 b4 b5 b6, rule110 b5 b6 false)

/-- Check whether the 4-bit port W = {3, 4, 5, 6} is autonomous on the zero background when cell 7
    (the immediate right neighbor outside W) varies between `false` and `true`. -/
def isPortAutonomousWithVaryingRightNeighbor : Bool :=
  let (b3, b4, b5, b6) : Bit4 := (false, false, false, false)
  let stepWithRight0 : Bit4 :=
    (rule110 false b3 b4, rule110 b3 b4 b5, rule110 b4 b5 b6, rule110 b5 b6 false)
  let stepWithRight1 : Bit4 :=
    (rule110 false b3 b4, rule110 b3 b4 b5, rule110 b4 b5 b6, rule110 b5 b6 true)
  stepWithRight0 == stepWithRight1

/-- Token learned on the Rule 110 Ether Ring (4-bit autonomous port, 0 external seam inputs, c_s=4, c_m=1). -/
def r110EtherPortToken : RevisionToken where
  tokenId            := 110
  originDomain       := 1
  portWidth          := 4
  requiredSeamInputs := 0
  residualGapBound   := 0
  discoverCost       := 4
  transferCost       := 1

/-- Target Environment 1: New episode on the Rule 110 Ether Ring (autonomous 4-bit port, 0 seam inputs). -/
def envR110EtherRing : TargetEnv where
  envId            := 1
  domain           := 1
  portWidth        := 4
  isPortAutonomous := true
  actualSeamInputs := 0
  maxAllowedGap    := 0

/-- Target Environment 2: Rule 110 Zero-Background / Chiral Seam regime
    (non-autonomous without the 4 right-cone chiral seam inputs `c_0..c_3`). -/
def envR110ZeroBgSeam : TargetEnv where
  envId            := 2
  domain           := 1
  portWidth        := 4
  isPortAutonomous := isPortAutonomousWithVaryingRightNeighbor
  actualSeamInputs := 4
  maxAllowedGap    := 0

/-- Target Environment 3: D4 Graph after adding a cross-layer shortcut edge
    (breaks 0-input tree-depth modularity by introducing 1 shortcut seam input and residual gap 2 > 0). -/
def envD4ShortcutGraph : TargetEnv where
  envId            := 3
  domain           := 4
  portWidth        := 4
  isPortAutonomous := false
  actualSeamInputs := 1
  maxAllowedGap    := 0

/-- Master Theorem for H11:
    1. On the Rule 110 Ether Ring, the 4-bit autonomous observer token is soundly recovered (`some`).
    2. On the Rule 110 Zero Background (`isPortAutonomousWithVaryingRightNeighbor = false`, 4 seam inputs),
       transfer of the 0-input ether token is fail-closed BLOCKED (`none`).
    3. On the D4 Graph with a shortcut edge, transfer is fail-closed BLOCKED (`none`). -/
theorem H11_unsound_transfer_blocked_on_r110_zero_bg_and_d4_shortcut :
    isPortAutonomousWithVaryingRightNeighbor = false ∧
    recoverToken [r110EtherPortToken] envR110EtherRing = some r110EtherPortToken ∧
    recoverToken [r110EtherPortToken] envR110ZeroBgSeam = none ∧
    recoverToken [r110EtherPortToken] envD4ShortcutGraph = none := by
  decide


/-! ============================================================================
    SECTION 7: H12 — CAUSAL-EPISTEMIC HORIZON SYNTHESIS
    Unifies `ADT-HYPOTHESIS/1` with `ContinuousSubject110` anomaly detection and
    `v1.5` Causal-Dynamic Operational Sufficiency (`RepairReach(W, t, t*)` and
    `minimaxVDyn`) on Rule 110.
    ============================================================================ -/

/-- N-step iteration of a world dynamics `step : World → World`. -/
def iterateN {World : Type} (step : World → World) : Nat → World → World
  | 0,     w => w
  | n + 1, w => step (iterateN step n w)

/-- Decidable predicate testing whether local actuator `act` repairs EVERY world `w ∈ W`
    by deadline `tStar` from current time `t` (`t ≤ tStar`). -/
def inRepairReach {World : Type}
    (step : World → World) (W : List World) (t tStar : Nat)
    (inv : World → Bool) (act : World → World) : Bool :=
  (t ≤ tStar) && W.all (fun w => inv (iterateN step (tStar - t) (act w)))

/-- Sublist of candidate local actuators `actions` that lie in `RepairReach(W, t, t*)`. -/
def repairReachList {World : Type}
    (step : World → World) (W : List World) (t tStar : Nat)
    (inv : World → Bool) (actions : List (World → World)) : List (World → World) :=
  if t ≤ tStar then
    actions.filter (fun act => W.all (fun w => inv (iterateN step (tStar - t) (act w))))
  else
    []

/-- Evolved observation branch `T^{Δt}(W_{q,y})`:
    evolves every `w ∈ W` by `delay` steps under `step`, then filters by observation `obs (T^{delay} w) == y`. -/
def evolveBranch {World Obs : Type} [DecidableEq Obs]
    (step : World → World) (delay : Nat) (obs : World → Obs)
    (W : List World) (y : Obs) : List World :=
  (W.map (iterateN step delay)).filter (fun ew => obs ew == y)

/-- Concrete 6-cell Rule 110 ring world with `DecidableEq` for direct kernel computation. -/
structure R6World where
  b0 : Bool
  b1 : Bool
  b2 : Bool
  b3 : Bool
  b4 : Bool
  b5 : Bool
  deriving DecidableEq, Repr

/-- Exact 1-step Rule 110 evolution on the 6-cell ring Z/6Z. -/
def stepR6 (w : R6World) : R6World where
  b0 := rule110 w.b5 w.b0 w.b1
  b1 := rule110 w.b0 w.b1 w.b2
  b2 := rule110 w.b1 w.b2 w.b3
  b3 := rule110 w.b2 w.b3 w.b4
  b4 := rule110 w.b3 w.b4 w.b5
  b5 := rule110 w.b4 w.b5 w.b0

/-- Minimal witness worlds `w0 = (1,0,0,0,1,0)` and `w1 = (1,0,0,1,1,0)` from `v1.5`,
    differing only at hidden cell 3 outside target (0), passive port (1), and actuator (2). -/
def r6W0 : R6World := ⟨true, false, false, false, true, false⟩
def r6W1 : R6World := ⟨true, false, false, true,  true, false⟩
def r6Candidates : List R6World := [r6W0, r6W1]

/-- Passive observation port at cell 1. -/
def r6Port1 (w : R6World) : Bool := w.b1

/-- Target invariant at deadline `t* = 3`: cell 0 must equal `false` (0). -/
def r6TargetInv (w : R6World) : Bool := !w.b0

/-- Named 1-cell local actuators at index 2 (`set_2_to_0` and `set_2_to_1`). -/
inductive R6Actuator where
  | set2To0 : R6Actuator
  | set2To1 : R6Actuator
  deriving DecidableEq, Repr

def R6Actuator.apply : R6Actuator → R6World → R6World
  | .set2To0, w => { w with b2 := false }
  | .set2To1, w => { w with b2 := true  }

def r6AllActuators : List R6Actuator := [.set2To0, .set2To1]

def r6ReachableActuators (W : List R6World) (t tStar : Nat) : List R6Actuator :=
  if t ≤ tStar then
    r6AllActuators.filter (fun a =>
      W.all (fun w => r6TargetInv (iterateN stepR6 (tStar - t) (a.apply w))))
  else
    []

/-- Causal-Epistemic Controller decision mode at `(W, t, t*)`:
    - `immediateSurgicalRepair a`: fires actuator `a` immediately at `t` when waiting `Δt` closes
      the repair horizon on at least one reachable branch;
    - `waitAndProbe`: waits `Δt` to disambiguate worlds when all evolved branches remain repairable;
    - `failClosedUnsat`: halts fail-closed if neither immediate nor delayed repair is possible. -/
inductive CausalEpistemicDecision where
  | immediateSurgicalRepair : R6Actuator → CausalEpistemicDecision
  | waitAndProbe            : CausalEpistemicDecision
  | failClosedUnsat         : CausalEpistemicDecision
  deriving DecidableEq, Repr

def selectCausalEpistemicAction (W : List R6World) (t tStar delay : Nat) : CausalEpistemicDecision :=
  let branchFalse := evolveBranch stepR6 delay r6Port1 W false
  let branchTrue  := evolveBranch stepR6 delay r6Port1 W true
  let delayedOk   := (t + delay ≤ tStar) &&
                     (branchFalse.isEmpty || !(r6ReachableActuators branchFalse (t + delay) tStar).isEmpty) &&
                     (branchTrue.isEmpty  || !(r6ReachableActuators branchTrue  (t + delay) tStar).isEmpty)
  if delayedOk then
    .waitAndProbe
  else
    match r6ReachableActuators W t tStar with
    | a :: _ => .immediateSurgicalRepair a
    | []     => .failClosedUnsat

/-- Master Theorem for H12a (Causal-Epistemic Horizon Closure & Controller Override):
    On Rule 110 (`r6Candidates = [r6W0, r6W1]`, `t = 0`, `t* = 3`, probe delay `Δt = 2`):
    1. At `t = 0`, `r6W0` and `r6W1` are colliding on passive port `r6Port1` (`r6Port1 r6W0 = r6Port1 r6W1`),
       and waiting `Δt = 2` completely identifies both worlds (`r6Port1 (T^2 r6W0) ≠ r6Port1 (T^2 r6W1)`).
    2. Yet waiting `Δt = 2` closes the causal repair horizon on BOTH evolved branches
       (`r6ReachableActuators` is `[]` on `[T^2 r6W0]` and `[]` on `[T^2 r6W1]`), even with remaining time `3 - 2 = 1 > 0`.
    3. At `t = 0`, immediate repair `R6Actuator.set2To1` lies in `RepairReach(W, 0, 3)`, and the unified
       Causal-Epistemic Controller overrides passive probing with `.immediateSurgicalRepair .set2To1`. -/
theorem H12_causal_epistemic_horizon_synthesis :
    r6Port1 r6W0 = r6Port1 r6W1 ∧
    r6Port1 (iterateN stepR6 2 r6W0) = false ∧
    r6Port1 (iterateN stepR6 2 r6W1) = true ∧
    r6ReachableActuators r6Candidates 0 3 = [R6Actuator.set2To1] ∧
    r6ReachableActuators (evolveBranch stepR6 2 r6Port1 r6Candidates false) 2 3 = [] ∧
    r6ReachableActuators (evolveBranch stepR6 2 r6Port1 r6Candidates true)  2 3 = [] ∧
    selectCausalEpistemicAction r6Candidates 0 3 2 =
      CausalEpistemicDecision.immediateSurgicalRepair R6Actuator.set2To1 := by
  decide

/-! ### Temporal Subject Anomaly Detection (`ContinuousSubject110.lean`) -> Licensed Repair -/

/-- Temporal observer (`Subject` from `ContinuousSubject110.lean`) tracking both the autonomous 4-bit port
    on the Rule 110 ether ring and the 1-bit endogenous register `q` across episodes. -/
structure Subject110 where
  q       : Bool
  current : Bit4
  deriving DecidableEq, Repr

/-- Exact Rule 110 Algebraic XOR Gate from `ContinuousSubject110.lean` (Theorem 1):
    When the left neighbor is `true` (1), local Rule 110 update computes `xor z k`. -/
theorem H12_rule110_algebraic_xor_gate (z k : Bool) :
    rule110 true z k = xor z k := by
  cases z <;> cases k <;> rfl

/-- Nominal periodic orbit state `(false, true, true, true)` of `etherAutomaton`
    (`etherAutomaton^2 (0111) = 0111`). -/
def nominalCycleState0 : Bit4 := (false, true, true, true)

/-- Checks whether the observed next 4-bit port state `obsNext` matches the subject's internal
    autonomous model `etherAutomaton s.current` (`SelfStep` vs `ExternalForcedStep`). -/
def subjectDetectsAnomaly (s : Subject110) (obsNext : Bit4) : Bool :=
  obsNext != etherAutomaton s.current

/-- Master Theorem for H12b (Temporal Subject Periodicity & Anomaly-Triggered Escalation):
    1. The subject's internal Rule 110 ether model `etherAutomaton` returns `nominalCycleState0`
       to itself in 2 steps (`etherAutomaton^2 (0111) = 0111`) with `subjectDetectsAnomaly = false`.
    2. An external perturbation forcing `(true, true, true, true)` is immediately detected
       as an anomaly (`subjectDetectsAnomaly = true`), licensing causal-dynamic repair. -/
theorem H12_temporal_subject_period2_and_anomaly_trigger :
    iterateN etherAutomaton 2 nominalCycleState0 = nominalCycleState0 ∧
    subjectDetectsAnomaly ⟨false, nominalCycleState0⟩ (etherAutomaton nominalCycleState0) = false ∧
    subjectDetectsAnomaly ⟨false, nominalCycleState0⟩ (true, true, true, true) = true := by
  decide

end CertifiedStrategySelectionV26

/-! ============================================================================
    AXIOM AUDIT FOR ALL 27 THEOREMS IN `certified_strategy_selection_v2_6.lean`
    ============================================================================ -/
#print axioms CertifiedStrategySelectionV26.H1_identifiable_implies_expressible
#print axioms CertifiedStrategySelectionV26.H1_identifiable_implies_distinguishable
#print axioms CertifiedStrategySelectionV26.H1_E1_expressible_not_distinguishable
#print axioms CertifiedStrategySelectionV26.H1_E2_distinguishable_not_expressible
#print axioms CertifiedStrategySelectionV26.H1_E3_expr_and_dist_not_identifiable
#print axioms CertifiedStrategySelectionV26.H1_three_coordinate_strict_separation
#print axioms CertifiedStrategySelectionV26.H2_queue_recognizes_fifo_copy
#print axioms CertifiedStrategySelectionV26.H2_stack_recognizes_lifo_palindrome
#print axioms CertifiedStrategySelectionV26.H2_stack_inv_false_rejects_w01
#print axioms CertifiedStrategySelectionV26.H2_stack_inv_true_rejects_w00
#print axioms CertifiedStrategySelectionV26.H2_gate13_queue_separates_from_arbitrary_stack
#print axioms CertifiedStrategySelectionV26.H3_checkSpuriousFin_sound
#print axioms CertifiedStrategySelectionV26.H3_detector_separates_spurious_from_genuine
#print axioms CertifiedStrategySelectionV26.H4_licensed_step_preserves_vector_budget
#print axioms CertifiedStrategySelectionV26.H4_privilege_separation_blocks_timeout_escalation
#print axioms CertifiedStrategySelectionV26.H5_spurious_port_blocked
#print axioms CertifiedStrategySelectionV26.H6_gate15_and_gate16_certificates_enforced
#print axioms CertifiedStrategySelectionV26.H7_licensed_step_strict_epistemic_progress
#print axioms CertifiedStrategySelectionV26.H8_partition_length_conservation
#print axioms CertifiedStrategySelectionV26.H8_algorithmic_metasynset_minimax_gain_ge_1
#print axioms CertifiedStrategySelectionV26.H8_cross_domain_instance_verified
#print axioms CertifiedStrategySelectionV26.H9_recoverToken_preserves_provenance_and_gap
#print axioms CertifiedStrategySelectionV26.H10_memory_transfer_strict_stream_amortization
#print axioms CertifiedStrategySelectionV26.H11_unsound_transfer_blocked_on_r110_zero_bg_and_d4_shortcut
#print axioms CertifiedStrategySelectionV26.H12_causal_epistemic_horizon_synthesis
#print axioms CertifiedStrategySelectionV26.H12_rule110_algebraic_xor_gate
#print axioms CertifiedStrategySelectionV26.H12_temporal_subject_period2_and_anomaly_trigger
