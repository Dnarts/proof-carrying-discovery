/-!
Full Tier-0 (DFA(S)) -> Tier-1 (1-DCA) Separation in Lean 4
===========================================================
Status: CANDIDATE / NOT_TYPECHECKED_IN_SANDBOX
(Standalone core Lean 4 module: zero external imports, zero `sorry`,
zero `native_decide`, zero custom global `axiom` declarations.)

Establishes end-to-end in a single kernel-checked file:
1. `pigeonhole`: Pigeonhole Principle on `Fin (n + 1) → Fin n`.
2. `mn_sound`: Myhill-Nerode impossibility theorem for `DFA α S`.
3. `OneDCA`: real-time deterministic one-counter automaton (Tier-1).
4. `dfaTo1DCAClosedEnv`: concrete instantiation of `ClosedEnv` whose
   Tier-0 is `DFA α S` and Tier-1 is `OneDCA α S'`, with `ax2_sound`
   proved via `mn_sound` and `ax4_privilege` proved for `defaultCtrl`.
5. `T1_dfa_no_false_escalation`: unconditional safety theorem for `DFA(S)`.
6. `anbn_not_dfa`: `∀ S, ¬ ∃ d : DFA Bool S, ∀ x, d.accepts x = langAnBn x`.
7. `anbn1DCA_accepts`: constructive 3-state `OneDCA Bool 3` recognizing `langAnBn`.
8. `anbn_tier_separation`: strict class separation `langAnBn ∉ DFA(S) ∧ langAnBn ∈ 1-DCA`.
-/

namespace DFAto1DCASeparation

/-! ## Part 1. Pigeonhole Principle on Fin -/

private def skipLast {n : Nat} (lastVal : Nat) (hLast : lastVal < n + 1)
    (v : Nat) (hv : v < n + 1) (hNe : v ≠ lastVal) : Fin n :=
  if h : v < lastVal then
    ⟨v, by omega⟩
  else
    ⟨v - 1, by omega⟩

private theorem skipLast_inj {n : Nat} {lastVal : Nat} (hLast : lastVal < n + 1)
    {v1 v2 : Nat} (hv1 : v1 < n + 1) (hv2 : v2 < n + 1)
    (hNe1 : v1 ≠ lastVal) (hNe2 : v2 ≠ lastVal)
    (hEq : skipLast lastVal hLast v1 hv1 hNe1 = skipLast lastVal hLast v2 hv2 hNe2) :
    v1 = v2 := by
  have hVal : (skipLast lastVal hLast v1 hv1 hNe1).val =
              (skipLast lastVal hLast v2 hv2 hNe2).val := congrArg Fin.val hEq
  dsimp [skipLast] at hVal
  split at hVal <;> split at hVal <;> dsimp at hVal <;> omega

/-- Pigeonhole principle: any map `Fin (n + 1) → Fin n` has a collision. -/
theorem pigeonhole : ∀ {n : Nat} (f : Fin (n + 1) → Fin n),
    ∃ i j : Fin (n + 1), i ≠ j ∧ f i = f j
  | 0, f => nomatch f ⟨0, by omega⟩
  | n + 1, f => by
    let lastIdx : Fin (n + 2) := ⟨n + 1, by omega⟩
    by_cases hHit : ∃ k : Fin (n + 1), f ⟨k.val, by omega⟩ = f lastIdx
    · rcases hHit with ⟨k, hk⟩
      refine ⟨⟨k.val, by omega⟩, lastIdx, ?_, hk⟩
      intro hEq
      have hVal : k.val = n + 1 := congrArg Fin.val hEq
      have hkLt : k.val < n + 1 := k.isLt
      omega
    · have hNeLast : ∀ k : Fin (n + 1), (f ⟨k.val, by omega⟩).val ≠ (f lastIdx).val := by
        intro k hEq
        apply hHit
        exact ⟨k, Fin.ext hEq⟩
      let g : Fin (n + 1) → Fin n := fun k =>
        skipLast (f lastIdx).val (f lastIdx).isLt
          (f ⟨k.val, by omega⟩).val (f ⟨k.val, by omega⟩).isLt (hNeLast k)
      rcases pigeonhole g with ⟨i, j, hNeIJ, hEqG⟩
      have hValEq : (f ⟨i.val, by omega⟩).val = (f ⟨j.val, by omega⟩).val :=
        skipLast_inj (f lastIdx).isLt
          (f ⟨i.val, by omega⟩).isLt (f ⟨j.val, by omega⟩).isLt
          (hNeLast i) (hNeLast j) hEqG
      refine ⟨⟨i.val, by omega⟩, ⟨j.val, by omega⟩, ?_, Fin.ext hValEq⟩
      intro hEqIdx
      apply hNeIJ
      have hValIJ : i.val = j.val := congrArg (Fin.val : Fin (n + 2) → Nat) hEqIdx
      exact Fin.ext hValIJ


/-! ## Part 2. Tier-0 (DFA) and Myhill-Nerode Impossibility Theorem -/

abbrev Lang (α : Type) := List α → Bool

structure DFA (α : Type) (S : Nat) where
  init : Fin S
  step : Fin S → α → Fin S
  accept : Fin S → Bool

def DFA.runFrom {α : Type} {S : Nat} (d : DFA α S) : Fin S → List α → Fin S
  | q, [] => q
  | q, a :: w => d.runFrom (d.step q a) w

def DFA.run {α : Type} {S : Nat} (d : DFA α S) (w : List α) : Fin S :=
  d.runFrom d.init w

def DFA.accepts {α : Type} {S : Nat} (d : DFA α S) (w : List α) : Bool :=
  d.accept (d.run w)

theorem DFA.runFrom_append {α : Type} {S : Nat} (d : DFA α S) :
    ∀ (q : Fin S) (u v : List α),
      d.runFrom q (u ++ v) = d.runFrom (d.runFrom q u) v
  | _, [], _ => rfl
  | q, a :: u, v => d.runFrom_append (d.step q a) u v

theorem DFA.accepts_congr {α : Type} {S : Nat} (d : DFA α S)
    (u1 u2 v : List α) (hState : d.run u1 = d.run u2) :
    d.accepts (u1 ++ v) = d.accepts (u2 ++ v) := by
  simp only [DFA.accepts, DFA.run, DFA.runFrom_append]
  simp only [DFA.run] at hState
  rw [hState]

structure MNWitness (α : Type) (S : Nat) where
  prefixes : Fin (S + 1) → List α
  sep : Fin (S + 1) → Fin (S + 1) → List α

def validMNWitness {α : Type} {S : Nat} (L : Lang α) (w : MNWitness α S) : Prop :=
  ∀ i j : Fin (S + 1), i ≠ j →
    L (w.prefixes i ++ w.sep i j) ≠ L (w.prefixes j ++ w.sep i j)

theorem mn_sound {α : Type} {S : Nat} (L : Lang α) (w : MNWitness α S)
    (hValid : validMNWitness L w) :
    ¬ ∃ d : DFA α S, ∀ x : List α, d.accepts x = L x := by
  rintro ⟨d, hRec⟩
  let f : Fin (S + 1) → Fin S := fun i => d.run (w.prefixes i)
  rcases pigeonhole f with ⟨i, j, hNe, hEq⟩
  have hAcc : d.accepts (w.prefixes i ++ w.sep i j) =
              d.accepts (w.prefixes j ++ w.sep i j) :=
    d.accepts_congr (w.prefixes i) (w.prefixes j) (w.sep i j) hEq
  have hLi : d.accepts (w.prefixes i ++ w.sep i j) = L (w.prefixes i ++ w.sep i j) := hRec _
  have hLj : d.accepts (w.prefixes j ++ w.sep i j) = L (w.prefixes j ++ w.sep i j) := hRec _
  have hL : L (w.prefixes i ++ w.sep i j) = L (w.prefixes j ++ w.sep i j) := by
    rw [← hLi, ← hLj]
    exact hAcc
  exact hValid i j hNe hL


/-! ## Part 3. Tier-1: Real-Time Deterministic One-Counter Automaton (1-DCA) -/

inductive CounterOp where
  | inc
  | dec
  | nop
  deriving DecidableEq, Repr

def CounterOp.apply : CounterOp → Nat → Nat
  | CounterOp.inc, c => c + 1
  | CounterOp.dec, c => c - 1
  | CounterOp.nop, c => c

/-- Real-time deterministic one-counter automaton with S control states. -/
structure OneDCA (α : Type) (S : Nat) where
  init : Fin S
  /-- Transition function taking (state, isZero, symbol) -> (nextState, counterOp). -/
  step : Fin S → Bool → α → Fin S × CounterOp
  /-- Acceptance predicate taking (finalState, isZero). -/
  accept : Fin S → Bool → Bool

def OneDCA.runFrom {α : Type} {S : Nat} (m : OneDCA α S) :
    Fin S → Nat → List α → Fin S × Nat
  | q, c, [] => (q, c)
  | q, c, a :: w =>
    let r := m.step q (c == 0) a
    m.runFrom r.1 (r.2.apply c) w

def OneDCA.accepts {α : Type} {S : Nat} (m : OneDCA α S) (w : List α) : Bool :=
  let r := m.runFrom m.init 0 w
  m.accept r.1 (r.2 == 0)


/-! ## Part 4. Concrete ClosedEnv (Tier-0 = DFA(S), Tier-1 = 1-DCA) and Safety T1 -/

inductive MemClass where
  | tier0
  | tier1
  deriving DecidableEq, Repr

inductive StructSignal (Witness : Type) where
  | none
  | stopStruct (w : Witness)
  deriving DecidableEq, Repr

inductive ResSignal where
  | ok
  | stopRes
  deriving DecidableEq, Repr

inductive CtrlAction (Witness : Type) where
  | continueSearch
  | changeStrategy
  | haltTimeout
  | haltUnsat (w : Witness)
  | escalateMemory (w : Witness)
  deriving DecidableEq, Repr

structure ClosedEnv (Task Prog Witness : Type) where
  verifies : Prog → Task → Prop
  inClass : MemClass → Prog → Prop
  validWitness : MemClass → Task → Witness → Prop
  ax2_sound :
    ∀ (m : MemClass) (task : Task) (w : Witness),
      validWitness m task w → ¬ ∃ p : Prog, inClass m p ∧ verifies p task
  sensStruct : MemClass → Task → StructSignal Witness
  sensStruct_certified :
    ∀ (m : MemClass) (task : Task) (w : Witness),
      sensStruct m task = StructSignal.stopStruct w → validWitness m task w
  ctrl : StructSignal Witness → ResSignal → CtrlAction Witness
  ax4_privilege :
    ∀ (ss : StructSignal Witness) (rs : ResSignal) (w : Witness),
      ctrl ss rs = CtrlAction.escalateMemory w → ss = StructSignal.stopStruct w

theorem T1_no_false_escalation
    {Task Prog Witness : Type}
    (env : ClosedEnv Task Prog Witness)
    (task : Task)
    (hSolvable : ∃ p : Prog, env.inClass MemClass.tier0 p ∧ env.verifies p task)
    (rs : ResSignal)
    (w : Witness) :
    env.ctrl (env.sensStruct MemClass.tier0 task) rs ≠ CtrlAction.escalateMemory w := by
  intro hEsc
  have hStop : env.sensStruct MemClass.tier0 task = StructSignal.stopStruct w :=
    env.ax4_privilege (env.sensStruct MemClass.tier0 task) rs w hEsc
  have hValid : env.validWitness MemClass.tier0 task w :=
    env.sensStruct_certified MemClass.tier0 task w hStop
  have hUnsolvable : ¬ ∃ p : Prog, env.inClass MemClass.tier0 p ∧ env.verifies p task :=
    env.ax2_sound MemClass.tier0 task w hValid
  exact hUnsolvable hSolvable

/-- Programs in the concrete two-tier space: Tier-0 = DFA(S), Tier-1 = OneDCA(S1). -/
inductive AutoProg (α : Type) (S S1 : Nat) where
  | dfa (d : DFA α S)
  | dca (m : OneDCA α S1)

def autoVerifies {α : Type} {S S1 : Nat} : AutoProg α S S1 → Lang α → Prop
  | AutoProg.dfa d, L => ∀ x, d.accepts x = L x
  | AutoProg.dca m, L => ∀ x, m.accepts x = L x

def autoInClass {α : Type} {S S1 : Nat} : MemClass → AutoProg α S S1 → Prop
  | MemClass.tier0, AutoProg.dfa _ => True
  | MemClass.tier0, AutoProg.dca _ => False
  | MemClass.tier1, _ => True

def autoValidWitness {α : Type} {S : Nat} : MemClass → Lang α → MNWitness α S → Prop
  | MemClass.tier0, L, w => validMNWitness L w
  | MemClass.tier1, _, _ => False

def defaultCtrl {Witness : Type} : StructSignal Witness → ResSignal → CtrlAction Witness
  | StructSignal.stopStruct w, _ => CtrlAction.escalateMemory w
  | StructSignal.none, ResSignal.stopRes => CtrlAction.haltTimeout
  | StructSignal.none, ResSignal.ok => CtrlAction.continueSearch

def dfaTo1DCAClosedEnv {α : Type} (S S1 : Nat)
    (sens : MemClass → Lang α → StructSignal (MNWitness α S))
    (hCert : ∀ m L w, sens m L = StructSignal.stopStruct w → autoValidWitness m L w) :
    ClosedEnv (Lang α) (AutoProg α S S1) (MNWitness α S) where
  verifies := autoVerifies
  inClass := autoInClass
  validWitness := autoValidWitness
  ax2_sound := by
    intro m L w hValid
    cases m with
    | tier0 =>
      rintro ⟨p, hIn, hVer⟩
      cases p with
      | dfa d => exact mn_sound L w hValid ⟨d, hVer⟩
      | dca _ => exact False.elim hIn
    | tier1 =>
      exact False.elim hValid
  sensStruct := sens
  sensStruct_certified := hCert
  ctrl := defaultCtrl
  ax4_privilege := by
    intro ss rs w hEsc
    cases ss with
    | none =>
      cases rs <;> simp [defaultCtrl] at hEsc
    | stopStruct w' =>
      simp only [defaultCtrl, CtrlAction.escalateMemory.injEq] at hEsc
      rw [hEsc]

theorem T1_dfa_no_false_escalation {α : Type} (S S1 : Nat)
    (sens : MemClass → Lang α → StructSignal (MNWitness α S))
    (hCert : ∀ m L w, sens m L = StructSignal.stopStruct w → autoValidWitness m L w)
    (L : Lang α)
    (hRegS : ∃ d : DFA α S, ∀ x, d.accepts x = L x)
    (rs : ResSignal)
    (w : MNWitness α S) :
    (dfaTo1DCAClosedEnv S S1 sens hCert).ctrl (sens MemClass.tier0 L) rs ≠
      CtrlAction.escalateMemory w := by
  rcases hRegS with ⟨d, hd⟩
  exact T1_no_false_escalation (dfaTo1DCAClosedEnv S S1 sens hCert) L
    ⟨AutoProg.dfa d, trivial, hd⟩ rs w


/-! ## Part 5. End-to-End Separation Witness: {a^n b^n | n ≥ 0} -/

def isAll (b : Bool) : List Bool → Bool
  | [] => true
  | x :: xs => (x == b) && isAll b xs

def matchAnBnAux : Nat → List Bool → Bool
  | 0, [] => true
  | _ + 1, [] => false
  | k, false :: xs => matchAnBnAux (k + 1) xs
  | 0, true :: _ => false
  | k + 1, true :: xs => (k == xs.length) && isAll true xs

def langAnBn (w : List Bool) : Bool := matchAnBnAux 0 w

theorem isAll_replicate (b : Bool) : ∀ (n : Nat), isAll b (List.replicate n b) = true
  | 0 => rfl
  | n + 1 => by
    simp only [List.replicate_succ, isAll, beq_self_eq_true, Bool.true_and]
    exact isAll_replicate b n

theorem matchAnBnAux_replicate_false : ∀ (i k : Nat) (v : List Bool),
    matchAnBnAux k (List.replicate i false ++ v) = matchAnBnAux (k + i) v
  | 0, _, _ => rfl
  | i + 1, k, v => by
    simp only [List.replicate_succ, List.cons_append, matchAnBnAux]
    rw [matchAnBnAux_replicate_false i (k + 1) v]
    have hEq : k + 1 + i = k + (i + 1) := by omega
    rw [hEq]

theorem langAnBn_replicate (i j : Nat) :
    langAnBn (List.replicate i false ++ List.replicate j true) = (i == j) := by
  unfold langAnBn
  rw [matchAnBnAux_replicate_false i 0 (List.replicate j true)]
  have hZero : 0 + i = i := Nat.zero_add i
  rw [hZero]
  cases j with
  | zero =>
    cases i <;> rfl
  | succ m =>
    cases i with
    | zero => rfl
    | succ k =>
      simp [List.replicate_succ, matchAnBnAux, List.length_replicate, isAll_replicate]

def anbnWitness (S : Nat) : MNWitness Bool S where
  prefixes := fun i => List.replicate i.val false
  sep := fun i _ => List.replicate i.val true

theorem anbn_valid_mn_witness (S : Nat) : validMNWitness langAnBn (anbnWitness S) := by
  intro i j hNe
  simp only [anbnWitness, langAnBn_replicate]
  have hValNe : j.val ≠ i.val := fun h => hNe (Fin.ext h.symm)
  simp [hValNe]

/-- Lower bound: no S-state DFA recognizes `langAnBn`. -/
theorem anbn_not_dfa (S : Nat) :
    ¬ ∃ d : DFA Bool S, ∀ x : List Bool, d.accepts x = langAnBn x :=
  mn_sound langAnBn (anbnWitness S) (anbn_valid_mn_witness S)

/-! ### Constructive 3-state 1-DCA recognizing `langAnBn` -/

def anbn1DCAStep (q : Fin 3) (isZero : Bool) (a : Bool) : Fin 3 × CounterOp :=
  match q.val, a, isZero with
  | 0, false, _ => (⟨0, by omega⟩, CounterOp.inc)
  | 0, true, false => (⟨1, by omega⟩, CounterOp.dec)
  | 1, true, false => (⟨1, by omega⟩, CounterOp.dec)
  | _, _, _ => (⟨2, by omega⟩, CounterOp.nop)

def anbn1DCAAccept (q : Fin 3) (isZero : Bool) : Bool :=
  match q.val, isZero with
  | 0, true => true
  | 1, true => true
  | _, _ => false

def anbn1DCA : OneDCA Bool 3 where
  init := ⟨0, by omega⟩
  step := anbn1DCAStep
  accept := anbn1DCAAccept

private def runAcc (q : Fin 3) (c : Nat) (w : List Bool) : Bool :=
  let r := anbn1DCA.runFrom q c w
  anbn1DCA.accept r.1 (r.2 == 0)

private theorem anbn1DCA_dead : ∀ (w : List Bool) (c : Nat),
    runAcc ⟨2, by omega⟩ c w = false
  | [], _ => rfl
  | a :: w, c => by
    have hStep : runAcc ⟨2, by omega⟩ c (a :: w) = runAcc ⟨2, by omega⟩ c w := rfl
    rw [hStep]
    exact anbn1DCA_dead w c

private theorem anbn1DCA_qB : ∀ (w : List Bool) (c : Nat),
    runAcc ⟨1, by omega⟩ c w = ((c == w.length) && isAll true w)
  | [], c => by
    cases c <;> rfl
  | false :: xs, c => by
    have hStep : runAcc ⟨1, by omega⟩ c (false :: xs) = runAcc ⟨2, by omega⟩ c xs := rfl
    rw [hStep, anbn1DCA_dead]
    simp [isAll]
  | true :: xs, c => by
    cases c with
    | zero =>
      have hStep : runAcc ⟨1, by omega⟩ 0 (true :: xs) = runAcc ⟨2, by omega⟩ 0 xs := rfl
      rw [hStep, anbn1DCA_dead]
      rfl
    | succ k =>
      have hStep : runAcc ⟨1, by omega⟩ (k + 1) (true :: xs) = runAcc ⟨1, by omega⟩ k xs := rfl
      rw [hStep, anbn1DCA_qB xs k]
      simp [isAll]

private theorem anbn1DCA_qA : ∀ (w : List Bool) (c : Nat),
    runAcc ⟨0, by omega⟩ c w = matchAnBnAux c w
  | [], c => by
    cases c <;> rfl
  | false :: xs, c => by
    have hStep : runAcc ⟨0, by omega⟩ c (false :: xs) = runAcc ⟨0, by omega⟩ (c + 1) xs := rfl
    rw [hStep, anbn1DCA_qA xs (c + 1)]
    cases c <;> rfl
  | true :: xs, c => by
    cases c with
    | zero =>
      have hStep : runAcc ⟨0, by omega⟩ 0 (true :: xs) = runAcc ⟨2, by omega⟩ 0 xs := rfl
      rw [hStep, anbn1DCA_dead]
      rfl
    | succ k =>
      have hStep : runAcc ⟨0, by omega⟩ (k + 1) (true :: xs) = runAcc ⟨1, by omega⟩ k xs := rfl
      rw [hStep, anbn1DCA_qB xs k]
      rfl

/-- Upper bound: the 3-state 1-DCA `anbn1DCA` recognizes `langAnBn` exactly. -/
theorem anbn1DCA_accepts (w : List Bool) :
    anbn1DCA.accepts w = langAnBn w :=
  anbn1DCA_qA w 0

/--
Strict Tier-0 / Tier-1 Class Separation Theorem:
`langAnBn` is NOT recognizable by any S-state DFA, yet IS constructively
recognized by the 3-state real-time one-counter automaton `anbn1DCA`.
-/
theorem anbn_tier_separation :
    (∀ S : Nat, ¬ ∃ d : DFA Bool S, ∀ x : List Bool, d.accepts x = langAnBn x) ∧
    (∃ m : OneDCA Bool 3, ∀ x : List Bool, m.accepts x = langAnBn x) :=
  ⟨anbn_not_dfa, ⟨anbn1DCA, anbn1DCA_accepts⟩⟩

end DFAto1DCASeparation