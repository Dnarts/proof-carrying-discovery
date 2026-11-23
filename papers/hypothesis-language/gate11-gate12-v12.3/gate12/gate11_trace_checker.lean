/-
  Gate 11 — Certified Trace Verifier & Typed 1-DCA DSL in Pure Lean 4 Core
  (Zero External Dependencies, Complete Proofs).

  Verify locally with:
      lean gate11_trace_checker.lean

  Eliminates Python from the Trusted Computing Base (TCB) for Gate 11 traces:
    1. `checkMNCert_sound`: if the executable checker `checkMNCert` returns `true`
       on finite observation trace `obs`, then NO `DFA k` agrees with `obs`.
    2. `checkDFATrace_sound`: if `checkDFATrace M obs = true`, then `M` agrees
       with every `(w, a) ∈ obs`.
    3. `checkCounterTrace_sound`: typed 1-DCA DSL (`CounterProgram`) with
       guaranteed termination (`w.length` steps) and proven agreement on `obs`.
    4. `checkEscalatedTrace_sound`: unified soundness theorem certifying BOTH
       impossibility of any `DFA k` AND exact agreement of the escalated `1-DCA`.
    5. `sample_0n1n_trace_verified` & `sample_0n1n_no_dfa4`: concrete execution
       of the certified checker via `by decide` on a Gate 11 `0^n 1^n` trace.
-/

namespace Gate11TraceChecker

abbrev Word := List Bool
abbrev Obs  := List (Word × Bool)

structure DFA (k : Nat) where
  start  : Fin k
  step   : Fin k → Bool → Fin k
  accept : Fin k → Bool

def DFA.runFrom {k : Nat} (M : DFA k) : Fin k → Word → Fin k
  | s, []      => s
  | s, c :: ws => M.runFrom (M.step s c) ws

def DFA.eval {k : Nat} (M : DFA k) (w : Word) : Bool :=
  M.accept (M.runFrom M.start w)

theorem dfa_runFrom_append {k : Nat} (M : DFA k) :
    ∀ (u v : Word) (s : Fin k),
      M.runFrom s (u ++ v) = M.runFrom (M.runFrom s u) v
  | [],      _, _ => rfl
  | c :: us, v, s => dfa_runFrom_append M us v (M.step s c)

/-! ## Constructive Pigeonhole Principle (Pure Core) -/

private def findFin : (n : Nat) → (P : Fin n → Prop) → [DecidablePred P] →
    Option { i : Fin n // P i }
  | 0,     _, _ => none
  | n + 1, P, _ =>
    if h : P ⟨n, Nat.lt_succ_self n⟩ then
      some ⟨⟨n, Nat.lt_succ_self n⟩, h⟩
    else
      match findFin n (fun i => P ⟨i.val, Nat.lt_trans i.isLt (Nat.lt_succ_self n)⟩) with
      | some ⟨i, hi⟩ => some ⟨⟨i.val, Nat.lt_trans i.isLt (Nat.lt_succ_self n)⟩, hi⟩
      | none         => none

private theorem findFin_none_spec :
    ∀ (n : Nat) (P : Fin n → Prop) [DecidablePred P],
      findFin n P = none → ∀ i : Fin n, ¬ P i
  | 0,     _, _, _, i => Fin.elim0 i
  | n + 1, P, _, hnone, i => by
    unfold findFin at hnone
    split at hnone
    · cases hnone
    · rename_i hlast
      cases hrec : findFin n (fun j => P ⟨j.val, Nat.lt_trans j.isLt (Nat.lt_succ_self n)⟩) with
      | some _ =>
        rw [hrec] at hnone
        cases hnone
      | none =>
        have hall := findFin_none_spec n
          (fun j => P ⟨j.val, Nat.lt_trans j.isLt (Nat.lt_succ_self n)⟩) hrec
        by_cases hi : i.val = n
        · have heq : i = ⟨n, Nat.lt_succ_self n⟩ := Fin.ext hi
          rw [heq]
          exact hlast
        · exact hall ⟨i.val, by omega⟩

theorem pigeonhole_fin :
    ∀ (k : Nat) (f : Fin (k + 1) → Fin k),
      ∃ i j : Fin (k + 1), i ≠ j ∧ f i = f j
  | 0, f => Fin.elim0 (f ⟨0, Nat.lt_succ_self 0⟩)
  | n + 1, f => by
    let last : Fin (n + 2) := ⟨n + 1, Nat.lt_succ_self (n + 1)⟩
    let c : Fin (n + 1) := f last
    let P : Fin (n + 1) → Prop :=
      fun i => f ⟨i.val, Nat.lt_trans i.isLt (Nat.lt_succ_self (n + 1))⟩ = c
    cases hfind : findFin (n + 1) P with
    | some val =>
      rcases val with ⟨i, hi⟩
      refine ⟨⟨i.val, Nat.lt_trans i.isLt (Nat.lt_succ_self (n + 1))⟩, last, ?_, hi⟩
      intro heq
      have hval : i.val = n + 1 := congrArg (fun x : Fin (n + 2) => x.val) heq
      omega
    | none =>
      have hneq : ∀ i : Fin (n + 1),
          f ⟨i.val, Nat.lt_trans i.isLt (Nat.lt_succ_self (n + 1))⟩ ≠ c :=
        findFin_none_spec (n + 1) P hfind
      let g : Fin (n + 1) → Fin n := fun i =>
        let y := f ⟨i.val, Nat.lt_trans i.isLt (Nat.lt_succ_self (n + 1))⟩
        have hy : y.val ≠ c.val := fun h => hneq i (Fin.ext h)
        if hlt : y.val < c.val then
          ⟨y.val, by omega⟩
        else
          ⟨y.val - 1, by omega⟩
      rcases pigeonhole_fin n g with ⟨a, b, hab, hgab⟩
      refine ⟨⟨a.val, Nat.lt_trans a.isLt (Nat.lt_succ_self (n + 1))⟩,
              ⟨b.val, Nat.lt_trans b.isLt (Nat.lt_succ_self (n + 1))⟩, ?_, ?_⟩
      · intro heq
        apply hab
        exact Fin.ext (congrArg (fun x : Fin (n + 2) => x.val) heq)
      · have hya : (f ⟨a.val, Nat.lt_trans a.isLt (Nat.lt_succ_self (n + 1))⟩).val ≠ c.val :=
          fun h => hneq a (Fin.ext h)
        have hyb : (f ⟨b.val, Nat.lt_trans b.isLt (Nat.lt_succ_self (n + 1))⟩).val ≠ c.val :=
          fun h => hneq b (Fin.ext h)
        have hval : (g a).val = (g b).val := congrArg (fun x : Fin n => x.val) hgab
        dsimp only [g] at hval
        apply Fin.ext
        split at hval <;> split at hval <;> dsimp only at hval <;> omega

/-! ## Executable Trace Lookup & Certified Myhill-Nerode Checker -/

def lookupObs : Obs → Word → Option Bool
  | [],               _ => none
  | (w', a) :: rest,  w => if w' == w then some a else lookupObs rest w

theorem lookupObs_mem : ∀ (obs : Obs) (w : Word) (a : Bool),
    lookupObs obs w = some a → (w, a) ∈ obs
  | [], _, _, h => by cases h
  | (w', a') :: rest, w, a, h => by
    unfold lookupObs at h
    split at h
    · rename_i hbeq
      have hw : w' = w := eq_of_beq hbeq
      cases h
      rw [hw]
      exact List.Mem.head rest
    · exact List.Mem.tail (w', a') (lookupObs_mem rest w a h)

def checkMNPair (obs : Obs) (u v suf : Word) : Bool :=
  match lookupObs obs (u ++ suf), lookupObs obs (v ++ suf) with
  | some a1, some a2 => a1 != a2
  | _,       _       => false

theorem checkMNPair_sound (obs : Obs) (u v suf : Word)
    (h : checkMNPair obs u v suf = true) :
    ∃ a1 a2 : Bool, (u ++ suf, a1) ∈ obs ∧ (v ++ suf, a2) ∈ obs ∧ a1 ≠ a2 := by
  unfold checkMNPair at h
  cases h1 : lookupObs obs (u ++ suf) with
  | none => rw [h1] at h; cases h
  | some a1 =>
    rw [h1] at h
    cases h2 : lookupObs obs (v ++ suf) with
    | none => rw [h2] at h; cases h
    | some a2 =>
      rw [h2] at h
      refine ⟨a1, a2, lookupObs_mem obs (u ++ suf) a1 h1, lookupObs_mem obs (v ++ suf) a2 h2, ?_⟩
      intro heq
      subst heq
      cases a1 <;> cases h

/-- Executable Myhill-Nerode certificate checker over a finite observation trace. -/
def checkMNCert (k : Nat) (obs : Obs)
    (prefs : Fin (k + 1) → Word)
    (sufs  : Fin (k + 1) → Fin (k + 1) → Word) : Bool :=
  decide (∀ i j : Fin (k + 1), i ≠ j →
    checkMNPair obs (prefs i) (prefs j) (sufs i j) = true)

/-- Theorem 1 (Certified Checker Soundness for Myhill-Nerode):
    If `checkMNCert` returns `true` on `obs`, then NO `DFA k` agrees with `obs`. -/
theorem checkMNCert_sound
    (k : Nat) (obs : Obs)
    (prefs : Fin (k + 1) → Word)
    (sufs  : Fin (k + 1) → Fin (k + 1) → Word)
    (hchk  : checkMNCert k obs prefs sufs = true) :
    ¬ ∃ M : DFA k, ∀ p ∈ obs, M.eval p.1 = p.2 := by
  have hall := of_decide_eq_true hchk
  rintro ⟨M, hM⟩
  let stateOf : Fin (k + 1) → Fin k := fun i => M.runFrom M.start (prefs i)
  rcases pigeonhole_fin k stateOf with ⟨i, j, hij, hst⟩
  have hpair := hall i j hij
  rcases checkMNPair_sound obs (prefs i) (prefs j) (sufs i j) hpair with ⟨a1, a2, hm1, hm2, hne⟩
  have he1 : M.eval (prefs i ++ sufs i j) = a1 := hM (prefs i ++ sufs i j, a1) hm1
  have he2 : M.eval (prefs j ++ sufs i j) = a2 := hM (prefs j ++ sufs i j, a2) hm2
  have hsame : M.eval (prefs i ++ sufs i j) = M.eval (prefs j ++ sufs i j) := by
    unfold DFA.eval
    rw [dfa_runFrom_append, dfa_runFrom_append]
    change M.accept (M.runFrom (stateOf i) (sufs i j)) =
           M.accept (M.runFrom (stateOf j) (sufs i j))
    rw [hst]
  rw [he1, he2] at hsame
  exact hne hsame

/-! ## Typed 1-DCA DSL & Executable Agreement Checkers -/

inductive CounterOp where
  | inc
  | dec
  | keep

/-- Typed one-counter automaton DSL (total, guaranteed termination in `w.length` steps). -/
structure CounterProgram (m : Nat) where
  startPhase : Fin m
  step       : Fin m → Bool → Bool → Option (Fin m × CounterOp)
  accept     : Fin m → Bool → Bool

def applyCounterOp (c : Nat) : CounterOp → Option Nat
  | .inc  => some (c + 1)
  | .keep => some c
  | .dec  => match c with
             | 0     => none
             | c + 1 => some c

def CounterProgram.runFrom {m : Nat} (C : CounterProgram m) :
    Option (Fin m × Nat) → Word → Option (Fin m × Nat)
  | st,             []      => st
  | none,           _ :: ws => C.runFrom none ws
  | some (ph, c),   b :: ws =>
    match C.step ph b (c == 0) with
    | none           => C.runFrom none ws
    | some (ph', op) =>
      match applyCounterOp c op with
      | none    => C.runFrom none ws
      | some c' => C.runFrom (some (ph', c')) ws

def CounterProgram.eval {m : Nat} (C : CounterProgram m) (w : Word) : Bool :=
  match C.runFrom (some (C.startPhase, 0)) w with
  | none         => false
  | some (ph, c) => C.accept ph (c == 0)

def checkAllObs (f : Word → Bool) : Obs → Bool
  | []              => true
  | (w, a) :: rest  => (f w == a) && checkAllObs f rest

theorem checkAllObs_sound (f : Word → Bool) :
    ∀ (obs : Obs), checkAllObs f obs = true → ∀ p ∈ obs, f p.1 = p.2
  | [], _, _, hp => by cases hp
  | (w, a) :: rest, h, p, hp => by
    unfold checkAllObs at h
    cases hfa : (f w == a) with
    | false => rw [hfa] at h; cases h
    | true =>
      rw [hfa] at h
      cases hp with
      | head => exact eq_of_beq hfa
      | tail _ hmem => exact checkAllObs_sound f rest h p hmem

/-- Theorem 2: Soundness of executable DFA trace checker. -/
def checkDFATrace {k : Nat} (M : DFA k) (obs : Obs) : Bool :=
  checkAllObs M.eval obs

theorem checkDFATrace_sound {k : Nat} (M : DFA k) (obs : Obs)
    (h : checkDFATrace M obs = true) : ∀ p ∈ obs, M.eval p.1 = p.2 :=
  checkAllObs_sound M.eval obs h

/-- Theorem 3: Soundness of executable 1-DCA trace checker. -/
def checkCounterTrace {m : Nat} (C : CounterProgram m) (obs : Obs) : Bool :=
  checkAllObs C.eval obs

theorem checkCounterTrace_sound {m : Nat} (C : CounterProgram m) (obs : Obs)
    (h : checkCounterTrace C obs = true) : ∀ p ∈ obs, C.eval p.1 = p.2 :=
  checkAllObs_sound C.eval obs h

/-- Unified executable checker for an escalated Gate 11 trace (DFA(<=k) refuted + 1-DCA accepted). -/
def checkEscalatedTrace {k m : Nat} (obs : Obs)
    (prefs : Fin (k + 1) → Word)
    (sufs  : Fin (k + 1) → Fin (k + 1) → Word)
    (C     : CounterProgram m) : Bool :=
  checkMNCert k obs prefs sufs && checkCounterTrace C obs

/-- Theorem 4 (Unified Certified Trace Soundness):
    If `checkEscalatedTrace` returns `true`, then BOTH:
      (a) no `DFA k` agrees with `obs`, AND
      (b) `C` agrees with every observation in `obs`. -/
theorem checkEscalatedTrace_sound {k m : Nat} (obs : Obs)
    (prefs : Fin (k + 1) → Word)
    (sufs  : Fin (k + 1) → Fin (k + 1) → Word)
    (C     : CounterProgram m)
    (h     : checkEscalatedTrace obs prefs sufs C = true) :
    (¬ ∃ M : DFA k, ∀ p ∈ obs, M.eval p.1 = p.2) ∧
    (∀ p ∈ obs, C.eval p.1 = p.2) := by
  unfold checkEscalatedTrace at h
  cases hmn : checkMNCert k obs prefs sufs with
  | false => rw [hmn] at h; cases h
  | true =>
    rw [hmn] at h
    exact ⟨checkMNCert_sound k obs prefs sufs hmn, checkCounterTrace_sound C obs h⟩

/-! ## Concrete Execution on a Gate 11 `0^n 1^n` Trace (Verified by `decide`) -/

def dsl_0n1n : CounterProgram 2 where
  startPhase := ⟨0, by decide⟩
  step := fun ph b _isZero =>
    match ph.val, b with
    | 0, false => some (⟨0, by decide⟩, .inc)
    | 0, true  => some (⟨1, by decide⟩, .dec)
    | _, false => none
    | _, true  => some (⟨1, by decide⟩, .dec)
  accept := fun _ph isZero => isZero

def samplePrefs : Fin 5 → Word := fun i => List.replicate i.val false
def sampleSufs  : Fin 5 → Fin 5 → Word := fun i _j => List.replicate i.val true

/-- Concrete finite observation trace covering all 25 `(0^i ++ 1^j)` probes plus long words. -/
def sampleObs_0n1n : Obs :=
  [ ([], true),
    ([true], false), ([true, true], false), ([true, true, true], false), ([true, true, true, true], false),
    ([false], false), ([false, true], true), ([false, true, true], false), ([false, true, true, true], false), ([false, true, true, true, true], false),
    ([false, false], false), ([false, false, true], false), ([false, false, true, true], true), ([false, false, true, true, true], false), ([false, false, true, true, true, true], false),
    ([false, false, false], false), ([false, false, false, true], false), ([false, false, false, true, true], false), ([false, false, false, true, true, true], true), ([false, false, false, true, true, true, true], false),
    ([false, false, false, false], false), ([false, false, false, false, true], false), ([false, false, false, false, true, true], false), ([false, false, false, false, true, true, true], false), ([false, false, false, false, true, true, true, true], true),
    (List.replicate 8 false ++ List.replicate 8 true, true),
    (List.replicate 9 false ++ List.replicate 8 true, false) ]

/-- Theorem 5a: The certified Lean checker accepts the concrete `0^n 1^n` trace by computation. -/
theorem sample_0n1n_trace_verified :
    checkEscalatedTrace sampleObs_0n1n samplePrefs sampleSufs dsl_0n1n = true := by
  decide

/-- Theorem 5b: Direct corollary — NO 4-state DFA agrees with `sampleObs_0n1n`, and `dsl_0n1n` agrees with all of it. -/
theorem sample_0n1n_certified_corollary :
    (¬ ∃ M : DFA 4, ∀ p ∈ sampleObs_0n1n, M.eval p.1 = p.2) ∧
    (∀ p ∈ sampleObs_0n1n, dsl_0n1n.eval p.1 = p.2) :=
  checkEscalatedTrace_sound sampleObs_0n1n samplePrefs sampleSufs dsl_0n1n sample_0n1n_trace_verified

end Gate11TraceChecker

#print axioms Gate11TraceChecker.checkMNCert_sound
#print axioms Gate11TraceChecker.checkDFATrace_sound
#print axioms Gate11TraceChecker.checkCounterTrace_sound
#print axioms Gate11TraceChecker.checkEscalatedTrace_sound
#print axioms Gate11TraceChecker.sample_0n1n_certified_corollary
