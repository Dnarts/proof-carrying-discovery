/-
  Gate 12 — Proof-Carrying Chomsky Escalation & Universal Class-Separation Checker
  (DFA -> 1-DCA -> DPDA/Stack) in Pure Lean 4 Core (Zero External Dependencies, Complete Proofs).

  Verify locally with:
      lean gate12_hierarchy_checker.lean

  Formalizes FIVE levels of machine-checked guarantees:
    1. Finite Trace Impossibility Certificates:
       - Level 1 (`DFA k`): `checkMNCert_sound` — (k + 1) pairwise distinguishable
         prefixes refute ALL k-state DFAs on `obs`.
       - Level 2 (`CounterProgram m`, 1-DCA): `check1DCACert_sound` —
         any `2 + m * (L + 1)` pairwise distinguishable prefixes of length `≤ L`
         refute ALL m-phase 1-DCAs on `obs`.
    2. Causal Escalation Chronology (`checkCausalEscalation_sound`):
       Verifies `0 < t1 < t2 ≤ obs.length` such that Level 1 (`DFA k`) is refuted on the
       historical prefix `obs.take t1`, Level 2 (`CounterProgram m`) is refuted on the
       historical prefix `obs.take t2`, and Level 3 (`StackProgram m'`) agrees with all `obs`.
    3. Parametric Infinite-Domain DPDA Meta-Theorem (`canonicalMidDPDA_eval_eq_true_iff`):
       For ANY synthesized `P : StackProgram 2` and binary transform `f : Sym → Sym`,
       if the computable structural check `isCanonicalMidDPDA P f` returns `true`
       (verified automatically via `by decide` with zero manual induction per task), then:
         `∀ w ∈ Σ*, P.eval w = true ↔ ∃ u ∈ {0,1}*, w = u ++ [#] ++ (u.map f).reverse`.
    4. Universal Unbounded Class Separation (`∀ m : Nat, ¬ 1-DCA(m)` and `∀ k : Nat, ¬ DFA(k)`):
       - `canonicalMidDPDA_not_1DCA`: for EVERY `m : Nat` (arbitrarily many phases),
         no `m`-phase 1-DCA agrees with `P` on `Σ*` (proven via `2^(2m+2) ≥ 2 + m(2m+3)`).
       - `canonicalMidDPDA_not_DFA`: for EVERY `k : Nat`, no `k`-state DFA agrees with `P` on `Σ*`.
    5. Master Protocol Theorem (`checkFullChomskyProtocol_sound`):
       A single `by decide` call simultaneously certifies finite causal chronology,
       infinite-domain specification `∀ w ∈ Σ*`, and unbounded impossibility `∀ k, ¬DFA(k)`
       and `∀ m, ¬1-DCA(m)`.
-/

namespace Gate12Hierarchy

/-- Three-symbol alphabet: 0 = '0', 1 = '1', 2 = '#' (delimiter). -/
abbrev Sym  := Fin 3
abbrev Word := List Sym
abbrev Obs  := List (Word × Bool)

def sym0 : Sym := ⟨0, by decide⟩
def sym1 : Sym := ⟨1, by decide⟩
def symHash : Sym := ⟨2, by decide⟩

def isBinarySym (b : Sym) : Bool := b.val == 0 || b.val == 1

def isBinaryWord : Word → Bool
  | []      => true
  | b :: bs => isBinarySym b && isBinaryWord bs

private theorem sym_cases (b : Sym) : b = sym0 ∨ b = sym1 ∨ b = symHash := by
  rcases b with ⟨v, hv⟩
  if h0 : v = 0 then
    left; exact Fin.ext h0
  else if h1 : v = 1 then
    right; left; exact Fin.ext h1
  else
    right; right
    have h2 : v = 2 := by omega
    exact Fin.ext h2

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

/-! ## Trace Lookup, Hygiene & Pair Witness Checker -/

def lookupObs : Obs → Word → Option Bool
  | [],              _ => none
  | (w', a) :: rest, w => if w' == w then some a else lookupObs rest w

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

def hasWord : Obs → Word → Bool
  | [],              _ => false
  | (w', _) :: rest, w => (w' == w) || hasWord rest w

def checkNoDupWords : Obs → Bool
  | []              => true
  | (w, _) :: rest  => (!hasWord rest w) && checkNoDupWords rest

def checkPairWitness (obs : Obs) (u v suf : Word) : Bool :=
  match lookupObs obs (u ++ suf), lookupObs obs (v ++ suf) with
  | some a1, some a2 => a1 != a2
  | _,       _       => false

theorem checkPairWitness_sound (obs : Obs) (u v suf : Word)
    (h : checkPairWitness obs u v suf = true) :
    ∃ a1 a2 : Bool, (u ++ suf, a1) ∈ obs ∧ (v ++ suf, a2) ∈ obs ∧ a1 ≠ a2 := by
  unfold checkPairWitness at h
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

/-! ## Level 1: DFA & Myhill-Nerode Impossibility Checkers (Finite & Infinite) -/

structure DFA (k : Nat) where
  start  : Fin k
  step   : Fin k → Sym → Fin k
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

def checkMNCert (k : Nat) (obs : Obs)
    (prefs : Fin (k + 1) → Word)
    (sufs  : Fin (k + 1) → Fin (k + 1) → Word) : Bool :=
  decide (∀ i j : Fin (k + 1), i ≠ j →
    checkPairWitness obs (prefs i) (prefs j) (sufs i j) = true)

theorem checkMNCert_sound (k : Nat) (obs : Obs)
    (prefs : Fin (k + 1) → Word)
    (sufs  : Fin (k + 1) → Fin (k + 1) → Word)
    (hchk  : checkMNCert k obs prefs sufs = true) :
    ¬ ∃ M : DFA k, ∀ p ∈ obs, M.eval p.1 = p.2 := by
  have hall := of_decide_eq_true hchk
  rintro ⟨M, hM⟩
  let stateOf : Fin (k + 1) → Fin k := fun i => M.runFrom M.start (prefs i)
  rcases pigeonhole_fin k stateOf with ⟨i, j, hij, hst⟩
  rcases checkPairWitness_sound obs (prefs i) (prefs j) (sufs i j) (hall i j hij)
    with ⟨a1, a2, hm1, hm2, hne⟩
  have h1 : M.eval (prefs i ++ sufs i j) = a1 := hM _ hm1
  have h2 : M.eval (prefs j ++ sufs i j) = a2 := hM _ hm2
  have hsame : M.eval (prefs i ++ sufs i j) = M.eval (prefs j ++ sufs i j) := by
    unfold DFA.eval
    rw [dfa_runFrom_append, dfa_runFrom_append]
    change M.accept (M.runFrom (stateOf i) (sufs i j)) =
           M.accept (M.runFrom (stateOf j) (sufs i j))
    rw [hst]
  rw [h1, h2] at hsame
  exact hne hsame

theorem dfa_oracle_impossibility (O : Word → Bool) (k : Nat)
    (prefs : Fin (k + 1) → Word)
    (hdist : ∀ i j : Fin (k + 1), i ≠ j → ∃ suf : Word, O (prefs i ++ suf) ≠ O (prefs j ++ suf)) :
    ¬ ∃ M : DFA k, ∀ w : Word, M.eval w = O w := by
  rintro ⟨M, hM⟩
  let stateOf : Fin (k + 1) → Fin k := fun i => M.runFrom M.start (prefs i)
  rcases pigeonhole_fin k stateOf with ⟨i, j, hij, hst⟩
  rcases hdist i j hij with ⟨suf, hsuf⟩
  have hsame : M.eval (prefs i ++ suf) = M.eval (prefs j ++ suf) := by
    unfold DFA.eval
    rw [dfa_runFrom_append, dfa_runFrom_append]
    change M.accept (M.runFrom (stateOf i) suf) = M.accept (M.runFrom (stateOf j) suf)
    rw [hst]
  rw [hM, hM] at hsame
  exact hsuf hsame

/-! ## Level 2: Typed 1-DCA & Constructive 1-DCA Impossibility Checkers (Finite & Infinite) -/

inductive CounterOp where
  | inc
  | dec
  | keep

structure CounterProgram (m : Nat) where
  startPhase : Fin m
  step       : Fin m → Sym → Bool → Option (Fin m × CounterOp)
  accept     : Fin m → Bool → Bool

def applyCounterOp (c : Nat) : CounterOp → Option Nat
  | .inc  => some (c + 1)
  | .keep => some c
  | .dec  => match c with
             | 0     => none
             | c + 1 => some c

def CounterProgram.stepCfg {m : Nat} (C : CounterProgram m)
    (cfg : Option (Fin m × Nat)) (b : Sym) : Option (Fin m × Nat) :=
  match cfg with
  | none          => none
  | some (ph, c)  =>
    match C.step ph b (c == 0) with
    | none           => none
    | some (ph', op) =>
      match applyCounterOp c op with
      | none    => none
      | some c' => some (ph', c')

def CounterProgram.runFrom {m : Nat} (C : CounterProgram m) :
    Option (Fin m × Nat) → Word → Option (Fin m × Nat)
  | cfg, []      => cfg
  | cfg, b :: ws => C.runFrom (C.stepCfg cfg b) ws

def CounterProgram.eval {m : Nat} (C : CounterProgram m) (w : Word) : Bool :=
  match C.runFrom (some (C.startPhase, 0)) w with
  | none         => false
  | some (ph, c) => C.accept ph (c == 0)

theorem counter_runFrom_append {m : Nat} (C : CounterProgram m) :
    ∀ (u v : Word) (cfg : Option (Fin m × Nat)),
      C.runFrom cfg (u ++ v) = C.runFrom (C.runFrom cfg u) v
  | [],      _, _   => rfl
  | b :: us, v, cfg => counter_runFrom_append C us v (C.stepCfg cfg b)

private theorem counter_stepCfg_le {m : Nat} (C : CounterProgram m)
    (ph ph' : Fin m) (c c' : Nat) (b : Sym)
    (h : C.stepCfg (some (ph, c)) b = some (ph', c')) : c' ≤ c + 1 := by
  unfold CounterProgram.stepCfg at h
  dsimp only at h
  cases hs : C.step ph b (c == 0) with
  | none => rw [hs] at h; cases h
  | some val =>
    rw [hs] at h
    rcases val with ⟨ph1, op⟩
    cases op with
    | inc => simp only [applyCounterOp] at h; cases h; omega
    | keep => simp only [applyCounterOp] at h; cases h; omega
    | dec =>
      cases c with
      | zero => simp only [applyCounterOp] at h; cases h
      | succ c0 => simp only [applyCounterOp] at h; cases h; omega

private theorem counter_runFrom_none {m : Nat} (C : CounterProgram m) :
    ∀ w : Word, C.runFrom none w = none
  | []      => rfl
  | _ :: ws => counter_runFrom_none C ws

private theorem counter_runFrom_le {m : Nat} (C : CounterProgram m) :
    ∀ (w : Word) (ph ph' : Fin m) (c c' : Nat),
      C.runFrom (some (ph, c)) w = some (ph', c') → c' ≤ c + w.length
  | [], _, _, _, _, h => by cases h; omega
  | b :: ws, ph, ph', c, c', h => by
    unfold CounterProgram.runFrom at h
    cases hst : C.stepCfg (some (ph, c)) b with
    | none => rw [hst, counter_runFrom_none] at h; cases h
    | some val =>
      rw [hst] at h
      rcases val with ⟨ph1, c1⟩
      have h1 : c1 ≤ c + 1 := counter_stepCfg_le C ph ph1 c c1 b hst
      have h2 : c' ≤ c1 + ws.length := counter_runFrom_le C ws ph1 ph' c1 c' h
      simp only [List.length_cons]; omega

def dcaConfigBound (m L : Nat) : Nat := 1 + m * (L + 1)

private def encodeDCACfg {m L : Nat} :
    (cfg : Option (Fin m × Nat)) → (∀ ph c, cfg = some (ph, c) → c ≤ L) → Fin (dcaConfigBound m L)
  | none, _ => ⟨0, by unfold dcaConfigBound; omega⟩
  | some (ph, c), hle =>
    have hc : c ≤ L := hle ph c rfl
    have hlt : 1 + ph.val * (L + 1) + c < 1 + m * (L + 1) := by
      have hph : ph.val + 1 ≤ m := ph.isLt
      have hmul : (ph.val + 1) * (L + 1) ≤ m * (L + 1) := Nat.mul_le_mul_right (L + 1) hph
      have hexp : ph.val * (L + 1) + (L + 1) = (ph.val + 1) * (L + 1) := by
        rw [Nat.add_mul, Nat.one_mul]
      omega
    ⟨1 + ph.val * (L + 1) + c, hlt⟩

private theorem encodeDCACfg_inj {m L : Nat}
    (cfg1 cfg2 : Option (Fin m × Nat))
    (h1 : ∀ ph c, cfg1 = some (ph, c) → c ≤ L)
    (h2 : ∀ ph c, cfg2 = some (ph, c) → c ≤ L)
    (heq : encodeDCACfg cfg1 h1 = encodeDCACfg cfg2 h2) :
    cfg1 = cfg2 := by
  cases cfg1 with
  | none =>
    cases cfg2 with
    | none => rfl
    | some p2 =>
      rcases p2 with ⟨ph2, c2⟩
      have hv := congrArg Fin.val heq
      dsimp only [encodeDCACfg] at hv; omega
  | some p1 =>
    rcases p1 with ⟨ph1, c1⟩
    cases cfg2 with
    | none =>
      have hv := congrArg Fin.val heq
      dsimp only [encodeDCACfg] at hv; omega
    | some p2 =>
      rcases p2 with ⟨ph2, c2⟩
      have hc1 : c1 ≤ L := h1 ph1 c1 rfl
      have hc2 : c2 ≤ L := h2 ph2 c2 rfl
      have hv := congrArg Fin.val heq
      dsimp only [encodeDCACfg] at hv
      have hlin : ph1.val * (L + 1) + c1 = ph2.val * (L + 1) + c2 := by omega
      have hph_eq : ph1.val = ph2.val := by
        by_cases hlt : ph1.val < ph2.val
        · have hstep : (ph1.val + 1) * (L + 1) ≤ ph2.val * (L + 1) := Nat.mul_le_mul_right (L + 1) hlt
          have hexp : ph1.val * (L + 1) + (L + 1) = (ph1.val + 1) * (L + 1) := by rw [Nat.add_mul, Nat.one_mul]
          omega
        · by_cases hgt : ph2.val < ph1.val
          · have hstep : (ph2.val + 1) * (L + 1) ≤ ph1.val * (L + 1) := Nat.mul_le_mul_right (L + 1) hgt
            have hexp : ph2.val * (L + 1) + (L + 1) = (ph2.val + 1) * (L + 1) := by rw [Nat.add_mul, Nat.one_mul]
            omega
          · omega
      have hc_eq : c1 = c2 := by rw [hph_eq] at hlin; omega
      rw [Fin.ext hph_eq, hc_eq]

def check1DCACert (m L : Nat) (obs : Obs)
    (prefs : Fin (dcaConfigBound m L + 1) → Word)
    (sufs  : Fin (dcaConfigBound m L + 1) → Fin (dcaConfigBound m L + 1) → Word) : Bool :=
  decide (
    (∀ i : Fin (dcaConfigBound m L + 1), (prefs i).length ≤ L) ∧
    (∀ i j : Fin (dcaConfigBound m L + 1), i ≠ j →
      checkPairWitness obs (prefs i) (prefs j) (sufs i j) = true)
  )

theorem check1DCACert_sound (m L : Nat) (obs : Obs)
    (prefs : Fin (dcaConfigBound m L + 1) → Word)
    (sufs  : Fin (dcaConfigBound m L + 1) → Fin (dcaConfigBound m L + 1) → Word)
    (hchk  : check1DCACert m L obs prefs sufs = true) :
    ¬ ∃ C : CounterProgram m, ∀ p ∈ obs, C.eval p.1 = p.2 := by
  rcases of_decide_eq_true hchk with ⟨hlen, hdist⟩
  rintro ⟨C, hC⟩
  let cfgOf : Fin (dcaConfigBound m L + 1) → Option (Fin m × Nat) :=
    fun i => C.runFrom (some (C.startPhase, 0)) (prefs i)
  have hbound : ∀ (i : Fin (dcaConfigBound m L + 1)) (ph : Fin m) (c : Nat),
      cfgOf i = some (ph, c) → c ≤ L := by
    intro i ph c hcfg
    have hle1 : c ≤ 0 + (prefs i).length := counter_runFrom_le C (prefs i) C.startPhase ph 0 c hcfg
    have hle2 : (prefs i).length ≤ L := hlen i
    omega
  let codeOf : Fin (dcaConfigBound m L + 1) → Fin (dcaConfigBound m L) :=
    fun i => encodeDCACfg (cfgOf i) (hbound i)
  rcases pigeonhole_fin (dcaConfigBound m L) codeOf with ⟨i, j, hij, hcode⟩
  have hcfg_eq : cfgOf i = cfgOf j :=
    encodeDCACfg_inj (cfgOf i) (cfgOf j) (hbound i) (hbound j) hcode
  rcases checkPairWitness_sound obs (prefs i) (prefs j) (sufs i j) (hdist i j hij)
    with ⟨a1, a2, hm1, hm2, hne⟩
  have he1 : C.eval (prefs i ++ sufs i j) = a1 := hC _ hm1
  have he2 : C.eval (prefs j ++ sufs i j) = a2 := hC _ hm2
  have hsame : C.eval (prefs i ++ sufs i j) = C.eval (prefs j ++ sufs i j) := by
    unfold CounterProgram.eval
    rw [counter_runFrom_append, counter_runFrom_append]
    change (match C.runFrom (cfgOf i) (sufs i j) with | none => false | some (ph, c) => C.accept ph (c == 0)) =
           (match C.runFrom (cfgOf j) (sufs i j) with | none => false | some (ph, c) => C.accept ph (c == 0))
    rw [hcfg_eq]
  rw [he1, he2] at hsame
  exact hne hsame

theorem dca_oracle_impossibility (O : Word → Bool) (m L : Nat)
    (prefs : Fin (dcaConfigBound m L + 1) → Word)
    (hlen  : ∀ i : Fin (dcaConfigBound m L + 1), (prefs i).length ≤ L)
    (hdist : ∀ i j : Fin (dcaConfigBound m L + 1), i ≠ j →
      ∃ suf : Word, O (prefs i ++ suf) ≠ O (prefs j ++ suf)) :
    ¬ ∃ C : CounterProgram m, ∀ w : Word, C.eval w = O w := by
  rintro ⟨C, hC⟩
  let cfgOf : Fin (dcaConfigBound m L + 1) → Option (Fin m × Nat) :=
    fun i => C.runFrom (some (C.startPhase, 0)) (prefs i)
  have hbound : ∀ (i : Fin (dcaConfigBound m L + 1)) (ph : Fin m) (c : Nat),
      cfgOf i = some (ph, c) → c ≤ L := by
    intro i ph c hcfg
    have hle1 : c ≤ 0 + (prefs i).length := counter_runFrom_le C (prefs i) C.startPhase ph 0 c hcfg
    have hle2 : (prefs i).length ≤ L := hlen i
    omega
  let codeOf : Fin (dcaConfigBound m L + 1) → Fin (dcaConfigBound m L) :=
    fun i => encodeDCACfg (cfgOf i) (hbound i)
  rcases pigeonhole_fin (dcaConfigBound m L) codeOf with ⟨i, j, hij, hcode⟩
  have hcfg_eq : cfgOf i = cfgOf j :=
    encodeDCACfg_inj (cfgOf i) (cfgOf j) (hbound i) (hbound j) hcode
  rcases hdist i j hij with ⟨suf, hsuf⟩
  have hsame : C.eval (prefs i ++ suf) = C.eval (prefs j ++ suf) := by
    unfold CounterProgram.eval
    rw [counter_runFrom_append, counter_runFrom_append]
    change (match C.runFrom (cfgOf i) suf with | none => false | some (ph, c) => C.accept ph (c == 0)) =
           (match C.runFrom (cfgOf j) suf with | none => false | some (ph, c) => C.accept ph (c == 0))
    rw [hcfg_eq]
  rw [hC, hC] at hsame
  exact hsuf hsame

/-! ## Level 3: Typed DPDA / StackProgram DSL & Finite/Causal Escalation Checkers -/

inductive StackOp where
  | push (s : Sym)
  | popMatch (s : Sym)
  | keep
  deriving DecidableEq

structure StackProgram (m : Nat) where
  startPhase : Fin m
  step       : Fin m → Sym → Option Sym → Option (Fin m × StackOp)
  accept     : Fin m → Bool → Bool

def applyStackOp (stk : List Sym) : StackOp → Option (List Sym)
  | .push s     => some (s :: stk)
  | .keep       => some stk
  | .popMatch s =>
    match stk with
    | top :: rest => if top == s then some rest else none
    | []          => none

def StackProgram.stepCfg {m : Nat} (P : StackProgram m)
    (cfg : Option (Fin m × List Sym)) (b : Sym) : Option (Fin m × List Sym) :=
  match cfg with
  | none            => none
  | some (ph, stk)  =>
    let top := match stk with | [] => none | t :: _ => some t
    match P.step ph b top with
    | none           => none
    | some (ph', op) =>
      match applyStackOp stk op with
      | none      => none
      | some stk' => some (ph', stk')

def StackProgram.runFrom {m : Nat} (P : StackProgram m) :
    Option (Fin m × List Sym) → Word → Option (Fin m × List Sym)
  | cfg, []      => cfg
  | cfg, b :: ws => P.runFrom (P.stepCfg cfg b) ws

def StackProgram.eval {m : Nat} (P : StackProgram m) (w : Word) : Bool :=
  match P.runFrom (some (P.startPhase, [])) w with
  | none           => false
  | some (ph, stk) => P.accept ph stk.isEmpty

def checkCounterTrace {m : Nat} (C : CounterProgram m) (obs : Obs) : Bool :=
  checkAllObs C.eval obs

def checkStackTrace {m : Nat} (P : StackProgram m) (obs : Obs) : Bool :=
  checkAllObs P.eval obs

theorem checkCounterTrace_sound {m : Nat} (C : CounterProgram m) (obs : Obs)
    (h : checkCounterTrace C obs = true) : ∀ p ∈ obs, C.eval p.1 = p.2 :=
  checkAllObs_sound C.eval obs h

theorem checkStackTrace_sound {m : Nat} (P : StackProgram m) (obs : Obs)
    (h : checkStackTrace P obs = true) : ∀ p ∈ obs, P.eval p.1 = p.2 :=
  checkAllObs_sound P.eval obs h

def checkLevel3Escalation {k m L m' : Nat} (obs : Obs)
    (mnPrefs  : Fin (k + 1) → Word)
    (mnSufs   : Fin (k + 1) → Fin (k + 1) → Word)
    (dcaPrefs : Fin (dcaConfigBound m L + 1) → Word)
    (dcaSufs  : Fin (dcaConfigBound m L + 1) → Fin (dcaConfigBound m L + 1) → Word)
    (P        : StackProgram m') : Bool :=
  checkNoDupWords obs &&
  checkMNCert k obs mnPrefs mnSufs &&
  check1DCACert m L obs dcaPrefs dcaSufs &&
  checkStackTrace P obs

theorem checkLevel3Escalation_sound {k m L m' : Nat} (obs : Obs)
    (mnPrefs  : Fin (k + 1) → Word)
    (mnSufs   : Fin (k + 1) → Fin (k + 1) → Word)
    (dcaPrefs : Fin (dcaConfigBound m L + 1) → Word)
    (dcaSufs  : Fin (dcaConfigBound m L + 1) → Fin (dcaConfigBound m L + 1) → Word)
    (P        : StackProgram m')
    (h        : checkLevel3Escalation obs mnPrefs mnSufs dcaPrefs dcaSufs P = true) :
    (¬ ∃ M : DFA k, ∀ p ∈ obs, M.eval p.1 = p.2) ∧
    (¬ ∃ C : CounterProgram m, ∀ p ∈ obs, C.eval p.1 = p.2) ∧
    (∀ p ∈ obs, P.eval p.1 = p.2) := by
  unfold checkLevel3Escalation at h
  cases hnd : checkNoDupWords obs with
  | false => rw [hnd] at h; cases h
  | true =>
    rw [hnd] at h
    cases hmn : checkMNCert k obs mnPrefs mnSufs with
    | false => rw [hmn] at h; cases h
    | true =>
      rw [hmn] at h
      cases hdca : check1DCACert m L obs dcaPrefs dcaSufs with
      | false => rw [hdca] at h; cases h
      | true =>
        rw [hdca] at h
        exact ⟨
          checkMNCert_sound k obs mnPrefs mnSufs hmn,
          check1DCACert_sound m L obs dcaPrefs dcaSufs hdca,
          checkStackTrace_sound P obs h
        ⟩

/-- Causal Escalation Chronology Checker:
    Certifies that Level 1 (`DFA k`) is refuted at historical timestamp `t1` (`obs.take t1`),
    Level 2 (`CounterProgram m`) is refuted at timestamp `t2` (`obs.take t2`) with `0 < t1 < t2 ≤ obs.length`,
    and Level 3 (`StackProgram m'`) agrees with the full observation history `obs`. -/
def checkCausalEscalation {k m L m' : Nat} (obs : Obs) (t1 t2 : Nat)
    (mnPrefs  : Fin (k + 1) → Word)
    (mnSufs   : Fin (k + 1) → Fin (k + 1) → Word)
    (dcaPrefs : Fin (dcaConfigBound m L + 1) → Word)
    (dcaSufs  : Fin (dcaConfigBound m L + 1) → Fin (dcaConfigBound m L + 1) → Word)
    (P        : StackProgram m') : Bool :=
  decide (0 < t1 ∧ t1 < t2 ∧ t2 ≤ obs.length) &&
  checkNoDupWords obs &&
  checkMNCert k (obs.take t1) mnPrefs mnSufs &&
  check1DCACert m L (obs.take t2) dcaPrefs dcaSufs &&
  checkStackTrace P obs

theorem checkCausalEscalation_sound {k m L m' : Nat} (obs : Obs) (t1 t2 : Nat)
    (mnPrefs  : Fin (k + 1) → Word)
    (mnSufs   : Fin (k + 1) → Fin (k + 1) → Word)
    (dcaPrefs : Fin (dcaConfigBound m L + 1) → Word)
    (dcaSufs  : Fin (dcaConfigBound m L + 1) → Fin (dcaConfigBound m L + 1) → Word)
    (P        : StackProgram m')
    (h        : checkCausalEscalation obs t1 t2 mnPrefs mnSufs dcaPrefs dcaSufs P = true) :
    (0 < t1 ∧ t1 < t2 ∧ t2 ≤ obs.length) ∧
    (¬ ∃ M : DFA k, ∀ p ∈ obs.take t1, M.eval p.1 = p.2) ∧
    (¬ ∃ C : CounterProgram m, ∀ p ∈ obs.take t2, C.eval p.1 = p.2) ∧
    (∀ p ∈ obs, P.eval p.1 = p.2) := by
  unfold checkCausalEscalation at h
  simp only [Bool.and_eq_true] at h
  rcases h with ⟨⟨⟨⟨ht, _⟩, hmn⟩, hdca⟩, hstk⟩
  exact ⟨
    of_decide_eq_true ht,
    checkMNCert_sound k (obs.take t1) mnPrefs mnSufs hmn,
    check1DCACert_sound m L (obs.take t2) dcaPrefs dcaSufs hdca,
    checkStackTrace_sound P obs hstk
  ⟩

/-! ## Binary Words Generator & Exponential Growth Bound (`2^(2m+2) ≥ 2 + m(2m+3)`) -/

def binWords : Nat → List Word
  | 0     => [[]]
  | L + 1 => (binWords L).map (fun w => sym0 :: w) ++ (binWords L).map (fun w => sym1 :: w)

theorem binWords_length : ∀ L : Nat, (binWords L).length = 2 ^ L
  | 0     => rfl
  | L + 1 => by
    simp only [binWords, List.length_append, List.length_map, binWords_length L]
    rw [Nat.pow_succ]
    omega

theorem binWords_word_length : ∀ (L : Nat) (w : Word), w ∈ binWords L → w.length = L
  | 0, w, hw => by
    simp only [binWords, List.mem_singleton] at hw
    rw [hw]; rfl
  | L + 1, w, hw => by
    simp only [binWords, List.mem_append, List.mem_map] at hw
    rcases hw with ⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩
    · simp [binWords_word_length L u hu]
    · simp [binWords_word_length L u hu]

theorem binWords_isBinary : ∀ (L : Nat) (w : Word), w ∈ binWords L → isBinaryWord w = true
  | 0, w, hw => by
    simp only [binWords, List.mem_singleton] at hw
    rw [hw]; rfl
  | L + 1, w, hw => by
    simp only [binWords, List.mem_append, List.mem_map] at hw
    rcases hw with ⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩
    · simp [isBinaryWord, isBinarySym, sym0, binWords_isBinary L u hu]
    · simp [isBinaryWord, isBinarySym, sym1, binWords_isBinary L u hu]

inductive Nodup {α : Type} : List α → Prop
  | nil  : Nodup []
  | cons : ∀ {x : α} {xs : List α}, x ∉ xs → Nodup xs → Nodup (x :: xs)

private theorem nodup_map_cons (s : Sym) :
    ∀ (xs : List Word), Nodup xs → Nodup (xs.map (fun w => s :: w))
  | [], .nil => .nil
  | x :: xs, .cons hnot hnd => by
    simp only [List.map]
    refine .cons ?_ (nodup_map_cons s xs hnd)
    intro hmem
    simp only [List.mem_map] at hmem
    rcases hmem with ⟨u, hu, heq⟩
    injection heq with _ hux
    subst hux
    exact hnot hu

private theorem nodup_append {α : Type} :
    ∀ (xs ys : List α), Nodup xs → Nodup ys → (∀ x ∈ xs, x ∉ ys) → Nodup (xs ++ ys)
  | [], ys, _, hys, _ => hys
  | x :: xs, ys, .cons hx hxs, hys, hdisj => by
    simp only [List.cons_append]
    refine .cons ?_ (nodup_append xs ys hxs hys (fun z hz => hdisj z (List.Mem.tail x hz)))
    intro hmem
    simp only [List.mem_append] at hmem
    rcases hmem with h1 | h2
    · exact hx h1
    · exact hdisj x (List.Mem.head xs) h2

theorem binWords_nodup : ∀ L : Nat, Nodup (binWords L)
  | 0     => .cons (by simp) .nil
  | L + 1 => by
    simp only [binWords]
    refine nodup_append _ _ (nodup_map_cons sym0 _ (binWords_nodup L))
      (nodup_map_cons sym1 _ (binWords_nodup L)) ?_
    intro x hx hy
    simp only [List.mem_map] at hx hy
    rcases hx with ⟨u, _, rfl⟩
    rcases hy with ⟨v, _, heq⟩
    injection heq with h01 _
    have hv := congrArg Fin.val h01
    cases hv

theorem get_mem {α : Type} : ∀ (xs : List α) (i : Fin xs.length), xs.get i ∈ xs
  | _ :: xs, ⟨0, _⟩ => List.Mem.head xs
  | x :: xs, ⟨n + 1, h⟩ => List.Mem.tail x (get_mem xs ⟨n, Nat.lt_of_succ_lt_succ h⟩)

theorem nodup_get_inj {α : Type} :
    ∀ (xs : List α), Nodup xs → ∀ (i j : Fin xs.length), xs.get i = xs.get j → i = j
  | [], _, i, _, _ => Fin.elim0 i
  | _ :: _, .cons _ _, ⟨0, _⟩, ⟨0, _⟩, _ => rfl
  | _ :: xs, .cons hnot _, ⟨0, _⟩, ⟨n + 1, h2⟩, heq => by
    dsimp only [List.get] at heq
    have hm := get_mem xs ⟨n, Nat.lt_of_succ_lt_succ h2⟩
    rw [← heq] at hm
    exact False.elim (hnot hm)
  | _ :: xs, .cons hnot _, ⟨n + 1, h1⟩, ⟨0, _⟩, heq => by
    dsimp only [List.get] at heq
    have hm := get_mem xs ⟨n, Nat.lt_of_succ_lt_succ h1⟩
    rw [heq] at hm
    exact False.elim (hnot hm)
  | _ :: xs, .cons _ hnd, ⟨n1 + 1, h1⟩, ⟨n2 + 1, h2⟩, heq => by
    dsimp only [List.get] at heq
    have hij := nodup_get_inj xs hnd ⟨n1, Nat.lt_of_succ_lt_succ h1⟩ ⟨n2, Nat.lt_of_succ_lt_succ h2⟩ heq
    have hval : n1 = n2 := congrArg Fin.val hij
    subst hval
    rfl

private theorem pow2_ge_succ : ∀ n : Nat, n + 1 ≤ 2 ^ n
  | 0     => by decide
  | n + 1 => by
    have ih := pow2_ge_succ n
    have h1 : 1 ≤ 2 ^ n := Nat.le_trans (by omega) ih
    rw [Nat.pow_succ]
    omega

private theorem exp_gt_dca_bound (m : Nat) :
    dcaConfigBound m (2 * m + 2) + 1 ≤ 2 ^ (2 * m + 2) := by
  unfold dcaConfigBound
  induction m with
  | zero => decide
  | succ m ih =>
    have hpow : 2 ^ (2 * (m + 1) + 2) = 4 * 2 ^ (2 * m + 2) := by
      have heq : 2 * (m + 1) + 2 = (2 * m + 2) + 1 + 1 := by omega
      rw [heq, Nat.pow_succ, Nat.pow_succ]
      omega
    have h1 : 2 * (m + 1) + 2 + 1 = (2 * m + 2 + 1) + 2 := by omega
    have h2 : (m + 1) * ((2 * m + 2 + 1) + 2) =
        m * (2 * m + 2 + 1) + 2 * m + (2 * m + 2 + 1) + 2 := by
      rw [Nat.add_mul, Nat.one_mul, Nat.mul_add]
      omega
    rw [h1, h2, hpow]
    have hge : 2 * m + 3 ≤ 2 ^ (2 * m + 2) := pow2_ge_succ (2 * m + 2)
    omega

/-! ## Parametric Infinite-Domain DPDA Meta-Theorem & Universal Class Separation -/

def checkStepAtTop (P : StackProgram 2) (f : Sym → Sym) (top : Option Sym) : Bool :=
  decide (
    P.step ⟨0, by decide⟩ sym0 top = some (⟨0, by decide⟩, .push (f sym0)) ∧
    P.step ⟨0, by decide⟩ sym1 top = some (⟨0, by decide⟩, .push (f sym1)) ∧
    P.step ⟨0, by decide⟩ symHash top = some (⟨1, by decide⟩, .keep) ∧
    P.step ⟨1, by decide⟩ sym0 top = some (⟨1, by decide⟩, .popMatch sym0) ∧
    P.step ⟨1, by decide⟩ sym1 top = some (⟨1, by decide⟩, .popMatch sym1) ∧
    P.step ⟨1, by decide⟩ symHash top = none
  )

/-- Computable structural recognizer for the parametric family of center-marked
    push-then-popMatch DPDAs parameterized by a binary symbol transform `f : Sym → Sym`. -/
def isCanonicalMidDPDA (P : StackProgram 2) (f : Sym → Sym) : Bool :=
  isBinarySym (f sym0) &&
  isBinarySym (f sym1) &&
  decide (P.startPhase = ⟨0, by decide⟩) &&
  checkStepAtTop P f none &&
  checkStepAtTop P f (some sym0) &&
  checkStepAtTop P f (some sym1) &&
  checkStepAtTop P f (some symHash) &&
  decide (
    P.accept ⟨0, by decide⟩ false = false ∧
    P.accept ⟨0, by decide⟩ true = false ∧
    P.accept ⟨1, by decide⟩ false = false ∧
    P.accept ⟨1, by decide⟩ true = true
  )

private theorem isCanonicalMidDPDA_spec (P : StackProgram 2) (f : Sym → Sym)
    (h : isCanonicalMidDPDA P f = true) :
    isBinarySym (f sym0) = true ∧
    isBinarySym (f sym1) = true ∧
    P.startPhase = ⟨0, by decide⟩ ∧
    (∀ top : Option Sym,
      P.step ⟨0, by decide⟩ sym0 top = some (⟨0, by decide⟩, .push (f sym0)) ∧
      P.step ⟨0, by decide⟩ sym1 top = some (⟨0, by decide⟩, .push (f sym1)) ∧
      P.step ⟨0, by decide⟩ symHash top = some (⟨1, by decide⟩, .keep) ∧
      P.step ⟨1, by decide⟩ sym0 top = some (⟨1, by decide⟩, .popMatch sym0) ∧
      P.step ⟨1, by decide⟩ sym1 top = some (⟨1, by decide⟩, .popMatch sym1) ∧
      P.step ⟨1, by decide⟩ symHash top = none) ∧
    (∀ isEmpty : Bool,
      P.accept ⟨0, by decide⟩ isEmpty = false ∧
      P.accept ⟨1, by decide⟩ isEmpty = isEmpty) := by
  unfold isCanonicalMidDPDA at h
  simp only [Bool.and_eq_true] at h
  rcases h with ⟨⟨⟨⟨⟨⟨⟨hf0, hf1⟩, hst⟩, htn⟩, ht0⟩, ht1⟩, ht2⟩, hacc⟩
  refine ⟨hf0, hf1, of_decide_eq_true hst, ?_, ?_⟩
  · intro top
    cases top with
    | none => exact of_decide_eq_true htn
    | some s =>
      rcases sym_cases s with rfl | rfl | rfl
      · exact of_decide_eq_true ht0
      · exact of_decide_eq_true ht1
      · exact of_decide_eq_true ht2
  · rcases of_decide_eq_true hacc with ⟨ha0f, ha0t, ha1f, ha1t⟩
    intro isEmpty
    cases isEmpty
    · exact ⟨ha0f, ha1f⟩
    · exact ⟨ha0t, ha1t⟩

private theorem stack_runFrom_none {m : Nat} (P : StackProgram m) :
    ∀ w : Word, P.runFrom none w = none
  | []      => rfl
  | _ :: ws => stack_runFrom_none P ws

def acceptStackCfg {m : Nat} (P : StackProgram m) : Option (Fin m × List Sym) → Bool
  | none           => false
  | some (ph, stk) => P.accept ph stk.isEmpty

private theorem canonical_stepCfg_ph1 (P : StackProgram 2) (f : Sym → Sym)
    (hcan : isCanonicalMidDPDA P f = true) (stk : List Sym) (b : Sym) :
    P.stepCfg (some (⟨1, by decide⟩, stk)) b =
      match isBinarySym b with
      | true =>
        match stk with
        | top :: rest =>
          match top == b with
          | true  => some (⟨1, by decide⟩, rest)
          | false => none
        | [] => none
      | false => none := by
  rcases isCanonicalMidDPDA_spec P f hcan with ⟨_, _, _, hstep, _⟩
  let topOpt := match stk with | [] => none | t :: _ => some t
  rcases hstep topOpt with ⟨_, _, _, hs10, hs11, hs12⟩
  rcases sym_cases b with rfl | rfl | rfl
  · unfold StackProgram.stepCfg
    dsimp only
    rw [hs10]
    have hb0 : isBinarySym sym0 = true := rfl
    rw [hb0]
    cases stk with
    | nil => rfl
    | cons top rest =>
      dsimp only [applyStackOp]
      cases (top == sym0) <;> rfl
  · unfold StackProgram.stepCfg
    dsimp only
    rw [hs11]
    have hb1 : isBinarySym sym1 = true := rfl
    rw [hb1]
    cases stk with
    | nil => rfl
    | cons top rest =>
      dsimp only [applyStackOp]
      cases (top == sym1) <;> rfl
  · unfold StackProgram.stepCfg
    dsimp only
    rw [hs12]
    rfl

private theorem canonical_stepCfg_ph0 (P : StackProgram 2) (f : Sym → Sym)
    (hcan : isCanonicalMidDPDA P f = true) (stk : List Sym) (b : Sym) :
    P.stepCfg (some (⟨0, by decide⟩, stk)) b =
      match isBinarySym b with
      | true  => some (⟨0, by decide⟩, f b :: stk)
      | false => some (⟨1, by decide⟩, stk) := by
  rcases isCanonicalMidDPDA_spec P f hcan with ⟨_, _, _, hstep, _⟩
  let topOpt := match stk with | [] => none | t :: _ => some t
  rcases hstep topOpt with ⟨hs00, hs01, hs02, _, _, _⟩
  rcases sym_cases b with rfl | rfl | rfl
  · unfold StackProgram.stepCfg; dsimp only; rw [hs00]; rfl
  · unfold StackProgram.stepCfg; dsimp only; rw [hs01]; rfl
  · unfold StackProgram.stepCfg; dsimp only; rw [hs02]; rfl

private theorem canonical_f_isBinary (P : StackProgram 2) (f : Sym → Sym)
    (hcan : isCanonicalMidDPDA P f = true) (b : Sym) (hb : isBinarySym b = true) :
    isBinarySym (f b) = true := by
  rcases isCanonicalMidDPDA_spec P f hcan with ⟨hf0, hf1, _, _, _⟩
  rcases sym_cases b with rfl | rfl | rfl
  · exact hf0
  · exact hf1
  · cases hb

private theorem canonical_ph1_accept_iff (P : StackProgram 2) (f : Sym → Sym)
    (hcan : isCanonicalMidDPDA P f = true) :
    ∀ (w stk : List Sym),
      isBinaryWord stk = true →
      (acceptStackCfg P (P.runFrom (some (⟨1, by decide⟩, stk)) w) = true ↔ w = stk)
  | [], [] => by
    intro _
    rcases isCanonicalMidDPDA_spec P f hcan with ⟨_, _, _, _, hacc⟩
    simp only [StackProgram.runFrom, acceptStackCfg, List.isEmpty, (hacc true).2]
  | [], top :: rest => by
    intro _
    rcases isCanonicalMidDPDA_spec P f hcan with ⟨_, _, _, _, hacc⟩
    simp only [StackProgram.runFrom, acceptStackCfg, List.isEmpty, (hacc false).2, Bool.false_eq_true, false_iff]
    intro h; cases h
  | b :: ws, [] => by
    intro _
    unfold StackProgram.runFrom
    rw [canonical_stepCfg_ph1 P f hcan [] b]
    cases isBinarySym b <;> simp [stack_runFrom_none, acceptStackCfg]
  | b :: ws, top :: rest => by
    intro hstk
    simp only [isBinaryWord, Bool.and_eq_true] at hstk
    rcases hstk with ⟨htop, hrest⟩
    unfold StackProgram.runFrom
    rw [canonical_stepCfg_ph1 P f hcan (top :: rest) b]
    cases hbin : isBinarySym b with
    | true =>
      dsimp only
      cases hbeq : (top == b) with
      | true =>
        dsimp only
        have heq : top = b := eq_of_beq hbeq
        rw [canonical_ph1_accept_iff P f hcan ws rest hrest]
        constructor
        · intro hws; rw [heq, hws]
        · intro hcons; injection hcons
      | false =>
        dsimp only
        rw [stack_runFrom_none]
        simp only [acceptStackCfg, Bool.false_eq_true, false_iff]
        intro hcons
        injection hcons with h1 _
        have hbt : (top == b) = true := beq_iff_eq.mpr h1.symm
        rw [hbt] at hbeq; cases hbeq
    | false =>
      dsimp only
      rw [stack_runFrom_none]
      simp only [acceptStackCfg, Bool.false_eq_true, false_iff]
      intro hcons
      injection hcons with h1 _
      subst h1
      rw [htop] at hbin; cases hbin

private theorem canonical_ph0_accept_iff (P : StackProgram 2) (f : Sym → Sym)
    (hcan : isCanonicalMidDPDA P f = true) :
    ∀ (w stk : List Sym),
      isBinaryWord stk = true →
      (acceptStackCfg P (P.runFrom (some (⟨0, by decide⟩, stk)) w) = true ↔
        ∃ u : Word, isBinaryWord u = true ∧ w = u ++ [symHash] ++ (u.map f).reverse ++ stk)
  | [], stk => by
    intro _
    rcases isCanonicalMidDPDA_spec P f hcan with ⟨_, _, _, _, hacc⟩
    simp only [StackProgram.runFrom, acceptStackCfg, (hacc stk.isEmpty).1, Bool.false_eq_true, false_iff]
    rintro ⟨u, _, hu⟩
    cases u <;> simp at hu
  | b :: ws, stk => by
    intro hstk
    unfold StackProgram.runFrom
    rw [canonical_stepCfg_ph0 P f hcan stk b]
    cases hbin : isBinarySym b with
    | true =>
      dsimp only
      have hfb : isBinarySym (f b) = true := canonical_f_isBinary P f hcan b hbin
      have hstk' : isBinaryWord (f b :: stk) = true := by
        simp [isBinaryWord, hfb, hstk]
      rw [canonical_ph0_accept_iff P f hcan ws (f b :: stk) hstk']
      constructor
      · rintro ⟨u, hu, hws⟩
        refine ⟨b :: u, ?_, ?_⟩
        · simp [isBinaryWord, hbin, hu]
        · simp [hws, List.append_assoc]
      · rintro ⟨u, hu, hcons⟩
        cases u with
        | nil =>
          simp only [List.nil_append, List.map_nil, List.reverse_nil] at hcons
          injection hcons with hbh _
          subst hbh; cases hbin
        | cons x xs =>
          simp only [List.cons_append, List.map_cons, List.reverse_cons] at hcons
          injection hcons with hbx htail
          subst hbx
          simp only [isBinaryWord, Bool.and_eq_true] at hu
          refine ⟨xs, hu.2, ?_⟩
          simpa [List.append_assoc] using htail
    | false =>
      dsimp only
      have hb_hash : b = symHash := by
        rcases sym_cases b with rfl | rfl | rfl
        · cases hbin
        · cases hbin
        · rfl
      subst hb_hash
      rw [canonical_ph1_accept_iff P f hcan ws stk hstk]
      constructor
      · intro hws
        refine ⟨[], rfl, ?_⟩
        simp [hws]
      · rintro ⟨u, hu, hcons⟩
        cases u with
        | nil =>
          simpa using hcons
        | cons x xs =>
          simp only [List.cons_append] at hcons
          injection hcons with hxh _
          rw [← hxh] at hu
          simp [isBinaryWord, isBinarySym, symHash] at hu

/-- Parametric Meta-Theorem 1 (Infinite-Domain Specification for ANY Canonical Synthesized DPDA):
    If `isCanonicalMidDPDA P f = true`, then for EVERY word `w ∈ Σ*`:
      `P.eval w = true ↔ ∃ u ∈ {0,1}*, w = u ++ [#] ++ (u.map f).reverse`. -/
theorem canonicalMidDPDA_eval_eq_true_iff (P : StackProgram 2) (f : Sym → Sym)
    (hcan : isCanonicalMidDPDA P f = true) (w : Word) :
    P.eval w = true ↔
      ∃ u : Word, isBinaryWord u = true ∧ w = u ++ [symHash] ++ (u.map f).reverse := by
  rcases isCanonicalMidDPDA_spec P f hcan with ⟨_, _, hstart, _, _⟩
  have h : P.eval w = acceptStackCfg P (P.runFrom (some (⟨0, by decide⟩, [])) w) := by
    unfold StackProgram.eval acceptStackCfg
    rw [hstart]
  have h0 := canonical_ph0_accept_iff P f hcan w [] rfl
  simp only [List.append_nil] at h0
  rw [h]
  exact h0

private theorem binary_split_hash_left :
    ∀ (u1 u2 s1 s2 : Word),
      isBinaryWord u1 = true →
      isBinaryWord u2 = true →
      u1 ++ [symHash] ++ s1 = u2 ++ [symHash] ++ s2 →
      u1 = u2 ∧ s1 = s2
  | [], [], s1, s2, _, _, h => by
    simp only [List.nil_append, List.singleton_append] at h
    injection h with _ hs
    exact ⟨rfl, hs⟩
  | [], b :: u2, s1, s2, _, hu2, h => by
    simp only [List.nil_append, List.cons_append] at h
    injection h with hhb _
    rw [← hhb] at hu2
    simp [isBinaryWord, isBinarySym, symHash] at hu2
  | a :: u1, [], s1, s2, hu1, _, h => by
    simp only [List.nil_append, List.cons_append] at h
    injection h with hah _
    rw [hah] at hu1
    simp [isBinaryWord, isBinarySym, symHash] at hu1
  | a :: u1, b :: u2, s1, s2, hu1, hu2, h => by
    simp only [List.cons_append] at h
    injection h with hab htail
    subst hab
    simp only [isBinaryWord, Bool.and_eq_true] at hu1 hu2
    rcases binary_split_hash_left u1 u2 s1 s2 hu1.2 hu2.2 htail with ⟨hu, hs⟩
    exact ⟨congrArg (List.cons a) hu, hs⟩

private theorem map_f_inj_on_binary (f : Sym → Sym) (hfinj : (f sym0 != f sym1) = true) :
    ∀ (u1 u2 : Word),
      isBinaryWord u1 = true →
      isBinaryWord u2 = true →
      u1.map f = u2.map f →
      u1 = u2
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, _, h => by cases h
  | _ :: _, [], _, _, h => by cases h
  | a :: u1, b :: u2, hu1, hu2, h => by
    simp only [List.map_cons] at h
    injection h with hfab htail
    simp only [isBinaryWord, Bool.and_eq_true] at hu1 hu2
    have hab : a = b := by
      rcases sym_cases a with rfl | rfl | rfl
      · rcases sym_cases b with rfl | rfl | rfl
        · rfl
        · have hbeq : (f sym0 == f sym1) = true := beq_iff_eq.mpr hfab
          rw [bne, hbeq] at hfinj
          cases hfinj
        · cases hu2.1
      · rcases sym_cases b with rfl | rfl | rfl
        · have hbeq : (f sym0 == f sym1) = true := beq_iff_eq.mpr hfab.symm
          rw [bne, hbeq] at hfinj
          cases hfinj
        · rfl
        · cases hu2.1
      · cases hu1.1
    subst hab
    exact congrArg (List.cons a) (map_f_inj_on_binary f hfinj u1 u2 hu1.2 hu2.2 htail)

private theorem canonicalMidDPDA_accepts_own_suffix (P : StackProgram 2) (f : Sym → Sym)
    (hcan : isCanonicalMidDPDA P f = true) (u : Word) (hu : isBinaryWord u = true) :
    P.eval (u ++ ([symHash] ++ (u.map f).reverse)) = true := by
  rw [← List.append_assoc, canonicalMidDPDA_eval_eq_true_iff P f hcan]
  exact ⟨u, hu, rfl⟩

private theorem canonicalMidDPDA_rejects_other_suffix (P : StackProgram 2) (f : Sym → Sym)
    (hcan : isCanonicalMidDPDA P f = true) (hfinj : (f sym0 != f sym1) = true)
    (u1 u2 : Word) (hu1 : isBinaryWord u1 = true) (hu2 : isBinaryWord u2 = true)
    (hne : u1 ≠ u2) :
    P.eval (u2 ++ ([symHash] ++ (u1.map f).reverse)) = false := by
  cases hev : P.eval (u2 ++ ([symHash] ++ (u1.map f).reverse)) with
  | false => rfl
  | true =>
    rw [← List.append_assoc, canonicalMidDPDA_eval_eq_true_iff P f hcan] at hev
    rcases hev with ⟨u, hu, heq⟩
    rcases binary_split_hash_left u2 u (u1.map f).reverse (u.map f).reverse hu2 hu heq with ⟨rfl, hrev⟩
    have hmap : u1.map f = u2.map f := by
      have hrr := congrArg List.reverse hrev
      simpa [List.reverse_reverse] using hrr
    have hu12 : u1 = u2 := map_f_inj_on_binary f hfinj u1 u2 hu1 hu2 hmap
    exact False.elim (hne hu12)

/-- Parametric Meta-Theorem 2 (Universal 1-DCA Impossibility for ALL `m : Nat`):
    For ANY `P : StackProgram 2` and bijective binary transform `f` (`f sym0 != f sym1`)
    satisfying `isCanonicalMidDPDA P f = true`, and for EVERY `m : Nat` (arbitrarily many
    phases), NO `m`-phase 1-DCA can recognize `P` on `Σ*`! -/
theorem canonicalMidDPDA_not_1DCA (P : StackProgram 2) (f : Sym → Sym)
    (hcan : isCanonicalMidDPDA P f = true) (hfinj : (f sym0 != f sym1) = true)
    (m : Nat) :
    ¬ ∃ C : CounterProgram m, ∀ w : Word, C.eval w = P.eval w := by
  let L := 2 * m + 2
  have hbound : dcaConfigBound m L + 1 ≤ (binWords L).length := by
    rw [binWords_length L]
    exact exp_gt_dca_bound m
  let prefs : Fin (dcaConfigBound m L + 1) → Word :=
    fun i => (binWords L).get ⟨i.val, Nat.lt_of_lt_of_le i.isLt hbound⟩
  apply dca_oracle_impossibility P.eval m L prefs
  · intro i
    have hmem : prefs i ∈ binWords L :=
      get_mem (binWords L) ⟨i.val, Nat.lt_of_lt_of_le i.isLt hbound⟩
    rw [binWords_word_length L (prefs i) hmem]
    exact Nat.le_refl L
  · intro i j hij
    have hmem_i : prefs i ∈ binWords L :=
      get_mem (binWords L) ⟨i.val, Nat.lt_of_lt_of_le i.isLt hbound⟩
    have hmem_j : prefs j ∈ binWords L :=
      get_mem (binWords L) ⟨j.val, Nat.lt_of_lt_of_le j.isLt hbound⟩
    have hbin_i : isBinaryWord (prefs i) = true := binWords_isBinary L (prefs i) hmem_i
    have hbin_j : isBinaryWord (prefs j) = true := binWords_isBinary L (prefs j) hmem_j
    have hne : prefs i ≠ prefs j := by
      intro heq
      have hinj := nodup_get_inj (binWords L) (binWords_nodup L)
        ⟨i.val, Nat.lt_of_lt_of_le i.isLt hbound⟩
        ⟨j.val, Nat.lt_of_lt_of_le j.isLt hbound⟩ heq
      have hval : i.val = j.val := congrArg (fun x : Fin (binWords L).length => x.val) hinj
      exact hij (Fin.ext hval)
    refine ⟨[symHash] ++ ((prefs i).map f).reverse, ?_⟩
    rw [canonicalMidDPDA_accepts_own_suffix P f hcan (prefs i) hbin_i,
        canonicalMidDPDA_rejects_other_suffix P f hcan hfinj (prefs i) (prefs j) hbin_i hbin_j hne]
    decide

/-- Parametric Meta-Theorem 3 (Universal DFA Impossibility for ALL `k : Nat`):
    For ANY `P : StackProgram 2` and bijective binary transform `f` (`f sym0 != f sym1`)
    satisfying `isCanonicalMidDPDA P f = true`, and for EVERY `k : Nat`,
    NO `k`-state DFA can recognize `P` on `Σ*`! -/
theorem canonicalMidDPDA_not_DFA (P : StackProgram 2) (f : Sym → Sym)
    (hcan : isCanonicalMidDPDA P f = true) (hfinj : (f sym0 != f sym1) = true)
    (k : Nat) :
    ¬ ∃ M : DFA k, ∀ w : Word, M.eval w = P.eval w := by
  have hbound : k + 1 ≤ (binWords k).length := by
    rw [binWords_length k]
    exact pow2_ge_succ k
  let prefs : Fin (k + 1) → Word :=
    fun i => (binWords k).get ⟨i.val, Nat.lt_of_lt_of_le i.isLt hbound⟩
  apply dfa_oracle_impossibility P.eval k prefs
  intro i j hij
  have hmem_i : prefs i ∈ binWords k :=
    get_mem (binWords k) ⟨i.val, Nat.lt_of_lt_of_le i.isLt hbound⟩
  have hmem_j : prefs j ∈ binWords k :=
    get_mem (binWords k) ⟨j.val, Nat.lt_of_lt_of_le j.isLt hbound⟩
  have hbin_i : isBinaryWord (prefs i) = true := binWords_isBinary k (prefs i) hmem_i
  have hbin_j : isBinaryWord (prefs j) = true := binWords_isBinary k (prefs j) hmem_j
  have hne : prefs i ≠ prefs j := by
    intro heq
    have hinj := nodup_get_inj (binWords k) (binWords_nodup k)
      ⟨i.val, Nat.lt_of_lt_of_le i.isLt hbound⟩
      ⟨j.val, Nat.lt_of_lt_of_le j.isLt hbound⟩ heq
    have hval : i.val = j.val := congrArg (fun x : Fin (binWords k).length => x.val) hinj
    exact hij (Fin.ext hval)
  refine ⟨[symHash] ++ ((prefs i).map f).reverse, ?_⟩
  rw [canonicalMidDPDA_accepts_own_suffix P f hcan (prefs i) hbin_i,
      canonicalMidDPDA_rejects_other_suffix P f hcan hfinj (prefs i) (prefs j) hbin_i hbin_j hne]
  decide

/-- Master Protocol Checker (`checkFullChomskyProtocol`):
    Single computable boolean function verifying:
      1. Causal escalation chronology (`0 < t1 < t2 ≤ obs.length`)
      2. Level-1 DFA(k) impossibility on prefix `obs.take t1`
      3. Level-2 1-DCA(m) impossibility on prefix `obs.take t2`
      4. Level-3 DPDA agreement on all `obs`
      5. Parametric canonical DPDA structure & bijectivity (`f sym0 != f sym1`) -/
def checkFullChomskyProtocol {k m L : Nat} (obs : Obs) (t1 t2 : Nat)
    (mnPrefs  : Fin (k + 1) → Word)
    (mnSufs   : Fin (k + 1) → Fin (k + 1) → Word)
    (dcaPrefs : Fin (dcaConfigBound m L + 1) → Word)
    (dcaSufs  : Fin (dcaConfigBound m L + 1) → Fin (dcaConfigBound m L + 1) → Word)
    (P        : StackProgram 2)
    (f        : Sym → Sym) : Bool :=
  checkCausalEscalation obs t1 t2 mnPrefs mnSufs dcaPrefs dcaSufs P &&
  isCanonicalMidDPDA P f &&
  (f sym0 != f sym1)

/-- Master Theorem (`checkFullChomskyProtocol_sound`):
    If `checkFullChomskyProtocol` evaluates to `true` (via a single `by decide`), then SIMULTANEOUSLY:
      (1) Causal escalation timestamps `0 < t1 < t2 ≤ obs.length` hold,
      (2) No `DFA k` agrees with the Level-1 historical prefix `obs.take t1`,
      (3) No `CounterProgram m` agrees with the Level-2 historical prefix `obs.take t2`,
      (4) The synthesized `P : StackProgram 2` agrees with all `(w, a) ∈ obs`,
      (5) Infinite-domain specification holds for ALL `w ∈ Σ*`:
            `P.eval w = true ↔ ∃ u ∈ {0,1}*, w = u ++ [#] ++ (u.map f).reverse`,
      (6) Universal DFA separation holds for ALL `k' : Nat`:
            `∀ k' : Nat, ¬ ∃ M : DFA k', ∀ w : Word, M.eval w = P.eval w`,
      (7) Universal 1-DCA separation holds for ALL `m' : Nat`:
            `∀ m' : Nat, ¬ ∃ C : CounterProgram m', ∀ w : Word, C.eval w = P.eval w`. -/
theorem checkFullChomskyProtocol_sound {k m L : Nat} (obs : Obs) (t1 t2 : Nat)
    (mnPrefs  : Fin (k + 1) → Word)
    (mnSufs   : Fin (k + 1) → Fin (k + 1) → Word)
    (dcaPrefs : Fin (dcaConfigBound m L + 1) → Word)
    (dcaSufs  : Fin (dcaConfigBound m L + 1) → Fin (dcaConfigBound m L + 1) → Word)
    (P        : StackProgram 2)
    (f        : Sym → Sym)
    (h        : checkFullChomskyProtocol obs t1 t2 mnPrefs mnSufs dcaPrefs dcaSufs P f = true) :
    (0 < t1 ∧ t1 < t2 ∧ t2 ≤ obs.length) ∧
    (¬ ∃ M : DFA k, ∀ p ∈ obs.take t1, M.eval p.1 = p.2) ∧
    (¬ ∃ C : CounterProgram m, ∀ p ∈ obs.take t2, C.eval p.1 = p.2) ∧
    (∀ p ∈ obs, P.eval p.1 = p.2) ∧
    (∀ w : Word, P.eval w = true ↔ ∃ u : Word, isBinaryWord u = true ∧ w = u ++ [symHash] ++ (u.map f).reverse) ∧
    (∀ k' : Nat, ¬ ∃ M : DFA k', ∀ w : Word, M.eval w = P.eval w) ∧
    (∀ m' : Nat, ¬ ∃ C : CounterProgram m', ∀ w : Word, C.eval w = P.eval w) := by
  unfold checkFullChomskyProtocol at h
  simp only [Bool.and_eq_true] at h
  rcases h with ⟨⟨hcaus, hcan⟩, hfinj⟩
  rcases checkCausalEscalation_sound obs t1 t2 mnPrefs mnSufs dcaPrefs dcaSufs P hcaus with
    ⟨ht, hmn, hdca, hstk⟩
  exact ⟨
    ht,
    hmn,
    hdca,
    hstk,
    canonicalMidDPDA_eval_eq_true_iff P f hcan,
    canonicalMidDPDA_not_DFA P f hcan hfinj,
    canonicalMidDPDA_not_1DCA P f hcan hfinj
  ⟩

end Gate12Hierarchy

#print axioms Gate12Hierarchy.checkMNCert_sound
#print axioms Gate12Hierarchy.check1DCACert_sound
#print axioms Gate12Hierarchy.checkCausalEscalation_sound
#print axioms Gate12Hierarchy.canonicalMidDPDA_eval_eq_true_iff
#print axioms Gate12Hierarchy.canonicalMidDPDA_not_1DCA
#print axioms Gate12Hierarchy.canonicalMidDPDA_not_DFA
#print axioms Gate12Hierarchy.checkFullChomskyProtocol_sound
