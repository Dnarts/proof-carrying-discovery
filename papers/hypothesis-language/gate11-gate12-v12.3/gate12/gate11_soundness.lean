/-
  Gate 11 — Formal Soundness of Myhill-Nerode Impossibility & 1-DCA Separation
  in Pure Lean 4 Core (Zero External Dependencies, Complete Proofs).

  Verify locally with:
      lean gate11_soundness.lean

  Formalizes:
    1. `dfa_runFrom_append`: compositional state transition law for any k-state DFA.
    2. `pigeonhole_fin`: constructive pigeonhole principle for `Fin (k + 1) → Fin k`
       in pure Lean 4 core (no Mathlib).
    3. `myhill_nerode_impossibility`: soundness of Gate 11's Myhill-Nerode certificate —
       any (k + 1) pairwise distinguishable prefixes refute ALL k-state DFAs.
    4. `oneDCA_0n1n_zeros_ones_true` & `oneDCA_0n1n_zeros_ones_false`: exact behavior
       of Gate 11's sandboxed 1-DCA (`one_dca_0n1n`) on `0^n 1^m`.
    5. `oneDCA_0n1n_not_regular`: strict class separation — for EVERY k : Nat, no
       k-state DFA agrees with `oneDCA_0n1n` on all of `{0,1}*`.
    6. `oneDCA_0n1n_eq_true_iff`: full infinite-domain soundness bridging the executable
       1-DCA directly to the specification `∃ n, w = 0^n ++ 1^n`.
-/

namespace Gate11Soundness

/-- Binary word over {0, 1} represented as `List Bool` (false = '0', true = '1'). -/
abbrev Word := List Bool

/-- Deterministic finite automaton with `k` states over binary alphabet `Bool`. -/
structure DFA (k : Nat) where
  start  : Fin k
  step   : Fin k → Bool → Fin k
  accept : Fin k → Bool

def DFA.runFrom {k : Nat} (M : DFA k) : Fin k → Word → Fin k
  | s, []      => s
  | s, c :: ws => M.runFrom (M.step s c) ws

def DFA.eval {k : Nat} (M : DFA k) (w : Word) : Bool :=
  M.accept (M.runFrom M.start w)

/-- Theorem 1: DFA transitions compose over word concatenation. -/
theorem dfa_runFrom_append {k : Nat} (M : DFA k) :
    ∀ (u v : Word) (s : Fin k),
      M.runFrom s (u ++ v) = M.runFrom (M.runFrom s u) v
  | [],      _, _ => rfl
  | c :: us, v, s => dfa_runFrom_append M us v (M.step s c)

/-- Helper: check if any `i : Fin n` satisfies a decidable predicate `P`. -/
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
      | some val =>
        rw [hrec] at hnone
        cases hnone
      | none =>
        have hall := findFin_none_spec n
          (fun j => P ⟨j.val, Nat.lt_trans j.isLt (Nat.lt_succ_self n)⟩) hrec
        by_cases hi : i.val = n
        · have heq : i = ⟨n, Nat.lt_succ_self n⟩ := Fin.ext hi
          rw [heq]
          exact hlast
        · have hlt : i.val < n := by omega
          exact hall ⟨i.val, hlt⟩

/-- Theorem 2: Constructive pigeonhole principle for `Fin (k + 1) → Fin k`. -/
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

/-- Theorem 3 (Soundness of Gate 11 Myhill-Nerode Certificate):
    If `prefixes` gives `k + 1` pairwise distinguishable prefixes for oracle `O`,
    then NO `k`-state DFA can agree with `O` on all words. -/
theorem myhill_nerode_impossibility
    (O : Word → Bool) (k : Nat) (prefixes : Fin (k + 1) → Word)
    (hdist : ∀ i j : Fin (k + 1), i ≠ j →
      ∃ v : Word, O (prefixes i ++ v) ≠ O (prefixes j ++ v)) :
    ¬ ∃ M : DFA k, ∀ w : Word, M.eval w = O w := by
  rintro ⟨M, hM⟩
  let stateOf : Fin (k + 1) → Fin k := fun i => M.runFrom M.start (prefixes i)
  rcases pigeonhole_fin k stateOf with ⟨i, j, hij, hst⟩
  rcases hdist i j hij with ⟨v, hv⟩
  have h1 : M.eval (prefixes i ++ v) = M.eval (prefixes j ++ v) := by
    unfold DFA.eval
    rw [dfa_runFrom_append, dfa_runFrom_append]
    change M.accept (M.runFrom (stateOf i) v) = M.accept (M.runFrom (stateOf j) v)
    rw [hst]
  rw [hM, hM] at h1
  exact hv h1

/-! ## Gate 11 Executable 1-DCA for `{0^n 1^n | n ≥ 0}` -/

def step0n1n : Option (Bool × Nat) → Bool → Option (Bool × Nat)
  | none,                  _     => none
  | some (false, c),       false => some (false, c + 1)
  | some (false, 0),       true  => none
  | some (false, c + 1),   true  => some (true, c)
  | some (true,  _),       false => none
  | some (true,  0),       true  => none
  | some (true,  c + 1),   true  => some (true, c)

def run0n1nFrom : Option (Bool × Nat) → Word → Option (Bool × Nat)
  | st, []      => st
  | st, c :: ws => run0n1nFrom (step0n1n st c) ws

def accept0n1n : Option (Bool × Nat) → Bool
  | some (_, 0) => true
  | _           => false

def oneDCA_0n1n (w : Word) : Bool :=
  accept0n1n (run0n1nFrom (some (false, 0)) w)

private theorem run0n1nFrom_none : ∀ w : Word, run0n1nFrom none w = none
  | []      => rfl
  | _ :: ws => run0n1nFrom_none ws

private theorem run0n1nFrom_append :
    ∀ (u v : Word) (st : Option (Bool × Nat)),
      run0n1nFrom st (u ++ v) = run0n1nFrom (run0n1nFrom st u) v
  | [],      _, _  => rfl
  | c :: us, v, st => run0n1nFrom_append us v (step0n1n st c)

private theorem run0n1nFrom_zeros :
    ∀ (n c : Nat),
      run0n1nFrom (some (false, c)) (List.replicate n false) = some (false, c + n)
  | 0,     c => rfl
  | n + 1, c => by
    simp only [List.replicate, run0n1nFrom, step0n1n]
    rw [run0n1nFrom_zeros n (c + 1)]
    have hadd : c + 1 + n = c + (n + 1) := by omega
    rw [hadd]

private theorem run0n1nFrom_ones_le :
    ∀ (m c : Nat) (ph : Bool), m ≤ c →
      accept0n1n (run0n1nFrom (some (ph, c)) (List.replicate m true)) =
        decide (c = m)
  | 0, 0, _, _ => rfl
  | 0, _ + 1, _, _ => rfl
  | m + 1, c + 1, ph, hle => by
    cases ph <;> simp only [List.replicate, run0n1nFrom, step0n1n]
    · rw [run0n1nFrom_ones_le m c true (by omega)]
      by_cases h : c = m <;> simp [h] <;> omega
    · rw [run0n1nFrom_ones_le m c true (by omega)]
      by_cases h : c = m <;> simp [h] <;> omega

private theorem run0n1nFrom_ones_gt :
    ∀ (m c : Nat) (ph : Bool), c < m →
      run0n1nFrom (some (ph, c)) (List.replicate m true) = none
  | m + 1, 0, ph, _ => by
    cases ph <;> simp only [List.replicate, run0n1nFrom, step0n1n, run0n1nFrom_none]
  | m + 1, c + 1, ph, hlt => by
    cases ph <;> simp only [List.replicate, run0n1nFrom, step0n1n]
    · exact run0n1nFrom_ones_gt m c true (by omega)
    · exact run0n1nFrom_ones_gt m c true (by omega)

/-- Theorem 4a: `oneDCA_0n1n` accepts `0^n 1^n` for all `n : Nat`. -/
theorem oneDCA_0n1n_zeros_ones_true (n : Nat) :
    oneDCA_0n1n (List.replicate n false ++ List.replicate n true) = true := by
  unfold oneDCA_0n1n
  rw [run0n1nFrom_append, run0n1nFrom_zeros]
  simp only [Nat.zero_add]
  rw [run0n1nFrom_ones_le n n false (Nat.le_refl n)]
  simp

/-- Theorem 4b: `oneDCA_0n1n` rejects `0^n 1^m` whenever `n ≠ m`. -/
theorem oneDCA_0n1n_zeros_ones_false (n m : Nat) (h : n ≠ m) :
    oneDCA_0n1n (List.replicate n false ++ List.replicate m true) = false := by
  unfold oneDCA_0n1n
  rw [run0n1nFrom_append, run0n1nFrom_zeros]
  simp only [Nat.zero_add]
  by_cases hle : m ≤ n
  · rw [run0n1nFrom_ones_le m n false hle]
    simp [h]
  · rw [run0n1nFrom_ones_gt m n false (by omega)]
    rfl

/-- Theorem 5 (Strict Class Separation for Gate 11):
    For EVERY `k : Nat`, no `k`-state DFA recognizes `oneDCA_0n1n`. -/
theorem oneDCA_0n1n_not_regular (k : Nat) :
    ¬ ∃ M : DFA k, ∀ w : Word, M.eval w = oneDCA_0n1n w := by
  apply myhill_nerode_impossibility oneDCA_0n1n k (fun i => List.replicate i.val false)
  intro i j hij
  refine ⟨List.replicate i.val true, ?_⟩
  rw [oneDCA_0n1n_zeros_ones_true i.val]
  have hval : j.val ≠ i.val := fun h => hij (Fin.ext h.symm)
  rw [oneDCA_0n1n_zeros_ones_false j.val i.val hval]
  decide

/-! ## Theorem 6: Full Infinite-Domain Soundness of `oneDCA_0n1n` -/

private theorem run0n1nFrom_true_accept_iff :
    ∀ (w : Word) (c : Nat),
      accept0n1n (run0n1nFrom (some (true, c)) w) = true ↔
        w = List.replicate c true
  | [], 0 => by simp [run0n1nFrom, accept0n1n]
  | [], c + 1 => by simp [run0n1nFrom, accept0n1n]
  | false :: ws, c => by
    simp only [run0n1nFrom, step0n1n, run0n1nFrom_none, accept0n1n, Bool.false_eq_true, false_iff]
    cases c <;> simp [List.replicate]
  | true :: ws, 0 => by
    simp [run0n1nFrom, step0n1n, run0n1nFrom_none, accept0n1n]
  | true :: ws, c + 1 => by
    simp only [run0n1nFrom, step0n1n, List.replicate]
    rw [run0n1nFrom_true_accept_iff ws c]
    constructor
    · intro h; rw [h]
    · intro h; injection h

private theorem run0n1nFrom_false_accept_iff :
    ∀ (w : Word) (c : Nat),
      accept0n1n (run0n1nFrom (some (false, c)) w) = true ↔
        ∃ k : Nat, w = List.replicate k false ++ List.replicate (c + k) true
  | [], 0 => by
    constructor
    · intro _; exact ⟨0, rfl⟩
    · intro _; rfl
  | [], c + 1 => by
    simp only [run0n1nFrom, accept0n1n, Bool.false_eq_true, false_iff]
    rintro ⟨k, hk⟩
    have hlen := congrArg List.length hk
    simp at hlen
    omega
  | false :: ws, c => by
    simp only [run0n1nFrom, step0n1n]
    rw [run0n1nFrom_false_accept_iff ws (c + 1)]
    constructor
    · rintro ⟨k, hk⟩
      refine ⟨k + 1, ?_⟩
      rw [List.replicate_succ, List.cons_append, hk]
      have hadd : c + 1 + k = c + (k + 1) := by omega
      rw [hadd]
    · rintro ⟨k, hk⟩
      cases k with
      | zero =>
        cases c with
        | zero => simp at hk
        | succ c' => simp [List.replicate] at hk
      | succ k' =>
        rw [List.replicate_succ, List.cons_append] at hk
        injection hk with _ htail
        refine ⟨k', ?_⟩
        rw [htail]
        have hadd : c + (k' + 1) = c + 1 + k' := by omega
        rw [hadd]
  | true :: ws, 0 => by
    simp only [run0n1nFrom, step0n1n, run0n1nFrom_none, accept0n1n]
    constructor
    · intro h; cases h
    · rintro ⟨k, hk⟩
      cases k with
      | zero => simp at hk
      | succ k' => simp [List.replicate] at hk
  | true :: ws, c + 1 => by
    simp only [run0n1nFrom, step0n1n]
    rw [run0n1nFrom_true_accept_iff ws c]
    constructor
    · intro h
      refine ⟨0, ?_⟩
      simp [List.replicate, h]
    · rintro ⟨k, hk⟩
      cases k with
      | zero =>
        simp [List.replicate] at hk
        exact hk
      | succ k' =>
        simp [List.replicate] at hk

/-- Theorem 6: `oneDCA_0n1n` accepts `w` if and only if `w = 0^n 1^n` for some `n : Nat`. -/
theorem oneDCA_0n1n_eq_true_iff (w : Word) :
    oneDCA_0n1n w = true ↔ ∃ n : Nat, w = List.replicate n false ++ List.replicate n true := by
  unfold oneDCA_0n1n
  simpa using run0n1nFrom_false_accept_iff w 0

end Gate11Soundness

#print axioms Gate11Soundness.dfa_runFrom_append
#print axioms Gate11Soundness.pigeonhole_fin
#print axioms Gate11Soundness.myhill_nerode_impossibility
#print axioms Gate11Soundness.oneDCA_0n1n_not_regular
#print axioms Gate11Soundness.oneDCA_0n1n_eq_true_iff
