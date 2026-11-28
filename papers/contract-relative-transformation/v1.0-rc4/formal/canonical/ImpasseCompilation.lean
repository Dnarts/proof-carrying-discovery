import BudgetedPruning

/-! Compiling a finite read obstruction into a reusable certified no-good.
The deletion algorithm produces inclusion-minimal cores, not minimum cardinality.
No empirical similarity, unchecked identity or classical choice is needed. -/
namespace CRTT.ImpasseCompilation
open CRTT.MorphismDiscovery CRTT.CertifiedPruning
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

def Sub (xs ys : List α) : Prop := ∀ e ∈ xs, e ∈ ys

def MonotoneBad (bad : List α → Bool) : Prop :=
  ∀ xs ys, Sub xs ys → bad xs = true → bad ys = true

def without [DecidableEq α] (xs : List α) (e : α) : List α :=
  xs.filter (fun v => decide (v ≠ e))

/-- Test each original occurrence once. Kept constraints need not be retested:
if removal was impossible before further deletions, it remains impossible. -/
def shrink (bad : List α → Bool) : List α → List α → List α
  | [], kept => kept
  | e :: todo, kept =>
    if bad (kept ++ todo) then shrink bad todo kept
    else shrink bad todo (e :: kept)

def ShrinkSpec [DecidableEq α] (bad : List α → Bool)
    (todo kept out : List α) : Prop :=
  bad out = true ∧ Sub out (kept ++ todo) ∧
    ∀ e ∈ out, e ∉ kept → bad (without out e) = false

theorem shrink_spec [DecidableEq α] (bad : List α → Bool) (mono : MonotoneBad bad) :
    ∀ (todo kept : List α), bad (kept ++ todo) = true →
      ShrinkSpec bad todo kept (shrink bad todo kept) := by
  intro todo
  induction todo with
  | nil =>
    intro kept hb
    have hk : bad kept = true := by simpa using hb
    exact ⟨hk, fun e he => List.mem_append.mpr (Or.inl he),
      fun e he hn => False.elim (hn he)⟩
  | cons a todo ih =>
    intro kept hb
    by_cases hd : bad (kept ++ todo) = true
    · have hi := ih kept hd
      have he : shrink bad (a :: todo) kept = shrink bad todo kept := by
        simp [shrink, hd]
      rw [he]
      refine ⟨hi.1, ?_, hi.2.2⟩
      intro e hm
      rcases List.mem_append.mp (hi.2.1 e hm) with h | h
      · exact List.mem_append.mpr (Or.inl h)
      · exact List.mem_append.mpr (Or.inr (List.Mem.tail _ h))
    · have hmove : Sub (kept ++ (a :: todo)) ((a :: kept) ++ todo) := by
        intro e hm
        rcases List.mem_append.mp hm with h | h
        · exact List.mem_append.mpr (Or.inl (List.Mem.tail _ h))
        · rcases List.mem_cons.mp h with he | ht
          · subst e
            exact List.mem_append.mpr (Or.inl (List.Mem.head _))
          · exact List.mem_append.mpr (Or.inr ht)
      have hi := ih (a :: kept) (mono _ _ hmove hb)
      have he : shrink bad (a :: todo) kept = shrink bad todo (a :: kept) := by
        simp [shrink, hd]
      rw [he]
      let out := shrink bad todo (a :: kept)
      have hsub : Sub out (kept ++ (a :: todo)) := by
        intro e hm
        rcases List.mem_append.mp (hi.2.1 e hm) with h | h
        · rcases List.mem_cons.mp h with he' | ht
          · subst e
            exact List.mem_append.mpr (Or.inr (List.Mem.head _))
          · exact List.mem_append.mpr (Or.inl ht)
        · exact List.mem_append.mpr (Or.inr (List.Mem.tail _ h))
      refine ⟨hi.1, hsub, ?_⟩
      intro e hm hn
      by_cases hea : e = a
      · subst e
        have hwithout : Sub (without out a) (kept ++ todo) := by
          intro v hv
          have hf : v ∈ out ∧ decide (v ≠ a) = true := List.mem_filter.mp hv
          have hne : v ≠ a := of_decide_eq_true hf.2
          rcases List.mem_append.mp (hsub v hf.1) with h | h
          · exact List.mem_append.mpr (Or.inl h)
          · rcases List.mem_cons.mp h with he' | ht
            · exact False.elim (hne he')
            · exact List.mem_append.mpr (Or.inr ht)
        change bad (without out a) = false
        cases hval : bad (without out a) with
        | false => rfl
        | true => exact False.elim (hd (mono _ _ hwithout hval))
      · exact hi.2.2 e hm (by
          intro h
          rcases List.mem_cons.mp h with h | h
          · exact hea h
          · exact hn h)

variable {sw sp sa tw tp ta : Nat}
variable (S : IndexedTask sw sp sa) (T : IndexedTask tw tp ta)

def rowBad (x : Fin tw) (rho : PartialAssign sp tp) : Bool :=
  (partialPortWorlds S T rho x).isEmpty

theorem rowBad_iff (x : Fin tw) (rho : PartialAssign sp tp) :
    rowBad S T x rho = true ↔ partialPortWorlds S T rho x = [] := by
  unfold rowBad
  cases partialPortWorlds S T rho x <;> simp

theorem rows_antitone (x : Fin tw) (a b : PartialAssign sp tp) (h : Sub a b) :
    Sub (partialPortWorlds S T b x) (partialPortWorlds S T a x) := by
  intro y hy
  unfold partialPortWorlds at hy ⊢
  rw [List.mem_filter] at hy ⊢
  refine ⟨hy.1, ?_⟩
  change allB (fun e : Fin sp × Fin tp => decide (T.read e.2 x = S.read e.1 y)) a = true
  have hall := (allB_iff (fun e : Fin sp × Fin tp => decide (T.read e.2 x = S.read e.1 y)) b).mp hy.2
  exact (allB_iff _ _).mpr (fun e he => hall e (h e he))

theorem rowBad_monotone (x : Fin tw) : MonotoneBad (rowBad S T x) := by
  intro a b hab ha
  apply (rowBad_iff S T x b).mpr
  have he := (rowBad_iff S T x a).mp ha
  cases hb : partialPortWorlds S T b x with
  | nil => rfl
  | cons y ys =>
    have hm : y ∈ partialPortWorlds S T b x := by rw [hb]; exact List.Mem.head _
    have hx := rows_antitone S T x a b hab y hm
    rw [he] at hx
    cases hx

structure ObstructionCore where
  world : Fin tw
  constraints : PartialAssign sp tp
  emptyRow : rowBad S T world constraints = true

structure Extraction (x : Fin tw) (rho : PartialAssign sp tp) where
  constraints : PartialAssign sp tp
  emptyRow : rowBad S T x constraints = true
  subset : Sub constraints rho
  irreducible : ∀ e ∈ constraints, rowBad S T x (without constraints e) = false

def extract (x : Fin tw) (rho : PartialAssign sp tp) (h : rowBad S T x rho = true) :
    Extraction S T x rho := by
  let out := shrink (rowBad S T x) rho []
  have hs := shrink_spec (rowBad S T x) (rowBad_monotone S T x) rho []
    (by simpa using h)
  exact ⟨out, hs.1, fun e he => by simpa using hs.2.1 e he,
    fun e he => hs.2.2 e he (by intro hn; cases hn)⟩

def toCore {x : Fin tw} {rho : PartialAssign sp tp} (e : Extraction S T x rho) :
    ObstructionCore S T := ⟨x, e.constraints, e.emptyRow⟩

-- `decide (x ∈ l)` instantiates `Decidable` through the `BEq`-based membership
-- instance, which is non-constructive and imports `Classical.choice` as soon as
-- it is unfolded. This structural checker branches on propositional equality
-- supplied by `DecidableEq`, so its correctness proof stays constructive.
def memB {α : Type} [DecidableEq α] (x : α) : List α → Bool
  | [] => false
  | y :: ys => if x = y then true else memB x ys

theorem memB_iff {α : Type} [DecidableEq α] (x : α) (l : List α) :
    memB x l = true ↔ x ∈ l := by
  induction l with
  | nil => simp [memB]
  | cons y ys ih =>
    unfold memB
    by_cases h : x = y
    · simp [h]
    · simp [h, ih]

def containsCore (core : PartialAssign sp tp) (rho : PartialAssign sp tp) : Bool :=
  allB (fun e => memB e rho) core

theorem containsCore_iff (core rho : PartialAssign sp tp) :
    containsCore core rho = true ↔ Sub core rho := by
  unfold containsCore Sub
  constructor
  · intro h e he
    have hm := (allB_iff (fun e => memB e rho) core).mp h e he
    exact (memB_iff e rho).mp hm
  · intro h
    apply (allB_iff _ _).mpr
    intro e he
    exact (memB_iff e rho).mpr (h e he)

theorem core_excludes (core : ObstructionCore S T) (rho : PartialAssign sp tp)
    (h : Sub core.constraints rho) : ¬ ∃ M : Morphism S T, Extends S T M rho := by
  have hb := rowBad_monotone S T core.world core.constraints rho h core.emptyRow
  exact empty_partialReadRow_prunes S T rho core.world ((rowBad_iff S T core.world rho).mp hb)

def compileCore (core : ObstructionCore S T) (cost : Nat) : CertifiedRule S T where
  keep := fun rho => !(containsCore core.constraints rho)
  cost := cost
  sound := by
    intro M rho hext
    change (!(containsCore core.constraints rho)) = true
    cases h : containsCore core.constraints rho with
    | false => rfl
    | true => exact False.elim (core_excludes S T core rho
        ((containsCore_iff core.constraints rho).mp h) ⟨M, hext⟩)

theorem compileCore_rejects (core : ObstructionCore S T) (cost : Nat)
    (rho : PartialAssign sp tp) (h : Sub core.constraints rho) :
    (compileCore S T core cost).keep rho = false := by
  change (!(containsCore core.constraints rho)) = false
  rw [(containsCore_iff core.constraints rho).mpr h]
  rfl

theorem compiled_search_complete (core : ObstructionCore S T) (cost : Nat)
    (N : Morphism S T) : N ∈ prunedDiscover S T (compileCore S T core cost) ↔ N ∈ discoverAll S T :=
  prunedDiscover_iff S T (compileCore S T core cost) N

/-! Exact set-cover interpretation: every source world is rejected by at
least one constraint. This is not a minimum-cover algorithm. -/
theorem allB_false_exists (p : α → Bool) (xs : List α) (h : allB p xs = false) :
    ∃ e ∈ xs, p e = false := by
  induction xs with
  | nil => simp [allB] at h
  | cons e rest ih =>
    cases hp : p e with
    | false => exact ⟨e, List.Mem.head _, hp⟩
    | true =>
      have ht : allB p rest = false := by simpa [allB, hp] using h
      obtain ⟨v, hv, hf⟩ := ih ht
      exact ⟨v, List.Mem.tail _ hv, hf⟩

theorem rowBad_cover_iff (x : Fin tw) (rho : PartialAssign sp tp) :
    rowBad S T x rho = true ↔
      ∀ y : Fin sw, ∃ e ∈ rho, T.read e.2 x ≠ S.read e.1 y := by
  constructor
  · intro h y
    have he := (rowBad_iff S T x rho).mp h
    cases hread : partialReadOK S T rho x y with
    | true =>
      have hm : y ∈ partialPortWorlds S T rho x :=
        List.mem_filter.mpr ⟨mem_indices sw y, hread⟩
      rw [he] at hm
      cases hm
    | false =>
      obtain ⟨e, hm, hf⟩ := allB_false_exists
        (fun e : Fin sp × Fin tp => decide (T.read e.2 x = S.read e.1 y)) rho hread
      exact ⟨e, hm, fun heq => by rw [decide_eq_true heq] at hf; cases hf⟩
  · intro h
    apply (rowBad_iff S T x rho).mpr
    cases hr : partialPortWorlds S T rho x with
    | nil => rfl
    | cons y rest =>
      have hm : y ∈ partialPortWorlds S T rho x := by rw [hr]; exact List.Mem.head _
      obtain ⟨e, he, hne⟩ := h y
      have hp : partialReadOK S T rho x y = true := (List.mem_filter.mp hm).2
      have hall : decide (T.read e.2 x = S.read e.1 y) = true :=
        (allB_iff _ _).mp hp e he
      exact False.elim (hne (of_decide_eq_true hall))

/-! Certified transfer: a new row can be empty for a different reason, but
this certificate specifically transports the old obstruction via reflection
of every translated constraint. Map direction on source worlds is new → old. -/
variable {sw' sp' sa' tw' tp' ta' : Nat}
variable (S' : IndexedTask sw' sp' sa') (T' : IndexedTask tw' tp' ta')

structure CoreTransport (core : ObstructionCore S T) where
  targetWorld : Fin tw'
  constraintMap : (Fin sp × Fin tp) → (Fin sp' × Fin tp')
  worldMap : Fin sw' → Fin sw
  reflectRead : ∀ e ∈ core.constraints, ∀ y : Fin sw',
    T'.read (constraintMap e).2 targetWorld = S'.read (constraintMap e).1 y →
    T.read e.2 core.world = S.read e.1 (worldMap y)

def transportCore (core : ObstructionCore S T) (m : CoreTransport S T S' T' core) :
    ObstructionCore S' T' := by
  refine ⟨m.targetWorld, core.constraints.map m.constraintMap, ?_⟩
  apply (rowBad_cover_iff S' T' _ _).mpr
  intro y
  obtain ⟨e, he, hn⟩ := (rowBad_cover_iff S T _ _).mp core.emptyRow (m.worldMap y)
  exact ⟨m.constraintMap e, List.mem_map.mpr ⟨e, he, rfl⟩,
    fun h => hn (m.reflectRead e he y h)⟩

#print axioms shrink_spec
#print axioms rowBad_iff
#print axioms rows_antitone
#print axioms rowBad_monotone
#print axioms extract
#print axioms containsCore_iff
#print axioms core_excludes
#print axioms compileCore
#print axioms compileCore_rejects
#print axioms compiled_search_complete
#print axioms allB_false_exists
#print axioms rowBad_cover_iff
#print axioms transportCore
end CRTT.ImpasseCompilation
