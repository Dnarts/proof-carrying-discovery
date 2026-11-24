/-
  repair_budget_atom_v1_1.lean
  Self-contained Lean 4.36.0 formalization of:
    - "Алгебра исследовательской ревизии" (epistemic-revision-adt.pdf)
    - "Атом исследовательского ремонта" (repair-budget-ca-prepreprint.ru.md.txt)

  13 Core Theorems (zero Mathlib, zero `sorry`, zero `native_decide`):
    1.  lemma1_common_repair_iff          (Lemma 1: C(W) <= B <-> immediate common repair)
    2.  pairwise_intersection_insufficient ({a,b}, {b,c}, {a,c} counterexample)
    3.  refinement_grows_common_repairs   (W' subset W -> G(W) subset G(W'))
    4.  lemma2_one_step_probe_iff         (Lemma 2: c(q) + max_y C(W_{q,y}) <= B <-> 1-step plan)
    5.  confidence_up_affordability_down  (Two-world atom: thresholds B=2, 3, 4)
    6.  minimaxV_iff_validPlanTree        (Soundness & completeness of minimax recursion V_h(W))
    7.  factorization_iff_kernel_inclusion (g = d o O_Q0|_W <-> ker(O_Q0|_W) subset ker(g|_W))
    8.  contravariant_refutation_transfer (Target->Source model map transfers refutation)
    9.  foldMasks_exact_common_repair     (Exactness of 5-state streaming mask fold for all N)
    10. foldMasks_order_invariant         (Commutativity & associativity of mask fold)
    11. myhill_nerode_five_states_distinct (All 5 FoldAcc states {EMPTY,00,01,10,11} pairwise distinct)
    12. marginal_equality_not_joint_equality (equal 1-D marginals, different 2-D joint law, 2 passive probes)
-/

namespace RepairBudgetAtomV1

/-! ## 1. Extended Cost Arithmetic (Nat ∪ {+∞}) -/

inductive Cost where
  | fin (n : Nat)
  | inf
  deriving DecidableEq, Repr

def leBudget : Cost → Nat → Prop
  | .fin n, B => n ≤ B
  | .inf, _ => False

instance instDecidableLeBudget (c : Cost) (B : Nat) : Decidable (leBudget c B) :=
  match c with
  | .fin n => inferInstanceAs (Decidable (n ≤ B))
  | .inf => isFalse (fun h => h)

def minCost : Cost → Cost → Cost
  | .fin a, .fin b => .fin (if a ≤ b then a else b)
  | .fin a, .inf => .fin a
  | .inf, c => c

def maxCost : Cost → Cost → Cost
  | .fin a, .fin b => .fin (if a ≤ b then b else a)
  | .inf, _ => .inf
  | _, .inf => .inf

def addNatCost (k : Nat) : Cost → Cost
  | .fin n => .fin (k + n)
  | .inf => .inf

private theorem leBudget_minCost (c1 c2 : Cost) (B : Nat) :
    leBudget (minCost c1 c2) B ↔ leBudget c1 B ∨ leBudget c2 B := by
  cases c1 <;> cases c2 <;> simp only [minCost, leBudget]
  · rename_i a b
    split <;> constructor <;> intro h <;> omega
  · constructor
    · intro h; exact Or.inl h
    · intro h; cases h with | inl h => exact h | inr h => exact False.elim h
  · constructor
    · intro h; exact Or.inr h
    · intro h; cases h with | inl h => exact False.elim h | inr h => exact h
  · constructor
    · intro h; exact False.elim h
    · intro h; cases h with | inl h => exact h | inr h => exact h

private theorem leBudget_maxCost (c1 c2 : Cost) (B : Nat) :
    leBudget (maxCost c1 c2) B ↔ leBudget c1 B ∧ leBudget c2 B := by
  cases c1 <;> cases c2 <;> simp only [maxCost, leBudget]
  · rename_i a b
    split <;> constructor <;> intro h <;> omega
  · constructor
    · intro h; exact False.elim h
    · intro h; exact h.2
  · constructor
    · intro h; exact False.elim h
    · intro h; exact h.1
  · constructor
    · intro h; exact False.elim h
    · intro h; exact h.1

private theorem leBudget_addNatCost (k : Nat) (c : Cost) (B : Nat) :
    leBudget (addNatCost k c) B ↔ k ≤ B ∧ leBudget c (B - k) := by
  cases c <;> simp only [addNatCost, leBudget]
  · constructor <;> intro h <;> omega
  · constructor
    · intro h; exact False.elim h
    · intro h; exact h.2

/-! ## 2. Lemma 1 (Common Repair), Monotonicity & Pairwise Counterexample -/

def repairOkBool {Ω A : Type} (R : Ω → A → Bool) (W : List Ω) (a : A) : Bool :=
  W.all (fun ω => R ω a)

def RepairOk {Ω A : Type} (R : Ω → A → Bool) (W : List Ω) (a : A) : Prop :=
  ∀ ω ∈ W, R ω a = true

private theorem repairOkBool_eq_true {Ω A : Type} (R : Ω → A → Bool) (W : List Ω) (a : A) :
    repairOkBool R W a = true ↔ RepairOk R W a := by
  induction W with
  | nil => simp [repairOkBool, RepairOk]
  | cons w ws ih =>
    unfold repairOkBool at ih ⊢
    simp only [List.all_cons, Bool.and_eq_true, RepairOk, List.mem_cons]
    rw [ih]
    constructor
    · intro h ω hmem
      rcases h with ⟨h1, h2⟩
      cases hmem with
      | inl heq => subst heq; exact h1
      | inr htail => exact h2 ω htail
    · intro h
      exact ⟨h w (Or.inl rfl), fun ω htail => h ω (Or.inr htail)⟩

def minCommonRepairCost {Ω A : Type} (R : Ω → A → Bool) (costA : A → Nat)
    (actions : List A) (W : List Ω) : Cost :=
  match actions with
  | [] => .inf
  | a :: rest =>
    let here := if repairOkBool R W a then .fin (costA a) else .inf
    minCost here (minCommonRepairCost R costA rest W)

def HasImmediateRepair {Ω A : Type} (R : Ω → A → Bool) (costA : A → Nat)
    (actions : List A) (W : List Ω) (B : Nat) : Prop :=
  ∃ a ∈ actions, RepairOk R W a ∧ costA a ≤ B

/-- Lemma 1: An immediate guaranteed repair exists iff C(W) <= B. -/
theorem lemma1_common_repair_iff {Ω A : Type} (R : Ω → A → Bool) (costA : A → Nat)
    (actions : List A) (W : List Ω) (B : Nat) :
    leBudget (minCommonRepairCost R costA actions W) B ↔
      HasImmediateRepair R costA actions W B := by
  induction actions with
  | nil =>
    simp [minCommonRepairCost, leBudget, HasImmediateRepair]
  | cons a rest ih =>
    simp only [minCommonRepairCost]
    rw [leBudget_minCost, ih]
    constructor
    · intro h
      cases h with
      | inl hHere =>
        cases hOk : repairOkBool R W a with
        | false =>
          rw [hOk] at hHere
          simp [leBudget] at hHere
        | true =>
          rw [hOk] at hHere
          simp [leBudget] at hHere
          exact ⟨a, List.Mem.head _, (repairOkBool_eq_true R W a).mp hOk, hHere⟩
      | inr hRest =>
        rcases hRest with ⟨a', ha', hOk', hCost'⟩
        exact ⟨a', List.Mem.tail _ ha', hOk', hCost'⟩
    · intro h
      rcases h with ⟨a', ha', hOk', hCost'⟩
      cases ha' with
      | head =>
        apply Or.inl
        have hB : repairOkBool R W a = true := (repairOkBool_eq_true R W a).mpr hOk'
        rw [hB]
        simp [leBudget, hCost']
      | tail _ hmem =>
        exact Or.inr ⟨a', hmem, hOk', hCost'⟩

/-- Refinement monotonicity: W' ⊆ W implies G(W) ⊆ G(W'). -/
theorem refinement_grows_common_repairs {Ω A : Type} (R : Ω → A → Bool)
    (W W' : List Ω) (hSub : ∀ ω ∈ W', ω ∈ W) (a : A) :
    RepairOk R W a → RepairOk R W' a :=
  fun hOk ω hMem => hOk ω (hSub ω hMem)

/-- Pairwise intersections ({a,b}, {b,c}, {a,c}) are non-empty, yet global intersection is empty. -/
private def R_pairwise (w a : Fin 3) : Bool := w != a

theorem pairwise_intersection_insufficient :
    (∀ w1 w2 : Fin 3, ∃ a : Fin 3, R_pairwise w1 a = true ∧ R_pairwise w2 a = true) ∧
    (¬ ∃ a : Fin 3, ∀ w : Fin 3, R_pairwise w a = true) := by
  decide

/-! ## 3. Lemma 2 (One-Step Probe) & Minimax Recursion V_h(W) -/

def branchWorlds {Ω : Type} (fq : Ω → Bool) (W : List Ω) (y : Bool) : List Ω :=
  W.filter (fun ω => fq ω == y)

def optBranchCost {Ω : Type} (W_y : List Ω) (c : Cost) : Cost :=
  match W_y with
  | [] => .fin 0
  | _ :: _ => c

private theorem leBudget_optBranchCost {Ω : Type} (W_y : List Ω) (c : Cost) (B : Nat) :
    leBudget (optBranchCost W_y c) B ↔ (W_y ≠ [] → leBudget c B) := by
  cases W_y with
  | nil =>
    simp [optBranchCost, leBudget]
  | cons x xs =>
    simp [optBranchCost]

def oneStepThreshold {Ω A : Type} (R : Ω → A → Bool) (costA : A → Nat) (actions : List A)
    (fq : Ω → Bool) (cq : Nat) (W : List Ω) : Cost :=
  let w0 := branchWorlds fq W false
  let w1 := branchWorlds fq W true
  let c0 := optBranchCost w0 (minCommonRepairCost R costA actions w0)
  let c1 := optBranchCost w1 (minCommonRepairCost R costA actions w1)
  addNatCost cq (maxCost c0 c1)

def HasOneStepPlan {Ω A : Type} (R : Ω → A → Bool) (costA : A → Nat) (actions : List A)
    (fq : Ω → Bool) (cq : Nat) (W : List Ω) (B : Nat) : Prop :=
  cq ≤ B ∧
  (∀ y : Bool, branchWorlds fq W y ≠ [] →
    HasImmediateRepair R costA actions (branchWorlds fq W y) (B - cq))

/-- Lemma 2: One-step probe + branch repair is guaranteed iff c(q) + max_y C(W_{q,y}) <= B. -/
theorem lemma2_one_step_probe_iff {Ω A : Type} (R : Ω → A → Bool) (costA : A → Nat)
    (actions : List A) (fq : Ω → Bool) (cq : Nat) (W : List Ω) (B : Nat) :
    leBudget (oneStepThreshold R costA actions fq cq W) B ↔
      HasOneStepPlan R costA actions fq cq W B := by
  simp only [oneStepThreshold, HasOneStepPlan]
  rw [leBudget_addNatCost, leBudget_maxCost, leBudget_optBranchCost, leBudget_optBranchCost]
  rw [lemma1_common_repair_iff, lemma1_common_repair_iff]
  constructor
  · intro h
    rcases h with ⟨hCq, h0, h1⟩
    refine ⟨hCq, ?_⟩
    intro y hNe
    cases y with
    | false => exact h0 hNe
    | true => exact h1 hNe
  · intro h
    rcases h with ⟨hCq, hAll⟩
    exact ⟨hCq, hAll false, hAll true⟩

/-- Minimax guaranteed budget V_h(W) for horizon <= h over finite probe menu Q. -/
def minOverProbes {Q : Type} (probes : List Q) (f : Q → Cost) : Cost :=
  match probes with
  | [] => .inf
  | q :: rest => minCost (f q) (minOverProbes rest f)

private theorem leBudget_minOverProbes {Q : Type} (probes : List Q) (f : Q → Cost) (B : Nat) :
    leBudget (minOverProbes probes f) B ↔ ∃ q ∈ probes, leBudget (f q) B := by
  induction probes with
  | nil => simp [minOverProbes, leBudget]
  | cons q rest ih =>
    simp only [minOverProbes]
    rw [leBudget_minCost, ih]
    constructor
    · intro h
      cases h with
      | inl hq => exact ⟨q, List.Mem.head _, hq⟩
      | inr hRest =>
        rcases hRest with ⟨q', hq', hB⟩
        exact ⟨q', List.Mem.tail _ hq', hB⟩
    · intro h
      rcases h with ⟨q', hq', hB⟩
      cases hq' with
      | head => exact Or.inl hB
      | tail _ hmem => exact Or.inr ⟨q', hmem, hB⟩

def minimaxV {Ω A Q : Type} (R : Ω → A → Bool) (costA : A → Nat) (actions : List A)
    (fq : Q → Ω → Bool) (costQ : Q → Nat) (probes : List Q) : Nat → List Ω → Cost
  | 0, W => minCommonRepairCost R costA actions W
  | h + 1, W =>
    let immediate := minCommonRepairCost R costA actions W
    let viaProbe := minOverProbes probes (fun q =>
      let w0 := branchWorlds (fq q) W false
      let w1 := branchWorlds (fq q) W true
      let c0 := optBranchCost w0 (minimaxV R costA actions fq costQ probes h w0)
      let c1 := optBranchCost w1 (minimaxV R costA actions fq costQ probes h w1)
      addNatCost (costQ q) (maxCost c0 c1))
    minCost immediate viaProbe

inductive ValidPlanTree {Ω A Q : Type} (R : Ω → A → Bool) (costA : A → Nat) (actions : List A)
    (fq : Q → Ω → Bool) (costQ : Q → Nat) (probes : List Q) : Nat → List Ω → Nat → Prop where
  | repair {h : Nat} {W : List Ω} {B : Nat} :
      HasImmediateRepair R costA actions W B →
      ValidPlanTree R costA actions fq costQ probes h W B
  | probe {h : Nat} {W : List Ω} {B : Nat} (q : Q) :
      q ∈ probes →
      costQ q ≤ B →
      (∀ y : Bool, branchWorlds (fq q) W y ≠ [] →
        ValidPlanTree R costA actions fq costQ probes h (branchWorlds (fq q) W y) (B - costQ q)) →
      ValidPlanTree R costA actions fq costQ probes (h + 1) W B

/-- Soundness & completeness of the minimax recursion V_h(W). -/
theorem minimaxV_iff_validPlanTree {Ω A Q : Type} (R : Ω → A → Bool) (costA : A → Nat)
    (actions : List A) (fq : Q → Ω → Bool) (costQ : Q → Nat) (probes : List Q) :
    ∀ (h : Nat) (W : List Ω) (B : Nat),
      leBudget (minimaxV R costA actions fq costQ probes h W) B ↔
        ValidPlanTree R costA actions fq costQ probes h W B
  | 0, W, B => by
      simp only [minimaxV]
      rw [lemma1_common_repair_iff]
      constructor
      · exact ValidPlanTree.repair
      · intro hTree
        cases hTree with
        | repair hImm => exact hImm
  | h + 1, W, B => by
      simp only [minimaxV]
      rw [leBudget_minCost, lemma1_common_repair_iff, leBudget_minOverProbes]
      constructor
      · intro hDisj
        cases hDisj with
        | inl hImm => exact ValidPlanTree.repair hImm
        | inr hVia =>
          rcases hVia with ⟨q, hq, hCost⟩
          rw [leBudget_addNatCost, leBudget_maxCost, leBudget_optBranchCost, leBudget_optBranchCost] at hCost
          rcases hCost with ⟨hCq, h0, h1⟩
          refine ValidPlanTree.probe q hq hCq ?_
          intro y hNe
          cases y with
          | false => exact (minimaxV_iff_validPlanTree R costA actions fq costQ probes h _ _).mp (h0 hNe)
          | true => exact (minimaxV_iff_validPlanTree R costA actions fq costQ probes h _ _).mp (h1 hNe)
      · intro hTree
        cases hTree with
        | repair hImm => exact Or.inl hImm
        | probe q hq hCq hBranches =>
          apply Or.inr
          refine ⟨q, hq, ?_⟩
          rw [leBudget_addNatCost, leBudget_maxCost, leBudget_optBranchCost, leBudget_optBranchCost]
          refine ⟨hCq, ?_, ?_⟩
          · intro hNe
            exact (minimaxV_iff_validPlanTree R costA actions fq costQ probes h _ _).mpr (hBranches false hNe)
          · intro hNe
            exact (minimaxV_iff_validPlanTree R costA actions fq costQ probes h _ _).mpr (hBranches true hNe)

/-! ## 4. Two-World Atom: Thresholds B = 2, 3, 4 ("Confidence Up, Affordability Down") -/

inductive AtomWorld where | wL | wP deriving DecidableEq, Repr
inductive AtomAction where | aL | aP deriving DecidableEq, Repr

def atomR : AtomWorld → AtomAction → Bool
  | .wL, .aL => true
  | .wP, .aP => true
  | _, _ => false

def atomCost : AtomAction → Nat
  | .aL => 1
  | .aP => 2

def atomCalProbe : AtomWorld → Bool
  | .wL => false
  | .wP => true

def atomWorlds : List AtomWorld := [.wL, .wP]
def atomActions : List AtomAction := [.aL, .aP]

theorem confidence_up_affordability_down :
    minCommonRepairCost atomR atomCost atomActions atomWorlds = .inf ∧
    oneStepThreshold atomR atomCost atomActions atomCalProbe 1 atomWorlds = .fin 3 ∧
    oneStepThreshold atomR atomCost atomActions atomCalProbe 2 atomWorlds = .fin 4 ∧
    (¬ leBudget (oneStepThreshold atomR atomCost atomActions atomCalProbe 1 atomWorlds) 2) ∧
    (leBudget (oneStepThreshold atomR atomCost atomActions atomCalProbe 1 atomWorlds) 3) := by
  decide

/-! ## 5. Epistemic Revision Invariants (Factorization & Contravariant Transfer) -/

/-- Distinguishability as factorization: g|_W = d ∘ O|_W <-> ker(O|_W) ⊆ ker(g|_W). -/
theorem factorization_iff_kernel_inclusion {Ω Obs G : Type} [Inhabited G]
    (W : Ω → Prop) (O : Ω → Obs) (g : Ω → G) :
    (∃ d : Obs → G, ∀ ω, W ω → g ω = d (O ω)) ↔
      (∀ ω₁ ω₂, W ω₁ → W ω₂ → O ω₁ = O ω₂ → g ω₁ = g ω₂) := by
  constructor
  · intro h ω₁ ω₂ h1 h2 hO
    rcases h with ⟨d, hd⟩
    rw [hd ω₁ h1, hd ω₂ h2, hO]
  · intro hKer
    classical
    refine ⟨fun y => if h : ∃ ω, W ω ∧ O ω = y then g (Classical.choose h) else default, ?_⟩
    intro ω hW
    have hex : ∃ ω', W ω' ∧ O ω' = O ω := ⟨ω, hW, rfl⟩
    simp only [hex, ↓reduceDIte]
    have hSpec := Classical.choose_spec hex
    exact hKer ω (Classical.choose hex) hW hSpec.1 hSpec.2.symm

/-- Contravariant refutation transfer: mapping every target model to a log-compatible
    source model transfers refutation of the source class to the target class. -/
theorem contravariant_refutation_transfer {H H' : Type}
    (agrees : H → Prop) (agrees' : H' → Prop)
    (hBack : ∀ h' : H', agrees' h' → ∃ h : H, agrees h)
    (hRefuted : ∀ h : H, ¬ agrees h) :
    ∀ h' : H', ¬ agrees' h' := by
  intro h' hA'
  rcases hBack h' hA' with ⟨h, hA⟩
  exact hRefuted h hA

/-! ## 6. Five-State Streaming Mask Fold & Myhill-Nerode Lower Bound -/

inductive Mask2 where
  | m00 | m01 | m10 | m11
  deriving DecidableEq, Repr

def maskAnd : Mask2 → Mask2 → Mask2
  | .m11, m => m
  | m, .m11 => m
  | .m01, .m01 => .m01
  | .m10, .m10 => .m10
  | _, _ => .m00

def hasBitL : Mask2 → Bool
  | .m10 | .m11 => true
  | _ => false

def hasBitP : Mask2 → Bool
  | .m01 | .m11 => true
  | _ => false

inductive FoldAcc where
  | empty
  | val (m : Mask2)
  deriving DecidableEq, Repr

def foldStep : FoldAcc → Mask2 → FoldAcc
  | .empty, m => .val m
  | .val a, m => .val (maskAnd a m)

def foldCombine : FoldAcc → FoldAcc → FoldAcc
  | .empty, y => y
  | x, .empty => x
  | .val a, .val b => .val (maskAnd a b)

def foldFrom : FoldAcc → List Mask2 → FoldAcc
  | acc, [] => acc
  | acc, m :: ms => foldFrom (foldStep acc m) ms

def foldMasks (ms : List Mask2) : FoldAcc :=
  foldFrom .empty ms

private theorem maskAnd_comm (a b : Mask2) : maskAnd a b = maskAnd b a := by
  cases a <;> cases b <;> rfl

private theorem maskAnd_assoc (a b c : Mask2) : maskAnd (maskAnd a b) c = maskAnd a (maskAnd b c) := by
  cases a <;> cases b <;> cases c <;> rfl

private theorem foldFrom_combine (acc1 acc2 : FoldAcc) (ms : List Mask2) :
    foldFrom (foldCombine acc1 acc2) ms = foldCombine acc1 (foldFrom acc2 ms) := by
  induction ms generalizing acc1 acc2 with
  | nil => rfl
  | cons m rest ih =>
    simp only [foldFrom]
    have hStep : foldStep (foldCombine acc1 acc2) m = foldCombine acc1 (foldStep acc2 m) := by
      cases acc1 with
      | empty => rfl
      | val a =>
        cases acc2 with
        | empty => rfl
        | val b => simp only [foldCombine, foldStep, maskAnd_assoc]
    rw [hStep]
    exact ih acc1 (foldStep acc2 m)

theorem foldMasks_order_invariant (ms1 ms2 : List Mask2) :
    foldMasks (ms1 ++ ms2) = foldMasks (ms2 ++ ms1) := by
  have hApp : ∀ xs ys : List Mask2, foldMasks (xs ++ ys) = foldCombine (foldMasks xs) (foldMasks ys) := by
    intro xs ys
    simp only [foldMasks]
    have hAux : ∀ (a : FoldAcc) (u v : List Mask2), foldFrom a (u ++ v) = foldFrom (foldFrom a u) v := by
      intro a u v
      induction u generalizing a with
      | nil => rfl
      | cons x rest ih => exact ih (foldStep a x)
    rw [hAux .empty xs ys]
    have hComb : foldFrom (foldFrom .empty xs) ys = foldFrom (foldCombine (foldFrom .empty xs) .empty) ys := by
      cases foldFrom .empty xs <;> rfl
    rw [hComb, foldFrom_combine]
  rw [hApp ms1 ms2, hApp ms2 ms1]
  cases foldMasks ms1 <;> cases foldMasks ms2 <;> simp only [foldCombine]
  · rw [maskAnd_comm]

theorem foldMasks_exact_common_repair (ms : List Mask2) :
    (foldMasks ms = .empty ↔ ms = []) ∧
    (∀ m : Mask2, foldMasks ms = .val m →
      (hasBitL m = true ↔ ∀ x ∈ ms, hasBitL x = true) ∧
      (hasBitP m = true ↔ ∀ x ∈ ms, hasBitP x = true)) := by
  have hBitL : ∀ a b : Mask2, hasBitL (maskAnd a b) = (hasBitL a && hasBitL b) := by
    intro a b; cases a <;> cases b <;> rfl
  have hBitP : ∀ a b : Mask2, hasBitP (maskAnd a b) = (hasBitP a && hasBitP b) := by
    intro a b; cases a <;> cases b <;> rfl
  have hNonEmpty : ∀ (m : Mask2) (rest : List Mask2), ∃ res, foldFrom (.val m) rest = .val res ∧
      (hasBitL res = true ↔ hasBitL m = true ∧ ∀ x ∈ rest, hasBitL x = true) ∧
      (hasBitP res = true ↔ hasBitP m = true ∧ ∀ x ∈ rest, hasBitP x = true) := by
    intro m rest
    induction rest generalizing m with
    | nil =>
      refine ⟨m, rfl, ?_, ?_⟩ <;> simp
    | cons x xs ih =>
      rcases ih (maskAnd m x) with ⟨res, hEq, hL, hP⟩
      refine ⟨res, hEq, ?_, ?_⟩
      · rw [hL, hBitL, Bool.and_eq_true]
        simp only [List.mem_cons]
        constructor
        · intro h
          rcases h with ⟨⟨hm, hx⟩, hxs⟩
          exact ⟨hm, fun y hy => by cases hy with | inl h => subst h; exact hx | inr h => exact hxs y h⟩
        · intro h
          rcases h with ⟨hm, hall⟩
          exact ⟨⟨hm, hall x (Or.inl rfl)⟩, fun y hy => hall y (Or.inr hy)⟩
      · rw [hP, hBitP, Bool.and_eq_true]
        simp only [List.mem_cons]
        constructor
        · intro h
          rcases h with ⟨⟨hm, hx⟩, hxs⟩
          exact ⟨hm, fun y hy => by cases hy with | inl h => subst h; exact hx | inr h => exact hxs y h⟩
        · intro h
          rcases h with ⟨hm, hall⟩
          exact ⟨⟨hm, hall x (Or.inl rfl)⟩, fun y hy => hall y (Or.inr hy)⟩
  cases ms with
  | nil =>
    simp [foldMasks, foldFrom]
  | cons x xs =>
    rcases hNonEmpty x xs with ⟨res, hEq, hL, hP⟩
    have hF : foldMasks (x :: xs) = .val res := hEq
    constructor
    · rw [hF]; simp
    · intro m hm
      rw [hF] at hm
      cases hm
      constructor
      · rw [hL]; simp only [List.mem_cons]
        constructor
        · intro h y hy
          rcases h with ⟨hx, hxs⟩
          cases hy with | inl h => subst h; exact hx | inr h => exact hxs y h
        · intro hall; exact ⟨hall x (Or.inl rfl), fun y hy => hall y (Or.inr hy)⟩
      · rw [hP]; simp only [List.mem_cons]
        constructor
        · intro h y hy
          rcases h with ⟨hx, hxs⟩
          cases hy with | inl h => subst h; exact hx | inr h => exact hxs y h
        · intro hall; exact ⟨hall x (Or.inl rfl), fun y hy => hall y (Or.inr hy)⟩

inductive FoldVerdict where
  | inconsistent | noCommon | hasCommon
  deriving DecidableEq, Repr

def classifyFold : FoldAcc → FoldVerdict
  | .empty => .inconsistent
  | .val .m00 => .noCommon
  | .val _ => .hasCommon

/-- Myhill-Nerode lower bound: all 5 states {EMPTY, 00, 01, 10, 11} are pairwise distinguishable
    by a suffix of length <= 1. -/
def allFiveStates : List FoldAcc := [.empty, .val .m00, .val .m01, .val .m10, .val .m11]
def testSuffixes : List (List Mask2) := [[], [.m01], [.m10]]

theorem myhill_nerode_five_states_distinct :
    allFiveStates.all (fun s1 =>
      allFiveStates.all (fun s2 =>
        (s1 == s2) || testSuffixes.any (fun suf =>
          classifyFold (foldFrom s1 suf) != classifyFold (foldFrom s2 suf)))) = true := by
  decide

/-! ## 6b. Moore-machine lower bound: any verdict-detector needs 5 states

  `myhill_nerode_five_states_distinct` says the five canonical `FoldAcc` states are pairwise
  separated by a test suffix. Because a detector must be correct on EVERY input (not only on
  the five canonical prefixes), two distinct prefixes can never be merged into one state:
  the separating suffix would force one output to be two different verdicts. -/

def runMoore {St : Type} (δ : St → Mask2 → St) : St → List Mask2 → St
  | q, [] => q
  | q, m :: ms => runMoore δ (δ q m) ms

theorem runMoore_append {St : Type} (δ : St → Mask2 → St)
    (q : St) (u v : List Mask2) :
    runMoore δ q (u ++ v) = runMoore δ (runMoore δ q u) v := by
  induction u generalizing q with
  | nil => rfl
  | cons m rest ih => exact ih (δ q m)

/-- The five canonical prefixes, one per `FoldAcc` state. -/
inductive StateIdx where
  | sEmpty | s00 | s01 | s10 | s11
  deriving DecidableEq, Repr

def witnessPrefix : StateIdx → List Mask2
  | .sEmpty => []
  | .s00    => [.m00]
  | .s01    => [.m01]
  | .s10    => [.m10]
  | .s11    => [.m11]

/-- **State lower bound.** Any Moore machine that computes `classifyFold ∘ foldMasks`
    must send the five canonical prefixes to pairwise different states, hence needs ≥ 5 states. -/
theorem five_states_lower_bound {St : Type}
    (δ : St → Mask2 → St) (q0 : St) (out : St → FoldVerdict)
    (hDet : ∀ ms : List Mask2, out (runMoore δ q0 ms) = classifyFold (foldMasks ms)) :
    ∀ i j : StateIdx,
      runMoore δ q0 (witnessPrefix i) = runMoore δ q0 (witnessPrefix j) → i = j := by
  intro i j hEq
  have hSuf : ∀ suf : List Mask2,
      classifyFold (foldMasks (witnessPrefix i ++ suf)) =
      classifyFold (foldMasks (witnessPrefix j ++ suf)) := by
    intro suf
    rw [← hDet, ← hDet, runMoore_append, runMoore_append, hEq]
  cases i <;> cases j
  all_goals first
    | rfl
    | (have h := hSuf []; exact absurd h (by decide))
    | (have h := hSuf [.m01]; exact absurd h (by decide))
    | (have h := hSuf [.m10]; exact absurd h (by decide))

/-- Corollary (Core-only form): five pairwise different states cannot fit into `Fin n` with `n < 5`.
    Stated without `Fintype`: an injective map `StateIdx → Fin n` forces `5 ≤ n`. -/
theorem five_le_of_injective_stateIdx {n : Nat} (f : StateIdx → Fin n)
    (hinj : Function.Injective f) : 5 ≤ n := by
  have h1 : f .sEmpty ≠ f .s00 := fun h => by cases hinj h
  have h2 : f .sEmpty ≠ f .s01 := fun h => by cases hinj h
  have h3 : f .sEmpty ≠ f .s10 := fun h => by cases hinj h
  have h4 : f .sEmpty ≠ f .s11 := fun h => by cases hinj h
  have h5 : f .s00 ≠ f .s01 := fun h => by cases hinj h
  have h6 : f .s00 ≠ f .s10 := fun h => by cases hinj h
  have h7 : f .s00 ≠ f .s11 := fun h => by cases hinj h
  have h8 : f .s01 ≠ f .s10 := fun h => by cases hinj h
  have h9 : f .s01 ≠ f .s11 := fun h => by cases hinj h
  have h10 : f .s10 ≠ f .s11 := fun h => by cases hinj h
  have := f .sEmpty
  have := f .s00
  have := f .s01
  have := f .s10
  have := f .s11
  omega

/-! ## 7. Boundary of Deterministic Core: Equal 1D Marginals != Adaptive Indistinguishability -/

/-- Over 4 equiprobable outcomes (2 bits):
    - Fixed hidden fair bit: (0,0), (0,0), (1,1), (1,1) -> marginal Pr(Y1=1)=2/4, Pr(Y1=Y2)=4/4
    - Independent fair bits: (0,0), (0,1), (1,0), (1,1) -> marginal Pr(Y1=1)=2/4, Pr(Y1=Y2)=2/4 -/
def fixedBitLaw : List (Bool × Bool) := [(false, false), (false, false), (true, true), (true, true)]
def iidBitLaw   : List (Bool × Bool) := [(false, false), (false, true),  (true, false), (true, true)]

def countPred {α : Type} (p : α → Bool) (xs : List α) : Nat :=
  (xs.filter p).length

theorem marginal_equality_not_joint_equality :
    countPred (fun xy => xy.1) fixedBitLaw = countPred (fun xy => xy.1) iidBitLaw ∧
    countPred (fun xy => xy.2) fixedBitLaw = countPred (fun xy => xy.2) iidBitLaw ∧
    countPred (fun xy => xy.1 == xy.2) fixedBitLaw ≠ countPred (fun xy => xy.1 == xy.2) iidBitLaw := by
  decide

#print axioms lemma1_common_repair_iff
#print axioms pairwise_intersection_insufficient
#print axioms refinement_grows_common_repairs
#print axioms lemma2_one_step_probe_iff
#print axioms confidence_up_affordability_down
#print axioms minimaxV_iff_validPlanTree
#print axioms factorization_iff_kernel_inclusion
#print axioms contravariant_refutation_transfer
#print axioms foldMasks_exact_common_repair
#print axioms foldMasks_order_invariant
#print axioms myhill_nerode_five_states_distinct
#print axioms marginal_equality_not_joint_equality
#print axioms five_states_lower_bound
#print axioms five_le_of_injective_stateIdx


/-! ## 8. Block F: Adaptive Advantage (F1) & (h, B)-Operational Congruence (F2) -/

/-! ### F1. Adaptive Plan Strictly Beats Every Non-Adaptive Plan at Budget B = 3 -/

inductive F1World  where | w00 | w01 | w10 | w11 deriving DecidableEq, Repr
inductive F1Action where | a00 | a01 | a10 | a11 deriving DecidableEq, Repr
inductive F1Probe  where | qRoot | qLeft | qRight deriving DecidableEq, Repr

def f1R : F1World → F1Action → Bool
  | .w00, .a00 => true
  | .w01, .a01 => true
  | .w10, .a10 => true
  | .w11, .a11 => true
  | _, _ => false

def f1CostA : F1Action → Nat := fun _ => 1
def f1CostQ : F1Probe → Nat := fun _ => 1

def f1Obs : F1Probe → F1World → Bool
  | .qRoot,  .w00 => false
  | .qRoot,  .w01 => false
  | .qRoot,  .w10 => true
  | .qRoot,  .w11 => true
  | .qLeft,  .w00 => false
  | .qLeft,  .w01 => true
  | .qLeft,  .w10 => false
  | .qLeft,  .w11 => false
  | .qRight, .w00 => false
  | .qRight, .w01 => false
  | .qRight, .w10 => false
  | .qRight, .w11 => true

def f1Worlds  : List F1World  := [.w00, .w01, .w10, .w11]
def f1Actions : List F1Action := [.a00, .a01, .a10, .a11]
def f1Probes  : List F1Probe  := [.qRoot, .qLeft, .qRight]

def sumProbeCost {Q : Type} (costQ : Q → Nat) : List Q → Nat
  | [] => 0
  | q :: qs => costQ q + sumProbeCost costQ qs

def NonAdaptiveSucceeds {Ω A Q : Type} (R : Ω → A → Bool) (costA : A → Nat) (actions : List A)
    (fq : Q → Ω → Bool) (costQ : Q → Nat) (W : List Ω) (qs : List Q) (B : Nat) : Prop :=
  sumProbeCost costQ qs ≤ B ∧
  ∀ w ∈ W,
    HasImmediateRepair R costA actions
      (W.filter (fun w' => qs.all (fun q => fq q w' == fq q w)))
      (B - sumProbeCost costQ qs)

/-- F1: At budget B = 3 and horizon h = 2, an adaptive ValidPlanTree succeeds on f1Worlds,
    whereas NO non-adaptive probe schedule `qs : List F1Probe` succeeds within budget B = 3. -/
theorem adaptive_strictly_beats_nonadaptive :
    ValidPlanTree f1R f1CostA f1Actions f1Obs f1CostQ f1Probes 2 f1Worlds 3 ∧
    (∀ qs : List F1Probe, ¬ NonAdaptiveSucceeds f1R f1CostA f1Actions f1Obs f1CostQ f1Worlds qs 3) := by
  constructor
  · exact (minimaxV_iff_validPlanTree f1R f1CostA f1Actions f1Obs f1CostQ f1Probes 2 f1Worlds 3).mp (by decide)
  · intro qs hNA
    rcases hNA with ⟨_, hAll⟩
    match qs with
    | [] =>
      have h0 := hAll .w00 (by decide)
      exact absurd ((lemma1_common_repair_iff _ _ _ _ _).mpr h0) (by decide)
    | [q1] =>
      cases q1
      all_goals first
        | (have h0 := hAll .w00 (by decide); exact absurd ((lemma1_common_repair_iff _ _ _ _ _).mpr h0) (by decide))
        | (have h1 := hAll .w10 (by decide); exact absurd ((lemma1_common_repair_iff _ _ _ _ _).mpr h1) (by decide))
    | [q1, q2] =>
      cases q1 <;> cases q2
      all_goals first
        | (have h0 := hAll .w00 (by decide); exact absurd ((lemma1_common_repair_iff _ _ _ _ _).mpr h0) (by decide))
        | (have h1 := hAll .w10 (by decide); exact absurd ((lemma1_common_repair_iff _ _ _ _ _).mpr h1) (by decide))
    | _ :: _ :: _ :: rest =>
      have h0 := hAll .w00 (by decide)
      rcases h0 with ⟨a, _, _, hCost⟩
      simp only [sumProbeCost, f1CostQ, f1CostA] at hCost
      omega

/-! ### F2. (h, B)-Operational Congruence: Dominance at h=0, Probe Sensitivity at h>=1, Budget Cutoff -/

/-- F2a (h = 0 dominance / antichain reduction): if w1 ∈ W and R(w1) ⊆ R(w2),
    then adding w2 to W does not change C(W). -/
theorem h0_dominated_world_redundant {Ω A : Type} (R : Ω → A → Bool) (costA : A → Nat)
    (actions : List A) (W : List Ω) (w1 w2 : Ω)
    (hw1 : w1 ∈ W) (hDom : ∀ a, R w1 a = true → R w2 a = true) :
    minCommonRepairCost R costA actions (w2 :: W) = minCommonRepairCost R costA actions W := by
  have hBool : ∀ a : A, repairOkBool R (w2 :: W) a = repairOkBool R W a := by
    intro a
    cases hW : repairOkBool R W a with
    | false =>
      simp only [repairOkBool, List.all_cons] at hW ⊢
      rw [hW, Bool.and_false]
    | true =>
      have hOkW : RepairOk R W a := (repairOkBool_eq_true R W a).mp hW
      have hw2 : R w2 a = true := hDom a (hOkW w1 hw1)
      simp only [repairOkBool, List.all_cons] at hW ⊢
      rw [hw2, hW]
      rfl
  induction actions with
  | nil => rfl
  | cons a rest ih =>
    simp only [minCommonRepairCost, hBool a, ih]

inductive F2World where | u1 | u2 | v deriving DecidableEq, Repr

def f2R : F2World → AtomAction → Bool
  | .u1, .aL => true
  | .u2, .aL => true
  | .v,  .aP => true
  | _, _ => false

def f2CostA : AtomAction → Nat := fun _ => 1
def f2Obs : Unit → F2World → Bool
  | (), .u1 => false
  | (), .u2 => true
  | (), .v  => true

/-- F2b (h >= 1): identical repair profiles R(u1) = R(u2) do NOT imply operational equivalence
    under probes, since f_q(u1) ≠ f_q(u2) yields V_1([u1, v]) = 2 ≠ +∞ = V_1([u2, v]). -/
theorem h1_part_repr : ∀ a : AtomAction, f2R .u1 a = f2R .u2 a := by
  intro a; cases a <;> rfl

theorem h1_part_u1 :
    minimaxV f2R f2CostA atomActions f2Obs (fun _ => 1) [()] 1 [.u1, .v] = .fin 2 := by
  decide

theorem h1_part_u2 :
    minimaxV f2R f2CostA atomActions f2Obs (fun _ => 1) [()] 1 [.u2, .v] = .inf := by
  decide

theorem h1_same_repair_different_probe_not_congruent :
    (∀ a : AtomAction, f2R .u1 a = f2R .u2 a) ∧
    minimaxV f2R f2CostA atomActions f2Obs (fun _ => 1) [()] 1 [.u1, .v] = .fin 2 ∧
    minimaxV f2R f2CostA atomActions f2Obs (fun _ => 1) [()] 1 [.u2, .v] = .inf :=
  ⟨h1_part_repr, h1_part_u1, h1_part_u2⟩

private theorem filter_congr_eq {α : Type} (p1 p2 : α → Bool) (xs : List α)
    (h : ∀ x, p1 x = p2 x) : xs.filter p1 = xs.filter p2 := by
  induction xs with
  | nil => rfl
  | cons x rest ih =>
    simp only [List.filter_cons, h x, ih]

/-- F2c ((h, B) budget cutoff): modifying probe observations arbitrarily on unaffordable probes
    (costQ q > B) preserves ValidPlanTree at budget B. -/
theorem unaffordable_probe_irrelevant {Ω A Q : Type} (R : Ω → A → Bool) (costA : A → Nat)
    (actions : List A) (fq1 fq2 : Q → Ω → Bool) (costQ : Q → Nat) (probes : List Q)
    {h : Nat} {W : List Ω} {B : Nat}
    (hTree : ValidPlanTree R costA actions fq1 costQ probes h W B) :
    (∀ q ∈ probes, costQ q ≤ B → ∀ ω, fq1 q ω = fq2 q ω) →
    ValidPlanTree R costA actions fq2 costQ probes h W B := by
  induction hTree with
  | repair hImm =>
    intro _
    exact ValidPlanTree.repair hImm
  | @probe h' W' B' q hq hCq _ ih =>
    intro hAgree
    have hBrEq : ∀ y, branchWorlds (fq1 q) W' y = branchWorlds (fq2 q) W' y := by
      intro y
      exact filter_congr_eq _ _ W' (fun ω => by rw [hAgree q hq hCq ω])
    refine ValidPlanTree.probe q hq hCq ?_
    intro y hNe
    rw [← hBrEq y] at hNe ⊢
    exact ih y hNe (fun q' hq' hCq' => hAgree q' hq' (Nat.le_trans hCq' (Nat.sub_le B' (costQ q))))

#print axioms adaptive_strictly_beats_nonadaptive
#print axioms h0_dominated_world_redundant
#print axioms h1_same_repair_different_probe_not_congruent
#print axioms unaffordable_probe_irrelevant

end RepairBudgetAtomV1
