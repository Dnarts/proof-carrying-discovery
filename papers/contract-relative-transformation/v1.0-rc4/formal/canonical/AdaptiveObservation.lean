import Std

/-!
CRTT T19: deterministic, finite, noiseless, binary observations.
The action loss can be instantiated with regret from T18. Observation
prices are fixed Nat costs; each port can be purchased at most once on a path.
A world is fixed during a run. The solver sees only a list of possible worlds,
not the actual world. Lists are the declared finite domains (duplicates do not
change worst-case loss). Empty branches have value zero.
-/
namespace CRTT.AdaptiveObservation

set_option maxRecDepth 4096

/-- Finite maximum, with zero for an empty branch. -/
def worstList (f : α → Nat) : List α → Nat
  | [] => 0
  | x :: xs => max (f x) (worstList f xs)

theorem le_worstList {f : α → Nat} : ∀ {xs : List α} {x : α},
    x ∈ xs → f x ≤ worstList f xs
  | _ :: _, _, h => by
    cases h with
    | head => exact Nat.le_max_left _ _
    | tail _ h' => exact Nat.le_trans (le_worstList h') (Nat.le_max_right _ _)

theorem worstList_le {f : α → Nat} {b : Nat} : ∀ {xs : List α},
    (∀ x ∈ xs, f x ≤ b) → worstList f xs ≤ b
  | [], _ => Nat.zero_le _
  | x :: _xs, h =>
    Nat.max_le.mpr ⟨h x (List.Mem.head _),
      worstList_le (fun y hy => h y (List.Mem.tail _ hy))⟩

/-- Explicit argmin; the default guarantees a nonempty candidate list. -/
def pick (f : α → Nat) (base : α) : List α → α
  | [] => base
  | x :: xs =>
    let b := pick f base xs
    if f x < f b then x else b

theorem pick_mem (f : α → Nat) (base : α) (xs : List α) :
    pick f base xs ∈ base :: xs := by
  induction xs with
  | nil => simp [pick]
  | cons x xs ih =>
    by_cases h : f x < f (pick f base xs)
    · simp [pick, h]
    · have he : pick f base (x :: xs) = pick f base xs := by
        simp [pick, h]
      rw [he]
      rcases List.mem_cons.mp ih with hbase | htail
      · exact List.mem_cons.mpr (Or.inl hbase)
      · exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr htail)))

theorem pick_le (f : α → Nat) (base : α) (xs : List α) (y : α)
    (hy : y ∈ base :: xs) : f (pick f base xs) ≤ f y := by
  induction xs generalizing y with
  | nil =>
    have he : y = base := by simpa using hy
    subst y
    exact Nat.le_refl _
  | cons x xs ih =>
    have hb : f (pick f base (x :: xs)) ≤ f (pick f base xs) := by
      by_cases h : f x < f (pick f base xs)
      · simpa [pick, h] using (Nat.le_of_lt h)
      · simp [pick, h]
    have hx : f (pick f base (x :: xs)) ≤ f x := by
      by_cases h : f x < f (pick f base xs)
      · simp [pick, h]
      · have hle : f (pick f base xs) ≤ f x := by omega
        simpa [pick, h] using hle
    rcases List.mem_cons.mp hy with he | ht
    · subst y
      exact Nat.le_trans hb (ih base (List.Mem.head _))
    · rcases List.mem_cons.mp ht with he | ht
      · subst y; exact hx
      · exact Nat.le_trans hb (ih y (List.Mem.tail _ ht))

def minFold (base : Nat) : List Nat → Nat
  | [] => base
  | x :: xs => min x (minFold base xs)

theorem pick_value (f : α → Nat) (base : α) (xs : List α) :
    f (pick f base xs) = minFold (f base) (xs.map f) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change f (if f x < f (pick f base xs) then x else pick f base xs) =
      min (f x) (minFold (f base) (xs.map f))
    rw [← ih]
    by_cases h : f x < f (pick f base xs)
    · simp [h, Nat.min_eq_left (Nat.le_of_lt h)]
    · have hle : f (pick f base xs) ≤ f x := by omega
      simp [h, Nat.min_eq_right hle]

structure Problem (World Port Action : Type) where
  defaultAction : Action
  otherActions : List Action
  read : Port → World → Bool
  price : Port → Nat
  loss : Action → World → Nat

def actions (P : Problem W Q A) : List A := P.defaultAction :: P.otherActions

inductive Investigation (Port Action : Type) where
  | act (a : Action)
  | observe (p : Port) (onFalse onTrue : Investigation Port Action)
  deriving Repr

/-- Operational semantics: only the observed branch is executed and charged. -/
def runCost (P : Problem W Q A) (w : W) : Investigation Q A → Nat
  | .act a => P.loss a w
  | .observe p l r => P.price p + (if P.read p w then runCost P w r else runCost P w l)

def worst (P : Problem W Q A) (B : List W) (t : Investigation Q A) : Nat :=
  worstList (fun w => runCost P w t) B

/-- Specialize the list maximum theorem to the actual operational cost.
Explicit arguments matter: Lean need not infer a function from its value at w. -/
theorem runCost_le_worst (P : Problem W Q A) (B : List W)
    (t : Investigation Q A) (w : W) (hw : w ∈ B) :
    runCost P w t ≤ worst P B t := by
  exact le_worstList (f := fun u : W => runCost P u t) (xs := B) (x := w) hw

def branch (P : Problem W Q A) (B : List W) (p : Q) (b : Bool) : List W :=
  B.filter (fun w => decide (P.read p w = b))

theorem mem_branch (P : Problem W Q A) (B : List W) (p : Q) (b : Bool) (w : W) :
    w ∈ branch P B p b ↔ w ∈ B ∧ P.read p w = b := by
  simp [branch, List.mem_filter]

def without [DecidableEq Q] (ports : List Q) (p : Q) : List Q :=
  ports.filter (fun q => decide (q ≠ p))

theorem without_excludes [DecidableEq Q] (ports : List Q) (p : Q) :
    p ∉ without ports p := by simp [without, List.mem_filter]

/-- Legality is indexed by remaining depth and remaining purchasable ports. -/
def Legal [DecidableEq Q] (P : Problem W Q A) :
    Nat → List Q → Investigation Q A → Prop
  | _, _, .act a => a ∈ actions P
  | 0, _, .observe _ _ _ => False
  | n+1, ports, .observe p l r =>
      p ∈ ports ∧ Legal P n (without ports p) l ∧ Legal P n (without ports p) r

/-- T19.1: exact Bellman cost of an observation node (nonempty current belief). -/
theorem worst_observe (P : Problem W Q A) (B : List W) (p : Q)
    (l r : Investigation Q A) (hne : B ≠ []) :
    worst P B (.observe p l r) =
      P.price p + max (worst P (branch P B p false) l)
                      (worst P (branch P B p true) r) := by
  apply Nat.le_antisymm
  · unfold worst
    apply worstList_le
    intro w hw
    cases h : P.read p w with
    | false =>
      have hm := (mem_branch P B p false w).mpr ⟨hw, h⟩
      have hb : runCost P w l ≤ worst P (branch P B p false) l :=
        runCost_le_worst P (branch P B p false) l w hm
      have hc := Nat.le_max_left (worst P (branch P B p false) l)
        (worst P (branch P B p true) r)
      change runCost P w (.observe p l r) ≤ P.price p +
        max (worst P (branch P B p false) l) (worst P (branch P B p true) r)
      rw [show runCost P w (.observe p l r) = P.price p + runCost P w l from by simp [runCost, h]]
      exact Nat.add_le_add_left (Nat.le_trans hb hc) _
    | true =>
      have hm := (mem_branch P B p true w).mpr ⟨hw, h⟩
      have hb : runCost P w r ≤ worst P (branch P B p true) r :=
        runCost_le_worst P (branch P B p true) r w hm
      have hc := Nat.le_max_right (worst P (branch P B p false) l)
        (worst P (branch P B p true) r)
      change runCost P w (.observe p l r) ≤ P.price p +
        max (worst P (branch P B p false) l) (worst P (branch P B p true) r)
      rw [show runCost P w (.observe p l r) = P.price p + runCost P w r from by simp [runCost, h]]
      exact Nat.add_le_add_left (Nat.le_trans hb hc) _
  · let v := worst P B (.observe p l r)
    have hprice : P.price p ≤ v := by
      cases B with
      | nil => exact False.elim (hne rfl)
      | cons w ws =>
        have hw : runCost P w (.observe p l r) ≤ v :=
          runCost_le_worst P (w :: ws) (.observe p l r) w (List.Mem.head ws)
        simp only [runCost] at hw
        omega
    have hl : worst P (branch P B p false) l ≤ v - P.price p := by
      unfold worst
      apply worstList_le
      intro w hw
      obtain ⟨hm, he⟩ := (mem_branch P B p false w).mp hw
      have h := runCost_le_worst P B (.observe p l r) w hm
      change runCost P w (.observe p l r) ≤ v at h
      rw [show runCost P w (.observe p l r) = P.price p + runCost P w l from by simp [runCost, he]] at h
      omega
    have hr : worst P (branch P B p true) r ≤ v - P.price p := by
      unfold worst
      apply worstList_le
      intro w hw
      obtain ⟨hm, he⟩ := (mem_branch P B p true w).mp hw
      have h := runCost_le_worst P B (.observe p l r) w hm
      change runCost P w (.observe p l r) ≤ v at h
      rw [show runCost P w (.observe p l r) = P.price p + runCost P w r from by simp [runCost, he]] at h
      omega
    have hm : max (worst P (branch P B p false) l) (worst P (branch P B p true) r) ≤ v - P.price p :=
      Nat.max_le.mpr ⟨hl, hr⟩
    change P.price p + max (worst P (branch P B p false) l)
      (worst P (branch P B p true) r) ≤ v
    omega

theorem observe_monotone (P : Problem W Q A) (B : List W) (p : Q)
    (l l' r r' : Investigation Q A)
    (hl : worst P (branch P B p false) l ≤ worst P (branch P B p false) l')
    (hr : worst P (branch P B p true) r ≤ worst P (branch P B p true) r') :
    worst P B (.observe p l r) ≤ worst P B (.observe p l' r') := by
  by_cases h : B = []
  · subst B; exact Nat.le_refl _
  · rw [worst_observe P B p l r h, worst_observe P B p l' r' h]
    apply Nat.add_le_add_left
    exact Nat.max_le.mpr ⟨Nat.le_trans hl (Nat.le_max_left _ _),
      Nat.le_trans hr (Nat.le_max_right _ _)⟩

/-- Optimal immediate action. -/
def terminal (P : Problem W Q A) (B : List W) : Investigation Q A :=
  .act (pick (fun a => worst P B (.act a)) P.defaultAction P.otherActions)

theorem terminal_legal [DecidableEq Q] (P : Problem W Q A) (B : List W)
    (n : Nat) (ports : List Q) : Legal P n ports (terminal P B) := by
  cases n <;> exact pick_mem _ _ _

theorem terminal_optimal (P : Problem W Q A) (B : List W) (a : A)
    (ha : a ∈ actions P) : worst P B (terminal P B) ≤ worst P B (.act a) := by
  exact pick_le (fun a' : A => worst P B (.act a'))
    P.defaultAction P.otherActions a ha

def candidates [DecidableEq Q] (P : Problem W Q A) (B : List W) (ports : List Q)
    (sub : List W → List Q → Investigation Q A) : List (Investigation Q A) :=
  ports.map (fun p => .observe p
    (sub (branch P B p false) (without ports p))
    (sub (branch P B p true) (without ports p)))

/-- Construct an optimal tree, not just its numerical value. -/
def solve [DecidableEq Q] (P : Problem W Q A) : Nat → List W → List Q → Investigation Q A
  | 0 => fun B _ => terminal P B
  | n+1 => fun B ports =>
      pick (worst P B) (terminal P B) (candidates P B ports (solve P n))

def value [DecidableEq Q] (P : Problem W Q A) (n : Nat) (B : List W) (ports : List Q) : Nat :=
  worst P B (solve P n B ports)

theorem solve_legal [DecidableEq Q] (P : Problem W Q A) (n : Nat) (B : List W) (ports : List Q) :
    Legal P n ports (solve P n B ports) := by
  induction n generalizing B ports with
  | zero => exact terminal_legal P B 0 ports
  | succ n ih =>
    have hm : solve P (n+1) B ports ∈ terminal P B :: candidates P B ports (solve P n) :=
      pick_mem _ _ _
    rcases List.mem_cons.mp hm with he | hc
    · rw [he]; exact terminal_legal P B (n+1) ports
    · unfold candidates at hc
      obtain ⟨p, hp, he⟩ := List.mem_map.mp hc
      rw [← he]
      exact ⟨hp, ih _ _, ih _ _⟩

/-- T19.2/3: universal lower bound, attained by the executable legal solver. -/
theorem solve_optimal [DecidableEq Q] (P : Problem W Q A) (n : Nat) (B : List W)
    (ports : List Q) (t : Investigation Q A) (ht : Legal P n ports t) :
    value P n B ports ≤ worst P B t := by
  induction n generalizing B ports t with
  | zero =>
    cases t with
    | act a => exact terminal_optimal P B a ht
    | observe p l r => exact False.elim ht
  | succ n ih =>
    cases t with
    | act a =>
      have h : worst P B (solve P (n+1) B ports) ≤ worst P B (terminal P B) :=
        pick_le _ _ _ _ (List.Mem.head _)
      exact Nat.le_trans h (terminal_optimal P B a ht)
    | observe p l r =>
      obtain ⟨hp, hl, hr⟩ := ht
      let l' := solve P n (branch P B p false) (without ports p)
      let r' := solve P n (branch P B p true) (without ports p)
      have hc : Investigation.observe p l' r' ∈ candidates P B ports (solve P n) := by
        unfold candidates
        exact List.mem_map.mpr ⟨p, hp, rfl⟩
      have h1 : worst P B (solve P (n+1) B ports) ≤ worst P B (.observe p l' r') :=
        pick_le _ _ _ _ (List.Mem.tail _ hc)
      have h2 := observe_monotone P B p l' l r' r (ih _ _ _ hl) (ih _ _ _ hr)
      exact Nat.le_trans h1 h2

/-- T19.2: the numerical recurrence follows from the operational tree solver. -/
theorem bellman [DecidableEq Q] (P : Problem W Q A) (n : Nat) (B : List W)
    (ports : List Q) (hne : B ≠ []) :
    value P (n+1) B ports = minFold (worst P B (terminal P B))
      (ports.map (fun p => P.price p +
        max (value P n (branch P B p false) (without ports p))
            (value P n (branch P B p true) (without ports p)))) := by
  have hfun :
      (fun p : Q => worst P B (.observe p
        (solve P n (branch P B p false) (without ports p))
        (solve P n (branch P B p true) (without ports p)))) =
      (fun p : Q => P.price p +
        max (value P n (branch P B p false) (without ports p))
            (value P n (branch P B p true) (without ports p))) := by
    funext p
    exact worst_observe P B p
      (solve P n (branch P B p false) (without ports p))
      (solve P n (branch P B p true) (without ports p)) hne
  have hmap : (candidates P B ports (solve P n)).map (worst P B) =
      ports.map (fun p => P.price p +
        max (value P n (branch P B p false) (without ports p))
            (value P n (branch P B p true) (without ports p))) := by
    unfold candidates
    rw [List.map_map]
    exact congrArg (fun f : Q → Nat => ports.map f) hfun
  calc
    value P (n+1) B ports =
        minFold (worst P B (terminal P B))
          ((candidates P B ports (solve P n)).map (worst P B)) :=
      pick_value (worst P B) (terminal P B) (candidates P B ports (solve P n))
    _ = _ := congrArg (minFold (worst P B (terminal P B))) hmap

theorem value_empty [DecidableEq Q] (P : Problem W Q A) (n : Nat) (ports : List Q) :
    value P n [] ports = 0 := rfl

theorem value_zero [DecidableEq Q] (P : Problem W Q A) (B : List W) (ports : List Q) :
    value P 0 B ports = worst P B (terminal P B) := rfl

theorem value_no_ports [DecidableEq Q] (P : Problem W Q A) (n : Nat) (B : List W) :
    value P n B [] = worst P B (terminal P B) := by cases n <;> rfl

/-- Threshold feasibility for TOTAL worst-case cost (observation + terminal loss). -/
theorem cost_feasible_iff [DecidableEq Q] (P : Problem W Q A) (n : Nat)
    (B : List W) (ports : List Q) (budget : Nat) :
    value P n B ports ≤ budget ↔
      ∃ t, Legal P n ports t ∧ worst P B t ≤ budget := by
  constructor
  · intro h; exact ⟨solve P n B ports, solve_legal P n B ports, h⟩
  · rintro ⟨t, ht, hb⟩
    exact Nat.le_trans (solve_optimal P n B ports t ht) hb

/-! T19.7: separately constrain observation expenditure and terminal regret.
A finite penalty of budget+1 is sufficient: it cannot be hidden by a cheap path.
-/

def observationCost (P : Problem W Q A) (w : W) : Investigation Q A → Nat
  | .act _ => 0
  | .observe p l r => P.price p +
      (if P.read p w then observationCost P w r else observationCost P w l)

def terminalLoss (P : Problem W Q A) (w : W) : Investigation Q A → Nat
  | .act a => P.loss a w
  | .observe p l r => if P.read p w then terminalLoss P w r else terminalLoss P w l

theorem runCost_split (P : Problem W Q A) (w : W) (t : Investigation Q A) :
    runCost P w t = observationCost P w t + terminalLoss P w t := by
  induction t with
  | act a => simp [runCost, observationCost, terminalLoss]
  | observe p l r ihl ihr =>
    cases h : P.read p w <;>
      simp [runCost, observationCost, terminalLoss, h, ihl, ihr, Nat.add_assoc]

def cappedProblem (P : Problem W Q A) (eps budget : Nat) : Problem W Q A :=
  { P with loss := fun a w => if P.loss a w ≤ eps then 0 else budget + 1 }

theorem capped_cost (P : Problem W Q A) (eps budget : Nat) (w : W)
    (t : Investigation Q A) :
    runCost (cappedProblem P eps budget) w t = observationCost P w t +
      (if terminalLoss P w t ≤ eps then 0 else budget + 1) := by
  induction t with
  | act a =>
    change (if P.loss a w ≤ eps then 0 else budget + 1) =
      0 + (if P.loss a w ≤ eps then 0 else budget + 1)
    exact (Nat.zero_add _).symm
  | observe p l r ihl ihr =>
    change P.price p + (if P.read p w then runCost (cappedProblem P eps budget) w r
      else runCost (cappedProblem P eps budget) w l) =
      (P.price p + (if P.read p w then observationCost P w r else observationCost P w l)) +
      (if (if P.read p w then terminalLoss P w r else terminalLoss P w l) ≤ eps then 0 else budget + 1)
    cases h : P.read p w <;> simp [ihl, ihr, Nat.add_assoc]

theorem capped_legal [DecidableEq Q] (P : Problem W Q A) (eps budget n : Nat)
    (ports : List Q) (t : Investigation Q A) :
    Legal (cappedProblem P eps budget) n ports t ↔ Legal P n ports t := by
  induction n generalizing ports t with
  | zero => cases t <;> rfl
  | succ n ih =>
    cases t with
    | act a => rfl
    | observe p l r =>
      change (p ∈ ports ∧ Legal (cappedProblem P eps budget) n (without ports p) l ∧
        Legal (cappedProblem P eps budget) n (without ports p) r) ↔
        (p ∈ ports ∧ Legal P n (without ports p) l ∧ Legal P n (without ports p) r)
      rw [ih (without ports p) l, ih (without ports p) r]

theorem capped_worst_iff (P : Problem W Q A) (eps budget : Nat)
    (B : List W) (t : Investigation Q A) :
    worst (cappedProblem P eps budget) B t ≤ budget ↔
      ∀ w ∈ B, observationCost P w t ≤ budget ∧ terminalLoss P w t ≤ eps := by
  constructor
  · intro h w hw
    have h1 : runCost (cappedProblem P eps budget) w t ≤ budget :=
      Nat.le_trans (runCost_le_worst (cappedProblem P eps budget) B t w hw) h
    rw [capped_cost] at h1
    by_cases he : terminalLoss P w t ≤ eps
    · simp [he] at h1
      exact ⟨h1, he⟩
    · simp [he] at h1 <;> omega
  · intro h
    unfold worst
    apply worstList_le
    intro w hw
    obtain ⟨hc, he⟩ := h w hw
    simpa [capped_cost, he] using hc

/-- T19.7: exact executable feasibility of a hard terminal regret tolerance. -/
theorem epsilon_budget_iff [DecidableEq Q] (P : Problem W Q A) (n : Nat)
    (B : List W) (ports : List Q) (eps budget : Nat) :
    value (cappedProblem P eps budget) n B ports ≤ budget ↔
      ∃ t, Legal P n ports t ∧
        ∀ w ∈ B, observationCost P w t ≤ budget ∧ terminalLoss P w t ≤ eps := by
  rw [cost_feasible_iff]
  constructor
  · rintro ⟨t, hl, hc⟩
    exact ⟨t, (capped_legal P eps budget n ports t).mp hl,
      (capped_worst_iff P eps budget B t).mp hc⟩
  · rintro ⟨t, hl, hc⟩
    exact ⟨t, (capped_legal P eps budget n ports t).mpr hl,
      (capped_worst_iff P eps budget B t).mpr hc⟩

/-! Static strategies: the order and set of ports is fixed before observations.
The terminal action may depend on the full observed history. -/
def Follows (P : Problem W Q A) : List Q → Investigation Q A → Prop
  | [], .act a => a ∈ actions P
  | p :: ps, .observe q l r => p = q ∧ Follows P ps l ∧ Follows P ps r
  | _, _ => False

def fixedSolve (P : Problem W Q A) : List Q → List W → Investigation Q A
  | [], B => terminal P B
  | p :: ps, B => .observe p (fixedSolve P ps (branch P B p false))
                              (fixedSolve P ps (branch P B p true))

def fixedValue (P : Problem W Q A) (B : List W) (qs : List Q) : Nat :=
  worst P B (fixedSolve P qs B)

theorem fixedSolve_follows (P : Problem W Q A) (qs : List Q) (B : List W) :
    Follows P qs (fixedSolve P qs B) := by
  induction qs generalizing B with
  | nil => exact pick_mem _ _ _
  | cons p ps ih => exact ⟨rfl, ih _, ih _⟩

theorem fixed_optimal (P : Problem W Q A) (qs : List Q) (B : List W)
    (t : Investigation Q A) (ht : Follows P qs t) :
    fixedValue P B qs ≤ worst P B t := by
  induction qs generalizing B t with
  | nil =>
    cases t with
    | act a => exact terminal_optimal P B a ht
    | observe p l r => exact False.elim ht
  | cons p ps ih =>
    cases t with
    | act a => exact False.elim ht
    | observe q l r =>
      obtain ⟨he, hl, hr⟩ := ht
      subst q
      exact observe_monotone P B p _ l _ r (ih _ _ hl) (ih _ _ hr)

def ScheduleLegal [DecidableEq Q] : List Q → List Q → Prop
  | _, [] => True
  | ports, p :: ps => p ∈ ports ∧ ScheduleLegal (without ports p) ps

theorem follows_legal [DecidableEq Q] (P : Problem W Q A) (qs : List Q) (ports : List Q)
    (n : Nat) (t : Investigation Q A) (hs : ScheduleLegal ports qs)
    (hlen : qs.length ≤ n) (ht : Follows P qs t) : Legal P n ports t := by
  induction qs generalizing ports n t with
  | nil =>
    cases t with
    | act a => cases n <;> exact ht
    | observe p l r => exact False.elim ht
  | cons p ps ih =>
    cases n with
    | zero => simp at hlen
    | succ n =>
      cases t with
      | act a => exact False.elim ht
      | observe q l r =>
        obtain ⟨he, hl, hr⟩ := ht
        subst q
        have hn : ps.length ≤ n := by simpa using hlen
        exact ⟨hs.1, ih _ _ _ hs.2 hn hl, ih _ _ _ hs.2 hn hr⟩

/-- T19.4: adaptive optimal cost is no worse than any legal fixed schedule. -/
theorem adaptive_le_fixed [DecidableEq Q] (P : Problem W Q A) (n : Nat) (B : List W)
    (ports qs : List Q) (hs : ScheduleLegal ports qs) (hlen : qs.length ≤ n) :
    value P n B ports ≤ fixedValue P B qs :=
  solve_optimal P n B ports _
    (follows_legal P qs ports n _ hs hlen (fixedSolve_follows P qs B))

/-- Enumerate every legal static schedule up to the given depth. -/
def schedules [DecidableEq Q] : Nat → List Q → List (List Q)
  | 0, _ => [[]]
  | n+1, ports => [] :: ports.flatMap (fun p => (schedules n (without ports p)).map (List.cons p))

theorem schedules_complete [DecidableEq Q] (n : Nat) (ports qs : List Q)
    (hs : ScheduleLegal ports qs) (hlen : qs.length ≤ n) : qs ∈ schedules n ports := by
  induction n generalizing ports qs with
  | zero =>
    cases qs with
    | nil => simp [schedules]
    | cons p ps => simp at hlen
  | succ n ih =>
    cases qs with
    | nil => simp [schedules]
    | cons p ps =>
      have hn : ps.length ≤ n := by simpa using hlen
      have hm := ih (without ports p) ps hs.2 hn
      apply List.mem_cons.mpr
      right
      exact List.mem_flatMap.mpr ⟨p, hs.1, List.mem_map.mpr ⟨ps, hm, rfl⟩⟩

theorem schedules_sound [DecidableEq Q] (n : Nat) (ports qs : List Q)
    (hm : qs ∈ schedules n ports) : ScheduleLegal ports qs ∧ qs.length ≤ n := by
  induction n generalizing ports qs with
  | zero =>
    have he : qs = [] := by simpa [schedules] using hm
    subst qs
    exact ⟨True.intro, Nat.le_refl _⟩
  | succ n ih =>
    change qs ∈ [] :: ports.flatMap (fun p => (schedules n (without ports p)).map (List.cons p)) at hm
    rcases List.mem_cons.mp hm with he | hm
    · subst qs; exact ⟨True.intro, Nat.zero_le _⟩
    · obtain ⟨p, hp, hm⟩ := List.mem_flatMap.mp hm
      obtain ⟨ps, hps, he⟩ := List.mem_map.mp hm
      rw [← he]
      obtain ⟨hs, hn⟩ := ih _ _ hps
      exact ⟨⟨hp, hs⟩, Nat.succ_le_succ hn⟩

def bestSchedule [DecidableEq Q] (P : Problem W Q A) (n : Nat) (B : List W) (ports : List Q) : List Q :=
  pick (fixedValue P B) [] (schedules n ports)

def staticValue [DecidableEq Q] (P : Problem W Q A) (n : Nat) (B : List W) (ports : List Q) : Nat :=
  fixedValue P B (bestSchedule P n B ports)

theorem bestSchedule_legal [DecidableEq Q] (P : Problem W Q A) (n : Nat) (B : List W) (ports : List Q) :
    ScheduleLegal ports (bestSchedule P n B ports) ∧ (bestSchedule P n B ports).length ≤ n := by
  have hm := pick_mem (fixedValue P B) [] (schedules n ports)
  rcases List.mem_cons.mp hm with he | hm
  · change bestSchedule P n B ports = [] at he
    rw [he]
    exact ⟨True.intro, Nat.zero_le _⟩
  · exact schedules_sound n ports _ hm

theorem static_optimal [DecidableEq Q] (P : Problem W Q A) (n : Nat) (B : List W)
    (ports qs : List Q) (t : Investigation Q A) (hs : ScheduleLegal ports qs)
    (hlen : qs.length ≤ n) (ht : Follows P qs t) : staticValue P n B ports ≤ worst P B t := by
  have hm := schedules_complete n ports qs hs hlen
  exact Nat.le_trans (pick_le (fixedValue P B) [] _ qs (List.Mem.tail _ hm))
    (fixed_optimal P qs B t ht)

theorem adaptive_le_static [DecidableEq Q] (P : Problem W Q A) (n : Nat) (B : List W) (ports : List Q) :
    value P n B ports ≤ staticValue P n B ports := by
  obtain ⟨hs, hn⟩ := bestSchedule_legal P n B ports
  exact adaptive_le_fixed P n B ports _ hs hn

/-! Closed witnesses: computed from the actual domain, loss and port semantics. -/
namespace Witnesses

inductive Port3 where
  | b | s | t
  deriving DecidableEq, Repr

abbrev World3 := Bool × Bool × Bool

def worlds3 : List World3 :=
  [(false,false,false), (false,false,true), (false,true,false), (false,true,true),
   (true,false,false), (true,false,true), (true,true,false), (true,true,true)]

def ports3 : List Port3 := [.b, .s, .t]

def mux (w : World3) : Bool := if w.1 then w.2.2 else w.2.1

def muxProblem : Problem World3 Port3 Bool where
  defaultAction := false
  otherActions := [true]
  read := fun p w => match p with
    | .b => w.1
    | .s => w.2.1
    | .t => w.2.2
  price := fun _ => 1
  loss := fun a w => if a = mux w then 0 else 4

def muxTree : Investigation Port3 Bool :=
  .observe .b (.observe .s (.act false) (.act true))
              (.observe .t (.act false) (.act true))

set_option maxHeartbeats 4000000 in
theorem mux_tree_legal : Legal muxProblem 3 ports3 muxTree := by
  unfold muxTree
  refine ⟨by decide, ?_, ?_⟩
  · refine ⟨by decide, ?_, ?_⟩
    · change false ∈ actions muxProblem; decide
    · change true ∈ actions muxProblem; decide
  · refine ⟨by decide, ?_, ?_⟩
    · change false ∈ actions muxProblem; decide
    · change true ∈ actions muxProblem; decide

theorem mux_tree_cost : worst muxProblem worlds3 muxTree = 2 := by decide

set_option maxHeartbeats 4000000 in
theorem mux_adaptive_value : value muxProblem 3 worlds3 ports3 = 2 := by decide

set_option maxHeartbeats 4000000 in
theorem mux_static_value : staticValue muxProblem 3 worlds3 ports3 = 3 := by decide

set_option maxHeartbeats 4000000 in
theorem mux_exact_observation_budget :
    (∃ t, Legal muxProblem 3 ports3 t ∧
      ∀ w ∈ worlds3, observationCost muxProblem w t ≤ 2 ∧ terminalLoss muxProblem w t ≤ 0) ∧
    ¬ (∃ t, Legal muxProblem 3 ports3 t ∧
      ∀ w ∈ worlds3, observationCost muxProblem w t ≤ 1 ∧ terminalLoss muxProblem w t ≤ 0) := by
  constructor
  · apply (epsilon_budget_iff muxProblem 3 worlds3 ports3 0 2).mp
    decide
  · intro h
    have h1 := (epsilon_budget_iff muxProblem 3 worlds3 ports3 0 1).mpr h
    have hn : ¬ (value (cappedProblem muxProblem 0 1) 3 worlds3 ports3 ≤ 1) := by decide
    exact hn h1

/-- T19.5: the computed optimum is strictly better than the computed static optimum. -/
theorem mux_adaptive_beats_static :
    value muxProblem 3 worlds3 ports3 < staticValue muxProblem 3 worlds3 ports3 := by
  rw [mux_adaptive_value, mux_static_value]
  decide

/-- No legal adaptive tree has cost below 2. -/
theorem mux_lower_bound (t : Investigation Port3 Bool) (ht : Legal muxProblem 3 ports3 t) :
    2 ≤ worst muxProblem worlds3 t := by
  rw [← mux_adaptive_value]
  exact solve_optimal _ _ _ _ _ ht

/-- No legal fixed schedule and following policy has cost below 3. -/
theorem mux_static_lower_bound (qs : List Port3) (t : Investigation Port3 Bool)
    (hs : ScheduleLegal ports3 qs) (hlen : qs.length ≤ 3) (ht : Follows muxProblem qs t) :
    3 ≤ worst muxProblem worlds3 t := by
  rw [← mux_static_value]
  exact static_optimal _ _ _ _ _ _ hs hlen ht

inductive Port2 where
  | left | right
  deriving DecidableEq, Repr

def worlds2 : List (Bool × Bool) := [(false,false),(false,true),(true,false),(true,true)]
def ports2 : List Port2 := [.left, .right]

def xorProblem : Problem (Bool × Bool) Port2 Bool where
  defaultAction := false
  otherActions := [true]
  read := fun p w => match p with | .left => w.1 | .right => w.2
  price := fun _ => 1
  loss := fun a w => if a = xor w.1 w.2 then 0 else 4

/-- T19.6: neither single observation improves on stopping, but the pair does. -/
theorem xor_greedy_failure :
    fixedValue xorProblem worlds2 [] = 4 ∧
    fixedValue xorProblem worlds2 [.left] = 5 ∧
    fixedValue xorProblem worlds2 [.right] = 5 ∧
    value xorProblem 2 worlds2 ports2 = 2 := by decide

end Witnesses

#print axioms pick_value
#print axioms runCost_le_worst
#print axioms terminal_optimal
#print axioms capped_cost
#print axioms capped_worst_iff
#print axioms solve_legal
#print axioms worst_observe
#print axioms solve_optimal
#print axioms bellman
#print axioms cost_feasible_iff
#print axioms runCost_split
#print axioms epsilon_budget_iff
#print axioms fixed_optimal
#print axioms schedules_complete
#print axioms schedules_sound
#print axioms static_optimal
#print axioms adaptive_le_static
#print axioms Witnesses.mux_adaptive_beats_static
#print axioms Witnesses.mux_exact_observation_budget
#print axioms Witnesses.mux_lower_bound
#print axioms Witnesses.mux_static_lower_bound
#print axioms Witnesses.xor_greedy_failure

end CRTT.AdaptiveObservation
