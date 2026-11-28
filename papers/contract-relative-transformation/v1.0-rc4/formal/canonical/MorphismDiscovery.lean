import InvestigationLibrary

/-!
T22, finite discovery of T20 morphisms. Complete indexed carriers; one or
more actions, possibly zero worlds or ports. This is a source candidate.
Only port/action maps are enumerated; world maps are synthesized locally.
No claim of efficient global search or arbitrary-path completeness is made.
-/
namespace CRTT.MorphismDiscovery

open CRTT.AdaptiveObservation CRTT.InvestigationTransfer CRTT.InvestigationLibrary
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

/-! Explicit finite enumeration, without an abstract choice operator. -/

def indices : (n : Nat) → List (Fin n)
  | 0 => []
  | n+1 => 0 :: (indices n).map Fin.succ

theorem mem_indices (n : Nat) (i : Fin n) : i ∈ indices n := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.cases (motive := fun k : Fin (n+1) => k ∈ indices (n+1))
      ?_ (fun j => ?_) i
    · exact List.Mem.head _
    · exact List.Mem.tail _ (List.mem_map.mpr ⟨j, ih j, rfl⟩)

def consMap (v : Fin m) (f : Fin n → Fin m) : Fin (n+1) → Fin m :=
  Fin.cases v f

def maps (m : Nat) : (n : Nat) → List (Fin n → Fin m)
  | 0 => [fun i => Fin.elim0 i]
  | n+1 => (indices m).flatMap (fun v => (maps m n).map (consMap v))

theorem maps_complete (m n : Nat) (f : Fin n → Fin m) : f ∈ maps m n := by
  induction n with
  | zero =>
    have he : (fun i : Fin 0 => (Fin.elim0 i : Fin m)) = f := by
      funext i
      exact Fin.elim0 i
    change f ∈ [fun i : Fin 0 => (Fin.elim0 i : Fin m)]
    -- `List.Mem.head` states membership of the binder form `fun i => f i`, which
    -- `simpa` will not unify with the bare `f` expected here; rewriting the goal
    -- by the extensional equality is direct.
    rw [← he]
    exact List.Mem.head _
  | succ n ih =>
    change f ∈ (indices m).flatMap (fun v => (maps m n).map (consMap v))
    refine List.mem_flatMap.mpr ⟨f 0, mem_indices m (f 0), ?_⟩
    refine List.mem_map.mpr ⟨fun i => f i.succ, ih (fun i => f i.succ), ?_⟩
    funext i
    refine Fin.cases (motive := fun k : Fin (n+1) =>
      consMap (f 0) (fun j => f j.succ) k = f k) ?_ (fun j => ?_) i
    · simp [consMap]
    · simp [consMap]

/-! Small executable search primitives, with soundness/completeness lemmas. -/

theorem and_true_iff (a b : Bool) : (a && b) = true ↔ a = true ∧ b = true := by
  cases a <;> cases b <;> decide

def allB (p : α → Bool) : List α → Bool
  | [] => true
  | x :: xs => p x && allB p xs

theorem allB_iff (p : α → Bool) (xs : List α) :
    allB p xs = true ↔ ∀ x ∈ xs, p x = true := by
  induction xs with
  | nil => simp [allB]
  | cons x xs ih =>
    constructor
    · intro h
      have hpair := (and_true_iff (p x) (allB p xs)).mp h
      have hx := hpair.1
      have ht := hpair.2
      intro y hy
      rcases List.mem_cons.mp hy with he | hm
      · subst y
        exact hx
      · exact ih.mp ht y hm
    · intro h
      have hx := h x (List.Mem.head _)
      have ht := ih.mpr (fun y hy => h y (List.Mem.tail _ hy))
      simp [allB, hx, ht]

def first (p : α → Bool) : List α → Option α
  | [] => none
  | x :: xs => if p x = true then some x else first p xs

theorem first_sound (p : α → Bool) (xs : List α) (x : α)
    (h : first p xs = some x) : x ∈ xs ∧ p x = true := by
  induction xs with
  | nil => simp [first] at h
  | cons y ys ih =>
    by_cases hy : p y = true
    · have hs : some y = some x := by simpa [first, hy] using h
      have he : y = x := Option.some.inj hs
      subst x
      exact ⟨List.Mem.head _, hy⟩
    · have ht : first p ys = some x := by simpa [first, hy] using h
      obtain ⟨hm, hp⟩ := ih ht
      exact ⟨List.Mem.tail _ hm, hp⟩

theorem first_complete (p : α → Bool) (xs : List α) (x : α)
    (hx : x ∈ xs) (hp : p x = true) : (first p xs).isSome = true := by
  induction xs with
  | nil => cases hx
  | cons y ys ih =>
    by_cases hy : p y = true
    · simp [first, hy]
    · rcases List.mem_cons.mp hx with he | hm
      · subst x
        exact False.elim (hy hp)
      · simpa [first, hy] using ih hm

/-- Extraction from a proved successful search. No dummy inhabitant. -/
def extractSome : (o : Option α) → o.isSome = true → α
  | some x, _ => x
  | none, h => by cases h

theorem extractSome_spec (o : Option α) (h : o.isSome = true) :
    o = some (extractSome o h) := by
  cases o with
  | none => cases h
  | some x => rfl

/-- Flatten successful dependent certificates without decidable equality on proofs. -/
def collectSome : List (Option α) → List α
  | [] => []
  | none :: xs => collectSome xs
  | some x :: xs => x :: collectSome xs

theorem mem_collectSome (xs : List (Option α)) (x : α) :
    x ∈ collectSome xs ↔ some x ∈ xs := by
  induction xs with
  | nil => simp [collectSome]
  | cons o xs ih =>
    cases o with
    | none => simp [collectSome, ih]
    | some y => simp [collectSome, ih]

/-! T22.1. Complete indexed tasks, bridged to the unchanged T19/T20/T21 API.
`a` counts additional actions: the full action type is Fin (a+1). -/

structure IndexedTask (w q a : Nat) where
  read : Fin q → Fin w → Bool
  price : Fin q → Nat
  loss : Fin (a+1) → Fin w → Nat
  depth : Nat

def IndexedTask.spec (D : IndexedTask w q a) :
    TaskSpec (Fin w) (Fin q) (Fin (a+1)) where
  problem := {
    defaultAction := 0
    otherActions := (indices a).map Fin.succ
    read := D.read
    price := D.price
    loss := D.loss }
  worlds := indices w
  ports := indices q
  depth := D.depth

def IndexedTask.pack (D : IndexedTask w q a) : ResearchTask where
  World := Fin w
  Port := Fin q
  Action := Fin (a+1)
  spec := D.spec
  portEq := inferInstance

theorem world_mem_all (D : IndexedTask w q a) (x : Fin w) : x ∈ D.spec.worlds :=
  mem_indices w x

theorem port_mem_all (D : IndexedTask w q a) (x : Fin q) : x ∈ D.spec.ports :=
  mem_indices q x

theorem action_mem_all (D : IndexedTask w q a) (x : Fin (a+1)) :
    x ∈ actions D.spec.problem := by
  change x ∈ indices (a+1)
  exact mem_indices (a+1) x

variable {sw sp sa tw tp ta : Nat}
variable (S : IndexedTask sw sp sa) (T : IndexedTask tw tp ta)

abbrev PortMap := Fin sp → Fin tp
abbrev ActionMap := Fin (sa+1) → Fin (ta+1)
abbrev Morphism := TransferMorphism S.spec T.spec

/-- Port-price and injectivity test (independent of worlds and actions). -/
def portOK (p : PortMap (sp := sp) (tp := tp)) : Bool :=
  allB (fun q : Fin sp => decide (T.price (p q) ≤ S.price q)) (indices sp) &&
  allB (fun q : Fin sp => allB (fun r : Fin sp =>
    decide (p q = p r → q = r)) (indices sp)) (indices sp)

theorem portOK_iff (p : PortMap (sp := sp) (tp := tp)) : portOK S T p = true ↔
    (∀ q, T.price (p q) ≤ S.price q) ∧
    (∀ q r, p q = p r → q = r) := by
  constructor
  · intro h
    have hparts :
        allB (fun q : Fin sp => decide (T.price (p q) ≤ S.price q)) (indices sp) = true ∧
        allB (fun q : Fin sp => allB (fun r : Fin sp =>
          decide (p q = p r → q = r)) (indices sp)) (indices sp) = true := by
      simpa only [portOK, and_true_iff] using h
    constructor
    · intro q
      have hd := (allB_iff (fun u : Fin sp => decide (T.price (p u) ≤ S.price u)) (indices sp)).mp hparts.1 q (mem_indices sp q)
      exact of_decide_eq_true hd
    · intro q r hqr
      have hq := (allB_iff (fun u : Fin sp => allB (fun v : Fin sp => decide (p u = p v → u = v)) (indices sp)) (indices sp)).mp hparts.2 q (mem_indices sp q)
      have hr := (allB_iff (fun v : Fin sp => decide (p q = p v → q = v)) (indices sp)).mp hq r (mem_indices sp r)
      have hi : p q = p r → q = r := of_decide_eq_true hr
      exact hi hqr
  · rintro ⟨hc, hi⟩
    unfold portOK
    apply (and_true_iff _ _).mpr
    constructor
    · apply (allB_iff _ _).mpr
      intro q _
      exact decide_eq_true (hc q)
    · apply (allB_iff _ _).mpr
      intro q _
      apply (allB_iff _ _).mpr
      intro r _
      exact decide_eq_true (hi q r)

/-- T22.2: local read compatibility, then local loss compatibility. -/
def readOK (p : PortMap (sp := sp) (tp := tp)) (x : Fin tw) (y : Fin sw) : Bool :=
  allB (fun q : Fin sp => decide (T.read (p q) x = S.read q y)) (indices sp)

def lossOK (a : ActionMap (sa := sa) (ta := ta)) (x : Fin tw) (y : Fin sw) : Bool :=
  allB (fun u : Fin (sa+1) => decide (T.loss (a u) x ≤ S.loss u y)) (indices (sa+1))

theorem readOK_iff (p : PortMap (sp := sp) (tp := tp)) (x : Fin tw) (y : Fin sw) :
    readOK S T p x y = true ↔ ∀ q, T.read (p q) x = S.read q y := by
  constructor
  · intro h q
    exact of_decide_eq_true ((allB_iff (fun u : Fin sp => decide (T.read (p u) x = S.read u y)) (indices sp)).mp h q (mem_indices sp q))
  · intro h
    apply (allB_iff _ _).mpr
    intro q _
    exact decide_eq_true (h q)

theorem lossOK_iff (a : ActionMap (sa := sa) (ta := ta)) (x : Fin tw) (y : Fin sw) :
    lossOK S T a x y = true ↔ ∀ u, T.loss (a u) x ≤ S.loss u y := by
  constructor
  · intro h u
    exact of_decide_eq_true ((allB_iff (fun v : Fin (sa+1) => decide (T.loss (a v) x ≤ S.loss v y)) (indices (sa+1))).mp h u (mem_indices (sa+1) u))
  · intro h
    apply (allB_iff _ _).mpr
    intro u _
    exact decide_eq_true (h u)

/-- B_p(x). Stage 1 filters ports before any action-map enumeration. -/
def portWorlds (p : PortMap (sp := sp) (tp := tp)) (x : Fin tw) : List (Fin sw) :=
  (indices sw).filter (readOK S T p x)

theorem portWorlds_iff (p : PortMap (sp := sp) (tp := tp)) (x : Fin tw) (y : Fin sw) :
    y ∈ portWorlds S T p x ↔ ∀ q, T.read (p q) x = S.read q y := by
  constructor
  · intro h
    have hr := (List.mem_filter.mp h).2
    exact (readOK_iff S T p x y).mp hr
  · intro h
    apply List.mem_filter.mpr
    exact ⟨mem_indices sw y, (readOK_iff S T p x y).mpr h⟩

/-- A read-only witness used by the port prefilter. -/
def readWitness (p : PortMap (sp := sp) (tp := tp)) (x : Fin tw) : Option (Fin sw) :=
  first (readOK S T p x) (indices sw)

def readCover (p : PortMap (sp := sp) (tp := tp)) : Bool :=
  allB (fun x => (readWitness S T p x).isSome) (indices tw)

/-- A single representative of B_{p,a}(x), not a global enumeration of h. -/
def worldWitness (p : PortMap (sp := sp) (tp := tp))
    (a : ActionMap (sa := sa) (ta := ta)) (x : Fin tw) : Option (Fin sw) :=
  first (lossOK S T a x) (portWorlds S T p x)

def worldCover (p : PortMap (sp := sp) (tp := tp)) (a : ActionMap (sa := sa) (ta := ta)) : Bool :=
  allB (fun x => (worldWitness S T p a x).isSome) (indices tw)

theorem worldWitness_sound (p : PortMap (sp := sp) (tp := tp))
    (a : ActionMap (sa := sa) (ta := ta)) (x : Fin tw) (y : Fin sw)
    (h : worldWitness S T p a x = some y) :
    (∀ q, T.read (p q) x = S.read q y) ∧
    (∀ u, T.loss (a u) x ≤ S.loss u y) := by
  obtain ⟨hm, hl⟩ := first_sound (lossOK S T a x) (portWorlds S T p x) y h
  exact ⟨(portWorlds_iff S T p x y).mp hm, (lossOK_iff S T a x y).mp hl⟩

theorem worldWitness_complete (p : PortMap (sp := sp) (tp := tp))
    (a : ActionMap (sa := sa) (ta := ta)) (x : Fin tw) (y : Fin sw)
    (hr : ∀ q, T.read (p q) x = S.read q y)
    (hl : ∀ u, T.loss (a u) x ≤ S.loss u y) :
    (worldWitness S T p a x).isSome = true :=
  first_complete (lossOK S T a x) (portWorlds S T p x) y
    ((portWorlds_iff S T p x y).mpr hr) ((lossOK_iff S T a x y).mpr hl)

/-- T22.3: total even for Fin 0. The proof of a successful local search
is supplied only for actual x : Fin tw; no Inhabited (Fin sw) is needed. -/
def synthWorldMap (p : PortMap (sp := sp) (tp := tp))
    (a : ActionMap (sa := sa) (ta := ta)) (h : worldCover S T p a = true) (x : Fin tw) : Fin sw :=
  extractSome (worldWitness S T p a x) ((allB_iff (fun z => (worldWitness S T p a z).isSome) (indices tw)).mp h x (mem_indices tw x))

theorem synthWorldMap_spec (p : PortMap (sp := sp) (tp := tp))
    (a : ActionMap (sa := sa) (ta := ta)) (h : worldCover S T p a = true) (x : Fin tw) :
    (∀ q, T.read (p q) x = S.read q (synthWorldMap S T p a h x)) ∧
    (∀ u, T.loss (a u) x ≤ S.loss u (synthWorldMap S T p a h x)) :=
  worldWitness_sound S T p a x _
    (extractSome_spec (worldWitness S T p a x) ((allB_iff (fun z => (worldWitness S T p a z).isSome) (indices tw)).mp h x (mem_indices tw x)))

/-- Exact local-world elimination lemma. The forward direction is computed,
not extracted from an arbitrary existential by classical choice. -/
theorem local_world_iff (p : PortMap (sp := sp) (tp := tp))
    (a : ActionMap (sa := sa) (ta := ta)) : worldCover S T p a = true ↔
    ∀ x : Fin tw, ∃ y : Fin sw,
      (∀ q, T.read (p q) x = S.read q y) ∧
      (∀ u, T.loss (a u) x ≤ S.loss u y) := by
  constructor
  · intro h x
    exact ⟨synthWorldMap S T p a h x, synthWorldMap_spec S T p a h x⟩
  · intro h
    apply (allB_iff _ _).mpr
    intro x _
    obtain ⟨y, hr, hl⟩ := h x
    exact worldWitness_complete S T p a x y hr hl

/-- T22.4: actual T20 certificate, not merely a Boolean acceptance flag. -/
def buildMorphism (p : PortMap (sp := sp) (tp := tp))
    (a : ActionMap (sa := sa) (ta := ta))
    (hd : S.depth ≤ T.depth) (hp : portOK S T p = true)
    (hw : worldCover S T p a = true) : Morphism S T where
  worldMap := synthWorldMap S T p a hw
  portMap := p
  actionMap := a
  world_mem := fun x _ => world_mem_all S (synthWorldMap S T p a hw x)
  port_mem := fun q _ => port_mem_all T (p q)
  action_mem := fun u _ => action_mem_all T (a u)
  port_injective := fun q _ r _ he => ((portOK_iff S T p).mp hp).2 q r he
  read_eq := fun q _ x _ => (synthWorldMap_spec S T p a hw x).1 q
  price_le := fun q _ => ((portOK_iff S T p).mp hp).1 q
  loss_le := fun u _ x _ => (synthWorldMap_spec S T p a hw x).2 u
  depth_le := hd

/-- Every T20 morphism over these full domains passes the finite checks. -/
theorem morphism_portOK (M : Morphism S T) : portOK S T M.portMap = true := by
  apply (portOK_iff S T M.portMap).mpr
  exact ⟨fun q => M.price_le q (port_mem_all S q),
    fun q r he => M.port_injective q (port_mem_all S q) r (port_mem_all S r) he⟩

theorem morphism_readCover (M : Morphism S T) : readCover S T M.portMap = true := by
  apply (allB_iff _ _).mpr
  intro x _
  exact first_complete (readOK S T M.portMap x) (indices sw) (M.worldMap x)
    (mem_indices sw (M.worldMap x))
    ((readOK_iff S T M.portMap x (M.worldMap x)).mpr
      (fun q => M.read_eq q (port_mem_all S q) x (world_mem_all T x)))

theorem morphism_worldCover (M : Morphism S T) :
    worldCover S T M.portMap M.actionMap = true := by
  apply (local_world_iff S T M.portMap M.actionMap).mpr
  intro x
  exact ⟨M.worldMap x,
    fun q => M.read_eq q (port_mem_all S q) x (world_mem_all T x),
    fun u => M.loss_le u (action_mem_all S u) x (world_mem_all T x)⟩

/-- Exact fixed-pair criterion: synthesis succeeds iff a T20 certificate with
these port and action maps exists. -/
theorem fixed_pair_iff (p : PortMap (sp := sp) (tp := tp))
    (a : ActionMap (sa := sa) (ta := ta)) :
    (S.depth ≤ T.depth ∧ portOK S T p = true ∧ worldCover S T p a = true) ↔
    ∃ M : Morphism S T, M.portMap = p ∧ M.actionMap = a := by
  constructor
  · rintro ⟨hd, hp, hw⟩
    exact ⟨buildMorphism S T p a hd hp hw, rfl, rfl⟩
  · rintro ⟨M, hp, ha⟩
    refine ⟨M.depth_le, ?_, ?_⟩
    · rw [← hp]
      exact morphism_portOK S T M
    · rw [← hp, ← ha]
      exact morphism_worldCover S T M

def certifyPair (p : PortMap (sp := sp) (tp := tp))
    (a : ActionMap (sa := sa) (ta := ta)) : Option (Morphism S T) :=
  if hd : S.depth ≤ T.depth then
    if hp : portOK S T p = true then
      if hw : worldCover S T p a = true then some (buildMorphism S T p a hd hp hw)
      else none
    else none
  else none

theorem certifyPair_of_checks (p : PortMap (sp := sp) (tp := tp))
    (a : ActionMap (sa := sa) (ta := ta))
    (hd : S.depth ≤ T.depth) (hp : portOK S T p = true)
    (hw : worldCover S T p a = true) :
    certifyPair S T p a = some (buildMorphism S T p a hd hp hw) := by
  simp [certifyPair, hd, hp, hw]

/-! T22.5: complete enumeration modulo the world-witness choice. -/

def portCandidates : List (PortMap (sp := sp) (tp := tp)) :=
  (maps tp sp).filter (fun p => portOK S T p && readCover S T p)

def discoverForPort (p : PortMap (sp := sp) (tp := tp)) : List (Morphism S T) :=
  collectSome ((maps (ta+1) (sa+1)).map (certifyPair S T p))

/-- This is an exhaustive finite reference search, not a budgeted solver.
Stage 1 precedes Stage 2; read rows may be recomputed in the reference code. -/
def discoverAll : List (Morphism S T) :=
  if S.depth ≤ T.depth then
    (portCandidates S T).flatMap (discoverForPort S T)
  else []

theorem morphism_portCandidate (M : Morphism S T) : M.portMap ∈ portCandidates S T := by
  apply List.mem_filter.mpr
  refine ⟨maps_complete tp sp M.portMap, ?_⟩
  simp [morphism_portOK S T M, morphism_readCover S T M]

/-- Complete for execution-relevant (p,a) pairs, not for all possible h. -/
theorem discover_complete (M : Morphism S T) :
    ∃ N ∈ discoverAll S T, N.portMap = M.portMap ∧ N.actionMap = M.actionMap := by
  let N := buildMorphism S T M.portMap M.actionMap M.depth_le
    (morphism_portOK S T M) (morphism_worldCover S T M)
  have ht : certifyPair S T M.portMap M.actionMap = some N :=
    certifyPair_of_checks S T M.portMap M.actionMap M.depth_le
      (morphism_portOK S T M) (morphism_worldCover S T M)
  have hm : some N ∈ (maps (ta+1) (sa+1)).map (certifyPair S T M.portMap) :=
    List.mem_map.mpr ⟨M.actionMap, maps_complete (ta+1) (sa+1) M.actionMap, ht⟩
  have hf : N ∈ discoverForPort S T M.portMap := (mem_collectSome _ _).mpr hm
  refine ⟨N, ?_, rfl, rfl⟩
  have hd : S.depth ≤ T.depth := M.depth_le
  simpa [discoverAll, hd] using
    (List.mem_flatMap.mpr ⟨M.portMap, morphism_portCandidate S T M, hf⟩ :
      N ∈ (portCandidates S T).flatMap (discoverForPort S T))

/-- An exhaustive empty result is a global impossibility certificate.
An interrupted/prefix search is not entitled to use this theorem. -/
theorem empty_iff_no_morphism : discoverAll S T = [] ↔ ¬ Nonempty (Morphism S T) := by
  constructor
  · intro h hn
    obtain ⟨M⟩ := hn
    obtain ⟨N, hm, _, _⟩ := discover_complete S T M
    rw [h] at hm
    cases hm
  · intro h
    cases discoverAll S T with
    | nil => rfl
    | cons M _rest => exact False.elim (h ⟨M⟩)

/-! T22.6: scoped obstruction certificates, not heuristic labels. -/

theorem depth_barrier (h : T.depth < S.depth) : ¬ Nonempty (Morphism S T) := by
  rintro ⟨M⟩
  exact (Nat.not_le_of_gt h) M.depth_le

theorem port_map_rejected (p : PortMap (sp := sp) (tp := tp))
    (h : portOK S T p = false) (M : Morphism S T) (he : M.portMap = p) : False := by
  have hp := morphism_portOK S T M
  rw [he, h] at hp
  cases hp

theorem empty_read_row_barrier (p : PortMap (sp := sp) (tp := tp)) (x : Fin tw)
    (h : portWorlds S T p x = []) (M : Morphism S T) (he : M.portMap = p) : False := by
  have hr : M.worldMap x ∈ portWorlds S T M.portMap x :=
    (portWorlds_iff S T M.portMap x (M.worldMap x)).mpr
      (fun q => M.read_eq q (port_mem_all S q) x (world_mem_all T x))
  rw [he, h] at hr
  cases hr

theorem empty_joint_row_barrier (p : PortMap (sp := sp) (tp := tp))
    (a : ActionMap (sa := sa) (ta := ta)) (x : Fin tw)
    (h : worldWitness S T p a x = none) (M : Morphism S T)
    (hp : M.portMap = p) (ha : M.actionMap = a) : False := by
  have hw : worldCover S T M.portMap M.actionMap = true := morphism_worldCover S T M
  rw [hp, ha] at hw
  have hx : (worldWitness S T p a x).isSome = true :=
    (allB_iff (fun z => (worldWitness S T p a z).isSome) (indices tw)).mp hw x (mem_indices tw x)
  rw [h] at hx
  cases hx

/-! T22.7: replace the witness without changing operational behavior. -/

theorem transfer_eq_of_maps (M N : Morphism S T)
    (hp : M.portMap = N.portMap) (ha : M.actionMap = N.actionMap)
    (t : Investigation (Fin sp) (Fin (sa+1))) : transfer M t = transfer N t := by
  change mapTree M.portMap M.actionMap t = mapTree N.portMap N.actionMap t
  rw [hp, ha]

theorem discover_same_execution (M : Morphism S T) (t : Investigation (Fin sp) (Fin (sa+1))) :
    ∃ N ∈ discoverAll S T, transfer N t = transfer M t := by
  obtain ⟨N, hn, hp, ha⟩ := discover_complete S T M
  exact ⟨N, hn, transfer_eq_of_maps S T N M hp ha t⟩

/-! Limited T22.8 bridge: single-edge T21 offers at an explicit map-only tariff.
This does NOT enumerate arbitrary priced multihop paths or arbitrary registries. -/

structure IndexedEntry (D : IndexedTask w q a) where
  provenance : String
  tree : Tree D.pack
  legalTree : taskLegal D.pack tree
  budget : Nat
  tolerance : Nat
  hardProof : HardContract D.pack tree budget tolerance

def IndexedEntry.toEntry {D : IndexedTask w q a} (e : IndexedEntry D) : LibraryEntry where
  provenance := e.provenance
  source := D.pack
  tree := e.tree
  legalTree := e.legalTree
  budget := e.budget
  tolerance := e.tolerance
  hardProof := e.hardProof

def directOffer (e : IndexedEntry S) (M : Morphism S T) (fee : EdgeExpense) :
    TransferCandidate T.pack where
  entry := e.toEntry
  route := .single M fee

def directOffers (e : IndexedEntry S)
    (fee : PortMap (sp := sp) (tp := tp) → ActionMap (sa := sa) (ta := ta) → EdgeExpense) :
    List (TransferCandidate T.pack) :=
  (discoverAll S T).map (fun M => directOffer S T e M (fee M.portMap M.actionMap))

/-- Cost-completeness for this explicit class of direct, map-priced offers.
Finding a certificate, pricing it, and ranking offers still incur real costs. -/
theorem direct_offer_complete (e : IndexedEntry S)
    (fee : PortMap (sp := sp) (tp := tp) → ActionMap (sa := sa) (ta := ta) → EdgeExpense)
    (M : Morphism S T) : ∃ c ∈ directOffers S T e fee,
      c.total = (directOffer S T e M (fee M.portMap M.actionMap)).total := by
  obtain ⟨N, hn, hp, ha⟩ := discover_complete S T M
  refine ⟨directOffer S T e N (fee N.portMap N.actionMap),
    List.mem_map.mpr ⟨N, hn, rfl⟩, ?_⟩
  change (fee N.portMap N.actionMap).total + cost T.spec (transfer N e.tree) =
    (fee M.portMap M.actionMap).total + cost T.spec (transfer M e.tree)
  have he := transfer_eq_of_maps S T N M hp ha e.tree
  have hf : (fee N.portMap N.actionMap).total = (fee M.portMap M.actionMap).total := by
    rw [hp, ha]
  calc
    _ = (fee M.portMap M.actionMap).total + cost T.spec (transfer N e.tree) :=
      congrArg (fun v => v + cost T.spec (transfer N e.tree)) hf
    _ = _ := congrArg (fun t => (fee M.portMap M.actionMap).total + cost T.spec t) he

namespace Witnesses

/-- Two worlds, a single binary port, two actions. -/
def bitTask (flip : Bool) : IndexedTask 2 1 1 where
  read := fun _ x => if flip then !(x.val == 1) else x.val == 1
  price := fun _ => 1
  loss := fun u x => if u.val = x.val then 0 else 4
  depth := 1

def zeroTask (w : Nat) : IndexedTask w 0 0 where
  read := fun q _ => Fin.elim0 q
  price := fun q => Fin.elim0 q
  loss := fun _ _ => 0
  depth := 0

/-- There is one operational pair for the flipped-bit translation. -/
theorem flipped_computes : (discoverAll (bitTask false) (bitTask true)).length = 1 := by decide

/-- Empty target and empty source: a total empty worldMap exists. -/
theorem empty_target_computes : (discoverAll (zeroTask 0) (zeroTask 0)).length = 1 := by decide

/-- Nonempty target and empty source: no total worldMap exists. -/
theorem empty_source_computes : (discoverAll (zeroTask 0) (zeroTask 1)).length = 0 := by decide

/-- Explicit world compatibility can fail even though the port map is legal. -/
def constantTask : IndexedTask 2 1 1 := { bitTask false with read := fun _ _ => false }

theorem read_barrier_computes :
    readCover constantTask (bitTask false) (fun _ => 0) = false := by decide

end Witnesses

#print axioms mem_indices
#print axioms maps_complete
#print axioms and_true_iff
#print axioms allB_iff
#print axioms first_sound
#print axioms first_complete
#print axioms extractSome_spec
#print axioms mem_collectSome
#print axioms action_mem_all
#print axioms portOK_iff
#print axioms readOK_iff
#print axioms lossOK_iff
#print axioms portWorlds_iff
#print axioms worldWitness_sound
#print axioms worldWitness_complete
#print axioms synthWorldMap_spec
#print axioms local_world_iff
#print axioms buildMorphism
#print axioms morphism_portOK
#print axioms morphism_readCover
#print axioms morphism_worldCover
#print axioms fixed_pair_iff
#print axioms certifyPair_of_checks
#print axioms morphism_portCandidate
#print axioms discover_complete
#print axioms empty_iff_no_morphism
#print axioms depth_barrier
#print axioms port_map_rejected
#print axioms empty_read_row_barrier
#print axioms empty_joint_row_barrier
#print axioms transfer_eq_of_maps
#print axioms discover_same_execution
#print axioms direct_offer_complete
#print axioms Witnesses.flipped_computes
#print axioms Witnesses.empty_target_computes
#print axioms Witnesses.empty_source_computes
#print axioms Witnesses.read_barrier_computes

end CRTT.MorphismDiscovery
