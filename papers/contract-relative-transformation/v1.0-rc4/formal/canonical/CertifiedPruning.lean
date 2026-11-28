import BudgetedDiscovery

namespace CRTT.CertifiedPruning
open CRTT.AdaptiveObservation CRTT.InvestigationTransfer CRTT.MorphismDiscovery CRTT.BudgetedDiscovery

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

variable {sw sp sa tw tp ta : Nat}
variable (S : IndexedTask sw sp sa) (T : IndexedTask tw tp ta)

/-- Partial port assignment: list of pairs (source port, target port). -/
abbrev PartialAssign (sp tp : Nat) := List (Fin sp × Fin tp)

/-- A full T20 morphism extends a partial port assignment ρ. -/
def Extends (M : Morphism S T) (ρ : PartialAssign sp tp) : Prop :=
  ∀ pair ∈ ρ, M.portMap pair.1 = pair.2

/-- Local read compatibility of target world x and source world y under partial assignment ρ. -/
def partialReadOK (ρ : PartialAssign sp tp) (x : Fin tw) (y : Fin sw) : Bool :=
  allB (fun pair : Fin sp × Fin tp => decide (T.read pair.2 x = S.read pair.1 y)) ρ

/-- Compatible source worlds B_J(x) for target world x under partial assignment ρ. -/
def partialPortWorlds (ρ : PartialAssign sp tp) (x : Fin tw) : List (Fin sw) :=
  (indices sw).filter (fun y => partialReadOK S T ρ x y)

/-- Every target world has at least one read-compatible source world under ρ. -/
def partialReadCover (ρ : PartialAssign sp tp) : Bool :=
  allB (fun x => !(partialPortWorlds S T ρ x).isEmpty) (indices tw)

/-- T23.1: Monotonicity of compatible world sets under extension of partial assignment. -/
theorem partialPortWorlds_monotone (ρ : PartialAssign sp tp) (q : Fin sp) (t : Fin tp)
    (x : Fin tw) (y : Fin sw) :
    y ∈ partialPortWorlds S T ((q, t) :: ρ) x → y ∈ partialPortWorlds S T ρ x := by
  intro hy
  unfold partialPortWorlds at hy ⊢
  rw [List.mem_filter] at hy ⊢
  refine ⟨hy.1, ?_⟩
  have hall := (allB_iff (fun pair : Fin sp × Fin tp => decide (T.read pair.2 x = S.read pair.1 y)) ((q, t) :: ρ)).mp hy.2
  exact (allB_iff (fun pair : Fin sp × Fin tp => decide (T.read pair.2 x = S.read pair.1 y)) ρ).mpr
    (fun pair hp => hall pair (List.Mem.tail _ hp))

/-- Every morphism extending ρ maps target world x into partialPortWorlds ρ x. -/
theorem morphism_mem_partialPortWorlds (M : Morphism S T) (ρ : PartialAssign sp tp)
    (hext : Extends S T M ρ) (x : Fin tw) :
    M.worldMap x ∈ partialPortWorlds S T ρ x := by
  unfold partialPortWorlds
  rw [List.mem_filter]
  refine ⟨mem_indices sw (M.worldMap x), ?_⟩
  apply (allB_iff (fun pair : Fin sp × Fin tp => decide (T.read pair.2 x = S.read pair.1 (M.worldMap x))) ρ).mpr
  intro pair hp
  have hmap : M.portMap pair.1 = pair.2 := hext pair hp
  -- `read_eq` takes four explicit arguments: the port, its membership in S.ports,
  -- the world, and its membership in T.worlds. The point must be followed by its
  -- membership proof, not by the world.
  have hread : T.read (M.portMap pair.1) x = S.read pair.1 (M.worldMap x) :=
    M.read_eq pair.1 (port_mem_all S pair.1) x (world_mem_all T x)
  rw [← hmap]
  exact decide_eq_true hread

/-- T23.2: Empty B_J(x) certifies that no full morphism can extend ρ. -/
theorem empty_partialReadRow_prunes (ρ : PartialAssign sp tp) (x : Fin tw)
    (hempty : partialPortWorlds S T ρ x = []) :
    ¬ ∃ M : Morphism S T, Extends S T M ρ := by
  intro h
  rcases h with ⟨M, hext⟩
  have hmem := morphism_mem_partialPortWorlds S T M ρ hext x
  rw [hempty] at hmem
  cases hmem

/-- Certified pruning rule on partial port assignments. -/
structure CertifiedRule where
  keep : PartialAssign sp tp → Bool
  cost : Nat
  sound : ∀ (M : Morphism S T) (ρ : PartialAssign sp tp),
    Extends S T M ρ → keep ρ = true

/-- T23.2 (rule form): Read-compatibility filter is a certified pruning rule. -/
def readCompatRule (cost : Nat) : CertifiedRule S T where
  keep := partialReadCover S T
  cost := cost
  sound := by
    intro M ρ hext
    unfold partialReadCover
    apply (allB_iff (fun x => !(partialPortWorlds S T ρ x).isEmpty) (indices tw)).mpr
    intro x _
    change (!(partialPortWorlds S T ρ x).isEmpty) = true
    have hmem := morphism_mem_partialPortWorlds S T M ρ hext x
    cases hrows : partialPortWorlds S T ρ x with
    | nil =>
      rw [hrows] at hmem
      cases hmem
    | cons _ _ => rfl

/-- Local price-non-increase check on partial assignment ρ. -/
def partialPriceOK (ρ : PartialAssign sp tp) : Bool :=
  allB (fun pair : Fin sp × Fin tp => decide (T.price pair.2 ≤ S.price pair.1)) ρ

def priceRule (cost : Nat) : CertifiedRule S T where
  keep := partialPriceOK S T
  cost := cost
  sound := by
    intro M ρ hext
    unfold partialPriceOK
    apply (allB_iff (fun pair : Fin sp × Fin tp => decide (T.price pair.2 ≤ S.price pair.1)) ρ).mpr
    intro pair hp
    have hmap := hext pair hp
    have hle := M.price_le pair.1 (mem_indices sp pair.1)
    rw [← hmap]
    exact decide_eq_true hle

/-- A failed sound rule excludes all extending T20 morphisms. -/
theorem rejected_region_empty (rule : CertifiedRule S T) (ρ : PartialAssign sp tp)
    (h : rule.keep ρ = false) : ¬ ∃ M : Morphism S T, Extends S T M ρ := by
  rintro ⟨M, hext⟩
  have hk := rule.sound M ρ hext
  rw [h] at hk
  cases hk

/-- Early injectivity: there is no reason to finish a colliding port map. -/
def partialInjectiveOK (ρ : PartialAssign sp tp) : Bool :=
  allB (fun e : Fin sp × Fin tp =>
    allB (fun f : Fin sp × Fin tp => decide (e.2 = f.2 → e.1 = f.1)) ρ) ρ

def injectiveRule (cost : Nat) : CertifiedRule S T where
  keep := partialInjectiveOK
  cost := cost
  sound := by
    intro M ρ hext
    unfold partialInjectiveOK
    apply (allB_iff _ _).mpr
    intro e he
    apply (allB_iff _ _).mpr
    intro f hf
    apply decide_eq_true
    intro h
    have hm : M.portMap e.1 = M.portMap f.1 := by
      rw [hext e he, hext f hf, h]
    exact M.port_injective e.1 (port_mem_all S e.1) f.1 (port_mem_all S f.1) hm

def depthRule (cost : Nat) : CertifiedRule S T where
  keep := fun _ => decide (S.depth ≤ T.depth)
  cost := cost
  sound := fun M _ _ => decide_eq_true M.depth_le

/-- T23.7: Composition of two certified pruning rules. -/
def composeRule (r1 r2 : CertifiedRule S T) : CertifiedRule S T where
  keep := fun ρ => r1.keep ρ && r2.keep ρ
  cost := r1.cost + r2.cost
  sound := by
    intro M ρ hext
    exact (CRTT.MorphismDiscovery.and_true_iff _ _).mpr
      ⟨r1.sound M ρ hext, r2.sound M ρ hext⟩

/-- Semantic conjunction is commutative; its short-circuit bill need not be. -/
theorem composeRule_same_keep (r1 r2 : CertifiedRule S T) (ρ : PartialAssign sp tp) :
    (composeRule S T r1 r2).keep ρ = (composeRule S T r2 r1).keep ρ := by
  change (r1.keep ρ && r2.keep ρ) = (r2.keep ρ && r1.keep ρ)
  cases r1.keep ρ <;> cases r2.keep ρ <;> rfl

/-- T23.8: Cumulative rule library as a list of certified rules. -/
abbrev RuleLibrary := List (CertifiedRule S T)

def applyLibrary : RuleLibrary S T → CertifiedRule S T
  | [] => ⟨fun _ => true, 0, fun _ _ _ => rfl⟩
  | r :: rs => composeRule S T r (applyLibrary rs)

theorem applyLibrary_sound (L : RuleLibrary S T) (M : Morphism S T)
    (ρ : PartialAssign sp tp) (hext : Extends S T M ρ) :
    (applyLibrary S T L).keep ρ = true :=
  (applyLibrary S T L).sound M ρ hext

/-- T23.3: Prefix-tree search with early pruning over remaining source ports. -/
def prunedExtend (rule : CertifiedRule S T) :
    List (Fin sp) → PartialAssign sp tp → List (PartialAssign sp tp)
  | [], ρ => if rule.keep ρ then [ρ] else []
  | q :: qs, ρ =>
    if rule.keep ρ then
      (indices tp).flatMap (fun t => prunedExtend rule qs ((q, t) :: ρ))
    else []

theorem prunedExtend_mem_prefix (rule : CertifiedRule S T) :
    ∀ (qs : List (Fin sp)) (ρ ρ' : PartialAssign sp tp),
      ρ' ∈ prunedExtend S T rule qs ρ → ∀ pair ∈ ρ, pair ∈ ρ' := by
  intro qs
  induction qs with
  | nil =>
    intro ρ ρ' hm
    by_cases hk : rule.keep ρ = true
    · have hm' : ρ' ∈ [ρ] := by simpa [prunedExtend, hk] using hm
      rcases List.mem_cons.mp hm' with he | ht
      · subst ρ'
        exact fun _ hp => hp
      · cases ht
    · simp [prunedExtend, hk] at hm
  | cons q qs ih =>
    intro ρ ρ' hm
    by_cases hk : rule.keep ρ = true
    · have hm' : ρ' ∈ (indices tp).flatMap
          (fun t => prunedExtend S T rule qs ((q, t) :: ρ)) := by
        simpa [prunedExtend, hk] using hm
      obtain ⟨t, _, ht⟩ := List.mem_flatMap.mp hm'
      intro pair hp
      exact ih ((q, t) :: ρ) ρ' ht pair (List.Mem.tail _ hp)
    · simp [prunedExtend, hk] at hm

/-- T23.4: every valid morphism has a surviving full port assignment. -/
theorem prunedExtend_complete (rule : CertifiedRule S T) (M : Morphism S T) :
    ∀ (qs : List (Fin sp)) (ρ : PartialAssign sp tp),
      Extends S T M ρ →
      ∃ ρ' ∈ prunedExtend S T rule qs ρ,
        Extends S T M ρ' ∧ ∀ q ∈ qs, (q, M.portMap q) ∈ ρ' := by
  intro qs
  induction qs with
  | nil =>
    intro ρ hext
    have hk := rule.sound M ρ hext
    refine ⟨ρ, ?_, hext, fun _ hq => by cases hq⟩
    simp [prunedExtend, hk]
  | cons q qs ih =>
    intro ρ hext
    have hk := rule.sound M ρ hext
    have hext' : Extends S T M ((q, M.portMap q) :: ρ) := by
      intro pair hp
      rcases List.mem_cons.mp hp with he | ht
      · subst pair
        rfl
      · exact hext pair ht
    obtain ⟨ρ', hm, hext'', hqs⟩ := ih ((q, M.portMap q) :: ρ) hext'
    refine ⟨ρ', ?_, hext'', ?_⟩
    · have hflat : ρ' ∈ (indices tp).flatMap
          (fun t => prunedExtend S T rule qs ((q, t) :: ρ)) :=
        List.mem_flatMap.mpr ⟨M.portMap q, mem_indices tp (M.portMap q), hm⟩
      simpa [prunedExtend, hk] using hflat
    · intro q' hq'
      rcases List.mem_cons.mp hq' with he | ht
      · subst q'
        exact prunedExtend_mem_prefix S T rule qs ((q, M.portMap q) :: ρ) ρ' hm
          (q, M.portMap q) (List.Mem.head _)
      · exact hqs q' ht

/-! ### Executable bridge to T22, without enumerating all full port maps
No default inhabitant of Fin tp is required. At a complete leaf, the lookup
proof is supplied only for actual source ports. Final certification is T22's
unchanged certifyPair, not the pruning predicate. -/

def assignmentWitness (ρ : PartialAssign sp tp) (q : Fin sp) :
    Option (Fin sp × Fin tp) :=
  first (fun e : Fin sp × Fin tp => decide (e.1 = q)) ρ

def assignmentCover (ρ : PartialAssign sp tp) : Bool :=
  allB (fun q => (assignmentWitness ρ q).isSome) (indices sp)

def selectedPair (ρ : PartialAssign sp tp) (h : assignmentCover ρ = true)
    (q : Fin sp) : Fin sp × Fin tp :=
  extractSome (assignmentWitness ρ q)
    ((allB_iff (fun r => (assignmentWitness ρ r).isSome) (indices sp)).mp h q
      (mem_indices sp q))

theorem selectedPair_spec (ρ : PartialAssign sp tp) (h : assignmentCover ρ = true)
    (q : Fin sp) : selectedPair ρ h q ∈ ρ ∧ (selectedPair ρ h q).1 = q := by
  have hw : assignmentWitness ρ q = some (selectedPair ρ h q) :=
    extractSome_spec (assignmentWitness ρ q)
      ((allB_iff (fun r => (assignmentWitness ρ r).isSome) (indices sp)).mp h q
        (mem_indices sp q))
  obtain ⟨hm, he⟩ := first_sound (fun e : Fin sp × Fin tp => decide (e.1 = q))
    ρ (selectedPair ρ h q) hw
  exact ⟨hm, of_decide_eq_true he⟩

def decodePortMap (ρ : PartialAssign sp tp) : Option (Fin sp → Fin tp) :=
  if h : assignmentCover ρ = true then some (fun q => (selectedPair ρ h q).2)
  else none

theorem decodePortMap_of_extends (M : Morphism S T) (ρ : PartialAssign sp tp)
    (hext : Extends S T M ρ) (hfull : ∀ q, (q, M.portMap q) ∈ ρ) :
    decodePortMap ρ = some M.portMap := by
  have hc : assignmentCover ρ = true := by
    apply (allB_iff _ _).mpr
    intro q _
    exact first_complete (fun e : Fin sp × Fin tp => decide (e.1 = q)) ρ
      (q, M.portMap q) (hfull q) (by simp)
  have he : (fun q => (selectedPair ρ hc q).2) = M.portMap := by
    funext q
    obtain ⟨hm, hq⟩ := selectedPair_spec ρ hc q
    have hv := hext (selectedPair ρ hc q) hm
    rw [hq] at hv
    exact hv.symm
  have hs : decodePortMap ρ = some (fun q => (selectedPair ρ hc q).2) := by
    simp [decodePortMap, hc]
  exact hs.trans (congrArg some he)

/-- T22's full port guard is retained, even for a trivial pruning rule. -/
def finishPort (p : Fin sp → Fin tp) : List (Morphism S T) :=
  if S.depth ≤ T.depth ∧ portOK S T p = true ∧ readCover S T p = true then
    discoverForPort S T p else []

def finishAssignment (ρ : PartialAssign sp tp) : List (Morphism S T) :=
  match decodePortMap ρ with
  | none => []
  | some p => finishPort S T p

def prunedDiscover (rule : CertifiedRule S T) : List (Morphism S T) :=
  (prunedExtend S T rule (indices sp) []).flatMap (finishAssignment S T)

/-- Successful pair certification preserves its operational maps. -/
theorem certified_pair_maps (p : Fin sp → Fin tp) (a : Fin (sa+1) → Fin (ta+1))
    (N : Morphism S T) (h : certifyPair S T p a = some N) :
    N.portMap = p ∧ N.actionMap = a := by
  by_cases hd : S.depth ≤ T.depth
  · by_cases hp : portOK S T p = true
    · by_cases hw : worldCover S T p a = true
      · rw [certifyPair_of_checks S T p a hd hp hw] at h
        have he := Option.some.inj h
        subst N
        exact ⟨rfl, rfl⟩
      · simp [certifyPair, hd, hp, hw] at h
    · simp [certifyPair, hd, hp] at h
  · simp [certifyPair, hd] at h

/-- No extraneous canonical certificate is returned by the pruned search. -/
theorem prunedDiscover_sound (rule : CertifiedRule S T) (N : Morphism S T)
    (h : N ∈ prunedDiscover S T rule) : N ∈ discoverAll S T := by
  change N ∈ (prunedExtend S T rule (indices sp) []).flatMap (finishAssignment S T) at h
  obtain ⟨ρ, _, hρ⟩ := List.mem_flatMap.mp h
  cases hp : decodePortMap ρ with
  | none => simp [finishAssignment, hp] at hρ
  | some p =>
    by_cases hc : S.depth ≤ T.depth ∧ portOK S T p = true ∧ readCover S T p = true
    · have hm : N ∈ discoverForPort S T p := by
        simpa [finishAssignment, hp, finishPort, hc] using hρ
      have hpc : p ∈ portCandidates S T := by
        apply List.mem_filter.mpr
        exact ⟨maps_complete tp sp p, (CRTT.MorphismDiscovery.and_true_iff _ _).mpr ⟨hc.2.1, hc.2.2⟩⟩
      have hflat : N ∈ (portCandidates S T).flatMap (discoverForPort S T) :=
        List.mem_flatMap.mpr ⟨p, hpc, hm⟩
      simpa [discoverAll, hc.1] using hflat
    · simp [finishAssignment, hp, finishPort, hc] at hρ

/-- Every canonical certificate of exhaustive T22 survives a sound rule. -/
theorem prunedDiscover_complete (rule : CertifiedRule S T) (N : Morphism S T)
    (h : N ∈ discoverAll S T) : N ∈ prunedDiscover S T rule := by
  have hd : S.depth ≤ T.depth := N.depth_le
  have hflat : N ∈ (portCandidates S T).flatMap (discoverForPort S T) := by
    simpa [discoverAll, hd] using h
  obtain ⟨p, hpc, hn⟩ := List.mem_flatMap.mp hflat
  have hpairs : portOK S T p = true ∧ readCover S T p = true :=
    (CRTT.MorphismDiscovery.and_true_iff _ _).mp (List.mem_filter.mp hpc).2
  have hm : some N ∈ (maps (ta+1) (sa+1)).map (certifyPair S T p) :=
    (mem_collectSome _ _).mp hn
  obtain ⟨a, _, ha⟩ := List.mem_map.mp hm
  have he : N.portMap = p := (certified_pair_maps S T p a N ha).1
  obtain ⟨ρ, hρ, hext, hfull⟩ := prunedExtend_complete S T rule N (indices sp) []
    (by intro e he'; cases he')
  have hdec : decodePortMap ρ = some p := by
    have hx := decodePortMap_of_extends S T N ρ hext
      (fun q => hfull q (mem_indices sp q))
    rw [he] at hx
    exact hx
  have hc : S.depth ≤ T.depth ∧ portOK S T p = true ∧ readCover S T p = true :=
    ⟨hd, hpairs.1, hpairs.2⟩
  change N ∈ (prunedExtend S T rule (indices sp) []).flatMap (finishAssignment S T)
  apply List.mem_flatMap.mpr
  refine ⟨ρ, hρ, ?_⟩
  simpa [finishAssignment, hdec, finishPort, hc] using hn

/-- Exact membership, not equality of traversal order or list multiplicity. -/
theorem prunedDiscover_iff (rule : CertifiedRule S T) (N : Morphism S T) :
    N ∈ prunedDiscover S T rule ↔ N ∈ discoverAll S T :=
  ⟨prunedDiscover_sound S T rule N, prunedDiscover_complete S T rule N⟩

theorem prunedDiscover_pair_complete (rule : CertifiedRule S T) (M : Morphism S T) :
    ∃ N ∈ prunedDiscover S T rule, N.portMap = M.portMap ∧ N.actionMap = M.actionMap := by
  obtain ⟨N, hN, hp, ha⟩ := discover_complete S T M
  exact ⟨N, prunedDiscover_complete S T rule N hN, hp, ha⟩

theorem prunedDiscover_empty_iff (rule : CertifiedRule S T) :
    prunedDiscover S T rule = [] ↔ ¬ Nonempty (Morphism S T) := by
  constructor
  · intro h hm
    obtain ⟨M⟩ := hm
    obtain ⟨N, hN, _, _⟩ := prunedDiscover_pair_complete S T rule M
    rw [h] at hN
    cases hN
  · intro h
    cases prunedDiscover S T rule with
    | nil => rfl
    | cons M _ => exact False.elim (h ⟨M⟩)

/-! ### T23.6 & T23.9: Exact Economics of Pruning Rules
This arithmetic model assumes supplied counts and a uniform charge at every
visited node. It is not a budgeted cursor or a theorem about runtime. -/

/-- Exact cost accounting for a search with `visited` nodes, unit node cost `nodeCost`,
    and a rule of cost `ruleCost` evaluated at every visited node. -/
def searchTotalCost (visited nodeCost ruleCost : Nat) : Nat :=
  visited * (nodeCost + ruleCost)

/-- T23.6: Exact profitability criterion for a pruning rule:
    pruned total cost < unpruned total cost iff saved node cost > filter overhead. -/
theorem pruning_profitable_iff (baseNodes prunedNodes nodeCost ruleCost : Nat)
    (hle : prunedNodes ≤ baseNodes) :
    searchTotalCost prunedNodes nodeCost ruleCost < searchTotalCost baseNodes nodeCost 0 ↔
    prunedNodes * ruleCost < (baseNodes - prunedNodes) * nodeCost := by
  have hsave : (baseNodes - prunedNodes) * nodeCost + prunedNodes * nodeCost =
      baseNodes * nodeCost := by
    calc
      _ = ((baseNodes - prunedNodes) + prunedNodes) * nodeCost :=
        (Nat.add_mul _ _ _).symm
      _ = baseNodes * nodeCost :=
        congrArg (fun k : Nat => k * nodeCost) (Nat.sub_add_cancel hle)
  unfold searchTotalCost
  rw [Nat.add_zero, Nat.mul_add]
  -- A bare `omega` on a `↔` over truncated `Nat` arithmetic falls back on a
  -- classical decision; splitting the directions keeps the proof constructive.
  constructor
  · intro h; omega
  · intro h; omega

/-- Abstract short-circuit charge on a fixed collection of n regions. passFirst
counts regions where the first rule returned true. Both rules are pure. -/
def orderedRuleCost (n passFirst firstCost secondCost : Nat) : Nat :=
  n * firstCost + passFirst * secondCost

/-- Order by rejection per cost for a fixed collection of regions. This does
not assert that the necessary pass counts are known for free. -/
theorem ordered_rule_cost_iff (n passA passB cA cB : Nat)
    (ha : passA ≤ n) (hb : passB ≤ n) :
    orderedRuleCost n passA cA cB < orderedRuleCost n passB cB cA ↔
      (n - passB) * cA < (n - passA) * cB := by
  have hA : (n - passA) * cB + passA * cB = n * cB := by
    calc
      _ = ((n - passA) + passA) * cB := (Nat.add_mul _ _ _).symm
      _ = n * cB := congrArg (fun k : Nat => k * cB) (Nat.sub_add_cancel ha)
  have hB : (n - passB) * cA + passB * cA = n * cA := by
    calc
      _ = ((n - passB) + passB) * cA := (Nat.add_mul _ _ _).symm
      _ = n * cA := congrArg (fun k : Nat => k * cA) (Nat.sub_add_cancel hb)
  unfold orderedRuleCost
  constructor
  · intro h; omega
  · intro h; omega

namespace Witnesses

/-- T23.9: Arithmetic witness of higher cost at unchanged node count.
    A separate end-to-end execution witness is tested in Python. -/
theorem sound_rule_hurts_economics :
    let baseNodes := 4
    let prunedNodes := 4
    let nodeCost := 2
    let ruleCost := 1
    searchTotalCost baseNodes nodeCost 0 < searchTotalCost prunedNodes nodeCost ruleCost := by
  decide

end Witnesses

#print axioms composeRule_same_keep
#print axioms ordered_rule_cost_iff
#print axioms rejected_region_empty
#print axioms injectiveRule
#print axioms depthRule
#print axioms selectedPair_spec
#print axioms decodePortMap_of_extends
#print axioms certified_pair_maps
#print axioms prunedDiscover_sound
#print axioms prunedDiscover_complete
#print axioms prunedDiscover_iff
#print axioms prunedDiscover_pair_complete
#print axioms prunedDiscover_empty_iff
#print axioms partialPortWorlds_monotone
#print axioms morphism_mem_partialPortWorlds
#print axioms empty_partialReadRow_prunes
#print axioms readCompatRule
#print axioms priceRule
#print axioms composeRule
#print axioms applyLibrary_sound
#print axioms prunedExtend_mem_prefix
#print axioms prunedExtend_complete
#print axioms pruning_profitable_iff
#print axioms Witnesses.sound_rule_hurts_economics

end CRTT.CertifiedPruning
