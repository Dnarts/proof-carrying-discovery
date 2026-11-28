import AdaptiveObservation

/-!
CRTT T20: certified transfer of deterministic, finite, noiseless binary
investigation trees. The upstream T19 module is copied byte-for-byte.
No complexity or transfer-discovery claim is made by existence of a morphism.
-/
namespace CRTT.InvestigationTransfer

open CRTT.AdaptiveObservation
set_option maxRecDepth 4096

variable {WS QS AS WT QT AT WU QU AU : Type}

/-- The finite domain and resource interface of an existing T19 problem. -/
structure TaskSpec (W Q A : Type) where
  problem : Problem W Q A
  worlds : List W
  ports : List Q
  depth : Nat

/-- All semantic obligations concern declared worlds, ports and actions.
The map of worlds is contravariant; maps of ports and actions are covariant. -/
structure TransferMorphism (S : TaskSpec WS QS AS) (T : TaskSpec WT QT AT) where
  worldMap : WT → WS
  portMap : QS → QT
  actionMap : AS → AT
  world_mem : ∀ w ∈ T.worlds, worldMap w ∈ S.worlds
  port_mem : ∀ q ∈ S.ports, portMap q ∈ T.ports
  action_mem : ∀ a ∈ actions S.problem, actionMap a ∈ actions T.problem
  port_injective : ∀ q ∈ S.ports, ∀ r ∈ S.ports, portMap q = portMap r → q = r
  read_eq : ∀ q ∈ S.ports, ∀ w ∈ T.worlds,
    T.problem.read (portMap q) w = S.problem.read q (worldMap w)
  price_le : ∀ q ∈ S.ports, T.problem.price (portMap q) ≤ S.problem.price q
  loss_le : ∀ a ∈ actions S.problem, ∀ w ∈ T.worlds,
    T.problem.loss (actionMap a) w ≤ S.problem.loss a (worldMap w)
  depth_le : S.depth ≤ T.depth

/-- Pure syntax translation: it cannot consult the target world. -/
def mapTree (p : QS → QT) (a : AS → AT) : Investigation QS AS → Investigation QT AT
  | .act x => .act (a x)
  | .observe q l r => .observe (p q) (mapTree p a l) (mapTree p a r)

abbrev transfer {S : TaskSpec WS QS AS} {T : TaskSpec WT QT AT}
    (M : TransferMorphism S T) (t : Investigation QS AS) : Investigation QT AT :=
  mapTree M.portMap M.actionMap t

abbrev legal [DecidableEq QS] (S : TaskSpec WS QS AS) (t : Investigation QS AS) : Prop :=
  Legal S.problem S.depth S.ports t

abbrev cost (S : TaskSpec WS QS AS) (t : Investigation QS AS) : Nat :=
  worst S.problem S.worlds t

abbrev optimalTree [DecidableEq QS] (S : TaskSpec WS QS AS) : Investigation QS AS :=
  solve S.problem S.depth S.worlds S.ports

abbrev optimum [DecidableEq QS] (S : TaskSpec WS QS AS) : Nat :=
  value S.problem S.depth S.worlds S.ports

/-- Removal respects membership and excludes the purchased port. -/
theorem mem_without_iff [DecidableEq QS] (ps : List QS) (p q : QS) :
    q ∈ without ps p ↔ q ∈ ps ∧ q ≠ p := by
  simp [without, List.mem_filter]

/-- Tree vocabulary, distinct from depth and non-repetition legality. -/
def Declared (S : TaskSpec WS QS AS) : Investigation QS AS → Prop
  | .act a => a ∈ actions S.problem
  | .observe q l r => q ∈ S.ports ∧ Declared S l ∧ Declared S r

theorem declared_of_legal_aux [DecidableEq QS] (S : TaskSpec WS QS AS)
    (n : Nat) (ps : List QS) (t : Investigation QS AS)
    (hsub : ∀ q ∈ ps, q ∈ S.ports) (ht : Legal S.problem n ps t) : Declared S t := by
  induction n generalizing ps t with
  | zero =>
    cases t with
    | act a => exact ht
    | observe q l r => exact False.elim ht
  | succ n ih =>
    cases t with
    | act a => exact ht
    | observe q l r =>
      obtain ⟨hq, hl, hr⟩ := ht
      have hsub' : ∀ u ∈ without ps q, u ∈ S.ports := by
        intro u hu
        exact hsub u ((mem_without_iff ps q u).mp hu).1
      exact ⟨hsub q hq, ih (without ps q) l hsub' hl, ih (without ps q) r hsub' hr⟩

theorem declared_of_legal [DecidableEq QS] (S : TaskSpec WS QS AS)
    (t : Investigation QS AS) (ht : legal S t) : Declared S t :=
  declared_of_legal_aux S S.depth S.ports t (fun _ h => h) ht

/-- T20.3: induction invariant includes remaining-port inclusion, not equality.
In particular extra target ports need not be queried. -/
theorem transfer_legal_aux [DecidableEq QS] [DecidableEq QT]
    {S : TaskSpec WS QS AS} {T : TaskSpec WT QT AT} (M : TransferMorphism S T)
    (n m : Nat) (ps : List QS) (pt : List QT) (t : Investigation QS AS)
    (hd : n ≤ m) (hsub : ∀ q ∈ ps, q ∈ S.ports)
    (hmap : ∀ q ∈ ps, M.portMap q ∈ pt) (ht : Legal S.problem n ps t) :
    Legal T.problem m pt (transfer M t) := by
  induction n generalizing m ps pt t with
  | zero =>
    cases t with
    | act a => cases m <;> exact M.action_mem a ht
    | observe q l r => exact False.elim ht
  | succ n ih =>
    cases t with
    | act a => cases m <;> exact M.action_mem a ht
    | observe q l r =>
      obtain ⟨hq, hl, hr⟩ := ht
      cases m with
      | zero =>
        -- `omega` closing a goal in the inductive `Legal` family by deriving a
        -- contradiction routes through a classical decision and imports
        -- `Classical.choice`. Naming the contradiction keeps it constructive.
        exact absurd hd (Nat.not_succ_le_zero n)
      | succ m =>
        have hd' : n ≤ m := Nat.le_of_succ_le_succ hd
        have hsub' : ∀ u ∈ without ps q, u ∈ S.ports := by
          intro u hu
          exact hsub u ((mem_without_iff ps q u).mp hu).1
        have hmap' : ∀ u ∈ without ps q, M.portMap u ∈ without pt (M.portMap q) := by
          intro u hu
          obtain ⟨hm, hne⟩ := (mem_without_iff ps q u).mp hu
          apply (mem_without_iff pt (M.portMap q) (M.portMap u)).mpr
          refine ⟨hmap u hm, ?_⟩
          intro he
          exact hne (M.port_injective u (hsub u hm) q (hsub q hq) he)
        change M.portMap q ∈ pt ∧
          Legal T.problem m (without pt (M.portMap q)) (transfer M l) ∧
          Legal T.problem m (without pt (M.portMap q)) (transfer M r)
        exact ⟨hmap q hq,
          ih m (without ps q) (without pt (M.portMap q)) l hd' hsub' hmap' hl,
          ih m (without ps q) (without pt (M.portMap q)) r hd' hsub' hmap' hr⟩

theorem transfer_legal [DecidableEq QS] [DecidableEq QT]
    {S : TaskSpec WS QS AS} {T : TaskSpec WT QT AT} (M : TransferMorphism S T)
    (t : Investigation QS AS) (ht : legal S t) : legal T (transfer M t) :=
  transfer_legal_aux M S.depth T.depth S.ports T.ports t M.depth_le
    (fun _ h => h) M.port_mem ht

/-- Realized port/outcome trace, excluding unexecuted branches. -/
def path (P : Problem WS QS AS) (w : WS) : Investigation QS AS → List (QS × Bool)
  | .act _ => []
  | .observe q l r =>
    if P.read q w then (q, true) :: path P w r else (q, false) :: path P w l

def leafAction (P : Problem WS QS AS) (w : WS) : Investigation QS AS → AS
  | .act a => a
  | .observe q l r => if P.read q w then leafAction P w r else leafAction P w l

/-- T20.2/4/5: trace commutation, leaf commutation, and separate cost bounds.
Only membership of the actual world and declared vocabulary are needed here.
The stronger legality theorem is independent of the numerical inequalities. -/
theorem transfer_semantics {S : TaskSpec WS QS AS} {T : TaskSpec WT QT AT}
    (M : TransferMorphism S T) (t : Investigation QS AS) (ht : Declared S t)
    (w : WT) (hw : w ∈ T.worlds) :
    path T.problem w (transfer M t) =
      (path S.problem (M.worldMap w) t).map (fun qb => (M.portMap qb.1, qb.2)) ∧
    leafAction T.problem w (transfer M t) = M.actionMap (leafAction S.problem (M.worldMap w) t) ∧
    observationCost T.problem w (transfer M t) ≤ observationCost S.problem (M.worldMap w) t ∧
    terminalLoss T.problem w (transfer M t) ≤ terminalLoss S.problem (M.worldMap w) t := by
  induction t with
  | act a => exact ⟨rfl, rfl, Nat.le_refl 0, M.loss_le a ht w hw⟩
  | observe q l r ihl ihr =>
    obtain ⟨hq, hl, hr⟩ := ht
    have he := M.read_eq q hq w hw
    have hc := M.price_le q hq
    cases hb : S.problem.read q (M.worldMap w) with
    | false =>
      have hb' : T.problem.read (M.portMap q) w = false := he.trans hb
      obtain ⟨hp, ha, ho, hv⟩ := ihl hl
      refine ⟨?_, ?_, ?_, ?_⟩
      · change path T.problem w (.observe (M.portMap q) (transfer M l) (transfer M r)) = _
        simp [path, hb, hb', hp]
      · change leafAction T.problem w (.observe (M.portMap q) (transfer M l) (transfer M r)) = _
        simp [leafAction, hb, hb', ha]
      · change observationCost T.problem w (.observe (M.portMap q) (transfer M l) (transfer M r)) ≤ _
        simpa [observationCost, hb, hb'] using Nat.add_le_add hc ho
      · change terminalLoss T.problem w (.observe (M.portMap q) (transfer M l) (transfer M r)) ≤ _
        simpa [terminalLoss, hb, hb'] using hv
    | true =>
      have hb' : T.problem.read (M.portMap q) w = true := he.trans hb
      obtain ⟨hp, ha, ho, hv⟩ := ihr hr
      refine ⟨?_, ?_, ?_, ?_⟩
      · change path T.problem w (.observe (M.portMap q) (transfer M l) (transfer M r)) = _
        simp [path, hb, hb', hp]
      · change leafAction T.problem w (.observe (M.portMap q) (transfer M l) (transfer M r)) = _
        simp [leafAction, hb, hb', ha]
      · change observationCost T.problem w (.observe (M.portMap q) (transfer M l) (transfer M r)) ≤ _
        simpa [observationCost, hb, hb'] using Nat.add_le_add hc ho
      · change terminalLoss T.problem w (.observe (M.portMap q) (transfer M l) (transfer M r)) ≤ _
        simpa [terminalLoss, hb, hb'] using hv

theorem transfer_runCost_le {S : TaskSpec WS QS AS} {T : TaskSpec WT QT AT}
    (M : TransferMorphism S T) (t : Investigation QS AS) (ht : Declared S t)
    (w : WT) (hw : w ∈ T.worlds) :
    runCost T.problem w (transfer M t) ≤ runCost S.problem (M.worldMap w) t := by
  obtain ⟨_, _, ho, hv⟩ := transfer_semantics M t ht w hw
  rw [runCost_split T.problem w, runCost_split S.problem (M.worldMap w)]
  exact Nat.add_le_add ho hv

/-- T20.4: the mapped target world must belong to the declared source list. -/
theorem transfer_worst_le [DecidableEq QS]
    {S : TaskSpec WS QS AS} {T : TaskSpec WT QT AT} (M : TransferMorphism S T)
    (t : Investigation QS AS) (ht : legal S t) : cost T (transfer M t) ≤ cost S t := by
  change worst T.problem T.worlds (transfer M t) ≤ worst S.problem S.worlds t
  unfold worst
  apply worstList_le
  intro w hw
  exact Nat.le_trans (transfer_runCost_le M t (declared_of_legal S t ht) w hw)
    (runCost_le_worst S.problem S.worlds t (M.worldMap w) (M.world_mem w hw))

/-- T20.5: separate preservation of observation budget and terminal tolerance. -/
theorem transfer_hard_contract [DecidableEq QS] [DecidableEq QT]
    {S : TaskSpec WS QS AS} {T : TaskSpec WT QT AT} (M : TransferMorphism S T)
    (t : Investigation QS AS) (ht : legal S t) (budget eps : Nat)
    (hc : ∀ w ∈ S.worlds, observationCost S.problem w t ≤ budget ∧ terminalLoss S.problem w t ≤ eps) :
    legal T (transfer M t) ∧
      ∀ w ∈ T.worlds, observationCost T.problem w (transfer M t) ≤ budget ∧
        terminalLoss T.problem w (transfer M t) ≤ eps := by
  refine ⟨transfer_legal M t ht, ?_⟩
  intro w hw
  obtain ⟨_, _, ho, hv⟩ := transfer_semantics M t (declared_of_legal S t ht) w hw
  obtain ⟨hb, he⟩ := hc (M.worldMap w) (M.world_mem w hw)
  exact ⟨Nat.le_trans ho hb, Nat.le_trans hv he⟩

/-- A morphism is a simulation; the target optimum can only improve. -/
theorem optimum_le [DecidableEq QS] [DecidableEq QT]
    {S : TaskSpec WS QS AS} {T : TaskSpec WT QT AT} (M : TransferMorphism S T) :
    optimum T ≤ optimum S := by
  have hs : legal S (optimalTree S) := solve_legal S.problem S.depth S.worlds S.ports
  have ht := transfer_legal M (optimalTree S) hs
  exact Nat.le_trans (solve_optimal T.problem T.depth T.worlds T.ports _ ht)
    (transfer_worst_le M (optimalTree S) hs)

/-- T20.6: two simulations are enough; no inverse or bijection is assumed. -/
theorem mutual_optimum_eq [DecidableEq QS] [DecidableEq QT]
    {S : TaskSpec WS QS AS} {T : TaskSpec WT QT AT}
    (M : TransferMorphism S T) (N : TransferMorphism T S) : optimum T = optimum S :=
  Nat.le_antisymm (optimum_le M) (optimum_le N)

/-- The transported source optimizer is itself optimal, not just equal in value
by an unrelated existence statement. -/
theorem transferred_optimizer [DecidableEq QS] [DecidableEq QT]
    {S : TaskSpec WS QS AS} {T : TaskSpec WT QT AT}
    (M : TransferMorphism S T) (N : TransferMorphism T S) :
    legal T (transfer M (optimalTree S)) ∧ cost T (transfer M (optimalTree S)) = optimum T := by
  have hs : legal S (optimalTree S) := solve_legal S.problem S.depth S.worlds S.ports
  have ht := transfer_legal M (optimalTree S) hs
  refine ⟨ht, Nat.le_antisymm ?_ ?_⟩
  · exact Nat.le_trans (transfer_worst_le M (optimalTree S) hs) (optimum_le N)
  · exact solve_optimal T.problem T.depth T.worlds T.ports _ ht

/-- Identity and composition of certified maps. No reverse map is needed. -/
def identity (S : TaskSpec WS QS AS) : TransferMorphism S S where
  worldMap := id
  portMap := id
  actionMap := id
  world_mem := fun _ h => h
  port_mem := fun _ h => h
  action_mem := fun _ h => h
  port_injective := fun _ _ _ _ h => h
  read_eq := fun _ _ _ _ => rfl
  price_le := fun _ _ => Nat.le_refl _
  loss_le := fun _ _ _ _ => Nat.le_refl _
  depth_le := Nat.le_refl _

/-- T20.7: membership and injectivity are preserved under composition. -/
def compose {S : TaskSpec WS QS AS} {T : TaskSpec WT QT AT} {U : TaskSpec WU QU AU}
    (M : TransferMorphism S T) (N : TransferMorphism T U) : TransferMorphism S U where
  worldMap := fun w => M.worldMap (N.worldMap w)
  portMap := fun q => N.portMap (M.portMap q)
  actionMap := fun a => N.actionMap (M.actionMap a)
  world_mem := fun w h => M.world_mem (N.worldMap w) (N.world_mem w h)
  port_mem := fun q h => N.port_mem (M.portMap q) (M.port_mem q h)
  action_mem := fun a h => N.action_mem (M.actionMap a) (M.action_mem a h)
  port_injective := by
    intro q hq r hr he
    exact M.port_injective q hq r hr
      (N.port_injective (M.portMap q) (M.port_mem q hq) (M.portMap r) (M.port_mem r hr) he)
  read_eq := by
    intro q hq w hw
    exact (N.read_eq (M.portMap q) (M.port_mem q hq) w hw).trans
      (M.read_eq q hq (N.worldMap w) (N.world_mem w hw))
  price_le := fun q h => Nat.le_trans (N.price_le (M.portMap q) (M.port_mem q h)) (M.price_le q h)
  loss_le := fun a ha w hw => Nat.le_trans
    (N.loss_le (M.actionMap a) (M.action_mem a ha) w hw)
    (M.loss_le a ha (N.worldMap w) (N.world_mem w hw))
  depth_le := Nat.le_trans M.depth_le N.depth_le

theorem transfer_identity (S : TaskSpec WS QS AS) (t : Investigation QS AS) :
    transfer (identity S) t = t := by
  induction t with
  | act a => rfl
  | observe q l r ihl ihr =>
    change Investigation.observe q (transfer (identity S) l) (transfer (identity S) r) =
      Investigation.observe q l r
    rw [ihl, ihr]

theorem transfer_compose {S : TaskSpec WS QS AS} {T : TaskSpec WT QT AT} {U : TaskSpec WU QU AU}
    (M : TransferMorphism S T) (N : TransferMorphism T U) (t : Investigation QS AS) :
    transfer (compose M N) t = transfer N (transfer M t) := by
  induction t with
  | act a => rfl
  | observe q l r ihl ihr =>
    change Investigation.observe (N.portMap (M.portMap q)) (transfer (compose M N) l)
      (transfer (compose M N) r) = Investigation.observe (N.portMap (M.portMap q))
      (transfer N (transfer M l)) (transfer N (transfer M r))
    rw [ihl, ihr]

/-- T20.9: actual fixed overhead, in the same units as operational cost.
The comparator must include any fresh synthesis/validation cost being claimed. -/
theorem paid_transfer_iff (overhead actual baseline : Nat) :
    overhead + actual < baseline ↔ overhead < baseline - actual := by
  -- A bare `omega` on a `↔` over truncated `Nat` subtraction falls back on a
  -- classical decision and drags in `Classical.choice`; splitting the two
  -- directions first keeps the proof constructive.
  constructor
  · intro h; omega
  · intro h; omega

theorem paid_transfer_sufficient [DecidableEq QS]
    {S : TaskSpec WS QS AS} {T : TaskSpec WT QT AT} (M : TransferMorphism S T)
    (t : Investigation QS AS) (ht : legal S t) (overhead baseline : Nat)
    (h : overhead + cost S t < baseline) : overhead + cost T (transfer M t) < baseline :=
  Nat.lt_of_le_of_lt (Nat.add_le_add_left (transfer_worst_le M t ht) overhead) h

namespace Witnesses

/-! Equal optimum alone is insufficient, even on very small tasks. -/
def bitProblem (flip : Bool) : Problem Bool Unit Bool where
  defaultAction := false
  otherActions := [true]
  read := fun _ w => if flip then !w else w
  price := fun _ => 1
  loss := fun a w => if a = w then 0 else 4

def bitTask (flip : Bool) : TaskSpec Bool Unit Bool where
  problem := bitProblem flip
  worlds := [false, true]
  ports := [()]
  depth := 1

def bitTree : Investigation Unit Bool := .observe () (.act false) (.act true)

theorem bit_tree_legal : legal (bitTask false) bitTree := by
  unfold bitTree
  refine ⟨by decide, ?_, ?_⟩
  · change false ∈ actions (bitProblem false)
    decide
  · change true ∈ actions (bitProblem false)
    decide

theorem bit_tree_optimal : cost (bitTask false) bitTree = optimum (bitTask false) := by decide

/-- T20.8a: a specified translation can fail despite identical optimum. -/
theorem equal_optimum_bad_translation :
    optimum (bitTask false) = 1 ∧ optimum (bitTask true) = 1 ∧
    cost (bitTask true) (mapTree id id bitTree) = 5 := by decide

/-- There *is* a certified alternative translation: complement world and action. -/
def flipMorphism : TransferMorphism (bitTask false) (bitTask true) where
  worldMap := fun w => !w
  portMap := id
  actionMap := fun a => !a
  world_mem := by intro w _hw; cases w <;> decide
  port_mem := fun q h => h
  action_mem := by intro a _ha; cases a <;> decide
  port_injective := fun _ _ _ _ h => h
  read_eq := by intro q _hq w _hw; cases q; cases w <;> rfl
  price_le := fun _ _ => Nat.le_refl _
  loss_le := by intro a _ha w _hw; cases a <;> cases w <;> decide
  depth_le := Nat.le_refl _

/-- The source has two interchangeable ports. A particular tree can still
transfer, but a globally injective vocabulary map into Unit cannot exist. -/
def redundantTask : TaskSpec Bool Bool Bool where
  problem :=
    { defaultAction := false, otherActions := [true], read := fun _ w => w,
      price := fun _ => 1, loss := fun a w => if a = w then 0 else 4 }
  worlds := [false, true]
  ports := [false, true]
  depth := 1

theorem equal_optimum_no_global_morphism :
    optimum redundantTask = 1 ∧ optimum (bitTask false) = 1 ∧
    ¬ Nonempty (TransferMorphism redundantTask (bitTask false)) := by
  refine ⟨by decide, by decide, ?_⟩
  intro h
  obtain ⟨M⟩ := h
  have he : M.portMap false = M.portMap true := Subsingleton.elim _ _
  have hf : false = true := M.port_injective false (by decide) true (by decide) he
  exact Bool.noConfusion hf

/-- Equal optima and equal port cardinality still do not suffice: the source
has a zero-loss action at each world, but the target has only unit-loss actions.
No world/action map can satisfy the terminal-loss inequality. -/
def flatTask : TaskSpec Bool Unit Bool where
  problem :=
    { defaultAction := false, otherActions := [true], read := fun _ _ => false,
      price := fun _ => 1, loss := fun _ _ => 1 }
  worlds := [false, true]
  ports := [()]
  depth := 1

theorem equal_optimum_no_loss_morphism :
    optimum (bitTask false) = 1 ∧ optimum flatTask = 1 ∧
    ¬ Nonempty (TransferMorphism (bitTask false) flatTask) := by
  refine ⟨by decide, by decide, ?_⟩
  intro h
  obtain ⟨M⟩ := h
  have ha : M.worldMap false ∈ actions (bitTask false).problem := by
    change M.worldMap false ∈ [false, true]
    cases M.worldMap false <;> decide
  have hh := M.loss_le (M.worldMap false) ha false (by decide)
  have hn : (1 : Nat) ≤ 0 := by
    simp [flatTask, bitTask, bitProblem] at hh
  omega

/-- The certified translation actually repairs the opposite-read task. -/
theorem flipped_tree_cost : cost (bitTask true) (transfer flipMorphism bitTree) = 1 := by decide

end Witnesses

#print axioms declared_of_legal
#print axioms transfer_legal
#print axioms transfer_semantics
#print axioms transfer_runCost_le
#print axioms transfer_worst_le
#print axioms transfer_hard_contract
#print axioms optimum_le
#print axioms mutual_optimum_eq
#print axioms transferred_optimizer
#print axioms identity
#print axioms compose
#print axioms transfer_identity
#print axioms transfer_compose
#print axioms paid_transfer_iff
#print axioms paid_transfer_sufficient
#print axioms Witnesses.bit_tree_legal
#print axioms Witnesses.bit_tree_optimal
#print axioms Witnesses.equal_optimum_bad_translation
#print axioms Witnesses.equal_optimum_no_global_morphism
#print axioms Witnesses.equal_optimum_no_loss_morphism
#print axioms Witnesses.flipMorphism
#print axioms Witnesses.flipped_tree_cost

end CRTT.InvestigationTransfer
