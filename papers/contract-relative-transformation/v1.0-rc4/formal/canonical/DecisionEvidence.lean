import MetaEvidenceAcquisition

/-! Decision-relative evidence. The hypothesis is a whole cost table, not
an underlying execution world. The benchmark and candidate bills are supplied
with certificates; preparing them is not free. Regret and actual expenditure
are distinct objectives. All claims are relative to the declared finite model. -/
namespace CRTT.DecisionEvidence
open CRTT.AdaptiveObservation
open CRTT.MetaEvidenceAcquisition (Bounds withLoss legal_withLoss worst_loss_le value_loss_le)
open CRTT.MetaInvestigation (walk walk_cost)
open CRTT.MorphismDiscovery (allB allB_iff)
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

structure Model (H C : Type) where
  defaultController : C
  otherControllers : List C
  bill : C → H → Nat
  reference : H → Nat
  referenceLower : ∀ c ∈ defaultController :: otherControllers, ∀ h, reference h ≤ bill c h

variable {H C E : Type}

def admitted (D : Model H C) : List C := D.defaultController :: D.otherControllers

def regret (D : Model H C) (c : C) (h : H) : Nat := D.bill c h - D.reference h

def robustRegret (D : Model H C) (belief : List H) (c : C) : Nat :=
  worstList (regret D c) belief

def terminalController (D : Model H C) (belief : List H) : C :=
  pick (robustRegret D belief) D.defaultController D.otherControllers

def residual (D : Model H C) (belief : List H) : Nat :=
  robustRegret D belief (terminalController D belief)

theorem terminal_admitted (D : Model H C) (belief : List H) :
    terminalController D belief ∈ admitted D :=
  pick_mem (robustRegret D belief) D.defaultController D.otherControllers

theorem residual_le (D : Model H C) (belief : List H) (c : C) (hc : c ∈ admitted D) :
    residual D belief ≤ robustRegret D belief c :=
  pick_le (robustRegret D belief) D.defaultController D.otherControllers c hc

/-- Exact decision certificate relative to the specified reference. No claim
that this reference is an oracle optimum until its separate proof is supplied. -/
theorem robust_iff (D : Model H C) (belief : List H) (c : C) (eps : Nat) :
    robustRegret D belief c ≤ eps ↔ ∀ h ∈ belief, D.bill c h ≤ D.reference h + eps := by
  constructor
  · intro hr h hm
    have hv : regret D c h ≤ eps := Nat.le_trans
      (le_worstList (f := regret D c) (xs := belief) (x := h) hm) hr
    unfold regret at hv
    omega
  · intro hr
    unfold robustRegret
    apply worstList_le
    intro h hm
    have hv := hr h hm
    unfold regret
    omega

theorem residual_iff (D : Model H C) (belief : List H) (eps : Nat) :
    residual D belief ≤ eps ↔
      ∃ c ∈ admitted D, ∀ h ∈ belief, D.bill c h ≤ D.reference h + eps := by
  constructor
  · intro h
    exact ⟨terminalController D belief, terminal_admitted D belief,
      (robust_iff D belief _ eps).mp h⟩
  · rintro ⟨c, hc, h⟩
    exact Nat.le_trans (residual_le D belief c hc) ((robust_iff D belief c eps).mpr h)

theorem robust_subset (D : Model H C) (old new : List H) (c : C)
    (hsub : ∀ h ∈ new, h ∈ old) : robustRegret D new c ≤ robustRegret D old c := by
  unfold robustRegret
  apply worstList_le
  intro h hh
  exact le_worstList (f := regret D c) (xs := old) (x := h) (hsub h hh)

theorem residual_subset (D : Model H C) (old new : List H)
    (hsub : ∀ h ∈ new, h ∈ old) : residual D new ≤ residual D old :=
  Nat.le_trans (residual_le D new _ (terminal_admitted D old))
    (robust_subset D old new _ hsub)

/-- Exact benchmark over the finite declared controller catalogue. -/
def catalogueModel (base : C) (others : List C) (bill : C → H → Nat) : Model H C where
  defaultController := base
  otherControllers := others
  bill := bill
  reference := fun h => bill (pick (fun c => bill c h) base others) h
  referenceLower := by
    intro c hc h
    exact pick_le (fun d => bill d h) base others c hc

theorem catalogue_reference_attained (base : C) (others : List C) (bill : C → H → Nat) (h : H) :
    ∃ c ∈ admitted (catalogueModel base others bill),
      bill c h = (catalogueModel base others bill).reference h :=
  ⟨pick (fun c => bill c h) base others, pick_mem _ _ _, rfl⟩

/-- Necessary and sufficient robust pairwise dominance (with additive slack),
relative to the catalogue optimum, not to arbitrary unlisted algorithms. -/
theorem catalogue_robust_iff (base : C) (others : List C) (bill : C → H → Nat)
    (belief : List H) (c : C) (eps : Nat) :
    robustRegret (catalogueModel base others bill) belief c ≤ eps ↔
      ∀ h ∈ belief, ∀ d ∈ base :: others, bill c h ≤ bill d h + eps := by
  constructor
  · intro hr h hh d hd
    let D := catalogueModel base others bill
    have h1 := (robust_iff D belief c eps).mp hr h hh
    have h2 := Nat.add_le_add_right (D.referenceLower d hd h) eps
    exact Nat.le_trans h1 h2
  · intro hr
    apply (robust_iff (catalogueModel base others bill) belief c eps).mpr
    intro h hh
    exact hr h hh (pick (fun d => bill d h) base others) (pick_mem _ _ _)

/-- Independent interval comparisons. Correlated exact hypotheses can give
stronger certificates than a rectangular interval enclosure. -/
theorem interval_pair (x y : Nat) (bx : Bounds x) (yb : Bounds y) (eps : Nat)
    (h : bx.upper ≤ yb.lower + eps) : x ≤ y + eps :=
  Nat.le_trans bx.upper_ok (Nat.le_trans h (Nat.add_le_add_right yb.lower_ok eps))

theorem catalogue_interval_certificate [DecidableEq C] (base : C) (others : List C) (bill : C → H → Nat)
    (bounds : ∀ c h, Bounds (bill c h)) (belief : List H) (c : C) (eps : Nat)
    (hc : ∀ h ∈ belief, ∀ d ∈ base :: others, d ≠ c →
      (bounds c h).upper ≤ (bounds d h).lower + eps) :
    robustRegret (catalogueModel base others bill) belief c ≤ eps := by
  apply (catalogue_robust_iff base others bill belief c eps).mpr
  intro h hh d hd
  by_cases he : d = c
  · subst d
    exact Nat.le_add_right _ _
  · exact interval_pair _ _ (bounds c h) (bounds d h) eps (hc h hh d hd he)

/-- Executable sufficient interval test. It reads only the certified endpoints,
not the exact bills or the optimum. A false result is not a refutation of
optimality. The self-comparison is skipped. -/
def intervalOK [DecidableEq C] (base : C) (others : List C) (bill : C → H → Nat)
    (bounds : ∀ c h, Bounds (bill c h)) (belief : List H) (c : C) (eps : Nat) : Bool :=
  allB (fun h => allB (fun d =>
    if d = c then true else decide ((bounds c h).upper ≤ (bounds d h).lower + eps))
    (base :: others)) belief

theorem intervalOK_sound [DecidableEq C] (base : C) (others : List C) (bill : C → H → Nat)
    (bounds : ∀ c h, Bounds (bill c h)) (belief : List H) (c : C) (eps : Nat)
    (hok : intervalOK base others bill bounds belief c eps = true) :
    robustRegret (catalogueModel base others bill) belief c ≤ eps := by
  apply catalogue_interval_certificate base others bill bounds belief c eps
  intro h hh d hd hne
  have hr : allB (fun d' => if d' = c then true else
      decide ((bounds c h).upper ≤ (bounds d' h).lower + eps)) (base :: others) = true :=
    (allB_iff (fun w => allB (fun d' => if d' = c then true else
      decide ((bounds c w).upper ≤ (bounds d' w).lower + eps)) (base :: others)) belief).mp hok h hh
  have hc : (if d = c then true else
      decide ((bounds c h).upper ≤ (bounds d h).lower + eps)) = true :=
    (allB_iff (fun d' => if d' = c then true else
      decide ((bounds c h).upper ≤ (bounds d' h).lower + eps)) (base :: others)).mp hr d hd
  rw [ite_eq_right hne] at hc
  exact of_decide_eq_true hc

def intervalCandidates [DecidableEq C] (base : C) (others : List C) (bill : C → H → Nat)
    (bounds : ∀ c h, Bounds (bill c h)) (belief : List H) (eps : Nat) : List C :=
  (base :: others).filter (fun c => intervalOK base others bill bounds belief c eps)

theorem intervalCandidate_sound [DecidableEq C] (base : C) (others : List C) (bill : C → H → Nat)
    (bounds : ∀ c h, Bounds (bill c h)) (belief : List H) (eps : Nat) (c : C)
    (hm : c ∈ intervalCandidates base others bill bounds belief eps) :
    c ∈ admitted (catalogueModel base others bill) ∧
      robustRegret (catalogueModel base others bill) belief c ≤ eps := by
  change c ∈ (base :: others).filter (fun d => intervalOK base others bill bounds belief d eps) at hm
  obtain ⟨hl, hk⟩ := List.mem_filter.mp hm
  exact ⟨hl, intervalOK_sound base others bill bounds belief c eps hk⟩

/-! A family of legal T19 controllers with EXACT supplied bills and benchmarks.
The full optimum is over all legal T19 trees for the base interface, not just
listed candidate trees. Membership and the cost identities are proof obligations. -/
section Family
variable {W Q A : Type} [DecidableEq Q]
variable (P : Problem W Q A) (n : Nat) (worlds : List W) (ports : List Q)

abbrev Controller := { t : Investigation Q A // Legal P n ports t }

def exactFamilyModel (losses : H → A → W → Nat)
    (base : Controller P n ports) (others : List (Controller P n ports))
    (bills : Controller P n ports → H → Nat) (refs : H → Nat)
    (hb : ∀ c h, bills c h = worst (withLoss P (losses h)) worlds c.val)
    (hr : ∀ h, refs h = value (withLoss P (losses h)) n worlds ports) :
    Model H (Controller P n ports) where
  defaultController := base
  otherControllers := others
  bill := bills
  reference := refs
  referenceLower := by
    intro c _ h
    rw [hr h, hb c h]
    exact solve_optimal (withLoss P (losses h)) n worlds ports c.val
      ((legal_withLoss P (losses h) n ports c.val).mpr c.property)

/-- A bridge to T26's shared endpoint certificate: the same upper optimizer
is near-optimal for every compatible whole cost table. -/
theorem shared_endpoint_regret (losses : H → A → W → Nat) (belief : List H)
    (lo hi : A → W → Nat)
    (hl : ∀ h ∈ belief, ∀ a w, lo a w ≤ losses h a w)
    (hu : ∀ h ∈ belief, ∀ a w, losses h a w ≤ hi a w)
    (h : H) (hm : h ∈ belief) :
    worst (withLoss P (losses h)) worlds (solve (withLoss P hi) n worlds ports) -
        value (withLoss P (losses h)) n worlds ports ≤
      value (withLoss P hi) n worlds ports - value (withLoss P lo) n worlds ports := by
  have hL := value_loss_le P lo (losses h) (hl h hm) n worlds ports
  have hU := worst_loss_le P (losses h) hi (hu h hm) worlds
    (solve (withLoss P hi) n worlds ports)
  change worst (withLoss P (losses h)) worlds (solve (withLoss P hi) n worlds ports) ≤
    value (withLoss P hi) n worlds ports at hU
  omega

end Family

/-! Explicit decision certificates, including for empty beliefs. The latter
are vacuous; actual deployment separately requires true hypothesis membership. -/
structure DecisionCertificate (D : Model H C) (belief : List H) (eps : Nat) where
  controller : C
  listed : controller ∈ admitted D
  bounded : robustRegret D belief controller ≤ eps

def assess (D : Model H C) (belief : List H) (eps : Nat) : Option (DecisionCertificate D belief eps) :=
  let c := terminalController D belief
  if h : robustRegret D belief c ≤ eps then
    some ⟨c, terminal_admitted D belief, h⟩
  else none

theorem assess_complete (D : Model H C) (belief : List H) (eps : Nat) :
    (assess D belief eps).isSome = true ↔ residual D belief ≤ eps := by
  by_cases h : robustRegret D belief (terminalController D belief) ≤ eps
  · simp [assess, residual, h]
  · simp [assess, residual, h]

theorem certificate_bill (D : Model H C) (belief : List H) (eps : Nat)
    (r : DecisionCertificate D belief eps) (h : H) (hm : h ∈ belief) :
    D.bill r.controller h ≤ D.reference h + eps :=
  (robust_iff D belief r.controller eps).mp r.bounded h hm

/-! T19 acquisition over whole cost hypotheses. The actual hypothesis is not
an argument of the solver. It is used only to specify the response semantics. -/
def evidenceProblem (D : Model H C) (read : E → H → Bool) (fee : E → Nat) : Problem H E C where
  defaultAction := D.defaultController
  otherActions := D.otherControllers
  read := read
  price := fee
  loss := regret D

def refine (read : E → H → Bool) (belief : List H) (q : E) (b : Bool) : List H :=
  belief.filter (fun h => decide (read q h = b))

theorem refine_membership (read : E → H → Bool) (belief : List H) (q : E) (b : Bool) (h : H) :
    h ∈ refine read belief q b ↔ h ∈ belief ∧ read q h = b := by
  simp [refine, List.mem_filter]

theorem refine_truth (read : E → H → Bool) (belief : List H) (q : E) (h : H)
    (hm : h ∈ belief) : h ∈ refine read belief q (read q h) :=
  (refine_membership read belief q (read q h) h).mpr ⟨hm, rfl⟩

theorem refine_residual_le (D : Model H C) (read : E → H → Bool)
    (belief : List H) (q : E) (b : Bool) : residual D (refine read belief q b) ≤ residual D belief :=
  residual_subset D belief _ (fun h hm => ((refine_membership read belief q b h).mp hm).1)

def acquisitionTree [DecidableEq E] (D : Model H C) (read : E → H → Bool) (fee : E → Nat)
    (n : Nat) (belief : List H) (ports : List E) : Investigation E C :=
  solve (evidenceProblem D read fee) n belief ports

def acquisitionValue [DecidableEq E] (D : Model H C) (read : E → H → Bool) (fee : E → Nat)
    (n : Nat) (belief : List H) (ports : List E) : Nat :=
  value (evidenceProblem D read fee) n belief ports

theorem acquisition_legal [DecidableEq E] (D : Model H C) (read : E → H → Bool) (fee : E → Nat)
    (n : Nat) (belief : List H) (ports : List E) :
    Legal (evidenceProblem D read fee) n ports (acquisitionTree D read fee n belief ports) :=
  solve_legal _ _ _ _

theorem acquisition_optimal [DecidableEq E] (D : Model H C) (read : E → H → Bool) (fee : E → Nat)
    (n : Nat) (belief : List H) (ports : List E) (t : Investigation E C)
    (ht : Legal (evidenceProblem D read fee) n ports t) :
    acquisitionValue D read fee n belief ports ≤ worst (evidenceProblem D read fee) belief t :=
  solve_optimal _ _ _ _ t ht

theorem acquisition_zero [DecidableEq E] (D : Model H C) (read : E → H → Bool) (fee : E → Nat)
    (belief : List H) (ports : List E) : acquisitionValue D read fee 0 belief ports = residual D belief := rfl

theorem acquisition_bellman [DecidableEq E] (D : Model H C) (read : E → H → Bool) (fee : E → Nat)
    (n : Nat) (belief : List H) (ports : List E) (hne : belief ≠ []) :
    acquisitionValue D read fee (n+1) belief ports = minFold (residual D belief)
      (ports.map (fun q => fee q + max
        (acquisitionValue D read fee n (refine read belief q false) (without ports q))
        (acquisitionValue D read fee n (refine read belief q true) (without ports q)))) :=
  bellman (evidenceProblem D read fee) n belief ports hne

/-! Execution uses the existing T25 walk interface. Its sense argument is
an operational port, not a hidden cost-table evaluator. -/
theorem walk_member [DecidableEq E] (P : Problem H E C) (h : H) :
    ∀ (t : Investigation E C) (n : Nat) (ports : List E), Legal P n ports t →
      (walk (fun q => P.read q h) P.price t).action ∈ actions P := by
  intro t
  induction t with
  | act c =>
    intro n ports ht
    cases n <;> exact ht
  | observe q l r ihl ihr =>
    intro n ports ht
    cases n with
    | zero => exact False.elim ht
    | succ n =>
      obtain ⟨_, hl, hr⟩ := ht
      cases he : P.read q h with
      | false => simpa [walk, he] using ihl n (without ports q) hl
      | true => simpa [walk, he] using ihr n (without ports q) hr

theorem walk_terminal (P : Problem H E C) (h : H) (t : Investigation E C) :
    P.loss (walk (fun q => P.read q h) P.price t).action h = terminalLoss P h t := by
  induction t with
  | act c => rfl
  | observe q l r ihl ihr =>
    cases he : P.read q h with
    | false => simpa [walk, terminalLoss, he] using ihl
    | true => simpa [walk, terminalLoss, he] using ihr

theorem walk_paid (P : Problem H E C) (h : H) (t : Investigation E C) :
    (walk (fun q => P.read q h) P.price t).paid = observationCost P h t := by
  induction t with
  | act c => rfl
  | observe q l r ihl ihr =>
    cases he : P.read q h with
    | false => simpa [walk, observationCost, he] using congrArg (fun k => P.price q + k) ihl
    | true => simpa [walk, observationCost, he] using congrArg (fun k => P.price q + k) ihr

/-- Fixed overhead is stated explicitly; it is not optimized for free. -/
def totalBill (D : Model H C) (read : E → H → Bool) (fee : E → Nat)
    (setup : Nat) (h : H) (t : Investigation E C) : Nat :=
  let d := walk (fun q => read q h) fee t
  setup + (d.paid + D.bill d.action h)

theorem total_bill_identity [DecidableEq E] (D : Model H C) (read : E → H → Bool) (fee : E → Nat)
    (setup : Nat) (h : H) (t : Investigation E C) (n : Nat) (ports : List E)
    (ht : Legal (evidenceProblem D read fee) n ports t) :
    totalBill D read fee setup h t = setup + (D.reference h + runCost (evidenceProblem D read fee) h t) := by
  let d := walk (fun q => read q h) fee t
  have hm : d.action ∈ admitted D := walk_member (evidenceProblem D read fee) h t n ports ht
  have hl := D.referenceLower d.action hm h
  have hc := walk_cost (evidenceProblem D read fee) h t
  change d.paid + (D.bill d.action h - D.reference h) =
    runCost (evidenceProblem D read fee) h t at hc
  change setup + (d.paid + D.bill d.action h) = _
  omega

theorem optimizer_bill_bound [DecidableEq E] (D : Model H C) (read : E → H → Bool) (fee : E → Nat)
    (setup : Nat) (n : Nat) (belief : List H) (ports : List E) (h : H) (hm : h ∈ belief) :
    totalBill D read fee setup h (acquisitionTree D read fee n belief ports) ≤
      setup + (D.reference h + acquisitionValue D read fee n belief ports) := by
  rw [total_bill_identity D read fee setup h _ n ports (acquisition_legal D read fee n belief ports)]
  exact Nat.add_le_add_left (Nat.add_le_add_left
    (runCost_le_worst (evidenceProblem D read fee) belief _ h hm) (D.reference h)) setup

/-! Separate hard epsilon from query budget. A cheap but inaccurate decision
must not pass a hard contract just because its regret+fee is small. -/
structure HardEvidence [DecidableEq E] (D : Model H C) (read : E → H → Bool) (fee : E → Nat)
    (n : Nat) (belief : List H) (ports : List E) (eps budget : Nat) where
  tree : Investigation E C
  legal : Legal (evidenceProblem D read fee) n ports tree
  funded : ∀ h ∈ belief, observationCost (evidenceProblem D read fee) h tree ≤ budget ∧
    terminalLoss (evidenceProblem D read fee) h tree ≤ eps

def hardAssess [DecidableEq E] (D : Model H C) (read : E → H → Bool) (fee : E → Nat)
    (n : Nat) (belief : List H) (ports : List E) (eps budget : Nat) :
    Option (HardEvidence D read fee n belief ports eps budget) :=
  let P := evidenceProblem D read fee
  let Pc := cappedProblem P eps budget
  let t := solve Pc n belief ports
  if h : worst Pc belief t ≤ budget then
    some ⟨t, (capped_legal P eps budget n ports t).mp (solve_legal Pc n belief ports),
      (capped_worst_iff P eps budget belief t).mp h⟩
  else none

theorem hard_assess_complete [DecidableEq E] (D : Model H C) (read : E → H → Bool) (fee : E → Nat)
    (n : Nat) (belief : List H) (ports : List E) (eps budget : Nat) :
    (hardAssess D read fee n belief ports eps budget).isSome = true ↔
      ∃ t, Legal (evidenceProblem D read fee) n ports t ∧
        ∀ h ∈ belief, observationCost (evidenceProblem D read fee) h t ≤ budget ∧
          terminalLoss (evidenceProblem D read fee) h t ≤ eps := by
  have he := epsilon_budget_iff (evidenceProblem D read fee) n belief ports eps budget
  rw [← he]
  change (hardAssess D read fee n belief ports eps budget).isSome = true ↔
    worst (cappedProblem (evidenceProblem D read fee) eps budget) belief
      (solve (cappedProblem (evidenceProblem D read fee) eps budget) n belief ports) ≤ budget
  by_cases h : worst (cappedProblem (evidenceProblem D read fee) eps budget) belief
      (solve (cappedProblem (evidenceProblem D read fee) eps budget) n belief ports) ≤ budget
  · simp [hardAssess, h]
  · simp [hardAssess, h]

theorem hard_execution [DecidableEq E] (D : Model H C) (read : E → H → Bool) (fee : E → Nat)
    (n : Nat) (belief : List H) (ports : List E) (eps budget : Nat)
    (r : HardEvidence D read fee n belief ports eps budget) (h : H) (hm : h ∈ belief) :
    let d := walk (fun q => read q h) fee r.tree
    d.action ∈ admitted D ∧ d.paid ≤ budget ∧ D.bill d.action h ≤ D.reference h + eps := by
  let P := evidenceProblem D read fee
  let d := walk (fun q => read q h) fee r.tree
  have hm' : d.action ∈ admitted D := walk_member P h r.tree n ports r.legal
  have hp : d.paid = observationCost P h r.tree := walk_paid P h r.tree
  have hl : regret D d.action h = terminalLoss P h r.tree := walk_terminal P h r.tree
  have hf := r.funded h hm
  change d.action ∈ admitted D ∧ d.paid ≤ budget ∧ D.bill d.action h ≤ D.reference h + eps
  refine ⟨hm', ?_, ?_⟩
  · rw [hp]
    exact hf.1
  · have hv : regret D d.action h ≤ eps := by
      rw [hl]
      exact hf.2
    unfold regret at hv
    omega

/-- Once the hard contract is feasible, the capped optimizer also minimizes
worst observation expenditure among all epsilon-valid legal trees, regardless
of whether the competitors themselves fit the stated budget. -/
theorem capped_worst_of_valid (P : Problem H E C) (belief : List H) (t : Investigation E C)
    (eps budget : Nat) (h : ∀ w ∈ belief, terminalLoss P w t ≤ eps) :
    worst (cappedProblem P eps budget) belief t = worstList (fun w => observationCost P w t) belief := by
  have he : ∀ w ∈ belief, runCost (cappedProblem P eps budget) w t = observationCost P w t := by
    intro w hw
    rw [capped_cost P eps budget w t, ite_eq_left (h w hw), Nat.add_zero]
  unfold worst
  apply Nat.le_antisymm
  · apply worstList_le
    intro w hw
    rw [he w hw]
    exact le_worstList (f := fun u => observationCost P u t) (xs := belief) (x := w) hw
  · apply worstList_le
    intro w hw
    rw [← he w hw]
    exact le_worstList (f := fun u => runCost (cappedProblem P eps budget) u t) (xs := belief) (x := w) hw

theorem hard_minimal_observation [DecidableEq E] (P : Problem H E C) (n : Nat) (belief : List H)
    (ports : List E) (eps budget : Nat)
    (hf : value (cappedProblem P eps budget) n belief ports ≤ budget)
    (t : Investigation E C) (ht : Legal P n ports t)
    (hv : ∀ w ∈ belief, terminalLoss P w t ≤ eps) :
    worstList (fun w => observationCost P w (solve (cappedProblem P eps budget) n belief ports)) belief ≤
      worstList (fun w => observationCost P w t) belief := by
  let s := solve (cappedProblem P eps budget) n belief ports
  have hs := (capped_worst_iff P eps budget belief s).mp hf
  have h1 := capped_worst_of_valid P belief s eps budget (fun w hw => (hs w hw).2)
  have h2 := capped_worst_of_valid P belief t eps budget hv
  have ho := solve_optimal (cappedProblem P eps budget) n belief ports t
    ((capped_legal P eps budget n ports t).mpr ht)
  change worst (cappedProblem P eps budget) belief s ≤ worst (cappedProblem P eps budget) belief t at ho
  rw [h1, h2] at ho
  exact ho

namespace Witnesses

def shiftBill (c h : Bool) : Nat := (if h then 100 else 0) + (if c then 1 else 0)
def shiftModel : Model Bool Bool := catalogueModel false [true] shiftBill

theorem common_optimum_uncertain_value :
    residual shiftModel [false, true] = 0 ∧
      shiftModel.reference true - shiftModel.reference false = 100 := by decide

def crossBill (c h : Bool) : Nat := if c == h then 0 else 8
def crossModel : Model Bool Bool := catalogueModel false [true] crossBill

theorem paid_bit_strict_gain :
    acquisitionValue crossModel (fun (_ : Bool) h => h) (fun _ => 2) 1 [false, true] [false] = 2 ∧
    residual crossModel [false, true] = 8 := by decide

def asymmetricBill (c h : Bool) : Nat :=
  if h then (if c then 100 else 110) else (if c then 11 else 0)
def asymmetricModel : Model Bool Bool := catalogueModel false [true] asymmetricBill

theorem regret_not_actual_bill :
    robustRegret asymmetricModel [false,true] false < robustRegret asymmetricModel [false,true] true ∧
      worstList (asymmetricBill true) [false,true] < worstList (asymmetricBill false) [false,true] := by decide

end Witnesses

#print axioms terminal_admitted
#print axioms residual_le
#print axioms robust_iff
#print axioms residual_iff
#print axioms robust_subset
#print axioms residual_subset
#print axioms catalogue_reference_attained
#print axioms catalogue_robust_iff
#print axioms interval_pair
#print axioms catalogue_interval_certificate
#print axioms intervalOK_sound
#print axioms intervalCandidate_sound
#print axioms exactFamilyModel
#print axioms shared_endpoint_regret
#print axioms assess_complete
#print axioms certificate_bill
#print axioms refine_membership
#print axioms refine_truth
#print axioms refine_residual_le
#print axioms acquisition_legal
#print axioms acquisition_optimal
#print axioms acquisition_zero
#print axioms acquisition_bellman
#print axioms walk_member
#print axioms walk_terminal
#print axioms walk_paid
#print axioms total_bill_identity
#print axioms optimizer_bill_bound
#print axioms hardAssess
#print axioms hard_assess_complete
#print axioms hard_execution
#print axioms capped_worst_of_valid
#print axioms hard_minimal_observation
#print axioms Witnesses.common_optimum_uncertain_value
#print axioms Witnesses.paid_bit_strict_gain
#print axioms Witnesses.regret_not_actual_bill
end CRTT.DecisionEvidence
