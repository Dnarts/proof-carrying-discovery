import MorphismDiscovery

namespace CRTT.BudgetedDiscovery
open CRTT.MorphismDiscovery

/-- Generic paid deterministic transition. A quote is strictly positive. -/
structure QuotedStep (State : Type) where
  fee : Nat
  positive : 0 < fee
  next : Unit → State

structure Account (State : Type) where
  state : State
  remaining : Nat
  spent : Nat

def topUp (s : Account State) (b : Nat) : Account State :=
  { s with remaining := s.remaining + b }

/-- Fuel counts transitions, not money. The thunk is forced only after payment. -/
def run (quote : State → Option (QuotedStep State)) : Nat → Account State → Account State
  | 0, s => s
  | n+1, s =>
    match quote s.state with
    | none => s
    | some q =>
      if q.fee ≤ s.remaining then
        run quote n ⟨q.next (), s.remaining - q.fee, s.spent + q.fee⟩
      else s

theorem accounting (quote : State → Option (QuotedStep State)) (n : Nat)
    (s : Account State) :
    (run quote n s).remaining + (run quote n s).spent = s.remaining + s.spent := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    cases h : quote s.state with
    | none => simp [run, h]
    | some q =>
      by_cases hp : q.fee ≤ s.remaining
      · let paid : Account State :=
          ⟨q.next (), s.remaining - q.fee, s.spent + q.fee⟩
        have hstep : run quote (n + 1) s = run quote n paid := by
          change run quote (n + 1) s =
            run quote n ⟨q.next (), s.remaining - q.fee, s.spent + q.fee⟩
          simp [run, h, hp]
        rw [hstep]
        calc
          (run quote n paid).remaining + (run quote n paid).spent =
              paid.remaining + paid.spent := ih paid
          _ = s.remaining + s.spent := by
            change (s.remaining - q.fee) + (s.spent + q.fee) =
              s.remaining + s.spent
            calc
              (s.remaining - q.fee) + (s.spent + q.fee) =
                  (s.remaining - q.fee) + (q.fee + s.spent) :=
                congrArg (fun k : Nat => (s.remaining - q.fee) + k)
                  (Nat.add_comm s.spent q.fee)
              _ = ((s.remaining - q.fee) + q.fee) + s.spent :=
                (Nat.add_assoc _ _ _).symm
              _ = s.remaining + s.spent :=
                congrArg (fun k : Nat => k + s.spent) (Nat.sub_add_cancel hp)
      · simp [run, h, hp]

theorem spent_monotone (quote : State → Option (QuotedStep State)) (n : Nat)
    (s : Account State) : s.spent ≤ (run quote n s).spent := by
  induction n generalizing s with
  | zero => exact Nat.le_refl _
  | succ n ih =>
    cases h : quote s.state with
    | none => simp [run, h]
    | some q =>
      by_cases hp : q.fee ≤ s.remaining
      · let paid : Account State :=
          ⟨q.next (), s.remaining - q.fee, s.spent + q.fee⟩
        have hstep : run quote (n + 1) s = run quote n paid := by
          change run quote (n + 1) s =
            run quote n ⟨q.next (), s.remaining - q.fee, s.spent + q.fee⟩
          simp [run, h, hp]
        rw [hstep]
        have hpaid : s.spent ≤ paid.spent := by
          change s.spent ≤ s.spent + q.fee
          exact Nat.le_add_right s.spent q.fee
        exact Nat.le_trans hpaid (ih paid)
      · simp [run, h, hp]

theorem budget_bound (quote : State → Option (QuotedStep State)) (n : Nat)
    (s : Account State) : (run quote n s).spent ≤ s.spent + s.remaining := by
  have h := accounting quote n s
  omega

/-- A paid prefix preserves any inductive invariant. -/
theorem invariant (quote : State → Option (QuotedStep State)) (P : State → Prop)
    (closed : ∀ s q, P s → quote s = some q → P (q.next ()))
    (n : Nat) (s : Account State) (hs : P s.state) : P (run quote n s).state := by
  induction n generalizing s with
  | zero => exact hs
  | succ n ih =>
    cases h : quote s.state with
    | none => simpa [run, h] using hs
    | some q =>
      by_cases hp : q.fee ≤ s.remaining
      · simp [run, h, hp]
        exact ih _ (closed s.state q hs h)
      · simpa [run, h, hp] using hs

variable {sw sp sa tw tp ta : Nat}
variable (S : IndexedTask sw sp sa) (T : IndexedTask tw tp ta)

structure Cursor where
  remainingPorts : List (Fin sp → Fin tp)
  activePort : Option ((Fin sp → Fin tp) × List (Fin (sa+1) → Fin (ta+1)))
  certificates : List (Morphism S T)

def initial : Cursor S T := ⟨maps tp sp, none, []⟩

structure Tariff where
  port : Nat
  action : Nat
  portPositive : 0 < port
  actionPositive : 0 < action

/-- No action list is generated for a rejected port. No certificate is computed
before its quoted transition is paid. Enumeration of raw port maps is upfront. -/
def quote (fees : Tariff) (s : Cursor S T) : Option (QuotedStep (Cursor S T)) :=
  match s.activePort with
  | some (p, a :: rest) => some ⟨fees.action, fees.actionPositive, fun _ =>
      let found := match certifyPair S T p a with
        | none => s.certificates
        | some m => s.certificates ++ [m]
      { s with activePort := if rest.isEmpty then none else some (p, rest),
               certificates := found }⟩
  | _ => match s.remainingPorts with
    | [] => none
    | p :: rest => some ⟨fees.port, fees.portPositive, fun _ =>
        { s with remainingPorts := rest,
                 activePort := if S.depth ≤ T.depth ∧ portOK S T p = true ∧ readCover S T p = true
                   then some (p, maps (ta+1) (sa+1)) else none }⟩

/-- Specification only: never called by the paid runner. -/
def pending (s : Cursor S T) : List (Morphism S T) :=
  let active := match s.activePort with
    | none => []
    | some (p, acts) => collectSome (acts.map (certifyPair S T p))
  active ++ (s.remainingPorts.flatMap fun p =>
    if S.depth ≤ T.depth ∧ portOK S T p = true ∧ readCover S T p = true
    then discoverForPort S T p else [])

def PartitionInvariant (s : Cursor S T) : Prop :=
  s.certificates ++ pending S T s = pending S T (initial S T)

/-- Early optimality is relative to the canonical representatives and score.
The caller must supply the partition and a genuine bound on the pending tail. -/
theorem early_optimal (s : Cursor S T) (score : Morphism S T → Nat)
    (best : Morphism S T) (L : Nat)
    (hb : best ∈ s.certificates)
    (hseen : ∀ m ∈ s.certificates, score best ≤ score m)
    (htail : ∀ m ∈ pending S T s, L ≤ score m)
    (hle : score best ≤ L) (hinv : PartitionInvariant S T s) :
    best ∈ pending S T (initial S T) ∧
    ∀ m ∈ pending S T (initial S T), score best ≤ score m := by
  unfold PartitionInvariant at hinv
  rw [← hinv]
  constructor
  · exact List.mem_append.mpr (Or.inl hb)
  · intro m hm
    rcases List.mem_append.mp hm with h | h
    · exact hseen m h
    · exact Nat.le_trans hle (htail m h)

/-! ### T22.9 Completion: generic run composition, measure, saturation, partition & verdicts -/

theorem run_stuck (quote : State → Option (QuotedStep State)) (n : Nat) (s : Account State)
    (h : match quote s.state with | none => True | some q => ¬ q.fee ≤ s.remaining) :
    run quote n s = s := by
  cases n with
  | zero => rfl
  | succ n =>
    cases hq : quote s.state with
    | none => simp [run, hq]
    | some q =>
      have hf : ¬ q.fee ≤ s.remaining := by simpa [hq] using h
      simp [run, hq, hf]

theorem run_add (quote : State → Option (QuotedStep State)) (n m : Nat) (s : Account State) :
    run quote (n + m) s = run quote m (run quote n s) := by
  induction n generalizing s with
  | zero => simp [run]
  | succ n ih =>
    rw [Nat.succ_add]
    cases hq : quote s.state with
    | none =>
      simp only [run, hq]
      exact (run_stuck quote m s (by simp [hq])).symm
    | some q =>
      by_cases hp : q.fee ≤ s.remaining
      · simp only [run, hq, hp, ↓reduceIte]
        exact ih ⟨q.next (), s.remaining - q.fee, s.spent + q.fee⟩
      · simp only [run, hq, hp, ↓reduceIte]
        exact (run_stuck quote m s (by simp [hq, hp])).symm

theorem run_stuck_of_ge_measure (quote : State → Option (QuotedStep State))
    (μ : State → Nat) (hdec : ∀ s q, quote s = some q → μ (q.next ()) < μ s)
    (n : Nat) (s : Account State) (hμ : μ s.state ≤ n) :
    match quote (run quote n s).state with
    | none => True
    | some q => ¬ q.fee ≤ (run quote n s).remaining := by
  induction n generalizing s with
  | zero =>
    cases hq : quote s.state with
    | none => simp [run, hq]
    | some q =>
      have hlt := hdec s.state q hq
      exact False.elim (Nat.not_lt_zero _ (Nat.lt_of_lt_of_le hlt hμ))
  | succ n ih =>
    cases hq : quote s.state with
    | none => simp [run, hq]
    | some q =>
      by_cases hp : q.fee ≤ s.remaining
      · simp only [run, hq, hp, ↓reduceIte]
        have hlt := hdec s.state q hq
        exact ih ⟨q.next (), s.remaining - q.fee, s.spent + q.fee⟩
          (Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hlt hμ))
      · simp [run, hq, hp]

theorem run_eq_of_ge_measure (quote : State → Option (QuotedStep State))
    (μ : State → Nat) (hdec : ∀ s q, quote s = some q → μ (q.next ()) < μ s)
    (n m : Nat) (s : Account State) (hn : μ s.state ≤ n) (hm : μ s.state ≤ m) :
    run quote n s = run quote m s := by
  by_cases hle : n ≤ m
  · have he : n + (m - n) = m := by omega
    calc
      run quote n s = run quote (m - n) (run quote n s) :=
        (run_stuck quote (m - n) (run quote n s)
          (run_stuck_of_ge_measure quote μ hdec n s hn)).symm
      _ = run quote (n + (m - n)) s := (run_add quote n (m - n) s).symm
      _ = run quote m s := congrArg (fun k => run quote k s) he
  · have he : m + (n - m) = n := by omega
    calc
      run quote n s = run quote (m + (n - m)) s :=
        congrArg (fun k => run quote k s) he.symm
      _ = run quote (n - m) (run quote m s) := run_add quote m (n - m) s
      _ = run quote m s := run_stuck quote (n - m) (run quote m s)
        (run_stuck_of_ge_measure quote μ hdec m s hm)

theorem run_measure_le (quote : State → Option (QuotedStep State))
    (μ : State → Nat) (hdec : ∀ s q, quote s = some q → μ (q.next ()) < μ s)
    (n : Nat) (s : Account State) :
    μ (run quote n s).state ≤ μ s.state := by
  induction n generalizing s with
  | zero => exact Nat.le_refl _
  | succ n ih =>
    cases hq : quote s.state with
    | none => simp [run, hq]
    | some q =>
      by_cases hp : q.fee ≤ s.remaining
      · let paid : Account State :=
          ⟨q.next (), s.remaining - q.fee, s.spent + q.fee⟩
        have hstep : run quote (n + 1) s = run quote n paid := by
          change run quote (n + 1) s =
            run quote n ⟨q.next (), s.remaining - q.fee, s.spent + q.fee⟩
          simp [run, hq, hp]
        have hpaid : μ paid.state ≤ μ s.state :=
          Nat.le_of_lt (hdec s.state q hq)
        rw [hstep]
        exact Nat.le_trans (ih paid) hpaid
      · simp [run, hq, hp]

theorem run_topUp_split (quote : State → Option (QuotedStep State))
    (μ : State → Nat) (hdec : ∀ s q, quote s = some q → μ (q.next ()) < μ s)
    (n : Nat) (s : Account State) (b : Nat) (hn : μ s.state ≤ n) :
    run quote n (topUp s b) = run quote n (topUp (run quote n s) b) := by
  induction n generalizing s with
  | zero =>
    cases hq : quote s.state with
    | none => rfl
    | some q =>
      have hlt := hdec s.state q hq
      exact False.elim (Nat.not_lt_zero _ (Nat.lt_of_lt_of_le hlt hn))
  | succ n ih =>
    cases hq : quote s.state with
    | none =>
      simp [run, topUp, hq]
    | some q =>
      by_cases hp : q.fee ≤ s.remaining
      · have hp' : q.fee ≤ s.remaining + b := Nat.le_trans hp (Nat.le_add_right _ _)
        let nextS : Account State := ⟨q.next (), s.remaining - q.fee, s.spent + q.fee⟩
        have hsub : (s.remaining + b) - q.fee = (s.remaining - q.fee) + b := by
          omega
        have hstepL : run quote (n + 1) (topUp s b) = run quote n (topUp nextS b) := by
          simp only [run, topUp, hq, hp', ↓reduceIte, hsub, nextS]
        have hstepR : run quote (n + 1) s = run quote n nextS := by
          change run quote (n + 1) s =
            run quote n ⟨q.next (), s.remaining - q.fee, s.spent + q.fee⟩
          simp [run, hq, hp]
        have hμ' : μ nextS.state ≤ n :=
          Nat.le_of_lt_succ (Nat.lt_of_lt_of_le (hdec s.state q hq) hn)
        have hμ'' : μ (topUp (run quote n nextS) b).state ≤ n := by
          change μ (run quote n nextS).state ≤ n
          exact Nat.le_trans (run_measure_le quote μ hdec n nextS) hμ'
        rw [hstepL, hstepR]
        rw [ih nextS hμ']
        exact run_eq_of_ge_measure quote μ hdec n (n + 1) (topUp (run quote n nextS) b)
          hμ'' (Nat.le_succ_of_le hμ'')
      · have hstuck : run quote (n + 1) s = s := by simp [run, hq, hp]
        rw [hstuck]

def saturate (quote : State → Option (QuotedStep State)) (μ : State → Nat)
    (s : Account State) : Account State :=
  run quote (μ s.state) s

theorem saturate_topUp_add (quote : State → Option (QuotedStep State))
    (μ : State → Nat) (hdec : ∀ s q, quote s = some q → μ (q.next ()) < μ s)
    (s : Account State) (b1 b2 : Nat) :
    saturate quote μ (topUp s (b1 + b2)) =
    saturate quote μ (topUp (saturate quote μ (topUp s b1)) b2) := by
  have htop : topUp s (b1 + b2) = topUp (topUp s b1) b2 := by
    simp [topUp, Nat.add_assoc]
  unfold saturate
  rw [htop]
  have h1 := run_topUp_split quote μ hdec (μ (topUp s b1).state) (topUp s b1) b2 (Nat.le_refl _)
  have hμ1 : μ (topUp (run quote (μ (topUp s b1).state) (topUp s b1)) b2).state ≤
      μ (topUp s b1).state := by
    change μ (run quote (μ (topUp s b1).state) (topUp s b1)).state ≤ μ (topUp s b1).state
    exact run_measure_le quote μ hdec _ _
  have h2 := run_eq_of_ge_measure quote μ hdec
    (μ (topUp s b1).state)
    (μ (topUp (run quote (μ (topUp s b1).state) (topUp s b1)) b2).state)
    (topUp (run quote (μ (topUp s b1).state) (topUp s b1)) b2)
    hμ1 (Nat.le_refl _)
  change run quote (μ (topUp s b1).state) (topUp (topUp s b1) b2) = _
  rw [h1, h2]

/-! ### Instantiation on `Cursor S T` -/

def activeCount (s : Cursor S T) : Nat :=
  match s.activePort with
  | none => 0
  | some (_, acts) => acts.length

def measure (s : Cursor S T) : Nat :=
  (1 + (maps (ta + 1) (sa + 1)).length) * s.remainingPorts.length + activeCount S T s

def Exhausted (s : Cursor S T) : Prop :=
  s.remainingPorts = [] ∧ activeCount S T s = 0

theorem measure_lt (fees : Tariff) (s : Cursor S T) (q : QuotedStep (Cursor S T))
    (hq : quote S T fees s = some q) :
    measure S T (q.next ()) < measure S T s := by
  cases ha : s.activePort with
  | none =>
    cases hp : s.remainingPorts with
    | nil => simp [quote, ha, hp] at hq
    | cons p rest =>
      simp [quote, ha, hp] at hq
      rw [← hq]
      by_cases hcond : S.depth ≤ T.depth ∧ portOK S T p = true ∧ readCover S T p = true
      · simp [measure, activeCount, ha, hp, hcond, Nat.mul_succ] <;> omega
      · simp [measure, activeCount, ha, hp, hcond, Nat.mul_succ] <;> omega
  | some pa =>
    rcases pa with ⟨p, acts⟩
    cases acts with
    | nil =>
      cases hp : s.remainingPorts with
      | nil => simp [quote, ha, hp] at hq
      | cons p' rest =>
        simp [quote, ha, hp] at hq
        rw [← hq]
        by_cases hcond : S.depth ≤ T.depth ∧ portOK S T p' = true ∧ readCover S T p' = true
        · simp [measure, activeCount, ha, hp, hcond, Nat.mul_succ] <;> omega
        · simp [measure, activeCount, ha, hp, hcond, Nat.mul_succ] <;> omega
    | cons a rest =>
      simp [quote, ha] at hq
      rw [← hq]
      cases rest <;> simp [measure, activeCount, ha] <;> omega

theorem partition_preserved (fees : Tariff) (s : Cursor S T) (q : QuotedStep (Cursor S T))
    (hq : quote S T fees s = some q) (hinv : PartitionInvariant S T s) :
    PartitionInvariant S T (q.next ()) := by
  unfold PartitionInvariant at hinv ⊢
  rw [← hinv]
  cases ha : s.activePort with
  | none =>
    cases hp : s.remainingPorts with
    | nil => simp [quote, ha, hp] at hq
    | cons p rest =>
      simp [quote, ha, hp] at hq
      rw [← hq]
      by_cases hcond : S.depth ≤ T.depth ∧ portOK S T p = true ∧ readCover S T p = true
      · simp [pending, ha, hp, hcond, discoverForPort]
      · simp [pending, ha, hp, hcond]
  | some pa =>
    rcases pa with ⟨p, acts⟩
    cases acts with
    | nil =>
      cases hp : s.remainingPorts with
      | nil => simp [quote, ha, hp] at hq
      | cons p' rest =>
        simp [quote, ha, hp] at hq
        rw [← hq]
        by_cases hcond : S.depth ≤ T.depth ∧ portOK S T p' = true ∧ readCover S T p' = true
        · simp [pending, ha, hp, hcond, discoverForPort, collectSome]
        · simp [pending, ha, hp, hcond, collectSome]
    | cons a rest =>
      simp [quote, ha] at hq
      rw [← hq]
      cases hc : certifyPair S T p a with
      | none =>
        cases rest with
        | nil => simp [pending, ha, hc, collectSome]
        | cons a' rest' => simp [pending, ha, hc, collectSome]
      | some m =>
        cases rest with
        | nil => simp [pending, ha, hc, collectSome, List.append_assoc]
        | cons a' rest' => simp [pending, ha, hc, collectSome, List.append_assoc]

theorem initial_partition_invariant : PartitionInvariant S T (initial S T) := rfl

private theorem flatMap_filter_eq (ps : List (Fin sp → Fin tp)) :
    (ps.flatMap fun p =>
      if S.depth ≤ T.depth ∧ portOK S T p = true ∧ readCover S T p = true
      then discoverForPort S T p else []) =
    if S.depth ≤ T.depth then
      (ps.filter (fun p => portOK S T p && readCover S T p)).flatMap (discoverForPort S T)
    else [] := by
  induction ps with
  | nil =>
    by_cases hd : S.depth ≤ T.depth <;> simp [hd]
  | cons p rest ih =>
    by_cases hd : S.depth ≤ T.depth
    · simp [hd] at ih
      by_cases hp : portOK S T p = true
      · by_cases hr : readCover S T p = true
        · simp [hd, hp, hr, ih]
        · simp [hd, hp, hr, ih]
      · simp [hd, hp]
        exact ih
    · simp [hd] at ih ⊢

theorem initial_pending_eq_discoverAll :
    pending S T (initial S T) = discoverAll S T := by
  unfold pending initial discoverAll portCandidates
  simp only [List.nil_append]
  exact flatMap_filter_eq S T (maps tp sp)

theorem pending_eq_nil_of_exhausted (s : Cursor S T) (hexh : Exhausted S T s) :
    pending S T s = [] := by
  rcases hexh with ⟨hrem, hact⟩
  cases ha : s.activePort with
  | none => simp [pending, ha, hrem]
  | some pa =>
    rcases pa with ⟨p, acts⟩
    cases acts with
    | nil => simp [pending, ha, hrem, collectSome]
    | cons a rest =>
      simp [activeCount, ha] at hact

theorem exhausted_certificates_eq_discoverAll (s : Cursor S T)
    (hinv : PartitionInvariant S T s) (hexh : Exhausted S T s) :
    s.certificates = discoverAll S T := by
  unfold PartitionInvariant at hinv
  rw [pending_eq_nil_of_exhausted S T s hexh, List.append_nil,
      initial_pending_eq_discoverAll S T] at hinv
  exact hinv

theorem exhausted_complete (s : Cursor S T)
    (hinv : PartitionInvariant S T s) (hexh : Exhausted S T s) (M : Morphism S T) :
    ∃ N ∈ s.certificates, N.portMap = M.portMap ∧ N.actionMap = M.actionMap := by
  rw [exhausted_certificates_eq_discoverAll S T s hinv hexh]
  exact discover_complete S T M

theorem exhausted_empty_impossible (s : Cursor S T)
    (hinv : PartitionInvariant S T s) (hexh : Exhausted S T s)
    (hempty : s.certificates = []) :
    ¬ Nonempty (Morphism S T) := by
  have h := exhausted_certificates_eq_discoverAll S T s hinv hexh
  rw [hempty] at h
  exact (empty_iff_no_morphism S T).mp h.symm

inductive DiscoveryOutcome (S : IndexedTask sw sp sa) (T : IndexedTask tw tp ta) where
  | found (m : Morphism S T)
  | impossible (h : ¬ Nonempty (Morphism S T))
  | inconclusive (s : Cursor S T)

def classify (s : Cursor S T) (hinv : PartitionInvariant S T s) : DiscoveryOutcome S T :=
  match hcert : s.certificates with
  | m :: _ => .found m
  | [] =>
    match hrem : s.remainingPorts with
    | [] =>
      if hact : activeCount S T s = 0 then
        .impossible (exhausted_empty_impossible S T s hinv ⟨hrem, hact⟩ hcert)
      else .inconclusive s
    | _ :: _ => .inconclusive s

theorem cursor_saturate_topUp_add (fees : Tariff) (s : Account (Cursor S T)) (b1 b2 : Nat) :
    saturate (quote S T fees) (measure S T) (topUp s (b1 + b2)) =
    saturate (quote S T fees) (measure S T)
      (topUp (saturate (quote S T fees) (measure S T) (topUp s b1)) b2) :=
  saturate_topUp_add (quote S T fees) (measure S T) (measure_lt S T fees) s b1 b2


/-! ### Completion bridges and budget-only execution
The combinatorial measure is a specification bound. The actual runner below
uses positive fees to bound transitions without enumerating all action maps. -/

def Stuck (qf : State → Option (QuotedStep State)) (s : Account State) : Prop :=
  match qf s.state with
  | none => True
  | some q => ¬ q.fee ≤ s.remaining

/-- Positive tariffs alone give a fuel bound. -/
theorem run_stuck_of_ge_budget (qf : State → Option (QuotedStep State))
    (n : Nat) (s : Account State) (hn : s.remaining ≤ n) :
    Stuck qf (run qf n s) := by
  induction n generalizing s with
  | zero =>
    change Stuck qf s
    unfold Stuck
    cases hq : qf s.state with
    | none => trivial
    | some q =>
      intro hp
      have hpos := q.positive
      omega
  | succ n ih =>
    cases hq : qf s.state with
    | none => simp [run, Stuck, hq]
    | some q =>
      by_cases hp : q.fee ≤ s.remaining
      · let paid : Account State :=
          ⟨q.next (), s.remaining - q.fee, s.spent + q.fee⟩
        have hstep : run qf (n + 1) s = run qf n paid := by
          change run qf (n + 1) s =
            run qf n ⟨q.next (), s.remaining - q.fee, s.spent + q.fee⟩
          simp [run, hq, hp]
        have hb : paid.remaining ≤ n := by
          change s.remaining - q.fee ≤ n
          have hpos := q.positive
          omega
        rw [hstep]
        exact ih paid hb
      · simp [run, Stuck, hq, hp]

/-- Any two stopped prefixes of the same deterministic run agree. -/
theorem run_eq_if_both_stuck (qf : State → Option (QuotedStep State))
    (n m : Nat) (s : Account State)
    (hn : Stuck qf (run qf n s)) (hm : Stuck qf (run qf m s)) :
    run qf n s = run qf m s := by
  by_cases h : n ≤ m
  · have he : n + (m - n) = m := by omega
    calc
      run qf n s = run qf (m - n) (run qf n s) :=
        (run_stuck qf (m - n) (run qf n s) hn).symm
      _ = run qf (n + (m - n)) s := (run_add qf n (m - n) s).symm
      _ = run qf m s := congrArg (fun k => run qf k s) he
  · have he : m + (n - m) = n := by omega
    calc
      run qf n s = run qf (m + (n - m)) s :=
        congrArg (fun k => run qf k s) he.symm
      _ = run qf (n - m) (run qf m s) := run_add qf m (n - m) s
      _ = run qf m s := run_stuck qf (n - m) (run qf m s) hm

def execute (qf : State → Option (QuotedStep State)) (s : Account State) : Account State :=
  run qf s.remaining s

theorem execute_eq_saturate (qf : State → Option (QuotedStep State))
    (mu : State → Nat) (hdec : ∀ s q, qf s = some q → mu (q.next ()) < mu s)
    (s : Account State) : execute qf s = saturate qf mu s := by
  exact run_eq_if_both_stuck qf s.remaining (mu s.state) s
    (run_stuck_of_ge_budget qf s.remaining s (Nat.le_refl _))
    (run_stuck_of_ge_measure qf mu hdec (mu s.state) s (Nat.le_refl _))

theorem execute_topUp_add (fees : Tariff) (s : Account (Cursor S T)) (b1 b2 : Nat) :
    execute (quote S T fees) (topUp s (b1 + b2)) =
      execute (quote S T fees) (topUp (execute (quote S T fees) (topUp s b1)) b2) := by
  simp only [execute_eq_saturate (quote S T fees) (measure S T) (measure_lt S T fees)]
  exact cursor_saturate_topUp_add S T fees s b1 b2

/-- Sufficient funds for every remaining transition imply termination, not merely
inability to pay. `cap` bounds fees on all states of the quoted system. -/
theorem run_exhausts_with_budget (qf : State → Option (QuotedStep State))
    (mu : State → Nat) (hdec : ∀ s q, qf s = some q → mu (q.next ()) < mu s)
    (cap : Nat) (hcap : ∀ s q, qf s = some q → q.fee ≤ cap)
    (n : Nat) (s : Account State) (hn : mu s.state ≤ n)
    (hb : cap * n ≤ s.remaining) : qf (run qf n s).state = none := by
  induction n generalizing s with
  | zero =>
    change qf s.state = none
    cases hq : qf s.state with
    | none => rfl
    | some q =>
      have hd := hdec s.state q hq
      omega
  | succ n ih =>
    cases hq : qf s.state with
    | none => simp [run, hq]
    | some q =>
      have hc := hcap s.state q hq
      have hcost : cap * n + cap ≤ s.remaining := by
        simpa only [Nat.mul_succ] using hb
      have hp : q.fee ≤ s.remaining := by omega
      let paid : Account State :=
        ⟨q.next (), s.remaining - q.fee, s.spent + q.fee⟩
      have hstep : run qf (n + 1) s = run qf n paid := by
        change run qf (n + 1) s =
          run qf n ⟨q.next (), s.remaining - q.fee, s.spent + q.fee⟩
        simp [run, hq, hp]
      have hmu : mu paid.state ≤ n :=
        Nat.le_of_lt_succ (Nat.lt_of_lt_of_le (hdec s.state q hq) hn)
      have hpaid : cap * n ≤ paid.remaining := by
        change cap * n ≤ s.remaining - q.fee
        omega
      rw [hstep]
      exact ih paid hmu hpaid

theorem quote_fee_le (fees : Tariff) (s : Cursor S T) (q : QuotedStep (Cursor S T))
    (hq : quote S T fees s = some q) : q.fee ≤ max fees.port fees.action := by
  cases ha : s.activePort with
  | none =>
    cases hp : s.remainingPorts with
    | nil => simp [quote, ha, hp] at hq
    | cons p rest =>
      simp [quote, ha, hp] at hq
      rw [← hq]
      exact Nat.le_max_left _ _
  | some pa =>
    rcases pa with ⟨p, acts⟩
    cases acts with
    | nil =>
      cases hp : s.remainingPorts with
      | nil => simp [quote, ha, hp] at hq
      | cons p' rest =>
        simp [quote, ha, hp] at hq
        rw [← hq]
        exact Nat.le_max_left _ _
    | cons a rest =>
      simp [quote, ha] at hq
      rw [← hq]
      exact Nat.le_max_right _ _

theorem quote_none_iff_exhausted (fees : Tariff) (s : Cursor S T) :
    quote S T fees s = none ↔ Exhausted S T s := by
  cases ha : s.activePort with
  | none =>
    cases hp : s.remainingPorts <;> simp [quote, Exhausted, activeCount, ha, hp]
  | some pa =>
    rcases pa with ⟨p, acts⟩
    cases acts with
    | nil =>
      cases hp : s.remainingPorts <;> simp [quote, Exhausted, activeCount, ha, hp]
    | cons a rest => simp [quote, Exhausted, activeCount, ha]

theorem execute_partition (fees : Tariff) (s : Account (Cursor S T))
    (hs : PartitionInvariant S T s.state) :
    PartitionInvariant S T (execute (quote S T fees) s).state := by
  exact invariant (quote S T fees) (PartitionInvariant S T)
    (fun u q hu hq => partition_preserved S T fees u q hq hu) s.remaining s hs

theorem quote_certificates_prefix (fees : Tariff) (s : Cursor S T)
    (q : QuotedStep (Cursor S T)) (hq : quote S T fees s = some q) :
    ∃ tail, (q.next ()).certificates = s.certificates ++ tail := by
  cases ha : s.activePort with
  | none =>
    cases hp : s.remainingPorts with
    | nil => simp [quote, ha, hp] at hq
    | cons p rest =>
      simp [quote, ha, hp] at hq
      rw [← hq]
      exact ⟨[], (List.append_nil _).symm⟩
  | some pa =>
    rcases pa with ⟨p, acts⟩
    cases acts with
    | nil =>
      cases hp : s.remainingPorts with
      | nil => simp [quote, ha, hp] at hq
      | cons p' rest =>
        simp [quote, ha, hp] at hq
        rw [← hq]
        exact ⟨[], (List.append_nil _).symm⟩
    | cons a rest =>
      simp [quote, ha] at hq
      rw [← hq]
      cases hc : certifyPair S T p a with
      | none => exact ⟨[], by simp⟩
      | some m => exact ⟨[m], by simp⟩

theorem execute_certificates_prefix (fees : Tariff) (s : Account (Cursor S T)) :
    ∃ tail, (execute (quote S T fees) s).state.certificates = s.state.certificates ++ tail := by
  let P : Cursor S T → Prop := fun u => ∃ tail, u.certificates = s.state.certificates ++ tail
  have hclosed : ∀ u q, P u → quote S T fees u = some q → P (q.next ()) := by
    intro u q hu hq
    obtain ⟨a, ha⟩ := hu
    obtain ⟨b, hb⟩ := quote_certificates_prefix S T fees u q hq
    exact ⟨a ++ b, by rw [hb, ha, List.append_assoc]⟩
  exact invariant (quote S T fees) P hclosed s.remaining s
    ⟨[], (List.append_nil _).symm⟩

theorem execute_exhausted_with_budget (fees : Tariff) (s : Account (Cursor S T))
    (hb : max fees.port fees.action * measure S T s.state ≤ s.remaining) :
    Exhausted S T (execute (quote S T fees) s).state := by
  rw [execute_eq_saturate (quote S T fees) (measure S T) (measure_lt S T fees)]
  apply (quote_none_iff_exhausted S T fees _).mp
  exact run_exhausts_with_budget (quote S T fees) (measure S T) (measure_lt S T fees)
    (max fees.port fees.action) (quote_fee_le S T fees) (measure S T s.state) s
    (Nat.le_refl _) hb

/-- The full search theorem connects actual execution to the verified T22 list. -/
theorem execute_full (fees : Tariff) (s : Account (Cursor S T))
    (hs : PartitionInvariant S T s.state)
    (hb : max fees.port fees.action * measure S T s.state ≤ s.remaining) :
    (execute (quote S T fees) s).state.certificates = discoverAll S T :=
  exhausted_certificates_eq_discoverAll S T _ (execute_partition S T fees s hs)
    (execute_exhausted_with_budget S T fees s hb)

/-- A resumable account retains both funds and the proof needed for classification. -/
structure CertifiedAccount where
  account : Account (Cursor S T)
  partition : PartitionInvariant S T account.state

def start (budget : Nat) : CertifiedAccount S T :=
  ⟨⟨initial S T, budget, 0⟩, initial_partition_invariant S T⟩

def resume (fees : Tariff) (s : CertifiedAccount S T) (extra : Nat) : CertifiedAccount S T :=
  ⟨execute (quote S T fees) (topUp s.account extra),
    execute_partition S T fees (topUp s.account extra) s.partition⟩

/-- Keep the whole certified account on every return, including `inconclusive`. -/
def classifyAccount (s : CertifiedAccount S T) : DiscoveryOutcome S T × CertifiedAccount S T :=
  (classify S T s.account.state s.partition, s)

theorem start_full (fees : Tariff) (budget : Nat)
    (hb : max fees.port fees.action * measure S T (initial S T) ≤ budget) :
    (resume S T fees (start S T budget) 0).account.state.certificates = discoverAll S T := by
  exact execute_full S T fees (topUp (start S T budget).account 0)
    (start S T budget).partition (by simpa [start, topUp] using hb)

#print axioms accounting
#print axioms spent_monotone
#print axioms budget_bound
#print axioms invariant
#print axioms early_optimal
#print axioms run_stuck
#print axioms run_add
#print axioms run_stuck_of_ge_measure
#print axioms run_eq_of_ge_measure
#print axioms run_measure_le
#print axioms run_topUp_split
#print axioms saturate_topUp_add
#print axioms measure_lt
#print axioms partition_preserved
#print axioms initial_partition_invariant
#print axioms initial_pending_eq_discoverAll
#print axioms pending_eq_nil_of_exhausted
#print axioms exhausted_certificates_eq_discoverAll
#print axioms exhausted_complete
#print axioms exhausted_empty_impossible
#print axioms cursor_saturate_topUp_add
#print axioms run_stuck_of_ge_budget
#print axioms run_eq_if_both_stuck
#print axioms execute_eq_saturate
#print axioms execute_topUp_add
#print axioms run_exhausts_with_budget
#print axioms quote_fee_le
#print axioms quote_none_iff_exhausted
#print axioms execute_partition
#print axioms quote_certificates_prefix
#print axioms execute_certificates_prefix
#print axioms execute_exhausted_with_budget
#print axioms execute_full
#print axioms start_full
end CRTT.BudgetedDiscovery
