/-
  epistemic_deformation_reachability_v3_2.lean
  Epistemic Deformation of Reachability (L_H^EDR, v3.2)
  Self-contained Lean 4.36.0 formalization (zero imports, no Mathlib, 0 sorry, 0 native_decide).

  Modules covered (12/12):
    1. CrossCore            : Monotone entailment, maximal-subset reduction & ConsistentIrreducible
    2. SinkGraph            : Native G1 signature (absorbing trap closed under all allowed actions)
    3. LinearProjectionF2   : Native G2 signature over F_2^2 (linearity, kernel vs specific collision)
    4. AuditBackAction      : Native G4 signature (StateChange / NonCommutation / DesignatedDestination)
    5. InterfaceGlue        : Load-bearing cross-domain alignment + two-tier CrossDiscoveryLicense
    6. SatisfactionBridge   : Parameterized translations m |=_Σ α(φ) ↔ β(m) |=_{Σ_i} φ (incl. IsLinear)
    7. JointEntailment      : ∀ k ∈ ℕ, ∀ pol : Policy, ¬ GuaranteedWin glue W pol k (via glue.trapEqDesignated)
    8. Countermodels        : Constructive winning policies for C1 (no G1), C2 (no G2), C4 (no G4)
    9. BooleanIndependence  : All 8/8 Boolean vectors of repaired diagnostic predicates (C1, C'2, C4_order)
   10. AntiInflation        : Counterexample U_P(s1) = s0 proving C1 ∧ C'2 ∧ C4_order ⊬ h_k
   11. SafeBeliefReach      : General iff characterization with passive port `pi` + formal PlanTree ↔ Policy bridge
   12. ProbabilisticVoI     : Discrete Blackwell monotonicity vs strict negative VoI (VoI_EDR = -1/3 < 0)
-/

namespace EpistemicDeformationReachabilityV32

/-! ============================================================================
    MODULE 1: CrossCore — Monotone Entailment & Maximal-Subset Reduction
    ============================================================================ -/

/-- A monotone semantic entailment relation indexed by finite lists of domain IDs. -/
structure MonotoneEntailment (D : Type) where
  entails : List D → Prop
  mono    : ∀ {A B : List D}, (∀ x, x ∈ A → x ∈ B) → entails A → entails B

/-- Remove all occurrences of domain `d` from list `M`. -/
def removeDomain {D : Type} [DecidableEq D] (M : List D) (d : D) : List D :=
  M.filter (fun x => decide (x ≠ d))

/-- `A` is a proper subset of `M` (as finite sets represented by lists). -/
def IsProperSubset {D : Type} (A M : List D) : Prop :=
  (∀ x, x ∈ A → x ∈ M) ∧ ∃ d, d ∈ M ∧ d ∉ A

/-- Full logical irreducibility: `M` entails `h`, and no proper subset `A ⊂ M` entails `h`. -/
def IsIrreducible {D : Type} (E : MonotoneEntailment D) (M : List D) : Prop :=
  E.entails M ∧ ∀ A, IsProperSubset A M → ¬ E.entails A

/-- Maximal proper-subset irreducibility: `M` entails `h`, and no `M \ {d}` entails `h`. -/
def IsMaximalIrreducible {D : Type} [DecidableEq D] (E : MonotoneEntailment D) (M : List D) : Prop :=
  E.entails M ∧ ∀ d, d ∈ M → ¬ E.entails (removeDomain M d)

/-- Consistent logical irreducibility: excludes vacuous *ex falso* minimal inconsistent sets. -/
def IsConsistentIrreducible {D : Type} (E : MonotoneEntailment D)
    (Consistent : List D → Prop) (M : List D) : Prop :=
  Consistent M ∧ IsIrreducible E M

/-- Theorem 1 (CrossCore): Under monotone entailment, logical irreducibility over all
    proper subsets `A ⊂ M` is equivalent to checking only the maximal subsets `M \ {d}`. -/
theorem crossCore_irreducible_iff_maximal {D : Type} [DecidableEq D]
    (E : MonotoneEntailment D) (M : List D) :
    IsIrreducible E M ↔ IsMaximalIrreducible E M := by
  constructor
  · intro hIrr
    refine ⟨hIrr.1, fun d hdM => ?_⟩
    apply hIrr.2 (removeDomain M d)
    refine ⟨fun x hx => (List.mem_filter.mp hx).1, ⟨d, hdM, fun hdIn => ?_⟩⟩
    have hne : d ≠ d := of_decide_eq_true (List.mem_filter.mp hdIn).2
    exact hne rfl
  · intro hMax
    refine ⟨hMax.1, fun A hProp hEntA => ?_⟩
    rcases hProp with ⟨hSub, d, hdM, hdNotA⟩
    have hSubRem : ∀ x, x ∈ A → x ∈ removeDomain M d := by
      intro x hxA
      apply List.mem_filter.mpr
      refine ⟨hSub x hxA, decide_eq_true ?_⟩
      intro hEq
      subst hEq
      exact hdNotA hxA
    exact hMax.2 d hdM (E.mono hSubRem hEntA)


/-! ============================================================================
    MODULE 2: SinkGraph (Native G1 Signature — Absorbing Trap Dynamics)
    ============================================================================ -/

/-- Native G1 structure: finite transition graph with a designated absorbing state `trap`.
    Contains no observation projection and no probe back-action semantics. -/
structure SinkGraph (S Act : Type) where
  step : S → Act → S
  win  : S → Bool
  trap : S

/-- G1 native axiom: `trap` is non-winning and closed under every allowed action. -/
def SinkGraph.IsAbsorbingTrap {S Act : Type} (G : SinkGraph S Act) : Prop :=
  G.win G.trap = false ∧ ∀ a : Act, G.step G.trap a = G.trap

/-- Iterated execution of a sequence of actions on a `SinkGraph`. -/
def SinkGraph.run {S Act : Type} (G : SinkGraph S Act) : S → List Act → S
  | s, []      => s
  | s, a :: as => G.run (G.step s a) as

/-- Theorem 2 (SinkGraph): Starting from an absorbing trap, no finite sequence of
    allowed actions can ever reach a winning state. -/
theorem sinkGraph_trap_never_reaches_win {S Act : Type} (G : SinkGraph S Act)
    (hTrap : G.IsAbsorbingTrap) (acts : List Act) :
    G.win (G.run G.trap acts) = false := by
  induction acts with
  | nil => exact hTrap.1
  | cons a as ih =>
    simp only [SinkGraph.run, hTrap.2 a]
    exact ih


/-! ============================================================================
    MODULE 3: LinearProjectionF2 (Native G2 Signature over F_2^2)
    ============================================================================ -/

/-- Vectors in F_2^2. -/
abbrev Bit2 := Bool × Bool

/-- Vector addition in F_2^2. -/
def xor2 (u v : Bit2) : Bit2 := (xor u.1 v.1, xor u.2 v.2)

/-- Zero vector in F_2^2. -/
def zero2 : Bit2 := (false, false)

/-- Canonical F_2^2 encoding of the 4 states:
    s0 = (0,0), s1 = (0,1), q = (1,0), w = (1,1). -/
def f2_s0 : Bit2 := (false, false)
def f2_s1 : Bit2 := (false, true)
def f2_q  : Bit2 := (true,  false)
def f2_w  : Bit2 := (true,  true)

/-- Native G2 structure: a projection map over F_2^2 together with a target pair `(u0, u1)`. -/
structure LinearProjectionF2 where
  proj : Bit2 → Bool
  u0   : Bit2
  u1   : Bit2

/-- Linearity over F_2^2. -/
def LinearProjectionF2.IsLinear (L : LinearProjectionF2) : Prop :=
  ∀ u v : Bit2, L.proj (xor2 u v) = xor (L.proj u) (L.proj v)

/-- Non-trivial kernel: some non-zero vector maps to 0. -/
def LinearProjectionF2.HasNontrivialKernel (L : LinearProjectionF2) : Prop :=
  ∃ v : Bit2, v ≠ zero2 ∧ L.proj v = false

/-- Specific collision certificate: `u0 ≠ u1` and `u0 ⊕ u1 ∈ ker(proj)` (equivalently `proj u0 = proj u1`). -/
def LinearProjectionF2.PairCollides (L : LinearProjectionF2) : Prop :=
  L.u0 ≠ L.u1 ∧ L.proj (xor2 L.u0 L.u1) = false ∧ L.proj L.u0 = L.proj L.u1

/-- Full G2 native axiom combining F_2^2 linearity with specific pair collision. -/
def LinearProjectionF2.IsLinearCollision (L : LinearProjectionF2) : Prop :=
  L.IsLinear ∧ L.PairCollides

/-- Theorem 3 (Algebraic F_2^2 Lemma): Under linearity, `proj (u0 ⊕ u1) = false ↔ proj u0 = proj u1`. -/
theorem linearProjectionF2_ker_iff_eq (L : LinearProjectionF2) (hLin : L.IsLinear) :
    L.proj (xor2 L.u0 L.u1) = false ↔ L.proj L.u0 = L.proj L.u1 := by
  rw [hLin L.u0 L.u1]
  cases L.proj L.u0 <;> cases L.proj L.u1 <;> decide

/-- First coordinate projection `π_1(x, y) = x`. -/
def projXModel : LinearProjectionF2 where
  proj := fun v => v.1
  u0   := f2_s0
  u1   := f2_s1

/-- Second coordinate projection `π_2(x, y) = y`. -/
def projYModel : LinearProjectionF2 where
  proj := fun v => v.2
  u0   := f2_s0
  u1   := f2_s1

/-- Theorem 4 (LinearProjectionF2): Both `π_1` and `π_2` are linear with non-trivial kernel,
    yet `π_1` collides on `(s0, s1)` whereas `π_2` separates `(s0, s1)`. -/
theorem linearProjectionF2_kernel_vs_specific_collision :
    projXModel.IsLinear ∧ projXModel.HasNontrivialKernel ∧ projXModel.PairCollides ∧
    projYModel.IsLinear ∧ projYModel.HasNontrivialKernel ∧ ¬ projYModel.PairCollides := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro u v; cases u; cases v; rfl
  · exact ⟨f2_s1, by decide, rfl⟩
  · exact ⟨by decide, rfl, rfl⟩
  · intro u v; cases u; cases v; rfl
  · exact ⟨f2_q, by decide, rfl⟩
  · intro hCol
    have hEq : projYModel.proj f2_s0 = projYModel.proj f2_s1 := hCol.2.2
    cases hEq


/-! ============================================================================
    MODULE 4: AuditBackAction (Native G4 Signature — Observer Back-Action)
    ============================================================================ -/

/-- Native G4 structure: control transitions, an active audit probe `(probeState, probeObs)`,
    and a designated destination state `designated` (NOT labeled as a trap inside G4). -/
structure AuditBackAction (S Act O : Type) where
  delta      : S → Act → S
  probeState : S → S
  probeObs   : S → O
  designated : S

/-- Three separated G4 properties (state change, non-commutation, designated entry). -/
def AuditBackAction.HasStateChange {S Act O : Type} (A : AuditBackAction S Act O) : Prop :=
  ∃ s : S, A.probeState s ≠ s

def AuditBackAction.HasNonCommutation {S Act O : Type} (A : AuditBackAction S Act O) : Prop :=
  ∃ (s : S) (a : Act), A.probeState (A.delta s a) ≠ A.delta (A.probeState s) a

def AuditBackAction.HitsDesignated {S Act O : Type} (A : AuditBackAction S Act O) (s : S) : Prop :=
  A.probeState s = A.designated


/-! ============================================================================
    COMMON EDR SIGNATURE Σ = ⟨S, O, Act, ObsAct, Win, π, δ, ω_obs⟩ & POLICIES
    ============================================================================ -/

inductive State4 where
  | s0 : State4
  | s1 : State4
  | w  : State4
  | q  : State4
  deriving DecidableEq, Repr

inductive Act2 where
  | L : Act2
  | R : Act2
  deriving DecidableEq, Repr

/-- Combined allowed action set (control actions + active probe) for G1 trap closure. -/
inductive AllowedAct where
  | ctrl  : Act2 → AllowedAct
  | probe : AllowedAct
  deriving DecidableEq, Repr

inductive Decision where
  | act   : Act2 → Decision
  | probe : Decision
  | stop  : Decision
  deriving DecidableEq, Repr

/-- Bijection between `State4` and `F_2^2`. -/
def encodeBit2 : State4 → Bit2
  | .s0 => f2_s0
  | .s1 => f2_s1
  | .q  => f2_q
  | .w  => f2_w

def decodeBit2 : Bit2 → State4
  | (false, false) => .s0
  | (false, true)  => .s1
  | (true,  false) => .q
  | (true,  true)  => .w

/-- Theorem 5a & 5b: Exact bijection between `State4` and `F_2^2`. -/
theorem decode_encode_bit2 (s : State4) : decodeBit2 (encodeBit2 s) = s := by
  cases s <;> rfl

theorem encode_decode_bit2 (v : Bit2) : encodeBit2 (decodeBit2 v) = v := by
  cases v with
  | mk x y => cases x <;> cases y <;> rfl

/-- Common EDR world model over `State4`, `Act2`, and binary observations `Bool`. -/
structure EDRWorld where
  win        : State4 → Bool
  pi         : State4 → Bool
  delta      : State4 → Act2 → State4
  probeState : State4 → State4
  probeObs   : State4 → Bool

/-- Step function over all allowed actions (control + probe). -/
def EDRWorld.allowedStep (W : EDRWorld) (s : State4) : AllowedAct → State4
  | .ctrl a => W.delta s a
  | .probe  => W.probeState s

/-- History seen by the policy: initial public observation + trace of `(decision, observation)`.
    The hidden state `State4` is NEVER exposed to the policy. -/
abbrev Hist := Bool × List (Decision × Bool)

/-- Deterministic history-dependent policy. -/
abbrev Policy := Hist → Decision

/-- Exact horizon-`k` execution semantics returning `true` iff `Win` is reached within `≤ k` steps. -/
def reachesWin (W : EDRWorld) (pol : Policy) : Nat → State4 → Hist → Bool
  | 0, s, _ => W.win s
  | k + 1, s, h =>
    if W.win s then
      true
    else
      match pol h with
      | .stop => false
      | .act a =>
        let s' := W.delta s a
        reachesWin W pol k s' (h.1, h.2 ++ [(.act a, W.pi s')])
      | .probe =>
        let s' := W.probeState s
        let y  := W.probeObs s
        reachesWin W pol k s' (h.1, h.2 ++ [(.probe, y)])


/-! ============================================================================
    MODULE 5: InterfaceGlue — Load-Bearing Alignment & Two-Tier License
    ============================================================================ -/

/-- Two distinct epistemic statuses: formal composition never auto-promotes to
    independent historical discovery. -/
inductive CrossDiscoveryLicense where
  | FORMAL_CROSS_IRREDUCIBILITY : CrossDiscoveryLicense
  | INDEPENDENT_CROSS_DISCOVERY : CrossDiscoveryLicense
  deriving DecidableEq, Repr

/-- Explicit, load-bearing InterfaceGlue aligning G1's trap, G2's colliding pair,
    and G4's designated destination. Passed directly into reducts and `joint_entailment_all_horizons`. -/
structure InterfaceGlue where
  g1TrapState      : State4
  g4Designated     : State4
  g2First          : State4
  g2Second         : State4
  trapEqDesignated : g4Designated = g1TrapState
  pairDistinct     : g2First ≠ g2Second
  license          : CrossDiscoveryLicense

def edrInterfaceGlue : InterfaceGlue where
  g1TrapState      := .q
  g4Designated     := .q
  g2First          := .s0
  g2Second         := .s1
  trapEqDesignated := rfl
  pairDistinct     := by decide
  license          := .FORMAL_CROSS_IRREDUCIBILITY

/-- Guaranteed winning policy over the aligned pair `{glue.g2First, glue.g2Second}` within `≤ k` steps. -/
def GuaranteedWin (glue : InterfaceGlue) (W : EDRWorld) (pol : Policy) (k : Nat) : Prop :=
  reachesWin W pol k glue.g2First (W.pi glue.g2First, []) = true ∧
  reachesWin W pol k glue.g2Second (W.pi glue.g2Second, []) = true

/-- Target impossibility claim `h_k(glue, W)`. -/
def ClaimH (glue : InterfaceGlue) (W : EDRWorld) (k : Nat) : Prop :=
  ∀ pol : Policy, ¬ GuaranteedWin glue W pol k

/-- Unbounded impossibility claim: `∀ k, h_k(glue, W)`. -/
def ClaimHAll (glue : InterfaceGlue) (W : EDRWorld) : Prop :=
  ∀ k : Nat, ClaimH glue W k


/-! ============================================================================
    MODULE 6: SatisfactionBridge — Parameterized Exact Translations (incl. IsLinear)
    ============================================================================ -/

/-- Generic SatisfactionBridge capturing `m |=_Σ α(φ) ↔ β(m) |=_{Σ_i} φ`. -/
structure SatisfactionBridge (SrcModel TgtModel SrcSent TgtSent : Type) where
  srcSat  : SrcModel → SrcSent → Prop
  tgtSat  : TgtModel → TgtSent → Prop
  alpha   : SrcSent → TgtSent
  beta    : TgtModel → SrcModel
  sat_iff : ∀ (m : TgtModel) (φ : SrcSent), tgtSat m (alpha φ) ↔ srcSat (beta m) φ

/-- Common base theory `Θ_0(glue, W)` fixed across all domain ablations. -/
def Theta0 (glue : InterfaceGlue) (W : EDRWorld) : Prop :=
  W.win glue.g2First = false ∧
  W.win glue.g2Second = false ∧
  W.win .w = true ∧
  W.delta glue.g2First .L = .w ∧
  W.delta glue.g2First .R = glue.g1TrapState ∧
  W.delta glue.g2Second .L = glue.g1TrapState ∧
  W.delta glue.g2Second .R = .w ∧
  W.delta .w .L = .w ∧
  W.delta .w .R = .w ∧
  W.probeObs glue.g2First = false ∧
  W.probeObs glue.g2Second = true

/-- Glue-parameterized model reducts `β_1, β_2, β_4` from `EDRWorld` to the three native signatures. -/
def reductG1 (glue : InterfaceGlue) (W : EDRWorld) : SinkGraph State4 AllowedAct where
  step := W.allowedStep
  win  := W.win
  trap := glue.g1TrapState

def reductG2 (glue : InterfaceGlue) (W : EDRWorld) : LinearProjectionF2 where
  proj := fun v => W.pi (decodeBit2 v)
  u0   := encodeBit2 glue.g2First
  u1   := encodeBit2 glue.g2Second

def reductG4 (glue : InterfaceGlue) (W : EDRWorld) : AuditBackAction State4 Act2 Bool where
  delta      := W.delta
  probeState := W.probeState
  probeObs   := W.probeObs
  designated := glue.g4Designated

/-- Translated G1, G2 (including F_2^2 `IsLinear`), and G4 axioms in the common signature. -/
def Theta1 (glue : InterfaceGlue) (W : EDRWorld) : Prop :=
  W.win glue.g1TrapState = false ∧ ∀ a : AllowedAct, W.allowedStep glue.g1TrapState a = glue.g1TrapState

def Theta2 (glue : InterfaceGlue) (W : EDRWorld) : Prop :=
  (∀ u v : Bit2, W.pi (decodeBit2 (xor2 u v)) = xor (W.pi (decodeBit2 u)) (W.pi (decodeBit2 v))) ∧
  encodeBit2 glue.g2First ≠ encodeBit2 glue.g2Second ∧
  W.pi (decodeBit2 (xor2 (encodeBit2 glue.g2First) (encodeBit2 glue.g2Second))) = false ∧
  W.pi (decodeBit2 (encodeBit2 glue.g2First)) = W.pi (decodeBit2 (encodeBit2 glue.g2Second))

def Theta4 (glue : InterfaceGlue) (W : EDRWorld) : Prop :=
  W.probeState glue.g2Second = glue.g4Designated

inductive G1Sent | trapClosed : G1Sent
inductive G2Sent | linearPairCollides : G2Sent
inductive G4Sent | hitsDesignatedOnSecond : G4Sent
inductive CommonSent | ax1 | ax2 | ax4 : CommonSent

def commonSat (glue : InterfaceGlue) (W : EDRWorld) : CommonSent → Prop
  | .ax1 => Theta1 glue W
  | .ax2 => Theta2 glue W
  | .ax4 => Theta4 glue W

/-- Glue-parameterized SatisfactionBridges for G1, G2 (with `IsLinear`), and G4. -/
def bridgeG1 (glue : InterfaceGlue) :
    SatisfactionBridge (SinkGraph State4 AllowedAct) EDRWorld G1Sent CommonSent where
  srcSat  := fun G _ => G.IsAbsorbingTrap
  tgtSat  := commonSat glue
  alpha   := fun _ => .ax1
  beta    := reductG1 glue
  sat_iff := fun _ φ => by cases φ; exact Iff.rfl

def bridgeG2 (glue : InterfaceGlue) :
    SatisfactionBridge LinearProjectionF2 EDRWorld G2Sent CommonSent where
  srcSat  := fun L _ => L.IsLinearCollision
  tgtSat  := commonSat glue
  alpha   := fun _ => .ax2
  beta    := reductG2 glue
  sat_iff := fun _ φ => by cases φ; exact Iff.rfl

def bridgeG4 (glue : InterfaceGlue) :
    SatisfactionBridge (AuditBackAction State4 Act2 Bool) EDRWorld G4Sent CommonSent where
  srcSat  := fun A _ => A.HitsDesignated glue.g2Second
  tgtSat  := commonSat glue
  alpha   := fun _ => .ax4
  beta    := reductG4 glue
  sat_iff := fun _ φ => by cases φ; exact Iff.rfl

/-- Theorem 6 (SatisfactionBridge): Exact satisfaction preservation for all 3 domains
    parameterized by any `glue : InterfaceGlue` across all `W : EDRWorld`. -/
theorem all_three_satisfaction_bridges_hold (glue : InterfaceGlue) (W : EDRWorld) :
    (commonSat glue W ((bridgeG1 glue).alpha .trapClosed) ↔ (reductG1 glue W).IsAbsorbingTrap) ∧
    (commonSat glue W ((bridgeG2 glue).alpha .linearPairCollides) ↔ (reductG2 glue W).IsLinearCollision) ∧
    (commonSat glue W ((bridgeG4 glue).alpha .hitsDesignatedOnSecond) ↔ (reductG4 glue W).HitsDesignated glue.g2Second) :=
  ⟨(bridgeG1 glue).sat_iff W .trapClosed,
   (bridgeG2 glue).sat_iff W .linearPairCollides,
   (bridgeG4 glue).sat_iff W .hitsDesignatedOnSecond⟩


/-! ============================================================================
    MODULE 7: JointEntailment — ∀ k ∈ ℕ, h_k Over ALL Models (via `glue.trapEqDesignated`)
    ============================================================================ -/

/-- Theorem 7 (Trap Closure): Once in `glue.g1TrapState`, no deterministic history-dependent
    policy can reach `Win` in any number of steps `k`. -/
theorem edr_trap_never_reachesWin (glue : InterfaceGlue) (W : EDRWorld) (h1 : Theta1 glue W) :
    ∀ (k : Nat) (pol : Policy) (h : Hist), reachesWin W pol k glue.g1TrapState h = false := by
  intro k
  induction k with
  | zero =>
    intro _ _
    exact h1.1
  | succ k ih =>
    intro pol h
    have hWinQ : W.win glue.g1TrapState = false := h1.1
    have hL : W.delta glue.g1TrapState .L = glue.g1TrapState := h1.2 (.ctrl .L)
    have hR : W.delta glue.g1TrapState .R = glue.g1TrapState := h1.2 (.ctrl .R)
    have hP : W.probeState glue.g1TrapState = glue.g1TrapState := h1.2 .probe
    simp only [reachesWin, hWinQ, Bool.false_eq_true, ↓reduceIte]
    cases pol h with
    | stop => rfl
    | act a =>
      cases a with
      | L => simp only [hL]; exact ih pol _
      | R => simp only [hR]; exact ih pol _
    | probe =>
      simp only [hP]; exact ih pol _

/-- Theorem 8 (JointEntailment): For ANY `glue : InterfaceGlue`, EVERY model `W` satisfying
    `Θ_0 ∧ Θ_1 ∧ Θ_2 ∧ Θ_4`, EVERY horizon `k ∈ ℕ`, and EVERY deterministic history-dependent
    policy `pol`, guaranteed victory is impossible. Uses `glue.trapEqDesignated` directly. -/
theorem joint_entailment_all_horizons (glue : InterfaceGlue) (W : EDRWorld)
    (h0 : Theta0 glue W) (h1 : Theta1 glue W) (h2 : Theta2 glue W) (h4 : Theta4 glue W) :
    ClaimHAll glue W := by
  intro k pol hWin
  rcases hWin with ⟨hS0, hS1⟩
  cases k with
  | zero =>
    have hf : W.win glue.g2First = false := h0.1
    simp only [reachesWin, hf] at hS0
    cases hS0
  | succ k =>
    have hWinS0 : W.win glue.g2First = false := h0.1
    have hWinS1 : W.win glue.g2Second = false := h0.2.1
    have hPiEqRaw : W.pi (decodeBit2 (encodeBit2 glue.g2First)) =
                    W.pi (decodeBit2 (encodeBit2 glue.g2Second)) := h2.2.2.2
    rw [decode_encode_bit2, decode_encode_bit2] at hPiEqRaw
    have hS0R : W.delta glue.g2First .R = glue.g1TrapState := h0.2.2.2.2.1
    have hS1L : W.delta glue.g2Second .L = glue.g1TrapState := h0.2.2.2.2.2.1
    simp only [reachesWin, hWinS0, Bool.false_eq_true, ↓reduceIte] at hS0
    simp only [reachesWin, hWinS1, Bool.false_eq_true, ↓reduceIte, ← hPiEqRaw] at hS1
    cases hDec : pol (W.pi glue.g2First, []) with
    | stop =>
      rw [hDec] at hS0
      cases hS0
    | act a =>
      rw [hDec] at hS0 hS1
      cases a with
      | L =>
        simp only [hS1L] at hS1
        rw [edr_trap_never_reachesWin glue W h1 k pol _] at hS1
        cases hS1
      | R =>
        simp only [hS0R] at hS0
        rw [edr_trap_never_reachesWin glue W h1 k pol _] at hS0
        cases hS0
    | probe =>
      rw [hDec] at hS1
      have hPS : W.probeState glue.g2Second = glue.g4Designated := h4
      rw [glue.trapEqDesignated] at hPS
      rw [hPS] at hS1
      rw [edr_trap_never_reachesWin glue W h1 k pol _] at hS1
      cases hS1


/-! ============================================================================
    MODULE 8: Countermodels (C1, C2, C4) & Consistent Logical Irreducibility
    ============================================================================ -/

/-- Base joint model `worldAll` (witnessing `Sat(Θ_0 ∪ Θ_1 ∪ Θ_2 ∪ Θ_4)`). -/
def worldAll : EDRWorld where
  win
    | .w => true
    | _  => false
  pi := fun s => projXModel.proj (encodeBit2 s)
  delta
    | .s0, .L => .w
    | .s0, .R => .q
    | .s1, .L => .q
    | .s1, .R => .w
    | .w,  _  => .w
    | .q,  _  => .q
  probeState
    | .s0 => .s0
    | .s1 => .q
    | .w  => .w
    | .q  => .q
  probeObs
    | .s0 => false
    | .s1 => true
    | .w  => true
    | .q  => false

/-- Countermodel `C1` (without G1: `L(q) = w`, trap broken). -/
def worldC1 : EDRWorld :=
  { worldAll with
    delta := fun s a =>
      match s, a with
      | .q, .L => .w
      | _,  _  => worldAll.delta s a }

/-- Countermodel `C2` (without G2: `π` switches from `π_1` to `π_2`, keeping `B_0 = {s0, s1}`). -/
def worldC2 : EDRWorld :=
  { worldAll with pi := fun s => projYModel.proj (encodeBit2 s) }

/-- Countermodel `C4` (without G4: `U_P(s1) = s1`, non-destructive probe). -/
def worldC4 : EDRWorld :=
  { worldAll with
    probeState := fun s =>
      match s with
      | .s1 => .s1
      | _   => worldAll.probeState s }

/-- Constructive winning policies for `C1`, `C2`, and `C4`. -/
def polC1 : Policy := fun _ => .act .L
def polC2 : Policy := fun h => if h.1 then .act .R else .act .L
def polC4 : Policy := fun h =>
  match h.2 with
  | []           => .probe
  | [(_, false)] => .act .L
  | _            => .act .R

private theorem worldAll_pi_linear :
    ∀ u v : Bit2, worldAll.pi (decodeBit2 (xor2 u v)) =
      xor (worldAll.pi (decodeBit2 u)) (worldAll.pi (decodeBit2 v)) := by
  intro u v
  cases u with
  | mk u1 u2 =>
    cases v with
    | mk v1 v2 =>
      cases u1 <;> cases u2 <;> cases v1 <;> cases v2 <;> rfl

/-- Theorem 9 (Joint Satisfiability): `worldAll` satisfies `Θ_0 ∧ Θ_1 ∧ Θ_2 ∧ Θ_4`. -/
theorem sat_joint_model_worldAll :
    Theta0 edrInterfaceGlue worldAll ∧
    Theta1 edrInterfaceGlue worldAll ∧
    Theta2 edrInterfaceGlue worldAll ∧
    Theta4 edrInterfaceGlue worldAll := by
  refine ⟨?_, ?_, ?_, rfl⟩
  · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · refine ⟨rfl, fun a => ?_⟩
    cases a with
    | ctrl c => cases c <;> rfl
    | probe  => rfl
  · exact ⟨worldAll_pi_linear, by decide, rfl, rfl⟩

/-- Theorems 10, 11, 12: Constructive ablation countermodels `C1`, `C2`, `C4`. -/
theorem countermodel_C1_refutes_without_G1 :
    Theta0 edrInterfaceGlue worldC1 ∧
    Theta2 edrInterfaceGlue worldC1 ∧
    Theta4 edrInterfaceGlue worldC1 ∧
    GuaranteedWin edrInterfaceGlue worldC1 polC1 2 := by
  refine ⟨?_, ?_, rfl, ⟨rfl, rfl⟩⟩
  · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · exact ⟨worldAll_pi_linear, by decide, rfl, rfl⟩

theorem countermodel_C2_refutes_without_G2 :
    Theta0 edrInterfaceGlue worldC2 ∧
    Theta1 edrInterfaceGlue worldC2 ∧
    Theta4 edrInterfaceGlue worldC2 ∧
    GuaranteedWin edrInterfaceGlue worldC2 polC2 1 := by
  refine ⟨?_, ?_, rfl, ⟨rfl, rfl⟩⟩
  · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · refine ⟨rfl, fun a => ?_⟩
    cases a with
    | ctrl c => cases c <;> rfl
    | probe  => rfl

theorem countermodel_C4_refutes_without_G4 :
    Theta0 edrInterfaceGlue worldC4 ∧
    Theta1 edrInterfaceGlue worldC4 ∧
    Theta2 edrInterfaceGlue worldC4 ∧
    GuaranteedWin edrInterfaceGlue worldC4 polC4 2 := by
  refine ⟨?_, ?_, ?_, ⟨rfl, rfl⟩⟩
  · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · refine ⟨rfl, fun a => ?_⟩
    cases a with
    | ctrl c => cases c <;> rfl
    | probe  => rfl
  · exact ⟨worldAll_pi_linear, by decide, rfl, rfl⟩

/-- Domain IDs for the `CrossCore` irreducibility instantiation. -/
inductive DomainID where
  | G1 : DomainID
  | G2 : DomainID
  | G4 : DomainID
  deriving DecidableEq, Repr

def domainAxiom (glue : InterfaceGlue) (W : EDRWorld) : DomainID → Prop
  | .G1 => Theta1 glue W
  | .G2 => Theta2 glue W
  | .G4 => Theta4 glue W

def satisfiesSubset (glue : InterfaceGlue) (W : EDRWorld) (S : List DomainID) : Prop :=
  Theta0 glue W ∧ ∀ d, d ∈ S → domainAxiom glue W d

def edrConsistent (S : List DomainID) : Prop :=
  ∃ W : EDRWorld, satisfiesSubset edrInterfaceGlue W S

def edrEntailment : MonotoneEntailment DomainID where
  entails := fun S => ∀ W : EDRWorld, satisfiesSubset edrInterfaceGlue W S → ClaimHAll edrInterfaceGlue W
  mono := by
    intro A B hSub hEntA W hSatB
    apply hEntA W
    exact ⟨hSatB.1, fun d hdA => hSatB.2 d (hSub d hdA)⟩

/-- Theorem 13 (Consistent Full Logical Irreducibility via CrossCore):
    `{G1, G2, G4}` is jointly consistent (`worldAll`), entails `∀ k, h_k`,
    and NO proper subset `A ⊂ {G1, G2, G4}` entails it. -/
theorem edr_full_logical_irreducibility :
    IsConsistentIrreducible edrEntailment edrConsistent [.G1, .G2, .G4] := by
  refine ⟨?_, ?_⟩
  · refine ⟨worldAll, sat_joint_model_worldAll.1, fun d _ => ?_⟩
    cases d with
    | G1 => exact sat_joint_model_worldAll.2.1
    | G2 => exact sat_joint_model_worldAll.2.2.1
    | G4 => exact sat_joint_model_worldAll.2.2.2
  · rw [crossCore_irreducible_iff_maximal]
    refine ⟨?_, ?_⟩
    · intro W hSat
      exact joint_entailment_all_horizons edrInterfaceGlue W hSat.1
        (hSat.2 .G1 (by decide))
        (hSat.2 .G2 (by decide))
        (hSat.2 .G4 (by decide))
    · intro d _ hEntRem
      cases d with
      | G1 =>
        have hC1 := countermodel_C1_refutes_without_G1
        have hSat : satisfiesSubset edrInterfaceGlue worldC1 (removeDomain [.G1, .G2, .G4] .G1) := by
          refine ⟨hC1.1, fun x hx => ?_⟩
          cases x with
          | G1 => exact absurd hx (by decide)
          | G2 => exact hC1.2.1
          | G4 => exact hC1.2.2.1
        exact hEntRem worldC1 hSat 2 polC1 hC1.2.2.2
      | G2 =>
        have hC2 := countermodel_C2_refutes_without_G2
        have hSat : satisfiesSubset edrInterfaceGlue worldC2 (removeDomain [.G1, .G2, .G4] .G2) := by
          refine ⟨hC2.1, fun x hx => ?_⟩
          cases x with
          | G1 => exact hC2.2.1
          | G2 => exact absurd hx (by decide)
          | G4 => exact hC2.2.2.1
        exact hEntRem worldC2 hSat 1 polC2 hC2.2.2.2
      | G4 =>
        have hC4 := countermodel_C4_refutes_without_G4
        have hSat : satisfiesSubset edrInterfaceGlue worldC4 (removeDomain [.G1, .G2, .G4] .G4) := by
          refine ⟨hC4.1, fun x hx => ?_⟩
          cases x with
          | G1 => exact hC4.2.1
          | G2 => exact hC4.2.2.1
          | G4 => exact absurd hx (by decide)
        exact hEntRem worldC4 hSat 2 polC4 hC4.2.2.2


/-! ============================================================================
    MODULE 9: BooleanIndependence — All 8/8 Vectors of Repaired Φ_3'
    ============================================================================ -/

def allStates4 : List State4 := [.s0, .s1, .w, .q]
def allActs2   : List Act2   := [.L, .R]

def predC1_trap (W : EDRWorld) : Bool :=
  allStates4.any (fun s =>
    !W.win s &&
    (W.delta s .L == s) &&
    (W.delta s .R == s) &&
    (W.probeState s == s))

def winActs1 (W : EDRWorld) (s : State4) : List Act2 :=
  allActs2.filter (fun a => W.win (W.delta s a))

def predC2_collision (W : EDRWorld) : Bool :=
  allStates4.any (fun x =>
    allStates4.any (fun y =>
      (x != y) &&
      (W.pi x == W.pi y) &&
      !(winActs1 W x).isEmpty &&
      !(winActs1 W y).isEmpty &&
      (winActs1 W x).all (fun a => !(winActs1 W y).contains a)))

def predC4_noncomm (W : EDRWorld) : Bool :=
  allStates4.any (fun s =>
    allActs2.any (fun a =>
      W.probeState (W.delta s a) != W.delta (W.probeState s) a))

def diagWorld (b1 b2 b4 : Bool) : EDRWorld where
  win := worldAll.win
  pi := if b2 then worldAll.pi else worldC2.pi
  delta := if b1 then worldAll.delta else worldC1.delta
  probeState := if b4 then worldAll.probeState else worldC4.probeState
  probeObs := worldAll.probeObs

def diagSignature (W : EDRWorld) : Bool × Bool × Bool :=
  (predC1_trap W, predC2_collision W, predC4_noncomm W)

/-- Theorem 14 (BooleanIndependence): All 8 Boolean combinations `(b1, b2, b4) ∈ {0,1}^3`
    of `(C1, C'2, C4_order)` are realized on the 4-state signature. -/
theorem phi3_prime_all_8_boolean_vectors_realized (b1 b2 b4 : Bool) :
    diagSignature (diagWorld b1 b2 b4) = (b1, b2, b4) := by
  cases b1 <;> cases b2 <;> cases b4 <;> rfl


/-! ============================================================================
    MODULE 10: AntiInflation — C1 ∧ C'2 ∧ C4_order ⊬ h_k (U_P(s1) = s0)
    ============================================================================ -/

def worldAntiInflation : EDRWorld :=
  { worldAll with
    probeState := fun s =>
      match s with
      | .s1 => .s0
      | _   => worldAll.probeState s }

def polAntiInflation : Policy := fun h =>
  match h.2 with
  | [] => .probe
  | _  => .act .L

/-- Theorem 15 (AntiInflation): Diagnostic triple `(C1, C'2, C4_order)` does NOT entail
    impossibility `h_k` — on `worldAntiInflation`, all three diagnostic predicates hold,
    yet `Probe(P) → Act(L)` wins from both `s0` and `s1` at `k = 2`. -/
theorem anti_inflation_diagnostics_do_not_imply_impossibility :
    predC1_trap worldAntiInflation = true ∧
    predC2_collision worldAntiInflation = true ∧
    predC4_noncomm worldAntiInflation = true ∧
    GuaranteedWin edrInterfaceGlue worldAntiInflation polAntiInflation 2 :=
  ⟨rfl, rfl, rfl, ⟨rfl, rfl⟩⟩


/-! ============================================================================
    MODULE 11: SafeBeliefReach — Passive Port `pi` & Formal `PlanTree ↔ Policy` Bridge
    ============================================================================ -/

/-- Generic finite EDR world WITH passive observation port `pi : S → O`. -/
structure GenEDRWorld (S O Act ObsAct : Type) where
  win        : S → Bool
  pi         : S → O
  delta      : S → Act → S
  probeState : S → ObsAct → S
  probeObs   : S → ObsAct → O

/-- Finite history-dependent decision tree branching on passive observation after `act`
    and on probe outcome after `probe`. -/
inductive PlanTree (Act ObsAct O : Type) where
  | stop  : PlanTree Act ObsAct O
  | act   : Act → (O → PlanTree Act ObsAct O) → PlanTree Act ObsAct O
  | probe : ObsAct → (O → PlanTree Act ObsAct O) → PlanTree Act ObsAct O

def allWin {S O Act ObsAct : Type} (W : GenEDRWorld S O Act ObsAct) (B : List S) : Prop :=
  ∀ s, s ∈ B → W.win s = true

/-- Active (not-yet-won) worlds in belief `B`. -/
def activeStates {S O Act ObsAct : Type} (W : GenEDRWorld S O Act ObsAct) (B : List S) : List S :=
  B.filter (fun s => !W.win s)

/-- Initial passive observation partition of `B` by `W.pi`. -/
def initBranch {S O Act ObsAct : Type} [DecidableEq O]
    (W : GenEDRWorld S O Act ObsAct) (o : O) (B : List S) : List S :=
  B.filter (fun s => decide (W.pi s = o))

/-- Post-action belief branch: advance active states by `a`, then filter by passive observation `y`. -/
def postActBranch {S O Act ObsAct : Type} [DecidableEq O]
    (W : GenEDRWorld S O Act ObsAct) (a : Act) (y : O) (B : List S) : List S :=
  ((activeStates W B).map (fun s => W.delta s a)).filter (fun s' => decide (W.pi s' = y))

/-- Post-probe belief branch: filter active states by probe outcome `y`, then apply `U_p`. -/
def postProbeBranch {S O Act ObsAct : Type} [DecidableEq O]
    (W : GenEDRWorld S O Act ObsAct) (p : ObsAct) (y : O) (B : List S) : List S :=
  ((activeStates W B).filter (fun s => decide (W.probeObs s p = y))).map (fun s => W.probeState s p)

/-- Validity of a decision tree `t` winning from every state in belief `B` within `≤ k` steps. -/
def ValidPlan {S O Act ObsAct : Type} [DecidableEq O]
    (W : GenEDRWorld S O Act ObsAct) : Nat → PlanTree Act ObsAct O → List S → Prop
  | 0, _, B => allWin W B
  | _, .stop, B => allWin W B
  | k + 1, .act a br, B =>
    allWin W B ∨ ∀ y : O, ValidPlan W k (br y) (postActBranch W a y B)
  | k + 1, .probe p br, B =>
    allWin W B ∨ ∀ y : O, ValidPlan W k (br y) (postProbeBranch W p y B)

/-- Recursive belief-space reachability game `SafeBeliefReach(W, k, B)` with passive port `pi`. -/
def SafeBeliefReach {S O Act ObsAct : Type} [DecidableEq O]
    (W : GenEDRWorld S O Act ObsAct) : Nat → List S → Prop
  | 0, B => allWin W B
  | k + 1, B =>
    allWin W B ∨
    (∃ a : Act, ∀ y : O, SafeBeliefReach W k (postActBranch W a y B)) ∨
    (∃ p : ObsAct, ∀ y : O, SafeBeliefReach W k (postProbeBranch W p y B))

/-- Initial-observation-aware belief reachability: every passive partition `initBranch W o B` wins. -/
def SafeBeliefReachInit {S O Act ObsAct : Type} [DecidableEq O]
    (W : GenEDRWorld S O Act ObsAct) (k : Nat) (B : List S) : Prop :=
  ∀ o : O, SafeBeliefReach W k (initBranch W o B)

/-- Theorem 16 (General Characterization): For ANY EDR system `W` (with passive port `pi`),
    horizon `k`, and belief `B`, `SafeBeliefReach W k B ↔ ∃ t, ValidPlan W k t B`. -/
theorem safeBeliefReach_iff_exists_validPlan {S O Act ObsAct : Type} [DecidableEq O]
    (W : GenEDRWorld S O Act ObsAct) :
    ∀ (k : Nat) (B : List S), SafeBeliefReach W k B ↔ ∃ t, ValidPlan W k t B := by
  intro k
  induction k with
  | zero =>
    intro B
    constructor
    · intro h; exact ⟨.stop, h⟩
    · intro ⟨_, h⟩; exact h
  | succ k ih =>
    intro B
    constructor
    · intro h
      rcases h with hWin | ⟨a, hAct⟩ | ⟨p, hPrb⟩
      · exact ⟨.stop, hWin⟩
      · have hEx : ∀ y : O, ∃ t', ValidPlan W k t' (postActBranch W a y B) :=
          fun y => (ih _).mp (hAct y)
        exact ⟨.act a (fun y => Classical.choose (hEx y)),
               Or.inr (fun y => Classical.choose_spec (hEx y))⟩
      · have hEx : ∀ y : O, ∃ t', ValidPlan W k t' (postProbeBranch W p y B) :=
          fun y => (ih _).mp (hPrb y)
        exact ⟨.probe p (fun y => Classical.choose (hEx y)),
               Or.inr (fun y => Classical.choose_spec (hEx y))⟩
    · intro ⟨t, ht⟩
      cases t with
      | stop => exact Or.inl ht
      | act a br =>
        rcases ht with hWin | hSub
        · exact Or.inl hWin
        · exact Or.inr (Or.inl ⟨a, fun y => (ih _).mpr ⟨br y, hSub y⟩⟩)
      | probe p br =>
        rcases ht with hWin | hSub
        · exact Or.inl hWin
        · exact Or.inr (Or.inr ⟨p, fun y => (ih _).mpr ⟨br y, hSub y⟩⟩)

/-- Faithfully embeds `EDRWorld` (including passive port `pi`) into `GenEDRWorld`. -/
def toGenEDR (W : EDRWorld) : GenEDRWorld State4 Bool Act2 Unit where
  win        := W.win
  pi         := W.pi
  delta      := W.delta
  probeState := fun s _ => W.probeState s
  probeObs   := fun s _ => W.probeObs s

/-- Direct state-level execution of a `PlanTree` on `EDRWorld`. -/
def runTree (W : EDRWorld) : Nat → PlanTree Act2 Unit Bool → State4 → Bool
  | 0, _, s => W.win s
  | _, .stop, s => W.win s
  | k + 1, .act a br, s =>
    if W.win s then true
    else
      let s' := W.delta s a
      runTree W k (br (W.pi s')) s'
  | k + 1, .probe _ br, s =>
    if W.win s then true
    else
      runTree W k (br (W.probeObs s)) (W.probeState s)

/-- Lemma 17a: `ValidPlan` on `toGenEDR W` is equivalent to `runTree` winning on every `s ∈ B`. -/
theorem validPlan_iff_forall_runTree (W : EDRWorld) :
    ∀ (k : Nat) (t : PlanTree Act2 Unit Bool) (B : List State4),
      ValidPlan (toGenEDR W) k t B ↔ ∀ s, s ∈ B → runTree W k t s = true := by
  intro k
  induction k with
  | zero =>
    intro t B
    exact Iff.rfl
  | succ k ih =>
    intro t B
    cases t with
    | stop => exact Iff.rfl
    | act a br =>
      constructor
      · intro hV s hs
        rcases hV with hAll | hBr
        · have hw : W.win s = true := hAll s hs
          simp only [runTree, hw, ↓reduceIte]
        · cases hw : W.win s with
          | true => simp only [runTree, hw, ↓reduceIte]
          | false =>
            simp only [runTree, hw, Bool.false_eq_true, ↓reduceIte]
            apply (ih (br (W.pi (W.delta s a))) _).mp (hBr (W.pi (W.delta s a)))
            apply List.mem_filter.mpr
            refine ⟨?_, decide_eq_true rfl⟩
            apply List.mem_map.mpr
            refine ⟨s, ?_, rfl⟩
            apply List.mem_filter.mpr
            exact ⟨hs, by simp [toGenEDR, hw]⟩
      · intro hRun
        right
        intro y
        apply (ih (br y) _).mpr
        intro s' hs'
        have hFilt := List.mem_filter.mp hs'
        have hPi : W.pi s' = y := of_decide_eq_true hFilt.2
        rcases List.mem_map.mp hFilt.1 with ⟨s, hsAct, hEq⟩
        have hAct := List.mem_filter.mp hsAct
        have hNotWin : W.win s = false := by
          cases hw : W.win s with
          | false => rfl
          | true =>
            have h2 := hAct.2
            simp [toGenEDR, hw] at h2
        have hRunS := hRun s hAct.1
        simp only [runTree, hNotWin, Bool.false_eq_true, ↓reduceIte] at hRunS
        subst hEq
        simp only [toGenEDR] at hPi ⊢
        rw [hPi] at hRunS
        exact hRunS
    | probe p br =>
      cases p
      constructor
      · intro hV s hs
        rcases hV with hAll | hBr
        · have hw : W.win s = true := hAll s hs
          simp only [runTree, hw, ↓reduceIte]
        · cases hw : W.win s with
          | true => simp only [runTree, hw, ↓reduceIte]
          | false =>
            simp only [runTree, hw, Bool.false_eq_true, ↓reduceIte]
            apply (ih (br (W.probeObs s)) _).mp (hBr (W.probeObs s))
            apply List.mem_map.mpr
            refine ⟨s, ?_, rfl⟩
            apply List.mem_filter.mpr
            refine ⟨?_, decide_eq_true rfl⟩
            apply List.mem_filter.mpr
            exact ⟨hs, by simp [toGenEDR, hw]⟩
      · intro hRun
        right
        intro y
        apply (ih (br y) _).mpr
        intro s' hs'
        rcases List.mem_map.mp hs' with ⟨s, hsObs, hEq⟩
        have hObs := List.mem_filter.mp hsObs
        have hY : W.probeObs s = y := of_decide_eq_true hObs.2
        have hAct := List.mem_filter.mp hObs.1
        have hNotWin : W.win s = false := by
          cases hw : W.win s with
          | false => rfl
          | true =>
            have h2 := hAct.2
            simp [toGenEDR, hw] at h2
        have hRunS := hRun s hAct.1
        simp only [runTree, hNotWin, Bool.false_eq_true, ↓reduceIte] at hRunS
        subst hEq
        rw [hY] at hRunS
        exact hRunS

/-- Convert any history-dependent `Policy` into a `PlanTree` rooted at history `h`. -/
def policyToTree (pol : Policy) : Nat → Hist → PlanTree Act2 Unit Bool
  | 0, _ => .stop
  | k + 1, h =>
    match pol h with
    | .stop  => .stop
    | .act a => .act a (fun y => policyToTree pol k (h.1, h.2 ++ [(.act a, y)]))
    | .probe => .probe () (fun y => policyToTree pol k (h.1, h.2 ++ [(.probe, y)]))

/-- Lemma 17b: Executing `policyToTree pol k h` matches `reachesWin W pol k s h` identically. -/
theorem runTree_policyToTree (W : EDRWorld) (pol : Policy) :
    ∀ (k : Nat) (s : State4) (h : Hist),
      runTree W k (policyToTree pol k h) s = reachesWin W pol k s h := by
  intro k
  induction k with
  | zero => intro _ _; rfl
  | succ k ih =>
    intro s h
    simp only [policyToTree, reachesWin]
    cases hDec : pol h with
    | stop =>
      cases hw : W.win s <;> simp [runTree, hw]
    | act a =>
      cases hw : W.win s with
      | true => simp [runTree, hw]
      | false =>
        simp only [runTree, hw, Bool.false_eq_true, ↓reduceIte]
        exact ih (W.delta s a) (h.1, h.2 ++ [(Decision.act a, W.pi (W.delta s a))])
    | probe =>
      cases hw : W.win s with
      | true => simp [runTree, hw]
      | false =>
        simp only [runTree, hw, Bool.false_eq_true, ↓reduceIte]
        exact ih (W.probeState s) (h.1, h.2 ++ [(Decision.probe, W.probeObs s)])

/-- Evaluate a `PlanTree` along a history suffix to recover a `Decision`. -/
def evalTreeHist : PlanTree Act2 Unit Bool → List (Decision × Bool) → Decision
  | .stop, _ => .stop
  | .act a _, [] => .act a
  | .act _ br, (_, y) :: rest => evalTreeHist (br y) rest
  | .probe _ _, [] => .probe
  | .probe _ br, (_, y) :: rest => evalTreeHist (br y) rest

/-- Convert a passive-observation-indexed family of `PlanTree`s into a `Policy`. -/
def treesToPolicy (trees : Bool → PlanTree Act2 Unit Bool) : Policy :=
  fun h => evalTreeHist (trees h.1) h.2

/-- Lemma 17c: Executing a `Policy` that agrees with `evalTreeHist t` on suffixes matches `runTree`. -/
theorem reachesWin_eq_runTree_of_agrees (W : EDRWorld) (pol : Policy) (o : Bool) :
    ∀ (k : Nat) (t : PlanTree Act2 Unit Bool) (s : State4) (pref : List (Decision × Bool)),
      (∀ suf, pol (o, pref ++ suf) = evalTreeHist t suf) →
      reachesWin W pol k s (o, pref) = runTree W k t s := by
  intro k
  induction k with
  | zero => intro _ _ _ _; rfl
  | succ k ih =>
    intro t s pref hAg
    cases t with
    | stop =>
      have h0 : pol (o, pref) = .stop := by
        have := hAg []
        simp only [List.append_nil, evalTreeHist] at this
        exact this
      cases hw : W.win s <;> simp [reachesWin, runTree, hw, h0]
    | act a br =>
      have h0 : pol (o, pref) = .act a := by
        have := hAg []
        simp only [List.append_nil, evalTreeHist] at this
        exact this
      cases hw : W.win s with
      | true => simp [reachesWin, runTree, hw]
      | false =>
        simp only [reachesWin, runTree, hw, Bool.false_eq_true, ↓reduceIte, h0]
        apply ih (br (W.pi (W.delta s a))) (W.delta s a) (pref ++ [(Decision.act a, W.pi (W.delta s a))])
        intro suf
        rw [List.append_assoc]
        exact hAg ((.act a, W.pi (W.delta s a)) :: suf)
    | probe p br =>
      cases p
      have h0 : pol (o, pref) = .probe := by
        have := hAg []
        simp only [List.append_nil, evalTreeHist] at this
        exact this
      cases hw : W.win s with
      | true => simp [reachesWin, runTree, hw]
      | false =>
        simp only [reachesWin, runTree, hw, Bool.false_eq_true, ↓reduceIte, h0]
        apply ih (br (W.probeObs s)) (W.probeState s) (pref ++ [(Decision.probe, W.probeObs s)])
        intro suf
        rw [List.append_assoc]
        exact hAg ((.probe, W.probeObs s) :: suf)

/-- Theorem 18 (Formal `PlanTree ↔ Policy` Bridge):
    `SafeBeliefReachInit (toGenEDR W) k [.s0, .s1]` holds IF AND ONLY IF there exists
    a deterministic history-dependent `pol : Policy` satisfying `GuaranteedWin edrInterfaceGlue W pol k`. -/
theorem safeBeliefReachInit_iff_exists_policy (W : EDRWorld) (k : Nat) :
    SafeBeliefReachInit (toGenEDR W) k [.s0, .s1] ↔
    ∃ pol : Policy, GuaranteedWin edrInterfaceGlue W pol k := by
  constructor
  · intro hInit
    have hEx : ∀ o : Bool, ∃ t, ValidPlan (toGenEDR W) k t (initBranch (toGenEDR W) o [.s0, .s1]) :=
      fun o => (safeBeliefReach_iff_exists_validPlan (toGenEDR W) k _).mp (hInit o)
    let trees : Bool → PlanTree Act2 Unit Bool := fun o => Classical.choose (hEx o)
    refine ⟨treesToPolicy trees, ?_, ?_⟩
    · have hSpec := Classical.choose_spec (hEx (W.pi .s0))
      have hRun := (validPlan_iff_forall_runTree W k (trees (W.pi .s0)) _).mp hSpec .s0
        (List.mem_filter.mpr ⟨by decide, decide_eq_true rfl⟩)
      simp only [edrInterfaceGlue]
      rw [reachesWin_eq_runTree_of_agrees W (treesToPolicy trees) (W.pi .s0) k (trees (W.pi .s0)) .s0 []
          (fun _ => rfl)]
      exact hRun
    · have hSpec := Classical.choose_spec (hEx (W.pi .s1))
      have hRun := (validPlan_iff_forall_runTree W k (trees (W.pi .s1)) _).mp hSpec .s1
        (List.mem_filter.mpr ⟨by decide, decide_eq_true rfl⟩)
      simp only [edrInterfaceGlue]
      rw [reachesWin_eq_runTree_of_agrees W (treesToPolicy trees) (W.pi .s1) k (trees (W.pi .s1)) .s1 []
          (fun _ => rfl)]
      exact hRun
  · intro ⟨pol, hS0, hS1⟩ o
    apply (safeBeliefReach_iff_exists_validPlan (toGenEDR W) k _).mpr
    refine ⟨policyToTree pol k (o, []), ?_⟩
    apply (validPlan_iff_forall_runTree W k _ _).mpr
    intro s hs
    have hF := List.mem_filter.mp hs
    have hPi : W.pi s = o := of_decide_eq_true hF.2
    rw [runTree_policyToTree W pol k s (o, []), ← hPi]
    cases hF.1 with
    | head => exact hS0
    | tail _ h2 =>
      cases h2 with
      | head => exact hS1
      | tail _ h3 => cases h3

/-- Theorem 19 (Full Separation via `SafeBeliefReachInit`, including `worldC2`!):
    `worldAll` fails `SafeBeliefReachInit` at every horizon `k`, whereas `worldC1`,
    `worldC2` (now faithfully preserved via `pi`!), `worldC4`, and `worldAntiInflation`
    all satisfy `SafeBeliefReachInit`. -/
theorem safeBeliefReachInit_separates_all_models :
    (∀ k : Nat, ¬ SafeBeliefReachInit (toGenEDR worldAll) k [.s0, .s1]) ∧
    SafeBeliefReachInit (toGenEDR worldC1) 2 [.s0, .s1] ∧
    SafeBeliefReachInit (toGenEDR worldC2) 1 [.s0, .s1] ∧
    SafeBeliefReachInit (toGenEDR worldC4) 2 [.s0, .s1] ∧
    SafeBeliefReachInit (toGenEDR worldAntiInflation) 2 [.s0, .s1] := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro k hInit
    obtain ⟨pol, hWin⟩ := (safeBeliefReachInit_iff_exists_policy worldAll k).mp hInit
    exact joint_entailment_all_horizons edrInterfaceGlue worldAll
      sat_joint_model_worldAll.1 sat_joint_model_worldAll.2.1
      sat_joint_model_worldAll.2.2.1 sat_joint_model_worldAll.2.2.2 k pol hWin
  · exact (safeBeliefReachInit_iff_exists_policy worldC1 2).mpr
      ⟨polC1, countermodel_C1_refutes_without_G1.2.2.2⟩
  · exact (safeBeliefReachInit_iff_exists_policy worldC2 1).mpr
      ⟨polC2, countermodel_C2_refutes_without_G2.2.2.2⟩
  · exact (safeBeliefReachInit_iff_exists_policy worldC4 2).mpr
      ⟨polC4, countermodel_C4_refutes_without_G4.2.2.2⟩
  · exact (safeBeliefReachInit_iff_exists_policy worldAntiInflation 2).mpr
      ⟨polAntiInflation, anti_inflation_diagnostics_do_not_imply_impossibility.2.2.2⟩


/-! ============================================================================
    MODULE 12: Probabilistic Value of Information (Blackwell vs EDR)
    ============================================================================ -/

def actWinMass {S Act : Type} (win : S → Bool) (delta : S → Act → S)
    (μ : S → Nat) (a : Act) : List S → Nat
  | []      => 0
  | s :: ss => (if win (delta s a) then μ s else 0) + actWinMass win delta μ a ss

def bestBlindMass {S : Type} (win : S → Bool) (delta : S → Act2 → S)
    (μ : S → Nat) (B : List S) : Nat :=
  max (actWinMass win delta μ .L B) (actWinMass win delta μ .R B)

theorem actWinMass_filter_partition {S Act : Type} (win : S → Bool) (delta : S → Act → S)
    (μ : S → Nat) (a : Act) (p : S → Bool) :
    ∀ B : List S,
      actWinMass win delta μ a (B.filter p) +
      actWinMass win delta μ a (B.filter (fun s => !p s)) =
      actWinMass win delta μ a B := by
  intro B
  induction B with
  | nil => rfl
  | cons s ss ih =>
    cases hps : p s with
    | false =>
      simp only [List.filter_cons, hps, Bool.not_false, Bool.false_eq_true, ↓reduceIte, actWinMass]
      omega
    | true =>
      simp only [List.filter_cons, hps, Bool.not_true, Bool.false_eq_true, ↓reduceIte, actWinMass]
      omega

/-- Theorem 20 (Discrete Blackwell Monotonicity for 1-Step Binary Passive Probes). -/
theorem passive_probe_voi_nonneg {S : Type} (win : S → Bool) (delta : S → Act2 → S)
    (μ : S → Nat) (p : S → Bool) (B : List S) :
    bestBlindMass win delta μ B ≤
      bestBlindMass win delta μ (B.filter p) +
      bestBlindMass win delta μ (B.filter (fun s => !p s)) := by
  have hL := actWinMass_filter_partition win delta μ .L p B
  have hR := actWinMass_filter_partition win delta μ .R p B
  simp only [bestBlindMass]
  omega

inductive State5 where
  | s0 : State5
  | s1 : State5
  | s2 : State5
  | w  : State5
  | q  : State5
  deriving DecidableEq, Repr

inductive Obs3 where
  | o0 : Obs3
  | o1 : Obs3
  | o2 : Obs3
  deriving DecidableEq, Repr

def voiWin : State5 → Bool
  | .w => true
  | _  => false

def voiDelta : State5 → Act2 → State5
  | .s0, .L => .w
  | .s1, .L => .w
  | .s2, .L => .q
  | .s0, .R => .q
  | .s1, .R => .q
  | .s2, .R => .w
  | .w,  _  => .w
  | .q,  _  => .q

def voiProbeState : State5 → State5
  | .s0 => .s0
  | .s1 => .q
  | .s2 => .q
  | .w  => .w
  | .q  => .q

def voiProbeObs : State5 → Obs3
  | .s0 => .o0
  | .s1 => .o1
  | .s2 => .o2
  | .w  => .o0
  | .q  => .o2

def voiWorld3 : GenEDRWorld State5 Obs3 Act2 Unit where
  win        := voiWin
  pi         := fun _ => .o0
  delta      := voiDelta
  probeState := fun s _ => voiProbeState s
  probeObs   := fun s _ => voiProbeObs s

def voiUniformPrior : State5 → Nat := fun _ => 1
def voiInitBelief   : List State5 := [.s0, .s1, .s2]

theorem voiWorld3_trap_never_wins :
    ∀ (k : Nat) (B : List State5), State5.q ∈ B → ¬ SafeBeliefReach voiWorld3 k B := by
  intro k
  induction k with
  | zero =>
    intro B hq hWin
    have ht : voiWin .q = true := hWin .q hq
    cases ht
  | succ k ih =>
    intro B hq hReach
    rcases hReach with hWin | ⟨a, hAct⟩ | ⟨p, hPrb⟩
    · have ht : voiWin .q = true := hWin .q hq
      cases ht
    · have hqAct : State5.q ∈ activeStates voiWorld3 B :=
        List.mem_filter.mpr ⟨hq, rfl⟩
      have hqBr : State5.q ∈ postActBranch voiWorld3 a .o0 B := by
        apply List.mem_filter.mpr
        refine ⟨?_, decide_eq_true rfl⟩
        apply List.mem_map.mpr
        refine ⟨.q, hqAct, ?_⟩
        cases a <;> rfl
      exact ih _ hqBr (hAct .o0)
    · have hqAct : State5.q ∈ activeStates voiWorld3 B :=
        List.mem_filter.mpr ⟨hq, rfl⟩
      have hqBr : State5.q ∈ postProbeBranch voiWorld3 p .o2 B := by
        apply List.mem_map.mpr
        refine ⟨.q, List.mem_filter.mpr ⟨hqAct, decide_eq_true rfl⟩, rfl⟩
      exact ih _ hqBr (hPrb .o2)

/-- Theorem 21 (Strict Negative VoI under Epistemic Deformation): `VoI_EDR = 1/3 - 2/3 = -1/3 < 0`. -/
theorem deforming_probe_strict_negative_voi :
    (voiProbeObs .s0 ≠ voiProbeObs .s1 ∧
     voiProbeObs .s0 ≠ voiProbeObs .s2 ∧
     voiProbeObs .s1 ≠ voiProbeObs .s2) ∧
    bestBlindMass voiWin voiDelta voiUniformPrior voiInitBelief = 2 ∧
    SafeBeliefReach voiWorld3 1 (postProbeBranch voiWorld3 () .o0 voiInitBelief) ∧
    (∀ k : Nat, ¬ SafeBeliefReach voiWorld3 k (postProbeBranch voiWorld3 () .o1 voiInitBelief)) ∧
    (∀ k : Nat, ¬ SafeBeliefReach voiWorld3 k (postProbeBranch voiWorld3 () .o2 voiInitBelief)) ∧
    (1 < bestBlindMass voiWin voiDelta voiUniformPrior voiInitBelief) := by
  refine ⟨⟨by decide, by decide, by decide⟩, rfl, ?_, ?_, ?_, by decide⟩
  · refine Or.inr (Or.inl ⟨.L, fun y => ?_⟩)
    cases y with
    | o0 =>
      intro s hs
      cases hs with
      | head => rfl
      | tail _ h => cases h
    | o1 => intro s hs; cases hs
    | o2 => intro s hs; cases hs
  · intro k hReach
    exact voiWorld3_trap_never_wins k _ (by decide) hReach
  · intro k hReach
    exact voiWorld3_trap_never_wins k _ (by decide) hReach

/-- Theorem 22 (Randomized Blind Mixture Dominance against Post-Probe Trap Ceiling `1/3`). -/
theorem randomized_blind_beats_post_probe_ceiling (pL pR : Nat) (hpL : 0 < pL) :
    1 * (pL + pR) < 2 * pL + 1 * pR := by
  omega

end EpistemicDeformationReachabilityV32

/-! ============================================================================
    AXIOM AUDIT FOR ALL 27 PUBLIC THEOREMS IN `epistemic_deformation_reachability_v3_2.lean`
    ============================================================================ -/
#print axioms EpistemicDeformationReachabilityV32.crossCore_irreducible_iff_maximal
#print axioms EpistemicDeformationReachabilityV32.sinkGraph_trap_never_reaches_win
#print axioms EpistemicDeformationReachabilityV32.linearProjectionF2_ker_iff_eq
#print axioms EpistemicDeformationReachabilityV32.linearProjectionF2_kernel_vs_specific_collision
#print axioms EpistemicDeformationReachabilityV32.decode_encode_bit2
#print axioms EpistemicDeformationReachabilityV32.encode_decode_bit2
#print axioms EpistemicDeformationReachabilityV32.all_three_satisfaction_bridges_hold
#print axioms EpistemicDeformationReachabilityV32.edr_trap_never_reachesWin
#print axioms EpistemicDeformationReachabilityV32.joint_entailment_all_horizons
#print axioms EpistemicDeformationReachabilityV32.sat_joint_model_worldAll
#print axioms EpistemicDeformationReachabilityV32.countermodel_C1_refutes_without_G1
#print axioms EpistemicDeformationReachabilityV32.countermodel_C2_refutes_without_G2
#print axioms EpistemicDeformationReachabilityV32.countermodel_C4_refutes_without_G4
#print axioms EpistemicDeformationReachabilityV32.edr_full_logical_irreducibility
#print axioms EpistemicDeformationReachabilityV32.phi3_prime_all_8_boolean_vectors_realized
#print axioms EpistemicDeformationReachabilityV32.anti_inflation_diagnostics_do_not_imply_impossibility
#print axioms EpistemicDeformationReachabilityV32.safeBeliefReach_iff_exists_validPlan
#print axioms EpistemicDeformationReachabilityV32.validPlan_iff_forall_runTree
#print axioms EpistemicDeformationReachabilityV32.runTree_policyToTree
#print axioms EpistemicDeformationReachabilityV32.reachesWin_eq_runTree_of_agrees
#print axioms EpistemicDeformationReachabilityV32.safeBeliefReachInit_iff_exists_policy
#print axioms EpistemicDeformationReachabilityV32.safeBeliefReachInit_separates_all_models
#print axioms EpistemicDeformationReachabilityV32.actWinMass_filter_partition
#print axioms EpistemicDeformationReachabilityV32.passive_probe_voi_nonneg
#print axioms EpistemicDeformationReachabilityV32.voiWorld3_trap_never_wins
#print axioms EpistemicDeformationReachabilityV32.deforming_probe_strict_negative_voi
#print axioms EpistemicDeformationReachabilityV32.randomized_blind_beats_post_probe_ceiling
