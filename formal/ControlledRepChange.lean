/-!
Controlled Representation Change under a Fixed Verifier
=======================================================
Status: KERNEL-CHECKED (Lean 4.36.0, zero `sorry`, zero `native_decide`,
zero external imports, zero custom global `axiom` declarations.)

Formalizes:
- ClosedEnv (Ax1: fixed verifier V; Ax2: fail-closed soundness of Sens_struct;
  Ax4: privilege separation — Sens_res cannot trigger memory escalation).
- T1_no_false_escalation: safety theorem preventing false memory escalation on
  tasks solvable in tier0.
- T2_modeE_dominates_modeA & T2_modeE_strict_separation: stream-level budget
  advantage of early UNSAT(W) termination (Mode E vs Mode A).
- T3_break_even & T3_break_even_savings: exact necessary and sufficient
  condition for adaptive escalation (Mode D) to outperform constant wide search
  (Mode B) on a mixed task stream.
- T4_static_lt_closure: structural separation between static deletion Delete(R)
  and dependency-closure deletion Delete(Closure(R)).

Note on Ax5 / T5:
The phenomenal predicate E(a, t) is intentionally absent from the signature of
this formalization (B_nom = DECLARED_NOT_DERIVED, status UN).
-/

namespace ControlledRepChange

/-! ## Part 1. Core Environment and Safety Theorem (Ax1, Ax2, Ax4 -> T1) -/

/-- Memory expressivity tiers (e.g., tier0 = DFA(S_max), tier1 = 1-DCA / Stack). -/
inductive MemClass where
  | tier0
  | tier1
  deriving DecidableEq, Repr

/-- Output of the structural monitor Sens_struct. -/
inductive StructSignal (Witness : Type) where
  | none
  | stopStruct (w : Witness)
  deriving DecidableEq, Repr

/-- Output of the resource monitor Sens_res. -/
inductive ResSignal where
  | ok
  | stopRes
  deriving DecidableEq, Repr

/-- Actions permitted to the interrupt controller Ctrl. -/
inductive CtrlAction (Witness : Type) where
  | continueSearch
  | changeStrategy
  | haltTimeout
  | haltUnsat (w : Witness)
  | escalateMemory (w : Witness)
  deriving DecidableEq, Repr

/--
Closed formal environment packaging Ax1 (invariant verifier V),
Ax2 (fail-closed soundness of Sens_struct), and Ax4 (privilege separation).
Packaging axioms as structure fields avoids polluting Lean's global axiom set.
-/
structure ClosedEnv (Task Prog Witness : Type) where
  /-- Ax1: fixed verifier predicate V(P, Φ) = PASS. -/
  verifies : Prog → Task → Prop
  /-- Hypothesis class H(M) parameterized by memory tier M. -/
  inClass : MemClass → Prog → Prop
  /-- Fixed refutation verifier V_ref(M, Φ, W) = PASS. -/
  validWitness : MemClass → Task → Witness → Prop
  /-- Ax2: every certified witness W establishes unsolvability in class M. -/
  ax2_sound :
    ∀ (m : MemClass) (task : Task) (w : Witness),
      validWitness m task w → ¬ ∃ p : Prog, inClass m p ∧ verifies p task
  /-- Structural monitor Sens_struct. -/
  sensStruct : MemClass → Task → StructSignal Witness
  /-- Sens_struct emits stopStruct(w) only when w is certified by V_ref. -/
  sensStruct_certified :
    ∀ (m : MemClass) (task : Task) (w : Witness),
      sensStruct m task = StructSignal.stopStruct w → validWitness m task w
  /-- Interrupt controller Ctrl consuming (Sens_struct, Sens_res). -/
  ctrl : StructSignal Witness → ResSignal → CtrlAction Witness
  /-- Ax4 (Privilege separation): escalating memory requires a certified
      structural stop signal; Sens_res alone can never escalate memory. -/
  ax4_privilege :
    ∀ (ss : StructSignal Witness) (rs : ResSignal) (w : Witness),
      ctrl ss rs = CtrlAction.escalateMemory w → ss = StructSignal.stopStruct w

/--
T1 (Safety / No-False-Escalation):
Under Ax1, Ax2, and Ax4, if a task is solvable in tier0 under the fixed
verifier V, then for any resource signal rs (including stopRes / TIMEOUT),
the controller Ctrl never triggers escalateMemory.
-/
theorem T1_no_false_escalation
    {Task Prog Witness : Type}
    (env : ClosedEnv Task Prog Witness)
    (task : Task)
    (hSolvable : ∃ p : Prog, env.inClass MemClass.tier0 p ∧ env.verifies p task)
    (rs : ResSignal)
    (w : Witness) :
    env.ctrl (env.sensStruct MemClass.tier0 task) rs ≠ CtrlAction.escalateMemory w := by
  intro hEsc
  have hStop : env.sensStruct MemClass.tier0 task = StructSignal.stopStruct w :=
    env.ax4_privilege (env.sensStruct MemClass.tier0 task) rs w hEsc
  have hValid : env.validWitness MemClass.tier0 task w :=
    env.sensStruct_certified MemClass.tier0 task w hStop
  have hUnsolvable : ¬ ∃ p : Prog, env.inClass MemClass.tier0 p ∧ env.verifies p task :=
    env.ax2_sound MemClass.tier0 task w hValid
  exact hUnsolvable hSolvable


/-! ## Part 2. Stream Economics: Mode E vs Mode A (T2) -/

/-- Task item in a sequential stream sharing a global budget B. -/
structure StreamTask where
  solvable0 : Bool
  cost0 : Nat
  timeoutCost : Nat
  witnessCost : Nat
  deriving DecidableEq, Repr

/-- Mode A (no structural monitor): burns timeoutCost on unsolvable tasks. -/
def solvedModeA : List StreamTask → Nat → Nat
  | [], _ => 0
  | t :: ts, B =>
    if t.solvable0 then
      if t.cost0 ≤ B then
        1 + solvedModeA ts (B - t.cost0)
      else
        0
    else
      if t.timeoutCost ≤ B then
        solvedModeA ts (B - t.timeoutCost)
      else
        0

/-- Mode E (structural monitor without escalation): pays witnessCost to halt
    early on unsolvable tasks, preserving budget for later tier0 tasks. -/
def solvedModeE : List StreamTask → Nat → Nat
  | [], _ => 0
  | t :: ts, B =>
    if t.solvable0 then
      if t.cost0 ≤ B then
        1 + solvedModeE ts (B - t.cost0)
      else
        0
    else
      if t.witnessCost ≤ B then
        solvedModeE ts (B - t.witnessCost)
      else
        0

/-- Monotonicity of solvedModeE with respect to available budget B. -/
theorem solvedModeE_mono (ts : List StreamTask) :
    ∀ {B1 B2 : Nat}, B1 ≤ B2 → solvedModeE ts B1 ≤ solvedModeE ts B2 := by
  induction ts with
  | nil =>
    intro B1 B2 _
    simp [solvedModeE]
  | cons t ts ih =>
    intro B1 B2 hLe
    simp only [solvedModeE]
    cases hSolv : t.solvable0
    · simp only [Bool.false_eq_true, ite_false]
      by_cases hW1 : t.witnessCost ≤ B1
      · have hW2 : t.witnessCost ≤ B2 := by omega
        simp only [hW1, hW2, ite_true]
        exact ih (by omega)
      · simp only [hW1, ite_false]
        exact Nat.zero_le _
    · simp only [ite_true]
      by_cases hC1 : t.cost0 ≤ B1
      · have hC2 : t.cost0 ≤ B2 := by omega
        simp only [hC1, hC2, ite_true]
        have hRec := ih (B1 := B1 - t.cost0) (B2 := B2 - t.cost0) (by omega)
        omega
      · simp only [hC1, ite_false]
        exact Nat.zero_le _

/--
T2a (Stream Dominance of Mode E over Mode A):
If building the UNSAT(W) certificate on every unsolvable task costs no more
than burning the per-task timeout budget, then Mode E solves at least as many
tasks as Mode A on any mixed stream and any shared budget B.
-/
theorem T2_modeE_dominates_modeA (ts : List StreamTask)
    (hCheaper : ∀ t, t ∈ ts → t.solvable0 = false → t.witnessCost ≤ t.timeoutCost) :
    ∀ B : Nat, solvedModeA ts B ≤ solvedModeE ts B := by
  induction ts with
  | nil =>
    intro B
    simp [solvedModeA, solvedModeE]
  | cons t ts ih =>
    intro B
    have hTail : ∀ u, u ∈ ts → u.solvable0 = false → u.witnessCost ≤ u.timeoutCost :=
      fun u hu => hCheaper u (List.Mem.tail t hu)
    simp only [solvedModeA, solvedModeE]
    cases hSolv : t.solvable0
    · simp only [Bool.false_eq_true, ite_false]
      by_cases hTo : t.timeoutCost ≤ B
      · have hWLeTo : t.witnessCost ≤ t.timeoutCost :=
          hCheaper t (List.Mem.head ts) hSolv
        have hW : t.witnessCost ≤ B := by omega
        simp only [hTo, hW, ite_true]
        have hStep1 : solvedModeA ts (B - t.timeoutCost) ≤ solvedModeE ts (B - t.timeoutCost) :=
          ih hTail (B - t.timeoutCost)
        have hStep2 : solvedModeE ts (B - t.timeoutCost) ≤ solvedModeE ts (B - t.witnessCost) :=
          solvedModeE_mono ts (by omega)
        exact Nat.le_trans hStep1 hStep2
      · simp only [hTo, ite_false]
        exact Nat.zero_le _
    · simp only [ite_true]
      by_cases hC : t.cost0 ≤ B
      · simp only [hC, ite_true]
        have hRec := ih hTail (B - t.cost0)
        omega
      · simp only [hC, ite_false]
        exact Nat.zero_le _

/--
T2b (Strict Separation on a Mixed Stream):
When an unsolvable task t1 precedes a solvable tier0 task t2 and the shared
budget B satisfies t1.witnessCost + t2.cost0 ≤ B < t1.timeoutCost + t2.cost0,
Mode E strictly outperforms Mode A (solving 1 task vs 0).
-/
theorem T2_modeE_strict_separation (t1 t2 : StreamTask) (B : Nat)
    (h1 : t1.solvable0 = false)
    (h2 : t2.solvable0 = true)
    (hLow : t1.witnessCost + t2.cost0 ≤ B)
    (hHigh : B < t1.timeoutCost + t2.cost0) :
    solvedModeA [t1, t2] B < solvedModeE [t1, t2] B := by
  have hW : t1.witnessCost ≤ B := by omega
  have hC2E : t2.cost0 ≤ B - t1.witnessCost := by omega
  have hE : solvedModeE [t1, t2] B = 1 := by
    simp [solvedModeE, h1, h2, hW, hC2E]
  have hA : solvedModeA [t1, t2] B = 0 := by
    by_cases hTo : t1.timeoutCost ≤ B
    · have hNoC2 : ¬ (t2.cost0 ≤ B - t1.timeoutCost) := by omega
      simp [solvedModeA, h1, h2, hTo, hNoC2]
    · simp [solvedModeA, h1, hTo]
  omega


/-! ## Part 3. Break-Even Theorem: Mode D vs Mode B (T3) -/

/-- Task item for comparing Mode B (constant H_full) vs Mode D (diagnostic escalation). -/
structure DTask where
  inTier0 : Bool
  costH0 : Nat
  costHfull : Nat
  diagAndRepairCost : Nat
  deriving DecidableEq, Repr

/-- Total cost of Mode B (constant wide language H_full) plus memory overhead memB. -/
def totalCostB : List DTask → Nat → Nat
  | [], memB => memB
  | t :: ts, memB => t.costHfull + totalCostB ts memB

/-- Total cost of Mode D (H_0 on tier0; diagnostic W + repair R_W + H_full on tier1)
    plus memory overhead memD. -/
def totalCostD : List DTask → Nat → Nat
  | [], memD => memD
  | t :: ts, memD =>
    (if t.inTier0 then t.costH0 else t.diagAndRepairCost + t.costHfull) + totalCostD ts memD

def costB_tier0 : List DTask → Nat
  | [] => 0
  | t :: ts => (if t.inTier0 then t.costHfull else 0) + costB_tier0 ts

def costD_tier0 : List DTask → Nat
  | [] => 0
  | t :: ts => (if t.inTier0 then t.costH0 else 0) + costD_tier0 ts

def diagOverhead : List DTask → Nat
  | [] => 0
  | t :: ts => (if t.inTier0 then 0 else t.diagAndRepairCost) + diagOverhead ts

def costShared_tier1 : List DTask → Nat
  | [] => 0
  | t :: ts => (if t.inTier0 then 0 else t.costHfull) + costShared_tier1 ts

def tier0Savings : List DTask → Nat
  | [] => 0
  | t :: ts => (if t.inTier0 then t.costHfull - t.costH0 else 0) + tier0Savings ts

private theorem totalCostB_decomp (ts : List DTask) (memB : Nat) :
    totalCostB ts memB = costB_tier0 ts + costShared_tier1 ts + memB := by
  induction ts with
  | nil => simp [totalCostB, costB_tier0, costShared_tier1]
  | cons t ts ih =>
    simp only [totalCostB, costB_tier0, costShared_tier1]
    cases t.inTier0 <;> simp <;> omega

private theorem totalCostD_decomp (ts : List DTask) (memD : Nat) :
    totalCostD ts memD = costD_tier0 ts + diagOverhead ts + costShared_tier1 ts + memD := by
  induction ts with
  | nil => simp [totalCostD, costD_tier0, diagOverhead, costShared_tier1]
  | cons t ts ih =>
    simp only [totalCostD, costD_tier0, diagOverhead, costShared_tier1]
    cases t.inTier0 <;> simp <;> omega

private theorem tier0Savings_add (ts : List DTask)
    (hSpec : ∀ t, t ∈ ts → t.inTier0 = true → t.costH0 ≤ t.costHfull) :
    tier0Savings ts + costD_tier0 ts = costB_tier0 ts := by
  induction ts with
  | nil => simp [tier0Savings, costD_tier0, costB_tier0]
  | cons t ts ih =>
    have hTail : ∀ u, u ∈ ts → u.inTier0 = true → u.costH0 ≤ u.costHfull :=
      fun u hu => hSpec u (List.Mem.tail t hu)
    have hRec := ih hTail
    simp only [tier0Savings, costD_tier0, costB_tier0]
    cases hT : t.inTier0
    · simp; omega
    · have hLe : t.costH0 ≤ t.costHfull := hSpec t (List.Mem.head ts) hT
      simp; omega

/--
T3 (Exact Break-Even Theorem, additive form):
Mode D strictly beats Mode B on total stream cost if and only if
narrow-tier cost + diagnostic/repair overhead + D's memory overhead
is strictly less than wide-tier cost on tier0 tasks + B's memory overhead.
-/
theorem T3_break_even (ts : List DTask) (memB memD : Nat) :
    totalCostD ts memD < totalCostB ts memB ↔
    costD_tier0 ts + diagOverhead ts + memD < costB_tier0 ts + memB := by
  rw [totalCostD_decomp, totalCostB_decomp]
  omega

/--
T3 Corollary (Savings vs Overhead Break-Even):
Under specialization (costH0 ≤ costHfull on tier0 tasks) and memB ≤ memD,
Mode D strictly beats Mode B iff total tier0 specialization savings strictly
exceed total diagnostic/repair overhead plus incremental memory cost.
-/
theorem T3_break_even_savings (ts : List DTask) (memB memD : Nat)
    (hSpec : ∀ t, t ∈ ts → t.inTier0 = true → t.costH0 ≤ t.costHfull)
    (hMem : memB ≤ memD) :
    totalCostD ts memD < totalCostB ts memB ↔
    diagOverhead ts + (memD - memB) < tier0Savings ts := by
  rw [T3_break_even]
  have hSav := tier0Savings_add ts hSpec
  omega


/-! ## Part 4. Structural Separation of Static vs Closure Deletion (T4) -/

/-- Recovery cost model for an artifact R with a dependent descendant I2. -/
def recoveryCost (hasR hasI2 : Bool) (cDirect cRecoverFromI2 cRediscover : Nat) : Nat :=
  if hasR then
    cDirect
  else if hasI2 then
    cRecoverFromI2
  else
    cRediscover

/--
T4 (Static Deletion ≠ Closure Deletion):
If descendant I2 remains in memory and permits recovering R at cost
cRecoverFromI2 < cRediscover, then static deletion Delete(R) incurs strictly
less recovery cost than closure deletion Delete(Closure(R)).
-/
theorem T4_static_lt_closure
    (cDirect cRecoverFromI2 cRediscover : Nat)
    (hRec : cRecoverFromI2 < cRediscover) :
    recoveryCost false true cDirect cRecoverFromI2 cRediscover <
    recoveryCost false false cDirect cRecoverFromI2 cRediscover := by
  simp [recoveryCost, hRec]

end ControlledRepChange