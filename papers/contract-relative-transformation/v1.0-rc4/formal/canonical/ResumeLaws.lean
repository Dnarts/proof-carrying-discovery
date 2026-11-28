import BudgetedDiscovery

/-! Exact top-up composition for every budget-independent deterministic quote.
No well-founded progress measure is needed. This does not prove exhaustion. -/
namespace CRTT.ResumeLaws
open CRTT.BudgetedDiscovery
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

variable {U : Type}

theorem run_eq_of_ge_budget (qf : U → Option (QuotedStep U))
    (n m : Nat) (s : Account U) (hn : s.remaining ≤ n) (hm : s.remaining ≤ m) :
    run qf n s = run qf m s :=
  run_eq_if_both_stuck qf n m s (run_stuck_of_ge_budget qf n s hn)
    (run_stuck_of_ge_budget qf m s hm)

theorem execute_paid (qf : U → Option (QuotedStep U)) (s : Account U)
    (q : QuotedStep U) (hq : qf s.state = some q) (hp : q.fee ≤ s.remaining) :
    execute qf s = execute qf ⟨q.next (), s.remaining - q.fee, s.spent + q.fee⟩ := by
  let paid : Account U := ⟨q.next (), s.remaining - q.fee, s.spent + q.fee⟩
  change execute qf s = execute qf paid
  cases hr : s.remaining with
  | zero =>
    have hpos := q.positive
    -- `omega` closing an equality goal by deriving a contradiction imports
    -- `Classical.choice`; naming the contradiction first keeps it constructive.
    exfalso
    omega
  | succ n =>
    have hstep : run qf (n+1) s = run qf n paid := by
      change run qf (n+1) s = run qf n ⟨q.next (), s.remaining - q.fee, s.spent + q.fee⟩
      simp [run, hq, hp]
    have hle : paid.remaining ≤ n := by
      change s.remaining - q.fee ≤ n
      have hpos := q.positive
      omega
    calc
      execute qf s = run qf (n+1) s := congrArg (fun k => run qf k s) hr
      _ = run qf n paid := hstep
      _ = execute qf paid := run_eq_of_ge_budget qf n paid.remaining paid hle (Nat.le_refl _)

/-- Every affordable prefix may be executed before adding more money. -/
theorem execute_topUp_prefix (qf : U → Option (QuotedStep U)) (n : Nat)
    (s : Account U) (b : Nat) :
    execute qf (topUp s b) = execute qf (topUp (run qf n s) b) := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    cases hq : qf s.state with
    | none => simp [run, hq]
    | some q =>
      by_cases hp : q.fee ≤ s.remaining
      · let paid : Account U := ⟨q.next (), s.remaining - q.fee, s.spent + q.fee⟩
        have hstep : run qf (n+1) s = run qf n paid := by
          change run qf (n+1) s = run qf n ⟨q.next (), s.remaining - q.fee, s.spent + q.fee⟩
          simp [run, hq, hp]
        have hp' : q.fee ≤ (topUp s b).remaining := by
          change q.fee ≤ s.remaining + b
          omega
        have hsub : s.remaining + b - q.fee = s.remaining - q.fee + b := by omega
        have he : (⟨q.next (), (topUp s b).remaining - q.fee,
            (topUp s b).spent + q.fee⟩ : Account U) = topUp paid b := by
          change (⟨q.next (), s.remaining + b - q.fee, s.spent + q.fee⟩ : Account U) =
            ⟨q.next (), s.remaining - q.fee + b, s.spent + q.fee⟩
          rw [hsub]
        calc
          execute qf (topUp s b) = execute qf ⟨q.next (), (topUp s b).remaining - q.fee,
              (topUp s b).spent + q.fee⟩ := execute_paid qf (topUp s b) q hq hp'
          _ = execute qf (topUp paid b) := congrArg (execute qf) he
          _ = execute qf (topUp (run qf n paid) b) := ih paid
          _ = execute qf (topUp (run qf (n+1) s) b) :=
            congrArg (fun a => execute qf (topUp a b)) hstep.symm
      · simp [run, hq, hp]

/-- Stronger than T22.9 saturation composition: no decreasing measure. -/
theorem execute_topUp_add (qf : U → Option (QuotedStep U)) (s : Account U)
    (b1 b2 : Nat) :
    execute qf (topUp s (b1+b2)) =
      execute qf (topUp (execute qf (topUp s b1)) b2) := by
  have ht : topUp s (b1+b2) = topUp (topUp s b1) b2 := by
    simp [topUp, Nat.add_assoc]
  rw [ht]
  exact execute_topUp_prefix qf (topUp s b1).remaining (topUp s b1) b2

/-- A loop that never terminates without an external resource bound. -/
def loopQuote (_ : Nat) : Option (QuotedStep Nat) :=
  some ⟨1, by decide, fun _ => 0⟩

theorem loop_no_decreasing_measure (mu : Nat → Nat) :
    ¬ (∀ s q, loopQuote s = some q → mu (q.next ()) < mu s) := by
  intro h
  let q : QuotedStep Nat := ⟨1, by decide, fun _ => 0⟩
  have hf : loopQuote 0 = some q := rfl
  have hx : mu 0 < mu 0 := h 0 q hf
  exact (Nat.lt_irrefl _) hx

#print axioms run_eq_of_ge_budget
#print axioms execute_paid
#print axioms execute_topUp_prefix
#print axioms execute_topUp_add
#print axioms loop_no_decreasing_measure
end CRTT.ResumeLaws
