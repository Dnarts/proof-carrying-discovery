import ControllerReplacement

/-! T29a: the economic witness only. Extracts the paired-evidence contract
from the pre-admission part of the failed T29 candidate. No session, dependent
verdict, or recursive trace is defined in this gate. The root tasks, tariff
contract, and actual old/new continuation identities remain fixed. -/
namespace CRTT.RelativeEvidence
open CRTT.MorphismDiscovery
open CRTT.ControllerReplacement (Controller Continuation SameContinuation
  remainingBill rebased)
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

/-- Each row bounds the old bill from below and the new bill from above
under the SAME possibility. These are not independent extrema. -/
abbrev Row := Nat × Nat

def relativeOK (fee : Nat) (rows : List Row) : Bool :=
  allB (fun p : Row => decide (fee + p.2 < p.1)) rows

theorem relativeOK_iff (fee : Nat) (rows : List Row) :
    relativeOK fee rows = true ↔ ∀ p ∈ rows, fee + p.2 < p.1 := by
  constructor
  · intro h p hp
    exact of_decide_eq_true ((allB_iff (fun r : Row => decide (fee + r.2 < r.1)) rows).mp h p hp)
  · intro h
    exact (allB_iff (fun r : Row => decide (fee + r.2 < r.1)) rows).mpr
      (fun p hp => decide_eq_true (h p hp))

/-- Subset refinement preserves a passing arithmetic test. A deployable
refinement must separately preserve the actual-pair coverage proof. -/
theorem relativeOK_refine (fee : Nat) (old new : List Row)
    (sub : ∀ p ∈ new, p ∈ old) (h : relativeOK fee old = true) : relativeOK fee new = true :=
  (relativeOK_iff fee new).mpr (fun p hp => (relativeOK_iff fee old).mp h p (sub p hp))

theorem paired_gain (fee old new : Nat) (rows : List Row)
    (actual : ∃ p ∈ rows, p.1 ≤ old ∧ new ≤ p.2)
    (h : relativeOK fee rows = true) : fee + new < old := by
  obtain ⟨p, hp, hl, hu⟩ := actual
  have hg := (relativeOK_iff fee rows).mp h p hp
  omega

/-- This is a proof-indexed refinement contract, not a search for the actual
row. It excludes the vacuous empty-list pass from economic admission. -/
theorem coverage_nonempty (old new : Nat) (rows : List Row)
    (actual : ∃ p ∈ rows, p.1 ≤ old ∧ new ≤ p.2) : rows ≠ [] := by
  intro h
  obtain ⟨p,hp,_,_⟩ := actual
  rw [h] at hp
  cases hp

variable {sw sp sa tw tp ta : Nat}
variable (S : IndexedTask sw sp sa) (T : IndexedTask tw tp ta)

structure Candidate (old : Continuation S T) where
  controller : Controller S T
  sameFees : controller.fees = old.controller.fees
  reserve : Nat
  funded : CRTT.BudgetedPruning.potential S T controller.rules controller.fees
    (CRTT.ControllerReplacement.rebase S T controller.rules old.frontier) ≤ reserve
  migration : Nat

def candidateNext (old : Continuation S T) (c : Candidate S T old) : Continuation S T :=
  rebased S T old c.controller c.reserve c.funded

structure RelativeOffer (old : Continuation S T) where
  candidate : Candidate S T old
  rows : List Row
  actual : ∃ p ∈ rows, p.1 ≤ remainingBill S T old ∧
    remainingBill S T (candidateNext S T old candidate) ≤ p.2
  evidenceLabel : String

def proposed (old : Continuation S T) (o : RelativeOffer S T old) : Continuation S T :=
  candidateNext S T old o.candidate

theorem offer_nonempty (old : Continuation S T) (o : RelativeOffer S T old) : o.rows ≠ [] :=
  coverage_nonempty _ _ o.rows o.actual

/-- Explicit boundary lemma for the later accounting gate. The reserved
amount checked during admission is exactly the installed reserve. -/
theorem proposed_reserve (old : Continuation S T) (o : RelativeOffer S T old) :
    (proposed S T old o).reserve = o.candidate.reserve := rfl

theorem proposed_same (old : Continuation S T) (o : RelativeOffer S T old) :
    SameContinuation S T old.frontier (proposed S T old o).frontier :=
  CRTT.ControllerReplacement.rebase_same S T o.candidate.controller.rules old.frontier

theorem proposed_fees (old : Continuation S T) (o : RelativeOffer S T old) :
    (proposed S T old o).controller.fees = old.controller.fees := o.candidate.sameFees

theorem proposed_bill_le_reserve (old : Continuation S T) (o : RelativeOffer S T old) :
    remainingBill S T (proposed S T old o) ≤ o.candidate.reserve := by
  have h := CRTT.ControllerReplacement.completion_bill_le S T (proposed S T old o)
  rw [proposed_reserve S T old o] at h
  exact h

theorem relative_sound (old : Continuation S T) (o : RelativeOffer S T old) (fee : Nat)
    (h : relativeOK (fee + o.candidate.migration) o.rows = true) :
    fee + o.candidate.migration + remainingBill S T (proposed S T old o) < remainingBill S T old :=
  paired_gain (fee + o.candidate.migration) _ _ o.rows o.actual h

/-- T28's absolute certificate embeds without changing any bound or cost. -/
def fromAbsolute (old : Continuation S T) (o : CRTT.ControllerReplacement.Offer S T old) :
    RelativeOffer S T old where
  candidate := ⟨o.newController,o.sameBaseFees,o.reserve,o.reserveSound,o.migration⟩
  rows := [(o.oldLower,o.newUpper)]
  actual := ⟨(o.oldLower,o.newUpper), List.Mem.head _, o.oldLowerSound, o.newUpperSound⟩
  evidenceLabel := o.evidenceLabel

theorem absolute_same_candidate (old : Continuation S T) (o : CRTT.ControllerReplacement.Offer S T old) :
    proposed S T old (fromAbsolute S T old o) = CRTT.ControllerReplacement.proposed S T old o := rfl

theorem absolute_gate (old : Continuation S T) (o : CRTT.ControllerReplacement.Offer S T old)
    (fee : Nat) : relativeOK (fee + o.migration) (fromAbsolute S T old o).rows = true ↔
      fee + o.migration + o.newUpper < o.oldLower := by
  change relativeOK (fee + o.migration) [(o.oldLower,o.newUpper)] = true ↔ _
  constructor
  · intro h
    exact (relativeOK_iff _ _).mp h _ (List.Mem.head _)
  · intro h
    apply (relativeOK_iff _ _).mpr
    intro p hp
    rcases List.mem_cons.mp hp with he | ht
    · subst p
      exact h
    · cases ht

/-! T27 bridge. A decision certificate bounds a candidate relative to the
reference. A separate strict incumbent margin and a jointly covering actual
hypothesis are still required. -/
variable {H C : Type}

def decisionRows (D : CRTT.DecisionEvidence.Model H C) (belief : List H)
    (incumbent : C) (eps : Nat) : List Row :=
  belief.map (fun h => (D.bill incumbent h, D.reference h + eps))

theorem decision_margin (D : CRTT.DecisionEvidence.Model H C) (belief : List H)
    (incumbent : C) (eps fee : Nat)
    (margin : ∀ h ∈ belief, fee + (D.reference h + eps) < D.bill incumbent h) :
    relativeOK fee (decisionRows D belief incumbent eps) = true := by
  apply (relativeOK_iff _ _).mpr
  intro p hp
  obtain ⟨h, hh, he⟩ := List.mem_map.mp hp
  subst p
  exact margin h hh

def fromDecision (old : Continuation S T) (c : Candidate S T old)
    (D : CRTT.DecisionEvidence.Model H C) (belief : List H) (incumbent : C) (eps : Nat)
    (r : CRTT.DecisionEvidence.DecisionCertificate D belief eps) (label : String)
    (actual : ∃ h ∈ belief, D.bill incumbent h ≤ remainingBill S T old ∧
      remainingBill S T (candidateNext S T old c) ≤ D.bill r.controller h) : RelativeOffer S T old where
  candidate := c
  rows := decisionRows D belief incumbent eps
  actual := by
    obtain ⟨h, hh, hl, hu⟩ := actual
    exact ⟨(D.bill incumbent h,D.reference h+eps), List.mem_map.mpr ⟨h,hh,rfl⟩,
      hl, Nat.le_trans hu (CRTT.DecisionEvidence.certificate_bill D belief eps r h hh)⟩
  evidenceLabel := label

theorem decision_offer_gain (old : Continuation S T) (c : Candidate S T old)
    (D : CRTT.DecisionEvidence.Model H C) (belief : List H) (incumbent : C) (eps : Nat)
    (r : CRTT.DecisionEvidence.DecisionCertificate D belief eps) (label : String)
    (actual : ∃ h ∈ belief, D.bill incumbent h ≤ remainingBill S T old ∧
      remainingBill S T (candidateNext S T old c) ≤ D.bill r.controller h)
    (fee : Nat) (margin : ∀ h ∈ belief,
      fee+c.migration+(D.reference h+eps) < D.bill incumbent h) :
    fee+c.migration+remainingBill S T (candidateNext S T old c) < remainingBill S T old :=
  relative_sound S T old (fromDecision S T old c D belief incumbent eps r label actual) fee
    (decision_margin D belief incumbent eps (fee+c.migration) margin)

namespace Witnesses

/-- Both rows permit the switch, whereas mixing their extrema does not. -/
theorem correlated_gap : relativeOK 1 [(10,8),(100,98)] = true ∧ ¬ (1+98 < (10 : Nat)) := by decide

theorem zero_regret_not_strict_improvement : relativeOK 1 [(10,10)] = false := by decide

/-- A raw empty scan is vacuous; `offer_nonempty` blocks such an offer. -/
theorem empty_scan : relativeOK 1 [] = true := rfl

open CRTT.ControllerReplacement.Witnesses (src dst oldContinuation offer)

/-- Synthetic joint enclosure for T28's concrete depth-obstruction task.
The actual row is (7,1). The second row is conservative extra uncertainty,
not a claim that a second physical execution world exists. -/
def liveOffer : RelativeOffer src dst oldContinuation where
  candidate := (fromAbsolute src dst oldContinuation offer).candidate
  rows := [(7,1),(70,64)]
  actual := ⟨(7,1), List.Mem.head _, offer.oldLowerSound, offer.newUpperSound⟩
  evidenceLabel := "paired enclosure of T28 depth-obstruction witness"

theorem paired_live_gain : 1 + liveOffer.candidate.migration +
    remainingBill src dst (proposed src dst oldContinuation liveOffer) < remainingBill src dst oldContinuation :=
  relative_sound src dst oldContinuation liveOffer 1 (by decide)

theorem paired_live_reserve : (proposed src dst oldContinuation liveOffer).reserve = 100 := rfl

end Witnesses

#print axioms relativeOK_iff
#print axioms relativeOK_refine
#print axioms paired_gain
#print axioms coverage_nonempty
#print axioms offer_nonempty
#print axioms proposed_reserve
#print axioms proposed_same
#print axioms proposed_fees
#print axioms proposed_bill_le_reserve
#print axioms relative_sound
#print axioms fromAbsolute
#print axioms absolute_same_candidate
#print axioms absolute_gate
#print axioms decision_margin
#print axioms fromDecision
#print axioms decision_offer_gain
#print axioms Witnesses.correlated_gap
#print axioms Witnesses.zero_regret_not_strict_improvement
#print axioms Witnesses.empty_scan
#print axioms Witnesses.paired_live_gain
#print axioms Witnesses.paired_live_reserve
end CRTT.RelativeEvidence
