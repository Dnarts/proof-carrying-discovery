/-
  Gate 5 v3.2 — Formal Invariants in Pure Lean 4 (Core Only, Zero External Dependencies, Complete Proofs).

  Verify locally with:
      lean gate5_invariants.lean

  Formalizes:
    1. Exact equivalence of Wolfram Rule 110 truth table and its Algebraic Normal Form (ANF).
    2. Minimum Hamming distance d_min(C_4) = 2 for C_4 = {0000, 0101, 1100, 1111}.
    3. Detection of all 16/16 single-bit flips in C_4.
    4. Exact 2-bit boundary: 10/24 two-bit flips map a codeword of C_4 to another codeword.
    5. Live post-certification invariant `liveCert`: passes 4/4 nominal states, rejects all 60/64
       mismatched `vs_mask` replacements, and rejects every single-bit flip of (ans, z1, za, zb, p).
    6. Information-theoretic lower bound: no 4-word binary code of length 2 achieves d_min >= 2.
-/

namespace Gate5V32

/-- Standard Wolfram Rule 110 local transition on (left, center, right). -/
def rule110 (l c r : Bool) : Bool :=
  match l, c, r with
  | true,  true,  true  => false
  | true,  true,  false => true
  | true,  false, true  => true
  | true,  false, false => false
  | false, true,  true  => true
  | false, true,  false => true
  | false, false, true  => true
  | false, false, false => false

/-- Algebraic Normal Form (ANF) of Rule 110 over F_2: c xor r xor (c & r) xor (l & c & r). -/
def rule110ANF (l c r : Bool) : Bool :=
  xor (xor c r) (xor (c && r) (l && c && r))

theorem rule110_eq_anf : ∀ l c r : Bool, rule110 l c r = rule110ANF l c r := by
  decide

/-- 4-bit observation codeword (z1, zA, zB, p). -/
abbrev Word4 := Bool × Bool × Bool × Bool

def codeword (h : Fin 4) : Word4 :=
  match h with
  | ⟨0, _⟩ => (false, false, false, false)  -- 0000
  | ⟨1, _⟩ => (false, true,  false, true)   -- 0101
  | ⟨2, _⟩ => (true,  true,  false, false)  -- 1100
  | ⟨3, _⟩ => (true,  true,  true,  true)   -- 1111

def inC3 (z1 za zb : Bool) : Option (Fin 4) :=
  match z1, za, zb with
  | false, false, false => some ⟨0, by decide⟩
  | false, true,  false => some ⟨1, by decide⟩
  | true,  true,  false => some ⟨2, by decide⟩
  | true,  true,  true  => some ⟨3, by decide⟩
  | _,     _,     _     => none

def inC4 (w : Word4) : Bool :=
  match w with
  | (z1, za, zb, p) =>
    match inC3 z1 za zb with
    | some _ => (xor (xor z1 za) (xor zb p)) == false
    | none   => false

def bdiff (a b : Bool) : Nat := if a == b then 0 else 1

def hdist4 (u v : Word4) : Nat :=
  let (u0, u1, u2, u3) := u
  let (v0, v1, v2, v3) := v
  bdiff u0 v0 + bdiff u1 v1 + bdiff u2 v2 + bdiff u3 v3

def flipBit4 (w : Word4) (i : Fin 4) : Word4 :=
  let (w0, w1, w2, w3) := w
  match i with
  | ⟨0, _⟩ => (!w0, w1, w2, w3)
  | ⟨1, _⟩ => (w0, !w1, w2, w3)
  | ⟨2, _⟩ => (w0, w1, !w2, w3)
  | ⟨3, _⟩ => (w0, w1, w2, !w3)

/-- Minimum Hamming distance of C_4 is at least 2 for all distinct codewords. -/
theorem c4_dmin_ge_2 :
    ∀ i j : Fin 4, i ≠ j → hdist4 (codeword i) (codeword j) ≥ 2 := by
  decide

/-- Minimum Hamming distance 2 is achieved (e.g., h=0 and h=1). -/
theorem c4_dmin_attained :
    hdist4 (codeword ⟨0, by decide⟩) (codeword ⟨1, by decide⟩) = 2 := by
  decide

/-- Every single-bit flip of any of the 4 codewords in C_4 (16/16 cases) leaves C_4. -/
theorem c4_detects_all_16_single_bit_flips :
    ∀ (h : Fin 4) (pos : Fin 4), inC4 (flipBit4 (codeword h) pos) = false := by
  decide

/-- Count how many of the 4 * C(4,2) = 24 two-bit flips map a C_4 codeword into C_4. -/
def countUndetectedTwoBitFlips : Nat :=
  let hs : List (Fin 4) := [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩]
  let pairs : List (Fin 4 × Fin 4) :=
    [ (⟨0, by decide⟩, ⟨1, by decide⟩), (⟨0, by decide⟩, ⟨2, by decide⟩),
      (⟨0, by decide⟩, ⟨3, by decide⟩), (⟨1, by decide⟩, ⟨2, by decide⟩),
      (⟨1, by decide⟩, ⟨3, by decide⟩), (⟨2, by decide⟩, ⟨3, by decide⟩) ]
  (hs.map fun h =>
    (pairs.filter fun (i, j) => inC4 (flipBit4 (flipBit4 (codeword h) i) j)).length
  ).foldl (· + ·) 0

/-- Exact 2-bit boundary of d_min = 2: 10 out of 24 two-bit flips remain in C_4. -/
theorem c4_two_bit_boundary_eq_10 : countUndetectedTwoBitFlips = 10 := by
  decide

/-- Live observation-certification predicate from Gate 5 v3.2. -/
def liveCert (vsMask : Fin 16) (ans : Fin 4) (w : Word4) : Bool :=
  let (z1, za, zb, p) := w
  let maskOk := vsMask.val == (1 <<< ans.val)
  let codeOk :=
    match inC3 z1 za zb with
    | some hCode => hCode == ans
    | none       => false
  let synOk := (xor (xor z1 za) (xor zb p)) == false
  maskOk && codeOk && synOk

def nominalMask (h : Fin 4) : Fin 16 :=
  match h with
  | ⟨0, _⟩ => ⟨1, by decide⟩
  | ⟨1, _⟩ => ⟨2, by decide⟩
  | ⟨2, _⟩ => ⟨4, by decide⟩
  | ⟨3, _⟩ => ⟨8, by decide⟩

/-- All 4 nominal states pass the live observation certificate. -/
theorem liveCert_nominal_all_4 :
    ∀ h : Fin 4, liveCert (nominalMask h) h (codeword h) = true := by
  decide

/-- All 60/64 mismatched `vs_mask` replacements are rejected by `liveCert`. -/
theorem liveCert_blocks_all_vs_mask_mismatches :
    ∀ (h : Fin 4) (m : Fin 16),
      m ≠ nominalMask h → liveCert m h (codeword h) = false := by
  decide

/-- Any change to `ans` (with intact `vs_mask` and receipt) is rejected by `liveCert`. -/
theorem liveCert_blocks_ans_corruption :
    ∀ (h a : Fin 4),
      a ≠ h → liveCert (nominalMask h) a (codeword h) = false := by
  decide

/-- Any single-bit flip in the stored 4-bit receipt (z1, zA, zB, p) is rejected by `liveCert`. -/
theorem liveCert_blocks_single_receipt_bit_flip :
    ∀ (h : Fin 4) (pos : Fin 4),
      liveCert (nominalMask h) h (flipBit4 (codeword h) pos) = false := by
  decide

/-- Information-theoretic lower bound: no 4-word binary code of length 2 achieves d_min >= 2. -/
abbrev Word2 := Bool × Bool

def hdist2 (u v : Word2) : Nat :=
  bdiff u.1 v.1 + bdiff u.2 v.2

private theorem no_len2_quad_dmin2 :
    ∀ a0 b0 a1 b1 a2 b2 a3 b3 : Bool,
      (a0, b0) ≠ (a1, b1) → (a0, b0) ≠ (a2, b2) → (a0, b0) ≠ (a3, b3) →
      (a1, b1) ≠ (a2, b2) → (a1, b1) ≠ (a3, b3) → (a2, b2) ≠ (a3, b3) →
      hdist2 (a0, b0) (a1, b1) < 2 ∨ hdist2 (a0, b0) (a2, b2) < 2 ∨ hdist2 (a0, b0) (a3, b3) < 2 ∨
      hdist2 (a1, b1) (a2, b2) < 2 ∨ hdist2 (a1, b1) (a3, b3) < 2 ∨ hdist2 (a2, b2) (a3, b3) < 2 := by
  decide

theorem no_len2_code_size4_dmin2 :
    ∀ f : Fin 4 → Word2,
      (∀ i j : Fin 4, i ≠ j → f i ≠ f j) →
      ∃ i j : Fin 4, i ≠ j ∧ hdist2 (f i) (f j) < 2 := by
  intro f hinj
  have h := no_len2_quad_dmin2
    (f ⟨0, by decide⟩).1 (f ⟨0, by decide⟩).2
    (f ⟨1, by decide⟩).1 (f ⟨1, by decide⟩).2
    (f ⟨2, by decide⟩).1 (f ⟨2, by decide⟩).2
    (f ⟨3, by decide⟩).1 (f ⟨3, by decide⟩).2
    (hinj ⟨0, by decide⟩ ⟨1, by decide⟩ (by decide))
    (hinj ⟨0, by decide⟩ ⟨2, by decide⟩ (by decide))
    (hinj ⟨0, by decide⟩ ⟨3, by decide⟩ (by decide))
    (hinj ⟨1, by decide⟩ ⟨2, by decide⟩ (by decide))
    (hinj ⟨1, by decide⟩ ⟨3, by decide⟩ (by decide))
    (hinj ⟨2, by decide⟩ ⟨3, by decide⟩ (by decide))
  match h with
  | Or.inl h01 => exact ⟨⟨0, by decide⟩, ⟨1, by decide⟩, by decide, h01⟩
  | Or.inr (Or.inl h02) => exact ⟨⟨0, by decide⟩, ⟨2, by decide⟩, by decide, h02⟩
  | Or.inr (Or.inr (Or.inl h03)) => exact ⟨⟨0, by decide⟩, ⟨3, by decide⟩, by decide, h03⟩
  | Or.inr (Or.inr (Or.inr (Or.inl h12))) => exact ⟨⟨1, by decide⟩, ⟨2, by decide⟩, by decide, h12⟩
  | Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h13)))) => exact ⟨⟨1, by decide⟩, ⟨3, by decide⟩, by decide, h13⟩
  | Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h23)))) => exact ⟨⟨2, by decide⟩, ⟨3, by decide⟩, by decide, h23⟩

end Gate5V32