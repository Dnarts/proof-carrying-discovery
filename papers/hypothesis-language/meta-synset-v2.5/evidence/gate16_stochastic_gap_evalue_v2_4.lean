/-!
===============================================================================
  GATE 16: QUANTITATIVE RESIDUAL GAP Δ_ε & INDEPENDENT TWO-STEP E-VALUE CERTIFICATION
  (Ось 2 → Ступень 3: Вероятностная ревизия на точных дискретных мерах)

  Чистый Lean 4 Core (0 внешних библиотек, 0 `sorry` / `admit` / `axiom`).
  Вся вероятностная арифметика представлена точно в `Nat` (масштабированные
  веса на `Fin n`), без вещественных чисел с плавающей точкой и без Mathlib.

  Разделы:
    §1. Точные конечные дискретные меры (`sumFin`, `totalMass`, `eventMass`, `expectNum`)
    §2. Неравенство Маркова (`markov_ineq`) и теорема валидности e-value
        (`evalue_false_rejection_bound`: `K * mass(reject) ≤ totalMass`, т.е. P(reject) ≤ 1/K)
    §3. Композиция двух независимых e-value (`indep_two_step_evalue_product_valid`)
    §4. Количественный остаточный разрыв `GapBound` (обобщение `GapEmpty` из v2.1),
        субаддитивность при композиции (`union_gap_bound`) и обратная совместимость
    §5. Вычислимый проверяющий (`checkEValueCert`, `checkGapBound`) и конкретная
        инстанциация стохастического роутера (`by decide`)
    §6. Проверка аксиом ядра Lean 4.36.0 (`#print axioms`)
===============================================================================
-/

namespace Gate16StochasticGap

/-! ## §1. Точные конечные дискретные меры на `Fin n` -/

/-- Сумма функции `f : Fin n → Nat` по всем элементам `Fin n` -/
def sumFin : (n : Nat) → (Fin n → Nat) → Nat
  | 0,     _ => 0
  | n + 1, f =>
      sumFin n (fun i => f ⟨i.val, Nat.lt_trans i.isLt (Nat.lt_succ_self n)⟩) +
      f ⟨n, Nat.lt_succ_self n⟩

/-- Базовые свойства `sumFin` (монотонность, линейность, вынесение константы) -/
theorem sumFin_le_sumFin : ∀ (n : Nat) (f g : Fin n → Nat),
    (∀ i, f i ≤ g i) → sumFin n f ≤ sumFin n g
  | 0, _, _, _ => Nat.le_refl 0
  | n + 1, f, g, hle => by
    dsimp only [sumFin]
    have h1 := sumFin_le_sumFin n
      (fun i => f ⟨i.val, Nat.lt_trans i.isLt (Nat.lt_succ_self n)⟩)
      (fun i => g ⟨i.val, Nat.lt_trans i.isLt (Nat.lt_succ_self n)⟩)
      (fun i => hle ⟨i.val, Nat.lt_trans i.isLt (Nat.lt_succ_self n)⟩)
    have h2 := hle ⟨n, Nat.lt_succ_self n⟩
    omega

theorem sumFin_add : ∀ (n : Nat) (f g : Fin n → Nat),
    sumFin n (fun i => f i + g i) = sumFin n f + sumFin n g
  | 0, _, _ => rfl
  | n + 1, f, g => by
    dsimp only [sumFin]
    rw [sumFin_add n
      (fun i => f ⟨i.val, Nat.lt_trans i.isLt (Nat.lt_succ_self n)⟩)
      (fun i => g ⟨i.val, Nat.lt_trans i.isLt (Nat.lt_succ_self n)⟩)]
    omega

theorem sumFin_mul_left : ∀ (n c : Nat) (f : Fin n → Nat),
    sumFin n (fun i => c * f i) = c * sumFin n f
  | 0, _, _ => by dsimp only [sumFin]; omega
  | n + 1, c, f => by
    dsimp only [sumFin]
    rw [sumFin_mul_left n c (fun i => f ⟨i.val, Nat.lt_trans i.isLt (Nat.lt_succ_self n)⟩)]
    rw [Nat.mul_add]

theorem sumFin_mul_right : ∀ (n c : Nat) (f : Fin n → Nat),
    sumFin n (fun i => f i * c) = sumFin n f * c
  | 0, _, _ => by dsimp only [sumFin]; omega
  | n + 1, c, f => by
    dsimp only [sumFin]
    rw [sumFin_mul_right n c (fun i => f ⟨i.val, Nat.lt_trans i.isLt (Nat.lt_succ_self n)⟩)]
    rw [Nat.add_mul]

theorem sumFin_zero : ∀ (n : Nat), sumFin n (fun _ => 0) = 0
  | 0     => rfl
  | n + 1 => by dsimp only [sumFin]; rw [sumFin_zero n]

/-- Полная масса меры `μ`, масса события `E` и ненормированное матожидание `E[X]` -/
def totalMass {n : Nat} (μ : Fin n → Nat) : Nat :=
  sumFin n μ

def eventMass {n : Nat} (μ : Fin n → Nat) (E : Fin n → Bool) : Nat :=
  sumFin n (fun i => if E i then μ i else 0)

def expectNum {n : Nat} (μ : Fin n → Nat) (X : Fin n → Nat) : Nat :=
  sumFin n (fun i => μ i * X i)

/-! ## §2. Неравенство Маркова и теорема валидности e-value -/

/-- Теорема 1 (точное неравенство Маркова на `Fin n`):
    для любой меры `μ`, неотрицательной величины `X` и порога `T`:
      `T * mass(μ, {i | T ≤ X i}) ≤ expectNum(μ, X)`. -/
theorem markov_ineq {n : Nat} (μ X : Fin n → Nat) (T : Nat) :
    T * eventMass μ (fun i => decide (T ≤ X i)) ≤ expectNum μ X := by
  unfold eventMass expectNum
  rw [← sumFin_mul_left n T]
  apply sumFin_le_sumFin
  intro i
  by_cases h : T ≤ X i
  · have hdec : decide (T ≤ X i) = true := decide_eq_true h
    simp only [hdec, ite_true]
    rw [Nat.mul_comm (μ i) (X i)]
    exact Nat.mul_le_mul_right (μ i) h
  · have hdec : decide (T ≤ X i) = false := decide_eq_false h
    simp only [hdec]
    exact Nat.zero_le _

/-- Валидная e-переменная под нулевой мерой `μ` со шкалой `D > 0`:
    `E_μ[E / D] ≤ 1`, записано точно без деления как `expectNum μ E ≤ D * totalMass μ`. -/
def ValidEValue {n : Nat} (μ E : Fin n → Nat) (D : Nat) : Prop :=
  0 < D ∧ expectNum μ E ≤ D * totalMass μ

/-- Теорема 2 (граница вероятности ложного опровержения для e-value):
    если `E` — валидная e-переменная шкалы `D > 0` под `μ`, то для любого порога `K`
    правило отклонения `E(i) ≥ K * D` удовлетворяет
      `K * eventMass μ reject ≤ totalMass μ`,  т.е.  `P_μ(reject) ≤ 1 / K`. -/
theorem evalue_false_rejection_bound {n : Nat} (μ E : Fin n → Nat) (D K : Nat)
    (hValid : ValidEValue μ E D) :
    K * eventMass μ (fun i => decide (K * D ≤ E i)) ≤ totalMass μ := by
  have hM := markov_ineq μ E (K * D)
  have hChain : K * D * eventMass μ (fun i => decide (K * D ≤ E i)) ≤ D * totalMass μ :=
    Nat.le_trans hM hValid.2
  have hReassoc : D * (K * eventMass μ (fun i => decide (K * D ≤ E i))) ≤ D * totalMass μ := by
    have hEq : K * D * eventMass μ (fun i => decide (K * D ≤ E i)) =
        D * (K * eventMass μ (fun i => decide (K * D ≤ E i))) := by
      rw [Nat.mul_comm K D, Nat.mul_assoc]
    rw [← hEq]
    exact hChain
  exact Nat.le_of_mul_le_mul_left hReassoc hValid.1

/-! ## §3. Композиция двух независимых e-value (фиксированный горизонт 2) -/

/-- Теорема 3 (мультипликативность независимых e-value):
    если `E₁` валидна для `μ₁` (шкала `D₁`) и `E₂` валидна для `μ₂` (шкала `D₂`),
    то произведение `E₁(i) * E₂(j)` валидно для меры-произведения `μ₁(i) * μ₂(j)`
    со шкалой `D₁ * D₂`. -/
theorem indep_two_step_evalue_product_valid {n₁ n₂ : Nat}
    (μ₁ E₁ : Fin n₁ → Nat) (D₁ : Nat)
    (μ₂ E₂ : Fin n₂ → Nat) (D₂ : Nat)
    (h1 : ValidEValue μ₁ E₁ D₁) (h2 : ValidEValue μ₂ E₂ D₂) :
    0 < D₁ * D₂ ∧
    sumFin n₁ (fun i => sumFin n₂ (fun j => (μ₁ i * μ₂ j) * (E₁ i * E₂ j))) ≤
      (D₁ * D₂) * (totalMass μ₁ * totalMass μ₂) := by
  refine ⟨Nat.mul_pos h1.1 h2.1, ?_⟩
  have hFactor :
      sumFin n₁ (fun i => sumFin n₂ (fun j => (μ₁ i * μ₂ j) * (E₁ i * E₂ j))) =
      expectNum μ₁ E₁ * expectNum μ₂ E₂ := by
    have hInner : ∀ i : Fin n₁,
        sumFin n₂ (fun j => (μ₁ i * μ₂ j) * (E₁ i * E₂ j)) =
        (μ₁ i * E₁ i) * expectNum μ₂ E₂ := by
      intro i
      unfold expectNum
      rw [← sumFin_mul_left n₂ (μ₁ i * E₁ i)]
      have hPt : ∀ j : Fin n₂, (μ₁ i * μ₂ j) * (E₁ i * E₂ j) = (μ₁ i * E₁ i) * (μ₂ j * E₂ j) := by
        intro j
        rw [Nat.mul_assoc (μ₁ i) (μ₂ j), ← Nat.mul_assoc (μ₂ j) (E₁ i),
            Nat.mul_comm (μ₂ j) (E₁ i), Nat.mul_assoc (E₁ i) (μ₂ j),
            ← Nat.mul_assoc (μ₁ i) (E₁ i)]
      have hFun : (fun j => (μ₁ i * μ₂ j) * (E₁ i * E₂ j)) =
                  (fun j => (μ₁ i * E₁ i) * (μ₂ j * E₂ j)) := funext hPt
      rw [hFun]
    have hOuter : (fun i => sumFin n₂ (fun j => (μ₁ i * μ₂ j) * (E₁ i * E₂ j))) =
                  (fun i => (μ₁ i * E₁ i) * expectNum μ₂ E₂) := funext hInner
    rw [hOuter, sumFin_mul_right n₁ (expectNum μ₂ E₂) (fun i => μ₁ i * E₁ i)]
    rfl
  rw [hFactor]
  have hProd : expectNum μ₁ E₁ * expectNum μ₂ E₂ ≤
      (D₁ * totalMass μ₁) * (D₂ * totalMass μ₂) :=
    Nat.mul_le_mul h1.2 h2.2
  have hSwap : (D₁ * totalMass μ₁) * (D₂ * totalMass μ₂) =
      (D₁ * D₂) * (totalMass μ₁ * totalMass μ₂) := by
    rw [Nat.mul_assoc D₁ (totalMass μ₁), ← Nat.mul_assoc (totalMass μ₁) D₂,
        Nat.mul_comm (totalMass μ₁) D₂, Nat.mul_assoc D₂ (totalMass μ₁),
        ← Nat.mul_assoc D₁ D₂]
  rw [← hSwap]
  exact hProd

/-! ## §4. Количественный остаточный разрыв `GapBound` (обобщение `GapEmpty`) -/

/-- Количественный остаточный разрыв: `μ(Gap) ≤ num / den`, записано точно в `Nat` -/
def HasGapBound {n : Nat} (μ : Fin n → Nat) (Gap : Fin n → Bool) (num den : Nat) : Prop :=
  0 < den ∧ eventMass μ Gap * den ≤ num * totalMass μ

/-- Количественно покрытое обоснование (обобщение `CoveredJustification` из v2.1) -/
structure QuantCovered (n : Nat) where
  μ         : Fin n → Nat
  R         : Fin n → Bool
  Covered   : Fin n → Bool
  Gap       : Fin n → Bool
  partition : ∀ i : Fin n, R i = true → Covered i = true ∨ Gap i = true

/-- Теорема 4 (обратная совместимость с `GapEmpty` из v2.1):
    если остаточный разрыв пуст (`∀ i, Gap i = false`), то его мера равна `0` (`HasGapBound μ Gap 0 1`). -/
theorem gapEmpty_implies_zero_gapBound {n : Nat} (μ : Fin n → Nat) (Gap : Fin n → Bool)
    (hEmpty : ∀ i : Fin n, Gap i = false) :
    HasGapBound μ Gap 0 1 := by
  unfold HasGapBound eventMass
  have hFun : (fun i => if Gap i then μ i else 0) = (fun _ => 0) :=
    funext (fun i => by rw [hEmpty i]; rfl)
  rw [hFun, sumFin_zero n]
  exact ⟨Nat.zero_lt_one, by omega⟩

/-- Теорема 5 (субаддитивность меры событий):
    `mass(μ, G₁ ∪ G₂) ≤ mass(μ, G₁) + mass(μ, G₂)`. -/
theorem eventMass_or_le {n : Nat} (μ : Fin n → Nat) (G₁ G₂ : Fin n → Bool) :
    eventMass μ (fun i => G₁ i || G₂ i) ≤ eventMass μ G₁ + eventMass μ G₂ := by
  unfold eventMass
  rw [← sumFin_add]
  apply sumFin_le_sumFin
  intro i
  by_cases h1 : G₁ i = true <;> by_cases h2 : G₂ i = true <;>
    simp only [h1, h2, Bool.true_or, Bool.false_or, ite_true] <;> omega

/-- Теорема 6 (алгебра количественного разрыва при композиции):
    если `μ(G₁) ≤ p₁ / q` и `μ(G₂) ≤ p₂ / q`, то `μ(G₁ ∪ G₂) ≤ (p₁ + p₂) / q`. -/
theorem union_gap_bound {n : Nat} (μ : Fin n → Nat) (G₁ G₂ : Fin n → Bool)
    (p₁ p₂ q : Nat)
    (h1 : HasGapBound μ G₁ p₁ q) (h2 : HasGapBound μ G₂ p₂ q) :
    HasGapBound μ (fun i => G₁ i || G₂ i) (p₁ + p₂) q := by
  unfold HasGapBound at h1 h2 ⊢
  refine ⟨h1.1, ?_⟩
  have hOr := eventMass_or_le μ G₁ G₂
  have hMul := Nat.mul_le_mul_right q hOr
  rw [Nat.add_mul] at hMul ⊢
  have h1m := h1.2
  have h2m := h2.2
  omega

/-! ## §5. Вычислимый проверяющий и инстанциация стохастического роутера -/

def checkEValueCert {n : Nat} (μ E : Fin n → Nat) (D : Nat) : Bool :=
  decide (0 < D) && decide (expectNum μ E ≤ D * totalMass μ)

theorem checkEValueCert_sound {n : Nat} (μ E : Fin n → Nat) (D : Nat)
    (h : checkEValueCert μ E D = true) : ValidEValue μ E D := by
  unfold checkEValueCert at h
  simp only [Bool.and_eq_true] at h
  exact ⟨of_decide_eq_true h.1, of_decide_eq_true h.2⟩

def checkGapBound {n : Nat} (μ : Fin n → Nat) (Gap : Fin n → Bool) (num den : Nat) : Bool :=
  decide (0 < den) && decide (eventMass μ Gap * den ≤ num * totalMass μ)

theorem checkGapBound_sound {n : Nat} (μ : Fin n → Nat) (Gap : Fin n → Bool) (num den : Nat)
    (h : checkGapBound μ Gap num den = true) : HasGapBound μ Gap num den := by
  unfold checkGapBound at h
  simp only [Bool.and_eq_true] at h
  exact ⟨of_decide_eq_true h.1, of_decide_eq_true h.2⟩

theorem den_zero_rejected_by_HasGapBound {n : Nat} (μ : Fin n → Nat) (Gap : Fin n → Bool) (num : Nat) :
    ¬ HasGapBound μ Gap num 0 := by
  intro h
  exact Nat.lt_irrefl 0 h.1

/-- Конкретный пример: 2-шаговый стохастический языковой роутер (`n = 4` исхода,
    равномерная нулевая мера `H₀: [1, 1, 1, 1]`, `totalMass = 4`).
    E-переменная `E = [0, 0, 0, 4]` (шкала `D = 1`) при пороге `K = 4` даёт
    гарантию ложного отклонения `P_{H₀}(reject) ≤ 1/4` одной тактикой `by decide`. -/
def unif4 : Fin 4 → Nat := fun _ => 1

def sampleEVal4 : Fin 4 → Nat
  | ⟨3, _⟩ => 4
  | _      => 0

theorem sample_evalue_cert_verified :
    checkEValueCert unif4 sampleEVal4 1 = true := by
  decide

theorem sample_evalue_rejection_corollary :
    4 * eventMass unif4 (fun i => decide (4 * 1 ≤ sampleEVal4 i)) ≤ totalMass unif4 :=
  evalue_false_rejection_bound unif4 sampleEVal4 1 4
    (checkEValueCert_sound unif4 sampleEVal4 1 sample_evalue_cert_verified)

/-- Анти-утечка стохастического режима:
    единичный «аномальный» исход (`i = 3`, вес 1 из 4) имеет непустой `Gap`,
    но мера разрыва строго ограничена `1/4` (`HasGapBound unif4 gap 1 4`). -/
def sampleStochGap : Fin 4 → Bool
  | ⟨3, _⟩ => true
  | _      => false

theorem sample_stoch_gap_verified :
    checkGapBound unif4 sampleStochGap 1 4 = true := by
  decide

theorem sample_stoch_gap_corollary :
    HasGapBound unif4 sampleStochGap 1 4 ∧ ¬ (∀ i, sampleStochGap i = false) := by
  refine ⟨checkGapBound_sound unif4 sampleStochGap 1 4 sample_stoch_gap_verified, ?_⟩
  intro hAll
  have h3 := hAll ⟨3, by decide⟩
  exact Bool.noConfusion h3

/-! ## §6. Проверка аксиом ядра Lean 4.36.0 -/

#print axioms Gate16StochasticGap.markov_ineq
#print axioms Gate16StochasticGap.evalue_false_rejection_bound
#print axioms Gate16StochasticGap.indep_two_step_evalue_product_valid
#print axioms Gate16StochasticGap.gapEmpty_implies_zero_gapBound
#print axioms Gate16StochasticGap.eventMass_or_le
#print axioms Gate16StochasticGap.union_gap_bound
#print axioms Gate16StochasticGap.checkEValueCert_sound
#print axioms Gate16StochasticGap.checkGapBound_sound
#print axioms Gate16StochasticGap.sample_evalue_rejection_corollary
#print axioms Gate16StochasticGap.sample_stoch_gap_corollary
#print axioms Gate16StochasticGap.den_zero_rejected_by_HasGapBound

end Gate16StochasticGap
