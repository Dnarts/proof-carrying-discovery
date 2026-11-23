/-!
===============================================================================
  GATE 15: INTERVENTION ALGEBRA, COMPUTABLE CONTROL MASK K & COMMUTATOR [T_L, T_R]
  (Ось 2 → Ступень 2: Доказательная алгебра вмешательств под нормализатором N)

  Чистый Lean 4 Core (0 внешних библиотек, 0 `sorry` / `admit` / `axiom`).

  Разделы:
    §1. Система оценки (`EvalSystem`), формальный нормализатор `N` и маска контроля `K`
    §2. Алгебра коммутатора под нормализатором (`CommutesUnderN`, теоремы эквивалентности
        и опровержения совместной инвариантности)
    §3. Вычислимый проверяющий ортогональной маски `K` и протокола некоммутативности
        (`checkOrthogonalControl`, `checkNonCommProtocol`, теоремы звучности)
    §4. Теоремы анти-утечки: ложная некоммутативность при смешении слоёв
        (нарушение `Held` в `T_L` или языковая зависимость нормализатора `N`)
    §5. Конкретные инстанциации: Модель A (коммутирующая) и Модель B (ортогональная,
        но некоммутирующая, сертифицированная одной тактикой `by decide`)
    §6. Проверка аксиом ядра Lean 4.36.0 (`#print axioms`)
===============================================================================
-/

namespace Gate15InterventionAlgebra

/-! ## §1. Система оценки, нормализатор N и ортогональная маска контроля K -/

inductive CoordStatus where
  | Held
  | Changed
  | Uncontrolled
  deriving DecidableEq, Repr

/-- Двухкоординатная система оценки:
    `langOf` извлекает наблюдаемый язык/поверхностную форму `ℓ : Lang`,
    `normOf` — языконезависимый формальный нормализатор `N : State → Sem`. -/
structure EvalSystem (State Lang Sem : Type) where
  langOf : State → Lang
  normOf : State → Sem

abbrev Intervention (State : Type) := State → State

/-- Ортогональная маска контроля `K` на базовом состоянии `x₀`:
    - `T_L` меняет `langOf` (`Changed`) при удержанном `normOf` (`Held`);
    - `T_R` меняет `normOf` (`Changed`) при удержанном `langOf` (`Held`). -/
structure OrthogonalControl {State Lang Sem : Type}
    (sys : EvalSystem State Lang Sem)
    (T_L T_R : Intervention State) (x₀ : State) : Prop where
  tl_changes_lang : sys.langOf (T_L x₀) ≠ sys.langOf x₀
  tl_holds_sem    : sys.normOf (T_L x₀) = sys.normOf x₀
  tr_changes_sem  : sys.normOf (T_R x₀) ≠ sys.normOf x₀
  tr_holds_lang   : sys.langOf (T_R x₀) = sys.langOf x₀

/-! ## §2. Алгебра коммутатора под нормализатором N -/

/-- Коммутирование двух вмешательств относительно формального нормализатора `N`:
    `N(T_L(T_R(x))) = N(T_R(T_L(x)))`. -/
def CommutesUnderN {State Lang Sem : Type}
    (sys : EvalSystem State Lang Sem)
    (T_L T_R : Intervention State) (x : State) : Prop :=
  sys.normOf (T_L (T_R x)) = sys.normOf (T_R (T_L x))

/-- Теорема 1: если смена языка `T_L` глобально сохраняет нормализованный результат `N`,
    то коммутирование `[T_L, T_R] = 0` в точке `x` равносильно языковой инвариантности
    стратегии `T_R` в точке `x`. -/
theorem lang_invariance_implies_commutativity_iff_strategy_invariance
    {State Lang Sem : Type}
    (sys : EvalSystem State Lang Sem)
    (T_L T_R : Intervention State) (x : State)
    (hInvL : ∀ s : State, sys.normOf (T_L s) = sys.normOf s) :
    CommutesUnderN sys T_L T_R x ↔ sys.normOf (T_R x) = sys.normOf (T_R (T_L x)) := by
  unfold CommutesUnderN
  rw [hInvL (T_R x)]

/-- Теорема 2: один воспроизводимый свидетель некоммутативности `N(T_L(T_R x)) ≠ N(T_R(T_L x))`
    опровергает совместную инвариантность (`T_L` сохраняет `N` везде И `T_R` не зависит от `T_L`). -/
theorem noncomm_refutes_joint_invariance
    {State Lang Sem : Type}
    (sys : EvalSystem State Lang Sem)
    (T_L T_R : Intervention State) (x : State)
    (hNonComm : ¬ CommutesUnderN sys T_L T_R x) :
    ¬ ((∀ s : State, sys.normOf (T_L s) = sys.normOf s) ∧
       (∀ s : State, sys.normOf (T_R (T_L s)) = sys.normOf (T_R s))) := by
  rintro ⟨hInvL, hInvR⟩
  apply hNonComm
  unfold CommutesUnderN
  rw [hInvL (T_R x), hInvR x]

/-! ## §3. Вычислимый проверяющий маски контроля K и протокола некоммутативности -/

def checkOrthogonalControl {State Lang Sem : Type}
    [DecidableEq Lang] [DecidableEq Sem]
    (sys : EvalSystem State Lang Sem)
    (T_L T_R : Intervention State) (x₀ : State) : Bool :=
  decide (sys.langOf (T_L x₀) ≠ sys.langOf x₀) &&
  decide (sys.normOf (T_L x₀) = sys.normOf x₀) &&
  decide (sys.normOf (T_R x₀) ≠ sys.normOf x₀) &&
  decide (sys.langOf (T_R x₀) = sys.langOf x₀)

def checkNonCommProtocol {State Lang Sem : Type}
    [DecidableEq Lang] [DecidableEq Sem]
    (sys : EvalSystem State Lang Sem)
    (T_L T_R : Intervention State) (x₀ : State) : Bool :=
  checkOrthogonalControl sys T_L T_R x₀ &&
  decide (sys.normOf (T_L (T_R x₀)) ≠ sys.normOf (T_R (T_L x₀)))

/-- Теорема 3 (звучность вычислимого проверяющего маски контроля K): -/
theorem checkOrthogonalControl_sound {State Lang Sem : Type}
    [DecidableEq Lang] [DecidableEq Sem]
    (sys : EvalSystem State Lang Sem)
    (T_L T_R : Intervention State) (x₀ : State)
    (h : checkOrthogonalControl sys T_L T_R x₀ = true) :
    OrthogonalControl sys T_L T_R x₀ := by
  unfold checkOrthogonalControl at h
  simp only [Bool.and_eq_true] at h
  rcases h with ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
  exact ⟨
    of_decide_eq_true h1,
    of_decide_eq_true h2,
    of_decide_eq_true h3,
    of_decide_eq_true h4
  ⟩

/-- Теорема 4 (звучность полного вычислимого протокола некоммутативности):
    одна проверка `checkNonCommProtocol ... = true` через `by decide` одновременно
    удостоверяет ортогональность маски `K` на `x₀` и некоммутативность `[T_L, T_R] ≠ 0` под `N`. -/
theorem checkNonCommProtocol_sound {State Lang Sem : Type}
    [DecidableEq Lang] [DecidableEq Sem]
    (sys : EvalSystem State Lang Sem)
    (T_L T_R : Intervention State) (x₀ : State)
    (h : checkNonCommProtocol sys T_L T_R x₀ = true) :
    OrthogonalControl sys T_L T_R x₀ ∧ ¬ CommutesUnderN sys T_L T_R x₀ := by
  unfold checkNonCommProtocol at h
  simp only [Bool.and_eq_true] at h
  have hnc : sys.normOf (T_L (T_R x₀)) ≠ sys.normOf (T_R (T_L x₀)) :=
    of_decide_eq_true h.2
  exact ⟨checkOrthogonalControl_sound sys T_L T_R x₀ h.1,
    fun hComm => hnc hComm⟩

/-! ## §4. Теоремы анти-утечки: смешение слоёв без маски K и без выравнивания N -/

/-- Теорема 5 (анти-утечка при нарушении маски K):
    если `T_L` нарушает `Held` на семантической координате (вносит смысловой сдвиг),
    то некоммутативность `N(T_L(T_R x₀)) ≠ N(T_R(T_L x₀))` возникает ДАЖЕ КОГДА
    стратегия `T_R` вообще не зависит от языка `langOf`! -/
theorem confounded_TL_fakes_noncomm_without_mask_K :
    ∃ (sys : EvalSystem (Bool × Bool) Bool Bool)
      (T_L T_R : Intervention (Bool × Bool)) (x₀ : Bool × Bool),
      (∀ l₁ l₂ s, sys.normOf (T_R (l₁, s)) = sys.normOf (T_R (l₂, s))) ∧
      ¬ OrthogonalControl sys T_L T_R x₀ ∧
      ¬ CommutesUnderN sys T_L T_R x₀ := by
  let sys : EvalSystem (Bool × Bool) Bool Bool := ⟨Prod.fst, Prod.snd⟩
  let T_L : Intervention (Bool × Bool) := fun p => (!p.1, true)        -- портит sem!
  let T_R : Intervention (Bool × Bool) := fun p => (p.1, !p.2)         -- чисто от sem, не зависит от lang
  let x₀  : Bool × Bool := (false, false)
  refine ⟨sys, T_L, T_R, x₀, ?_, ?_, ?_⟩
  · intro _ _ _
    rfl
  · intro hOrt
    have hHold := hOrt.tl_holds_sem
    exact Bool.noConfusion hHold
  · intro hComm
    exact Bool.noConfusion hComm

/-- Теорема 6 (анти-утечка при невыровненном нормализаторе N):
    если нормализатор `N_bad` зависит от языка, он ложно фиксирует изменение смысла
    на `T_L x₀` даже для строго коммутирующей пары операторов `∀ x, T_L (T_R x) = T_R (T_L x)`. -/
theorem unaligned_normalizer_fakes_semantic_shift :
    ∃ (sysBad : EvalSystem (Bool × Bool) Bool Bool)
      (T_L T_R : Intervention (Bool × Bool)) (x₀ : Bool × Bool),
      (∀ x, T_L (T_R x) = T_R (T_L x)) ∧
      sysBad.normOf (T_L x₀) ≠ sysBad.normOf x₀ := by
  let sysBad : EvalSystem (Bool × Bool) Bool Bool := ⟨Prod.fst, fun p => p.1 && p.2⟩
  let T_L : Intervention (Bool × Bool) := fun p => (!p.1, p.2)
  let T_R : Intervention (Bool × Bool) := fun p => (p.1, !p.2)
  let x₀  : Bool × Bool := (false, true)
  refine ⟨sysBad, T_L, T_R, x₀, ?_, ?_⟩
  · intro ⟨l, s⟩
    rfl
  · decide

/-! ## §5. Конкретные инстанциации: Модель A (коммутирующая) и Модель B (некоммутирующая) -/

def binEvalSys : EvalSystem (Bool × Bool) Bool Bool where
  langOf := Prod.fst
  normOf := Prod.snd

/-- Модель A: независимые смена языка и смена стратегии -/
def T_L_indep : Intervention (Bool × Bool) := fun p => (!p.1, p.2)
def T_R_indep : Intervention (Bool × Bool) := fun p => (p.1, !p.2)

theorem modelA_orthogonal_verified :
    checkOrthogonalControl binEvalSys T_L_indep T_R_indep (false, false) = true := by
  decide

theorem modelA_commutes_everywhere (x : Bool × Bool) :
    CommutesUnderN binEvalSys T_L_indep T_R_indep x := by
  rfl

/-- Модель B: чистая смена языка `T_L_indep` (глобально сохраняющая `normOf`)
    и стратегия `T_R_coupled`, зависящая от языка представления (`l = false` → `!s`, `l = true` → `s`). -/
def T_R_coupled : Intervention (Bool × Bool) :=
  fun p => (p.1, if p.1 then p.2 else !p.2)

theorem modelB_noncomm_protocol_verified :
    checkNonCommProtocol binEvalSys T_L_indep T_R_coupled (false, false) = true := by
  decide

/-- Главное следствие Модели B: одной тактикой `by decide` удостоверены
    (1) ортогональная маска контроля `K` на `(false, false)`,
    (2) некоммутативность `[T_L, T_R] ≠ 0` под `N`,
    (3) опровержение совместной инвариантности. -/
theorem modelB_certified_corollary :
    OrthogonalControl binEvalSys T_L_indep T_R_coupled (false, false) ∧
    ¬ CommutesUnderN binEvalSys T_L_indep T_R_coupled (false, false) ∧
    ¬ ((∀ s, binEvalSys.normOf (T_L_indep s) = binEvalSys.normOf s) ∧
       (∀ s, binEvalSys.normOf (T_R_coupled (T_L_indep s)) = binEvalSys.normOf (T_R_coupled s))) := by
  rcases checkNonCommProtocol_sound binEvalSys T_L_indep T_R_coupled (false, false)
    modelB_noncomm_protocol_verified with ⟨hOrt, hNonComm⟩
  exact ⟨hOrt, hNonComm, noncomm_refutes_joint_invariance binEvalSys T_L_indep T_R_coupled (false, false) hNonComm⟩

/-! ## §6. Проверка аксиом ядра Lean 4.36.0 -/

#print axioms Gate15InterventionAlgebra.lang_invariance_implies_commutativity_iff_strategy_invariance
#print axioms Gate15InterventionAlgebra.noncomm_refutes_joint_invariance
#print axioms Gate15InterventionAlgebra.checkOrthogonalControl_sound
#print axioms Gate15InterventionAlgebra.checkNonCommProtocol_sound
#print axioms Gate15InterventionAlgebra.confounded_TL_fakes_noncomm_without_mask_K
#print axioms Gate15InterventionAlgebra.unaligned_normalizer_fakes_semantic_shift
#print axioms Gate15InterventionAlgebra.modelA_commutes_everywhere
#print axioms Gate15InterventionAlgebra.modelB_certified_corollary

end Gate15InterventionAlgebra
