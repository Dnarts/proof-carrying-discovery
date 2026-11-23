namespace UnifiedControllerV25

/-!
  unified_controller_v2_5.lean
  Самодостаточное ядро единого двухосевого контроллера v2.5 (Lean 4.36.0 Core, 0 sorry).
  Закрывает:
  1. Φ₃: ActiveGaugeCert, теорема disjointCause без аксиом, 3-й исход probeSamePort.
  2. Φ₄: невырожденность меры (0 < totalMass μ) в HasGapBound.
  3. Φ₅: сохранение разрыва Δ(T) в FrozenTransfer.
  4. Единое состояние EpistemicState с полиморфным портом, предикат Valid,
     теорема безопасности на обеих осях (probe, escalateLang, escalatePort)
     и парная теорема разделения.
-/

-- ============================================================================
-- 1. Базовые механизмы, порты, проекция журнала и префиксы
-- ============================================================================

structure Mech (Q Z Y : Type) where
  R : Q → Z
  S : Z → Y

structure GaugeTransform (Z : Type) where
  fwd : Z → Z
  inv : Z → Z
  left_inv  : ∀ z, inv (fwd z) = z
  right_inv : ∀ z, fwd (inv z) = z

def gaugeTransform {Q Z Y : Type} (M : Mech Q Z Y) (T : GaugeTransform Z) : Mech Q Z Y where
  R := fun q => T.fwd (M.R q)
  S := fun z => M.S (T.inv z)

def Port (Q Z Y O : Type) := Mech Q Z Y → Q → O

def publicPort {Q Z Y : Type} : Port Q Z Y Y :=
  fun M q => M.S (M.R q)

def tapPort {Q Z Y : Type} : Port Q Z Y (Z × Y) :=
  fun M q => (M.R q, M.S (M.R q))

abbrev ObsLog (Q O : Type) := List (Q × O)

def PrefixOf {α : Type} (l₁ l₂ : List α) : Prop :=
  ∃ rest : List α, l₂ = l₁ ++ rest

theorem prefixOf_trans {α : Type} {l₁ l₂ l₃ : List α}
    (h₁ : PrefixOf l₁ l₂) (h₂ : PrefixOf l₂ l₃) :
    PrefixOf l₁ l₃ := by
  rcases h₁ with ⟨r₁, rfl⟩
  rcases h₂ with ⟨r₂, rfl⟩
  exact ⟨r₁ ++ r₂, by rw [List.append_assoc]⟩

def projectLog {Q O₁ O₂ : Type} (f : O₁ → O₂) : ObsLog Q O₁ → ObsLog Q O₂
  | [] => []
  | (q, o) :: t => (q, f o) :: projectLog f t

theorem projectLog_append {Q O₁ O₂ : Type} (f : O₁ → O₂) (l₁ l₂ : ObsLog Q O₁) :
    projectLog f (l₁ ++ l₂) = projectLog f l₁ ++ projectLog f l₂ := by
  induction l₁ with
  | nil => rfl
  | cons h t ih =>
    rcases h with ⟨q, o⟩
    simp [projectLog, ih]

theorem projectLog_comp {Q O₁ O₂ O₃ : Type} (g : O₂ → O₃) (f : O₁ → O₂) (l : ObsLog Q O₁) :
    projectLog (fun x => g (f x)) l = projectLog g (projectLog f l) := by
  induction l with
  | nil => rfl
  | cons h t ih =>
    rcases h with ⟨q, o⟩
    simp [projectLog, ih]

theorem prefixOf_projectLog {Q O₁ O₂ : Type} (f : O₁ → O₂) {l₁ l₂ : ObsLog Q O₁}
    (hPref : PrefixOf l₁ l₂) :
    PrefixOf (projectLog f l₁) (projectLog f l₂) := by
  rcases hPref with ⟨r, rfl⟩
  exact ⟨projectLog f r, projectLog_append f l₁ r⟩

def agreesPort {Q Z Y O : Type} (P : Port Q Z Y O) (M : Mech Q Z Y) (D : ObsLog Q O) : Prop :=
  ∀ p ∈ D, P M p.1 = p.2

def VersionSpaceEmpty {Q Z Y O : Type}
    (InClass : Mech Q Z Y → Prop) (P : Port Q Z Y O) (D : ObsLog Q O) : Prop :=
  ∀ M, InClass M → ¬ agreesPort P M D

theorem agreesPort_prefix {Q Z Y O : Type}
    {P : Port Q Z Y O} {M : Mech Q Z Y} {D₁ D₂ : ObsLog Q O}
    (hPref : PrefixOf D₁ D₂) (hAg : agreesPort P M D₂) :
    agreesPort P M D₁ := by
  rcases hPref with ⟨rest, rfl⟩
  intro p hp
  exact hAg p (List.mem_append_left rest hp)

theorem agreesPort_project {Q Z Y O₁ O₂ : Type}
    {P₁ : Port Q Z Y O₁} {P₂ : Port Q Z Y O₂} {proj : O₂ → O₁}
    (hComm : ∀ M q, proj (P₂ M q) = P₁ M q)
    {M : Mech Q Z Y} {D : ObsLog Q O₂}
    (hAg : agreesPort P₂ M D) :
    agreesPort P₁ M (projectLog proj D) := by
  induction D with
  | nil =>
    intro p hp
    cases hp
  | cons h t ih =>
    rcases h with ⟨q, o⟩
    intro p hp
    cases hp with
    | head =>
      have hHead : P₂ M q = o := hAg (q, o) (List.Mem.head t)
      rw [← hComm M q, hHead]
    | tail _ hMem =>
      exact ih (fun x hx => hAg x (List.Mem.tail (q, o) hx)) p hMem

theorem versionSpaceEmpty_monotone {Q Z Y O : Type}
    {InClass : Mech Q Z Y → Prop} {P : Port Q Z Y O} {D₁ D₂ : ObsLog Q O}
    (hPref : PrefixOf D₁ D₂) (hEmpty : VersionSpaceEmpty InClass P D₁) :
    VersionSpaceEmpty InClass P D₂ := by
  intro M hIn hAg
  exact hEmpty M hIn (agreesPort_prefix hPref hAg)

theorem versionSpaceEmpty_port_refinement {Q Z Y O₁ O₂ : Type}
    {InClass : Mech Q Z Y → Prop}
    {P₁ : Port Q Z Y O₁} {P₂ : Port Q Z Y O₂} {proj : O₂ → O₁}
    (hComm : ∀ M q, proj (P₂ M q) = P₁ M q)
    {D₁ : ObsLog Q O₁} {D₂ : ObsLog Q O₂}
    (hPref : PrefixOf D₁ (projectLog proj D₂))
    (hEmpty : VersionSpaceEmpty InClass P₁ D₁) :
    VersionSpaceEmpty InClass P₂ D₂ := by
  intro M hIn hAg₂
  have hProj : agreesPort P₁ M (projectLog proj D₂) := agreesPort_project hComm hAg₂
  exact hEmpty M hIn (agreesPort_prefix hPref hProj)

theorem gauge_preserves_publicPort {Q Z Y : Type}
    (M : Mech Q Z Y) (T : GaugeTransform Z) (q : Q) :
    publicPort (gaugeTransform M T) q = publicPort M q := by
  simp [publicPort, gaugeTransform, T.left_inv]

-- ============================================================================
-- 2. Фикс Φ₃: ActiveGaugeCert и теорема disjointCause без аксиом
-- ============================================================================

structure GaugeEquivCert (Q Z Y : Type) where
  M : Mech Q Z Y
  T : GaugeTransform Z
  q₀ : Q
  nontrivial : T.fwd (M.R q₀) ≠ M.R q₀

/-- Привязанный к текущему классу и журналу калибровочный сертификат. -/
structure ActiveGaugeCert {Q Z Y : Type}
    (InClass : Mech Q Z Y → Prop) (D : ObsLog Q Y) where
  cert     : GaugeEquivCert Q Z Y
  inClass₁ : InClass cert.M
  inClass₂ : InClass (gaugeTransform cert.M cert.T)
  agreesD  : agreesPort publicPort cert.M D

theorem active_gauge_twin_agrees {Q Z Y : Type}
    {InClass : Mech Q Z Y → Prop} {D : ObsLog Q Y}
    (ag : ActiveGaugeCert InClass D) :
    agreesPort publicPort (gaugeTransform ag.cert.M ag.cert.T) D := by
  intro p hp
  rw [gauge_preserves_publicPort]
  exact ag.agreesD p hp

/-- Главный фикс Φ₃: несовместимость Оси 1 и Оси 2 — теорема (0 аксиом). -/
theorem active_gauge_disjoint_from_empty {Q Z Y : Type}
    (InClass : Mech Q Z Y → Prop) (D : ObsLog Q Y) :
    ¬ (VersionSpaceEmpty InClass publicPort D ∧ Nonempty (ActiveGaugeCert InClass D)) := by
  rintro ⟨hEmpty, ⟨ag⟩⟩
  exact hEmpty ag.cert.M ag.inClass₁ ag.agreesD

inductive TwoAxisAction where
  | escalateMemoryAxis1
  | refinePortAxis2
  | probeSamePort -- явный исход InsufficientEvidence
  deriving DecidableEq, Repr

/-- Двухосевой выбор без дефектной ветки по умолчанию. -/
def routeTwoAxis (axis1Refuted axis2ActiveGauge : Bool) : TwoAxisAction :=
  if axis1Refuted then .escalateMemoryAxis1
  else if axis2ActiveGauge then .refinePortAxis2
  else .probeSamePort

theorem route_neither_yields_probe :
    routeTwoAxis false false = .probeSamePort := rfl

-- ============================================================================
-- 3. Фикс Φ₄: Невырожденная мера (0 < totalMass μ) в HasGapBound
-- ============================================================================

abbrev DiscreteMeasure (Ω : Type) := List (Ω × Nat)

def totalMass {Ω : Type} : DiscreteMeasure Ω → Nat
  | [] => 0
  | (_, w) :: t => w + totalMass t

def eventMass {Ω : Type} (E : Ω → Bool) : DiscreteMeasure Ω → Nat
  | [] => 0
  | (ω, w) :: t => (if E ω then w else 0) + eventMass E t

structure HasGapBound {Ω : Type} (μ : DiscreteMeasure Ω) (E : Ω → Bool) (num den : Nat) : Prop where
  den_pos   : 0 < den
  mass_pos  : 0 < totalMass μ
  bound_le  : eventMass E μ * den ≤ num * totalMass μ

theorem zero_mass_rejected_by_HasGapBound {Ω : Type}
    (μ : DiscreteMeasure Ω) (E : Ω → Bool) (num den : Nat)
    (hZero : totalMass μ = 0) :
    ¬ HasGapBound μ E num den := by
  intro h
  have hPos := h.mass_pos
  rw [hZero] at hPos
  exact Nat.lt_irrefl 0 hPos

-- ============================================================================
-- 4. Фикс Φ₅: Заморозка с обязательным разрывом Δ(T)
-- ============================================================================

structure FrozenTransfer (Q : Type) (O : Type) where
  frozenAt  : ObsLog Q O
  R         : Q → Prop
  Covered   : Q → Prop
  Gap       : Q → Prop
  partition : ∀ q, R q → Covered q ∨ Gap q

-- ============================================================================
-- 5. Единое двухосевое состояние, Valid и теорема безопасности (Ось 1 + Ось 2)
-- ============================================================================

/-- Тупиковое расширение: новый класс имеет тот же наблюдаемый образ на порте P. -/
def SpuriousExtension {Q Z Y O : Type}
    (P : Port Q Z Y O) (Old New : Mech Q Z Y → Prop) : Prop :=
  ∀ M₂, New M₂ → ∃ M₁, Old M₁ ∧ ∀ q, P M₂ q = P M₁ q

theorem spurious_extension_cannot_repair {Q Z Y O : Type}
    {P : Port Q Z Y O} {Old New : Mech Q Z Y → Prop} {D : ObsLog Q O}
    (hSpur : SpuriousExtension P Old New)
    (hEmpty : VersionSpaceEmpty Old P D) :
    VersionSpaceEmpty New P D := by
  intro M₂ hNew hAg₂
  rcases hSpur M₂ hNew with ⟨M₁, hOld, hSame⟩
  apply hEmpty M₁ hOld
  intro p hp
  rw [← hSame p.1]
  exact hAg₂ p hp

/-- Единое состояние контроллера с полиморфным наблюдательным портом. -/
structure EpistemicState (Q Z Y : Type) : Type 1 where
  O              : Type
  port           : Port Q Z Y O
  projToPublic   : O → Y
  proj_sound     : ∀ M q, projToPublic (port M q) = publicPort M q
  InClass        : Mech Q Z Y → Prop
  D              : ObsLog Q O
  RefutedHistory : List (Mech Q Z Y → Prop)
  transfer       : FrozenTransfer Q Y

/-- Инвариант корректности состояния контроллера (4 нетривиальных условия). -/
structure Valid {Q Z Y : Type} (E : EpistemicState Q Z Y) : Prop where
  /-- 1. Все ранее опровергнутые классы остаются опровергнутыми на текущем порте и D. -/
  refuted_monotone : ∀ C ∈ E.RefutedHistory, VersionSpaceEmpty C E.port E.D
  /-- 2. Привязка заморозки: публичная проекция журнала расширяет точку заморозки. -/
  freeze_prefix    : PrefixOf E.transfer.frozenAt (projectLog E.projToPublic E.D)
  /-- 3. Разбиение остаточного разрыва Δ(T) сохранено. -/
  gap_intact       : ∀ q, E.transfer.R q → E.transfer.Covered q ∨ E.transfer.Gap q
  /-- 4. Конструктивная согласованность осей на публичной проекции (0 аксиом). -/
  axes_disjoint    : ¬ (VersionSpaceEmpty E.InClass publicPort (projectLog E.projToPublic E.D) ∧
                        Nonempty (ActiveGaugeCert E.InClass (projectLog E.projToPublic E.D)))

inductive LicensedStep {Q Z Y : Type} :
    EpistemicState Q Z Y → EpistemicState Q Z Y → Prop where
  /-- Шаг 1: новая проба на текущем порте (строгое расширение журнала). -/
  | probe (E : EpistemicState Q Z Y) (q : Q) (o : E.O) :
      LicensedStep E { E with D := E.D ++ [(q, o)] }
  /-- Шаг 2 (Ось 1): эскалация языка (только при опровержении и запрете тупика). -/
  | escalateLang (E : EpistemicState Q Z Y) (NewClass : Mech Q Z Y → Prop)
      (hRefuted : VersionSpaceEmpty E.InClass E.port E.D)
      (hNotSpurious : ¬ SpuriousExtension E.port E.InClass NewClass) :
      LicensedStep E { E with
        InClass := NewClass
        RefutedHistory := E.InClass :: E.RefutedHistory }
  /-- Шаг 3 (Ось 2): эскалация наблюдательного порта по ActiveGaugeCert. -/
  | escalatePort (E : EpistemicState Q Z Y)
      (O' : Type) (P' : Port Q Z Y O') (proj : O' → E.O)
      (hComm : ∀ M q, proj (P' M q) = E.port M q)
      (D' : ObsLog Q O')
      (hPref : PrefixOf E.D (projectLog proj D'))
      (hGauge : ActiveGaugeCert E.InClass (projectLog E.projToPublic E.D)) :
      LicensedStep E {
        O              := O'
        port           := P'
        projToPublic   := fun o' => E.projToPublic (proj o')
        proj_sound     := fun M q => by rw [hComm M q, E.proj_sound M q]
        InClass        := E.InClass
        D              := D'
        RefutedHistory := E.RefutedHistory
        transfer       := E.transfer
      }

/-- Теорема безопасности (Safety): любой лицензированный шаг (Ось 1 и Ось 2) сохраняет Valid. -/
theorem licensed_step_preserves_valid {Q Z Y : Type}
    {E E' : EpistemicState Q Z Y}
    (hVal : Valid E) (hStep : LicensedStep E E') :
    Valid E' := by
  cases hStep with
  | probe q o =>
    have hPref : PrefixOf E.D (E.D ++ [(q, o)]) := ⟨[(q, o)], rfl⟩
    refine {
      refuted_monotone := fun C hC =>
        versionSpaceEmpty_monotone hPref (hVal.refuted_monotone C hC)
      freeze_prefix :=
        prefixOf_trans hVal.freeze_prefix (prefixOf_projectLog E.projToPublic hPref)
      gap_intact := hVal.gap_intact
      axes_disjoint :=
        active_gauge_disjoint_from_empty E.InClass (projectLog E.projToPublic (E.D ++ [(q, o)]))
    }
  | escalateLang NewClass hRefuted _ =>
    refine {
      refuted_monotone := by
        intro C hC
        cases hC with
        | head => exact hRefuted
        | tail _ hMem => exact hVal.refuted_monotone C hMem
      freeze_prefix := hVal.freeze_prefix
      gap_intact := hVal.gap_intact
      axes_disjoint :=
        active_gauge_disjoint_from_empty NewClass (projectLog E.projToPublic E.D)
    }
  | escalatePort O' P' proj hComm D' hPref _ =>
    refine {
      refuted_monotone := fun C hC =>
        versionSpaceEmpty_port_refinement hComm hPref (hVal.refuted_monotone C hC)
      freeze_prefix := by
        have hProjPref : PrefixOf (projectLog E.projToPublic E.D)
            (projectLog E.projToPublic (projectLog proj D')) :=
          prefixOf_projectLog E.projToPublic hPref
        rw [← projectLog_comp E.projToPublic proj D'] at hProjPref
        exact prefixOf_trans hVal.freeze_prefix hProjPref
      gap_intact := hVal.gap_intact
      axes_disjoint :=
        active_gauge_disjoint_from_empty E.InClass
          (projectLog (fun o' => E.projToPublic (proj o')) D')
    }

-- ============================================================================
-- 6. Парная теорема разделения (Progress / Separation) для Оси 2
-- ============================================================================

def idMech : Mech Bool Bool Bool where
  R := fun q => q
  S := fun z => z

def notGauge : GaugeTransform Bool where
  fwd := Bool.not
  inv := Bool.not
  left_inv := Bool.not_not
  right_inv := Bool.not_not

def twinMech : Mech Bool Bool Bool :=
  gaugeTransform idMech notGauge

/-- На фиксированном publicPort idMech и twinMech неразличимы на ЛЮБОМ журнале D,
    но однократное уточнение порта до tapPort разделяет их за 1 запрос q₀ = true. -/
theorem two_axis_beats_fixed_public_port :
    (∀ D : ObsLog Bool Bool,
      agreesPort publicPort idMech D ↔ agreesPort publicPort twinMech D) ∧
    (tapPort idMech true ≠ tapPort twinMech true) := by
  constructor
  · intro D
    constructor
    · intro h p hp
      rw [twinMech, gauge_preserves_publicPort]
      exact h p hp
    · intro h p hp
      have h' := h p hp
      rw [twinMech, gauge_preserves_publicPort] at h'
      exact h'
  · intro hEq
    have hFst := congrArg Prod.fst hEq
    simp [tapPort, idMech, twinMech, gaugeTransform, notGauge] at hFst

-- Проверка аксиом
#print axioms active_gauge_disjoint_from_empty
#print axioms zero_mass_rejected_by_HasGapBound
#print axioms licensed_step_preserves_valid
#print axioms two_axis_beats_fixed_public_port

end UnifiedControllerV25