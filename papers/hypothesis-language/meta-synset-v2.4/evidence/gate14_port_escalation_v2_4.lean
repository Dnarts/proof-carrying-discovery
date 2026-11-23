/-!
===============================================================================
  GATE 14: PORT ESCALATION, GAUGE NON-IDENTIFIABILITY & SPURIOUS EXTENSIONS
  (Ось 2: Эскалация наблюдательного порта поверх ядра EpistemicRevisionV2)

  Чистый Lean 4 Core (0 внешних библиотек, 0 `sorry` / `admit` / `axiom`).

  Разделы:
    §1. Двухступенчатые механизмы (`TwoStageMech`) и наблюдательные порты (`ObsPort`)
    §2. Калибровочный сертификат (`GaugeEquivCert`) и невозможность разделения
        на одном порте (`gaugeCert_blocks_single_port_id`)
    §3. Уточнение и эскалация порта (`PortRefinement`), теорема разбиения
        калибровочного слоя (`tapPort_breaks_gaugeCert`) и сохранение опровержений
    §4. Детектор и блокировка тупиковых расширений (`SpuriousExtension`,
        `spurious_extension_zero_discriminatory_gain`, `spurious_hidden_var_concrete_witness`)
    §5. Связка с ядром ревизии (`PortEscalationTrigger`) и конкретная инстанциация
    §6. Проверка аксиом ядра Lean 4.36.0 (`#print axioms`)
===============================================================================
-/

namespace Gate14PortEscalation

/-! ## §1. Двухступенчатые механизмы и наблюдательные порты -/

/-- Двухступенчатый механизм `Q --R--> Z --S--> Y`:
    `R` строит скрытое внутреннее представление `z : Z`,
    `S` отображает его в публичный наблюдаемый выход `y : Y`. -/
structure TwoStageMech (Q Z Y : Type) where
  R : Q → Z
  S : Z → Y

/-- Абстрактный наблюдательный порт: извлекает наблюдаемый выход `Out`
    из механизма `Mech` на запросе `Query`. -/
structure ObsPort (Mech Query Out : Type) where
  observe : Mech → Query → Out

/-- Согласованность механизма с конечным журналом наблюдений на данном порте -/
def agreesPort {Mech Query Out : Type}
    (P : ObsPort Mech Query Out) (M : Mech) (D : List (Query × Out)) : Prop :=
  ∀ p ∈ D, P.observe M p.1 = p.2

/-- Публичный порт: наблюдателю доступна только композиция `S ∘ R` -/
def publicPort (Q Z Y : Type) : ObsPort (TwoStageMech Q Z Y) Q Y where
  observe M q := M.S (M.R q)

/-- Расширенный порт (эскалация порта Δ_port):
    открывает промежуточное представление `z = R(q)` вместе с публичным выходом `y` -/
def tapPort (Q Z Y : Type) : ObsPort (TwoStageMech Q Z Y) Q (Z × Y) where
  observe M q := (M.R q, M.S (M.R q))

/-! ## §2. Калибровочная симметрия и сертификат неидентифицируемости -/

/-- Обратимое преобразование скрытого пространства `Z` (калибровочная замена) -/
structure Bijection (Z : Type) where
  toFun    : Z → Z
  invFun   : Z → Z
  left_inv : ∀ z : Z, invFun (toFun z) = z
  right_inv: ∀ z : Z, toFun (invFun z) = z

/-- Калибровочное преобразование механизма: `R' = T ∘ R`, `S' = S ∘ T⁻¹` -/
def gaugeTransform {Q Z Y : Type}
    (M : TwoStageMech Q Z Y) (T : Bijection Z) : TwoStageMech Q Z Y where
  R q := T.toFun (M.R q)
  S z := M.S (T.invFun z)

/-- Теорема 1 (инвариантность публичного порта относительно калибровки):
    `S' ∘ R' = S ∘ R` на каждом запросе `q : Q`. -/
theorem gauge_preserves_publicPort {Q Z Y : Type}
    (M : TwoStageMech Q Z Y) (T : Bijection Z) (q : Q) :
    (publicPort Q Z Y).observe (gaugeTransform M T) q =
    (publicPort Q Z Y).observe M q := by
  dsimp only [publicPort, gaugeTransform]
  rw [T.left_inv]

/-- Конструктивный сертификат калибровочной неидентифицируемости (`GaugeEquivCert`):
    предъявляет механизм `M`, обратимую замену `T` и запрос `q₀`, на котором
    скрытое состояние реально меняется (`T(R(q₀)) ≠ R(q₀)`). -/
structure GaugeEquivCert (Q Z Y : Type) where
  M          : TwoStageMech Q Z Y
  T          : Bijection Z
  q₀         : Q
  nontrivial : T.toFun (M.R q₀) ≠ M.R q₀

/-- Теорема 2 (структурная невозможность идентификации на одном порте):
    при наличии `GaugeEquivCert` существуют два различных внутренних механизма
    `M₁ ≠ M₂`, которые абсолютно неразличимы на ЛЮБОМ журнале `D` через `publicPort`. -/
theorem gaugeCert_blocks_single_port_id {Q Z Y : Type}
    (cert : GaugeEquivCert Q Z Y) :
    let M₁ := cert.M
    let M₂ := gaugeTransform cert.M cert.T
    M₁ ≠ M₂ ∧
    ∀ (D : List (Q × Y)),
      agreesPort (publicPort Q Z Y) M₁ D ↔ agreesPort (publicPort Q Z Y) M₂ D := by
  intro M₁ M₂
  refine ⟨?_, ?_⟩
  · intro hEq
    have hR : M₁.R = M₂.R := congrArg TwoStageMech.R hEq
    have hRq : M₁.R cert.q₀ = M₂.R cert.q₀ := congrFun hR cert.q₀
    exact cert.nontrivial hRq.symm
  · intro D
    constructor
    · intro hAg p hp
      rw [gauge_preserves_publicPort cert.M cert.T p.1]
      exact hAg p hp
    · intro hAg p hp
      rw [← gauge_preserves_publicPort cert.M cert.T p.1]
      exact hAg p hp

/-! ## §3. Эскалация наблюдательного порта (`PortRefinement`) -/

/-- Нестрогое уточнение наблюдательного порта:
    порт `P₂` не теряет ни одного наблюдения порта `P₁`, поскольку
    существует проекция `proj : O₂ → O₁` с `proj ∘ P₂ = P₁`. -/
structure PortRefinement {Mech Query O₁ O₂ : Type}
    (P₁ : ObsPort Mech Query O₁) (P₂ : ObsPort Mech Query O₂) where
  proj     : O₂ → O₁
  commutes : ∀ (M : Mech) (q : Query), proj (P₂.observe M q) = P₁.observe M q

/-- Теорема 3: `tapPort` является нестрогим уточнением `publicPort` (строгость разделения доказывается в `tapPort_breaks_gaugeCert`) через `Prod.snd`. -/
def tapPort_refines_publicPort (Q Z Y : Type) :
    PortRefinement (publicPort Q Z Y) (tapPort Q Z Y) where
  proj     := Prod.snd
  commutes := fun _ _ => rfl

/-- Теорема 4 (разбиение калибровочного слоя после эскалации порта):
    для ЛЮБОГО сертификата `GaugeEquivCert` эскалированный порт `tapPort`
    строго разделяет `M₁` и `M₂` уже на ОДНОМ запросе `cert.q₀`. -/
theorem tapPort_breaks_gaugeCert {Q Z Y : Type}
    (cert : GaugeEquivCert Q Z Y) :
    (tapPort Q Z Y).observe cert.M cert.q₀ ≠
    (tapPort Q Z Y).observe (gaugeTransform cert.M cert.T) cert.q₀ := by
  intro hEq
  have hZ : cert.M.R cert.q₀ = cert.T.toFun (cert.M.R cert.q₀) := congrArg Prod.fst hEq
  exact cert.nontrivial hZ.symm

/-- Проекция журнала расширенного порта `P₂` на базовый порт `P₁` -/
def projectLog {Query O₁ O₂ : Type} (proj : O₂ → O₁)
    (D₂ : List (Query × O₂)) : List (Query × O₁) :=
  D₂.map (fun p => (p.1, proj p.2))

/-- Теорема 5 (монотонность опровержений при эскалации порта):
    если уточнение порта `P₂` согласовано с `D₂`, то базовый порт `P₁`
    согласован с проекцией `projectLog proj D₂`. Следовательно, опровержение
    класса на `P₁` автоматически сохраняется на `P₂`! -/
theorem port_refinement_preserves_agreement {Mech Query O₁ O₂ : Type}
    {P₁ : ObsPort Mech Query O₁} {P₂ : ObsPort Mech Query O₂}
    (ref : PortRefinement P₁ P₂) (M : Mech) (D₂ : List (Query × O₂)) :
    agreesPort P₂ M D₂ → agreesPort P₁ M (projectLog ref.proj D₂) := by
  intro hAg p hp
  rcases List.mem_map.mp hp with ⟨⟨q, o₂⟩, hMem, rfl⟩
  dsimp only
  rw [← ref.commutes M q, hAg (q, o₂) hMem]

theorem port_refinement_preserves_refutation {Mech Query O₁ O₂ : Type}
    {P₁ : ObsPort Mech Query O₁} {P₂ : ObsPort Mech Query O₂}
    (ref : PortRefinement P₁ P₂) (InClass : Mech → Prop) (D₂ : List (Query × O₂)) :
    (¬ ∃ M, InClass M ∧ agreesPort P₁ M (projectLog ref.proj D₂)) →
    (¬ ∃ M, InClass M ∧ agreesPort P₂ M D₂) := by
  intro hRef ⟨M, hIn, hAg₂⟩
  exact hRef ⟨M, hIn, port_refinement_preserves_agreement ref M D₂ hAg₂⟩

/-! ## §4. Детектор и блокировка тупиковых расширений (`SpuriousExtension`) -/

/-- Наблюдаемый образ класса механизмов `InClass` на порте `P` -/
def ObsImage {Mech Query Out : Type}
    (P : ObsPort Mech Query Out) (InClass : Mech → Prop) (f : Query → Out) : Prop :=
  ∃ M : Mech, InClass M ∧ ∀ q : Query, P.observe M q = f q

/-- Тупиковое расширение (`SpuriousExtension`):
    новый класс `L₁` строго шире `L₀` по описаниям (`∃ M, L₁ M ∧ ¬ L₀ M`),
    но НЕ добавляет ни одного нового наблюдаемого поведения на порте `P`. -/
structure SpuriousExtension {Mech Query Out : Type}
    (P : ObsPort Mech Query Out) (L₀ L₁ : Mech → Prop) : Prop where
  sub     : ∀ M, L₀ M → L₁ M
  strict  : ∃ M, L₁ M ∧ ¬ L₀ M
  sameObs : ∀ f : Query → Out, ObsImage P L₁ f ↔ ObsImage P L₀ f

/-- Теорема 6 (нулевая различительная и ремонтная сила тупикового расширения):
    если `L₀ ↪ L₁` — тупиковое расширение на порте `P`, то для ЛЮБОГО журнала `D`
    существование согласованной модели в `L₁` эквивалентно существованию в `L₀`.
    В частности, добавление скрытой переменной без нового порта НЕ МОЖЕТ
    починить опровергнутый класс! -/
theorem spurious_extension_zero_discriminatory_gain {Mech Query Out : Type}
    {P : ObsPort Mech Query Out} {L₀ L₁ : Mech → Prop}
    (hSpur : SpuriousExtension P L₀ L₁) (D : List (Query × Out)) :
    (∃ M, L₀ M ∧ agreesPort P M D) ↔ (∃ M, L₁ M ∧ agreesPort P M D) := by
  constructor
  · rintro ⟨M, hL₀, hAg⟩
    exact ⟨M, hSpur.sub M hL₀, hAg⟩
  · rintro ⟨M₁, hL₁, hAg⟩
    have hIn₁ : ObsImage P L₁ (fun q => P.observe M₁ q) := ⟨M₁, hL₁, fun _ => rfl⟩
    rcases (hSpur.sameObs _).mp hIn₁ with ⟨M₀, hL₀, hObsEq⟩
    refine ⟨M₀, hL₀, fun p hp => ?_⟩
    rw [hObsEq p.1]
    exact hAg p hp

theorem spurious_extension_cannot_repair_refutation {Mech Query Out : Type}
    {P : ObsPort Mech Query Out} {L₀ L₁ : Mech → Prop}
    (hSpur : SpuriousExtension P L₀ L₁) (D : List (Query × Out)) :
    (¬ ∃ M, L₀ M ∧ agreesPort P M D) → (¬ ∃ M, L₁ M ∧ agreesPort P M D) := by
  intro hRef hEx₁
  exact hRef ((spurious_extension_zero_discriminatory_gain hSpur D).mpr hEx₁)

/-- Теорема 7 (конкретный свидетель тупикового расширения — скрытый тег языка `z : Bool`):
    добавление ненаблюдаемого бита «внутреннего языка» к детерминированному выходу
    без расширения наблюдательного порта является тупиковым расширением. -/
def hiddenTagPort : ObsPort (Bool × Bool) Unit Bool where
  observe m _ := m.1

theorem spurious_hidden_var_concrete_witness :
    SpuriousExtension hiddenTagPort
      (fun m => m.2 = false)
      (fun _ => True) where
  sub    := fun _ _ => trivial
  strict := ⟨(false, true), trivial, fun h => Bool.noConfusion h⟩
  sameObs := fun f => by
    constructor
    · rintro ⟨⟨y, _⟩, _, hEq⟩
      refine ⟨(y, false), rfl, fun q => ?_⟩
      exact hEq q
    · rintro ⟨m, _, hEq⟩
      exact ⟨m, trivial, hEq⟩

/-! ## §5. Конкретная инстанциация Gate 14 (модель смены кодировки `Bool.not`) -/

def boolNotBijection : Bijection Bool where
  toFun     := Bool.not
  invFun    := Bool.not
  left_inv  := fun b => by cases b <;> rfl
  right_inv := fun b => by cases b <;> rfl

def exampleIdentityMech : TwoStageMech Bool Bool Bool where
  R q := q
  S z := z

def exampleGaugeCert : GaugeEquivCert Bool Bool Bool where
  M          := exampleIdentityMech
  T          := boolNotBijection
  q₀         := true
  nontrivial := by decide

/-- На публичном порте `exampleIdentityMech` и его калибровочный двойник неразличимы
    на любом журнале `D` (0 аксиом). -/
theorem example_gauge_unidentifiable :
    let M₁ := exampleGaugeCert.M
    let M₂ := gaugeTransform exampleGaugeCert.M exampleGaugeCert.T
    M₁ ≠ M₂ ∧
    ∀ (D : List (Bool × Bool)),
      agreesPort (publicPort Bool Bool Bool) M₁ D ↔
      agreesPort (publicPort Bool Bool Bool) M₂ D :=
  gaugeCert_blocks_single_port_id exampleGaugeCert

/-- Эскалация порта `publicPort → tapPort` разбивает калибровочный слой за 1 запрос `true`. -/
theorem example_tap_separates :
    (tapPort Bool Bool Bool).observe exampleGaugeCert.M true ≠
    (tapPort Bool Bool Bool).observe (gaugeTransform exampleGaugeCert.M exampleGaugeCert.T) true :=
  tapPort_breaks_gaugeCert exampleGaugeCert

/-! ## §6. Проверка аксиом ядра Lean 4.36.0 -/

#print axioms Gate14PortEscalation.gauge_preserves_publicPort
#print axioms Gate14PortEscalation.gaugeCert_blocks_single_port_id
#print axioms Gate14PortEscalation.tapPort_breaks_gaugeCert
#print axioms Gate14PortEscalation.port_refinement_preserves_agreement
#print axioms Gate14PortEscalation.port_refinement_preserves_refutation
#print axioms Gate14PortEscalation.spurious_extension_zero_discriminatory_gain
#print axioms Gate14PortEscalation.spurious_extension_cannot_repair_refutation
#print axioms Gate14PortEscalation.spurious_hidden_var_concrete_witness
#print axioms Gate14PortEscalation.example_gauge_unidentifiable
#print axioms Gate14PortEscalation.example_tap_separates

end Gate14PortEscalation
