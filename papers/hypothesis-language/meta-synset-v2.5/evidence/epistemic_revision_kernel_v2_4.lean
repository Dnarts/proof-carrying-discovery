/-!
===============================================================================
  МЕТА-СИНСЕТ И ИНВАРИАНТ (v2.4 — Zero-Warning Clean Core, Complete SymbolLift Symmetry & Conditional Two-Axis Router):
  ТИПИЗИРОВАННАЯ ФОРМАЛЬНАЯ СИСТЕМА РЕВИЗИИ ИССЛЕДОВАТЕЛЬСКИХ ПРЕДСТАВЛЕНИЙ

  Чистый Lean 4 Core (0 внешних библиотек, 0 `sorry` / `admit` / `axiom`).

  Разделы:
    §0. Топология областей (Scope) и картография объектов
    §1. Интенсиональные утверждения Claim s и семантический функтор Denote
    §2. Запечатанное свидетельство DirectEvidence (закрытие лазейки "scope-only")
    §3. Алгебра остаточного разрыва Gap (Covered vs Total, композиция, LiftScope)
    §4. Зависимая лицензия вывода Judgement и теоремы звучности / анти-утечки
    §5. Префиксная монотонность RawLog, необратимость Freeze и CertifiedRev
    §6. Инстанциация на ветвящемся меню StepBranch (DPDA vs Queue, SymbolLift, Gain_min)
    §7. Негативные и позитивные тесты ядра (#print axioms)
===============================================================================
-/

namespace EpistemicRevisionV2

/-! ## §0. Топология областей (Scope) и картография носителей -/

inductive Scope where
  | FinitePrefix      -- конечный префикс сырого append-only журнала
  | LanguageMenu      -- замороженное конечное меню конкурирующих гипотез/классов
  | InfiniteLanguage  -- всё бесконечное множество слов Σ*
  | RevisionSpace     -- пространство трасс и слоёв ревизии (Δ_L, Δ_D, Δ_π)
  deriving DecidableEq, Repr

inductive Carrier where
  | ManualProof
  | LeanKernelTerm
  | FiniteCert
  | ExhaustiveEnum
  | EmpiricalProtocol
  deriving DecidableEq, Repr

inductive RawEdit where
  | EditLang   (fromLang toLang : String)
  | EditData   (addedCount : Nat)
  | EditPolicy (fromPol toPol : String)
  deriving DecidableEq, Repr

/-! ## §1. Интенсиональные утверждения Claim s и функтор Denote -/

abbrev Sym := Fin 3
abbrev Word := List Sym

def sym0 : Sym := ⟨0, by decide⟩
def sym1 : Sym := ⟨1, by decide⟩
def symHash : Sym := ⟨2, by decide⟩

def isBinarySym (b : Sym) : Bool := b.val == 0 || b.val == 1

def isBinaryWord : Word → Bool
  | []      => true
  | b :: bs => isBinarySym b && isBinaryWord bs

/-- Сырой append-only журнал наблюдений -/
abbrev ObsEntry := Word × Bool
abbrev RawLog := List ObsEntry

/-- Префиксно-монотонное отношение журналов: `PrefixOf l₁ l₂` означает `l₂ = l₁ ++ tail` -/
def PrefixOf (l₁ l₂ : RawLog) : Prop :=
  ∃ tail : RawLog, l₂ = l₁ ++ tail

theorem prefixOf_refl (l : RawLog) : PrefixOf l l :=
  ⟨[], by simp⟩

theorem prefixOf_trans {l₁ l₂ l₃ : RawLog} :
    PrefixOf l₁ l₂ → PrefixOf l₂ l₃ → PrefixOf l₁ l₃
  | ⟨t₁, h₁⟩, ⟨t₂, h₂⟩ => ⟨t₁ ++ t₂, by rw [h₂, h₁, List.append_assoc]⟩

theorem prefixOf_mem {l₁ l₂ : RawLog} (h : PrefixOf l₁ l₂) (p : ObsEntry) :
    p ∈ l₁ → p ∈ l₂ := by
  rcases h with ⟨tail, rfl⟩
  intro hp
  exact List.mem_append_left tail hp

/-- Абстрактный объектный язык программ над словами -/
structure ObjLang (Prog : Type) where
  eval : Prog → Word → Bool

/-- Семантическое пространство версий V(L, D) -/
def agreesOn {Prog : Type} (L : ObjLang Prog) (D : RawLog) (h : Prog) : Prop :=
  ∀ p ∈ D, L.eval h p.1 = p.2

def VersionSpaceEmpty {Prog : Type} (L : ObjLang Prog) (D : RawLog) : Prop :=
  ¬ ∃ h : Prog, agreesOn L D h

/-- Гомоморфное продолжение посимвольного отображения f на строки (`SymbolLift f`) -/
structure SymbolLift (f : Sym → Sym) where
  binPreserving : isBinarySym (f sym0) = true ∧ isBinarySym (f sym1) = true
  injectiveBin  : f sym0 ≠ f sym1
  homomorphic   : ∀ u v : Word, List.map f (u ++ v) = List.map f u ++ List.map f v :=
    fun _ _ => List.map_append

/-- Индексированный тип проверяемых утверждений: утверждение жёстко привязано к Scope -/
inductive Claim : Scope → Type 1 where
  | LangRefuted     : {Prog : Type} → ObjLang Prog → RawLog → Claim .FinitePrefix
  | TraceAgrees     : {Prog : Type} → ObjLang Prog → Prog → RawLog → Claim .FinitePrefix
  | MenuSplit       : (Menu : Type) → (menuSize : Nat) → (gainMin : Nat) → Claim .LanguageMenu
  | InfiniteProp    : (P : Word → Prop) → Claim .InfiniteLanguage
  | UniversalSep    : {Prog : Type} → ObjLang Prog → (target : Word → Bool) → Claim .InfiniteLanguage
  | ModelLayerObs   : (Attr : Type) → (attrEqOnFibers : Prop) → Claim .RevisionSpace

/-- Семантический функтор `Denote`: переводит синтаксический `Claim s` в реальный `Prop` ядра -/
def Denote : ∀ {s : Scope}, Claim s → Prop
  | .FinitePrefix,     .LangRefuted L D       => VersionSpaceEmpty L D
  | .FinitePrefix,     .TraceAgrees L h D     => agreesOn L D h
  | .LanguageMenu,     .MenuSplit _ n g       => 0 < g ∧ g ≤ n
  | .InfiniteLanguage, .InfiniteProp P        => ∀ w : Word, P w
  | .InfiniteLanguage, .UniversalSep L target =>
      ¬ ∃ h, ∀ w : Word, L.eval h w = target w
  | .RevisionSpace,    .ModelLayerObs _ P     => P

/-! ## §2. Запечатанное свидетельство DirectEvidence (закрытие лазейки "scope-only") -/

abbrev Premise := Prop

/-- Запечатанное прямое свидетельство:
    параметризовано ТОЧНОЙ областью `s`, предпосылкой `A` и конкретным утверждением `c : Claim s`.
    Хранит реальный терм доказательства `A → Denote c`, поэтому подмена `c₁ ≠ c₂`
    и подделка `FiniteCert` для `InfiniteLanguage` невозможны на уровне типов. -/
structure DirectEvidence (s : Scope) (A : Premise) (c : Claim s) where
  carrier : Carrier
  proof   : A → Denote c

def mkFiniteEvidence {A : Premise} {c : Claim .FinitePrefix}
    (prf : A → Denote c) : DirectEvidence .FinitePrefix A c :=
  ⟨.FiniteCert, prf⟩

def mkInfiniteLeanEvidence {A : Premise} {c : Claim .InfiniteLanguage}
    (prf : A → Denote c) : DirectEvidence .InfiniteLanguage A c :=
  ⟨.LeanKernelTerm, prf⟩

/-- Отрицательный тест №1 (интенсиональность):
    свидетельство для `cTrue` не может населить `DirectEvidence` для `cFalse` даже в том же `Scope`. -/
theorem claim_distinct_not_reusable :
    let cFalse : Claim .InfiniteLanguage := .InfiniteProp (fun _ => False)
    let cTrue  : Claim .InfiniteLanguage := .InfiniteProp (fun _ => True)
    (∃ _ : DirectEvidence .InfiniteLanguage True cTrue, True) ∧
    (¬ ∃ _ : DirectEvidence .InfiniteLanguage True cFalse, True) := by
  refine ⟨⟨⟨.LeanKernelTerm, fun _ _ => trivial⟩, trivial⟩, ?_⟩
  intro ⟨ev, _⟩
  exact ev.proof trivial []

/-! ## §3. Алгебра остаточного разрыва Gap (точечно-зависимые утверждения c : Q → Claim s) -/

/-- Покрытое обоснование вывода над множеством сценариев/моделей `Q`:
    утверждение `c : Q → Claim s` индексировано самой точкой `q : Q`,
    а поле `partition` запрещает подставлять `Gap := False` при неполном покрытии. -/
structure CoveredJustification (Q : Type) (s : Scope) (A : Premise) (c : Q → Claim s) where
  R          : Q → Prop
  Covered    : Q → Prop
  Gap        : Q → Prop
  partition  : ∀ q : Q, R q → Covered q ∨ Gap q
  localProof : A → ∀ q : Q, Covered q → Denote (c q)

/-- Полное обоснование над `Q`: каждая точка `q` в запросе `R`
    обеспечена собственным запечатанным `DirectEvidence s A (c q)`. -/
structure TotalJustification (Q : Type) (s : Scope) (A : Premise) (c : Q → Claim s) where
  R          : Q → Prop
  evidenceAt : ∀ q : Q, R q → DirectEvidence s A (c q)
  fullCover  : A → ∀ q : Q, R q → Denote (c q)

/-- Конструктивное условие пустоты разрыва Δ(T) = ∅ -/
structure GapEmpty {Q : Type} (Gap : Q → Prop) : Prop where
  noGap : ∀ q : Q, ¬ Gap q

/-- Позитивный тест: при `GapEmpty Gap` точечно-зависимое `CoveredJustification`
    законно превращается в `TotalJustification`. -/
def bridgeComplete {Q : Type} {s : Scope} {A : Premise} {c : Q → Claim s}
    (cj : CoveredJustification Q s A c)
    (hEmpty : GapEmpty cj.Gap) : TotalJustification Q s A c where
  R := cj.R
  evidenceAt := fun q hRq =>
    { carrier := .LeanKernelTerm
      proof := fun hA => by
        rcases cj.partition q hRq with hCov | hGap
        · exact cj.localProof hA q hCov
        · exact False.elim (hEmpty.noGap q hGap) }
  fullCover := fun hA q hRq => by
    rcases cj.partition q hRq with hCov | hGap
    · exact cj.localProof hA q hCov
    · exact False.elim (hEmpty.noGap q hGap)

/-- Отрицательный тест №2a: непустой `Gap` блокирует `bridgeComplete`. -/
theorem nonempty_gap_blocks_total {Q : Type} {s : Scope} {A : Premise} {c : Q → Claim s}
    (cj : CoveredJustification Q s A c)
    (hGap : ∃ q : Q, cj.Gap q) :
    ¬ GapEmpty cj.Gap := by
  intro he
  rcases hGap with ⟨q, hq⟩
  exact he.noGap q hq

/-- Отрицательный тест №2b (закрытие обхода `bridgeComplete`):
    если существует точка `q₀` в области запроса `R` (например, модель с ε-переходами),
    для которой при посылке `A` утверждение `Denote (c q₀)` не выполнено,
    то НИКАКОЙ терм `TotalJustification Q s A c` вообще не существует (ни через
    `bridgeComplete`, ни собранный напрямую). -/
theorem pointwise_unproved_blocks_any_total {Q : Type} {s : Scope} {A : Premise} {c : Q → Claim s}
    (R : Q → Prop)
    (hCounter : ∃ q₀ : Q, R q₀ ∧ A ∧ ¬ Denote (c q₀)) :
    ¬ ∃ tot : TotalJustification Q s A c, tot.R = R := by
  rintro ⟨tot, hReq⟩
  rcases hCounter with ⟨q₀, hRq₀, hA, hNot⟩
  rw [← hReq] at hRq₀
  exact hNot (tot.fullCover hA q₀ hRq₀)

/-- Алгебра разрывов при композиции переносов (Теорема 2 Мета-синсета II): -/
structure TransferCoverage (Q : Type) where
  R         : Q → Prop
  S_ok      : Q → Prop
  Gap       : Q → Prop
  partition : ∀ q : Q, R q → S_ok q ∨ Gap q

def composeCoverage {Q₁ Q₂ : Type} (f : Q₁ → Q₂)
    (t₁ : TransferCoverage Q₁) (t₂ : TransferCoverage Q₂)
    (hImg : ∀ q : Q₁, t₁.R q → t₂.R (f q)) : TransferCoverage Q₁ where
  R q    := t₁.R q
  S_ok q := t₁.S_ok q ∧ t₂.S_ok (f q)
  Gap q  := t₁.Gap q ∨ t₂.Gap (f q)
  partition := fun q hRq => by
    rcases t₁.partition q hRq with h1 | g1
    · rcases t₂.partition (f q) (hImg q hRq) with h2 | g2
      · exact Or.inl ⟨h1, h2⟩
      · exact Or.inr (Or.inr g2)
    · exact Or.inr (Or.inl g1)

theorem composeCoverage_gap_empty_iff {Q₁ Q₂ : Type} (f : Q₁ → Q₂)
    (t₁ : TransferCoverage Q₁) (t₂ : TransferCoverage Q₂)
    (hImg : ∀ q : Q₁, t₁.R q → t₂.R (f q)) :
    GapEmpty (composeCoverage f t₁ t₂ hImg).Gap ↔
      (GapEmpty t₁.Gap ∧ ∀ q : Q₁, ¬ t₂.Gap (f q)) := by
  constructor
  · intro h
    refine ⟨⟨fun q hq => h.noGap q (Or.inl hq)⟩, fun q hq => h.noGap q (Or.inr hq)⟩
  · intro ⟨h1, h2⟩
    exact ⟨fun q hq => by
      rcases hq with g1 | g2
      · exact h1.noGap q g1
      · exact h2 q g2⟩

/-- Точечно-условный межобластной мост `ScopeBridge`:
    доказывает `Denote (c₂ q)` только для подмножества `ModelOk q` целевых объектов `Q₂`. -/
structure ScopeBridge (Q₂ : Type) (s₁ s₂ : Scope) (A₁ A₂ : Premise)
    (c₁ : Claim s₁) (c₂ : Q₂ → Claim s₂) (ModelOk : Q₂ → Prop) where
  liftProof : A₂ → Denote c₁ → ∀ q : Q₂, ModelOk q → Denote (c₂ q)

/-- Подъём области `liftScope`:
    принимает полное обоснование `c₁` в точке `q₁` (в области `s₁`) и условный мост `ScopeBridge`,
    возвращает `CoveredJustification` в `s₂` для точечно-зависимого `c₂ : Q₂ → Claim s₂`
    с явным остаточным разрывом `ModelGap`. -/
def liftScope {Q₁ Q₂ : Type} {s₁ s₂ : Scope} {A₁ A₂ : Premise}
    {c₁ : Q₁ → Claim s₁} {c₂ : Q₂ → Claim s₂}
    (tot₁ : TotalJustification Q₁ s₁ A₁ c₁)
    (q₁ : Q₁) (hRq₁ : tot₁.R q₁)
    (R₂ : Q₂ → Prop)
    (ModelOk : Q₂ → Prop)
    (ModelGap : Q₂ → Prop)
    (bridge : ScopeBridge Q₂ s₁ s₂ A₁ A₂ (c₁ q₁) c₂ ModelOk)
    (hPart : ∀ q : Q₂, R₂ q → ModelOk q ∨ ModelGap q) :
    CoveredJustification Q₂ s₂ (A₁ ∧ A₂) c₂ where
  R := R₂
  Covered := ModelOk
  Gap := ModelGap
  partition := hPart
  localProof := fun ⟨hA₁, hA₂⟩ q hOk =>
    bridge.liftProof hA₂ (tot₁.fullCover hA₁ q₁ hRq₁) q hOk

/-! ## §4. Зависимая лицензия вывода Judgement и теоремы звучности / анти-утечки -/

/-- Семантическое вложение языков: каждая программа `L₂` эквивалентна некоторой программе `L₁` -/
def LangEmbed {P₂ P₁ : Type} (L₂ : ObjLang P₂) (L₁ : ObjLang P₁) : Prop :=
  ∀ h₂ : P₂, ∃ h₁ : P₁, ∀ w : Word, L₁.eval h₁ w = L₂.eval h₂ w

/-- Семантическая единственность на наблюдениях D (|Ṽ(L, D)| ≤ 1) -/
def VersionSpaceUnique {Prog : Type} (L : ObjLang Prog) (D : RawLog) : Prop :=
  ∀ h₁ h₂ : Prog, agreesOn L D h₁ → agreesOn L D h₂ → ∀ w : Word, L.eval h₁ w = L.eval h₂ w

/-- Конструкторы лицензии вывода κ : Judgement(α, δ) —
    определяют НЕ ярлык метода, а множество РАЗРЕШЁННЫХ выводов Γ(e). -/
inductive Judgement where
  | Transport     (domPhi : Word → Prop) (srcProp tgtProp : Word → Prop)
  | LocalIso      (subProp : Word → Prop)
  | Refutation    {Prog : Type} (L : ObjLang Prog) (D : RawLog)
  | NonIdent      {Prog : Type} (L : ObjLang Prog) (D : RawLog) (h₁ h₂ : Prog)
  | Expansion     {P₁ P₂ : Type} (L₁ : ObjLang P₁) (L₂ : ObjLang P₂)
  | Restriction   {P₁ P₂ : Type} (L₁ : ObjLang P₁) (L₂ : ObjLang P₂) (D : RawLog)
  | FormalTheorem (T : Prop)
  | FiniteCheck   (bound : Nat) (P : Word → Bool)

/-- Что именно разрешено выводить (оператор Γ(κ) -> Prop) -/
def AllowedConclusion : Judgement → Prop
  | .Transport domPhi srcP tgtP => ∀ w, domPhi w → (srcP w ↔ tgtP w)
  | .LocalIso subP              => ∀ w, subP w → True
  | .Refutation L D             => VersionSpaceEmpty L D
  | .NonIdent L D h₁ h₂         => agreesOn L D h₁ ∧ agreesOn L D h₂ ∧ h₁ ≠ h₂
  | .Expansion _ _              => True  -- разрешает лишь фиксацию: старые опровержения могут утратить силу
  | .Restriction L₁ L₂ D        =>
      LangEmbed L₂ L₁ ∧
      (VersionSpaceEmpty L₁ D → VersionSpaceEmpty L₂ D) ∧
      (VersionSpaceUnique L₁ D → VersionSpaceUnique L₂ D)
  | .FormalTheorem T            => T
  | .FiniteCheck bound P        => ∀ w : Word, w.length ≤ bound → P w = true

/-- Связанное свидетельство с лицензией κ и доказательством его предпосылки -/
structure LicensedEvidence (j : Judgement) where
  sound : AllowedConclusion j

/-- Теорема звучности лицензии: всё, что выдаёт Γ(κ), гарантировано типом. -/
theorem judgement_sound (j : Judgement) (ev : LicensedEvidence j) :
    AllowedConclusion j :=
  ev.sound

/-- Нетривиальная семантика `Restriction`: при вложении `L₂ ↪ L₁`
    сужение языка сохраняет как опровержение (`V = ∅`), так и единственность идентификации (`|Ṽ| ≤ 1`). -/
theorem restriction_sound {P₁ P₂ : Type} (L₁ : ObjLang P₁) (L₂ : ObjLang P₂) (D : RawLog)
    (hEmb : LangEmbed L₂ L₁) :
    AllowedConclusion (.Restriction L₁ L₂ D) := by
  refine ⟨hEmb, ?_, ?_⟩
  · intro hEmpty ⟨h₂, hAgree₂⟩
    rcases hEmb h₂ with ⟨h₁, hEq⟩
    apply hEmpty
    refine ⟨h₁, fun p hp => ?_⟩
    rw [hEq p.1]
    exact hAgree₂ p hp
  · intro hUniq h₂a h₂b hAgA hAgB w
    rcases hEmb h₂a with ⟨h₁a, hEqA⟩
    rcases hEmb h₂b with ⟨h₁b, hEqB⟩
    have hAg1A : agreesOn L₁ D h₁a := fun p hp => by rw [hEqA p.1]; exact hAgA p hp
    have hAg1B : agreesOn L₁ D h₁b := fun p hp => by rw [hEqB p.1]; exact hAgB p hp
    have h1Eq := hUniq h₁a h₁b hAg1A hAg1B w
    rw [← hEqA w, ← hEqB w]
    exact h1Eq

/-- Теоремы анти-утечки (невыводимости запрещённых обобщений):
    1) Конечная проверка `FiniteCheck bound P` НЕ влечёт универсальное `∀ w, P w = true`. -/
theorem finiteCheck_blocks_universal :
    ∃ (bound : Nat) (P : Word → Bool),
      AllowedConclusion (.FiniteCheck bound P) ∧ ¬ (∀ w : Word, P w = true) := by
  refine ⟨0, (fun w => w.length == 0), ?_, ?_⟩
  · intro w hw
    have hz : w.length = 0 := Nat.eq_zero_of_le_zero hw
    exact decide_eq_true (by simp [hz])
  · intro hAll
    have h1 := hAll [sym0]
    simp at h1

/-- 2) Опровержение `Refutation L₁ D` НЕ влечёт опровержение расширенного языка `L₂`. -/
theorem refutation_blocks_extended :
    ∃ (L₁ : ObjLang Unit) (L₂ : ObjLang Bool) (D : RawLog),
      AllowedConclusion (.Refutation L₁ D) ∧ ¬ VersionSpaceEmpty L₂ D := by
  let L₁ : ObjLang Unit := ⟨fun _ _ => false⟩
  let L₂ : ObjLang Bool := ⟨fun b _ => b⟩
  let D  : RawLog := [([sym0], true)]
  refine ⟨L₁, L₂, D, ?_, ?_⟩
  · rintro ⟨h, hAgree⟩
    have hh := hAgree ([sym0], true) (List.Mem.head _)
    simp [L₁] at hh
  · intro hEmpty
    apply hEmpty
    refine ⟨true, fun p hp => ?_⟩
    simp only [D, List.mem_singleton] at hp
    rw [hp]

/-! ## §5. Префиксная монотонность RawLog, необратимость Freeze и CertifiedRev -/

theorem versionSpaceEmpty_monotone {Prog : Type} (L : ObjLang Prog)
    {l₁ l₂ : RawLog} (hPref : PrefixOf l₁ l₂) :
    VersionSpaceEmpty L l₁ → VersionSpaceEmpty L l₂ := by
  intro hEmpty ⟨h, hAgree⟩
  apply hEmpty
  refine ⟨h, fun p hp => hAgree p (prefixOf_mem hPref p hp)⟩

structure FrozenMenu (Branch : Type) where
  frozenAt : RawLog
  branches : List Branch
  nonEmpty : 0 < branches.length

structure CertifiedRev (Q : Type) (s : Scope) (A : Premise) (c : Q → Claim s) where
  beforeLog : RawLog
  afterLog  : RawLog
  monotone  : PrefixOf beforeLog afterLog
  edits     : List RawEdit
  just      : CoveredJustification Q s A c

structure DiscoveryChain (Branch Prog : Type) where
  rawLog       : RawLog
  menu         : FrozenMenu Branch
  menuFixed    : PrefixOf menu.frozenAt rawLog
  finalProg    : Prog
  residualGaps : List String

/-! ## §6. Ветвящийся шаг `StepBranch` с несущим `SymbolLift.binPreserving` -/

inductive MemBranch where
  | CanonicalDPDA  (f : Sym → Sym)
  | CanonicalQueue (f : Sym → Sym)

/-- Оценка 2-битных слов с проверкой бинарности обеих половин (как в Gate 12-13):
    теперь `SymbolLift.binPreserving` является математически НЕОБХОДИМЫМ условием. -/
def memEval : MemBranch → (Sym → Sym) → Word → Bool
  | .CanonicalDPDA _, f, w =>
    match w with
    | [a, b, h, c, d] =>
        isBinarySym a && isBinarySym b && (h == symHash) &&
        isBinarySym c && isBinarySym d && (c == f b) && (d == f a)
    | _ => false
  | .CanonicalQueue _, f, w =>
    match w with
    | [a, b, h, c, d] =>
        isBinarySym a && isBinarySym b && (h == symHash) &&
        isBinarySym c && isBinarySym d && (c == f a) && (d == f b)
    | _ => false

/-- Теорема о минимальном 1-шаговом зонде порядка `q* = [0, 1, #, f(1), f(0)]`:
    существенно использует ОБА поля `SymbolLift f`: `binPreserving` и `injectiveBin`. -/
theorem stepBranch_order_probe_splits (f : Sym → Sym) (hlift : SymbolLift f) :
    let qStar : Word := [sym0, sym1, symHash, f sym1, f sym0]
    memEval (.CanonicalDPDA f) f qStar = true ∧
    memEval (.CanonicalQueue f) f qStar = false := by
  intro qStar
  have hb0 : isBinarySym (f sym0) = true := hlift.binPreserving.1
  have hb1 : isBinarySym (f sym1) = true := hlift.binPreserving.2
  have hneq : (f sym1 == f sym0) = false := by
    cases h : (f sym1 == f sym0)
    · rfl
    · exact False.elim (hlift.injectiveBin (of_decide_eq_true h).symm)
  have hb0' : isBinarySym sym0 = true := by decide
  have hb1' : isBinarySym sym1 = true := by decide
  refine ⟨?_, ?_⟩
  · dsimp only [qStar, memEval]
    simp only [symHash, hb0', hb1', hb0, hb1]
    simp [sym0, sym1]
  · dsimp only [qStar, memEval]
    simp only [symHash, hb0', hb1', hb0, hb1]
    simp [sym0, sym1]
    intro hEq
    exact absurd hEq.symm hlift.injectiveBin

/-- Контрпример необходимости `binPreserving`:
    если `f_bad` инъективно на `{0,1}` (`0 ↦ #`, `1 ↦ 0`), но нарушает `binPreserving`,
    то ОБЕ ветви дают `false` на `q*` (зонд теряет различающую силу, `Gain_min = 0`). -/
def badTransform : Sym → Sym
  | ⟨0, _⟩ => symHash
  | ⟨1, _⟩ => sym0
  | b      => b

theorem stepBranch_fails_without_binPreserving :
    badTransform sym0 ≠ badTransform sym1 ∧
    let qStar : Word := [sym0, sym1, symHash, badTransform sym1, badTransform sym0]
    memEval (.CanonicalDPDA badTransform) badTransform qStar = false ∧
    memEval (.CanonicalQueue badTransform) badTransform qStar = false := by
  refine ⟨by decide, ?_, ?_⟩ <;> decide

/-- Контрпример необходимости `injectiveBin`:
    если `f_const` сохраняет бинарность (`0 ↦ 0, 1 ↦ 0`), но нарушает инъективность,
    то ОБЕ ветви возвращают `true` на `q*` (зонд не различает LIFO и FIFO, `Gain_min = 0`). -/
def constZeroTransform : Sym → Sym
  | ⟨0, _⟩ => sym0
  | ⟨1, _⟩ => sym0
  | b      => b

theorem stepBranch_fails_without_injectiveBin :
    (isBinarySym (constZeroTransform sym0) = true ∧ isBinarySym (constZeroTransform sym1) = true) ∧
    let qStar : Word := [sym0, sym1, symHash, constZeroTransform sym1, constZeroTransform sym0]
    memEval (.CanonicalDPDA constZeroTransform) constZeroTransform qStar = true ∧
    memEval (.CanonicalQueue constZeroTransform) constZeroTransform qStar = true := by
  refine ⟨⟨by decide, by decide⟩, ?_, ?_⟩ <;> decide

def stepBranchCertifiedRev (f : Sym → Sym) (_hlift : SymbolLift f) (log : RawLog) :
    CertifiedRev Unit .LanguageMenu (Nonempty (SymbolLift f)) (fun _ => .MenuSplit MemBranch 2 1) where
  beforeLog := log
  afterLog := log ++ [([sym0, sym1, symHash, f sym1, f sym0], false)]
  monotone := ⟨[([sym0, sym1, symHash, f sym1, f sym0], false)], rfl⟩
  edits := [.EditData 1, .EditLang "Menu{DPDA,Queue}" "CanonicalQueue"]
  just :=
    { R := fun _ => True
      Covered := fun _ => True
      Gap := fun _ => False
      partition := fun _ _ => Or.inl trivial
      localProof := fun _ _ _ => by simp [Denote] }

/-! ## §7. Мост к параметрическим теоремам Gate 12–13 с точечным модельным разрывом -/

/-- Параметрический межобластной подъём Gate 12–13 для точечно-зависимого семейства `c_model : Q_mod → Claim .InfiniteLanguage`:
    доказывает разделение (или свойство) только для real-time моделей (`isRealTime m`),
    явно оставляя модели с ε-переходами (`hasEpsilon m`) в `Gap`. -/
def gate12_13_parametric_lift {P_tgt Q_mod : Type}
    (L_tgt : ObjLang P_tgt) (prog : P_tgt) (obs : RawLog)
    {A₁ A₂ : Premise}
    (finTot : TotalJustification Unit .FinitePrefix A₁ (fun _ => .TraceAgrees L_tgt prog obs))
    (hUnit : finTot.R ())
    (c_model : Q_mod → Claim .InfiniteLanguage)
    (isRealTime : Q_mod → Prop)
    (hasEpsilon : Q_mod → Prop)
    (hPart : ∀ m : Q_mod, True → isRealTime m ∨ hasEpsilon m)
    (hMeta : A₂ → Denote (.TraceAgrees L_tgt prog obs) →
                  ∀ m : Q_mod, isRealTime m → Denote (c_model m)) :
    CoveredJustification Q_mod .InfiniteLanguage (A₁ ∧ A₂) c_model :=
  liftScope finTot () hUnit (fun _ => True) isRealTime hasEpsilon ⟨hMeta⟩ hPart

/-- Сильная теорема честной границы Gate 13 (закрывает прямой обход `bridgeComplete`):
    если в `Q_mod` существует модель `m₀` с ε-переходами, для которой утверждение `c_model m₀`
    не следует из посылок `A₁ ∧ A₂` (`¬ Denote (c_model m₀)` при `A₁ ∧ A₂`),
    то `TotalJustification Q_mod .InfiniteLanguage (A₁ ∧ A₂) c_model` на всём `Q_mod`
    НЕ СУЩЕСТВУЕТ В ПРИНЦИПЕ (нельзя собрать даже напрямую в обход `bridgeComplete`). -/
theorem gate12_13_epsilon_blocks_any_total {Q_mod : Type}
    {A₁ A₂ : Premise}
    (c_model : Q_mod → Claim .InfiniteLanguage)
    (hEpsCounter : ∃ m₀ : Q_mod, A₁ ∧ A₂ ∧ ¬ Denote (c_model m₀)) :
    ¬ ∃ tot : TotalJustification Q_mod .InfiniteLanguage (A₁ ∧ A₂) c_model,
        tot.R = (fun _ => True) := by
  rcases hEpsCounter with ⟨m₀, hA₁, hA₂, hNot⟩
  exact pointwise_unproved_blocks_any_total (fun _ => True) ⟨m₀, trivial, ⟨hA₁, hA₂⟩, hNot⟩

/-! ## §7b. Операторы Meta-Synset (Proj/Split/Freeze) и единая развилка Ось 1 ↔ Ось 2 -/

/-- Минимальное состояние операнда `M_t` с аксиомой анти-вырождения (`2 ≤ domainCount`) -/
structure MetaOperand (Branch : Type) where
  domainCount : Nat
  antiDegen   : 2 ≤ domainCount
  candidates  : List Branch
  nonEmpty    : 0 < candidates.length

/-- `Proj`: проекция в новый домен увеличивает `domainCount` и добавляет кандидатов -/
def metaProj {Branch : Type} (m : MetaOperand Branch) (newBranches : List Branch) :
    MetaOperand Branch where
  domainCount := m.domainCount + 1
  antiDegen   := Nat.le_trans m.antiDegen (Nat.le_succ _)
  candidates  := m.candidates ++ newBranches
  nonEmpty    := by
    rw [List.length_append]
    exact Nat.lt_of_lt_of_le m.nonEmpty (Nat.le_add_right _ _)

/-- `Freeze`: фазовый переход в необратимо замороженное меню `FrozenMenu` (остаток `gap` не теряется) -/
def metaFreeze {Branch : Type} (m : MetaOperand Branch) (log : RawLog) : FrozenMenu Branch where
  frozenAt := log
  branches := m.candidates
  nonEmpty := m.nonEmpty

theorem metaFreeze_preserves_candidates {Branch : Type}
    (m : MetaOperand Branch) (log : RawLog) :
    (metaFreeze m log).branches = m.candidates ∧ 0 < (metaFreeze m log).branches.length :=
  ⟨rfl, m.nonEmpty⟩

/-- Единая развилка двух осей (связка Оси 1 и Оси 2 в одном типе выбора):
    - `EscalateAxis1Memory`: пространство версий пусто (`VersionSpaceEmpty`), переключаем класс памяти
      и выбираем ветвь по `SymbolLift` (`Gain_min = 1`);
    - `EscalateAxis2Port`: пространство версий не сжимается из-за калибровочной эквивалентности
      (`GaugeConflict`), поэтому расширение языка внутри того же порта заблокировано,
      и контроллер обязан сменить порт / перейти к алгебре вмешательств. -/
inductive TwoAxisAction where
  | EscalateAxis1Memory (chosen : MemBranch)
  | EscalateAxis2Port   (reason : String)

structure TwoAxisEvidence {Prog : Type} (L : ObjLang Prog) (D : RawLog) where
  axis1Refuted  : Prop
  axis2Gauge    : Prop
  disjointCause : ¬ (axis1Refuted ∧ axis2Gauge) -- в фиксированном контексте либо |V| = 0, либо |V| > 1

def chooseConditionalTwoAxisAction {Prog : Type} (L : ObjLang Prog) (D : RawLog)
    (ev : TwoAxisEvidence L D)
    [Decidable ev.axis1Refuted] : TwoAxisAction :=
  if _ : ev.axis1Refuted then .EscalateAxis1Memory (.CanonicalQueue id)
  else .EscalateAxis2Port "GaugeNonIdentifiableOnCurrentPort"

/-- Условная теорема двухосевого контроллера:
    при постулированной несовместимости причин (`ev.disjointCause`) и наличии
    калибровочной неидентифицируемости (`ev.axis2Gauge`) контроллер
    направляет ревизию в Ось 2 (`EscalateAxis2Port`), блокируя слепую эскалацию памяти. -/
theorem conditional_two_axis_routing_blocks_spurious_memory_escalation {Prog : Type}
    (L : ObjLang Prog) (D : RawLog)
    (ev : TwoAxisEvidence L D)
    [Decidable ev.axis1Refuted]
    (hGauge : ev.axis2Gauge) :
    ∃ msg, chooseConditionalTwoAxisAction L D ev = .EscalateAxis2Port msg := by
  unfold chooseConditionalTwoAxisAction
  split
  · rename_i hRef
    exact False.elim (ev.disjointCause ⟨hRef, hGauge⟩)
  · exact ⟨_, rfl⟩

/-! ## §8. Проверка аксиом ядра Lean 4.36.0 -/

#print axioms EpistemicRevisionV2.claim_distinct_not_reusable
#print axioms EpistemicRevisionV2.nonempty_gap_blocks_total
#print axioms EpistemicRevisionV2.pointwise_unproved_blocks_any_total
#print axioms EpistemicRevisionV2.composeCoverage_gap_empty_iff
#print axioms EpistemicRevisionV2.judgement_sound
#print axioms EpistemicRevisionV2.restriction_sound
#print axioms EpistemicRevisionV2.finiteCheck_blocks_universal
#print axioms EpistemicRevisionV2.refutation_blocks_extended
#print axioms EpistemicRevisionV2.versionSpaceEmpty_monotone
#print axioms EpistemicRevisionV2.stepBranch_order_probe_splits
#print axioms EpistemicRevisionV2.stepBranch_fails_without_binPreserving
#print axioms EpistemicRevisionV2.stepBranch_fails_without_injectiveBin
#print axioms EpistemicRevisionV2.metaFreeze_preserves_candidates
#print axioms EpistemicRevisionV2.conditional_two_axis_routing_blocks_spurious_memory_escalation
#print axioms EpistemicRevisionV2.gate12_13_epsilon_blocks_any_total

end EpistemicRevisionV2
