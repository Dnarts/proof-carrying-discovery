# Gate 11–12 Final Verified Bundle v12.3 (Pure Lean 4.36.0 + Causal Chomsky Escalation + Universal `∀ m, ¬1-DCA(m)` & Parametric DPDA Meta-Theorem)

**Статус:** `LEAN4_VERIFIED_CHOMSKY_ESCALATION_PASS` (`Lean 4.36.0`, `arm64-apple-darwin`, 0 `sorry`/`admit`/`axiom`, `LEAN_EXIT_CODE: 0` по всем Lean-модулям).

## Закрытые методологические границы (v12.3)

1. **Универсальное разделение классов для любого числа состояний/фаз ($\forall m \in \mathbb N,\ \neg\operatorname{1-DCA}(m)$ и $\forall k \in \mathbb N,\ \neg\operatorname{DFA}(k)$):**
   В `gate12_hierarchy_checker.lean` и `gate12_exported_pal_mid.lean` доказаны теоремы `canonicalMidDPDA_not_1DCA` (`exportedStackProg_not_1DCA`) и `canonicalMidDPDA_not_DFA` (`exportedStackProg_not_DFA`): через экспоненциальную оценку $2^{2m+2} \ge 2 + m(2m+3)$ установлено, что **ни один $m$-фазный односчётчиковый автомат ни для какого $m \in \mathbb N$** (и ни один $k$-состоянийный DFA ни для какого $k \in \mathbb N$) не может распознать синтезированный DPDA на $\Sigma^*$.
2. **Параметрическая мета-теорема бесконечной корректности без ручных шаблонов индукции (`checkFullChomskyProtocol_sound`):**
   Любой синтезированный `P : StackProgram 2`, проходящий вычислимую проверку `isCanonicalMidDPDA P f && (f sym0 != f sym1)` одной тактикой `by decide`, автоматически получает полное доказательство на бесконечном домене:
   $$\forall w \in \Sigma^*,\ P.\text{eval}(w) = \text{true} \iff \exists u \in \{0,1\}^*,\ w = u \mathbin{+\!\!+} [\#] \mathbin{+\!\!+} (u.\text{map } f)^R.$$
   Продемонстрировано сразу на **двух** независимо синтезированных вслепую задачах в одном файле:
   - **Задача A (`exportedStackProg`):** палиндромы с центральным маркером $u \# u^R$ ($f = \text{id}$),
   - **Задача B (`exportedAntiStackProg`):** анти-палиндромы битового дополнения $u \# \overline{u}^R$ ($f(0)=1, f(1)=0$).
3. **Сертифицированная причинная хронология эскалации ($0 < t_1 < t_2 \le |\text{obs}|$):**
   Чекер `checkCausalEscalation_sound` проверяет внутри Lean 4, что Уровень 1 (`DFA 3`) опровергнут на строгом историческом префиксе `obs.take t1` ($t_1 = 9$), Уровень 2 (`CounterProgram 2`) — на историческом префиксе `obs.take t2` ($t_2 = 54$), и только после этого принят автомат Уровня 3 (`StackProgram 2`) на всей истории `obs`.

## Состав комплекта (10 файлов)

1. `gate11_soundness.lean` + `gate11_lean_verification.log` — 5 теорем (`dfa_runFrom_append`, `pigeonhole_fin`, `myhill_nerode_impossibility`, `oneDCA_0n1n_not_regular`, `oneDCA_0n1n_eq_true_iff`); аксиомы `[propext, Quot.sound]`.
2. `gate11_trace_checker.lean` + `gate11_trace_checker_verification.log` — сертифицированный верификатор конечных трасс Gate 11 (`checkMNCert_sound`, `checkDFATrace_sound`, `checkCounterTrace_sound`, `checkEscalatedTrace_sound`, `sample_0n1n_certified_corollary`); аксиомы `[propext, Quot.sound]`.
3. `gate12_hierarchy_checker.lean` — ядро 3-уровневой причинной эскалации Хомского (`DFA → 1-DCA → DPDA`) с параметрической мета-теоремой бесконечной спецификации и универсальным разделением классов (`checkMNCert_sound`, `check1DCACert_sound`, `checkCausalEscalation_sound`, `canonicalMidDPDA_eval_eq_true_iff`, `canonicalMidDPDA_not_1DCA`, `canonicalMidDPDA_not_DFA`, `checkFullChomskyProtocol_sound`).
4. `gate12_blind_chomsky_escalation.py` — слепой синтезатор (3 встроенных теста: `0^n 1^n`, `u # u^R`, `u # flip(u)^R`) с записью причинной хронологии $0 < t_1 < t_2 \le |\text{obs}|$ и автоэкспортом в Lean 4.
5. `gate12_exported_pal_mid.lean` + `gate12_lean_verification.log` — автоэкспортированные трассы и доказательства для задач A и B, машинно верифицированные в Lean 4.36.0 (12 теорем).
6. `gate12_final_manifest.json` — контрольные суммы SHA-256 всех файлов комплекта.

## Воспроизведение

```bash
./run_gate12_verification.sh
```
