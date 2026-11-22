# Proof-Carrying Discovery

**Can a program make its next search easier by remembering a useful rule—and show why that rule is valid?**

Small, reproducible experiments in **program synthesis, invariant inference, and causal attribution**, within the InvariantNet research project.

**English** · [Русский](#русский)

**Read the preprint:** [English PDF](PREPRINT_v1.1.en.pdf) · [English Markdown](PREPRINT_v1.1.en.md) · [Русский PDF](PREPRINT_v1.1.ru.pdf) · [Русский Markdown](PREPRINT_v1.1.ru.md)

**New formal supplement (22 Nov 2026):** [English — Lean theorems and verification](docs/FORMAL_RESULTS.en.md) · [Русский — формальные результаты](docs/FORMAL_RESULTS.ru.md) · [Lean source](formal/) · [verification receipts](formal/verification/). The original v1.1 preprints and Python results are preserved unchanged. The formal supplement proves a bounded-DFA witness theorem and a concrete three-control-state 1-DCA separation, not automatic invention of a new memory architecture.


**Aleksandr Strand · Software v1.1.1 · 22 November 2026**

## The idea in plain language

A program can solve a problem by trying many possible solutions. After it succeeds, it can save the solution as a shortcut. It can also learn a rule about that shortcut: which expressions mean the same thing, or which relationship remains true as the program runs.

Those are different kinds of knowledge. A shortcut can make a solution shorter. A rule can help the search avoid trying the same idea in several forms. Adding too many shortcuts can also make search slower, because there are more choices to examine.

This project asks three practical questions:

1. **What did the system actually learn?** A reusable program, a mathematical rule, or both?
2. **Did that knowledge help?** Repeat the search with different discoveries enabled, including the work required to acquire them.
3. **When should the system use a more capable representation?** Require evidence that the current, explicitly bounded class cannot solve the task.

The search code stays fixed. What changes is the knowledge available to it and the search options that knowledge supports.

## Two experiments

### 1. Learning a shortcut—and rules for using it

The first experiment builds tiny circuits that work with bits, `0` and `1`.

It starts with one operation, **NAND**, which returns `0` only when both inputs are `1`. It then searches for a circuit implementing **XOR**, which returns `1` when two inputs differ. Saving that circuit creates a reusable shortcut, called a *macro*.

The system also checks algebraic rules, such as swapping XOR's inputs without changing the answer, regrouping nested XOR operations, and cancelling two identical inputs. These rules let it skip equivalent expressions during later searches.

The experiment repeats all **eight combinations of three acquisition events**: learning the NAND rule, building the XOR macro, and learning XOR's rules. Each combination starts again from NAND alone. XOR's rules can be used only after XOR has been acquired.

The follow-up tasks ask whether three or four bits contain an odd number of `1`s, and whether three bits are all `1` (`AND3`). The XOR shortcut helps with parity, but can burden the search for AND3. Its rules can reduce that burden.

To assign credit, the experiment uses **Shapley values**: it averages how much each discovery changes the result across the different combinations. The score includes acquisition and subsequent search under an explicit cost model. It is not a count of how often a shortcut appears in the final answer.

### 2. Learning a counting program—and explaining it

The second experiment recognizes strings such as `01$`, `0011$`, and `000111$`: some zeros, followed by the same number of ones, then an end marker `$`.

The system first considers a **finite-state machine** with at most five states. Distinguishing examples prove that this limit is insufficient. The engine then searches a predefined class of machines with an integer counter. It fills an initially empty transition table to construct the program.

An **invariant** is a relationship that remains true while a program runs. Here the program's counter has a simple meaning:

- While reading zeros, `counter = zeros seen`.
- While reading ones, `counter = zeros seen − ones seen`.

The system derives these coefficients from the synthesized transitions, within a specified two-phase linear template, and checks the required conditions. The invariant is an explicit output, alongside the program and its evidence.

For a second task—one more `1` than `0`, as in `00111$`—the learned counting pattern reduces the search:

| Task | Explored search branches |
|---|---:|
| Equal numbers of zeros and ones | 26 |
| One extra one, without the transferred rule | 57 |
| One extra one, with the transferred rule | 28 |

The last comparison is about **2.04× fewer search branches**, not a measured wall-clock speedup. A deliberately wrong transferred rule is also tested: if the restricted search fails to produce a certifiable program, the engine retries without the restriction.

The finite-state evidence establishes that **five states are insufficient**. For an arbitrary unknown target, that evidence alone does not rule out every larger finite-state machine. The counter representation is available in advance; the system selects it rather than inventing a new memory architecture.

## What “proof-carrying” means here

A result comes with more than an answer: the repository records the generated program, the inferred relationship, its assumptions, and evidence that can be checked.

Depending on the experiment, that evidence includes complete Boolean truth tables, distinguishing suffixes for a state lower bound, checks of transition conditions, and an exact comparison of two explicitly given finite-state machines. Separate tests check observable behavior against reference implementations.

These are **Python checks within stated models, together with the paper's mathematical arguments**. This release is not a Lean or Coq formalization, a general invariant prover, or a demonstration of independence from arbitrary architectures and encodings. The paper states these boundaries explicitly.

## How to read the measurements

The Boolean experiment records candidate evaluations, normalization calls, law checks, and verification work separately. Its default score gives each counted operation one modeled unit and includes the cost of acquiring knowledge. Acquisition is charged once for the three-task sequence.

Under that convention, the XOR macro has a **negative Shapley contribution on AND3** (approximately `−0.868` natural-log units, or *nats*). Across the full three-task sequence, the contributions of the NAND rule, XOR macro, and XOR rules are approximately `+0.546`, `+1.925`, and `+0.442` nats, respectively. These values belong to this experiment and cost model; they are not seconds or universal values of the discoveries.

An unsolved task receives an explicit 200,000-unit penalty for its base search component. Acquisition and normalization are accounted for separately. The penalty does not mean a solution was found at step 200,000. Alternative normalization weights and full event histories are included in the [Boolean results](v1_1/abc_historical_v1_1_results.json).

## Run it yourself

The experiments and their checks require **Python 3.10 or later**, using only the standard library. No training data download, API key, or package installation is required.

```bash
git clone https://github.com/Dnarts/proof-carrying-discovery.git
cd proof-carrying-discovery
python3 tests/audit_release.py
```

The audit runs the tests, reruns both experiments, compares deterministic results with the saved reports, and checks file hashes. A successful run prints a JSON report with `"status": "PASS"`.

To run either experiment separately and inspect a fresh JSON report:

```bash
python3 v1_1/dfa_to_1dca_v1_1.py
python3 v1_1/abc_historical_v1_1.py
```

Runtime and platform metadata can differ between machines. The audit compares the deterministic fields separately from that metadata.

The PDFs are ready to read. The optional `build_preprints.py` rebuilds them locally from Markdown using Pandoc, ReportLab, Matplotlib, Pillow, and DejaVu fonts. These document tools are separate from the experiments' Python-only requirements.

## Where to look

| File or directory | What it contains |
|---|---|
| [English preprint](PREPRINT_v1.1.en.md) / [Russian preprint](PREPRINT_v1.1.ru.md) | Definitions, arguments, results, limitations, and references |
| [`v1_1/`](v1_1/) | Current experiment code and saved JSON results |
| [`tests/`](tests/) | Reference checks, negative controls, and the release audit |
| [`FIXES.md`](FIXES.md) | What the v1.0 audit found and how the revised release addresses it |
| [`legacy/`](legacy/) | Preserved v1.0 code, results, and audit history |
| [`history/`](history/) | Exact v1.1.0 archive preserved before the publication patch |
| [`MANIFEST.json`](MANIFEST.json) / [`SHA256SUMS.txt`](SHA256SUMS.txt) | File identities and integrity checks |

Version v1.1 was prepared after auditing v1.0; it is not a preregistered experiment. Original v1.0 artifacts are preserved. The v1.1.1 publication patch strengthens certificate checking while retaining the reported experimental results. The next research step is to recover equivalent invariants across different representations and explicitly verify the transformations between them.

## Related research

This work is part of a series of questions: **what can influence a result, what can be recovered from an observation, what should be remembered, and when a stored rule helps a later search**.

- [Rule 110 dependency fronts](https://github.com/Dnarts/rule110-dependency-fronts) studies which initial cells can affect a target, and related questions about observation and retained memory.
- [Channel topology and memory](https://github.com/Dnarts/channel-topology-and-memory) studies information, memory, and preserving distinctions useful for a decision.

These are conceptual connections between separate studies. This repository's experiments use Boolean circuits and automata; they do not execute inside Rule 110, and they do not inherit a formal verification result from the other repositories.

## Citation and license

Please cite **Aleksandr Strand**, the preprint, and the exact software version or commit used. Machine-readable citation metadata is in [`CITATION.cff`](CITATION.cff). This is a working preprint; no DOI is claimed.

See [LICENSE](LICENSE) for the repository's MIT license.

---

# Русский

**Может ли программа облегчить следующий поиск, запомнив полезное правило, и показать, почему это правило верно?**

Небольшие воспроизводимые эксперименты по **синтезу программ, выводу инвариантов и причинной атрибуции** в рамках исследовательского проекта InvariantNet.

**Препринт:** [English PDF](PREPRINT_v1.1.en.pdf) · [English Markdown](PREPRINT_v1.1.en.md) · [Русский PDF](PREPRINT_v1.1.ru.pdf) · [Русский Markdown](PREPRINT_v1.1.ru.md)

**Aleksandr Strand · Версия программы v1.1.1 · 22 ноября 2026**

## Идея простыми словами

Программа может решить задачу, перебрав множество вариантов. После этого она может сохранить решение как готовую подпрограмму. А ещё — найти правило: какие выражения дают одинаковый результат или какое соотношение сохраняется во время работы программы.

Это разные виды знания. Готовая подпрограмма позволяет записать решение короче. Правило помогает не проверять одну и ту же идею в нескольких формах. Но слишком большая библиотека подпрограмм может замедлить поиск: выбирать приходится из большего числа вариантов.

В этой работе проверяются три вопроса:

1. **Что именно приобрела система?** Готовую программу, математическое правило или и то и другое?
2. **Помогло ли это знание?** Для ответа поиск повторяется с разными разрешёнными открытиями, включая затраты на их получение.
3. **Когда нужно перейти к более выразительному представлению?** Для перехода требуется свидетельство, что текущий класс с явно заданным ограничением недостаточен.

Код поиска остаётся фиксированным. Меняется доступное ему знание и то, какие варианты поиска оно позволяет использовать.

## Два эксперимента

### 1. Найти подпрограмму и правила её использования

Первый эксперимент собирает маленькие схемы, работающие с битами `0` и `1`.

Исходный набор содержит одну операцию — **NAND**. Она возвращает `0`, только когда оба входа равны `1`. Из неё система строит схему **XOR**, которая возвращает `1`, когда два входа различаются. Сохранённая схема становится готовой подпрограммой — *макросом*.

Затем система проверяет алгебраические правила: входы XOR можно переставлять, вложенные операции — перегруппировывать, а два одинаковых входа — сокращать. При следующих поисках эти правила позволяют пропускать эквивалентные выражения.

Эксперимент повторяет все **восемь сочетаний трёх событий приобретения**: найти закон NAND, построить макрос XOR и найти законы XOR. Каждое сочетание начинает заново, имея только NAND. Законы XOR доступны только после приобретения самого XOR.

Следующие задачи — определить, нечётно ли число единиц среди трёх или четырёх битов, и проверить, равны ли все три бита единице (`AND3`). Макрос XOR помогает с чётностью, но может усложнять поиск AND3. Его законы способны уменьшить этот штраф.

Для распределения вклада используются **значения Шепли**: усредняется, насколько каждое открытие меняет результат при разных сочетаниях остальных открытий. Оценка учитывает приобретение знаний и последующий поиск в явно заданной модели затрат. Она отличается от простого подсчёта вызовов подпрограммы в итоговом решении.

### 2. Найти программу со счётчиком и объяснить её работу

Второй эксперимент распознаёт строки вроде `01$`, `0011$` и `000111$`: сначала несколько нулей, затем столько же единиц, затем маркер конца `$`.

Система сначала рассматривает **конечный автомат** не более чем с пятью состояниями. Различающие примеры доказывают, что этого ограничения недостаточно. Тогда движок переходит к заранее доступному классу автоматов с целочисленным счётчиком. Программа строится заполнением исходно пустой таблицы переходов.

**Инвариант** — это соотношение, которое сохраняется во время работы программы. В этом примере смысл счётчика прост:

- Пока читаются нули: `счётчик = число прочитанных нулей`.
- Пока читаются единицы: `счётчик = число прочитанных нулей − число прочитанных единиц`.

Система выводит коэффициенты этих равенств из найденных переходов в заданном двухфазном линейном шаблоне и проверяет необходимые условия. Инвариант становится явным результатом работы вместе с программой и свидетельствами её проверки.

Для второй задачи — единиц на одну больше, чем нулей, как в `00111$` — найденное правило счёта сокращает поиск:

| Задача | Проверено ветвей поиска |
|---|---:|
| Нулей и единиц поровну | 26 |
| Одна лишняя единица, без переноса правила | 57 |
| Одна лишняя единица, с переносом правила | 28 |

В последнем сравнении ветвей поиска **примерно в 2,04 раза меньше**. Это не измеренное ускорение по физическому времени. Отдельно проверяется заведомо неверное перенесённое правило: если ограниченный поиск не даёт программы, проходящей сертификацию, движок повторяет поиск без этого ограничения.

Конечное свидетельство устанавливает, что **пяти состояний недостаточно**. Для произвольного неизвестного языка оно само по себе не исключает все более крупные конечные автоматы. Представление со счётчиком задано заранее: система выбирает его, но не изобретает новую архитектуру памяти.

## Что здесь означает «proof-carrying»

Результат содержит больше, чем готовый ответ: сохраняются найденная программа, выведенное соотношение, его предпосылки и проверяемые свидетельства.

В зависимости от эксперимента это полные булевы таблицы истинности, различающие суффиксы для нижней границы числа состояний, проверки условий переходов или точное сравнение двух явно заданных конечных автоматов. Отдельные тесты сопоставляют наблюдаемое поведение с эталонными реализациями.

Это **проверки на Python внутри указанных моделей вместе с математическими аргументами статьи**. Данная версия не является формализацией в Lean или Coq, универсальным доказателем инвариантов или демонстрацией независимости от произвольных архитектур и кодировок. Эти границы явно указаны в препринте.

## Как читать измерения

Булев эксперимент раздельно считает оценки кандидатов, вызовы нормализатора, проверки законов и работу по верификации. В основной модели каждая учитываемая операция стоит одну условную единицу; приобретение знаний также оплачивается. Для последовательности из трёх задач стоимость приобретения учитывается один раз.

При такой конвенции макрос XOR имеет **отрицательный вклад Шепли на AND3**: примерно `−0,868` единицы натурального логарифма, или *ната*. Для полной последовательности трёх задач вклады закона NAND, макроса XOR и законов XOR составляют примерно `+0,546`, `+1,925` и `+0,442` ната. Эти числа относятся к данному эксперименту и модели затрат; они не измеряются в секундах и не являются универсальной ценностью открытий.

Если задача не решена, её базовой поисковой составляющей присваивается явный штраф 200 000 условных единиц. Приобретение и нормализация учитываются отдельно. Штраф не означает, что решение найдено на шаге 200 000. Другие веса нормализации и полные истории событий доступны в [результатах булева эксперимента](v1_1/abc_historical_v1_1_results.json).

## Как запустить

Для экспериментов и проверок нужен **Python 3.10 или новее**, только стандартная библиотека. Скачивать обучающие данные, получать API-ключ или устанавливать дополнительные пакеты не требуется.

```bash
git clone https://github.com/Dnarts/proof-carrying-discovery.git
cd proof-carrying-discovery
python3 tests/audit_release.py
```

Аудит запускает тесты, повторяет оба эксперимента, сравнивает детерминированные результаты с сохранёнными отчётами и проверяет хеши файлов. Успешный запуск выводит JSON-отчёт с `"status": "PASS"`.

Для отдельного запуска экспериментов и просмотра нового JSON-отчёта:

```bash
python3 v1_1/dfa_to_1dca_v1_1.py
python3 v1_1/abc_historical_v1_1.py
```

Время выполнения и сведения о платформе могут различаться между компьютерами. Аудит проверяет детерминированные поля отдельно от этих метаданных.

PDF уже готовы для чтения. Дополнительный скрипт `build_preprints.py` пересобирает их локально из Markdown с помощью Pandoc, ReportLab, Matplotlib, Pillow и шрифтов DejaVu. Эти инструменты сборки документов не нужны для экспериментов и их проверок на Python.

## Где что находится

| Файл или каталог | Содержание |
|---|---|
| [Английский препринт](PREPRINT_v1.1.en.md) / [Русский препринт](PREPRINT_v1.1.ru.md) | Определения, аргументы, результаты, ограничения и литература |
| [`v1_1/`](v1_1/) | Текущий код экспериментов и сохранённые результаты JSON |
| [`tests/`](tests/) | Эталонные проверки, отрицательные контроли и аудит выпуска |
| [`FIXES.md`](FIXES.md) | Что обнаружил аудит v1.0 и как это учтено в исправленной версии |
| [`legacy/`](legacy/) | Сохранённые код, результаты и история аудита v1.0 |
| [`history/`](history/) | Точный архив v1.1.0, сохранённый до публикационной правки |
| [`MANIFEST.json`](MANIFEST.json) / [`SHA256SUMS.txt`](SHA256SUMS.txt) | Идентичность файлов и проверки целостности |

Версия v1.1 подготовлена после аудита v1.0; это не предварительно зарегистрированный эксперимент. Исходные артефакты v1.0 сохранены. Публикационная правка v1.1.1 усиливает проверку сертификатов; приведённые результаты экспериментов сохраняются. Следующий исследовательский шаг — получать эквивалентные инварианты в разных представлениях и явно проверять преобразования между ними.

## Связанные исследования

Работа входит в серию вопросов: **что может повлиять на результат, что можно восстановить по наблюдению, что следует сохранять в памяти и когда сохранённое правило помогает следующему поиску**.

- [Rule 110 dependency fronts](https://github.com/Dnarts/rule110-dependency-fronts) исследует, какие исходные клетки способны повлиять на целевую, а также связанные вопросы наблюдения и сохраняемой памяти.
- [Channel topology and memory](https://github.com/Dnarts/channel-topology-and-memory) исследует информацию, память и сохранение различий, полезных для принятия решения.

Это смысловые связи между отдельными исследованиями. Эксперименты данного репозитория используют булевы схемы и автоматы; они не исполняются внутри Rule 110 и не наследуют формальную верификацию из других репозиториев.

## Цитирование и лицензия

При цитировании указывайте **Aleksandr Strand**, препринт и точную версию программы или использованный коммит. Машиночитаемые сведения находятся в [`CITATION.cff`](CITATION.cff). Это рабочий препринт; наличие DOI не заявляется.

Репозиторий распространяется по лицензии MIT: [LICENSE](LICENSE).
