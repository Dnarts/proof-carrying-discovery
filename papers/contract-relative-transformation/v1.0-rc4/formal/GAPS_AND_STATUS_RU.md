# Границы свидетельств и пробелы

## Текущий принятый стек

Для T19–T32 сохранены исходный принятый ZIP, все 144 канонических файла, полный успешный Lean 4.36.0-журнал, агрегат и 21 лог по модулям. Повторный аудит дал PASS: 542 точных цели, соответствие модульных логов полному журналу и девять CLI-сценариев. Все 45 новых Python-команд завершились с кодом 0.

Исторический runner exit=127 относится к первоначальной среде подготовки. Пользователь сообщил о последующем запуске; предоставленный журнал содержит успешные компиляционные статусы и финальную отметку PASS. Факт отдельного нового запуска не подтверждён независимо: полный журнал побайтово совпадает с frozen-свидетельством, а отдельного внешнего process-exit receipt нет. При согласующей пересборке Lean не запускался. Подробности: [VERIFICATION_RU.md](VERIFICATION_RU.md), машинный статус — [catalog/VERIFICATION.json](catalog/VERIFICATION.json).

## Ранняя нумерация

Индивидуальная первичная спецификация не найдена для T01, T02 и T04–T13. Эти 12 номеров сохранены с незаполненной доказательной привязкой. Тематические ориентиры указаны только как неподтверждённая поздняя реконструкция. Содержательные формальные результаты раннего ядра отдельно сохранены в catalog/EARLY_ARCHITECTURE.json / unnumbered_core.

## Выявленные исторические границы

### H02

Прямые связи номера и формального содержания найдены только для T03,T14,T15,T16,T17,T18.

Для остальных двенадцати номеров сохранён пробел и отдельно неподтверждённое ретроспективное имя.

- [canonical/ARCHITECTURE_RU.md](canonical/ARCHITECTURE_RU.md)
- [history/T03-T19/CRTT-T03-T19-v0.1.1/SufficientPartitions.lean](history/T03-T19/CRTT-T03-T19-v0.1.1/SufficientPartitions.lean)
- [history/T01-T18/CRTT-v0.2/CumulativeDiscovery.lean](history/T01-T18/CRTT-v0.2/CumulativeDiscovery.lean)
- [history/documents/951ca8989fe24ca7--README.md](history/documents/951ca8989fe24ca7--README.md)
- [history/documents/0227e00743cbc817--README.md](history/documents/0227e00743cbc817--README.md)

### H03

Verified T17/T18 заменяют исходные модули и не содержат их README; исходные README не описывают тождественные тексты.

Опубликованный журнал относится только к конкретным verified SHA.

- [history/T01-T18/CRTT-T17-v0.1/OnlineDiscovery.lean](history/T01-T18/CRTT-T17-v0.1/OnlineDiscovery.lean)
- [history/referenced-sources/2a21ca02c93f08aa/CRTT-T17-v0.1/OnlineDiscovery.lean](history/referenced-sources/2a21ca02c93f08aa/CRTT-T17-v0.1/OnlineDiscovery.lean)
- [history/T01-T18/CRTT-T18-v0.1/ObservationValue.lean](history/T01-T18/CRTT-T18-v0.1/ObservationValue.lean)
- [history/referenced-sources/5ca9e3cf2f157b04/CRTT-T18-v0.1/ObservationValue.lean](history/referenced-sources/5ca9e3cf2f157b04/CRTT-T18-v0.1/ObservationValue.lean)
- [history/documents/951ca8989fe24ca7--README.md](history/documents/951ca8989fe24ca7--README.md)
- [history/documents/0227e00743cbc817--README.md](history/documents/0227e00743cbc817--README.md)

### H04

T18 policy_attains в verified версии доказывает точечное существование действия, а не глобальную вычислимую argmin-политику.

Упоминание argminPolicy в T03 README оставлено неподтверждённым; глобальный draft не повышен до verified.

- [history/T01-T18/CRTT-T18-v0.1/ObservationValue.lean](history/T01-T18/CRTT-T18-v0.1/ObservationValue.lean)
- [history/referenced-sources/5ca9e3cf2f157b04/CRTT-T18-v0.1/ObservationValue.lean](history/referenced-sources/5ca9e3cf2f157b04/CRTT-T18-v0.1/ObservationValue.lean)
- [history/T03-T19/CRTT-T03-T19-v0.1.1/README.md](history/T03-T19/CRTT-T03-T19-v0.1.1/README.md)

### H05

T18 adaptive_beats_fixed в verified версии — арифметика констант 2<3<4, без семантики мультиплексора.

Семантический адаптивный гейт относится к последующему T19, а не к этой числовой теореме.

- [history/T01-T18/CRTT-T18-v0.1/ObservationValue.lean](history/T01-T18/CRTT-T18-v0.1/ObservationValue.lean)
- [history/referenced-sources/5ca9e3cf2f157b04/CRTT-T18-v0.1/ObservationValue.lean](history/referenced-sources/5ca9e3cf2f157b04/CRTT-T18-v0.1/ObservationValue.lean)
- [history/T03-T19/CRTT-T03-T19-v0.1.1/AdaptiveObservation.lean](history/T03-T19/CRTT-T03-T19-v0.1.1/AdaptiveObservation.lean)

### H06

Фраза no theorem in this release depends on Classical.choice в verified CRTT-v0.2 README шире доступных audit reports; core явно использует Classical.choice/choose.

Без-выборный статус отнесён только к перечисленным проверенным новым целям, не ко всему старому core.

- [history/T01-T18/CRTT-v0.2/CRTTCore.lean](history/T01-T18/CRTT-v0.2/CRTTCore.lean)
- [history/T01-T18/CRTT-v0.2/README.md](history/T01-T18/CRTT-v0.2/README.md)
- [originals/supplied_logs/crtt_kernel_audit_20261127_154921.log](originals/supplied_logs/crtt_kernel_audit_20261127_154921.log)

### H07

Ранний runner имеет set -u без set -e/pipefail и без записи индивидуальных exit codes.

Есть исторический transcript с OK и axiom reports, но финальное DONE само по себе не является строгим aggregate PASS.

- [history/T01-T18/run_crtt_kernel_audit.sh](history/T01-T18/run_crtt_kernel_audit.sh)
- [originals/supplied_logs/crtt_kernel_audit_20261127_154921.log](originals/supplied_logs/crtt_kernel_audit_20261127_154921.log)

### H08

Полный kernel transcript T03 не включён в отдельный 7-файловый verified ZIP.

Статус компиляции T03 подтверждён описанием в README, а не отдельным предоставленным полным stdout/stderr.

- [history/T03-T19/CRTT-T03-T19-v0.1.1/README.md](history/T03-T19/CRTT-T03-T19-v0.1.1/README.md)
- [history/T03-T19/CRTT-T03-T19-v0.1.1/run_verify.sh](history/T03-T19/CRTT-T03-T19-v0.1.1/run_verify.sh)
- [history/T03-T19/CRTT-T03-T19-v0.1.1/FINITE_CHECK.log](history/T03-T19/CRTT-T03-T19-v0.1.1/FINITE_CHECK.log)

### H09

Verified T18 Python не перечисляет все политики для проверки decomposition; он вычисляет саму слойную формулу.

Счётчик T18.1 нельзя называть независимой проверкой глобального minimax attainment.

- [history/T01-T18/CRTT-T18-v0.1/check_observation.py](history/T01-T18/CRTT-T18-v0.1/check_observation.py)
- [history/T01-T18/CRTT-T18-v0.1/FINITE_CHECK.log](history/T01-T18/CRTT-T18-v0.1/FINITE_CHECK.log)
- [history/documents/0227e00743cbc817--README.md](history/documents/0227e00743cbc817--README.md)

### H10

HISTORY_T01_T18.zip — точная копия 044615… (CRTT-v0.2/T17/T18), а не восемнадцать самостоятельных пакетов.

Название вложенного архива не доказывает полноту исторической нумерации.

- [canonical/HISTORY_T01_T18.zip](canonical/HISTORY_T01_T18.zip)
- [originals/archives/CRTT-T17-T18-v0.1.2-verified.zip](originals/archives/CRTT-T17-T18-v0.1.2-verified.zip)

### H11

Внешнее имя CRTT-T03-T19-v0.1.2-verified.zip содержит внутреннюю папку CRTT-T03-T19-v0.1.1; это сохранённое имя папки, не отдельная стадия.

Версию и происхождение устанавливать по SHA, а не только имени корня.

- [originals/archives/CRTT-T03-T19-v0.1.2-verified.zip](originals/archives/CRTT-T03-T19-v0.1.2-verified.zip)
- [history/T03-T19/CRTT-T03-T19-v0.1.1/README.md](history/T03-T19/CRTT-T03-T19-v0.1.1/README.md)

## Сохранённые статусы исходных документов

Оригинальные README/ARCHITECTURE/RELEASE_ACCEPTANCE содержат статусы времени подготовки соответствующего кандидата. Финальный статус определяется актом FREEZE и точным успешным журналом, а новые конечные проверки — отдельной папкой evidence/recheck. Сохранение старого документа не означает принятия каждого его исторического утверждения.

## Полнота файлового среза

Все 54 доступных CRTT ZIP-файла, найденные по именам в каталоге, включены. Три пары совпадающих ZIP-байтов сохранены под их исходными именами; уникальных SHA — 51. Это полный найденный файловый срез, а не утверждение о восстановлении несохранённых разговоров или отсутствовавших сертификатов.
