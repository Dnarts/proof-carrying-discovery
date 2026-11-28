import Release

/-- Closed reference examples, not a generic untrusted proof loader. -/
def renderNats (xs : List Nat) : String := String.intercalate "," (xs.map toString)
def renderMap (v : CRTT.Release.MapView) : String :=
  renderNats v.worlds ++ "|" ++ renderNats v.ports ++ "|" ++ renderNats v.actions

def main : IO Unit := do
  for (label,s) in CRTT.Release.Witnesses.reports do
    IO.println ("T32|" ++ label ++ "|" ++ s.terminal ++ "|" ++ toString s.spent ++ "|" ++ toString s.balance ++
      "|" ++ toString s.funds ++ "|" ++ toString s.remainingJobs ++ "|" ++ toString s.upgradeCount ++
      "|" ++ toString s.paidUpgrades ++ "|" ++ toString s.acceptedUpgrades ++ "|" ++ toString s.certificates.length ++
      "|" ++ toString s.finishBill ++ "|" ++ toString s.episodeEvents.length)
    IO.println ("T32STATUS|" ++ label ++ "|" ++ s.episodeStatus)
    for v in s.upgradeStatuses do
      IO.println ("T32UPGRADE|" ++ label ++ "|" ++ v)
    for v in s.episodeEvents do
      IO.println ("T32EVENT|" ++ label ++ "|" ++ v)
    for v in s.relativeJournal do
      IO.println ("T32JOURNAL|" ++ label ++ "|" ++ v)
    for v in s.searchReceipts do
      IO.println ("T32SEARCH|" ++ label ++ "|" ++ reprStr v.kind ++ "|" ++ toString v.fee)
    for v in s.initialCertificates do
      IO.println ("T32PRIOR|" ++ label ++ "|" ++ renderMap v)
    for v in s.certificates do
      IO.println ("T32CERT|" ++ label ++ "|" ++ renderMap v)
    IO.println (reprStr s)
