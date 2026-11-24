# v2.6.1 corrected editorial edition / Исправленная редакция / 修订版

The three editions correct the abstract, §5.2, the statement and scope note for H12 in §6, and the limitations in §7. The clamped port model, the freely evolving ether orbit, and the port transfer eligibility record are distinct. The free-ring trajectory is a separate finite check; it is not a new Lean theorem. H11 tests three specified environment records and does not derive autonomy of the free ring. H12 retains the two-tick return in the clamped model and the separate deadline-3 witness. An anomaly signal is not a repair certificate.

The published Lean and Python evidence are unchanged. The old Lean comment on `etherAutomaton` describing two seven-cycles does not describe the implemented map. Its actual cycles are `(0000)`, `(1000)`, `(0100,1100)`, `(0111,1101)`, and `(0010,0110,1110)`. The remaining seven states are transient. Verify the figures with `python3 check_ether_orbit.py`. The standalone deadline selector is a feasibility rule on nonempty candidate sets, not a budget or information-gain optimizer.

Compile each TeX source twice with XeLaTeX and the Noto fonts. The corrected papers retain the version of the unchanged formal artifacts and are marked as a corrected edition, not as a new formal release.
