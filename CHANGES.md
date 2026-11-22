# CHANGES: statement changes

Log new findings or changes to Theorem 1's statement here first, then update `RimRule/Defs.lean`.

## 2026-11-21: initial statement
- `Defs.lean` follows the council part-2 note §5, with the referee fixes. Theorem 1(b) uses the core hypotheses (H1ₘ, H2ₘ, H5′, H6, H7, F_A) plus H3 and H4, with σ_i ≠ ∅. The stimulus space X is arbitrary.

## 2026-11-22: Theorem 1(b) conclusion strengthened
- `Theorem1b` now concludes `¬ IsOpenConvex C ∧ ¬ IsClosedConvex C` (was `¬ IsOpenConvex C`), as in the council note §5 (b). Hypotheses unchanged. The closed half follows from Theorem 1(a) because H4 implies F_B (`fB_of_h4`). The old statement is kept as `theorem1b_open`. Referee DEF_CHECK.md F5.
