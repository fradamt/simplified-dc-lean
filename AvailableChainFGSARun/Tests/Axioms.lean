module

/-! Kernel dependency audit of the FG-SA run library (plan
`docs/plans/2026-09-29-fgsa-composition-t7-t1.md`, T7.1): one `#print axioms`
line for each public theorem and each E5 value of the library. Each line
prints only `propext`, `Classical.choice`, `Quot.sound`, or no axiom.
`scripts/CheckFGSARunAxioms.lean` checks every constant of the library
mechanically. T7.1 adds no declaration, so this file has no line yet. -/
