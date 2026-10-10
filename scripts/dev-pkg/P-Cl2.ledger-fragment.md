## P-Cl2 — PREPARED Clean claims, wrappers and growth (2026-10-10)

Base: d34509a2 on sleep-pcl2. Apply this block in the serial ledger window.
P-Cl2 is PREPARED, not CLOSED. No shared ledger, inventory, facade, S-Ap record,
P-Cl1 core, Shared proof, Outage/Export or Claims/Outage file was edited.

- P10/P11: Claims/Clean uses approved D018–D021. History has confirmed-reader
  ordering, enabled nonempty gates, joined transfer, and current-epoch saved and
  fast-write origins. Durable leases and S origins still span past epochs.
- Clean/Export takes CleanCutSet. Its zero lane adapts the compiled zero body:
  impossible pre-zero gate origins discharge the new enabled/epoch obligations.
  A private copy of the exact zero adapters compiles and passes strict audits.
  The production module remains EXPECTED-FAIL because of its P-Cl1 imports.
- P7/P20: clean_growth_body consumes the recurrence's joined proposer, including
  its restart cutoff. Trigger readers and deadline readers have separate scopes.
  The deadline remains t + G + 6 * Δ. Compatibility plus no-future gives strict
  growth at the trigger; scoped inclusion gives the deadline conclusion.
- Internal statement, exact true sleep form: clean_growth_body replaces the old
  all-honest inclusion/monotonicity route with explicit proposal compatibility at
  the trigger and scoped inclusion at the deadline. These are internal supplier
  inputs, not new public CleanGrowthClaim premises. Consumer: Outage/Export.
  P-Ou/assembly must prove these inputs before closing the public growth exporter.
  Scoped inclusion and scoped monotonicity alone do not cover a trigger reader
  that sleeps at the deadline. No endpoint-reader implication is assumed.

### Exact handoff to sole editor P-Ou

1. Claims/Outage: replace AvailableGrowthConcl by approved packet D026 (P20):
   its first output quantifier is `∀ x, confirmedReader p c E rho x t → ...`;
   its second is `∀ x, confirmedReader p c E rho x d → ...`.
   Keep the proposal, time and getter binders and CleanGrowthClaim unchanged.
2. Outage/Export: replace the clean-growth call by
   `clean_growth_body E rho G ΔF hset hcompatible hinclusion hrec hgap t ht hhor`.
   Both inputs have the exact types printed in Outage/Growth.lean:24 and :31.
   Prove hcompatible from the Clean/proposal chain suppliers; prove hinclusion
   from the scoped clean_inclusion_body. Do not add either to CleanGrowthClaim.
   An exact internal exporter with both inputs is in the P-Cl2 report.
3. Clean-history projection consumers: use confirmed-reader ordering, enabled
   nonempty gates, joined transfer, and restartFree plus activeCompatible for
   saved-cache retention. Use hset.sleepPre.sleepPre for the sleep cut.
4. Before CLOSED, supply the actual compatibility proof, scoped inclusion proof,
   P-Ou consumer build, and strict audit; a conditional wrapper is only PREPARED.

### Inputs still needed for closure

- P-Cl1 must close TransferFrame, StepGate, Transfer, Closure and Safety. The
  unfolded history/truncation/gate/safety body types must match D018–D021.
- S-Ap must close its receipt record and audit/facade. Claims/Tests/Axioms:678
  currently omits the new anchor/readiness inputs; this is a supplier port item.
- Count still forces dl(anchor) = dl(send). Wake 24, old acceptance 8, Δ = 2
  cannot meet deadline 10. The current S-Ap record is unchanged. No false old
  deadline is supplied. Wait for the anchor-relative design and caller ports.
- P-ShA round 6 RegimesService is absent at the base. No sleep consumer may use
  a legacy regime service by fabricating NoRestart; use its _on form at closure.
- The lead applies this ledger block and the audit fragment in the serial window,
  then rebuilds Clean/Export and checks canonical audits before CLOSED.

Approved public meaning changes beyond the packet: none. Public STOPs: none.
