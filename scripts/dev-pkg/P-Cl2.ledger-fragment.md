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
   Both inputs have the exact types printed in Outage/Growth.lean:23 and :30.
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
  passes Recovery₂ to KernelACSideClaim_W, which now needs RecoverySleep₂.
  This is a S-Ap/P-Fi finality test supplier port item.
- Count still forces dl(anchor) = dl(send). Wake 24, old acceptance 8, Δ = 2
  cannot meet deadline 10. The current S-Ap record is unchanged. No false old
  deadline is supplied. Wait for the anchor-relative design and caller ports.
- P-ShA round 6 RegimesService is absent at the base. No sleep consumer may use
  a legacy regime service by fabricating NoRestart; use its _on form at closure.
- The lead applies this ledger block and the audit fragment in the serial window,
  then rebuilds Clean/Export and checks canonical audits before CLOSED.

Approved public meaning changes beyond the packet: none. Public STOPs: none.

P-Ou sole-editor handoff. No P-Ou file was edited.

Replace only AvailableGrowthConcl in Claims/Outage with the approved P20 form:

```lean
def AvailableGrowthConcl (t d : Time) : Prop :=
  ∃ s B,
    t < V2.D.proposalTime (fgsaInterface p c) s ∧
    HonestProposal E rho (fgsaInterface p c) s B ∧
    ∀ g ∈ [(fgsaInterface p c).stable,
           (fgsaInterface p c).confirmed],
      (∀ x, confirmedReader p c E rho x t →
        Block.Prec (V2.D.outputAt E rho g x t) B) ∧
      (∀ x, confirmedReader p c E rho x d →
        Block.Preceq B (V2.D.outputAt E rho g x d))
```

Replace the clean-growth exporter with this exact conditional internal supplier form.
Keep the public CleanGrowthClaim binders unchanged. Prove both suppliers from the
ported Clean/proposal/inclusion cores before CLOSED. Their proof remains open.

```lean
theorem outage_cleanGrowthClaim_of (p : Params)
    (hcompatible : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (ΔF : Time),
      CleanSet p c E rho ΔF →
      ∀ s B, HonestProposal E rho (fgsaInterface p c) s B →
      SA.gateTime p.toParams s ≤ rho.horizon →
      ∀ u x g, 0 ≤ u → u < V2.D.proposalTime (fgsaInterface p c) s →
        confirmedReader p c E rho x u →
        g ∈ [(fgsaInterface p c).stable, (fgsaInterface p c).confirmed] →
        Block.Compatible (V2.D.outputAt E rho g x u) B)
    (hinclusion : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (ΔF : Time),
      CleanSet p c E rho ΔF →
      ∀ s B, HonestProposal E rho (fgsaInterface p c) s B →
      SA.gateTime p.toParams s ≤ rho.horizon →
      ∀ u x g, SA.gateTime p.toParams s ≤ u → u ≤ rho.horizon →
        confirmedReader p c E rho x u →
        g ∈ [(fgsaInterface p c).stable, (fgsaInterface p c).confirmed] →
        Block.Preceq B (V2.D.outputAt E rho g x u)) :
    CleanGrowthClaim p := by
  intro G ΔF V _ _ In c E rho t hset hrec hgap ht hhor
  exact clean_growth_body E rho G ΔF hset
    (hcompatible c E rho ΔF hset) (hinclusion c E rho ΔF hset) hrec hgap t ht hhor
```

Use the current Growth module. Its join guard comes from hrec, including hjoined.2.2.
Use the sleep cut hset.sleepPre.sleepPre in the remaining Clean-history callers.
Use the approved scoped ordering, enabled gate, joined voter and epoch projections.

### Prepared validation

- P-Cl2 DCK PASS: 466 GREEN, 8 EXPECTED-FAIL; default negative controls PASS.
- GREEN lake build --wfail PASS. Strict audits: 38 roots, 2799 results.
- Exact four-definition audit, three zero adapters and P-Ou handoff audit PASS.
- Complete green-root exports: 95 proof modules, 250 exports, 0 unaccepted.
- Layers: 72 baseline findings, 0 new. Approved-form comparison PASS.
- Clean/Export EXPECTED-FAIL: Shared/Regimes and P-Cl1/TransferFrame suppliers.
- Diff and all changed-file line lengths PASS. CLOSED remains open.
