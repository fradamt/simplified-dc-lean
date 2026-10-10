# P-As Round 1 handoff

Base: a395a69d. Branch: sleep-pas1. Full assembly is OPEN.
A GREEN module is a build result. It does not close a conditional family supplier.

## Ready bridges

- Shared/CatchUp:416 supplies `fgsa_target_service_genesis`. Finality assembly passes it.
- Assembly/Foundations:11 supplies `assembly_sleep_channels p c E rho` with type
  `RStoreDurable ∧ RStoreEpoch ∧ RMonoAll ∧ RFrameNextEpoch` at the same run.
- Assembly/Foundations:19 supplies `assembly_rows_of_healingSet p c E rho h` with type
  `TRows p c E rho ΔF`. Its `receipt` field is the H2 row-service supplier.
- Assembly/ProgressAttempt:45 supplies `healing_progressAttemptStatement p G ΔF rows`.
  Its result is `ProgressAttemptStatement p G ΔF`. Its input is
  `ProgressAttemptRows p G ΔF`; H2 must supply the four budget rows.
- Assembly/ResetSource:11 supplies `assembly_reset_emittedName p c E rho hb ha he`.
  It keeps the source, height/root, gate result, source prefix below the result, and fast key.
  This small module builds without the unfinished Healing export.

Paths above start with `AvailableChainFGSAProofs/Proofs/`.

## Exact owner requests

P-H2, Tests/HealingAttempt:505: pass `rows : ProgressAttemptRows p G ΔF` before `hδ`.
The field producers are Healing/AttemptRows:502/:536/:268/:338:
`healing_attempt_raise_contest`, `healing_attempt_raise_other`,
`healing_attempt_firstRow_contest`, and `healing_attempt_firstRow_other`.
Supply all four fields. Do not replace the input with
an assumed complete `ProgressAttemptStatement`. The four proofs remain H2-owned.

P-H2, Tests/HealingReset:25/:83: the checked early source supplier is
`assembly_reset_emittedName`, in Assembly/ResetSource:11. Its complete telescope is the
same as `healing_reset_emittedName` in Assembly/ResetArrival:19. The latter module still
imports unfinished H1/H2 proofs. Full reset arrival and H-time remain OPEN.

P-H1/P-H2, Healing/AttemptSettle:13/:15 and AttemptRows:206: use `RMonoAll` and the
exact held-target service below. The all-run monotonicity producer is checked in
Assembly/Foundations. The held-target producer remains a family obligation.

```lean
∀ i (ev : V2.Event V (Obj p)) x W y,
  rho.events[i]? = some ev → x ∈ rho.honest → y ∈ rho.honest →
  E.t_GST ≤ ev.time → W ∈ (storeAt p c E rho (i + 1) x).fg.TF →
  ev.time + p.Δ ≤ rho.horizon →
  TargetReceiptService E rho (eraseFG W) (ev.time + p.Δ) y
```

TVOTE-CUT supersedes the unrestricted FinalityVoteReceipts supplier request.
S-Ap's public TVote text and P-Fi's internal record, adapters, and exports are DONE
at 4a42c596. Finality/Export:19 proves `fgsa_kernelACSide_W p : KernelACSideClaim_W p`
without a supplier. Assembly/Finality consumes these revised exports without hR.
Keep both public per-read GST cutoffs:

```lean
-- Proposal read:
E.t_GST ≤ slotStartZ p (((v - 1 : Slot) : Int) - 1)
-- Action read:
E.t_GST ≤ slotStartZ p (((r * p.R + 1 : Slot) : Int) - 1)
```

P-Fi, ReceiptSuppliers:267: the checked held-target helper has an actual tick, original
stored block, public anchor, strict GST cutoff, horizon, and finality guard. It does not
supply the unrestricted event-index contract above by a type conversion.

P-Ou, OutageContinuation/Export:35: port `outageV_body` to the callback of
Shared/Claims.outageContinuation_of_body at :499. Pass the exact public Clean products:
`SourceDisciplineAt`, `CleanHistoryAt`, `CleanTruncAt`, and
`OutageContinuationSleepPrem`. Keep `fast`, `T`, `b₀`, and `b₁` in the conclusion.
There is no unguarded saved-row or all-node output projection in this callback.
The continuation body proof remains P-Ou-owned.

P-WC, WeakContinuation/ExactProposal:39 and Inclusion:131: return joined read forms with
`RestartsAtWakes`, receipt roots, durable store, local stamps, and all-run FG bounds.
Current forms still require `NoRestart` and awake vote cardinality. P-As does not edit them.

P-WC/P-As, Assembly/WeakContinuationGrowth:351/:519/:572: T02 now takes the actual joined
reader and supplies its awake tick. The remaining admission receipt port is OPEN.
T03 still needs the full current-epoch service producer. Its old original-gate tick route
is OPEN and must be replaced; it is not GREEN evidence. Keep all-time joined participation
until the intermediate gate actor is selected. Keep independent later confirmed readers.

P-WC/P-As, Assembly/WeakContinuationGrowthSeed:306/:313/:328/:332: consume restart-aware
occurrence replay. Assembly/ContinuationReplay has a checked tick proof at phase-zero
wakes. Its actual Export import is blocked by P-WC, so the module remains EXPECTED-FAIL.
The proof was checked against the prepared Replay module, with a strict axiom command.
Row/action replay and the empty-suffix consumer still need P-WC's returned export types.
Do not add a continuation participation premise to the empty-suffix route.

P-Fx/P-As, Inhabit/WeakContinuationWitness:131 and WeakContinuationW1:1860:
the old source has horizon 247, but the current sleep endpoint is 253.
SleepPositive.old_w1_endpoint_gap proves the mismatch. The generator is unchanged.
Full W1 execution, receipt-root constructors, and RowPermission consumers remain OPEN.

S-Ap/lead, Claims/Statements/ComposeStmt:161/:182: reset statement bounds still use GST,
while the package fields and H0 reset use recoveryStart. The packet gives no exact
replacement text for these two statement names. No new public meaning is installed here.
Return the intended exact statement after the family proof or scope check.

## Packet and serial records

D040 in the approved packet explicitly changes AvailableGSTClaim and
AvailableGrowthGSTClaim to recoveryStart. This round applies that missing text in
Claims/Claims/Outage:212/:228. No compatibility, inclusion, or receipt premise is added.
All other public FGSAClaims definitions are unchanged.

Apply P-As.audit-fragment.txt to the existing Proofs.Tests.Axioms key, and
P-As.inhabit-audit-fragment.txt to the existing Inhabit.Tests.Axioms key at serial join.
P-As.coverage-fragment.txt keeps those existing keys. P-As.ledger-fragment.md records
this slice. P-As.facade-fragment.txt lists the new production imports for final join.
The genesis strict command and coverage row are already installed as item 0 requires.

## initialAt cleanup order

Keep initialAt until the live restart consumers are repaired.

1. Inhabit/WeakContinuationW1:106–108/:1185–1187: replace the old initial-store restart
   branches with kept-store and replay proofs. The generic signature invariant needs
   retained proposal HEAD provenance; clearing a pool does not prove that provenance.
2. Proofs/Tests/NonVacuity/Adversarial:1889–1891/:2981–2983: repair the same consumers.
3. FGSA/Proofs/StoreInv:185, Metadata:279, LeaseOutput:25, and
   FGSARun/Proofs/AncestorDeadlinesStore:48: remove obsolete initialAt helpers only after
   all consumers above build.
4. FGSA/Model/Store:56: remove initialAt last. Update its existing audit rows at serial join.

No initialAt definition or helper is deleted in this round.
