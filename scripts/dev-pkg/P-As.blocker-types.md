# P-As Round 7 — current blocker types

Base: da788502, branch sleep-pas7. Full P-As and full Root acceptance remain OPEN.
P-H1 production and P-Ou exporters are CLOSED on this base. P-H2 is not CLOSED.
This register replaces the Round 6 requests. Evidence: .lake/sleep-pas-r7/.
Paths below start with AvailableChainFGSAProofs/Proofs/ unless stated otherwise.
No public Claims/Statements definition or family source changes in this round.

## Closed requests

OU-CONT and OU-CLOSE are CLOSED. Assembly/Outage:15 constructs
assembly_outage_clean_cut_supplier from the actual HealthyPrefixSleep₂, FaultQ,
FGFoundation and SrcFrameAboveStmt. Each record field has a Clean producer:
clean_invariant, cleanState_of_hist, clean_gateOutput_body, cleanHistoryAt_body
and clean_epoch_saved_row. Root:158 uses the exact Round 15 exporter call.
The old W-seed input is absent. Continuation reads use the amended
OutageRepairReady qualification already on this base; Join and FGSAClaims are unchanged.

Assembly/Outage:268/:275/:281 use outage_outageCompatClaim_of and its true/false
projections. The four foundation/Clean suppliers are named producers. The retained
CleanCutClaim wrapper argument is already proved by fgsa_cleanCutClaim; it is not
an open request. Assembly/Outage and Tests/OutageExport build with --wfail.
Tests/OutageContinuationAxioms and the P-H1 NonVacuity/HealingRun fixture also build.

FAST, Clean state/safety, joined continuation replay, inclusion and growth remain
closed. Root:77 now uses fgsa_finalizedMonotonicityRestartClaim for the existing
FinalizedMonotonicityRestartClaim field. The legacy NoRestart producer is not used.

## H1-PERM-ROUTE — exact lane-boundary request, P-H2

Healing/RecoveryPerm:15 already proves healing_tPerm_recovery. Its inputs are
RecoverySleep₂, RMonoAll, RXing and the actual last-write origin. It takes no
phase-service factory. Assembly/ResetArrival:37 supplies these inputs from
HealingSet, fgsa_rMonoAll, fgsa_rXing and fgsa_leaseOrigins_lastWrite.
Assembly/Healing:50 uses the same producer for promotion.

Healing/Export does not yet expose RecoveryPerm. Add its public import there,
or expose the exact existing theorem through that Export. P-As keeps the Export
route and adds no direct Assembly-to-Healing leaf import or layer exception.
The exact assembly_healing_tPerm_of_set body passes with the lower P-H1 imports.
This is a route request, not an open P-H1 permanence proof.

## PROMOTION-JST — exact named producer request, P-H2

Healing/PromotionRenewed:20 healing_renewedPromotion must compile with
RecoverySleep₂ and RMonoAll and supply the current RenewedPromotionConcl domain.
The current body still states GST <= u and imports the failing Promotion:194.
The public conclusion starts at recoveryStart p E. Keep its three deadlines.
The existing Healing/Export:31 wrapper must also use RecoverySleep₂ for hperm;
a Recovery₂-only caller cannot construct the restart cutoff.

Assembly/Healing:17 proves assembly_healing_proposal_service from the actual
emission, post-GST anchor, finite deadline, compatible receiver floor, history
and local restart epoch. No proposal-service record remains as an Assembly input.
The row receipt, progress coverage/fold, FaultQ and quorum inputs have named
Foundations/Finality/Shared producers. The full promotion module remains OPEN.
After P-H2 ports the named body to Jst, P-As removes the old GST conversion at
its call if the producer's telescope then requires Jst directly.

## HG5-JST — exact selected search request, P-H2

Assembly/ResetArrival:50 healing_resetArrival consumes the smallest existing HG.5
result. :63 healing_frontierSearch_of_set is an explicit result adapter, not a producer.
The :70 search factory is passed through the existing reset and H-time callers.
The exact obligation for each actual healing run is:

```lean
(c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
(hset : HealingSet p c E rho G ΔF) (hbound : LivenessBoundW p ΔF) :
  FrontierSearchStatement p c E rho G ΔF
```

Healing/FrontierSearchFull:19 healing_frontierSearch is the named P-H2 endpoint.
P-H2 must construct its held-witness, repair, opening and frontier services at
Jst. The current GST-wide RepairServiceScopes and OpeningServiceScopes are not
accepted as Assembly inputs. A scope conversion or the :63 adapter is not a producer.
P-H1 permanence and selected P1-P10 services are available; higher service assembly
and HG.5 remain P-H2 work. No all-TF, all-node prior join or pre-GST service is added.

## FULL-H0-JST — exact selected extension request, P-H2

Assembly/ResetArrival:574 assembly_resetArrivalFull_of_extension composes the
reset-only statement and this explicit obligation at the selected witness:

```lean
p.δt = 2 * p.R →
∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
  (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
  HealingSet p c E rho G ΔF → LivenessBoundW p ΔF →
  ∀ w, H0Reset p c E rho w →
  p.actionTime w.rStar + Γ p G + 4 * p.Δ ≤ rho.horizon →
  ∃ u Q, H0 p c E rho {w with u := u, QStar := Q}
```

The adapter keeps rStar and the strict arrival bound at recoveryStart. Its body
passes. Healing/PostResetHealed:135 healing_h0_of is the existing completion
consumer. P-H2 must supply its real reset carrier from the current all-cut proof.
The extension is an exact result request; no carrier or scope record is assumed.

## INPUT-JST — exact selected input requests, P-H2

Assembly/ResetArrival:600 assembly_hTimeClaim_of_reset_input takes the full-reset
statement and HealingInputOfH0Statement. Healing/Time:12 defines the latter with
the actual Jst full-reset horizon. P-H2 must produce it, with this exact result:

```lean
p.δt = 2 * p.R →
∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
  (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
  HealingSet p c E rho G ΔF → LivenessBoundW p ΔF →
  recoveryStart p E + B'_resetF p ΔF G + Γ p G + 4 * p.Δ ≤ rho.horizon →
  ∀ w, H0 p c E rho w →
    HealingInput p c E rho w ΔF ∧
      tstar p w ≤ p.actionTime w.rStar + Γ p G + 4 * p.Δ
```

For the public input claim, Assembly/ResetArrival:608
assembly_healingInputClaim_of_input uses the smaller local-horizon obligation:

```lean
p.δt = 2 * p.R →
∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
  (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
  HealingSet p c E rho G ΔF → LivenessBoundW p ΔF →
  ∀ w, H0 p c E rho w → tstar p w ≤ rho.horizon → HealingInput p c E rho w ΔF
```

Both inputs are explicit lemma arguments. No record field or full reset budget is
added to the local input claim. The adapters pass with the unchanged public types.
Healing/HealingInputExport and the post-reset producers remain P-H2-owned.

## POST-RESET — exact all-cut step requests, P-H2

The existing conditional chains retain these literal step inputs under HealingSet
and the actual H0Reset witness. The all-cut family API port is still open:

```lean
∀ i, PostResetResetLeaseStep p c E rho w i
∀ i, PostResetLeaseStep p c E rho w i
∀ i, PostResetRawStep p c E rho w i
∀ i, PostResetConeStep p c E rho w i
```

Definitions: Healing/PostResetJoint:70/:78/:87 and PostResetJoint2:37.
Named producer targets: PostResetRawStep:1103 postReset_resetLease_succ',
PostResetLeaseStep:1594 postReset_leaseSafe_succ,
PostResetRawStep:1073 postReset_rawTransfer_succ, and
PostResetCone:69 healing_postReset_coneStep. Their run adapters in Assembly remain
unvalidated through Healing.Export. They are not reported as closed producers.
P-H2 must port the old RMono and last-write consumers to RMonoAll and joined writes.
No whole-run NoRestart follows from the sleep suffix. PostResetTHigh:146 still
projects removed base.noRestart; PostResetH2Prime:281/:287 still drops reader scopes.
These are owner source repairs, not valid input requests to P-As.

## Root and fixture ports — P-As after the P-H2 return

Root's seven exact ready bodies include fgsaClaims_of_open, fgsaClaims_of_hTime,
FGSASafetyClaims, both explicit-HTime continuation helpers, and the companion.
They are checked separately; this does not replace a Root module build.
The unconditional Root endpoints still require a real HTimeClaim producer.
The old healing_hTimeClaim route is now conditional on HG.5 and also needs the
current post-reset family APIs. P-As must wire the returned HG.5/full-H0/input
producers at the Root call and port its actual test callers before acceptance.

The actual Root importer build fails in P-H2 AttemptStop, Promotion, PhaseBoot,
PhaseSettle, Repair, FrontierSeed, FrontierServiceGate, FrontierServiceSupport,
OpeningServiceGate, PostResetTHigh and PostResetH2Prime. Full modules stay EXPECTED-FAIL.

Local fixture ports remain P-As work: NonVacuity/Adversarial:3559 has the old Base₂
constructor; :1889-1891 and :2981-2983 use initialAt for restart stores. HealingPackages
and HealingReset still need current wake-time restore calls and assembly input adapters.
Tests/HealingHTime must pass the exact new search request. No positive fixture is
weakened or removed. P-H1's HealingRun now builds and remains unchanged here.
Bare P23, G-S2, final regeneration and deferred initialAt cleanup remain OPEN.

## Explicit input audit

Proved: local proposal service, finite Clean supplier, reset source names and the
Jst reset/H-time arithmetic. Named producers: Foundation channels, crossing,
last-write origins, rows, coverage/fold, quorum, FAST and P-H1 universal permanence.
Exact P-H2 obligations: HG.5, the selected full-H0 extension, bounded full-H0 input,
local input and current post-reset step APIs. These use the actual finite sleep-run
premises and unchanged joined-start endpoints. No forbidden universal service record,
whole-run NoRestart, future delivery, early join or phase-service factory is supplied.
All new adapter bodies retain their true scoped inputs; no conditional check closes
an unproduced family result. Full healing assembly and Root acceptance stay OPEN.

## Final manifest result

The required full script FAILS at the inherited legacy snapshot entry
AvailableChain.KitFG.pins. Its type is unchanged. Its descriptive Trees 3a label
now says "unsaved joined gate" and "joined tick"; the checked legacy snapshot
still has the earlier text. Pins.lean, the snapshot and extractor are unchanged
since da788502. This is a lead/P-Da serial snapshot item, not a P-H2 proof failure.
No snapshot or checker is changed to hide it. The exact diagnostic is saved in
.lake/sleep-pas-r7/legacy-pin-diff.log and legacy-pin-scope.log.

The current FG-SA shallow and deep checks PASS: 1,358 entries in 59 modules;
1,358 deep roots and 3,818 dependency nodes. Separate V2, Generic and Compose
snapshot checks PASS. The separate Claims check is EXPECTED-FAIL through P-H2:
Healing/Promotion.olean is missing after its source fails at Promotion:194.
All public Claims source prerequisites do build. The full manifest script stops
before its snapshot controls; the 24 standalone DCK controls do PASS.
Evidence: manifest-final.log, manifest-v2.log, manifest-gen.log,
manifest-compose.log, manifest-claims-final.log and manifest-claims-prereqs-final.log.
