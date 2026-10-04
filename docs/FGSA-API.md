# FG-SA API manifest

_Baseline for G-F0a (D15, lead ruling DC 2026-09-30)._

This file lists every public declaration under the Statements prefixes of
`AvailableChainFGSA`, `AvailableChainFGSARun` and `AvailableChainFGSAClaims`,
by fully qualified name and grouped by library and module. FGSA has no anchor rule.

## Baseline rule

Before G-F0a, a missing doc makes the check print SKIP and exit 0. F0 writers
do not update this doc. At G-F0a, run `bash scripts/fgsa-freeze.sh` to write
this doc, copy it to `docs/FGSA-API-frozen.md`, and record the frozen SHA-256
in `scripts/fgsa-manifest-frozen.sha256`. From G-F0a the API is append-only.
Every frozen entry must keep its kind and hash; new entries pass. A changed
or removed entry needs an allow line in `scripts/fgsa-manifest-allow.txt`:
`<name>\t<reason>\t<plan revision>`, with actual tabs and no empty field.
Stale allow lines fail. Structure widening has no exception: put later fields
in new structures.

## ROOT-DIGEST W1c class exception

The [Gen exception list](GEN-API.md#root-digest-option-3-exception) names all four frozen walk
entries and their kernel evidence under plan r2.1 and r2.2. No frozen FG-SA walk entry needs a
new premise. The non-frozen `AvailableChain.FGSA.fgsa_headInTree_reanchor_of_pivot` now takes
root uniqueness on its arbitrary `tree`. CStoreInv supplies this for each erasedList view.
The census is `.lake/rdw1c-census.md`. FGSAClaims fields and Base₂ text are unchanged by W1c.
The FG-SA manifest tool remains blocked by the W3 `AvailableChainFGSA.Tests.Support` fixture.
No generated FG-SA entry, frozen baseline, SHA, or allow policy is changed here.

## ROOT-DIGEST W2b D1 exception

Plan r2.3 permits `AvailableChain.FGSA.Run.CPPrefix` and `CPPrefix_def` to take
`RootBlockInRun p c E rho (eraseFG B)` after honest membership. EntryBelow is unchanged.
CPPrefix now quantifies over run blocks only. Evidence:
`TS/codex/reports/rdigest/w2/rdw2/cp-prefix-stop.lean`:
"counterexample to the local inference only". This is not a full-run claim counterexample.

## How to check

`scripts/V2Manifest.lean` generates and checks this list.

- `lake env lean --run scripts/V2Manifest.lean --scope fgsa --list` prints
the module blocks from the environment, in source order, with hashes.
- `lake env lean --run scripts/V2Manifest.lean --scope fgsa --write` writes this doc.
- `lake env lean --run scripts/V2Manifest.lean --scope fgsa --check` checks
the names, modules, kinds, hashes and completeness (D15), then the frozen
SHA-256 and append-only rule. A failed check exits 1.
- `--manifest <path>`, `--frozen <path>`, `--allow <path>` and
`--frozen-sha <path>` override the paths. `--anchor` requires v2.

Each entry hash uses the shared hash rules in `scripts/V2Manifest.lean`:
types and definition values, generated or private helpers in the closure,
type binder names and infos, reducibility, and instance status. Theorem
proofs do not affect the hash. Public `_def` theorems are entries. Each public
structure projection is a separate `field` entry beside the structure entry.

## `AvailableChainFGSA`

### `AvailableChainFGSA.Statements.FinalityView`

```text
def AvailableChain.FGSA.finalityView f86cac6f46832901
theorem AvailableChain.FGSA.finalityView_def 1defbcb125e22963
```

### `AvailableChainFGSA.Statements.Invariants`

```text
inductive AvailableChain.FGSA.Reachable 13b25b25971926ea
ctor AvailableChain.FGSA.Reachable.init f111928ba979b940
ctor AvailableChain.FGSA.Reachable.tick 055be03180266adb
ctor AvailableChain.FGSA.Reachable.deliver 1b5692ec4652dffd
def AvailableChain.FGSA.NestOK 5136fd2b21a203a6
def AvailableChain.FGSA.SACompat f3b6ab178b996afd
def AvailableChain.FGSA.LeaseBelowOutputStore 5c59d0a0978e86ea
theorem AvailableChain.FGSA.LeaseBelowOutputStore_def 124f6f13f65f43ca
def AvailableChain.FGSA.FastOrigin 55103ff0d11f32d6
structure AvailableChain.FGSA.CStoreInv cb980d5cc624cc81
ctor AvailableChain.FGSA.CStoreInv.mk 80616cb5ab152e78
field AvailableChain.FGSA.CStoreInv.fg c1deb7786fb3d7eb
field AvailableChain.FGSA.CStoreInv.rootInj bb704c9e61292aff
field AvailableChain.FGSA.CStoreInv.baseTree 8f80f2a9339f7579
field AvailableChain.FGSA.CStoreInv.saCompat bb90981a09bbbfcf
field AvailableChain.FGSA.CStoreInv.Smem fe9debf2b9b49454
field AvailableChain.FGSA.CStoreInv.fastOrigin 1c55ea1227a90e90
field AvailableChain.FGSA.CStoreInv.fastDom da8e022726d41a63
field AvailableChain.FGSA.CStoreInv.genuineKeys 5c02221cb2f7be5e
field AvailableChain.FGSA.CStoreInv.leaseKeys a50343d2d48f081c
def AvailableChain.FGSA.Inv0 943f6078f8c70340
structure AvailableChain.FGSA.MetaInv 254adc80bd0e3cfc
ctor AvailableChain.FGSA.MetaInv.mk 5e10e9e659a8da86
field AvailableChain.FGSA.MetaInv.wireTree 1cfadccb15838efd
field AvailableChain.FGSA.MetaInv.treeWire 83c16a8b186ecb00
field AvailableChain.FGSA.MetaInv.proposalsNodup 56bdbbf7a844777c
field AvailableChain.FGSA.MetaInv.stampKeys a2c8134234c8b054
field AvailableChain.FGSA.MetaInv.blocksNodup 275ee1602c689a2b
field AvailableChain.FGSA.MetaInv.poolDecodes b9d50981a2f0470c
field AvailableChain.FGSA.MetaInv.poolNodup e3d5e55df701b574
field AvailableChain.FGSA.MetaInv.noGenesisWire 831cfbb328685b16
def AvailableChain.FGSA.ContentAgree 9f1216009903713b
```

### `AvailableChainFGSA.Statements.Store`

```text
def AvailableChain.FGSA.OutputNestingStored 1885b00da7e09524
def AvailableChain.FGSA.StoreInvariant 0e07dc5ec27ec206
structure AvailableChain.FGSA.StoreBundle 92284a770a6a9997
ctor AvailableChain.FGSA.StoreBundle.mk cd437ca8fc0bb474
field AvailableChain.FGSA.StoreBundle.cstore d5eb7d4836683d23
field AvailableChain.FGSA.StoreBundle.meta 7f6556246d926935
field AvailableChain.FGSA.StoreBundle.nest f8e6a3828a9e0452
field AvailableChain.FGSA.StoreBundle.lease e12331fd86652837
def AvailableChain.FGSA.StoreBundleInvariant 730551da289ae6f5
theorem AvailableChain.FGSA.StoreBundleInvariant_def 83f08bfde256b019
def AvailableChain.FGSA.FMonotone 13987992597d4f8f
def AvailableChain.FGSA.MetadataInvariant 791aba803df12f4f
```

### `AvailableChainFGSA.Statements.WindowCertificate`

```text
def AvailableChain.FGSA.Window.projectFinality ba05ae418852b5ca
theorem AvailableChain.FGSA.Window.projectFinality_def 73cc801dfe20c6b2
def AvailableChain.FGSA.Window.projectCertEntry e041d7ad22bd1ba7
theorem AvailableChain.FGSA.Window.projectCertEntry_def 25fe0f85797c49a3
def AvailableChain.FGSA.Window.certificateHeight a0b51be547ad4981
theorem AvailableChain.FGSA.Window.certificateHeight_def 9f9b71d4b7a068b3
def AvailableChain.FGSA.Window.certificateFinality d481ba15c7e37159
theorem AvailableChain.FGSA.Window.certificateFinality_def b35d5f5b3742c183
def AvailableChain.FGSA.Window.certificateFolded 2cb5c528dc514dbf
theorem AvailableChain.FGSA.Window.certificateFolded_def 9856dc7b2679dd2d
def AvailableChain.FGSA.Window.certificateSelection 359fd279864172e9
theorem AvailableChain.FGSA.Window.certificateSelection_def 7cdac046ad446ad9
def AvailableChain.FGSA.Window.EntryOriginAt fadb800486589259
theorem AvailableChain.FGSA.Window.EntryOriginAt_def 926282b6e22ab42b
```

### `AvailableChainFGSA.Statements.WindowEntries`

```text
def AvailableChain.FGSA.Window.RetainedW f3a4f0de9eb685b1
theorem AvailableChain.FGSA.Window.RetainedW_def 89b861dd733f7560
def AvailableChain.FGSA.Window.CoveredW 139f69bec2cd2ab8
theorem AvailableChain.FGSA.Window.CoveredW_def a1289877806b338c
def AvailableChain.FGSA.Window.EntryBitW cde8ada231b23ffa
theorem AvailableChain.FGSA.Window.EntryBitW_def 474b336873be8e87
```

### `AvailableChainFGSA.Statements.WindowHeight`

```text
```

## `AvailableChainFGSARun`

### `AvailableChainFGSARun.Statements.AC`

```text
def AvailableChain.FGSA.Run.fgsaAC bd43e97787b5eb4c
```

### `AvailableChainFGSARun.Statements.Acceptance`

```text
def AvailableChain.FGSA.Run.fgsaAdmissionTime bedfcddab6bbb51e
def AvailableChain.FGSA.Run.fgsaTimely c0c2ad54c5e0cdb2
def AvailableChain.FGSA.Run.fgsaAcceptanceInv ba55a152bf76f1d0
def AvailableChain.FGSA.Run.fgsaTrigger 0208880847e7ed0d
```

### `AvailableChainFGSARun.Statements.Client`

```text
def AvailableChain.FGSA.Run.EmitsRow e7abd57d119b14cb
def AvailableChain.FGSA.Run.EmittedRowsNoSlash 04884cd03c9f1b45
def AvailableChain.FGSA.Run.decodeRowObject c65deef1e5daf902
def AvailableChain.FGSA.Run.fgClientEvent 56263517d6766068
def AvailableChain.FGSA.Run.fgClientEvents 6e3487aa203c1462
```

### `AvailableChainFGSARun.Statements.Emission`

```text
def AvailableChain.FGSA.Run.EmissionRowsValid 041ac080a7f2aa25
def AvailableChain.FGSA.Run.decode c06272443aaec6cb
def AvailableChain.FGSA.Run.HonestEmissionWellFormed 0f66b41898b2901d
def AvailableChain.FGSA.Run.HonestProposalDecodes 39db8e9e6973e979
```

### `AvailableChainFGSARun.Statements.Excludes`

```text
inductive AvailableChain.FGSA.Run.EpochStep 7c8557b6f51e68f4
ctor AvailableChain.FGSA.Run.EpochStep.deliver 3660483a210ca62a
ctor AvailableChain.FGSA.Run.EpochStep.clock 0b4baf11d8c55f0e
def AvailableChain.FGSA.Run.Epoch ba7ef0927cdea62a
def AvailableChain.FGSA.Run.excludesFixed 2c75cb86829888c6
```

### `AvailableChainFGSARun.Statements.Interface`

```text
def AvailableChain.FGSA.Run.isRowObject 46c1a87e68a912bf
theorem AvailableChain.FGSA.Run.isRowObject_def eb00db839d1d7c38
def AvailableChain.FGSA.Run.fgsaDelay 0f058916fd796f4a
theorem AvailableChain.FGSA.Run.fgsaDelay_def 54d3e26d8ba60814
def AvailableChain.FGSA.Run.fgsaInterface a1406b872fb3bca0
def AvailableChain.FGSA.Run.fgsaOutputs 104fd6786011cbee
def AvailableChain.FGSA.Run.finalizedOut 24ed8491960825ab
```

### `AvailableChainFGSARun.Statements.ReceiptCoverage`

```text
structure AvailableChain.FGSA.Run.ReceiptCoveragePremises 085d644ebebbc3ed
ctor AvailableChain.FGSA.Run.ReceiptCoveragePremises.mk 454c0f1db1490e4f
field AvailableChain.FGSA.Run.ReceiptCoveragePremises.within 360029311c3e895a
field AvailableChain.FGSA.Run.ReceiptCoveragePremises.slotWindow 5ad5f7d3ee110400
field AvailableChain.FGSA.Run.ReceiptCoveragePremises.compat a8b6c8ab0c19b24e
field AvailableChain.FGSA.Run.ReceiptCoveragePremises.deadline f7a6687c39b1d7a9
def AvailableChain.FGSA.Run.ReceiptCoverageStatement a28be47fe92d029f
theorem AvailableChain.FGSA.Run.ReceiptCoverageStatement_def 9747e8aa83d0f867
```

### `AvailableChainFGSARun.Statements.Receipts`

```text
def AvailableChain.FGSA.Run.blockOf? 594cc77aaa075947
```

### `AvailableChainFGSARun.Statements.Roots`

```text
def AvailableChain.FGSA.Run.DirectRootBlockInRun 0cda911e3f5e887f
def AvailableChain.FGSA.Run.RootBlockInRun dfcd6a30657cac78
structure AvailableChain.FGSA.Run.NamedRootCollisionFree b9425652497b6919
ctor AvailableChain.FGSA.Run.NamedRootCollisionFree.mk edec9d795980372f
field AvailableChain.FGSA.Run.NamedRootCollisionFree.root_injective eab9e6d71479e6f1
```

### `AvailableChainFGSARun.Statements.Slashing`

```text
def AvailableChain.FGSA.Run.fgsaEvidence 1b9808a1a59c7fca
def AvailableChain.FGSA.Run.fgsaSlashing e9f5d4710aa1e814
```

## `AvailableChainFGSAClaims`

### `AvailableChainFGSAClaims.Claims.Clean`

```text
def AvailableChain.FGSA.Run.CleanHistoryAt cebec014e00b705e
def AvailableChain.FGSA.Run.CleanGateAt 041c9d3e00cdc35d
def AvailableChain.FGSA.Run.CleanTruncAt 21bfc529919ca585
def AvailableChain.FGSA.Run.CleanSafetyAt 4ead0b9ffdb19d2f
def AvailableChain.FGSA.Run.CleanCutClaim e772db98bcd36773
def AvailableChain.FGSA.Run.CleanCutZeroClaim b062ee6b917f3530
def AvailableChain.FGSA.Run.CleanHistoryClaim ed6fdc10e3f39b5d
def AvailableChain.FGSA.Run.CleanPrefixTruncationClaim 149c8dce12c08b7c
def AvailableChain.FGSA.Run.CleanSafetyClaim e7041ffefd4aefc5
def AvailableChain.FGSA.Run.CleanCutPosClaim fef1c58fc8b2d856
```

### `AvailableChainFGSAClaims.Claims.Finality`

```text
def AvailableChain.FGSA.Run.FinalityKernelClaim_W 7971aa75293ec8ea
def AvailableChain.FGSA.Run.KernelACSideClaim_W eeceb0b6b6cd3dbd
def AvailableChain.FGSA.Run.FinalityKernelJoinedClaim_W 5cbfbb244e49b1d4
def AvailableChain.FGSA.Run.TailKernelClaim_W 24ed4e3a470588b5
def AvailableChain.FGSA.Run.FinalityLivenessConcl_W c796441203ce82a2
def AvailableChain.FGSA.Run.FirstFinalityConcl_W e6a51153c42020cf
def AvailableChain.FGSA.Run.ProposalFinalConcl_W a836d8ca2382e48b
def AvailableChain.FGSA.Run.AboveFrontierConcl_W d36a5285b1ceca73
def AvailableChain.FGSA.Run.FirstFinalityRecFEClaim_W f4ada4de01ceae63
def AvailableChain.FGSA.Run.FirstFinalityRecF4Claim_W c804428b531b0f2a
def AvailableChain.FGSA.Run.FinalityLivenessRecFEClaim_W a81a32e3ad405738
def AvailableChain.FGSA.Run.FinalityLivenessRecF4Claim_W ca2342a863a63573
def AvailableChain.FGSA.Run.ProposalFinalRecFEClaim_W 8910539d0dde804e
def AvailableChain.FGSA.Run.ProposalFinalRecF4Claim_W 22a4640f8567d2ff
def AvailableChain.FGSA.Run.AboveFrontierRecFEClaim_W 8bc1e44317d99413
def AvailableChain.FGSA.Run.AboveFrontierRecF4Claim_W f4d04422d5aa889b
def AvailableChain.FGSA.Run.FinalityLivenessGSTClaim_W f0815f6d649d93bb
def AvailableChain.FGSA.Run.ProposalFinalGSTClaim_W 1e15c0b6c10c34c3
def AvailableChain.FGSA.Run.AboveFrontierGSTClaim_W 9e0d2d1e1973c964
```

### `AvailableChainFGSAClaims.Claims.Foundations`

```text
def AvailableChain.FGSA.Run.ClientSafeAll 97851f3d7d9dac80
def AvailableChain.FGSA.Run.ClientSafetyClaim 2f7f72c03b17c016
def AvailableChain.FGSA.Run.ClientSafetyBaseClaim 3d8a031d4e98871a
def AvailableChain.FGSA.Run.FGFoundationClaim b9d64d08fa674451
def AvailableChain.FGSA.Run.SrcFrameAboveClaim 7c439af0ba03021b
def AvailableChain.FGSA.Run.RunFGBlock 83f9168e58a1eafd
def AvailableChain.FGSA.Run.CarrierAt 7b6f8f267e34004c
def AvailableChain.FGSA.Run.StoreAt cf438ba65b75acc5
def AvailableChain.FGSA.Run.ActiveViewAt 19fc45d85605fb94
def AvailableChain.FGSA.Run.LeaseOriginsAt 0360d030e28c4e05
def AvailableChain.FGSA.Run.SourceDisciplineBaseAt c0ee9f0e77c9569e
def AvailableChain.FGSA.Run.SourceDisciplineAt 646bd27f6b507256
def AvailableChain.FGSA.Run.CarrierClaim 61d74ff4f545a2ca
def AvailableChain.FGSA.Run.ChainCertificatesAt 9f395ba822711df3
def AvailableChain.FGSA.Run.ChainCertificatesClaim 5371d21aa78af522
def AvailableChain.FGSA.Run.StoreClaim 2dad20468bd8d15d
def AvailableChain.FGSA.Run.ActiveViewClaim 083b435498cd1212
def AvailableChain.FGSA.Run.LeaseOriginsClaim a96322f202094fee
def AvailableChain.FGSA.Run.ReconcileAt 1ec6c337533b2665
def AvailableChain.FGSA.Run.ReconcileClaim d81c9414b35b337d
def AvailableChain.FGSA.Run.OutputNestingAt 3fc9a866e1ccdff1
def AvailableChain.FGSA.Run.OutputNestingClaim 32f554d40869840f
def AvailableChain.FGSA.Run.FrameAt f1347f4866324fb1
def AvailableChain.FGSA.Run.FrameClaim d382f4c098e8a0f0
def AvailableChain.FGSA.Run.SourceDisciplineBaseClaim 767e89eb734b4cd8
def AvailableChain.FGSA.Run.SourceDisciplineClaim 0a8abad42e2406c9
def AvailableChain.FGSA.Run.RowServiceBaseClaim 860ecdfcbfb85ea4
def AvailableChain.FGSA.Run.RowServiceClaim 04f11cf987fc7d56
def AvailableChain.FGSA.Run.PureAccountableClaim c8647a5737a4db34
def AvailableChain.FGSA.Run.PureAgreementClaim 18c8a1db5132d365
def AvailableChain.FGSA.Run.WholeRunAccountableClaim 5ee95331d29fb49c
def AvailableChain.FGSA.Run.WholeRunAgreementClaim 7e246d6274a6af17
def AvailableChain.FGSA.Run.EventPrefixAgreementClaim 61f2b3083c20a5d6
def AvailableChain.FGSA.Run.FaultCountSlashableBoundClaim f752ff54e1e27f1c
def AvailableChain.FGSA.Run.FinalizedMonotonicityClaim 4fa50038d0f1e2e6
def AvailableChain.FGSA.Run.HonestNeverSlashedClaim 35cbfe9af4eb843c
def AvailableChain.FGSA.Run.FinalizedSafetyConcl cf82484076a4534e
def AvailableChain.FGSA.Run.FinalizedSafetyClaim 031ac3b5366cf022
def AvailableChain.FGSA.Run.FinalLockClaim b3e9aa701d59000e
```

### `AvailableChainFGSAClaims.Claims.Healing`

```text
def AvailableChain.FGSA.Run.RowPermissionAt 1be00227922b6573
def AvailableChain.FGSA.Run.RowPermissionClaim 86bd07af2408fce7
def AvailableChain.FGSA.Run.HealingInputClaim 4c2b67676a2e0981
def AvailableChain.FGSA.Run.HTimeConcl b08df9cc89779110
def AvailableChain.FGSA.Run.HTimeClaim 8e28fd6035f9c993
def AvailableChain.FGSA.Run.ResetArrivalConcl 76f45bf2399583bb
def AvailableChain.FGSA.Run.ResetArrivalClaim 6207e2320227ae41
def AvailableChain.FGSA.Run.RenewedPromotionConcl 9e9a7d791f65562f
def AvailableChain.FGSA.Run.RenewedPromotionClaim 23703f554bd429fd
def AvailableChain.FGSA.Run.HTimeBestClaim e5b690e27d171481
def AvailableChain.FGSA.Run.HTimeSearchClaim 6aefecefe37e364f
```

### `AvailableChainFGSAClaims.Claims.Outage`

```text
def AvailableChain.FGSA.Run.ExactProposalAt 42379d7fc5d80b04
def AvailableChain.FGSA.Run.ExactProposalClaim 8e7e7d37f1543b8c
def AvailableChain.FGSA.Run.InclusionPostGateAt ec3728742c8b2b41
def AvailableChain.FGSA.Run.InclusionAt 2de7c117fb56598e
def AvailableChain.FGSA.Run.CleanInclusionPostGateClaim af0c32e0db75bed9
def AvailableChain.FGSA.Run.CleanInclusionClaim 176b702fefcabba9
def AvailableChain.FGSA.Run.DutiesExtendOn 6a6c4bfb2caa38da
def AvailableChain.FGSA.Run.FCompatBefore e30849395e61769c
def AvailableChain.FGSA.Run.P1Concl 28e972304e8e66ab
def AvailableChain.FGSA.Run.LeaseOrFFrom b2ff25efc46dc1b2
def AvailableChain.FGSA.Run.OutageCompatAt 8b190e2c33982590
def AvailableChain.FGSA.Run.OutageCompatClaim 47bc9ee7926817c6
def AvailableChain.FGSA.Run.FastP1Claim 5a45b3a67b2780ea
def AvailableChain.FGSA.Run.SlowP1Claim 249402ac3e61f97b
def AvailableChain.FGSA.Run.AvailableFromConcl 660c9ef5186b2d13
def AvailableChain.FGSA.Run.AvailableGrowthConcl 9259d8deeb8023ac
def AvailableChain.FGSA.Run.AvailableGSTClaim 16450e46b23f3253
def AvailableChain.FGSA.Run.AvailableGrowthGSTClaim 3d5fba0ab633fbdb
def AvailableChain.FGSA.Run.CleanGrowthClaim e9e33b45cdd8da16
```

### `AvailableChainFGSAClaims.Claims.Shared`

```text
def AvailableChain.FGSA.Run.SameLabelAt 8c1a486d0b907324
def AvailableChain.FGSA.Run.SameLabelClaim 674fd2c2c8a1a583
def AvailableChain.FGSA.Run.HeadReachesLoAt 392761e01c7d91d1
def AvailableChain.FGSA.Run.HeadReachesLoClaim 5d5bde5a5ff6cf45
def AvailableChain.FGSA.Run.ReleaseStoreAt 118347761a3c505e
def AvailableChain.FGSA.Run.ReleaseStoreClaim 25351981b7e88ffa
def AvailableChain.FGSA.Run.ReleaseAt 59ef9153558e5b3e
def AvailableChain.FGSA.Run.ReleaseClaim a09f3145662807a7
```

### `AvailableChainFGSAClaims.Claims.WeakContinuation`

```text
def AvailableChain.FGSA.Run.WeakContinuationClaim d95d6cc3d141c7ea
def AvailableChain.FGSA.Run.WeakContinuationLiveClaim f469c05870eb8b8c
```

### `AvailableChainFGSAClaims.FGSAClaims`

```text
structure AvailableChain.FGSA.Run.FGSASafetyClaims d9c49cd6f866800c
ctor AvailableChain.FGSA.Run.FGSASafetyClaims.mk 80bd156b1f283534
field AvailableChain.FGSA.Run.FGSASafetyClaims.carrier f645867c4fb59343
field AvailableChain.FGSA.Run.FGSASafetyClaims.chainCertificates c5419dfb712b65e2
field AvailableChain.FGSA.Run.FGSASafetyClaims.store 05ce7bc917f67a27
field AvailableChain.FGSA.Run.FGSASafetyClaims.activeView 831eaa1e04cf9264
field AvailableChain.FGSA.Run.FGSASafetyClaims.leaseOrigins 9cf7cff04ba695dd
field AvailableChain.FGSA.Run.FGSASafetyClaims.reconcile 6b585816046cbc01
field AvailableChain.FGSA.Run.FGSASafetyClaims.outputNesting fdc00abcad6dafda
field AvailableChain.FGSA.Run.FGSASafetyClaims.frame 05a55a18a4332629
field AvailableChain.FGSA.Run.FGSASafetyClaims.clientSafety 6774e5f9590414a9
field AvailableChain.FGSA.Run.FGSASafetyClaims.clientSafetyBase 6cf20e9bcee8a124
field AvailableChain.FGSA.Run.FGSASafetyClaims.sourceDisciplineBase 2714f8c7c38fdd70
field AvailableChain.FGSA.Run.FGSASafetyClaims.sourceDiscipline 207619c68731dc7a
field AvailableChain.FGSA.Run.FGSASafetyClaims.sameLabel e52cddb096567a68
field AvailableChain.FGSA.Run.FGSASafetyClaims.releaseStore 90c948610f35c6c7
field AvailableChain.FGSA.Run.FGSASafetyClaims.release fe6892a695a9002a
field AvailableChain.FGSA.Run.FGSASafetyClaims.headReachesLo 1d955331178fcaa2
field AvailableChain.FGSA.Run.FGSASafetyClaims.cleanCut e2a8cad3b6ea391c
field AvailableChain.FGSA.Run.FGSASafetyClaims.cleanHistory 72b0a24d3e922303
field AvailableChain.FGSA.Run.FGSASafetyClaims.cleanPrefixTruncation 049ac23f8c389c53
field AvailableChain.FGSA.Run.FGSASafetyClaims.cleanSafety 90b540085ed7b849
structure AvailableChain.FGSA.Run.FGSASafetyInterfaces fc05df15089a8aff
ctor AvailableChain.FGSA.Run.FGSASafetyInterfaces.mk 52892dac88ab2c20
field AvailableChain.FGSA.Run.FGSASafetyInterfaces.fgFoundation eb32192e1738b28f
field AvailableChain.FGSA.Run.FGSASafetyInterfaces.srcFrameAbove 5ba3fa460e03ee4f
field AvailableChain.FGSA.Run.FGSASafetyInterfaces.cpPrefix 0864f12b14cdffbd
field AvailableChain.FGSA.Run.FGSASafetyInterfaces.cpCompat 57c88dd979be1efa
field AvailableChain.FGSA.Run.FGSASafetyInterfaces.tSrc 061b66833279d2fa
field AvailableChain.FGSA.Run.FGSASafetyInterfaces.labelBound 362bf8489c9d935e
field AvailableChain.FGSA.Run.FGSASafetyInterfaces.timingContract 6b56b3d29da017d1
structure AvailableChain.FGSA.Run.FGSAFinalityClaims a5824976e114c8cd
ctor AvailableChain.FGSA.Run.FGSAFinalityClaims.mk 5d9ad70430c69f36
field AvailableChain.FGSA.Run.FGSAFinalityClaims.accountable 8f87613cf7e2a2c1
field AvailableChain.FGSA.Run.FGSAFinalityClaims.agreement 102924397ee6d162
field AvailableChain.FGSA.Run.FGSAFinalityClaims.runAccountable e2d2a348caf52c71
field AvailableChain.FGSA.Run.FGSAFinalityClaims.runAgreement 8dcc1d21e6bef640
field AvailableChain.FGSA.Run.FGSAFinalityClaims.eventPrefixAgreement 5c1ddcc9506cc384
field AvailableChain.FGSA.Run.FGSAFinalityClaims.faultCountSlashableBound 39f8ababafce9089
field AvailableChain.FGSA.Run.FGSAFinalityClaims.finalizedMonotone 01b389a1f99b574c
field AvailableChain.FGSA.Run.FGSAFinalityClaims.honestNeverSlashed e8ce26cfbff6d8d8
structure AvailableChain.FGSA.Run.FGSAClaims dd1fc68ee9951ed7
field AvailableChain.FGSA.Run.FGSAClaims.toFGSASafetyClaims 54a684174b0d69da
ctor AvailableChain.FGSA.Run.FGSAClaims.mk 240460545136be14
field AvailableChain.FGSA.Run.FGSAClaims.finality 019b25aeb9abf796
field AvailableChain.FGSA.Run.FGSAClaims.finalizedSafety 04e3e17db88b933f
field AvailableChain.FGSA.Run.FGSAClaims.finalLock 10e5500c6a9acc86
field AvailableChain.FGSA.Run.FGSAClaims.outageCompat 8a7a139c619f5d16
field AvailableChain.FGSA.Run.FGSAClaims.fastP1 91db021f96fda116
field AvailableChain.FGSA.Run.FGSAClaims.slowP1 c69a85a218759011
field AvailableChain.FGSA.Run.FGSAClaims.exactProposal 27f12395abacfc6d
field AvailableChain.FGSA.Run.FGSAClaims.cleanInclusionPostGate f1aab05a2685d6ae
field AvailableChain.FGSA.Run.FGSAClaims.cleanInclusion 1f4ce7c46f2febad
field AvailableChain.FGSA.Run.FGSAClaims.firstFinalityRecFE 62c7ebe1f50d1ae1
field AvailableChain.FGSA.Run.FGSAClaims.firstFinalityRecF4 35ed0d9646a3e3ce
field AvailableChain.FGSA.Run.FGSAClaims.finalityLivenessGSTRecFE 7c4d21a73c1bf039
field AvailableChain.FGSA.Run.FGSAClaims.finalityLivenessGSTRecF4 2200509f21748aeb
field AvailableChain.FGSA.Run.FGSAClaims.proposalFinalGSTRecFE 8edc9da0192e1610
field AvailableChain.FGSA.Run.FGSAClaims.proposalFinalGSTRecF4 0fe30f005997ae2f
field AvailableChain.FGSA.Run.FGSAClaims.aboveFrontierGSTRecFE f13e3d0aed8db2db
field AvailableChain.FGSA.Run.FGSAClaims.aboveFrontierGSTRecF4 47fa7d4092b05d3f
field AvailableChain.FGSA.Run.FGSAClaims.availableGST fddba078d64e69b5
field AvailableChain.FGSA.Run.FGSAClaims.availableGrowthGST 571b4e92d7557d99
field AvailableChain.FGSA.Run.FGSAClaims.cleanGrowth ad8bc24666014e8a
```

### `AvailableChainFGSAClaims.Statements.Bounds`

```text
def AvailableChain.FGSA.Run.L 8d4e932a42cf7b48
def AvailableChain.FGSA.Run.P f47871c3f7f4e6ab
def AvailableChain.FGSA.Run.Γ 548fe9969771212f
def AvailableChain.FGSA.Run.ρΓ e28f4f6a1e9f2b3b
def AvailableChain.FGSA.Run.ρ₁ 9022e67716777304
def AvailableChain.FGSA.Run.ρ 9cfc682cff55879f
def AvailableChain.FGSA.Run.E_g 655c22c6b0b26d2e
def AvailableChain.FGSA.Run.E_j c875c1583c2122b0
def AvailableChain.FGSA.Run.B_c 8370be549cfde2a9
def AvailableChain.FGSA.Run.D_c 63ef7ccc088b1d3a
def AvailableChain.FGSA.Run.B_reset 6f3cf78da4b1a20f
def AvailableChain.FGSA.Run.B 7fe30c11b48773f6
def AvailableChain.FGSA.Run.B_H2 3a2f311cd4245aa1
def AvailableChain.FGSA.Run.B_H1 4f3822b9e41b1443
def AvailableChain.FGSA.Run.B_H eebbb104be63948b
def AvailableChain.FGSA.Run.W_F d6cc6ebee1684526
def AvailableChain.FGSA.Run.B_F ad04a713598ea2f7
def AvailableChain.FGSA.Run.B_heal 5c1726465beadb54
def AvailableChain.FGSA.Run.B_best 6f92fac690aedf28
def AvailableChain.FGSA.Run.carrierTime2 fcf77c71390b7fee
def AvailableChain.FGSA.Run.kernelDeadline c14a31b66db5f07e
def AvailableChain.FGSA.Run.ActionDeliveryBounds ff4cca06e8d066c0
def AvailableChain.FGSA.Run.KernelBeforeNextAction 2e7642e148d854d6
def AvailableChain.FGSA.Run.VoteBeforeAction 8fd853db14856b97
def AvailableChain.FGSA.Run.GateAfterCarrier2 cc2a283cea1a2479
def AvailableChain.FGSA.Run.GateActionOrder 3591a84fddb52054
def AvailableChain.FGSA.Run.FourteenBeforeTwoRounds ff90f4dcf8415a1b
```

### `AvailableChainFGSAClaims.Statements.BoundsW`

```text
def AvailableChain.FGSA.Run.kappaF 6371313005b273e9
def AvailableChain.FGSA.Run.betaF e4d2aedc4cde665f
def AvailableChain.FGSA.Run.epsF 5ab7054c134be9ef
def AvailableChain.FGSA.Run.carrierTimeW c488dec9df90298f
def AvailableChain.FGSA.Run.kernelDeadlineW 54745f3905c6f92b
def AvailableChain.FGSA.Run.W_W 279bf1ae475f6868
def AvailableChain.FGSA.Run.E_gF 17dd82d9bc11cfaa
def AvailableChain.FGSA.Run.E_jF fd6e9996cf068a97
def AvailableChain.FGSA.Run.B_cF 4b6c14f5460230d3
def AvailableChain.FGSA.Run.D_cF 2b808c0dc7e16ca5
def AvailableChain.FGSA.Run.B_resetF c294cb223d30623f
def AvailableChain.FGSA.Run.BF e373703c25aa133c
def AvailableChain.FGSA.Run.B_H2F aa9b46c752f0d574
def AvailableChain.FGSA.Run.B_H1F 6fdcb4ef645c6017
def AvailableChain.FGSA.Run.B_HF 05073841effcea16
def AvailableChain.FGSA.Run.B'_resetF f2027477445bc4bd
def AvailableChain.FGSA.Run.B_bestF be84b53201b78f15
def AvailableChain.FGSA.Run.ActionDeliveryBoundsW 02e3698eb5609617
def AvailableChain.FGSA.Run.KernelBeforeNextActionW 4b349af3e0c9f776
structure AvailableChain.FGSA.Run.LivenessBoundW add6843622665972
ctor AvailableChain.FGSA.Run.LivenessBoundW.mk f3f84757bb6d5cb4
field AvailableChain.FGSA.Run.LivenessBoundW.kappa_le_R de51cf339cd35edf
def AvailableChain.FGSA.Run.FE_W a0c2f0e811b5b21a
def AvailableChain.FGSA.Run.F4_W 420d214e499c6aae
def AvailableChain.FGSA.Run.FGoodE_Wp d5de884b95205234
def AvailableChain.FGSA.Run.FGood4_Wp 4b7ff8450f774337
def AvailableChain.FGSA.Run.Tail_Wp e568443262ba9390
def AvailableChain.FGSA.Run.B_FW 191aeaa5a607d5a9
theorem AvailableChain.FGSA.Run.kappaF_def fef901c039d62410
theorem AvailableChain.FGSA.Run.betaF_def 166167f826d5cb48
theorem AvailableChain.FGSA.Run.epsF_def 4438023ec2765319
theorem AvailableChain.FGSA.Run.carrierTimeW_def 2c9ef5e4eb73f0ef
theorem AvailableChain.FGSA.Run.kernelDeadlineW_def 4ad3c17af5511fb5
theorem AvailableChain.FGSA.Run.W_W_def 38b7a5a5044fed7d
theorem AvailableChain.FGSA.Run.E_gF_def 769dbd5fbebe2867
theorem AvailableChain.FGSA.Run.E_jF_def 5c42de4200fe33a1
theorem AvailableChain.FGSA.Run.B_cF_def ab6d669d29d267e7
theorem AvailableChain.FGSA.Run.D_cF_def df333c137aa19c83
theorem AvailableChain.FGSA.Run.B_resetF_def fe4f48a7e6f4e54e
theorem AvailableChain.FGSA.Run.BF_def f469038bc44d01a8
theorem AvailableChain.FGSA.Run.B_H2F_def f424a92b7f97c935
theorem AvailableChain.FGSA.Run.B_H1F_def 1ab795f6987d8ed1
theorem AvailableChain.FGSA.Run.B_HF_def 4ec142c9de6daf1e
theorem AvailableChain.FGSA.Run.B'_resetF_def ffd7344c460472e6
theorem AvailableChain.FGSA.Run.B_bestF_def a56741daed1285e5
theorem AvailableChain.FGSA.Run.ActionDeliveryBoundsW_def 9afe336447a0417c
theorem AvailableChain.FGSA.Run.KernelBeforeNextActionW_def f86f12fe200a6474
theorem AvailableChain.FGSA.Run.FE_W_def 426a7f82308dc80c
theorem AvailableChain.FGSA.Run.F4_W_def b4bb5b3dda93721a
theorem AvailableChain.FGSA.Run.FGoodE_Wp_def 1939eb5083c4b78b
theorem AvailableChain.FGSA.Run.FGood4_Wp_def ed2611e4dfaad59f
theorem AvailableChain.FGSA.Run.Tail_Wp_def f39b312bcb078ed3
theorem AvailableChain.FGSA.Run.B_FW_def 6ff7a073be682df8
```

### `AvailableChainFGSAClaims.Statements.ChannelProps`

```text
def AvailableChain.FGSA.Run.RCarrierView 93617bcc1bb8a6ac
theorem AvailableChain.FGSA.Run.RCarrierView_def 831e9871d8a38531
def AvailableChain.FGSA.Run.RStore a9ef4afafd6afb62
theorem AvailableChain.FGSA.Run.RStore_def 3c94f13026b04646
def AvailableChain.FGSA.Run.RActive 8d13d711ac54d457
theorem AvailableChain.FGSA.Run.RActive_def 07c12bfee2c96e59
def AvailableChain.FGSA.Run.RStoreCumul 47f8257a4d7c0960
theorem AvailableChain.FGSA.Run.RStoreCumul_def cd900ed4fc8bda2c
def AvailableChain.FGSA.Run.RMono 611ed7fcb02392ef
theorem AvailableChain.FGSA.Run.RMono_def 849026a9316fa7d9
def AvailableChain.FGSA.Run.RFrameExact 413248d631b51f2b
theorem AvailableChain.FGSA.Run.RFrameExact_def bd674a9e5c1c7fe3
def AvailableChain.FGSA.Run.RFrame a1e61af586aeb3db
theorem AvailableChain.FGSA.Run.RFrame_def 7c3198363ce4af6b
def AvailableChain.FGSA.Run.RGeo 28a674e421943229
theorem AvailableChain.FGSA.Run.RGeo_def a8f52a9d6c6ce94e
def AvailableChain.FGSA.Run.RCert 5d4d0d968ae6d4fb
theorem AvailableChain.FGSA.Run.RCert_def f4639658393d4ee9
def AvailableChain.FGSA.Run.RRec b9a2c7029000c2d4
theorem AvailableChain.FGSA.Run.RRec_def 513b69bf82702bbe
def AvailableChain.FGSA.Run.TSrc 58063ac7d9e8e7da
theorem AvailableChain.FGSA.Run.TSrc_def cab3f3b3626c23d2
def AvailableChain.FGSA.Run.LabelBound f8ca3e63605da1e2
theorem AvailableChain.FGSA.Run.LabelBound_def 668b868fc8ece611
def AvailableChain.FGSA.Run.TChain 0b6d8e3fc094b75a
theorem AvailableChain.FGSA.Run.TChain_def f6ade2bf3837c5d1
def AvailableChain.FGSA.Run.TCompat 5bf53bb7d850a2af
theorem AvailableChain.FGSA.Run.TCompat_def 29b223c995a98f77
structure AvailableChain.FGSA.Run.AncestorClosed a82d5e35de829ed2
ctor AvailableChain.FGSA.Run.AncestorClosed.mk fa2827ea0465c6d5
field AvailableChain.FGSA.Run.AncestorClosed.down 6a9b1aab4f3ebb3e
def AvailableChain.FGSA.Run.FrameBelow d170caf7c923ca81
theorem AvailableChain.FGSA.Run.FrameBelow_def b261817e5cd74fb3
def AvailableChain.FGSA.Run.RStrat 7e000bf26169441e
theorem AvailableChain.FGSA.Run.RStrat_def 9f76f645ab990860
def AvailableChain.FGSA.Run.RQCOrigin 83ebcb8f39c6b8f7
theorem AvailableChain.FGSA.Run.RQCOrigin_def a23958aaaf90668f
def AvailableChain.FGSA.Run.SrcFrameAbove ac5a5a152d132407
theorem AvailableChain.FGSA.Run.SrcFrameAbove_def 7a47ee7f0289b677
def AvailableChain.FGSA.Run.SrcFrame f592d51ad85b9e39
def AvailableChain.FGSA.Run.SrcFrameAboveStmt ead9d4e493a7a2c1
theorem AvailableChain.FGSA.Run.SrcFrameAboveStmt_def 9eb722e9d8ea5e07
def AvailableChain.FGSA.Run.CPPrefix b617e115098ef128
theorem AvailableChain.FGSA.Run.CPPrefix_def 524220fcb4af0154
def AvailableChain.FGSA.Run.CPCompat ed00806b66a59062
theorem AvailableChain.FGSA.Run.CPCompat_def bad34c67b01f1949
def AvailableChain.FGSA.Run.RXing e0c63a83b09d927d
def AvailableChain.FGSA.Run.RCap 0b6920f3a1278da9
def AvailableChain.FGSA.Run.THigh 4d530dd7fbcfca24
def AvailableChain.FGSA.Run.TCarrier 0cbd7cdfde265693
def AvailableChain.FGSA.Run.TRowsSelect b7868ee0152e7853
def AvailableChain.FGSA.Run.TRowsSync b103c611fd35126e
def AvailableChain.FGSA.Run.TRowsReceipt e525a48d76b1aa17
theorem AvailableChain.FGSA.Run.TRowsReceipt_def 9c7bcbf60fb9b4c7
structure AvailableChain.FGSA.Run.TRows cbcab83c4458311c
ctor AvailableChain.FGSA.Run.TRows.mk dd8258b05777b711
field AvailableChain.FGSA.Run.TRows.select c9ed713cf86a3891
field AvailableChain.FGSA.Run.TRows.sync 02b5818d595c5d61
field AvailableChain.FGSA.Run.TRows.receipt a5af345ccdeb0302
def AvailableChain.FGSA.Run.SourceBefore 87891fca840a92bf
def AvailableChain.FGSA.Run.Kept 14c8e0cfba87564b
def AvailableChain.FGSA.Run.KeepOrCause 0daec0c9dfdc0408
def AvailableChain.FGSA.Run.RExcl 584afe090d667e01
def AvailableChain.FGSA.Run.RKeep 279823497a938c05
def AvailableChain.FGSA.Run.RFProv b2bbcbea529a2222
def AvailableChain.FGSA.Run.TDel 90aaea95fdcdf290
def AvailableChain.FGSA.Run.TDelReset 22e6e8aeb90a8d02
def AvailableChain.FGSA.Run.TGeom 879cf615867e4739
def AvailableChain.FGSA.Run.ExactService c8e833a45eaad58a
def AvailableChain.FGSA.Run.PhaseInterval c9f74746c3e9c93f
def AvailableChain.FGSA.Run.Transfers 70535be68777f118
def AvailableChain.FGSA.Run.PhaseBody 3c16f15d6d736d8d
def AvailableChain.FGSA.Run.TPerm 630ca5bb6b7c62b4
def AvailableChain.FGSA.Run.ProposalGap d8ce6f2853c37dba
def AvailableChain.FGSA.Run.RepairAfter 024522afc96636ef
def AvailableChain.FGSA.Run.TRepair f2fad4faf03fcdfa
def AvailableChain.FGSA.Run.OpeningCovered 79b399e4828cb308
def AvailableChain.FGSA.Run.OpeningEntry 6bece33f654d43b3
def AvailableChain.FGSA.Run.TCommon a632f2cd30f5e248
def AvailableChain.FGSA.Run.TFrontier a12216126c606ee8
def AvailableChain.FGSA.Run.FinalityRowCarriage ced3893ab4eb6207
theorem AvailableChain.FGSA.Run.FinalityRowCarriage_def 80205a79366d1f4d
```

### `AvailableChainFGSAClaims.Statements.Channels`

```text
def AvailableChain.FGSA.Run.certified 80e4a3693bf2d89c
theorem AvailableChain.FGSA.Run.certified_def a5d675c89a272887
def AvailableChain.FGSA.Run.treeT 2b69ec7b0e57e60e
def AvailableChain.FGSA.Run.treeErased 781b0a26d002a754
def AvailableChain.FGSA.Run.frameR 395107f87e1057e7
def AvailableChain.FGSA.Run.domainR 4161e11ed74ec34d
def AvailableChain.FGSA.Run.finR aac46ba18b4700c2
def AvailableChain.FGSA.Run.FAdvance 295788c25e134f22
def AvailableChain.FGSA.Run.sourceCandidates 15ae2568da2c93f7
def AvailableChain.FGSA.Run.jointSource 0c24947a4c7a783b
def AvailableChain.FGSA.Run.proposerHead b9b8415a6df36962
def AvailableChain.FGSA.Run.outputS f3f1bf40e501d936
theorem AvailableChain.FGSA.Run.outputS_def 6f0e9f78ba8dc35c
theorem AvailableChain.FGSA.Run.frameR_def 46870ba5dac194b2
theorem AvailableChain.FGSA.Run.jointSource_def 884a9f045b72de73
theorem AvailableChain.FGSA.Run.sourceCandidates_def a419a14c1319e0ab
theorem AvailableChain.FGSA.Run.domainR_def 729fb9eaa24e05a3
theorem AvailableChain.FGSA.Run.treeT_def 3acc17fc60e79846
theorem AvailableChain.FGSA.Run.proposerHead_def 23840b24f59e59b6
theorem AvailableChain.FGSA.Run.FAdvance_def 910b82c4a0274160
def AvailableChain.FGSA.Run.R_at 5eb2067c15edefad
def AvailableChain.FGSA.Run.D_at b07cd2ddfc8d3741
def AvailableChain.FGSA.Run.FAdvanceAt c4c358b4c17a83c3
def AvailableChain.FGSA.Run.candidatesAt bfc1d93215030683
def AvailableChain.FGSA.Run.proposalHeadAt 640f46478c0cfb91
def AvailableChain.FGSA.Run.actionHead e30fd4f6d966b4ac
def AvailableChain.FGSA.Run.actionTriple 30e62b911e59660c
def AvailableChain.FGSA.Run.namedEntry a50c73e0c7ee36db
def AvailableChain.FGSA.Run.EntryBelow 70f4e667e4654e34
def AvailableChain.FGSA.Run.RowSigner 39af93ee0ccbab5f
def AvailableChain.FGSA.Run.HonestRowAt 1792dfa7b92b12c9
def AvailableChain.FGSA.Run.HonestRowBefore 3f7b8ec6bb5e5028
theorem AvailableChain.FGSA.Run.HonestRowBefore_def 856c675561f53504
def AvailableChain.FGSA.Run.RowComplete 55b7cc313cf34797
def AvailableChain.FGSA.Run.HonestCarrier db0441c84ac1ed7b
def AvailableChain.FGSA.Run.HeldAt faee4f9adb20fdb7
def AvailableChain.FGSA.Run.BlockInRunBefore 3c8b292c2e3b0601
theorem AvailableChain.FGSA.Run.RowSigner_def 3f800379ce0dcec8
theorem AvailableChain.FGSA.Run.HonestRowAt_def 711ff59cfa1c9df6
def AvailableChain.FGSA.Run.rowHeld 10b14191989e4cf6
def AvailableChain.FGSA.Run.proposalStateAt f768de8cf55977a3
def AvailableChain.FGSA.Run.heldAtProposal e2909ae35f9ca3ff
def AvailableChain.FGSA.Run.onParentChain 94cfd6d191a449a0
def AvailableChain.FGSA.Run.HeldBefore d00b6e7cc1b5cb14
def AvailableChain.FGSA.Run.ValidForParent 796c17f850eca4a2
theorem AvailableChain.FGSA.Run.ValidForParent_def b6c9f94bd8cc7a7f
def AvailableChain.FGSA.Run.HeightMatch b0d9461efc091698
theorem AvailableChain.FGSA.Run.HeightMatch_def 91823409c26bff1c
def AvailableChain.FGSA.Run.headAtLabel 732485e0312b81d8
theorem AvailableChain.FGSA.Run.RowComplete_def b0279e1c16bb5ce3
theorem AvailableChain.FGSA.Run.HonestCarrier_def ba50c46960fc9e20
theorem AvailableChain.FGSA.Run.HeldAt_def 13e37f5b17442fff
theorem AvailableChain.FGSA.Run.namedEntry_def f3827e3bef137733
```

### `AvailableChainFGSAClaims.Statements.ComposeStmt`

```text
def AvailableChain.FGSA.Run.windowIdx f2a7ceb24a82bd68
structure AvailableChain.FGSA.Run.TimingContract d27447b522c1f337
ctor AvailableChain.FGSA.Run.TimingContract.mk 0e82bb5d629a2c60
field AvailableChain.FGSA.Run.TimingContract.rowLag f88d189dada3fdf3
field AvailableChain.FGSA.Run.TimingContract.certLag 66c75fc5f5fdaf06
field AvailableChain.FGSA.Run.TimingContract.label 56c60451198139a2
field AvailableChain.FGSA.Run.TimingContract.atomic 81e1382808062ce2
field AvailableChain.FGSA.Run.TimingContract.tickFG cc8afee8c5306c08
structure AvailableChain.FGSA.Run.FGFoundation efe0832dbda68cff
ctor AvailableChain.FGSA.Run.FGFoundation.mk 138b2346c99f9a67
field AvailableChain.FGSA.Run.FGFoundation.store 6955076899661c46
field AvailableChain.FGSA.Run.FGFoundation.cumul a1949a41d6dcfbc4
field AvailableChain.FGSA.Run.FGFoundation.mono b6ac1b814b44d05c
field AvailableChain.FGSA.Run.FGFoundation.frame 0e19db9a2972012d
field AvailableChain.FGSA.Run.FGFoundation.geo f8d216e4fb902c3e
field AvailableChain.FGSA.Run.FGFoundation.strat d302e146b604d315
field AvailableChain.FGSA.Run.FGFoundation.reconcile c0ebd0c28d1c2128
def AvailableChain.FGSA.Run.TStart 9f8e31794d414719
def AvailableChain.FGSA.Run.FullVoteService ac58a365e228dbc0
def AvailableChain.FGSA.Run.TVote 9b573b1e1967c3e7
def AvailableChain.FGSA.Run.WalkBatch 345ddfcfaa9d0442
def AvailableChain.FGSA.Run.TWalk 9ead74cb26cae197
structure AvailableChain.FGSA.Run.CoreServices 33813078e3120cfe
ctor AvailableChain.FGSA.Run.CoreServices.mk 60780ecbf0fe7447
field AvailableChain.FGSA.Run.CoreServices.start 797b3fa2dc42ca46
field AvailableChain.FGSA.Run.CoreServices.vote bd14effe915bad2a
field AvailableChain.FGSA.Run.CoreServices.walk 3b8e677be1451b1a
inductive AvailableChain.FGSA.Run.PhaseKind c1b8ad8e15380e60
ctor AvailableChain.FGSA.Run.PhaseKind.gap 5e88dc1d014a063a
ctor AvailableChain.FGSA.Run.PhaseKind.topJ ef3517c6daf975b3
ctor AvailableChain.FGSA.Run.PhaseKind.contest 09d7f16d016aa074
inductive AvailableChain.FGSA.Run.AttemptTask 90defab1dcdb57a7
ctor AvailableChain.FGSA.Run.AttemptTask.raise fe31883cbb822cf7
ctor AvailableChain.FGSA.Run.AttemptTask.firstRow 6412d6399a447594
structure AvailableChain.FGSA.Run.AttemptKey ab5f1b1e8d1673ae
ctor AvailableChain.FGSA.Run.AttemptKey.mk 1752ea276d7f0293
field AvailableChain.FGSA.Run.AttemptKey.start 2fde4ea3fa941fa2
field AvailableChain.FGSA.Run.AttemptKey.frontier dee085abe8607002
field AvailableChain.FGSA.Run.AttemptKey.phase 84195c8f48291dfb
field AvailableChain.FGSA.Run.AttemptKey.task 6a4993e3f16b51cb
field AvailableChain.FGSA.Run.AttemptKey.served 36c55bac0872d02c
def AvailableChain.FGSA.Run.ResetArrivalStatement f7c3256c8d183381
theorem AvailableChain.FGSA.Run.ResetArrivalStatement_def 34cda50693a93c57
def AvailableChain.FGSA.Run.ResetArrivalFullStatement 4da823b477ce69ab
theorem AvailableChain.FGSA.Run.ResetArrivalFullStatement_def 9c6ae6ec2a014f44
structure AvailableChain.FGSA.Run.KernelPt 9235f1fbc5c48477
ctor AvailableChain.FGSA.Run.KernelPt.mk 32c96b623cc6f691
field AvailableChain.FGSA.Run.KernelPt.w 6cbd0d7075070f20
field AvailableChain.FGSA.Run.KernelPt.r e581c6d88b7635d7
def AvailableChain.FGSA.Run.kernelStart 3a8a5275b6f2ca2c
def AvailableChain.FGSA.Run.OpeningCarrier_W eec3a7ce0ced64c5
theorem AvailableChain.FGSA.Run.OpeningCarrier_W_def 4b49744ef68e28cb
def AvailableChain.FGSA.Run.KernelConclusion_W 4cfcfa3b9fc99ac9
theorem AvailableChain.FGSA.Run.KernelConclusion_W_def 3443df2290db0d39
structure AvailableChain.FGSA.Run.KernelPrem_W 7a899d5e9079ae6c
ctor AvailableChain.FGSA.Run.KernelPrem_W.mk 1051d18621bd4d8d
field AvailableChain.FGSA.Run.KernelPrem_W.set c559cccf0b7957d8
field AvailableChain.FGSA.Run.KernelPrem_W.bound fe3e94332733855a
field AvailableChain.FGSA.Run.KernelPrem_W.window edcd81f58fcf6213
field AvailableChain.FGSA.Run.KernelPrem_W.start e28fc3dcda7d13b7
field AvailableChain.FGSA.Run.KernelPrem_W.hhor 65b3066c07b80d44
field AvailableChain.FGSA.Run.KernelPrem_W.input d0ca8a53e9a6063c
field AvailableChain.FGSA.Run.KernelPrem_W.services abf412494cd2ede4
structure AvailableChain.FGSA.Run.TailKernelPt b330d4900d1ca7d6
ctor AvailableChain.FGSA.Run.TailKernelPt.mk 41cdd6cb6261ae64
field AvailableChain.FGSA.Run.TailKernelPt.w b55caf984a16e648
field AvailableChain.FGSA.Run.TailKernelPt.r 4006ca4b73b3c4a7
field AvailableChain.FGSA.Run.TailKernelPt.carrier 62ca7b0096b16566
field AvailableChain.FGSA.Run.TailKernelPt.U 5b648aaa4a87357a
structure AvailableChain.FGSA.Run.TailKernelPrem_W bb0a610ea1b87b7e
ctor AvailableChain.FGSA.Run.TailKernelPrem_W.mk 58e4bb4d4aa4e4da
field AvailableChain.FGSA.Run.TailKernelPrem_W.set 01845b5b4db05690
field AvailableChain.FGSA.Run.TailKernelPrem_W.bound d069cd8ecda849b8
field AvailableChain.FGSA.Run.TailKernelPrem_W.input c9de42728604b8ab
field AvailableChain.FGSA.Run.TailKernelPrem_W.start fca924720235b39b
field AvailableChain.FGSA.Run.TailKernelPrem_W.window d434215cbb4771f2
field AvailableChain.FGSA.Run.TailKernelPrem_W.carrier 4cffa67150436793
field AvailableChain.FGSA.Run.TailKernelPrem_W.high 957603131896b71e
field AvailableChain.FGSA.Run.TailKernelPrem_W.cover aaedc38bcfe49fa7
field AvailableChain.FGSA.Run.TailKernelPrem_W.hhor 8225266ad0b4b724
structure AvailableChain.FGSA.Run.HealTContract c380210db0b4ad2f
ctor AvailableChain.FGSA.Run.HealTContract.mk 11ff31b5d3c845d8
field AvailableChain.FGSA.Run.HealTContract.del 14f6a7b17c818609
field AvailableChain.FGSA.Run.HealTContract.delReset ffab9935bca7d4d0
field AvailableChain.FGSA.Run.HealTContract.perm 374223621c952cf4
field AvailableChain.FGSA.Run.HealTContract.repair 6cabbb12f44330fe
field AvailableChain.FGSA.Run.HealTContract.common e098f04736f59b82
field AvailableChain.FGSA.Run.HealTContract.frontier 136a18e4391303c7
field AvailableChain.FGSA.Run.HealTContract.geom 6a61151ba4fb5aeb
def AvailableChain.FGSA.Run.frontierAtIdx 46705feccc0a8753
def AvailableChain.FGSA.Run.TopEvidence 4b92e2dbec79d96a
def AvailableChain.FGSA.Run.ContestEvidence 3323ec8cdf349d23
def AvailableChain.FGSA.Run.EffectiveEvent 910e415f02044b40
def AvailableChain.FGSA.Run.AttemptPhaseAt cff52c8a2d4430b8
def AvailableChain.FGSA.Run.ServedFrontier 73b4eeac3939a46c
def AvailableChain.FGSA.Run.AttemptValid 624bffe59c6b6f72
def AvailableChain.FGSA.Run.attemptBudget b92a1475dc2a8a8b
def AvailableChain.FGSA.Run.AttemptEndsBy 5085e6834bee77e3
def AvailableChain.FGSA.Run.SettledPhaseFrame 362bcbb7ba51ca7e
theorem AvailableChain.FGSA.Run.SettledPhaseFrame_def 2350c57f4b2aabd0
def AvailableChain.FGSA.Run.RPhase 3f29a5defff97a70
theorem AvailableChain.FGSA.Run.RPhase_def 8aa75d3f0c581caf
structure AvailableChain.FGSA.Run.HealRContract 987c1cf70c74dcfb
ctor AvailableChain.FGSA.Run.HealRContract.mk 5c7cc244428d8fcb
field AvailableChain.FGSA.Run.HealRContract.xing 1967978e1b118029
field AvailableChain.FGSA.Run.HealRContract.cap fe1579e06b9d090d
field AvailableChain.FGSA.Run.HealRContract.phase e608d7264acd2411
field AvailableChain.FGSA.Run.HealRContract.excl e38a9c037ca22e47
field AvailableChain.FGSA.Run.HealRContract.keep 72a13a3aadc16860
field AvailableChain.FGSA.Run.HealRContract.fprov 76dab2ee8732a7f9
def AvailableChain.FGSA.Run.ProgressAttemptStatement 1769c7219d35818e
theorem AvailableChain.FGSA.Run.ProgressAttemptStatement_def afe5e5834d24eb89
```

### `AvailableChainFGSAClaims.Statements.Counts`

```text
def AvailableChain.FGSA.Run.awakeHonestIn 54415ad59f9cd90a
def AvailableChain.FGSA.Run.HonestProposal ae9f4b671ef57b39
```

### `AvailableChainFGSAClaims.Statements.FinalityApi`

```text
def AvailableChain.FGSA.Run.FinalityFinalizedAt 07c61af64b2952e5
theorem AvailableChain.FGSA.Run.FinalityFinalizedAt_def 5d19c2698c4c9d8e
def AvailableChain.FGSA.Run.FinalityBlock c4c6407218a58352
theorem AvailableChain.FGSA.Run.FinalityBlock_def 75c57a88ce795c77
def AvailableChain.FGSA.Run.finalityRows 0095a1b4bd82114d
theorem AvailableChain.FGSA.Run.finalityRows_def 33877122b770dbb3
def AvailableChain.FGSA.Run.FinalitySlashableBound 886cde87842a0550
theorem AvailableChain.FGSA.Run.FinalitySlashableBound_def bb613b5b5fe6e8e2
def AvailableChain.FGSA.Run.FinalityExecution 9cea20ad89114186
theorem AvailableChain.FGSA.Run.FinalityExecution_def 165bf15750b9cedf
def AvailableChain.FGSA.Run.WholeRunAccountable bdd1e7bfd0030829
theorem AvailableChain.FGSA.Run.WholeRunAccountable_def a18d966f0d17db8d
def AvailableChain.FGSA.Run.WholeRunAgreement 9723595f8314c7db
theorem AvailableChain.FGSA.Run.WholeRunAgreement_def 9c78e3633b7c0895
```

### `AvailableChainFGSAClaims.Statements.Fold`

```text
inductive AvailableChain.FGSA.Run.RowKind da2d1119c2ef39fc
ctor AvailableChain.FGSA.Run.RowKind.target a127adc0838fa2e4
ctor AvailableChain.FGSA.Run.RowKind.progress e22f9613e6edb955
def AvailableChain.FGSA.Run.RowNames c882dc72ac13848c
def AvailableChain.FGSA.Run.SlotChain 026b8cab17d0c00f
def AvailableChain.FGSA.Run.EntryAt 6a182d85dcf4ffba
def AvailableChain.FGSA.Run.JustifiedCross 4220b788bb017546
def AvailableChain.FGSA.Run.MixedCross 1c0f9778f6d9b446
def AvailableChain.FGSA.Run.NoMixedOnPath 3e473ddff4cc55e1
def AvailableChain.FGSA.Run.SeatCovers 0d72d8b768d2a82c
def AvailableChain.FGSA.Run.CoveredByChild c5e54547daf9eb39
def AvailableChain.FGSA.Run.foldTrichotomy 3f91adf7d9eba691
def AvailableChain.FGSA.Run.StoredProgressConsume bcb8f879ae014395
def AvailableChain.FGSA.Run.NoMixedMaturity f968c4f72940f18d
def AvailableChain.FGSA.Run.NamesEntry 4157bcc504c0ab7f
def AvailableChain.FGSA.Run.rowHeight 8e2499ef46ddafdd
def AvailableChain.FGSA.Run.eventTime 4bdaaa69edcc1980
def AvailableChain.FGSA.Run.honestSeats dc6382cb266fd19c
theorem AvailableChain.FGSA.Run.rowHeight_def 770f0d6454ee9f76
theorem AvailableChain.FGSA.Run.eventTime_def 58ef7b966e9699ec
theorem AvailableChain.FGSA.Run.honestSeats_def 8c9d2835a4ff884b
def AvailableChain.FGSA.Run.ChainRowsBefore 26c5e008d1babb9b
structure AvailableChain.FGSA.Run.PreBatchPrem 60a5202c34981b34
ctor AvailableChain.FGSA.Run.PreBatchPrem.mk b1fc59212503969d
field AvailableChain.FGSA.Run.PreBatchPrem.base e31f7ac85785f241
field AvailableChain.FGSA.Run.PreBatchPrem.faultQ 5c34bccae86ef932
field AvailableChain.FGSA.Run.PreBatchPrem.entry 2803f6816a3f4d8d
field AvailableChain.FGSA.Run.PreBatchPrem.path 02ec342f202bdd10
field AvailableChain.FGSA.Run.PreBatchPrem.cut b6e4153986ebe8ee
field AvailableChain.FGSA.Run.PreBatchPrem.early a61c2fd188b2cbd5
field AvailableChain.FGSA.Run.PreBatchPrem.rows e4d928a1b809575b
field AvailableChain.FGSA.Run.PreBatchPrem.noRow 970f0da813393384
def AvailableChain.FGSA.Run.NoMixedPreBatchParent d64b4d50b4accd9d
structure AvailableChain.FGSA.Run.BatchPrem 765c04d7e19687c4
ctor AvailableChain.FGSA.Run.BatchPrem.mk 802f1613ed9984c9
field AvailableChain.FGSA.Run.BatchPrem.base 7ee4e0b47238d35e
field AvailableChain.FGSA.Run.BatchPrem.faultQ bb374bc3a5b7194c
field AvailableChain.FGSA.Run.BatchPrem.deltaF 5cb3cc0ec2ca2ba6
field AvailableChain.FGSA.Run.BatchPrem.rowsReceipt 3d93d37880f532ce
field AvailableChain.FGSA.Run.BatchPrem.horizon 12c4a1e340335e87
field AvailableChain.FGSA.Run.BatchPrem.carrier 47ff72215c62dec1
field AvailableChain.FGSA.Run.BatchPrem.after 6bc83dd72008618f
field AvailableChain.FGSA.Run.BatchPrem.valid a627a7581dfdce51
field AvailableChain.FGSA.Run.BatchPrem.entry f83a46992e125c98
field AvailableChain.FGSA.Run.BatchPrem.path 154c0d3661f1febf
field AvailableChain.FGSA.Run.BatchPrem.above c8a952c4bd22e824
def AvailableChain.FGSA.Run.BatchCoverage 237cf77af5f41ae0
theorem AvailableChain.FGSA.Run.JustifiedCross_def df81b827b773af75
theorem AvailableChain.FGSA.Run.MixedCross_def 9bb1a7e85401f709
theorem AvailableChain.FGSA.Run.foldTrichotomy_def 132834b174b22f9b
theorem AvailableChain.FGSA.Run.StoredProgressConsume_def 36cd5ccc9859c367
def AvailableChain.FGSA.Run.FinRowNames 94adce64d3029936
def AvailableChain.FGSA.Run.FinalityCoveredByChild_W 643922320c84f168
def AvailableChain.FGSA.Run.FinalityNames 6502008fb69955a7
structure AvailableChain.FGSA.Run.FinalityBatchPrem_W 252882e2247f46ae
ctor AvailableChain.FGSA.Run.FinalityBatchPrem_W.mk 28162a72ec95a2a4
field AvailableChain.FGSA.Run.FinalityBatchPrem_W.base d9a4e1b34d1e2f28
field AvailableChain.FGSA.Run.FinalityBatchPrem_W.faultQ b8027d2e4dd16942
field AvailableChain.FGSA.Run.FinalityBatchPrem_W.deltaF 1899bc01b8f722b2
field AvailableChain.FGSA.Run.FinalityBatchPrem_W.rowsReceipt 0dd2fa13f49b6d4b
field AvailableChain.FGSA.Run.FinalityBatchPrem_W.carrier abb156f0ac39ed76
field AvailableChain.FGSA.Run.FinalityBatchPrem_W.after 981deb409e8890c5
field AvailableChain.FGSA.Run.FinalityBatchPrem_W.horizon 77cd8a85cc1220be
field AvailableChain.FGSA.Run.FinalityBatchPrem_W.parent c7b6858b8aa3f151
field AvailableChain.FGSA.Run.FinalityBatchPrem_W.birth af925cc48f48f150
field AvailableChain.FGSA.Run.FinalityBatchPrem_W.retainedOrCovered 7598c74d4bd833ba
field AvailableChain.FGSA.Run.FinalityBatchPrem_W.batch f9d46eb62fbeb0d7
def AvailableChain.FGSA.Run.FinalityBatchCoverage_W c3d37e086dba8bfa
structure AvailableChain.FGSA.Run.PendingFold_W 5f973f39dc1fdc9c
ctor AvailableChain.FGSA.Run.PendingFold_W.mk 05cc06274674b236
field AvailableChain.FGSA.Run.PendingFold_W.child 8966d5943b8bb5c5
field AvailableChain.FGSA.Run.PendingFold_W.cover 9f4386d5fd82c86d
theorem AvailableChain.FGSA.Run.FinalityCoveredByChild_W_def b949f1a305ead8fa
theorem AvailableChain.FGSA.Run.FinRowNames_def ed158b1dc934a188
theorem AvailableChain.FGSA.Run.FinalityNames_def 008a06cf02c71175
theorem AvailableChain.FGSA.Run.FinalityBatchCoverage_W_def 975ca4fcb09e6271
```

### `AvailableChainFGSAClaims.Statements.Healed`

```text
def AvailableChain.FGSA.Run.healStart efa6a7582ec2d6b4
def AvailableChain.FGSA.Run.HealSuffix 7ba34c83b5710930
def AvailableChain.FGSA.Run.Healed 8cd7b745ebef5fb6
def AvailableChain.FGSA.Run.H2A a8e7d38eabf4785d
def AvailableChain.FGSA.Run.H2Prime f9b4804e0257a710
def AvailableChain.FGSA.Run.H3 5a3991e5d662039f
def AvailableChain.FGSA.Run.H4 4c53212b4b93c908
def AvailableChain.FGSA.Run.H5RawTransfer ad31c854e0fb787f
def AvailableChain.FGSA.Run.H6GateService 6c8153401edd7f2e
structure AvailableChain.FGSA.Run.HealT 1d43ff8229c8ed21
ctor AvailableChain.FGSA.Run.HealT.mk e6b4879dd83cc10b
field AvailableChain.FGSA.Run.HealT.h1 b7c62ddc1e9a9d56
field AvailableChain.FGSA.Run.HealT.h2 2e3313a97e65a99a
field AvailableChain.FGSA.Run.HealT.rows 90bf2f22241ad631
structure AvailableChain.FGSA.Run.HealAC 3ba46162bafe5e70
ctor AvailableChain.FGSA.Run.HealAC.mk 470b3d1a7bfc44fb
field AvailableChain.FGSA.Run.HealAC.h2A f62d9a2cf5967dd7
field AvailableChain.FGSA.Run.HealAC.h2' 5dfb2b8e3f21cde6
field AvailableChain.FGSA.Run.HealAC.h3 8b093b154317f3f7
field AvailableChain.FGSA.Run.HealAC.h4 6308693efedb753e
field AvailableChain.FGSA.Run.HealAC.h5 c7c34a9625599330
field AvailableChain.FGSA.Run.HealAC.h6 1b654d31a062c189
structure AvailableChain.FGSA.Run.HealingInput 04b90a31affed920
ctor AvailableChain.FGSA.Run.HealingInput.mk e04af8c31ee9c5b5
field AvailableChain.FGSA.Run.HealingInput.healed 750eef30b10acad0
field AvailableChain.FGSA.Run.HealingInput.wit 5c10da8bd76a000f
field AvailableChain.FGSA.Run.HealingInput.t e081edf3abd7003a
field AvailableChain.FGSA.Run.HealingInput.ac 416de2c0ae609beb
def AvailableChain.FGSA.Run.HTimeStatement b71c4ae70fa3cd3b
theorem AvailableChain.FGSA.Run.HTimeStatement_def fa4c69b9c633030b
theorem AvailableChain.FGSA.Run.HealSuffix_def fade22ac42dafd52
theorem AvailableChain.FGSA.Run.healStart_def acf60d495bc2ba83
```

### `AvailableChainFGSAClaims.Statements.HealedBest`

```text
def AvailableChain.FGSA.Run.HTimeBestConcl ac404ec0a01a61c2
theorem AvailableChain.FGSA.Run.HTimeBestConcl_def 1c5efcec3f997b17
```

### `AvailableChainFGSAClaims.Statements.LiveDC`

```text
def AvailableChain.FGSA.Run.liveDCDeadline_W 98bb35b3a856b670
theorem AvailableChain.FGSA.Run.liveDCDeadline_W_def 69c7b1824c4488b2
def AvailableChain.FGSA.Run.LiveDCConcl_W e785e4897b8ca1a4
theorem AvailableChain.FGSA.Run.LiveDCConcl_W_def 5fcf6dfbf8d36b4f
def AvailableChain.FGSA.Run.LiveDCFromWindowsStatement b74c2cd2b1dce651
theorem AvailableChain.FGSA.Run.LiveDCFromWindowsStatement_def f62222cee774f1c4
```

### `AvailableChainFGSAClaims.Statements.OutputReads`

```text
def AvailableChain.FGSA.Run.ServedFromGateAt 6a74b0215342e605
theorem AvailableChain.FGSA.Run.ServedFromGateAt_def a038bb9660f47e44
def AvailableChain.FGSA.Run.JointGrowthAt 41c0b48a633a7292
theorem AvailableChain.FGSA.Run.JointGrowthAt_def 37c0f4265dec5079
```

### `AvailableChainFGSAClaims.Statements.Packages.Finality`

```text
inductive AvailableChain.FGSA.Run.FinFormW e65aa35faec5d780
ctor AvailableChain.FGSA.Run.FinFormW.recFE f5bdcad089b74a37
ctor AvailableChain.FGSA.Run.FinFormW.recF4 9740b2983363dec5
def AvailableChain.FGSA.Run.FinFormW.holdsW 4649365580aa48ae
theorem AvailableChain.FGSA.Run.FinFormW.holdsW_def 0c25c65a15eb1f5b
structure AvailableChain.FGSA.Run.FinalitySet_W 40ec4cbbe278cb81
ctor AvailableChain.FGSA.Run.FinalitySet_W.mk 6510a75d3b787335
field AvailableChain.FGSA.Run.FinalitySet_W.core 32e8479197f58c64
field AvailableChain.FGSA.Run.FinalitySet_W.bound c190de1b8ce9cc37
field AvailableChain.FGSA.Run.FinalitySet_W.recur cf0f2ef3a64924cf
def AvailableChain.FGSA.Run.finalityWindow_W 257edaf1d0233a74
theorem AvailableChain.FGSA.Run.finalityWindow_W_def 7713675ab497d5a2
structure AvailableChain.FGSA.Run.FirstFinalityPrem_W c314d8eaee212a77
ctor AvailableChain.FGSA.Run.FirstFinalityPrem_W.mk fb8acc4635658b50
field AvailableChain.FGSA.Run.FirstFinalityPrem_W.set 1bc7d398cd0695f6
field AvailableChain.FGSA.Run.FirstFinalityPrem_W.hhor 6a21db1f2b41cbc5
structure AvailableChain.FGSA.Run.FinalityLivenessPrem_W 232aa34cbf1c1c53
ctor AvailableChain.FGSA.Run.FinalityLivenessPrem_W.mk 0862254a917f8cf0
field AvailableChain.FGSA.Run.FinalityLivenessPrem_W.set 0dbead77b5f59c6a
field AvailableChain.FGSA.Run.FinalityLivenessPrem_W.input 93c1b47e3699c98d
field AvailableChain.FGSA.Run.FinalityLivenessPrem_W.start 76d1bab77d8b3d08
field AvailableChain.FGSA.Run.FinalityLivenessPrem_W.hhor 2c9d83ff61292ee1
structure AvailableChain.FGSA.Run.ProposalFinalPrem_W 3254a3969615a5bc
ctor AvailableChain.FGSA.Run.ProposalFinalPrem_W.mk de9dde8bcc583ded
field AvailableChain.FGSA.Run.ProposalFinalPrem_W.set 791697ef56d2aaa8
field AvailableChain.FGSA.Run.ProposalFinalPrem_W.input 5d88105877b8fafb
field AvailableChain.FGSA.Run.ProposalFinalPrem_W.prop ae8e1d6bf58b8e61
field AvailableChain.FGSA.Run.ProposalFinalPrem_W.start 69ce082a6ec1093e
field AvailableChain.FGSA.Run.ProposalFinalPrem_W.hhor 357fbc825a994a87
structure AvailableChain.FGSA.Run.AboveFrontierPrem_W bff07712146b66d9
ctor AvailableChain.FGSA.Run.AboveFrontierPrem_W.mk 0b00cf70f4e94814
field AvailableChain.FGSA.Run.AboveFrontierPrem_W.set 7f2a7ee7d48f4427
field AvailableChain.FGSA.Run.AboveFrontierPrem_W.input 17b49dd96af5ce0f
field AvailableChain.FGSA.Run.AboveFrontierPrem_W.start ad80bb914bae3280
field AvailableChain.FGSA.Run.AboveFrontierPrem_W.firstHorizon 8bcb08337788ef37
field AvailableChain.FGSA.Run.AboveFrontierPrem_W.hhor 81236cf0fc6ebb11
```

### `AvailableChainFGSAClaims.Statements.Packages.FinalityGST`

```text
structure AvailableChain.FGSA.Run.FinalityLivenessGSTPrem_W dacc8c16cb675795
ctor AvailableChain.FGSA.Run.FinalityLivenessGSTPrem_W.mk c2322208f3e2307b
field AvailableChain.FGSA.Run.FinalityLivenessGSTPrem_W.set a88e42b072a57f89
field AvailableChain.FGSA.Run.FinalityLivenessGSTPrem_W.late 41e850d42bd32857
field AvailableChain.FGSA.Run.FinalityLivenessGSTPrem_W.hhor 0562404fad816c62
structure AvailableChain.FGSA.Run.ProposalFinalGSTPrem_W 234fb7797a59aaaf
ctor AvailableChain.FGSA.Run.ProposalFinalGSTPrem_W.mk e91f50622096abdc
field AvailableChain.FGSA.Run.ProposalFinalGSTPrem_W.set cf491e3519945add
field AvailableChain.FGSA.Run.ProposalFinalGSTPrem_W.prop 0256f3d68e8a308d
field AvailableChain.FGSA.Run.ProposalFinalGSTPrem_W.late db1229663894bff0
field AvailableChain.FGSA.Run.ProposalFinalGSTPrem_W.hhor 9411426498806333
structure AvailableChain.FGSA.Run.AboveFrontierGSTPrem_W 31b82724921081e7
ctor AvailableChain.FGSA.Run.AboveFrontierGSTPrem_W.mk df99c39e7a13bf37
field AvailableChain.FGSA.Run.AboveFrontierGSTPrem_W.set 8c81ef40f9a267a6
field AvailableChain.FGSA.Run.AboveFrontierGSTPrem_W.late 6f1831029f32ba51
field AvailableChain.FGSA.Run.AboveFrontierGSTPrem_W.hhor 5857bc77cb4fb9bf
```

### `AvailableChainFGSAClaims.Statements.Packages.Healing`

```text
structure AvailableChain.FGSA.Run.PtU cdac5d36b3aeedbe
ctor AvailableChain.FGSA.Run.PtU.mk 625fb9a6fbf8a302
field AvailableChain.FGSA.Run.PtU.u 40df3815e8005f72
structure AvailableChain.FGSA.Run.PtW eb1adc0bd9b6b352
ctor AvailableChain.FGSA.Run.PtW.mk 711d02cd9776871a
field AvailableChain.FGSA.Run.PtW.w cf526e58be9745f5
structure AvailableChain.FGSA.Run.PtM 059377273aab57dc
ctor AvailableChain.FGSA.Run.PtM.mk e29feda302f8ab79
field AvailableChain.FGSA.Run.PtM.m 4751e98c84b7e6b1
structure AvailableChain.FGSA.Run.PtR 3dd0516b2fc1a7b0
ctor AvailableChain.FGSA.Run.PtR.mk 6f9192a830d167ad
field AvailableChain.FGSA.Run.PtR.r 4752d821807cec4c
structure AvailableChain.FGSA.Run.PtK cf42500a5cf0ea56
ctor AvailableChain.FGSA.Run.PtK.mk 8ef059b2f2ea090a
field AvailableChain.FGSA.Run.PtK.k d4dcaa4e26dd6859
structure AvailableChain.FGSA.Run.HealingPrem 870a5fdcb0911517
ctor AvailableChain.FGSA.Run.HealingPrem.mk 9c996d32df7a4d04
field AvailableChain.FGSA.Run.HealingPrem.set 8483eba91086ae87
field AvailableChain.FGSA.Run.HealingPrem.bound 68fa1574a8ed7f1c
structure AvailableChain.FGSA.Run.HealingWitnessPrem 1b2e091eee3a4482
field AvailableChain.FGSA.Run.HealingWitnessPrem.toHealingPrem 5f448d744bf5ae72
ctor AvailableChain.FGSA.Run.HealingWitnessPrem.mk f30c23e65340ad45
field AvailableChain.FGSA.Run.HealingWitnessPrem.h0 e2f4dab843cee808
structure AvailableChain.FGSA.Run.HealingTimePrem 7a0db15f51f418ad
field AvailableChain.FGSA.Run.HealingTimePrem.toHealingPrem 5f3998d1e63fabc4
ctor AvailableChain.FGSA.Run.HealingTimePrem.mk e405eb7f2276e33b
field AvailableChain.FGSA.Run.HealingTimePrem.hhor 8c8c07a15de1e257
structure AvailableChain.FGSA.Run.ResetArrivalPrem 3a3b4c6ee33121b4
field AvailableChain.FGSA.Run.ResetArrivalPrem.toHealingPrem 14df4052f43a7129
ctor AvailableChain.FGSA.Run.ResetArrivalPrem.mk 80b56a39816417f9
field AvailableChain.FGSA.Run.ResetArrivalPrem.hhor a8b7a2dbd4c208a0
structure AvailableChain.FGSA.Run.ResetArrivalFullPrem b3a18c189ece34a3
field AvailableChain.FGSA.Run.ResetArrivalFullPrem.toHealingPrem 2a8da12af8f09128
ctor AvailableChain.FGSA.Run.ResetArrivalFullPrem.mk b96171144789cf8e
field AvailableChain.FGSA.Run.ResetArrivalFullPrem.hhor 1a18b1146e58b1cd
structure AvailableChain.FGSA.Run.KernelJoinedPrem 24b71b28fda5a0fa
ctor AvailableChain.FGSA.Run.KernelJoinedPrem.mk f93e388edf2c3548
field AvailableChain.FGSA.Run.KernelJoinedPrem.set 6c3be0523a5e574b
field AvailableChain.FGSA.Run.KernelJoinedPrem.bound be33321ad8f63912
field AvailableChain.FGSA.Run.KernelJoinedPrem.window fa1b8a905aefaf66
field AvailableChain.FGSA.Run.KernelJoinedPrem.start 5a1345766cca69d1
field AvailableChain.FGSA.Run.KernelJoinedPrem.hhor 9f897c452bc8fe2c
structure AvailableChain.FGSA.Run.HealingAttemptPrem 857f813484962806
field AvailableChain.FGSA.Run.HealingAttemptPrem.toHealingPrem ef2e397a3d6527bb
ctor AvailableChain.FGSA.Run.HealingAttemptPrem.mk 9f88c72dd5654933
field AvailableChain.FGSA.Run.HealingAttemptPrem.valid f727021ebf0a2039
field AvailableChain.FGSA.Run.HealingAttemptPrem.hhor 4081b3c8ca6ea4db
structure AvailableChain.FGSA.Run.HealingInputPrem d99f0c2f5574d8e1
field AvailableChain.FGSA.Run.HealingInputPrem.toHealingWitnessPrem 4098c9dff54072c3
ctor AvailableChain.FGSA.Run.HealingInputPrem.mk 0ee62792fadde89e
field AvailableChain.FGSA.Run.HealingInputPrem.hhor 7dd19dad1dfec26d
structure AvailableChain.FGSA.Run.RenewedPromotionPrem 060c84e429d8c4ce
field AvailableChain.FGSA.Run.RenewedPromotionPrem.toHealingPrem 210ae1d8e17efcef
ctor AvailableChain.FGSA.Run.RenewedPromotionPrem.mk 6bdf0f1960c533f3
field AvailableChain.FGSA.Run.RenewedPromotionPrem.hhor bf0b6831aeecc0ac
```

### `AvailableChainFGSAClaims.Statements.Packages.Inclusion`

```text
structure AvailableChain.FGSA.Run.CleanInclusionPrem 389c5b8fb783c71f
ctor AvailableChain.FGSA.Run.CleanInclusionPrem.mk 713a18ccc210b9c8
field AvailableChain.FGSA.Run.CleanInclusionPrem.set b7bc6e7db8a20023
field AvailableChain.FGSA.Run.CleanInclusionPrem.prop 6e7ada1dfa00d2c9
field AvailableChain.FGSA.Run.CleanInclusionPrem.hhor 59ea1c3c3c518f04
structure AvailableChain.FGSA.Run.ExactProposalPrem 9770ed4e77cebf05
ctor AvailableChain.FGSA.Run.ExactProposalPrem.mk b1bdb81702034da2
field AvailableChain.FGSA.Run.ExactProposalPrem.set f2135ba82c26db5f
field AvailableChain.FGSA.Run.ExactProposalPrem.prop 15dcc429d4c0c745
field AvailableChain.FGSA.Run.ExactProposalPrem.hhor 72ea9c5c5e737edc
```

### `AvailableChainFGSAClaims.Statements.Packages.Outage`

```text
structure AvailableChain.FGSA.Run.OutagePrem 1cbd730716f4125c
ctor AvailableChain.FGSA.Run.OutagePrem.mk 7c41cc940449eb40
field AvailableChain.FGSA.Run.OutagePrem.set e28d2763714f948f
```

### `AvailableChainFGSAClaims.Statements.Packages.Safety`

```text
structure AvailableChain.FGSA.Run.PtS 3ddf285bec98b83f
ctor AvailableChain.FGSA.Run.PtS.mk e720a461b1a5424f
field AvailableChain.FGSA.Run.PtS.s 5bb84050690af37e
structure AvailableChain.FGSA.Run.PtSP fc8097886eb4d267
ctor AvailableChain.FGSA.Run.PtSP.mk 4958d7d8e28fc3d5
field AvailableChain.FGSA.Run.PtSP.s cf868e7b2f18c993
field AvailableChain.FGSA.Run.PtSP.P a52da557be0edaf9
structure AvailableChain.FGSA.Run.PtSX 24cf4f0edad717bf
ctor AvailableChain.FGSA.Run.PtSX.mk e83b82d3cde3d0fa
field AvailableChain.FGSA.Run.PtSX.s 70175b03c2a302e4
field AvailableChain.FGSA.Run.PtSX.X e89f8f1bdf903974
structure AvailableChain.FGSA.Run.BasePrem 1b4408e2a4a0c11a
ctor AvailableChain.FGSA.Run.BasePrem.mk aa4ea98951391114
field AvailableChain.FGSA.Run.BasePrem.set 2b0c1e4fe061a5f0
structure AvailableChain.FGSA.Run.SameLabelPrem 15e0d24d53de35da
ctor AvailableChain.FGSA.Run.SameLabelPrem.mk 34945a797a2ae18c
field AvailableChain.FGSA.Run.SameLabelPrem.set 856ff30f728442e7
field AvailableChain.FGSA.Run.SameLabelPrem.sync c2a17b0255955408
structure AvailableChain.FGSA.Run.SourceDisciplinePrem b5b0cb92d7118239
ctor AvailableChain.FGSA.Run.SourceDisciplinePrem.mk 625fe398ac47608f
field AvailableChain.FGSA.Run.SourceDisciplinePrem.set 0b6953cdae71fc96
field AvailableChain.FGSA.Run.SourceDisciplinePrem.quorum 29a455fcd6a47327
structure AvailableChain.FGSA.Run.FinalizedSafetyPrem 80f24b5a1907dd97
ctor AvailableChain.FGSA.Run.FinalizedSafetyPrem.mk d1f8a0ca2d15ac9d
field AvailableChain.FGSA.Run.FinalizedSafetyPrem.set 0232b19ff35765fc
field AvailableChain.FGSA.Run.FinalizedSafetyPrem.fault a79d105228104f14
structure AvailableChain.FGSA.Run.CleanPrem 7e447b0e705eef1b
ctor AvailableChain.FGSA.Run.CleanPrem.mk 8c2d4c30b1d57968
field AvailableChain.FGSA.Run.CleanPrem.set 6709327a300a8021
structure AvailableChain.FGSA.Run.CleanPrefixPrem 35cfde88c5f6da06
ctor AvailableChain.FGSA.Run.CleanPrefixPrem.mk 26c7c0874ac03f64
field AvailableChain.FGSA.Run.CleanPrefixPrem.set cc5e56d8f4a066b2
structure AvailableChain.FGSA.Run.CleanCutPrem 5eb98a074bb46e8f
ctor AvailableChain.FGSA.Run.CleanCutPrem.mk 31c335a485dff5a7
field AvailableChain.FGSA.Run.CleanCutPrem.set f6f66429ca4714b5
structure AvailableChain.FGSA.Run.ReleasePrem 56f2ceccee033d1a
ctor AvailableChain.FGSA.Run.ReleasePrem.mk cd2508ce59c5293b
field AvailableChain.FGSA.Run.ReleasePrem.set 6050e4722995ac3f
field AvailableChain.FGSA.Run.ReleasePrem.lt f12b8dc1464df613
```

### `AvailableChainFGSAClaims.Statements.Phases`

```text
def AvailableChain.FGSA.Run.finHeight 45ca642905486866
structure AvailableChain.FGSA.Run.FreshPrem e78058af0cd581d5
ctor AvailableChain.FGSA.Run.FreshPrem.mk a87f693fb4fdca8a
field AvailableChain.FGSA.Run.FreshPrem.base 34222c8f46f23ebc
field AvailableChain.FGSA.Run.FreshPrem.faultQ dc5b56a87b59882e
field AvailableChain.FGSA.Run.FreshPrem.cut 56d7b19d046171c6
field AvailableChain.FGSA.Run.FreshPrem.early 225f857061db9366
field AvailableChain.FGSA.Run.FreshPrem.rows 8ccd41a3078ba74c
field AvailableChain.FGSA.Run.FreshPrem.noNextRow 02b0b3358b5c4076
field AvailableChain.FGSA.Run.FreshPrem.noFinRow 318d0bae8d0f9ad5
def AvailableChain.FGSA.Run.JustifyAt 4f632ffc688bc358
def AvailableChain.FGSA.Run.JustifyFresh_W 697d55fa87ed953b
def AvailableChain.FGSA.Run.Ready_W 15e41e8d55a1288f
def AvailableChain.FGSA.Run.receiptInsert_W fc2da9dc2ed2625f
structure AvailableChain.FGSA.Run.ReceiptWitness_W 96480f7d786199e2
ctor AvailableChain.FGSA.Run.ReceiptWitness_W.mk 1c433d7a0bb74541
field AvailableChain.FGSA.Run.ReceiptWitness_W.index d94469eb94339260
field AvailableChain.FGSA.Run.ReceiptWitness_W.time 4a999c5986ac6c0a
structure AvailableChain.FGSA.Run.BlockDelivery_W 7f5d7ac1fb42db2e
ctor AvailableChain.FGSA.Run.BlockDelivery_W.mk 5de7f3e9af01295a
field AvailableChain.FGSA.Run.BlockDelivery_W.selected 6d29bf516618695f
field AvailableChain.FGSA.Run.BlockDelivery_W.witness b66f6c1878551e89
structure AvailableChain.FGSA.Run.AcceptGuards_W 7f0eff96531909c5
ctor AvailableChain.FGSA.Run.AcceptGuards_W.mk ece2408f6e4ba59d
field AvailableChain.FGSA.Run.AcceptGuards_W.finCmp 79292ddb33dc5aca
field AvailableChain.FGSA.Run.AcceptGuards_W.jPath 1205be8847b25542
field AvailableChain.FGSA.Run.AcceptGuards_W.cap b71c5127054d6d0d
structure AvailableChain.FGSA.Run.AcceptPrem_W fde5f48f808a5a6a
ctor AvailableChain.FGSA.Run.AcceptPrem_W.mk 3f8de2db68d14e49
field AvailableChain.FGSA.Run.AcceptPrem_W.base 2e18e1a443702bb7
field AvailableChain.FGSA.Run.AcceptPrem_W.faultBound 1516a2a69270c666
field AvailableChain.FGSA.Run.AcceptPrem_W.finalized a79c75ddfdd46f85
field AvailableChain.FGSA.Run.AcceptPrem_W.deliver bcac119125698bf1
field AvailableChain.FGSA.Run.AcceptPrem_W.guards 71cc2bbb21e7a427
field AvailableChain.FGSA.Run.AcceptPrem_W.horizon c1afe69cd0c0d40e
def AvailableChain.FGSA.Run.AcceptBefore_W 8e97aade00b51485
structure AvailableChain.FGSA.Run.FinalizePrem_W 95de2ca17128ae1b
ctor AvailableChain.FGSA.Run.FinalizePrem_W.mk 1f7623cdc561ca11
field AvailableChain.FGSA.Run.FinalizePrem_W.fold 94b2748e2b6e19c7
field AvailableChain.FGSA.Run.FinalizePrem_W.base 7806747c8e7786a6
field AvailableChain.FGSA.Run.FinalizePrem_W.faultBound dfb6e0390eb37d49
field AvailableChain.FGSA.Run.FinalizePrem_W.deliver ad607525eb8b07aa
field AvailableChain.FGSA.Run.FinalizePrem_W.guards 464de1eaccbb96a3
field AvailableChain.FGSA.Run.FinalizePrem_W.horizon 36812d8e418399bf
def AvailableChain.FGSA.Run.FinalizePending_W 0c75bd397ea1698b
theorem AvailableChain.FGSA.Run.JustifyAt_def cb9916438df18f33
theorem AvailableChain.FGSA.Run.JustifyFresh_W_def d73b678ce10d8c27
theorem AvailableChain.FGSA.Run.Ready_W_def e95e02c8686b222b
theorem AvailableChain.FGSA.Run.receiptInsert_W_def 31947a53b791e562
theorem AvailableChain.FGSA.Run.AcceptBefore_W_def c128d5417fc61de4
theorem AvailableChain.FGSA.Run.FinalizePending_W_def 029eedf671368e1a
def AvailableChain.FGSA.Run.FreshFinalityRows_W 331db65bae8b7671
structure AvailableChain.FGSA.Run.TerminalCarriagePrem_W 4fad39790b0dfae5
ctor AvailableChain.FGSA.Run.TerminalCarriagePrem_W.mk 0d63361108992f9d
field AvailableChain.FGSA.Run.TerminalCarriagePrem_W.base 95c75d2cc0c180ae
field AvailableChain.FGSA.Run.TerminalCarriagePrem_W.faultQ 478e2cbc03b6d9c5
field AvailableChain.FGSA.Run.TerminalCarriagePrem_W.deltaF 1bb51cc8f6762814
field AvailableChain.FGSA.Run.TerminalCarriagePrem_W.carrier 5de8312c5425a559
field AvailableChain.FGSA.Run.TerminalCarriagePrem_W.parent 46436666b638cc60
field AvailableChain.FGSA.Run.TerminalCarriagePrem_W.path 85d2c47b973a30e2
field AvailableChain.FGSA.Run.TerminalCarriagePrem_W.freshHeight 4f48181e0bd676d6
field AvailableChain.FGSA.Run.TerminalCarriagePrem_W.retainedOrCovered c9a0eacace668ab1
field AvailableChain.FGSA.Run.TerminalCarriagePrem_W.horizon 8cf3773cbb8e70dd
field AvailableChain.FGSA.Run.TerminalCarriagePrem_W.seats a28fba988c8a8d74
field AvailableChain.FGSA.Run.TerminalCarriagePrem_W.rows b905eee45f45d50e
field AvailableChain.FGSA.Run.TerminalCarriagePrem_W.fresh f4c65302cca62190
field AvailableChain.FGSA.Run.TerminalCarriagePrem_W.heightEntry 62510410d7873d4c
field AvailableChain.FGSA.Run.TerminalCarriagePrem_W.receipt 68128c6fcf0516e0
def AvailableChain.FGSA.Run.TerminalCarriage_W fbe1916d63e5a942
theorem AvailableChain.FGSA.Run.FreshFinalityRows_W_def 57094e5b3b6be8c1
theorem AvailableChain.FGSA.Run.TerminalCarriage_W_def 3416588099dd5371
theorem AvailableChain.FGSA.Run.finHeight_def 9b7a4c751f560d6e
```

### `AvailableChainFGSAClaims.Statements.Reads`

```text
def AvailableChain.FGSA.Run.cutPred 3c25f45ea3dd1e64
def AvailableChain.FGSA.Run.afterTicksIdx fa2bf1c57bf37a45
def AvailableChain.FGSA.Run.SuffixIdx c99ac279f60dfd73
def AvailableChain.FGSA.Run.timeIdx 95f9d6305e8acf84
def AvailableChain.FGSA.Run.afterTicks 471393c48a52aa8a
def AvailableChain.FGSA.Run.preTick 214a3db929c139fc
theorem AvailableChain.FGSA.Run.preTick_def 4e0b8b76fc8422d2
def AvailableChain.FGSA.Run.postClock fa10da1ff3118dc7
theorem AvailableChain.FGSA.Run.postClock_def 72ce1732777b08e9
def AvailableChain.FGSA.Run.postTick 4b0ae333cc158bb0
def AvailableChain.FGSA.Run.storeAt 2535bcdea78c7b89
def AvailableChain.FGSA.Run.S_at e26e4ff1a684dfad
def AvailableChain.FGSA.Run.F_at 34e5d05dde7fb4e3
def AvailableChain.FGSA.Run.J_at ff327f809a52e1ea
def AvailableChain.FGSA.Run.gateIn 903a7069ca47e2b5
theorem AvailableChain.FGSA.Run.gateIn_def 276858e425ffe7e7
def AvailableChain.FGSA.Run.gateResult 2ac33bfe4dd9df2e
theorem AvailableChain.FGSA.Run.gateResult_def 72263c2295452a8a
def AvailableChain.FGSA.Run.isGateTime de71406ad46da144
theorem AvailableChain.FGSA.Run.isGateTime_def a991674f5c9d52f5
def AvailableChain.FGSA.Run.IsGateTick 1f29c1e999fcb4a7
def AvailableChain.FGSA.Run.gateResultAt 32f3b51769699e88
def AvailableChain.FGSA.Run.gatePassedAt 7a8b5ba7703d67c5
def AvailableChain.FGSA.Run.fastAt d3445c4834243a31
def AvailableChain.FGSA.Run.headAtIdx 91b9c4bc185cc6b3
def AvailableChain.FGSA.Run.vHead 05269fed05eaac50
theorem AvailableChain.FGSA.Run.vHead_def 0920adf31e84891d
def AvailableChain.FGSA.Run.actionSourceFG 23c8a71e89118bc8
theorem AvailableChain.FGSA.Run.actionSourceFG_def 67d279028dc8736b
def AvailableChain.FGSA.Run.actionSource 553e5b7639459a4d
def AvailableChain.FGSA.Run.labelBoundAt 5017526837dda64f
def AvailableChain.FGSA.Run.DeliveredAt a2bb51c3e876c5b8
def AvailableChain.FGSA.Run.HandlesRowAt fdedb97e0f04e2a3
def AvailableChain.FGSA.Run.AcceptsFinalBefore 6b3afe9f9e6b0d44
def AvailableChain.FGSA.Run.cleanResults 032a6867f03e96ee
def AvailableChain.FGSA.Run.BelowLabel fbd9a06073c519d9
theorem AvailableChain.FGSA.Run.S_at_def dc62fc05a97e8745
```

### `AvailableChainFGSAClaims.Statements.Recurrence`

```text
```

### `AvailableChainFGSAClaims.Statements.Regimes`

```text
structure AvailableChain.FGSA.Run.Base₂ 162ffa15988e6c33
ctor AvailableChain.FGSA.Run.Base₂.mk daf3ce3f676d7a83
field AvailableChain.FGSA.Run.Base₂.valid c2e3118a88ba6287
field AvailableChain.FGSA.Run.Base₂.linked fd086ba4014f4e05
field AvailableChain.FGSA.Run.Base₂.cstar 02c7fbe8fb004737
field AvailableChain.FGSA.Run.Base₂.noRestart e2237444ab2384e9
field AvailableChain.FGSA.Run.Base₂.delta 68176ff33fb35c7b
field AvailableChain.FGSA.Run.Base₂.idealization 5d7d4a2561760d0b
structure AvailableChain.FGSA.Run.HealthyPrefix₂ 9e6946d421c6384c
ctor AvailableChain.FGSA.Run.HealthyPrefix₂.mk f7366530148cb98a
field AvailableChain.FGSA.Run.HealthyPrefix₂.base 8b72685395694cc2
field AvailableChain.FGSA.Run.HealthyPrefix₂.cut 3c2212c71979da56
field AvailableChain.FGSA.Run.HealthyPrefix₂.healthy 11b22244fdef54bf
field AvailableChain.FGSA.Run.HealthyPrefix₂.deltaF e28acf6f8fd340cf
field AvailableChain.FGSA.Run.HealthyPrefix₂.partBefore 2a0af0df97862b6a
structure AvailableChain.FGSA.Run.CleanPrefix₂ 72b286e0987219a1
field AvailableChain.FGSA.Run.CleanPrefix₂.toHealthyPrefix₂ d7f0507f9e73bf2f
ctor AvailableChain.FGSA.Run.CleanPrefix₂.mk 7d405a41315d43b3
field AvailableChain.FGSA.Run.CleanPrefix₂.partAt cbd856fdb9427899
def AvailableChain.FGSA.Run.CleanCut₂ dd3430f0ace2511c
structure AvailableChain.FGSA.Run.Clean₂ 342cb81f8505827e
ctor AvailableChain.FGSA.Run.Clean₂.mk 3a3a3734bd249030
field AvailableChain.FGSA.Run.Clean₂.pre e023db8f4418b048
field AvailableChain.FGSA.Run.Clean₂.gst 5788ef22158a8650
structure AvailableChain.FGSA.Run.Recovery₂ 26c8bf3649f0657f
ctor AvailableChain.FGSA.Run.Recovery₂.mk cca7ff74ace7c59d
field AvailableChain.FGSA.Run.Recovery₂.sync c56e4f2a75575a26
field AvailableChain.FGSA.Run.Recovery₂.deltaF ec6ce0ce35f6bea2
field AvailableChain.FGSA.Run.Recovery₂.gap c31a72c637fab894
field AvailableChain.FGSA.Run.Recovery₂.base 7a4e2fae3ba21629
field AvailableChain.FGSA.Run.Recovery₂.fault 414dd221ecf48db9
field AvailableChain.FGSA.Run.Recovery₂.awake b7de3e61e9647ba4
field AvailableChain.FGSA.Run.Recovery₂.gapPos 3fff3f197a3f5408
def AvailableChain.FGSA.Run.BaseSet e25d76e2ca32b650
def AvailableChain.FGSA.Run.CleanSet 34daabedff4ab5b7
def AvailableChain.FGSA.Run.CleanCutSet 264aa7ca0fee5b50
def AvailableChain.FGSA.Run.CleanPrefixSet ef39a58f533ad899
def AvailableChain.FGSA.Run.HealingSet 9f7eb99282649a1a
def AvailableChain.FGSA.Run.AwakeProposerRecurrenceFrom 33d0f3d1b6ac0b96
structure AvailableChain.FGSA.Run.Outage₂ 0d62d8fea2833818
ctor AvailableChain.FGSA.Run.Outage₂.mk d022fb0f43b3a92e
field AvailableChain.FGSA.Run.Outage₂.pre 4c2ed6d265704073
field AvailableChain.FGSA.Run.Outage₂.sleepy 83f2b2292041e11b
field AvailableChain.FGSA.Run.Outage₂.order d16bce806ba99de5
field AvailableChain.FGSA.Run.Outage₂.lag e31707dc6985b991
field AvailableChain.FGSA.Run.Outage₂.budget bf25ae064beefc2f
field AvailableChain.FGSA.Run.Outage₂.fastPart 4786a66ba4182432
def AvailableChain.FGSA.Run.OutageSet 6b394b0f0d9804ce
```

### `AvailableChainFGSAClaims.Statements.WeakContinuation`

```text
structure AvailableChain.FGSA.Run.StrongRecoverySearchPrefix₂ 15b734c330f74d53
field AvailableChain.FGSA.Run.StrongRecoverySearchPrefix₂.toRecovery₂ b197c9c135dc06f6
ctor AvailableChain.FGSA.Run.StrongRecoverySearchPrefix₂.mk 55b107f5d7ec6549
field AvailableChain.FGSA.Run.StrongRecoverySearchPrefix₂.liveness c67f52eb77323328
field AvailableChain.FGSA.Run.StrongRecoverySearchPrefix₂.endpoint e482a77f6b0ab3ce
structure AvailableChain.FGSA.Run.AgreesThrough₂ b8997781866ad1c4
ctor AvailableChain.FGSA.Run.AgreesThrough₂.mk 0b175299db6b1d26
field AvailableChain.FGSA.Run.AgreesThrough₂.honest 51386aa3b0271d1a
field AvailableChain.FGSA.Run.AgreesThrough₂.gst edf34f79aa8bdd0e
field AvailableChain.FGSA.Run.AgreesThrough₂.delta bedcd580b58b2ed0
field AvailableChain.FGSA.Run.AgreesThrough₂.seats 5d6f5ead57c432e3
field AvailableChain.FGSA.Run.AgreesThrough₂.inputs 11b5e1b69e056a74
field AvailableChain.FGSA.Run.AgreesThrough₂.awake 805aab831f83adab
field AvailableChain.FGSA.Run.AgreesThrough₂.events 8a7a794d66e75eb3
field AvailableChain.FGSA.Run.AgreesThrough₂.suffixTime 23e186e6df1bda47
structure AvailableChain.FGSA.Run.CleanContinuation₂ 91eaa435e92b38a4
ctor AvailableChain.FGSA.Run.CleanContinuation₂.mk 83d68eb3f49dd948
field AvailableChain.FGSA.Run.CleanContinuation₂.base 600ee96832db8ced
field AvailableChain.FGSA.Run.CleanContinuation₂.agrees 7f89f0fe953816fc
field AvailableChain.FGSA.Run.CleanContinuation₂.covered c55f5f461d150af4
field AvailableChain.FGSA.Run.CleanContinuation₂.sync 3300f3e401ead487
field AvailableChain.FGSA.Run.CleanContinuation₂.deltaF f8ff45728c0133da
field AvailableChain.FGSA.Run.CleanContinuation₂.participation cb2a5ea349f4e1d9
structure AvailableChain.FGSA.Run.BoundedHealingCut₂ 0d51d64c392de5f4
ctor AvailableChain.FGSA.Run.BoundedHealingCut₂.mk 404a3d494f486002
field AvailableChain.FGSA.Run.BoundedHealingCut₂.afterGST 6fc9f3ce91b6fc7f
field AvailableChain.FGSA.Run.BoundedHealingCut₂.beforeEnd dc3426768880111d
field AvailableChain.FGSA.Run.BoundedHealingCut₂.cut 32d1ebb1f3b2642e
field AvailableChain.FGSA.Run.BoundedHealingCut₂.actualProposal d0e2481d0eb05703
field AvailableChain.FGSA.Run.BoundedHealingCut₂.refreshed 48bcc53bc2649999
structure AvailableChain.FGSA.Run.SSafeFromCut₂ 40cfba02b089e70a
ctor AvailableChain.FGSA.Run.SSafeFromCut₂.mk 653e503b4c5bbf4f
field AvailableChain.FGSA.Run.SSafeFromCut₂.compatible 11976809c2f2966f
field AvailableChain.FGSA.Run.SSafeFromCut₂.monotone 44ac58facfd0be50
field AvailableChain.FGSA.Run.SSafeFromCut₂.seed 8557b96cf35fe6fe
field AvailableChain.FGSA.Run.SSafeFromCut₂.finalBelow 5ec8496461234956
field AvailableChain.FGSA.Run.SSafeFromCut₂.outputs 108ae0c0fd3cbdb3
def AvailableChain.FGSA.Run.BoundedSafetyRecovery₂ b36268e251f2a1c9
```

### `AvailableChainFGSAClaims.Statements.WeakContinuationLive`

```text
structure AvailableChain.FGSA.Run.WeakContinuationLiveAt₂ 235d509fcfe6895c
ctor AvailableChain.FGSA.Run.WeakContinuationLiveAt₂.mk 39a08de60092c94d
field AvailableChain.FGSA.Run.WeakContinuationLiveAt₂.safety b0332b45e79672ce
field AvailableChain.FGSA.Run.WeakContinuationLiveAt₂.inclusion b113af3880ebadc2
field AvailableChain.FGSA.Run.WeakContinuationLiveAt₂.growth bfe668474ca05c77
def AvailableChain.FGSA.Run.BoundedSafetyLivenessRecovery₂ a25f7e6581a31a0b
theorem AvailableChain.FGSA.Run.BoundedSafetyLivenessRecovery₂_def 9bd08b08375470c3
```

### `AvailableChainFGSAClaims.Statements.Windows`

```text
def AvailableChain.FGSA.Run.WinSpec bd054845d8d1e0ae
structure AvailableChain.FGSA.Run.PtB₀ 1c361d6c128ea00c
ctor AvailableChain.FGSA.Run.PtB₀.mk aa2a197a9df55eeb
field AvailableChain.FGSA.Run.PtB₀.b₀ 7e217271b019a6fe
structure AvailableChain.FGSA.Run.PtT f95204a9e0d403e6
ctor AvailableChain.FGSA.Run.PtT.mk 8dab17e0e2809d52
field AvailableChain.FGSA.Run.PtT.t c32afb93eb197b78
structure AvailableChain.FGSA.Run.PtOut ead6c93e9ea77c06
ctor AvailableChain.FGSA.Run.PtOut.mk f30bb183780a0d12
field AvailableChain.FGSA.Run.PtOut.T 001b9946784cc15c
field AvailableChain.FGSA.Run.PtOut.b₀ fbbe596c7589671a
field AvailableChain.FGSA.Run.PtOut.b₁ 112b2b150c9e3c48
def AvailableChain.FGSA.Run.cleanWinAt 6f605c42bbaaff37
def AvailableChain.FGSA.Run.cleanWin 619120f93b5efb5f
def AvailableChain.FGSA.Run.cleanPrefixWin 60eb3e4dbc5156d0
def AvailableChain.FGSA.Run.cleanLabelWin 459363f5b3b70b39
def AvailableChain.FGSA.Run.gapWin ae1dc19f7091ccd7
def AvailableChain.FGSA.Run.formWinAt 582c1a6cf034d00a
def AvailableChain.FGSA.Run.kernelWin b955dd9dafb6a299
def AvailableChain.FGSA.Run.trigWin f7b50abd86c6d3f6
def AvailableChain.FGSA.Run.outWin b8e14e4999aa4f1b
def AvailableChain.FGSA.Run.TerminalRetention_W fcae20d56cabc8a1
theorem AvailableChain.FGSA.Run.TerminalRetention_W_def 23f17c485239de66
```

### `AvailableChainFGSAClaims.Statements.Witness`

```text
structure AvailableChain.FGSA.Run.HealingWitness 98857114d31fca1b
ctor AvailableChain.FGSA.Run.HealingWitness.mk 533a1ca9d6d6e71f
field AvailableChain.FGSA.Run.HealingWitness.rG 24abf3bc4016a096
field AvailableChain.FGSA.Run.HealingWitness.u₀ a69f530f1425b734
field AvailableChain.FGSA.Run.HealingWitness.M 931bea3059c247b7
field AvailableChain.FGSA.Run.HealingWitness.rStar 4b76ab1c2e507188
field AvailableChain.FGSA.Run.HealingWitness.sStar 2d11909925076825
field AvailableChain.FGSA.Run.HealingWitness.CStar a6650ab30193da26
field AvailableChain.FGSA.Run.HealingWitness.u 53e15c872782e203
field AvailableChain.FGSA.Run.HealingWitness.QStar c0854bdbccdf113f
def AvailableChain.FGSA.Run.tstar 337454ec3bb362a4
theorem AvailableChain.FGSA.Run.tstar_def 3389582619b0d6ee
def AvailableChain.FGSA.Run.oldRowHeights 21050c3b3fb7be43
def AvailableChain.FGSA.Run.muOf 222823839e1ae5ae
def AvailableChain.FGSA.Run.high ca2be6cd67aaf5eb
def AvailableChain.FGSA.Run.honestFrontier f010d243330d4a49
def AvailableChain.FGSA.Run.HeightRow 090c1baef4cea286
structure AvailableChain.FGSA.Run.H0Reset 9b797e612accc59f
ctor AvailableChain.FGSA.Run.H0Reset.mk b78bbf2f7b7aa7b4
field AvailableChain.FGSA.Run.H0Reset.rG_after 3e6e4664147d2d0c
field AvailableChain.FGSA.Run.H0Reset.rG_first d93a1b19de9d1100
field AvailableChain.FGSA.Run.H0Reset.cut b40db8e5b76eb923
field AvailableChain.FGSA.Run.H0Reset.frontier c293867fc394ef94
field AvailableChain.FGSA.Run.H0Reset.rowCap 1aae608149b78b7e
field AvailableChain.FGSA.Run.H0Reset.mu_le 2d45f5af68c32748
field AvailableChain.FGSA.Run.H0Reset.cut_lower 729ba6690c2f4f4e
field AvailableChain.FGSA.Run.H0Reset.cut_upper bd56e73951c93e85
field AvailableChain.FGSA.Run.H0Reset.reset_row 7267177868cec658
field AvailableChain.FGSA.Run.H0Reset.reset_first 208500fbad2ed084
field AvailableChain.FGSA.Run.H0Reset.label fb621bbc00eb2537
field AvailableChain.FGSA.Run.H0Reset.fresh 0b4b729fc210f554
field AvailableChain.FGSA.Run.H0Reset.synchronous 0839d31a17f30ca0
structure AvailableChain.FGSA.Run.H0 fe2784704183d7a1
field AvailableChain.FGSA.Run.H0.toH0Reset aa64dd17f3d9df27
ctor AvailableChain.FGSA.Run.H0.mk b408e53dc6dafe64
field AvailableChain.FGSA.Run.H0.proposal_lower 283ebb1da3d23a52
field AvailableChain.FGSA.Run.H0.proposal d24a28c1bff3eff1
field AvailableChain.FGSA.Run.H0.proposal_first 1b21f811ec694886
field AvailableChain.FGSA.Run.H0.after_gst 8c75cb4f0fd82522
field AvailableChain.FGSA.Run.H0.source_prefix 53dd08149449194f
def AvailableChain.FGSA.Run.tstarOf b05473c83df3aac4
theorem AvailableChain.FGSA.Run.muOf_def 9f21db6cc0c17d03
theorem AvailableChain.FGSA.Run.high_def 943f4315935708a9
```
