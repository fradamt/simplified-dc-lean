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
def AvailableChain.FGSA.finalityView e2c4e266725cbbc0
theorem AvailableChain.FGSA.finalityView_def 55c167904162f852
```

### `AvailableChainFGSA.Statements.Invariants`

```text
inductive AvailableChain.FGSA.Reachable fea16232e7a4f06d
ctor AvailableChain.FGSA.Reachable.init f59f940194817b77
ctor AvailableChain.FGSA.Reachable.tick 226aca6366687204
ctor AvailableChain.FGSA.Reachable.deliver b9bc200aed317062
def AvailableChain.FGSA.NestOK 130e2646fb4577ff
def AvailableChain.FGSA.SACompat f338d5747785cc54
def AvailableChain.FGSA.LeaseBelowOutputStore 5c59d0a0978e86ea
theorem AvailableChain.FGSA.LeaseBelowOutputStore_def 124f6f13f65f43ca
def AvailableChain.FGSA.FastOrigin 55103ff0d11f32d6
structure AvailableChain.FGSA.CStoreInv 345498e4dd5a1965
ctor AvailableChain.FGSA.CStoreInv.mk 89328f1c233c0574
field AvailableChain.FGSA.CStoreInv.fg 248638901e611daf
field AvailableChain.FGSA.CStoreInv.rootInj 6c01cfaa6613cccb
field AvailableChain.FGSA.CStoreInv.baseTree 25f1c413ee92169d
field AvailableChain.FGSA.CStoreInv.saCompat c45a0b9dc9479d0b
field AvailableChain.FGSA.CStoreInv.Smem 9d1b1cd364a2c3d8
field AvailableChain.FGSA.CStoreInv.fastOrigin a916f14958bb5cbc
field AvailableChain.FGSA.CStoreInv.fastDom cdd0a20c933777e7
field AvailableChain.FGSA.CStoreInv.genuineKeys 42536e4a00cd1e32
field AvailableChain.FGSA.CStoreInv.leaseKeys 477159b79c2da050
def AvailableChain.FGSA.Inv0 532a581a2c0a1c7c
structure AvailableChain.FGSA.MetaInv e1df297b65033e12
ctor AvailableChain.FGSA.MetaInv.mk 0754e39317729dd0
field AvailableChain.FGSA.MetaInv.wireTree df1a58ad31546e11
field AvailableChain.FGSA.MetaInv.treeWire 26a1303886b61f16
field AvailableChain.FGSA.MetaInv.proposalsNodup e836180a87b3b88e
field AvailableChain.FGSA.MetaInv.stampKeys 6d90f9bcef684042
field AvailableChain.FGSA.MetaInv.blocksNodup efb9adc68be91d1d
field AvailableChain.FGSA.MetaInv.poolDecodes 6cc15221e99198ee
field AvailableChain.FGSA.MetaInv.poolNodup 05850b8875460fd6
field AvailableChain.FGSA.MetaInv.noGenesisWire f1000d5fccf690ac
def AvailableChain.FGSA.ContentAgree 9f1216009903713b
```

### `AvailableChainFGSA.Statements.Store`

```text
def AvailableChain.FGSA.OutputNestingStored ccfdb94f1c2be5db
def AvailableChain.FGSA.StoreInvariant 46e61127f8675921
structure AvailableChain.FGSA.StoreBundle 6c14973dc070b7bc
ctor AvailableChain.FGSA.StoreBundle.mk cda6e4decdd46e7f
field AvailableChain.FGSA.StoreBundle.cstore 0c4123493dfc9050
field AvailableChain.FGSA.StoreBundle.meta a0f9ef49d26bbc16
field AvailableChain.FGSA.StoreBundle.nest d1d732976728548d
field AvailableChain.FGSA.StoreBundle.lease 7713b0c699b2a82c
def AvailableChain.FGSA.StoreBundleInvariant 485938d14b9e8472
theorem AvailableChain.FGSA.StoreBundleInvariant_def adacfe15f272b1b6
def AvailableChain.FGSA.FMonotone bdeb6c011704b5fc
def AvailableChain.FGSA.MetadataInvariant 65ad7248c775e400
```

### `AvailableChainFGSA.Statements.WindowCertificate`

```text
def AvailableChain.FGSA.Window.projectFinality ba05ae418852b5ca
theorem AvailableChain.FGSA.Window.projectFinality_def 73cc801dfe20c6b2
def AvailableChain.FGSA.Window.projectCertEntry e041d7ad22bd1ba7
theorem AvailableChain.FGSA.Window.projectCertEntry_def 25fe0f85797c49a3
def AvailableChain.FGSA.Window.certificateHeight 534b94c1a2f24f40
theorem AvailableChain.FGSA.Window.certificateHeight_def 241333fc60104452
def AvailableChain.FGSA.Window.certificateFinality 75147f3f96e54f48
theorem AvailableChain.FGSA.Window.certificateFinality_def b146c1863c810d42
def AvailableChain.FGSA.Window.certificateFolded 72e98cb5bac69706
theorem AvailableChain.FGSA.Window.certificateFolded_def 4d8566404fb3bb84
def AvailableChain.FGSA.Window.certificateSelection 8db245578e481f78
theorem AvailableChain.FGSA.Window.certificateSelection_def 82ec07706e18b2c8
def AvailableChain.FGSA.Window.EntryOriginAt f98f289712a35478
theorem AvailableChain.FGSA.Window.EntryOriginAt_def 4335bcdc22894f7a
```

### `AvailableChainFGSA.Statements.WindowEntries`

```text
def AvailableChain.FGSA.Window.RetainedW 741c6c599dd2e060
theorem AvailableChain.FGSA.Window.RetainedW_def edacd5fd4f100831
def AvailableChain.FGSA.Window.CoveredW 00a2635f2a6702f9
theorem AvailableChain.FGSA.Window.CoveredW_def 8f010b7f3cd42345
def AvailableChain.FGSA.Window.EntryBitW 2478fa53ede5093b
theorem AvailableChain.FGSA.Window.EntryBitW_def 974b6508f7ad308e
```

### `AvailableChainFGSA.Statements.WindowHeight`

```text
```

## `AvailableChainFGSARun`

### `AvailableChainFGSARun.Statements.AC`

```text
def AvailableChain.FGSA.Run.fgsaAC c197665b6e30bb4b
```

### `AvailableChainFGSARun.Statements.Acceptance`

```text
def AvailableChain.FGSA.Run.fgsaAdmissionTime bedfcddab6bbb51e
def AvailableChain.FGSA.Run.fgsaTimely c0c2ad54c5e0cdb2
def AvailableChain.FGSA.Run.fgsaAcceptanceInv db34cffd5122c89c
def AvailableChain.FGSA.Run.fgsaTrigger ca09ae953b0f4fc2
```

### `AvailableChainFGSARun.Statements.Client`

```text
def AvailableChain.FGSA.Run.EmitsRow a4860cc37a3db058
def AvailableChain.FGSA.Run.EmittedRowsNoSlash 9e216c30900b3532
def AvailableChain.FGSA.Run.decodeRowObject c65deef1e5daf902
def AvailableChain.FGSA.Run.fgClientEvent 95acbd22212ad5f7
def AvailableChain.FGSA.Run.fgClientEvents 93993eb5f5e604cd
```

### `AvailableChainFGSARun.Statements.Emission`

```text
def AvailableChain.FGSA.Run.EmissionRowsValid 041ac080a7f2aa25
def AvailableChain.FGSA.Run.decode c06272443aaec6cb
def AvailableChain.FGSA.Run.HonestEmissionWellFormed 81711e3d2ce19e52
def AvailableChain.FGSA.Run.HonestProposalDecodes 16c1e66af34cdd26
```

### `AvailableChainFGSARun.Statements.Excludes`

```text
inductive AvailableChain.FGSA.Run.EpochStep 3d42c97be07f96ef
ctor AvailableChain.FGSA.Run.EpochStep.deliver 46432e90eb4f18e1
ctor AvailableChain.FGSA.Run.EpochStep.clock e7dc0a9fb198827d
def AvailableChain.FGSA.Run.Epoch ec94d5700bcdd449
def AvailableChain.FGSA.Run.excludesFixed 2aa11debc4518792
```

### `AvailableChainFGSARun.Statements.Interface`

```text
def AvailableChain.FGSA.Run.isRowObject 46c1a87e68a912bf
theorem AvailableChain.FGSA.Run.isRowObject_def eb00db839d1d7c38
def AvailableChain.FGSA.Run.fgsaDelay 0f058916fd796f4a
theorem AvailableChain.FGSA.Run.fgsaDelay_def 54d3e26d8ba60814
def AvailableChain.FGSA.Run.fgsaInterface 85cd5514811e98f3
def AvailableChain.FGSA.Run.fgsaOutputs 52713af8d05b976d
def AvailableChain.FGSA.Run.finalizedOut 55643171cdfdcd96
```

### `AvailableChainFGSARun.Statements.ReceiptCoverage`

```text
structure AvailableChain.FGSA.Run.ReceiptCoveragePremises d771ed158fc93c42
ctor AvailableChain.FGSA.Run.ReceiptCoveragePremises.mk 4dfdd23dc73c197c
field AvailableChain.FGSA.Run.ReceiptCoveragePremises.within 42522367919e7c29
field AvailableChain.FGSA.Run.ReceiptCoveragePremises.slotWindow f134ab3e41bcc413
field AvailableChain.FGSA.Run.ReceiptCoveragePremises.compat affd641566e6bc5d
field AvailableChain.FGSA.Run.ReceiptCoveragePremises.deadline 88bdaf1ba71d198a
def AvailableChain.FGSA.Run.ReceiptCoverageStatement 1e58652eb9c63fab
theorem AvailableChain.FGSA.Run.ReceiptCoverageStatement_def 8c3418f800231946
```

### `AvailableChainFGSARun.Statements.Receipts`

```text
def AvailableChain.FGSA.Run.blockOf? 594cc77aaa075947
```

### `AvailableChainFGSARun.Statements.Slashing`

```text
def AvailableChain.FGSA.Run.fgsaEvidence 1b9808a1a59c7fca
def AvailableChain.FGSA.Run.fgsaSlashing a8fabe0a65c9176b
```

## `AvailableChainFGSAClaims`

### `AvailableChainFGSAClaims.Claims.Clean`

```text
def AvailableChain.FGSA.Run.CleanHistoryAt 2911c4f1cf653c79
def AvailableChain.FGSA.Run.CleanGateAt d2697d475885e5ee
def AvailableChain.FGSA.Run.CleanTruncAt 4628ce5ebdc49606
def AvailableChain.FGSA.Run.CleanSafetyAt c70b7ad7e46d82e0
def AvailableChain.FGSA.Run.CleanCutClaim 271356c8a3da4880
def AvailableChain.FGSA.Run.CleanCutZeroClaim f3b7617ea6e54f9f
def AvailableChain.FGSA.Run.CleanHistoryClaim 78c837f9bcae396e
def AvailableChain.FGSA.Run.CleanPrefixTruncationClaim a20c389b8c8d79b3
def AvailableChain.FGSA.Run.CleanSafetyClaim 477f3eff00cdded6
def AvailableChain.FGSA.Run.CleanCutPosClaim 015b49ef453a1611
```

### `AvailableChainFGSAClaims.Claims.Finality`

```text
def AvailableChain.FGSA.Run.FinalityKernelClaim_W d081d39a7462a3f5
def AvailableChain.FGSA.Run.KernelACSideClaim_W 8a7008307605da66
def AvailableChain.FGSA.Run.FinalityKernelJoinedClaim_W 2343b43cde126f37
def AvailableChain.FGSA.Run.TailKernelClaim_W a5b443012d2ba6c2
def AvailableChain.FGSA.Run.FinalityLivenessConcl_W 22f5a830093afa51
def AvailableChain.FGSA.Run.FirstFinalityConcl_W 0dbc39302c571b50
def AvailableChain.FGSA.Run.ProposalFinalConcl_W 9a902f0db9dc8800
def AvailableChain.FGSA.Run.AboveFrontierConcl_W abf30553d06dacbc
def AvailableChain.FGSA.Run.FirstFinalityRecFEClaim_W afd7dfa05536f340
def AvailableChain.FGSA.Run.FirstFinalityRecF4Claim_W af5b880209836b4d
def AvailableChain.FGSA.Run.FinalityLivenessRecFEClaim_W 1d727c737b46c077
def AvailableChain.FGSA.Run.FinalityLivenessRecF4Claim_W 90bb52bbcf245b70
def AvailableChain.FGSA.Run.ProposalFinalRecFEClaim_W 8e1defc080ff8b69
def AvailableChain.FGSA.Run.ProposalFinalRecF4Claim_W 52eabff641ff95e4
def AvailableChain.FGSA.Run.AboveFrontierRecFEClaim_W 2fd789227508f890
def AvailableChain.FGSA.Run.AboveFrontierRecF4Claim_W 9a15bc59bde68c58
def AvailableChain.FGSA.Run.FinalityLivenessGSTClaim_W ad42fa3c074490c3
def AvailableChain.FGSA.Run.ProposalFinalGSTClaim_W ac8a6a461e3d2484
def AvailableChain.FGSA.Run.AboveFrontierGSTClaim_W 39fdaf18e2556eff
```

### `AvailableChainFGSAClaims.Claims.Foundations`

```text
def AvailableChain.FGSA.Run.ClientSafeAll 5468ec33d95b2d0b
def AvailableChain.FGSA.Run.ClientSafetyClaim bbd169e9289fa695
def AvailableChain.FGSA.Run.ClientSafetyBaseClaim b12465ca3a450751
def AvailableChain.FGSA.Run.FGFoundationClaim 885320e9a27d0fe2
def AvailableChain.FGSA.Run.SrcFrameAboveClaim 7bcfd945fcecbb00
def AvailableChain.FGSA.Run.RunFGBlock 2223369bcc90f1f2
def AvailableChain.FGSA.Run.CarrierAt 3631acb75f4a758f
def AvailableChain.FGSA.Run.StoreAt 967d09e6652038ba
def AvailableChain.FGSA.Run.ActiveViewAt 3a9be63127326237
def AvailableChain.FGSA.Run.LeaseOriginsAt aa2777b4cf8649e2
def AvailableChain.FGSA.Run.SourceDisciplineBaseAt 4b50d12a26076005
def AvailableChain.FGSA.Run.SourceDisciplineAt fd2e0925d69b9c5d
def AvailableChain.FGSA.Run.CarrierClaim dadc50489a1b7b69
def AvailableChain.FGSA.Run.ChainCertificatesAt 7d9e1b2f7c0ac454
def AvailableChain.FGSA.Run.ChainCertificatesClaim 6bcdb792aff5fad1
def AvailableChain.FGSA.Run.StoreClaim b290614759624f4a
def AvailableChain.FGSA.Run.ActiveViewClaim 301e282106aaef21
def AvailableChain.FGSA.Run.LeaseOriginsClaim e841e826310601cd
def AvailableChain.FGSA.Run.ReconcileAt 0b854ac1559f9330
def AvailableChain.FGSA.Run.ReconcileClaim af1d38f2cca63e46
def AvailableChain.FGSA.Run.OutputNestingAt d77c4aeb946a7b3e
def AvailableChain.FGSA.Run.OutputNestingClaim 968d6e935a21d5b0
def AvailableChain.FGSA.Run.FrameAt 134bf3f8f7a8ecce
def AvailableChain.FGSA.Run.FrameClaim 83ca4fda79b18c4b
def AvailableChain.FGSA.Run.SourceDisciplineBaseClaim ea163331d5ffc4bb
def AvailableChain.FGSA.Run.SourceDisciplineClaim 1532a8b60f82f3c6
def AvailableChain.FGSA.Run.RowServiceBaseClaim 643d0c202aa52c87
def AvailableChain.FGSA.Run.RowServiceClaim ab1f29952a6b3ced
def AvailableChain.FGSA.Run.PureAccountableClaim 72fcb4798c509c59
def AvailableChain.FGSA.Run.PureAgreementClaim fb7e3a3f9faeff52
def AvailableChain.FGSA.Run.WholeRunAccountableClaim 2d2a586da5db7edd
def AvailableChain.FGSA.Run.WholeRunAgreementClaim f28a7e91d622feb0
def AvailableChain.FGSA.Run.EventPrefixAgreementClaim 1e5c67c4191cf236
def AvailableChain.FGSA.Run.FaultCountSlashableBoundClaim d7a3f1ef27e0e0b7
def AvailableChain.FGSA.Run.FinalizedMonotonicityClaim c1b39a63f208eccd
def AvailableChain.FGSA.Run.HonestNeverSlashedClaim 2a4aac9c0665320f
def AvailableChain.FGSA.Run.FinalizedSafetyConcl 9c9671910764a659
def AvailableChain.FGSA.Run.FinalizedSafetyClaim 8edd0df6a2d0ce99
def AvailableChain.FGSA.Run.FinalLockClaim d36e9394a7c1b72d
```

### `AvailableChainFGSAClaims.Claims.Healing`

```text
def AvailableChain.FGSA.Run.RowPermissionAt 1c910b23821e75e4
def AvailableChain.FGSA.Run.RowPermissionClaim a0780a2e37256eec
def AvailableChain.FGSA.Run.HealingInputClaim bfbca1c66667cb06
def AvailableChain.FGSA.Run.HTimeConcl 175d04c1574329c3
def AvailableChain.FGSA.Run.HTimeClaim f5d61d7a7a37297c
def AvailableChain.FGSA.Run.ResetArrivalConcl 7c58d028a7438644
def AvailableChain.FGSA.Run.ResetArrivalClaim d91804917b1c03c6
def AvailableChain.FGSA.Run.RenewedPromotionConcl 5706de43765b9044
def AvailableChain.FGSA.Run.RenewedPromotionClaim 834e4d2fba3a6f2e
def AvailableChain.FGSA.Run.HTimeBestClaim f001679c4117ae06
def AvailableChain.FGSA.Run.HTimeSearchClaim c672eabdb0aefd80
```

### `AvailableChainFGSAClaims.Claims.Outage`

```text
def AvailableChain.FGSA.Run.ExactProposalAt cb651c94fadc426b
def AvailableChain.FGSA.Run.ExactProposalClaim 60e32b0504e08cab
def AvailableChain.FGSA.Run.InclusionPostGateAt 06ebe08a63b80d3a
def AvailableChain.FGSA.Run.InclusionAt 25722c6ab48881d9
def AvailableChain.FGSA.Run.CleanInclusionPostGateClaim 91a92aac89fff4a2
def AvailableChain.FGSA.Run.CleanInclusionClaim d8d2f023cf6ae252
def AvailableChain.FGSA.Run.DutiesExtendOn be68a5c7dfa5def5
def AvailableChain.FGSA.Run.FCompatBefore 387aab948ad0dc3b
def AvailableChain.FGSA.Run.P1Concl 2f1a80fdb8e29ee8
def AvailableChain.FGSA.Run.LeaseOrFFrom ddcc71e78b104a81
def AvailableChain.FGSA.Run.OutageCompatAt 16c692b3d53580cf
def AvailableChain.FGSA.Run.OutageCompatClaim c142860a5fbd6239
def AvailableChain.FGSA.Run.FastP1Claim 1c5b0b74bed093d5
def AvailableChain.FGSA.Run.SlowP1Claim 6a6894b3f3979058
def AvailableChain.FGSA.Run.AvailableFromConcl 9ae879d33eb30b54
def AvailableChain.FGSA.Run.AvailableGrowthConcl 2b050e224aaead83
def AvailableChain.FGSA.Run.AvailableGSTClaim d62ed92834157a3c
def AvailableChain.FGSA.Run.AvailableGrowthGSTClaim 6dd1e1356af1e024
def AvailableChain.FGSA.Run.CleanGrowthClaim b345cc1a9ac2a929
```

### `AvailableChainFGSAClaims.Claims.Shared`

```text
def AvailableChain.FGSA.Run.SameLabelAt bc227bbff603d5ab
def AvailableChain.FGSA.Run.SameLabelClaim 5a69cc370ceba758
def AvailableChain.FGSA.Run.HeadReachesLoAt cddd48e87afe1ae5
def AvailableChain.FGSA.Run.HeadReachesLoClaim 91b2c5c9cdc6cbee
def AvailableChain.FGSA.Run.ReleaseStoreAt e83760d4e3844d23
def AvailableChain.FGSA.Run.ReleaseStoreClaim 543b8ade45fd298f
def AvailableChain.FGSA.Run.ReleaseAt cc9011ff8e5aba09
def AvailableChain.FGSA.Run.ReleaseClaim 7ce1c9e2699ad4a8
```

### `AvailableChainFGSAClaims.Claims.WeakContinuation`

```text
def AvailableChain.FGSA.Run.WeakContinuationClaim 7343e86e8a87d8c1
def AvailableChain.FGSA.Run.WeakContinuationLiveClaim c3dc6104736035e7
```

### `AvailableChainFGSAClaims.FGSAClaims`

```text
structure AvailableChain.FGSA.Run.FGSASafetyClaims b12cba834fbc983b
ctor AvailableChain.FGSA.Run.FGSASafetyClaims.mk 21d6d2a32bda593f
field AvailableChain.FGSA.Run.FGSASafetyClaims.carrier 0220620f37433be0
field AvailableChain.FGSA.Run.FGSASafetyClaims.chainCertificates 5caed0ddb5506319
field AvailableChain.FGSA.Run.FGSASafetyClaims.store f5a7771b8a4e2544
field AvailableChain.FGSA.Run.FGSASafetyClaims.activeView bc30688c6e34261f
field AvailableChain.FGSA.Run.FGSASafetyClaims.leaseOrigins fa0b6a71ecf0f0be
field AvailableChain.FGSA.Run.FGSASafetyClaims.reconcile 51abee43b25e7912
field AvailableChain.FGSA.Run.FGSASafetyClaims.outputNesting 16accf0cb41161e1
field AvailableChain.FGSA.Run.FGSASafetyClaims.frame 13c784e56758b22a
field AvailableChain.FGSA.Run.FGSASafetyClaims.clientSafety 32c66453f15fa0aa
field AvailableChain.FGSA.Run.FGSASafetyClaims.clientSafetyBase 5441e56e5cefca5f
field AvailableChain.FGSA.Run.FGSASafetyClaims.sourceDisciplineBase e32fc5ffc548b55b
field AvailableChain.FGSA.Run.FGSASafetyClaims.sourceDiscipline 62f89c9706a69001
field AvailableChain.FGSA.Run.FGSASafetyClaims.sameLabel c0a9f392a6268f43
field AvailableChain.FGSA.Run.FGSASafetyClaims.releaseStore 4fdb157a0f058064
field AvailableChain.FGSA.Run.FGSASafetyClaims.release 53a5f61a0379d091
field AvailableChain.FGSA.Run.FGSASafetyClaims.headReachesLo bcfaa1a56523ad59
field AvailableChain.FGSA.Run.FGSASafetyClaims.cleanCut ddbeb0859d4480a7
field AvailableChain.FGSA.Run.FGSASafetyClaims.cleanHistory cc704615b3fc6320
field AvailableChain.FGSA.Run.FGSASafetyClaims.cleanPrefixTruncation 2e016c0b0a627b50
field AvailableChain.FGSA.Run.FGSASafetyClaims.cleanSafety 8b5921ea39bd6a4a
structure AvailableChain.FGSA.Run.FGSASafetyInterfaces d6b97d00e3110828
ctor AvailableChain.FGSA.Run.FGSASafetyInterfaces.mk 7793b9e23753784b
field AvailableChain.FGSA.Run.FGSASafetyInterfaces.fgFoundation e64a26407efe75bc
field AvailableChain.FGSA.Run.FGSASafetyInterfaces.srcFrameAbove d4e0ec5b68e439fc
field AvailableChain.FGSA.Run.FGSASafetyInterfaces.cpPrefix 3d2f5770576b8e2e
field AvailableChain.FGSA.Run.FGSASafetyInterfaces.cpCompat a18110e00c7161b9
field AvailableChain.FGSA.Run.FGSASafetyInterfaces.tSrc af702c8391753249
field AvailableChain.FGSA.Run.FGSASafetyInterfaces.labelBound 775da09961a4df2d
field AvailableChain.FGSA.Run.FGSASafetyInterfaces.timingContract 6f53ee395e5b0ce2
structure AvailableChain.FGSA.Run.FGSAFinalityClaims a383cd8a2751faca
ctor AvailableChain.FGSA.Run.FGSAFinalityClaims.mk 66894dd0d5b35aa9
field AvailableChain.FGSA.Run.FGSAFinalityClaims.accountable b9b9233ed06b995e
field AvailableChain.FGSA.Run.FGSAFinalityClaims.agreement 32ce7aaa56ea5495
field AvailableChain.FGSA.Run.FGSAFinalityClaims.runAccountable cc1d0467c6509bae
field AvailableChain.FGSA.Run.FGSAFinalityClaims.runAgreement 3afdf6674946c057
field AvailableChain.FGSA.Run.FGSAFinalityClaims.eventPrefixAgreement 19ad5a913cc0fb7b
field AvailableChain.FGSA.Run.FGSAFinalityClaims.faultCountSlashableBound aa484228245f81b6
field AvailableChain.FGSA.Run.FGSAFinalityClaims.finalizedMonotone de243b029c6a8833
field AvailableChain.FGSA.Run.FGSAFinalityClaims.honestNeverSlashed 46ebc39e22b4559f
structure AvailableChain.FGSA.Run.FGSAClaims ed767df9cd2f9bb8
field AvailableChain.FGSA.Run.FGSAClaims.toFGSASafetyClaims 7dcccd1d8f8fa845
ctor AvailableChain.FGSA.Run.FGSAClaims.mk cf31270b944931f3
field AvailableChain.FGSA.Run.FGSAClaims.finality 556a3ea80b476941
field AvailableChain.FGSA.Run.FGSAClaims.finalizedSafety 01c0b054de1ff758
field AvailableChain.FGSA.Run.FGSAClaims.finalLock 9061028f34e0e091
field AvailableChain.FGSA.Run.FGSAClaims.outageCompat dedf2a757d1c06c1
field AvailableChain.FGSA.Run.FGSAClaims.fastP1 d5a67266a6dd02c1
field AvailableChain.FGSA.Run.FGSAClaims.slowP1 619a4cd8b7da825e
field AvailableChain.FGSA.Run.FGSAClaims.exactProposal 6560e29e27272c7a
field AvailableChain.FGSA.Run.FGSAClaims.cleanInclusionPostGate b24966c46482afe9
field AvailableChain.FGSA.Run.FGSAClaims.cleanInclusion 9366ec489dc78a3a
field AvailableChain.FGSA.Run.FGSAClaims.firstFinalityRecFE 6ccc22317725e48e
field AvailableChain.FGSA.Run.FGSAClaims.firstFinalityRecF4 8590c7c392b2ec09
field AvailableChain.FGSA.Run.FGSAClaims.finalityLivenessGSTRecFE 77108ea6c8ddeef6
field AvailableChain.FGSA.Run.FGSAClaims.finalityLivenessGSTRecF4 c49fa3d74fae10b4
field AvailableChain.FGSA.Run.FGSAClaims.proposalFinalGSTRecFE 25f958ece9985d1f
field AvailableChain.FGSA.Run.FGSAClaims.proposalFinalGSTRecF4 e6662179f03825a8
field AvailableChain.FGSA.Run.FGSAClaims.aboveFrontierGSTRecFE 9ec77815141c10c4
field AvailableChain.FGSA.Run.FGSAClaims.aboveFrontierGSTRecF4 e8731bce870cdc58
field AvailableChain.FGSA.Run.FGSAClaims.availableGST 6e7e68c4ae24e1b2
field AvailableChain.FGSA.Run.FGSAClaims.availableGrowthGST 631b4ac7cce7df56
field AvailableChain.FGSA.Run.FGSAClaims.cleanGrowth e9f51e9173701ed5
```

### `AvailableChainFGSAClaims.Statements.Bounds`

```text
def AvailableChain.FGSA.Run.L 8d4e932a42cf7b48
def AvailableChain.FGSA.Run.P f47871c3f7f4e6ab
def AvailableChain.FGSA.Run.Γ 6e4892a24a1b40ec
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
def AvailableChain.FGSA.Run.RCarrierView 40dd9bca1b6dc60f
theorem AvailableChain.FGSA.Run.RCarrierView_def da823c0e6a695336
def AvailableChain.FGSA.Run.RStore a1536347b788bc11
theorem AvailableChain.FGSA.Run.RStore_def 77e31cdd75e7613d
def AvailableChain.FGSA.Run.RActive 9740d2582e245648
theorem AvailableChain.FGSA.Run.RActive_def 0deb5d55c130ce1e
def AvailableChain.FGSA.Run.RStoreCumul 05aaeb629317cdeb
theorem AvailableChain.FGSA.Run.RStoreCumul_def a23c77e100ae31cf
def AvailableChain.FGSA.Run.RMono f3faf75aa51c57e0
theorem AvailableChain.FGSA.Run.RMono_def e7ffa26d88e256d2
def AvailableChain.FGSA.Run.RFrameExact 377cca22288d0874
theorem AvailableChain.FGSA.Run.RFrameExact_def 85da4cd2ef5aa3f4
def AvailableChain.FGSA.Run.RFrame d7bdd7453f480f8f
theorem AvailableChain.FGSA.Run.RFrame_def c542cd9331b44062
def AvailableChain.FGSA.Run.RGeo f3c03ceee93f1e0e
theorem AvailableChain.FGSA.Run.RGeo_def 027862b5cb616745
def AvailableChain.FGSA.Run.RCert 4d7aa85bc4ff7a24
theorem AvailableChain.FGSA.Run.RCert_def 8e983a34e0b1ec22
def AvailableChain.FGSA.Run.RRec 34e773ec8b250b77
theorem AvailableChain.FGSA.Run.RRec_def 1c08e6520262e555
def AvailableChain.FGSA.Run.TSrc c7a11b79ca401649
theorem AvailableChain.FGSA.Run.TSrc_def c6ed3d18b3047d1d
def AvailableChain.FGSA.Run.LabelBound 2df9d3c0835d2eb5
theorem AvailableChain.FGSA.Run.LabelBound_def 4d983d3bd95c8aa6
def AvailableChain.FGSA.Run.TChain 92c8c6f9326c779d
theorem AvailableChain.FGSA.Run.TChain_def aee79fc5864e636a
def AvailableChain.FGSA.Run.TCompat 1228b92050647ca0
theorem AvailableChain.FGSA.Run.TCompat_def 26d4f570c0013a10
structure AvailableChain.FGSA.Run.AncestorClosed a82d5e35de829ed2
ctor AvailableChain.FGSA.Run.AncestorClosed.mk fa2827ea0465c6d5
field AvailableChain.FGSA.Run.AncestorClosed.down 6a9b1aab4f3ebb3e
def AvailableChain.FGSA.Run.FrameBelow 2e13106f5cdb3da0
theorem AvailableChain.FGSA.Run.FrameBelow_def 7e57286905f105b2
def AvailableChain.FGSA.Run.RStrat 34043dd16cb04f31
theorem AvailableChain.FGSA.Run.RStrat_def decab20da3d96d03
def AvailableChain.FGSA.Run.RQCOrigin 76344d245f5d169c
theorem AvailableChain.FGSA.Run.RQCOrigin_def aba8da742abbe7d0
def AvailableChain.FGSA.Run.SrcFrameAbove 5b7e27c9eecdd3b0
theorem AvailableChain.FGSA.Run.SrcFrameAbove_def fe81350f827417b8
def AvailableChain.FGSA.Run.SrcFrame 20c78197b37d593a
def AvailableChain.FGSA.Run.SrcFrameAboveStmt 2a9b67aea7604c6a
theorem AvailableChain.FGSA.Run.SrcFrameAboveStmt_def d81be50fafe4377c
def AvailableChain.FGSA.Run.CPPrefix 0ba08b2a23983c08
theorem AvailableChain.FGSA.Run.CPPrefix_def ee68d48dc5e7b4e9
def AvailableChain.FGSA.Run.CPCompat b676864ddfaa8acd
theorem AvailableChain.FGSA.Run.CPCompat_def 25a2be49af45717a
def AvailableChain.FGSA.Run.RXing d0a56afa972c020a
def AvailableChain.FGSA.Run.RCap ed791eead8e24ef2
def AvailableChain.FGSA.Run.THigh d57dc8f86186542f
def AvailableChain.FGSA.Run.TCarrier fe9409dc42f3c3a4
def AvailableChain.FGSA.Run.TRowsSelect 79fc83e217bab274
def AvailableChain.FGSA.Run.TRowsSync 2cffe2c054e61d69
def AvailableChain.FGSA.Run.TRowsReceipt f7ee299943bc3024
theorem AvailableChain.FGSA.Run.TRowsReceipt_def 6c1597898a5b87a8
structure AvailableChain.FGSA.Run.TRows e0f3f07b8c532a73
ctor AvailableChain.FGSA.Run.TRows.mk 47a16213e0a5cf86
field AvailableChain.FGSA.Run.TRows.select e6954dc109cdea16
field AvailableChain.FGSA.Run.TRows.sync 05ce5be54e1c9666
field AvailableChain.FGSA.Run.TRows.receipt e92a235356e46c3d
def AvailableChain.FGSA.Run.SourceBefore 524de7fdaf97b048
def AvailableChain.FGSA.Run.Kept 45af8ac3e7a51fdc
def AvailableChain.FGSA.Run.KeepOrCause 5f98b01df78eca57
def AvailableChain.FGSA.Run.RExcl 5cfa659504a2d266
def AvailableChain.FGSA.Run.RKeep b1c689968ded2e9e
def AvailableChain.FGSA.Run.RFProv 4db76189c57546a5
def AvailableChain.FGSA.Run.TDel 857bf49dc79c72fb
def AvailableChain.FGSA.Run.TDelReset 48468fcc661e2d05
def AvailableChain.FGSA.Run.TGeom 5c1109000595a5a6
def AvailableChain.FGSA.Run.ExactService 648ec32709cc12a9
def AvailableChain.FGSA.Run.PhaseInterval acbc38f7b24b8ff0
def AvailableChain.FGSA.Run.Transfers 9f79cc67a1ae4eff
def AvailableChain.FGSA.Run.PhaseBody dcee5ee2a798f402
def AvailableChain.FGSA.Run.TPerm b00b4ab81e979e0b
def AvailableChain.FGSA.Run.ProposalGap 1d909e8399fb9685
def AvailableChain.FGSA.Run.RepairAfter 78ed2a3d8e8bc06c
def AvailableChain.FGSA.Run.TRepair de45f33bb12274cd
def AvailableChain.FGSA.Run.OpeningCovered 18b7a10efd09c74f
def AvailableChain.FGSA.Run.OpeningEntry b07b2043c3d3ead4
def AvailableChain.FGSA.Run.TCommon ae431fa50bd35733
def AvailableChain.FGSA.Run.TFrontier ff29b68dfe2d4c42
def AvailableChain.FGSA.Run.FinalityRowCarriage 02ab956f748c5b90
theorem AvailableChain.FGSA.Run.FinalityRowCarriage_def 2bafc2918220a116
```

### `AvailableChainFGSAClaims.Statements.Channels`

```text
def AvailableChain.FGSA.Run.certified a89ddf0a7a24ebc5
theorem AvailableChain.FGSA.Run.certified_def 6669abc5a8f0fc8e
def AvailableChain.FGSA.Run.treeT 2b69ec7b0e57e60e
def AvailableChain.FGSA.Run.treeErased 781b0a26d002a754
def AvailableChain.FGSA.Run.frameR 795a9a08fb7cf90e
def AvailableChain.FGSA.Run.domainR b6007be9f764ac54
def AvailableChain.FGSA.Run.finR aac46ba18b4700c2
def AvailableChain.FGSA.Run.FAdvance 295788c25e134f22
def AvailableChain.FGSA.Run.sourceCandidates 15ae2568da2c93f7
def AvailableChain.FGSA.Run.jointSource a8e774b37966a38f
def AvailableChain.FGSA.Run.proposerHead 4848c6880d5bdd2a
def AvailableChain.FGSA.Run.outputS f3f1bf40e501d936
theorem AvailableChain.FGSA.Run.outputS_def 6f0e9f78ba8dc35c
theorem AvailableChain.FGSA.Run.frameR_def e647c3d9dd45e6b3
theorem AvailableChain.FGSA.Run.jointSource_def eadd593b9688b0c7
theorem AvailableChain.FGSA.Run.sourceCandidates_def a419a14c1319e0ab
theorem AvailableChain.FGSA.Run.domainR_def 6c0d28aeb87659e2
theorem AvailableChain.FGSA.Run.treeT_def 3acc17fc60e79846
theorem AvailableChain.FGSA.Run.proposerHead_def 3e2bb21a33588f06
theorem AvailableChain.FGSA.Run.FAdvance_def 910b82c4a0274160
def AvailableChain.FGSA.Run.R_at a1cefbbf232fd55a
def AvailableChain.FGSA.Run.D_at ca164e67f4c9722a
def AvailableChain.FGSA.Run.FAdvanceAt d54dc7022be3a514
def AvailableChain.FGSA.Run.candidatesAt 46abe865653ba6c4
def AvailableChain.FGSA.Run.proposalHeadAt 66c44c3194b4400a
def AvailableChain.FGSA.Run.actionHead 44b859afb75004f7
def AvailableChain.FGSA.Run.actionTriple b8580461eb1f2a57
def AvailableChain.FGSA.Run.namedEntry a50c73e0c7ee36db
def AvailableChain.FGSA.Run.EntryBelow 8a1bd8bb5b374ead
def AvailableChain.FGSA.Run.RowSigner e137c56cda2c9bb8
def AvailableChain.FGSA.Run.HonestRowAt 5bd309f1cfd131ea
def AvailableChain.FGSA.Run.HonestRowBefore f6953ec09b1bbebf
theorem AvailableChain.FGSA.Run.HonestRowBefore_def cebc3f6527bcda2b
def AvailableChain.FGSA.Run.RowComplete 0dc20c20996a0fc4
def AvailableChain.FGSA.Run.HonestCarrier e65fd8670f5897ac
def AvailableChain.FGSA.Run.HeldAt 3921e2109a1bf6f0
def AvailableChain.FGSA.Run.BlockInRunBefore 1330ef54102dd8ee
theorem AvailableChain.FGSA.Run.RowSigner_def 480488de9793759b
theorem AvailableChain.FGSA.Run.HonestRowAt_def 11c777e073ae0ead
def AvailableChain.FGSA.Run.rowHeld 10b14191989e4cf6
def AvailableChain.FGSA.Run.proposalStateAt beefc1b220cf998c
def AvailableChain.FGSA.Run.heldAtProposal 8791e928438869cc
def AvailableChain.FGSA.Run.onParentChain 682f7b550789d973
def AvailableChain.FGSA.Run.HeldBefore 7fefae0d8623c7df
def AvailableChain.FGSA.Run.ValidForParent 7dc86a1f2d227c59
theorem AvailableChain.FGSA.Run.ValidForParent_def afbdef6d40ecdd90
def AvailableChain.FGSA.Run.HeightMatch 08cbd4e2a4572b2f
theorem AvailableChain.FGSA.Run.HeightMatch_def 6dab81f044f4f4b3
def AvailableChain.FGSA.Run.headAtLabel 11a6197ae324c6ff
theorem AvailableChain.FGSA.Run.RowComplete_def 7658fcce09dc2a7c
theorem AvailableChain.FGSA.Run.HonestCarrier_def f7bfbe79dc6bd98f
theorem AvailableChain.FGSA.Run.HeldAt_def d159b86605f14840
theorem AvailableChain.FGSA.Run.namedEntry_def f3827e3bef137733
```

### `AvailableChainFGSAClaims.Statements.ComposeStmt`

```text
def AvailableChain.FGSA.Run.windowIdx eaabfff46933e92b
structure AvailableChain.FGSA.Run.TimingContract 578137ce153a10b0
ctor AvailableChain.FGSA.Run.TimingContract.mk 864f6148856c6693
field AvailableChain.FGSA.Run.TimingContract.rowLag 7f0ec2576d87dbe8
field AvailableChain.FGSA.Run.TimingContract.certLag 71858c5e00d0b585
field AvailableChain.FGSA.Run.TimingContract.label 529593837f9a8761
field AvailableChain.FGSA.Run.TimingContract.atomic a5728e599cb3bf59
field AvailableChain.FGSA.Run.TimingContract.tickFG 390bf1b7f5befbdb
structure AvailableChain.FGSA.Run.FGFoundation 120025d0e1d450c4
ctor AvailableChain.FGSA.Run.FGFoundation.mk 4343a1f6a87c48e4
field AvailableChain.FGSA.Run.FGFoundation.store aad062ba1953fbf5
field AvailableChain.FGSA.Run.FGFoundation.cumul e88fe644ed61a9e7
field AvailableChain.FGSA.Run.FGFoundation.mono 21fa149a351b628f
field AvailableChain.FGSA.Run.FGFoundation.frame d0c62f4dec651e86
field AvailableChain.FGSA.Run.FGFoundation.geo 8648d156f3ce6d9d
field AvailableChain.FGSA.Run.FGFoundation.strat 428a7f5f473dcd7e
field AvailableChain.FGSA.Run.FGFoundation.reconcile 29935f1c44c78bfb
def AvailableChain.FGSA.Run.TStart 60a7b3c14cd52e86
def AvailableChain.FGSA.Run.FullVoteService 5950066da334a737
def AvailableChain.FGSA.Run.TVote 4ae984bca3332710
def AvailableChain.FGSA.Run.WalkBatch 061b8a6c63afd221
def AvailableChain.FGSA.Run.TWalk 6b3dd888905b5488
structure AvailableChain.FGSA.Run.CoreServices 9e726e2b8b496a7d
ctor AvailableChain.FGSA.Run.CoreServices.mk 929b31ca231ea420
field AvailableChain.FGSA.Run.CoreServices.start cc473362f3ae1259
field AvailableChain.FGSA.Run.CoreServices.vote 76e378d329fe7bbd
field AvailableChain.FGSA.Run.CoreServices.walk 99e7f91e5f5960cd
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
def AvailableChain.FGSA.Run.ResetArrivalStatement 9ab8d938a9ccc1ba
theorem AvailableChain.FGSA.Run.ResetArrivalStatement_def d6132dca93872274
def AvailableChain.FGSA.Run.ResetArrivalFullStatement d9b679577c1daaf8
theorem AvailableChain.FGSA.Run.ResetArrivalFullStatement_def 00971b6fc6f04393
structure AvailableChain.FGSA.Run.KernelPt 9235f1fbc5c48477
ctor AvailableChain.FGSA.Run.KernelPt.mk 32c96b623cc6f691
field AvailableChain.FGSA.Run.KernelPt.w 6cbd0d7075070f20
field AvailableChain.FGSA.Run.KernelPt.r e581c6d88b7635d7
def AvailableChain.FGSA.Run.kernelStart 57c052413c823243
def AvailableChain.FGSA.Run.OpeningCarrier_W ed5f9fb4af32ffee
theorem AvailableChain.FGSA.Run.OpeningCarrier_W_def 21c2a35ed4981fbc
def AvailableChain.FGSA.Run.KernelConclusion_W 6f4d2c5c9443466e
theorem AvailableChain.FGSA.Run.KernelConclusion_W_def 5507599ca8fce50a
structure AvailableChain.FGSA.Run.KernelPrem_W 11fb5fc2e7ea1c3b
ctor AvailableChain.FGSA.Run.KernelPrem_W.mk 19263ff76db494c2
field AvailableChain.FGSA.Run.KernelPrem_W.set d66810be65dd0c3f
field AvailableChain.FGSA.Run.KernelPrem_W.bound b878e3cc7b64d16d
field AvailableChain.FGSA.Run.KernelPrem_W.window 61b0f5344f825afc
field AvailableChain.FGSA.Run.KernelPrem_W.start fa602bc39ed92ff0
field AvailableChain.FGSA.Run.KernelPrem_W.hhor 3808f6b95d17e303
field AvailableChain.FGSA.Run.KernelPrem_W.input d52c10b41f647263
field AvailableChain.FGSA.Run.KernelPrem_W.services e4f096b2a6c9b903
structure AvailableChain.FGSA.Run.TailKernelPt b330d4900d1ca7d6
ctor AvailableChain.FGSA.Run.TailKernelPt.mk 41cdd6cb6261ae64
field AvailableChain.FGSA.Run.TailKernelPt.w b55caf984a16e648
field AvailableChain.FGSA.Run.TailKernelPt.r 4006ca4b73b3c4a7
field AvailableChain.FGSA.Run.TailKernelPt.carrier 62ca7b0096b16566
field AvailableChain.FGSA.Run.TailKernelPt.U 5b648aaa4a87357a
structure AvailableChain.FGSA.Run.TailKernelPrem_W 2e31f38d9123ee01
ctor AvailableChain.FGSA.Run.TailKernelPrem_W.mk 0b8f8a201286ce8d
field AvailableChain.FGSA.Run.TailKernelPrem_W.set 687802f86e1293f7
field AvailableChain.FGSA.Run.TailKernelPrem_W.bound 7ee56efd49ced04f
field AvailableChain.FGSA.Run.TailKernelPrem_W.input 655f0ef23ed0b784
field AvailableChain.FGSA.Run.TailKernelPrem_W.start 0118dd6483944514
field AvailableChain.FGSA.Run.TailKernelPrem_W.window c914316853c2367d
field AvailableChain.FGSA.Run.TailKernelPrem_W.carrier 0024ea7ed8a2b43c
field AvailableChain.FGSA.Run.TailKernelPrem_W.high dc3c60d6536a6619
field AvailableChain.FGSA.Run.TailKernelPrem_W.cover 2b2708f2cfe02890
field AvailableChain.FGSA.Run.TailKernelPrem_W.hhor 13ff2957410b6b5b
structure AvailableChain.FGSA.Run.HealTContract e43a0178b0f71ee8
ctor AvailableChain.FGSA.Run.HealTContract.mk 64355a73223fdda7
field AvailableChain.FGSA.Run.HealTContract.del 2a12479cec44792e
field AvailableChain.FGSA.Run.HealTContract.delReset 16055960a82cae6f
field AvailableChain.FGSA.Run.HealTContract.perm 5424ceab9bf6da63
field AvailableChain.FGSA.Run.HealTContract.repair 4ddb4325e8363139
field AvailableChain.FGSA.Run.HealTContract.common dedaebc76d19dd3d
field AvailableChain.FGSA.Run.HealTContract.frontier 524f83bd02140e38
field AvailableChain.FGSA.Run.HealTContract.geom 188810bb95a8c72c
def AvailableChain.FGSA.Run.frontierAtIdx 281a4d1ce4becc4c
def AvailableChain.FGSA.Run.TopEvidence 12962f0c856704b9
def AvailableChain.FGSA.Run.ContestEvidence 393fea25bb15504c
def AvailableChain.FGSA.Run.EffectiveEvent a5c49caff9128db3
def AvailableChain.FGSA.Run.AttemptPhaseAt 73aeb2763a6ca1c3
def AvailableChain.FGSA.Run.ServedFrontier 04655731e876b6db
def AvailableChain.FGSA.Run.AttemptValid 65dec93df361af39
def AvailableChain.FGSA.Run.attemptBudget b92a1475dc2a8a8b
def AvailableChain.FGSA.Run.AttemptEndsBy de7e6cfba6a06da4
def AvailableChain.FGSA.Run.SettledPhaseFrame f87d106f405bbe47
theorem AvailableChain.FGSA.Run.SettledPhaseFrame_def 4b280490963082f1
def AvailableChain.FGSA.Run.RPhase 427f39cbdafb6e03
theorem AvailableChain.FGSA.Run.RPhase_def f5627f0d2257c77c
structure AvailableChain.FGSA.Run.HealRContract 3324bc270c388828
ctor AvailableChain.FGSA.Run.HealRContract.mk 59730fc7b091ed44
field AvailableChain.FGSA.Run.HealRContract.xing a7e1c656eeee6736
field AvailableChain.FGSA.Run.HealRContract.cap 476f3b1e76a46e2a
field AvailableChain.FGSA.Run.HealRContract.phase b2d5cdd9a825473e
field AvailableChain.FGSA.Run.HealRContract.excl 170afdd521498050
field AvailableChain.FGSA.Run.HealRContract.keep 0b2351ad712d1d97
field AvailableChain.FGSA.Run.HealRContract.fprov dc48a749c4f4a936
def AvailableChain.FGSA.Run.ProgressAttemptStatement 6dd5fd8297ef6469
theorem AvailableChain.FGSA.Run.ProgressAttemptStatement_def a0625868eacb4eea
```

### `AvailableChainFGSAClaims.Statements.Counts`

```text
def AvailableChain.FGSA.Run.awakeHonestIn 54415ad59f9cd90a
def AvailableChain.FGSA.Run.HonestProposal ae9f4b671ef57b39
```

### `AvailableChainFGSAClaims.Statements.FinalityApi`

```text
def AvailableChain.FGSA.Run.FinalityFinalizedAt a2574db69210cf4c
theorem AvailableChain.FGSA.Run.FinalityFinalizedAt_def 746fdb8f0e06ab67
def AvailableChain.FGSA.Run.FinalityBlock e33bfcb4735f7515
theorem AvailableChain.FGSA.Run.FinalityBlock_def d6c07f44208a322c
def AvailableChain.FGSA.Run.finalityRows 0095a1b4bd82114d
theorem AvailableChain.FGSA.Run.finalityRows_def 33877122b770dbb3
def AvailableChain.FGSA.Run.FinalitySlashableBound 9fc5e855812cfcbb
theorem AvailableChain.FGSA.Run.FinalitySlashableBound_def 46b69852d78030e5
def AvailableChain.FGSA.Run.FinalityExecution 057f35f1bdc787b1
theorem AvailableChain.FGSA.Run.FinalityExecution_def 9797d1ddd6d6a644
def AvailableChain.FGSA.Run.WholeRunAccountable b3f1346a38c4000e
theorem AvailableChain.FGSA.Run.WholeRunAccountable_def aa111cd414a3d41a
def AvailableChain.FGSA.Run.WholeRunAgreement 93e4d085abeca704
theorem AvailableChain.FGSA.Run.WholeRunAgreement_def 5e2c8bf93bee4d5a
```

### `AvailableChainFGSAClaims.Statements.Fold`

```text
inductive AvailableChain.FGSA.Run.RowKind da2d1119c2ef39fc
ctor AvailableChain.FGSA.Run.RowKind.target a127adc0838fa2e4
ctor AvailableChain.FGSA.Run.RowKind.progress e22f9613e6edb955
def AvailableChain.FGSA.Run.RowNames c882dc72ac13848c
def AvailableChain.FGSA.Run.SlotChain 026b8cab17d0c00f
def AvailableChain.FGSA.Run.EntryAt 4687fd7f795b2e7b
def AvailableChain.FGSA.Run.JustifiedCross 3d863cdfc9c4dc7f
def AvailableChain.FGSA.Run.MixedCross 6711fbed09e44ddf
def AvailableChain.FGSA.Run.NoMixedOnPath c1f5df4a2bf64380
def AvailableChain.FGSA.Run.SeatCovers ef27a741a6c070e5
def AvailableChain.FGSA.Run.CoveredByChild d3ed03707322e248
def AvailableChain.FGSA.Run.foldTrichotomy e1e76fb258f28bf0
def AvailableChain.FGSA.Run.StoredProgressConsume bb8df16d9f67160c
def AvailableChain.FGSA.Run.NoMixedMaturity 37554265ce976d54
def AvailableChain.FGSA.Run.NamesEntry 4157bcc504c0ab7f
def AvailableChain.FGSA.Run.rowHeight 8e2499ef46ddafdd
def AvailableChain.FGSA.Run.eventTime 4bdaaa69edcc1980
def AvailableChain.FGSA.Run.honestSeats da6d029ce398a2d3
theorem AvailableChain.FGSA.Run.rowHeight_def 770f0d6454ee9f76
theorem AvailableChain.FGSA.Run.eventTime_def 58ef7b966e9699ec
theorem AvailableChain.FGSA.Run.honestSeats_def adb2bb518fa5f274
def AvailableChain.FGSA.Run.ChainRowsBefore 2953d8ea725f8958
structure AvailableChain.FGSA.Run.PreBatchPrem b7f85466ce8b4cff
ctor AvailableChain.FGSA.Run.PreBatchPrem.mk ffc586ac4898317e
field AvailableChain.FGSA.Run.PreBatchPrem.base 0dae403cb65836d2
field AvailableChain.FGSA.Run.PreBatchPrem.faultQ 991161997b1c4af1
field AvailableChain.FGSA.Run.PreBatchPrem.entry 1f806a94d26a543e
field AvailableChain.FGSA.Run.PreBatchPrem.path 9a5ab5e0cba14f43
field AvailableChain.FGSA.Run.PreBatchPrem.cut a58cff244805eaad
field AvailableChain.FGSA.Run.PreBatchPrem.early 9ebb4b7d0d706c66
field AvailableChain.FGSA.Run.PreBatchPrem.rows 1edcec16cb599498
field AvailableChain.FGSA.Run.PreBatchPrem.noRow a16abd5110bb105f
def AvailableChain.FGSA.Run.NoMixedPreBatchParent aee0bb64fe306cfe
structure AvailableChain.FGSA.Run.BatchPrem a81812ec2f1b7847
ctor AvailableChain.FGSA.Run.BatchPrem.mk 7dbea909841151a6
field AvailableChain.FGSA.Run.BatchPrem.base bd6bb4ffc6305601
field AvailableChain.FGSA.Run.BatchPrem.faultQ ee056ad1d53a3dd3
field AvailableChain.FGSA.Run.BatchPrem.deltaF 76ff179dd77d5879
field AvailableChain.FGSA.Run.BatchPrem.rowsReceipt 3eef8f583c926f81
field AvailableChain.FGSA.Run.BatchPrem.horizon 7388a0b976393190
field AvailableChain.FGSA.Run.BatchPrem.carrier 128aef469fd7624e
field AvailableChain.FGSA.Run.BatchPrem.after 4f1e743bb8d58bc8
field AvailableChain.FGSA.Run.BatchPrem.valid 5cecd63d5a2181fe
field AvailableChain.FGSA.Run.BatchPrem.entry bd89a27c04f6272f
field AvailableChain.FGSA.Run.BatchPrem.path b5d5e9c0aa1ce548
field AvailableChain.FGSA.Run.BatchPrem.above 469b015ccec67ecb
def AvailableChain.FGSA.Run.BatchCoverage 7ed2cd34f8cab6cf
theorem AvailableChain.FGSA.Run.JustifiedCross_def 29125f944d7a5fcc
theorem AvailableChain.FGSA.Run.MixedCross_def a7825373b7452568
theorem AvailableChain.FGSA.Run.foldTrichotomy_def 810ba530fc8b531a
theorem AvailableChain.FGSA.Run.StoredProgressConsume_def 7455bc0f4a0392de
def AvailableChain.FGSA.Run.FinRowNames 94adce64d3029936
def AvailableChain.FGSA.Run.FinalityCoveredByChild_W 1c5e351c50356ef9
def AvailableChain.FGSA.Run.FinalityNames 6502008fb69955a7
structure AvailableChain.FGSA.Run.FinalityBatchPrem_W 08ecfc1da01b5669
ctor AvailableChain.FGSA.Run.FinalityBatchPrem_W.mk dd99190f013dc13b
field AvailableChain.FGSA.Run.FinalityBatchPrem_W.base f5667046372e0d4f
field AvailableChain.FGSA.Run.FinalityBatchPrem_W.faultQ 3bc363b2b191a455
field AvailableChain.FGSA.Run.FinalityBatchPrem_W.deltaF 45068c9122b101f5
field AvailableChain.FGSA.Run.FinalityBatchPrem_W.rowsReceipt 3ef6ef5907d6d4b4
field AvailableChain.FGSA.Run.FinalityBatchPrem_W.carrier 10a28486c2d167e9
field AvailableChain.FGSA.Run.FinalityBatchPrem_W.after 5435a0456bb4cd02
field AvailableChain.FGSA.Run.FinalityBatchPrem_W.horizon 2ba68ec3baacc721
field AvailableChain.FGSA.Run.FinalityBatchPrem_W.parent 6e0fbcf3fd80c3ce
field AvailableChain.FGSA.Run.FinalityBatchPrem_W.birth b30895fe73f6f877
field AvailableChain.FGSA.Run.FinalityBatchPrem_W.retainedOrCovered 15f672b13608abcd
field AvailableChain.FGSA.Run.FinalityBatchPrem_W.batch 0b78c83f40de1cf0
def AvailableChain.FGSA.Run.FinalityBatchCoverage_W 75e49f15caafc6b5
structure AvailableChain.FGSA.Run.PendingFold_W 1c51c60f16167bc5
ctor AvailableChain.FGSA.Run.PendingFold_W.mk a0574b014dbeef8f
field AvailableChain.FGSA.Run.PendingFold_W.child ed5955d007ae27ec
field AvailableChain.FGSA.Run.PendingFold_W.cover c4a1e13565c1b054
theorem AvailableChain.FGSA.Run.FinalityCoveredByChild_W_def 884d254eb20db65b
theorem AvailableChain.FGSA.Run.FinRowNames_def ed158b1dc934a188
theorem AvailableChain.FGSA.Run.FinalityNames_def 008a06cf02c71175
theorem AvailableChain.FGSA.Run.FinalityBatchCoverage_W_def b97a9d4ce98bc672
```

### `AvailableChainFGSAClaims.Statements.Healed`

```text
def AvailableChain.FGSA.Run.healStart cb5c86f6b8d7d28b
def AvailableChain.FGSA.Run.HealSuffix c00ccd19915d6c77
def AvailableChain.FGSA.Run.Healed d56aa4b809a755b5
def AvailableChain.FGSA.Run.H2A 9bc0d9b9ab75b2de
def AvailableChain.FGSA.Run.H2Prime 7a33e618cf427677
def AvailableChain.FGSA.Run.H3 d7abfaa21fb73354
def AvailableChain.FGSA.Run.H4 5b1119405f6c6acf
def AvailableChain.FGSA.Run.H5RawTransfer c017feac7ee354b4
def AvailableChain.FGSA.Run.H6GateService d1ac8b937f779d19
structure AvailableChain.FGSA.Run.HealT 2ad93861ec9ac64e
ctor AvailableChain.FGSA.Run.HealT.mk 92eb70e51a59dc2c
field AvailableChain.FGSA.Run.HealT.h1 99b3086713787301
field AvailableChain.FGSA.Run.HealT.h2 3623b491c3b5f285
field AvailableChain.FGSA.Run.HealT.rows 6d25fd5fe2c628f6
structure AvailableChain.FGSA.Run.HealAC e042b2afae39ecd7
ctor AvailableChain.FGSA.Run.HealAC.mk 1f69654e526dc5ac
field AvailableChain.FGSA.Run.HealAC.h2A 99dc921330b1a278
field AvailableChain.FGSA.Run.HealAC.h2' f6ed5cb484a35b71
field AvailableChain.FGSA.Run.HealAC.h3 34b5ff2c6c90c818
field AvailableChain.FGSA.Run.HealAC.h4 318d9fa3a432d699
field AvailableChain.FGSA.Run.HealAC.h5 04b36172ba0e5d0f
field AvailableChain.FGSA.Run.HealAC.h6 a62780879101441e
structure AvailableChain.FGSA.Run.HealingInput c5d601b8e0a632cf
ctor AvailableChain.FGSA.Run.HealingInput.mk 5987ef3f30c269ba
field AvailableChain.FGSA.Run.HealingInput.healed 9a64c7b9ff911077
field AvailableChain.FGSA.Run.HealingInput.wit dc58a22fab1b51e8
field AvailableChain.FGSA.Run.HealingInput.t ce6ab438eb5d9085
field AvailableChain.FGSA.Run.HealingInput.ac 104a593c7fe48e84
def AvailableChain.FGSA.Run.HTimeStatement 99c16a93fb2da368
theorem AvailableChain.FGSA.Run.HTimeStatement_def 802f73b6f7584190
theorem AvailableChain.FGSA.Run.HealSuffix_def 77fd85e015683d8d
theorem AvailableChain.FGSA.Run.healStart_def 2dda0ae3b45847ac
```

### `AvailableChainFGSAClaims.Statements.HealedBest`

```text
def AvailableChain.FGSA.Run.HTimeBestConcl 78f2e0390d426581
theorem AvailableChain.FGSA.Run.HTimeBestConcl_def c66e237fef033d80
```

### `AvailableChainFGSAClaims.Statements.OutputReads`

```text
def AvailableChain.FGSA.Run.ServedFromGateAt 0310fd73fd295186
theorem AvailableChain.FGSA.Run.ServedFromGateAt_def f21f1b534914bea3
def AvailableChain.FGSA.Run.JointGrowthAt 61b4b74a663fd4e5
theorem AvailableChain.FGSA.Run.JointGrowthAt_def c875ad0c5d6c7afa
```

### `AvailableChainFGSAClaims.Statements.Packages.Finality`

```text
inductive AvailableChain.FGSA.Run.FinFormW e65aa35faec5d780
ctor AvailableChain.FGSA.Run.FinFormW.recFE f5bdcad089b74a37
ctor AvailableChain.FGSA.Run.FinFormW.recF4 9740b2983363dec5
def AvailableChain.FGSA.Run.FinFormW.holdsW 4649365580aa48ae
theorem AvailableChain.FGSA.Run.FinFormW.holdsW_def 0c25c65a15eb1f5b
structure AvailableChain.FGSA.Run.FinalitySet_W cff695b9fdd4941a
ctor AvailableChain.FGSA.Run.FinalitySet_W.mk 05471c9984ccaf86
field AvailableChain.FGSA.Run.FinalitySet_W.core 9f5c9c320f8a965f
field AvailableChain.FGSA.Run.FinalitySet_W.bound 6f69105824c289ec
field AvailableChain.FGSA.Run.FinalitySet_W.recur 151db2b30ff928a4
def AvailableChain.FGSA.Run.finalityWindow_W 257edaf1d0233a74
theorem AvailableChain.FGSA.Run.finalityWindow_W_def 7713675ab497d5a2
structure AvailableChain.FGSA.Run.FirstFinalityPrem_W 58bc70e47e0d7ea4
ctor AvailableChain.FGSA.Run.FirstFinalityPrem_W.mk 64ccb058d76c521b
field AvailableChain.FGSA.Run.FirstFinalityPrem_W.set 12de54007bd5ba5d
field AvailableChain.FGSA.Run.FirstFinalityPrem_W.hhor 6ee12b995424207e
structure AvailableChain.FGSA.Run.FinalityLivenessPrem_W d40fc3a3822ea4d8
ctor AvailableChain.FGSA.Run.FinalityLivenessPrem_W.mk bfbca5590bb8bfc3
field AvailableChain.FGSA.Run.FinalityLivenessPrem_W.set 2f716637d36afa11
field AvailableChain.FGSA.Run.FinalityLivenessPrem_W.input b3e8624528ec9b1e
field AvailableChain.FGSA.Run.FinalityLivenessPrem_W.start 1940849e67201ee3
field AvailableChain.FGSA.Run.FinalityLivenessPrem_W.hhor 53fd68d76bce44f2
structure AvailableChain.FGSA.Run.ProposalFinalPrem_W 036f2d2f8a35c82b
ctor AvailableChain.FGSA.Run.ProposalFinalPrem_W.mk ecd7df302139a7f6
field AvailableChain.FGSA.Run.ProposalFinalPrem_W.set 56cb6c3c9c6c4793
field AvailableChain.FGSA.Run.ProposalFinalPrem_W.input 597d0e4bb9096b38
field AvailableChain.FGSA.Run.ProposalFinalPrem_W.prop d257b0f277f18012
field AvailableChain.FGSA.Run.ProposalFinalPrem_W.start 1d40576b795cb055
field AvailableChain.FGSA.Run.ProposalFinalPrem_W.hhor 3111926aeccd64e4
structure AvailableChain.FGSA.Run.AboveFrontierPrem_W 1bf3466439be998a
ctor AvailableChain.FGSA.Run.AboveFrontierPrem_W.mk f121b134ec2ab69f
field AvailableChain.FGSA.Run.AboveFrontierPrem_W.set 9c9778ecc3d1c414
field AvailableChain.FGSA.Run.AboveFrontierPrem_W.input e3e883e8014d441c
field AvailableChain.FGSA.Run.AboveFrontierPrem_W.start 7571a448b34a616b
field AvailableChain.FGSA.Run.AboveFrontierPrem_W.firstHorizon 8830399af353af14
field AvailableChain.FGSA.Run.AboveFrontierPrem_W.hhor 83c360531d641d5a
```

### `AvailableChainFGSAClaims.Statements.Packages.FinalityGST`

```text
structure AvailableChain.FGSA.Run.FinalityLivenessGSTPrem_W da55b17362dc6aaa
ctor AvailableChain.FGSA.Run.FinalityLivenessGSTPrem_W.mk 57d7d5e620b6c388
field AvailableChain.FGSA.Run.FinalityLivenessGSTPrem_W.set aad454d1707d28ea
field AvailableChain.FGSA.Run.FinalityLivenessGSTPrem_W.late 32d72a99cb7b2e34
field AvailableChain.FGSA.Run.FinalityLivenessGSTPrem_W.hhor 818152f3bab92df1
structure AvailableChain.FGSA.Run.ProposalFinalGSTPrem_W ad0de17b7c6b9518
ctor AvailableChain.FGSA.Run.ProposalFinalGSTPrem_W.mk ac4de60862bd0d0f
field AvailableChain.FGSA.Run.ProposalFinalGSTPrem_W.set 801c423efc7b5e1e
field AvailableChain.FGSA.Run.ProposalFinalGSTPrem_W.prop 5e7a52bc9df89a16
field AvailableChain.FGSA.Run.ProposalFinalGSTPrem_W.late c2be209c1578f363
field AvailableChain.FGSA.Run.ProposalFinalGSTPrem_W.hhor 9675956340887cd8
structure AvailableChain.FGSA.Run.AboveFrontierGSTPrem_W a9a0e6ca30bb4c70
ctor AvailableChain.FGSA.Run.AboveFrontierGSTPrem_W.mk a21a6dc3c20f79e4
field AvailableChain.FGSA.Run.AboveFrontierGSTPrem_W.set 57e1caea73ffc785
field AvailableChain.FGSA.Run.AboveFrontierGSTPrem_W.late 126828bfdb0909c2
field AvailableChain.FGSA.Run.AboveFrontierGSTPrem_W.hhor d594d1743483b24c
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
structure AvailableChain.FGSA.Run.HealingPrem 4b345724e84be4b4
ctor AvailableChain.FGSA.Run.HealingPrem.mk ff7805955c1602d3
field AvailableChain.FGSA.Run.HealingPrem.set faf7947fa658baf8
field AvailableChain.FGSA.Run.HealingPrem.bound c3aaa500b7af8c7b
structure AvailableChain.FGSA.Run.HealingWitnessPrem db8c3ed06eb0a259
field AvailableChain.FGSA.Run.HealingWitnessPrem.toHealingPrem 876448fe55824295
ctor AvailableChain.FGSA.Run.HealingWitnessPrem.mk 91e44ff29147676a
field AvailableChain.FGSA.Run.HealingWitnessPrem.h0 629bf620e91e656f
structure AvailableChain.FGSA.Run.HealingTimePrem 8c05bf614c0e1336
field AvailableChain.FGSA.Run.HealingTimePrem.toHealingPrem 63586e6b932c0073
ctor AvailableChain.FGSA.Run.HealingTimePrem.mk 4c22ced90cdc2fbc
field AvailableChain.FGSA.Run.HealingTimePrem.hhor 14ccb1dc357d81e8
structure AvailableChain.FGSA.Run.ResetArrivalPrem 3f94e6d547dea1e3
field AvailableChain.FGSA.Run.ResetArrivalPrem.toHealingPrem aad0f9089af11d0e
ctor AvailableChain.FGSA.Run.ResetArrivalPrem.mk f3e6fd5453cc3e5e
field AvailableChain.FGSA.Run.ResetArrivalPrem.hhor d695bf0952b07adf
structure AvailableChain.FGSA.Run.ResetArrivalFullPrem b0127ddf885be338
field AvailableChain.FGSA.Run.ResetArrivalFullPrem.toHealingPrem 4f3adcffe0797f57
ctor AvailableChain.FGSA.Run.ResetArrivalFullPrem.mk b1142c8b00ca3c69
field AvailableChain.FGSA.Run.ResetArrivalFullPrem.hhor 8ca075681a2c9c12
structure AvailableChain.FGSA.Run.KernelJoinedPrem 4e55d876ea0a1791
ctor AvailableChain.FGSA.Run.KernelJoinedPrem.mk 2334f536313f8d0f
field AvailableChain.FGSA.Run.KernelJoinedPrem.set 8d6568f769d7ee54
field AvailableChain.FGSA.Run.KernelJoinedPrem.bound 8e80a7916d9c307d
field AvailableChain.FGSA.Run.KernelJoinedPrem.window f36ef5c9e25c6289
field AvailableChain.FGSA.Run.KernelJoinedPrem.start d3a0ff144151edf6
field AvailableChain.FGSA.Run.KernelJoinedPrem.hhor ac33bdf2d2b15553
structure AvailableChain.FGSA.Run.HealingAttemptPrem df1c6c9004e2d8e5
field AvailableChain.FGSA.Run.HealingAttemptPrem.toHealingPrem b797c95a3d3c4af4
ctor AvailableChain.FGSA.Run.HealingAttemptPrem.mk 61855113bfdd20dc
field AvailableChain.FGSA.Run.HealingAttemptPrem.valid 5908938f37d34d86
field AvailableChain.FGSA.Run.HealingAttemptPrem.hhor 055acedd097b0fa4
structure AvailableChain.FGSA.Run.HealingInputPrem 529ad033f9610116
field AvailableChain.FGSA.Run.HealingInputPrem.toHealingWitnessPrem 15bc7539746b0204
ctor AvailableChain.FGSA.Run.HealingInputPrem.mk 1e303d6813fe81e9
field AvailableChain.FGSA.Run.HealingInputPrem.hhor 40f0870ce71b719a
structure AvailableChain.FGSA.Run.RenewedPromotionPrem 75c1ae083edf90f1
field AvailableChain.FGSA.Run.RenewedPromotionPrem.toHealingPrem 1093531f05bed250
ctor AvailableChain.FGSA.Run.RenewedPromotionPrem.mk 16e1d8368dc80444
field AvailableChain.FGSA.Run.RenewedPromotionPrem.hhor 02ff694c681bbd8b
```

### `AvailableChainFGSAClaims.Statements.Packages.Inclusion`

```text
structure AvailableChain.FGSA.Run.CleanInclusionPrem 34629f79f5dc9e40
ctor AvailableChain.FGSA.Run.CleanInclusionPrem.mk 3b2c72b504c139d7
field AvailableChain.FGSA.Run.CleanInclusionPrem.set 9160398d095bc154
field AvailableChain.FGSA.Run.CleanInclusionPrem.prop bdc12db5435c146e
field AvailableChain.FGSA.Run.CleanInclusionPrem.hhor bfa0a29690206c73
structure AvailableChain.FGSA.Run.ExactProposalPrem 08f20203f7500772
ctor AvailableChain.FGSA.Run.ExactProposalPrem.mk b4c584129e5adebd
field AvailableChain.FGSA.Run.ExactProposalPrem.set b0519237fdf452e0
field AvailableChain.FGSA.Run.ExactProposalPrem.prop 3512026b8585f7fa
field AvailableChain.FGSA.Run.ExactProposalPrem.hhor 78ff4f064c367d9b
```

### `AvailableChainFGSAClaims.Statements.Packages.Outage`

```text
structure AvailableChain.FGSA.Run.OutagePrem 652d156e8e88b8ef
ctor AvailableChain.FGSA.Run.OutagePrem.mk b1c20c16a39b891b
field AvailableChain.FGSA.Run.OutagePrem.set 3418c59387e2cfcc
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
structure AvailableChain.FGSA.Run.BasePrem 0d65766c64d58225
ctor AvailableChain.FGSA.Run.BasePrem.mk 970acab4387063d7
field AvailableChain.FGSA.Run.BasePrem.set e4fbebe6e2d2021b
structure AvailableChain.FGSA.Run.SameLabelPrem 5cb58838c36ef6a1
ctor AvailableChain.FGSA.Run.SameLabelPrem.mk eb3fe94a659304ff
field AvailableChain.FGSA.Run.SameLabelPrem.set aaa5cff459111bec
field AvailableChain.FGSA.Run.SameLabelPrem.sync 050f60bdf337f91b
structure AvailableChain.FGSA.Run.SourceDisciplinePrem 116b3d4ba2fc1cba
ctor AvailableChain.FGSA.Run.SourceDisciplinePrem.mk 3663c0f72659fab4
field AvailableChain.FGSA.Run.SourceDisciplinePrem.set 658e49117f6b721d
field AvailableChain.FGSA.Run.SourceDisciplinePrem.quorum 0e3a6c417832f494
structure AvailableChain.FGSA.Run.FinalizedSafetyPrem 1c492c61a9ea0a94
ctor AvailableChain.FGSA.Run.FinalizedSafetyPrem.mk 18371046245b99a6
field AvailableChain.FGSA.Run.FinalizedSafetyPrem.set 2a7e6c404de73c87
field AvailableChain.FGSA.Run.FinalizedSafetyPrem.fault f6a131634e452acf
structure AvailableChain.FGSA.Run.CleanPrem d2f590f40630d498
ctor AvailableChain.FGSA.Run.CleanPrem.mk 9828ed393007e7d3
field AvailableChain.FGSA.Run.CleanPrem.set 94926be74265eeda
structure AvailableChain.FGSA.Run.CleanPrefixPrem 394ef0b9b1aff4dd
ctor AvailableChain.FGSA.Run.CleanPrefixPrem.mk 2f4f77eb07c829df
field AvailableChain.FGSA.Run.CleanPrefixPrem.set 5e80b2f672727ce1
structure AvailableChain.FGSA.Run.CleanCutPrem 9433d5dd87421c40
ctor AvailableChain.FGSA.Run.CleanCutPrem.mk af8c4f54c575aa7c
field AvailableChain.FGSA.Run.CleanCutPrem.set cdf508f8cfd59726
structure AvailableChain.FGSA.Run.ReleasePrem 5f531f3a62acc0ed
ctor AvailableChain.FGSA.Run.ReleasePrem.mk 699ef472ca774590
field AvailableChain.FGSA.Run.ReleasePrem.set 90f9bf4ee742d4cc
field AvailableChain.FGSA.Run.ReleasePrem.lt 96dccc819a34ccc0
```

### `AvailableChainFGSAClaims.Statements.Phases`

```text
def AvailableChain.FGSA.Run.finHeight 45ca642905486866
structure AvailableChain.FGSA.Run.FreshPrem 0b1a751f0f0fcb62
ctor AvailableChain.FGSA.Run.FreshPrem.mk 5780d9167ffe3fd9
field AvailableChain.FGSA.Run.FreshPrem.base c4b221858540216f
field AvailableChain.FGSA.Run.FreshPrem.faultQ 4f07eeffbdd73e45
field AvailableChain.FGSA.Run.FreshPrem.cut ba29e61b882af085
field AvailableChain.FGSA.Run.FreshPrem.early 90f7df0adbfc33ed
field AvailableChain.FGSA.Run.FreshPrem.rows 687436d673e7bfff
field AvailableChain.FGSA.Run.FreshPrem.noNextRow 03cf6c85c78c1b2d
field AvailableChain.FGSA.Run.FreshPrem.noFinRow 7bc3a93899de5cde
def AvailableChain.FGSA.Run.JustifyAt da44c662e7b74cf9
def AvailableChain.FGSA.Run.JustifyFresh_W 16939cca5b13eaa0
def AvailableChain.FGSA.Run.Ready_W f2b21713b94e9921
def AvailableChain.FGSA.Run.receiptInsert_W cf242a50a897ddfc
structure AvailableChain.FGSA.Run.ReceiptWitness_W 96480f7d786199e2
ctor AvailableChain.FGSA.Run.ReceiptWitness_W.mk 1c433d7a0bb74541
field AvailableChain.FGSA.Run.ReceiptWitness_W.index d94469eb94339260
field AvailableChain.FGSA.Run.ReceiptWitness_W.time 4a999c5986ac6c0a
structure AvailableChain.FGSA.Run.BlockDelivery_W 7aa410a6b3bb0bc1
ctor AvailableChain.FGSA.Run.BlockDelivery_W.mk 075391f24ecb7321
field AvailableChain.FGSA.Run.BlockDelivery_W.selected b704a0d093f456c4
field AvailableChain.FGSA.Run.BlockDelivery_W.witness fde510a9c0ecee22
structure AvailableChain.FGSA.Run.AcceptGuards_W 9c9d71d303f2a646
ctor AvailableChain.FGSA.Run.AcceptGuards_W.mk 6c5ce7f06d5425fe
field AvailableChain.FGSA.Run.AcceptGuards_W.finCmp 4642b91b782dde61
field AvailableChain.FGSA.Run.AcceptGuards_W.jPath cf65103b1231a1d1
field AvailableChain.FGSA.Run.AcceptGuards_W.cap 45560e4dd7fae4de
structure AvailableChain.FGSA.Run.AcceptPrem_W bc293cdfe432bf85
ctor AvailableChain.FGSA.Run.AcceptPrem_W.mk 6eea8d7384a73922
field AvailableChain.FGSA.Run.AcceptPrem_W.base 3889dde069617eb4
field AvailableChain.FGSA.Run.AcceptPrem_W.faultBound e43557a357b775fd
field AvailableChain.FGSA.Run.AcceptPrem_W.finalized e629b2ce9e8d6346
field AvailableChain.FGSA.Run.AcceptPrem_W.deliver 5ffe234058ae405a
field AvailableChain.FGSA.Run.AcceptPrem_W.guards 4b1a8a0bd333a17c
field AvailableChain.FGSA.Run.AcceptPrem_W.horizon 0d72f8cddebebd55
def AvailableChain.FGSA.Run.AcceptBefore_W a365f0960aa136e2
structure AvailableChain.FGSA.Run.FinalizePrem_W beeeb643f3d7c1b0
ctor AvailableChain.FGSA.Run.FinalizePrem_W.mk 112fa3004904147a
field AvailableChain.FGSA.Run.FinalizePrem_W.fold da71d2370f2fea24
field AvailableChain.FGSA.Run.FinalizePrem_W.base 29d50840debc1fed
field AvailableChain.FGSA.Run.FinalizePrem_W.faultBound 7beb5f2d4f2ffbfa
field AvailableChain.FGSA.Run.FinalizePrem_W.deliver 2abb7bb0be5b3031
field AvailableChain.FGSA.Run.FinalizePrem_W.guards 6131daca195802c0
field AvailableChain.FGSA.Run.FinalizePrem_W.horizon 222d635d0a9f3934
def AvailableChain.FGSA.Run.FinalizePending_W 009226740f489f60
theorem AvailableChain.FGSA.Run.JustifyAt_def 1d4e390ee06a6c32
theorem AvailableChain.FGSA.Run.JustifyFresh_W_def dab0def8d05044a4
theorem AvailableChain.FGSA.Run.Ready_W_def 2edbfde86d4f9e61
theorem AvailableChain.FGSA.Run.receiptInsert_W_def 554fd44079cd3b69
theorem AvailableChain.FGSA.Run.AcceptBefore_W_def fbeda7634e01320b
theorem AvailableChain.FGSA.Run.FinalizePending_W_def a075b5c2b413236d
def AvailableChain.FGSA.Run.FreshFinalityRows_W 3ef06747763d689e
structure AvailableChain.FGSA.Run.TerminalCarriagePrem_W 8f308207cf8468b6
ctor AvailableChain.FGSA.Run.TerminalCarriagePrem_W.mk 65db7509eaec202a
field AvailableChain.FGSA.Run.TerminalCarriagePrem_W.base d06be4dcb84d0321
field AvailableChain.FGSA.Run.TerminalCarriagePrem_W.faultQ 58ceb74105ba57b2
field AvailableChain.FGSA.Run.TerminalCarriagePrem_W.deltaF 1144c3937398eecb
field AvailableChain.FGSA.Run.TerminalCarriagePrem_W.carrier 3c7df35d027ce2a6
field AvailableChain.FGSA.Run.TerminalCarriagePrem_W.parent d31faa2da114a987
field AvailableChain.FGSA.Run.TerminalCarriagePrem_W.path ee2daf6ed7511c05
field AvailableChain.FGSA.Run.TerminalCarriagePrem_W.freshHeight 9d8fef818bebf1d9
field AvailableChain.FGSA.Run.TerminalCarriagePrem_W.retainedOrCovered 047691fb3ef1d52e
field AvailableChain.FGSA.Run.TerminalCarriagePrem_W.horizon 03b580bd069ac08a
field AvailableChain.FGSA.Run.TerminalCarriagePrem_W.seats 4a0184de05498713
field AvailableChain.FGSA.Run.TerminalCarriagePrem_W.rows d5756c8448a035a9
field AvailableChain.FGSA.Run.TerminalCarriagePrem_W.fresh d3dd646bf6b37d77
field AvailableChain.FGSA.Run.TerminalCarriagePrem_W.heightEntry d273ffa4914d45e3
field AvailableChain.FGSA.Run.TerminalCarriagePrem_W.receipt 0e72a79461882f77
def AvailableChain.FGSA.Run.TerminalCarriage_W 975b3d16f0e9ec55
theorem AvailableChain.FGSA.Run.FreshFinalityRows_W_def 5233573c6df65266
theorem AvailableChain.FGSA.Run.TerminalCarriage_W_def 9b0257f618a69f02
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
def AvailableChain.FGSA.Run.storeAt efe0a51c0b69f5be
def AvailableChain.FGSA.Run.S_at db8d3f9e104c43c6
def AvailableChain.FGSA.Run.F_at ab2b59463fb6b3f8
def AvailableChain.FGSA.Run.J_at cad0d8339c4bed45
def AvailableChain.FGSA.Run.gateIn a2be0b6110a0211e
theorem AvailableChain.FGSA.Run.gateIn_def 2a70f432ba5d3b10
def AvailableChain.FGSA.Run.gateResult cacd0376e6d56215
theorem AvailableChain.FGSA.Run.gateResult_def 526174cb65c59771
def AvailableChain.FGSA.Run.isGateTime de71406ad46da144
theorem AvailableChain.FGSA.Run.isGateTime_def a991674f5c9d52f5
def AvailableChain.FGSA.Run.IsGateTick 74e5995d1a317244
def AvailableChain.FGSA.Run.gateResultAt e1a78565f88f84ab
def AvailableChain.FGSA.Run.gatePassedAt 28e0b9b0a073bd76
def AvailableChain.FGSA.Run.fastAt 5b96ef369bdd415a
def AvailableChain.FGSA.Run.headAtIdx fff802c0d36a0568
def AvailableChain.FGSA.Run.vHead f0786114a798afe3
theorem AvailableChain.FGSA.Run.vHead_def d5b5dae710c77ab2
def AvailableChain.FGSA.Run.actionSourceFG f6a269f746155417
theorem AvailableChain.FGSA.Run.actionSourceFG_def f7eb42f4bcb9f140
def AvailableChain.FGSA.Run.actionSource a3230e4513a55166
def AvailableChain.FGSA.Run.labelBoundAt 0296587616e6afa0
def AvailableChain.FGSA.Run.DeliveredAt 0442ed425514a227
def AvailableChain.FGSA.Run.HandlesRowAt 8b75822a1d00a018
def AvailableChain.FGSA.Run.AcceptsFinalBefore 4cc0fb9af7db4ce7
def AvailableChain.FGSA.Run.cleanResults f0df2d276deac5e5
def AvailableChain.FGSA.Run.BelowLabel 0744de2d9ea42c8a
theorem AvailableChain.FGSA.Run.S_at_def 6c021b70d01d96d6
```

### `AvailableChainFGSAClaims.Statements.Recurrence`

```text
```

### `AvailableChainFGSAClaims.Statements.Regimes`

```text
structure AvailableChain.FGSA.Run.Base₂ 5c8985f2220a940c
ctor AvailableChain.FGSA.Run.Base₂.mk b9945522133ac188
field AvailableChain.FGSA.Run.Base₂.valid 7c38c12e3ea22ce4
field AvailableChain.FGSA.Run.Base₂.linked 1b2da23612f39ade
field AvailableChain.FGSA.Run.Base₂.cstar 6a51d7c11703de8c
field AvailableChain.FGSA.Run.Base₂.noRestart c76099cb19e266ea
field AvailableChain.FGSA.Run.Base₂.delta b4b2677d685aef70
structure AvailableChain.FGSA.Run.HealthyPrefix₂ 674bd9a86d37337b
ctor AvailableChain.FGSA.Run.HealthyPrefix₂.mk cce5411a42383d49
field AvailableChain.FGSA.Run.HealthyPrefix₂.base 0df21d6e9d514e91
field AvailableChain.FGSA.Run.HealthyPrefix₂.cut d9ba7fd71a3a572d
field AvailableChain.FGSA.Run.HealthyPrefix₂.healthy a0147559b8b34e9c
field AvailableChain.FGSA.Run.HealthyPrefix₂.deltaF 44d0ca6711ae814c
field AvailableChain.FGSA.Run.HealthyPrefix₂.partBefore 4e4ab77683024bb1
structure AvailableChain.FGSA.Run.CleanPrefix₂ 118a6895828036b2
field AvailableChain.FGSA.Run.CleanPrefix₂.toHealthyPrefix₂ 72d089064d560b2c
ctor AvailableChain.FGSA.Run.CleanPrefix₂.mk 3233313c7fd21060
field AvailableChain.FGSA.Run.CleanPrefix₂.partAt 5f67518edadfc3fa
def AvailableChain.FGSA.Run.CleanCut₂ 60cbb1acca411f0b
structure AvailableChain.FGSA.Run.Clean₂ 0ca7b2b310e71c29
ctor AvailableChain.FGSA.Run.Clean₂.mk 3368ddfb046b3ea3
field AvailableChain.FGSA.Run.Clean₂.pre 76f2e5a2de30ad13
field AvailableChain.FGSA.Run.Clean₂.gst 6333c9aaf3d2b6c3
structure AvailableChain.FGSA.Run.Recovery₂ a61d93b6ea26f79c
ctor AvailableChain.FGSA.Run.Recovery₂.mk 9bb2b1bc6151e0e2
field AvailableChain.FGSA.Run.Recovery₂.sync daef726f4f609c71
field AvailableChain.FGSA.Run.Recovery₂.deltaF a14fbbf13eafdc5d
field AvailableChain.FGSA.Run.Recovery₂.gap b4231df6d0c16183
field AvailableChain.FGSA.Run.Recovery₂.base 9da6662f9dd97a0e
field AvailableChain.FGSA.Run.Recovery₂.fault 32e056ec4877397e
field AvailableChain.FGSA.Run.Recovery₂.awake a8db52210c86dc13
field AvailableChain.FGSA.Run.Recovery₂.gapPos c705801f7cb2f3b7
def AvailableChain.FGSA.Run.BaseSet 98934dcbe432a13b
def AvailableChain.FGSA.Run.CleanSet dd65e099952bf12c
def AvailableChain.FGSA.Run.CleanCutSet ad817ec49f1956a7
def AvailableChain.FGSA.Run.CleanPrefixSet 05bee7f55ecfe8d2
def AvailableChain.FGSA.Run.HealingSet 185c977500a213f1
def AvailableChain.FGSA.Run.AwakeProposerRecurrenceFrom 6c6bbcba21c92ad1
structure AvailableChain.FGSA.Run.Outage₂ 13cd99cf71c5d597
ctor AvailableChain.FGSA.Run.Outage₂.mk 9c2b7d706b009545
field AvailableChain.FGSA.Run.Outage₂.pre c737a9e99e9560a8
field AvailableChain.FGSA.Run.Outage₂.sleepy 302d9651300dbce0
field AvailableChain.FGSA.Run.Outage₂.order 00858d9a77378876
field AvailableChain.FGSA.Run.Outage₂.lag e5e59efcfc8175b2
field AvailableChain.FGSA.Run.Outage₂.budget 47a5e6182f35eea4
field AvailableChain.FGSA.Run.Outage₂.fastPart 6604a961af71a7e9
def AvailableChain.FGSA.Run.OutageSet 2ecffc04a57d3239
```

### `AvailableChainFGSAClaims.Statements.WeakContinuation`

```text
structure AvailableChain.FGSA.Run.StrongRecoverySearchPrefix₂ b475a2398d548514
field AvailableChain.FGSA.Run.StrongRecoverySearchPrefix₂.toRecovery₂ e5f8db975d648b81
ctor AvailableChain.FGSA.Run.StrongRecoverySearchPrefix₂.mk a1621c910ab228de
field AvailableChain.FGSA.Run.StrongRecoverySearchPrefix₂.liveness ddad761513bd24b7
field AvailableChain.FGSA.Run.StrongRecoverySearchPrefix₂.endpoint 4fbc1cf6cb6a3b89
structure AvailableChain.FGSA.Run.AgreesThrough₂ b8811820b8082c7b
ctor AvailableChain.FGSA.Run.AgreesThrough₂.mk bb80c7463e37ef4d
field AvailableChain.FGSA.Run.AgreesThrough₂.honest ec5c2f538f0a8a71
field AvailableChain.FGSA.Run.AgreesThrough₂.gst d1e3a51fa082ccfd
field AvailableChain.FGSA.Run.AgreesThrough₂.delta 45f9c62c5d0bd7a3
field AvailableChain.FGSA.Run.AgreesThrough₂.seats 53564ccb1db154f8
field AvailableChain.FGSA.Run.AgreesThrough₂.inputs 6fd4f87123da3e87
field AvailableChain.FGSA.Run.AgreesThrough₂.awake 50e571dfe03e47a8
field AvailableChain.FGSA.Run.AgreesThrough₂.events 9012178e5d53ea10
field AvailableChain.FGSA.Run.AgreesThrough₂.suffixTime 1a19b7e1670e852c
structure AvailableChain.FGSA.Run.CleanContinuation₂ b21bce324f7312cb
ctor AvailableChain.FGSA.Run.CleanContinuation₂.mk bb43f4213f832f7b
field AvailableChain.FGSA.Run.CleanContinuation₂.base ab49370a22e51aee
field AvailableChain.FGSA.Run.CleanContinuation₂.agrees 167e347a9594305f
field AvailableChain.FGSA.Run.CleanContinuation₂.covered 3fbd65e5d39ccbe7
field AvailableChain.FGSA.Run.CleanContinuation₂.sync 80bf12cbea5c786c
field AvailableChain.FGSA.Run.CleanContinuation₂.deltaF c87b5c8ec0aeb5f9
field AvailableChain.FGSA.Run.CleanContinuation₂.participation b2dac5212f94cc0a
structure AvailableChain.FGSA.Run.BoundedHealingCut₂ cc042a558c997d43
ctor AvailableChain.FGSA.Run.BoundedHealingCut₂.mk 04833623f937294d
field AvailableChain.FGSA.Run.BoundedHealingCut₂.afterGST 656db0ab551d8e20
field AvailableChain.FGSA.Run.BoundedHealingCut₂.beforeEnd f973b3cb665babd2
field AvailableChain.FGSA.Run.BoundedHealingCut₂.cut 6221c560aaef44e9
field AvailableChain.FGSA.Run.BoundedHealingCut₂.actualProposal 778311163ebc0fa4
field AvailableChain.FGSA.Run.BoundedHealingCut₂.refreshed 682eab4d8d558e6e
structure AvailableChain.FGSA.Run.SSafeFromCut₂ e404f90cae7aa0d5
ctor AvailableChain.FGSA.Run.SSafeFromCut₂.mk b7bdebfd3076a100
field AvailableChain.FGSA.Run.SSafeFromCut₂.compatible 2f911bbd5dc8e130
field AvailableChain.FGSA.Run.SSafeFromCut₂.monotone 92135520edf77fcf
field AvailableChain.FGSA.Run.SSafeFromCut₂.seed 96d7d1232ee31459
field AvailableChain.FGSA.Run.SSafeFromCut₂.finalBelow 07e8af118ce16bf1
field AvailableChain.FGSA.Run.SSafeFromCut₂.outputs 00557223598e2c84
def AvailableChain.FGSA.Run.BoundedSafetyRecovery₂ a4ddace4f3e90b7e
```

### `AvailableChainFGSAClaims.Statements.WeakContinuationLive`

```text
structure AvailableChain.FGSA.Run.WeakContinuationLiveAt₂ 444aa594c122432f
ctor AvailableChain.FGSA.Run.WeakContinuationLiveAt₂.mk 78a1b9694a381da2
field AvailableChain.FGSA.Run.WeakContinuationLiveAt₂.safety 914a9494377582b9
field AvailableChain.FGSA.Run.WeakContinuationLiveAt₂.inclusion 9bd576559e0b7f6d
field AvailableChain.FGSA.Run.WeakContinuationLiveAt₂.growth b779e5f8a16cf1b8
def AvailableChain.FGSA.Run.BoundedSafetyLivenessRecovery₂ b140751d03ed26f4
theorem AvailableChain.FGSA.Run.BoundedSafetyLivenessRecovery₂_def eacdfbd983755b5c
```

### `AvailableChainFGSAClaims.Statements.Windows`

```text
def AvailableChain.FGSA.Run.WinSpec 33772d46f51abab5
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
def AvailableChain.FGSA.Run.cleanWinAt d4105affe5ef0210
def AvailableChain.FGSA.Run.cleanWin 323c31881e0c7790
def AvailableChain.FGSA.Run.cleanPrefixWin 1754af14b655e863
def AvailableChain.FGSA.Run.cleanLabelWin 54ec4cd1097d69ee
def AvailableChain.FGSA.Run.gapWin d499adc81ffd0a64
def AvailableChain.FGSA.Run.formWinAt 07cc07bc002a3e6d
def AvailableChain.FGSA.Run.kernelWin 51122369d4f1c1da
def AvailableChain.FGSA.Run.trigWin ab54cfb8428d58d1
def AvailableChain.FGSA.Run.outWin 4792c9bb24947a74
def AvailableChain.FGSA.Run.TerminalRetention_W 200fe47773b3c650
theorem AvailableChain.FGSA.Run.TerminalRetention_W_def f7ad656ec260442f
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
def AvailableChain.FGSA.Run.oldRowHeights dc389602ef719188
def AvailableChain.FGSA.Run.muOf 76f2326ad2478ce1
def AvailableChain.FGSA.Run.high 7ff53a720615a0ba
def AvailableChain.FGSA.Run.honestFrontier 5f0d42e69690f0ae
def AvailableChain.FGSA.Run.HeightRow caf1abdc361d0839
structure AvailableChain.FGSA.Run.H0Reset 0ae1d31177850d1c
ctor AvailableChain.FGSA.Run.H0Reset.mk d3d059a523afe5af
field AvailableChain.FGSA.Run.H0Reset.rG_after f18f6edde0715b4f
field AvailableChain.FGSA.Run.H0Reset.rG_first 351e635ab78d3cf3
field AvailableChain.FGSA.Run.H0Reset.cut 8bbd244ea7b2feb8
field AvailableChain.FGSA.Run.H0Reset.frontier cfbefa506dc607af
field AvailableChain.FGSA.Run.H0Reset.rowCap aa70f5ba63fb3c05
field AvailableChain.FGSA.Run.H0Reset.mu_le 5a9f4efda0824b6b
field AvailableChain.FGSA.Run.H0Reset.cut_lower a0435e7009657145
field AvailableChain.FGSA.Run.H0Reset.cut_upper caa92feef10c04d6
field AvailableChain.FGSA.Run.H0Reset.reset_row 53cdd89d845543db
field AvailableChain.FGSA.Run.H0Reset.reset_first b9081833cc5b6d27
field AvailableChain.FGSA.Run.H0Reset.label 6e81ff8a4ad246dc
field AvailableChain.FGSA.Run.H0Reset.fresh a5c413f6b6907bdf
field AvailableChain.FGSA.Run.H0Reset.synchronous 7438bd2053856cdb
structure AvailableChain.FGSA.Run.H0 61aabbb2c52ddee2
field AvailableChain.FGSA.Run.H0.toH0Reset 444c0e4fcc076948
ctor AvailableChain.FGSA.Run.H0.mk ac3dccd999f1696b
field AvailableChain.FGSA.Run.H0.proposal_lower d59665b0ea13acdd
field AvailableChain.FGSA.Run.H0.proposal 9c199fec996661f6
field AvailableChain.FGSA.Run.H0.proposal_first b8304ef1005fd171
field AvailableChain.FGSA.Run.H0.after_gst 9e1af4e6abf48bdd
field AvailableChain.FGSA.Run.H0.source_prefix 11a2e72ff6824828
def AvailableChain.FGSA.Run.tstarOf dc0679feeb6093fb
theorem AvailableChain.FGSA.Run.muOf_def 9b70ccd6d9fa8e04
theorem AvailableChain.FGSA.Run.high_def 9b5235dbcdbbef28
```
