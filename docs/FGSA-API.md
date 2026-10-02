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
def AvailableChain.FGSA.finalityView b5f9198670a43d0c
theorem AvailableChain.FGSA.finalityView_def d8b336019bd1a196
```

### `AvailableChainFGSA.Statements.Invariants`

```text
inductive AvailableChain.FGSA.Reachable 6475ab43a8bf8961
ctor AvailableChain.FGSA.Reachable.init dd2ac4576edf10ab
ctor AvailableChain.FGSA.Reachable.tick 99facd2394fc6e30
ctor AvailableChain.FGSA.Reachable.deliver 67e3d1722d7f236e
def AvailableChain.FGSA.NestOK 130e2646fb4577ff
def AvailableChain.FGSA.SACompat f338d5747785cc54
def AvailableChain.FGSA.LeaseBelowOutputStore 5c59d0a0978e86ea
theorem AvailableChain.FGSA.LeaseBelowOutputStore_def 124f6f13f65f43ca
def AvailableChain.FGSA.FastOrigin 55103ff0d11f32d6
structure AvailableChain.FGSA.CStoreInv cfaaddc60f50053e
ctor AvailableChain.FGSA.CStoreInv.mk 103c888a74af1ccf
field AvailableChain.FGSA.CStoreInv.fg ee14b3f42239ac94
field AvailableChain.FGSA.CStoreInv.rootInj ad7310f7e9365d90
field AvailableChain.FGSA.CStoreInv.baseTree 1cb9132de30017ae
field AvailableChain.FGSA.CStoreInv.saCompat c01c9441e95dd6e0
field AvailableChain.FGSA.CStoreInv.Smem 1de588a18f153d73
field AvailableChain.FGSA.CStoreInv.fastOrigin bd41d8c26aa50f1f
field AvailableChain.FGSA.CStoreInv.fastDom 0f0610a099eaf80c
field AvailableChain.FGSA.CStoreInv.genuineKeys 4698263b4de130a9
field AvailableChain.FGSA.CStoreInv.leaseKeys 1ae5b95d75b2488b
def AvailableChain.FGSA.Inv0 f6eec569284a068f
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
def AvailableChain.FGSA.OutputNestingStored c798c0b33f1aeed7
def AvailableChain.FGSA.StoreInvariant 1d55e07f20d57235
structure AvailableChain.FGSA.StoreBundle 7bbcc3b9066575ff
ctor AvailableChain.FGSA.StoreBundle.mk c9a68c6485eb1724
field AvailableChain.FGSA.StoreBundle.cstore c58394a4f328ba8b
field AvailableChain.FGSA.StoreBundle.meta 2bfc8e8b6832fafd
field AvailableChain.FGSA.StoreBundle.nest 64775dd340e0ae36
field AvailableChain.FGSA.StoreBundle.lease a346494bfd9c0667
def AvailableChain.FGSA.StoreBundleInvariant fa3e8f2410b1ae7a
theorem AvailableChain.FGSA.StoreBundleInvariant_def e9250617bbffd16e
def AvailableChain.FGSA.FMonotone dfdb68ba2d50278c
def AvailableChain.FGSA.MetadataInvariant bf73605bc92375c0
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

### `AvailableChainFGSA.Statements.WindowHeight`

```text
```

## `AvailableChainFGSARun`

### `AvailableChainFGSARun.Statements.AC`

```text
def AvailableChain.FGSA.Run.fgsaAC 4bb49dff50b34a1f
```

### `AvailableChainFGSARun.Statements.Acceptance`

```text
def AvailableChain.FGSA.Run.fgsaAdmissionTime bedfcddab6bbb51e
def AvailableChain.FGSA.Run.fgsaTimely c0c2ad54c5e0cdb2
def AvailableChain.FGSA.Run.fgsaAcceptanceInv e569330571972857
def AvailableChain.FGSA.Run.fgsaTrigger f829d800f0b3e01a
```

### `AvailableChainFGSARun.Statements.Client`

```text
def AvailableChain.FGSA.Run.EmitsRow fedb989026f8aea4
def AvailableChain.FGSA.Run.EmittedRowsNoSlash 1956fb14df2f9ee2
def AvailableChain.FGSA.Run.decodeRowObject c65deef1e5daf902
def AvailableChain.FGSA.Run.fgClientEvent eb54cde1598d4057
def AvailableChain.FGSA.Run.fgClientEvents 75fa75dc55bc77cd
```

### `AvailableChainFGSARun.Statements.Emission`

```text
def AvailableChain.FGSA.Run.EmissionRowsValid 041ac080a7f2aa25
def AvailableChain.FGSA.Run.decode c06272443aaec6cb
def AvailableChain.FGSA.Run.HonestEmissionWellFormed 288c1b28e024f92a
def AvailableChain.FGSA.Run.HonestProposalDecodes 45aee49cc52851f6
```

### `AvailableChainFGSARun.Statements.Excludes`

```text
inductive AvailableChain.FGSA.Run.EpochStep fd4ceac3383d83af
ctor AvailableChain.FGSA.Run.EpochStep.deliver 6426b097ea826e09
ctor AvailableChain.FGSA.Run.EpochStep.clock d52eac00641b4d25
def AvailableChain.FGSA.Run.Epoch b8255fcc593847d1
def AvailableChain.FGSA.Run.excludesFixed 33450e1e228f9c3e
```

### `AvailableChainFGSARun.Statements.Interface`

```text
def AvailableChain.FGSA.Run.isRowObject 46c1a87e68a912bf
theorem AvailableChain.FGSA.Run.isRowObject_def eb00db839d1d7c38
def AvailableChain.FGSA.Run.fgsaDelay 0f058916fd796f4a
theorem AvailableChain.FGSA.Run.fgsaDelay_def 54d3e26d8ba60814
def AvailableChain.FGSA.Run.fgsaInterface 9d61225024dbd13b
def AvailableChain.FGSA.Run.fgsaOutputs b1b0a8b3a36f7bd5
def AvailableChain.FGSA.Run.finalizedOut 55643171cdfdcd96
```

### `AvailableChainFGSARun.Statements.ReceiptCoverage`

```text
structure AvailableChain.FGSA.Run.ReceiptCoveragePremises 22127cd25c416eb2
ctor AvailableChain.FGSA.Run.ReceiptCoveragePremises.mk 93a4a094bfa53070
field AvailableChain.FGSA.Run.ReceiptCoveragePremises.within 17094b265aed6bb5
field AvailableChain.FGSA.Run.ReceiptCoveragePremises.slotWindow c8079a80fb7da5df
field AvailableChain.FGSA.Run.ReceiptCoveragePremises.compat 7cd82ed6851bc859
field AvailableChain.FGSA.Run.ReceiptCoveragePremises.deadline e39ddeee31de2de6
def AvailableChain.FGSA.Run.ReceiptCoverageStatement 6b77202db9f7e373
theorem AvailableChain.FGSA.Run.ReceiptCoverageStatement_def 8cf50c70ba9ac15a
```

### `AvailableChainFGSARun.Statements.Receipts`

```text
def AvailableChain.FGSA.Run.blockOf? 594cc77aaa075947
```

### `AvailableChainFGSARun.Statements.Slashing`

```text
def AvailableChain.FGSA.Run.fgsaEvidence 1b9808a1a59c7fca
def AvailableChain.FGSA.Run.fgsaSlashing b202475bb3b5734f
```

## `AvailableChainFGSAClaims`

### `AvailableChainFGSAClaims.Claims.Clean`

```text
def AvailableChain.FGSA.Run.CleanHistoryAt 2142b45013c99511
def AvailableChain.FGSA.Run.CleanGateAt 672e013271acffca
def AvailableChain.FGSA.Run.CleanTruncAt 0cdcb011f6bae73e
def AvailableChain.FGSA.Run.CleanSafetyAt 8372df216d2446ec
def AvailableChain.FGSA.Run.CleanCutClaim d72f0d5cbb665a18
def AvailableChain.FGSA.Run.CleanCutZeroClaim 387ed8f55014f80b
def AvailableChain.FGSA.Run.CleanHistoryClaim 435c26d85e12acfa
def AvailableChain.FGSA.Run.CleanPrefixTruncationClaim 91d7768b4841bdb7
def AvailableChain.FGSA.Run.CleanSafetyClaim 9e4fd760bca2ed4e
def AvailableChain.FGSA.Run.CleanCutPosClaim b7f0458d51f037fd
```

### `AvailableChainFGSAClaims.Claims.Foundations`

```text
def AvailableChain.FGSA.Run.ClientSafeAll 6891a92b0a2bb4a7
def AvailableChain.FGSA.Run.ClientSafetyClaim a19b6005fbd27a71
def AvailableChain.FGSA.Run.ClientSafetyBaseClaim b1a167a7144b7bb5
def AvailableChain.FGSA.Run.FGFoundationClaim 5a74d0356347ab36
def AvailableChain.FGSA.Run.SrcFrameAboveClaim 1debf3a49a50a4dc
def AvailableChain.FGSA.Run.RunFGBlock 8e05285ea4b6647a
def AvailableChain.FGSA.Run.CarrierAt fb39f3ab232d590f
def AvailableChain.FGSA.Run.StoreAt 687db83dfd0c0472
def AvailableChain.FGSA.Run.ActiveViewAt 855039d0af6d641b
def AvailableChain.FGSA.Run.LeaseOriginsAt 17fdc5804dcbd95a
def AvailableChain.FGSA.Run.SourceDisciplineBaseAt 2c999e3410f572a8
def AvailableChain.FGSA.Run.SourceDisciplineAt 5c53925ab9c8a781
def AvailableChain.FGSA.Run.CarrierClaim 6f8c7f1489826501
def AvailableChain.FGSA.Run.ChainCertificatesAt abc84b6e6125763c
def AvailableChain.FGSA.Run.ChainCertificatesClaim 451d7cb9c4b6fc75
def AvailableChain.FGSA.Run.StoreClaim e2d6d2fa63ad9cda
def AvailableChain.FGSA.Run.ActiveViewClaim f63330656c5be005
def AvailableChain.FGSA.Run.LeaseOriginsClaim 2739fefaa77c8a89
def AvailableChain.FGSA.Run.ReconcileAt 0b854ac1559f9330
def AvailableChain.FGSA.Run.ReconcileClaim 32212cdcfcedc15e
def AvailableChain.FGSA.Run.OutputNestingAt 6032e1967d69dd8e
def AvailableChain.FGSA.Run.OutputNestingClaim dd15ac70d244d3d8
def AvailableChain.FGSA.Run.FrameAt 8b87c8d211be709a
def AvailableChain.FGSA.Run.FrameClaim 778f7592b9269d93
def AvailableChain.FGSA.Run.SourceDisciplineBaseClaim 26b785d202de501f
def AvailableChain.FGSA.Run.SourceDisciplineClaim 6a9a27a2457c67b6
def AvailableChain.FGSA.Run.RowServiceBaseClaim c3b4548271e501af
def AvailableChain.FGSA.Run.RowServiceClaim 09d790af1f244f65
```

### `AvailableChainFGSAClaims.Claims.Healing`

```text
def AvailableChain.FGSA.Run.RowPermissionAt 9f628441ca7b84d8
def AvailableChain.FGSA.Run.RowPermissionClaim 5353838e611a7ed0
def AvailableChain.FGSA.Run.HealingInputClaim 8eaed8b271945ef7
def AvailableChain.FGSA.Run.HTimeConcl 3bbfcb2616890fda
def AvailableChain.FGSA.Run.HTimeClaim 5e4dd0f9a647ae39
def AvailableChain.FGSA.Run.ResetArrivalConcl 7523b1735eef07b5
def AvailableChain.FGSA.Run.ResetArrivalClaim da1c8d77ce5805f0
def AvailableChain.FGSA.Run.RenewedPromotionConcl 7341af55b3f64d07
def AvailableChain.FGSA.Run.RenewedPromotionClaim 34b5193eed0e51b6
```

### `AvailableChainFGSAClaims.Claims.Shared`

```text
def AvailableChain.FGSA.Run.SameLabelAt bf9823a6f43a241b
def AvailableChain.FGSA.Run.SameLabelClaim 9c0d99fa744f684c
def AvailableChain.FGSA.Run.HeadReachesLoAt ea9605b11af49c6d
def AvailableChain.FGSA.Run.HeadReachesLoClaim 99c8bf3815f43186
def AvailableChain.FGSA.Run.ReleaseStoreAt e83760d4e3844d23
def AvailableChain.FGSA.Run.ReleaseStoreClaim 543b8ade45fd298f
def AvailableChain.FGSA.Run.ReleaseAt 1916c3a7fb9437c1
def AvailableChain.FGSA.Run.ReleaseClaim 7533f3da0f9be398
```

### `AvailableChainFGSAClaims.FGSAClaims`

```text
structure AvailableChain.FGSA.Run.FGSASafetyClaims 4405799e15b6a07b
ctor AvailableChain.FGSA.Run.FGSASafetyClaims.mk a7b82577aaa8a413
field AvailableChain.FGSA.Run.FGSASafetyClaims.carrier 6cce7781082db3e4
field AvailableChain.FGSA.Run.FGSASafetyClaims.chainCertificates 4168423b0e96b00d
field AvailableChain.FGSA.Run.FGSASafetyClaims.store 24c38fd51eeaca90
field AvailableChain.FGSA.Run.FGSASafetyClaims.activeView daddd73ee78e00db
field AvailableChain.FGSA.Run.FGSASafetyClaims.leaseOrigins a1c2a7c676a663ea
field AvailableChain.FGSA.Run.FGSASafetyClaims.reconcile 352442585220ee26
field AvailableChain.FGSA.Run.FGSASafetyClaims.outputNesting ea2b3c0c0aec54c5
field AvailableChain.FGSA.Run.FGSASafetyClaims.frame b97001055061d3ce
field AvailableChain.FGSA.Run.FGSASafetyClaims.clientSafety 0f481ebd2fd7b24e
field AvailableChain.FGSA.Run.FGSASafetyClaims.clientSafetyBase d8239e899740961b
field AvailableChain.FGSA.Run.FGSASafetyClaims.sourceDisciplineBase 5098c4c3eb3414ff
field AvailableChain.FGSA.Run.FGSASafetyClaims.sourceDiscipline cf2010579ee78065
field AvailableChain.FGSA.Run.FGSASafetyClaims.sameLabel 4c7e955e72e8f137
field AvailableChain.FGSA.Run.FGSASafetyClaims.releaseStore a3ef1e94748e78b0
field AvailableChain.FGSA.Run.FGSASafetyClaims.release 40c1d2d73abe0995
field AvailableChain.FGSA.Run.FGSASafetyClaims.headReachesLo 948197213e8f494d
field AvailableChain.FGSA.Run.FGSASafetyClaims.cleanCut 1a53c40c2a341c93
field AvailableChain.FGSA.Run.FGSASafetyClaims.cleanHistory d5e5e10b1740c224
field AvailableChain.FGSA.Run.FGSASafetyClaims.cleanPrefixTruncation a9ee397a39ea00f4
field AvailableChain.FGSA.Run.FGSASafetyClaims.cleanSafety 583d2568de01286e
structure AvailableChain.FGSA.Run.FGSASafetyInterfaces 02029afd58ccca98
ctor AvailableChain.FGSA.Run.FGSASafetyInterfaces.mk f9d952f9013c3b4f
field AvailableChain.FGSA.Run.FGSASafetyInterfaces.fgFoundation 1a88af7cffbfcf68
field AvailableChain.FGSA.Run.FGSASafetyInterfaces.srcFrameAbove 583826a6ea6f1ba8
field AvailableChain.FGSA.Run.FGSASafetyInterfaces.cpPrefix 1d3ea7c61444632a
field AvailableChain.FGSA.Run.FGSASafetyInterfaces.cpCompat 152c07ee31dd6fdd
field AvailableChain.FGSA.Run.FGSASafetyInterfaces.tSrc 939525cc66361245
field AvailableChain.FGSA.Run.FGSASafetyInterfaces.labelBound b61c97b4f4e5ea51
field AvailableChain.FGSA.Run.FGSASafetyInterfaces.timingContract df9d01adb2d80bc6
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
def AvailableChain.FGSA.Run.B_Q b33324d24b04476e
def AvailableChain.FGSA.Run.B_skip f9a58a9a8e078eff
def AvailableChain.FGSA.Run.γ f21165d8e5c3936c
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
```

### `AvailableChainFGSAClaims.Statements.ChannelProps`

```text
def AvailableChain.FGSA.Run.RCarrierView 6eb109c64322d957
theorem AvailableChain.FGSA.Run.RCarrierView_def a1ec19fbc8ea30aa
def AvailableChain.FGSA.Run.RStore 5639142adea98275
theorem AvailableChain.FGSA.Run.RStore_def 5cd1c0918093bb99
def AvailableChain.FGSA.Run.RActive 58d828d0c8c76fa0
theorem AvailableChain.FGSA.Run.RActive_def ac68bbddc5734426
def AvailableChain.FGSA.Run.RStoreCumul 287cd14e8f15b047
theorem AvailableChain.FGSA.Run.RStoreCumul_def 09bb469318d40993
def AvailableChain.FGSA.Run.RMono 70f35780d30491d8
theorem AvailableChain.FGSA.Run.RMono_def b1fa94a7c566c486
def AvailableChain.FGSA.Run.RFrameExact 16f79721e50c993f
theorem AvailableChain.FGSA.Run.RFrameExact_def 729cf0be93b5bc37
def AvailableChain.FGSA.Run.RFrame e7d46550d641ccb9
theorem AvailableChain.FGSA.Run.RFrame_def 8911db2884abe91c
def AvailableChain.FGSA.Run.RGeo b73b14901c078702
theorem AvailableChain.FGSA.Run.RGeo_def a1eaf3143fff52ac
def AvailableChain.FGSA.Run.RCert bf90754da36cbfc4
theorem AvailableChain.FGSA.Run.RCert_def eaa972a2fa7496a9
def AvailableChain.FGSA.Run.RRec 76c9b003e37c279b
theorem AvailableChain.FGSA.Run.RRec_def fa0b704023fca2b1
def AvailableChain.FGSA.Run.TSrc 54cb214b0fb0bc2d
theorem AvailableChain.FGSA.Run.TSrc_def 7a2730ca3a8f7325
def AvailableChain.FGSA.Run.LabelBound 8eac53261fb52d5d
theorem AvailableChain.FGSA.Run.LabelBound_def 9532bf9d1afd8676
def AvailableChain.FGSA.Run.TChain a391d965ba5c249c
theorem AvailableChain.FGSA.Run.TChain_def 17193d1e1a827164
def AvailableChain.FGSA.Run.TCompat 0581a1cc21978f98
theorem AvailableChain.FGSA.Run.TCompat_def efb70428819a7b20
structure AvailableChain.FGSA.Run.AncestorClosed a82d5e35de829ed2
ctor AvailableChain.FGSA.Run.AncestorClosed.mk fa2827ea0465c6d5
field AvailableChain.FGSA.Run.AncestorClosed.down 6a9b1aab4f3ebb3e
def AvailableChain.FGSA.Run.FrameBelow a056c6a9d68936a7
theorem AvailableChain.FGSA.Run.FrameBelow_def e3cde698e9716757
def AvailableChain.FGSA.Run.RStrat 3dc42d829010fe22
theorem AvailableChain.FGSA.Run.RStrat_def ecf35b7ca6bf28a3
def AvailableChain.FGSA.Run.RQCOrigin 3b1360378ffe903b
theorem AvailableChain.FGSA.Run.RQCOrigin_def eb8a97ccf2b6a019
def AvailableChain.FGSA.Run.SrcFrameAbove d063fbb3b5ba87cf
theorem AvailableChain.FGSA.Run.SrcFrameAbove_def 8cb56977188ad634
def AvailableChain.FGSA.Run.SrcFrame d7c622c40472252e
def AvailableChain.FGSA.Run.SrcFrameAboveStmt 5c6ae67191c48c9e
theorem AvailableChain.FGSA.Run.SrcFrameAboveStmt_def 0265ab343f8ecd20
def AvailableChain.FGSA.Run.CPPrefix d320e46e0c53f992
theorem AvailableChain.FGSA.Run.CPPrefix_def f3f75bb74f56f4e6
def AvailableChain.FGSA.Run.CPCompat f82654dce7488e20
theorem AvailableChain.FGSA.Run.CPCompat_def e9d76f3dc0e0320d
def AvailableChain.FGSA.Run.RXing fbf62a404d461df4
def AvailableChain.FGSA.Run.RCap ca66d6bf8d75bb3b
def AvailableChain.FGSA.Run.THigh 942fd2b7a886886b
def AvailableChain.FGSA.Run.TCarrier a023f3732760d570
def AvailableChain.FGSA.Run.TRowsSelect e81e738a1ef9c408
def AvailableChain.FGSA.Run.TRowsSync 0bd3a7b9a0a7bf05
def AvailableChain.FGSA.Run.TRowsReceipt f7b8e5aac7f4b630
theorem AvailableChain.FGSA.Run.TRowsReceipt_def 09ed541c7e045fd0
structure AvailableChain.FGSA.Run.TRows ed05771d6c946637
ctor AvailableChain.FGSA.Run.TRows.mk 3ff4b7fc66411cba
field AvailableChain.FGSA.Run.TRows.select 2b5b554c0de1dafa
field AvailableChain.FGSA.Run.TRows.sync f1f67238dda193ca
field AvailableChain.FGSA.Run.TRows.receipt 923c18306065e0e9
def AvailableChain.FGSA.Run.SourceBefore 1e816fe050657438
def AvailableChain.FGSA.Run.Kept fb7bf8d8fc6a5df4
def AvailableChain.FGSA.Run.KeepOrCause d34e41386cdc68ab
def AvailableChain.FGSA.Run.RExcl d230230c17a78fee
def AvailableChain.FGSA.Run.RKeep 62529e3c70ada648
def AvailableChain.FGSA.Run.RFProv 106c9127fae89aa5
def AvailableChain.FGSA.Run.TDel 30b52c83e608617b
def AvailableChain.FGSA.Run.TDelReset cfb5960cbda61a51
def AvailableChain.FGSA.Run.TGeom 5660f7e08d47c078
def AvailableChain.FGSA.Run.ExactService 0cdb87185db63da1
def AvailableChain.FGSA.Run.PhaseInterval d31a4aec09d9162a
def AvailableChain.FGSA.Run.Transfers 2bf0298d7431f744
def AvailableChain.FGSA.Run.PhaseBody 147be2d3cd30982a
def AvailableChain.FGSA.Run.TPerm e1cdcd352338da2f
def AvailableChain.FGSA.Run.ProposalGap 80a9c13f1cbbe0d1
def AvailableChain.FGSA.Run.RepairAfter 6fa9c6421bc3edec
def AvailableChain.FGSA.Run.TRepair a554a7410d3df5a1
def AvailableChain.FGSA.Run.OpeningCovered 7695659534b0605c
def AvailableChain.FGSA.Run.OpeningEntry 6095ece9d9386ba2
def AvailableChain.FGSA.Run.TCommon fc663ce7f709baea
def AvailableChain.FGSA.Run.TFrontier ac9fa69e7bb607ec
def AvailableChain.FGSA.Run.FinalityRowCarriage 613cd1d6bed644c0
theorem AvailableChain.FGSA.Run.FinalityRowCarriage_def b6233699f9a69ffa
```

### `AvailableChainFGSAClaims.Statements.Channels`

```text
def AvailableChain.FGSA.Run.certified 207960d7a7d972ed
theorem AvailableChain.FGSA.Run.certified_def 677a018958ebc702
def AvailableChain.FGSA.Run.treeT 2b69ec7b0e57e60e
def AvailableChain.FGSA.Run.treeErased 781b0a26d002a754
def AvailableChain.FGSA.Run.frameR bab4814904993b95
def AvailableChain.FGSA.Run.domainR aa29e3ca1373c9e3
def AvailableChain.FGSA.Run.finR aac46ba18b4700c2
def AvailableChain.FGSA.Run.FAdvance 295788c25e134f22
def AvailableChain.FGSA.Run.sourceCandidates 15ae2568da2c93f7
def AvailableChain.FGSA.Run.jointSource 86267d5e1b3a154c
def AvailableChain.FGSA.Run.proposerHead 06f25d657c41d8e9
def AvailableChain.FGSA.Run.outputS f3f1bf40e501d936
theorem AvailableChain.FGSA.Run.frameR_def 146407f11f684960
theorem AvailableChain.FGSA.Run.jointSource_def b4ef51a350df402c
theorem AvailableChain.FGSA.Run.sourceCandidates_def a419a14c1319e0ab
theorem AvailableChain.FGSA.Run.domainR_def 197fc05ac5bd6f6e
theorem AvailableChain.FGSA.Run.treeT_def 3acc17fc60e79846
theorem AvailableChain.FGSA.Run.proposerHead_def 2e8145564355fb0d
theorem AvailableChain.FGSA.Run.FAdvance_def 910b82c4a0274160
def AvailableChain.FGSA.Run.R_at 33b8cc8663f7f84a
def AvailableChain.FGSA.Run.D_at 1f8c0d604d14168e
def AvailableChain.FGSA.Run.FAdvanceAt 0ac18b6ff88e6ddc
def AvailableChain.FGSA.Run.candidatesAt 12ed284f8da5279c
def AvailableChain.FGSA.Run.proposalHeadAt 16dbe0bb638b150a
def AvailableChain.FGSA.Run.actionHead e0047c0cf96342f3
def AvailableChain.FGSA.Run.actionTriple 8c3032c495b611d3
def AvailableChain.FGSA.Run.namedEntry a50c73e0c7ee36db
def AvailableChain.FGSA.Run.EntryBelow cd3e92dff737d1ed
def AvailableChain.FGSA.Run.RowSigner 5b24ba2c710a1be8
def AvailableChain.FGSA.Run.HonestRowAt 25b00ce1534b9f36
def AvailableChain.FGSA.Run.HonestRowBefore 1600ef7fabd7eaaf
theorem AvailableChain.FGSA.Run.HonestRowBefore_def 06495d79820fea3b
def AvailableChain.FGSA.Run.RowComplete 24956392a482c870
def AvailableChain.FGSA.Run.HonestCarrier 0deefe540ab8d538
def AvailableChain.FGSA.Run.HeldAt 1e011c576a9009a0
def AvailableChain.FGSA.Run.BlockInRunBefore 678607105eef5bbe
theorem AvailableChain.FGSA.Run.RowSigner_def 3ec58e72d469a30f
theorem AvailableChain.FGSA.Run.HonestRowAt_def 14b6a6cb0af0ea09
def AvailableChain.FGSA.Run.rowHeld 10b14191989e4cf6
def AvailableChain.FGSA.Run.proposalStateAt 2ab29b361cb24b50
def AvailableChain.FGSA.Run.heldAtProposal 0b46c9e0ddac1b6c
def AvailableChain.FGSA.Run.onParentChain 16001f9178f4d1bb
def AvailableChain.FGSA.Run.HeldBefore d58d259ed41e569b
def AvailableChain.FGSA.Run.ValidForParent fabaedac3b5ca6e0
theorem AvailableChain.FGSA.Run.ValidForParent_def 0c867b6f1e9d7fa3
def AvailableChain.FGSA.Run.HeightMatch f0c9e773cba2ba8b
theorem AvailableChain.FGSA.Run.HeightMatch_def b7cc79b84da0a4b8
def AvailableChain.FGSA.Run.headAtLabel a7da3a49751f5eef
```

### `AvailableChainFGSAClaims.Statements.ComposeStmt`

```text
def AvailableChain.FGSA.Run.windowIdx f4b1a721298821e7
structure AvailableChain.FGSA.Run.TimingContract 2df88e69ba0612b8
ctor AvailableChain.FGSA.Run.TimingContract.mk 6a789d25a3f338d7
field AvailableChain.FGSA.Run.TimingContract.rowLag ea03afcb1077268c
field AvailableChain.FGSA.Run.TimingContract.certLag 9aa5d3c696fc2c49
field AvailableChain.FGSA.Run.TimingContract.label 36b500e9dcde08fd
field AvailableChain.FGSA.Run.TimingContract.atomic a84dba28e3272335
field AvailableChain.FGSA.Run.TimingContract.tickFG b19b67c3b015181f
structure AvailableChain.FGSA.Run.FGFoundation c3dd06b6b61e2ea8
ctor AvailableChain.FGSA.Run.FGFoundation.mk 7a9a2e486c0bf9f8
field AvailableChain.FGSA.Run.FGFoundation.store 68f1e9ee46ddc0b9
field AvailableChain.FGSA.Run.FGFoundation.cumul 227ce01d9aa6aabb
field AvailableChain.FGSA.Run.FGFoundation.mono da8f07dc45202d73
field AvailableChain.FGSA.Run.FGFoundation.frame 5cd2e27f6e31bb6a
field AvailableChain.FGSA.Run.FGFoundation.geo 9b5b361b1c886f51
field AvailableChain.FGSA.Run.FGFoundation.strat 888b860d75ba0432
field AvailableChain.FGSA.Run.FGFoundation.reconcile c54f31d4b136a9d7
def AvailableChain.FGSA.Run.TStart 0ceff4344da2a212
def AvailableChain.FGSA.Run.FullVoteService b59707086c1e9bff
def AvailableChain.FGSA.Run.TVote f1a12919b5e6bf2c
def AvailableChain.FGSA.Run.WalkBatch 79402ecbcc9dd2b5
def AvailableChain.FGSA.Run.TWalk d0fadacd3140689e
structure AvailableChain.FGSA.Run.CoreServices 8d12d3a545504ecd
ctor AvailableChain.FGSA.Run.CoreServices.mk 22236a6866e763fc
field AvailableChain.FGSA.Run.CoreServices.start e79aeb8a9547089d
field AvailableChain.FGSA.Run.CoreServices.vote 6bb2c6304a5d87b9
field AvailableChain.FGSA.Run.CoreServices.walk cee97cf92cf884e9
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
def AvailableChain.FGSA.Run.B'_reset efabed0ebbb1a5ad
def AvailableChain.FGSA.Run.ResetArrivalStatement 12e9f5ddefedb391
theorem AvailableChain.FGSA.Run.ResetArrivalStatement_def bbb460f6787bb2f1
def AvailableChain.FGSA.Run.ResetArrivalFullStatement a2264e05015d5a24
theorem AvailableChain.FGSA.Run.ResetArrivalFullStatement_def c22e76a70a961002
def AvailableChain.FGSA.Run.KernelConclusion 676e24812132504b
structure AvailableChain.FGSA.Run.KernelPt 9235f1fbc5c48477
ctor AvailableChain.FGSA.Run.KernelPt.mk 32c96b623cc6f691
field AvailableChain.FGSA.Run.KernelPt.w 6cbd0d7075070f20
field AvailableChain.FGSA.Run.KernelPt.r e581c6d88b7635d7
structure AvailableChain.FGSA.Run.KernelPrem f71ff401f4e7adbc
ctor AvailableChain.FGSA.Run.KernelPrem.mk 26f067c2d6f35bb0
field AvailableChain.FGSA.Run.KernelPrem.set 48551cb75be55c0a
field AvailableChain.FGSA.Run.KernelPrem.window 41ba4fc29103de90
field AvailableChain.FGSA.Run.KernelPrem.start 49215b89fc522545
field AvailableChain.FGSA.Run.KernelPrem.hhor fcebbe8fc96c3e2a
field AvailableChain.FGSA.Run.KernelPrem.input f672be76e615befc
field AvailableChain.FGSA.Run.KernelPrem.services 433fad4093986cfe
def AvailableChain.FGSA.Run.KernelFromContract 8c6f93788413417c
def AvailableChain.FGSA.Run.KernelACSide aeca224d5be55dc9
def AvailableChain.FGSA.Run.kernelStart e6b6603fb8e48a3f
structure AvailableChain.FGSA.Run.HealTContract 4f5b2b564182827c
ctor AvailableChain.FGSA.Run.HealTContract.mk e43e9aa4258f5e43
field AvailableChain.FGSA.Run.HealTContract.del 57a9c0101fa8d9d2
field AvailableChain.FGSA.Run.HealTContract.delReset f9b0eb422a67d1fb
field AvailableChain.FGSA.Run.HealTContract.perm afc128d7b76c2b87
field AvailableChain.FGSA.Run.HealTContract.repair 8cd430b4eadf320d
field AvailableChain.FGSA.Run.HealTContract.common f258abd3ad99b2e9
field AvailableChain.FGSA.Run.HealTContract.frontier cd96d52abd301234
field AvailableChain.FGSA.Run.HealTContract.geom e3124fc82d48c790
def AvailableChain.FGSA.Run.frontierAtIdx e1d19089f154845c
def AvailableChain.FGSA.Run.TopEvidence ce3611626f58a15d
def AvailableChain.FGSA.Run.ContestEvidence d885b8f32c09d89c
def AvailableChain.FGSA.Run.EffectiveEvent a8661afe977559a7
def AvailableChain.FGSA.Run.AttemptPhaseAt 5ed5bc449e969f8f
def AvailableChain.FGSA.Run.ServedFrontier 1bbc7f8117fd8013
def AvailableChain.FGSA.Run.AttemptValid 563986719354a05a
def AvailableChain.FGSA.Run.attemptBudget b92a1475dc2a8a8b
def AvailableChain.FGSA.Run.AttemptEndsBy cc1bd92e0301309c
def AvailableChain.FGSA.Run.SettledPhaseFrame 24a04da0419fe77d
theorem AvailableChain.FGSA.Run.SettledPhaseFrame_def 8d420fa765edeb84
def AvailableChain.FGSA.Run.RPhase 244d67a1833be9ba
theorem AvailableChain.FGSA.Run.RPhase_def f1d27fe4f276e6fa
structure AvailableChain.FGSA.Run.HealRContract 78103b399f25c6af
ctor AvailableChain.FGSA.Run.HealRContract.mk 961a753344ea35d7
field AvailableChain.FGSA.Run.HealRContract.xing 42331a79b343af71
field AvailableChain.FGSA.Run.HealRContract.cap 424d51e90e15e13d
field AvailableChain.FGSA.Run.HealRContract.phase 2463cd684f00c839
field AvailableChain.FGSA.Run.HealRContract.excl f1c002e3dc9d688f
field AvailableChain.FGSA.Run.HealRContract.keep c196cccabce3e978
field AvailableChain.FGSA.Run.HealRContract.fprov 663d79e0ae0460ed
def AvailableChain.FGSA.Run.ProgressAttemptStatement 6924bb1a6bc24266
theorem AvailableChain.FGSA.Run.ProgressAttemptStatement_def 5915f6f25556a356
```

### `AvailableChainFGSAClaims.Statements.Counts`

```text
def AvailableChain.FGSA.Run.awakeHonestIn 54415ad59f9cd90a
def AvailableChain.FGSA.Run.HonestProposal ae9f4b671ef57b39
```

### `AvailableChainFGSAClaims.Statements.Fold`

```text
inductive AvailableChain.FGSA.Run.RowKind da2d1119c2ef39fc
ctor AvailableChain.FGSA.Run.RowKind.target a127adc0838fa2e4
ctor AvailableChain.FGSA.Run.RowKind.progress e22f9613e6edb955
def AvailableChain.FGSA.Run.RowNames c882dc72ac13848c
def AvailableChain.FGSA.Run.SlotChain 026b8cab17d0c00f
def AvailableChain.FGSA.Run.EntryAt aea819f8aa95fe86
def AvailableChain.FGSA.Run.JustifiedCross 6b8cbe6c88240a4a
def AvailableChain.FGSA.Run.MixedCross a506f2fc0515cc03
def AvailableChain.FGSA.Run.NoMixedOnPath 791608de6fa8694b
def AvailableChain.FGSA.Run.SeatCovers 646bf4c87d3ca5d0
def AvailableChain.FGSA.Run.CoveredByChild 6c10ed96dd39c013
def AvailableChain.FGSA.Run.foldTrichotomy df0c8abaa962728d
def AvailableChain.FGSA.Run.StoredProgressConsume fc68b4d6c4103c3b
def AvailableChain.FGSA.Run.NoMixedMaturity f87fa58d8eac1c2f
def AvailableChain.FGSA.Run.NamesEntry 4157bcc504c0ab7f
def AvailableChain.FGSA.Run.rowHeight 8e2499ef46ddafdd
def AvailableChain.FGSA.Run.eventTime 4bdaaa69edcc1980
def AvailableChain.FGSA.Run.honestSeats 8b72b586fce141a3
def AvailableChain.FGSA.Run.ChainRowsBefore 9a8e9fc09b9bfc14
structure AvailableChain.FGSA.Run.PreBatchPrem d05d65038f2a37a3
ctor AvailableChain.FGSA.Run.PreBatchPrem.mk 179561dfb54934ca
field AvailableChain.FGSA.Run.PreBatchPrem.base 066701e40a841286
field AvailableChain.FGSA.Run.PreBatchPrem.faultQ 81d6eda8b7ca10c5
field AvailableChain.FGSA.Run.PreBatchPrem.entry eb1b2962c1e13c2a
field AvailableChain.FGSA.Run.PreBatchPrem.path a3e0351de957af87
field AvailableChain.FGSA.Run.PreBatchPrem.cut 0da3645c1f8c5be9
field AvailableChain.FGSA.Run.PreBatchPrem.early 39ce1372a10a4d3a
field AvailableChain.FGSA.Run.PreBatchPrem.rows 91709441c8c91d8c
field AvailableChain.FGSA.Run.PreBatchPrem.noRow 2603e3703a25858b
def AvailableChain.FGSA.Run.NoMixedPreBatchParent 8dbd9cdb73f694c2
structure AvailableChain.FGSA.Run.BatchPrem 33ac4508d921ea1f
ctor AvailableChain.FGSA.Run.BatchPrem.mk a879660792f1368a
field AvailableChain.FGSA.Run.BatchPrem.base 66d260bd6ff72825
field AvailableChain.FGSA.Run.BatchPrem.faultQ 537f196e70fcdc47
field AvailableChain.FGSA.Run.BatchPrem.deltaF a5cdbff1afb3c21d
field AvailableChain.FGSA.Run.BatchPrem.rowsReceipt fac57f659ee82105
field AvailableChain.FGSA.Run.BatchPrem.horizon 9478e904974f806c
field AvailableChain.FGSA.Run.BatchPrem.carrier 05324962f3beec22
field AvailableChain.FGSA.Run.BatchPrem.after 2fb3f0136154b0f4
field AvailableChain.FGSA.Run.BatchPrem.valid 49c4ade389a00df2
field AvailableChain.FGSA.Run.BatchPrem.entry 7240641d1fbb073b
field AvailableChain.FGSA.Run.BatchPrem.path 59a0a7bcd9e6aa94
field AvailableChain.FGSA.Run.BatchPrem.above 1a86b0d0543dd40f
def AvailableChain.FGSA.Run.BatchCoverage 9cab76f73953c4c1
def AvailableChain.FGSA.Run.FirstCross 023091fce982a4f7
def AvailableChain.FGSA.Run.ProposalWalk edad2064583210c9
```

### `AvailableChainFGSAClaims.Statements.Healed`

```text
def AvailableChain.FGSA.Run.healStart 1b930249fbeb559b
def AvailableChain.FGSA.Run.HealSuffix e1b5678a61476327
def AvailableChain.FGSA.Run.Healed c6e03a3b74d87d55
def AvailableChain.FGSA.Run.H2A 419d37e727f037f8
def AvailableChain.FGSA.Run.H2Prime 6a0174bacd15f09b
def AvailableChain.FGSA.Run.H3 e0e50448d7eb4024
def AvailableChain.FGSA.Run.H4 f39b40a2b441b3f3
def AvailableChain.FGSA.Run.H5RawTransfer 4c8699cf4a54b63d
def AvailableChain.FGSA.Run.H6GateService 8ee6648b06de57d1
structure AvailableChain.FGSA.Run.HealT 9d23f993c8b7b52d
ctor AvailableChain.FGSA.Run.HealT.mk afd3f2b415c260bd
field AvailableChain.FGSA.Run.HealT.h1 3bb20eb459f57541
field AvailableChain.FGSA.Run.HealT.h2 ddf52ea8189b2ea8
field AvailableChain.FGSA.Run.HealT.rows 161bddfdd7b0b0b4
structure AvailableChain.FGSA.Run.HealAC eb178fcc50e96efb
ctor AvailableChain.FGSA.Run.HealAC.mk f348b5aec04a8e10
field AvailableChain.FGSA.Run.HealAC.h2A 42fa1f962abd5784
field AvailableChain.FGSA.Run.HealAC.h2' ea138af7cf976965
field AvailableChain.FGSA.Run.HealAC.h3 2461b19af26a5e24
field AvailableChain.FGSA.Run.HealAC.h4 faa22b926afd219d
field AvailableChain.FGSA.Run.HealAC.h5 530a45851eabfcab
field AvailableChain.FGSA.Run.HealAC.h6 188357881afdc812
structure AvailableChain.FGSA.Run.HealingInput 45199104cda7dcb1
ctor AvailableChain.FGSA.Run.HealingInput.mk f9c948ba45bd3659
field AvailableChain.FGSA.Run.HealingInput.healed 68ea39dc75fee5ea
field AvailableChain.FGSA.Run.HealingInput.wit 9e36395d58813193
field AvailableChain.FGSA.Run.HealingInput.t 81e29bad14d4242e
field AvailableChain.FGSA.Run.HealingInput.ac 31a54502d78384d5
def AvailableChain.FGSA.Run.HTimeStatement e248f4f27aa69bcd
theorem AvailableChain.FGSA.Run.HTimeStatement_def ebdd667a6e0753b3
def AvailableChain.FGSA.Run.HTimeBestStatement 68d4d34b235e0414
theorem AvailableChain.FGSA.Run.HTimeBestStatement_def a59b142516d9146b
def AvailableChain.FGSA.Run.HTimeSearchStatement bdfc45519b8b77c6
theorem AvailableChain.FGSA.Run.HTimeSearchStatement_def 610bea6a76dfa446
```

### `AvailableChainFGSAClaims.Statements.Packages.Finality`

```text
def AvailableChain.FGSA.Run.finalityWindow 255d8581daab93d3
structure AvailableChain.FGSA.Run.FirstFinalityPrem 9852e823d08b3ef5
ctor AvailableChain.FGSA.Run.FirstFinalityPrem.mk 32d3a490b162d140
field AvailableChain.FGSA.Run.FirstFinalityPrem.set 10cba112185d8b60
field AvailableChain.FGSA.Run.FirstFinalityPrem.hhor cc2fea7b31bad028
structure AvailableChain.FGSA.Run.FinalityLivenessPrem 213a93bc5b960826
ctor AvailableChain.FGSA.Run.FinalityLivenessPrem.mk c88fa64074d5961e
field AvailableChain.FGSA.Run.FinalityLivenessPrem.set 0c805abdb040e5a7
field AvailableChain.FGSA.Run.FinalityLivenessPrem.late 08aeda8ea6fd9067
field AvailableChain.FGSA.Run.FinalityLivenessPrem.hhor 1a7b8bb8534a8d50
structure AvailableChain.FGSA.Run.ProposalFinalPrem 0eeeae31adf8e866
ctor AvailableChain.FGSA.Run.ProposalFinalPrem.mk e261d1f24621fae7
field AvailableChain.FGSA.Run.ProposalFinalPrem.set aa4aa230f129b4d0
field AvailableChain.FGSA.Run.ProposalFinalPrem.prop da0cb65540b0119f
field AvailableChain.FGSA.Run.ProposalFinalPrem.late b494b45b59852bad
field AvailableChain.FGSA.Run.ProposalFinalPrem.hhor 0f8348f6c953b545
structure AvailableChain.FGSA.Run.AboveFrontierPrem 25d9a2a35a4957db
ctor AvailableChain.FGSA.Run.AboveFrontierPrem.mk c49ec3d7cdf8d323
field AvailableChain.FGSA.Run.AboveFrontierPrem.set 8699d44562ce5651
field AvailableChain.FGSA.Run.AboveFrontierPrem.late b675abcf63588a2c
field AvailableChain.FGSA.Run.AboveFrontierPrem.hhor 5bd8ee0d232fe26d
structure AvailableChain.FGSA.Run.QualifiedFinalityPrem 6938f5e549d25da0
ctor AvailableChain.FGSA.Run.QualifiedFinalityPrem.mk 7d636aaf892e68a0
field AvailableChain.FGSA.Run.QualifiedFinalityPrem.set 59a0971da3cd9554
field AvailableChain.FGSA.Run.QualifiedFinalityPrem.hhor c5c6a54031e8dfce
structure AvailableChain.FGSA.Run.SkipFinalityPrem 1cf5bed42af742c6
ctor AvailableChain.FGSA.Run.SkipFinalityPrem.mk 1e98e8c9fa9c508c
field AvailableChain.FGSA.Run.SkipFinalityPrem.set 2a1dd3a5ea5924a2
field AvailableChain.FGSA.Run.SkipFinalityPrem.hhor f75be1cf65d046be
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
structure AvailableChain.FGSA.Run.HealingPrem 955d363124bd7afb
ctor AvailableChain.FGSA.Run.HealingPrem.mk 0b8a173faa192501
field AvailableChain.FGSA.Run.HealingPrem.set f9a93367ce5aa24b
structure AvailableChain.FGSA.Run.HealingWitnessPrem 50d6bfdea9529a6b
field AvailableChain.FGSA.Run.HealingWitnessPrem.toHealingPrem bb32b5aefcd93f3c
ctor AvailableChain.FGSA.Run.HealingWitnessPrem.mk 5024797d96c72fef
field AvailableChain.FGSA.Run.HealingWitnessPrem.h0 efc3370ddda473cc
structure AvailableChain.FGSA.Run.HealingTimePrem 70353f5fdcf05b3c
field AvailableChain.FGSA.Run.HealingTimePrem.toHealingPrem 1e992e0c96035b78
ctor AvailableChain.FGSA.Run.HealingTimePrem.mk 3c9acc9df859440f
field AvailableChain.FGSA.Run.HealingTimePrem.hhor d763db397282c22f
structure AvailableChain.FGSA.Run.ResetArrivalPrem 49f20917e3ddbde7
field AvailableChain.FGSA.Run.ResetArrivalPrem.toHealingPrem ad6d9b2c008c7f45
ctor AvailableChain.FGSA.Run.ResetArrivalPrem.mk 7d8798b3909c26be
field AvailableChain.FGSA.Run.ResetArrivalPrem.hhor 2ed1bc5364ebc6e0
structure AvailableChain.FGSA.Run.ResetArrivalFullPrem 9252e9baff67e275
field AvailableChain.FGSA.Run.ResetArrivalFullPrem.toHealingPrem b92124fabfc568d6
ctor AvailableChain.FGSA.Run.ResetArrivalFullPrem.mk f0f7dac548bb437e
field AvailableChain.FGSA.Run.ResetArrivalFullPrem.hhor ea3061a5c7b8de4e
structure AvailableChain.FGSA.Run.KernelJoinedPrem 261a48995bd9518a
ctor AvailableChain.FGSA.Run.KernelJoinedPrem.mk 72a431de0f7e1630
field AvailableChain.FGSA.Run.KernelJoinedPrem.set ac51bf7b42438076
field AvailableChain.FGSA.Run.KernelJoinedPrem.window 7078498fc71f68b8
field AvailableChain.FGSA.Run.KernelJoinedPrem.start 94f7cf78b3879fc3
field AvailableChain.FGSA.Run.KernelJoinedPrem.hhor 6a14359dad50ca06
structure AvailableChain.FGSA.Run.HealingAttemptPrem ab4400dbd04cf230
field AvailableChain.FGSA.Run.HealingAttemptPrem.toHealingPrem 12c92dbafc3b8662
ctor AvailableChain.FGSA.Run.HealingAttemptPrem.mk dfd3a701710619a3
field AvailableChain.FGSA.Run.HealingAttemptPrem.valid 23ebeb3c864511df
structure AvailableChain.FGSA.Run.HealingInputPrem 7585de2d3c6e0dad
field AvailableChain.FGSA.Run.HealingInputPrem.toHealingWitnessPrem 7f73be0c8df0706e
ctor AvailableChain.FGSA.Run.HealingInputPrem.mk 0e6b26e90e288d5f
field AvailableChain.FGSA.Run.HealingInputPrem.hhor 324f5eb808273bdf
structure AvailableChain.FGSA.Run.RenewedPromotionPrem d91bb382265cd744
field AvailableChain.FGSA.Run.RenewedPromotionPrem.toHealingPrem e62feb7c4abbb52c
ctor AvailableChain.FGSA.Run.RenewedPromotionPrem.mk 5d295f003b062fea
field AvailableChain.FGSA.Run.RenewedPromotionPrem.hhor 4334c405d02e1b02
```

### `AvailableChainFGSAClaims.Statements.Packages.Outage`

```text
structure AvailableChain.FGSA.Run.OutagePrem fbaf02e3fef83403
ctor AvailableChain.FGSA.Run.OutagePrem.mk a3355ae30a565fb7
field AvailableChain.FGSA.Run.OutagePrem.set 15345d5744f2db50
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
structure AvailableChain.FGSA.Run.BasePrem 4a309e3ff82d7c65
ctor AvailableChain.FGSA.Run.BasePrem.mk f2cdee284742a583
field AvailableChain.FGSA.Run.BasePrem.set 826ab106e753ebcf
structure AvailableChain.FGSA.Run.SameLabelPrem a8fd0ddfbb1ace6d
ctor AvailableChain.FGSA.Run.SameLabelPrem.mk 200315923956a9f3
field AvailableChain.FGSA.Run.SameLabelPrem.set 4648bb862402afa0
field AvailableChain.FGSA.Run.SameLabelPrem.sync 8476a0f76ad34a27
structure AvailableChain.FGSA.Run.SourceDisciplinePrem 6a59f4c068ad3cee
ctor AvailableChain.FGSA.Run.SourceDisciplinePrem.mk e8d8e747825ebe90
field AvailableChain.FGSA.Run.SourceDisciplinePrem.set d8de5d92065ca209
field AvailableChain.FGSA.Run.SourceDisciplinePrem.quorum 577d626942c85d00
structure AvailableChain.FGSA.Run.FinalizedSafetyPrem e279c616a154d758
ctor AvailableChain.FGSA.Run.FinalizedSafetyPrem.mk 32589dc584ce8af2
field AvailableChain.FGSA.Run.FinalizedSafetyPrem.set 43af0512cfa04853
field AvailableChain.FGSA.Run.FinalizedSafetyPrem.fault ed1f1bd58bdf72eb
structure AvailableChain.FGSA.Run.CleanPrem df572a8cbd001694
ctor AvailableChain.FGSA.Run.CleanPrem.mk 909c10bdf8493af7
field AvailableChain.FGSA.Run.CleanPrem.set 109fc5c490bc4b96
structure AvailableChain.FGSA.Run.CleanPrefixPrem 76ab918789128ef9
ctor AvailableChain.FGSA.Run.CleanPrefixPrem.mk e1c4a4b03231482b
field AvailableChain.FGSA.Run.CleanPrefixPrem.set aa89caa00f372465
structure AvailableChain.FGSA.Run.CleanCutPrem b9b14ed4c9388528
ctor AvailableChain.FGSA.Run.CleanCutPrem.mk e5de08b4199d1838
field AvailableChain.FGSA.Run.CleanCutPrem.set 95ec236bb9b84472
structure AvailableChain.FGSA.Run.ReleasePrem f951ebd1a4a2c8d5
ctor AvailableChain.FGSA.Run.ReleasePrem.mk 93cdd403d23fcd24
field AvailableChain.FGSA.Run.ReleasePrem.set 795f576984533d88
field AvailableChain.FGSA.Run.ReleasePrem.lt 55d7d9cc8e4b1ae4
```

### `AvailableChainFGSAClaims.Statements.Phases`

```text
def AvailableChain.FGSA.Run.finHeight 45ca642905486866
structure AvailableChain.FGSA.Run.FreshPrem 10f1729fe47cc0ba
ctor AvailableChain.FGSA.Run.FreshPrem.mk c6291830e117dde5
field AvailableChain.FGSA.Run.FreshPrem.base ddd1a3bcf2e3e11b
field AvailableChain.FGSA.Run.FreshPrem.faultQ 1c6c2c37eac63811
field AvailableChain.FGSA.Run.FreshPrem.cut 5d37b44ed1bf8a39
field AvailableChain.FGSA.Run.FreshPrem.early 4c8825aef3795431
field AvailableChain.FGSA.Run.FreshPrem.rows b98ba9124f67a2bb
field AvailableChain.FGSA.Run.FreshPrem.noNextRow 59165eb7fdda8871
field AvailableChain.FGSA.Run.FreshPrem.noFinRow 3d5ee6afb878f05a
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
def AvailableChain.FGSA.Run.storeAt c71cd96c91fbce76
def AvailableChain.FGSA.Run.S_at 6467bab7fa19033a
def AvailableChain.FGSA.Run.F_at 5a7d143bc876285c
def AvailableChain.FGSA.Run.J_at c1ed18e9ed9536fd
def AvailableChain.FGSA.Run.gateIn 30899bafd84a12e2
theorem AvailableChain.FGSA.Run.gateIn_def e284ee2cb2082440
def AvailableChain.FGSA.Run.gateResult e6e9f9413811ec41
theorem AvailableChain.FGSA.Run.gateResult_def f27d6b2cb41c283d
def AvailableChain.FGSA.Run.isGateTime de71406ad46da144
theorem AvailableChain.FGSA.Run.isGateTime_def a991674f5c9d52f5
def AvailableChain.FGSA.Run.IsGateTick a36c0c514860a140
def AvailableChain.FGSA.Run.gateResultAt 97c213cda6d15617
def AvailableChain.FGSA.Run.gatePassedAt 3cd9531ba4117d92
def AvailableChain.FGSA.Run.fastAt 1904a8ef80ae087e
def AvailableChain.FGSA.Run.headAtIdx 6b1f7153ab168704
def AvailableChain.FGSA.Run.vHead b40976acf14ea737
theorem AvailableChain.FGSA.Run.vHead_def 2e0a8049daf15d0a
def AvailableChain.FGSA.Run.actionSourceFG 6fec2f14d6768d4f
theorem AvailableChain.FGSA.Run.actionSourceFG_def 25a63036c6d5a8c4
def AvailableChain.FGSA.Run.actionSource 5b57a14cbf059cfa
def AvailableChain.FGSA.Run.labelBoundAt dab34539d19976f0
def AvailableChain.FGSA.Run.DeliveredAt d60df4331e8db6df
def AvailableChain.FGSA.Run.HandlesRowAt 499c4d8f1411a9fc
def AvailableChain.FGSA.Run.AcceptsFinalBefore ddebb5d18830748b
def AvailableChain.FGSA.Run.cleanResults 712b426b4b78c6b9
def AvailableChain.FGSA.Run.BelowLabel 9d247e155c38c25e
```

### `AvailableChainFGSAClaims.Statements.Recurrence`

```text
```

### `AvailableChainFGSAClaims.Statements.Regimes`

```text
structure AvailableChain.FGSA.Run.Base₂ e8cf2d8b90d4b364
ctor AvailableChain.FGSA.Run.Base₂.mk c4cf856795efe7b4
field AvailableChain.FGSA.Run.Base₂.valid c0d7cb1b879918b8
field AvailableChain.FGSA.Run.Base₂.linked 86d0e70f190f34da
field AvailableChain.FGSA.Run.Base₂.cstar 0121cdffa25d0378
field AvailableChain.FGSA.Run.Base₂.noRestart 7b86012bc65f284e
field AvailableChain.FGSA.Run.Base₂.delta 49d3863db95e66fc
structure AvailableChain.FGSA.Run.HealthyPrefix₂ fa2f6f4586200873
ctor AvailableChain.FGSA.Run.HealthyPrefix₂.mk 5121a8bc065be485
field AvailableChain.FGSA.Run.HealthyPrefix₂.base 73cb09cf78348dbd
field AvailableChain.FGSA.Run.HealthyPrefix₂.cut 676a499deb68d6a9
field AvailableChain.FGSA.Run.HealthyPrefix₂.healthy 39a94daafbb125c8
field AvailableChain.FGSA.Run.HealthyPrefix₂.deltaF 3f5c5c175f2d2318
field AvailableChain.FGSA.Run.HealthyPrefix₂.partBefore defb81a33e8763ed
structure AvailableChain.FGSA.Run.CleanPrefix₂ b69d9435fd39f09e
field AvailableChain.FGSA.Run.CleanPrefix₂.toHealthyPrefix₂ ddfa583c56880d98
ctor AvailableChain.FGSA.Run.CleanPrefix₂.mk e519a79bc1131d34
field AvailableChain.FGSA.Run.CleanPrefix₂.partAt 0b84ada72e5cf0a6
def AvailableChain.FGSA.Run.CleanCut₂ 65844070ec71441b
structure AvailableChain.FGSA.Run.Clean₂ 3c453b9406cbdcf1
ctor AvailableChain.FGSA.Run.Clean₂.mk 475c42052ff0c077
field AvailableChain.FGSA.Run.Clean₂.pre 2281b143011050b7
field AvailableChain.FGSA.Run.Clean₂.gst 613af87bb933bf5f
structure AvailableChain.FGSA.Run.Recovery₂ 1c37259cbb539a9c
ctor AvailableChain.FGSA.Run.Recovery₂.mk 1145d9d8f873c95e
field AvailableChain.FGSA.Run.Recovery₂.sync 5055e87ce0597b25
field AvailableChain.FGSA.Run.Recovery₂.deltaF 66d519654dc17b19
field AvailableChain.FGSA.Run.Recovery₂.gap d1a6440cd46584f7
field AvailableChain.FGSA.Run.Recovery₂.base db1fef8013de7652
field AvailableChain.FGSA.Run.Recovery₂.fault a0c8dbe9ef0533c2
field AvailableChain.FGSA.Run.Recovery₂.awake fca31e3aed22b5f7
field AvailableChain.FGSA.Run.Recovery₂.gapPos bf94a1317601d583
def AvailableChain.FGSA.Run.BaseSet 395b606b2562acb7
def AvailableChain.FGSA.Run.CleanSet 0f63644313f9c168
def AvailableChain.FGSA.Run.CleanCutSet f68326f7d266749f
def AvailableChain.FGSA.Run.CleanPrefixSet 38efe081d557ceee
def AvailableChain.FGSA.Run.HealingSet f0fd0cfb16bb1655
structure AvailableChain.FGSA.Run.FinalitySet 09e5552942c9e214
ctor AvailableChain.FGSA.Run.FinalitySet.mk 290807db6557097e
field AvailableChain.FGSA.Run.FinalitySet.core 9bf60c92ff8e6c89
field AvailableChain.FGSA.Run.FinalitySet.recur aad09273fa7bf5d7
structure AvailableChain.FGSA.Run.Outage₂ fd45d040f3180fdf
ctor AvailableChain.FGSA.Run.Outage₂.mk 09ddccefa4647809
field AvailableChain.FGSA.Run.Outage₂.pre d8617200f9d599f4
field AvailableChain.FGSA.Run.Outage₂.sleepy 44c5a8210bbaa50c
field AvailableChain.FGSA.Run.Outage₂.order b4a8fb5713dd32e2
field AvailableChain.FGSA.Run.Outage₂.lag c2a36e0810595c9e
field AvailableChain.FGSA.Run.Outage₂.budget 0f0571ae9977b790
field AvailableChain.FGSA.Run.Outage₂.fastPart 0a15c0b652169035
def AvailableChain.FGSA.Run.OutageSet c147b13e3d746099
```

### `AvailableChainFGSAClaims.Statements.Windows`

```text
def AvailableChain.FGSA.Run.WinSpec fa4fc5d533070a99
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
def AvailableChain.FGSA.Run.cleanWinAt 338ae8933ae34604
def AvailableChain.FGSA.Run.cleanWin 0ec265466f61dab4
def AvailableChain.FGSA.Run.cleanPrefixWin 7495dce92a51dc1b
def AvailableChain.FGSA.Run.cleanLabelWin 4e71d16ab5d84dea
def AvailableChain.FGSA.Run.gapWin 15d97ea8fba6aad0
def AvailableChain.FGSA.Run.formWin a9d9b48d6c5c8557
def AvailableChain.FGSA.Run.formWinAt 841b9f4563fff07d
def AvailableChain.FGSA.Run.kernelWin e301fa04f3c4e966
def AvailableChain.FGSA.Run.trigWin 479f59f4bd597d09
def AvailableChain.FGSA.Run.outWin 8132f22ff3b6aaf0
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
def AvailableChain.FGSA.Run.oldRowHeights 503e042e4855519c
def AvailableChain.FGSA.Run.muOf d20850f2c7b96e21
def AvailableChain.FGSA.Run.high 0f28f9ddeef86251
def AvailableChain.FGSA.Run.honestFrontier a675c4e6ca5a3a36
def AvailableChain.FGSA.Run.HeightRow b2d61434a278ef79
structure AvailableChain.FGSA.Run.H0Reset ac54a81f6990dca8
ctor AvailableChain.FGSA.Run.H0Reset.mk 6219051fb34469c0
field AvailableChain.FGSA.Run.H0Reset.rG_after d663e3d69b97f50b
field AvailableChain.FGSA.Run.H0Reset.rG_first 7010c8f04965747f
field AvailableChain.FGSA.Run.H0Reset.cut d0c2a8f3da5bae24
field AvailableChain.FGSA.Run.H0Reset.frontier 258b757512334b83
field AvailableChain.FGSA.Run.H0Reset.rowCap 9bd482cb842f8c51
field AvailableChain.FGSA.Run.H0Reset.mu_le b441f679c84cd727
field AvailableChain.FGSA.Run.H0Reset.cut_lower 5eeeb8f6870483f9
field AvailableChain.FGSA.Run.H0Reset.cut_upper eba0fa035b3ed9d2
field AvailableChain.FGSA.Run.H0Reset.reset_row 679c4f1749eb0237
field AvailableChain.FGSA.Run.H0Reset.reset_first f5a88c44abae0dfb
field AvailableChain.FGSA.Run.H0Reset.label 87be72df0895f1a8
field AvailableChain.FGSA.Run.H0Reset.fresh bec6a6d34a5fc3bd
field AvailableChain.FGSA.Run.H0Reset.synchronous 2f90ef59186dafa7
structure AvailableChain.FGSA.Run.H0 653012a7716ea8f2
field AvailableChain.FGSA.Run.H0.toH0Reset 4d87f1b1390248c4
ctor AvailableChain.FGSA.Run.H0.mk 2bbcf0827a1937ef
field AvailableChain.FGSA.Run.H0.proposal_lower 6143a5804b7361c9
field AvailableChain.FGSA.Run.H0.proposal 1eca3fbcc95b70aa
field AvailableChain.FGSA.Run.H0.proposal_first 6b378d946f15c825
field AvailableChain.FGSA.Run.H0.after_gst 69f15196ea2977d9
field AvailableChain.FGSA.Run.H0.source_prefix 91d61fe678df9714
def AvailableChain.FGSA.Run.tstarOf 6014f50f8ffd4bf7
```
