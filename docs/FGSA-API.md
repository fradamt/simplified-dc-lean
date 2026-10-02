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

### `AvailableChainFGSA.Statements.Invariants`

```text
inductive AvailableChain.FGSA.Reachable 714cca319d21438b
ctor AvailableChain.FGSA.Reachable.init bf1f83e0424a3f81
ctor AvailableChain.FGSA.Reachable.tick cfbe0e960e9980ba
ctor AvailableChain.FGSA.Reachable.deliver 0d5ba56521e2c53c
def AvailableChain.FGSA.NestOK 130e2646fb4577ff
def AvailableChain.FGSA.SACompat f338d5747785cc54
def AvailableChain.FGSA.LeaseBelowOutputStore 0c24caa058c09550
theorem AvailableChain.FGSA.LeaseBelowOutputStore_def 8e4138cdcdeca65c
def AvailableChain.FGSA.FastOrigin 55103ff0d11f32d6
structure AvailableChain.FGSA.CStoreInv 49cb65e7f2a75634
ctor AvailableChain.FGSA.CStoreInv.mk 3e0297ff43fa20b2
field AvailableChain.FGSA.CStoreInv.fg 8153e2ec292ccfdd
field AvailableChain.FGSA.CStoreInv.rootInj e7627b033572d7be
field AvailableChain.FGSA.CStoreInv.baseTree 0cf0595766c4cff4
field AvailableChain.FGSA.CStoreInv.saCompat ff6a3cb5a37fcd52
field AvailableChain.FGSA.CStoreInv.Smem 562616cdbd18f36d
field AvailableChain.FGSA.CStoreInv.fastOrigin cf14e2571e3b7891
field AvailableChain.FGSA.CStoreInv.fastDom 0928b8d813132a96
field AvailableChain.FGSA.CStoreInv.genuineKeys 6ec409b9bb2270df
field AvailableChain.FGSA.CStoreInv.leaseKeys 139f30251a1ecc71
def AvailableChain.FGSA.Inv0 c1b4da1db5894d5b
structure AvailableChain.FGSA.MetaInv 1b4fbaa6d9735884
ctor AvailableChain.FGSA.MetaInv.mk e6c31b66606bc64e
field AvailableChain.FGSA.MetaInv.wireTree c0da483971744edb
field AvailableChain.FGSA.MetaInv.treeWire 2afb5f800eadd408
field AvailableChain.FGSA.MetaInv.proposalsNodup 5e7eb4ecd7272044
field AvailableChain.FGSA.MetaInv.stampKeys 9c018709bb2edbac
field AvailableChain.FGSA.MetaInv.blocksNodup 0f696455c493a663
field AvailableChain.FGSA.MetaInv.poolDecodes b3ae42636cd66eb4
field AvailableChain.FGSA.MetaInv.poolNodup 951044634854696c
field AvailableChain.FGSA.MetaInv.noGenesisWire 3d5faa31609512be
def AvailableChain.FGSA.ContentAgree 9f1216009903713b
```

### `AvailableChainFGSA.Statements.Store`

```text
def AvailableChain.FGSA.OutputNestingStored fc8b44e7de347a4d
def AvailableChain.FGSA.StoreInvariant 0e45d2cf5f139e27
structure AvailableChain.FGSA.StoreBundle 3ed7e1a89ee9734d
ctor AvailableChain.FGSA.StoreBundle.mk b4e59e34b0cd6606
field AvailableChain.FGSA.StoreBundle.cstore d1bd9e027de5c439
field AvailableChain.FGSA.StoreBundle.meta 86acdee99beaac27
field AvailableChain.FGSA.StoreBundle.nest f148a72dd3aeac58
field AvailableChain.FGSA.StoreBundle.lease 94fc9c3eeef6ae05
def AvailableChain.FGSA.StoreBundleInvariant f36a89c0824f2bbc
theorem AvailableChain.FGSA.StoreBundleInvariant_def 17a9a027e220d898
def AvailableChain.FGSA.FMonotone 997812adaed071f2
def AvailableChain.FGSA.MetadataInvariant 1a43f749c669202e
```

### `AvailableChainFGSA.Statements.WindowCertificate`

```text
def AvailableChain.FGSA.Window.projectFinality ba05ae418852b5ca
theorem AvailableChain.FGSA.Window.projectFinality_def 73cc801dfe20c6b2
def AvailableChain.FGSA.Window.projectCertEntry e041d7ad22bd1ba7
theorem AvailableChain.FGSA.Window.projectCertEntry_def 25fe0f85797c49a3
def AvailableChain.FGSA.Window.certificateHeight 2bd4da292d2d6222
theorem AvailableChain.FGSA.Window.certificateHeight_def f2bba24fbbb2bbfc
def AvailableChain.FGSA.Window.certificateFinality 887aba06a0ba72ca
theorem AvailableChain.FGSA.Window.certificateFinality_def 135966bdf1bb604c
def AvailableChain.FGSA.Window.certificateFolded 889244aacc68bd78
theorem AvailableChain.FGSA.Window.certificateFolded_def 4bbee960c0339cd6
def AvailableChain.FGSA.Window.certificateSelection 597e28d5dc1d531a
theorem AvailableChain.FGSA.Window.certificateSelection_def a44a4ea81205f60e
def AvailableChain.FGSA.Window.EntryOriginAt 1f60aee4cca77eb2
theorem AvailableChain.FGSA.Window.EntryOriginAt_def be6c0c6b1bd29ca4
```

### `AvailableChainFGSA.Statements.WindowHeight`

```text
def AvailableChain.FGSA.Window.projectHeight d465358b1b5b1c3f
theorem AvailableChain.FGSA.Window.projectHeight_def 27c7c57450a8487c
```

## `AvailableChainFGSARun`

### `AvailableChainFGSARun.Statements.AC`

```text
def AvailableChain.FGSA.Run.fgsaAC 3dd5cfbf39f77c59
```

### `AvailableChainFGSARun.Statements.Acceptance`

```text
def AvailableChain.FGSA.Run.fgsaAdmissionTime 125ef115ff9f9458
def AvailableChain.FGSA.Run.fgsaTimely cc013efc3ef4b7c4
def AvailableChain.FGSA.Run.fgsaAcceptanceInv bfb9c63bb709ea85
def AvailableChain.FGSA.Run.fgsaTrigger 4c563adf00e16df0
```

### `AvailableChainFGSARun.Statements.Client`

```text
def AvailableChain.FGSA.Run.EmitsRow c231d91fabf02ff2
def AvailableChain.FGSA.Run.EmittedRowsNoSlash 5fad5b120530a728
def AvailableChain.FGSA.Run.decodeRowObject edb41e1a5863faa8
def AvailableChain.FGSA.Run.fgClientEvent 23fd92aa64c3b34d
def AvailableChain.FGSA.Run.fgClientEvents 4636395814a705f7
```

### `AvailableChainFGSARun.Statements.Emission`

```text
def AvailableChain.FGSA.Run.EmissionRowsValid 28980a41f78a6dd3
def AvailableChain.FGSA.Run.decode c06272443aaec6cb
def AvailableChain.FGSA.Run.HonestEmissionWellFormed c10e2089994e17c0
def AvailableChain.FGSA.Run.HonestProposalDecodes 3d0ba57961b5f05c
```

### `AvailableChainFGSARun.Statements.Excludes`

```text
inductive AvailableChain.FGSA.Run.EpochStep ac8e6ccad8c70539
ctor AvailableChain.FGSA.Run.EpochStep.deliver 44dc247048dd0bdf
ctor AvailableChain.FGSA.Run.EpochStep.clock 88575ec15646fdc3
def AvailableChain.FGSA.Run.Epoch c5d95b2bb576d0df
def AvailableChain.FGSA.Run.excludesFixed 99f1d66534b5de44
```

### `AvailableChainFGSARun.Statements.Interface`

```text
def AvailableChain.FGSA.Run.isRowObject 2d6bc9ca969b9a25
theorem AvailableChain.FGSA.Run.isRowObject_def 9615d7df30b94276
def AvailableChain.FGSA.Run.fgsaDelay 137d4db1c0898648
theorem AvailableChain.FGSA.Run.fgsaDelay_def 3cc5c1ee294c5602
def AvailableChain.FGSA.Run.fgsaInterface 592ec9e38803db69
def AvailableChain.FGSA.Run.fgsaOutputs 05ade1602887227f
def AvailableChain.FGSA.Run.finalizedOut eb13de3f9e21b2a8
```

### `AvailableChainFGSARun.Statements.ReceiptCoverage`

```text
structure AvailableChain.FGSA.Run.ReceiptCoveragePremises 4a784e25509762b8
ctor AvailableChain.FGSA.Run.ReceiptCoveragePremises.mk 9bd24ec90b71f10e
field AvailableChain.FGSA.Run.ReceiptCoveragePremises.within 79fb74e2fc0b8b9b
field AvailableChain.FGSA.Run.ReceiptCoveragePremises.slotWindow f9c3e346a43293a1
field AvailableChain.FGSA.Run.ReceiptCoveragePremises.compat 547eca20dec203bf
field AvailableChain.FGSA.Run.ReceiptCoveragePremises.deadline 8b84f2d09ecfe2f8
def AvailableChain.FGSA.Run.ReceiptCoverageStatement d93dc877d9366149
theorem AvailableChain.FGSA.Run.ReceiptCoverageStatement_def a466271be62ea2ac
```

### `AvailableChainFGSARun.Statements.Receipts`

```text
def AvailableChain.FGSA.Run.blockOf? d87770b19fcbcf65
```

### `AvailableChainFGSARun.Statements.Slashing`

```text
def AvailableChain.FGSA.Run.fgsaEvidence 9eba3b221236d864
def AvailableChain.FGSA.Run.fgsaSlashing 96af9fb016428e91
```

## `AvailableChainFGSAClaims`

### `AvailableChainFGSAClaims.Claims.Clean`

```text
def AvailableChain.FGSA.Run.CleanHistoryAt f6aa7a46bc53d933
def AvailableChain.FGSA.Run.CleanGateAt a911e2e489c00514
def AvailableChain.FGSA.Run.CleanTruncAt dcbc5748dd3670f4
def AvailableChain.FGSA.Run.CleanSafetyAt 33f9d609b2ffc9c2
def AvailableChain.FGSA.Run.CleanCutClaim f6f6730b43af5dca
def AvailableChain.FGSA.Run.CleanCutZeroClaim a24b78944acd412d
def AvailableChain.FGSA.Run.CleanHistoryClaim 85278ed388d386dc
def AvailableChain.FGSA.Run.CleanPrefixTruncationClaim 0d23ea5f282f4db9
def AvailableChain.FGSA.Run.CleanSafetyClaim 0cbbd09f67cb1bc4
def AvailableChain.FGSA.Run.CleanCutPosClaim 48b210d71c1e473b
```

### `AvailableChainFGSAClaims.Claims.Foundations`

```text
def AvailableChain.FGSA.Run.ClientSafeAll 804e7b70f505fb71
def AvailableChain.FGSA.Run.ClientSafetyClaim d042c948f2367b07
def AvailableChain.FGSA.Run.ClientSafetyBaseClaim 5735cec3a335a36b
def AvailableChain.FGSA.Run.FGFoundationClaim bbba81fb9ef9c360
def AvailableChain.FGSA.Run.SrcFrameAboveClaim 90eeed4a0db332b2
def AvailableChain.FGSA.Run.RunFGBlock 5b1e1030f99b3b48
def AvailableChain.FGSA.Run.CarrierAt a8774382083d3655
def AvailableChain.FGSA.Run.StoreAt d0b8c3d0a8540f68
def AvailableChain.FGSA.Run.ActiveViewAt 7d22435be27bbef5
def AvailableChain.FGSA.Run.LeaseOriginsAt d05e3cbcbfab2948
def AvailableChain.FGSA.Run.SourceDisciplineBaseAt c5d33b7f07efef62
def AvailableChain.FGSA.Run.SourceDisciplineAt b6e50f3f52e2a867
def AvailableChain.FGSA.Run.CarrierClaim 102e148c4ec71bd3
def AvailableChain.FGSA.Run.ChainCertificatesAt 173b2bca0ac3e27e
def AvailableChain.FGSA.Run.ChainCertificatesClaim e1b45dafab7440a3
def AvailableChain.FGSA.Run.StoreClaim cb22bc90f96c3940
def AvailableChain.FGSA.Run.ActiveViewClaim 3656279947d6ac13
def AvailableChain.FGSA.Run.LeaseOriginsClaim 24456d17c784aaaf
def AvailableChain.FGSA.Run.ReconcileAt bea5ba077a213f02
def AvailableChain.FGSA.Run.ReconcileClaim 853ab37782086228
def AvailableChain.FGSA.Run.OutputNestingAt a2d538253995cb34
def AvailableChain.FGSA.Run.OutputNestingClaim 838170a5a67f01da
def AvailableChain.FGSA.Run.FrameAt b205463da1b6faec
def AvailableChain.FGSA.Run.FrameClaim 6ce4bd608dc8ba59
def AvailableChain.FGSA.Run.SourceDisciplineBaseClaim bace5bb70864a9b9
def AvailableChain.FGSA.Run.SourceDisciplineClaim 947371be08c23314
def AvailableChain.FGSA.Run.RowServiceBaseClaim a24b4f986a5f3c45
def AvailableChain.FGSA.Run.RowServiceClaim 9fd8d7ffc003d337
```

### `AvailableChainFGSAClaims.Claims.Healing`

```text
def AvailableChain.FGSA.Run.RowPermissionAt 4d8c43cb75b93cca
def AvailableChain.FGSA.Run.RowPermissionClaim fc0c883ed6677bf2
def AvailableChain.FGSA.Run.HealingInputClaim 6b8499811d8328cd
def AvailableChain.FGSA.Run.HTimeConcl c28c00abfa1885c8
def AvailableChain.FGSA.Run.HTimeClaim 8e1c04bbc7a89b5b
def AvailableChain.FGSA.Run.ResetArrivalConcl 939e769d617d1b2f
def AvailableChain.FGSA.Run.ResetArrivalClaim d4936b2abf26ab56
def AvailableChain.FGSA.Run.RenewedPromotionConcl 9c2f0e955750ec51
def AvailableChain.FGSA.Run.RenewedPromotionClaim 86698f6df461858c
```

### `AvailableChainFGSAClaims.Claims.Shared`

```text
def AvailableChain.FGSA.Run.SameLabelAt cb5cc9016b0fe621
def AvailableChain.FGSA.Run.SameLabelClaim 7ef3b761845acc82
def AvailableChain.FGSA.Run.HeadReachesLoAt b7df7a59c61bd2cf
def AvailableChain.FGSA.Run.HeadReachesLoClaim e53147e3198cb830
def AvailableChain.FGSA.Run.ReleaseStoreAt 4821a3dc715fe93d
def AvailableChain.FGSA.Run.ReleaseStoreClaim 8686f70b1a563f39
def AvailableChain.FGSA.Run.ReleaseAt 15316b89685903f3
def AvailableChain.FGSA.Run.ReleaseClaim cbe0b3d5fba8ceca
```

### `AvailableChainFGSAClaims.FGSAClaims`

```text
structure AvailableChain.FGSA.Run.FGSASafetyClaims 7ab44509b6f0b821
ctor AvailableChain.FGSA.Run.FGSASafetyClaims.mk f071eb2a5be2fbb5
field AvailableChain.FGSA.Run.FGSASafetyClaims.carrier 73aff145dc36952a
field AvailableChain.FGSA.Run.FGSASafetyClaims.chainCertificates a84d900a5fcc977b
field AvailableChain.FGSA.Run.FGSASafetyClaims.store 9723da5e119c011e
field AvailableChain.FGSA.Run.FGSASafetyClaims.activeView 2720065cb01ce0ad
field AvailableChain.FGSA.Run.FGSASafetyClaims.leaseOrigins ee2e8ddd30bc3d24
field AvailableChain.FGSA.Run.FGSASafetyClaims.reconcile c0c6a65f71cbe558
field AvailableChain.FGSA.Run.FGSASafetyClaims.outputNesting af037751e9b28bd3
field AvailableChain.FGSA.Run.FGSASafetyClaims.frame 4f91d27e4380c400
field AvailableChain.FGSA.Run.FGSASafetyClaims.clientSafety 6362b88f75761380
field AvailableChain.FGSA.Run.FGSASafetyClaims.clientSafetyBase 5df12576ba27826d
field AvailableChain.FGSA.Run.FGSASafetyClaims.sourceDisciplineBase 1042711bfd265599
field AvailableChain.FGSA.Run.FGSASafetyClaims.sourceDiscipline c1d18ad9b25dcf33
field AvailableChain.FGSA.Run.FGSASafetyClaims.sameLabel dc72bb72bf83df31
field AvailableChain.FGSA.Run.FGSASafetyClaims.releaseStore 8fdb7722e871e5fe
field AvailableChain.FGSA.Run.FGSASafetyClaims.release 2441b4adc3cb6023
field AvailableChain.FGSA.Run.FGSASafetyClaims.headReachesLo 6bf133ee122bff3b
field AvailableChain.FGSA.Run.FGSASafetyClaims.cleanCut 4a0d339b24f9b605
field AvailableChain.FGSA.Run.FGSASafetyClaims.cleanHistory 17ec062f790a38ea
field AvailableChain.FGSA.Run.FGSASafetyClaims.cleanPrefixTruncation aa45c0ddb481a73a
field AvailableChain.FGSA.Run.FGSASafetyClaims.cleanSafety 95764d4e08240a60
structure AvailableChain.FGSA.Run.FGSASafetyInterfaces 354b0ae2296ec222
ctor AvailableChain.FGSA.Run.FGSASafetyInterfaces.mk da63da38282ce6c1
field AvailableChain.FGSA.Run.FGSASafetyInterfaces.fgFoundation 84151390aea20736
field AvailableChain.FGSA.Run.FGSASafetyInterfaces.srcFrameAbove fc9d94762ae647f6
field AvailableChain.FGSA.Run.FGSASafetyInterfaces.cpPrefix 2da9ceef81c64db4
field AvailableChain.FGSA.Run.FGSASafetyInterfaces.cpCompat d1fc8ac359042763
field AvailableChain.FGSA.Run.FGSASafetyInterfaces.tSrc b3d1183179d67cc3
field AvailableChain.FGSA.Run.FGSASafetyInterfaces.labelBound 354b9dec077bf797
field AvailableChain.FGSA.Run.FGSASafetyInterfaces.timingContract de69a68d6a7aea58
```

### `AvailableChainFGSAClaims.Statements.Bounds`

```text
def AvailableChain.FGSA.Run.L 7b7cfa0590c3db52
def AvailableChain.FGSA.Run.P bd21d25525521825
def AvailableChain.FGSA.Run.Γ a8f07481ac7f4562
def AvailableChain.FGSA.Run.ρΓ 98d2e90026653d91
def AvailableChain.FGSA.Run.ρ₁ 15ee277519d1925a
def AvailableChain.FGSA.Run.ρ 889cbcdb0f67cfa5
def AvailableChain.FGSA.Run.E_g 8179027592bf19e0
def AvailableChain.FGSA.Run.E_j 4203faae1100b1fe
def AvailableChain.FGSA.Run.B_c 5f20fdc9e7c5922b
def AvailableChain.FGSA.Run.D_c 2636ae26bf5eaf50
def AvailableChain.FGSA.Run.B_reset 6efacee954020125
def AvailableChain.FGSA.Run.B 1ace4f202d617908
def AvailableChain.FGSA.Run.B_H2 01db6aec00e78d93
def AvailableChain.FGSA.Run.B_H1 ce30c2ac7d2065b9
def AvailableChain.FGSA.Run.B_H 2dc6980b656c0281
def AvailableChain.FGSA.Run.W_F 502c9dc77ccbb6d8
def AvailableChain.FGSA.Run.B_F 2b2639111049e909
def AvailableChain.FGSA.Run.B_heal 87d8979f4a9ef05e
def AvailableChain.FGSA.Run.B_best 99099c3e29c43a22
def AvailableChain.FGSA.Run.B_Q 6e9abf0385ddcebc
def AvailableChain.FGSA.Run.B_skip a94bc91c55caea91
def AvailableChain.FGSA.Run.γ f21165d8e5c3936c
def AvailableChain.FGSA.Run.carrierTime2 f6de72471b331e20
def AvailableChain.FGSA.Run.kernelDeadline e65f9194a6b30590
def AvailableChain.FGSA.Run.ActionDeliveryBounds ebe23696522649ae
def AvailableChain.FGSA.Run.KernelBeforeNextAction 17d766e4a1e64768
def AvailableChain.FGSA.Run.VoteBeforeAction c4cab2539d287701
def AvailableChain.FGSA.Run.GateAfterCarrier2 aff6f5bb090a314f
def AvailableChain.FGSA.Run.GateActionOrder 127ca8eb55b136ca
def AvailableChain.FGSA.Run.FourteenBeforeTwoRounds a5fed03ea4cae181
```

### `AvailableChainFGSAClaims.Statements.BoundsW`

```text
def AvailableChain.FGSA.Run.kappaF 43b254ad4a134ee3
def AvailableChain.FGSA.Run.betaF 38ed79064a2bdd9d
def AvailableChain.FGSA.Run.epsF 2d260b2cda59a1cd
def AvailableChain.FGSA.Run.carrierTimeW 1f59430a1ad46481
def AvailableChain.FGSA.Run.kernelDeadlineW 4c119e0b90497fed
def AvailableChain.FGSA.Run.W_W 91c33b8ada0405ce
def AvailableChain.FGSA.Run.E_gF 6d7456f352e11adc
def AvailableChain.FGSA.Run.E_jF 382e1661b387db0d
def AvailableChain.FGSA.Run.B_cF cd1120a04f34d5f9
def AvailableChain.FGSA.Run.D_cF 70dd41dffd743163
def AvailableChain.FGSA.Run.B_resetF 9e1634eaafb72b75
def AvailableChain.FGSA.Run.BF 18afdf3309a4dfca
def AvailableChain.FGSA.Run.B_H2F 043fbbd5ad62f86e
def AvailableChain.FGSA.Run.B_H1F 79816e4710fd5991
def AvailableChain.FGSA.Run.B_HF 84c992ba0e3628c4
def AvailableChain.FGSA.Run.B'_resetF ae37dd88d08eb8a3
def AvailableChain.FGSA.Run.B_bestF ff7a43c8731be123
def AvailableChain.FGSA.Run.ActionDeliveryBoundsW 0721d6f52cb02629
def AvailableChain.FGSA.Run.KernelBeforeNextActionW 942140b9a60b1fb4
structure AvailableChain.FGSA.Run.LivenessBoundW 78e1ed50c8fa00ec
ctor AvailableChain.FGSA.Run.LivenessBoundW.mk 68f8b39d66b47ade
field AvailableChain.FGSA.Run.LivenessBoundW.kappa_le_R 8cf11b27f9f15a15
theorem AvailableChain.FGSA.Run.kappaF_def 3c0bff1d3dc565aa
theorem AvailableChain.FGSA.Run.betaF_def 84c974826a81a23a
theorem AvailableChain.FGSA.Run.epsF_def dc5b483f64e11f5f
theorem AvailableChain.FGSA.Run.carrierTimeW_def 6cc485fc59ed7fb9
theorem AvailableChain.FGSA.Run.kernelDeadlineW_def f3c39e8fef85cd73
theorem AvailableChain.FGSA.Run.W_W_def b10025e10dfcafdb
theorem AvailableChain.FGSA.Run.E_gF_def 2655b59d74545b5d
theorem AvailableChain.FGSA.Run.E_jF_def b0ead6c0ce5d341b
theorem AvailableChain.FGSA.Run.B_cF_def 856b2268351f4dad
theorem AvailableChain.FGSA.Run.D_cF_def 0c9e577e538ac341
theorem AvailableChain.FGSA.Run.B_resetF_def 682e8156e3e5f2e4
theorem AvailableChain.FGSA.Run.BF_def e9426c4b3ae669ee
theorem AvailableChain.FGSA.Run.B_H2F_def 46a90acd6b079cf7
theorem AvailableChain.FGSA.Run.B_H1F_def 49dceb6c1b7371a3
theorem AvailableChain.FGSA.Run.B_HF_def b8d08ff539c46474
theorem AvailableChain.FGSA.Run.B'_resetF_def 5b4233754e4a8764
theorem AvailableChain.FGSA.Run.B_bestF_def 02bb625918c327eb
theorem AvailableChain.FGSA.Run.ActionDeliveryBoundsW_def 3371def2b2057db2
theorem AvailableChain.FGSA.Run.KernelBeforeNextActionW_def ff13cf19ea6ce282
```

### `AvailableChainFGSAClaims.Statements.ChannelProps`

```text
def AvailableChain.FGSA.Run.RCarrierView 5b4602e3399423ad
theorem AvailableChain.FGSA.Run.RCarrierView_def eb8a33460e066f64
def AvailableChain.FGSA.Run.RStore fe32292ae73a90d3
theorem AvailableChain.FGSA.Run.RStore_def cadcfbd1a85612ef
def AvailableChain.FGSA.Run.RActive a2103acc5dea1f12
theorem AvailableChain.FGSA.Run.RActive_def 8893afceeab489bc
def AvailableChain.FGSA.Run.RStoreCumul 88b14369fb59c099
theorem AvailableChain.FGSA.Run.RStoreCumul_def a1285a2a33a51335
def AvailableChain.FGSA.Run.RMono f324a2e33e24a02a
theorem AvailableChain.FGSA.Run.RMono_def 288739eb661e72f8
def AvailableChain.FGSA.Run.RFrameExact 504bdb803b2db251
theorem AvailableChain.FGSA.Run.RFrameExact_def cebd835c9ddeec21
def AvailableChain.FGSA.Run.RFrame 861f965b0de0d50b
theorem AvailableChain.FGSA.Run.RFrame_def c97be9cad8f08d0e
def AvailableChain.FGSA.Run.RGeo d1789f9f6561c548
theorem AvailableChain.FGSA.Run.RGeo_def ebca4640d2682642
def AvailableChain.FGSA.Run.RCert c592c2e4070687c6
theorem AvailableChain.FGSA.Run.RCert_def 6fd97d0792806cb7
def AvailableChain.FGSA.Run.RRec 6563cb68ca02207d
theorem AvailableChain.FGSA.Run.RRec_def f7671b18df64e9c7
def AvailableChain.FGSA.Run.TSrc 8cedb8f3ed33428b
theorem AvailableChain.FGSA.Run.TSrc_def 20a6f346eccd214f
def AvailableChain.FGSA.Run.LabelBound 7fcab03bb50aa0e7
theorem AvailableChain.FGSA.Run.LabelBound_def b753e4d58463c704
def AvailableChain.FGSA.Run.TChain b4e204c6830f2ab2
theorem AvailableChain.FGSA.Run.TChain_def 842b3d6d20c5cc66
def AvailableChain.FGSA.Run.TCompat 17bbac0158e11b2a
theorem AvailableChain.FGSA.Run.TCompat_def ed5c6c87d43d857a
structure AvailableChain.FGSA.Run.AncestorClosed 593b2f5afe7c4910
ctor AvailableChain.FGSA.Run.AncestorClosed.mk b48754dc553f2a0f
field AvailableChain.FGSA.Run.AncestorClosed.down 3036e679b5e16c54
def AvailableChain.FGSA.Run.FrameBelow b5f99579a3eceef5
theorem AvailableChain.FGSA.Run.FrameBelow_def d4f3816f09fe5405
def AvailableChain.FGSA.Run.RStrat 1c525a0eaf60fda4
theorem AvailableChain.FGSA.Run.RStrat_def f8779609a5056815
def AvailableChain.FGSA.Run.RQCOrigin 1dc8a0ad22540c51
theorem AvailableChain.FGSA.Run.RQCOrigin_def 75db5bce21c7736f
def AvailableChain.FGSA.Run.SrcFrameAbove 048e04a90c2eb269
theorem AvailableChain.FGSA.Run.SrcFrameAbove_def 39908315be10f476
def AvailableChain.FGSA.Run.SrcFrame 39d6d6aa642138d8
def AvailableChain.FGSA.Run.SrcFrameAboveStmt a648029fd04d5ed0
theorem AvailableChain.FGSA.Run.SrcFrameAboveStmt_def e972f3dda78669f6
def AvailableChain.FGSA.Run.CPPrefix b2f1d5eed41d17b4
theorem AvailableChain.FGSA.Run.CPPrefix_def 87a4bdeb2c08e0e8
def AvailableChain.FGSA.Run.CPCompat f3194501235d87ce
theorem AvailableChain.FGSA.Run.CPCompat_def cc2ce3171e3c4d5f
def AvailableChain.FGSA.Run.RXing 90801354f2560596
def AvailableChain.FGSA.Run.RCap 374da8650be39151
def AvailableChain.FGSA.Run.THigh 8d14b866b382794d
def AvailableChain.FGSA.Run.TCarrier 2ca3d568b4dcbe4e
def AvailableChain.FGSA.Run.TRowsSelect 99686555b1523626
def AvailableChain.FGSA.Run.TRowsSync a7881b148c407e33
def AvailableChain.FGSA.Run.TRowsReceipt 50bf67a3c52a717e
theorem AvailableChain.FGSA.Run.TRowsReceipt_def 6d09bb56bd2f3e12
structure AvailableChain.FGSA.Run.TRows 1344e062d56e1319
ctor AvailableChain.FGSA.Run.TRows.mk 93c1f56c37439ed4
field AvailableChain.FGSA.Run.TRows.select 6e0c15fc42fedad4
field AvailableChain.FGSA.Run.TRows.sync e3f92e0867b2e724
field AvailableChain.FGSA.Run.TRows.receipt 429961152b7bb87f
def AvailableChain.FGSA.Run.SourceBefore 7ea41c547473fc0a
def AvailableChain.FGSA.Run.Kept 88b95f179ab283a6
def AvailableChain.FGSA.Run.KeepOrCause 7701b7360c315291
def AvailableChain.FGSA.Run.RExcl 4f2bc0eefbeeee04
def AvailableChain.FGSA.Run.RKeep df8c8216116ae1b2
def AvailableChain.FGSA.Run.RFProv dcf40ad973f48463
def AvailableChain.FGSA.Run.TDel 5f4d3f195c379f5d
def AvailableChain.FGSA.Run.TDelReset 3a7ece35c928d8df
def AvailableChain.FGSA.Run.TGeom 25ee0b67c8d28436
def AvailableChain.FGSA.Run.ExactService 9b8d9dd178d33233
def AvailableChain.FGSA.Run.PhaseInterval 2aaf871762eb9288
def AvailableChain.FGSA.Run.Transfers e53b9efa0c3f1af6
def AvailableChain.FGSA.Run.PhaseBody bd6ba46d2fcd9298
def AvailableChain.FGSA.Run.TPerm f5c89296e82459d1
def AvailableChain.FGSA.Run.ProposalGap 2ab378dbfb37ad87
def AvailableChain.FGSA.Run.RepairAfter e96240be5b5d95a6
def AvailableChain.FGSA.Run.TRepair 2100587ea238f81f
def AvailableChain.FGSA.Run.OpeningCovered d26bdf7a9800ed5a
def AvailableChain.FGSA.Run.OpeningEntry 609eb2448c473290
def AvailableChain.FGSA.Run.TCommon 8990e7632e1d32ec
def AvailableChain.FGSA.Run.TFrontier 3f31b01fac88b8aa
def AvailableChain.FGSA.Run.FinalityRowCarriage 0bec6a8a5eb714a2
theorem AvailableChain.FGSA.Run.FinalityRowCarriage_def 7eaefa1a339b12d4
```

### `AvailableChainFGSAClaims.Statements.Channels`

```text
def AvailableChain.FGSA.Run.certified 4720a9cfc81e8a5f
theorem AvailableChain.FGSA.Run.certified_def c0bb002c30562f98
def AvailableChain.FGSA.Run.treeT 76db33eeaf9376b0
def AvailableChain.FGSA.Run.treeErased 7ebb41647352198e
def AvailableChain.FGSA.Run.frameR fa24245573c0e23f
def AvailableChain.FGSA.Run.domainR 5c6dae51f8d56f5d
def AvailableChain.FGSA.Run.finR 9f88a695b79f86cc
def AvailableChain.FGSA.Run.FAdvance b3f22bf2eab21210
def AvailableChain.FGSA.Run.sourceCandidates 6b4c633fa496f6d1
def AvailableChain.FGSA.Run.jointSource 56702dcb432d56da
def AvailableChain.FGSA.Run.proposerHead dabed0e96db90353
def AvailableChain.FGSA.Run.outputS 55f476301c4168ec
theorem AvailableChain.FGSA.Run.frameR_def 67c32f187e138bb2
theorem AvailableChain.FGSA.Run.jointSource_def 357a6db471f593ba
theorem AvailableChain.FGSA.Run.sourceCandidates_def 0350c826a0ad8445
theorem AvailableChain.FGSA.Run.domainR_def 13cee2a0164c4e68
theorem AvailableChain.FGSA.Run.treeT_def dc333386265d3b0c
theorem AvailableChain.FGSA.Run.proposerHead_def 89bf32c899866b7b
theorem AvailableChain.FGSA.Run.FAdvance_def 891b0382df50801a
def AvailableChain.FGSA.Run.R_at 9abda0a32dfad810
def AvailableChain.FGSA.Run.D_at db2e5a5a61e791b0
def AvailableChain.FGSA.Run.FAdvanceAt 803cbc4e81886c66
def AvailableChain.FGSA.Run.candidatesAt 5db1db3dabf83d26
def AvailableChain.FGSA.Run.proposalHeadAt 97b90a3e90dcdcd0
def AvailableChain.FGSA.Run.actionHead 1e5d78f0ef2affa5
def AvailableChain.FGSA.Run.actionTriple 381abe53e34c5585
def AvailableChain.FGSA.Run.namedEntry a50c73e0c7ee36db
def AvailableChain.FGSA.Run.EntryBelow 8b562d8188ed8ea7
def AvailableChain.FGSA.Run.RowSigner b0a9f3c5f4bcfb22
def AvailableChain.FGSA.Run.HonestRowAt 0526d66c654e30b0
def AvailableChain.FGSA.Run.HonestRowBefore c7d2e7d7e202d0dd
theorem AvailableChain.FGSA.Run.HonestRowBefore_def 0583bb4ae7fa93c1
def AvailableChain.FGSA.Run.RowComplete dd953a30907fd776
def AvailableChain.FGSA.Run.HonestCarrier a614d70314378196
def AvailableChain.FGSA.Run.HeldAt 30949eb0b46f3cfa
def AvailableChain.FGSA.Run.BlockInRunBefore 9b99ebb0bb73ebc4
theorem AvailableChain.FGSA.Run.RowSigner_def 28196811d0074c21
theorem AvailableChain.FGSA.Run.HonestRowAt_def 7fe855e5a80f7b4f
def AvailableChain.FGSA.Run.rowHeld 1e060eb840e6be0c
def AvailableChain.FGSA.Run.proposalStateAt 1d9ede7ad8f17206
def AvailableChain.FGSA.Run.heldAtProposal 8031e599465df2e6
def AvailableChain.FGSA.Run.onParentChain 265908a8e51f5949
def AvailableChain.FGSA.Run.HeldBefore 34bff5c89af5444d
def AvailableChain.FGSA.Run.ValidForParent b04f0fa58e525756
theorem AvailableChain.FGSA.Run.ValidForParent_def 51f424faa79e0659
def AvailableChain.FGSA.Run.HeightMatch e0630d278024b165
theorem AvailableChain.FGSA.Run.HeightMatch_def 88ea1ee05f8df76a
def AvailableChain.FGSA.Run.headAtLabel e34b7e914b2d4bb5
```

### `AvailableChainFGSAClaims.Statements.ComposeStmt`

```text
def AvailableChain.FGSA.Run.windowIdx 0f72b3544a6fe081
structure AvailableChain.FGSA.Run.TimingContract b331f96fe1084042
ctor AvailableChain.FGSA.Run.TimingContract.mk bb558945a1da6761
field AvailableChain.FGSA.Run.TimingContract.rowLag 9323af04fbe840ea
field AvailableChain.FGSA.Run.TimingContract.certLag b74ceb09dd0e3147
field AvailableChain.FGSA.Run.TimingContract.label 5a49aeb936d52093
field AvailableChain.FGSA.Run.TimingContract.atomic 880a04acaa2519db
field AvailableChain.FGSA.Run.TimingContract.tickFG 4ef167b8667e8139
structure AvailableChain.FGSA.Run.FGFoundation 2807e127961cde56
ctor AvailableChain.FGSA.Run.FGFoundation.mk e579b24ec8f9db7e
field AvailableChain.FGSA.Run.FGFoundation.store 11c9e6065d5eab87
field AvailableChain.FGSA.Run.FGFoundation.cumul 7ada7fa655e442d5
field AvailableChain.FGSA.Run.FGFoundation.mono b44917e46132a46d
field AvailableChain.FGSA.Run.FGFoundation.frame eddca3e41ff6925c
field AvailableChain.FGSA.Run.FGFoundation.geo f0a9565a62fd19ff
field AvailableChain.FGSA.Run.FGFoundation.strat 87e6190d41fcff24
field AvailableChain.FGSA.Run.FGFoundation.reconcile 74c229cf6bc7ea49
def AvailableChain.FGSA.Run.TStart a57ca445660dedd4
def AvailableChain.FGSA.Run.FullVoteService 360bb6612ed95395
def AvailableChain.FGSA.Run.TVote b4b817eec6babf6a
def AvailableChain.FGSA.Run.WalkBatch 488c9e5882e3685b
def AvailableChain.FGSA.Run.TWalk cae706cb2defee54
structure AvailableChain.FGSA.Run.CoreServices 604b176a266b3f77
ctor AvailableChain.FGSA.Run.CoreServices.mk 390c4d9ec591eb7a
field AvailableChain.FGSA.Run.CoreServices.start e2cf0a8685673373
field AvailableChain.FGSA.Run.CoreServices.vote 46b9a9bd0fba5627
field AvailableChain.FGSA.Run.CoreServices.walk 2329cce6f06aba57
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
def AvailableChain.FGSA.Run.B'_reset 82fedc6cb744ef8f
def AvailableChain.FGSA.Run.ResetArrivalStatement 2d7b5b82f52f7987
theorem AvailableChain.FGSA.Run.ResetArrivalStatement_def 4f5298dcf48da067
def AvailableChain.FGSA.Run.ResetArrivalFullStatement 8603732bbe3c4f4e
theorem AvailableChain.FGSA.Run.ResetArrivalFullStatement_def 40037ec752bdb980
def AvailableChain.FGSA.Run.KernelConclusion 2ba6582e67030969
structure AvailableChain.FGSA.Run.KernelPt 9235f1fbc5c48477
ctor AvailableChain.FGSA.Run.KernelPt.mk 32c96b623cc6f691
field AvailableChain.FGSA.Run.KernelPt.w 6cbd0d7075070f20
field AvailableChain.FGSA.Run.KernelPt.r e581c6d88b7635d7
structure AvailableChain.FGSA.Run.KernelPrem 8c1017b133af4a86
ctor AvailableChain.FGSA.Run.KernelPrem.mk ed1360282511a506
field AvailableChain.FGSA.Run.KernelPrem.set cfdf898392548534
field AvailableChain.FGSA.Run.KernelPrem.window eea586caa597794e
field AvailableChain.FGSA.Run.KernelPrem.start 36798fda2cb07a53
field AvailableChain.FGSA.Run.KernelPrem.hhor 4778f1101e1a740c
field AvailableChain.FGSA.Run.KernelPrem.input d60682ea0c85181a
field AvailableChain.FGSA.Run.KernelPrem.services 84a62aa513f2e458
def AvailableChain.FGSA.Run.KernelFromContract 5890e327e3b0adc6
def AvailableChain.FGSA.Run.KernelACSide 2147bff851e7d16f
def AvailableChain.FGSA.Run.kernelStart 1480ca310e6e4411
structure AvailableChain.FGSA.Run.HealTContract 37b924cd2a6ac21a
ctor AvailableChain.FGSA.Run.HealTContract.mk 0e208ef762ea95f5
field AvailableChain.FGSA.Run.HealTContract.del 38b4ce7b976e52fc
field AvailableChain.FGSA.Run.HealTContract.delReset c16a8aed0f0c2d2d
field AvailableChain.FGSA.Run.HealTContract.perm be804ee63590e0b1
field AvailableChain.FGSA.Run.HealTContract.repair 882b10359602726b
field AvailableChain.FGSA.Run.HealTContract.common df0a9d7f385666ff
field AvailableChain.FGSA.Run.HealTContract.frontier 32e7199bfdbe27ea
field AvailableChain.FGSA.Run.HealTContract.geom 442af9b5a4aa1e2e
def AvailableChain.FGSA.Run.frontierAtIdx 84fca8cd5768fef6
def AvailableChain.FGSA.Run.TopEvidence 15f437e08547fcdb
def AvailableChain.FGSA.Run.ContestEvidence d9d1bd34aa6f659e
def AvailableChain.FGSA.Run.EffectiveEvent 6979a18bc2f7e8d9
def AvailableChain.FGSA.Run.AttemptPhaseAt e20346eea9d58821
def AvailableChain.FGSA.Run.ServedFrontier e7f01f4249b223dd
def AvailableChain.FGSA.Run.AttemptValid 139288d479bd4b14
def AvailableChain.FGSA.Run.attemptBudget 3b25a39342572741
def AvailableChain.FGSA.Run.AttemptEndsBy f9bad78a5664899e
def AvailableChain.FGSA.Run.SettledPhaseFrame 6539bf4b2036683f
theorem AvailableChain.FGSA.Run.SettledPhaseFrame_def 2d0ae95e984384ae
def AvailableChain.FGSA.Run.RPhase 151cc2bf6cbb35d8
theorem AvailableChain.FGSA.Run.RPhase_def 1a7c83b5a69c9150
structure AvailableChain.FGSA.Run.HealRContract c1b6195be36a2995
ctor AvailableChain.FGSA.Run.HealRContract.mk 11346aa0bc70b801
field AvailableChain.FGSA.Run.HealRContract.xing af7cb4aa4ab0dcaf
field AvailableChain.FGSA.Run.HealRContract.cap bb40df0a89578423
field AvailableChain.FGSA.Run.HealRContract.phase d980649dcec0f227
field AvailableChain.FGSA.Run.HealRContract.excl a5b04a8f7060cd91
field AvailableChain.FGSA.Run.HealRContract.keep aef77138d563897e
field AvailableChain.FGSA.Run.HealRContract.fprov 99d7c7591b31eb6b
def AvailableChain.FGSA.Run.ProgressAttemptStatement b852fa2f96423964
theorem AvailableChain.FGSA.Run.ProgressAttemptStatement_def eea5abcc8cbdf26c
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
def AvailableChain.FGSA.Run.RowNames 39fe22fa04b59fd6
def AvailableChain.FGSA.Run.SlotChain 026b8cab17d0c00f
def AvailableChain.FGSA.Run.EntryAt 88ea77cc4662bb24
def AvailableChain.FGSA.Run.JustifiedCross 805d0c291ae7ac7c
def AvailableChain.FGSA.Run.MixedCross 355c7cffb4af5d69
def AvailableChain.FGSA.Run.NoMixedOnPath 7316627a45eb0fcd
def AvailableChain.FGSA.Run.SeatCovers fe64e62ef752d2b2
def AvailableChain.FGSA.Run.CoveredByChild f79ab24c6edc5e21
def AvailableChain.FGSA.Run.foldTrichotomy eb92ad4b46bff303
def AvailableChain.FGSA.Run.StoredProgressConsume 329f0e2a95b4832d
def AvailableChain.FGSA.Run.NoMixedMaturity af5e67c0045546d9
def AvailableChain.FGSA.Run.NamesEntry affe4f8475120b69
def AvailableChain.FGSA.Run.rowHeight 8e2499ef46ddafdd
def AvailableChain.FGSA.Run.eventTime 4bdaaa69edcc1980
def AvailableChain.FGSA.Run.honestSeats 88708d0d333ad751
def AvailableChain.FGSA.Run.ChainRowsBefore b12e08b80e55bb9a
structure AvailableChain.FGSA.Run.PreBatchPrem 2980250b48c219dd
ctor AvailableChain.FGSA.Run.PreBatchPrem.mk 228c46b895c661dc
field AvailableChain.FGSA.Run.PreBatchPrem.base ad8f03ba4cdcbe60
field AvailableChain.FGSA.Run.PreBatchPrem.faultQ 52c91e16581727fb
field AvailableChain.FGSA.Run.PreBatchPrem.entry 5cf87c11e43ce21c
field AvailableChain.FGSA.Run.PreBatchPrem.path 07647ecb8cac77c9
field AvailableChain.FGSA.Run.PreBatchPrem.cut 9b3c7b050fe415f7
field AvailableChain.FGSA.Run.PreBatchPrem.early 9dc22514a4a48cbc
field AvailableChain.FGSA.Run.PreBatchPrem.rows b29ac624c7603eda
field AvailableChain.FGSA.Run.PreBatchPrem.noRow 9237c93cd1d26c75
def AvailableChain.FGSA.Run.NoMixedPreBatchParent 5c6fba48ca40ff74
structure AvailableChain.FGSA.Run.BatchPrem 658810eafa2a3ff5
ctor AvailableChain.FGSA.Run.BatchPrem.mk f838ca37e56dd0cc
field AvailableChain.FGSA.Run.BatchPrem.base fb3275b4e069d90b
field AvailableChain.FGSA.Run.BatchPrem.faultQ 868bbe220607c149
field AvailableChain.FGSA.Run.BatchPrem.deltaF 31d013d6008b6903
field AvailableChain.FGSA.Run.BatchPrem.rowsReceipt b911be2e92c22cbb
field AvailableChain.FGSA.Run.BatchPrem.horizon 2f747e65be8045ca
field AvailableChain.FGSA.Run.BatchPrem.carrier 0de63626c844fb94
field AvailableChain.FGSA.Run.BatchPrem.after a58803a9adc17c02
field AvailableChain.FGSA.Run.BatchPrem.valid a3e1de9e83a6dc64
field AvailableChain.FGSA.Run.BatchPrem.entry 542ee0f2decaf2b5
field AvailableChain.FGSA.Run.BatchPrem.path 8713b3d07c5e2242
field AvailableChain.FGSA.Run.BatchPrem.above 3b77f5b5db96c4b1
def AvailableChain.FGSA.Run.BatchCoverage 07c8380e742f6a8f
def AvailableChain.FGSA.Run.FirstCross adbde28ac8b11fa1
def AvailableChain.FGSA.Run.ProposalWalk cd310f07a398e41f
```

### `AvailableChainFGSAClaims.Statements.Healed`

```text
def AvailableChain.FGSA.Run.healStart 929394764619aab9
def AvailableChain.FGSA.Run.HealSuffix 44a0e030137e944d
def AvailableChain.FGSA.Run.Healed 4b82ed168ffcba4f
def AvailableChain.FGSA.Run.H2A af3de7a77c83645e
def AvailableChain.FGSA.Run.H2Prime 73c7a5c2d40b45a5
def AvailableChain.FGSA.Run.H3 a0d2eace79ef6a56
def AvailableChain.FGSA.Run.H4 8e7a6ece8e9deefd
def AvailableChain.FGSA.Run.H5RawTransfer 03ffa9642bfbfa73
def AvailableChain.FGSA.Run.H6GateService 620bda85cc711ba3
structure AvailableChain.FGSA.Run.HealT 256f22e894b95097
ctor AvailableChain.FGSA.Run.HealT.mk b7c92b0dbd93ce0b
field AvailableChain.FGSA.Run.HealT.h1 0285bf74a32a0977
field AvailableChain.FGSA.Run.HealT.h2 b3c9a28799427bd6
field AvailableChain.FGSA.Run.HealT.rows 2f7651601142be1a
structure AvailableChain.FGSA.Run.HealAC 187c3f7047f4dc05
ctor AvailableChain.FGSA.Run.HealAC.mk 8b2f59b5d9cae68e
field AvailableChain.FGSA.Run.HealAC.h2A 815518ecb86b0a2a
field AvailableChain.FGSA.Run.HealAC.h2' c9350e94ca3e6883
field AvailableChain.FGSA.Run.HealAC.h3 877ba502c35d478a
field AvailableChain.FGSA.Run.HealAC.h4 450c5ce4360bc73b
field AvailableChain.FGSA.Run.HealAC.h5 dfd1a2183a094d8d
field AvailableChain.FGSA.Run.HealAC.h6 909a6f707d67684c
structure AvailableChain.FGSA.Run.HealingInput 1b8b192f338f2433
ctor AvailableChain.FGSA.Run.HealingInput.mk 19a27d7cd0e8a01f
field AvailableChain.FGSA.Run.HealingInput.healed 4e5b7f1eea5bbb7c
field AvailableChain.FGSA.Run.HealingInput.wit e072f4b5e2050815
field AvailableChain.FGSA.Run.HealingInput.t ba79572e339180c0
field AvailableChain.FGSA.Run.HealingInput.ac cf37e0d311147ed3
def AvailableChain.FGSA.Run.HTimeStatement 90da2ffdcf25c253
theorem AvailableChain.FGSA.Run.HTimeStatement_def 145dc5a4ea51ef05
def AvailableChain.FGSA.Run.HTimeBestStatement d46a31b5c6f67022
theorem AvailableChain.FGSA.Run.HTimeBestStatement_def 1b105285965af5e5
def AvailableChain.FGSA.Run.HTimeSearchStatement b5f4ecf4c8ce2eb8
theorem AvailableChain.FGSA.Run.HTimeSearchStatement_def 311c5e5d81cd8cf8
```

### `AvailableChainFGSAClaims.Statements.Packages.Finality`

```text
def AvailableChain.FGSA.Run.finalityWindow 9aa7616d35b182b1
structure AvailableChain.FGSA.Run.FirstFinalityPrem b3004179207515d7
ctor AvailableChain.FGSA.Run.FirstFinalityPrem.mk e8ffa80a2386ca36
field AvailableChain.FGSA.Run.FirstFinalityPrem.set b1950aedd8ed27a6
field AvailableChain.FGSA.Run.FirstFinalityPrem.hhor d9a911710c7e706e
structure AvailableChain.FGSA.Run.FinalityLivenessPrem 9d831a82ac057c1c
ctor AvailableChain.FGSA.Run.FinalityLivenessPrem.mk be0d4c4da0331ac8
field AvailableChain.FGSA.Run.FinalityLivenessPrem.set b2a3115a76425609
field AvailableChain.FGSA.Run.FinalityLivenessPrem.late 68f9aad03b868489
field AvailableChain.FGSA.Run.FinalityLivenessPrem.hhor 13e642fd9c143756
structure AvailableChain.FGSA.Run.ProposalFinalPrem c06f4168e258dfdc
ctor AvailableChain.FGSA.Run.ProposalFinalPrem.mk 5767a5409e26acc9
field AvailableChain.FGSA.Run.ProposalFinalPrem.set ca1da48af2606256
field AvailableChain.FGSA.Run.ProposalFinalPrem.prop a1701a52ca14f0a1
field AvailableChain.FGSA.Run.ProposalFinalPrem.late bade16921a60b2b3
field AvailableChain.FGSA.Run.ProposalFinalPrem.hhor 2a1741997bf64e6b
structure AvailableChain.FGSA.Run.AboveFrontierPrem d22dcaf84aa86ed5
ctor AvailableChain.FGSA.Run.AboveFrontierPrem.mk 1521f65141177d9d
field AvailableChain.FGSA.Run.AboveFrontierPrem.set 0ee40e422ecb02af
field AvailableChain.FGSA.Run.AboveFrontierPrem.late ce0303bed7be8aba
field AvailableChain.FGSA.Run.AboveFrontierPrem.hhor c2fbd57b648f0b63
structure AvailableChain.FGSA.Run.QualifiedFinalityPrem 062c7e5f5481f20e
ctor AvailableChain.FGSA.Run.QualifiedFinalityPrem.mk 7480fc672ef566ce
field AvailableChain.FGSA.Run.QualifiedFinalityPrem.set bdf2a7795b79cf7a
field AvailableChain.FGSA.Run.QualifiedFinalityPrem.hhor 4b9d59283f71d420
structure AvailableChain.FGSA.Run.SkipFinalityPrem dfa3ff98d8249f38
ctor AvailableChain.FGSA.Run.SkipFinalityPrem.mk 29422f358e5df6b2
field AvailableChain.FGSA.Run.SkipFinalityPrem.set 7a138dfa98124bdc
field AvailableChain.FGSA.Run.SkipFinalityPrem.hhor e8d09ab2c58bf3a0
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
structure AvailableChain.FGSA.Run.HealingPrem 33e2166838ed8c99
ctor AvailableChain.FGSA.Run.HealingPrem.mk 2f17782ba983cec7
field AvailableChain.FGSA.Run.HealingPrem.set 7dcc58b37f506ccd
structure AvailableChain.FGSA.Run.HealingWitnessPrem 49ede11bc8dc5cd1
field AvailableChain.FGSA.Run.HealingWitnessPrem.toHealingPrem df33ff929fdf382a
ctor AvailableChain.FGSA.Run.HealingWitnessPrem.mk 3c21b8e8fca71d39
field AvailableChain.FGSA.Run.HealingWitnessPrem.h0 6572d4d20c6d7bb2
structure AvailableChain.FGSA.Run.HealingTimePrem 7673d13ae746ac2e
field AvailableChain.FGSA.Run.HealingTimePrem.toHealingPrem 45113eaa32c880e6
ctor AvailableChain.FGSA.Run.HealingTimePrem.mk 41b1b5e651afe6d9
field AvailableChain.FGSA.Run.HealingTimePrem.hhor b8049dbf39dd0f29
structure AvailableChain.FGSA.Run.ResetArrivalPrem 8c7ebf4162277f81
field AvailableChain.FGSA.Run.ResetArrivalPrem.toHealingPrem 4f32964f41efb6b3
ctor AvailableChain.FGSA.Run.ResetArrivalPrem.mk bb6b80d6415cc240
field AvailableChain.FGSA.Run.ResetArrivalPrem.hhor d1c33afc2617990e
structure AvailableChain.FGSA.Run.ResetArrivalFullPrem a3dad0abcaa5df6b
field AvailableChain.FGSA.Run.ResetArrivalFullPrem.toHealingPrem a0257abdcd9a6928
ctor AvailableChain.FGSA.Run.ResetArrivalFullPrem.mk 69d7903211fca190
field AvailableChain.FGSA.Run.ResetArrivalFullPrem.hhor 3c40a559dd51b1c0
structure AvailableChain.FGSA.Run.KernelJoinedPrem 0df2492259503554
ctor AvailableChain.FGSA.Run.KernelJoinedPrem.mk 4c9c8e7553b816de
field AvailableChain.FGSA.Run.KernelJoinedPrem.set 91b3cd39e5fbb2a0
field AvailableChain.FGSA.Run.KernelJoinedPrem.window 1afef0b3f0b9575e
field AvailableChain.FGSA.Run.KernelJoinedPrem.start d1946994ef88b98d
field AvailableChain.FGSA.Run.KernelJoinedPrem.hhor b807fd226b2b9ea8
structure AvailableChain.FGSA.Run.HealingAttemptPrem ee7555ba97b332fe
field AvailableChain.FGSA.Run.HealingAttemptPrem.toHealingPrem 35872f07ec1baf6c
ctor AvailableChain.FGSA.Run.HealingAttemptPrem.mk 52d987359ef98abd
field AvailableChain.FGSA.Run.HealingAttemptPrem.valid 9259ba5f738b6209
structure AvailableChain.FGSA.Run.HealingInputPrem 6a98bcc02c274f9f
field AvailableChain.FGSA.Run.HealingInputPrem.toHealingWitnessPrem 1655bf9240f14648
ctor AvailableChain.FGSA.Run.HealingInputPrem.mk 94567c23305e5269
field AvailableChain.FGSA.Run.HealingInputPrem.hhor 8cbcbb3693e8b8f1
structure AvailableChain.FGSA.Run.RenewedPromotionPrem 9b74b2a4cceb0bf6
field AvailableChain.FGSA.Run.RenewedPromotionPrem.toHealingPrem 9b3caf4bac48e152
ctor AvailableChain.FGSA.Run.RenewedPromotionPrem.mk b2a38f89fd2ae3c4
field AvailableChain.FGSA.Run.RenewedPromotionPrem.hhor bb8dbe978da62c8c
```

### `AvailableChainFGSAClaims.Statements.Packages.Outage`

```text
structure AvailableChain.FGSA.Run.OutagePrem 4adad84970dc54cd
ctor AvailableChain.FGSA.Run.OutagePrem.mk 491ab8429be3f1b1
field AvailableChain.FGSA.Run.OutagePrem.set b0bf7b29f48620a6
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
structure AvailableChain.FGSA.Run.BasePrem bc4960f75e7d868f
ctor AvailableChain.FGSA.Run.BasePrem.mk eba6ef2bf73d81e5
field AvailableChain.FGSA.Run.BasePrem.set e3dd43184e01b229
structure AvailableChain.FGSA.Run.SameLabelPrem 650c2985ea84b943
ctor AvailableChain.FGSA.Run.SameLabelPrem.mk d991fd7b4c2d67c5
field AvailableChain.FGSA.Run.SameLabelPrem.set e819381f4791a716
field AvailableChain.FGSA.Run.SameLabelPrem.sync 230516a7aac1c0d1
structure AvailableChain.FGSA.Run.SourceDisciplinePrem 333d5cc690cc02d8
ctor AvailableChain.FGSA.Run.SourceDisciplinePrem.mk 07c9d73a4dcd0696
field AvailableChain.FGSA.Run.SourceDisciplinePrem.set 470aaf5c83a839cf
field AvailableChain.FGSA.Run.SourceDisciplinePrem.quorum 96e95761bcabad06
structure AvailableChain.FGSA.Run.FinalizedSafetyPrem ce0c9f6b2ba4c0ee
ctor AvailableChain.FGSA.Run.FinalizedSafetyPrem.mk d7a3792ef873d8a4
field AvailableChain.FGSA.Run.FinalizedSafetyPrem.set 0ab3321932adc4e5
field AvailableChain.FGSA.Run.FinalizedSafetyPrem.fault 3a90ddf34b2b379d
structure AvailableChain.FGSA.Run.CleanPrem a4560fb8ccd3585a
ctor AvailableChain.FGSA.Run.CleanPrem.mk de53a26e2cdc9fe9
field AvailableChain.FGSA.Run.CleanPrem.set ffacde22724d01f0
structure AvailableChain.FGSA.Run.CleanPrefixPrem 8f90df4d08503b2f
ctor AvailableChain.FGSA.Run.CleanPrefixPrem.mk 87fc0cba406b9175
field AvailableChain.FGSA.Run.CleanPrefixPrem.set 50f29a73e25f342b
structure AvailableChain.FGSA.Run.CleanCutPrem 91ac8f4aceb475c2
ctor AvailableChain.FGSA.Run.CleanCutPrem.mk 80e05709a95196e6
field AvailableChain.FGSA.Run.CleanCutPrem.set 881afa3e1e84d9cc
structure AvailableChain.FGSA.Run.ReleasePrem 8a342c5756d0b9b7
ctor AvailableChain.FGSA.Run.ReleasePrem.mk 0b6d04cf47ee8902
field AvailableChain.FGSA.Run.ReleasePrem.set 62937de1fb2f20ce
field AvailableChain.FGSA.Run.ReleasePrem.lt 09e5c4c8fec5e022
```

### `AvailableChainFGSAClaims.Statements.Phases`

```text
def AvailableChain.FGSA.Run.finHeight 45ca642905486866
structure AvailableChain.FGSA.Run.FreshPrem fbc61de9d89d1988
ctor AvailableChain.FGSA.Run.FreshPrem.mk 872a44dc6faf27cb
field AvailableChain.FGSA.Run.FreshPrem.base 996bd01ff70dfc45
field AvailableChain.FGSA.Run.FreshPrem.faultQ 872c0d0185abaaaf
field AvailableChain.FGSA.Run.FreshPrem.cut eb2f2164722a1577
field AvailableChain.FGSA.Run.FreshPrem.early fc0b60df917e471f
field AvailableChain.FGSA.Run.FreshPrem.rows 4aea4db49be74ce5
field AvailableChain.FGSA.Run.FreshPrem.noNextRow d769ca32ca0a929f
field AvailableChain.FGSA.Run.FreshPrem.noFinRow 0ea056debe8d77ec
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
def AvailableChain.FGSA.Run.storeAt a4f9f8f6d356eaec
def AvailableChain.FGSA.Run.S_at 30260ba5ef871c4c
def AvailableChain.FGSA.Run.F_at 307ce7c7434e94ea
def AvailableChain.FGSA.Run.J_at a4111f3bfd622c27
def AvailableChain.FGSA.Run.gateIn 54e63ade93e75d1c
theorem AvailableChain.FGSA.Run.gateIn_def 801a051e17b3e972
def AvailableChain.FGSA.Run.gateResult edcdb8f9f309184f
theorem AvailableChain.FGSA.Run.gateResult_def 89b410154f2874eb
def AvailableChain.FGSA.Run.isGateTime e8fa74ed0e358d9a
theorem AvailableChain.FGSA.Run.isGateTime_def 339eae8b30dc753b
def AvailableChain.FGSA.Run.IsGateTick 97be87a09e36ac7e
def AvailableChain.FGSA.Run.gateResultAt f4506c6b00507c21
def AvailableChain.FGSA.Run.gatePassedAt b0bb18e32f79f2bc
def AvailableChain.FGSA.Run.fastAt 4c2e66a095fa70c0
def AvailableChain.FGSA.Run.headAtIdx cd7e52118ca39872
def AvailableChain.FGSA.Run.vHead 208985542246e1a9
theorem AvailableChain.FGSA.Run.vHead_def 04316b0eab5d2440
def AvailableChain.FGSA.Run.actionSourceFG aa96187915a8fce5
theorem AvailableChain.FGSA.Run.actionSourceFG_def c1cdcafe36188a72
def AvailableChain.FGSA.Run.actionSource 762f45046c676a2c
def AvailableChain.FGSA.Run.labelBoundAt dc03cc6c88fb9522
def AvailableChain.FGSA.Run.DeliveredAt b07d2f3f29cd10d5
def AvailableChain.FGSA.Run.HandlesRowAt 4e88c9336f0e4452
def AvailableChain.FGSA.Run.AcceptsFinalBefore c2807bf8e9bb2b25
def AvailableChain.FGSA.Run.cleanResults ce52ce5247e6e1cf
def AvailableChain.FGSA.Run.BelowLabel 939445e3da702e80
```

### `AvailableChainFGSAClaims.Statements.Recurrence`

```text
```

### `AvailableChainFGSAClaims.Statements.Regimes`

```text
structure AvailableChain.FGSA.Run.Base₂ fc2b95558ba31dd6
ctor AvailableChain.FGSA.Run.Base₂.mk ee2d73b62d754f1a
field AvailableChain.FGSA.Run.Base₂.valid 598008f7b1c54056
field AvailableChain.FGSA.Run.Base₂.linked c8944fb6eedba71c
field AvailableChain.FGSA.Run.Base₂.cstar 8e479379c66eecbe
field AvailableChain.FGSA.Run.Base₂.noRestart 0d7fa1e86e9341d8
field AvailableChain.FGSA.Run.Base₂.delta 071f50f7c67b6692
structure AvailableChain.FGSA.Run.HealthyPrefix₂ 6fd6ef349cf352b9
ctor AvailableChain.FGSA.Run.HealthyPrefix₂.mk a82619224570c813
field AvailableChain.FGSA.Run.HealthyPrefix₂.base 95b6bfc4842919eb
field AvailableChain.FGSA.Run.HealthyPrefix₂.cut 6a4d66d650f18c77
field AvailableChain.FGSA.Run.HealthyPrefix₂.healthy b13673495f3f26d6
field AvailableChain.FGSA.Run.HealthyPrefix₂.deltaF 13f1b9c7a14028e6
field AvailableChain.FGSA.Run.HealthyPrefix₂.partBefore 68622197efc2342b
structure AvailableChain.FGSA.Run.CleanPrefix₂ 2e9c65b9d1923b68
field AvailableChain.FGSA.Run.CleanPrefix₂.toHealthyPrefix₂ 33d1fdec03938906
ctor AvailableChain.FGSA.Run.CleanPrefix₂.mk e60bb977e59916fa
field AvailableChain.FGSA.Run.CleanPrefix₂.partAt b56a8ba592f0e310
def AvailableChain.FGSA.Run.CleanCut₂ 08621686fe8cffb1
structure AvailableChain.FGSA.Run.Clean₂ 23e9eefa917812c3
ctor AvailableChain.FGSA.Run.Clean₂.mk e0c09c72ccd591e9
field AvailableChain.FGSA.Run.Clean₂.pre ef15dda60e2fa559
field AvailableChain.FGSA.Run.Clean₂.gst ced0444fe7640f19
structure AvailableChain.FGSA.Run.Recovery₂ 2392489c3ab4c3f6
ctor AvailableChain.FGSA.Run.Recovery₂.mk 6576489ce3bda740
field AvailableChain.FGSA.Run.Recovery₂.sync 411119bf20d54ee3
field AvailableChain.FGSA.Run.Recovery₂.deltaF 36534cdb83ca974f
field AvailableChain.FGSA.Run.Recovery₂.gap 8173b1453014ea41
field AvailableChain.FGSA.Run.Recovery₂.base 1be222d63b9defac
field AvailableChain.FGSA.Run.Recovery₂.fault 0e0f9cec29e4857c
field AvailableChain.FGSA.Run.Recovery₂.awake 338563427e12d161
field AvailableChain.FGSA.Run.Recovery₂.gapPos 8a3686de734552c5
def AvailableChain.FGSA.Run.BaseSet 029ed410fb299109
def AvailableChain.FGSA.Run.CleanSet 31d6c3525878fa9e
def AvailableChain.FGSA.Run.CleanCutSet 97d8d9b3804e8d85
def AvailableChain.FGSA.Run.CleanPrefixSet 481fb2ee37592820
def AvailableChain.FGSA.Run.HealingSet 470ed854792b1a7b
structure AvailableChain.FGSA.Run.FinalitySet 759abc22e682d2da
ctor AvailableChain.FGSA.Run.FinalitySet.mk 3a7f20e9e5221de0
field AvailableChain.FGSA.Run.FinalitySet.core 1e28d3a0a7d3f84f
field AvailableChain.FGSA.Run.FinalitySet.recur 28b117544cd3fee1
structure AvailableChain.FGSA.Run.Outage₂ c4ae1407491eac25
ctor AvailableChain.FGSA.Run.Outage₂.mk 5d8a01bada34ecdf
field AvailableChain.FGSA.Run.Outage₂.pre a3f785620cb1ea12
field AvailableChain.FGSA.Run.Outage₂.sleepy 66dc51f577fa7eaa
field AvailableChain.FGSA.Run.Outage₂.order 6ace19d083624b3c
field AvailableChain.FGSA.Run.Outage₂.lag 5b575303e7bcd8a8
field AvailableChain.FGSA.Run.Outage₂.budget 0d07791c8d36919e
field AvailableChain.FGSA.Run.Outage₂.fastPart 017dae319280d333
def AvailableChain.FGSA.Run.OutageSet 028d9b82c1f40f7b
```

### `AvailableChainFGSAClaims.Statements.Windows`

```text
def AvailableChain.FGSA.Run.WinSpec 56c3ae6aa5615737
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
def AvailableChain.FGSA.Run.cleanWinAt 1fcf90dff1946f42
def AvailableChain.FGSA.Run.cleanWin 706b69ecccf3ef9a
def AvailableChain.FGSA.Run.cleanPrefixWin 7cc7b4f75cd4a519
def AvailableChain.FGSA.Run.cleanLabelWin ac84c3c7abb02924
def AvailableChain.FGSA.Run.gapWin 6419446b6ecfed3e
def AvailableChain.FGSA.Run.formWin dd562b72634ba01d
def AvailableChain.FGSA.Run.formWinAt 1a13839e29ab9a3f
def AvailableChain.FGSA.Run.kernelWin b5fbf2f6dc6a05c0
def AvailableChain.FGSA.Run.trigWin 789257cd395eee53
def AvailableChain.FGSA.Run.outWin 2309fa20efcaba26
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
def AvailableChain.FGSA.Run.tstar baaa14187df71f6a
def AvailableChain.FGSA.Run.oldRowHeights e9155b1b9b7c373a
def AvailableChain.FGSA.Run.muOf a8339f81e45a8803
def AvailableChain.FGSA.Run.high 137ca53654e215bf
def AvailableChain.FGSA.Run.honestFrontier 0bc127bbc50e716c
def AvailableChain.FGSA.Run.HeightRow e6a6bfa94581dccb
structure AvailableChain.FGSA.Run.H0Reset 27d41f736a377116
ctor AvailableChain.FGSA.Run.H0Reset.mk c9f036be8592a0c6
field AvailableChain.FGSA.Run.H0Reset.rG_after d6d7d78a0edfd745
field AvailableChain.FGSA.Run.H0Reset.rG_first b586dedf2d483e11
field AvailableChain.FGSA.Run.H0Reset.cut 794b7919e1445952
field AvailableChain.FGSA.Run.H0Reset.frontier ace696cf8c6ca4bd
field AvailableChain.FGSA.Run.H0Reset.rowCap c6202608e4831f7f
field AvailableChain.FGSA.Run.H0Reset.mu_le f36f38d4bcaf5d99
field AvailableChain.FGSA.Run.H0Reset.cut_lower be41420b9239cf07
field AvailableChain.FGSA.Run.H0Reset.cut_upper 6797c8172fc08324
field AvailableChain.FGSA.Run.H0Reset.reset_row 52a17269893a32a9
field AvailableChain.FGSA.Run.H0Reset.reset_first 65bd7155a7ff1495
field AvailableChain.FGSA.Run.H0Reset.label bbd3bdf13f8ae44e
field AvailableChain.FGSA.Run.H0Reset.fresh 31ce5afc30301063
field AvailableChain.FGSA.Run.H0Reset.synchronous 3bc516f4a8c74899
structure AvailableChain.FGSA.Run.H0 58b706e20fec3dc0
field AvailableChain.FGSA.Run.H0.toH0Reset 18a8c469ca88397a
ctor AvailableChain.FGSA.Run.H0.mk 0d22bb105a632041
field AvailableChain.FGSA.Run.H0.proposal_lower 72676e16bf4d193f
field AvailableChain.FGSA.Run.H0.proposal 224f0504557944e4
field AvailableChain.FGSA.Run.H0.proposal_first e34a49adc05c15e3
field AvailableChain.FGSA.Run.H0.after_gst 7d808348f94a039f
field AvailableChain.FGSA.Run.H0.source_prefix 2aa2bd3ba4c62db2
def AvailableChain.FGSA.Run.tstarOf 1bfa18c39c91bb89
```
