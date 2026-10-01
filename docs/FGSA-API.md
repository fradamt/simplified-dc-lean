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
def AvailableChain.FGSA.Run.fgsaInterface 592ec9e38803db69
def AvailableChain.FGSA.Run.fgsaOutputs 05ade1602887227f
def AvailableChain.FGSA.Run.finalizedOut eb13de3f9e21b2a8
```

### `AvailableChainFGSARun.Statements.ReceiptCoverage`

```text
structure AvailableChain.FGSA.Run.ReceiptCoveragePremises 659b12fe9de22825
ctor AvailableChain.FGSA.Run.ReceiptCoveragePremises.mk 96e7238be0fde851
field AvailableChain.FGSA.Run.ReceiptCoveragePremises.within 4485ca6aab7c531f
field AvailableChain.FGSA.Run.ReceiptCoveragePremises.slotWindow 3aee28382b5c7444
field AvailableChain.FGSA.Run.ReceiptCoveragePremises.compat 3101562d352f4a5a
field AvailableChain.FGSA.Run.ReceiptCoveragePremises.deadline 1e4eeb4f350adddd
def AvailableChain.FGSA.Run.ReceiptCoverageStatement 6d58fcadd2083b4c
theorem AvailableChain.FGSA.Run.ReceiptCoverageStatement_def e1989d3236c04221
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
def AvailableChain.FGSA.Run.CleanCutClaim 9e1eec99739a3a1b
def AvailableChain.FGSA.Run.CleanCutZeroClaim 0940c47e1f894b30
def AvailableChain.FGSA.Run.CleanHistoryClaim cfe398d819a36b82
def AvailableChain.FGSA.Run.CleanPrefixTruncationClaim c6399c706001ff4a
def AvailableChain.FGSA.Run.CleanSafetyClaim 5d5ad85522c45737
def AvailableChain.FGSA.Run.CleanCutPosClaim 6a5459bc5202bfa6
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
def AvailableChain.FGSA.Run.SourceDisciplineBaseAt 585e8b747e994190
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
```

### `AvailableChainFGSAClaims.Claims.Shared`

```text
def AvailableChain.FGSA.Run.SameLabelAt cb5cc9016b0fe621
def AvailableChain.FGSA.Run.SameLabelClaim 96139da4a21fa3f7
def AvailableChain.FGSA.Run.HeadReachesLoAt b7df7a59c61bd2cf
def AvailableChain.FGSA.Run.HeadReachesLoClaim e53147e3198cb830
def AvailableChain.FGSA.Run.ReleaseStoreAt 4821a3dc715fe93d
def AvailableChain.FGSA.Run.ReleaseStoreClaim 8686f70b1a563f39
def AvailableChain.FGSA.Run.ReleaseAt 15316b89685903f3
def AvailableChain.FGSA.Run.ReleaseClaim cbe0b3d5fba8ceca
```

### `AvailableChainFGSAClaims.FGSAClaims`

```text
structure AvailableChain.FGSA.Run.FGSASafetyClaims 213de0a1b6c01dcc
ctor AvailableChain.FGSA.Run.FGSASafetyClaims.mk dac0433db7f8fd80
field AvailableChain.FGSA.Run.FGSASafetyClaims.carrier 61c073a8151d6bdf
field AvailableChain.FGSA.Run.FGSASafetyClaims.chainCertificates db10fbe824dd444e
field AvailableChain.FGSA.Run.FGSASafetyClaims.store 133c5e896cba0093
field AvailableChain.FGSA.Run.FGSASafetyClaims.activeView 5a510f0401cd52f0
field AvailableChain.FGSA.Run.FGSASafetyClaims.leaseOrigins b526c20ce2aa7d89
field AvailableChain.FGSA.Run.FGSASafetyClaims.reconcile 5f9dcc9c2ae1c6bd
field AvailableChain.FGSA.Run.FGSASafetyClaims.outputNesting 0016ca0116df4c06
field AvailableChain.FGSA.Run.FGSASafetyClaims.frame b50cfbca0ac52a05
field AvailableChain.FGSA.Run.FGSASafetyClaims.clientSafety daf91f80f74db885
field AvailableChain.FGSA.Run.FGSASafetyClaims.clientSafetyBase 81ae85f2f3292630
field AvailableChain.FGSA.Run.FGSASafetyClaims.sourceDisciplineBase 06e5eeec9149cabc
field AvailableChain.FGSA.Run.FGSASafetyClaims.sourceDiscipline 6df5cc47e37c39a6
field AvailableChain.FGSA.Run.FGSASafetyClaims.sameLabel 895f8b6c68c0fd14
field AvailableChain.FGSA.Run.FGSASafetyClaims.releaseStore b1e1d07a35f0cd33
field AvailableChain.FGSA.Run.FGSASafetyClaims.release 5af8f09d6e5933f6
field AvailableChain.FGSA.Run.FGSASafetyClaims.headReachesLo abf463b664e7808e
field AvailableChain.FGSA.Run.FGSASafetyClaims.cleanCut 071b823e2281cc88
field AvailableChain.FGSA.Run.FGSASafetyClaims.cleanHistory 3ba349f1b05c581f
field AvailableChain.FGSA.Run.FGSASafetyClaims.cleanPrefixTruncation 3959dc567b9b520f
field AvailableChain.FGSA.Run.FGSASafetyClaims.cleanSafety 8ac92150d61310a5
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
def AvailableChain.FGSA.Run.TRowsSync 88d60f844a22e135
structure AvailableChain.FGSA.Run.TRows 8d28e71e8d5c3e54
ctor AvailableChain.FGSA.Run.TRows.mk 9dacb3bd5b6ad935
field AvailableChain.FGSA.Run.TRows.select 4f36b310343fb9f8
field AvailableChain.FGSA.Run.TRows.sync 5dc73a5e6c527d78
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
def AvailableChain.FGSA.Run.OpeningExtends db05cf9b61711cc8
def AvailableChain.FGSA.Run.OpeningEntry 609eb2448c473290
def AvailableChain.FGSA.Run.TCommon 44500106cdaa15e1
def AvailableChain.FGSA.Run.TFrontier 56de1d67d9bfa471
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
def AvailableChain.FGSA.Run.TVote f6f063ab7d26a516
def AvailableChain.FGSA.Run.WalkBatch 488c9e5882e3685b
def AvailableChain.FGSA.Run.TWalk cae706cb2defee54
structure AvailableChain.FGSA.Run.CoreServices 9318869a8d1d69e6
ctor AvailableChain.FGSA.Run.CoreServices.mk d3e11352b6300d23
field AvailableChain.FGSA.Run.CoreServices.start a7e489fcd2e94caa
field AvailableChain.FGSA.Run.CoreServices.vote e365a6276d5278ee
field AvailableChain.FGSA.Run.CoreServices.walk bb1ee07c06fad07e
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
def AvailableChain.FGSA.Run.ResetArrivalStatement 1c33eece58ad67ca
def AvailableChain.FGSA.Run.ResetArrivalFullStatement 9d17a622d6ebe3e3
def AvailableChain.FGSA.Run.KernelConclusion 2ba6582e67030969
structure AvailableChain.FGSA.Run.KernelPt 9235f1fbc5c48477
ctor AvailableChain.FGSA.Run.KernelPt.mk 32c96b623cc6f691
field AvailableChain.FGSA.Run.KernelPt.w 6cbd0d7075070f20
field AvailableChain.FGSA.Run.KernelPt.r e581c6d88b7635d7
structure AvailableChain.FGSA.Run.KernelPrem 3dcc24f1667d68d3
ctor AvailableChain.FGSA.Run.KernelPrem.mk b52af712ff361f0e
field AvailableChain.FGSA.Run.KernelPrem.set 50d315d7d04989d2
field AvailableChain.FGSA.Run.KernelPrem.window 3725ec26b40fa933
field AvailableChain.FGSA.Run.KernelPrem.start d79c03d19ee482ce
field AvailableChain.FGSA.Run.KernelPrem.hhor 5858baa7c8846a89
field AvailableChain.FGSA.Run.KernelPrem.input d873e801e8ef5827
field AvailableChain.FGSA.Run.KernelPrem.services b5d113d49bb08895
def AvailableChain.FGSA.Run.KernelFromContract 97bfb50da14a8713
def AvailableChain.FGSA.Run.KernelACSide 99509b516f6ed6c9
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
```

### `AvailableChainFGSAClaims.Statements.Counts`

```text
def AvailableChain.FGSA.Run.awakeHonestIn 54415ad59f9cd90a
def AvailableChain.FGSA.Run.HonestProposal ae9f4b671ef57b39
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
structure AvailableChain.FGSA.Run.HealT abf0db6740f9b0f4
ctor AvailableChain.FGSA.Run.HealT.mk b9fe3628c15f7d98
field AvailableChain.FGSA.Run.HealT.h1 550c0a5aeff6ce97
field AvailableChain.FGSA.Run.HealT.h2 130baaa6fe17cbdf
field AvailableChain.FGSA.Run.HealT.rows c0db5abff093bbca
structure AvailableChain.FGSA.Run.HealAC 187c3f7047f4dc05
ctor AvailableChain.FGSA.Run.HealAC.mk 8b2f59b5d9cae68e
field AvailableChain.FGSA.Run.HealAC.h2A 815518ecb86b0a2a
field AvailableChain.FGSA.Run.HealAC.h2' c9350e94ca3e6883
field AvailableChain.FGSA.Run.HealAC.h3 877ba502c35d478a
field AvailableChain.FGSA.Run.HealAC.h4 450c5ce4360bc73b
field AvailableChain.FGSA.Run.HealAC.h5 dfd1a2183a094d8d
field AvailableChain.FGSA.Run.HealAC.h6 909a6f707d67684c
structure AvailableChain.FGSA.Run.HealingInput 1b8b192f338f2433
ctor AvailableChain.FGSA.Run.HealingInput.mk 3d41e77ce292812d
field AvailableChain.FGSA.Run.HealingInput.healed 4e5b7f1eea5bbb7c
field AvailableChain.FGSA.Run.HealingInput.wit e072f4b5e2050815
field AvailableChain.FGSA.Run.HealingInput.t 85f43a6c88e273a7
field AvailableChain.FGSA.Run.HealingInput.ac cf37e0d311147ed3
def AvailableChain.FGSA.Run.HTimeStatement cec0828dfdca0f36
def AvailableChain.FGSA.Run.HTimeBestStatement 7a52a02748c9872f
def AvailableChain.FGSA.Run.HTimeSearchStatement 7aca01fb53d67235
```

### `AvailableChainFGSAClaims.Statements.Packages.Finality`

```text
def AvailableChain.FGSA.Run.finalityWindow 9aa7616d35b182b1
structure AvailableChain.FGSA.Run.FirstFinalityPrem 4ec6c555dacc6b7e
ctor AvailableChain.FGSA.Run.FirstFinalityPrem.mk abb8acc90ec3d017
field AvailableChain.FGSA.Run.FirstFinalityPrem.set 2989f0305ac9726f
field AvailableChain.FGSA.Run.FirstFinalityPrem.hhor ac6c8f5d440812a7
structure AvailableChain.FGSA.Run.FinalityLivenessPrem 9edde22b741ab275
ctor AvailableChain.FGSA.Run.FinalityLivenessPrem.mk 86ff04aac814f6d1
field AvailableChain.FGSA.Run.FinalityLivenessPrem.set 35284181533abfa8
field AvailableChain.FGSA.Run.FinalityLivenessPrem.late 05189d9cf0cf1f18
field AvailableChain.FGSA.Run.FinalityLivenessPrem.hhor b4ac5873f037281f
structure AvailableChain.FGSA.Run.ProposalFinalPrem 5171c2cd1d9ce7b5
ctor AvailableChain.FGSA.Run.ProposalFinalPrem.mk 3d975ed5cc4e5080
field AvailableChain.FGSA.Run.ProposalFinalPrem.set 1d9de66b5b8ed40f
field AvailableChain.FGSA.Run.ProposalFinalPrem.prop f2c24bc564329ab8
field AvailableChain.FGSA.Run.ProposalFinalPrem.late d889613146ec3652
field AvailableChain.FGSA.Run.ProposalFinalPrem.hhor fdef673c1bbd3dea
structure AvailableChain.FGSA.Run.AboveFrontierPrem 1001ab2436c5b434
ctor AvailableChain.FGSA.Run.AboveFrontierPrem.mk 2901aaa6e628a084
field AvailableChain.FGSA.Run.AboveFrontierPrem.set 899480f2b3739a7e
field AvailableChain.FGSA.Run.AboveFrontierPrem.late d94618bfeff73e53
field AvailableChain.FGSA.Run.AboveFrontierPrem.hhor f23aca8d18aaa902
structure AvailableChain.FGSA.Run.QualifiedFinalityPrem 6c3eb11db71bfdd7
ctor AvailableChain.FGSA.Run.QualifiedFinalityPrem.mk 8f10e20daf43f1a7
field AvailableChain.FGSA.Run.QualifiedFinalityPrem.set a66a6a177c5dd86b
field AvailableChain.FGSA.Run.QualifiedFinalityPrem.hhor f753c33cefb4dc21
structure AvailableChain.FGSA.Run.SkipFinalityPrem 316aca189a23eef1
ctor AvailableChain.FGSA.Run.SkipFinalityPrem.mk 83edf9978cb3245b
field AvailableChain.FGSA.Run.SkipFinalityPrem.set 13df4cb41f1a28ed
field AvailableChain.FGSA.Run.SkipFinalityPrem.hhor a6206c43963ee4a1
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
structure AvailableChain.FGSA.Run.HealingPrem 3c7596c7d27fa6e8
ctor AvailableChain.FGSA.Run.HealingPrem.mk 60c4dc2b4aa73ac6
field AvailableChain.FGSA.Run.HealingPrem.set ce411272b5b8b284
structure AvailableChain.FGSA.Run.HealingWitnessPrem a55d45a5fd6f34bc
field AvailableChain.FGSA.Run.HealingWitnessPrem.toHealingPrem bfec52e80ad9023f
ctor AvailableChain.FGSA.Run.HealingWitnessPrem.mk 16a0b700a13a010c
field AvailableChain.FGSA.Run.HealingWitnessPrem.h0 ffde30741adfea1f
structure AvailableChain.FGSA.Run.HealingTimePrem 7645d7fb722b767f
field AvailableChain.FGSA.Run.HealingTimePrem.toHealingPrem be8f6008064fb3e7
ctor AvailableChain.FGSA.Run.HealingTimePrem.mk e656d2d3132b5000
field AvailableChain.FGSA.Run.HealingTimePrem.hhor 1464bdc7a01663b8
structure AvailableChain.FGSA.Run.ResetArrivalPrem 9a0dc65650f5da28
field AvailableChain.FGSA.Run.ResetArrivalPrem.toHealingPrem dff7623498b5349a
ctor AvailableChain.FGSA.Run.ResetArrivalPrem.mk 5ea0ef859790e7c1
field AvailableChain.FGSA.Run.ResetArrivalPrem.hhor 86f75a3d8a09f4a7
structure AvailableChain.FGSA.Run.ResetArrivalFullPrem f29060e0da575562
field AvailableChain.FGSA.Run.ResetArrivalFullPrem.toHealingPrem ce69b3463b973389
ctor AvailableChain.FGSA.Run.ResetArrivalFullPrem.mk 03d6b22a4de8c6a9
field AvailableChain.FGSA.Run.ResetArrivalFullPrem.hhor 938e65a339e74fb1
structure AvailableChain.FGSA.Run.KernelJoinedPrem c8e1c0c642279411
ctor AvailableChain.FGSA.Run.KernelJoinedPrem.mk ea18c04df6b5d3e4
field AvailableChain.FGSA.Run.KernelJoinedPrem.set 75d9c0f3940ee31c
field AvailableChain.FGSA.Run.KernelJoinedPrem.window bf7937f3c56e3323
field AvailableChain.FGSA.Run.KernelJoinedPrem.start e3bc018643d49558
field AvailableChain.FGSA.Run.KernelJoinedPrem.hhor 35ba394fdbf901a5
structure AvailableChain.FGSA.Run.HealingAttemptPrem b4ee26049d840f0b
field AvailableChain.FGSA.Run.HealingAttemptPrem.toHealingPrem 52035276b24a9851
ctor AvailableChain.FGSA.Run.HealingAttemptPrem.mk fa0e74f8ce6f33c0
field AvailableChain.FGSA.Run.HealingAttemptPrem.valid 3de7907d9ab13ef4
```

### `AvailableChainFGSAClaims.Statements.Packages.Outage`

```text
structure AvailableChain.FGSA.Run.OutagePrem 27bbbe113f47f70d
ctor AvailableChain.FGSA.Run.OutagePrem.mk fbad3fdd8e773765
field AvailableChain.FGSA.Run.OutagePrem.set e15a8271bca9352a
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
structure AvailableChain.FGSA.Run.SameLabelPrem 54ad2a09645e204e
ctor AvailableChain.FGSA.Run.SameLabelPrem.mk 44be30f0060439a1
field AvailableChain.FGSA.Run.SameLabelPrem.set 1dec07e6834aff7b
field AvailableChain.FGSA.Run.SameLabelPrem.sync 534f2bff2277bec5
structure AvailableChain.FGSA.Run.SourceDisciplinePrem 333d5cc690cc02d8
ctor AvailableChain.FGSA.Run.SourceDisciplinePrem.mk 07c9d73a4dcd0696
field AvailableChain.FGSA.Run.SourceDisciplinePrem.set 470aaf5c83a839cf
field AvailableChain.FGSA.Run.SourceDisciplinePrem.quorum 96e95761bcabad06
structure AvailableChain.FGSA.Run.FinalizedSafetyPrem ce0c9f6b2ba4c0ee
ctor AvailableChain.FGSA.Run.FinalizedSafetyPrem.mk d7a3792ef873d8a4
field AvailableChain.FGSA.Run.FinalizedSafetyPrem.set 0ab3321932adc4e5
field AvailableChain.FGSA.Run.FinalizedSafetyPrem.fault 3a90ddf34b2b379d
structure AvailableChain.FGSA.Run.CleanPrem d6d67471b7854014
ctor AvailableChain.FGSA.Run.CleanPrem.mk 26cb49ea1796164a
field AvailableChain.FGSA.Run.CleanPrem.set afb75bcb7d630ee3
structure AvailableChain.FGSA.Run.CleanPrefixPrem 36916327c83ca419
ctor AvailableChain.FGSA.Run.CleanPrefixPrem.mk 8fdd8b1d726ecc9b
field AvailableChain.FGSA.Run.CleanPrefixPrem.set 597e2acaa550d757
structure AvailableChain.FGSA.Run.CleanCutPrem abb96a0955c6eed9
ctor AvailableChain.FGSA.Run.CleanCutPrem.mk 68c4839d7d039b0e
field AvailableChain.FGSA.Run.CleanCutPrem.set d06b8442d452429d
structure AvailableChain.FGSA.Run.ReleasePrem 8a342c5756d0b9b7
ctor AvailableChain.FGSA.Run.ReleasePrem.mk 0b6d04cf47ee8902
field AvailableChain.FGSA.Run.ReleasePrem.set 62937de1fb2f20ce
field AvailableChain.FGSA.Run.ReleasePrem.lt 09e5c4c8fec5e022
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
structure AvailableChain.FGSA.Run.HealthyPrefix₂ 676d3569f28abcee
ctor AvailableChain.FGSA.Run.HealthyPrefix₂.mk 9a48c1dfa084db0d
field AvailableChain.FGSA.Run.HealthyPrefix₂.base a3c82b099243c426
field AvailableChain.FGSA.Run.HealthyPrefix₂.cut db3539ac99baa053
field AvailableChain.FGSA.Run.HealthyPrefix₂.healthy 9de0229cf3b76c46
field AvailableChain.FGSA.Run.HealthyPrefix₂.partBefore 1665e327e864efe3
structure AvailableChain.FGSA.Run.CleanPrefix₂ 9eb1ce99757a14f3
field AvailableChain.FGSA.Run.CleanPrefix₂.toHealthyPrefix₂ 2043febd275207bf
ctor AvailableChain.FGSA.Run.CleanPrefix₂.mk cbc8baf02b506226
field AvailableChain.FGSA.Run.CleanPrefix₂.partAt 779cd6daa686c9fa
def AvailableChain.FGSA.Run.CleanCut₂ 0ba8abc0d73e20c7
structure AvailableChain.FGSA.Run.Clean₂ d9d432d1a7b24aa7
ctor AvailableChain.FGSA.Run.Clean₂.mk ae476e1f1ff51de0
field AvailableChain.FGSA.Run.Clean₂.pre d022e5f32aa34120
field AvailableChain.FGSA.Run.Clean₂.gst 87d5a4994f1c2e69
structure AvailableChain.FGSA.Run.Recovery₂ 1b61f1e8af217d3e
field AvailableChain.FGSA.Run.Recovery₂.toRecoveryCore 01e0ce6305a7bc33
ctor AvailableChain.FGSA.Run.Recovery₂.mk 4b248dfbc548805a
field AvailableChain.FGSA.Run.Recovery₂.base 78eee3f951f03831
field AvailableChain.FGSA.Run.Recovery₂.fault 43255b7e17206d9c
field AvailableChain.FGSA.Run.Recovery₂.awake 8259f1ac9f50f7b9
field AvailableChain.FGSA.Run.Recovery₂.gapPos 56c585446044aac2
def AvailableChain.FGSA.Run.BaseSet 029ed410fb299109
def AvailableChain.FGSA.Run.CleanSet ae7008bb8e17c45b
def AvailableChain.FGSA.Run.CleanCutSet 67ac7d89b5320576
def AvailableChain.FGSA.Run.CleanPrefixSet c358a06f6b00e0b5
def AvailableChain.FGSA.Run.HealingSet d4fe657d4de83645
structure AvailableChain.FGSA.Run.FinalitySet 0f63a30fee7e1e4b
ctor AvailableChain.FGSA.Run.FinalitySet.mk 9b51e854b181fa59
field AvailableChain.FGSA.Run.FinalitySet.core e0d23e61645a9be4
field AvailableChain.FGSA.Run.FinalitySet.recur 410e57da9ec97580
structure AvailableChain.FGSA.Run.Outage₂ f3015b1207351315
ctor AvailableChain.FGSA.Run.Outage₂.mk 81add662c7d3ea13
field AvailableChain.FGSA.Run.Outage₂.pre e9439ea74bf4da05
field AvailableChain.FGSA.Run.Outage₂.sleepy bead469cee572c28
field AvailableChain.FGSA.Run.Outage₂.order 65ceb616f7b7ee40
field AvailableChain.FGSA.Run.Outage₂.lag 1997c30e99903c4e
field AvailableChain.FGSA.Run.Outage₂.budget 01b2e4fcff2ffe7d
field AvailableChain.FGSA.Run.Outage₂.fastPart bf1664fc5fe83102
def AvailableChain.FGSA.Run.OutageSet dcd44cc984c2c5c6
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
