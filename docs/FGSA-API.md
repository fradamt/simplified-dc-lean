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
inductive AvailableChain.FGSA.Reachable 551052dced3030c7
ctor AvailableChain.FGSA.Reachable.init 90146c8b7940c5e9
ctor AvailableChain.FGSA.Reachable.tick ad591eec5853eeb2
ctor AvailableChain.FGSA.Reachable.deliver c9a48f1cdaf298ec
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
structure AvailableChain.FGSA.MetaInv 47b4504e54402bb8
ctor AvailableChain.FGSA.MetaInv.mk 3a006ab9945dea3d
field AvailableChain.FGSA.MetaInv.wireTree 6a7caf56a3178f9e
field AvailableChain.FGSA.MetaInv.treeWire 6e621d5717aff5a4
field AvailableChain.FGSA.MetaInv.proposalsNodup a8881ca5289cdf64
field AvailableChain.FGSA.MetaInv.stampKeys d8cb266fb0f2a890
field AvailableChain.FGSA.MetaInv.blocksNodup 7fcdd3cc73ea039f
field AvailableChain.FGSA.MetaInv.poolDecodes 8b78fbd1ef713804
field AvailableChain.FGSA.MetaInv.poolNodup 0f6159c9553c718c
field AvailableChain.FGSA.MetaInv.poolCap 3f3bab3852bb0908
field AvailableChain.FGSA.MetaInv.noGenesisWire 9e26f031d5f1b8ce
def AvailableChain.FGSA.ContentAgree 9f1216009903713b
```

### `AvailableChainFGSA.Statements.Store`

```text
def AvailableChain.FGSA.OutputNestingStored c23fc5e78ebae681
def AvailableChain.FGSA.StoreInvariant 026fc456bd252bf3
structure AvailableChain.FGSA.StoreBundle 39bba6f0449fabed
ctor AvailableChain.FGSA.StoreBundle.mk 388f03d0d8c0153e
field AvailableChain.FGSA.StoreBundle.cstore ff4be3db65bcffb9
field AvailableChain.FGSA.StoreBundle.meta 2d8549f2f1445db7
field AvailableChain.FGSA.StoreBundle.nest d8ac747570bb5e6c
field AvailableChain.FGSA.StoreBundle.lease ffb1f85f36f5636d
def AvailableChain.FGSA.StoreBundleInvariant 8ef4f06bb69a1750
theorem AvailableChain.FGSA.StoreBundleInvariant_def 500ba4f0a1e364a4
def AvailableChain.FGSA.FMonotone d88c5d37bee7874a
def AvailableChain.FGSA.MetadataInvariant a9c25d5970c6ec6a
```

## `AvailableChainFGSARun`

### `AvailableChainFGSARun.Statements.AC`

```text
def AvailableChain.FGSA.Run.fgsaAC a24636d781e6a379
```

### `AvailableChainFGSARun.Statements.Acceptance`

```text
def AvailableChain.FGSA.Run.fgsaAdmissionTime 5a24d5a7aeb94175
def AvailableChain.FGSA.Run.fgsaTimely fcf504746459e1fa
def AvailableChain.FGSA.Run.fgsaAcceptanceInv bfb9c63bb709ea85
def AvailableChain.FGSA.Run.fgsaTrigger 444e05cfb77d1de4
```

### `AvailableChainFGSARun.Statements.Client`

```text
def AvailableChain.FGSA.Run.EmitsRow c63f711563e5793b
def AvailableChain.FGSA.Run.EmittedRowsNoSlash a3163750992050bc
def AvailableChain.FGSA.Run.decodeRowObject 9be96723480d8b10
def AvailableChain.FGSA.Run.fgClientEvent 493661c0e29d1bf9
def AvailableChain.FGSA.Run.fgClientEvents e9aba1b9b06ce593
```

### `AvailableChainFGSARun.Statements.Emission`

```text
def AvailableChain.FGSA.Run.EmissionRowsValid afc79bdc5378f587
def AvailableChain.FGSA.Run.decode c06272443aaec6cb
def AvailableChain.FGSA.Run.HonestEmissionWellFormed 3e7d37efcbe07bed
def AvailableChain.FGSA.Run.HonestProposalDecodes 427726e6a20714a6
```

### `AvailableChainFGSARun.Statements.Excludes`

```text
inductive AvailableChain.FGSA.Run.EpochStep 7abf4af6e699de0d
ctor AvailableChain.FGSA.Run.EpochStep.deliver d1ab595395e70913
ctor AvailableChain.FGSA.Run.EpochStep.clock 453a830ba19d8c73
def AvailableChain.FGSA.Run.Epoch e3eb270a65a419c3
def AvailableChain.FGSA.Run.excludesFixed bd11d81ffefde495
```

### `AvailableChainFGSARun.Statements.Interface`

```text
def AvailableChain.FGSA.Run.fgsaInterface bd86aa5f5df805cb
def AvailableChain.FGSA.Run.fgsaOutputs 2a91d07c031d4c8b
def AvailableChain.FGSA.Run.finalizedOut eb13de3f9e21b2a8
```

### `AvailableChainFGSARun.Statements.ReceiptCoverage`

```text
structure AvailableChain.FGSA.Run.ReceiptCoveragePremises d6634e19f5c18c0c
ctor AvailableChain.FGSA.Run.ReceiptCoveragePremises.mk 1950337ea93bc2c1
field AvailableChain.FGSA.Run.ReceiptCoveragePremises.within aff49a1af66fc149
field AvailableChain.FGSA.Run.ReceiptCoveragePremises.slotWindow d9a73e72784c38dd
field AvailableChain.FGSA.Run.ReceiptCoveragePremises.compat 926fb680a277fe9c
field AvailableChain.FGSA.Run.ReceiptCoveragePremises.deadline 025e7df9c49cdf66
def AvailableChain.FGSA.Run.ReceiptCoverageStatement cc234e43f161b161
theorem AvailableChain.FGSA.Run.ReceiptCoverageStatement_def 414eecaab2d0bcbb
```

### `AvailableChainFGSARun.Statements.Receipts`

```text
def AvailableChain.FGSA.Run.blockOf? 237207ab41bcc56a
```

### `AvailableChainFGSARun.Statements.Slashing`

```text
def AvailableChain.FGSA.Run.fgsaEvidence 9eba3b221236d864
def AvailableChain.FGSA.Run.fgsaSlashing 565d370043431ab5
```

## `AvailableChainFGSAClaims`

### `AvailableChainFGSAClaims.Claims.Clean`

```text
def AvailableChain.FGSA.Run.CleanHistoryAt b2d6f02720d7d8bf
def AvailableChain.FGSA.Run.CleanGateAt 5b3aa1675ae68fe0
def AvailableChain.FGSA.Run.CleanTruncAt 624399b662aaf234
def AvailableChain.FGSA.Run.CleanSafetyAt 6f61be66491e5a1b
def AvailableChain.FGSA.Run.CleanCutClaim 2bea789dffe71f77
def AvailableChain.FGSA.Run.CleanCutZeroClaim ed10a3e70335547f
def AvailableChain.FGSA.Run.CleanHistoryClaim 5085382ec89a4a94
def AvailableChain.FGSA.Run.CleanPrefixTruncationClaim 7830ad0bde014323
def AvailableChain.FGSA.Run.CleanSafetyClaim 34e068b5d6e22974
def AvailableChain.FGSA.Run.CleanCutPosClaim fb59f9611d5e7799
```

### `AvailableChainFGSAClaims.Claims.Foundations`

```text
def AvailableChain.FGSA.Run.ClientSafeAll 8feee12f7945e03e
def AvailableChain.FGSA.Run.ClientSafetyClaim c99e8fed71a507f1
def AvailableChain.FGSA.Run.ClientSafetyBaseClaim 97a4eb8deb34d216
def AvailableChain.FGSA.Run.FGFoundationClaim 4d70524eb70a6848
def AvailableChain.FGSA.Run.SrcFrameAboveClaim 66ef3f30b19843c4
def AvailableChain.FGSA.Run.RunFGBlock 48bfd6d9cfb6cdfc
def AvailableChain.FGSA.Run.CarrierAt 42d167f2c762b13e
def AvailableChain.FGSA.Run.StoreAt 3f3caa1cdaa20ffe
def AvailableChain.FGSA.Run.ActiveViewAt b68f130678c81e9d
def AvailableChain.FGSA.Run.LeaseOriginsAt acaf094f4e40f1c1
def AvailableChain.FGSA.Run.SourceDisciplineBaseAt de893e0367a90873
def AvailableChain.FGSA.Run.SourceDisciplineAt c478f10c0e38dc8c
def AvailableChain.FGSA.Run.CarrierClaim 521938599aca946a
def AvailableChain.FGSA.Run.ChainCertificatesAt baea88a31b1fbce2
def AvailableChain.FGSA.Run.ChainCertificatesClaim 2786e3621e1d0a39
def AvailableChain.FGSA.Run.StoreClaim bd5d04591d0262b2
def AvailableChain.FGSA.Run.ActiveViewClaim a236ec62b0bf3c29
def AvailableChain.FGSA.Run.LeaseOriginsClaim fa2724ec77436e03
def AvailableChain.FGSA.Run.ReconcileAt bea5ba077a213f02
def AvailableChain.FGSA.Run.ReconcileClaim ad8b5acd45a30c54
def AvailableChain.FGSA.Run.OutputNestingAt 9b897a9e51b12138
def AvailableChain.FGSA.Run.OutputNestingClaim 1cfdd101faf76177
def AvailableChain.FGSA.Run.FrameAt 386aa56b362297f7
def AvailableChain.FGSA.Run.FrameClaim b5d3c684a1d73257
def AvailableChain.FGSA.Run.SourceDisciplineBaseClaim 20decd24ed6b4a05
def AvailableChain.FGSA.Run.SourceDisciplineClaim 8a2bb0769cca7267
```

### `AvailableChainFGSAClaims.Claims.Shared`

```text
def AvailableChain.FGSA.Run.SameLabelAt c36bb6ed2beeacc4
def AvailableChain.FGSA.Run.SameLabelClaim 8212a2e8aa3bdd55
def AvailableChain.FGSA.Run.HeadReachesLoAt b7df7a59c61bd2cf
def AvailableChain.FGSA.Run.HeadReachesLoClaim f5f5bad9ada773ec
def AvailableChain.FGSA.Run.ReleaseStoreAt 4821a3dc715fe93d
def AvailableChain.FGSA.Run.ReleaseStoreClaim 8686f70b1a563f39
def AvailableChain.FGSA.Run.ReleaseAt c687e575c9ba1656
def AvailableChain.FGSA.Run.ReleaseClaim 793f6110d742f35c
```

### `AvailableChainFGSAClaims.FGSAClaims`

```text
structure AvailableChain.FGSA.Run.FGSASafetyClaims 00ada3b57d3faaa9
ctor AvailableChain.FGSA.Run.FGSASafetyClaims.mk 3cc0836f3f7d5119
field AvailableChain.FGSA.Run.FGSASafetyClaims.carrier e38dce591a05913e
field AvailableChain.FGSA.Run.FGSASafetyClaims.chainCertificates 7f3e491070144f1f
field AvailableChain.FGSA.Run.FGSASafetyClaims.store 927c8cb59dd2736a
field AvailableChain.FGSA.Run.FGSASafetyClaims.activeView 9f6e7c4fc9c090b9
field AvailableChain.FGSA.Run.FGSASafetyClaims.leaseOrigins 04dd5346be5ef4e0
field AvailableChain.FGSA.Run.FGSASafetyClaims.reconcile 8434f29601ad609c
field AvailableChain.FGSA.Run.FGSASafetyClaims.outputNesting bee3b6330cf7d077
field AvailableChain.FGSA.Run.FGSASafetyClaims.frame 4438a93d47e12e84
field AvailableChain.FGSA.Run.FGSASafetyClaims.clientSafety 6e8cee9137868a04
field AvailableChain.FGSA.Run.FGSASafetyClaims.clientSafetyBase 858de138465f1979
field AvailableChain.FGSA.Run.FGSASafetyClaims.sourceDisciplineBase b57eeaceaf8d7ead
field AvailableChain.FGSA.Run.FGSASafetyClaims.sourceDiscipline 8a363c91fa1e59d7
field AvailableChain.FGSA.Run.FGSASafetyClaims.sameLabel 6a9c11768c7bf1a5
field AvailableChain.FGSA.Run.FGSASafetyClaims.releaseStore 296941ff2414e6ca
field AvailableChain.FGSA.Run.FGSASafetyClaims.release 02c12bd920b2be87
field AvailableChain.FGSA.Run.FGSASafetyClaims.headReachesLo 02ee3107a47e80df
field AvailableChain.FGSA.Run.FGSASafetyClaims.cleanCut f1890b5fabd01bd1
field AvailableChain.FGSA.Run.FGSASafetyClaims.cleanHistory 998ab83c7b1421fe
field AvailableChain.FGSA.Run.FGSASafetyClaims.cleanPrefixTruncation 526057dd3e7dff4e
field AvailableChain.FGSA.Run.FGSASafetyClaims.cleanSafety ac9f18b20669a164
structure AvailableChain.FGSA.Run.FGSASafetyInterfaces 60e0c6ec94f09334
ctor AvailableChain.FGSA.Run.FGSASafetyInterfaces.mk 146752004bc593a3
field AvailableChain.FGSA.Run.FGSASafetyInterfaces.fgFoundation 0311616d33e96d4c
field AvailableChain.FGSA.Run.FGSASafetyInterfaces.srcFrameAbove e2950246ccf04d0c
field AvailableChain.FGSA.Run.FGSASafetyInterfaces.cpPrefix 31fc8cbb6069167c
field AvailableChain.FGSA.Run.FGSASafetyInterfaces.cpCompat c0ff1bcac226fd78
field AvailableChain.FGSA.Run.FGSASafetyInterfaces.tSrc 70b751f6d0b7ea15
field AvailableChain.FGSA.Run.FGSASafetyInterfaces.labelBound 254b0cc2855c4b17
field AvailableChain.FGSA.Run.FGSASafetyInterfaces.timingContract 98e50f560943bdf1
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
def AvailableChain.FGSA.Run.RCarrierView 049c5615ebc159d8
theorem AvailableChain.FGSA.Run.RCarrierView_def 3141293d1d7ac37a
def AvailableChain.FGSA.Run.RStore 5a3a4a59084f9b2a
theorem AvailableChain.FGSA.Run.RStore_def 45dbee6cdfcd662a
def AvailableChain.FGSA.Run.RActive 94cad8039e5e744f
theorem AvailableChain.FGSA.Run.RActive_def 3431b7faa9340c80
def AvailableChain.FGSA.Run.RStoreCumul 60f1b245b3a922d7
theorem AvailableChain.FGSA.Run.RStoreCumul_def 54aea7689731e6c6
def AvailableChain.FGSA.Run.RMono 77bdd129ecff6606
theorem AvailableChain.FGSA.Run.RMono_def 5fc203c6ef3e76ee
def AvailableChain.FGSA.Run.RFrameExact ebc82d4ae349f581
theorem AvailableChain.FGSA.Run.RFrameExact_def f233d2c2a9be393d
def AvailableChain.FGSA.Run.RFrame 99001362b1c594fc
theorem AvailableChain.FGSA.Run.RFrame_def 31f0f7b07347bc20
def AvailableChain.FGSA.Run.RGeo ed5d658b0b95b755
theorem AvailableChain.FGSA.Run.RGeo_def b48ed470d9b34963
def AvailableChain.FGSA.Run.RCert 781a4f8b9bd9035d
theorem AvailableChain.FGSA.Run.RCert_def 39c87ff938fdf80c
def AvailableChain.FGSA.Run.RRec b024049ed209982c
theorem AvailableChain.FGSA.Run.RRec_def d1f42b6f2028599e
def AvailableChain.FGSA.Run.TSrc 4727471f2871e0e1
theorem AvailableChain.FGSA.Run.TSrc_def 34c1f2f28a589bdd
def AvailableChain.FGSA.Run.LabelBound 9a153c5d6a1f1d3d
theorem AvailableChain.FGSA.Run.LabelBound_def c990de3df41826ea
def AvailableChain.FGSA.Run.TChain 6530b155d84f8c66
theorem AvailableChain.FGSA.Run.TChain_def f766a80b36b4438d
def AvailableChain.FGSA.Run.TCompat 5c7c643d7dc88e99
theorem AvailableChain.FGSA.Run.TCompat_def 77b05e7adaa40156
structure AvailableChain.FGSA.Run.AncestorClosed 593b2f5afe7c4910
ctor AvailableChain.FGSA.Run.AncestorClosed.mk b48754dc553f2a0f
field AvailableChain.FGSA.Run.AncestorClosed.down 3036e679b5e16c54
def AvailableChain.FGSA.Run.FrameBelow b5f99579a3eceef5
theorem AvailableChain.FGSA.Run.FrameBelow_def d4f3816f09fe5405
def AvailableChain.FGSA.Run.RStrat 73710c5fd6b43745
theorem AvailableChain.FGSA.Run.RStrat_def 659d5d0d0540b15b
def AvailableChain.FGSA.Run.RQCOrigin f09a120ae9f6423a
theorem AvailableChain.FGSA.Run.RQCOrigin_def e956116825d198f5
def AvailableChain.FGSA.Run.SrcFrameAbove c52cea0be2d5bc4b
theorem AvailableChain.FGSA.Run.SrcFrameAbove_def 7aa90982fd8b0520
def AvailableChain.FGSA.Run.SrcFrame 64ab9f8f0222b6ec
def AvailableChain.FGSA.Run.SrcFrameAboveStmt 02a9bc569732ac82
theorem AvailableChain.FGSA.Run.SrcFrameAboveStmt_def 388c77ff95d5c6d0
def AvailableChain.FGSA.Run.CPPrefix 66d8d057d71f1d60
theorem AvailableChain.FGSA.Run.CPPrefix_def 1fbf42dc6ded7bd4
def AvailableChain.FGSA.Run.CPCompat 9f1fd75708e67b45
theorem AvailableChain.FGSA.Run.CPCompat_def 3ded647b8e138b36
def AvailableChain.FGSA.Run.RXing 4b0163d3e3184c07
def AvailableChain.FGSA.Run.RCap e3560f537fb82d7a
def AvailableChain.FGSA.Run.THigh cc195e7a5ccc7cbf
def AvailableChain.FGSA.Run.TCarrier 0f2f8bc13925d5e2
def AvailableChain.FGSA.Run.TRowsSelect 35044c81ff658f77
def AvailableChain.FGSA.Run.TRowsSync 6bca138d5bd4f186
structure AvailableChain.FGSA.Run.TRows d98fcac77d0b4a60
ctor AvailableChain.FGSA.Run.TRows.mk 75249cf8d068f2c2
field AvailableChain.FGSA.Run.TRows.select d11898e694797073
field AvailableChain.FGSA.Run.TRows.sync d481b96e96c24364
def AvailableChain.FGSA.Run.SourceBefore c55ac18f92215637
def AvailableChain.FGSA.Run.Kept bb482cdff6cc3cfd
def AvailableChain.FGSA.Run.KeepOrCause 36a105eba214780f
def AvailableChain.FGSA.Run.RExcl addb6f8a193b04bc
def AvailableChain.FGSA.Run.RKeep 2388f079045c1be0
def AvailableChain.FGSA.Run.RFProv aff58b35784afa67
def AvailableChain.FGSA.Run.TDel d46107ada697c38f
def AvailableChain.FGSA.Run.TDelReset db8dcf68cb0db4be
def AvailableChain.FGSA.Run.TGeom f97549b43a102be9
def AvailableChain.FGSA.Run.ExactService a2a9f51fd1de4f92
def AvailableChain.FGSA.Run.PhaseInterval 9ddef16a2a3b652f
def AvailableChain.FGSA.Run.Transfers 5aecb9a0b307633a
def AvailableChain.FGSA.Run.PhaseBody eee0a39289331a54
def AvailableChain.FGSA.Run.TPerm e6a0d30812c6fc2b
def AvailableChain.FGSA.Run.ProposalGap 3ca431db71b977bd
def AvailableChain.FGSA.Run.RepairAfter b5072d5bded184af
def AvailableChain.FGSA.Run.TRepair e15e7b8870aa6c89
def AvailableChain.FGSA.Run.OpeningExtends fae779be520df050
def AvailableChain.FGSA.Run.OpeningEntry 14c1e67b7e754cd8
def AvailableChain.FGSA.Run.TCommon e33463b0396acce6
def AvailableChain.FGSA.Run.TFrontier 0de812ec6b3140d7
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
def AvailableChain.FGSA.Run.R_at 89b926d23867a5f5
def AvailableChain.FGSA.Run.D_at e79a37dddcbb64b5
def AvailableChain.FGSA.Run.FAdvanceAt c705ab54a24343b1
def AvailableChain.FGSA.Run.candidatesAt 2dcbe2f6532023a9
def AvailableChain.FGSA.Run.proposalHeadAt f44ff2a62a054584
def AvailableChain.FGSA.Run.actionHead ae4bcdead2fa9ccc
def AvailableChain.FGSA.Run.actionTriple f39bc51d2dcb863b
def AvailableChain.FGSA.Run.namedEntry a50c73e0c7ee36db
def AvailableChain.FGSA.Run.EntryBelow 8b562d8188ed8ea7
def AvailableChain.FGSA.Run.RowSigner c038dfc4e89a9afa
def AvailableChain.FGSA.Run.HonestRowAt 629b32366dc139e9
def AvailableChain.FGSA.Run.HonestRowBefore 000964b7961cf900
theorem AvailableChain.FGSA.Run.HonestRowBefore_def e54cea66aa05af91
def AvailableChain.FGSA.Run.RowComplete 949b1c814329c668
def AvailableChain.FGSA.Run.HonestCarrier aa3aa20ceffc29ee
def AvailableChain.FGSA.Run.HeldAt 9332377a6e83f871
def AvailableChain.FGSA.Run.BlockInRunBefore 7b968a9bcdfeb937
theorem AvailableChain.FGSA.Run.RowSigner_def 12caa3320e081dc2
theorem AvailableChain.FGSA.Run.HonestRowAt_def 25f1ec677f848162
def AvailableChain.FGSA.Run.rowHeld 430bb778b0f3cf8f
def AvailableChain.FGSA.Run.proposalStateAt 1cbb023285a771eb
def AvailableChain.FGSA.Run.heldAtProposal b18112a70a6e85ab
def AvailableChain.FGSA.Run.onParentChain 2284f466fb1d471f
def AvailableChain.FGSA.Run.HeldBefore 942ac64b1489c85e
def AvailableChain.FGSA.Run.InRowWindow 1beded69f5536d2f
def AvailableChain.FGSA.Run.headAtLabel 7b7b075730527741
```

### `AvailableChainFGSAClaims.Statements.ComposeStmt`

```text
def AvailableChain.FGSA.Run.windowIdx e0126360a4d1dbea
structure AvailableChain.FGSA.Run.TimingContract 42085a0db1d9b588
ctor AvailableChain.FGSA.Run.TimingContract.mk b694ca2d7adbdb18
field AvailableChain.FGSA.Run.TimingContract.rowLag 773ef5f262448c49
field AvailableChain.FGSA.Run.TimingContract.certLag cb82e9b0b1c45460
field AvailableChain.FGSA.Run.TimingContract.label 063db079c55649b3
field AvailableChain.FGSA.Run.TimingContract.atomic a437d4eae88ae04f
field AvailableChain.FGSA.Run.TimingContract.tickFG 0605ed44133026e7
structure AvailableChain.FGSA.Run.FGFoundation bea6c621ddbfec37
ctor AvailableChain.FGSA.Run.FGFoundation.mk d392c566d3dc51d7
field AvailableChain.FGSA.Run.FGFoundation.store 345b7b918ba462ee
field AvailableChain.FGSA.Run.FGFoundation.cumul 629442a893077cdd
field AvailableChain.FGSA.Run.FGFoundation.mono 025e5b8fc928037d
field AvailableChain.FGSA.Run.FGFoundation.frame 7180a4617b13912d
field AvailableChain.FGSA.Run.FGFoundation.geo 0a57b40b60900f0f
field AvailableChain.FGSA.Run.FGFoundation.strat afa91d9f2b3b17b5
field AvailableChain.FGSA.Run.FGFoundation.reconcile c5b03a36f009821e
def AvailableChain.FGSA.Run.TStart 8ae86e9f782f8013
def AvailableChain.FGSA.Run.FullVoteService 7a4b0d28317dbed6
def AvailableChain.FGSA.Run.TVote 029cfae17baee28f
def AvailableChain.FGSA.Run.WalkBatch eb0a3c186e9e8947
def AvailableChain.FGSA.Run.TWalk 627c8b114254115b
structure AvailableChain.FGSA.Run.CoreServices 208f0dcc3768d198
ctor AvailableChain.FGSA.Run.CoreServices.mk a3533142ff11472f
field AvailableChain.FGSA.Run.CoreServices.start a43fdd98d99c4965
field AvailableChain.FGSA.Run.CoreServices.vote fd9100f8ab1c8551
field AvailableChain.FGSA.Run.CoreServices.walk 3ab73862deb39970
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
def AvailableChain.FGSA.Run.ResetArrivalStatement 40476e13c238d63f
def AvailableChain.FGSA.Run.ResetArrivalFullStatement 44bf84732383f04c
def AvailableChain.FGSA.Run.KernelConclusion 78b9f0abd0057c01
structure AvailableChain.FGSA.Run.KernelPt 9235f1fbc5c48477
ctor AvailableChain.FGSA.Run.KernelPt.mk 32c96b623cc6f691
field AvailableChain.FGSA.Run.KernelPt.w 6cbd0d7075070f20
field AvailableChain.FGSA.Run.KernelPt.r e581c6d88b7635d7
structure AvailableChain.FGSA.Run.KernelPrem b65935177baa62fa
ctor AvailableChain.FGSA.Run.KernelPrem.mk 199e29e501bc4c5f
field AvailableChain.FGSA.Run.KernelPrem.set ad0d841d69cb3f09
field AvailableChain.FGSA.Run.KernelPrem.window bce54d9349ad2c03
field AvailableChain.FGSA.Run.KernelPrem.start 0620c6b05dd6f1d3
field AvailableChain.FGSA.Run.KernelPrem.hhor 10db9d96e080527c
field AvailableChain.FGSA.Run.KernelPrem.input 77afadd8af91e768
field AvailableChain.FGSA.Run.KernelPrem.services 747952ee19fbe28e
def AvailableChain.FGSA.Run.KernelFromContract 1d6cd85e2afe7060
def AvailableChain.FGSA.Run.KernelACSide 57c818d8f349cc04
def AvailableChain.FGSA.Run.kernelStart 6484daab9c494bc9
structure AvailableChain.FGSA.Run.HealTContract 21f1407ee2f6dff3
ctor AvailableChain.FGSA.Run.HealTContract.mk 058ff127fe5924ed
field AvailableChain.FGSA.Run.HealTContract.del d75029cc31e7747e
field AvailableChain.FGSA.Run.HealTContract.delReset 860737ea5697a67e
field AvailableChain.FGSA.Run.HealTContract.perm d46ef0e100ed3ae1
field AvailableChain.FGSA.Run.HealTContract.repair b833d3acce0f4a62
field AvailableChain.FGSA.Run.HealTContract.common 640e0038b894d686
field AvailableChain.FGSA.Run.HealTContract.frontier b1e3663f2b482478
field AvailableChain.FGSA.Run.HealTContract.geom 3d78b9367b8e2bf7
def AvailableChain.FGSA.Run.frontierAtIdx 43d6bd1cffeb92be
def AvailableChain.FGSA.Run.TopEvidence 8c089ddcaf503417
def AvailableChain.FGSA.Run.ContestEvidence b6acd3a8e3cc3a1c
def AvailableChain.FGSA.Run.EffectiveEvent 37f69be587839f33
def AvailableChain.FGSA.Run.AttemptPhaseAt cac1c3dec081e70c
def AvailableChain.FGSA.Run.ServedFrontier b102f86869cbbb31
def AvailableChain.FGSA.Run.AttemptValid 1e2b6da3ae166582
def AvailableChain.FGSA.Run.attemptBudget 3b25a39342572741
def AvailableChain.FGSA.Run.AttemptEndsBy 75ba4968e24567c6
```

### `AvailableChainFGSAClaims.Statements.Counts`

```text
def AvailableChain.FGSA.Run.awakeHonestIn e6da9b5b14f52cbe
def AvailableChain.FGSA.Run.HonestProposal a6bc4ac45f62db72
```

### `AvailableChainFGSAClaims.Statements.Healed`

```text
def AvailableChain.FGSA.Run.healStart 880932e9f4eefa58
def AvailableChain.FGSA.Run.HealSuffix 5a72f2bf575e2232
def AvailableChain.FGSA.Run.Healed 7d1190e75214f5be
def AvailableChain.FGSA.Run.H2A 32ffaab55e4ebcb1
def AvailableChain.FGSA.Run.H2Prime 5ed7be4e42a0f6b7
def AvailableChain.FGSA.Run.H3 6f8c3e5d5966fa0e
def AvailableChain.FGSA.Run.H4 053db74b63bd4c3f
def AvailableChain.FGSA.Run.H5RawTransfer 10d7b1a6fcafcf7b
def AvailableChain.FGSA.Run.H6GateService d9f1213f020e4cec
structure AvailableChain.FGSA.Run.HealT 310fbc99bba1a706
ctor AvailableChain.FGSA.Run.HealT.mk 1b5d77d9eb82b625
field AvailableChain.FGSA.Run.HealT.h1 aab8464d21f681fd
field AvailableChain.FGSA.Run.HealT.h2 258fcff3edf988b4
field AvailableChain.FGSA.Run.HealT.rows ead51058e5ad1e18
structure AvailableChain.FGSA.Run.HealAC f8411e298ddc70b3
ctor AvailableChain.FGSA.Run.HealAC.mk aaeb97d9e6962445
field AvailableChain.FGSA.Run.HealAC.h2A 1722b895e0c5b395
field AvailableChain.FGSA.Run.HealAC.h2' cd8a437dc725f475
field AvailableChain.FGSA.Run.HealAC.h3 1d4c83b5fb7ca019
field AvailableChain.FGSA.Run.HealAC.h4 b0d6f1a7f46e02f3
field AvailableChain.FGSA.Run.HealAC.h5 24a6505b20c20180
field AvailableChain.FGSA.Run.HealAC.h6 d66f0f9f4c517774
structure AvailableChain.FGSA.Run.HealingInput 8e4eb1edd261fb3c
ctor AvailableChain.FGSA.Run.HealingInput.mk f52d7b6f150e7656
field AvailableChain.FGSA.Run.HealingInput.healed 6b5b563cb7a8dee0
field AvailableChain.FGSA.Run.HealingInput.wit ff1ebe1d642b6ce3
field AvailableChain.FGSA.Run.HealingInput.t 5270be1e05954813
field AvailableChain.FGSA.Run.HealingInput.ac ec69ea9be1309449
def AvailableChain.FGSA.Run.HTimeStatement 4a1704ba9f36df44
def AvailableChain.FGSA.Run.HTimeBestStatement 90a495f84e66235a
def AvailableChain.FGSA.Run.HTimeSearchStatement bd952e1c18d74fc6
```

### `AvailableChainFGSAClaims.Statements.Packages.Finality`

```text
def AvailableChain.FGSA.Run.finalityWindow 9aa7616d35b182b1
structure AvailableChain.FGSA.Run.FirstFinalityPrem 58cc3671cc47f38a
ctor AvailableChain.FGSA.Run.FirstFinalityPrem.mk cfffcceb39c25862
field AvailableChain.FGSA.Run.FirstFinalityPrem.set b7e28e40f32da107
field AvailableChain.FGSA.Run.FirstFinalityPrem.hhor 4da217883797ae0f
structure AvailableChain.FGSA.Run.FinalityLivenessPrem c6794441ee9e0360
ctor AvailableChain.FGSA.Run.FinalityLivenessPrem.mk c49406cd37be3300
field AvailableChain.FGSA.Run.FinalityLivenessPrem.set db4b7da6437d4140
field AvailableChain.FGSA.Run.FinalityLivenessPrem.late 79cf493bf5415ecd
field AvailableChain.FGSA.Run.FinalityLivenessPrem.hhor 0ce5d2d5e9350689
structure AvailableChain.FGSA.Run.ProposalFinalPrem e3a61cbe4e2a8d36
ctor AvailableChain.FGSA.Run.ProposalFinalPrem.mk 29d9060269a7e629
field AvailableChain.FGSA.Run.ProposalFinalPrem.set 446a544e6c4892d3
field AvailableChain.FGSA.Run.ProposalFinalPrem.prop 422e91f57286f5e8
field AvailableChain.FGSA.Run.ProposalFinalPrem.late 035651d54df6179b
field AvailableChain.FGSA.Run.ProposalFinalPrem.hhor 7acb86f4e83700a5
structure AvailableChain.FGSA.Run.AboveFrontierPrem d518b9cdd66dce2e
ctor AvailableChain.FGSA.Run.AboveFrontierPrem.mk 6dae9a10cebbf23d
field AvailableChain.FGSA.Run.AboveFrontierPrem.set 1e95c5fd28882053
field AvailableChain.FGSA.Run.AboveFrontierPrem.late d92d442a1793f08c
field AvailableChain.FGSA.Run.AboveFrontierPrem.hhor 61f15745ecab9083
structure AvailableChain.FGSA.Run.QualifiedFinalityPrem ad556479bd14a1fc
ctor AvailableChain.FGSA.Run.QualifiedFinalityPrem.mk 5ffd03d64b82b405
field AvailableChain.FGSA.Run.QualifiedFinalityPrem.set d97432bc0e9b1cbf
field AvailableChain.FGSA.Run.QualifiedFinalityPrem.hhor 1637e5714ecfedd7
structure AvailableChain.FGSA.Run.SkipFinalityPrem c2addf339acf02dc
ctor AvailableChain.FGSA.Run.SkipFinalityPrem.mk e717a126d731319b
field AvailableChain.FGSA.Run.SkipFinalityPrem.set fe5c8b93a5f2f6c7
field AvailableChain.FGSA.Run.SkipFinalityPrem.hhor 8273cf5c24886453
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
structure AvailableChain.FGSA.Run.HealingPrem be6b33b2758de48b
ctor AvailableChain.FGSA.Run.HealingPrem.mk 7c51bb9fdf86c8df
field AvailableChain.FGSA.Run.HealingPrem.set 2d8a678016875e3f
structure AvailableChain.FGSA.Run.HealingWitnessPrem c00e648f90c751b0
field AvailableChain.FGSA.Run.HealingWitnessPrem.toHealingPrem 83090234c8db94d9
ctor AvailableChain.FGSA.Run.HealingWitnessPrem.mk 88b8a24733e38411
field AvailableChain.FGSA.Run.HealingWitnessPrem.h0 ba9c0ade44a3a43d
structure AvailableChain.FGSA.Run.HealingTimePrem d48f9886ac928fa2
field AvailableChain.FGSA.Run.HealingTimePrem.toHealingPrem 73654c72c7bbcf0a
ctor AvailableChain.FGSA.Run.HealingTimePrem.mk a89ebb0caed98af7
field AvailableChain.FGSA.Run.HealingTimePrem.hhor 3328531656f5a741
structure AvailableChain.FGSA.Run.ResetArrivalPrem d42f8026c7fded5c
field AvailableChain.FGSA.Run.ResetArrivalPrem.toHealingPrem 43bce4a7ee992985
ctor AvailableChain.FGSA.Run.ResetArrivalPrem.mk ec21f66a5da8943e
field AvailableChain.FGSA.Run.ResetArrivalPrem.hhor fcb6f5c30e8630e7
structure AvailableChain.FGSA.Run.ResetArrivalFullPrem ca392490305bcd92
field AvailableChain.FGSA.Run.ResetArrivalFullPrem.toHealingPrem 5ae08d5de60c51b7
ctor AvailableChain.FGSA.Run.ResetArrivalFullPrem.mk f6bbbfb09998d1d2
field AvailableChain.FGSA.Run.ResetArrivalFullPrem.hhor ae28bc904b6b5c81
structure AvailableChain.FGSA.Run.KernelJoinedPrem 465aee1a13486abf
ctor AvailableChain.FGSA.Run.KernelJoinedPrem.mk b36b6c35a3a06739
field AvailableChain.FGSA.Run.KernelJoinedPrem.set 3800d90ad2e697e3
field AvailableChain.FGSA.Run.KernelJoinedPrem.window 915988a092cfaec5
field AvailableChain.FGSA.Run.KernelJoinedPrem.start 87ff58bbd3cd1bf9
field AvailableChain.FGSA.Run.KernelJoinedPrem.hhor 0010f30d2a86ce0c
structure AvailableChain.FGSA.Run.HealingAttemptPrem 41db220f450b7bca
field AvailableChain.FGSA.Run.HealingAttemptPrem.toHealingPrem 9b4ddc27e50cedc0
ctor AvailableChain.FGSA.Run.HealingAttemptPrem.mk 66ae3974c4fd5c85
field AvailableChain.FGSA.Run.HealingAttemptPrem.valid ff9840c6ec1d345a
```

### `AvailableChainFGSAClaims.Statements.Packages.Outage`

```text
structure AvailableChain.FGSA.Run.OutagePrem a89e2227fba01ad0
ctor AvailableChain.FGSA.Run.OutagePrem.mk 41cda0cc6ec58a36
field AvailableChain.FGSA.Run.OutagePrem.set a27474dc5c7130d0
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
structure AvailableChain.FGSA.Run.BasePrem fa2ff1db75e3df2f
ctor AvailableChain.FGSA.Run.BasePrem.mk 5aa4f4143ffb8a2b
field AvailableChain.FGSA.Run.BasePrem.set a49f6368d7bd74a8
structure AvailableChain.FGSA.Run.SameLabelPrem 4d3fc59ea61687b5
ctor AvailableChain.FGSA.Run.SameLabelPrem.mk e88d257843467bc8
field AvailableChain.FGSA.Run.SameLabelPrem.set 24ce1e0e6834841c
field AvailableChain.FGSA.Run.SameLabelPrem.sync 4efb6c7718428fa0
structure AvailableChain.FGSA.Run.SourceDisciplinePrem c119705c2fb20e58
ctor AvailableChain.FGSA.Run.SourceDisciplinePrem.mk a1fb6ce4be6295b4
field AvailableChain.FGSA.Run.SourceDisciplinePrem.set 81e7073d8c03b5cc
field AvailableChain.FGSA.Run.SourceDisciplinePrem.quorum 6b42d5366f739ea0
structure AvailableChain.FGSA.Run.FinalizedSafetyPrem 81e8d73146fbf042
ctor AvailableChain.FGSA.Run.FinalizedSafetyPrem.mk 1a246566ca6f8b80
field AvailableChain.FGSA.Run.FinalizedSafetyPrem.set 035ad43ef0c45b3e
field AvailableChain.FGSA.Run.FinalizedSafetyPrem.fault 001c9bfdfbb3af76
structure AvailableChain.FGSA.Run.CleanPrem 79a830ca5ce9f581
ctor AvailableChain.FGSA.Run.CleanPrem.mk 83ff6b1ed1972877
field AvailableChain.FGSA.Run.CleanPrem.set 13eb4bce23c4a968
structure AvailableChain.FGSA.Run.CleanPrefixPrem a8d39cad82cd9d27
ctor AvailableChain.FGSA.Run.CleanPrefixPrem.mk 0cf0d0853a3149a8
field AvailableChain.FGSA.Run.CleanPrefixPrem.set e7d6786729aa3d2c
structure AvailableChain.FGSA.Run.CleanCutPrem a1c39d2db2d73049
ctor AvailableChain.FGSA.Run.CleanCutPrem.mk 66e528ac1f900edd
field AvailableChain.FGSA.Run.CleanCutPrem.set 16d19fe30f69013f
structure AvailableChain.FGSA.Run.ReleasePrem 0fa56c2bba87819a
ctor AvailableChain.FGSA.Run.ReleasePrem.mk 5a151ee548a27305
field AvailableChain.FGSA.Run.ReleasePrem.set 134f0127fc820c2a
field AvailableChain.FGSA.Run.ReleasePrem.lt b7da875bd5324f47
```

### `AvailableChainFGSAClaims.Statements.Reads`

```text
def AvailableChain.FGSA.Run.cutPred 928872abbacb070c
def AvailableChain.FGSA.Run.afterTicksIdx f25a6624c659a3d3
def AvailableChain.FGSA.Run.SuffixIdx 86fb3d8031826d46
def AvailableChain.FGSA.Run.timeIdx a98c0a6c084a5cfe
def AvailableChain.FGSA.Run.afterTicks 4536c4599457544e
def AvailableChain.FGSA.Run.preTick 29639433ae79189d
theorem AvailableChain.FGSA.Run.preTick_def 74a64f75b67bab65
def AvailableChain.FGSA.Run.postClock 164cd3acf4cbfcdd
theorem AvailableChain.FGSA.Run.postClock_def b29f3ebca232d386
def AvailableChain.FGSA.Run.postTick 24a2e1ec9669cac2
def AvailableChain.FGSA.Run.storeAt cfab306b8ac1dfe2
def AvailableChain.FGSA.Run.S_at c98c650091136e81
def AvailableChain.FGSA.Run.F_at 52d0985c444f9344
def AvailableChain.FGSA.Run.J_at acdefaf4f8681b98
def AvailableChain.FGSA.Run.gateIn 0a0effd3acbf7542
theorem AvailableChain.FGSA.Run.gateIn_def ae0d1045db93ff07
def AvailableChain.FGSA.Run.gateResult cae1eefddfd6008f
theorem AvailableChain.FGSA.Run.gateResult_def 939c9ccff21aab1e
def AvailableChain.FGSA.Run.isGateTime e8fa74ed0e358d9a
theorem AvailableChain.FGSA.Run.isGateTime_def 339eae8b30dc753b
def AvailableChain.FGSA.Run.IsGateTick d60d905c11813cda
def AvailableChain.FGSA.Run.gateResultAt 6e696b37833a7cf5
def AvailableChain.FGSA.Run.gatePassedAt 722a740b0f889a13
def AvailableChain.FGSA.Run.fastAt 1a4ad4a80169d1e6
def AvailableChain.FGSA.Run.headAtIdx a825e0d49fe685b3
def AvailableChain.FGSA.Run.vHead 14d3f985615b50e4
theorem AvailableChain.FGSA.Run.vHead_def ab7b48047ba29cb5
def AvailableChain.FGSA.Run.actionSourceFG 4789c1d1f326f79a
theorem AvailableChain.FGSA.Run.actionSourceFG_def 0d2b9d8e6ca489b2
def AvailableChain.FGSA.Run.actionSource 77e5a9e16335258a
def AvailableChain.FGSA.Run.labelBoundAt f7b784ce35d5430c
def AvailableChain.FGSA.Run.DeliveredAt 7d121b9739163bce
def AvailableChain.FGSA.Run.HandlesRowAt d36e77c738bd2d61
def AvailableChain.FGSA.Run.AcceptsFinalBefore d2e487022e16077e
def AvailableChain.FGSA.Run.cleanResults 000dd10286bf38ac
def AvailableChain.FGSA.Run.BelowLabel 35f3bed00547d127
```

### `AvailableChainFGSAClaims.Statements.Recurrence`

```text
```

### `AvailableChainFGSAClaims.Statements.Regimes`

```text
structure AvailableChain.FGSA.Run.Base₂ ff7a0ed066aac98c
ctor AvailableChain.FGSA.Run.Base₂.mk f5bb89a2a4af7cd3
field AvailableChain.FGSA.Run.Base₂.valid 48908e718e18f9d4
field AvailableChain.FGSA.Run.Base₂.linked 50997ccd4abe0def
field AvailableChain.FGSA.Run.Base₂.cstar bf467aa39ed51ae1
field AvailableChain.FGSA.Run.Base₂.noRestart 386ad2b11f8656b8
field AvailableChain.FGSA.Run.Base₂.delta 23e36fe59cf1f425
structure AvailableChain.FGSA.Run.HealthyPrefix₂ fcd1ea494c96f6f8
ctor AvailableChain.FGSA.Run.HealthyPrefix₂.mk ae5af6432fc46e3c
field AvailableChain.FGSA.Run.HealthyPrefix₂.base d8735ff796d49232
field AvailableChain.FGSA.Run.HealthyPrefix₂.cut da7b2a38216f952c
field AvailableChain.FGSA.Run.HealthyPrefix₂.healthy d3c6fbea73fb3502
field AvailableChain.FGSA.Run.HealthyPrefix₂.partBefore c9bf15be3b57385a
structure AvailableChain.FGSA.Run.CleanPrefix₂ 137fe6a521e4ae87
field AvailableChain.FGSA.Run.CleanPrefix₂.toHealthyPrefix₂ 10ffca6a897bea41
ctor AvailableChain.FGSA.Run.CleanPrefix₂.mk ad17203c0155c582
field AvailableChain.FGSA.Run.CleanPrefix₂.partAt 65c6cc9ad5a0d971
def AvailableChain.FGSA.Run.CleanCut₂ 05e91bba3e03c033
structure AvailableChain.FGSA.Run.Clean₂ b76da1599608d326
ctor AvailableChain.FGSA.Run.Clean₂.mk e123caa35c7c29db
field AvailableChain.FGSA.Run.Clean₂.pre b756d5e43a619944
field AvailableChain.FGSA.Run.Clean₂.gst 791912633c560565
structure AvailableChain.FGSA.Run.Recovery₂ dbe6a8a9459b34f2
field AvailableChain.FGSA.Run.Recovery₂.toRecoveryCore 925f64c94a0520b7
ctor AvailableChain.FGSA.Run.Recovery₂.mk de387bd1e6258d8c
field AvailableChain.FGSA.Run.Recovery₂.base 724deff3d67ca092
field AvailableChain.FGSA.Run.Recovery₂.fault a74932690ba9e806
field AvailableChain.FGSA.Run.Recovery₂.awake 2e222e5a79174b32
field AvailableChain.FGSA.Run.Recovery₂.gapPos 803f26e9ebee94a1
def AvailableChain.FGSA.Run.BaseSet 9d2d801f3332fb51
def AvailableChain.FGSA.Run.CleanSet d028e1f72b8763de
def AvailableChain.FGSA.Run.CleanCutSet e4ea1dfe21ec0e2c
def AvailableChain.FGSA.Run.CleanPrefixSet 6f4b81d48a21005f
def AvailableChain.FGSA.Run.HealingSet 6ece8957359955c6
structure AvailableChain.FGSA.Run.FinalitySet 11b22669a9d0bb13
ctor AvailableChain.FGSA.Run.FinalitySet.mk a56cd62bd371f480
field AvailableChain.FGSA.Run.FinalitySet.core 725c7228ebc1897c
field AvailableChain.FGSA.Run.FinalitySet.recur 2d3c54bd376352ef
structure AvailableChain.FGSA.Run.Outage₂ d15c12e34590f092
ctor AvailableChain.FGSA.Run.Outage₂.mk ce16554b094e0674
field AvailableChain.FGSA.Run.Outage₂.pre a287b69a0376ae7b
field AvailableChain.FGSA.Run.Outage₂.sleepy b7216e32195b5f9a
field AvailableChain.FGSA.Run.Outage₂.order 33b4db4a66b0a808
field AvailableChain.FGSA.Run.Outage₂.lag 5529976283200c10
field AvailableChain.FGSA.Run.Outage₂.budget d7d01d61462d4197
field AvailableChain.FGSA.Run.Outage₂.fastPart 4d9de1c4a0e09622
def AvailableChain.FGSA.Run.OutageSet 589ed4790c2fe4c9
```

### `AvailableChainFGSAClaims.Statements.Windows`

```text
def AvailableChain.FGSA.Run.WinSpec f24d30ce59abf57d
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
def AvailableChain.FGSA.Run.cleanWinAt 7a4ed9ee271877d6
def AvailableChain.FGSA.Run.cleanWin f5b21c2e43a97cfb
def AvailableChain.FGSA.Run.cleanPrefixWin ca77ab851b39d8ef
def AvailableChain.FGSA.Run.cleanLabelWin 644a34cbe668098a
def AvailableChain.FGSA.Run.gapWin 249801f69201217a
def AvailableChain.FGSA.Run.formWin 1aa195c308f7c125
def AvailableChain.FGSA.Run.formWinAt 4b4823f46a0a376c
def AvailableChain.FGSA.Run.kernelWin eeceff4632e80ceb
def AvailableChain.FGSA.Run.trigWin 4ebab3ed21cf57cc
def AvailableChain.FGSA.Run.outWin 4ecaf12f1dd1e83a
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
def AvailableChain.FGSA.Run.oldRowHeights a34a998df6b93384
def AvailableChain.FGSA.Run.muOf 6afbba12978bc0c7
def AvailableChain.FGSA.Run.high 137ca53654e215bf
def AvailableChain.FGSA.Run.honestFrontier 72120fe1de55c189
def AvailableChain.FGSA.Run.HeightRow 5a9f642a06a65447
structure AvailableChain.FGSA.Run.H0Reset 1294b9cc245cd42d
ctor AvailableChain.FGSA.Run.H0Reset.mk bf7120d39de1316c
field AvailableChain.FGSA.Run.H0Reset.rG_after 863ee678ecf4a1d5
field AvailableChain.FGSA.Run.H0Reset.rG_first 15af8af9a9c78674
field AvailableChain.FGSA.Run.H0Reset.cut 23adebaa7fd4c761
field AvailableChain.FGSA.Run.H0Reset.frontier c5cb892dcee48a40
field AvailableChain.FGSA.Run.H0Reset.rowCap a3324652c7fa81c3
field AvailableChain.FGSA.Run.H0Reset.mu_le decc3daa9eb13b87
field AvailableChain.FGSA.Run.H0Reset.cut_lower 9f101beb3ecc5158
field AvailableChain.FGSA.Run.H0Reset.cut_upper 36f6eedf485b1c83
field AvailableChain.FGSA.Run.H0Reset.reset_row f6a1b54b3f19b692
field AvailableChain.FGSA.Run.H0Reset.reset_first 1ab9f02cf4aa7b14
field AvailableChain.FGSA.Run.H0Reset.label 74b1f45b2a699da3
field AvailableChain.FGSA.Run.H0Reset.fresh 8cb783265c792b91
field AvailableChain.FGSA.Run.H0Reset.synchronous f69f103831be85f2
structure AvailableChain.FGSA.Run.H0 806049c29cdb0dc5
field AvailableChain.FGSA.Run.H0.toH0Reset fbc155348302fcbd
ctor AvailableChain.FGSA.Run.H0.mk 32c54234db5851ad
field AvailableChain.FGSA.Run.H0.proposal_lower b144b4cebef96ff4
field AvailableChain.FGSA.Run.H0.proposal f4ca207c72a009c9
field AvailableChain.FGSA.Run.H0.proposal_first 4b94bb7436ce4794
field AvailableChain.FGSA.Run.H0.after_gst b1a3058e9bd1147f
field AvailableChain.FGSA.Run.H0.source_prefix 74f09723bea3c61d
def AvailableChain.FGSA.Run.tstarOf 08e2657de55ba9c4
```

