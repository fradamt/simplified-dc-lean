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
Stale allow lines fail. Put later fields in new structures unless a named
exception below permits the exact aggregate change.

## WC plan r2.1 aggregate exception

Lead ruling 2026-10-05, WC plan r2.1, §8 Job 4; DC: SAME source witness order.
Append exactly one field after `cleanGrowth` in `AvailableChain.FGSA.Run.FGSAClaims`:
`weakContinuationLive : ∀ G : Time, WeakContinuationLiveClaim p G`.
The permitted delta is this aggregate, its constructor, every existing generated
projection, and the new field entry. Each changed frozen entry has one measured
allow line. The new field is additive and needs no frozen allowance.
Root fills the field with the complete WC proof and the closed H-time producer.
`fgsaClaims (p) : FGSAClaims p` stays hypothesis-free. The live-to-safety adapter
stays in Shared/Claims. Source non-vacuity still requires `4 * p.Δ ≤ G`.
No other frozen entry changes under this exception. Preserve the frozen file
bytes and SHA. All earlier exception records still apply.

## ROOT-DIGEST-2 option-3 exception

ROOT-DIGEST-2, option 3, 2026-10-04. Full identity means equality of recursive NamedProposal,
including each ancestor's body, signed rows, raw HEAD list, and support list. This supersedes
root-digest-plan r2's body-only limitation and its instruction to retain the old ContentAgree.
The exception permits the exact N/A/H/E/Q changes in root-digest2-plan §4.1, the 64-entry generic
mode delta in §9, and their measured representation dependencies. It permits exact named-parent
admission and root-identifier HEAD handling in the shared GridCO base, with legacy block-mode
behavior retained for the deferred protocols. The closed fgsaClaims type, all claim fields,
numerical bounds, original observation scopes, and prior named exceptions remain. Each changed
frozen entry must have an old/new type or hash and a cause. No frozen baseline or SHA is replaced.

## ROOT-DIGEST W1c class exception

The [Gen exception list](GEN-API.md#root-digest-option-3-exception) names all four frozen walk
entries and their kernel evidence under plan r2.1 and r2.2. No frozen FG-SA walk entry needs a
new premise. The non-frozen `AvailableChain.FGSA.fgsa_headInTree_reanchor_of_pivot` now takes
root uniqueness on its arbitrary `tree`. CStoreInv supplies this for each erasedList view.
The census is `.lake/rdw1c-census.md`. FGSAClaims fields and Base₂ text are unchanged by W1c.
W3 has migrated `AvailableChainFGSA.Tests.Support`. Final manifest generation waits for W2.
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
inductive AvailableChain.FGSA.Reachable b8ebe90e84f54451
ctor AvailableChain.FGSA.Reachable.init 3eac19650fcdc2cf
ctor AvailableChain.FGSA.Reachable.tick 90a34c7f00023bec
ctor AvailableChain.FGSA.Reachable.deliver 719465d9a5f61c82
def AvailableChain.FGSA.NestOK 33ad573c238f8a2f
def AvailableChain.FGSA.SACompat c4047629eda6178e
def AvailableChain.FGSA.LeaseBelowOutputStore 5a26063b06ffa2b3
theorem AvailableChain.FGSA.LeaseBelowOutputStore_def eb04df6daba0bcc7
def AvailableChain.FGSA.FastOrigin a060b278304561e6
structure AvailableChain.FGSA.CStoreInv cb980d5cc624cc81
ctor AvailableChain.FGSA.CStoreInv.mk 7dbdcf83111fdc21
field AvailableChain.FGSA.CStoreInv.fg c1deb7786fb3d7eb
field AvailableChain.FGSA.CStoreInv.rootInj bb704c9e61292aff
field AvailableChain.FGSA.CStoreInv.baseTree 03a6ba0feaea5526
field AvailableChain.FGSA.CStoreInv.saCompat bb90981a09bbbfcf
field AvailableChain.FGSA.CStoreInv.Smem 36136e441223d8d5
field AvailableChain.FGSA.CStoreInv.fastOrigin 1c55ea1227a90e90
field AvailableChain.FGSA.CStoreInv.fastDom 06f389d97cd62401
field AvailableChain.FGSA.CStoreInv.genuineKeys 710fd01d0cfd5c00
field AvailableChain.FGSA.CStoreInv.leaseKeys 07eb8bd41ac0489c
def AvailableChain.FGSA.Inv0 ff334c1483718cab
structure AvailableChain.FGSA.MetaInv f45d5aef38f40570
ctor AvailableChain.FGSA.MetaInv.mk 53dc0ab2c18cda32
field AvailableChain.FGSA.MetaInv.wireTree 504b601c11f0758a
field AvailableChain.FGSA.MetaInv.treeWire 8f520c74259a4688
field AvailableChain.FGSA.MetaInv.proposalsNodup f11e7a262bfecc18
field AvailableChain.FGSA.MetaInv.stampKeys 91b08b3725ff1b75
field AvailableChain.FGSA.MetaInv.blocksNodup 1ee4473d396dce9d
field AvailableChain.FGSA.MetaInv.poolDecodes fb10c17a18b86c58
field AvailableChain.FGSA.MetaInv.poolNodup 17f1d74196004c20
field AvailableChain.FGSA.MetaInv.noGenesisWire 642062fc8864b40a
def AvailableChain.FGSA.ContentAgree f5ead200f3526dd2
```

### `AvailableChainFGSA.Statements.Store`

```text
def AvailableChain.FGSA.OutputNestingStored e186acf4b7f53a78
def AvailableChain.FGSA.StoreInvariant 89801cbcfec46fed
structure AvailableChain.FGSA.StoreBundle 867f0e9c7427b71f
ctor AvailableChain.FGSA.StoreBundle.mk 8f25d5f3d68a092c
field AvailableChain.FGSA.StoreBundle.cstore f854db2e029ec633
field AvailableChain.FGSA.StoreBundle.meta fb08046851103ce5
field AvailableChain.FGSA.StoreBundle.nest 359244bfc55aca26
field AvailableChain.FGSA.StoreBundle.lease 7f394be9d8c9c17f
def AvailableChain.FGSA.StoreBundleInvariant a01298cc3d076602
theorem AvailableChain.FGSA.StoreBundleInvariant_def 033611f02e57a446
def AvailableChain.FGSA.FMonotone b2e0a19659fd5948
def AvailableChain.FGSA.MetadataInvariant e01cbd59d6dc4650
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
def AvailableChain.FGSA.Run.fgsaAC 517d61b7ecd57024
```

### `AvailableChainFGSARun.Statements.Acceptance`

```text
def AvailableChain.FGSA.Run.fgsaAdmissionTime bedfcddab6bbb51e
def AvailableChain.FGSA.Run.fgsaTimely 5044aee82cfb94ef
def AvailableChain.FGSA.Run.fgsaAcceptanceInv ba55a152bf76f1d0
def AvailableChain.FGSA.Run.fgsaTrigger 30c0c4eda97644c7
```

### `AvailableChainFGSARun.Statements.Client`

```text
def AvailableChain.FGSA.Run.EmitsRow fd577ef85a0a2d95
def AvailableChain.FGSA.Run.EmittedRowsNoSlash 2f0118499d236b8f
def AvailableChain.FGSA.Run.decodeRowObject 35e2c252c32a9ecd
def AvailableChain.FGSA.Run.fgClientEvent 6193655d7e4e41ba
def AvailableChain.FGSA.Run.fgClientEvents d841fa48e50caf20
```

### `AvailableChainFGSARun.Statements.Emission`

```text
def AvailableChain.FGSA.Run.EmissionRowsValid 4d0f72aeedade33f
def AvailableChain.FGSA.Run.decode c06272443aaec6cb
def AvailableChain.FGSA.Run.HonestEmissionWellFormed c18e98eb0cce11f7
def AvailableChain.FGSA.Run.HonestProposalDecodes 56f282b52afecaf2
def AvailableChain.FGSA.Run.HeadTargetAtEmission 200e1c001b1fde8b
```

### `AvailableChainFGSARun.Statements.Excludes`

```text
inductive AvailableChain.FGSA.Run.EpochStep 7dc1af808a60ee8b
ctor AvailableChain.FGSA.Run.EpochStep.deliver 5f3326534c3223b5
ctor AvailableChain.FGSA.Run.EpochStep.clock 744759b146a785e7
def AvailableChain.FGSA.Run.Epoch 05624c24e911bc05
def AvailableChain.FGSA.Run.excludesFixed d078abd01e68b82e
```

### `AvailableChainFGSARun.Statements.Interface`

```text
def AvailableChain.FGSA.Run.isRowObject 32e8f31ea396b155
theorem AvailableChain.FGSA.Run.isRowObject_def 58e7750cdba35442
def AvailableChain.FGSA.Run.fgsaDelay 00fcdbeb68f38c80
theorem AvailableChain.FGSA.Run.fgsaDelay_def 79c81256b4dd243e
def AvailableChain.FGSA.Run.fgsaInterface dfc933192366d562
def AvailableChain.FGSA.Run.fgsaOutputs 4c4f60eb1d9ffcf4
def AvailableChain.FGSA.Run.finalizedOut 24ed8491960825ab
```

### `AvailableChainFGSARun.Statements.ReceiptCoverage`

```text
structure AvailableChain.FGSA.Run.ReceiptCoveragePremises 466e3f5350f8c29a
ctor AvailableChain.FGSA.Run.ReceiptCoveragePremises.mk 2bf52d5f67bc8b42
field AvailableChain.FGSA.Run.ReceiptCoveragePremises.within 2e056349f6b554d1
field AvailableChain.FGSA.Run.ReceiptCoveragePremises.slotWindow 92ec2e6378e9b0df
field AvailableChain.FGSA.Run.ReceiptCoveragePremises.compat 17b5504f060fcd65
field AvailableChain.FGSA.Run.ReceiptCoveragePremises.deadline 96162a4c61717829
def AvailableChain.FGSA.Run.ReceiptCoverageStatement 3846a79abb6ad9e5
theorem AvailableChain.FGSA.Run.ReceiptCoverageStatement_def 72cc86976db2eb30
```

### `AvailableChainFGSARun.Statements.Receipts`

```text
def AvailableChain.FGSA.Run.blockOf? 1eb10aaed544fcb1
```

### `AvailableChainFGSARun.Statements.Roots`

```text
def AvailableChain.FGSA.Run.DirectNamedProposalInRun d254cdec64f6c6d2
def AvailableChain.FGSA.Run.NamedProposalInRun 1320714817529438
structure AvailableChain.FGSA.Run.NamedRootCollisionFree 035673ee1c72744a
ctor AvailableChain.FGSA.Run.NamedRootCollisionFree.mk cbf0679b3f248bec
field AvailableChain.FGSA.Run.NamedRootCollisionFree.root_injective ba2aa52c5e510d48
def AvailableChain.FGSA.Run.DirectRootBlockInRun d47318901411df79
def AvailableChain.FGSA.Run.RootBlockInRun cc3cb8c1d3a6b8bb
```

### `AvailableChainFGSARun.Statements.Slashing`

```text
def AvailableChain.FGSA.Run.fgsaEvidence 1b9808a1a59c7fca
def AvailableChain.FGSA.Run.fgsaSlashing cf55acb40a4f1278
```

## `AvailableChainFGSAClaims`

### `AvailableChainFGSAClaims.Claims.Clean`

```text
def AvailableChain.FGSA.Run.CleanHistoryAt 3339a2407f0974b6
def AvailableChain.FGSA.Run.CleanGateAt 49c50712c67e0ccb
def AvailableChain.FGSA.Run.CleanTruncAt 8d0a1d5d92755a95
def AvailableChain.FGSA.Run.CleanSafetyAt db4650ea58a01643
def AvailableChain.FGSA.Run.CleanCutClaim bf21227f8d10ea93
def AvailableChain.FGSA.Run.CleanCutZeroClaim 4bc1ed741af0aa74
def AvailableChain.FGSA.Run.CleanHistoryClaim e05dea4a9ea92e3b
def AvailableChain.FGSA.Run.CleanPrefixTruncationClaim c5b5dbe373f3ef20
def AvailableChain.FGSA.Run.CleanSafetyClaim d5d8b49212e5f5e1
def AvailableChain.FGSA.Run.CleanCutPosClaim 548dcd10c9a79d82
```

### `AvailableChainFGSAClaims.Claims.Finality`

```text
def AvailableChain.FGSA.Run.FinalityKernelClaim_W 4c9272288d1d3ed6
def AvailableChain.FGSA.Run.KernelACSideClaim_W df69a20f8c8af5c5
def AvailableChain.FGSA.Run.FinalityKernelJoinedClaim_W 0c904da56f4ec488
def AvailableChain.FGSA.Run.TailKernelClaim_W f652bebcd468271d
def AvailableChain.FGSA.Run.FinalityLivenessConcl_W af2e24061f24689f
def AvailableChain.FGSA.Run.FirstFinalityConcl_W 03c7f6f55ffea7fb
def AvailableChain.FGSA.Run.ProposalFinalConcl_W b003c96c65a6fe1d
def AvailableChain.FGSA.Run.AboveFrontierConcl_W 45562d752a4cc0b1
def AvailableChain.FGSA.Run.FirstFinalityRecFEClaim_W 2058ab29ad89456b
def AvailableChain.FGSA.Run.FirstFinalityRecF4Claim_W 34f7ba8ef879e9ae
def AvailableChain.FGSA.Run.FinalityLivenessRecFEClaim_W 9c901ab5a08a19b4
def AvailableChain.FGSA.Run.FinalityLivenessRecF4Claim_W 1f53a41104ff381b
def AvailableChain.FGSA.Run.ProposalFinalRecFEClaim_W c659f0e3c6e1b842
def AvailableChain.FGSA.Run.ProposalFinalRecF4Claim_W d6511c7688e70a67
def AvailableChain.FGSA.Run.AboveFrontierRecFEClaim_W 86c872a29e12c6fb
def AvailableChain.FGSA.Run.AboveFrontierRecF4Claim_W 4cdb9df0eb300083
def AvailableChain.FGSA.Run.FinalityLivenessGSTClaim_W 83a4b839e4a7763f
def AvailableChain.FGSA.Run.ProposalFinalGSTClaim_W 457d7a396d3b7ac7
def AvailableChain.FGSA.Run.AboveFrontierGSTClaim_W a97636ebf91c2f9c
```

### `AvailableChainFGSAClaims.Claims.Foundations`

```text
def AvailableChain.FGSA.Run.ClientSafeAll d99b52aec19a190e
def AvailableChain.FGSA.Run.ClientSafetyClaim a7352160f95201f0
def AvailableChain.FGSA.Run.ClientSafetyBaseClaim 818ea498991e52c5
def AvailableChain.FGSA.Run.FGFoundationClaim ea2999aa2c5922b2
def AvailableChain.FGSA.Run.SrcFrameAboveClaim 4837514b7babbaa0
def AvailableChain.FGSA.Run.RunFGBlock 60bfb0a38c01ddac
def AvailableChain.FGSA.Run.CarrierAt f8cbd373fc246044
def AvailableChain.FGSA.Run.StoreAt b7d2fc82a011ae2f
def AvailableChain.FGSA.Run.ActiveViewAt 0892caade3823412
def AvailableChain.FGSA.Run.LeaseOriginsAt be55c65822aeff50
def AvailableChain.FGSA.Run.SourceDisciplineBaseAt 547ade9a6d77f5c8
def AvailableChain.FGSA.Run.SourceDisciplineAt 1871a71553ef13f0
def AvailableChain.FGSA.Run.CarrierClaim 7109c56af78f8c4a
def AvailableChain.FGSA.Run.ChainCertificatesAt 415737e559245cb1
def AvailableChain.FGSA.Run.ChainCertificatesClaim 07d71b1123c7d77c
def AvailableChain.FGSA.Run.StoreClaim 8be36ed2cdb90a77
def AvailableChain.FGSA.Run.ActiveViewClaim 32291503abadd2ec
def AvailableChain.FGSA.Run.LeaseOriginsClaim 433cd45420c04fb8
def AvailableChain.FGSA.Run.ReconcileAt d85ad555266125ac
def AvailableChain.FGSA.Run.ReconcileClaim 86f26349759a5962
def AvailableChain.FGSA.Run.OutputNestingAt a2af90b371ca259b
def AvailableChain.FGSA.Run.OutputNestingClaim c54322f0d790125d
def AvailableChain.FGSA.Run.FrameAt 0e66347c16aafb70
def AvailableChain.FGSA.Run.FrameClaim 5a6d6f4e43644429
def AvailableChain.FGSA.Run.SourceDisciplineBaseClaim c02ce321d7d1e5b7
def AvailableChain.FGSA.Run.SourceDisciplineClaim 49c15b215c611c5a
def AvailableChain.FGSA.Run.RowServiceBaseClaim f552e578294f511d
def AvailableChain.FGSA.Run.RowServiceClaim b7988df4971b78da
def AvailableChain.FGSA.Run.PureAccountableClaim c8647a5737a4db34
def AvailableChain.FGSA.Run.PureAgreementClaim 18c8a1db5132d365
def AvailableChain.FGSA.Run.WholeRunAccountableClaim 58d8dce3fa0c5153
def AvailableChain.FGSA.Run.WholeRunAgreementClaim dcf6b79cf3c42a54
def AvailableChain.FGSA.Run.EventPrefixAgreementClaim 1e589de395eec331
def AvailableChain.FGSA.Run.FaultCountSlashableBoundClaim d67c93f189f136c2
def AvailableChain.FGSA.Run.FinalizedMonotonicityClaim 2ed938de757502c0
def AvailableChain.FGSA.Run.HonestNeverSlashedClaim c57e208e12a7297c
def AvailableChain.FGSA.Run.FinalizedSafetyConcl 65c6a96ef65bf7f4
def AvailableChain.FGSA.Run.FinalizedSafetyClaim ec0fd49cccf9b5dd
def AvailableChain.FGSA.Run.FinalLockClaim e59705c6c1c10391
```

### `AvailableChainFGSAClaims.Claims.Healing`

```text
def AvailableChain.FGSA.Run.RowPermissionAt cfd2ee6179a69e89
def AvailableChain.FGSA.Run.RowPermissionClaim 9762b962beabc737
def AvailableChain.FGSA.Run.HealingInputClaim 61f653ed25ae00d9
def AvailableChain.FGSA.Run.HTimeConcl 3c022a5700a83800
def AvailableChain.FGSA.Run.HTimeClaim 64f390ecf80ea7a3
def AvailableChain.FGSA.Run.ResetArrivalConcl 1a4a33940590e551
def AvailableChain.FGSA.Run.ResetArrivalClaim f8fdeac7530cb399
def AvailableChain.FGSA.Run.RenewedPromotionConcl 000b536670af5987
def AvailableChain.FGSA.Run.RenewedPromotionClaim 71309ef1f406fcf5
def AvailableChain.FGSA.Run.HTimeBestClaim 12634e4ab8e2f9d9
def AvailableChain.FGSA.Run.HTimeSearchClaim 63a9ef1d4381736f
```

### `AvailableChainFGSAClaims.Claims.Outage`

```text
def AvailableChain.FGSA.Run.ExactProposalAt 5bfe4ec7dbd5b338
def AvailableChain.FGSA.Run.ExactProposalClaim 3b335755a2a92a04
def AvailableChain.FGSA.Run.InclusionPostGateAt c13dfe58beee1867
def AvailableChain.FGSA.Run.InclusionAt db3859715298dcaa
def AvailableChain.FGSA.Run.CleanInclusionPostGateClaim 0f19b61f0a8fe835
def AvailableChain.FGSA.Run.CleanInclusionClaim a2c7b3071257e4a5
def AvailableChain.FGSA.Run.DutiesExtendOn fe87ec7c439fadc6
def AvailableChain.FGSA.Run.FCompatBefore e4572eb465cb25ce
def AvailableChain.FGSA.Run.P1Concl 3fdff004a3e9147b
def AvailableChain.FGSA.Run.LeaseOrFFrom 86fa9f285d9877cc
def AvailableChain.FGSA.Run.OutageCompatAt d9b5b5ec4855a0a4
def AvailableChain.FGSA.Run.OutageCompatClaim 9710aaf3a7b28f26
def AvailableChain.FGSA.Run.FastP1Claim e07a41c0e0b410fa
def AvailableChain.FGSA.Run.SlowP1Claim ccd307719db620ff
def AvailableChain.FGSA.Run.AvailableFromConcl 7df465927046452f
def AvailableChain.FGSA.Run.AvailableGrowthConcl 361d4e2a89d61370
def AvailableChain.FGSA.Run.AvailableGSTClaim 877c76b8e4a48363
def AvailableChain.FGSA.Run.AvailableGrowthGSTClaim 6072041819bb7c8b
def AvailableChain.FGSA.Run.CleanGrowthClaim ad27d9e2270c1a56
```

### `AvailableChainFGSAClaims.Claims.OutageContinuation`

```text
def AvailableChain.FGSA.Run.OutageContinuationClaim 4486260beeae6bd1
```

### `AvailableChainFGSAClaims.Claims.Shared`

```text
def AvailableChain.FGSA.Run.SameLabelAt 20de187bff3346de
def AvailableChain.FGSA.Run.SameLabelClaim 718f60490a8cef91
def AvailableChain.FGSA.Run.HeadReachesLoAt cb7ed7d1a16e1810
def AvailableChain.FGSA.Run.HeadReachesLoClaim 56ea7b30b6b29155
def AvailableChain.FGSA.Run.ReleaseStoreAt 285defc3d4981499
def AvailableChain.FGSA.Run.ReleaseStoreClaim 25351981b7e88ffa
def AvailableChain.FGSA.Run.ReleaseAt 9ad9599a6d919e1d
def AvailableChain.FGSA.Run.ReleaseClaim 4efcfc6ebf094234
```

### `AvailableChainFGSAClaims.Claims.WeakContinuation`

```text
def AvailableChain.FGSA.Run.WeakContinuationClaim 86a0139ab94ac9ce
def AvailableChain.FGSA.Run.WeakContinuationLiveClaim 8a7a0b669ed803e8
```

### `AvailableChainFGSAClaims.Claims.WeakContinuationGrowth`

```text
def AvailableChain.FGSA.Run.WeakContinuationGrowthClaim 01892b3a7e006e51
```

### `AvailableChainFGSAClaims.FGSAClaims`

```text
structure AvailableChain.FGSA.Run.FGSASafetyClaims d85fe886dc58ec97
ctor AvailableChain.FGSA.Run.FGSASafetyClaims.mk b8267d66b2664d5f
field AvailableChain.FGSA.Run.FGSASafetyClaims.carrier 2525ec259f492800
field AvailableChain.FGSA.Run.FGSASafetyClaims.chainCertificates 802d7892e455bc75
field AvailableChain.FGSA.Run.FGSASafetyClaims.store 34d59aae6f4d2634
field AvailableChain.FGSA.Run.FGSASafetyClaims.activeView 0d176f473c1ff043
field AvailableChain.FGSA.Run.FGSASafetyClaims.leaseOrigins a7e7e652cdb54096
field AvailableChain.FGSA.Run.FGSASafetyClaims.reconcile e1306dbe56026d3a
field AvailableChain.FGSA.Run.FGSASafetyClaims.outputNesting fc2bf423ff4e41dd
field AvailableChain.FGSA.Run.FGSASafetyClaims.frame 1ca55ef1328988f2
field AvailableChain.FGSA.Run.FGSASafetyClaims.clientSafety 94132d98757ae472
field AvailableChain.FGSA.Run.FGSASafetyClaims.clientSafetyBase 6b7bb8d3c2985c03
field AvailableChain.FGSA.Run.FGSASafetyClaims.sourceDisciplineBase 25c622dad28dcf5f
field AvailableChain.FGSA.Run.FGSASafetyClaims.sourceDiscipline e58c5612b954a73d
field AvailableChain.FGSA.Run.FGSASafetyClaims.sameLabel f8d706ead92470a7
field AvailableChain.FGSA.Run.FGSASafetyClaims.releaseStore f39c41361b9b6e94
field AvailableChain.FGSA.Run.FGSASafetyClaims.release 122151730a0fe32d
field AvailableChain.FGSA.Run.FGSASafetyClaims.headReachesLo 63e2e4a3e799eb35
field AvailableChain.FGSA.Run.FGSASafetyClaims.cleanCut 3f8b6a1c9826360b
field AvailableChain.FGSA.Run.FGSASafetyClaims.cleanHistory 9552daaa5ca778c0
field AvailableChain.FGSA.Run.FGSASafetyClaims.cleanPrefixTruncation ef2be349f94ca310
field AvailableChain.FGSA.Run.FGSASafetyClaims.cleanSafety 6ea03f208953b952
structure AvailableChain.FGSA.Run.FGSASafetyInterfaces 14fb23196a1266dc
ctor AvailableChain.FGSA.Run.FGSASafetyInterfaces.mk 00b47b484a8f7acb
field AvailableChain.FGSA.Run.FGSASafetyInterfaces.fgFoundation e5128885ec9bc6a4
field AvailableChain.FGSA.Run.FGSASafetyInterfaces.srcFrameAbove c7445217f6d63864
field AvailableChain.FGSA.Run.FGSASafetyInterfaces.cpPrefix 401121e05db7dbe6
field AvailableChain.FGSA.Run.FGSASafetyInterfaces.cpCompat fa4da9b899e10a11
field AvailableChain.FGSA.Run.FGSASafetyInterfaces.tSrc 4fcbe7129566c839
field AvailableChain.FGSA.Run.FGSASafetyInterfaces.labelBound 4c3e49bec0e20c35
field AvailableChain.FGSA.Run.FGSASafetyInterfaces.timingContract 4e663fc50493a012
structure AvailableChain.FGSA.Run.FGSAFinalityClaims 18115678535d959c
ctor AvailableChain.FGSA.Run.FGSAFinalityClaims.mk d8b1ba7c4800011b
field AvailableChain.FGSA.Run.FGSAFinalityClaims.accountable 01b5be78a14eb034
field AvailableChain.FGSA.Run.FGSAFinalityClaims.agreement 926e58e3ef5c01ff
field AvailableChain.FGSA.Run.FGSAFinalityClaims.runAccountable 6856b3c9b7bb43c4
field AvailableChain.FGSA.Run.FGSAFinalityClaims.runAgreement acb5ad84aa89149d
field AvailableChain.FGSA.Run.FGSAFinalityClaims.eventPrefixAgreement 928d617af7a48849
field AvailableChain.FGSA.Run.FGSAFinalityClaims.faultCountSlashableBound d71971b17d7b1bbc
field AvailableChain.FGSA.Run.FGSAFinalityClaims.finalizedMonotone c203bcc84666adf1
field AvailableChain.FGSA.Run.FGSAFinalityClaims.honestNeverSlashed 88cbce8179191455
structure AvailableChain.FGSA.Run.FGSAClaims d8b2bb6875cfa430
field AvailableChain.FGSA.Run.FGSAClaims.toFGSASafetyClaims 958e9ddf34deb309
ctor AvailableChain.FGSA.Run.FGSAClaims.mk fe7d357de128923d
field AvailableChain.FGSA.Run.FGSAClaims.finality 2767f89208e4a6c5
field AvailableChain.FGSA.Run.FGSAClaims.finalizedSafety 170d891e9f223730
field AvailableChain.FGSA.Run.FGSAClaims.finalLock 49e04391d4bffc35
field AvailableChain.FGSA.Run.FGSAClaims.outageCompat 6e598a19d5f11745
field AvailableChain.FGSA.Run.FGSAClaims.fastP1 dfc0f00643876b45
field AvailableChain.FGSA.Run.FGSAClaims.slowP1 289ddf7104e52c7e
field AvailableChain.FGSA.Run.FGSAClaims.exactProposal b25125d06744813a
field AvailableChain.FGSA.Run.FGSAClaims.cleanInclusionPostGate 4a53e1900d52e84d
field AvailableChain.FGSA.Run.FGSAClaims.cleanInclusion 19b10b1e7dc4537a
field AvailableChain.FGSA.Run.FGSAClaims.firstFinalityRecFE f2a31ad6a788f54e
field AvailableChain.FGSA.Run.FGSAClaims.firstFinalityRecF4 5b8733a809487fad
field AvailableChain.FGSA.Run.FGSAClaims.finalityLivenessGSTRecFE ed9bd332a7201d16
field AvailableChain.FGSA.Run.FGSAClaims.finalityLivenessGSTRecF4 1d80107d67bce41c
field AvailableChain.FGSA.Run.FGSAClaims.proposalFinalGSTRecFE 7cf97be145941833
field AvailableChain.FGSA.Run.FGSAClaims.proposalFinalGSTRecF4 a13f0d766391a450
field AvailableChain.FGSA.Run.FGSAClaims.aboveFrontierGSTRecFE 5d23e0e64923c9cc
field AvailableChain.FGSA.Run.FGSAClaims.aboveFrontierGSTRecF4 744012b26cc85fa0
field AvailableChain.FGSA.Run.FGSAClaims.availableGST de755e826b4ac0d2
field AvailableChain.FGSA.Run.FGSAClaims.availableGrowthGST 44a0f9534e819916
field AvailableChain.FGSA.Run.FGSAClaims.cleanGrowth 3610f9c12a1e5239
field AvailableChain.FGSA.Run.FGSAClaims.weakContinuationLive 3d2e6dc505d159dc
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
def AvailableChain.FGSA.Run.RCarrierView b3ee79d34bfcb404
theorem AvailableChain.FGSA.Run.RCarrierView_def 6a0386012b18d28d
def AvailableChain.FGSA.Run.RStore 47919556c657266a
theorem AvailableChain.FGSA.Run.RStore_def e110e7d7eb5fee35
def AvailableChain.FGSA.Run.RActive 479446cde30cdd84
theorem AvailableChain.FGSA.Run.RActive_def 39953bd518c1091d
def AvailableChain.FGSA.Run.RStoreCumul 94d927d5b9df0bcd
theorem AvailableChain.FGSA.Run.RStoreCumul_def 34455641e93d0f70
def AvailableChain.FGSA.Run.RMono 52341a206628869d
theorem AvailableChain.FGSA.Run.RMono_def 3b538eed0123daef
def AvailableChain.FGSA.Run.RFrameExact 0bdfefed335429f9
theorem AvailableChain.FGSA.Run.RFrameExact_def 46df11334d932fb9
def AvailableChain.FGSA.Run.RFrame 579c2c4d2c67a97e
theorem AvailableChain.FGSA.Run.RFrame_def 5ef217e04b2361cf
def AvailableChain.FGSA.Run.RGeo d02a86338f4e5c93
theorem AvailableChain.FGSA.Run.RGeo_def 341d83ce718f7850
def AvailableChain.FGSA.Run.RCert ba38f9f3377df989
theorem AvailableChain.FGSA.Run.RCert_def 20c5fc10cde1587f
def AvailableChain.FGSA.Run.RRec 126bc948580d9e82
theorem AvailableChain.FGSA.Run.RRec_def 53447b3b8b0f15dc
def AvailableChain.FGSA.Run.TSrc 044bf4cb0a015a64
theorem AvailableChain.FGSA.Run.TSrc_def 5316ad2933d50398
def AvailableChain.FGSA.Run.LabelBound 3642123c29146e88
theorem AvailableChain.FGSA.Run.LabelBound_def df08b8aa68880d43
def AvailableChain.FGSA.Run.TChain c82bed73b5dd26d0
theorem AvailableChain.FGSA.Run.TChain_def b78e13102974b527
def AvailableChain.FGSA.Run.TCompat 27e1aa699c016e5d
theorem AvailableChain.FGSA.Run.TCompat_def 793a731ba170e8cd
structure AvailableChain.FGSA.Run.AncestorClosed a82d5e35de829ed2
ctor AvailableChain.FGSA.Run.AncestorClosed.mk fa2827ea0465c6d5
field AvailableChain.FGSA.Run.AncestorClosed.down 6a9b1aab4f3ebb3e
def AvailableChain.FGSA.Run.FrameBelow d170caf7c923ca81
theorem AvailableChain.FGSA.Run.FrameBelow_def b261817e5cd74fb3
def AvailableChain.FGSA.Run.RStrat 8deae5edcf9b146c
theorem AvailableChain.FGSA.Run.RStrat_def ad68c38a154da92e
def AvailableChain.FGSA.Run.RQCOrigin 867dd348b2420d81
theorem AvailableChain.FGSA.Run.RQCOrigin_def 374c498c715805ce
def AvailableChain.FGSA.Run.SrcFrameAbove c5c978cf02ea346d
theorem AvailableChain.FGSA.Run.SrcFrameAbove_def 588ecd71ef717e15
def AvailableChain.FGSA.Run.SrcFrame 738f1892f154a4bf
def AvailableChain.FGSA.Run.SrcFrameAboveStmt 993ac1f6ff36788f
theorem AvailableChain.FGSA.Run.SrcFrameAboveStmt_def f7fa3be05f7df121
def AvailableChain.FGSA.Run.CPPrefix 416694407259064f
theorem AvailableChain.FGSA.Run.CPPrefix_def 1d80c3a6eec49e83
def AvailableChain.FGSA.Run.CPCompat a0125976b5b18d70
theorem AvailableChain.FGSA.Run.CPCompat_def acdd5ad686af121f
def AvailableChain.FGSA.Run.RXing 224970f7b2762a27
def AvailableChain.FGSA.Run.RCap e9319f42516f2227
def AvailableChain.FGSA.Run.THigh de07614eb279e73a
def AvailableChain.FGSA.Run.TCarrier f60ba80d9d7fbb4f
def AvailableChain.FGSA.Run.TRowsSelect 0bee25914977877f
def AvailableChain.FGSA.Run.TRowsSync 0ce7623d6c36cfba
def AvailableChain.FGSA.Run.TRowsReceipt f865ef71ed1e52b1
theorem AvailableChain.FGSA.Run.TRowsReceipt_def 3ec8f5d30a20b5a5
structure AvailableChain.FGSA.Run.TRows 40e3861f17c65c30
ctor AvailableChain.FGSA.Run.TRows.mk 88217cf3c10e83c5
field AvailableChain.FGSA.Run.TRows.select 977379289217ad1d
field AvailableChain.FGSA.Run.TRows.sync 9dfe8b7620fe0235
field AvailableChain.FGSA.Run.TRows.receipt e884c09fc3859e4e
def AvailableChain.FGSA.Run.SourceBefore e413a3c650c24e6d
def AvailableChain.FGSA.Run.Kept 368ec3d50e474499
def AvailableChain.FGSA.Run.KeepOrCause 42d881a1191bc212
def AvailableChain.FGSA.Run.RExcl 6276c6bb9fc5b4bb
def AvailableChain.FGSA.Run.RKeep e267bb257d5ce655
def AvailableChain.FGSA.Run.RFProv 0024d15347354ae8
def AvailableChain.FGSA.Run.TDel ef040011dd5d0b26
def AvailableChain.FGSA.Run.TDelReset 39743b8cf5f78ac6
def AvailableChain.FGSA.Run.TGeom 6abf4ecbd31034cd
def AvailableChain.FGSA.Run.ExactService d02c052e4fb8f18a
def AvailableChain.FGSA.Run.PhaseInterval 210a48bc15bbb165
def AvailableChain.FGSA.Run.Transfers 41b35dc05da60e94
def AvailableChain.FGSA.Run.PhaseBody 23ce64cab0e771e0
def AvailableChain.FGSA.Run.TPerm 370495ef228a3848
def AvailableChain.FGSA.Run.ProposalGap c57b5f7b44322abe
def AvailableChain.FGSA.Run.RepairAfter 01feadfc4583a957
def AvailableChain.FGSA.Run.TRepair 5fddd820d15e0e36
def AvailableChain.FGSA.Run.OpeningCovered 8c843426d597bf4a
def AvailableChain.FGSA.Run.OpeningEntry 8299eff2680b9fb9
def AvailableChain.FGSA.Run.TCommon c1add80b3e235768
def AvailableChain.FGSA.Run.TFrontier 08fa3ae9bb6b2c48
def AvailableChain.FGSA.Run.FinalityRowCarriage ebb404f308fa40e5
theorem AvailableChain.FGSA.Run.FinalityRowCarriage_def 401e9643261771eb
```

### `AvailableChainFGSAClaims.Statements.Channels`

```text
def AvailableChain.FGSA.Run.certified 80e4a3693bf2d89c
theorem AvailableChain.FGSA.Run.certified_def a5d675c89a272887
def AvailableChain.FGSA.Run.treeT 2b69ec7b0e57e60e
def AvailableChain.FGSA.Run.treeErased b78204b44e3c46cd
def AvailableChain.FGSA.Run.frameR 395107f87e1057e7
def AvailableChain.FGSA.Run.domainR 4161e11ed74ec34d
def AvailableChain.FGSA.Run.finR aac46ba18b4700c2
def AvailableChain.FGSA.Run.FAdvance 295788c25e134f22
def AvailableChain.FGSA.Run.sourceCandidates ea2b20c12ea3f181
def AvailableChain.FGSA.Run.jointSource 0c24947a4c7a783b
def AvailableChain.FGSA.Run.proposerHead b9b8415a6df36962
def AvailableChain.FGSA.Run.outputS 1d0f4a9dbb766c1e
theorem AvailableChain.FGSA.Run.outputS_def 78e519431fcc26cb
theorem AvailableChain.FGSA.Run.frameR_def 46870ba5dac194b2
theorem AvailableChain.FGSA.Run.jointSource_def 884a9f045b72de73
theorem AvailableChain.FGSA.Run.sourceCandidates_def 7cd6a98c9f1d7d5a
theorem AvailableChain.FGSA.Run.domainR_def 729fb9eaa24e05a3
theorem AvailableChain.FGSA.Run.treeT_def 3acc17fc60e79846
theorem AvailableChain.FGSA.Run.proposerHead_def 23840b24f59e59b6
theorem AvailableChain.FGSA.Run.FAdvance_def 910b82c4a0274160
def AvailableChain.FGSA.Run.R_at 4f7d96998b31fa17
def AvailableChain.FGSA.Run.D_at e356dee5388df8e7
def AvailableChain.FGSA.Run.FAdvanceAt d06c98bf7872b719
def AvailableChain.FGSA.Run.candidatesAt 07ad0774410a2c89
def AvailableChain.FGSA.Run.proposalHeadAt 6540cec168f36c19
def AvailableChain.FGSA.Run.actionHead fc5c78fe126be972
def AvailableChain.FGSA.Run.actionTriple 17b4a3729e36e652
def AvailableChain.FGSA.Run.namedEntry a50c73e0c7ee36db
def AvailableChain.FGSA.Run.EntryBelow 70f4e667e4654e34
def AvailableChain.FGSA.Run.RowSigner ca5008030c0041d5
def AvailableChain.FGSA.Run.HonestRowAt 6aa6b423adb4fb57
def AvailableChain.FGSA.Run.HonestRowBefore 4520e3ef3c9577ea
theorem AvailableChain.FGSA.Run.HonestRowBefore_def 99d7d51b460ad76e
def AvailableChain.FGSA.Run.RowComplete 4aafbb8f09202a49
def AvailableChain.FGSA.Run.HonestCarrier 3437d2cddfcf647a
def AvailableChain.FGSA.Run.HeldAt 31cedc366f5cfa9d
def AvailableChain.FGSA.Run.BlockInRunBefore 75322d18a8b0e9db
theorem AvailableChain.FGSA.Run.RowSigner_def 6acb929e1493f01e
theorem AvailableChain.FGSA.Run.HonestRowAt_def 454ab80286414b68
def AvailableChain.FGSA.Run.rowHeld b4f2f67df3ca81ea
def AvailableChain.FGSA.Run.proposalStateAt 216ed0e0f8651247
def AvailableChain.FGSA.Run.heldAtProposal c8f9071842c3b8e7
def AvailableChain.FGSA.Run.onParentChain a73c22862abe8850
def AvailableChain.FGSA.Run.HeldBefore 8a18471e6c50d04a
def AvailableChain.FGSA.Run.ValidForParent e3900faa73bcf5aa
theorem AvailableChain.FGSA.Run.ValidForParent_def d046d93a70b9d113
def AvailableChain.FGSA.Run.HeightMatch c8ba28c2f779aacc
theorem AvailableChain.FGSA.Run.HeightMatch_def 37f7e18c398bd1f8
def AvailableChain.FGSA.Run.headAtLabel 6bc8f82127a2e652
theorem AvailableChain.FGSA.Run.RowComplete_def 2182859446593099
theorem AvailableChain.FGSA.Run.HonestCarrier_def a5a034591a5c8926
theorem AvailableChain.FGSA.Run.HeldAt_def 8d52287d8682e40d
theorem AvailableChain.FGSA.Run.namedEntry_def f3827e3bef137733
```

### `AvailableChainFGSAClaims.Statements.ComposeStmt`

```text
def AvailableChain.FGSA.Run.windowIdx e47c962b5cec7ce6
structure AvailableChain.FGSA.Run.TimingContract e0ae7c4d6ad48a55
ctor AvailableChain.FGSA.Run.TimingContract.mk 476b0bad079d0a1e
field AvailableChain.FGSA.Run.TimingContract.rowLag 2d1a1ba0fc29015d
field AvailableChain.FGSA.Run.TimingContract.certLag d63fe2aabcdd1210
field AvailableChain.FGSA.Run.TimingContract.label 866412fc66d096cc
field AvailableChain.FGSA.Run.TimingContract.atomic 6ee599c7fed1c704
field AvailableChain.FGSA.Run.TimingContract.tickFG a99925814e6b18b6
structure AvailableChain.FGSA.Run.FGFoundation 53e868554b22feb1
ctor AvailableChain.FGSA.Run.FGFoundation.mk 932525ec6bfde269
field AvailableChain.FGSA.Run.FGFoundation.store 1133ef4754e244f0
field AvailableChain.FGSA.Run.FGFoundation.cumul 6579275db70b2b12
field AvailableChain.FGSA.Run.FGFoundation.mono dfd90d9aca8b4dea
field AvailableChain.FGSA.Run.FGFoundation.frame 4275284b459ad83b
field AvailableChain.FGSA.Run.FGFoundation.geo 9958b41b46b0c0c8
field AvailableChain.FGSA.Run.FGFoundation.strat 9f70a3237df82483
field AvailableChain.FGSA.Run.FGFoundation.reconcile f4fc37672a2b6676
def AvailableChain.FGSA.Run.TStart b1e91001758b6a7d
def AvailableChain.FGSA.Run.FullVoteService 891184abc5df42b0
def AvailableChain.FGSA.Run.TVote ef6ede9e96745920
def AvailableChain.FGSA.Run.WalkBatch 853eff513447e8f8
def AvailableChain.FGSA.Run.TWalk 9c14fc2a41eb0494
structure AvailableChain.FGSA.Run.CoreServices 752de3e0b2f4043f
ctor AvailableChain.FGSA.Run.CoreServices.mk b6b662392ce9dd7a
field AvailableChain.FGSA.Run.CoreServices.start afd2d399653eb813
field AvailableChain.FGSA.Run.CoreServices.vote 83d96000551bd4df
field AvailableChain.FGSA.Run.CoreServices.walk 8ac4a6d330a33b2f
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
def AvailableChain.FGSA.Run.ResetArrivalStatement f113f6c628363e35
theorem AvailableChain.FGSA.Run.ResetArrivalStatement_def c9bf11bc66ddf03b
def AvailableChain.FGSA.Run.ResetArrivalFullStatement d9718b61fabda387
theorem AvailableChain.FGSA.Run.ResetArrivalFullStatement_def 03ee19568603944c
structure AvailableChain.FGSA.Run.KernelPt 9235f1fbc5c48477
ctor AvailableChain.FGSA.Run.KernelPt.mk 32c96b623cc6f691
field AvailableChain.FGSA.Run.KernelPt.w 6cbd0d7075070f20
field AvailableChain.FGSA.Run.KernelPt.r e581c6d88b7635d7
def AvailableChain.FGSA.Run.kernelStart 5b40679c7bd5d7f8
def AvailableChain.FGSA.Run.OpeningCarrier_W 88b013a6f3fdeeed
theorem AvailableChain.FGSA.Run.OpeningCarrier_W_def 065f9bb08304db05
def AvailableChain.FGSA.Run.KernelConclusion_W f864ba83776e4f15
theorem AvailableChain.FGSA.Run.KernelConclusion_W_def 04d49ffd79f520d9
structure AvailableChain.FGSA.Run.KernelPrem_W 6357137cbee89f20
ctor AvailableChain.FGSA.Run.KernelPrem_W.mk a88c1987e250ac7d
field AvailableChain.FGSA.Run.KernelPrem_W.set b3e3d8ed77fa4d10
field AvailableChain.FGSA.Run.KernelPrem_W.bound 05f1996e7bc135e2
field AvailableChain.FGSA.Run.KernelPrem_W.window 90b71aaab8030d63
field AvailableChain.FGSA.Run.KernelPrem_W.start 6800478defe6d46f
field AvailableChain.FGSA.Run.KernelPrem_W.hhor f7f67e8ba8fd9a5c
field AvailableChain.FGSA.Run.KernelPrem_W.input 8173b64ef9d33014
field AvailableChain.FGSA.Run.KernelPrem_W.services 5361ef03d3ea5134
structure AvailableChain.FGSA.Run.TailKernelPt b330d4900d1ca7d6
ctor AvailableChain.FGSA.Run.TailKernelPt.mk 41cdd6cb6261ae64
field AvailableChain.FGSA.Run.TailKernelPt.w b55caf984a16e648
field AvailableChain.FGSA.Run.TailKernelPt.r 4006ca4b73b3c4a7
field AvailableChain.FGSA.Run.TailKernelPt.carrier 62ca7b0096b16566
field AvailableChain.FGSA.Run.TailKernelPt.U 5b648aaa4a87357a
structure AvailableChain.FGSA.Run.TailKernelPrem_W 815dec615b98122e
ctor AvailableChain.FGSA.Run.TailKernelPrem_W.mk 89d53bc76eabe1ee
field AvailableChain.FGSA.Run.TailKernelPrem_W.set 70672d31908b5484
field AvailableChain.FGSA.Run.TailKernelPrem_W.bound d1c37c089d76c084
field AvailableChain.FGSA.Run.TailKernelPrem_W.input 51a771740adf5db7
field AvailableChain.FGSA.Run.TailKernelPrem_W.start ff09e6ec3dc7deb7
field AvailableChain.FGSA.Run.TailKernelPrem_W.window be1a05e5b33ea046
field AvailableChain.FGSA.Run.TailKernelPrem_W.carrier e616e2f670fcef87
field AvailableChain.FGSA.Run.TailKernelPrem_W.high 220b60e7114f08a2
field AvailableChain.FGSA.Run.TailKernelPrem_W.cover b850fbceae884853
field AvailableChain.FGSA.Run.TailKernelPrem_W.hhor abf37d0835369858
structure AvailableChain.FGSA.Run.HealTContract 13443ba3a76edcbb
ctor AvailableChain.FGSA.Run.HealTContract.mk 94d61bea2f3a182c
field AvailableChain.FGSA.Run.HealTContract.del d556845c18ccb1dd
field AvailableChain.FGSA.Run.HealTContract.delReset 6b5fbd2daa27e074
field AvailableChain.FGSA.Run.HealTContract.perm 39ecc70f98c5a4b8
field AvailableChain.FGSA.Run.HealTContract.repair 42aa1cd7db2f5d82
field AvailableChain.FGSA.Run.HealTContract.common e8fb887301d046e6
field AvailableChain.FGSA.Run.HealTContract.frontier aec902726e9fd1db
field AvailableChain.FGSA.Run.HealTContract.geom 359d6a28bc670a1f
def AvailableChain.FGSA.Run.frontierAtIdx e30099ac19ba28f9
def AvailableChain.FGSA.Run.TopEvidence ab2e51ca8e9d1534
def AvailableChain.FGSA.Run.ContestEvidence dd76952754c37761
def AvailableChain.FGSA.Run.EffectiveEvent 792050fd42ab84e6
def AvailableChain.FGSA.Run.AttemptPhaseAt aa71bf549795934e
def AvailableChain.FGSA.Run.ServedFrontier 57d7b42dc94d5828
def AvailableChain.FGSA.Run.AttemptValid ee66ab10ec81e82a
def AvailableChain.FGSA.Run.attemptBudget b92a1475dc2a8a8b
def AvailableChain.FGSA.Run.AttemptEndsBy 7baaa9dd89024b21
def AvailableChain.FGSA.Run.SettledPhaseFrame 362bcbb7ba51ca7e
theorem AvailableChain.FGSA.Run.SettledPhaseFrame_def 2350c57f4b2aabd0
def AvailableChain.FGSA.Run.RPhase c6aae53ba917c7ce
theorem AvailableChain.FGSA.Run.RPhase_def e90acbfb1058b729
structure AvailableChain.FGSA.Run.HealRContract 4e287a0c74235efb
ctor AvailableChain.FGSA.Run.HealRContract.mk b4dd0f2546d846e7
field AvailableChain.FGSA.Run.HealRContract.xing 6ba60c2b7908261d
field AvailableChain.FGSA.Run.HealRContract.cap 6f35860d9d4dd121
field AvailableChain.FGSA.Run.HealRContract.phase 83112002ae00b825
field AvailableChain.FGSA.Run.HealRContract.excl 4fd283314ff3253b
field AvailableChain.FGSA.Run.HealRContract.keep c223432f67d0dc24
field AvailableChain.FGSA.Run.HealRContract.fprov 119dfae96fc8aafd
def AvailableChain.FGSA.Run.ProgressAttemptStatement 58cc8a677646ecde
theorem AvailableChain.FGSA.Run.ProgressAttemptStatement_def 171344516fa2bae5
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
def AvailableChain.FGSA.Run.FinalityBlock cfbb9ad88b44a531
theorem AvailableChain.FGSA.Run.FinalityBlock_def 184df157211c9881
def AvailableChain.FGSA.Run.finalityRows 0095a1b4bd82114d
theorem AvailableChain.FGSA.Run.finalityRows_def 33877122b770dbb3
def AvailableChain.FGSA.Run.FinalitySlashableBound 3fe697449ff3b7e6
theorem AvailableChain.FGSA.Run.FinalitySlashableBound_def 2354c56b42c5d2b0
def AvailableChain.FGSA.Run.FinalityExecution 64cb1ca09c582fc4
theorem AvailableChain.FGSA.Run.FinalityExecution_def 926b19ca6cd9ff71
def AvailableChain.FGSA.Run.WholeRunAccountable a656472744572293
theorem AvailableChain.FGSA.Run.WholeRunAccountable_def 29b1f0e7882927a7
def AvailableChain.FGSA.Run.WholeRunAgreement 71a7833b670014e9
theorem AvailableChain.FGSA.Run.WholeRunAgreement_def 3b2553aea404a2b7
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
def AvailableChain.FGSA.Run.honestSeats 92ae8f68c75eb12e
theorem AvailableChain.FGSA.Run.rowHeight_def 770f0d6454ee9f76
theorem AvailableChain.FGSA.Run.eventTime_def 58ef7b966e9699ec
theorem AvailableChain.FGSA.Run.honestSeats_def 7f24813bf5940b99
def AvailableChain.FGSA.Run.ChainRowsBefore 88cf39a928d5f3bd
structure AvailableChain.FGSA.Run.PreBatchPrem 761b5311861f031f
ctor AvailableChain.FGSA.Run.PreBatchPrem.mk 1be09952cc0440ba
field AvailableChain.FGSA.Run.PreBatchPrem.base b3328d2c47511ea6
field AvailableChain.FGSA.Run.PreBatchPrem.faultQ 68883ff478d323e5
field AvailableChain.FGSA.Run.PreBatchPrem.entry 17c1b92be9eb401a
field AvailableChain.FGSA.Run.PreBatchPrem.path f4382597007b3ac7
field AvailableChain.FGSA.Run.PreBatchPrem.cut 9e2f0cf5ea592be9
field AvailableChain.FGSA.Run.PreBatchPrem.early dc489bee94ac8eda
field AvailableChain.FGSA.Run.PreBatchPrem.rows 5053bbf42b22ab0c
field AvailableChain.FGSA.Run.PreBatchPrem.noRow 7e4898c6798ef5eb
def AvailableChain.FGSA.Run.NoMixedPreBatchParent 8139bba66b96028e
structure AvailableChain.FGSA.Run.BatchPrem 66c462550f10a5b9
ctor AvailableChain.FGSA.Run.BatchPrem.mk e08f4786033ee5d4
field AvailableChain.FGSA.Run.BatchPrem.base e7101b14aad6d753
field AvailableChain.FGSA.Run.BatchPrem.faultQ 5b8344cdf5c37b79
field AvailableChain.FGSA.Run.BatchPrem.deltaF 4e640da3e41c94a3
field AvailableChain.FGSA.Run.BatchPrem.rowsReceipt 13a34cf9c16b227b
field AvailableChain.FGSA.Run.BatchPrem.horizon 657f267d419174fa
field AvailableChain.FGSA.Run.BatchPrem.carrier c32dae4a593a934c
field AvailableChain.FGSA.Run.BatchPrem.after bef1a5ad862adc52
field AvailableChain.FGSA.Run.BatchPrem.valid c80f89b463e28b3c
field AvailableChain.FGSA.Run.BatchPrem.entry ebc846eb1bd51f0d
field AvailableChain.FGSA.Run.BatchPrem.path 4f5f56d7900b6422
field AvailableChain.FGSA.Run.BatchPrem.above 119199a4f6d58991
def AvailableChain.FGSA.Run.BatchCoverage df1864fff76060d1
theorem AvailableChain.FGSA.Run.JustifiedCross_def df81b827b773af75
theorem AvailableChain.FGSA.Run.MixedCross_def 9bb1a7e85401f709
theorem AvailableChain.FGSA.Run.foldTrichotomy_def 132834b174b22f9b
theorem AvailableChain.FGSA.Run.StoredProgressConsume_def 36cd5ccc9859c367
def AvailableChain.FGSA.Run.FinRowNames 94adce64d3029936
def AvailableChain.FGSA.Run.FinalityCoveredByChild_W 643922320c84f168
def AvailableChain.FGSA.Run.FinalityNames 6502008fb69955a7
structure AvailableChain.FGSA.Run.FinalityBatchPrem_W bcdef18c7a7f0567
ctor AvailableChain.FGSA.Run.FinalityBatchPrem_W.mk d744630993100b91
field AvailableChain.FGSA.Run.FinalityBatchPrem_W.base 1509d666b20036bd
field AvailableChain.FGSA.Run.FinalityBatchPrem_W.faultQ 6a66268f307aaa8f
field AvailableChain.FGSA.Run.FinalityBatchPrem_W.deltaF cf46cd64b503ab37
field AvailableChain.FGSA.Run.FinalityBatchPrem_W.rowsReceipt 9483d65bb13092f6
field AvailableChain.FGSA.Run.FinalityBatchPrem_W.carrier f61bcc82e9a43973
field AvailableChain.FGSA.Run.FinalityBatchPrem_W.after 05f762e91413e8d8
field AvailableChain.FGSA.Run.FinalityBatchPrem_W.horizon 13a2e0b64b06be8b
field AvailableChain.FGSA.Run.FinalityBatchPrem_W.parent 12bf6fc72551e2a4
field AvailableChain.FGSA.Run.FinalityBatchPrem_W.birth 606d65774a1365bd
field AvailableChain.FGSA.Run.FinalityBatchPrem_W.retainedOrCovered b2bedd89928bc55f
field AvailableChain.FGSA.Run.FinalityBatchPrem_W.batch b23282dbc237ec42
def AvailableChain.FGSA.Run.FinalityBatchCoverage_W bdfa14a9fb32c71b
structure AvailableChain.FGSA.Run.PendingFold_W 5f973f39dc1fdc9c
ctor AvailableChain.FGSA.Run.PendingFold_W.mk 05cc06274674b236
field AvailableChain.FGSA.Run.PendingFold_W.child 8966d5943b8bb5c5
field AvailableChain.FGSA.Run.PendingFold_W.cover 9f4386d5fd82c86d
theorem AvailableChain.FGSA.Run.FinalityCoveredByChild_W_def b949f1a305ead8fa
theorem AvailableChain.FGSA.Run.FinRowNames_def ed158b1dc934a188
theorem AvailableChain.FGSA.Run.FinalityNames_def 008a06cf02c71175
theorem AvailableChain.FGSA.Run.FinalityBatchCoverage_W_def 970563a98c533bf4
```

### `AvailableChainFGSAClaims.Statements.Healed`

```text
def AvailableChain.FGSA.Run.healStart 8c43e1bb6db01456
def AvailableChain.FGSA.Run.HealSuffix 2968e93d9c2e793a
def AvailableChain.FGSA.Run.Healed ff5f2686ca7c6eae
def AvailableChain.FGSA.Run.H2A 7cd1259fa219fb4b
def AvailableChain.FGSA.Run.H2Prime 4c69ef789883c29c
def AvailableChain.FGSA.Run.H3 011df4b88719ebbf
def AvailableChain.FGSA.Run.H4 a3ffd1895ff3b684
def AvailableChain.FGSA.Run.H5RawTransfer 67adcc38d1b5f336
def AvailableChain.FGSA.Run.H6GateService a143d8005ab40fdc
structure AvailableChain.FGSA.Run.HealT 2c7cd59d63483235
ctor AvailableChain.FGSA.Run.HealT.mk aeef31e6b04bb8ff
field AvailableChain.FGSA.Run.HealT.h1 d8fcc223af6664ca
field AvailableChain.FGSA.Run.HealT.h2 516803c4e198724e
field AvailableChain.FGSA.Run.HealT.rows e110cdc32074068d
structure AvailableChain.FGSA.Run.HealAC 014942e3e5e7363c
ctor AvailableChain.FGSA.Run.HealAC.mk b8c8374f71beb117
field AvailableChain.FGSA.Run.HealAC.h2A bb58b5e7ef2d9323
field AvailableChain.FGSA.Run.HealAC.h2' 97cbd54338919dba
field AvailableChain.FGSA.Run.HealAC.h3 66c7be0ab4ff9cc3
field AvailableChain.FGSA.Run.HealAC.h4 9fe7aa0d9a092432
field AvailableChain.FGSA.Run.HealAC.h5 c3f92a80a9c2b274
field AvailableChain.FGSA.Run.HealAC.h6 9441ec5075ad3095
structure AvailableChain.FGSA.Run.HealingInput 509d0300e33c207c
ctor AvailableChain.FGSA.Run.HealingInput.mk 451101fed76fddf9
field AvailableChain.FGSA.Run.HealingInput.healed a028e1ff29b31adc
field AvailableChain.FGSA.Run.HealingInput.wit e1b6ffb0029f3b33
field AvailableChain.FGSA.Run.HealingInput.t ff486c8eea78aabe
field AvailableChain.FGSA.Run.HealingInput.ac f944927472ef39df
def AvailableChain.FGSA.Run.HTimeStatement ae2f57261247a9b7
theorem AvailableChain.FGSA.Run.HTimeStatement_def 17d0b285068bd017
theorem AvailableChain.FGSA.Run.HealSuffix_def 29e6169e3c5e9b48
theorem AvailableChain.FGSA.Run.healStart_def 71d0955cb1c27cc1
```

### `AvailableChainFGSAClaims.Statements.HealedBest`

```text
def AvailableChain.FGSA.Run.HTimeBestConcl e18f99790f165442
theorem AvailableChain.FGSA.Run.HTimeBestConcl_def 045ebfdf65e62ddb
```

### `AvailableChainFGSAClaims.Statements.LiveDC`

```text
def AvailableChain.FGSA.Run.liveDCDeadline_W 98bb35b3a856b670
theorem AvailableChain.FGSA.Run.liveDCDeadline_W_def 69c7b1824c4488b2
def AvailableChain.FGSA.Run.LiveDCConcl_W ce5564d01ca16ad3
theorem AvailableChain.FGSA.Run.LiveDCConcl_W_def cc3dbb918c460c62
def AvailableChain.FGSA.Run.LiveDCFromWindowsStatement be831f6ababf21c5
theorem AvailableChain.FGSA.Run.LiveDCFromWindowsStatement_def 185bd932cb7c9d84
```

### `AvailableChainFGSAClaims.Statements.OutageContinuation`

```text
def AvailableChain.FGSA.Run.OutageLengthV df9f8cdb53ebe336
theorem AvailableChain.FGSA.Run.OutageLengthV_def a5143e0190facb37
structure AvailableChain.FGSA.Run.OutageContinuationPrem f325410a0e482ea2
ctor AvailableChain.FGSA.Run.OutageContinuationPrem.mk 362c4888743b42db
field AvailableChain.FGSA.Run.OutageContinuationPrem.pre 6a88f3ea3a8b686b
field AvailableChain.FGSA.Run.OutageContinuationPrem.sleepy fa900c719e641893
field AvailableChain.FGSA.Run.OutageContinuationPrem.order eec10cb9f3e2f476
field AvailableChain.FGSA.Run.OutageContinuationPrem.lag 8752be0fcb6f16f1
field AvailableChain.FGSA.Run.OutageContinuationPrem.lengthV 990ecc883b6b0b89
field AvailableChain.FGSA.Run.OutageContinuationPrem.fastPart 3c9bbb1603278916
field AvailableChain.FGSA.Run.OutageContinuationPrem.sync 329dcddd442f7a43
field AvailableChain.FGSA.Run.OutageContinuationPrem.gst 028325cea697bed2
field AvailableChain.FGSA.Run.OutageContinuationPrem.partAfter b944594b942273f9
def AvailableChain.FGSA.Run.OutageContinuationConcl 64658e60df285c44
```

### `AvailableChainFGSAClaims.Statements.OutputReads`

```text
def AvailableChain.FGSA.Run.ServedFromGateAt b44e2bddf051f50d
theorem AvailableChain.FGSA.Run.ServedFromGateAt_def 6fe447444d36d480
def AvailableChain.FGSA.Run.JointGrowthAt 2e43df612254ea9e
theorem AvailableChain.FGSA.Run.JointGrowthAt_def 96445960ba4c90b9
```

### `AvailableChainFGSAClaims.Statements.Packages.Finality`

```text
inductive AvailableChain.FGSA.Run.FinFormW e65aa35faec5d780
ctor AvailableChain.FGSA.Run.FinFormW.recFE f5bdcad089b74a37
ctor AvailableChain.FGSA.Run.FinFormW.recF4 9740b2983363dec5
def AvailableChain.FGSA.Run.FinFormW.holdsW 4649365580aa48ae
theorem AvailableChain.FGSA.Run.FinFormW.holdsW_def 0c25c65a15eb1f5b
structure AvailableChain.FGSA.Run.FinalitySet_W a2059e3bf2781a51
ctor AvailableChain.FGSA.Run.FinalitySet_W.mk cbf5a70663a61d71
field AvailableChain.FGSA.Run.FinalitySet_W.core bc8c898d35a42c00
field AvailableChain.FGSA.Run.FinalitySet_W.bound e43058afdddd04cb
field AvailableChain.FGSA.Run.FinalitySet_W.recur d99edde7b57e8ec3
def AvailableChain.FGSA.Run.finalityWindow_W 257edaf1d0233a74
theorem AvailableChain.FGSA.Run.finalityWindow_W_def 7713675ab497d5a2
structure AvailableChain.FGSA.Run.FirstFinalityPrem_W 03249abe60568507
ctor AvailableChain.FGSA.Run.FirstFinalityPrem_W.mk c533bb0edf74338c
field AvailableChain.FGSA.Run.FirstFinalityPrem_W.set 4a9bb2fd99306f72
field AvailableChain.FGSA.Run.FirstFinalityPrem_W.hhor 8aa30fbba1446dc9
structure AvailableChain.FGSA.Run.FinalityLivenessPrem_W d4e5095ef44eff53
ctor AvailableChain.FGSA.Run.FinalityLivenessPrem_W.mk 19e1c955425b1014
field AvailableChain.FGSA.Run.FinalityLivenessPrem_W.set cd7b9632f7cb4e76
field AvailableChain.FGSA.Run.FinalityLivenessPrem_W.input 1dc4d67f57984dd9
field AvailableChain.FGSA.Run.FinalityLivenessPrem_W.start 5ebba954f43e92d4
field AvailableChain.FGSA.Run.FinalityLivenessPrem_W.hhor 19a43dee193879dd
structure AvailableChain.FGSA.Run.ProposalFinalPrem_W d48fc65c7761ac10
ctor AvailableChain.FGSA.Run.ProposalFinalPrem_W.mk 8efb80fafae22c81
field AvailableChain.FGSA.Run.ProposalFinalPrem_W.set e3762b3109d76c74
field AvailableChain.FGSA.Run.ProposalFinalPrem_W.input 349358ef46541ff7
field AvailableChain.FGSA.Run.ProposalFinalPrem_W.prop 2d5f053224f28d0d
field AvailableChain.FGSA.Run.ProposalFinalPrem_W.start 3bca1d43fe44206a
field AvailableChain.FGSA.Run.ProposalFinalPrem_W.hhor 84ce763d6bb23fb3
structure AvailableChain.FGSA.Run.AboveFrontierPrem_W 420f18f350a3b2c1
ctor AvailableChain.FGSA.Run.AboveFrontierPrem_W.mk 5a0f0f0c0c3cabb0
field AvailableChain.FGSA.Run.AboveFrontierPrem_W.set a53ada53875774d3
field AvailableChain.FGSA.Run.AboveFrontierPrem_W.input 115215194fe7b4db
field AvailableChain.FGSA.Run.AboveFrontierPrem_W.start 4fcc8e233f74163c
field AvailableChain.FGSA.Run.AboveFrontierPrem_W.firstHorizon 811a36b9d04d9943
field AvailableChain.FGSA.Run.AboveFrontierPrem_W.hhor 8acd259af8cde455
```

### `AvailableChainFGSAClaims.Statements.Packages.FinalityGST`

```text
structure AvailableChain.FGSA.Run.FinalityLivenessGSTPrem_W 8cf0ca0661d7dfc9
ctor AvailableChain.FGSA.Run.FinalityLivenessGSTPrem_W.mk b5a5119d01319b37
field AvailableChain.FGSA.Run.FinalityLivenessGSTPrem_W.set 5cc945800a3ffcf5
field AvailableChain.FGSA.Run.FinalityLivenessGSTPrem_W.late 7d8767a61fac4f63
field AvailableChain.FGSA.Run.FinalityLivenessGSTPrem_W.hhor 6249b9e31c20c426
structure AvailableChain.FGSA.Run.ProposalFinalGSTPrem_W ace3b7a7abc5337b
ctor AvailableChain.FGSA.Run.ProposalFinalGSTPrem_W.mk 38965d9c39b6d200
field AvailableChain.FGSA.Run.ProposalFinalGSTPrem_W.set 055b36c7868eaa29
field AvailableChain.FGSA.Run.ProposalFinalGSTPrem_W.prop 77252b79c5a2fd81
field AvailableChain.FGSA.Run.ProposalFinalGSTPrem_W.late 698845f9e0c24e44
field AvailableChain.FGSA.Run.ProposalFinalGSTPrem_W.hhor cd866d4a1e5de0d7
structure AvailableChain.FGSA.Run.AboveFrontierGSTPrem_W b4109fb14a168dd3
ctor AvailableChain.FGSA.Run.AboveFrontierGSTPrem_W.mk d95d11cbcc3820c3
field AvailableChain.FGSA.Run.AboveFrontierGSTPrem_W.set b2c3e73e8da4308a
field AvailableChain.FGSA.Run.AboveFrontierGSTPrem_W.late 5ab4be4e741c274d
field AvailableChain.FGSA.Run.AboveFrontierGSTPrem_W.hhor b2de8a6f9e0a328b
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
structure AvailableChain.FGSA.Run.HealingPrem 30b3e72f909dc7bb
ctor AvailableChain.FGSA.Run.HealingPrem.mk 51e8f74bdf175d70
field AvailableChain.FGSA.Run.HealingPrem.set c346d83a439e69c3
field AvailableChain.FGSA.Run.HealingPrem.bound 1a31ce55b97554f8
structure AvailableChain.FGSA.Run.HealingWitnessPrem 9568ab03e16e3eee
field AvailableChain.FGSA.Run.HealingWitnessPrem.toHealingPrem 555b44ae2024180e
ctor AvailableChain.FGSA.Run.HealingWitnessPrem.mk 51e5a6c1a4928ee1
field AvailableChain.FGSA.Run.HealingWitnessPrem.h0 8314469403473574
structure AvailableChain.FGSA.Run.HealingTimePrem 2dd6b748ad76de89
field AvailableChain.FGSA.Run.HealingTimePrem.toHealingPrem 1efa4a40d4f3fb78
ctor AvailableChain.FGSA.Run.HealingTimePrem.mk fc1419b83115bfff
field AvailableChain.FGSA.Run.HealingTimePrem.hhor ed6e2c4c71a2b593
structure AvailableChain.FGSA.Run.ResetArrivalPrem 17ac33740f3ba524
field AvailableChain.FGSA.Run.ResetArrivalPrem.toHealingPrem aaaa1cb7cfa5fbc5
ctor AvailableChain.FGSA.Run.ResetArrivalPrem.mk ce7fbb8e3611f86d
field AvailableChain.FGSA.Run.ResetArrivalPrem.hhor 7f15f7e664d529f4
structure AvailableChain.FGSA.Run.ResetArrivalFullPrem 24cb217489098b27
field AvailableChain.FGSA.Run.ResetArrivalFullPrem.toHealingPrem aee9ae1824aa794c
ctor AvailableChain.FGSA.Run.ResetArrivalFullPrem.mk eccc865d5b05203a
field AvailableChain.FGSA.Run.ResetArrivalFullPrem.hhor 71ac9d262928e621
structure AvailableChain.FGSA.Run.KernelJoinedPrem dfe878899c5687c6
ctor AvailableChain.FGSA.Run.KernelJoinedPrem.mk d96e86e6765e6894
field AvailableChain.FGSA.Run.KernelJoinedPrem.set e37366d375b03c6f
field AvailableChain.FGSA.Run.KernelJoinedPrem.bound 42f45d5ee1752696
field AvailableChain.FGSA.Run.KernelJoinedPrem.window 33f398556a85f08a
field AvailableChain.FGSA.Run.KernelJoinedPrem.start d9a0c8f65a3b8925
field AvailableChain.FGSA.Run.KernelJoinedPrem.hhor 6931165a45bcdd20
structure AvailableChain.FGSA.Run.HealingAttemptPrem ea42098dd84b076a
field AvailableChain.FGSA.Run.HealingAttemptPrem.toHealingPrem d9af68cccacadabf
ctor AvailableChain.FGSA.Run.HealingAttemptPrem.mk 500c27eb165a4677
field AvailableChain.FGSA.Run.HealingAttemptPrem.valid 039d4e6049b1e01d
field AvailableChain.FGSA.Run.HealingAttemptPrem.hhor 399ab95d302e92df
structure AvailableChain.FGSA.Run.HealingInputPrem fdad11e5b9cde541
field AvailableChain.FGSA.Run.HealingInputPrem.toHealingWitnessPrem 018ca69785cef0c7
ctor AvailableChain.FGSA.Run.HealingInputPrem.mk 9ce4c580b57a6412
field AvailableChain.FGSA.Run.HealingInputPrem.hhor 33b2c3f62afc5299
structure AvailableChain.FGSA.Run.RenewedPromotionPrem 5204b70d1581ea66
field AvailableChain.FGSA.Run.RenewedPromotionPrem.toHealingPrem eb982166fb01617b
ctor AvailableChain.FGSA.Run.RenewedPromotionPrem.mk 237095dd6d258e07
field AvailableChain.FGSA.Run.RenewedPromotionPrem.hhor 6f394153b39a3210
```

### `AvailableChainFGSAClaims.Statements.Packages.Inclusion`

```text
structure AvailableChain.FGSA.Run.CleanInclusionPrem 4c8c9764c3219d47
ctor AvailableChain.FGSA.Run.CleanInclusionPrem.mk 27442bfa6971c114
field AvailableChain.FGSA.Run.CleanInclusionPrem.set 3af35e03560380f7
field AvailableChain.FGSA.Run.CleanInclusionPrem.prop 0bd32b60dcec3965
field AvailableChain.FGSA.Run.CleanInclusionPrem.hhor 0e0c84a0e1525608
structure AvailableChain.FGSA.Run.ExactProposalPrem 7e87f0ea323b21e5
ctor AvailableChain.FGSA.Run.ExactProposalPrem.mk 1c99a7a0fd7371ee
field AvailableChain.FGSA.Run.ExactProposalPrem.set bc61075ccd4c9383
field AvailableChain.FGSA.Run.ExactProposalPrem.prop d88a92f4916928f1
field AvailableChain.FGSA.Run.ExactProposalPrem.hhor 790898a0017ed8b0
```

### `AvailableChainFGSAClaims.Statements.Packages.Outage`

```text
structure AvailableChain.FGSA.Run.OutagePrem 48ed624f0241662e
ctor AvailableChain.FGSA.Run.OutagePrem.mk 6b11331dd6b47576
field AvailableChain.FGSA.Run.OutagePrem.set c5b794eea3ed5fc1
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
structure AvailableChain.FGSA.Run.BasePrem 451b0fe4fd17d829
ctor AvailableChain.FGSA.Run.BasePrem.mk d1c5438a534f2c8f
field AvailableChain.FGSA.Run.BasePrem.set 5fca3893bd2c5323
structure AvailableChain.FGSA.Run.SameLabelPrem 435d2909b28a14e8
ctor AvailableChain.FGSA.Run.SameLabelPrem.mk 058c38a5a97d2322
field AvailableChain.FGSA.Run.SameLabelPrem.set 2c585638a507dd49
field AvailableChain.FGSA.Run.SameLabelPrem.sync 5d0853bb8579bc8e
structure AvailableChain.FGSA.Run.SourceDisciplinePrem e003239cf2ff50be
ctor AvailableChain.FGSA.Run.SourceDisciplinePrem.mk c1ab3d728b620e34
field AvailableChain.FGSA.Run.SourceDisciplinePrem.set ae7732ebc8c934f5
field AvailableChain.FGSA.Run.SourceDisciplinePrem.quorum 02aabe853d294d0c
structure AvailableChain.FGSA.Run.FinalizedSafetyPrem fed3766d2c583da8
ctor AvailableChain.FGSA.Run.FinalizedSafetyPrem.mk a89082cfb3986d8e
field AvailableChain.FGSA.Run.FinalizedSafetyPrem.set 0c6c1039568e6b17
field AvailableChain.FGSA.Run.FinalizedSafetyPrem.fault 8754f521911a420f
structure AvailableChain.FGSA.Run.CleanPrem 0ad3a1d51bae4ac1
ctor AvailableChain.FGSA.Run.CleanPrem.mk 4a5a2d035dd526de
field AvailableChain.FGSA.Run.CleanPrem.set 1ad15961eb8341df
structure AvailableChain.FGSA.Run.CleanPrefixPrem 994a18237f967a6c
ctor AvailableChain.FGSA.Run.CleanPrefixPrem.mk 1214127e9503ba9a
field AvailableChain.FGSA.Run.CleanPrefixPrem.set ef6d082c99eb5f9c
structure AvailableChain.FGSA.Run.CleanCutPrem b601ec8f714d2a21
ctor AvailableChain.FGSA.Run.CleanCutPrem.mk c7ea1b2a74ba9391
field AvailableChain.FGSA.Run.CleanCutPrem.set a4bc986a9541ac5b
structure AvailableChain.FGSA.Run.ReleasePrem 937187bb0ed58aa1
ctor AvailableChain.FGSA.Run.ReleasePrem.mk 639d40cb1f8f38d0
field AvailableChain.FGSA.Run.ReleasePrem.set ba1cb7e58b7b09ac
field AvailableChain.FGSA.Run.ReleasePrem.lt f2d9303ec87d71a8
```

### `AvailableChainFGSAClaims.Statements.Phases`

```text
def AvailableChain.FGSA.Run.finHeight 45ca642905486866
structure AvailableChain.FGSA.Run.FreshPrem a70644875f0b20ba
ctor AvailableChain.FGSA.Run.FreshPrem.mk b4747f025fe9e865
field AvailableChain.FGSA.Run.FreshPrem.base 68ba483365c76ebb
field AvailableChain.FGSA.Run.FreshPrem.faultQ 7e7a456313ecf091
field AvailableChain.FGSA.Run.FreshPrem.cut 4c71ef1791b0e6d9
field AvailableChain.FGSA.Run.FreshPrem.early 063180e4e82ee4b1
field AvailableChain.FGSA.Run.FreshPrem.rows 51b76257389259db
field AvailableChain.FGSA.Run.FreshPrem.noNextRow c06b53d064c71971
field AvailableChain.FGSA.Run.FreshPrem.noFinRow e4479917794df6da
def AvailableChain.FGSA.Run.JustifyAt 4f632ffc688bc358
def AvailableChain.FGSA.Run.JustifyFresh_W d4e1baff391aa5ac
def AvailableChain.FGSA.Run.Ready_W 92d61ac79e238ad3
def AvailableChain.FGSA.Run.receiptInsert_W ad63688422576031
structure AvailableChain.FGSA.Run.ReceiptWitness_W 96480f7d786199e2
ctor AvailableChain.FGSA.Run.ReceiptWitness_W.mk 1c433d7a0bb74541
field AvailableChain.FGSA.Run.ReceiptWitness_W.index d94469eb94339260
field AvailableChain.FGSA.Run.ReceiptWitness_W.time 4a999c5986ac6c0a
structure AvailableChain.FGSA.Run.BlockDelivery_W 45683347b6716eb4
ctor AvailableChain.FGSA.Run.BlockDelivery_W.mk ee0e86454c28e5f4
field AvailableChain.FGSA.Run.BlockDelivery_W.selected 2382828b738fe189
field AvailableChain.FGSA.Run.BlockDelivery_W.witness 28b4c53bb4fdf69f
structure AvailableChain.FGSA.Run.AcceptGuards_W 22c8f00c77dd721b
ctor AvailableChain.FGSA.Run.AcceptGuards_W.mk f9db8a4fa14ea99b
field AvailableChain.FGSA.Run.AcceptGuards_W.finCmp f03f8986ae032ea4
field AvailableChain.FGSA.Run.AcceptGuards_W.jPath 5b1f07dab57af6d4
field AvailableChain.FGSA.Run.AcceptGuards_W.cap 04ec6e3653a0cefb
structure AvailableChain.FGSA.Run.AcceptPrem_W b36f1eb0a12fa9a9
ctor AvailableChain.FGSA.Run.AcceptPrem_W.mk 43b409a9f740390a
field AvailableChain.FGSA.Run.AcceptPrem_W.base b5c1a86735d1e6f4
field AvailableChain.FGSA.Run.AcceptPrem_W.faultBound 898641b25549e465
field AvailableChain.FGSA.Run.AcceptPrem_W.finalized 3750b8213ecfef16
field AvailableChain.FGSA.Run.AcceptPrem_W.deliver c9d9c26d7a690d62
field AvailableChain.FGSA.Run.AcceptPrem_W.guards 82c549c9c2f3ad6c
field AvailableChain.FGSA.Run.AcceptPrem_W.horizon e83dd88e2b95cb6d
def AvailableChain.FGSA.Run.AcceptBefore_W e5e16683ead6b8ae
structure AvailableChain.FGSA.Run.FinalizePrem_W c2d60eaf88629b14
ctor AvailableChain.FGSA.Run.FinalizePrem_W.mk bed0592aa30c4e3a
field AvailableChain.FGSA.Run.FinalizePrem_W.fold 0de6025c88c2f7e4
field AvailableChain.FGSA.Run.FinalizePrem_W.base 121e66df5c9ce915
field AvailableChain.FGSA.Run.FinalizePrem_W.faultBound d6da0b9b18a149aa
field AvailableChain.FGSA.Run.FinalizePrem_W.deliver 9abcc71b87991199
field AvailableChain.FGSA.Run.FinalizePrem_W.guards 421d408ea59a7728
field AvailableChain.FGSA.Run.FinalizePrem_W.horizon 49c4f11d24fa3424
def AvailableChain.FGSA.Run.FinalizePending_W e1442c9323ac7ec4
theorem AvailableChain.FGSA.Run.JustifyAt_def cb9916438df18f33
theorem AvailableChain.FGSA.Run.JustifyFresh_W_def 0ea96edfff18d020
theorem AvailableChain.FGSA.Run.Ready_W_def 9552b8b43986fc9d
theorem AvailableChain.FGSA.Run.receiptInsert_W_def 6d4c1fa91b4da1a4
theorem AvailableChain.FGSA.Run.AcceptBefore_W_def 4b2b9ba2d6078397
theorem AvailableChain.FGSA.Run.FinalizePending_W_def 17ba1fc7daa69fa1
def AvailableChain.FGSA.Run.FreshFinalityRows_W 81755bdd90b61c5b
structure AvailableChain.FGSA.Run.TerminalCarriagePrem_W 17e7a63e1b36e618
ctor AvailableChain.FGSA.Run.TerminalCarriagePrem_W.mk c7da5216eaaeafa0
field AvailableChain.FGSA.Run.TerminalCarriagePrem_W.base 6b151c9be382db13
field AvailableChain.FGSA.Run.TerminalCarriagePrem_W.faultQ c0690622a5c90170
field AvailableChain.FGSA.Run.TerminalCarriagePrem_W.deltaF 9fac7d82eb547a11
field AvailableChain.FGSA.Run.TerminalCarriagePrem_W.carrier f3000183cc1b3ff4
field AvailableChain.FGSA.Run.TerminalCarriagePrem_W.parent aaa34aa718383a1d
field AvailableChain.FGSA.Run.TerminalCarriagePrem_W.path 570601645614b3ff
field AvailableChain.FGSA.Run.TerminalCarriagePrem_W.freshHeight e0c2e65095dd7e53
field AvailableChain.FGSA.Run.TerminalCarriagePrem_W.retainedOrCovered 7240191dd555f60c
field AvailableChain.FGSA.Run.TerminalCarriagePrem_W.horizon 02ed48e01cf9e788
field AvailableChain.FGSA.Run.TerminalCarriagePrem_W.seats c1e4a48ee7823a09
field AvailableChain.FGSA.Run.TerminalCarriagePrem_W.rows 4ca08182fb6e300b
field AvailableChain.FGSA.Run.TerminalCarriagePrem_W.fresh 93ea729dacf6dacd
field AvailableChain.FGSA.Run.TerminalCarriagePrem_W.heightEntry e37677c6a7d60089
field AvailableChain.FGSA.Run.TerminalCarriagePrem_W.receipt ea9948e7923b0a1d
def AvailableChain.FGSA.Run.TerminalCarriage_W 1c7d672f3e9430fb
theorem AvailableChain.FGSA.Run.FreshFinalityRows_W_def ee2dac8b4e3089e3
theorem AvailableChain.FGSA.Run.TerminalCarriage_W_def f58975e203ee8424
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
def AvailableChain.FGSA.Run.storeAt fd0954e18a44e243
def AvailableChain.FGSA.Run.S_at 60355029eeb5c3ce
def AvailableChain.FGSA.Run.F_at b2528d4624b2fa3d
def AvailableChain.FGSA.Run.J_at 4a1425996f193230
def AvailableChain.FGSA.Run.gateIn 3de6caf8c676ae43
theorem AvailableChain.FGSA.Run.gateIn_def 2425dc46ff71f805
def AvailableChain.FGSA.Run.gateResult 28187279574f5188
theorem AvailableChain.FGSA.Run.gateResult_def 0e95192d97e747bb
def AvailableChain.FGSA.Run.isGateTime de71406ad46da144
theorem AvailableChain.FGSA.Run.isGateTime_def a991674f5c9d52f5
def AvailableChain.FGSA.Run.IsGateTick 86d7f4f1c5e58801
def AvailableChain.FGSA.Run.gateResultAt cd1f166d24c4d99a
def AvailableChain.FGSA.Run.gatePassedAt edea2f801c8686e6
def AvailableChain.FGSA.Run.fastAt ce5805ca8ec3e9a8
def AvailableChain.FGSA.Run.headAtIdx cbb50980c755a205
def AvailableChain.FGSA.Run.vHead aadbf5a41f44e086
theorem AvailableChain.FGSA.Run.vHead_def c7f7ecbd30fee7d7
def AvailableChain.FGSA.Run.actionSourceFG 12411249bb7c6652
theorem AvailableChain.FGSA.Run.actionSourceFG_def 1b54c8d190a9bf75
def AvailableChain.FGSA.Run.actionSource 200a91cb2787fe33
def AvailableChain.FGSA.Run.labelBoundAt 83f1360f3d28192d
def AvailableChain.FGSA.Run.DeliveredAt 4b70e9fb0f5903c2
def AvailableChain.FGSA.Run.HandlesRowAt 34fd57b000a90fa5
def AvailableChain.FGSA.Run.AcceptsFinalBefore 4f3be1691e9736e2
def AvailableChain.FGSA.Run.cleanResults 11c048fa32968c98
def AvailableChain.FGSA.Run.BelowLabel 66d32de991489047
theorem AvailableChain.FGSA.Run.S_at_def ce5ebdfd1fb4375b
```

### `AvailableChainFGSAClaims.Statements.Recurrence`

```text
```

### `AvailableChainFGSAClaims.Statements.Regimes`

```text
structure AvailableChain.FGSA.Run.Base₂ e8ee139117374ec8
ctor AvailableChain.FGSA.Run.Base₂.mk 406ebcd5ebd4ad28
field AvailableChain.FGSA.Run.Base₂.valid 24dc2e569c3fbc4c
field AvailableChain.FGSA.Run.Base₂.linked c1baa4e6270eddb6
field AvailableChain.FGSA.Run.Base₂.cstar 1fa2b5d42eb74a14
field AvailableChain.FGSA.Run.Base₂.noRestart 4459ad33f916c172
field AvailableChain.FGSA.Run.Base₂.delta 99729bcd34a13628
field AvailableChain.FGSA.Run.Base₂.idealization 4c49c74fa9ca7098
structure AvailableChain.FGSA.Run.HealthyPrefix₂ 6d432210e9c27fba
ctor AvailableChain.FGSA.Run.HealthyPrefix₂.mk c3dbe4ff6c553724
field AvailableChain.FGSA.Run.HealthyPrefix₂.base ed30945c89a7f82c
field AvailableChain.FGSA.Run.HealthyPrefix₂.cut 726baa246351f878
field AvailableChain.FGSA.Run.HealthyPrefix₂.healthy f3f0c495f4fea8f1
field AvailableChain.FGSA.Run.HealthyPrefix₂.deltaF ea0c1cb543500d21
field AvailableChain.FGSA.Run.HealthyPrefix₂.partBefore df3479521ec0017c
structure AvailableChain.FGSA.Run.CleanPrefix₂ 9a7136641dcd96fb
field AvailableChain.FGSA.Run.CleanPrefix₂.toHealthyPrefix₂ 82e805b12ce1f7e1
ctor AvailableChain.FGSA.Run.CleanPrefix₂.mk 4eb5708757ac8005
field AvailableChain.FGSA.Run.CleanPrefix₂.partAt e0672c28ba39627f
def AvailableChain.FGSA.Run.CleanCut₂ cc5747b7e3cca1f2
structure AvailableChain.FGSA.Run.Clean₂ 53543b4783be4f88
ctor AvailableChain.FGSA.Run.Clean₂.mk 73c0159ef3e86a7e
field AvailableChain.FGSA.Run.Clean₂.pre d857dac8cc958b0e
field AvailableChain.FGSA.Run.Clean₂.gst 614a0c0555c833de
structure AvailableChain.FGSA.Run.Recovery₂ 649ecc686e9ac8e3
ctor AvailableChain.FGSA.Run.Recovery₂.mk c835d41a0da29d89
field AvailableChain.FGSA.Run.Recovery₂.sync f795ca65e3ac25aa
field AvailableChain.FGSA.Run.Recovery₂.deltaF 62f00627c2df2dde
field AvailableChain.FGSA.Run.Recovery₂.gap dc3d0e79dc7b3220
field AvailableChain.FGSA.Run.Recovery₂.base 741b3f8da4d89445
field AvailableChain.FGSA.Run.Recovery₂.fault aebac8b0f196e935
field AvailableChain.FGSA.Run.Recovery₂.awake a23e042a23efdb98
field AvailableChain.FGSA.Run.Recovery₂.gapPos b145526f7736ec64
def AvailableChain.FGSA.Run.BaseSet 3be676cb30e7cdd7
def AvailableChain.FGSA.Run.CleanSet 759ee545d232d5d5
def AvailableChain.FGSA.Run.CleanCutSet 6499fb7a8ce59df6
def AvailableChain.FGSA.Run.CleanPrefixSet f2faa0176da829b3
def AvailableChain.FGSA.Run.HealingSet 73649cad5266976e
def AvailableChain.FGSA.Run.AwakeProposerRecurrenceFrom 9860123f152cdd32
structure AvailableChain.FGSA.Run.Outage₂ a099b1930d0f595e
ctor AvailableChain.FGSA.Run.Outage₂.mk f89972fcb6ccdec0
field AvailableChain.FGSA.Run.Outage₂.pre 2549927a9a56063d
field AvailableChain.FGSA.Run.Outage₂.sleepy 9c0a4ca125498085
field AvailableChain.FGSA.Run.Outage₂.order 19169691eb75ec6b
field AvailableChain.FGSA.Run.Outage₂.lag be3a6cd29ed94d67
field AvailableChain.FGSA.Run.Outage₂.budget 55afae6c097dcab9
field AvailableChain.FGSA.Run.Outage₂.fastPart e50217aee3c6dcf4
def AvailableChain.FGSA.Run.OutageSet f3671a282514e580
```

### `AvailableChainFGSAClaims.Statements.WeakContinuation`

```text
structure AvailableChain.FGSA.Run.StrongRecoverySearchPrefix₂ 22fe04f43bd7961b
field AvailableChain.FGSA.Run.StrongRecoverySearchPrefix₂.toRecovery₂ 763cc9fd19479152
ctor AvailableChain.FGSA.Run.StrongRecoverySearchPrefix₂.mk ce48eda27b7c277d
field AvailableChain.FGSA.Run.StrongRecoverySearchPrefix₂.liveness ea4218447f67a2ac
field AvailableChain.FGSA.Run.StrongRecoverySearchPrefix₂.endpoint 366859172cbb8fb2
structure AvailableChain.FGSA.Run.AgreesThrough₂ d4771a60b81c6426
ctor AvailableChain.FGSA.Run.AgreesThrough₂.mk 45ba1c61e8fe0b40
field AvailableChain.FGSA.Run.AgreesThrough₂.honest 45bf6d418cc1c164
field AvailableChain.FGSA.Run.AgreesThrough₂.gst e0005c6dd4c6f3f0
field AvailableChain.FGSA.Run.AgreesThrough₂.delta a155db1a3d8d1396
field AvailableChain.FGSA.Run.AgreesThrough₂.seats 2b0f9e35809df8d5
field AvailableChain.FGSA.Run.AgreesThrough₂.inputs a148ea825ec3979a
field AvailableChain.FGSA.Run.AgreesThrough₂.awake 1920071985160265
field AvailableChain.FGSA.Run.AgreesThrough₂.events 3e1d5e41b53e35ad
field AvailableChain.FGSA.Run.AgreesThrough₂.suffixTime ff9dc9b262319e79
structure AvailableChain.FGSA.Run.CleanContinuation₂ e2e7eae99093415a
ctor AvailableChain.FGSA.Run.CleanContinuation₂.mk e93a3fe906b61b96
field AvailableChain.FGSA.Run.CleanContinuation₂.base a82c220cf4cce3b3
field AvailableChain.FGSA.Run.CleanContinuation₂.agrees 642df72c00e2df0a
field AvailableChain.FGSA.Run.CleanContinuation₂.covered 8954ca03b272b702
field AvailableChain.FGSA.Run.CleanContinuation₂.sync 66afa6faac09f271
field AvailableChain.FGSA.Run.CleanContinuation₂.deltaF 89b5b8001af8f6f4
field AvailableChain.FGSA.Run.CleanContinuation₂.participation 79f106c851a1bcdf
structure AvailableChain.FGSA.Run.BoundedHealingCut₂ 136ad2d782d6c0e0
ctor AvailableChain.FGSA.Run.BoundedHealingCut₂.mk a5fbe7b2f2a3d02e
field AvailableChain.FGSA.Run.BoundedHealingCut₂.afterGST 79761e7c41e1adab
field AvailableChain.FGSA.Run.BoundedHealingCut₂.beforeEnd fec31e2ce3e45469
field AvailableChain.FGSA.Run.BoundedHealingCut₂.cut 7ab7be2fe3826b42
field AvailableChain.FGSA.Run.BoundedHealingCut₂.actualProposal 83ba6d28a782d417
field AvailableChain.FGSA.Run.BoundedHealingCut₂.refreshed 24d01db5b8ddb62d
structure AvailableChain.FGSA.Run.SSafeFromCut₂ 214f2612bb06dfde
ctor AvailableChain.FGSA.Run.SSafeFromCut₂.mk 5a310989c957f713
field AvailableChain.FGSA.Run.SSafeFromCut₂.compatible ecc4b2641cb50023
field AvailableChain.FGSA.Run.SSafeFromCut₂.monotone 6ebe8f8b5767a984
field AvailableChain.FGSA.Run.SSafeFromCut₂.seed 28056caf4b9310aa
field AvailableChain.FGSA.Run.SSafeFromCut₂.finalBelow 21d080049557ba52
field AvailableChain.FGSA.Run.SSafeFromCut₂.outputs 5f8f19783c1641ef
def AvailableChain.FGSA.Run.BoundedSafetyRecovery₂ fd187331f0665919
```

### `AvailableChainFGSAClaims.Statements.WeakContinuationGrowth`

```text
structure AvailableChain.FGSA.Run.RetainedAgreesThrough₂ 3ca74db9e3882d7d
ctor AvailableChain.FGSA.Run.RetainedAgreesThrough₂.mk 305f104af202b678
field AvailableChain.FGSA.Run.RetainedAgreesThrough₂.honest d9336d293598db8e
field AvailableChain.FGSA.Run.RetainedAgreesThrough₂.gst 3a166376e5efdedc
field AvailableChain.FGSA.Run.RetainedAgreesThrough₂.delta ad415de1e72155ea
field AvailableChain.FGSA.Run.RetainedAgreesThrough₂.seats b87bc8ba8a651372
field AvailableChain.FGSA.Run.RetainedAgreesThrough₂.inputs 7583a2b19d526b8d
field AvailableChain.FGSA.Run.RetainedAgreesThrough₂.awake 9e8f9b0281f2d024
field AvailableChain.FGSA.Run.RetainedAgreesThrough₂.events 7e789e9ccb492e21
structure AvailableChain.FGSA.Run.PendingSourceDelivery₂ abf312de2a87bf36
ctor AvailableChain.FGSA.Run.PendingSourceDelivery₂.mk 8e1b426308829f85
field AvailableChain.FGSA.Run.PendingSourceDelivery₂.sourceBroadcast febc052096dbe75b
field AvailableChain.FGSA.Run.PendingSourceDelivery₂.sourceRelay 01f05df3f62f295a
structure AvailableChain.FGSA.Run.CleanGrowthContinuation₂ c83792bd793ff8b3
ctor AvailableChain.FGSA.Run.CleanGrowthContinuation₂.mk 28a9272ab8649a66
field AvailableChain.FGSA.Run.CleanGrowthContinuation₂.base aab74e5d8516493f
field AvailableChain.FGSA.Run.CleanGrowthContinuation₂.agrees 1164ca4a67fa7928
field AvailableChain.FGSA.Run.CleanGrowthContinuation₂.covered 6f8600467dd1ae51
field AvailableChain.FGSA.Run.CleanGrowthContinuation₂.sync d314825f3f70c6ca
field AvailableChain.FGSA.Run.CleanGrowthContinuation₂.pending df12476f625ec466
field AvailableChain.FGSA.Run.CleanGrowthContinuation₂.deltaF fbac4b851e1adecd
field AvailableChain.FGSA.Run.CleanGrowthContinuation₂.accountable e160902d1309b29a
field AvailableChain.FGSA.Run.CleanGrowthContinuation₂.participation c69fa8883188fc0b
def AvailableChain.FGSA.Run.BoundedGrowthRecovery₂ 1f820ffb829f34fe
theorem AvailableChain.FGSA.Run.BoundedGrowthRecovery₂_def 6f198dc838e2ac34
```

### `AvailableChainFGSAClaims.Statements.WeakContinuationLive`

```text
structure AvailableChain.FGSA.Run.WeakContinuationLiveAt₂ 0f0653eafd403214
ctor AvailableChain.FGSA.Run.WeakContinuationLiveAt₂.mk 60a6a5a445b22f39
field AvailableChain.FGSA.Run.WeakContinuationLiveAt₂.safety 61db359ef5c44c42
field AvailableChain.FGSA.Run.WeakContinuationLiveAt₂.inclusion d95fef856d851b2e
field AvailableChain.FGSA.Run.WeakContinuationLiveAt₂.growth 9e27fad4b1d6d223
def AvailableChain.FGSA.Run.BoundedSafetyLivenessRecovery₂ 2670d544b29b8ea3
theorem AvailableChain.FGSA.Run.BoundedSafetyLivenessRecovery₂_def 8dba0951be05e863
```

### `AvailableChainFGSAClaims.Statements.Windows`

```text
def AvailableChain.FGSA.Run.WinSpec 4bba5b1bc8269c68
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
def AvailableChain.FGSA.Run.cleanWinAt d78ff25d70208033
def AvailableChain.FGSA.Run.cleanWin e5c028a8672a4403
def AvailableChain.FGSA.Run.cleanPrefixWin 65a7cf3d33ded7d0
def AvailableChain.FGSA.Run.cleanLabelWin df538837c0718835
def AvailableChain.FGSA.Run.gapWin 855fc2460e54b271
def AvailableChain.FGSA.Run.formWinAt b52901971716b548
def AvailableChain.FGSA.Run.kernelWin fc0770d15d932a67
def AvailableChain.FGSA.Run.trigWin 2de7e558565f3f1c
def AvailableChain.FGSA.Run.outWin df1385f4a0f5a1ef
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
def AvailableChain.FGSA.Run.oldRowHeights 5814574e40871535
def AvailableChain.FGSA.Run.muOf 9679f0b10223d2fc
def AvailableChain.FGSA.Run.high ca2be6cd67aaf5eb
def AvailableChain.FGSA.Run.honestFrontier 7810236a8404ca33
def AvailableChain.FGSA.Run.HeightRow d60114a97ba2c6c4
structure AvailableChain.FGSA.Run.H0Reset 7461cc2881a94561
ctor AvailableChain.FGSA.Run.H0Reset.mk 4729d447aa1a154a
field AvailableChain.FGSA.Run.H0Reset.rG_after cfab7cce8b89357a
field AvailableChain.FGSA.Run.H0Reset.rG_first 09f702849ddcccfe
field AvailableChain.FGSA.Run.H0Reset.cut 42cb7470b4132f1d
field AvailableChain.FGSA.Run.H0Reset.frontier 4172781ff8f45b2a
field AvailableChain.FGSA.Run.H0Reset.rowCap 394ce74db9e79090
field AvailableChain.FGSA.Run.H0Reset.mu_le 159bef41fb87f486
field AvailableChain.FGSA.Run.H0Reset.cut_lower 1de1df35c0f5fa00
field AvailableChain.FGSA.Run.H0Reset.cut_upper f89e06892eac0e1b
field AvailableChain.FGSA.Run.H0Reset.reset_row dcab89a37373e9d6
field AvailableChain.FGSA.Run.H0Reset.reset_first f091c51f34567cd2
field AvailableChain.FGSA.Run.H0Reset.label 22d888a4ad1c3e21
field AvailableChain.FGSA.Run.H0Reset.fresh a343f837d8732f7a
field AvailableChain.FGSA.Run.H0Reset.synchronous c0063e622f2aca76
structure AvailableChain.FGSA.Run.H0 1fab0ac7b4484fe1
field AvailableChain.FGSA.Run.H0.toH0Reset 5dad570e2046785b
ctor AvailableChain.FGSA.Run.H0.mk 741a39154ca6e078
field AvailableChain.FGSA.Run.H0.proposal_lower 4daea16ec7a01046
field AvailableChain.FGSA.Run.H0.proposal 47cc7137006ffe75
field AvailableChain.FGSA.Run.H0.proposal_first 00a32d6c0dc4f84a
field AvailableChain.FGSA.Run.H0.after_gst 0b2d7c442c7eeebe
field AvailableChain.FGSA.Run.H0.source_prefix 1300f49765e1c773
def AvailableChain.FGSA.Run.tstarOf 165f06a0b9400160
theorem AvailableChain.FGSA.Run.muOf_def 02d27b209d53abb9
theorem AvailableChain.FGSA.Run.high_def 943f4315935708a9
```
