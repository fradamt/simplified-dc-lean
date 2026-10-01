# Generic API manifest

_Baseline for A0 step 2 (I23, ruling D15), 2026-09-30._

This file lists every public declaration of
`AvailableChainGeneric.Statements.*` (Pure, V2 and AC), by fully qualified
name and grouped by module. Gen has no anchor rule.

## Baseline rule

Baseline at the A0 step-2 close. Before G-F0a a Gen Statements edit re-writes this file in the SAME commit (visible diff); from G-F0a it is append-only.

## How to check

`scripts/V2Manifest.lean` generates and checks this list.

- `lake env lean --run scripts/V2Manifest.lean --scope gen --list` prints
  the module blocks from the environment, in source order, with hashes.
- `lake env lean --run scripts/V2Manifest.lean --scope gen --check` checks
  the names, modules, kinds, hashes and completeness. A failed check exits 1.
- `--manifest <path>` overrides this file. `--anchor` is a usage error for Gen.

Each entry hash uses the shared hash rules in `scripts/V2Manifest.lean`:
types and definition values, generated or private helpers in the closure,
type binder names and infos, reducibility, and instance status. Theorem
proofs do not affect the hash.

## Entries

### `AvailableChainGeneric.Statements.AC.History`

```text
def AvailableChain.Gen.AC.GenuineExtends 556207e658222cc7
theorem AvailableChain.Gen.AC.GenuineExtends_def 0c37dc0c06d2bd47
def AvailableChain.Gen.AC.GenuineContinues 5f485ce081b0331d
theorem AvailableChain.Gen.AC.GenuineContinues_def ca7629309eaee03a
def AvailableChain.Gen.AC.GenuineHistory 3502d976ab2dfbbc
theorem AvailableChain.Gen.AC.GenuineHistory_def 9cea22f77780332e
```

### `AvailableChainGeneric.Statements.AC.Lease`

```text
def AvailableChain.Gen.AC.UniqueLeaseKeys f579ca9777621413
theorem AvailableChain.Gen.AC.UniqueLeaseKeys_def ff7e66035b1293cc
def AvailableChain.Gen.AC.LeaseMapChain de69aa196585741b
theorem AvailableChain.Gen.AC.LeaseMapChain_def 14d80912a3e24bfa
def AvailableChain.Gen.AC.ProtectsUntil 10383820b179918c
theorem AvailableChain.Gen.AC.ProtectsUntil_def f6ded131614158c4
def AvailableChain.Gen.AC.LeaseChainStatement fc3471acd62e969a
theorem AvailableChain.Gen.AC.LeaseChainStatement_def bc48f0949fc5a96c
def AvailableChain.Gen.AC.PendingGateHarmlessStatement 47d9de1d2d4e6bb2
theorem AvailableChain.Gen.AC.PendingGateHarmlessStatement_def 4f8ae58f4e732a40
```

### `AvailableChainGeneric.Statements.AC.Reads`

```text
def AvailableChain.Gen.AC.Lease.target aad22ad0056fd139
theorem AvailableChain.Gen.AC.Lease.target_def 164e5a182d372255
def AvailableChain.Gen.AC.Lease.level 42c85bad2c55f945
theorem AvailableChain.Gen.AC.Lease.level_def caeb148a16653149
def AvailableChain.Gen.AC.Lease.deadline 1182940e6800fd25
theorem AvailableChain.Gen.AC.Lease.deadline_def 8ef0adfd44046be4
structure AvailableChain.Gen.AC.ACReads f8f221d4c2d52e83
ctor AvailableChain.Gen.AC.ACReads.mk 03ef9a93d8b00a16
def AvailableChain.Gen.AC.ACReads.I d89c0983cc856786
def AvailableChain.Gen.AC.ACReads.prm faf9ed9dfe0b5420
def AvailableChain.Gen.AC.ACReads.output c4c29d4d1b75f7ba
def AvailableChain.Gen.AC.ACReads.anchor 69303fb557c6f759
def AvailableChain.Gen.AC.ACReads.head 696eb04620b0841b
def AvailableChain.Gen.AC.ACReads.parent 535f700d3426ca31
def AvailableChain.Gen.AC.ACReads.raw 03227068f3fce5e5
def AvailableChain.Gen.AC.ACReads.leases 4b992383332692f3
def AvailableChain.Gen.AC.ACReads.fast 561369f6a8eb3c35
def AvailableChain.Gen.AC.ACReads.now 343cf4cd26dcf6d8
def AvailableChain.Gen.AC.ACReads.activeView 4eb061d1efcefa62
def AvailableChain.Gen.AC.ACReads.admissionLevels 9a1c60c125eeb78a
def AvailableChain.Gen.AC.LeaseBelowOutput a2b143545922f72a
theorem AvailableChain.Gen.AC.LeaseBelowOutput_def 2980f74156fd8c7f
def AvailableChain.Gen.AC.normalizeOutput 6086d429b83a2959
theorem AvailableChain.Gen.AC.normalizeOutput_def ba667e529303f966
def AvailableChain.Gen.AC.ACReads.saved 20cd54bfcf7ab1e6
theorem AvailableChain.Gen.AC.ACReads.saved_def be4a5b869f96eac2
def AvailableChain.Gen.AC.ACReads.gateView fe0cc4aa55281af3
theorem AvailableChain.Gen.AC.ACReads.gateView_def 6e2f70e0cac4b88f
def AvailableChain.Gen.AC.ACReads.gateLevels 238ad23316d37aff
theorem AvailableChain.Gen.AC.ACReads.gateLevels_def c74c5e441122aa32
def AvailableChain.Gen.AC.ACReads.gatePrefixes 0e0c1bc81e47fec4
theorem AvailableChain.Gen.AC.ACReads.gatePrefixes_def a52421a29c69e2af
def AvailableChain.Gen.AC.ACReads.gateLeases 8626ab6832e3ba78
theorem AvailableChain.Gen.AC.ACReads.gateLeases_def b6978344581576c8
def AvailableChain.Gen.AC.ACReads.gateFast 17013d83dd57c95a
theorem AvailableChain.Gen.AC.ACReads.gateFast_def 350a772b05e6f2ef
def AvailableChain.Gen.AC.GateWrite 91c079d477610e83
theorem AvailableChain.Gen.AC.GateWrite_def 9561aaaf03692ce3
def AvailableChain.Gen.AC.Reconcile 5cd6f8efab444635
theorem AvailableChain.Gen.AC.Reconcile_def 4487809adc40c719
structure AvailableChain.Gen.AC.GateRunSpec 5bc672e8252addb8
ctor AvailableChain.Gen.AC.GateRunSpec.mk 466815b5a5da9a8d
theorem AvailableChain.Gen.AC.GateRunSpec.empty b625abf11cc42c9d
theorem AvailableChain.Gen.AC.GateRunSpec.veto 73eb76d2286dbaa3
theorem AvailableChain.Gen.AC.GateRunSpec.accept 35027533ee12f87e
structure AvailableChain.Gen.AC.GateWriteAtSpec 651c5913fd3ee9d2
ctor AvailableChain.Gen.AC.GateWriteAtSpec.mk a5e7103a3ff0bf4c
theorem AvailableChain.Gen.AC.GateWriteAtSpec.view_output e0494d09bfc428e4
theorem AvailableChain.Gen.AC.GateWriteAtSpec.view_leases d31c556941783348
theorem AvailableChain.Gen.AC.GateWriteAtSpec.view_now f0fe46750e1adfa2
theorem AvailableChain.Gen.AC.GateWriteAtSpec.anchor_eq d50de7b11c5a2d16
theorem AvailableChain.Gen.AC.GateWriteAtSpec.raw_eq 31cf2e0ab7810837
theorem AvailableChain.Gen.AC.GateWriteAtSpec.saved_other 9ae5cad923c7565f
theorem AvailableChain.Gen.AC.GateWriteAtSpec.saved 0fd8a25abbdd910d
theorem AvailableChain.Gen.AC.GateWriteAtSpec.fresh 4a3f04bf77ec6fb7
theorem AvailableChain.Gen.AC.GateWriteAtSpec.effects a7db09e4797f3d0f
def AvailableChain.Gen.AC.GateWriteSpec 52eaf103bbcb24ae
theorem AvailableChain.Gen.AC.GateWriteSpec_def 24629fb144820084
structure AvailableChain.Gen.AC.ACLaws 738486376dfbe0c0
ctor AvailableChain.Gen.AC.ACLaws.mk 6216b63541a922bc
theorem AvailableChain.Gen.AC.ACLaws.anchor_le_output 2fa58791c2f54841
theorem AvailableChain.Gen.AC.ACLaws.lease_le_output 95d527e2fea25f64
theorem AvailableChain.Gen.AC.ACLaws.output_step d83a2ffa9fca4368
theorem AvailableChain.Gen.AC.ACLaws.gate_write 2f28d336a378176c
def AvailableChain.Gen.AC.GateWriteOfScheduleWellFormedStatement c4f3ec07b22ee828
theorem AvailableChain.Gen.AC.GateWriteOfScheduleWellFormedStatement_def d350ef2384bf313f
```

### `AvailableChainGeneric.Statements.Pure.FirstBad`

```text
structure AvailableChain.Gen.Pure.AGRule 46e50bbdeaec7d7d
ctor AvailableChain.Gen.Pure.AGRule.mk 67a2f061f4994885
theorem AvailableChain.Gen.Pure.AGRule.fg 7d013258bce9227d
theorem AvailableChain.Gen.Pure.AGRule.ac 008e8507fd98a824
def AvailableChain.Gen.Pure.FirstFailure cf165501a2bc40c0
theorem AvailableChain.Gen.Pure.FirstFailure_def 2c4b32de8ca79aea
structure AvailableChain.Gen.Pure.WindowRule a7813d30dfce5a62
ctor AvailableChain.Gen.Pure.WindowRule.mk 226cef7dead12103
theorem AvailableChain.Gen.Pure.WindowRule.fg 75d8d24fc23fb861
theorem AvailableChain.Gen.Pure.WindowRule.ac a4d0212513f6ce44
def AvailableChain.Gen.Pure.RetroAt 1abf5fc4395a6ca9
theorem AvailableChain.Gen.Pure.RetroAt_def 9bd2bf6e9719f279
```

### `AvailableChainGeneric.Statements.Pure.Props`

```text
def AvailableChain.Gen.Pure.CompatOn cbff768115ea78ad
theorem AvailableChain.Gen.Pure.CompatOn_def c86ac57904958cf5
def AvailableChain.Gen.Pure.CompatAt 58dfb0ffa3474202
theorem AvailableChain.Gen.Pure.CompatAt_def c163895e8357386e
def AvailableChain.Gen.Pure.MonoOn 8f64c2cb49e13b69
theorem AvailableChain.Gen.Pure.MonoOn_def 7aaeb4d73f3f3bba
def AvailableChain.Gen.Pure.BelowOn fc80e65d84b837d2
theorem AvailableChain.Gen.Pure.BelowOn_def deca29c78975f8b5
def AvailableChain.Gen.Pure.ServedOn 1d4f8e9b20045cea
theorem AvailableChain.Gen.Pure.ServedOn_def 0ec9a3a5ece68131
def AvailableChain.Gen.Pure.CompatOnOfCompatAtMonoStatement 6f6f9180bd36d34e
theorem AvailableChain.Gen.Pure.CompatOnOfCompatAtMonoStatement_def 6fc9b363256f62a5
def AvailableChain.Gen.Pure.ServedOnMonoStatement 1b9d631fbfb77cd6
theorem AvailableChain.Gen.Pure.ServedOnMonoStatement_def 9e1e69ca011d4a97
```

### `AvailableChainGeneric.Statements.Pure.Quorum`

```text
def AvailableChain.Gen.Pure.qF ae529dfc3c462349
theorem AvailableChain.Gen.Pure.qF_def e08107be1213d410
structure AvailableChain.Gen.Pure.FaultQ 928e5614fc369202
ctor AvailableChain.Gen.Pure.FaultQ.mk a955b7e4c423d667
theorem AvailableChain.Gen.Pure.FaultQ.lt 2b93600cb65ce5c6
structure AvailableChain.Gen.Pure.FaultX 65be94d7b4a0558f
ctor AvailableChain.Gen.Pure.FaultX.mk 7709df0ca8368407
theorem AvailableChain.Gen.Pure.FaultX.lt 5390ba1b72281660
structure AvailableChain.Gen.Pure.Batch 26e76499508d472a
ctor AvailableChain.Gen.Pure.Batch.mk a23404471be031b8
theorem AvailableChain.Gen.Pure.Batch.lt 0cac4cb2266d91cb
structure AvailableChain.Gen.Pure.Weights a11426921553aa73
ctor AvailableChain.Gen.Pure.Weights.mk 0031422fa3ad6721
def AvailableChain.Gen.Pure.Weights.weight 277ca4ceecf278ad
theorem AvailableChain.Gen.Pure.Weights.weight_pos 6b3dee14e2eb0802
def AvailableChain.Gen.Pure.Weights.totalWeight ef8de7dfc4dcc054
theorem AvailableChain.Gen.Pure.Weights.totalWeight_def e7ab9affaa88f744
def AvailableChain.Gen.Pure.Weights.weightOf e81988caf1da057e
theorem AvailableChain.Gen.Pure.Weights.weightOf_def 60a769dfafc93f2a
def AvailableChain.Gen.Pure.Weights.q 50465e982d329a6d
theorem AvailableChain.Gen.Pure.Weights.q_def bf5a87bb975124d9
def AvailableChain.Gen.Pure.Weights.IsQuorum ac368b5929b58361
theorem AvailableChain.Gen.Pure.Weights.IsQuorum_def d2a15031c260a64b
```

### `AvailableChainGeneric.Statements.Pure.Schedule`

```text
def AvailableChain.Gen.Pure.Pattern 7dff956f2e33a782
def AvailableChain.Gen.Pure.PatAt 3ad854a77bf199eb
def AvailableChain.Gen.Pure.InWindow 34e15c11a978b1ee
def AvailableChain.Gen.Pure.slotLen 9e79808d787b00e7
def AvailableChain.Gen.Pure.Pattern.lastRound 97abfa378c1b8822
def AvailableChain.Gen.Pure.Pattern.lastSlot 7f9b7399bba72e73
def AvailableChain.Gen.Pure.Pattern.tailEnd 0cb56f75a604481e
def AvailableChain.Gen.Pure.windowEnd d259690829a58bb1
def AvailableChain.Gen.Pure.windowEndAt 159048b0feb42faf
def AvailableChain.Gen.Pure.RecPat b752c2ad00320b7b
def AvailableChain.Gen.Pure.RecPatAt 0a1079b10b5a739d
def AvailableChain.Gen.Pure.Qualified c68e844c9654bdf7
def AvailableChain.Gen.Pure.Strong 32c7650997cc49e3
def AvailableChain.Gen.Pure.FGood dea7eb9a50130b03
def AvailableChain.Gen.Pure.FGood4 1a66c5c2a592d877
def AvailableChain.Gen.Pure.Skip 52b2caa4ea7e02c9
inductive AvailableChain.Gen.Pure.FinForm 063698c5b0ec33d8
ctor AvailableChain.Gen.Pure.FinForm.fgood b3ac3d1f42d41663
ctor AvailableChain.Gen.Pure.FinForm.fgood4 8689eecadb3bf414
ctor AvailableChain.Gen.Pure.FinForm.recF 6cef56b9565db2b5
ctor AvailableChain.Gen.Pure.FinForm.recF4 13279765d2474ddb
ctor AvailableChain.Gen.Pure.FinForm.recS a802c6e4962674c1
ctor AvailableChain.Gen.Pure.FinForm.recSkip 988c191fcfadc815
ctor AvailableChain.Gen.Pure.FinForm.recC 3b98459c10ac7439
ctor AvailableChain.Gen.Pure.FinForm.strongW 26fad114129b821c
ctor AvailableChain.Gen.Pure.FinForm.lit ef84213504efb083
def AvailableChain.Gen.Pure.FinForm.pat 1dadfdceb137e5cf
def AvailableChain.Gen.Pure.FinForm.lo 7f63b420154efba0
def AvailableChain.Gen.Pure.FinForm.len 143c42d0f3f7ae13
def AvailableChain.Gen.Pure.FinForm.holds a2d5f1ef43be8d28
def AvailableChain.Gen.Pure.RecS 1b5778ec2b1fafcb
def AvailableChain.Gen.Pure.RecF 4df0dc1a7578b1c8
def AvailableChain.Gen.Pure.RecF4 4e79b4e26318ecf5
def AvailableChain.Gen.Pure.RecSkip 77923f13fbe2c774
def AvailableChain.Gen.Pure.StrongRecW 69de715bb231940a
def AvailableChain.Gen.Pure.Lit 9fd9ad82b0e8620a
def AvailableChain.Gen.Pure.RecC 64dced289989140b
def AvailableChain.Gen.Pure.windowEndA a1d3a3b90b3fe150
def AvailableChain.Gen.Pure.windowEndAtA c386f6ede786b4d6
def AvailableChain.Gen.Pure.QualSearch 2e13c24384bd6607
def AvailableChain.Gen.Pure.lastSlotIdx 4c8722b71b9b3219
def AvailableChain.Gen.Pure.Pattern.Compat 2a366ded81a3c6da
theorem AvailableChain.Gen.Pure.PatAt_def cf0560fdf81fd46f
theorem AvailableChain.Gen.Pure.InWindow_def 1a3bc08ce32a9ad9
theorem AvailableChain.Gen.Pure.slotLen_def 2999d0a0fb168be4
theorem AvailableChain.Gen.Pure.Pattern.lastRound_def 84b8379088b523fa
theorem AvailableChain.Gen.Pure.Pattern.lastSlot_def 20b0ed02557a21ff
theorem AvailableChain.Gen.Pure.Pattern.tailEnd_def 7606d4bbf843eeb0
theorem AvailableChain.Gen.Pure.windowEnd_def 356a123adf97574d
theorem AvailableChain.Gen.Pure.windowEndAt_def b1e49b51e0508b53
theorem AvailableChain.Gen.Pure.RecPat_def ce9f8c2c46967065
theorem AvailableChain.Gen.Pure.RecPatAt_def 4bad50620313dc32
theorem AvailableChain.Gen.Pure.Qualified_def f8ff9c550a705169
theorem AvailableChain.Gen.Pure.Strong_def 6dd62c9439d48ebe
theorem AvailableChain.Gen.Pure.FGood_def d0acd2d178473847
theorem AvailableChain.Gen.Pure.FGood4_def ca52d6cd2c2b3d98
theorem AvailableChain.Gen.Pure.Skip_def 845af5e987431fdf
theorem AvailableChain.Gen.Pure.FinForm.pat_def 0dce2abffa4e15ff
theorem AvailableChain.Gen.Pure.FinForm.lo_def 41e0cbbf2f40b80e
theorem AvailableChain.Gen.Pure.FinForm.len_def 038b729bb671ca20
theorem AvailableChain.Gen.Pure.FinForm.holds_def 82bc52096b76ce58
theorem AvailableChain.Gen.Pure.RecS_def e8c03d1555668c13
theorem AvailableChain.Gen.Pure.RecF_def a237c75fb6278010
theorem AvailableChain.Gen.Pure.RecF4_def 346e42c3b43196d5
theorem AvailableChain.Gen.Pure.RecSkip_def b6858e96cd99f8d7
theorem AvailableChain.Gen.Pure.StrongRecW_def bb20d45216b8b0d5
theorem AvailableChain.Gen.Pure.Lit_def 512c386d638cbd46
theorem AvailableChain.Gen.Pure.RecC_def 810e8fe53e32c7c8
theorem AvailableChain.Gen.Pure.windowEndA_def f87e9dd6603e5be8
theorem AvailableChain.Gen.Pure.windowEndAtA_def 5e81d5ada40527c3
theorem AvailableChain.Gen.Pure.QualSearch_def 40c01d8f6de66fe3
theorem AvailableChain.Gen.Pure.lastSlotIdx_def ac67f7fdf03fbbc2
theorem AvailableChain.Gen.Pure.Pattern.Compat_def 3fda32ca12862609
```

### `AvailableChainGeneric.Statements.Pure.Walk`

```text
def AvailableChain.Gen.Pure.DominatedSuffix da46ec2a61082efe
theorem AvailableChain.Gen.Pure.DominatedSuffix_def 23f5fee700b459b5
def AvailableChain.Gen.Pure.NoEligibleChild 0ab642e77e88d097
theorem AvailableChain.Gen.Pure.NoEligibleChild_def 0c2a2108fd9531d4
def AvailableChain.Gen.Pure.AnchorClosed 9184359a5997f435
theorem AvailableChain.Gen.Pure.AnchorClosed_def 576da8551ca389b8
def AvailableChain.Gen.Pure.DescendantDepthBound 06ed060b6e567817
theorem AvailableChain.Gen.Pure.DescendantDepthBound_def c31a98f3f4fdaee6
def AvailableChain.Gen.Pure.SuffixPersists 491b96c0d306eafc
theorem AvailableChain.Gen.Pure.SuffixPersists_def a02db90b7ebb221c
def AvailableChain.Gen.Pure.SuffixReflects bf943ac443afecb3
theorem AvailableChain.Gen.Pure.SuffixReflects_def 438332a5fff5e2c3
def AvailableChain.Gen.Pure.SuffixScoresAgree 1c56ca73374f6e4f
theorem AvailableChain.Gen.Pure.SuffixScoresAgree_def c0298dbec87fbe07
def AvailableChain.Gen.Pure.WalkCoversOfDominatedSuffixStatement dd370c99f130bca6
theorem AvailableChain.Gen.Pure.WalkCoversOfDominatedSuffixStatement_def 415b64d1853f7b7b
def AvailableChain.Gen.Pure.WalkExactOfDominatedSuffixStatement 779ac63322a69584
theorem AvailableChain.Gen.Pure.WalkExactOfDominatedSuffixStatement_def 8b71ef267c031681
def AvailableChain.Gen.Pure.WalkReanchorOfDominatedSuffixStatement e1d25e32083c85db
theorem AvailableChain.Gen.Pure.WalkReanchorOfDominatedSuffixStatement_def eba9e67de323a81c
def AvailableChain.Gen.Pure.WalkAvoidsUnsupportedChildStatement bf92392755cb55c9
theorem AvailableChain.Gen.Pure.WalkAvoidsUnsupportedChildStatement_def 9de671ae4903da00
def AvailableChain.Gen.Pure.WalkCoversOfDominatedSuffixOfAnchorEligibleStatement 04f3b390a0070b3f
theorem AvailableChain.Gen.Pure.WalkCoversOfDominatedSuffixOfAnchorEligibleStatement_def ec4d786c278ac43f
def AvailableChain.Gen.Pure.WalkTerminalOfDescendantDepthBoundStatement 0383376a3f1fac6b
theorem AvailableChain.Gen.Pure.WalkTerminalOfDescendantDepthBoundStatement_def 362f6282f730e355
def AvailableChain.Gen.Pure.WalkNoEligibleChildOfAnchorClosedStatement 594efa6956805067
theorem AvailableChain.Gen.Pure.WalkNoEligibleChildOfAnchorClosedStatement_def f44105eff0f46eb7
def AvailableChain.Gen.Pure.GhostTransferSfxStatement 86e56762231deccc
theorem AvailableChain.Gen.Pure.GhostTransferSfxStatement_def 8318f9c64d8c9652
def AvailableChain.Gen.Pure.BestAncestry f85c0b55cba8beed
theorem AvailableChain.Gen.Pure.BestAncestry_def 052b2208fd600434
def AvailableChain.Gen.Pure.WalkCoversOfRetainedTransportStatement 3385b4377a3077f7
theorem AvailableChain.Gen.Pure.WalkCoversOfRetainedTransportStatement_def f2834ebaab4d115e
```

### `AvailableChainGeneric.Statements.V2.Counts`

```text
def AvailableChain.Gen.V2.faulty 4a2d53e414b33e26
theorem AvailableChain.Gen.V2.faulty_def c739d436a0afc038
def AvailableChain.Gen.V2.awakeHonest 437e76baad254159
theorem AvailableChain.Gen.V2.awakeHonest_def 7c7c6c461ea51265
```

### `AvailableChainGeneric.Statements.V2.Interface`

```text
structure AvailableChain.Gen.V2.FinalityInterface 252a5d5a17c5a471
def AvailableChain.Gen.V2.FinalityInterface.toInterface 733135287ad6c393
ctor AvailableChain.Gen.V2.FinalityInterface.mk 848463d1279135ba
def AvailableChain.Gen.V2.FinalityInterface.finalized 0f75e18dd7551e51
```

### `AvailableChainGeneric.Statements.V2.Linked`

```text
def AvailableChain.Gen.V2.LinkedHolderEqStatement 084f3d8b9097f1e8
theorem AvailableChain.Gen.V2.LinkedHolderEqStatement_def 64a41f8f324f4332
def AvailableChain.Gen.V2.LinkedCardLeOfHoldersStatement b3cf9088e09907a4
theorem AvailableChain.Gen.V2.LinkedCardLeOfHoldersStatement_def be69bde6fe08bb30
```

### `AvailableChainGeneric.Statements.V2.Obs`

```text
structure AvailableChain.Gen.V2.Obs 36f2d94a7564af53
ctor AvailableChain.Gen.V2.Obs.mk 7e04f4a6101c948e
def AvailableChain.Gen.V2.Obs.honest f3929bc039663fb1
def AvailableChain.Gen.V2.Obs.horizon 8136e7527536bd51
def AvailableChain.Gen.V2.Obs.out ae45cdbb42f4f80b
def AvailableChain.Gen.V2.Obs.proposalTime 5eee9ba433134317
def AvailableChain.Gen.V2.Obs.proposer fb8ddf95a0550b04
def AvailableChain.Gen.V2.Obs.proposed e242683635989038
def AvailableChain.Gen.V2.Obs.awake 762e380c88044614
def AvailableChain.Gen.V2.Obs.opening 8a914fac79f2e276
```

### `AvailableChainGeneric.Statements.V2.Reads`

```text
def AvailableChain.V2.Run.idxBefore 330023bfe0389ecb
theorem AvailableChain.V2.Run.idxBefore_def 41072a9adbf10dc0
def AvailableChain.V2.Run.nthIdx? ade2a237ddab397a
theorem AvailableChain.V2.Run.nthIdx?_def 96a6d84f40b65c5f
def AvailableChain.Gen.V2.pubFloor 426d79833e197614
theorem AvailableChain.Gen.V2.pubFloor_def a2afeb0a28120829
def AvailableChain.Gen.V2.HonestSlot 609c00845efe5768
theorem AvailableChain.Gen.V2.HonestSlot_def 90ae4bd22be09caa
def AvailableChain.Gen.V2.HoldsBefore 05c88a204ff8c588
theorem AvailableChain.Gen.V2.HoldsBefore_def 3d54f870ba50a47c
def AvailableChain.Gen.V2.MonoAlong 687a73d2e9109571
theorem AvailableChain.Gen.V2.MonoAlong_def d552800e48aacdcd
def AvailableChain.Gen.V2.Pending 146254f3313d45fe
theorem AvailableChain.Gen.V2.Pending_def ab1e446f7d89302a
def AvailableChain.Gen.V2.StateBeforeIdxBeforeStatement 945b4f02b4f41524
theorem AvailableChain.Gen.V2.StateBeforeIdxBeforeStatement_def 6effdbdb2d7478f2
def AvailableChain.Gen.V2.HoldsBeforeIffExistsIdxStatement 30f57f1d322513ff
theorem AvailableChain.Gen.V2.HoldsBeforeIffExistsIdxStatement_def 4604dfd6f0748219
```

### `AvailableChainGeneric.Statements.V2.Receipt`

```text
def AvailableChain.Gen.V2.Trigger 14cd826b1af3872e
theorem AvailableChain.Gen.V2.Trigger_def 9156d168343315c0
structure AvailableChain.Gen.V2.DeliveryWithin 6de7c37da778b941
ctor AvailableChain.Gen.V2.DeliveryWithin.mk ba16e0cc4c81cb76
theorem AvailableChain.Gen.V2.DeliveryWithin.broadcast e40c4af951b16892
theorem AvailableChain.Gen.V2.DeliveryWithin.relay 395fcc0df9317951
structure AvailableChain.Gen.V2.TimelyClock dbb29ecc1878cd98
ctor AvailableChain.Gen.V2.TimelyClock.mk 0b608c3d40296466
def AvailableChain.Gen.V2.TimelyClock.actTime b1b409bf1f469288
def AvailableChain.Gen.V2.TimelyClock.clockOf 72f6f88b50345456
theorem AvailableChain.Gen.V2.TimelyClock.timely_iff 91dbf0d8c5aa5124
def AvailableChain.Gen.V2.TimelyClock.clock e7f7c01513926071
theorem AvailableChain.Gen.V2.TimelyClock.clockOf_eq 0d951b6bfbaa5374
structure AvailableChain.Gen.V2.AcceptanceLaw d5d0ec4d336542ed
ctor AvailableChain.Gen.V2.AcceptanceLaw.mk a24b797fa0db582a
theorem AvailableChain.Gen.V2.AcceptanceLaw.accepts aa764d29f2b3e723
structure AvailableChain.Gen.V2.AdmitSound 00c6781191a9f6d4
ctor AvailableChain.Gen.V2.AdmitSound.mk 0aa63f249f4f8aab
theorem AvailableChain.Gen.V2.AdmitSound.timely 8572cd21a779bfad
def AvailableChain.Gen.V2.TimelyOfClockStatement 3255eedae708cc6c
theorem AvailableChain.Gen.V2.TimelyOfClockStatement_def b7896d70f307da43
def AvailableChain.Gen.V2.TimelyOfEmitStatement 1c31d6719a952b0b
theorem AvailableChain.Gen.V2.TimelyOfEmitStatement_def eeff51d78e3c470c
def AvailableChain.Gen.V2.TimelyOfRelayStatement 29ee3f73225c6563
theorem AvailableChain.Gen.V2.TimelyOfRelayStatement_def 8c8260d22287923b
def AvailableChain.Gen.V2.AcceptedByDeadlineStatement ff834a06111208ce
theorem AvailableChain.Gen.V2.AcceptedByDeadlineStatement_def 4258f4f3996c240a
def AvailableChain.Gen.V2.FirstAcceptOfProcessedStatement c20dde2bb2feb628
theorem AvailableChain.Gen.V2.FirstAcceptOfProcessedStatement_def f730d8f69e108181
```

### `AvailableChainGeneric.Statements.V2.Regimes`

```text
def AvailableChain.Gen.V2.LabelSync f10226438ae43498
theorem AvailableChain.Gen.V2.LabelSync_def 618e46c42378ed0a
structure AvailableChain.Gen.V2.LabelFacts eae62a359e340f7e
ctor AvailableChain.Gen.V2.LabelFacts.mk 9484a7aa9fb6b8b9
theorem AvailableChain.Gen.V2.LabelFacts.sync 93b8b872e86e9ab8
theorem AvailableChain.Gen.V2.LabelFacts.batch c9d4dc9f9e957214
structure AvailableChain.Gen.V2.BaseCore 38f986dd5299b77e
ctor AvailableChain.Gen.V2.BaseCore.mk bafc5b3ad725a394
theorem AvailableChain.Gen.V2.BaseCore.valid bbbf41381c9d8e84
theorem AvailableChain.Gen.V2.BaseCore.noRestart d349302eed33a29d
structure AvailableChain.Gen.V2.HealthyCore ce2754dfb1fbefdb
ctor AvailableChain.Gen.V2.HealthyCore.mk 3b12841804ac0b31
theorem AvailableChain.Gen.V2.HealthyCore.healthy 1cd5d800f1251645
structure AvailableChain.Gen.V2.CutCore b57052a8af85b1e8
theorem AvailableChain.Gen.V2.CutCore.toHealthyCore d27abd66dec761f9
ctor AvailableChain.Gen.V2.CutCore.mk aba6ea9a411cd6c4
theorem AvailableChain.Gen.V2.CutCore.cut c922047a2be8b9aa
structure AvailableChain.Gen.V2.OutageCore 6d29723ec86868f8
ctor AvailableChain.Gen.V2.OutageCore.mk ab5d901eeb594681
theorem AvailableChain.Gen.V2.OutageCore.order 701722dd1cb7fbb5
structure AvailableChain.Gen.V2.RecoveryCore dfd6e758d52b808e
ctor AvailableChain.Gen.V2.RecoveryCore.mk b11c29fb5a6c0be4
theorem AvailableChain.Gen.V2.RecoveryCore.sync 7f8a292f9fcd76fc
theorem AvailableChain.Gen.V2.RecoveryCore.gap a66c348345c25268
def AvailableChain.Gen.V2.SeedAt 780753617390c751
theorem AvailableChain.Gen.V2.SeedAt_def 69701b3a54d54510
```

### `AvailableChainGeneric.Statements.V2.Signatures`

```text
def AvailableChain.Gen.V2.EmittedUniquePerLabelStatement c36c47f1e7214d31
theorem AvailableChain.Gen.V2.EmittedUniquePerLabelStatement_def bffd654004ae0429
def AvailableChain.Gen.V2.HonestUniquePerLabelStatement a9107be70e395855
theorem AvailableChain.Gen.V2.HonestUniquePerLabelStatement_def 25dbc71e6280bc4c
```


### `AvailableChainGeneric.Statements.AC.Transfer`

```text
def AvailableChain.Gen.AC.GateService 883c459a1b9e5e59
theorem AvailableChain.Gen.AC.GateService_def 09cd9fcbf014596a
def AvailableChain.Gen.AC.GateOfCoveringBatchStatement 0297b3b2934e1759
theorem AvailableChain.Gen.AC.GateOfCoveringBatchStatement_def 2a20fc97cfe76483
def AvailableChain.Gen.AC.SEqOfExactStatement 1ce786afb9bad8f0
theorem AvailableChain.Gen.AC.SEqOfExactStatement_def 16b40e4e7fb021d6
```

### `AvailableChainGeneric.Statements.V2.Slashing`

```text
structure AvailableChain.Gen.V2.SlashingInterface cfd5424eefe61c74
def AvailableChain.Gen.V2.SlashingInterface.toFinalityInterface 85edd9caae2fe671
ctor AvailableChain.Gen.V2.SlashingInterface.mk 0636988bbb255725
def AvailableChain.Gen.V2.SlashingInterface.slashes e464437d9cc362da
def AvailableChain.Gen.V2.HonestNeverSlashed cb7d6d1806cfe47c
theorem AvailableChain.Gen.V2.HonestNeverSlashed_def a06df42e8668cf32
```

### `AvailableChainGeneric.Statements.AC.Votes`

```text
def AvailableChain.Gen.AC.voteSupports a505536f79025d49
theorem AvailableChain.Gen.AC.voteSupports_def fbeb911519ac5daa
def AvailableChain.Gen.AC.poolSupports 03597e7e42083241
theorem AvailableChain.Gen.AC.poolSupports_def 0e3741e4847fd349
def AvailableChain.Gen.AC.plainSupporters bb457f8923e27222
theorem AvailableChain.Gen.AC.plainSupporters_def b06c151456abbe93
def AvailableChain.Gen.AC.TransferBounds 97f0347e35d97f16
theorem AvailableChain.Gen.AC.TransferBounds_def bd506dc92b7c135c
def AvailableChain.Gen.AC.TransferStatement 998560a5e56c286a
theorem AvailableChain.Gen.AC.TransferStatement_def 9ec4bd661e6f64e8
def AvailableChain.Gen.AC.BatchBounds 66706533377eff22
theorem AvailableChain.Gen.AC.BatchBounds_def afae6f825fcfbeb8
def AvailableChain.Gen.AC.BatchCountsStatement 5ca999a37650b98a
theorem AvailableChain.Gen.AC.BatchCountsStatement_def 0cd4477e06dabc30
def AvailableChain.Gen.AC.TransferN2Statement e2835c94ad4a9f70
theorem AvailableChain.Gen.AC.TransferN2Statement_def 0a75145b33fb9ab6
def AvailableChain.Gen.AC.ScoreEqOnStatement d54234e3c4437ea9
theorem AvailableChain.Gen.AC.ScoreEqOnStatement_def 25895f1df739d585
def AvailableChain.Gen.AC.CapVoteStatement b3d2b00a2dbc17ce
theorem AvailableChain.Gen.AC.CapVoteStatement_def 62a98693cb5705aa
def AvailableChain.Gen.AC.CapPairStatement 4509997bea2e6d5a
theorem AvailableChain.Gen.AC.CapPairStatement_def 2a79f83cee317a4a
def AvailableChain.Gen.AC.BatchStatement a43eace6488382e3
theorem AvailableChain.Gen.AC.BatchStatement_def d9c839bb3c6a24f1
```

### `AvailableChainGeneric.Statements.Pure.QuorumInter`

```text
def AvailableChain.Gen.Pure.FaultXInterHonestStatement 70a213ef2f525312
theorem AvailableChain.Gen.Pure.FaultXInterHonestStatement_def a9d4c80022e7c64c
```

### `AvailableChainGeneric.Statements.Pure.SupportCounts`

```text
def AvailableChain.Gen.Pure.TwoMajoritiesIntersectStatement b13b774ed3285246
theorem AvailableChain.Gen.Pure.TwoMajoritiesIntersectStatement_def 000afeafe2351fbc
```

### `AvailableChainGeneric.Statements.AC.Support`

```text
def AvailableChain.Gen.AC.GoldfishScoreAntitoneStatement 2a644bd0f046ed36
theorem AvailableChain.Gen.AC.GoldfishScoreAntitoneStatement_def 1fa3f58fdc73fcc6
def AvailableChain.Gen.AC.ConflictingScoreSumLeStatement e1f28e1d341992b7
theorem AvailableChain.Gen.AC.ConflictingScoreSumLeStatement_def 95bfcc57ccfdf0d5
def AvailableChain.Gen.AC.VoterCountLeOfSeatsSubsetStatement fc03228e36af1195
theorem AvailableChain.Gen.AC.VoterCountLeOfSeatsSubsetStatement_def 7029677e43acf1a8
```

### `AvailableChainGeneric.Statements.Pure.HonestCount`

```text
def AvailableChain.Gen.Pure.HonestOriginOfCountStatement b90084bf6382c94d
theorem AvailableChain.Gen.Pure.HonestOriginOfCountStatement_def 7590cf1650656970
```

### `AvailableChainGeneric.Statements.AC.LeaseWindow`

```text
def AvailableChain.Gen.AC.SlowWindowConflictAbsurdStatement 0bf60151901c729a
theorem AvailableChain.Gen.AC.SlowWindowConflictAbsurdStatement_def c300da53046dea8e
def AvailableChain.Gen.AC.ExpireByThresholdStatement fd661a182a71632b
theorem AvailableChain.Gen.AC.ExpireByThresholdStatement_def 3798a2e9c79cf96c
```

### `AvailableChainGeneric.Statements.Pure.Dominance`

```text
def AvailableChain.Gen.Pure.MajUniqueChildStatement c2a3c1fcca7f79e9
theorem AvailableChain.Gen.Pure.MajUniqueChildStatement_def e11d19cd90604607
```

### `AvailableChainGeneric.Statements.V2.DCRegimes`

```text
def AvailableChain.Gen.V2.SingleProposerRecurrence 8b54094a6819f6fb
theorem AvailableChain.Gen.V2.SingleProposerRecurrence_def e68862c9867837c9
def AvailableChain.Gen.V2.OutageInterval fa178df343dc8583
theorem AvailableChain.Gen.V2.OutageInterval_def 3e0808ebf805aab3
```

### `AvailableChainGeneric.Statements.V2.DCProps`

```text
def AvailableChain.Gen.V2.ConsistentFrom 8292f6c22dd20f4b
theorem AvailableChain.Gen.V2.ConsistentFrom_def 797ebb7fc55efba1
def AvailableChain.Gen.V2.AgreeFrom 824a873856bb3790
theorem AvailableChain.Gen.V2.AgreeFrom_def 78a9a9ab5a3c4181
def AvailableChain.Gen.V2.MonotoneFrom 94f80f94ab5d3d15
theorem AvailableChain.Gen.V2.MonotoneFrom_def f2e8d8f8dd279c5f
structure AvailableChain.Gen.V2.SafeFrom 354557a8b804d905
ctor AvailableChain.Gen.V2.SafeFrom.mk 3b720032cb646ef1
theorem AvailableChain.Gen.V2.SafeFrom.agree 3406c889410b79aa
theorem AvailableChain.Gen.V2.SafeFrom.monotone 8d7f43af5aab7df0
theorem AvailableChain.Gen.V2.SafeFrom_def e90a07acd5629b93
def AvailableChain.Gen.V2.InBy da03ae296b98ca77
theorem AvailableChain.Gen.V2.InBy_def 7e6be42ee55cb800
def AvailableChain.Gen.V2.PersistsFrom 52d2bc3b2b773572
theorem AvailableChain.Gen.V2.PersistsFrom_def 757a827fa355d001
```
### `AvailableChainGeneric.Statements.Pure.ChainSearch`

```text
def AvailableChain.Gen.Pure.ChainSearchStatement e03dd4291fdb26dc
theorem AvailableChain.Gen.Pure.ChainSearchStatement_def b26f4f0d039c1507
def AvailableChain.Gen.Pure.AntitoneChainSearchStatement e7383de4aeb45541
theorem AvailableChain.Gen.Pure.AntitoneChainSearchStatement_def c894dc5c18fc6207
def AvailableChain.Gen.Pure.TwoStepChainSearchStatement 3baf40b90947fa21
theorem AvailableChain.Gen.Pure.TwoStepChainSearchStatement_def 66f2097822f16a55
```

### `AvailableChainGeneric.Statements.Pure.KernelArithmetic`

```text
def AvailableChain.Gen.Pure.KernelArithmeticStatement 267f14d9d8350775
theorem AvailableChain.Gen.Pure.KernelArithmeticStatement_def 515b2bdb7edf06e8
def AvailableChain.Gen.Pure.ActionCarrierArithmeticStatement c0d60f4960fa2c49
theorem AvailableChain.Gen.Pure.ActionCarrierArithmeticStatement_def 63e6cdf50fbc7ea5
```

### `AvailableChainGeneric.Statements.Pure.SlotGrid`

```text
def AvailableChain.Gen.Pure.SlotGrid.t 2b9ef82a987a733a
def AvailableChain.Gen.Pure.SlotGrid.v a5463418c0b75741
def AvailableChain.Gen.Pure.SlotGrid.q a6aeb3a55074a225
def AvailableChain.Gen.Pure.SlotGrid.e b6d0824acae6f14b
def AvailableChain.Gen.Pure.SlotGrid.z a030bf9d188cbb32
def AvailableChain.Gen.Pure.SlotGrid.d d0895f55825db292
def AvailableChain.Gen.Pure.SlotGrid.P a4ac5c67c9460e8f
def AvailableChain.Gen.Pure.SlotGrid.L b093791dc454df89
def AvailableChain.Gen.Pure.SlotGrid.T 3ef01a73b480fcd5
def AvailableChain.Gen.Pure.SlotGrid.a 9211f398acbe0e5a
theorem AvailableChain.Gen.Pure.SlotGrid.t_def 33e1487a185e8735
theorem AvailableChain.Gen.Pure.SlotGrid.v_def d3167312e13a6cd9
theorem AvailableChain.Gen.Pure.SlotGrid.q_def 5a432bcef7c30157
theorem AvailableChain.Gen.Pure.SlotGrid.e_def 37fa0e5a5e1e1f49
theorem AvailableChain.Gen.Pure.SlotGrid.z_def d826f53a7dca1b83
theorem AvailableChain.Gen.Pure.SlotGrid.d_def ce93e0291ceaa710
theorem AvailableChain.Gen.Pure.SlotGrid.P_def 31638300030281a9
theorem AvailableChain.Gen.Pure.SlotGrid.L_def 162b3ef2587f4797
theorem AvailableChain.Gen.Pure.SlotGrid.T_def b507f81827daef5a
theorem AvailableChain.Gen.Pure.SlotGrid.a_def f43f7b45c2f71cb4
def AvailableChain.Gen.Pure.GridIdentitiesStatement 5997f3fb3b064cca
def AvailableChain.Gen.Pure.GridPredecessorStatement e58bd1aff9e45549
def AvailableChain.Gen.Pure.GridRoundEquationsStatement c9496fe98b71b6ab
def AvailableChain.Gen.Pure.GridOffsetOrderStatement e8313d0231d92e53
def AvailableChain.Gen.Pure.InFlightLabelAtGateStatement 439ac1b360706d41
def AvailableChain.Gen.Pure.NoGateBetweenReleaseAndGateStatement 6c345c475fc8a742
def AvailableChain.Gen.Pure.LiveLeaseLabelBoundsStatement 9b7da328c170eacc
def AvailableChain.Gen.Pure.RepairExpiryEquationsStatement eed67e9e3222519f
theorem AvailableChain.Gen.Pure.GridIdentitiesStatement_def 5d2f92e80154d4db
theorem AvailableChain.Gen.Pure.GridPredecessorStatement_def 40acb1834396aad0
theorem AvailableChain.Gen.Pure.GridRoundEquationsStatement_def 2766f4aca09be510
theorem AvailableChain.Gen.Pure.GridOffsetOrderStatement_def 2289552662c7f07e
theorem AvailableChain.Gen.Pure.InFlightLabelAtGateStatement_def c96bea68418ced9d
theorem AvailableChain.Gen.Pure.NoGateBetweenReleaseAndGateStatement_def b9be29422937727b
theorem AvailableChain.Gen.Pure.LiveLeaseLabelBoundsStatement_def 4bbf01a619e54cc5
theorem AvailableChain.Gen.Pure.RepairExpiryEquationsStatement_def 016dc7f97c608a66
```

### `AvailableChainGeneric.Statements.Pure.Stages`

```text
def AvailableChain.Gen.Pure.SublistStageFoldStatement bb56d2c8ac1b7a16
theorem AvailableChain.Gen.Pure.SublistStageFoldStatement_def c937a3aecf0536bc
def AvailableChain.Gen.Pure.OrderedStageFoldStatement 93cc8fea00265160
theorem AvailableChain.Gen.Pure.OrderedStageFoldStatement_def c36c5a5f6b9c36e2
def AvailableChain.Gen.Pure.NatOrderedStageFoldStatement bee33b0f6ee02dd3
theorem AvailableChain.Gen.Pure.NatOrderedStageFoldStatement_def 011554e59c139f16
def AvailableChain.Gen.Pure.ProductOrderedStageFoldStatement b4138089e7b45b6f
theorem AvailableChain.Gen.Pure.ProductOrderedStageFoldStatement_def ee18132438625dfa
```


### `AvailableChainGeneric.Statements.Pure.AdditiveStages`

```text
def AvailableChain.Gen.Pure.ComposeStagesAddStatement 9c1a51577d38680c
theorem AvailableChain.Gen.Pure.ComposeStagesAddStatement_def 58889a91c2e5817c
def AvailableChain.Gen.Pure.OrderedStagesAddBoundStatement e316921ca948ebf8
theorem AvailableChain.Gen.Pure.OrderedStagesAddBoundStatement_def bfb52ab06fc8d12c
```

### `AvailableChainGeneric.Statements.Pure.HeadAfterSettlement`

```text
def AvailableChain.Gen.Pure.FirstHeadAfterStatement b2e3a704037d1e09
theorem AvailableChain.Gen.Pure.FirstHeadAfterStatement_def bdfc5bab9b356a0d
def AvailableChain.Gen.Pure.FirstHeadAfterBoundStatement 87dcbd505791b4c5
theorem AvailableChain.Gen.Pure.FirstHeadAfterBoundStatement_def 49a94a460d37e180
```

### `AvailableChainGeneric.Statements.Pure.OpeningAfterGate`

```text
def AvailableChain.Gen.Pure.FirstOpeningAfterGateStatement e54d3f77916f9072
theorem AvailableChain.Gen.Pure.FirstOpeningAfterGateStatement_def 826adcbec5d6c494
```

### `AvailableChainGeneric.Statements.Pure.PeriodicStages`

```text
def AvailableChain.Gen.Pure.PeriodicShiftStatement 666bd911ad40142b
theorem AvailableChain.Gen.Pure.PeriodicShiftStatement_def e4c664f33169ce54
```

### `AvailableChainGeneric.Statements.Pure.StageStops`

```text
def AvailableChain.Gen.Pure.StageOrStopStatement 76fcaf283fdddd19
theorem AvailableChain.Gen.Pure.StageOrStopStatement_def 0e72e073136c9507
```

### `AvailableChainGeneric.Statements.Pure.BatchDominance`

```text
def AvailableChain.Gen.Pure.AnchorPassesStatement ec51b5d1110f4b85
theorem AvailableChain.Gen.Pure.AnchorPassesStatement_def a9ed45056cd5b46a
def AvailableChain.Gen.Pure.UnsupportedFailsStatement bf95cef2d4dbc7ae
theorem AvailableChain.Gen.Pure.UnsupportedFailsStatement_def ce73179934a4832d
```

### `AvailableChainGeneric.Statements.V2.Duty.Linked`

```text
def AvailableChain.Gen.V2.Duty.LinkedSingletonStatement 7a66d63616e38f6e
theorem AvailableChain.Gen.V2.Duty.LinkedSingletonStatement_def edd932fe1db60b08
```

### `AvailableChainGeneric.Statements.V2.Duty.Signatures`

```text
def AvailableChain.Gen.V2.Duty.SingleDuty b7fda1cf039ba6a7
theorem AvailableChain.Gen.V2.Duty.SingleDuty_def bea8d45f3930dc35
def AvailableChain.Gen.V2.Duty.EmitOnceUnder 6d594298765da4ac
theorem AvailableChain.Gen.V2.Duty.EmitOnceUnder_def c3331f6dab8fb598
def AvailableChain.Gen.V2.Duty.EmittedUniqueSingleDutyStatement cb1fcd35b30c5f24
def AvailableChain.Gen.V2.Duty.EmitUniqueOfEmitOnceStatement a56722291f9c47fd
theorem AvailableChain.Gen.V2.Duty.EmittedUniqueSingleDutyStatement_def 6e02fdf39b25fa63
theorem AvailableChain.Gen.V2.Duty.EmitUniqueOfEmitOnceStatement_def e93d6a158f298c0f
def AvailableChain.Gen.V2.Duty.HonestUniqueSingleDutyStatement 0015f25e8ba5db64
theorem AvailableChain.Gen.V2.Duty.HonestUniqueSingleDutyStatement_def a469b07dea7fae63
```

### `AvailableChainGeneric.Statements.V2.Duty.Counts`

```text
def AvailableChain.Gen.V2.Duty.faulty 96d155c121398e6f
theorem AvailableChain.Gen.V2.Duty.faulty_def 18039f964ed57d6b
def AvailableChain.Gen.V2.Duty.awakeHonest ed629a46bfa5c649
theorem AvailableChain.Gen.V2.Duty.awakeHonest_def 17993f86511829fa
```

### `AvailableChainGeneric.Statements.V2.Duty.Interface`

```text
structure AvailableChain.Gen.V2.Duty.FinalityInterface 4e22b8b344b74142
def AvailableChain.Gen.V2.Duty.FinalityInterface.toInterface ab2ad3cb09e901f0
ctor AvailableChain.Gen.V2.Duty.FinalityInterface.mk 341569a5c2f73bb2
def AvailableChain.Gen.V2.Duty.FinalityInterface.finalized a3f402d051ef335a
```

### `AvailableChainGeneric.Statements.V2.Duty.LinkedHolders`

```text
def AvailableChain.Gen.V2.Duty.LinkedHolderEqStatement 20810c5aeefc278d
theorem AvailableChain.Gen.V2.Duty.LinkedHolderEqStatement_def 075f6dd5a1d3260c
def AvailableChain.Gen.V2.Duty.LinkedCardLeOfHoldersStatement 171155983d688132
theorem AvailableChain.Gen.V2.Duty.LinkedCardLeOfHoldersStatement_def b48cb2a179b12916
```

### `AvailableChainGeneric.Statements.V2.Duty.Reads`

```text
def AvailableChain.V2.D.Run.idxBefore 0171afe8870c6009
theorem AvailableChain.V2.D.Run.idxBefore_def 1a5a9aa48e61272b
def AvailableChain.V2.D.Run.nthIdx? d6e71563c1d4964c
theorem AvailableChain.V2.D.Run.nthIdx?_def ca0ebb9ec7bfa1eb
def AvailableChain.Gen.V2.Duty.pubFloor 6447af84257e3668
theorem AvailableChain.Gen.V2.Duty.pubFloor_def 116dd2802c1f4fe4
def AvailableChain.Gen.V2.Duty.HonestSlot 29fdb849eea4789d
theorem AvailableChain.Gen.V2.Duty.HonestSlot_def 54c4c580d53f4763
def AvailableChain.Gen.V2.Duty.HoldsBefore f9a7212def9e9f42
theorem AvailableChain.Gen.V2.Duty.HoldsBefore_def 169bb4b908a5edd4
def AvailableChain.Gen.V2.Duty.MonoAlong dd2e37a6669201ba
theorem AvailableChain.Gen.V2.Duty.MonoAlong_def 0e14dca63f455297
def AvailableChain.Gen.V2.Duty.Pending 710029f7dfd9ec2f
theorem AvailableChain.Gen.V2.Duty.Pending_def fa072067f219d7f5
def AvailableChain.Gen.V2.Duty.StateBeforeIdxBeforeStatement 09ea058a301bc5a0
theorem AvailableChain.Gen.V2.Duty.StateBeforeIdxBeforeStatement_def 65d33a8aa802cb10
def AvailableChain.Gen.V2.Duty.HoldsBeforeIffExistsIdxStatement e1992af2f65494df
theorem AvailableChain.Gen.V2.Duty.HoldsBeforeIffExistsIdxStatement_def 27ef10f4aaa86e09
```

### `AvailableChainGeneric.Statements.V2.Duty.Receipt`

```text
def AvailableChain.Gen.V2.Duty.Trigger d0db54eb307cacc8
theorem AvailableChain.Gen.V2.Duty.Trigger_def 266f17135f2e3259
structure AvailableChain.Gen.V2.Duty.DeliveryWithin 6e134a47971a720c
ctor AvailableChain.Gen.V2.Duty.DeliveryWithin.mk cda581110d1e2951
theorem AvailableChain.Gen.V2.Duty.DeliveryWithin.broadcast 50bc2935928ddd4c
theorem AvailableChain.Gen.V2.Duty.DeliveryWithin.relay 513578083198059e
structure AvailableChain.Gen.V2.Duty.TimelyClock 39d3a2c87e5e6dbd
ctor AvailableChain.Gen.V2.Duty.TimelyClock.mk 7c8b523bf9d91fc1
def AvailableChain.Gen.V2.Duty.TimelyClock.actTime d92b791b6fe56f77
def AvailableChain.Gen.V2.Duty.TimelyClock.clockOf 3e2224f77ebdee04
theorem AvailableChain.Gen.V2.Duty.TimelyClock.timely_iff a3edd99375d877b7
def AvailableChain.Gen.V2.Duty.TimelyClock.clock cd4352d0f60fc03d
theorem AvailableChain.Gen.V2.Duty.TimelyClock.clockOf_eq 00fcb70020ed0949
structure AvailableChain.Gen.V2.Duty.AcceptanceLaw 6c7eaa2a48d44244
ctor AvailableChain.Gen.V2.Duty.AcceptanceLaw.mk d689e60ffe7406ba
theorem AvailableChain.Gen.V2.Duty.AcceptanceLaw.accepts 628e2b0c12ffb3b4
structure AvailableChain.Gen.V2.Duty.AdmitSound 7a2f4909068fa479
ctor AvailableChain.Gen.V2.Duty.AdmitSound.mk 49174b94800eb964
theorem AvailableChain.Gen.V2.Duty.AdmitSound.timely 4ffe4dc89e0ee9c7
def AvailableChain.Gen.V2.Duty.TimelyOfClockStatement 904acc5d4305e9e2
theorem AvailableChain.Gen.V2.Duty.TimelyOfClockStatement_def ed1fea2dba2f419b
def AvailableChain.Gen.V2.Duty.TimelyOfEmitStatement 1272283a23c718f3
theorem AvailableChain.Gen.V2.Duty.TimelyOfEmitStatement_def 650ccd3a357175cf
def AvailableChain.Gen.V2.Duty.TimelyOfRelayStatement 0822d6aaccd283a5
theorem AvailableChain.Gen.V2.Duty.TimelyOfRelayStatement_def c71e803668caee45
def AvailableChain.Gen.V2.Duty.AcceptedByDeadlineStatement 3f49ad27ccd8a0e6
theorem AvailableChain.Gen.V2.Duty.AcceptedByDeadlineStatement_def 77cb15b04b12d4b4
def AvailableChain.Gen.V2.Duty.FirstAcceptOfProcessedStatement 4bd4f124a60de5a2
theorem AvailableChain.Gen.V2.Duty.FirstAcceptOfProcessedStatement_def 3847c6cb30703883
```

### `AvailableChainGeneric.Statements.V2.Duty.Regimes`

```text
def AvailableChain.Gen.V2.Duty.LabelSync 4a2d3df62caea6df
theorem AvailableChain.Gen.V2.Duty.LabelSync_def de4d8d7f7b671252
structure AvailableChain.Gen.V2.Duty.LabelFacts 16ef33d5c79acc69
ctor AvailableChain.Gen.V2.Duty.LabelFacts.mk 19b215272871a9c8
theorem AvailableChain.Gen.V2.Duty.LabelFacts.sync 23a6e497c21cba74
theorem AvailableChain.Gen.V2.Duty.LabelFacts.batch 5b7b1ee3f0a2df43
structure AvailableChain.Gen.V2.Duty.BaseCore a3793dbb36498554
ctor AvailableChain.Gen.V2.Duty.BaseCore.mk bc7695a54df26ea3
theorem AvailableChain.Gen.V2.Duty.BaseCore.valid 74437c65222ae628
theorem AvailableChain.Gen.V2.Duty.BaseCore.noRestart d4ba08873aeb0b46
structure AvailableChain.Gen.V2.Duty.HealthyCore 576b943f8bc27be7
ctor AvailableChain.Gen.V2.Duty.HealthyCore.mk 8de6bb2ab5a62e76
theorem AvailableChain.Gen.V2.Duty.HealthyCore.healthy 8505b6dc8f981ff5
structure AvailableChain.Gen.V2.Duty.CutCore b95693c556191e0a
theorem AvailableChain.Gen.V2.Duty.CutCore.toHealthyCore c1621eb12214e572
ctor AvailableChain.Gen.V2.Duty.CutCore.mk 06ec35a745ce006b
theorem AvailableChain.Gen.V2.Duty.CutCore.cut d0cb6a8d07a8ce93
structure AvailableChain.Gen.V2.Duty.OutageCore ad970265475f5567
ctor AvailableChain.Gen.V2.Duty.OutageCore.mk 00bed2b2e8fafe28
theorem AvailableChain.Gen.V2.Duty.OutageCore.order 160fa5f46a7d1ab2
structure AvailableChain.Gen.V2.Duty.RecoveryCore e2d22634e68dc292
ctor AvailableChain.Gen.V2.Duty.RecoveryCore.mk 34f1bb3c97478a93
theorem AvailableChain.Gen.V2.Duty.RecoveryCore.sync db61156d7ed16772
theorem AvailableChain.Gen.V2.Duty.RecoveryCore.gap 2b1163959368cf54
def AvailableChain.Gen.V2.Duty.SeedAt 2682ff099dbc9b29
theorem AvailableChain.Gen.V2.Duty.SeedAt_def fb87a372566a5971
```

### `AvailableChainGeneric.Statements.V2.Duty.Slashing`

```text
structure AvailableChain.Gen.V2.Duty.SlashingInterface 0da323b6925658c1
def AvailableChain.Gen.V2.Duty.SlashingInterface.toFinalityInterface 2c6d030558622884
ctor AvailableChain.Gen.V2.Duty.SlashingInterface.mk 3f731882449ddf08
def AvailableChain.Gen.V2.Duty.SlashingInterface.slashes 271674c5cc2fa491
def AvailableChain.Gen.V2.Duty.HonestNeverSlashed b9b28b7e4a7eef19
theorem AvailableChain.Gen.V2.Duty.HonestNeverSlashed_def 6733fb0d1ab3ea67
```
