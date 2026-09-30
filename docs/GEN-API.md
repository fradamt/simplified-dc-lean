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
