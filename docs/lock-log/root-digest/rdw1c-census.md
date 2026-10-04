# ROOT-DIGEST W1c — census before source edits

Date: 2026-10-04. Starting HEAD: 2faeee8. Scope: all library Lean files, including tests.
This file was written before any W1c source edit. Line numbers refer to that source snapshot.
The JSON companion retains full names, signatures, references, and classifications.
Frozen status is an exact-name lookup in the three API manifests. A definition equation does
not require a new hypothesis unless its predicate body changes. Audit rows are listed separately.
“Needs” means the proof uses scoped uniqueness, including premises already added by W1/W1b.
“Source none” on a generic helper means its explicit local hypothesis must be supplied by a
caller. On a fixture it means a finite fixture proof. It never means global injectivity.
The B2 lexMax entries retain their existing scoped premises; no new class exception is needed.

The new frozen class entries are WalkCoversOfRetainedTransportStatement and its _def, on
targetTree. The existing no-eligible-child pair remains an exception on tree. BestAncestry
itself permits ties and stays unchanged. DominatedSuffix has strict score dominance; selected
source steps supply uniqueness for suffix transport. These entries need no extra premise.
The non-frozen pivot helper needs uniqueness on tree. Its W2 caller and the W2 retained helpers
are outside W1 edit scope. Their exact discharge obligations will be recorded in the final report.

```text
┌──────────┬──────────┬──────────┐
│ Owner    │ No       │ Yes      │
├──────────┼──────────┼──────────┤
│ W1       │ 164      │ 60       │
│ W2       │ 29       │ 9        │
│ W3       │ 73       │ 8        │
└──────────┴──────────┴──────────┘
```

## W1 users

Entry 1: `AvailableChain.FGSA.headInTree`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainFGSA/Model/Frame.lean:44                                     │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ ghost                                                                      │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 2: `AvailableChain.FGSA.headInTree_stored`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainFGSA/Proofs/Head.lean:26                                     │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ ghost, ghostWalk_mem                                                       │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 3: `AvailableChain.FGSA.liveRoot_preceq_headInTree`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainFGSA/Proofs/Head.lean:60                                     │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ ghost_extends                                                              │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 4: `AvailableChain.FGSA.fgsa_confirmationFrom_covers_majority`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainFGSA/Proofs/Head/Pool.lean:108                               │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ DominatedSuffix, DominatedSuffix_def, ghost,                               │
│                 │ walk_covers_of_dominated_suffix_of_anchor_eligible                         │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 5: `AvailableChain.FGSA.fgsa_getHead_covers_of_dominated_suffix`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainFGSA/Proofs/Head/Walk.lean:17                                │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ DominatedSuffix_def, walk_covers_of_dominated_suffix                       │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 6: `AvailableChain.FGSA.fgsa_getHead_exact_of_dominated_suffix`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainFGSA/Proofs/Head/Walk.lean:38                                │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ DominatedSuffix, NoEligibleChild, walk_exact_of_dominated_suffix           │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 7: `AvailableChain.FGSA.fgsa_getHead_reanchor_of_dominated_suffix`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainFGSA/Proofs/Head/Walk.lean:51                                │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ DominatedSuffix, fgsa_getHead_reanchor_of_dominated_suffix, ghost,         │
│                 │ walk_reanchor_of_dominated_suffix                                          │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 8: `AvailableChain.FGSA.fgsa_getHead_avoids_unsupported_child`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainFGSA/Proofs/Head/Walk.lean:64                                │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ walk_avoids_unsupported_child                                              │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 9: `AvailableChain.FGSA.fgsa_headInTree_reanchor_of_pivot`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainFGSA/Proofs/Head/Walk.lean:81                                │
│ Frozen          │ no                                                                         │
│ Needs premise   │ yes                                                                        │
│ Reason          │ Equal best keys need uniqueness on the walked tree. Arbitrary tree: add    │
│                 │ class hypothesis; caller must scope it.                                    │
│ Premise source  │ none                                                                       │
│ Uses            │ DominatedSuffix, fgsa_headInTree_reanchor_of_pivot, ghost,                 │
│                 │ walk_reanchor_of_best_ancestry, walk_reanchor_of_dominated_suffix          │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 10: `AvailableChain.FGSA.fgsa_confirmationFrom_exact_of_dominated_suffix`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainFGSA/Proofs/Head/Walk.lean:112                               │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ DominatedSuffix, NoEligibleChild, ghost, walk_exact_of_dominated_suffix    │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 11: `AvailableChain.FGSA.fgsa_headInTree_covers_of_transfer`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainFGSA/Proofs/Head/Walk.lean:156                               │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ DominatedSuffix_def, walk_covers_of_dominated_suffix                       │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 12: `AvailableChain.FGSA.fgsa_headInTree_mem_or_anchor`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainFGSA/Proofs/Head/Walk.lean:222                               │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ ghostWalk_mem                                                              │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 13: `AvailableChain.FGSA.fgsa_filtered_anchorClosed`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainFGSA/Proofs/Head/Walk.lean:236                               │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ AnchorClosed                                                               │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 14: `AvailableChain.FGSA.fgsa_headInTree_noEligibleChild`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainFGSA/Proofs/Head/Walk.lean:270                               │
│ Frozen          │ no                                                                         │
│ Needs premise   │ yes                                                                        │
│ Reason          │ Equal best keys need uniqueness on the walked tree.                        │
│ Premise source  │ CStoreInv                                                                  │
│ Uses            │ fgsa_headInTree_noEligibleChild, walk_noEligibleChild_of_anchorClosed      │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 15: `AvailableChain.FGSA.fgHead_stored`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainFGSA/Proofs/StoreInv.lean:768                                │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ ghost, ghostWalk_mem                                                       │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 16: `AvailableChain.FGSA.Window.window_lexMax_eq`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainFGSA/Proofs/WindowReaders.lean:29                            │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ lexMax, lexMaxView, lexMax_of_bridge, window_lexMax_eq                     │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 17: `AvailableChain.FGSA.Window.window_pair_iff`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainFGSA/Proofs/WindowStore.lean:136                             │
│ Frozen          │ no                                                                         │
│ Needs premise   │ yes                                                                        │
│ Reason          │ Selector existence/equality uses the scoped B2 root premise (already       │
│                 │ applied). Local ViewRootInj/StoreStepRoots comes from admission.           │
│ Premise source  │ CStoreInv                                                                  │
│ Uses            │ lexMax, lexMax_eq_of_greatest, lexMax_spec                                 │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 18: `AvailableChain.FGSA.Window.windowStoreInvariant_accept`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainFGSA/Proofs/WindowStore.lean:179                             │
│ Frozen          │ no                                                                         │
│ Needs premise   │ yes                                                                        │
│ Reason          │ Selector existence/equality uses the scoped B2 root premise (already       │
│                 │ applied). Local ViewRootInj/StoreStepRoots comes from admission.           │
│ Premise source  │ CStoreInv                                                                  │
│ Uses            │ lexMax, lexMax_insert, lexMax_of_advance, lexMax_spec                      │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 78: `AvailableChain.Gen.AC.batch_anchored`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGeneric/Proofs/AC/Batch.lean:14                              │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ DominatedSuffix_def, walk_covers_of_dominated_suffix_of_anchor_eligible    │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 79: `AvailableChain.Gen.Pure.walk_aux_chooseChild_origin`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGeneric/Proofs/Pure/Walk.lean:23                             │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ walk_aux_chooseChild_origin                                                │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 80: `AvailableChain.Gen.Pure.walk_aux_fold_choose_keeps`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGeneric/Proofs/Pure/Walk.lean:31                             │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ walk_aux_fold_choose_keeps                                                 │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 81: `AvailableChain.Gen.Pure.walk_aux_fold_choose_dominates`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGeneric/Proofs/Pure/Walk.lean:47                             │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ walk_aux_chooseChild_origin, walk_aux_fold_choose_dominates,               │
│                 │ walk_aux_fold_choose_keeps                                                 │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 82: `AvailableChain.Gen.Pure.walk_aux_ghostStep_of_strict_dominance`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGeneric/Proofs/Pure/Walk.lean:78                             │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ ghostStep, walk_aux_fold_choose_dominates,                                 │
│                 │ walk_aux_ghostStep_of_strict_dominance                                     │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 83: `AvailableChain.Gen.Pure.walk_aux_fold_choose_origin`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGeneric/Proofs/Pure/Walk.lean:111                            │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ walk_aux_chooseChild_origin, walk_aux_fold_choose_origin                   │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 84: `AvailableChain.Gen.Pure.walk_aux_fold_choose_some`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGeneric/Proofs/Pure/Walk.lean:124                            │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ walk_aux_chooseChild_origin, walk_aux_fold_choose_some                     │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 85: `AvailableChain.Gen.Pure.walk_aux_ghostStep_eq_fold_of_rootInjective`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGeneric/Proofs/Pure/Walk.lean:136                            │
│ Frozen          │ no                                                                         │
│ Needs premise   │ yes                                                                        │
│ Reason          │ Equal best keys need uniqueness on the walked tree. Existing scoped        │
│                 │ hypothesis or finite initial tree supplies it.                             │
│ Premise source  │ none                                                                       │
│ Uses            │ ghostStep, walk_aux_fold_choose_origin,                                    │
│                 │ walk_aux_ghostStep_eq_fold_of_rootInjective                                │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 86: `AvailableChain.Gen.Pure.walk_aux_ghostStep_none_iff_of_rootInjective`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGeneric/Proofs/Pure/Walk.lean:170                            │
│ Frozen          │ no                                                                         │
│ Needs premise   │ yes                                                                        │
│ Reason          │ Equal best keys need uniqueness on the walked tree. Existing scoped        │
│                 │ hypothesis or finite initial tree supplies it.                             │
│ Premise source  │ none                                                                       │
│ Uses            │ ghostStep, walk_aux_fold_choose_some,                                      │
│                 │ walk_aux_ghostStep_eq_fold_of_rootInjective,                               │
│                 │ walk_aux_ghostStep_none_iff_of_rootInjective                               │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 87: `AvailableChain.Gen.Pure.walk_aux_ghostStep_none_of_noEligibleChild`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGeneric/Proofs/Pure/Walk.lean:200                            │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ NoEligibleChild, ghostStep, walk_aux_ghostStep_none_of_noEligibleChild     │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 88: `AvailableChain.Gen.Pure.walk_aux_ghostStep_child`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGeneric/Proofs/Pure/Walk.lean:221                            │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ ghostStep, walk_aux_fold_choose_origin, walk_aux_ghostStep_child           │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 89: `AvailableChain.Gen.Pure.walk_aux_child_depth`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGeneric/Proofs/Pure/Walk.lean:249                            │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ walk_aux_child_depth                                                       │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 90: `AvailableChain.Gen.Pure.walk_aux_parent_prefix`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGeneric/Proofs/Pure/Walk.lean:259                            │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ walk_aux_parent_prefix                                                     │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 91: `AvailableChain.Gen.Pure.walk_aux_walk_none`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGeneric/Proofs/Pure/Walk.lean:269                            │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ ghostStep, ghostWalk, walk_aux_walk_none                                   │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 92: `AvailableChain.Gen.Pure.walk_aux_walk_some`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGeneric/Proofs/Pure/Walk.lean:278                            │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ ghostStep, ghostWalk, walk_aux_walk_some                                   │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 93: `AvailableChain.Gen.Pure.walk_aux_ghostWalk_extends`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGeneric/Proofs/Pure/Walk.lean:288                            │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ ghostStep, ghostWalk, walk_aux_ghostStep_child,                            │
│                 │ walk_aux_ghostWalk_extends, walk_aux_parent_prefix, walk_aux_walk_none,    │
│                 │ walk_aux_walk_some                                                         │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 94: `AvailableChain.Gen.Pure.walk_aux_ghostWalk_eligible`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGeneric/Proofs/Pure/Walk.lean:302                            │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ ghostStep, ghostWalk, walk_aux_ghostStep_child,                            │
│                 │ walk_aux_ghostWalk_eligible, walk_aux_walk_none, walk_aux_walk_some        │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 95: `AvailableChain.Gen.Pure.walk_aux_siblings_incompatible`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGeneric/Proofs/Pure/Walk.lean:320                            │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ walk_aux_siblings_incompatible                                             │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 96: `AvailableChain.Gen.Pure.walk_aux_prec_iff`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGeneric/Proofs/Pure/Walk.lean:342                            │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ walk_aux_prec_iff                                                          │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 97: `AvailableChain.Gen.Pure.walk_aux_suffix_depth_le_card`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGeneric/Proofs/Pure/Walk.lean:350                            │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ walk_aux_prec_iff, walk_aux_suffix_depth_le_card                           │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 98: `AvailableChain.Gen.Pure.walk_aux_suffix_depth_le_fuel`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGeneric/Proofs/Pure/Walk.lean:382                            │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ walk_aux_suffix_depth_le_card, walk_aux_suffix_depth_le_fuel               │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 99: `AvailableChain.Gen.Pure.walk_aux_ghostWalk_covers_path`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGeneric/Proofs/Pure/Walk.lean:394                            │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ DominatedSuffix, ghostWalk, walk_aux_child_depth,                          │
│                 │ walk_aux_ghostStep_of_strict_dominance, walk_aux_ghostWalk_covers_path,    │
│                 │ walk_aux_ghostWalk_extends, walk_aux_parent_prefix, walk_aux_prec_iff,     │
│                 │ walk_aux_walk_some                                                         │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 100: `AvailableChain.Gen.Pure.walk_aux_ghost_covers_of_path_dominance`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGeneric/Proofs/Pure/Walk.lean:425                            │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ DominatedSuffix, ghost, walk_aux_ghostWalk_covers_path,                    │
│                 │ walk_aux_ghostWalk_extends, walk_aux_ghost_covers_of_path_dominance,       │
│                 │ walk_aux_suffix_depth_le_fuel                                              │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 101: `AvailableChain.Gen.Pure.walk_aux_ghostWalk_terminal_of_depth_bound`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGeneric/Proofs/Pure/Walk.lean:442                            │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ DescendantDepthBound, ghostStep, ghostWalk, walk_aux_child_depth,          │
│                 │ walk_aux_ghostStep_child, walk_aux_ghostStep_none_of_noEligibleChild,      │
│                 │ walk_aux_ghostWalk_terminal_of_depth_bound, walk_aux_parent_prefix,        │
│                 │ walk_aux_walk_none, walk_aux_walk_some                                     │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 102: `AvailableChain.Gen.Pure.walk_aux_ghost_result_no_eligible_child`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGeneric/Proofs/Pure/Walk.lean:468                            │
│ Frozen          │ no                                                                         │
│ Needs premise   │ yes                                                                        │
│ Reason          │ Equal best keys need uniqueness on the walked tree. Existing scoped        │
│                 │ hypothesis or finite initial tree supplies it.                             │
│ Premise source  │ none                                                                       │
│ Uses            │ AnchorClosed, NoEligibleChild, ghost,                                      │
│                 │ walk_aux_ghostStep_none_iff_of_rootInjective,                              │
│                 │ walk_aux_ghostWalk_terminal_of_depth_bound,                                │
│                 │ walk_aux_ghost_result_no_eligible_child, walk_aux_prec_iff,                │
│                 │ walk_aux_suffix_depth_le_fuel                                              │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 103: `AvailableChain.Gen.Pure.walk_aux_rank_refl`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGeneric/Proofs/Pure/Walk.lean:489                            │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ walk_aux_rank_refl                                                         │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 104: `AvailableChain.Gen.Pure.walk_aux_rank_trans`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGeneric/Proofs/Pure/Walk.lean:493                            │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ walk_aux_rank_trans                                                        │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 105: `AvailableChain.Gen.Pure.walk_aux_choose_bounds`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGeneric/Proofs/Pure/Walk.lean:504                            │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ walk_aux_choose_bounds, walk_aux_rank_refl                                 │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 106: `AvailableChain.Gen.Pure.walk_aux_fold_bounds`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGeneric/Proofs/Pure/Walk.lean:534                            │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ walk_aux_choose_bounds, walk_aux_fold_bounds, walk_aux_rank_refl,          │
│                 │ walk_aux_rank_trans                                                        │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 107: `AvailableChain.Gen.Pure.walk_aux_ghostStep_best`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGeneric/Proofs/Pure/Walk.lean:555                            │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ ghostStep, walk_aux_fold_bounds, walk_aux_ghostStep_best                   │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 108: `AvailableChain.Gen.Pure.walk_aux_ghostStep_of_best`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGeneric/Proofs/Pure/Walk.lean:583                            │
│ Frozen          │ no                                                                         │
│ Needs premise   │ yes                                                                        │
│ Reason          │ Equal best keys need uniqueness on the walked tree. Existing scoped        │
│                 │ hypothesis or finite initial tree supplies it.                             │
│ Premise source  │ none                                                                       │
│ Uses            │ ghostStep, walk_aux_ghostStep_best, walk_aux_ghostStep_child,              │
│                 │ walk_aux_ghostStep_none_iff_of_rootInjective, walk_aux_ghostStep_of_best   │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 109: `AvailableChain.Gen.Pure.walk_aux_ghostStep_unique`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGeneric/Proofs/Pure/Walk.lean:608                            │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ ghostStep, walk_aux_ghostStep_unique                                       │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 110: `AvailableChain.Gen.Pure.walk_aux_ghostStep_of_unique_best`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGeneric/Proofs/Pure/Walk.lean:640                            │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ ghostStep, walk_aux_fold_bounds, walk_aux_fold_choose_origin,              │
│                 │ walk_aux_fold_choose_some, walk_aux_ghostStep_of_unique_best               │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 111: `AvailableChain.Gen.Pure.walk_aux_ghostStep_transport_of_subset`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGeneric/Proofs/Pure/Walk.lean:686                            │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ ghostStep, walk_aux_ghostStep_best, walk_aux_ghostStep_child,              │
│                 │ walk_aux_ghostStep_of_unique_best, walk_aux_ghostStep_transport_of_subset, │
│                 │ walk_aux_ghostStep_unique                                                  │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 112: `AvailableChain.Gen.Pure.walk_aux_ghostStep_eraseDups`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGeneric/Proofs/Pure/Walk.lean:714                            │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ ghostStep, walk_aux_ghostStep_child, walk_aux_ghostStep_eraseDups,         │
│                 │ walk_aux_ghostStep_transport_of_subset                                     │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 113: `AvailableChain.Gen.Pure.walk_aux_ghostWalk_terminal_of_card`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGeneric/Proofs/Pure/Walk.lean:737                            │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ ghostStep, ghostWalk, walk_aux_child_depth, walk_aux_ghostStep_child,      │
│                 │ walk_aux_ghostStep_none_of_noEligibleChild,                                │
│                 │ walk_aux_ghostWalk_terminal_of_card, walk_aux_parent_prefix,               │
│                 │ walk_aux_prec_iff, walk_aux_walk_none, walk_aux_walk_some                  │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 114: `AvailableChain.Gen.Pure.walk_aux_ghost_terminal`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGeneric/Proofs/Pure/Walk.lean:787                            │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ ghost, ghostStep, walk_aux_ghostWalk_terminal_of_card,                     │
│                 │ walk_aux_ghost_terminal                                                    │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 115: `AvailableChain.Gen.Pure.walk_aux_ghostWalk_of_terminal`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGeneric/Proofs/Pure/Walk.lean:793                            │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ ghostStep, ghostWalk, walk_aux_ghostWalk_of_terminal, walk_aux_walk_none   │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 116: `AvailableChain.Gen.Pure.walk_aux_ghostWalk_terminal_unique`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGeneric/Proofs/Pure/Walk.lean:801                            │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ ghostStep, ghostWalk, walk_aux_ghostWalk_of_terminal,                      │
│                 │ walk_aux_ghostWalk_terminal_unique, walk_aux_walk_some                     │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 117: `AvailableChain.Gen.Pure.walk_aux_ghostWalk_step_towards_result`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGeneric/Proofs/Pure/Walk.lean:824                            │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ ghostStep, ghostWalk, walk_aux_child_depth, walk_aux_ghostStep_child,      │
│                 │ walk_aux_ghostWalk_extends, walk_aux_ghostWalk_step_towards_result,        │
│                 │ walk_aux_walk_none, walk_aux_walk_some                                     │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 118: `AvailableChain.Gen.Pure.walk_aux_child_prefix_of_common`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGeneric/Proofs/Pure/Walk.lean:863                            │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ walk_aux_child_depth, walk_aux_child_prefix_of_common, walk_aux_prec_iff   │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 119: `AvailableChain.Gen.Pure.walk_aux_same_child_of_common`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGeneric/Proofs/Pure/Walk.lean:878                            │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ walk_aux_same_child_of_common, walk_aux_siblings_incompatible              │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 120: `AvailableChain.Gen.Pure.walk_aux_ghost_step_towards_prefix`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGeneric/Proofs/Pure/Walk.lean:888                            │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ ghost, ghostStep, walk_aux_child_prefix_of_common,                         │
│                 │ walk_aux_ghostStep_child, walk_aux_ghostWalk_step_towards_result,          │
│                 │ walk_aux_ghost_step_towards_prefix, walk_aux_prec_iff                      │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 121: `AvailableChain.Gen.Pure.walk_aux_ghostWalk_reanchor_terminal`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGeneric/Proofs/Pure/Walk.lean:903                            │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ ghostStep, ghostWalk, walk_aux_child_prefix_of_common,                     │
│                 │ walk_aux_ghostStep_child, walk_aux_ghostWalk_extends,                      │
│                 │ walk_aux_ghostWalk_reanchor_terminal, walk_aux_ghostWalk_terminal_unique,  │
│                 │ walk_aux_prec_iff, walk_aux_walk_none, walk_aux_walk_some                  │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 122: `AvailableChain.Gen.Pure.walk_aux_walk_covers_steps`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGeneric/Proofs/Pure/Walk.lean:932                            │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ ghostStep, ghostWalk, walk_aux_child_depth, walk_aux_ghostStep_child,      │
│                 │ walk_aux_ghostWalk_extends, walk_aux_parent_prefix, walk_aux_prec_iff,     │
│                 │ walk_aux_walk_covers_steps, walk_aux_walk_some                             │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 123: `AvailableChain.Gen.Pure.walk_aux_source_suffix_selected`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGeneric/Proofs/Pure/Walk.lean:954                            │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ ghost, ghostStep, walk_aux_ghostStep_child, walk_aux_ghostStep_eraseDups,  │
│                 │ walk_aux_ghost_step_towards_prefix, walk_aux_parent_prefix,                │
│                 │ walk_aux_prec_iff, walk_aux_same_child_of_common,                          │
│                 │ walk_aux_source_suffix_selected                                            │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 124: `AvailableChain.Gen.Pure.walk_covers_of_dominated_suffix_statement`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGeneric/Proofs/Pure/Walk.lean:986                            │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ WalkCoversOfDominatedSuffixStatement,                                      │
│                 │ WalkCoversOfDominatedSuffixStatement_def,                                  │
│                 │ walk_aux_ghost_covers_of_path_dominance,                                   │
│                 │ walk_covers_of_dominated_suffix_statement                                  │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 125: `AvailableChain.Gen.Pure.walk_covers_of_dominated_suffix_of_anchor_eligible_statement`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGeneric/Proofs/Pure/Walk.lean:991                            │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ WalkCoversOfDominatedSuffixOfAnchorEligibleStatement,                      │
│                 │ WalkCoversOfDominatedSuffixOfAnchorEligibleStatement_def, ghostWalk,       │
│                 │ walk_aux_ghostWalk_eligible,                                               │
│                 │ walk_covers_of_dominated_suffix_of_anchor_eligible_statement,              │
│                 │ walk_covers_of_dominated_suffix_statement                                  │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 126: `AvailableChain.Gen.Pure.walk_terminal_of_descendant_depth_bound_statement`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGeneric/Proofs/Pure/Walk.lean:1005                           │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ WalkTerminalOfDescendantDepthBoundStatement,                               │
│                 │ WalkTerminalOfDescendantDepthBoundStatement_def,                           │
│                 │ walk_aux_ghostWalk_terminal_of_depth_bound,                                │
│                 │ walk_terminal_of_descendant_depth_bound_statement                          │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 127: `AvailableChain.Gen.Pure.walk_noEligibleChild_of_anchorClosed_statement`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGeneric/Proofs/Pure/Walk.lean:1012                           │
│ Frozen          │ no                                                                         │
│ Needs premise   │ yes                                                                        │
│ Reason          │ Equal best keys need uniqueness on the walked tree. Existing scoped        │
│                 │ hypothesis or finite initial tree supplies it.                             │
│ Premise source  │ none                                                                       │
│ Uses            │ WalkNoEligibleChildOfAnchorClosedStatement,                                │
│                 │ WalkNoEligibleChildOfAnchorClosedStatement_def,                            │
│                 │ walk_aux_ghost_result_no_eligible_child,                                   │
│                 │ walk_noEligibleChild_of_anchorClosed_statement                             │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 128: `AvailableChain.Gen.Pure.walk_reanchor_of_dominated_suffix_statement`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGeneric/Proofs/Pure/Walk.lean:1018                           │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ WalkReanchorOfDominatedSuffixStatement,                                    │
│                 │ WalkReanchorOfDominatedSuffixStatement_def,                                │
│                 │ walk_aux_ghostWalk_reanchor_terminal, walk_aux_ghost_terminal,             │
│                 │ walk_covers_of_dominated_suffix_statement,                                 │
│                 │ walk_reanchor_of_dominated_suffix_statement                                │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 129: `AvailableChain.Gen.Pure.walk_exact_of_dominated_suffix_statement`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGeneric/Proofs/Pure/Walk.lean:1031                           │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ WalkExactOfDominatedSuffixStatement,                                       │
│                 │ WalkExactOfDominatedSuffixStatement_def,                                   │
│                 │ walk_aux_ghostStep_none_of_noEligibleChild,                                │
│                 │ walk_aux_ghostWalk_of_terminal, walk_exact_of_dominated_suffix_statement,  │
│                 │ walk_reanchor_of_dominated_suffix_statement                                │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 130: `AvailableChain.Gen.Pure.walk_avoids_unsupported_child_statement`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGeneric/Proofs/Pure/Walk.lean:1041                           │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ WalkAvoidsUnsupportedChildStatement,                                       │
│                 │ WalkAvoidsUnsupportedChildStatement_def, walk_aux_child_depth,             │
│                 │ walk_aux_ghostStep_child, walk_aux_ghost_step_towards_prefix,              │
│                 │ walk_aux_parent_prefix, walk_aux_prec_iff,                                 │
│                 │ walk_avoids_unsupported_child_statement                                    │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 131: `AvailableChain.Gen.Pure.ghost_transfer_sfx_statement`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGeneric/Proofs/Pure/Walk.lean:1058                           │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ GhostTransferSfxStatement, GhostTransferSfxStatement_def, ghostStep,       │
│                 │ ghost_transfer_sfx_statement, walk_aux_ghostStep_eraseDups,                │
│                 │ walk_aux_ghostStep_transport_of_subset,                                    │
│                 │ walk_aux_ghost_step_towards_prefix, walk_aux_source_suffix_selected,       │
│                 │ walk_aux_suffix_depth_le_fuel, walk_aux_walk_covers_steps                  │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 132: `AvailableChain.Gen.Pure.walk_covers_of_dominated_suffix`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGeneric/Proofs/Pure/Walk.lean:1082                           │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ DominatedSuffix, ghost, walk_covers_of_dominated_suffix,                   │
│                 │ walk_covers_of_dominated_suffix_statement                                  │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 133: `AvailableChain.Gen.Pure.walk_exact_of_dominated_suffix`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGeneric/Proofs/Pure/Walk.lean:1090                           │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ DominatedSuffix, NoEligibleChild, ghost, walk_exact_of_dominated_suffix,   │
│                 │ walk_exact_of_dominated_suffix_statement                                   │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 134: `AvailableChain.Gen.Pure.walk_reanchor_of_dominated_suffix`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGeneric/Proofs/Pure/Walk.lean:1097                           │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ DominatedSuffix, ghost, walk_reanchor_of_dominated_suffix,                 │
│                 │ walk_reanchor_of_dominated_suffix_statement                                │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 135: `AvailableChain.Gen.Pure.walk_avoids_unsupported_child`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGeneric/Proofs/Pure/Walk.lean:1104                           │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ ghost, walk_avoids_unsupported_child,                                      │
│                 │ walk_avoids_unsupported_child_statement                                    │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 136: `AvailableChain.Gen.Pure.walk_covers_of_dominated_suffix_of_anchor_eligible`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGeneric/Proofs/Pure/Walk.lean:1111                           │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ DominatedSuffix, ghost,                                                    │
│                 │ walk_covers_of_dominated_suffix_of_anchor_eligible,                        │
│                 │ walk_covers_of_dominated_suffix_of_anchor_eligible_statement               │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 137: `AvailableChain.Gen.Pure.walk_terminal_of_descendant_depth_bound`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGeneric/Proofs/Pure/Walk.lean:1121                           │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ DescendantDepthBound, ghostStep, ghostWalk,                                │
│                 │ walk_terminal_of_descendant_depth_bound,                                   │
│                 │ walk_terminal_of_descendant_depth_bound_statement                          │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 138: `AvailableChain.Gen.Pure.walk_noEligibleChild_of_anchorClosed`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGeneric/Proofs/Pure/Walk.lean:1128                           │
│ Frozen          │ no                                                                         │
│ Needs premise   │ yes                                                                        │
│ Reason          │ Equal best keys need uniqueness on the walked tree. Existing scoped        │
│                 │ hypothesis or finite initial tree supplies it.                             │
│ Premise source  │ none                                                                       │
│ Uses            │ AnchorClosed, ghost, walk_noEligibleChild_of_anchorClosed,                 │
│                 │ walk_noEligibleChild_of_anchorClosed_statement                             │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 139: `AvailableChain.Gen.Pure.ghost_transfer_sfx`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGeneric/Proofs/Pure/Walk.lean:1135                           │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ SuffixPersists, SuffixReflects, SuffixScoresAgree, ghost,                  │
│                 │ ghost_transfer_sfx, ghost_transfer_sfx_statement                           │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 140: `AvailableChain.Gen.Pure.walk_reanchor_of_best_ancestry`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGeneric/Proofs/Pure/Walk.lean:1152                           │
│ Frozen          │ no                                                                         │
│ Needs premise   │ yes                                                                        │
│ Reason          │ Equal best keys need uniqueness on the walked tree. Existing scoped        │
│                 │ hypothesis or finite initial tree supplies it.                             │
│ Premise source  │ none                                                                       │
│ Uses            │ ghost, walk_aux_ghostStep_eraseDups, walk_aux_ghostStep_of_best,           │
│                 │ walk_aux_ghostWalk_reanchor_terminal, walk_aux_ghost_terminal,             │
│                 │ walk_aux_parent_prefix, walk_aux_prec_iff, walk_aux_same_child_of_common,  │
│                 │ walk_aux_suffix_depth_le_fuel, walk_aux_walk_covers_steps,                 │
│                 │ walk_reanchor_of_best_ancestry                                             │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 141: `AvailableChain.Gen.Pure.walk_best_ancestry_of_cover`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGeneric/Proofs/Pure/Walk.lean:1197                           │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ ghost, walk_aux_ghostStep_best, walk_aux_ghostStep_child,                  │
│                 │ walk_aux_ghostStep_eraseDups, walk_aux_ghost_step_towards_prefix,          │
│                 │ walk_best_ancestry_of_cover                                                │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 142: `AvailableChain.Gen.Pure.bestAncestry_restrict`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGeneric/Proofs/Pure/Walk.lean:1223                           │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ BestAncestry, bestAncestry_restrict, walk_aux_child_prefix_of_common,      │
│                 │ walk_aux_prec_iff                                                          │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 143: `AvailableChain.Gen.Pure.bestAncestry_concat`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGeneric/Proofs/Pure/Walk.lean:1243                           │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ BestAncestry, bestAncestry_concat, walk_aux_prec_iff                       │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 144: `AvailableChain.Gen.Pure.bestAncestry_of_dominatedSuffix`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGeneric/Proofs/Pure/Walk.lean:1263                           │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ BestAncestry, DominatedSuffix, bestAncestry_of_dominatedSuffix,            │
│                 │ walk_aux_child_depth, walk_aux_parent_prefix, walk_aux_prec_iff            │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 145: `AvailableChain.Gen.Pure.walk_covers_of_retained_transport`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGeneric/Proofs/Pure/Walk.lean:1290                           │
│ Frozen          │ no                                                                         │
│ Needs premise   │ yes                                                                        │
│ Reason          │ Equal best keys need uniqueness on the walked tree. Existing scoped        │
│                 │ hypothesis or finite initial tree supplies it.                             │
│ Premise source  │ none                                                                       │
│ Uses            │ BestAncestry, SuffixPersists, SuffixReflects, SuffixScoresAgree, ghost,    │
│                 │ ghost_transfer_sfx, walk_aux_ghostWalk_reanchor_terminal,                  │
│                 │ walk_aux_ghost_terminal, walk_covers_of_retained_transport,                │
│                 │ walk_reanchor_of_best_ancestry                                             │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 146: `AvailableChain.Gen.Pure.walk_covers_of_retained_transport_statement`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGeneric/Proofs/Pure/Walk.lean:1327                           │
│ Frozen          │ no                                                                         │
│ Needs premise   │ yes                                                                        │
│ Reason          │ Equal best keys need uniqueness on the walked tree. Existing scoped        │
│                 │ hypothesis or finite initial tree supplies it.                             │
│ Premise source  │ none                                                                       │
│ Uses            │ WalkCoversOfRetainedTransportStatement,                                    │
│                 │ WalkCoversOfRetainedTransportStatement_def,                                │
│                 │ walk_covers_of_retained_transport,                                         │
│                 │ walk_covers_of_retained_transport_statement                                │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 147: `AvailableChain.Gen.AC.BatchStatement`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGeneric/Statements/AC/Votes.lean:360                         │
│ Frozen          │ GEN-API:530                                                                │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ ghost                                                                      │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 148: `AvailableChain.Gen.AC.BatchStatement_def`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGeneric/Statements/AC/Votes.lean:385                         │
│ Frozen          │ GEN-API:531                                                                │
│ Needs premise   │ no                                                                         │
│ Reason          │ Definition equation only; no selection existence is asserted.              │
│ Premise source  │ none                                                                       │
│ Uses            │ ghost                                                                      │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 149: `AvailableChain.Gen.Pure.DominatedSuffix`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGeneric/Statements/Pure/Walk.lean:21                         │
│ Frozen          │ GEN-API:307                                                                │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ DominatedSuffix                                                            │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 150: `AvailableChain.Gen.Pure.DominatedSuffix_def`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGeneric/Statements/Pure/Walk.lean:28                         │
│ Frozen          │ GEN-API:308                                                                │
│ Needs premise   │ no                                                                         │
│ Reason          │ Definition equation only; no selection existence is asserted.              │
│ Premise source  │ none                                                                       │
│ Uses            │ DominatedSuffix, DominatedSuffix_def                                       │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 151: `AvailableChain.Gen.Pure.NoEligibleChild`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGeneric/Statements/Pure/Walk.lean:38                         │
│ Frozen          │ GEN-API:309                                                                │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ NoEligibleChild                                                            │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 152: `AvailableChain.Gen.Pure.NoEligibleChild_def`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGeneric/Statements/Pure/Walk.lean:41                         │
│ Frozen          │ GEN-API:310                                                                │
│ Needs premise   │ no                                                                         │
│ Reason          │ Definition equation only; no selection existence is asserted.              │
│ Premise source  │ none                                                                       │
│ Uses            │ NoEligibleChild, NoEligibleChild_def                                       │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 153: `AvailableChain.Gen.Pure.AnchorClosed`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGeneric/Statements/Pure/Walk.lean:48                         │
│ Frozen          │ GEN-API:311                                                                │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ AnchorClosed                                                               │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 154: `AvailableChain.Gen.Pure.AnchorClosed_def`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGeneric/Statements/Pure/Walk.lean:52                         │
│ Frozen          │ GEN-API:312                                                                │
│ Needs premise   │ no                                                                         │
│ Reason          │ Definition equation only; no selection existence is asserted.              │
│ Premise source  │ none                                                                       │
│ Uses            │ AnchorClosed, AnchorClosed_def                                             │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 155: `AvailableChain.Gen.Pure.DescendantDepthBound`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGeneric/Statements/Pure/Walk.lean:60                         │
│ Frozen          │ GEN-API:313                                                                │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ DescendantDepthBound                                                       │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 156: `AvailableChain.Gen.Pure.DescendantDepthBound_def`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGeneric/Statements/Pure/Walk.lean:63                         │
│ Frozen          │ GEN-API:314                                                                │
│ Needs premise   │ no                                                                         │
│ Reason          │ Definition equation only; no selection existence is asserted.              │
│ Premise source  │ none                                                                       │
│ Uses            │ DescendantDepthBound, DescendantDepthBound_def                             │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 157: `AvailableChain.Gen.Pure.SuffixPersists`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGeneric/Statements/Pure/Walk.lean:70                         │
│ Frozen          │ GEN-API:315                                                                │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ SuffixPersists, ghostStep                                                  │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 158: `AvailableChain.Gen.Pure.SuffixPersists_def`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGeneric/Statements/Pure/Walk.lean:76                         │
│ Frozen          │ GEN-API:316                                                                │
│ Needs premise   │ no                                                                         │
│ Reason          │ Definition equation only; no selection existence is asserted.              │
│ Premise source  │ none                                                                       │
│ Uses            │ SuffixPersists, SuffixPersists_def, ghostStep                              │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 159: `AvailableChain.Gen.Pure.SuffixReflects`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGeneric/Statements/Pure/Walk.lean:87                         │
│ Frozen          │ GEN-API:317                                                                │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ SuffixReflects                                                             │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 160: `AvailableChain.Gen.Pure.SuffixReflects_def`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGeneric/Statements/Pure/Walk.lean:93                         │
│ Frozen          │ GEN-API:318                                                                │
│ Needs premise   │ no                                                                         │
│ Reason          │ Definition equation only; no selection existence is asserted.              │
│ Premise source  │ none                                                                       │
│ Uses            │ SuffixReflects, SuffixReflects_def                                         │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 161: `AvailableChain.Gen.Pure.SuffixScoresAgree`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGeneric/Statements/Pure/Walk.lean:103                        │
│ Frozen          │ GEN-API:319                                                                │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ SuffixScoresAgree                                                          │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 162: `AvailableChain.Gen.Pure.SuffixScoresAgree_def`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGeneric/Statements/Pure/Walk.lean:109                        │
│ Frozen          │ GEN-API:320                                                                │
│ Needs premise   │ no                                                                         │
│ Reason          │ Definition equation only; no selection existence is asserted.              │
│ Premise source  │ none                                                                       │
│ Uses            │ SuffixScoresAgree, SuffixScoresAgree_def                                   │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 163: `AvailableChain.Gen.Pure.WalkCoversOfDominatedSuffixStatement`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGeneric/Statements/Pure/Walk.lean:120                        │
│ Frozen          │ GEN-API:321                                                                │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ DominatedSuffix, WalkCoversOfDominatedSuffixStatement, ghost               │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 164: `AvailableChain.Gen.Pure.WalkCoversOfDominatedSuffixStatement_def`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGeneric/Statements/Pure/Walk.lean:126                        │
│ Frozen          │ GEN-API:322                                                                │
│ Needs premise   │ no                                                                         │
│ Reason          │ Definition equation only; no selection existence is asserted.              │
│ Premise source  │ none                                                                       │
│ Uses            │ DominatedSuffix, WalkCoversOfDominatedSuffixStatement,                     │
│                 │ WalkCoversOfDominatedSuffixStatement_def, ghost                            │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 165: `AvailableChain.Gen.Pure.WalkExactOfDominatedSuffixStatement`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGeneric/Statements/Pure/Walk.lean:137                        │
│ Frozen          │ GEN-API:323                                                                │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ DominatedSuffix, NoEligibleChild, WalkExactOfDominatedSuffixStatement,     │
│                 │ ghost                                                                      │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 166: `AvailableChain.Gen.Pure.WalkExactOfDominatedSuffixStatement_def`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGeneric/Statements/Pure/Walk.lean:143                        │
│ Frozen          │ GEN-API:324                                                                │
│ Needs premise   │ no                                                                         │
│ Reason          │ Definition equation only; no selection existence is asserted.              │
│ Premise source  │ none                                                                       │
│ Uses            │ DominatedSuffix, NoEligibleChild, WalkExactOfDominatedSuffixStatement,     │
│                 │ WalkExactOfDominatedSuffixStatement_def, ghost                             │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 167: `AvailableChain.Gen.Pure.WalkReanchorOfDominatedSuffixStatement`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGeneric/Statements/Pure/Walk.lean:155                        │
│ Frozen          │ GEN-API:325                                                                │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ DominatedSuffix, WalkReanchorOfDominatedSuffixStatement, ghost             │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 168: `AvailableChain.Gen.Pure.WalkReanchorOfDominatedSuffixStatement_def`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGeneric/Statements/Pure/Walk.lean:161                        │
│ Frozen          │ GEN-API:326                                                                │
│ Needs premise   │ no                                                                         │
│ Reason          │ Definition equation only; no selection existence is asserted.              │
│ Premise source  │ none                                                                       │
│ Uses            │ DominatedSuffix, WalkReanchorOfDominatedSuffixStatement,                   │
│                 │ WalkReanchorOfDominatedSuffixStatement_def, ghost                          │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 169: `AvailableChain.Gen.Pure.WalkAvoidsUnsupportedChildStatement`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGeneric/Statements/Pure/Walk.lean:173                        │
│ Frozen          │ GEN-API:327                                                                │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ WalkAvoidsUnsupportedChildStatement, ghost                                 │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 170: `AvailableChain.Gen.Pure.WalkAvoidsUnsupportedChildStatement_def`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGeneric/Statements/Pure/Walk.lean:179                        │
│ Frozen          │ GEN-API:328                                                                │
│ Needs premise   │ no                                                                         │
│ Reason          │ Definition equation only; no selection existence is asserted.              │
│ Premise source  │ none                                                                       │
│ Uses            │ WalkAvoidsUnsupportedChildStatement,                                       │
│                 │ WalkAvoidsUnsupportedChildStatement_def, ghost                             │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 171: `AvailableChain.Gen.Pure.WalkCoversOfDominatedSuffixOfAnchorEligibleStatement`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGeneric/Statements/Pure/Walk.lean:190                        │
│ Frozen          │ GEN-API:329                                                                │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ DominatedSuffix, WalkCoversOfDominatedSuffixOfAnchorEligibleStatement,     │
│                 │ ghost                                                                      │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 172: `AvailableChain.Gen.Pure.WalkCoversOfDominatedSuffixOfAnchorEligibleStatement_def`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGeneric/Statements/Pure/Walk.lean:198                        │
│ Frozen          │ GEN-API:330                                                                │
│ Needs premise   │ no                                                                         │
│ Reason          │ Definition equation only; no selection existence is asserted.              │
│ Premise source  │ none                                                                       │
│ Uses            │ DominatedSuffix, WalkCoversOfDominatedSuffixOfAnchorEligibleStatement,     │
│                 │ WalkCoversOfDominatedSuffixOfAnchorEligibleStatement_def, ghost            │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 173: `AvailableChain.Gen.Pure.WalkTerminalOfDescendantDepthBoundStatement`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGeneric/Statements/Pure/Walk.lean:211                        │
│ Frozen          │ GEN-API:331                                                                │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ DescendantDepthBound, WalkTerminalOfDescendantDepthBoundStatement,         │
│                 │ ghostStep, ghostWalk                                                       │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 174: `AvailableChain.Gen.Pure.WalkTerminalOfDescendantDepthBoundStatement_def`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGeneric/Statements/Pure/Walk.lean:217                        │
│ Frozen          │ GEN-API:332                                                                │
│ Needs premise   │ no                                                                         │
│ Reason          │ Definition equation only; no selection existence is asserted.              │
│ Premise source  │ none                                                                       │
│ Uses            │ DescendantDepthBound, WalkTerminalOfDescendantDepthBoundStatement,         │
│                 │ WalkTerminalOfDescendantDepthBoundStatement_def, ghostStep, ghostWalk      │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 175: `AvailableChain.Gen.Pure.WalkNoEligibleChildOfAnchorClosedStatement`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGeneric/Statements/Pure/Walk.lean:229                        │
│ Frozen          │ GEN-API:333                                                                │
│ Needs premise   │ yes                                                                        │
│ Reason          │ Equal best keys need uniqueness on the walked tree. Existing scoped        │
│                 │ hypothesis or finite initial tree supplies it.                             │
│ Premise source  │ none                                                                       │
│ Uses            │ AnchorClosed, WalkNoEligibleChildOfAnchorClosedStatement, ghost            │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 176: `AvailableChain.Gen.Pure.WalkNoEligibleChildOfAnchorClosedStatement_def`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGeneric/Statements/Pure/Walk.lean:237                        │
│ Frozen          │ GEN-API:334                                                                │
│ Needs premise   │ yes                                                                        │
│ Reason          │ Equal best keys need uniqueness on the walked tree. Existing scoped        │
│                 │ hypothesis or finite initial tree supplies it.                             │
│ Premise source  │ none                                                                       │
│ Uses            │ AnchorClosed, WalkNoEligibleChildOfAnchorClosedStatement,                  │
│                 │ WalkNoEligibleChildOfAnchorClosedStatement_def, ghost                      │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 177: `AvailableChain.Gen.Pure.GhostTransferSfxStatement`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGeneric/Statements/Pure/Walk.lean:251                        │
│ Frozen          │ GEN-API:335                                                                │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ GhostTransferSfxStatement, SuffixPersists, SuffixReflects,                 │
│                 │ SuffixScoresAgree, ghost                                                   │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 178: `AvailableChain.Gen.Pure.GhostTransferSfxStatement_def`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGeneric/Statements/Pure/Walk.lean:261                        │
│ Frozen          │ GEN-API:336                                                                │
│ Needs premise   │ no                                                                         │
│ Reason          │ Definition equation only; no selection existence is asserted.              │
│ Premise source  │ none                                                                       │
│ Uses            │ GhostTransferSfxStatement, GhostTransferSfxStatement_def, SuffixPersists,  │
│                 │ SuffixReflects, SuffixScoresAgree, ghost                                   │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 179: `AvailableChain.Gen.Pure.BestAncestry`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGeneric/Statements/Pure/Walk.lean:280                        │
│ Frozen          │ GEN-API:337                                                                │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ BestAncestry                                                               │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 180: `AvailableChain.Gen.Pure.BestAncestry_def`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGeneric/Statements/Pure/Walk.lean:290                        │
│ Frozen          │ GEN-API:338                                                                │
│ Needs premise   │ no                                                                         │
│ Reason          │ Definition equation only; no selection existence is asserted.              │
│ Premise source  │ none                                                                       │
│ Uses            │ BestAncestry, BestAncestry_def                                             │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 181: `AvailableChain.Gen.Pure.WalkCoversOfRetainedTransportStatement`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGeneric/Statements/Pure/Walk.lean:304                        │
│ Frozen          │ GEN-API:339                                                                │
│ Needs premise   │ yes                                                                        │
│ Reason          │ Equal best keys need uniqueness on the walked tree. Existing scoped        │
│                 │ hypothesis or finite initial tree supplies it.                             │
│ Premise source  │ none                                                                       │
│ Uses            │ BestAncestry, SuffixPersists, SuffixReflects, SuffixScoresAgree,           │
│                 │ WalkCoversOfRetainedTransportStatement, ghost                              │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 182: `AvailableChain.Gen.Pure.WalkCoversOfRetainedTransportStatement_def`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGeneric/Statements/Pure/Walk.lean:323                        │
│ Frozen          │ GEN-API:340                                                                │
│ Needs premise   │ yes                                                                        │
│ Reason          │ Equal best keys need uniqueness on the walked tree. Existing scoped        │
│                 │ hypothesis or finite initial tree supplies it.                             │
│ Premise source  │ none                                                                       │
│ Uses            │ BestAncestry, SuffixPersists, SuffixReflects, SuffixScoresAgree,           │
│                 │ WalkCoversOfRetainedTransportStatement,                                    │
│                 │ WalkCoversOfRetainedTransportStatement_def, ghost                          │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 236: `AvailableChain.GridCO.forkChoice`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGridCO/Model/Protocol.lean:253                               │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ ghost                                                                      │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 237: `AvailableChain.GridCO.confirmationFrom`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGridCO/Model/Protocol.lean:359                               │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ ghost                                                                      │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 238: `AvailableChain.GridCO.confirmation`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGridCO/Model/Protocol.lean:370                               │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ ghost                                                                      │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 239: `AvailableChain.GridCO.ghostStep`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGridCO/Model/Walk.lean:10                                    │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ ghostStep                                                                  │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 240: `AvailableChain.GridCO.ghostWalk`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGridCO/Model/Walk.lean:25                                    │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ ghostStep, ghostWalk                                                       │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 241: `AvailableChain.GridCO.ghost`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGridCO/Model/Walk.lean:33                                    │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ ghost, ghostWalk                                                           │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 242: `AvailableChain.GridCO.clean_proposal_parent_ordinary`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGridCO/Proofs/CleanInclusion.lean:94                         │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ ghost, ghostWalk_mem, ghost_reanchor                                       │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 243: `AvailableChain.GridCO.confirmationFrom_extends`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGridCO/Proofs/Goldfish.lean:24                               │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ ghost_extends                                                              │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 244: `AvailableChain.GridCO.forkChoice_extends_liveRoot`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGridCO/Proofs/Goldfish.lean:34                               │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ ghost_extends                                                              │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 245: `AvailableChain.GridCO.head_walk_mem_blocks`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGridCO/Proofs/HeadTargets.lean:116                           │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ ghost, ghostWalk_mem                                                       │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 246: `AvailableChain.GridCO.ghost_adopts_of_rooted_proposal_transport`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGridCO/Proofs/ProposalAdoption.lean:31                       │
│ Frozen          │ no                                                                         │
│ Needs premise   │ yes                                                                        │
│ Reason          │ Equal best keys need uniqueness on the walked tree. Existing scoped        │
│                 │ hypothesis or finite initial tree supplies it.                             │
│ Premise source  │ none                                                                       │
│ Uses            │ ghost, ghostStep_child, ghost_adopts_fresh_child,                          │
│                 │ ghost_adopts_of_rooted_proposal_transport, ghost_result_no_eligible_child  │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 247: `AvailableChain.GridCO.ghost_adopts_of_eligible_proposal_transport`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGridCO/Proofs/ProposalAdoption.lean:104                      │
│ Frozen          │ no                                                                         │
│ Needs premise   │ yes                                                                        │
│ Reason          │ Equal best keys need uniqueness on the walked tree. Existing scoped        │
│                 │ hypothesis or finite initial tree supplies it.                             │
│ Premise source  │ none                                                                       │
│ Uses            │ ghost, ghost_adopts_of_eligible_proposal_transport,                        │
│                 │ ghost_adopts_of_rooted_proposal_transport                                  │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 248: `AvailableChain.GridCO.forkChoice_adopts_of_proposal_transport`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGridCO/Proofs/ProposalAdoption.lean:134                      │
│ Frozen          │ no                                                                         │
│ Needs premise   │ yes                                                                        │
│ Reason          │ Equal best keys need uniqueness on the walked tree. Existing scoped        │
│                 │ hypothesis or finite initial tree supplies it.                             │
│ Premise source  │ none                                                                       │
│ Uses            │ ghost, ghost_adopts_of_eligible_proposal_transport                         │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 249: `AvailableChain.GridCO.forkChoice_adopts_stored_proposal`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGridCO/Proofs/ProposalAdoption.lean:156                      │
│ Frozen          │ no                                                                         │
│ Needs premise   │ yes                                                                        │
│ Reason          │ Equal best keys need uniqueness on the walked tree. Existing scoped        │
│                 │ hypothesis or finite initial tree supplies it.                             │
│ Premise source  │ none                                                                       │
│ Uses            │ ghost                                                                      │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 250: `AvailableChain.GridCO.honest_proposal_parent_stored`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGridCO/Proofs/ProposalViewRelay.lean:206                     │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ ghost, ghostWalk_mem                                                       │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 251: `AvailableChain.GridCO.ordinaryProposalHead`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGridCO/Proofs/ProposerTransfer.lean:18                       │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ ghost                                                                      │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 252: `AvailableChain.GridCO.proposal_parent_ordinary_of_root`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGridCO/Proofs/RecoveryRepair.lean:123                        │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ ghost, ghostWalk_mem, ghost_reanchor                                       │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 253: `AvailableChain.GridCO.ghostStep_child`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGridCO/Proofs/StoreFacts.lean:32                             │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ ghostStep, ghostStep_child                                                 │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 254: `AvailableChain.GridCO.ghostWalk_mem`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGridCO/Proofs/StoreFacts.lean:77                             │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ ghostStep, ghostStep_child, ghostWalk, ghostWalk_mem                       │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 255: `AvailableChain.GridCO.confirmationFrom_mem`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGridCO/Proofs/StoreFacts.lean:97                             │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ ghostWalk_mem                                                              │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 256: `AvailableChain.GridCO.ghostWalk_extends`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGridCO/Proofs/StoreFacts.lean:239                            │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ ghostStep, ghostStep_child, ghostWalk, ghostWalk_extends                   │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 257: `AvailableChain.GridCO.ghost_extends`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGridCO/Proofs/StoreFacts.lean:254                            │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ ghost, ghostWalk_extends, ghost_extends                                    │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 258: `AvailableChain.GridCO.confirmation_covers_majority`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGridCO/Proofs/Support.lean:126                               │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ ghost, ghostWalk_eligible, ghost_covers_of_path_dominance                  │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 259: `AvailableChain.GridCO.ghostStep_of_strict_dominance`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGridCO/Proofs/Walk.lean:78                                   │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ ghostStep, ghostStep_of_strict_dominance                                   │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 260: `AvailableChain.GridCO.depth_le_ghost_fuel`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGridCO/Proofs/Walk.lean:165                                  │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ depth_le_ghost_fuel                                                        │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 261: `AvailableChain.GridCO.ghostWalk_covers_path`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGridCO/Proofs/Walk.lean:178                                  │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ ghostStep_of_strict_dominance, ghostWalk, ghostWalk_covers_path,           │
│                 │ ghostWalk_extends                                                          │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 262: `AvailableChain.GridCO.ghost_covers_of_path_dominance`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGridCO/Proofs/Walk.lean:214                                  │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ depth_le_ghost_fuel, ghost, ghostWalk_covers_path,                         │
│                 │ ghost_covers_of_path_dominance, ghost_extends                              │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 263: `AvailableChain.GridCO.forkChoice_covers_of_path_dominance`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGridCO/Proofs/Walk.lean:230                                  │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ ghost_covers_of_path_dominance                                             │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 264: `AvailableChain.GridCO.ghostWalk_eligible`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGridCO/Proofs/Walk.lean:243                                  │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ ghostStep, ghostStep_child, ghostWalk, ghostWalk_eligible                  │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 265: `AvailableChain.GridCO.ghostStep_eq_fold_of_rootInjective`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGridCO/Proofs/Walk.lean:296                                  │
│ Frozen          │ no                                                                         │
│ Needs premise   │ yes                                                                        │
│ Reason          │ Equal best keys need uniqueness on the walked tree. Existing scoped        │
│                 │ hypothesis or finite initial tree supplies it.                             │
│ Premise source  │ none                                                                       │
│ Uses            │ ghostStep, ghostStep_eq_fold_of_rootInjective                              │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 266: `AvailableChain.GridCO.ghostStep_none_iff_of_rootInjective`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGridCO/Proofs/Walk.lean:326                                  │
│ Frozen          │ no                                                                         │
│ Needs premise   │ yes                                                                        │
│ Reason          │ Equal best keys need uniqueness on the walked tree. Existing scoped        │
│                 │ hypothesis or finite initial tree supplies it.                             │
│ Premise source  │ none                                                                       │
│ Uses            │ ghostStep, ghostStep_eq_fold_of_rootInjective,                             │
│                 │ ghostStep_none_iff_of_rootInjective                                        │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 267: `AvailableChain.GridCO.ghostWalk_terminal_of_depth_bound`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGridCO/Proofs/Walk.lean:356                                  │
│ Frozen          │ no                                                                         │
│ Needs premise   │ yes                                                                        │
│ Reason          │ Equal best keys need uniqueness on the walked tree. Existing scoped        │
│                 │ hypothesis or finite initial tree supplies it.                             │
│ Premise source  │ none                                                                       │
│ Uses            │ ghostStep, ghostStep_child, ghostStep_none_iff_of_rootInjective,           │
│                 │ ghostWalk, ghostWalk_terminal_of_depth_bound                               │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 268: `AvailableChain.GridCO.ghost_result_no_eligible_child`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGridCO/Proofs/Walk.lean:384                                  │
│ Frozen          │ no                                                                         │
│ Needs premise   │ yes                                                                        │
│ Reason          │ Equal best keys need uniqueness on the walked tree. Existing scoped        │
│                 │ hypothesis or finite initial tree supplies it.                             │
│ Premise source  │ none                                                                       │
│ Uses            │ depth_le_ghost_fuel, ghost, ghostStep_none_iff_of_rootInjective,           │
│                 │ ghostWalk_terminal_of_depth_bound, ghost_result_no_eligible_child          │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 269: `AvailableChain.GridCO.ghostStep_best`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGridCO/Proofs/WalkTransport.lean:91                          │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ ghostStep, ghostStep_best                                                  │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 270: `AvailableChain.GridCO.ghostStep_of_best`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGridCO/Proofs/WalkTransport.lean:114                         │
│ Frozen          │ no                                                                         │
│ Needs premise   │ yes                                                                        │
│ Reason          │ Equal best keys need uniqueness on the walked tree. Existing scoped        │
│                 │ hypothesis or finite initial tree supplies it.                             │
│ Premise source  │ none                                                                       │
│ Uses            │ ghostStep, ghostStep_best, ghostStep_child,                                │
│                 │ ghostStep_none_iff_of_rootInjective, ghostStep_of_best                     │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 271: `AvailableChain.GridCO.ghostStep_transport_of_subset`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGridCO/Proofs/WalkTransport.lean:138                         │
│ Frozen          │ no                                                                         │
│ Needs premise   │ yes                                                                        │
│ Reason          │ Equal best keys need uniqueness on the walked tree. Existing scoped        │
│                 │ hypothesis or finite initial tree supplies it.                             │
│ Premise source  │ none                                                                       │
│ Uses            │ ghostStep, ghostStep_best, ghostStep_child, ghostStep_of_best,             │
│                 │ ghostStep_transport_of_subset                                              │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 272: `AvailableChain.GridCO.ghostStep_eraseDups`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGridCO/Proofs/WalkTransport.lean:157                         │
│ Frozen          │ no                                                                         │
│ Needs premise   │ yes                                                                        │
│ Reason          │ Equal best keys need uniqueness on the walked tree. Existing scoped        │
│                 │ hypothesis or finite initial tree supplies it.                             │
│ Premise source  │ none                                                                       │
│ Uses            │ ghostStep, ghostStep_child, ghostStep_eraseDups,                           │
│                 │ ghostStep_none_iff_of_rootInjective, ghostStep_transport_of_subset         │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 273: `AvailableChain.GridCO.ghostWalk_step_towards_result`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGridCO/Proofs/WalkTransport.lean:215                         │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ ghostStep, ghostStep_child, ghostWalk, ghostWalk_extends,                  │
│                 │ ghostWalk_step_towards_result                                              │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 274: `AvailableChain.GridCO.ghost_step_towards_result`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGridCO/Proofs/WalkTransport.lean:255                         │
│ Frozen          │ no                                                                         │
│ Needs premise   │ yes                                                                        │
│ Reason          │ Equal best keys need uniqueness on the walked tree. Existing scoped        │
│                 │ hypothesis or finite initial tree supplies it.                             │
│ Premise source  │ none                                                                       │
│ Uses            │ ghost, ghostStep, ghostStep_eraseDups, ghostWalk_step_towards_result,      │
│                 │ ghost_step_towards_result                                                  │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 275: `AvailableChain.GridCO.walk_covers_steps`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGridCO/Proofs/WalkTransport.lean:265                         │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ ghostStep, ghostStep_child, ghostWalk, ghostWalk_extends,                  │
│                 │ walk_covers_steps                                                          │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 276: `AvailableChain.GridCO.ghost_covers_of_steps`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGridCO/Proofs/WalkTransport.lean:287                         │
│ Frozen          │ no                                                                         │
│ Needs premise   │ yes                                                                        │
│ Reason          │ Equal best keys need uniqueness on the walked tree. Existing scoped        │
│                 │ hypothesis or finite initial tree supplies it.                             │
│ Premise source  │ none                                                                       │
│ Uses            │ depth_le_ghost_fuel, ghost, ghostStep, ghostStep_eraseDups,                │
│                 │ ghost_covers_of_steps, walk_covers_steps                                   │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 277: `AvailableChain.GridCO.ghost_transport_covers`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGridCO/Proofs/WalkTransport.lean:304                         │
│ Frozen          │ no                                                                         │
│ Needs premise   │ yes                                                                        │
│ Reason          │ Equal best keys need uniqueness on the walked tree. Existing scoped        │
│                 │ hypothesis or finite initial tree supplies it.                             │
│ Premise source  │ none                                                                       │
│ Uses            │ ghost, ghostStep, ghostStep_transport_of_subset, ghost_covers_of_steps,    │
│                 │ ghost_step_towards_result, ghost_transport_covers                          │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 278: `AvailableChain.GridCO.ghost_prefix_of_score_transport`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGridCO/Proofs/WalkTransport.lean:335                         │
│ Frozen          │ no                                                                         │
│ Needs premise   │ yes                                                                        │
│ Reason          │ Equal best keys need uniqueness on the walked tree. Existing scoped        │
│                 │ hypothesis or finite initial tree supplies it.                             │
│ Premise source  │ none                                                                       │
│ Uses            │ ghost, ghostStep_best, ghostStep_child, ghostStep_of_best,                 │
│                 │ ghost_covers_of_steps, ghost_prefix_of_score_transport,                    │
│                 │ ghost_step_towards_result                                                  │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 279: `AvailableChain.GridCO.ghost_adopts_fresh_child`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGridCO/Proofs/WalkTransport.lean:388                         │
│ Frozen          │ no                                                                         │
│ Needs premise   │ yes                                                                        │
│ Reason          │ Equal best keys need uniqueness on the walked tree. Existing scoped        │
│                 │ hypothesis or finite initial tree supplies it.                             │
│ Premise source  │ none                                                                       │
│ Uses            │ ghost, ghostStep, ghostStep_of_best, ghostStep_transport_of_subset,        │
│                 │ ghost_adopts_fresh_child, ghost_covers_of_steps, ghost_step_towards_result │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 280: `AvailableChain.GridCO.ghost_reanchor`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGridCO/Proofs/WalkTransport.lean:437                         │
│ Frozen          │ no                                                                         │
│ Needs premise   │ yes                                                                        │
│ Reason          │ Equal best keys need uniqueness on the walked tree. Existing scoped        │
│                 │ hypothesis or finite initial tree supplies it.                             │
│ Premise source  │ none                                                                       │
│ Uses            │ ghost, ghostStep_child, ghost_reanchor, ghost_result_no_eligible_child,    │
│                 │ ghost_step_towards_result, ghost_transport_covers                          │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 281: `AvailableChain.KitFG.lexMax_eq_of_greatest`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainKitFG/Correspondence.lean:63                                 │
│ Frozen          │ no                                                                         │
│ Needs premise   │ yes                                                                        │
│ Reason          │ Selector existence/equality uses the scoped B2 root premise (already       │
│                 │ applied). Existing scoped hypothesis or finite initial tree supplies it.   │
│ Premise source  │ none                                                                       │
│ Uses            │ lexMax, lexMax_eq_of_greatest                                              │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 282: `AvailableChain.KitFG.lexMax_spec`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainKitFG/Correspondence.lean:98                                 │
│ Frozen          │ no                                                                         │
│ Needs premise   │ yes                                                                        │
│ Reason          │ Selector existence/equality uses the scoped B2 root premise (already       │
│                 │ applied). Existing scoped hypothesis or finite initial tree supplies it.   │
│ Premise source  │ none                                                                       │
│ Uses            │ lexMax, lexMax_eq_of_greatest, lexMax_spec                                 │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 283: `AvailableChain.KitFG.lexMax_of_none`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainKitFG/Correspondence.lean:119                                │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ lexMax, lexMax_of_none                                                     │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 284: `AvailableChain.KitFG.lexMax_insert`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainKitFG/Correspondence.lean:150                                │
│ Frozen          │ no                                                                         │
│ Needs premise   │ yes                                                                        │
│ Reason          │ Selector existence/equality uses the scoped B2 root premise (already       │
│                 │ applied). Existing scoped hypothesis or finite initial tree supplies it.   │
│ Premise source  │ none                                                                       │
│ Uses            │ lexMax, lexMax_eq_of_greatest, lexMax_insert, lexMax_spec                  │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 285: `AvailableChain.KitFG.lexMax_of_advance`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainKitFG/Correspondence.lean:176                                │
│ Frozen          │ no                                                                         │
│ Needs premise   │ yes                                                                        │
│ Reason          │ Selector existence/equality uses the scoped B2 root premise (already       │
│                 │ applied). Existing scoped hypothesis or finite initial tree supplies it.   │
│ Premise source  │ none                                                                       │
│ Uses            │ lexMax, lexMax_eq_of_greatest, lexMax_of_advance, lexMax_spec              │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 286: `AvailableChain.KitFG.lexMax_mono`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainKitFG/Correspondence.lean:219                                │
│ Frozen          │ no                                                                         │
│ Needs premise   │ yes                                                                        │
│ Reason          │ Selector existence/equality uses the scoped B2 root premise (already       │
│                 │ applied). Existing scoped hypothesis or finite initial tree supplies it.   │
│ Premise source  │ none                                                                       │
│ Uses            │ lexMax, lexMax_mono, lexMax_of_none, lexMax_spec                           │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 287: `AvailableChain.KitFG.storeInv_init`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainKitFG/Correspondence.lean:327                                │
│ Frozen          │ no                                                                         │
│ Needs premise   │ yes                                                                        │
│ Reason          │ Selector existence/equality uses the scoped B2 root premise (already       │
│                 │ applied). Existing scoped hypothesis or finite initial tree supplies it.   │
│ Premise source  │ none                                                                       │
│ Uses            │ lexMax, lexMax_eq_of_greatest                                              │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 288: `AvailableChain.KitFG.storeInv_accept`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainKitFG/Correspondence.lean:356                                │
│ Frozen          │ no                                                                         │
│ Needs premise   │ yes                                                                        │
│ Reason          │ Selector existence/equality uses the scoped B2 root premise (already       │
│                 │ applied). Existing scoped hypothesis or finite initial tree supplies it.   │
│ Premise source  │ none                                                                       │
│ Uses            │ lexMax, lexMax_insert, lexMax_of_advance                                   │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 289: `AvailableChain.KitFG.lexMax_of_candidate`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainKitFG/Correspondence.lean:600                                │
│ Frozen          │ no                                                                         │
│ Needs premise   │ yes                                                                        │
│ Reason          │ Selector existence/equality uses the scoped B2 root premise (already       │
│                 │ applied). Existing scoped hypothesis or finite initial tree supplies it.   │
│ Premise source  │ none                                                                       │
│ Uses            │ lexMax, lexMax_of_candidate, lexMax_spec                                   │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 290: `AvailableChain.KitFG.fjFrame_Z_mem_D`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainKitFG/Correspondence.lean:647                                │
│ Frozen          │ no                                                                         │
│ Needs premise   │ yes                                                                        │
│ Reason          │ Selector existence/equality uses the scoped B2 root premise (already       │
│                 │ applied). Existing scoped hypothesis or finite initial tree supplies it.   │
│ Premise source  │ none                                                                       │
│ Uses            │ lexMax_of_candidate                                                        │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 291: `AvailableChain.KitFG.frame_facts`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainKitFG/Correspondence.lean:758                                │
│ Frozen          │ no                                                                         │
│ Needs premise   │ yes                                                                        │
│ Reason          │ Selector existence/equality uses the scoped B2 root premise (already       │
│                 │ applied). Existing scoped hypothesis or finite initial tree supplies it.   │
│ Premise source  │ none                                                                       │
│ Uses            │ lexMax_spec                                                                │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 292: `AvailableChain.KitFG.lexMax_of_bridge`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainKitFG/FrameBridge.lean:30                                    │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ lexMax, lexMaxView, lexMaxView_def, lexMax_of_bridge                       │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 293: `AvailableChain.KitFG.fjControls_of_bridge`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainKitFG/FrameBridge.lean:77                                    │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ lexMax, lexMax_of_bridge                                                   │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 294: `AvailableChain.KitFG.lexMaxView`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainKitFG/FrameBridgeDef.lean:22                                 │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ lexMaxView                                                                 │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 295: `AvailableChain.KitFG.lexMaxView_def`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainKitFG/FrameBridgeDef.lean:30                                 │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Definition equation only; no selection existence is asserted.              │
│ Premise source  │ none                                                                       │
│ Uses            │ lexMaxView, lexMaxView_def                                                 │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 296: `AvailableChain.KitFG.fjControlsView`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainKitFG/FrameBridgeDef.lean:75                                 │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ lexMaxView                                                                 │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 297: `AvailableChain.KitFG.fjControlsView_def`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainKitFG/FrameBridgeDef.lean:81                                 │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Definition equation only; no selection existence is asserted.              │
│ Premise source  │ none                                                                       │
│ Uses            │ lexMaxView                                                                 │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 298: `AvailableChain.KitFG.frame_J_carrier`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainKitFG/FrameChannels.lean:16                                  │
│ Frozen          │ no                                                                         │
│ Needs premise   │ yes                                                                        │
│ Reason          │ Selector existence/equality uses the scoped B2 root premise (already       │
│                 │ applied). Existing scoped hypothesis or finite initial tree supplies it.   │
│ Premise source  │ none                                                                       │
│ Uses            │ lexMax_spec                                                                │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 299: `AvailableChain.KitFG.frameGeometry_lexMax_of_inv`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainKitFG/FrameGeometry.lean:46                                  │
│ Frozen          │ no                                                                         │
│ Needs premise   │ yes                                                                        │
│ Reason          │ Selector existence/equality uses the scoped B2 root premise (already       │
│                 │ applied). Existing scoped hypothesis or finite initial tree supplies it.   │
│ Premise source  │ none                                                                       │
│ Uses            │ frameGeometry_lexMax_of_inv, lexMaxView, lexMaxView_def                    │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 300: `AvailableChain.KitFG.storeControlsView_eq_fjControlsView_of_inv`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainKitFG/FrameGeometry.lean:85                                  │
│ Frozen          │ no                                                                         │
│ Needs premise   │ yes                                                                        │
│ Reason          │ Selector existence/equality uses the scoped B2 root premise (already       │
│                 │ applied). Existing scoped hypothesis or finite initial tree supplies it.   │
│ Premise source  │ none                                                                       │
│ Uses            │ frameGeometry_lexMax_of_inv                                                │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 301: `AvailableChain.KitFG.inBandLock`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainKitFG/InBandLock.lean:32                                     │
│ Frozen          │ no                                                                         │
│ Needs premise   │ yes                                                                        │
│ Reason          │ Selector existence/equality uses the scoped B2 root premise (already       │
│                 │ applied). Existing scoped hypothesis or finite initial tree supplies it.   │
│ Premise source  │ none                                                                       │
│ Uses            │ lexMax, lexMax_spec                                                        │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 302: `AvailableChain.KitFG.pins`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainKitFG/Pins.lean:152                                          │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ lexMax_of_candidate                                                        │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 303: `AvailableChain.KitFG.helpers`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainKitFG/Pins.lean:586                                          │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ lexMax_mono                                                                │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 304: `AvailableChain.KitFG.<example@771>`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainKitFG/Pins.lean:771                                          │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ lexMax_of_candidate                                                        │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 305: `AvailableChain.KitFG.<example@798>`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainKitFG/Pins.lean:798                                          │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ lexMax_mono                                                                │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 306: `AvailableChain.KitFG.noHighContest`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainKitFG/RecordHigh.lean:73                                     │
│ Frozen          │ no                                                                         │
│ Needs premise   │ yes                                                                        │
│ Reason          │ Selector existence/equality uses the scoped B2 root premise (already       │
│                 │ applied). Existing scoped hypothesis or finite initial tree supplies it.   │
│ Premise source  │ none                                                                       │
│ Uses            │ lexMax, lexMax_of_none, lexMax_spec                                        │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 307: `AvailableChain.KitFG.StoreInv`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainKitFG/StoreInvDef.lean:19                                    │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ lexMax                                                                     │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 308: `AvailableChain.KitFG.simplexStoreInvariant`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainKitFG/StoreSafetySimplex.lean:22                             │
│ Frozen          │ no                                                                         │
│ Needs premise   │ yes                                                                        │
│ Reason          │ Selector existence/equality uses the scoped B2 root premise (already       │
│                 │ applied). Existing scoped hypothesis or finite initial tree supplies it.   │
│ Premise source  │ none                                                                       │
│ Uses            │ lexMax_spec                                                                │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 313: `AvailableChain.KitFG.lexMax_fst_lt`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainKitFG/TwoChanges.lean:193                                    │
│ Frozen          │ no                                                                         │
│ Needs premise   │ yes                                                                        │
│ Reason          │ Selector existence/equality uses the scoped B2 root premise (already       │
│                 │ applied). Existing scoped hypothesis or finite initial tree supplies it.   │
│ Premise source  │ none                                                                       │
│ Uses            │ lexMax, lexMax_fst_lt, lexMax_of_none, lexMax_spec                         │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 314: `AvailableChain.KitFG.lexMax_top_of_carrier`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainKitFG/TwoChanges.lean:205                                    │
│ Frozen          │ no                                                                         │
│ Needs premise   │ yes                                                                        │
│ Reason          │ Selector existence/equality uses the scoped B2 root premise (already       │
│                 │ applied). Existing scoped hypothesis or finite initial tree supplies it.   │
│ Premise source  │ none                                                                       │
│ Uses            │ lexMax, lexMax_spec, lexMax_top_of_carrier                                 │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 315: `AvailableChain.KitFG.lexMax_carrier_of_top`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainKitFG/TwoChanges.lean:221                                    │
│ Frozen          │ no                                                                         │
│ Needs premise   │ yes                                                                        │
│ Reason          │ Selector existence/equality uses the scoped B2 root premise (already       │
│                 │ applied). Existing scoped hypothesis or finite initial tree supplies it.   │
│ Premise source  │ none                                                                       │
│ Uses            │ lexMax, lexMax_carrier_of_top, lexMax_of_none, lexMax_spec                 │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 316: `AvailableChain.KitFG.effFrame_of_bits`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainKitFG/TwoChanges.lean:247                                    │
│ Frozen          │ no                                                                         │
│ Needs premise   │ yes                                                                        │
│ Reason          │ Selector existence/equality uses the scoped B2 root premise (already       │
│                 │ applied). Existing scoped hypothesis or finite initial tree supplies it.   │
│ Premise source  │ none                                                                       │
│ Uses            │ lexMax, lexMax_carrier_of_top, lexMax_fst_lt, lexMax_top_of_carrier        │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 317: `AvailableChain.KitFG.Fmove_below`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainKitFG/TwoChanges.lean:517                                    │
│ Frozen          │ no                                                                         │
│ Needs premise   │ yes                                                                        │
│ Reason          │ Selector existence/equality uses the scoped B2 root premise (already       │
│                 │ applied). Existing scoped hypothesis or finite initial tree supplies it.   │
│ Premise source  │ none                                                                       │
│ Uses            │ lexMax, lexMax_carrier_of_top, lexMax_fst_lt, lexMax_of_advance,           │
│                 │ lexMax_top_of_carrier                                                      │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 318: `AvailableChain.KitFG.Fmove_atTop`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainKitFG/TwoChanges.lean:655                                    │
│ Frozen          │ no                                                                         │
│ Needs premise   │ yes                                                                        │
│ Reason          │ Selector existence/equality uses the scoped B2 root premise (already       │
│                 │ applied). Existing scoped hypothesis or finite initial tree supplies it.   │
│ Premise source  │ none                                                                       │
│ Uses            │ lexMax, lexMax_carrier_of_top, lexMax_top_of_carrier                       │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 319: `AvailableChain.LStar.ghostStep`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainLStar/Model/Protocol.lean:135                                │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ ghostStep                                                                  │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 320: `AvailableChain.LStar.ghostWalk`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainLStar/Model/Protocol.lean:150                                │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ ghostStep, ghostWalk                                                       │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 321: `AvailableChain.LStar.ghost`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainLStar/Model/Protocol.lean:158                                │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ ghost, ghostWalk                                                           │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 322: `AvailableChain.LStar.forkChoice`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainLStar/Model/Protocol.lean:248                                │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ ghost                                                                      │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 323: `AvailableChain.LStar.confirmation`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainLStar/Model/Protocol.lean:360                                │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ ghost                                                                      │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 324: `AvailableChain.SAPC.floor`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainSAPC/Model/Choice.lean:26                                    │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ ghost                                                                      │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 325: `AvailableChain.SAPC.choice`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainSAPC/Model/Choice.lean:44                                    │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ ghost                                                                      │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 326: `AvailableChain.SAPC.active_quorum_walk_covers`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainSAPC/Proofs/EffectiveScores.lean:156                         │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ ghost, ghost_covers_of_path_dominance                                      │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 327: `AvailableChain.SAPC.floor_properties`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainSAPC/Proofs/Floor.lean:60                                    │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ ghost                                                                      │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 328: `AvailableChain.SAPC.floor_covers`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainSAPC/Proofs/Floor.lean:79                                    │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ ghost                                                                      │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 329: `AvailableChain.SAPC.choice_covers_of_floor`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainSAPC/Proofs/Floor.lean:133                                   │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ ghost_extends                                                              │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 330: `AvailableChain.SAPC.choice_covers_of_ordinary_floor`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainSAPC/Proofs/Floor.lean:175                                   │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ ghost                                                                      │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 331: `AvailableChain.SAPC.choice_covers_of_genuine_transfer`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainSAPC/Proofs/GenuineTransfer.lean:392                         │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ ghost, ghost_covers_of_path_dominance                                      │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 332: `AvailableChain.SAPC.choice_mem_blocks`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainSAPC/Proofs/HeadTargets.lean:88                              │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ ghost, ghostWalk_mem                                                       │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 333: `AvailableChain.SAPC.choice_extends_liveRoot`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainSAPC/Proofs/OutageProtection.lean:13                         │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ ghost_extends                                                              │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 334: `AvailableChain.SAPC.floor_prefix_of_score_transport`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainSAPC/Proofs/ProposalFloors.lean:8                            │
│ Frozen          │ no                                                                         │
│ Needs premise   │ yes                                                                        │
│ Reason          │ Equal best keys need uniqueness on the walked tree. Existing scoped        │
│                 │ hypothesis or finite initial tree supplies it.                             │
│ Premise source  │ none                                                                       │
│ Uses            │ ghost_prefix_of_score_transport                                            │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 335: `AvailableChain.SAPC.clean_active_honest_proposal_head`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainSAPC/Proofs/ProposalHeads.lean:82                            │
│ Frozen          │ no                                                                         │
│ Needs premise   │ yes                                                                        │
│ Reason          │ Equal best keys need uniqueness on the walked tree. Existing scoped        │
│                 │ hypothesis or finite initial tree supplies it.                             │
│ Premise source  │ none                                                                       │
│ Uses            │ ghost_adopts_of_eligible_proposal_transport                                │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 336: `AvailableChain.SAPC.clean_proposal_parent_ordinary`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainSAPC/Proofs/ProposalRoots.lean:156                           │
│ Frozen          │ no                                                                         │
│ Needs premise   │ yes                                                                        │
│ Reason          │ Equal best keys need uniqueness on the walked tree. Existing scoped        │
│                 │ hypothesis or finite initial tree supplies it.                             │
│ Premise source  │ none                                                                       │
│ Uses            │ ghost, ghostWalk_mem, ghost_reanchor                                       │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 337: `AvailableChain.SAPC.recovery_honest_proposal_head_quorum`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainSAPC/Proofs/RecoveryProposal.lean:165                        │
│ Frozen          │ no                                                                         │
│ Needs premise   │ yes                                                                        │
│ Reason          │ Equal best keys need uniqueness on the walked tree. Existing scoped        │
│                 │ hypothesis or finite initial tree supplies it.                             │
│ Premise source  │ none                                                                       │
│ Uses            │ ghost, ghost_adopts_of_rooted_proposal_transport, ghost_extends            │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 338: `AvailableChain.SAPC.choice_covers_of_pc`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainSAPC/Proofs/StrongSteps.lean:51                              │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ ghost_extends                                                              │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 342: `AvailableChain.SimplexFG.lexMax`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainSimplexFG/Frame.lean:95                                      │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ lexMax                                                                     │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 343: `AvailableChain.SimplexFG.fjControls`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainSimplexFG/Frame.lean:105                                     │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ lexMax                                                                     │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

## W2 users

Entry 25: `AvailableChain.FGSA.Run.fgsa_tWalk`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainFGSAProofs/Proofs/Finality/CoreServices.lean:65              │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ walk_best_ancestry_of_cover                                                │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 26: `AvailableChain.FGSA.Run.healing_proposer_floor`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainFGSAProofs/Proofs/Healing/Frame.lean:176                     │
│ Frozen          │ no                                                                         │
│ Needs premise   │ yes                                                                        │
│ Reason          │ Equal best keys need uniqueness on the walked tree. Store/prefix invariant │
│                 │ is available in this caller.                                               │
│ Premise source  │ CStoreInv                                                                  │
│ Uses            │ fgsa_headInTree_noEligibleChild                                            │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 27: `AvailableChain.FGSA.Run.written_walk_extends`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainFGSAProofs/Proofs/Healing/PostResetLeaseStep.lean:34         │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ DominatedSuffix_def, ghost, walk_covers_of_dominated_suffix                │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 28: `AvailableChain.FGSA.Run.fgsa_gate_zero_of_receipts`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainFGSAProofs/Proofs/Shared/Count.lean:296                      │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ DominatedSuffix, DominatedSuffix_def, NoEligibleChild,                     │
│                 │ NoEligibleChild_def, ghost, walk_exact_of_dominated_suffix                 │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 29: `AvailableChain.FGSA.Run.fgsa_headVote_best_ancestry_of_cover`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainFGSAProofs/Proofs/Shared/ExactHead.lean:18                   │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ walk_best_ancestry_of_cover                                                │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 30: `AvailableChain.FGSA.Run.ExactHeadGeometry`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainFGSAProofs/Proofs/Shared/ExactHead.lean:44                   │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ NoEligibleChild                                                            │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 31: `AvailableChain.FGSA.Run.fgsa_headVote_exact_of_covered_parent`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainFGSAProofs/Proofs/Shared/ExactHead.lean:60                   │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ DominatedSuffix                                                            │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 32: `AvailableChain.FGSA.Run.exactHead_of_proposal_on_run`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainFGSAProofs/Proofs/Shared/ExactHead.lean:89                   │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ fgsa_ghost_transfer_sfx_on_run, walk_covers_of_dominated_suffix            │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 33: `AvailableChain.FGSA.Run.exactService_gate_raw_of_head`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainFGSAProofs/Proofs/Shared/ExactService.lean:81                │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ ghost                                                                      │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 34: `AvailableChain.FGSA.Run.fgsa_headReachesLo`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainFGSAProofs/Proofs/Shared/HeadGeometry.lean:16                │
│ Frozen          │ no                                                                         │
│ Needs premise   │ yes                                                                        │
│ Reason          │ Equal best keys need uniqueness on the walked tree. Store/prefix invariant │
│                 │ is available in this caller.                                               │
│ Premise source  │ CStoreInv                                                                  │
│ Uses            │ fgsa_headInTree_noEligibleChild, walk_exact_of_dominated_suffix            │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 35: `AvailableChain.FGSA.Run.fgsa_domain_anchorClosed_mono`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainFGSAProofs/Proofs/Shared/KeepExact.lean:99                   │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ AnchorClosed                                                               │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 36: `AvailableChain.FGSA.Run.exactHead_of_pivot_ancestry`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainFGSAProofs/Proofs/Shared/KeepExact.lean:129                  │
│ Frozen          │ no                                                                         │
│ Needs premise   │ yes                                                                        │
│ Reason          │ Equal best keys need uniqueness on the walked tree. Local helper lacks     │
│                 │ invariant; W2 must thread a class premise.                                 │
│ Premise source  │ none                                                                       │
│ Uses            │ DominatedSuffix, NoEligibleChild, fgsa_headInTree_reanchor_of_pivot,       │
│                 │ walk_exact_of_dominated_suffix                                             │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 37: `AvailableChain.FGSA.Run.exactHead_of_pivot`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainFGSAProofs/Proofs/Shared/KeepExact.lean:195                  │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ AnchorClosed, DominatedSuffix, NoEligibleChild, SuffixPersists,            │
│                 │ SuffixReflects, SuffixScoresAgree, ghost, ghost_transfer_sfx,              │
│                 │ walk_best_ancestry_of_cover, walk_reanchor_of_dominated_suffix             │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 38: `AvailableChain.FGSA.Run.fgsa_ghost_transfer_sfx_on_clean`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainFGSAProofs/Proofs/Shared/Regimes.lean:406                    │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ fgsa_ghost_transfer_sfx_on_clean, fgsa_ghost_transfer_sfx_on_run           │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 39: `AvailableChain.FGSA.Run.fgsa_ghost_transfer_sfx_on_recovery`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainFGSAProofs/Proofs/Shared/Regimes.lean:447                    │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ fgsa_ghost_transfer_sfx_on_recovery, fgsa_ghost_transfer_sfx_on_run        │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 40: `AvailableChain.FGSA.Run.consumer_supported_cover`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainFGSAProofs/Proofs/Shared/RetainedConsumers.lean:50           │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ ghost                                                                      │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 41: `AvailableChain.FGSA.Run.consumer_prior_cover`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainFGSAProofs/Proofs/Shared/RetainedConsumers.lean:76           │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ DominatedSuffix_def, ghost, walk_covers_of_dominated_suffix                │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 42: `AvailableChain.FGSA.Run.consumer_trunk_prefix`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainFGSAProofs/Proofs/Shared/RetainedConsumers.lean:128          │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ BestAncestry                                                               │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 43: `AvailableChain.FGSA.Run.consumer_h6_fields`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainFGSAProofs/Proofs/Shared/RetainedConsumers.lean:250          │
│ Frozen          │ no                                                                         │
│ Needs premise   │ yes                                                                        │
│ Reason          │ Equal best keys need uniqueness on the walked tree. Store/prefix invariant │
│                 │ is available in this caller.                                               │
│ Premise source  │ CStoreInv                                                                  │
│ Uses            │ walk_best_ancestry_of_cover, walk_reanchor_of_best_ancestry                │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 44: `AvailableChain.FGSA.Run.fgsa_retainedReads_H6`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainFGSAProofs/Proofs/Shared/RetainedConsumers.lean:333          │
│ Frozen          │ no                                                                         │
│ Needs premise   │ yes                                                                        │
│ Reason          │ Equal best keys need uniqueness on the walked tree. Store/prefix invariant │
│                 │ is available in this caller.                                               │
│ Premise source  │ CStoreInv                                                                  │
│ Uses            │ walk_best_ancestry_of_cover, walk_reanchor_of_best_ancestry                │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 45: `AvailableChain.FGSA.Run.consumer_cone_starts`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainFGSAProofs/Proofs/Shared/RetainedConsumers.lean:444          │
│ Frozen          │ no                                                                         │
│ Needs premise   │ yes                                                                        │
│ Reason          │ Equal best keys need uniqueness on the walked tree. Store/prefix invariant │
│                 │ is available in this caller.                                               │
│ Premise source  │ CStoreInv                                                                  │
│ Uses            │ BestAncestry, walk_best_ancestry_of_cover, walk_reanchor_of_best_ancestry  │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 46: `AvailableChain.FGSA.Run.consumer_cone_fields`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainFGSAProofs/Proofs/Shared/RetainedConsumers.lean:552          │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ walk_best_ancestry_of_cover                                                │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 47: `AvailableChain.FGSA.Run.fgsa_exactHeadGeometry_of_retained_endpoint`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainFGSAProofs/Proofs/Shared/RetainedEndpoint.lean:64            │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ NoEligibleChild                                                            │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 48: `AvailableChain.FGSA.Run.headInTree_unfold`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainFGSAProofs/Proofs/Shared/RetainedEndpoint.lean:93            │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ ghost                                                                      │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 49: `AvailableChain.FGSA.Run.fgsa_headVote_covers_parent_of_retained_geometry`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainFGSAProofs/Proofs/Shared/RetainedEndpoint.lean:103           │
│ Frozen          │ no                                                                         │
│ Needs premise   │ yes                                                                        │
│ Reason          │ Equal best keys need uniqueness on the walked tree. Local helper lacks     │
│                 │ invariant; W2 must thread a class premise.                                 │
│ Premise source  │ none                                                                       │
│ Uses            │ BestAncestry_def, ghost, walk_covers_of_retained_transport                 │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 50: `AvailableChain.FGSA.Run.fgsa_retained_source_stop`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainFGSAProofs/Proofs/Shared/RetainedEndpoint.lean:239           │
│ Frozen          │ no                                                                         │
│ Needs premise   │ yes                                                                        │
│ Reason          │ Equal best keys need uniqueness on the walked tree. Store/prefix invariant │
│                 │ is available in this caller.                                               │
│ Premise source  │ CStoreInv                                                                  │
│ Uses            │ NoEligibleChild, fgsa_headInTree_noEligibleChild                           │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 51: `AvailableChain.FGSA.Run.fgsa_retained_persists_of_path`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainFGSAProofs/Proofs/Shared/RetainedPersist.lean:131            │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ SuffixPersists                                                             │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 52: `AvailableChain.FGSA.Run.fgsa_retained_path_persists_on_run`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainFGSAProofs/Proofs/Shared/RetainedPersist.lean:234            │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ SuffixPersists                                                             │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 53: `AvailableChain.FGSA.Run.RetainedReadPremises`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainFGSAProofs/Proofs/Shared/RetainedReflect.lean:54             │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ BestAncestry                                                               │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 54: `AvailableChain.FGSA.Run.fgsa_retained_old_child_reflects_on_run`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainFGSAProofs/Proofs/Shared/RetainedReflect.lean:286            │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ SuffixReflects                                                             │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 55: `AvailableChain.FGSA.Run.fgsa_retained_scores_of_candidates`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainFGSAProofs/Proofs/Shared/RetainedScores.lean:119             │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ SuffixScoresAgree                                                          │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 56: `AvailableChain.FGSA.Run.RetainedWalkRunGeometry`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainFGSAProofs/Proofs/Shared/RetainedWalk.lean:65                │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ BestAncestry, SuffixPersists, SuffixReflects, SuffixScoresAgree            │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 57: `AvailableChain.FGSA.Run.fgsa_retained_prefix_of_trunk_or_support`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainFGSAProofs/Proofs/Shared/RetainedWalk.lean:101               │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ BestAncestry                                                               │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 58: `AvailableChain.FGSA.fgsa_ordinary_parent_of_live_prefix`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainFGSAProofs/Proofs/Shared/RetainedWalkStore.lean:26           │
│ Frozen          │ no                                                                         │
│ Needs premise   │ yes                                                                        │
│ Reason          │ Equal best keys need uniqueness on the walked tree. Local helper lacks     │
│                 │ invariant; W2 must thread a class premise.                                 │
│ Premise source  │ none                                                                       │
│ Uses            │ ghost, walk_reanchor_of_best_ancestry                                      │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 59: `AvailableChain.FGSA.fgsa_ordinary_parent_of_live_cover`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainFGSAProofs/Proofs/Shared/RetainedWalkStore.lean:59           │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ ghost, walk_best_ancestry_of_cover                                         │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 60: `AvailableChain.FGSA.Run.WalkRunGeometry`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainFGSAProofs/Proofs/Shared/ScoreRun.lean:25                    │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ DominatedSuffix                                                            │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 61: `AvailableChain.FGSA.Run.walkRun_step_child`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainFGSAProofs/Proofs/Shared/ScoreRun.lean:1211                  │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ ghostStep                                                                  │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 62: `AvailableChain.FGSA.Run.fgsa_ghost_transfer_sfx_on_run`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainFGSAProofs/Proofs/Shared/ScoreRun.lean:1267                  │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ SuffixPersists, SuffixReflects, SuffixScoresAgree,                         │
│                 │ fgsa_ghost_transfer_sfx_on_run, ghost, ghost_transfer_sfx,                 │
│                 │ walk_covers_of_dominated_suffix, walk_reanchor_of_dominated_suffix         │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

## W3 users

Entry 19: `#print axioms AvailableChain.GridCO.ghostStep_child`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainFGSA/Tests/Axioms.lean:321                                   │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Audit/reference only; no proof call.                                       │
│ Premise source  │ none                                                                       │
│ Uses            │ ghostStep_child                                                            │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 20: `#print axioms AvailableChain.GridCO.ghostWalk_mem`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainFGSA/Tests/Axioms.lean:322                                   │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Audit/reference only; no proof call.                                       │
│ Premise source  │ none                                                                       │
│ Uses            │ ghostWalk_mem                                                              │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 21: `#print axioms AvailableChain.FGSA.fgsa_getHead_reanchor_of_dominated_suffix`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainFGSA/Tests/Axioms.lean:356                                   │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Audit/reference only; no proof call.                                       │
│ Premise source  │ none                                                                       │
│ Uses            │ fgsa_getHead_reanchor_of_dominated_suffix                                  │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 22: `#print axioms AvailableChain.FGSA.fgsa_headInTree_noEligibleChild`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainFGSA/Tests/Axioms.lean:368                                   │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Audit/reference only; no proof call.                                       │
│ Premise source  │ none                                                                       │
│ Uses            │ fgsa_headInTree_noEligibleChild                                            │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 23: `#print axioms AvailableChain.FGSA.fgsa_headInTree_reanchor_of_pivot`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainFGSA/Tests/Axioms.lean:371                                   │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Audit/reference only; no proof call.                                       │
│ Premise source  │ none                                                                       │
│ Uses            │ fgsa_headInTree_reanchor_of_pivot                                          │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 24: `#print axioms AvailableChain.FGSA.Window.window_lexMax_eq`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainFGSA/Tests/Axioms.lean:472                                   │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Audit/reference only; no proof call.                                       │
│ Premise source  │ none                                                                       │
│ Uses            │ window_lexMax_eq                                                           │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 63: `#print axioms AvailableChain.FGSA.Run.fgsa_ghost_transfer_sfx_on_run`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainFGSAProofs/Tests/Axioms.lean:708                             │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Audit/reference only; no proof call.                                       │
│ Premise source  │ none                                                                       │
│ Uses            │ fgsa_ghost_transfer_sfx_on_run                                             │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 64: `#print axioms AvailableChain.FGSA.Run.fgsa_ghost_transfer_sfx_on_clean`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainFGSAProofs/Tests/Axioms.lean:709                             │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Audit/reference only; no proof call.                                       │
│ Premise source  │ none                                                                       │
│ Uses            │ fgsa_ghost_transfer_sfx_on_clean                                           │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 65: `#print axioms AvailableChain.FGSA.Run.fgsa_ghost_transfer_sfx_on_recovery`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainFGSAProofs/Tests/Axioms.lean:710                             │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Audit/reference only; no proof call.                                       │
│ Premise source  │ none                                                                       │
│ Uses            │ fgsa_ghost_transfer_sfx_on_recovery                                        │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 66: `AvailableChain.FGSA.Run.Tests.KeepExact.upperStartEmptyTreeCounterexample`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainFGSAProofs/Tests/KeepExact.lean:15                           │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ AnchorClosed, DominatedSuffix, NoEligibleChild, SuffixPersists,            │
│                 │ SuffixReflects, SuffixScoresAgree, ghost                                   │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 67: `AvailableChain.FGSA.Run.Tests.KeepExact.<example@82>`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainFGSAProofs/Tests/KeepExact.lean:82                           │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ ghost                                                                      │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 68: `AvailableChain.FGSA.Run.Tests.KeepExact.maximalScoreAncestryCounterexample`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainFGSAProofs/Tests/KeepExact.lean:86                           │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ ghost                                                                      │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 69: `AvailableChain.FGSA.Run.Tests.KeepExact.maximalScoreAllWalkPremisesCounterexample`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainFGSAProofs/Tests/KeepExact.lean:119                          │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ AnchorClosed, DominatedSuffix, NoEligibleChild, SuffixPersists,            │
│                 │ SuffixReflects, SuffixScoresAgree, SuffixScoresAgree_def, ghost, ghostStep │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 70: `AvailableChain.FGSA.Run.Tests.KeepExact.intermediateAnchorReanchor`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainFGSAProofs/Tests/KeepExact.lean:291                          │
│ Frozen          │ no                                                                         │
│ Needs premise   │ yes                                                                        │
│ Reason          │ Fixture must supply its finite scope; W3 owns migration.                   │
│ Premise source  │ none                                                                       │
│ Uses            │ ghost, walk_best_ancestry_of_cover, walk_reanchor_of_best_ancestry         │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 71: `AvailableChain.FGSA.Run.Tests.RetainedEndpoint.consumer_source_prefix`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainFGSAProofs/Tests/RetainedEndpoint.lean:298                   │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ BestAncestry, BestAncestry_def                                             │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 72: `AvailableChain.FGSA.Run.Tests.RetainedEndpoint.consumer_H6_instance`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainFGSAProofs/Tests/RetainedEndpoint.lean:334                   │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ BestAncestry_def                                                           │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 73: `AvailableChain.FGSA.Run.Tests.RetainedPersist.persists_instance`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainFGSAProofs/Tests/RetainedPersist.lean:173                    │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ SuffixPersists                                                             │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 74: `AvailableChain.FGSA.Run.Tests.RetainedPersist.selected_edge`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainFGSAProofs/Tests/RetainedPersist.lean:189                    │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ ghostStep                                                                  │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 75: `AvailableChain.FGSA.Run.Tests.RetainedScores.retained_scores`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainFGSAProofs/Tests/RetainedScores.lean:104                     │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ SuffixScoresAgree                                                          │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 76: `AvailableChain.FGSA.Run.Tests.RetainedWalk.trunk_and_support`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainFGSAProofs/Tests/RetainedWalk.lean:51                        │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ BestAncestry                                                               │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 77: `AvailableChain.FGSA.Run.Tests.RetainedWalk.walk_geometry`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainFGSAProofs/Tests/RetainedWalk.lean:90                        │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ walk_geometry                                                              │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 183: `#print axioms AvailableChain.Gen.Pure.DominatedSuffix_def`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGeneric/Tests/Axioms.lean:160                                │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Audit/reference only; no proof call.                                       │
│ Premise source  │ none                                                                       │
│ Uses            │ DominatedSuffix_def                                                        │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 184: `#print axioms AvailableChain.Gen.Pure.NoEligibleChild_def`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGeneric/Tests/Axioms.lean:161                                │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Audit/reference only; no proof call.                                       │
│ Premise source  │ none                                                                       │
│ Uses            │ NoEligibleChild_def                                                        │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 185: `#print axioms AvailableChain.Gen.Pure.AnchorClosed_def`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGeneric/Tests/Axioms.lean:162                                │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Audit/reference only; no proof call.                                       │
│ Premise source  │ none                                                                       │
│ Uses            │ AnchorClosed_def                                                           │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 186: `#print axioms AvailableChain.Gen.Pure.DescendantDepthBound_def`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGeneric/Tests/Axioms.lean:163                                │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Audit/reference only; no proof call.                                       │
│ Premise source  │ none                                                                       │
│ Uses            │ DescendantDepthBound_def                                                   │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 187: `#print axioms AvailableChain.Gen.Pure.SuffixPersists_def`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGeneric/Tests/Axioms.lean:164                                │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Audit/reference only; no proof call.                                       │
│ Premise source  │ none                                                                       │
│ Uses            │ SuffixPersists_def                                                         │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 188: `#print axioms AvailableChain.Gen.Pure.SuffixReflects_def`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGeneric/Tests/Axioms.lean:165                                │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Audit/reference only; no proof call.                                       │
│ Premise source  │ none                                                                       │
│ Uses            │ SuffixReflects_def                                                         │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 189: `#print axioms AvailableChain.Gen.Pure.SuffixScoresAgree_def`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGeneric/Tests/Axioms.lean:166                                │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Audit/reference only; no proof call.                                       │
│ Premise source  │ none                                                                       │
│ Uses            │ SuffixScoresAgree_def                                                      │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 190: `#print axioms AvailableChain.Gen.Pure.walk_covers_of_dominated_suffix_statement`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGeneric/Tests/Axioms.lean:431                                │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Audit/reference only; no proof call.                                       │
│ Premise source  │ none                                                                       │
│ Uses            │ walk_covers_of_dominated_suffix_statement                                  │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 191: `#print axioms AvailableChain.Gen.Pure.walk_covers_of_dominated_suffix`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGeneric/Tests/Axioms.lean:432                                │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Audit/reference only; no proof call.                                       │
│ Premise source  │ none                                                                       │
│ Uses            │ walk_covers_of_dominated_suffix                                            │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 192: `#print axioms AvailableChain.Gen.Pure.walk_exact_of_dominated_suffix_statement`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGeneric/Tests/Axioms.lean:433                                │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Audit/reference only; no proof call.                                       │
│ Premise source  │ none                                                                       │
│ Uses            │ walk_exact_of_dominated_suffix_statement                                   │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 193: `#print axioms AvailableChain.Gen.Pure.walk_exact_of_dominated_suffix`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGeneric/Tests/Axioms.lean:434                                │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Audit/reference only; no proof call.                                       │
│ Premise source  │ none                                                                       │
│ Uses            │ walk_exact_of_dominated_suffix                                             │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 194: `#print axioms AvailableChain.Gen.Pure.walk_reanchor_of_dominated_suffix_statement`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGeneric/Tests/Axioms.lean:435                                │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Audit/reference only; no proof call.                                       │
│ Premise source  │ none                                                                       │
│ Uses            │ walk_reanchor_of_dominated_suffix_statement                                │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 195: `#print axioms AvailableChain.Gen.Pure.walk_reanchor_of_dominated_suffix`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGeneric/Tests/Axioms.lean:436                                │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Audit/reference only; no proof call.                                       │
│ Premise source  │ none                                                                       │
│ Uses            │ walk_reanchor_of_dominated_suffix                                          │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 196: `#print axioms AvailableChain.Gen.Pure.walk_avoids_unsupported_child_statement`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGeneric/Tests/Axioms.lean:437                                │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Audit/reference only; no proof call.                                       │
│ Premise source  │ none                                                                       │
│ Uses            │ walk_avoids_unsupported_child_statement                                    │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 197: `#print axioms AvailableChain.Gen.Pure.walk_avoids_unsupported_child`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGeneric/Tests/Axioms.lean:438                                │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Audit/reference only; no proof call.                                       │
│ Premise source  │ none                                                                       │
│ Uses            │ walk_avoids_unsupported_child                                              │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 198:
`#print axioms AvailableChain.Gen.Pure.walk_covers_of_dominated_suffix_of_anchor_eligible_statement`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGeneric/Tests/Axioms.lean:439                                │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Audit/reference only; no proof call.                                       │
│ Premise source  │ none                                                                       │
│ Uses            │ walk_covers_of_dominated_suffix_of_anchor_eligible_statement               │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 199:
`#print axioms AvailableChain.Gen.Pure.walk_covers_of_dominated_suffix_of_anchor_eligible`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGeneric/Tests/Axioms.lean:440                                │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Audit/reference only; no proof call.                                       │
│ Premise source  │ none                                                                       │
│ Uses            │ walk_covers_of_dominated_suffix_of_anchor_eligible                         │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 200: `#print axioms AvailableChain.Gen.Pure.walk_terminal_of_descendant_depth_bound_statement`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGeneric/Tests/Axioms.lean:441                                │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Audit/reference only; no proof call.                                       │
│ Premise source  │ none                                                                       │
│ Uses            │ walk_terminal_of_descendant_depth_bound_statement                          │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 201: `#print axioms AvailableChain.Gen.Pure.walk_terminal_of_descendant_depth_bound`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGeneric/Tests/Axioms.lean:442                                │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Audit/reference only; no proof call.                                       │
│ Premise source  │ none                                                                       │
│ Uses            │ walk_terminal_of_descendant_depth_bound                                    │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 202: `#print axioms AvailableChain.Gen.Pure.walk_noEligibleChild_of_anchorClosed_statement`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGeneric/Tests/Axioms.lean:443                                │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Audit/reference only; no proof call.                                       │
│ Premise source  │ none                                                                       │
│ Uses            │ walk_noEligibleChild_of_anchorClosed_statement                             │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 203: `#print axioms AvailableChain.Gen.Pure.walk_noEligibleChild_of_anchorClosed`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGeneric/Tests/Axioms.lean:444                                │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Audit/reference only; no proof call.                                       │
│ Premise source  │ none                                                                       │
│ Uses            │ walk_noEligibleChild_of_anchorClosed                                       │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 204: `#print axioms AvailableChain.Gen.Pure.ghost_transfer_sfx_statement`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGeneric/Tests/Axioms.lean:445                                │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Audit/reference only; no proof call.                                       │
│ Premise source  │ none                                                                       │
│ Uses            │ ghost_transfer_sfx_statement                                               │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 205: `#print axioms AvailableChain.Gen.Pure.ghost_transfer_sfx`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGeneric/Tests/Axioms.lean:446                                │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Audit/reference only; no proof call.                                       │
│ Premise source  │ none                                                                       │
│ Uses            │ ghost_transfer_sfx                                                         │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 206: `#print axioms AvailableChain.Gen.Pure.walk_reanchor_of_best_ancestry`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGeneric/Tests/Axioms.lean:620                                │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Audit/reference only; no proof call.                                       │
│ Premise source  │ none                                                                       │
│ Uses            │ walk_reanchor_of_best_ancestry                                             │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 207: `#print axioms AvailableChain.Gen.Pure.walk_best_ancestry_of_cover`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGeneric/Tests/Axioms.lean:621                                │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Audit/reference only; no proof call.                                       │
│ Premise source  │ none                                                                       │
│ Uses            │ walk_best_ancestry_of_cover                                                │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 208: `#print axioms AvailableChain.Gen.Pure.BestAncestry`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGeneric/Tests/Axioms.lean:790                                │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Audit/reference only; no proof call.                                       │
│ Premise source  │ none                                                                       │
│ Uses            │ BestAncestry                                                               │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 209: `#print axioms AvailableChain.Gen.Pure.BestAncestry_def`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGeneric/Tests/Axioms.lean:791                                │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Audit/reference only; no proof call.                                       │
│ Premise source  │ none                                                                       │
│ Uses            │ BestAncestry_def                                                           │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 210: `#print axioms AvailableChain.Gen.Pure.WalkCoversOfRetainedTransportStatement`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGeneric/Tests/Axioms.lean:792                                │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Audit/reference only; no proof call.                                       │
│ Premise source  │ none                                                                       │
│ Uses            │ WalkCoversOfRetainedTransportStatement                                     │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 211: `#print axioms AvailableChain.Gen.Pure.WalkCoversOfRetainedTransportStatement_def`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGeneric/Tests/Axioms.lean:793                                │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Audit/reference only; no proof call.                                       │
│ Premise source  │ none                                                                       │
│ Uses            │ WalkCoversOfRetainedTransportStatement_def                                 │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 212: `#print axioms AvailableChain.Gen.Pure.walk_covers_of_retained_transport`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGeneric/Tests/Axioms.lean:794                                │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Audit/reference only; no proof call.                                       │
│ Premise source  │ none                                                                       │
│ Uses            │ walk_covers_of_retained_transport                                          │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 213: `#print axioms AvailableChain.Gen.Pure.walk_covers_of_retained_transport_statement`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGeneric/Tests/Axioms.lean:795                                │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Audit/reference only; no proof call.                                       │
│ Premise source  │ none                                                                       │
│ Uses            │ walk_covers_of_retained_transport_statement                                │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 214: `#print axioms AvailableChain.Gen.Pure.bestAncestry_restrict`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGeneric/Tests/Axioms.lean:796                                │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Audit/reference only; no proof call.                                       │
│ Premise source  │ none                                                                       │
│ Uses            │ bestAncestry_restrict                                                      │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 215: `#print axioms AvailableChain.Gen.Pure.bestAncestry_concat`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGeneric/Tests/Axioms.lean:797                                │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Audit/reference only; no proof call.                                       │
│ Premise source  │ none                                                                       │
│ Uses            │ bestAncestry_concat                                                        │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 216: `#print axioms AvailableChain.Gen.Pure.bestAncestry_of_dominatedSuffix`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGeneric/Tests/Axioms.lean:798                                │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Audit/reference only; no proof call.                                       │
│ Premise source  │ none                                                                       │
│ Uses            │ bestAncestry_of_dominatedSuffix                                            │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 217: `AvailableChain.Gen.AC.Tests.Batch.<example@30>`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGeneric/Tests/Batch.lean:30                                  │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ ghost                                                                      │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 218: `AvailableChain.Gen.AC.Tests.Batch.<example@56>`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGeneric/Tests/Batch.lean:56                                  │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ ghost                                                                      │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 219: `AvailableChain.Gen.Pure.Tests.RetainedWalk.retained_walk_root_ties`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGeneric/Tests/RetainedWalk.lean:20                           │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ ghostStep                                                                  │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 220: `AvailableChain.Gen.Pure.Tests.RetainedWalk.retained_walk_tie_reverse_list`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGeneric/Tests/RetainedWalk.lean:27                           │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ ghostStep                                                                  │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 221: `AvailableChain.Gen.Pure.Tests.RetainedWalk.retained_walk_tie_not_dominated`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGeneric/Tests/RetainedWalk.lean:31                           │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ DominatedSuffix                                                            │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 222: `AvailableChain.Gen.Pure.Tests.RetainedWalk.retained_walk_suffix_fields`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGeneric/Tests/RetainedWalk.lean:51                           │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ SuffixPersists, SuffixReflects, SuffixScoresAgree, ghostStep               │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 223: `AvailableChain.Gen.Pure.Tests.RetainedWalk.retained_walk_removed_trunk_transport`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGeneric/Tests/RetainedWalk.lean:70                           │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ BestAncestry, SuffixPersists, SuffixReflects, SuffixScoresAgree,           │
│                 │ walk_best_ancestry_of_cover                                                │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 224: `AvailableChain.Gen.Pure.Tests.RetainedWalk.retained_walk_source_before_target`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGeneric/Tests/RetainedWalk.lean:85                           │
│ Frozen          │ no                                                                         │
│ Needs premise   │ yes                                                                        │
│ Reason          │ Fixture must supply its finite scope; W3 owns migration.                   │
│ Premise source  │ none                                                                       │
│ Uses            │ ghost, walk_covers_of_retained_transport                                   │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 225: `AvailableChain.Gen.Pure.Tests.RetainedWalk.retained_walk_lower_target_transport`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGeneric/Tests/RetainedWalk.lean:95                           │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ BestAncestry, SuffixPersists, SuffixReflects, SuffixScoresAgree,           │
│                 │ walk_best_ancestry_of_cover                                                │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 226: `AvailableChain.Gen.Pure.Tests.RetainedWalk.retained_walk_target_before_source`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGeneric/Tests/RetainedWalk.lean:115                          │
│ Frozen          │ no                                                                         │
│ Needs premise   │ yes                                                                        │
│ Reason          │ Fixture must supply its finite scope; W3 owns migration.                   │
│ Premise source  │ none                                                                       │
│ Uses            │ ghost, walk_covers_of_retained_transport                                   │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 227: `AvailableChain.Gen.Pure.Tests.RetainedWalk.retained_walk_self_best`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGeneric/Tests/RetainedWalk.lean:132                          │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ BestAncestry                                                               │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 228: `AvailableChain.Gen.Pure.Tests.RetainedWalk.retained_walk_self_suffix`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGeneric/Tests/RetainedWalk.lean:137                          │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ SuffixPersists, SuffixReflects, SuffixScoresAgree                          │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 229: `AvailableChain.Gen.Pure.Tests.RetainedWalk.retained_walk_zero_length_prefix`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGeneric/Tests/RetainedWalk.lean:150                          │
│ Frozen          │ no                                                                         │
│ Needs premise   │ yes                                                                        │
│ Reason          │ Fixture must supply its finite scope; W3 owns migration.                   │
│ Premise source  │ none                                                                       │
│ Uses            │ ghost, walk_covers_of_retained_transport                                   │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 230: `AvailableChain.Gen.Pure.Tests.RetainedWalk.retained_walk_source_coverage`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGeneric/Tests/RetainedWalk.lean:158                          │
│ Frozen          │ no                                                                         │
│ Needs premise   │ yes                                                                        │
│ Reason          │ Fixture must supply its finite scope; W3 owns migration.                   │
│ Premise source  │ none                                                                       │
│ Uses            │ ghost, walk_covers_of_retained_transport                                   │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 231: `AvailableChain.Gen.Pure.Tests.RetainedWalk.retained_walk_source_at_parent`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGeneric/Tests/RetainedWalk.lean:168                          │
│ Frozen          │ no                                                                         │
│ Needs premise   │ yes                                                                        │
│ Reason          │ Fixture must supply its finite scope; W3 owns migration.                   │
│ Premise source  │ none                                                                       │
│ Uses            │ ghost, walk_best_ancestry_of_cover, walk_covers_of_retained_transport      │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 232: `AvailableChain.Gen.Pure.Tests.RetainedWalk.retained_walk_empty_trees`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGeneric/Tests/RetainedWalk.lean:178                          │
│ Frozen          │ no                                                                         │
│ Needs premise   │ yes                                                                        │
│ Reason          │ Fixture must supply its finite scope; W3 owns migration.                   │
│ Premise source  │ none                                                                       │
│ Uses            │ ghost, walk_covers_of_retained_transport                                   │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 233: `AvailableChain.Gen.Pure.Tests.RetainedWalk.retained_walk_best_split_join`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGeneric/Tests/RetainedWalk.lean:186                          │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ BestAncestry, bestAncestry_concat, bestAncestry_restrict,                  │
│                 │ walk_best_ancestry_of_cover                                                │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 234: `AvailableChain.Gen.Pure.Tests.RetainedWalk.retained_walk_losing_target_prefix`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGeneric/Tests/RetainedWalk.lean:195                          │
│ Frozen          │ no                                                                         │
│ Needs premise   │ yes                                                                        │
│ Reason          │ Fixture must supply its finite scope; W3 owns migration.                   │
│ Premise source  │ none                                                                       │
│ Uses            │ BestAncestry, ghost, walk_reanchor_of_best_ancestry                        │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 235: `AvailableChain.Gen.Pure.Tests.RetainedWalk.retained_walk_dominated_adapter`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainGeneric/Tests/RetainedWalk.lean:204                          │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ BestAncestry, bestAncestry_of_dominatedSuffix                              │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 309: `AvailableChain.KitFG.Tests.FrameBridge.<example@24>`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainKitFG/Tests/FrameBridge.lean:24                              │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ lexMax, lexMaxView, lexMax_of_bridge                                       │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 310: `AvailableChain.KitFG.Tests.FrameBridge.<example@47>`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainKitFG/Tests/FrameBridge.lean:47                              │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Structural law, definition, or explicit selected/strict path; ties are     │
│                 │ allowed.                                                                   │
│ Premise source  │ none                                                                       │
│ Uses            │ lexMax, lexMaxView                                                         │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 311: `#print axioms lexMaxView_def`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainKitFG/Tests/FrameBridge.lean:71                              │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Audit/reference only; no proof call.                                       │
│ Premise source  │ none                                                                       │
│ Uses            │ lexMaxView_def                                                             │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 312: `#print axioms lexMax_of_bridge`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainKitFG/Tests/FrameBridge.lean:77                              │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Audit/reference only; no proof call.                                       │
│ Premise source  │ none                                                                       │
│ Uses            │ lexMax_of_bridge                                                           │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 339: `#print axioms AvailableChain.GridCO.ghost_prefix_of_score_transport`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainSAPC/Tests/Axioms.lean:718                                   │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Audit/reference only; no proof call.                                       │
│ Premise source  │ none                                                                       │
│ Uses            │ ghost_prefix_of_score_transport                                            │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 340: `#print axioms AvailableChain.GridCO.ghost_adopts_of_eligible_proposal_transport`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainSAPC/Tests/Axioms.lean:764                                   │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Audit/reference only; no proof call.                                       │
│ Premise source  │ none                                                                       │
│ Uses            │ ghost_adopts_of_eligible_proposal_transport                                │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```

Entry 341: `#print axioms AvailableChain.GridCO.ghost_adopts_of_rooted_proposal_transport`

```text
┌─────────────────┬────────────────────────────────────────────────────────────────────────────┐
│ Field           │ Value                                                                      │
├─────────────────┼────────────────────────────────────────────────────────────────────────────┤
│ File:line       │ AvailableChainSAPC/Tests/Axioms.lean:983                                   │
│ Frozen          │ no                                                                         │
│ Needs premise   │ no                                                                         │
│ Reason          │ Audit/reference only; no proof call.                                       │
│ Premise source  │ none                                                                       │
│ Uses            │ ghost_adopts_of_rooted_proposal_transport                                  │
└─────────────────┴────────────────────────────────────────────────────────────────────────────┘
```


## W2 caller-chain supplement

The direct census above was saved before source edits. This supplement follows all code references
from the three changed walk helpers to their W2 callers. These W2 files are unchanged from HEAD.
It lists 118 declarations, including the direct callers already in the table above. Source lines
still refer to the initial W2 snapshot. Every entry is non-frozen in the three API manifests.
No W2 declaration was edited. “Run boundary” means that prefix/clock CStoreInv can discharge the
local premise; it is not a claim that these currently failing W2 files compile.
Local helpers must pass the exact tree premise, or use a structural selected-path proof where
coverage already supplies uniqueness. They must not add a stronger run or FGSAClaims premise.

AvailableChain.FGSA.Run.exactHead_of_pivot_ancestry

```text
┌───────────────────┬──────────────────────────────────────────────────────────────────────────┐
│ File:line         │ AvailableChainFGSAProofs/Proofs/Shared/KeepExact.lean:129                │
│ Frozen            │ no                                                                       │
│ Needs premise     │ yes, if retaining the current call chain                                 │
│ Premise source    │ none in current binders                                                  │
│ Reason            │ Local helper: use the exact walked-tree hypothesis; preserve existing    │
│                   │ conclusion.                                                              │
│ Calls             │ fgsa_headInTree_reanchor_of_pivot                                        │
└───────────────────┴──────────────────────────────────────────────────────────────────────────┘
```

AvailableChain.FGSA.Run.consumer_h6_fields

```text
┌───────────────────┬──────────────────────────────────────────────────────────────────────────┐
│ File:line         │ AvailableChainFGSAProofs/Proofs/Shared/RetainedConsumers.lean:250        │
│ Frozen            │ no                                                                       │
│ Needs premise     │ yes, if retaining the current call chain                                 │
│ Premise source    │ CStoreInv                                                                │
│ Reason            │ Local helper: use the exact walked-tree hypothesis; preserve existing    │
│                   │ conclusion.                                                              │
│ Calls             │ walk_reanchor_of_best_ancestry                                           │
└───────────────────┴──────────────────────────────────────────────────────────────────────────┘
```

AvailableChain.FGSA.Run.fgsa_retainedReads_H6

```text
┌───────────────────┬──────────────────────────────────────────────────────────────────────────┐
│ File:line         │ AvailableChainFGSAProofs/Proofs/Shared/RetainedConsumers.lean:333        │
│ Frozen            │ no                                                                       │
│ Needs premise     │ no new run/top-level premise                                             │
│ Premise source    │ CStoreInv at the run boundary                                            │
│ Reason            │ Discharge for each prefix/clock state before entering the local helper   │
│                   │ chain.                                                                   │
│ Calls             │ walk_reanchor_of_best_ancestry                                           │
└───────────────────┴──────────────────────────────────────────────────────────────────────────┘
```

AvailableChain.FGSA.Run.consumer_cone_starts

```text
┌───────────────────┬──────────────────────────────────────────────────────────────────────────┐
│ File:line         │ AvailableChainFGSAProofs/Proofs/Shared/RetainedConsumers.lean:444        │
│ Frozen            │ no                                                                       │
│ Needs premise     │ yes, if retaining the current call chain                                 │
│ Premise source    │ CStoreInv                                                                │
│ Reason            │ Local helper: use the exact walked-tree hypothesis; preserve existing    │
│                   │ conclusion.                                                              │
│ Calls             │ walk_reanchor_of_best_ancestry                                           │
└───────────────────┴──────────────────────────────────────────────────────────────────────────┘
```

AvailableChain.FGSA.Run.fgsa_headVote_covers_parent_of_retained_geometry

```text
┌───────────────────┬──────────────────────────────────────────────────────────────────────────┐
│ File:line         │ AvailableChainFGSAProofs/Proofs/Shared/RetainedEndpoint.lean:103         │
│ Frozen            │ no                                                                       │
│ Needs premise     │ yes, if retaining the current call chain                                 │
│ Premise source    │ none in current binders                                                  │
│ Reason            │ Local helper: use the exact walked-tree hypothesis; preserve existing    │
│                   │ conclusion.                                                              │
│ Calls             │ walk_covers_of_retained_transport                                        │
└───────────────────┴──────────────────────────────────────────────────────────────────────────┘
```

AvailableChain.FGSA.fgsa_ordinary_parent_of_live_prefix

```text
┌───────────────────┬──────────────────────────────────────────────────────────────────────────┐
│ File:line         │ AvailableChainFGSAProofs/Proofs/Shared/RetainedWalkStore.lean:26         │
│ Frozen            │ no                                                                       │
│ Needs premise     │ yes, if retaining the current call chain                                 │
│ Premise source    │ none in current binders                                                  │
│ Reason            │ Local helper: use the exact walked-tree hypothesis; preserve existing    │
│                   │ conclusion.                                                              │
│ Calls             │ walk_reanchor_of_best_ancestry                                           │
└───────────────────┴──────────────────────────────────────────────────────────────────────────┘
```

AvailableChain.FGSA.Run.frontier_seed_qSucc_head

```text
┌───────────────────┬──────────────────────────────────────────────────────────────────────────┐
│ File:line         │ AvailableChainFGSAProofs/Proofs/Healing/FrontierSeed.lean:187            │
│ Frozen            │ no                                                                       │
│ Needs premise     │ no new run/top-level premise                                             │
│ Premise source    │ CStoreInv at the run boundary                                            │
│ Reason            │ Discharge for each prefix/clock state before entering the local helper   │
│                   │ chain.                                                                   │
│ Calls             │ fgsa_retainedReads_H6                                                    │
└───────────────────┴──────────────────────────────────────────────────────────────────────────┘
```

AvailableChain.FGSA.Run.repair_head_exact

```text
┌───────────────────┬──────────────────────────────────────────────────────────────────────────┐
│ File:line         │ AvailableChainFGSAProofs/Proofs/Healing/RepairH6.lean:539                │
│ Frozen            │ no                                                                       │
│ Needs premise     │ no new run/top-level premise                                             │
│ Premise source    │ CStoreInv at the run boundary                                            │
│ Reason            │ Discharge for each prefix/clock state before entering the local helper   │
│                   │ chain.                                                                   │
│ Calls             │ fgsa_retainedReads_H6                                                    │
└───────────────────┴──────────────────────────────────────────────────────────────────────────┘
```

AvailableChain.FGSA.Run.fgsa_headVote_exact_of_covered_parent

```text
┌───────────────────┬──────────────────────────────────────────────────────────────────────────┐
│ File:line         │ AvailableChainFGSAProofs/Proofs/Shared/ExactHead.lean:60                 │
│ Frozen            │ no                                                                       │
│ Needs premise     │ yes, if retaining the current call chain                                 │
│ Premise source    │ none in current binders                                                  │
│ Reason            │ Local helper: use the exact walked-tree hypothesis; preserve existing    │
│                   │ conclusion.                                                              │
│ Calls             │ exactHead_of_pivot_ancestry                                              │
└───────────────────┴──────────────────────────────────────────────────────────────────────────┘
```

AvailableChain.FGSA.Run.exactHead_of_pivot

```text
┌───────────────────┬──────────────────────────────────────────────────────────────────────────┐
│ File:line         │ AvailableChainFGSAProofs/Proofs/Shared/KeepExact.lean:195                │
│ Frozen            │ no                                                                       │
│ Needs premise     │ yes, if retaining the current call chain                                 │
│ Premise source    │ none in current binders                                                  │
│ Reason            │ Local helper: use the exact walked-tree hypothesis; preserve existing    │
│                   │ conclusion.                                                              │
│ Calls             │ exactHead_of_pivot_ancestry                                              │
└───────────────────┴──────────────────────────────────────────────────────────────────────────┘
```

AvailableChain.FGSA.Run.consumer_cone_fields

```text
┌───────────────────┬──────────────────────────────────────────────────────────────────────────┐
│ File:line         │ AvailableChainFGSAProofs/Proofs/Shared/RetainedConsumers.lean:552        │
│ Frozen            │ no                                                                       │
│ Needs premise     │ yes, if retaining the current call chain                                 │
│ Premise source    │ CStoreInv                                                                │
│ Reason            │ Local helper: use the exact walked-tree hypothesis; preserve existing    │
│                   │ conclusion.                                                              │
│ Calls             │ consumer_cone_starts                                                     │
└───────────────────┴──────────────────────────────────────────────────────────────────────────┘
```

AvailableChain.FGSA.Run.fgsa_retainedReads_H17

```text
┌───────────────────┬──────────────────────────────────────────────────────────────────────────┐
│ File:line         │ AvailableChainFGSAProofs/Proofs/Shared/RetainedConsumers.lean:625        │
│ Frozen            │ no                                                                       │
│ Needs premise     │ no new run/top-level premise                                             │
│ Premise source    │ CStoreInv at the run boundary                                            │
│ Reason            │ Discharge for each prefix/clock state before entering the local helper   │
│                   │ chain.                                                                   │
│ Calls             │ consumer_cone_starts                                                     │
└───────────────────┴──────────────────────────────────────────────────────────────────────────┘
```

AvailableChain.FGSA.Run.fgsa_retainedReads_H6S

```text
┌───────────────────┬──────────────────────────────────────────────────────────────────────────┐
│ File:line         │ AvailableChainFGSAProofs/Proofs/Shared/RetainedConsumersH6S.lean:18      │
│ Frozen            │ no                                                                       │
│ Needs premise     │ no new run/top-level premise                                             │
│ Premise source    │ CStoreInv at the run boundary                                            │
│ Reason            │ Discharge for each prefix/clock state before entering the local helper   │
│                   │ chain.                                                                   │
│ Calls             │ fgsa_retainedReads_H6                                                    │
└───────────────────┴──────────────────────────────────────────────────────────────────────────┘
```

AvailableChain.FGSA.Run.exactService_head_of_retained_proposal

```text
┌───────────────────┬──────────────────────────────────────────────────────────────────────────┐
│ File:line         │ AvailableChainFGSAProofs/Proofs/Shared/RetainedEndpoint.lean:257         │
│ Frozen            │ no                                                                       │
│ Needs premise     │ no new run/top-level premise                                             │
│ Premise source    │ CStoreInv at the run boundary                                            │
│ Reason            │ Discharge for each prefix/clock state before entering the local helper   │
│                   │ chain.                                                                   │
│ Calls             │ fgsa_headVote_covers_parent_of_retained_geometry                         │
└───────────────────┴──────────────────────────────────────────────────────────────────────────┘
```

AvailableChain.FGSA.fgsa_ordinary_parent_of_live_cover

```text
┌───────────────────┬──────────────────────────────────────────────────────────────────────────┐
│ File:line         │ AvailableChainFGSAProofs/Proofs/Shared/RetainedWalkStore.lean:59         │
│ Frozen            │ no                                                                       │
│ Needs premise     │ yes, if retaining the current call chain                                 │
│ Premise source    │ none in current binders                                                  │
│ Reason            │ Local helper: use the exact walked-tree hypothesis; preserve existing    │
│                   │ conclusion.                                                              │
│ Calls             │ fgsa_ordinary_parent_of_live_prefix                                      │
└───────────────────┴──────────────────────────────────────────────────────────────────────────┘
```

AvailableChain.FGSA.Run.frontier_seed_qSucc_exactService

```text
┌───────────────────┬──────────────────────────────────────────────────────────────────────────┐
│ File:line         │ AvailableChainFGSAProofs/Proofs/Healing/FrontierService.lean:74          │
│ Frozen            │ no                                                                       │
│ Needs premise     │ no new run/top-level premise                                             │
│ Premise source    │ CStoreInv at the run boundary                                            │
│ Reason            │ Discharge for each prefix/clock state before entering the local helper   │
│                   │ chain.                                                                   │
│ Calls             │ frontier_seed_qSucc_head                                                 │
└───────────────────┴──────────────────────────────────────────────────────────────────────────┘
```

AvailableChain.FGSA.Run.frontier_later_head

```text
┌───────────────────┬──────────────────────────────────────────────────────────────────────────┐
│ File:line         │ AvailableChainFGSAProofs/Proofs/Healing/FrontierService.lean:112         │
│ Frozen            │ no                                                                       │
│ Needs premise     │ no new run/top-level premise                                             │
│ Premise source    │ CStoreInv at the run boundary                                            │
│ Reason            │ Discharge for each prefix/clock state before entering the local helper   │
│                   │ chain.                                                                   │
│ Calls             │ exactService_head_of_retained_proposal                                   │
└───────────────────┴──────────────────────────────────────────────────────────────────────────┘
```

AvailableChain.FGSA.Run.healing_postReset_exactHead_at

```text
┌───────────────────┬──────────────────────────────────────────────────────────────────────────┐
│ File:line         │ AvailableChainFGSAProofs/Proofs/Healing/PostResetOpening.lean:91         │
│ Frozen            │ no                                                                       │
│ Needs premise     │ no new run/top-level premise                                             │
│ Premise source    │ CStoreInv at the run boundary                                            │
│ Reason            │ Discharge for each prefix/clock state before entering the local helper   │
│                   │ chain.                                                                   │
│ Calls             │ exactService_head_of_retained_proposal                                   │
└───────────────────┴──────────────────────────────────────────────────────────────────────────┘
```

AvailableChain.FGSA.Run.healing_postReset_retainedReads_at

```text
┌───────────────────┬──────────────────────────────────────────────────────────────────────────┐
│ File:line         │ AvailableChainFGSAProofs/Proofs/Healing/PostResetRead.lean:147           │
│ Frozen            │ no                                                                       │
│ Needs premise     │ no new run/top-level premise                                             │
│ Premise source    │ CStoreInv at the run boundary                                            │
│ Reason            │ Discharge for each prefix/clock state before entering the local helper   │
│                   │ chain.                                                                   │
│ Calls             │ fgsa_retainedReads_H17                                                   │
└───────────────────┴──────────────────────────────────────────────────────────────────────────┘
```

AvailableChain.FGSA.Run.repair_exact_service

```text
┌───────────────────┬──────────────────────────────────────────────────────────────────────────┐
│ File:line         │ AvailableChainFGSAProofs/Proofs/Healing/Repair.lean:67                   │
│ Frozen            │ no                                                                       │
│ Needs premise     │ no new run/top-level premise                                             │
│ Premise source    │ CStoreInv at the run boundary                                            │
│ Reason            │ Discharge for each prefix/clock state before entering the local helper   │
│                   │ chain.                                                                   │
│ Calls             │ repair_head_exact                                                        │
└───────────────────┴──────────────────────────────────────────────────────────────────────────┘
```

AvailableChain.FGSA.Run.repair_head_two

```text
┌───────────────────┬──────────────────────────────────────────────────────────────────────────┐
│ File:line         │ AvailableChainFGSAProofs/Proofs/Healing/RepairH6.lean:710                │
│ Frozen            │ no                                                                       │
│ Needs premise     │ no new run/top-level premise                                             │
│ Premise source    │ CStoreInv at the run boundary                                            │
│ Reason            │ Discharge for each prefix/clock state before entering the local helper   │
│                   │ chain.                                                                   │
│ Calls             │ repair_head_exact                                                        │
└───────────────────┴──────────────────────────────────────────────────────────────────────────┘
```

AvailableChain.FGSA.Run.repair_head_one

```text
┌───────────────────┬──────────────────────────────────────────────────────────────────────────┐
│ File:line         │ AvailableChainFGSAProofs/Proofs/Healing/RepairH6S.lean:118               │
│ Frozen            │ no                                                                       │
│ Needs premise     │ no new run/top-level premise                                             │
│ Premise source    │ CStoreInv at the run boundary                                            │
│ Reason            │ Discharge for each prefix/clock state before entering the local helper   │
│                   │ chain.                                                                   │
│ Calls             │ repair_head_exact                                                        │
└───────────────────┴──────────────────────────────────────────────────────────────────────────┘
```

AvailableChain.FGSA.Run.inclusion_retained_reads

```text
┌───────────────────┬──────────────────────────────────────────────────────────────────────────┐
│ File:line         │ AvailableChainFGSAProofs/Proofs/Outage/ExactProposalRetained.lean:312    │
│ Frozen            │ no                                                                       │
│ Needs premise     │ no new run/top-level premise                                             │
│ Premise source    │ CStoreInv at the run boundary                                            │
│ Reason            │ Discharge for each prefix/clock state before entering the local helper   │
│                   │ chain.                                                                   │
│ Calls             │ fgsa_retainedReads_H17                                                   │
└───────────────────┴──────────────────────────────────────────────────────────────────────────┘
```

AvailableChain.FGSA.Run.exactHead_of_proposal_on_run

```text
┌───────────────────┬──────────────────────────────────────────────────────────────────────────┐
│ File:line         │ AvailableChainFGSAProofs/Proofs/Shared/ExactHead.lean:89                 │
│ Frozen            │ no                                                                       │
│ Needs premise     │ no new run/top-level premise                                             │
│ Premise source    │ CStoreInv at the run boundary                                            │
│ Reason            │ Discharge for each prefix/clock state before entering the local helper   │
│                   │ chain.                                                                   │
│ Calls             │ fgsa_headVote_exact_of_covered_parent                                    │
└───────────────────┴──────────────────────────────────────────────────────────────────────────┘
```

AvailableChain.FGSA.Run.exactService_head_of_retained_proposal_clean

```text
┌───────────────────┬──────────────────────────────────────────────────────────────────────────┐
│ File:line         │ AvailableChainFGSAProofs/Proofs/Shared/Regimes.lean:556                  │
│ Frozen            │ no                                                                       │
│ Needs premise     │ no new run/top-level premise                                             │
│ Premise source    │ CStoreInv at the run boundary                                            │
│ Reason            │ Discharge for each prefix/clock state before entering the local helper   │
│                   │ chain.                                                                   │
│ Calls             │ exactService_head_of_retained_proposal                                   │
└───────────────────┴──────────────────────────────────────────────────────────────────────────┘
```

AvailableChain.FGSA.Run.exactService_head_of_retained_proposal_recovery

```text
┌───────────────────┬──────────────────────────────────────────────────────────────────────────┐
│ File:line         │ AvailableChainFGSAProofs/Proofs/Shared/Regimes.lean:600                  │
│ Frozen            │ no                                                                       │
│ Needs premise     │ no new run/top-level premise                                             │
│ Premise source    │ CStoreInv at the run boundary                                            │
│ Reason            │ Discharge for each prefix/clock state before entering the local helper   │
│                   │ chain.                                                                   │
│ Calls             │ exactService_head_of_retained_proposal                                   │
└───────────────────┴──────────────────────────────────────────────────────────────────────────┘
```

AvailableChain.FGSA.Run.fgsa_retainedReads_L2

```text
┌───────────────────┬──────────────────────────────────────────────────────────────────────────┐
│ File:line         │ AvailableChainFGSAProofs/Proofs/Shared/RetainedConsumersL2.lean:53       │
│ Frozen            │ no                                                                       │
│ Needs premise     │ no new run/top-level premise                                             │
│ Premise source    │ CStoreInv at the run boundary                                            │
│ Reason            │ Discharge for each prefix/clock state before entering the local helper   │
│                   │ chain.                                                                   │
│ Calls             │ fgsa_retainedReads_H17                                                   │
└───────────────────┴──────────────────────────────────────────────────────────────────────────┘
```

AvailableChain.FGSA.Run.fgsa_retainedReads_L4R

```text
┌───────────────────┬──────────────────────────────────────────────────────────────────────────┐
│ File:line         │ AvailableChainFGSAProofs/Proofs/Shared/RetainedConsumersQ.lean:16        │
│ Frozen            │ no                                                                       │
│ Needs premise     │ no new run/top-level premise                                             │
│ Premise source    │ CStoreInv at the run boundary                                            │
│ Reason            │ Discharge for each prefix/clock state before entering the local helper   │
│                   │ chain.                                                                   │
│ Calls             │ fgsa_retainedReads_H17                                                   │
└───────────────────┴──────────────────────────────────────────────────────────────────────────┘
```

AvailableChain.FGSA.Run.fgsa_retainedReads_HG1

```text
┌───────────────────┬──────────────────────────────────────────────────────────────────────────┐
│ File:line         │ AvailableChainFGSAProofs/Proofs/Shared/RetainedConsumersQ.lean:56        │
│ Frozen            │ no                                                                       │
│ Needs premise     │ no new run/top-level premise                                             │
│ Premise source    │ CStoreInv at the run boundary                                            │
│ Reason            │ Discharge for each prefix/clock state before entering the local helper   │
│                   │ chain.                                                                   │
│ Calls             │ fgsa_retainedReads_H17                                                   │
└───────────────────┴──────────────────────────────────────────────────────────────────────────┘
```

AvailableChain.FGSA.Run.frontier_later_exactService

```text
┌───────────────────┬──────────────────────────────────────────────────────────────────────────┐
│ File:line         │ AvailableChainFGSAProofs/Proofs/Healing/FrontierService.lean:186         │
│ Frozen            │ no                                                                       │
│ Needs premise     │ no new run/top-level premise                                             │
│ Premise source    │ CStoreInv at the run boundary                                            │
│ Reason            │ Discharge for each prefix/clock state before entering the local helper   │
│                   │ chain.                                                                   │
│ Calls             │ frontier_later_head                                                      │
└───────────────────┴──────────────────────────────────────────────────────────────────────────┘
```

AvailableChain.FGSA.Run.frontier_service_core

```text
┌───────────────────┬──────────────────────────────────────────────────────────────────────────┐
│ File:line         │ AvailableChainFGSAProofs/Proofs/Healing/FrontierService.lean:231         │
│ Frozen            │ no                                                                       │
│ Needs premise     │ no new run/top-level premise                                             │
│ Premise source    │ CStoreInv at the run boundary                                            │
│ Reason            │ Discharge for each prefix/clock state before entering the local helper   │
│                   │ chain.                                                                   │
│ Calls             │ frontier_seed_qSucc_exactService                                         │
└───────────────────┴──────────────────────────────────────────────────────────────────────────┘
```

AvailableChain.FGSA.Run.healing_postReset_headGeometry_at

```text
┌───────────────────┬──────────────────────────────────────────────────────────────────────────┐
│ File:line         │ AvailableChainFGSAProofs/Proofs/Healing/PostResetOpening.lean:53         │
│ Frozen            │ no                                                                       │
│ Needs premise     │ no new run/top-level premise                                             │
│ Premise source    │ CStoreInv at the run boundary                                            │
│ Reason            │ Discharge for each prefix/clock state before entering the local helper   │
│                   │ chain.                                                                   │
│ Calls             │ healing_postReset_retainedReads_at                                       │
└───────────────────┴──────────────────────────────────────────────────────────────────────────┘
```

AvailableChain.FGSA.Run.healing_postReset_gate_covered_prefix_at

```text
┌───────────────────┬──────────────────────────────────────────────────────────────────────────┐
│ File:line         │ AvailableChainFGSAProofs/Proofs/Healing/PostResetOpening.lean:252        │
│ Frozen            │ no                                                                       │
│ Needs premise     │ no new run/top-level premise                                             │
│ Premise source    │ CStoreInv at the run boundary                                            │
│ Reason            │ Discharge for each prefix/clock state before entering the local helper   │
│                   │ chain.                                                                   │
│ Calls             │ healing_postReset_exactHead_at                                           │
└───────────────────┴──────────────────────────────────────────────────────────────────────────┘
```

AvailableChain.FGSA.Run.healing_postReset_gate_raw_at

```text
┌───────────────────┬──────────────────────────────────────────────────────────────────────────┐
│ File:line         │ AvailableChainFGSAProofs/Proofs/Healing/PostResetOpening.lean:402        │
│ Frozen            │ no                                                                       │
│ Needs premise     │ no new run/top-level premise                                             │
│ Premise source    │ CStoreInv at the run boundary                                            │
│ Reason            │ Discharge for each prefix/clock state before entering the local helper   │
│                   │ chain.                                                                   │
│ Calls             │ healing_postReset_exactHead_at                                           │
└───────────────────┴──────────────────────────────────────────────────────────────────────────┘
```

AvailableChain.FGSA.Run.healing_postReset_exactHead

```text
┌───────────────────┬──────────────────────────────────────────────────────────────────────────┐
│ File:line         │ AvailableChainFGSAProofs/Proofs/Healing/PostResetOpening.lean:657        │
│ Frozen            │ no                                                                       │
│ Needs premise     │ no new run/top-level premise                                             │
│ Premise source    │ CStoreInv at the run boundary                                            │
│ Reason            │ Discharge for each prefix/clock state before entering the local helper   │
│                   │ chain.                                                                   │
│ Calls             │ healing_postReset_exactHead_at                                           │
└───────────────────┴──────────────────────────────────────────────────────────────────────────┘
```

AvailableChain.FGSA.Run.healing_postReset_retainedReads

```text
┌───────────────────┬──────────────────────────────────────────────────────────────────────────┐
│ File:line         │ AvailableChainFGSAProofs/Proofs/Healing/PostResetRead.lean:169           │
│ Frozen            │ no                                                                       │
│ Needs premise     │ no new run/top-level premise                                             │
│ Premise source    │ CStoreInv at the run boundary                                            │
│ Reason            │ Discharge for each prefix/clock state before entering the local helper   │
│                   │ chain.                                                                   │
│ Calls             │ healing_postReset_retainedReads_at                                       │
└───────────────────┴──────────────────────────────────────────────────────────────────────────┘
```

AvailableChain.FGSA.Run.healing_postReset_opening_target_floor_at

```text
┌───────────────────┬──────────────────────────────────────────────────────────────────────────┐
│ File:line         │ AvailableChainFGSAProofs/Proofs/Healing/PostResetService.lean:57         │
│ Frozen            │ no                                                                       │
│ Needs premise     │ no new run/top-level premise                                             │
│ Premise source    │ CStoreInv at the run boundary                                            │
│ Reason            │ Discharge for each prefix/clock state before entering the local helper   │
│                   │ chain.                                                                   │
│ Calls             │ healing_postReset_exactHead_at                                           │
└───────────────────┴──────────────────────────────────────────────────────────────────────────┘
```

AvailableChain.FGSA.Run.healing_postReset_gate_geometry_at

```text
┌───────────────────┬──────────────────────────────────────────────────────────────────────────┐
│ File:line         │ AvailableChainFGSAProofs/Proofs/Healing/PostResetService.lean:144        │
│ Frozen            │ no                                                                       │
│ Needs premise     │ no new run/top-level premise                                             │
│ Premise source    │ CStoreInv at the run boundary                                            │
│ Reason            │ Discharge for each prefix/clock state before entering the local helper   │
│                   │ chain.                                                                   │
│ Calls             │ healing_postReset_exactHead_at                                           │
└───────────────────┴──────────────────────────────────────────────────────────────────────────┘
```

AvailableChain.FGSA.Run.healing_postReset_service_step_at

```text
┌───────────────────┬──────────────────────────────────────────────────────────────────────────┐
│ File:line         │ AvailableChainFGSAProofs/Proofs/Healing/PostResetService.lean:208        │
│ Frozen            │ no                                                                       │
│ Needs premise     │ no new run/top-level premise                                             │
│ Premise source    │ CStoreInv at the run boundary                                            │
│ Reason            │ Discharge for each prefix/clock state before entering the local helper   │
│                   │ chain.                                                                   │
│ Calls             │ healing_postReset_exactHead_at                                           │
└───────────────────┴──────────────────────────────────────────────────────────────────────────┘
```

AvailableChain.FGSA.Run.repair_after_of_cover

```text
┌───────────────────┬──────────────────────────────────────────────────────────────────────────┐
│ File:line         │ AvailableChainFGSAProofs/Proofs/Healing/Repair.lean:114                  │
│ Frozen            │ no                                                                       │
│ Needs premise     │ no new run/top-level premise                                             │
│ Premise source    │ CStoreInv at the run boundary                                            │
│ Reason            │ Discharge for each prefix/clock state before entering the local helper   │
│                   │ chain.                                                                   │
│ Calls             │ repair_exact_service                                                     │
└───────────────────┴──────────────────────────────────────────────────────────────────────────┘
```

AvailableChain.FGSA.Run.inclusion_exact_compat

```text
┌───────────────────┬──────────────────────────────────────────────────────────────────────────┐
│ File:line         │ AvailableChainFGSAProofs/Proofs/Outage/ExactProposalRetained.lean:680    │
│ Frozen            │ no                                                                       │
│ Needs premise     │ no new run/top-level premise                                             │
│ Premise source    │ CStoreInv at the run boundary                                            │
│ Reason            │ Discharge for each prefix/clock state before entering the local helper   │
│                   │ chain.                                                                   │
│ Calls             │ inclusion_retained_reads                                                 │
└───────────────────┴──────────────────────────────────────────────────────────────────────────┘
```

AvailableChain.FGSA.Run.inclusion_exact_head

```text
┌───────────────────┬──────────────────────────────────────────────────────────────────────────┐
│ File:line         │ AvailableChainFGSAProofs/Proofs/Outage/ExactProposalRetained.lean:771    │
│ Frozen            │ no                                                                       │
│ Needs premise     │ no new run/top-level premise                                             │
│ Premise source    │ CStoreInv at the run boundary                                            │
│ Reason            │ Discharge for each prefix/clock state before entering the local helper   │
│                   │ chain.                                                                   │
│ Calls             │ exactService_head_of_retained_proposal_clean, inclusion_retained_reads   │
└───────────────────┴──────────────────────────────────────────────────────────────────────────┘
```

AvailableChain.FGSA.Run.exactService_head_of_proposal

```text
┌───────────────────┬──────────────────────────────────────────────────────────────────────────┐
│ File:line         │ AvailableChainFGSAProofs/Proofs/Shared/ExactHead.lean:159                │
│ Frozen            │ no                                                                       │
│ Needs premise     │ no new run/top-level premise                                             │
│ Premise source    │ CStoreInv at the run boundary                                            │
│ Reason            │ Discharge for each prefix/clock state before entering the local helper   │
│                   │ chain.                                                                   │
│ Calls             │ exactHead_of_proposal_on_run                                             │
└───────────────────┴──────────────────────────────────────────────────────────────────────────┘
```

AvailableChain.FGSA.Run.frontier_service

```text
┌───────────────────┬──────────────────────────────────────────────────────────────────────────┐
│ File:line         │ AvailableChainFGSAProofs/Proofs/Healing/FrontierService.lean:307         │
│ Frozen            │ no                                                                       │
│ Needs premise     │ no new run/top-level premise                                             │
│ Premise source    │ CStoreInv at the run boundary                                            │
│ Reason            │ Discharge for each prefix/clock state before entering the local helper   │
│                   │ chain.                                                                   │
│ Calls             │ frontier_service_core                                                    │
└───────────────────┴──────────────────────────────────────────────────────────────────────────┘
```

AvailableChain.FGSA.Run.healing_postReset_serviceStep₂

```text
┌───────────────────┬──────────────────────────────────────────────────────────────────────────┐
│ File:line         │ AvailableChainFGSAProofs/Proofs/Healing/PostResetJointStep2.lean:50      │
│ Frozen            │ no                                                                       │
│ Needs premise     │ no new run/top-level premise                                             │
│ Premise source    │ CStoreInv at the run boundary                                            │
│ Reason            │ Discharge for each prefix/clock state before entering the local helper   │
│                   │ chain.                                                                   │
│ Calls             │ healing_postReset_service_step_at                                        │
└───────────────────┴──────────────────────────────────────────────────────────────────────────┘
```

AvailableChain.FGSA.Run.healing_postReset_headCarrier_at

```text
┌───────────────────┬──────────────────────────────────────────────────────────────────────────┐
│ File:line         │ AvailableChainFGSAProofs/Proofs/Healing/PostResetOpening.lean:111        │
│ Frozen            │ no                                                                       │
│ Needs premise     │ no new run/top-level premise                                             │
│ Premise source    │ CStoreInv at the run boundary                                            │
│ Reason            │ Discharge for each prefix/clock state before entering the local helper   │
│                   │ chain.                                                                   │
│ Calls             │ healing_postReset_headGeometry_at                                        │
└───────────────────┴──────────────────────────────────────────────────────────────────────────┘
```

AvailableChain.FGSA.Run.healing_postReset_opening_source_prefix_at

```text
┌───────────────────┬──────────────────────────────────────────────────────────────────────────┐
│ File:line         │ AvailableChainFGSAProofs/Proofs/Healing/PostResetOpening.lean:473        │
│ Frozen            │ no                                                                       │
│ Needs premise     │ no new run/top-level premise                                             │
│ Premise source    │ CStoreInv at the run boundary                                            │
│ Reason            │ Discharge for each prefix/clock state before entering the local helper   │
│                   │ chain.                                                                   │
│ Calls             │ healing_postReset_gate_raw_at                                            │
└───────────────────┴──────────────────────────────────────────────────────────────────────────┘
```

AvailableChain.FGSA.Run.healing_postReset_headGeometry

```text
┌───────────────────┬──────────────────────────────────────────────────────────────────────────┐
│ File:line         │ AvailableChainFGSAProofs/Proofs/Healing/PostResetOpening.lean:638        │
│ Frozen            │ no                                                                       │
│ Needs premise     │ no new run/top-level premise                                             │
│ Premise source    │ CStoreInv at the run boundary                                            │
│ Reason            │ Discharge for each prefix/clock state before entering the local helper   │
│                   │ chain.                                                                   │
│ Calls             │ healing_postReset_headGeometry_at                                        │
└───────────────────┴──────────────────────────────────────────────────────────────────────────┘
```

AvailableChain.FGSA.Run.healing_postReset_gate_covered_prefix

```text
┌───────────────────┬──────────────────────────────────────────────────────────────────────────┐
│ File:line         │ AvailableChainFGSAProofs/Proofs/Healing/PostResetOpening.lean:714        │
│ Frozen            │ no                                                                       │
│ Needs premise     │ no new run/top-level premise                                             │
│ Premise source    │ CStoreInv at the run boundary                                            │
│ Reason            │ Discharge for each prefix/clock state before entering the local helper   │
│                   │ chain.                                                                   │
│ Calls             │ healing_postReset_gate_covered_prefix_at                                 │
└───────────────────┴──────────────────────────────────────────────────────────────────────────┘
```

AvailableChain.FGSA.Run.healing_postReset_gate_raw

```text
┌───────────────────┬──────────────────────────────────────────────────────────────────────────┐
│ File:line         │ AvailableChainFGSAProofs/Proofs/Healing/PostResetOpening.lean:752        │
│ Frozen            │ no                                                                       │
│ Needs premise     │ no new run/top-level premise                                             │
│ Premise source    │ CStoreInv at the run boundary                                            │
│ Reason            │ Discharge for each prefix/clock state before entering the local helper   │
│                   │ chain.                                                                   │
│ Calls             │ healing_postReset_gate_raw_at                                            │
└───────────────────┴──────────────────────────────────────────────────────────────────────────┘
```

AvailableChain.FGSA.Run.healing_postReset_opening_target_floor

```text
┌───────────────────┬──────────────────────────────────────────────────────────────────────────┐
│ File:line         │ AvailableChainFGSAProofs/Proofs/Healing/PostResetService.lean:305        │
│ Frozen            │ no                                                                       │
│ Needs premise     │ no new run/top-level premise                                             │
│ Premise source    │ CStoreInv at the run boundary                                            │
│ Reason            │ Discharge for each prefix/clock state before entering the local helper   │
│                   │ chain.                                                                   │
│ Calls             │ healing_postReset_opening_target_floor_at                                │
└───────────────────┴──────────────────────────────────────────────────────────────────────────┘
```

AvailableChain.FGSA.Run.healing_postReset_gate_geometry

```text
┌───────────────────┬──────────────────────────────────────────────────────────────────────────┐
│ File:line         │ AvailableChainFGSAProofs/Proofs/Healing/PostResetService.lean:362        │
│ Frozen            │ no                                                                       │
│ Needs premise     │ no new run/top-level premise                                             │
│ Premise source    │ CStoreInv at the run boundary                                            │
│ Reason            │ Discharge for each prefix/clock state before entering the local helper   │
│                   │ chain.                                                                   │
│ Calls             │ healing_postReset_gate_geometry_at                                       │
└───────────────────┴──────────────────────────────────────────────────────────────────────────┘
```

AvailableChain.FGSA.Run.healing_postReset_service_step

```text
┌───────────────────┬──────────────────────────────────────────────────────────────────────────┐
│ File:line         │ AvailableChainFGSAProofs/Proofs/Healing/PostResetService.lean:375        │
│ Frozen            │ no                                                                       │
│ Needs premise     │ no new run/top-level premise                                             │
│ Premise source    │ CStoreInv at the run boundary                                            │
│ Reason            │ Discharge for each prefix/clock state before entering the local helper   │
│                   │ chain.                                                                   │
│ Calls             │ healing_postReset_service_step_at                                        │
└───────────────────┴──────────────────────────────────────────────────────────────────────────┘
```

AvailableChain.FGSA.Run.repair_two_lease

```text
┌───────────────────┬──────────────────────────────────────────────────────────────────────────┐
│ File:line         │ AvailableChainFGSAProofs/Proofs/Healing/Repair.lean:158                  │
│ Frozen            │ no                                                                       │
│ Needs premise     │ no new run/top-level premise                                             │
│ Premise source    │ CStoreInv at the run boundary                                            │
│ Reason            │ Discharge for each prefix/clock state before entering the local helper   │
│                   │ chain.                                                                   │
│ Calls             │ repair_after_of_cover                                                    │
└───────────────────┴──────────────────────────────────────────────────────────────────────────┘
```

AvailableChain.FGSA.Run.repair_synchronous

```text
┌───────────────────┬──────────────────────────────────────────────────────────────────────────┐
│ File:line         │ AvailableChainFGSAProofs/Proofs/Healing/Repair.lean:254                  │
│ Frozen            │ no                                                                       │
│ Needs premise     │ no new run/top-level premise                                             │
│ Premise source    │ CStoreInv at the run boundary                                            │
│ Reason            │ Discharge for each prefix/clock state before entering the local helper   │
│                   │ chain.                                                                   │
│ Calls             │ repair_after_of_cover                                                    │
└───────────────────┴──────────────────────────────────────────────────────────────────────────┘
```

AvailableChain.FGSA.Run.inclusion_exact_receipt

```text
┌───────────────────┬──────────────────────────────────────────────────────────────────────────┐
│ File:line         │ AvailableChainFGSAProofs/Proofs/Outage/ExactProposalRetained.lean:735    │
│ Frozen            │ no                                                                       │
│ Needs premise     │ no new run/top-level premise                                             │
│ Premise source    │ CStoreInv at the run boundary                                            │
│ Reason            │ Discharge for each prefix/clock state before entering the local helper   │
│                   │ chain.                                                                   │
│ Calls             │ inclusion_exact_compat                                                   │
└───────────────────┴──────────────────────────────────────────────────────────────────────────┘
```

AvailableChain.FGSA.Run.outage_exactProposalClaim_of

```text
┌───────────────────┬──────────────────────────────────────────────────────────────────────────┐
│ File:line         │ AvailableChainFGSAProofs/Proofs/Outage/Export.lean:83                    │
│ Frozen            │ no                                                                       │
│ Needs premise     │ no new run/top-level premise                                             │
│ Premise source    │ CStoreInv at the run boundary                                            │
│ Reason            │ Discharge for each prefix/clock state before entering the local helper   │
│                   │ chain.                                                                   │
│ Calls             │ inclusion_exact_head                                                     │
└───────────────────┴──────────────────────────────────────────────────────────────────────────┘
```

AvailableChain.FGSA.Run.inclusion_headAtLabel

```text
┌───────────────────┬──────────────────────────────────────────────────────────────────────────┐
│ File:line         │ AvailableChainFGSAProofs/Proofs/Outage/InclusionGate.lean:21             │
│ Frozen            │ no                                                                       │
│ Needs premise     │ no new run/top-level premise                                             │
│ Premise source    │ CStoreInv at the run boundary                                            │
│ Reason            │ Discharge for each prefix/clock state before entering the local helper   │
│                   │ chain.                                                                   │
│ Calls             │ inclusion_exact_head                                                     │
└───────────────────┴──────────────────────────────────────────────────────────────────────────┘
```

AvailableChain.FGSA.Run.exactService_head_of_proposal_clean

```text
┌───────────────────┬──────────────────────────────────────────────────────────────────────────┐
│ File:line         │ AvailableChainFGSAProofs/Proofs/Shared/Regimes.lean:486                  │
│ Frozen            │ no                                                                       │
│ Needs premise     │ no new run/top-level premise                                             │
│ Premise source    │ CStoreInv at the run boundary                                            │
│ Reason            │ Discharge for each prefix/clock state before entering the local helper   │
│                   │ chain.                                                                   │
│ Calls             │ exactService_head_of_proposal                                            │
└───────────────────┴──────────────────────────────────────────────────────────────────────────┘
```

AvailableChain.FGSA.Run.exactService_head_of_proposal_recovery

```text
┌───────────────────┬──────────────────────────────────────────────────────────────────────────┐
│ File:line         │ AvailableChainFGSAProofs/Proofs/Shared/Regimes.lean:522                  │
│ Frozen            │ no                                                                       │
│ Needs premise     │ no new run/top-level premise                                             │
│ Premise source    │ CStoreInv at the run boundary                                            │
│ Reason            │ Discharge for each prefix/clock state before entering the local helper   │
│                   │ chain.                                                                   │
│ Calls             │ exactService_head_of_proposal                                            │
└───────────────────┴──────────────────────────────────────────────────────────────────────────┘
```

AvailableChain.FGSA.Run.fgsa_exactProposalClaim_of_clean

```text
┌───────────────────┬──────────────────────────────────────────────────────────────────────────┐
│ File:line         │ AvailableChainFGSAProofs/Proofs/Assembly/Outage.lean:14                  │
│ Frozen            │ no                                                                       │
│ Needs premise     │ no new run/top-level premise                                             │
│ Premise source    │ CStoreInv at the run boundary                                            │
│ Reason            │ Discharge for each prefix/clock state before entering the local helper   │
│                   │ chain.                                                                   │
│ Calls             │ outage_exactProposalClaim_of                                             │
└───────────────────┴──────────────────────────────────────────────────────────────────────────┘
```

AvailableChain.FGSA.Run.healing_postReset_inv_cone_of_open₂

```text
┌───────────────────┬──────────────────────────────────────────────────────────────────────────┐
│ File:line         │ AvailableChainFGSAProofs/Proofs/Assembly/ResetArrival.lean:271           │
│ Frozen            │ no                                                                       │
│ Needs premise     │ no new run/top-level premise                                             │
│ Premise source    │ CStoreInv at the run boundary                                            │
│ Reason            │ Discharge for each prefix/clock state before entering the local helper   │
│                   │ chain.                                                                   │
│ Calls             │ healing_postReset_serviceStep₂                                           │
└───────────────────┴──────────────────────────────────────────────────────────────────────────┘
```

AvailableChain.FGSA.Run.healing_frontierSearch

```text
┌───────────────────┬──────────────────────────────────────────────────────────────────────────┐
│ File:line         │ AvailableChainFGSAProofs/Proofs/Healing/FrontierSearchFull.lean:18       │
│ Frozen            │ no                                                                       │
│ Needs premise     │ no new run/top-level premise                                             │
│ Premise source    │ CStoreInv at the run boundary                                            │
│ Reason            │ Discharge for each prefix/clock state before entering the local helper   │
│                   │ chain.                                                                   │
│ Calls             │ frontier_service                                                         │
└───────────────────┴──────────────────────────────────────────────────────────────────────────┘
```

AvailableChain.FGSA.Run.healing_frontierTail

```text
┌───────────────────┬──────────────────────────────────────────────────────────────────────────┐
│ File:line         │ AvailableChainFGSAProofs/Proofs/Healing/FrontierSearchRise.lean:108      │
│ Frozen            │ no                                                                       │
│ Needs premise     │ no new run/top-level premise                                             │
│ Premise source    │ CStoreInv at the run boundary                                            │
│ Reason            │ Discharge for each prefix/clock state before entering the local helper   │
│                   │ chain.                                                                   │
│ Calls             │ frontier_service                                                         │
└───────────────────┴──────────────────────────────────────────────────────────────────────────┘
```

AvailableChain.FGSA.Run.healing_frontierTail_row

```text
┌───────────────────┬──────────────────────────────────────────────────────────────────────────┐
│ File:line         │ AvailableChainFGSAProofs/Proofs/Healing/FrontierSearchTail.lean:22       │
│ Frozen            │ no                                                                       │
│ Needs premise     │ no new run/top-level premise                                             │
│ Premise source    │ CStoreInv at the run boundary                                            │
│ Reason            │ Discharge for each prefix/clock state before entering the local helper   │
│                   │ chain.                                                                   │
│ Calls             │ frontier_service                                                         │
└───────────────────┴──────────────────────────────────────────────────────────────────────────┘
```

AvailableChain.FGSA.Run.healing_healTContract_reset

```text
┌───────────────────┬──────────────────────────────────────────────────────────────────────────┐
│ File:line         │ AvailableChainFGSAProofs/Proofs/Healing/PostReset.lean:28                │
│ Frozen            │ no                                                                       │
│ Needs premise     │ no new run/top-level premise                                             │
│ Premise source    │ CStoreInv at the run boundary                                            │
│ Reason            │ Discharge for each prefix/clock state before entering the local helper   │
│                   │ chain.                                                                   │
│ Calls             │ frontier_service                                                         │
└───────────────────┴──────────────────────────────────────────────────────────────────────────┘
```

AvailableChain.FGSA.Run.healing_postReset_serviceStep

```text
┌───────────────────┬──────────────────────────────────────────────────────────────────────────┐
│ File:line         │ AvailableChainFGSAProofs/Proofs/Healing/PostResetJointStep.lean:51       │
│ Frozen            │ no                                                                       │
│ Needs premise     │ no new run/top-level premise                                             │
│ Premise source    │ CStoreInv at the run boundary                                            │
│ Reason            │ Discharge for each prefix/clock state before entering the local helper   │
│                   │ chain.                                                                   │
│ Calls             │ healing_postReset_service_step                                           │
└───────────────────┴──────────────────────────────────────────────────────────────────────────┘
```

AvailableChain.FGSA.Run.healing_postReset_opening_stored_at

```text
┌───────────────────┬──────────────────────────────────────────────────────────────────────────┐
│ File:line         │ AvailableChainFGSAProofs/Proofs/Healing/PostResetOpening.lean:137        │
│ Frozen            │ no                                                                       │
│ Needs premise     │ no new run/top-level premise                                             │
│ Premise source    │ CStoreInv at the run boundary                                            │
│ Reason            │ Discharge for each prefix/clock state before entering the local helper   │
│                   │ chain.                                                                   │
│ Calls             │ healing_postReset_headCarrier_at                                         │
└───────────────────┴──────────────────────────────────────────────────────────────────────────┘
```

AvailableChain.FGSA.Run.healing_postReset_openingDomain_new_tick_at

```text
┌───────────────────┬──────────────────────────────────────────────────────────────────────────┐
│ File:line         │ AvailableChainFGSAProofs/Proofs/Healing/PostResetOpening.lean:530        │
│ Frozen            │ no                                                                       │
│ Needs premise     │ no new run/top-level premise                                             │
│ Premise source    │ CStoreInv at the run boundary                                            │
│ Reason            │ Discharge for each prefix/clock state before entering the local helper   │
│                   │ chain.                                                                   │
│ Calls             │ healing_postReset_opening_source_prefix_at                               │
└───────────────────┴──────────────────────────────────────────────────────────────────────────┘
```

AvailableChain.FGSA.Run.healing_postReset_headCarrier

```text
┌───────────────────┬──────────────────────────────────────────────────────────────────────────┐
│ File:line         │ AvailableChainFGSAProofs/Proofs/Healing/PostResetOpening.lean:669        │
│ Frozen            │ no                                                                       │
│ Needs premise     │ no new run/top-level premise                                             │
│ Premise source    │ CStoreInv at the run boundary                                            │
│ Reason            │ Discharge for each prefix/clock state before entering the local helper   │
│                   │ chain.                                                                   │
│ Calls             │ healing_postReset_headCarrier_at                                         │
└───────────────────┴──────────────────────────────────────────────────────────────────────────┘
```

AvailableChain.FGSA.Run.healing_postReset_opening_source_prefix

```text
┌───────────────────┬──────────────────────────────────────────────────────────────────────────┐
│ File:line         │ AvailableChainFGSAProofs/Proofs/Healing/PostResetOpening.lean:765        │
│ Frozen            │ no                                                                       │
│ Needs premise     │ no new run/top-level premise                                             │
│ Premise source    │ CStoreInv at the run boundary                                            │
│ Reason            │ Discharge for each prefix/clock state before entering the local helper   │
│                   │ chain.                                                                   │
│ Calls             │ healing_postReset_opening_source_prefix_at                               │
└───────────────────┴──────────────────────────────────────────────────────────────────────────┘
```

AvailableChain.FGSA.Run.healing_tRepair

```text
┌───────────────────┬──────────────────────────────────────────────────────────────────────────┐
│ File:line         │ AvailableChainFGSAProofs/Proofs/Healing/Repair.lean:346                  │
│ Frozen            │ no                                                                       │
│ Needs premise     │ no new run/top-level premise                                             │
│ Premise source    │ CStoreInv at the run boundary                                            │
│ Reason            │ Discharge for each prefix/clock state before entering the local helper   │
│                   │ chain.                                                                   │
│ Calls             │ repair_synchronous, repair_two_lease                                     │
└───────────────────┴──────────────────────────────────────────────────────────────────────────┘
```

AvailableChain.FGSA.Run.inclusion_preGate_bounds

```text
┌───────────────────┬──────────────────────────────────────────────────────────────────────────┐
│ File:line         │ AvailableChainFGSAProofs/Proofs/Outage/InclusionGateBounds.lean:268      │
│ Frozen            │ no                                                                       │
│ Needs premise     │ no new run/top-level premise                                             │
│ Premise source    │ CStoreInv at the run boundary                                            │
│ Reason            │ Discharge for each prefix/clock state before entering the local helper   │
│                   │ chain.                                                                   │
│ Calls             │ inclusion_headAtLabel                                                    │
└───────────────────┴──────────────────────────────────────────────────────────────────────────┘
```

AvailableChain.FGSA.Run.inclusion_gate_exact

```text
┌───────────────────┬──────────────────────────────────────────────────────────────────────────┐
│ File:line         │ AvailableChainFGSAProofs/Proofs/Outage/InclusionGateService.lean:63      │
│ Frozen            │ no                                                                       │
│ Needs premise     │ no new run/top-level premise                                             │
│ Premise source    │ CStoreInv at the run boundary                                            │
│ Reason            │ Discharge for each prefix/clock state before entering the local helper   │
│                   │ chain.                                                                   │
│ Calls             │ inclusion_headAtLabel                                                    │
└───────────────────┴──────────────────────────────────────────────────────────────────────────┘
```

AvailableChain.FGSA.Run.healing_frontierSearch_of_set

```text
┌───────────────────┬──────────────────────────────────────────────────────────────────────────┐
│ File:line         │ AvailableChainFGSAProofs/Proofs/Assembly/ResetArrival.lean:53            │
│ Frozen            │ no                                                                       │
│ Needs premise     │ no new run/top-level premise                                             │
│ Premise source    │ CStoreInv at the run boundary                                            │
│ Reason            │ Discharge for each prefix/clock state before entering the local helper   │
│                   │ chain.                                                                   │
│ Calls             │ healing_frontierSearch, healing_tRepair                                  │
└───────────────────┴──────────────────────────────────────────────────────────────────────────┘
```

AvailableChain.FGSA.Run.healing_postReset_inv_of_open

```text
┌───────────────────┬──────────────────────────────────────────────────────────────────────────┐
│ File:line         │ AvailableChainFGSAProofs/Proofs/Assembly/ResetArrival.lean:107           │
│ Frozen            │ no                                                                       │
│ Needs premise     │ no new run/top-level premise                                             │
│ Premise source    │ CStoreInv at the run boundary                                            │
│ Reason            │ Discharge for each prefix/clock state before entering the local helper   │
│                   │ chain.                                                                   │
│ Calls             │ healing_postReset_serviceStep                                            │
└───────────────────┴──────────────────────────────────────────────────────────────────────────┘
```

AvailableChain.FGSA.Run.healing_resetArrivalFull_of_open₂

```text
┌───────────────────┬──────────────────────────────────────────────────────────────────────────┐
│ File:line         │ AvailableChainFGSAProofs/Proofs/Assembly/ResetArrival.lean:340           │
│ Frozen            │ no                                                                       │
│ Needs premise     │ no new run/top-level premise                                             │
│ Premise source    │ CStoreInv at the run boundary                                            │
│ Reason            │ Discharge for each prefix/clock state before entering the local helper   │
│                   │ chain.                                                                   │
│ Calls             │ healing_postReset_inv_cone_of_open₂                                      │
└───────────────────┴──────────────────────────────────────────────────────────────────────────┘
```

AvailableChain.FGSA.Run.healing_hTimeClaim_of_open₂

```text
┌───────────────────┬──────────────────────────────────────────────────────────────────────────┐
│ File:line         │ AvailableChainFGSAProofs/Proofs/Assembly/ResetArrival.lean:363           │
│ Frozen            │ no                                                                       │
│ Needs premise     │ no new run/top-level premise                                             │
│ Premise source    │ CStoreInv at the run boundary                                            │
│ Reason            │ Discharge for each prefix/clock state before entering the local helper   │
│                   │ chain.                                                                   │
│ Calls             │ healing_postReset_inv_cone_of_open₂                                      │
└───────────────────┴──────────────────────────────────────────────────────────────────────────┘
```

AvailableChain.FGSA.Run.healing_healingInputClaim

```text
┌───────────────────┬──────────────────────────────────────────────────────────────────────────┐
│ File:line         │ AvailableChainFGSAProofs/Proofs/Assembly/ResetArrival.lean:517           │
│ Frozen            │ no                                                                       │
│ Needs premise     │ no new run/top-level premise                                             │
│ Premise source    │ CStoreInv at the run boundary                                            │
│ Reason            │ Discharge for each prefix/clock state before entering the local helper   │
│                   │ chain.                                                                   │
│ Calls             │ healing_postReset_inv_cone_of_open₂                                      │
└───────────────────┴──────────────────────────────────────────────────────────────────────────┘
```

AvailableChain.FGSA.Run.fgsaClaims_of_open

```text
┌───────────────────┬──────────────────────────────────────────────────────────────────────────┐
│ File:line         │ AvailableChainFGSAProofs/Proofs/Assembly/Root.lean:53                    │
│ Frozen            │ no                                                                       │
│ Needs premise     │ no new run/top-level premise                                             │
│ Premise source    │ CStoreInv at the run boundary                                            │
│ Reason            │ Discharge for each prefix/clock state before entering the local helper   │
│                   │ chain.                                                                   │
│ Calls             │ fgsa_exactProposalClaim_of_clean                                         │
└───────────────────┴──────────────────────────────────────────────────────────────────────────┘
```

AvailableChain.FGSA.Run.attempt_repair_opening

```text
┌───────────────────┬──────────────────────────────────────────────────────────────────────────┐
│ File:line         │ AvailableChainFGSAProofs/Proofs/Healing/AttemptRows.lean:172             │
│ Frozen            │ no                                                                       │
│ Needs premise     │ no new run/top-level premise                                             │
│ Premise source    │ CStoreInv at the run boundary                                            │
│ Reason            │ Discharge for each prefix/clock state before entering the local helper   │
│                   │ chain.                                                                   │
│ Calls             │ healing_tRepair                                                          │
└───────────────────┴──────────────────────────────────────────────────────────────────────────┘
```

AvailableChain.FGSA.Run.frontierSearch_row_task

```text
┌───────────────────┬──────────────────────────────────────────────────────────────────────────┐
│ File:line         │ AvailableChainFGSAProofs/Proofs/Healing/FrontierSearchTasks.lean:115     │
│ Frozen            │ no                                                                       │
│ Needs premise     │ no new run/top-level premise                                             │
│ Premise source    │ CStoreInv at the run boundary                                            │
│ Reason            │ Discharge for each prefix/clock state before entering the local helper   │
│                   │ chain.                                                                   │
│ Calls             │ healing_frontierTail_row                                                 │
└───────────────────┴──────────────────────────────────────────────────────────────────────────┘
```

AvailableChain.FGSA.Run.healing_postReset_opening_clock_stored_at

```text
┌───────────────────┬──────────────────────────────────────────────────────────────────────────┐
│ File:line         │ AvailableChainFGSAProofs/Proofs/Healing/PostResetOpening.lean:179        │
│ Frozen            │ no                                                                       │
│ Needs premise     │ no new run/top-level premise                                             │
│ Premise source    │ CStoreInv at the run boundary                                            │
│ Reason            │ Discharge for each prefix/clock state before entering the local helper   │
│                   │ chain.                                                                   │
│ Calls             │ healing_postReset_opening_stored_at                                      │
└───────────────────┴──────────────────────────────────────────────────────────────────────────┘
```

AvailableChain.FGSA.Run.healing_postReset_openingDomain_step_at

```text
┌───────────────────┬──────────────────────────────────────────────────────────────────────────┐
│ File:line         │ AvailableChainFGSAProofs/Proofs/Healing/PostResetOpening.lean:616        │
│ Frozen            │ no                                                                       │
│ Needs premise     │ no new run/top-level premise                                             │
│ Premise source    │ CStoreInv at the run boundary                                            │
│ Reason            │ Discharge for each prefix/clock state before entering the local helper   │
│                   │ chain.                                                                   │
│ Calls             │ healing_postReset_openingDomain_new_tick_at                              │
└───────────────────┴──────────────────────────────────────────────────────────────────────────┘
```

AvailableChain.FGSA.Run.healing_postReset_opening_stored

```text
┌───────────────────┬──────────────────────────────────────────────────────────────────────────┐
│ File:line         │ AvailableChainFGSAProofs/Proofs/Healing/PostResetOpening.lean:686        │
│ Frozen            │ no                                                                       │
│ Needs premise     │ no new run/top-level premise                                             │
│ Premise source    │ CStoreInv at the run boundary                                            │
│ Reason            │ Discharge for each prefix/clock state before entering the local helper   │
│                   │ chain.                                                                   │
│ Calls             │ healing_postReset_opening_stored_at                                      │
└───────────────────┴──────────────────────────────────────────────────────────────────────────┘
```

AvailableChain.FGSA.Run.healing_postReset_openingDomain_new_tick

```text
┌───────────────────┬──────────────────────────────────────────────────────────────────────────┐
│ File:line         │ AvailableChainFGSAProofs/Proofs/Healing/PostResetOpening.lean:782        │
│ Frozen            │ no                                                                       │
│ Needs premise     │ no new run/top-level premise                                             │
│ Premise source    │ CStoreInv at the run boundary                                            │
│ Reason            │ Discharge for each prefix/clock state before entering the local helper   │
│                   │ chain.                                                                   │
│ Calls             │ healing_postReset_openingDomain_new_tick_at                              │
└───────────────────┴──────────────────────────────────────────────────────────────────────────┘
```

AvailableChain.FGSA.Run.healing_rise_one_repair

```text
┌───────────────────┬──────────────────────────────────────────────────────────────────────────┐
│ File:line         │ AvailableChainFGSAProofs/Proofs/Healing/RiseOneRepair.lean:51            │
│ Frozen            │ no                                                                       │
│ Needs premise     │ no new run/top-level premise                                             │
│ Premise source    │ CStoreInv at the run boundary                                            │
│ Reason            │ Discharge for each prefix/clock state before entering the local helper   │
│                   │ chain.                                                                   │
│ Calls             │ healing_tRepair                                                          │
└───────────────────┴──────────────────────────────────────────────────────────────────────────┘
```

AvailableChain.FGSA.Run.healing_rise_one_repair_synchronous

```text
┌───────────────────┬──────────────────────────────────────────────────────────────────────────┐
│ File:line         │ AvailableChainFGSAProofs/Proofs/Healing/RiseOneRepair.lean:90            │
│ Frozen            │ no                                                                       │
│ Needs premise     │ no new run/top-level premise                                             │
│ Premise source    │ CStoreInv at the run boundary                                            │
│ Reason            │ Discharge for each prefix/clock state before entering the local helper   │
│                   │ chain.                                                                   │
│ Calls             │ healing_tRepair                                                          │
└───────────────────┴──────────────────────────────────────────────────────────────────────────┘
```

AvailableChain.FGSA.Run.clean_inclusion_post_gate_body

```text
┌───────────────────┬──────────────────────────────────────────────────────────────────────────┐
│ File:line         │ AvailableChainFGSAProofs/Proofs/Outage/InclusionGateBody.lean:17         │
│ Frozen            │ no                                                                       │
│ Needs premise     │ no new run/top-level premise                                             │
│ Premise source    │ CStoreInv at the run boundary                                            │
│ Reason            │ Discharge for each prefix/clock state before entering the local helper   │
│                   │ chain.                                                                   │
│ Calls             │ inclusion_gate_exact                                                     │
└───────────────────┴──────────────────────────────────────────────────────────────────────────┘
```

AvailableChain.FGSA.Run.healing_resetArrivalStatement

```text
┌───────────────────┬──────────────────────────────────────────────────────────────────────────┐
│ File:line         │ AvailableChainFGSAProofs/Proofs/Assembly/ResetArrival.lean:78            │
│ Frozen            │ no                                                                       │
│ Needs premise     │ no new run/top-level premise                                             │
│ Premise source    │ CStoreInv at the run boundary                                            │
│ Reason            │ Discharge for each prefix/clock state before entering the local helper   │
│                   │ chain.                                                                   │
│ Calls             │ healing_frontierSearch_of_set                                            │
└───────────────────┴──────────────────────────────────────────────────────────────────────────┘
```

AvailableChain.FGSA.Run.healing_resetArrivalFull_of_open

```text
┌───────────────────┬──────────────────────────────────────────────────────────────────────────┐
│ File:line         │ AvailableChainFGSAProofs/Proofs/Assembly/ResetArrival.lean:166           │
│ Frozen            │ no                                                                       │
│ Needs premise     │ no new run/top-level premise                                             │
│ Premise source    │ CStoreInv at the run boundary                                            │
│ Reason            │ Discharge for each prefix/clock state before entering the local helper   │
│                   │ chain.                                                                   │
│ Calls             │ healing_postReset_inv_of_open                                            │
└───────────────────┴──────────────────────────────────────────────────────────────────────────┘
```

AvailableChain.FGSA.Run.healing_hTimeClaim_of_open

```text
┌───────────────────┬──────────────────────────────────────────────────────────────────────────┐
│ File:line         │ AvailableChainFGSAProofs/Proofs/Assembly/ResetArrival.lean:197           │
│ Frozen            │ no                                                                       │
│ Needs premise     │ no new run/top-level premise                                             │
│ Premise source    │ CStoreInv at the run boundary                                            │
│ Reason            │ Discharge for each prefix/clock state before entering the local helper   │
│                   │ chain.                                                                   │
│ Calls             │ healing_postReset_inv_of_open                                            │
└───────────────────┴──────────────────────────────────────────────────────────────────────────┘
```

AvailableChain.FGSA.Run.healing_hTimeClaim_of_steps

```text
┌───────────────────┬──────────────────────────────────────────────────────────────────────────┐
│ File:line         │ AvailableChainFGSAProofs/Proofs/Assembly/ResetArrival.lean:437           │
│ Frozen            │ no                                                                       │
│ Needs premise     │ no new run/top-level premise                                             │
│ Premise source    │ CStoreInv at the run boundary                                            │
│ Reason            │ Discharge for each prefix/clock state before entering the local helper   │
│                   │ chain.                                                                   │
│ Calls             │ healing_hTimeClaim_of_open₂                                              │
└───────────────────┴──────────────────────────────────────────────────────────────────────────┘
```

AvailableChain.FGSA.Run.healing_resetArrivalFull

```text
┌───────────────────┬──────────────────────────────────────────────────────────────────────────┐
│ File:line         │ AvailableChainFGSAProofs/Proofs/Assembly/ResetArrival.lean:508           │
│ Frozen            │ no                                                                       │
│ Needs premise     │ no new run/top-level premise                                             │
│ Premise source    │ CStoreInv at the run boundary                                            │
│ Reason            │ Discharge for each prefix/clock state before entering the local helper   │
│                   │ chain.                                                                   │
│ Calls             │ healing_resetArrivalFull_of_open₂                                        │
└───────────────────┴──────────────────────────────────────────────────────────────────────────┘
```

AvailableChain.FGSA.Run.fgsaClaims_of_hTime

```text
┌───────────────────┬──────────────────────────────────────────────────────────────────────────┐
│ File:line         │ AvailableChainFGSAProofs/Proofs/Assembly/Root.lean:98                    │
│ Frozen            │ no                                                                       │
│ Needs premise     │ no new run/top-level premise                                             │
│ Premise source    │ CStoreInv at the run boundary                                            │
│ Reason            │ Discharge for each prefix/clock state before entering the local helper   │
│                   │ chain.                                                                   │
│ Calls             │ fgsaClaims_of_open                                                       │
└───────────────────┴──────────────────────────────────────────────────────────────────────────┘
```

AvailableChain.FGSA.Run.healing_attempt_firstRow_contest

```text
┌───────────────────┬──────────────────────────────────────────────────────────────────────────┐
│ File:line         │ AvailableChainFGSAProofs/Proofs/Healing/AttemptRows.lean:266             │
│ Frozen            │ no                                                                       │
│ Needs premise     │ no new run/top-level premise                                             │
│ Premise source    │ CStoreInv at the run boundary                                            │
│ Reason            │ Discharge for each prefix/clock state before entering the local helper   │
│                   │ chain.                                                                   │
│ Calls             │ attempt_repair_opening                                                   │
└───────────────────┴──────────────────────────────────────────────────────────────────────────┘
```

AvailableChain.FGSA.Run.healing_attempt_firstRow_other

```text
┌───────────────────┬──────────────────────────────────────────────────────────────────────────┐
│ File:line         │ AvailableChainFGSAProofs/Proofs/Healing/AttemptRows.lean:335             │
│ Frozen            │ no                                                                       │
│ Needs premise     │ no new run/top-level premise                                             │
│ Premise source    │ CStoreInv at the run boundary                                            │
│ Reason            │ Discharge for each prefix/clock state before entering the local helper   │
│                   │ chain.                                                                   │
│ Calls             │ attempt_repair_opening                                                   │
└───────────────────┴──────────────────────────────────────────────────────────────────────────┘
```

AvailableChain.FGSA.Run.healing_attempt_raise_contest

```text
┌───────────────────┬──────────────────────────────────────────────────────────────────────────┐
│ File:line         │ AvailableChainFGSAProofs/Proofs/Healing/AttemptRows.lean:498             │
│ Frozen            │ no                                                                       │
│ Needs premise     │ no new run/top-level premise                                             │
│ Premise source    │ CStoreInv at the run boundary                                            │
│ Reason            │ Discharge for each prefix/clock state before entering the local helper   │
│                   │ chain.                                                                   │
│ Calls             │ attempt_repair_opening                                                   │
└───────────────────┴──────────────────────────────────────────────────────────────────────────┘
```

AvailableChain.FGSA.Run.healing_attempt_raise_other

```text
┌───────────────────┬──────────────────────────────────────────────────────────────────────────┐
│ File:line         │ AvailableChainFGSAProofs/Proofs/Healing/AttemptRows.lean:531             │
│ Frozen            │ no                                                                       │
│ Needs premise     │ no new run/top-level premise                                             │
│ Premise source    │ CStoreInv at the run boundary                                            │
│ Reason            │ Discharge for each prefix/clock state before entering the local helper   │
│                   │ chain.                                                                   │
│ Calls             │ attempt_repair_opening                                                   │
└───────────────────┴──────────────────────────────────────────────────────────────────────────┘
```

AvailableChain.FGSA.Run.healing_postReset_openingDomainStep₂

```text
┌───────────────────┬──────────────────────────────────────────────────────────────────────────┐
│ File:line         │ AvailableChainFGSAProofs/Proofs/Healing/PostResetJointStep2.lean:38      │
│ Frozen            │ no                                                                       │
│ Needs premise     │ no new run/top-level premise                                             │
│ Premise source    │ CStoreInv at the run boundary                                            │
│ Reason            │ Discharge for each prefix/clock state before entering the local helper   │
│                   │ chain.                                                                   │
│ Calls             │ healing_postReset_openingDomain_step_at                                  │
└───────────────────┴──────────────────────────────────────────────────────────────────────────┘
```

AvailableChain.FGSA.Run.healing_postReset_opening_clock_stored

```text
┌───────────────────┬──────────────────────────────────────────────────────────────────────────┐
│ File:line         │ AvailableChainFGSAProofs/Proofs/Healing/PostResetOpening.lean:699        │
│ Frozen            │ no                                                                       │
│ Needs premise     │ no new run/top-level premise                                             │
│ Premise source    │ CStoreInv at the run boundary                                            │
│ Reason            │ Discharge for each prefix/clock state before entering the local helper   │
│                   │ chain.                                                                   │
│ Calls             │ healing_postReset_opening_clock_stored_at                                │
└───────────────────┴──────────────────────────────────────────────────────────────────────────┘
```

AvailableChain.FGSA.Run.healing_postReset_openingDomain_step

```text
┌───────────────────┬──────────────────────────────────────────────────────────────────────────┐
│ File:line         │ AvailableChainFGSAProofs/Proofs/Healing/PostResetOpening.lean:796        │
│ Frozen            │ no                                                                       │
│ Needs premise     │ no new run/top-level premise                                             │
│ Premise source    │ CStoreInv at the run boundary                                            │
│ Reason            │ Discharge for each prefix/clock state before entering the local helper   │
│                   │ chain.                                                                   │
│ Calls             │ healing_postReset_openingDomain_step_at                                  │
└───────────────────┴──────────────────────────────────────────────────────────────────────────┘
```

AvailableChain.FGSA.Run.healing_rise_one_repair_opening

```text
┌───────────────────┬──────────────────────────────────────────────────────────────────────────┐
│ File:line         │ AvailableChainFGSAProofs/Proofs/Healing/RiseOneRepair.lean:239           │
│ Frozen            │ no                                                                       │
│ Needs premise     │ no new run/top-level premise                                             │
│ Premise source    │ CStoreInv at the run boundary                                            │
│ Reason            │ Discharge for each prefix/clock state before entering the local helper   │
│                   │ chain.                                                                   │
│ Calls             │ healing_rise_one_repair                                                  │
└───────────────────┴──────────────────────────────────────────────────────────────────────────┘
```

AvailableChain.FGSA.Run.outage_cleanInclusionPostGateClaim_of

```text
┌───────────────────┬──────────────────────────────────────────────────────────────────────────┐
│ File:line         │ AvailableChainFGSAProofs/Proofs/Outage/Export.lean:116                   │
│ Frozen            │ no                                                                       │
│ Needs premise     │ no new run/top-level premise                                             │
│ Premise source    │ CStoreInv at the run boundary                                            │
│ Reason            │ Discharge for each prefix/clock state before entering the local helper   │
│                   │ chain.                                                                   │
│ Calls             │ clean_inclusion_post_gate_body                                           │
└───────────────────┴──────────────────────────────────────────────────────────────────────────┘
```

AvailableChain.FGSA.Run.clean_inclusion_body

```text
┌───────────────────┬──────────────────────────────────────────────────────────────────────────┐
│ File:line         │ AvailableChainFGSAProofs/Proofs/Outage/InclusionGateBody.lean:71         │
│ Frozen            │ no                                                                       │
│ Needs premise     │ no new run/top-level premise                                             │
│ Premise source    │ CStoreInv at the run boundary                                            │
│ Reason            │ Discharge for each prefix/clock state before entering the local helper   │
│                   │ chain.                                                                   │
│ Calls             │ clean_inclusion_post_gate_body                                           │
└───────────────────┴──────────────────────────────────────────────────────────────────────────┘
```

AvailableChain.FGSA.Run.fgsa_cleanInclusionPostGateClaim_of_clean

```text
┌───────────────────┬──────────────────────────────────────────────────────────────────────────┐
│ File:line         │ AvailableChainFGSAProofs/Proofs/Assembly/Outage.lean:38                  │
│ Frozen            │ no                                                                       │
│ Needs premise     │ no new run/top-level premise                                             │
│ Premise source    │ CStoreInv at the run boundary                                            │
│ Reason            │ Discharge for each prefix/clock state before entering the local helper   │
│                   │ chain.                                                                   │
│ Calls             │ outage_cleanInclusionPostGateClaim_of                                    │
└───────────────────┴──────────────────────────────────────────────────────────────────────────┘
```

AvailableChain.FGSA.Run.healing_hTimeClaim

```text
┌───────────────────┬──────────────────────────────────────────────────────────────────────────┐
│ File:line         │ AvailableChainFGSAProofs/Proofs/Assembly/ResetArrival.lean:498           │
│ Frozen            │ no                                                                       │
│ Needs premise     │ no new run/top-level premise                                             │
│ Premise source    │ CStoreInv at the run boundary                                            │
│ Reason            │ Discharge for each prefix/clock state before entering the local helper   │
│                   │ chain.                                                                   │
│ Calls             │ healing_hTimeClaim_of_steps                                              │
└───────────────────┴──────────────────────────────────────────────────────────────────────────┘
```

AvailableChain.FGSA.Run.fgsaClaims

```text
┌───────────────────┬──────────────────────────────────────────────────────────────────────────┐
│ File:line         │ AvailableChainFGSAProofs/Proofs/Assembly/Root.lean:112                   │
│ Frozen            │ no                                                                       │
│ Needs premise     │ no new run/top-level premise                                             │
│ Premise source    │ CStoreInv at the run boundary                                            │
│ Reason            │ Discharge for each prefix/clock state before entering the local helper   │
│                   │ chain.                                                                   │
│ Calls             │ fgsaClaims_of_hTime                                                      │
└───────────────────┴──────────────────────────────────────────────────────────────────────────┘
```

AvailableChain.FGSA.Run.healing_progressAttempt

```text
┌───────────────────┬──────────────────────────────────────────────────────────────────────────┐
│ File:line         │ AvailableChainFGSAProofs/Proofs/Healing/Attempt.lean:112                 │
│ Frozen            │ no                                                                       │
│ Needs premise     │ no new run/top-level premise                                             │
│ Premise source    │ CStoreInv at the run boundary                                            │
│ Reason            │ Discharge for each prefix/clock state before entering the local helper   │
│                   │ chain.                                                                   │
│ Calls             │ healing_attempt_firstRow_contest, healing_attempt_firstRow_other,        │
│                   │ healing_attempt_raise_contest, healing_attempt_raise_other               │
└───────────────────┴──────────────────────────────────────────────────────────────────────────┘
```

AvailableChain.FGSA.Run.healing_postReset_openingDomainStep

```text
┌───────────────────┬──────────────────────────────────────────────────────────────────────────┐
│ File:line         │ AvailableChainFGSAProofs/Proofs/Healing/PostResetJointStep.lean:40       │
│ Frozen            │ no                                                                       │
│ Needs premise     │ no new run/top-level premise                                             │
│ Premise source    │ CStoreInv at the run boundary                                            │
│ Reason            │ Discharge for each prefix/clock state before entering the local helper   │
│                   │ chain.                                                                   │
│ Calls             │ healing_postReset_openingDomain_step                                     │
└───────────────────┴──────────────────────────────────────────────────────────────────────────┘
```

AvailableChain.FGSA.Run.healing_rise_one_rise

```text
┌───────────────────┬──────────────────────────────────────────────────────────────────────────┐
│ File:line         │ AvailableChainFGSAProofs/Proofs/Healing/RiseOneRise.lean:20              │
│ Frozen            │ no                                                                       │
│ Needs premise     │ no new run/top-level premise                                             │
│ Premise source    │ CStoreInv at the run boundary                                            │
│ Reason            │ Discharge for each prefix/clock state before entering the local helper   │
│                   │ chain.                                                                   │
│ Calls             │ healing_rise_one_repair_opening                                          │
└───────────────────┴──────────────────────────────────────────────────────────────────────────┘
```

AvailableChain.FGSA.Run.outage_cleanInclusionClaim_of

```text
┌───────────────────┬──────────────────────────────────────────────────────────────────────────┐
│ File:line         │ AvailableChainFGSAProofs/Proofs/Outage/Export.lean:138                   │
│ Frozen            │ no                                                                       │
│ Needs premise     │ no new run/top-level premise                                             │
│ Premise source    │ CStoreInv at the run boundary                                            │
│ Reason            │ Discharge for each prefix/clock state before entering the local helper   │
│                   │ chain.                                                                   │
│ Calls             │ clean_inclusion_body                                                     │
└───────────────────┴──────────────────────────────────────────────────────────────────────────┘
```

AvailableChain.FGSA.Run.clean_growth_body

```text
┌───────────────────┬──────────────────────────────────────────────────────────────────────────┐
│ File:line         │ AvailableChainFGSAProofs/Proofs/Outage/Growth.lean:21                    │
│ Frozen            │ no                                                                       │
│ Needs premise     │ no new run/top-level premise                                             │
│ Premise source    │ CStoreInv at the run boundary                                            │
│ Reason            │ Discharge for each prefix/clock state before entering the local helper   │
│                   │ chain.                                                                   │
│ Calls             │ clean_inclusion_body                                                     │
└───────────────────┴──────────────────────────────────────────────────────────────────────────┘
```

AvailableChain.FGSA.Run.fgsa_cleanInclusionClaim_of_clean

```text
┌───────────────────┬──────────────────────────────────────────────────────────────────────────┐
│ File:line         │ AvailableChainFGSAProofs/Proofs/Assembly/Outage.lean:66                  │
│ Frozen            │ no                                                                       │
│ Needs premise     │ no new run/top-level premise                                             │
│ Premise source    │ CStoreInv at the run boundary                                            │
│ Reason            │ Discharge for each prefix/clock state before entering the local helper   │
│                   │ chain.                                                                   │
│ Calls             │ outage_cleanInclusionClaim_of                                            │
└───────────────────┴──────────────────────────────────────────────────────────────────────────┘
```

AvailableChain.FGSA.Run.healing_progressAttemptStatement

```text
┌───────────────────┬──────────────────────────────────────────────────────────────────────────┐
│ File:line         │ AvailableChainFGSAProofs/Proofs/Assembly/ProgressAttempt.lean:14         │
│ Frozen            │ no                                                                       │
│ Needs premise     │ no new run/top-level premise                                             │
│ Premise source    │ CStoreInv at the run boundary                                            │
│ Reason            │ Discharge for each prefix/clock state before entering the local helper   │
│                   │ chain.                                                                   │
│ Calls             │ healing_progressAttempt                                                  │
└───────────────────┴──────────────────────────────────────────────────────────────────────────┘
```

AvailableChain.FGSA.Run.healing_hTimeClaim_all

```text
┌───────────────────┬──────────────────────────────────────────────────────────────────────────┐
│ File:line         │ AvailableChainFGSAProofs/Proofs/Assembly/ResetArrival.lean:504           │
│ Frozen            │ no                                                                       │
│ Needs premise     │ no new run/top-level premise                                             │
│ Premise source    │ CStoreInv at the run boundary                                            │
│ Reason            │ Discharge for each prefix/clock state before entering the local helper   │
│                   │ chain.                                                                   │
│ Calls             │ healing_hTimeClaim                                                       │
└───────────────────┴──────────────────────────────────────────────────────────────────────────┘
```

AvailableChain.FGSA.Run.outage_cleanGrowthClaim_of

```text
┌───────────────────┬──────────────────────────────────────────────────────────────────────────┐
│ File:line         │ AvailableChainFGSAProofs/Proofs/Outage/Export.lean:160                   │
│ Frozen            │ no                                                                       │
│ Needs premise     │ no new run/top-level premise                                             │
│ Premise source    │ CStoreInv at the run boundary                                            │
│ Reason            │ Discharge for each prefix/clock state before entering the local helper   │
│                   │ chain.                                                                   │
│ Calls             │ clean_growth_body                                                        │
└───────────────────┴──────────────────────────────────────────────────────────────────────────┘
```

AvailableChain.FGSA.Run.fgsa_cleanGrowthClaim_of_clean

```text
┌───────────────────┬──────────────────────────────────────────────────────────────────────────┐
│ File:line         │ AvailableChainFGSAProofs/Proofs/Assembly/Outage.lean:93                  │
│ Frozen            │ no                                                                       │
│ Needs premise     │ no new run/top-level premise                                             │
│ Premise source    │ CStoreInv at the run boundary                                            │
│ Reason            │ Discharge for each prefix/clock state before entering the local helper   │
│                   │ chain.                                                                   │
│ Calls             │ outage_cleanGrowthClaim_of                                               │
└───────────────────┴──────────────────────────────────────────────────────────────────────────┘
```

