# Formation (C7): OPEN inputs

This file lists the inputs that C7 `FormationClaim` still needs. The
Formation writer owns this file and the `Clean/Formation*` modules.
`Clean/OPEN.md` covers the rest of the Clean lane.

## Status

`Assembly/Formation.lean` proves C7 under named hypotheses:

- `pcsa_formation_of_open`: `FormationPrem` and the two OPEN inputs below
  give `FormationConcl`.
- `pcsa_formation_source_of_open`: `FormationPrem` and the retained HEAD
  facts give the Formation source with C1 connected.

The `FormationClaim` field of `PCSAClaims` stays OPEN until both inputs
are proved.

The F4 statement fix is part of this landing. It adds
`FormationRootReachable` and the `proposerRootReachable` fields of
`FormationPrem` and `HealedSourcePrem` (at `r * p.R`). Without it,
`FormationPrem` is false. `docs/PCSA-API.md` is regenerated.

Proved inputs, with their producers:

- Frozen-PC origins, receipt, collection, freeze retention, stop, and
  non-equivocation: `FormationOrigins`, `FormationCollection`,
  `FormationFreeze`, `FormationTerminal`, `FormationHeads`.
- Proposal presence and metadata at `v_s` and `e_s`, resolution, support
  retention, raw-HEAD carriage, the current child:
  `FormationInputs`, from Shared body relay and honest-proposal receipt.
- Exact honest HEADs: `pcsa_formation_head_exact_of_retained`, from the
  retained inputs only.
- Early HEAD receipt: `pcsa_formation_early_heads_of_exact`
  (`FormationEarlyHeads`). Formation delivery after `z_{s-1}` is the
  strict `t + Δ` delivery of the Clean receipt proofs.
- Ack admission: `pcsa_formation_preFreeze_ack_admit`, from Clean
  `pcsa_honest_ack_admitted`.

## OPEN input 1: the five retained HEAD facts

The binder is `hRetained`, with type `FormationRetainedHeadOpen p src dst s N`.
It covers the honest proposer read at `t_s` (`src`) and each honest voter
awake at `v_s` (`dst`):

- `hRawBack`: each voter raw HEAD is in the proposer raw list, or its seat
  is capped there.
- `hSupportBack`: the same, for the support lists.
- `hKeep`: `Gen.Pure.SuffixPersists` below `parent(P)`.
- `hReflect`: `Gen.Pure.SuffixReflects` below `parent(P)`.
- `hUnique`: `N.erase` is the only eligible voter child of `parent(P)`.

Plan (Codex plan `plan-formation-inputs-sol.md`, items 4–8):

1. Port the two-arm Clean raw transfer (`pcsa_common_raw_transfer`). Adapt
   the frozen HEAD relay helper to the Formation deadline.
2. Adapt `pcsa_honest_support_backward` for `hSupportBack`.
3. Prove the voter-tree inclusion `C = N.erase ∨ C ∈ sourceTree` and equal
   eligibility. These close `hKeep`, `hReflect` and `hUnique`.

## OPEN input 2: the late gate counts

The binder is `hGateCounts`: for each honest gate read, there is an `H`
with `(awakeHonestLabel p c E rho s).card ≤ H` and
`FormationGateCounts p st s N.erase H f`. Its fields are `hVoters`,
`hPath`, `hRivals` and `hChildren`.

Plan (Codex plan, items 1, 2, 9, 10): take `H` as the number of honest
HEAD seats awake at `v_s`, that is, all honest HEAD senders. The smaller
choice `H := h_s` is refuted (the plan gives an `n = 8` run). Adapt
`pcsa_late_participant_bound` for `hVoters`. For `hChildren`, keep the
additive inequality and use a disjoint child-support seat set.
