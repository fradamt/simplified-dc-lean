# Formation (C7): OPEN inputs

This file lists the inputs that C7 `FormationClaim` still needs. The
Formation writer owns this file and the `Clean/Formation*` modules.
`Clean/OPEN.md` covers the rest of the Clean lane.

## Status

`Assembly/Formation.lean` proves C7 under named hypotheses:

- `pcsa_formation_of_open`: `FormationPrem` and the two OPEN inputs below
  give `FormationConcl`.
- `pcsa_formation_source_of_open`: `FormationPrem` and the two back
  receipts give the Formation source with C1 connected.

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
- Retained walk facts `hKeep`, `hReflect`, `hUnique`
  (`FormationRetainedTree`): equal stage-1 eligibility
  (`pcsa_formation_retained_eligible_eq`, from the two back receipts) and
  voter-tree inclusion (`pcsa_formation_retained_tree`: each voter-tree
  body is `N.erase` or a proposer-tree body). Formation body relay carries
  the frozen bodies to the proposer by `t_s`; the other bodies are
  prefixes of the unique slot-`s` body.

## OPEN input 1: the two retained back receipts

The binder is `hBack`, with type `FormationRetainedBackOpen p src dst s N`.
It covers the honest proposer read at `t_s` (`src`) and each honest voter
awake at `v_s` (`dst`):

- `hRawBack`: each voter raw HEAD is in the proposer raw list, or its seat
  is capped there.
- `hSupportBack`: the same, for the support lists.

`pcsa_formation_retained_open_of_back` derives the five retained HEAD
facts (`FormationRetainedHeadOpen`) from these two.

Plan (Codex plan `plan-formation-inputs-sol.md`, items 4–8): the carried
arm is the proposal's own lists. The frozen arm needs the windowed form of
the Clean frozen relay (`pcsa_frozen_input_in_proposer`,
`pcsa_frozen_support_in_proposer`) for the Formation deadline. Then port
the two-arm Clean proofs `pcsa_common_raw_transfer` and
`pcsa_honest_support_backward`.

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
