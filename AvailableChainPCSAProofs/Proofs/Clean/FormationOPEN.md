# Formation (C7): OPEN inputs

This file lists the inputs that C7 `FormationClaim` still needs. The
Formation writer owns this file and the `Clean/Formation*` modules.
`Clean/OPEN.md` covers the rest of the Clean lane.

## Status

`Assembly/Formation.lean` proves C7 under named hypotheses:

- `pcsa_formation_of_open`: `FormationPrem` and the two OPEN inputs below
  give `FormationConcl`.
- `pcsa_formation_source_of_open`: `FormationPrem` and the frozen raw
  relay give the Formation source with C1 connected.

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
- Retained back receipts `hRawBack`, `hSupportBack`
  (`pcsa_formation_retained_back_of_frozen`, `FormationRetainedBack`): the
  carried arms are the proposal's own lists. A frozen support HEAD relays
  as a raw HEAD; Formation body relay gives its body at the proposer
  (`pcsa_formation_frozen_body_in_proposer`).

## OPEN input 1: the frozen raw relay

The binder is `hFrozen`, with type `FormationFrozenRawOpen p src dst s`.
It covers the honest proposer read at `t_s` (`src`) and each honest voter
awake at `v_s` (`dst`): a HEAD `⟨seat (s-1) i, head r⟩` in the voter pool
with a stamp before `z_{s-1}` is in the proposer raw list
(`proposerVotes src.st s`), or seat `i` is capped there.

`pcsa_formation_preFreeze_inputs_of_frozen` derives all pre-freeze inputs
from it.

Plan: this is the Clean `pcsa_frozen_input_in_proposer` at slot `s - 1`,
with the windowed delivery `max t z_{s-1} + Δ` in place of
`HealthyPrefixDeliveryBy`. Its only delivery step is the relay of the
accepted HEAD (`pcsa_head_relay_late_or_cap`), with deadline `t_s` in place
of `t + Δ`. The windowed relay helpers of the Clean restart work supply it.

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
