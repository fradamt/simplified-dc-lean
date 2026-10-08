# Formation (C7): OPEN inputs

This file lists the inputs that C7 `FormationClaim` still needs. The
Formation writer owns this file and the `Clean/Formation*` modules.
`Clean/OPEN.md` covers the rest of the Clean lane.

## Status

`Assembly/Formation.lean` proves the claims under one named OPEN input,
`hFrozen`: a producer of the frozen raw relay at every Formation context
(the same binders as `FormationClaim`):

- `pcsa_formation_of_open`: `hFrozen` gives `FormationClaim p`.
- `pcsa_formation_source_of_open`: `hFrozen` gives the body of
  `FormationSourceClaim p` (`Claims/Finality.lean`). No Export of this
  branch imports `Claims.Finality`, so the statement is the unfolded body.

The `FormationClaim` and `FormationSourceClaim` fields stay OPEN until
`hFrozen` is proved.

The F4 statement fix is part of this landing. It adds
`FormationRootReachable` and the `proposerRootReachable` fields of
`FormationPrem` and `HealedSourcePrem` (at `r * p.R`). Without this clause,
the old `FormationClaim` and `FormationSourceClaim` were false under those
premises; the old premises were satisfiable. `docs/PCSA-API.md` is
regenerated.

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
- Late gate counts: `pcsa_formation_gate_counts`
  (`FormationGateCounts`), from the exact honest HEADs. `H` is the number
  of honest HEAD seats awake at `v_s`.
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

## OPEN input: the frozen raw relay

The binder is `hFrozen`, with type `FormationFrozenRawOpen p src dst s` at
the honest proposer read at `t_s` (`src`) and each honest voter awake at
`v_s` (`dst`): a HEAD `⟨seat (s-1) i, head r⟩` in the voter pool with a
stamp before `z_{s-1}` is in the proposer raw list (`proposerVotes src.st
s`), or seat `i` is capped there.

`pcsa_formation_preFreeze_inputs_of_frozen` derives all pre-freeze inputs
from it.

Plan: this is the Clean `pcsa_frozen_input_in_proposer` at slot `s - 1`,
with the windowed delivery `max t z_{s-1} + Δ` in place of
`HealthyPrefixDeliveryBy`. Its only delivery step is the relay of the
accepted HEAD (`pcsa_head_relay_late_or_cap`), with deadline `t_s` in place
of `t + Δ`. The windowed HEAD relay of the Clean restart work supplies it.
