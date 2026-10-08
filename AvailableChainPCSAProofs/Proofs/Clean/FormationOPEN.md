# Formation (C7): OPEN inputs

This file lists the inputs that C7 `FormationClaim` still needs. The
Formation writer owns this file and the `Clean/Formation*` modules.
`Clean/OPEN.md` covers the rest of the Clean lane.

## Status

`Assembly/Formation.lean` proves the claims under one named OPEN input,
`hRetained`: a producer of the five retained HEAD facts at every Formation
context (the same binders as `FormationClaim`):

- `pcsa_formation_of_open`: `hRetained` gives `FormationClaim p`.
- `pcsa_formation_source_of_open`: `hRetained` gives the body of
  `FormationSourceClaim p` (`Claims/Finality.lean`). No Export of this
  branch imports `Claims.Finality`, so the statement is the unfolded body.

The `FormationClaim` and `FormationSourceClaim` fields stay OPEN until
`hRetained` is proved.

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

## OPEN input: the five retained HEAD facts

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
