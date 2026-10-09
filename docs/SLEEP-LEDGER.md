# Sleep premise ledger

Before G-S0, each package records one row per internal theorem that uses a proposed
premise. Use packet row IDs from plan §5.1. At G-S0, change each status to approved
or rework. P-Da keeps this file as a record.

```text
┌──────────────┬──────────────┬─────────────┬────────────────────┐
│ Theorem name │ File         │ Packet rows │ Status             │
├──────────────┼──────────────┼─────────────┼────────────────────┤
└──────────────┴──────────────┴─────────────┴────────────────────┘
```

## W2a — approved packet, 2026-10-10

Approval: `sleep-packet-approved.md`, P1–P24, G-S0 passed.
Each row below is approved. No additional premise or public claim text is proposed.

- `Reachable.restart` — `P24`, approved.
  `AvailableChainFGSA/Statements/Invariants.lean`.
  Repair: old reset → prior reachable wipe.

- `joinedNow; joinedAtTime` — `P24`, approved.
  `AvailableChainFGSA/Model/Store.lean`.
  Repair: inclusive previous slot, integer subtraction.

- `wipe; acRestart; reachable_acRestart` — `P24`, approved.
  `AvailableChainFGSA/Model/Restart.lean`.
  `AvailableChainFGSA/Proofs/Restart.lean`.
  Repair: durable fields kept, HEAD-only replay.

- `gateStep_fresh` — `P24`, approved.
  `AvailableChainFGSA/Proofs/Fields.lean`.
  Repair: add joinedNow at the gate input.

- `clockPre_eq` — `P24`, approved.
  `AvailableChainFGSA/Proofs/ActView.lean`.
  Repair: release gains the tick-time join guard.

- `clock_eq_saClock_offGate` — `P24`, approved.
  `AvailableChainFGSA/Proofs/ActView.lean`.
  Repair: add joinedAtTime at t.

- `clock_eq_saClockFrom_gate; gate'` — `P24`, approved.
  `AvailableChainFGSA/Proofs/ActView.lean`.
  Repair: add joinedAtTime at t.

- `storeInvariant; metadataInvariant` — `P24`, approved.
  `AvailableChainFGSA/Proofs/StoreInv.lean`.
  `AvailableChainFGSA/Proofs/Metadata.lean`.
  Repair: prior invariant supplies retained content.

- `rowsValidStored_reachable; stored_r6wW` — `P24`, approved.
  `AvailableChainFGSA/Proofs/Metadata.lean`.
  `AvailableChainFGSA/WindowAdmissionInvariant.lean`.
  Repair: retained rows keep their validity.

- `outputNesting_stored; base_headDomain_none` — `P24`, approved.
  `AvailableChainFGSA/Proofs/Nesting.lean`.
  `AvailableChainFGSA/Proofs/HeadDomain.lean`.
  Repair: F/S kept; headDomain cleared.

- `storeBundleInvariant` — `P24`, approved.
  `AvailableChainFGSA/Proofs/StoreBundle.lean`.
  Repair: all stored target bounds survive any w.

Constructor record: remove `AvailableChain.FGSA.Reachable.reset`;
add `AvailableChain.FGSA.Reachable.restart`. D0e-a must use the new spelling.
Run callers remain with W2b/W3; other owners are in `scripts/dev-pkg/W2a.txt`.
