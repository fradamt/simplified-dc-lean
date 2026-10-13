# Available chain / FG-SA

This repository is a Lean 4 formalization of FG-SA (“Goldilocks”): the SA available chain with a finality gadget, in a sleepy model with committees. It includes the protocol model, claim statements, proofs, and generic supporting libraries; it does not include a client implementation.

The headline theorem is `AvailableChain.FGSA.Run.fgsaClaims : FGSAClaims p`, assembled in [AvailableChainFGSAProofs/Proofs/Assembly/Root.lean](AvailableChainFGSAProofs/Proofs/Assembly/Root.lean). Its claim types retain their regime premises; in particular, the output contract treats recovery as a premise. The complete field definitions are in [AvailableChainFGSAClaims/FGSAClaims.lean](AvailableChainFGSAClaims/FGSAClaims.lean):

- Inherited safety fields: `carrier`, `chainCertificates`, `store`, `activeView`, `leaseOrigins`, `reconcile`, `outputNesting`, `frame`, `clientSafety`, `clientSafetyBase`, `sourceDisciplineBase`, `sourceDiscipline`, `sameLabel`, `releaseStore`, `release`, `headReachesLo`, `cleanCut`, `cleanHistory`, `cleanPrefixTruncation`, `cleanSafety`.
- Additional fields: `finality`, `finalizedSafety`, `finalLock`, `outageCompat`, `fastP1`, `slowP1`, `exactProposal`, `cleanInclusionPostGate`, `cleanInclusion`, `firstFinalityRecFE`, `firstFinalityRecF4`, `finalityLivenessGSTRecFE`, `finalityLivenessGSTRecF4`, `proposalFinalGSTRecFE`, `proposalFinalGSTRecF4`, `aboveFrontierGSTRecFE`, `aboveFrontierGSTRecF4`, `availableGST`, `availableGrowthGST`, `cleanGrowth`, `weakContinuationLive`.
- The `finality` record contains `accountable`, `agreement`, `runAccountable`, `runAgreement`, `eventPrefixAgreement`, `faultCountSlashableBound`, `finalizedMonotone`, `honestNeverSlashed`.

The earlier model decisions in [docs/CONTRACT.md §1](docs/CONTRACT.md#1-decisions) specify committees containing all `n` unit-weight seats, assigned to validators by a fresh hidden bijection per label, with claims quantified over every assignment rather than sampling error. Corruption is static: the faulty set is fixed for a run. Asleep nodes receive and process but do not emit; joining means listening for a while, with no state transfer in that contract model. Sleepy regimes start at `GST = t₀ = 0`; a later global stabilization time requires recovery. FG-SA's claim-specific assumptions are given by the linked claim types and their imported statements.

The PC-SA libraries (`AvailableChainPCSA`, `AvailableChainPCSARun`, `AvailableChainPCSAClaims`, `AvailableChainPCSAProofs`) are an older variant with preconfirmations. They are not ported to the current sleep model, the checks skip them, and they are not part of the FG-SA result; see [docs/PCSA-DISABLED.md](docs/PCSA-DISABLED.md). Earlier or auxiliary developments remain: [docs/SA-STATUS.md](docs/SA-STATUS.md) records the SA contract and fast P1 as proved; [docs/SAPC-STATUS.md](docs/SAPC-STATUS.md) records the SA-PC base and strong bundles as proved; [docs/GRIDCO-STATUS.md](docs/GRIDCO-STATUS.md) records all Grid CO contract claims as proved. SAPC is distinct from the PC-SA libraries. For LStar, [docs/MAP.md](docs/MAP.md#l-instance-definitions-and-statement-no-claim-proofs) records model and contract definitions, hook proofs and smoke tests, with the general P1 proof pending. The FG-SA blueprint's partial/open items are recorded separately in [docs/FGSA-BLUEPRINT-LEAN.json](docs/FGSA-BLUEPRINT-LEAN.json) and [docs/FGSA-BLUEPRINT-OPEN.md](docs/FGSA-BLUEPRINT-OPEN.md); the aggregate theorem is not a claim that every blueprint item is closed.

## Repository map

Each library is a top-level folder `AvailableChainX/` with a root file `AvailableChainX.lean`. The folders are not grouped yet; a regrouping into five folders is planned. Until then, read them in these groups.

```text
┌──────────────────────┬──────────────────────────────────────────────────────────────┐
│ Group                │ Libraries (prefix AvailableChain)                            │
├──────────────────────┼──────────────────────────────────────────────────────────────┤
│ FG-SA (start here)   │ FGSA (model, statements), FGSARun (run-level statements),    │
│                      │ FGSAClaims (the claims), FGSAProofs (the proofs; root        │
│                      │ theorem in Proofs/Assembly/Root.lean), FGSAInhabit           │
│                      │ (non-vacuity witnesses)                                      │
│ Generic libraries    │ Generic, Kit, KitV2, KitFG (available-chain and finality     │
│                      │ building blocks), FGCompose (the finality-gadget results in  │
│                      │ a protocol-independent form)                                 │
│ Engine               │ EngineV2 (the execution model with sleep and duties), Model, │
│                      │ Statements, Witnesses, Framework, Registry                   │
│ Older protocols      │ SA, SAPC, GridCO, LStar, SimplexFG                           │
│ PC-SA (not ported)   │ PCSA, PCSARun, PCSAClaims, PCSAProofs                        │
└──────────────────────┴──────────────────────────────────────────────────────────────┘
```

Other folders: `scripts/` holds the checkers and gates named below; `docs/` holds the contract ([docs/CONTRACT.md](docs/CONTRACT.md)), the architecture map ([docs/ARCHITECTURE.md](docs/ARCHITECTURE.md)), the API manifests ([docs/FGSA-API.md](docs/FGSA-API.md)) and internal working notes.

A short reading path for FG-SA: [AvailableChainFGSAClaims/FGSAClaims.lean](AvailableChainFGSAClaims/FGSAClaims.lean) (what is claimed), then [AvailableChainFGSAProofs/Proofs/Assembly/Root.lean](AvailableChainFGSAProofs/Proofs/Assembly/Root.lean) (how the claims are assembled), then the model under [AvailableChainFGSA/](AvailableChainFGSA/).

## Build and checks

Use the version pinned in [lean-toolchain](lean-toolchain) (`leanprover/lean4:v4.34.1`):

```sh
lake exe cache get
lake build
lake build --wfail @ AvailableChainFGSAClaimsTests AvailableChainFGSAProofsTests AvailableChainFGSAInhabitTests
```

After building, the main checks are:

```sh
bash scripts/precheck.sh .
python3 -B scripts/check-gly-rules.py
python3 -B scripts/check-layers.py
python3 -B scripts/check-module-headers.py
bash scripts/shake-report.sh --fail-on-new
lake build AvailableChainCheckSupport
LEAN_CAP_GB=12 lake env lean --run scripts/CheckProofEqns.lean --baseline scripts/baselines/check-proof-eqns.txt
LEAN_CAP_GB=12 python3 -B scripts/check-proof-coverage.py
python3 -B scripts/check-fg-finality-coverage.py
python3 -B scripts/check-fg-compose-source.py
python3 -B scripts/api-snapshot.py --scope compose --check
LEAN_CAP_GB=12 bash scripts/check-fg-compose.sh
LEAN_CAP_GB=12 bash scripts/check-fgsa-claims.sh
```

Precheck enforces source policy before compilation. The GLY, layer and header scripts check generic-library rules, import boundaries and module headers. Shake reports unused imports and rejects new removal suggestions. `CheckProofEqns.lean` checks equation exports and statement-definition backstops; the coverage scripts check owning axiom-audit inventories and public finality-safety declarations. The Compose source check enforces its source/export policy, the API check compares the compiled snapshot, and the two shell checks build and audit their declared scopes and run controls. These are mechanical checks of their stated scopes, not proofs of blueprint-to-Lean semantic equivalence (see [scripts/check-fgsa-blueprint.py](scripts/check-fgsa-blueprint.py)).

Run the existing axiom audit, which includes `#print axioms AvailableChain.FGSA.Run.fgsaClaims` in [AvailableChainFGSAProofs/Tests/Axioms.lean](AvailableChainFGSAProofs/Tests/Axioms.lean):

```sh
LEAN_CAP_GB=12 lake env lean AvailableChainFGSAProofs/Tests/Axioms.lean
```

The licence is [CC0 1.0 Universal](LICENSE).
