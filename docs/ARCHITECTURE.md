# FG-SA architecture map

_Shared map for three sessions. Created 2026-09-29 from DC-simplify's
draft 1. One screen per section; detail goes in the linked documents.
Update it when a module, an interface, a constraint or the milestone order
changes, and tell the other sessions._

```text
┌────────────────┬──────────────────────────────────┬─────────────────────┐
│ Session        │ Owns                             │ Map sections        │
├────────────────┼──────────────────────────────────┼─────────────────────┤
│ DC-simplify    │ spec, blueprint, research        │ §1–§2, §6–§7        │
│ (tip-stability)│                                  │                     │
│ lean-framework │ engine, framework, I9, 2a/2b/2c, │ §3–§4               │
│                │ 1c                               │                     │
│ fgsa-lean      │ T7/T1, F0–F6 (FG-SA claims in    │ (reports to both)   │
│                │ Lean); docs/FG-COMPOSITION.md    │                     │
│                │ (registry, pins)                 │                     │
│ all            │ milestones, links                │ §5, §8 (shared)     │
└────────────────┴──────────────────────────────────┴─────────────────────┘
```

## 1. Goal and priority

- Target: **FG-SA fully specified and verified** (user, 2026-09-29).
  FG-SA = the plain SA available chain (AC) + the DC finality gadget (FG),
  with the FJ root rule.
- Order: FG-SA needs first, then SA (its base), then the rest. Grid CO,
  SA-PC, L* and SimplexFG work is DEFERRED, not deleted; existing code and
  registry entries stay and stay green (user clarification, 2026-09-29).
- End state: the spec is frozen, and every main blueprint claim is a
  checked Lean theorem about FG-SA runs.

## 2. Protocol architecture (paper)

```text
┌──────────────────────────────────────────────────────────────────────┐
│ Substrate: cumulative tree Σ.T (fixed σ, stamps), admission F ⪯ B,   │
│ receipt premise                                                      │
├───────────────────────────────┬──────────────────────────────────────┤
│ AC = plain SA                 │ FG = DC finality gadget              │
│ votes, leases, fast/slow      │ rows, chain states σ, F, J, h_max,   │
│ lock, genuine results,        │ window W of ≤ K_W justifications,    │
│ available output              │ finality acceptance, Λ record        │
├───────────────────────────────┴──────────────────────────────────────┤
│ Composition: joint selection functions                               │
│ live_root · HEAD eligibility · C_fg · proposer head · finality head  │
│ (triple (h_j, J, h_F); finality_pair is FG's client function on it)  │
└──────────────────────────────────────────────────────────────────────┘
 AC → joint: X_r and leases; HEAD votes in the substrate pools (T-VOTE);
          AC services to the joint selections (H2′, HEAD clauses of H2.A
          and H3). S enters proofs only (T-START, T-SMONO).
 joint → FG: C_fg; the finality-head triple, also with no source; the
          carrier chain (honest proposals from slot s+2 have K ⪯ parent
          and carry rows, T-ROWS).
 FG → joint/AC (frame): FJ root Z + contest band; floor lo also relaxes
          AC eligibility; F for act(Σ), admission, reconcile, and the
          gate walk from Σ.F.
```

- Minimal AC→FG channel (blueprint 01 §1, r212/r212b): source
  candidates/C_fg and the carrier chain. The head selections read the
  substrate vote pools directly (proposer: previous-slot pool; finality
  head: current-slot pool), as `propose_block` and `get_fg_vote` do. So
  "HEAD votes are not a third AC→FG stream" holds for this partition
  only: the finality head reads HEAD votes through the joint function.

- The glue goes both ways by design (user): AC creates targets for FG; FG
  feeds back restrictions on the tree. Modular-spec study
  (`tip-stability/codex/scratch/modular-spec-study.md`): the spec splits
  into substrate, FG module, AC module and a composition section; no
  protocol change is needed.
- Proofs compose by induction over the trace index, as in DC. Clean and
  P1 use their stated channel properties; 6Δ inclusion also uses the
  proposer's full-tree walk (a joint function). The finality kernel is a
  composition theorem: it uses the healing witness, source/carrier facts,
  H2′, the HEAD clause of H2.A, H3/H4, the composition services
  T-START/T-SMONO/T-EXACT/T-VOTE/T-WALK, T-ROWS with matching-state bit
  persistence, and FG/substrate facts. The frozen finality claim set is
  the recurrence route only: FF5–FF7 from `HEALING_INPUT` through the
  FGoodE_W/Tail_W kernels. QF2/QF4 (Qual/Skip routes, Rec_sT/Rec_skipT,
  B_Q/B_skip) are open extensions outside the freeze (user, 2026-10-01).
  Healing supplies one common witness tuple (r_G, u₀, M, r*, s*, C*)
  through H.22, and μ = μ(run, GST) as a function of the run, not a
  witness field; H-time supplies the GST bound.
- Lean consequence: v2 `Isolation` cannot express the channels
  (`fgsaIso` puts the whole FG store in base), so F0 adds channel files
  in the FG-SA claims library (`Channels`, `ChannelProps`, `Compose`).
- Transport: two delivery families (user, 2026-10-01). Blocks, HEAD/SA
  votes and their relays use Δ; gossiped FG rows and their relays use
  Δ_F ≥ Δ; a row carried in a block arrives with the block (Δ). Rows
  travel packed in the block body (I9 `packBody`, `rowsOk` in
  `wellFormed`); the block root commits to them. Carriage uses the carrier
  offset κ. In Lean, Δ_F is a regime parameter bound by the family-indexed
  delivery premise (`PartialSynchronyBy`), not an `Env` field.
- FG-SA finality is an FG-SA-specific WINDOW fold over the unchanged
  SimplexFG fold (user, 2026-10-01): FG-SA no longer uses SimplexFG's
  latest-only finality fold. The window keeps ≤ K_W justifications
  (K_W ≥ 2); target/progress steps are unchanged, and a height bridge
  (blueprint 01 §3.1a) transfers height facts between the two folds.
- Design rules (user): stay close to DC and justify every divergence;
  a bounded window of ≤ K_W justifications (K_W ≥ 2), not the latest
  certificate only; outputs nest by construction; FG never vetoes
  blocks; timeliness only on sending.
- Authority (window + Δ_F, final 2026-10-01; SHA-256 prefixes):
  `spec/fgsa-protocol.tex` 59bb0dda; blueprint 00 e4a145dc, 01 7a160200
  (§3.1 window invariants, §3.1a height bridge), 21 eaef7cfe, 22 8b7eaffe,
  23 7332c7a0. Previous authority: `spec/fgsa-protocol.tex` (adopted c1ea1db0, 2026-09-29;
  replaces 4e85ff34 with two changes: the pre-GST delivery clause of the
  partial-synchrony premise (OD6, as v2 `PartialSynchrony`) and the
  healing-interface names aligned with the blueprint;
  `spec/archive/CHANGES-4e85ff34-to-c1ea1db0.md`; 4e85ff34 made the SA
  walk start at Σ.F). Blueprint line citations use the 4e85ff34 numbering.
  Proofs: `blueprint/` (00 outline; 01 foundations; 02
  Clean; 03 P1 and inclusion; 21 healing with `HEALING_INPUT`; 22
  finality).

- ROOT-DIGEST-2 uses recursive `NamedProposal` values. Each value keeps its exact named
  parent, body, ordered signed rows, raw HEAD list, and support list. `Block` and `FGBlock`
  remain geometric projections. Admission requires the exact named parent in `namedBodies`,
  rechecks the body and digest, and keeps the incoming value. Missing parents are dependencies.
- FG-SA uses root-mode GridCO/SA. HEAD wires, vote keys, stamps, counts, and equivocation
  use root identifiers. A read resolves one identifier in the cumulative store domain. No
  body or multiple distinct bodies leave the vote unresolved. Active views keep that domain;
  filtering the tree cannot remove ambiguity. Deferred protocols keep legacy block mode.
- The named run scope contains directly delivered proposals, honest prefix-held proposals,
  and their named ancestors. It includes rejected delivered bodies. Equal roots in this scope
  identify full recursive content. HEAD-only names and emitted-only tips add no scope seeds.
  Genesis enters through a held body or ancestry. `Base₂` keeps one idealization field.
- Duty `ACReads` is mode-indexed. FG-SA uses root-mode reads; legacy interfaces remain.
  The [ROOT-DIGEST-2 option-3 exception](FGSA-API.md#root-digest-2-option-3-exception)
  records the representation and frozen statement changes. The closed `fgsaClaims` type,
  claim fields, bounds, and prior exceptions remain.
- Integration order: compile and sign the W1 model/interface checkpoint; then run W2 proof
  work and W3 fixture/document work in separate trees. After W2 lands, the owner runs W3b
  for manifests, exact-hash allow data, catalog lock records, paired costs, and all gates.
  The lead applies the separate spec/blueprint patch. Historical pins stay unchanged.

## 3. Lean architecture (available-chain)

Layers (design §1). L0, L1, LM, L2 and L3 import nothing from L4–L6.

```text
┌────┬────────────┬──────────────────────────────────────────────────────┐
│ L  │ Layer      │ Lean libraries                                       │
├────┼────────────┼──────────────────────────────────────────────────────┤
│ L0 │ Engine     │ AvailableChainModel (objects; Block with stored      │
│    │            │ roots after ROOT-DIGEST; v1 Generic engine);         │
│    │            │ AvailableChainEngineV2/Engine (v2, from 2a)          │
│ L1 │ Conditions │ AvailableChainStatements (v1); EngineV2/Conditions,  │
│    │            │ EngineV2/Laws (Isolation, HooksSound, OutputsFactor) │
│ LM │ Modules    │ AvailableChainSimplexFG (FG store, chain states,     │
│    │            │ client, evidence)                                    │
│ L2 │ Facets     │ Framework/Facets; v2 Interface (EngineV2)            │
│ L3 │ Catalog    │ AvailableChainFramework (Claim, Profile, Catalog/*)  │
│ L4 │ Instances  │ GridCO (policy-generic; SA = GridCO at               │
│    │            │ slowLeasePolicy), SA, FGSA, SAPC, LStar;             │
│    │            │ Registry/Instances                                   │
│ L5 │ Kits       │ AvailableChainKit (v1), AvailableChainKitV2,         │
│    │            │ AvailableChainKitFG (FG proofs, Pins)                │
│ L6 │ Registry   │ AvailableChainRegistry, catalog.lock, MATRIX.md      │
└────┴────────────┴──────────────────────────────────────────────────────┘
```

A0 step 2 adds `AvailableChainGeneric`, a default library with separate
Statements and Proofs modules in Pure, V2 and AC. Statements expose definitions
and `f_def` lemmas; Proofs have a public section without `@[expose]`.
`AvailableChainGeneric.lean` imports the 21 modules below in order. The library
glob also builds Tests; the facade does not import Tests. Paths below are
relative to `AvailableChainGeneric/` and omit `.lean`.

```text
┌──────────────────────────┬──────────────────────────────────────────────┐
│ Module                   │ Role                                         │
├──────────────────────────┼──────────────────────────────────────────────┤
│ Statements/Pure/Quorum   │ qF; FaultQ, FaultX and Batch bounds          │
│ Statements/Pure/FirstBad │ AGRule, FirstFailure, WindowRule, RetroAt    │
│ Statements/Pure/Schedule │ Patterns, recurrence and window definitions  │
│ Statements/Pure/Walk     │ Suffix premises and E-4 walk statements      │
│ Statements/Pure/Props    │ CompatOn/At, MonoOn, BelowOn, ServedOn       │
│ Statements/Pure/PCQuorum │ qN = ⌈3n/4⌉, qA = ⌈n/2⌉; PC count contracts  │
│ Statements/Pure/PCRank   │ PC record, Formed, rank, pickPC, preferPC    │
│ Statements/Pure/PCFloor  │ pcFloor output floor and its contracts       │
│ Statements/V2/Reads      │ Run indices, pubFloor, HonestSlot, Pending   │
│                          │ E-9 time/index statement PROVED              │
│ Statements/V2/Counts     │ faulty and awakeHonest                       │
│ Statements/V2/Obs        │ Time observations with optional proposals    │
│ Statements/V2/Interface  │ FinalityInterface extends the v2 interface   │
│ Statements/V2/Receipt    │ DeliveryWithin; E-9 statements PROVED        │
│ Statements/V2/Regimes    │ Regime cores, LabelSync, LabelFacts, SeedAt  │
│ Statements/V2/Duty/      │ PC companion over Duty runs: DC mirrors      │
│   PCCompanion            │ (InBy, PersistsFrom, IncludedFrom, …),       │
│                          │ PCInterface, PCArmedRegime, PCIncluded,      │
│                          │ PCCompanion (statements only)                │
│ Statements/AC/Reads      │ ACReads, ACLaws, gate and reconcile reads    │
│ Proofs/Pure/FirstBad     │ Strong induction for the FirstBad rules      │
│ Proofs/Pure/Schedule     │ Pattern, window and recurrence facts         │
│ Proofs/Pure/BlockOrder   │ Block order, compatibility and path facts    │
│ Proofs/Pure/PCQuorum     │ qN/qA intersection, honest seat, uniqueness  │
│ Proofs/Pure/PCRank       │ Rank preorder; preferPC total, monotone,     │
│                          │ idempotent; folds; same-slot PC target       │
│ Proofs/Pure/PCFloor      │ pcFloor cases, target bound, nest, monotone  │
│ Proofs/V2/Fields         │ ownRecord_fold_restart                       │
│ Proofs/V2/Reads          │ E-9 time/index bridge                        │
│ Proofs/V2/Induction      │ Invariant and interval lifts; kept_from_seed │
│ Proofs/V2/Receipt        │ E-9 proofs; two DeliveryWithin producers     │
│ Proofs/V2/Regimes        │ Six LabelSync and LabelFacts facts           │
│ Proofs/AC/Output         │ output_step_of_restartFree                   │
│ Tests/Axioms             │ Kernel axiom audit of every public theorem   │
│ Tests/FoldRestart        │ Two special cases of the restart fold        │
│ Tests/Schedule           │ Window-bound and recurrence examples         │
└──────────────────────────┴──────────────────────────────────────────────┘
```

- PC-SA PC layer (2026-10-05; `pcsa-decisions.md`, 3n/4 version and R-g):
  `PCQuorum` (thresholds `qN`, `qA`; two `qN` sets share `qA` seats; honest
  seat in a `qA` set; one block per slot with a `qN` exact-HEAD set),
  `PCRank` (abstract PC record with acker seats; rank by slot, then a tie
  key; `preferPC` keeps the rank-maximal PC; two formed PCs of one slot
  have one target) and `PCFloor` (available output = `S` if the PC target
  is `⪯ S`, else the target; target bound, nesting below the output,
  monotonicity). Import constraint: Pure layer, closure Mathlib +
  `AvailableChainModel.Objects.*` + Generic Pure only (GLY F-4, F-12); no
  V2, AC, GridCO or FG-SA import. Consumer: the PCSA family.
- PC persistence companion (2026-10-05; `pcsa34-r3.md` §5.4, App. B):
  `Statements/V2/Duty/PCCompanion` over Duty runs, modelled on the frozen v1
  `StrongClaims` (`AvailableChainStatements/Strong`, unchanged). `PCArmedRegime`
  is `StrongArmedRegime` with lag 3Δ, `a < q_A n`, `HealthyPrefixDeliveryBy`
  from the run start to `b₀` (ARM-healthy) and no restart; `PCIncludedRegime`
  has full participation and `4a ≤ n`. Both take a label family `Fam` with
  `CStar` and `n` seats per label (validator count = seat count, as `cstar` in
  FG-SA `Base₂`) and `delayPos` (the instance pins `delayOf`). Import constraint: S/V2 rule
  (GLY-SV2): Generic Pure and V2 statements, EngineV2 Engine/Conditions/Laws.
  PC-SA does not instantiate this companion: `PCArmedRegime` and
  `PCIncludedRegime` do not bound the faulty FG seats, so an unrestricted
  instance is false. The PC-SA-native forms replace it: stage 1
  `ArmHealthyClaim`, `StrongIncludedClaim` (over every FG mode with
  `StageOneFrame`; the AC-only instance `pcsaAC` discharges it by
  `AcOnlyFrameClaim`), stage 2 `ArmHealthyStageTwoClaim`,
  `StrongIncludedStageTwoClaim` (`Clean₂`, `a ≤ f`, no frame premise) in
  `AvailableChainPCSAClaims`.
- PC-SA shared proof layer (2026-10-07; stage 1 and stage 2). Paths are
  under `AvailableChainPCSAProofs/Proofs/`. `Shared/` holds lane-neutral run
  and store facts; it imports only `Foundations`, `Shared` and the allowed
  upstream layers, never a lane. Stage 1 moves `Certificates`,
  `HeadSupport`, `RunEvidence` and `StoreEvidence` from `PC/` to `Shared/`;
  the four `PC/` modules stay as compatibility shims that import the
  `Shared/` module, so open lanes keep their `PC/` imports. Stage 1 also
  adds the PC relay layer: `CollectClosed`, `StageStore` (the stage-1 store
  invariant; it keeps the names `OutageStore` and `pcsa_outage_*` from the
  move), `StageRun`, `RelayStore`, `RelayRun` (whole-PC relay and
  `pcsa_keyHeld_accepted`) and `PCViews` (best-PC rank, view target,
  installed-PC acceptance, PC retention). Stage 2 adds `Proposal` (the honest
  proposal is built at the proposer post-clock state: parent and `N.pc`),
  `Clock` (`pcsaClock`, `pcsa_clock_now`, `pcsa_process_now`), the body
  layer `BodyScope`, `TreeReceipt`, `BodyPersistence`, `BodyAdmission` and
  `BodyReceipt` (body origin, and `pcsa_body_relay_admitted`: a relayed
  accepted body is admitted by a deadline `d`, given the relay step to `d`)
  and `BodyRelay` (the same over a `DeliveryWithinOn` premise with the lane's
  deadline map). Stage 2b adds `HonestProposal`: the rows of an honest
  proposal pass R6, so no receiver excludes it; under `DeliveryWithinOn` each
  honest receiver holds its wire and a valid carried PC
  (`pcsa_honest_proposal_receipt`; `pcsa_honest_proposal_from_vote` from
  `v_s`, and `pcsa_honest_proposal_early` at the early read).
  Shared keeps the `HealthyPrefixDeliveryBy` wrapper
  (`pcsa_body_relay_before_deadline` in `Shared/BodyReceipt`, through
  `Shared/Relay`), used by Outage and Clean. The other lanes supply the relay
  step from their own delivery premises through `BodyRelay` (Recovery: the
  RECOVERY deadline `max t z_{s-1} + Δ`; Formation: `FormationPrem.delivery`).
  Stage 3 adds `VoterView`: every stored slot-`s` proposal is the honest one, so
  its PC is the only carried PC; every frozen PC of slot `s - 1` has a
  whole-PC acceptance by `z_{s-1}`, so under the deadline `max t z_{s-1} + Δ`
  its key is held at the proposer before `t_s`, and every honest voter view at
  `v_s` has the proposer target (`pcsa_commonView_of_delivery`, the F3 field of
  `FormationPrem`). These lemmas are the Formation lane's `pcsa_formation_*`
  lemmas with smaller premises, without the lane prefix (Shared carries no lane
  names); Formation drops its copies when it switches.
  The CI restart (2026-10-08) adds `CleanWindow`, the delivery window of the
  clean induction from a label `j₀`. `StrictFrom E rho T₀ cut` is non-row
  delivery with a deadline `dl t` that is `t + Δ` from the floor `T₀` and at
  most `max t T₀ + Δ` before it. Converters: `pcsa_strictFrom_of_healthy`
  (`HealthyPrefixDeliveryBy`, any `T₀`), `pcsa_strictFrom_of_sync`
  (`PartialSynchronyBy`, `T₀ = t_GST`) and `pcsa_strictFrom_of_within` (a
  `DeliveryWithinOn` premise with deadline `max t T₀ + Δ`, as
  `FormationPrem.delivery` with `T₀ = z_{s-1}`). `CleanWindow E rho j₀ T₀ b₀`
  adds `Base₂`, the cut, `T₀ ≤ t_{j₀}` and `a < h_j` at each label `j ≥ j₀` with
  `e_j ≤ b₀`; `Clean₂` gives it with `j₀ = 0`, `T₀ = 0`, and the RECOVERY
  components give it with `T₀ = t_GST`. The `_win` lemmas of `Shared/Relay`,
  `Shared/BodyReceipt` and the Clean lane take `StrictFrom` (or `CleanWindow`);
  the old `HealthyPrefixDeliveryBy` names are wrappers with unchanged types.
  `Clean/StampFrom.pcsa_clean_honestProposal_stamped_from` proves pre-freeze
  stamping in this window from equal honest HEADs and the awake N quorum.
  It needs `T₀ ≤ z_s` for the proposal at `s + 1`. It does not use
  `CleanRestartSeed`; recovery can use its conclusion to supply a seed stamp.
- PC-SA CI restart from a label `a` (2026-10-08; steps 4a, 4b, 5a and K2).
  The clean induction restarts at a seed label `a > 0` with seed block `A`.
  Shared modules:
  `Shared/SlotOrder` holds the slot-order facts that were in
  `Recovery/LockWindow` (`RecoverySlotOrdered`, `StoreSlotOrdered`,
  `ResultsSlotBound`, `pcsa_reachable_slot_order`, `pcsa_stored_strict_slots`,
  `pcsa_result_prefix_slot`, `pcsa_saved_result_slot`); `Recovery/LockWindow`
  keeps the four `recovery_` names as one-line wrappers with unchanged types.
  `Shared/LockRankSafe` is the store-level lock rank invariant
  (`pcsa_lock_rank_compatible`, `pcsa_live_lock_rank_compatible`), copied from
  `Recovery/LockRank` on `pcsa-recov-long`; the Recovery names become wrappers
  when that branch lands. `Shared/StampKeep` keeps PC stamps after their
  install (root uniqueness). `Shared/RestartSeed` defines the positive seed
  `CleanRestartSeed a A` (`0 < a`, `A.slot = a`, a PC `(a, A)` stamped before
  `z_a` at every honest node, every honest HEAD and proposal of label `a` is
  `A`, every result of label `a` is `A`, every lock from `z_a` to the input of
  gate `a` is `⪯ A` (`locksFromFreeze`), and `ArmConcl a A (a + 1)`), and K1:
  from `z_a`, the proposer PC, the voter snapshot and the gate rank have slot
  `≥ a`. `Shared/RestartSuffix` defines the output interface
  `RecoveredSuffixInvariant s P cut` with eight fields: `resultsChain`,
  `pcChain`, `pcResults`, `selected`, `recordOrigin`, `recordMono`,
  `gateAdvance` and `honestGate`.
  Clean modules: `LockFromCut` (K3: a lock after a cut index was stored at the
  cut or written by a later own gate), `RestartRecord` (K4: after gate `a`
  the record is `A`), `RestartRoots` (the root at `v_{a+1}` is `A`; the root
  sources and ack dissemination from `a`), `RestartState` (the seven-field
  state `CleanStateFrom a j`: results, HEADs above results, equal HEADs,
  PC/result pairs, roots, ack/HEAD and ack/result coverage, every label
  quantifier from `a`), `RestartKernels` (the joint-step kernels from `a`),
  `RestartStep` (the joint step and `pcsa_restart_state_from`, for every
  `j ≥ a` with `d_j ≤ cut`), `RestartOutputs` (record history from gate `a`
  and `pcsa_restart_suffix_invariant`, over `CleanWindow E rho a T₀ cut`,
  `StageOneFrame`, `FaultsBelowQA` and the seed) and `RestartLocks` (K2:
  `pcsa_restart_locks_from_freeze` proves `locksFromFreeze`; every stored
  lock rank comes from an earlier own gate below `a`, so the held seed PC
  ranks above it).
  K2 and K4 are in Clean: they use Clean record and lock provenance, and K2
  needs no Recovery lemma. `pcsa_cleanRestartSeed_mk` builds the seed from
  `0 < a`, `A.slot = a`, the stamp, the HEADs, the proposal, the results,
  `ArmConcl` and `z_a ≤ horizon`.
  Open boundary: the Recovery assembly that supplies the seed and the window.
  The seed stamp comes from `pcsa_clean_honestProposal_stamped_from` at
  `s = a - 1`, with `T₀ = t_GST ≤ z_{a-1}`. The Clean, Shared and
  Recovery copies of the lock and record event inductions become one Shared
  provenance core after this chain lands.
- PC-SA Formation (C7; 2026-10-08). Paths are under
  `AvailableChainPCSAProofs/Proofs/`. The Formation proofs are the
  `Clean/Formation*` modules; `Clean/FormationExport` collects them. It is an
  ordinary Clean module, not a lane Export. The layer checker grants one exact
  edge for it, `Assembly.Formation → Clean.FormationExport`
  (`scripts/check-layers.py`); no other module may import it across lanes.
  `Shared/FormationWindow` holds the pre-freeze interface
  `FormationPreFreezePrem`: `FormationPrem` with the delivery cut at
  `freezeTime s` and the Formation deadline `max t z_{s-1} + Δ`.
  `FormationPrem` carries the F4 clause `FormationRootReachable` (the
  proposer walk from the carried PC target, or `Z`, reaches `liveRoot`);
  `HealedSourcePrem` carries the same clause at `r * p.R`. Parts 1–4 of the
  conclusion follow from `FormationPreFreezeInputs`; the gate counts
  (`Clean/FormationGateCounts`) give part 5. `Assembly/Formation` proves
  `FormationClaim` (`pcsa_formationClaim`) and `FormationSourceClaim`
  (`pcsa_formationSourceClaim`, through `Finality/Export`) with no open input.
  `Clean/FormationRetainedTree` and `Clean/FormationRetainedBack` prove the
  five retained HEAD facts; `Clean/FormationFrozenRaw` proves the frozen raw
  relay from the Clean windowed HEAD relay (`StrictFrom` at `T₀ = z_{s-1}`).
  See `Clean/FormationOPEN.md`.
- PC-SA finality safety (P12): `Foundations/FGSafetyBridge` converts the PC
  reads and applies Compose `SafetyAccountable`, `SafetyCount`,
  `SafetyMonotone`, and `SafetySlashing` through four exact `COMPOSE_EDGES`.
  `Foundations/FinalitySafety` supplies the six run bodies. `Finality/Export`
  proves the two pure fields with KitFG and closes all eight frozen claims.
  `Assembly/Finality` supplies `PCSAClaims.finality` with
  `pcsaSafetyFinalityClaims`. Both FG modes are covered. Count retains
  all-run carriage; honest non-slashing uses stored-row carriage.
- PC-SA recovery lock history (2026-10-08). `Recovery/LockRank` proves the
  held-PC rank invariant for live locks. `Recovery/LockHistory` retains exact
  rows and ranks across receipts and clocks outside gates. It locates the gate
  at the start of the final uninterrupted interval of a row and its rank.
  The derived write witness keeps that interval, the fresh gate, the current
  result, the preceding saved window, the write rank, and the exact deadline.
  `recovery_live_lock_last_write` supplies it at an actual post-clock read.
- PC-SA recovery anchor (2026-10-08). `Recovery/AnchorBase` bounds the
  proposer base from one node's anchor stamp and the C8 strong-output bound.
  `Recovery/FirstSlot` proves the first formation slot and its separate
  `RecoveryRootReachable` clauses from the anchor and saved-result bounds.
  `Assembly/Recovery` supplies three wrappers:
  `pcsa_recovery_cleanSaved_from_anchor` bounds saved results below the anchor;
  `pcsa_recovery_anchor_from_shortBreak` supplies the anchor proposal, stamp,
  ARM, and C8 conclusion; `pcsa_recovery_firstSlot_short` supplies the first
  formation slot and its separate root clauses from `ShortBreakPrem`.
- PC-SA Outage items (2026-10-06): `AvailableChainPCSAClaims/Statements/OutageItems`
  holds the statement-only items of the Outage lane: `LockRow`, the ARM-healthy
  items `CleanHeldPCRelay`, `CleanArmAcks`, `CleanArmItems` (5.4.2) and the slow
  P1 boundary `CleanSlowBoundary`, `CleanSlowItems` (5.5 steps 1–2). They are
  not claims. A lane module may import them (Statements are upstream of every
  lane); the proofs stay in their lanes. The pending-label Clean claims
  (`CleanResultsNonemptyClaim`, `CleanResultsChainPendingClaim`,
  `CleanDisseminationPendingClaim`) and `CleanBlockReceiptClaim` (the relay item) are
  in `Claims/Clean`, outside the `PCSAClaims` record. C8 ARM-healthy uses the
  vote-time HEAD cone `CleanVoteConeItems` and C10 slow P1 uses the full HEAD
  cone `CleanConeItems` (`Outage/CleanBridge`). The Outage assembly proves both
  from the Clean cone theorems and closes C8 (`pcsa_armHealthyClaim`) and C10
  (`pcsa_slowP1Claim`) with no open hypothesis (see
  `AvailableChainPCSAProofs/Proofs/Outage/OPEN.md`).
  `Outage/BlockReceipt` proves block receipt from the Shared body relay;
  Assembly/Outage packages it as `CleanBlockReceiptClaim`.
- KitFG definition modules: `StoreInvDef` holds the unchanged `StoreInv`;
  `ViewLock` states the strict height bound; `HonestRows` holds the three
  honest-row premises. Each uses `@[expose] public section`.
- KitFG `Certificates` adds E-15 row-step commutativity and idempotence,
  fold permutation and duplicate removal, and transition equality by row set.
- KitFG FG-fold consumption (pure SimplexFG facts, 2026-10-01): `FinalityConsume`
  (finality write from quorum coverage), `HeightConsume` (target/progress
  advance), `NoEarlyMixed` (early crossing is justified; first height edge;
  plateau J), `RowHistory` (row-occurrence history). FG-SA uses them on the
  window fold only through the height bridge; the finality lemmas stay
  SimplexFG facts.
- KitFG window core (height bridge, blueprint 01 §3.1a): definition modules
  `HeightCoreDef` (FGHeight projection without finality fields, HeightRowsEq
  selector condition, deriveWithSelector on the same block geometry,
  HeightStepBridge, HeightFoldRefinement) and `HeightLawsDef` (FGHeightLaws);
  proofs `HeightFold`, `HeightBridge`, `HeightLaws`, `HeightConsumeTransfer`,
  `HeightHistoryTransfer`. FG-SA supplies the window instance
  (`HeightFoldRefinement` for its raw window fold); KitFG never imports FGSA.
- KitFG window certificate (migration stage 2, 2026-10-02): definition modules
  `CertificateCoreDef` (FGFinality projection, TargetQCAt, JustificationBirth,
  FGCertificateLaws), `CertificateSelectionDef` (entries keyed by (j, X) with
  their quorum; greatest-ready selection read from the pre-finality list;
  pruned lower entries covered by X ⪯ F with no own QC; eviction gives no
  coverage; pruneCertEntries), `StoreSafetyDef` (F-lock with explicit fault /
  no-slash premises) and `ProvenanceCoreDef`. Shared cores, with no
  `CertificateSimplex` in their import closure: `AccountableCore`, `CrossingCore`,
  `ProvenanceCore` (forms that need only the height laws take FGHeightLaws),
  `SelectionCore` (FGSelectionLaws.of_core, FGCertificateLaws.of_selection),
  `StoreSafety`. SimplexFG adapters: `CertificateSimplexDef`,
  `CertificateSimplex`, `StoreSafetySimplex`. Existing KitFG proofs stay
  unchanged; the cores are added companions. FG-SA proves the window instance
  (FG2) and calls the cores.
- KitFG frame bridge (for the FG5 switch, 2026-10-02): `FrameBridgeDef` states
  these SimplexFG readers over a height view v: frontier, lexMax, filteredFrom,
  storeControls, storeFrame, fjControls and fjFrame (`…View`); `FrameBridge`
  proves each equal to its view form under `HeightBridge E cfg v`, plus
  hOf_of_bridge. They read only height fields. SimplexFG is unchanged. Readers
  of the finality fields (on_block, update_finality) are not covered; FG5
  replaces them with the window store.
- KitFG frame geometry (LF8, FG5 job J1, 2026-10-02): `FrameGeometry` states the
  frame facts that FG-SA took from `StoreInv` over `FGStoreInvariant H f` in
  view form (controls = FJ controls, full frame, crossed-prefix height,
  no-contest, contest, retention), by the structural route (J carrier from
  `pair`, `hmax`, `gen`), plus `mem_filteredFromView`.
  `JustificationLawsDef` adds `FGJustificationLaws H` (J entry, J height,
  J zero), with `FGJustificationLaws.of_bridge` for every bridged view.
  `CausalCapCore.finalityCap_row_of_certificate` is the finality-cap row over
  `FGCertificateLaws`.
- FGSA E-11 adds `LeaseBelowOutputStore` in `Statements/Invariants` and
  `StoreBundle` with `StoreBundleInvariant` in `Statements/Store`. The bundle
  has cstore, meta, nest and lease fields; the E-11 statements are PROVED.
- `AvailableChainFGSA/Proofs/LeaseOutput` proves the E-11 stored-target invariant.
- `AvailableChainFGSA/Proofs/StoreBundle` proves E-11 by bundle induction
  (`storeBundleInvariant`).
- FG-SA window (stages 1–2, on main; additive until the switch J4):
  `Model/Window` (window state with ≤ K_W retained justifications, the raw
  fold `transition p K`, `derive p K`, R6W row validity), `Model/WindowStore`
  (window store and viable tree); `Statements/WindowHeight` and
  `Statements/WindowCertificate` (projections, pre-finality state);
  `Proofs/WindowHeightBridge` (windowHeightBridge, window height laws),
  `WindowInvariant` (structural window invariants), `WindowSelection` and
  `WindowCertificates` (the KitFG certificate and selection records),
  `WindowProvenance` (provenance forms), `WindowHistory`, `WindowStore`
  (store invariant over the window views), `Statements/WindowEntries`
  (`RetainedW`, `CoveredW`: the window key (j, U)), `WindowLiveness` and
  `WindowRetention` (pure stage-4 bit, retention and exact-row facts).
  Since J4 (2308c42): the model runs the window fold. `heightView` =
  projectHeight of `Window.derive p p.K_W`; `finalityView` = certificate
  finality; `admitBlock` checks every row with R6W (`rowValidW`) against one
  pre-fold `Window.parentState`; the client reads window head finality. The
  height bridge keeps the shared source projection and the height-only Claims
  readers equal until J6. `scripts/CheckFGSAOldReads.lean` audits that no
  active declaration reads the old fold's finality.
- 07-H adds Claims `Fold` for height batches, raw action-history inputs in
  `Phases`, and `Claims/Healing` adapters. `Foundations/RowService` proves
  strict all-emissions receipt at ΔF, parent-valid selection, and height
  coverage on the current fold. `HeightMatch` is explicit at height consumers.
  `TRowsSelect` remains the R7 validity selector. Finality-bit ports wait for 07-F.
- FG-SA healing lane (S5 CONE): `Proofs/Healing/PostResetCone` proves the
  cone step at each event cut; `PostResetConeFrame` supplies the common pivot
  and floors; `PostResetConeHeads` bounds source and live-lease heads;
  `PostResetConeInput` assembles the cone input; `PostResetConePool` proves
  the honest-seat and frozen-pool bounds; `PostResetConeReceipts` proves
  receipt and batch-seat facts. `Tests/HealingPostResetCone` checks the step,
  the empty cut and the run projection. Paths are under `AvailableChainFGSAProofs/`.
- FG-SA healing lane (RE-BIND): `Proofs/Healing/PostResetConeAt` projects the
  cone at a bounded HEAD label; `PostResetJointStep2` supplies the opening
  and service steps from the cone at the step cut.
- `AvailableChainFGSARun` (T7.2) holds the v2 protocol, label families,
  isolation, wire adapters, and exclusion proofs, with separate Tests.

- SYN L58: `Proofs/Assembly/Root` imports the `FGSAClaims` facade and the named
  lower Assembly modules `Foundations`, `Shared`, `Clean`, `Outage`, `Finality`,
  `ResetArrival`, `WeakContinuation`, `WeakContinuationGrowth`, and
  `WeakContinuationGrowthSeed`. The other layer rules still apply.

- WC plan r2.1, §8 Job 4; DC: SAME source witness before continuation.
  `Proofs/Assembly/WeakContinuation` takes the H-time producer from Root.
  It selects the source witness, constructs one seed, then replays the seed
  and supplies the 34 separate [L] premises for each continuation.
  `Proofs/WeakContinuation/Live` combines seeded safety with `wc_checkpoint`.
  `WeakContinuation/Export` re-exports this helper and replay for Assembly.
  Its four Statement inputs use the actual Job 2 producers. The result contains
  safety, persistent inclusion, and growth at `t + G' + 6 * p.Δ`.
  `Proofs/Shared/Claims` projects the live claim to the safety claim.
  Root fills the appended `FGSAClaims.weakContinuationLive` field with the
  closed `healing_hTimeClaim`. `fgsaClaims` has no additional hypothesis.
  Assembly/WeakContinuation imports WC Export and Shared/Claims; it imports
  no Assembly module.

- FG-SA outage continuation under (V): `Proofs/Outage/ContinuationTiming`,
  `ContinuationInduction`, `ContinuationReceipt`, `ContinuationFrame`,
  `ContinuationGate`, and `ContinuationJoint` prove the continuation body.
  `Proofs/OutageContinuation/Export` exports `outageContinuation_claim_of`.
  `Proofs/Shared/Claims` uses `outageContinuation_of_body` to bridge the body
  to `OutageContinuationClaim`. `Proofs/Assembly/Clean` supplies the interfaces
  and proves `fgsa_outageContinuationClaim`. The exact lane import exception
  in `scripts/check-layers.py` permits `OutageContinuation.Export` to import
  exactly the six `Outage/Continuation*` modules listed above. No other lane
  import allowance changes. `FGSAClaims` is unchanged; this is a companion claim.

- WC corruption growth adds `fgsa_weakContinuationGrowthClaim` in
  `Proofs/Assembly/Root`, without changing the frozen `FGSAClaims` field.
  `Assembly/WeakContinuationGrowthSeed` selects one bounded source witness.
  `WeakContinuationGrowth/Replay` transfers retained local traces through
  the inclusive endpoint, with separate source and continuation cut indices.
  `Assembly/WeakContinuationGrowth` joins the nonempty suffix branch with
  weak participation and the empty suffix branch with prefix-only replay.
  The claim keeps safety, both outputs, inclusion, and conditional growth
  under the whole-run `FinalitySlashableBound` premise.

How the pieces meet:
- FG-SA store: `FGSA.State` keeps a root-mode `GridCO.State`, an FG store, and pools.
  GridCO proofs use `slowLeasePolicy`; FG store facts come from KitFG. Duty `ACReads`
  carries the HEAD mode. Deferred protocols retain their legacy block-mode reads.
- ROOT-DIGEST-2: `NamedProposal` keeps every ancestor's body and signed lists.
  `namedProposal` sets the six-field digest; `namedContentOk` checks it. Admission
  requires the exact named parent, keeps the received named value, and also checks
  the FG-parent projection. The I9 BODY codec remains the row/geometry projection.
  HEAD targets are identifiers. Resolution uses the cumulative domain even in active views.
  Standalone legacy GridCO, LStar, and SAPC keep `nodeRoot`.
- Named run scope: directly delivered proposals and honest prefix-held named bodies,
  closed under named ancestry. Rejected deliveries are seeds. HEAD-only identifiers
  and emitted-only tips are not seeds. `RootBlockInRun` is the existential erasure
  projection. `Base₂.idealization` has the one `NamedRootCollisionFree` field.
  Its DC-shaped clause identifies full named ancestors of either scoped tip.
  `FGSARun/Proofs/NamedScope` proves named equality and geometric projections;
  `FGSARun/Proofs/Roots` supplies origins. `KitFG/RootScopeDef` keeps the explicit
  pure two-chain premise.
- Store safety: `FGStoreSafety` takes `StepOK`; `StoreStepRoots` requires
  root uniqueness on the inserted tree. `KitFG/StoreSafetyDef` defines this
  interface. `storeStepRoots_of_blockAccepted` proves it at admission.
  Option-3 exceptions r2.1–r2.2 require uniqueness on each exact walked
  tree; r2.3 adds body scope for `eraseFG B` to `CPPrefix` after honest
  membership. See [the exception record](lock-log/root-digest/README.md).
- Generic FG finality safety (2026-10-07). `AvailableChainFGCompose` states
  the safety contracts (`Statements/SafetyReads`, `SafetyStore`,
  `SafetyClient`, `SafetyClaims`) and proves the accountability fields 3-5 in
  `Proofs/SafetyStore` and `Proofs/SafetyAccountable`, the client and count
  results in `Proofs/SafetyClient` and `Proofs/SafetyCount`, finalized
  monotonicity in `Proofs/SafetyMonotone`, and field 8 (honest non-slashing)
  in `Proofs/SafetySlashing`. FG-SA supplies the laws in
  `Shared/FGSafetyClient`, `Shared/FGSafetyStore` and `Shared/FGSafetyScope`.
  `Foundations/FGSafetyBridge` states these results at the FG-SA reads:
  accountability, the pool count, client safety and row origins, finalized
  monotonicity and honest non-slashing. `Accountable`, `Client`,
  `ClientOrigin`, `FinalizedSafety` and `HonestNeverSlashed` call the bridge.
  Its public types use only FG-SA terms, with the `FinalityRunBlock` body
  expanded, because `Foundations/Accountable` imports the bridge. Its four
  Compose imports are the exact pairs `Foundations.FGSafetyBridge` →
  `AvailableChainFGCompose.Proofs.SafetyAccountable`, `.SafetyCount`,
  `.SafetyMonotone` and `.SafetySlashing` (`COMPOSE_EDGES` and
  `laneUpstream`). The five callers reach the Compose proofs only through
  the bridge.
- FG-SA on engine v2 (T7): `Node = {st, rec}`, `base = st`, `rec = Λ`
  (durable). Label families: HEAD labels AP and fresh (`CStar`); FG labels
  `Linked`; proposal labels AP and `SingleSeat`, one label per slot
  (`Interface.propLabel_injective`).
- Walks: `ghost` takes an anchor. The base has `confirmationFrom a`,
  `gateFrom a` and `clockFrom a` (713f56f); the old names are the genesis
  forms. SA uses genesis; FG-SA uses Σ.F (spec sync, 1944bb8).

Engine v2 decisions (design §2), one line each:
- E1 duties and keys: `Auth = seat ℓ i | none`; a proposal duty is a
  one-seat label; no global `n`.
- E2 seats: `seats ℓ`, `Run.seatOf ℓ`; committee models are conditions
  (`CStar`, `Linked`, `SingleSeat`).
- E3 weights: later additions (seat multiplicity plus conditions).
- E4 delivery outcomes: a delivery calls the handler; exclusions are
  explicit; deliverability (`RelayFeasible`) comes in plan 1c.
- E5 own-signature record: `selfVisible`, `recordOwn`, atomic tick;
  `Isolation` factors the AP part through `base`, so AC facts transport to
  the AP projection.
- E6 restart: `restart v t`, `st ↦ restore (durable st)`. FG-SA interim
  form: Λ durable, store reset; the anchor form (Λ + F) comes with the
  optional anchor-and-pruning claim.

## 4. Constraints

- Proofs: no `sorry`, `admit`, `native_decide` or new axioms;
  `decide +kernel` is allowed. Every gate runs an axiom check.
- Toolchain v4.34.1, Mathlib d13f23b7; never `lake update`; never a new `lean_exe`
  (scripts run with `lake env lean --run`). The Mac has 3 Lean slots
  (check `pgrep -fl lean` first); FCR builds run on the NUC.
- Landing check-fg skip (lead ruling 2026-10-03): `scripts/check-fg.sh` runs
  on the Mac only (its pin check hashes archived research files). A merge-tier
  landing may skip it when `python3 scripts/fg-closure.py --changed <main>
  <head>` exits 0: the diff touches no file of the FG closure at either
  revision. The closure is: every file that the lakefile globs of the targets
  check-fg builds match (AvailableChainKitFG.* includes its Tests), their
  in-repo import closure and that of the Lean scripts check-fg runs;
  check-fg.sh, its helpers and the files they name; lakefile, toolchain,
  manifest. The closure is recomputed at each landing, any script error means
  "run check-fg", and each skip logs its line. `--selftest` runs the negative
  controls. FULL-tier gates and the daily full main run always run check-fg.
- Lock: `scripts/CatalogLock.lean` hashes the dependency closure of every
  declaration in the locked modules (framework, statements, catalog; not
  the protocol libraries). A change needs an expected-name list,
  `--write --allow-changes`, a clean `--check`, and a lock-log entry in
  design §8. Companions and optional claims only add lines.
- V2 freeze (2a gate, 1aa6885): every declaration in `docs/V2-API.md` is
  frozen, with a per-entry hash; `scripts/V2Manifest.lean --check` checks
  it. Engine entries are also locked through anchor defs in
  `AvailableChainFramework.V2`. Never edit `anchor`; add a new anchor def.
  New declarations go after the existing ones or in a new module; the
  manifest module blocks are append-only.
- T7 import guard: the FG-SA run library imports no v1 Kit, v1
  Statements, v1 engine or `GridCO.Proofs.*` directly, and a used-constant
  check backs the rule (the import closure cannot be v1-free). FG-SA
  reaches Grid CO walk and score lemmas through wrappers in
  `AvailableChainFGSA.Proofs.*` (option b2; `fgHead_stored` is the
  precedent). Wrapper statements use only model-level constants. The move
  of the pure lemmas to `GridCO/Walk/` (about 70 declarations) is deferred.
- DC Lean is a reference, not a dependency (`using!`, R ≥ 3).
- Process: a plan per phase with an audit; a task review for each task and
  a final branch review; Claude + Astra before big decisions, a full audit
  before major ones; decisions taken without the user are logged. Codex
  always with `-c service_tier="fast"`. Commits by explicit path;
  worktrees under `~/worktrees/`.

- Generic API: `docs/GEN-API.md` records Statements types and values;
  `lake env lean --run scripts/V2Manifest.lean --scope gen --check` checks it.
  Before G-F0a, a Statements edit updates the manifest in the same commit;
  from G-F0a it is append-only (D15).
- Before a branch-to-branch merge without a gate, run `bash scripts/check-gly-rules.sh`
  and `SKIP_CONE=0 bash scripts/check-build.sh` on the merge result after a full build.
- `bash scripts/check-build.sh` runs all checks below after a full build.
  `docs/LEAN-ARCHITECTURE.md` gives the module and import rules.

```text
┌───────┬─────────────────────────┬──────────────────────────────────────────┐
│ Check │ Script (scripts/)       │ Rule                                     │
├───────┼─────────────────────────┼──────────────────────────────────────────┤
│ (a)   │ check-module-headers.py │ module headers and public imports        │
│ (b)   │ check-expose.py         │ Proofs expose only allowed definitions   │
│ (c)   │ rebuild-cone-test.sh    │ A proof-only edit rebuilds one module    │
│ (d)   │ CheckProofEqns.lean     │ Proofs export no new equation lemmas     │
│ (e)   │ check-layers.py         │ Module imports follow the layer rules    │
│ (f)   │ shake-report.sh         │ Unused imports; report only, no --fix    │
│ (g)   │ chain-depth.py          │ Longest import chain; report only        │
│ (h)   │ check-transparency.py   │ Transparency option position and reasons │
│ (i)   │ check-gly-rules.sh      │ GLY rules and per-rule baselines         │
└───────┴─────────────────────────┴──────────────────────────────────────────┘
```

## 5. Milestones

```text
┌────┬──────────────────────────────────────┬──────────────────────────┐
│ M  │ Content                              │ Status 2026-09-30        │
├────┼──────────────────────────────────────┼──────────────────────────┤
│ 1  │ I9 derived roots + engine v2 core    │ done: I9 3403e58; 2a     │
│    │ (2a)                                 │ 1aa6885                  │
│ 1+ │ Post-I9: walk anchor                 │ anchor 713f56f and spec  │
│    │ (`confirmationFrom`/`gateFrom`);     │ sync 1944bb8 done; Pins  │
│    │ FG-SA spec sync (walk from F, Pins)  │ re-pin next (fgsa-lean)  │
│ 2  │ T7/T1: FG-SA run instance on v2,     │ T7.0 base ready;         │
│    │ FGSAClaims, registry map             │ T7.2 landed (30a843f)    │
│ A0 │ Step 2: Generic statements and kits  │ I01–I23, I25 landed;     │
│    │ plus the build checks and manifest  │ I24 close gate in review │
│ 3  │ 1c for FG-SA: run construction and   │ to plan; order (before   │
│    │ inhabitation for every horizon       │ 2b/2c) waits for user    │
│ 4  │ F0 statement layer → F1 foundations  │ scoped; F0–F2 draft      │
│    │ → safety lane (Clean, P1/inclusion)  │ running                  │
│    │ ∥ liveness lane (finality kernel,    │                          │
│    │ healing) → F6 GST bounds             │                          │
│ -  │ Deferred: 2b lift, 2c (restart       │ deferred                 │
│    │ extension, I1 floor), Grid CO items, │                          │
│    │ anchor + pruning optional claim      │                          │
└────┴──────────────────────────────────────┴──────────────────────────┘
```

Window migration (stages, `tip-stability/codex/reports/window-migration.md`
§1): 0 close the current no-round migration (06/07, Δ_F delivery) → 1 add
the window core (additive; SimplexFG unchanged; height bridge) → 2 prove
the interfaces (height transfers, provenance, window store invariants) →
3 switch FG-SA to the window fold once → 4 finish 07-F and re-freeze →
5 prove liveness on the window API.

Stage 3 is split (lead rulings, `tip-stability/codex/reports/fg5-rulings.md`
with its addendum): readers and invariants are ported green BEFORE the switch,
and only the instance swap is atomic.

```text
┌────┬────────────────┬──────────────────────────────────────────────────────┐
│ Job│ Owner          │ Scope                                                │
├────┼────────────────┼──────────────────────────────────────────────────────┤
│ J0 │ both           │ land w3 (FG4 + FG2), LF5 fixes + LF6 + LF7, achfix   │
│ J1 │ lean-framework │ LF8: frame geometry over FGStoreInvariant,           │
│    │                │ FGJustificationLaws, generic finality-cap row        │
│ J2 │ fgsa-lean      │ FG5a: Params.K_W (2 ≤ K_W); Model/WindowViews; view- │
│    │                │ form readers, bridge-equal; no meaning change        │
│ J3 │ fgsa-lean      │ FG5b: store invariants → FGStoreInvariant (views     │
│    │                │ still simplex); WindowStoreInv removed               │
│ J4 │ fgsa-lean      │ FG5c, ATOMIC: views and updaters → window fold, R6W  │
│    │                │ admission, window head fields; instance proofs.      │
│    │                │ DONE 2308c42 (J0–J3 and J5 also done)                │
│ J5 │ lead           │ review of J4 (two models)                            │
│ J6 │ fgsa-lean      │ FG5d: height-only Claims readers → H (cosmetic)      │
│ J7 │ fgsa-lean      │ IF.3(b) producer on the window (SO-COV)              │
└────┴────────────────┴──────────────────────────────────────────────────────┘
```

## 6. Decisions that shape the architecture

- ROOT-DIGEST-2: the run premise identifies full recursive named proposals.
  FG-SA checks the digest and exact named parent and uses root-mode HEAD handling.
  The I9 BODY codec supplies row and geometry projections. Legacy GridCO, LStar,
  and SAPC keep `nodeRoot`. The option-3 exception retains the closed claim fields.
- Restart: interim form keeps Λ and resets the store; the faithful form
  (Λ + anchor at F) comes with the optional anchor feature.
- SA walk starts at F (user, 2026-09-29).
- Pruning: an optional claim "prunable at F", not an obligation; no root
  set needed.
- Leak claims: parked; not in the first verification target.

## 7. Open architectural questions

- Interface gap: CLOSED in the blueprint (r212/r212b, 2026-09-29):
  `HEALING_INPUT` split with H5/H6, exact map to the spec's H0–H4, kernel
  dependency list, scoreSuffix for X ⪰ D. Open: align the spec's
  `HEALING_INPUT` names (next spec revision, with the OD6 pre-GST
  sentence).
- Registry: new ids fj.descent.v2, fj.twoChanges.core.v2,
  ap.headReachesLo.v6 (blueprint 21); the three old ids are WITHDRAWN for
  current use (policy §0; v5 still true in its scope); fj.frame.v4 comes
  with r213. The re-pin commit (fgsa-lean) follows r213.
- Representation option (needs a proof first): filter AC records by the
  current F at read time, as DC does, instead of the reconcile write.
- The post-gate cut: F0–F2 draft uses a new reader `afterTicks` (no v2
  change).
- One-repair healing is open. Healing bounds (k ≤ 2R+1, G = 8Δ): B_H
  stays 295Δ/343Δ as the general target (the F6 Lean target). Separate
  bounds: HG.7 upper 268Δ/312Δ; HG.8a upper 204Δ/240Δ (lemma L4-R, no
  cut change, no spec change; in review, then r213). Lower bound
  89Δ−1 tick / 105Δ−1 tick for Δ ≥ 2 (reviewed VALID). The cut change B
  (196Δ/228Δ) is a documented option only.

## 8. Where the detail is

- Research (tip-stability): `state.md`, `log.md`, `spec/`, `blueprint/`,
  `codex/`.
- Lean: `docs/FRAMEWORK-DESIGN.md` (framework), `docs/FG-COMPOSITION.md`
  (FG composition), `docs/MAP.md` (contract to Lean), `docs/audit/`.
- Lean module rules: `docs/LEAN-ARCHITECTURE.md`; Generic Statements API:
  `docs/GEN-API.md` (checked by `V2Manifest --scope gen --check`).
- Plans (`docs/plans/`): framework-phase0, phase1a-gate-catalog,
  phase1b-instances, fg-module, fgsa-model-store (all closed);
  i9-derived-roots (merged 3403e58); phase2a-engine-v2-core (merged
  1aa6885; `docs/PHASE2A-REPORT.md`);
  fgsa-composition-t7-t1 (r11 adopted, 2ec3003; in
  `~/worktrees/available-chain-fgsa-plan`).

- PC-SA long-break transport (2026-10-08). `Recovery/LockTransport` holds
  lane-neutral receipt and pool facts from label `g`. `Assembly/Recovery`
  proves all seven suppliers from lane exports. PC key receipt uses only early
  and vote cutoffs. The run wrapper has no OPEN transport premise.

- PC-SA lock overlap (2026-10-08). `Recovery/LockOverlap` proves mix-time
  expiry, overlap compatibility, and PC relay compatibility at the write
  and within a surviving interval. `Recovery/LockView` proves the voter-view
  rank bound.

- PC-SA recovery rank dissemination (2026-10-08). `Recovery/LockStamp` derives
  a held key before the early cutoff from the actual PC stamp history, then
  relays its rank before the freeze. `Recovery/LockView` retains that rank
  in later voter candidates and proves K for pending writes and surviving
  rows, including PCs carried by proposals. Existing lock signatures stay fixed.

- PC-SA surviving-lock coverage (2026-10-08). `Recovery/LockDomain` proves
  the cumulative resolution domain. `LockCounts` transfers a saved gate
  result to the actual next voter pool. `LockBatch` gives later honest
  batch counts. `LockFollow` proves F′ from the last write and exact-row
  survival, then derives preceding HEAD coverage from a live read.

- PC-SA long proposal paths (2026-10-08). `Recovery/ProposalPaths` transfers
  the actual preceding honest HEAD batch into the proposer pools. It proves
  the walk from the selected base reaches the live root and the voter F4
  lease clause. Both use the survival proof in `LockFollow`.

- PC-SA long first-slot assembly (2026-10-08). `Recovery/LongFirstSlot`
  constructs `FormationPrem` and the explicit proposer-root walk conjunct.
  `Recovery/Export` proves the predicate conversion with the defining equation.
  `pcsa_recovery_firstSlot_long_of_run` selects a bounded slot from the long
  claim premises. The Formation literal also uses the existing root proof.
