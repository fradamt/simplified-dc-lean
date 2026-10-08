# PC-SA recovery anchor report

Base: `5995104a`. Branch: `pcsa-recov-anchor`. No push.

## Commits

- `00e0a155`: step 3, anchor-to-proposer-base bound.
- `031f5e4d`: first-slot kernel from explicit anchor facts.
- `2153c628`: regenerated proof-audit coverage.
- `3536a568`: initial report and placement request.
- `6d8d0553`: step 1, saved-result anchor wrapper.
- `9a3e0fe1`: step 2, anchor proposal, stamp, ARM, and ARM conclusion.
- `4148bea2`: step 4, exact short-break first-slot wrapper.
- `358ae7b1`: regenerated coverage for the three wrappers.

All commits have the requested Claude-Session trailer.

## Plan status

- Step 1: **PROVED**. `pcsa_recovery_cleanSaved_from_anchor` bounds saved
  results through the clean predecessor gate and the proposal parent.
- Step 2: **PROVED**. `pcsa_recovery_anchor_from_shortBreak` supplies the
  honest anchor proposal, common stamp, ARM, and its C8 conclusion.
- Step 3: **PROVED**. `pcsa_recovery_anchor_proposer_base` has the planned type.
  C8 bounds the strong output at the integer time before the proposal tick.
  The tick preserves PCs. All held PCs are active in stage one, so the
  proposer base is this strong output. No new C1 argument is needed.
- Step 4: **PROVED**. `pcsa_recovery_firstSlot_short` has the exact planned
  type. It applies `recovery_firstSlot_of_anchor` to steps 1 and 2.
  `RecoveryRootReachable` remains separate from `FormationPrem`.

No counterexample or false statement was found. All four plan steps are proved.

## Placement decision

The lead approved the three wrappers in `Assembly/Recovery.lean`.
They use the existing lane Export imports. No import was added.
No checker, guard, or policy edit was needed or made.

Claims, Statements, Model, Clean, Shared, and Finality files are unchanged.
The formation F4 field, long-break proof, suffix invariant, and CI restart
are outside this change.

## Validation

- PASS: each wrapper's Assembly build with `--wfail`, before its commit.
- PASS: default `lake build --wfail` (4,585 jobs).
- PASS: layer check (zero new findings) and layer self-test (37 controls).
- PASS: F-13 under `LC_ALL=C` (zero failing or stale entries).
- Name check under `LC_ALL=C`: no clashes on `main`, `pcsa-w2-formation`,
  `pcsa-ci-win-1`, or `pcsa-fsrc`. All four branches are now visible.
- All three wrappers have explicit `#print axioms` lines.
  Only `propext`, `Classical.choice`, and `Quot.sound` occur.
- PASS: `LC_ALL=C bash scripts/check-build.sh`, including proof equations,
  all GLY checks, and all checker self-tests. No unaccepted equation exports.
- PASS: `NEG=0 bash scripts/check-fgsa-claims.sh`.
- PASS: `NEG=0 bash scripts/check-pcsa-manifest.sh` (421 entries, 21 modules,
  hashes match).
- PASS: coverage regeneration with `--write` and coverage verification
  (5,867 declarations across 13 audits). The inventory adds only three names.
- PASS: precheck from the MAIN repository (`main=5995104`, `target=358ae7b`).
- PASS: final diff check. Only the five permitted tracked files changed.
  Each wrapper was committed after its Assembly build passed.

## Final public signatures

These declarations use the namespace `AvailableChain.PCSA.Run` and the
ambient parameters from their source modules.

```lean
theorem recovery_base_of_arm (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : V2.D.ScheduleWellFormed E rho)
    (hnr : V2.D.NoRestart rho)
    (hf : StageOneFrame p c E rho) (cA : Slot) (P : Block)
    (x : V) (hx : x ∈ rho.honest)
    (hs : PCStampedBefore p c E rho x (SA.freezeTime p.toParams cA) cA P)
    (hstrong : ∀ t t' : Time, t ≤ t' →
      (∃ pc ∈ (storeAt p c E rho x t).pcs, pc.slot = cA ∧ pc.target = P) →
      Block.Preceq P (strong (storeAt p c E rho x t')))
    (t : Time)
    (ht : SA.freezeTime p.toParams cA < t)
    (nd : Node p) (hn : pcsa_postClock E rho x t = some nd) :
    Block.Preceq P (walkBase p nd.st (proposerPC p nd.st))
```

```lean
theorem pcsa_recovery_anchor_proposer_base (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) {G ΔF : Time} {cA s₁ : Slot}
    (h : ShortBreakPrem p c E rho G ΔF cA s₁)
    (N : NamedProposal p.n)
    (hStamp : ∀ y ∈ rho.honest,
      PCStampedBefore p c E rho y (SA.freezeTime p.toParams cA) cA N.erase)
    (hArm : ArmConcl p c E rho cA N.erase (cA + 1)) :
    ∀ nd, pcsa_postClock E rho
      (V2.D.proposerOf rho (pcsaInterface p c (m := m)).toInterface s₁)
      (SA.proposalTime p.toParams s₁) = some nd →
      Block.Preceq N.erase (walkBase p nd.st (proposerPC p nd.st))
```

```lean
theorem recovery_firstSlot_of_anchor (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) {G ΔF : Time}
    (h : Recovery₂ p c E rho G ΔF) (hf : StageOneFrame p c E rho)
    (cA s : Slot) (P : Block) (horder : cA < s)
    (hwindow : s - 1 - cA ≤ p.k - 1)
    (hafter : E.t_GST + p.Δ ≤ SA.proposalTime p.toParams s)
    (hprop : Gen.V2.Duty.HonestAwakeProposer E
      (pcsaInterface p c (m := m)).toInterface rho s)
    (horizon : SA.gateTime p.toParams s ≤ rho.horizon)
    (hStamp : ∀ y ∈ rho.honest,
      PCStampedBefore p c E rho y (SA.freezeTime p.toParams cA) cA P)
    (hArm : ArmConcl p c E rho cA P (cA + 1))
    (hSaved : ∀ x ∈ rho.honest, ∀ (i : Nat) (r : Slot) (C : Block), r < cA →
      GridCO.savedGenuine (V2.D.Run.stateBefore E rho i x).st.base r = some (some C) →
      Block.Preceq C P) :
    ∃ N : NamedProposal p.n,
      FormationPrem p c E rho s N ΔF ∧ RecoveryRootReachable p c E rho s
```

The three Assembly wrappers have these signatures.

```lean
theorem pcsa_recovery_cleanSaved_from_anchor [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) {ΔF : Time} (cA : Slot) (N : NamedProposal p.n)
    (hPos : 0 < cA)
    (hClean : Clean₂ p c E rho (SA.freezeTime p.toParams cA) ΔF)
    (hFault : FaultsBelowQA p c rho) (hFrame : StageOneFrame p c E rho)
    (hN : HonestNamedProposal p c E rho cA N) :
    ∀ x ∈ rho.honest, ∀ (i : Nat) (r : Slot) (C : Block), r < cA →
      GridCO.savedGenuine (V2.D.Run.stateBefore E rho i x).st.base r = some (some C) →
      Block.Preceq C N.erase
```

```lean
theorem pcsa_recovery_anchor_from_shortBreak [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) {G ΔF : Time} {cA s₁ : Slot}
    (h : ShortBreakPrem p c E rho G ΔF cA s₁) :
    ∃ N : NamedProposal p.n,
      HonestNamedProposal p c E rho cA N ∧
      (∀ y ∈ rho.honest,
        PCStampedBefore p c E rho y (SA.freezeTime p.toParams cA) cA N.erase) ∧
      Arm p c E rho cA N.erase (cA + 1) ∧
      ArmConcl p c E rho cA N.erase (cA + 1)
```

```lean
theorem pcsa_recovery_firstSlot_short [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) {G ΔF : Time} {cA s₁ : Slot}
    (h : ShortBreakPrem p c E rho G ΔF cA s₁) :
    ∃ N : NamedProposal p.n,
      FormationPrem p c E rho s₁ N ΔF ∧ RecoveryRootReachable p c E rho s₁
```
