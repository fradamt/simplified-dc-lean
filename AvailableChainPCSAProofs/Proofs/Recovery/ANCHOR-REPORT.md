# PC-SA recovery anchor report

Base: `5995104a`. Branch: `pcsa-recov-anchor`. No push.

## Commits

- `00e0a155`: step 3, anchor-to-proposer-base bound.
- `031f5e4d`: first-slot kernel from explicit anchor facts.
- `2153c628`: regenerated proof-audit coverage.

All commits have the requested Claude-Session trailer.

## Plan status

- Step 1: **STOPPED**. The saved-result target needs
  `pcsa_clean_result_below_proposal_parent` from `Clean.Export`.
  The Recovery-only limit prevents this import. The layer policy rejects it.
- Step 2: **STOPPED**. The anchor target needs
  `pcsa_clean_honestProposal_stamped` from `Clean.Export` and
  `recovery_persistence_of_run` from `Assembly.Recovery`.
  Recovery cannot import these cross-lane suppliers.
- Step 3: **PROVED**. `pcsa_recovery_anchor_proposer_base` has the planned type.
  C8 bounds the strong output at the integer time before the proposal tick.
  The tick preserves PCs. All held PCs are active in stage one, so the
  proposer base is this strong output. No new C1 argument is needed.
- Step 4: **STOPPED** for the exact target `pcsa_recovery_firstSlot_short`.
  The kernel `recovery_firstSlot_of_anchor` is proved. It supplies
  `FormationPrem` and the separate `RecoveryRootReachable` predicate from
  the step 1 saved-result bound and the step 2 stamp and ARM conclusion.
  All live voter locks are below the proposal parent. This proves F4 directly.

No counterexample or false statement was found. The remaining block is scope.

## Required placement decision

Plan section 6 requires cross-lane composition in `Assembly/Recovery.lean`.
The exact requested scope exception is to append these three wrappers there:

- `pcsa_recovery_cleanSaved_from_anchor`
- `pcsa_recovery_anchor_from_shortBreak`
- `pcsa_recovery_firstSlot_short`

The permission question is pending. No checker, guard, or policy edit is
needed if this placement is allowed. No such edit was made.
The existing Assembly module already imports the required lane exports.

Claims, Statements, Model, Clean, Shared, and Finality files are unchanged.
The formation F4 field, long-break proof, suffix invariant, and CI restart
are outside this change.

## Validation

- PASS: default `lake build --wfail` (4,585 jobs).
- PASS: layer check (zero new findings) and layer self-test (37 controls).
- PASS: F-13 under `LC_ALL=C` (zero failing or stale entries).
- PASS: `NEG=0 check-pcsa-manifest.sh` (421 entries, 21 modules, hashes match).
- PASS: coverage regeneration (5,864 declarations across 13 audits).
- PASS: main-repository precheck (`main=5995104`, `target=2153c62`).
- PASS: coverage check (all 13 audits).
- PASS: `LC_ALL=C bash scripts/check-build.sh`, including proof equations,
  GLY, and all checker self-tests. No unaccepted equation exports.
- PASS: `NEG=0 bash scripts/check-fgsa-claims.sh`.
- The first full build check failed its unchanged-worktree control because
  this report was edited during the layer self-test. The rerun kept all
  worktree files fixed and passed. No checker change was made.
- Name check under `LC_ALL=C`: no clashes on visible `main`,
  `pcsa-w2-formation`, or `pcsa-ci-win-1`. `pcsa-fsrc` is not visible; skipped.
- All three new public names have explicit `#print axioms` lines.
  Only `propext`, `Classical.choice`, and `Quot.sound` occur.

## Final public signatures

These declarations use the namespace `AvailableChain.PCSA.Run` and the
ambient parameters from their source modules.

```lean
theorem recovery_base_of_arm (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho)
    (hf : StageOneFrame p c E rho) (cA : Slot) (P : Block)
    (hs : ∀ y ∈ rho.honest,
      PCStampedBefore p c E rho y (SA.freezeTime p.toParams cA) cA P)
    (ha : ArmConcl p c E rho cA P (cA + 1))
    (x : V) (hx : x ∈ rho.honest) (t : Time)
    (ht : SA.freezeTime p.toParams cA < t)
    (nd : Node p) (hn : pcsa_postClock E rho x t = some nd) :
    Block.Preceq P (walkBase p nd.st (proposerPC p nd.st))
```

```lean
theorem pcsa_recovery_anchor_proposer_base (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) {G ΔF : Time} {cA s₁ : Slot}
    (h : ShortBreakPrem p c E rho G ΔF cA s₁)
    (N : NamedProposal p.n)
    (_hN : HonestNamedProposal p c E rho cA N)
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
    (cA s : Slot) (P : Block) (hpos : 0 < s) (horder : cA < s)
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
