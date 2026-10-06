module
public import AvailableChainPCSAClaims.Statements.Premises

@[expose] public section

/-! [PC-SA claims, W0; pcsa-proof-plan §1 C6, C7, C9, C14] The Clean lane
statements: the stamp convention of the PC snapshot, the joint clean invariant
CI (pcsa34-r4 5.2.2, stage 1), formation (5.3), and the clean corollaries
(5.2.3). Each claim is `∀ {V} [DecidableEq V] [Fintype V] {In} (c E rho),
premise → conclusion` (FG-SA claim shape), with a `_def` equation and no
proof. Stage 1: every claim takes `StageOneFrame` (CI item (vi) and the
formation premises (F6)/(F7) are vacuous). The fault bounds are as r4.3 §1.1
states them. -/

namespace AvailableChain.PCSA.Run

open AvailableChain.SimplexFG
open Gen.V2.Duty (faulty awakeHonest)

/-- [PC-SA claims, W0; pcsa34-r4 1.4 (stamps), 3.3 (sources); plan §5 risk
"stamped < z"] The snapshot of `z_s` holds exactly the PCs held after the
ticks at `z_s`: the PCs accepted before the tick `z_s` (stamp `< z_s`). The
claim fixes the r4.3 stamp convention against the model's `pcSnapshotAt`.
No fault premise. -/
def PCSnapshotStampClaim (p : Params) : Prop :=
  ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (pcsa p c)),
    Base₂ p c E rho →
    ∀ y ∈ rho.honest, ∀ s : Slot, SA.freezeTime p.toParams s ≤ rho.horizon →
      pcSnapshotAt (storeAfterTicks p c E rho y (SA.freezeTime p.toParams s)) s =
        (storeAfterTicks p c E rho y (SA.freezeTime p.toParams s)).pcs

theorem PCSnapshotStampClaim_def (p : Params) : PCSnapshotStampClaim p =
    (∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
      (E : Generic.Env V) (rho : V2.D.Run V (pcsa p c)),
      Base₂ p c E rho →
      ∀ y ∈ rho.honest, ∀ s : Slot, SA.freezeTime p.toParams s ≤ rho.horizon →
        pcSnapshotAt (storeAfterTicks p c E rho y (SA.freezeTime p.toParams s)) s =
          (storeAfterTicks p c E rho y (SA.freezeTime p.toParams s)).pcs) := by
  rw [PCSnapshotStampClaim]

section Invariant

variable (p : Params) {In : Type} (c : AppCodec In) {V : Type} [DecidableEq V] [Fintype V]
    (E : Generic.Env V) (rho : V2.D.Run V (pcsa p c))

/-- [PC-SA claims, W0; pcsa34-r4 5.2.2 CI(j), stage 1] The clean invariant at
label `j`, at every honest node and every time `t < v_{j+1}`. Item (vi) (the
frame) is stage 2 and is not a field. Results are the raw gate results
`R_x(i)` (`gateResultAt`); HEADs are the HEADs of honest awake voters.
- (i) `resultsChain`: honest results of labels `≤ j` are pairwise compatible,
  and a result of a later label extends every result of an earlier label
  (r4.3 (i) "D_{i+1} ⪰ D_i" with step (c) "results ⪰ D_{s−1}").
- (ii) `headsAbove`: every honest HEAD of label `i ≤ j` is `⪰` every honest
  result of label `i − 1`; `headsEqual`: at a label with an honest proposal
  `P` every honest HEAD is `P` (step (b)).
- (iii) `pcAck`: every held PC has an honest ack on its target (5.1);
  `pcChain`: held PC targets are pairwise compatible and rank order is prefix
  order (step (d)); `pcResults`: PC targets are compatible with every honest
  result (CL4).
- (iv) `leaseBelowResult`: every lease target is `⪯` an honest result;
  `leaseCompatible`: every live lease is compatible with every PC held at its
  node. The model has the effective-lease rule, not L*′, so r4.3's
  "L*′ skips or deletes none" has no field.
- (v) `recordOrigin`: every honest `S` is `F` or an own result of a label
  `≤ j`; `recordMono`, `recordCompatible`: `S` is monotone at a node and
  honest `S` values are pairwise compatible.
- (vii) `roots`: every honest root for `v_{j+1}` is compatible with every
  honest result of label `j` and every honest HEAD of label `j` (r4.3: the
  root is `Z`, a PC target or a lease target; that part is the definition of
  `live_root`). -/
structure CleanInvariantAt (j : Slot) : Prop where
  resultsChain : ∀ x ∈ rho.honest, ∀ y ∈ rho.honest, ∀ (i i' : Slot) (X Y : Block),
    i ≤ i' → i' ≤ j →
    gateResultAt p c E rho x i = some (some X) → gateResultAt p c E rho y i' = some (some Y) →
    (i < i' → Block.Preceq X Y) ∧ (i = i' → Block.Compatible X Y)
  headsAbove : ∀ (i : Slot) (x y : V) (H X : Block), 0 < i → i ≤ j →
    HonestHeadAt p c E rho x i H → y ∈ rho.honest →
    gateResultAt p c E rho y (i - 1) = some (some X) → Block.Preceq X H
  headsEqual : ∀ (i : Slot) (P : Block) (x : V) (H : Block), i ≤ j →
    Gen.V2.Duty.HonestProposalAt E (pcsaInterface p c).toInterface rho i P →
    HonestHeadAt p c E rho x i H → H = P
  pcAck : ∀ x ∈ rho.honest, ∀ (t : Time) (pc : PC p.n),
    t < SA.voteTime p.toParams (j + 1) → pc ∈ (storeAt p c E rho x t).pcs →
    ∃ y, HonestAckAt p c E rho y pc.slot pc.target
  pcChain : ∀ x ∈ rho.honest, ∀ y ∈ rho.honest, ∀ (t t' : Time) (pc pc' : PC p.n),
    t < SA.voteTime p.toParams (j + 1) → t' < SA.voteTime p.toParams (j + 1) →
    pc ∈ (storeAt p c E rho x t).pcs → pc' ∈ (storeAt p c E rho y t').pcs →
    Block.Compatible pc.target pc'.target ∧ (pc.slot < pc'.slot → Block.Preceq pc.target pc'.target)
  pcResults : ∀ x ∈ rho.honest, ∀ y ∈ rho.honest, ∀ (t : Time) (pc : PC p.n) (i : Slot)
    (X : Block), t < SA.voteTime p.toParams (j + 1) → pc ∈ (storeAt p c E rho x t).pcs →
    i ≤ j → gateResultAt p c E rho y i = some (some X) → Block.Compatible pc.target X
  leaseBelowResult : ∀ x ∈ rho.honest, ∀ (t : Time) row,
    t < SA.voteTime p.toParams (j + 1) → row ∈ (storeAt p c E rho x t).base.obligations →
    ∃ y ∈ rho.honest, ∃ (i : Slot) (X : Block), i ≤ j ∧
      gateResultAt p c E rho y i = some (some X) ∧ Block.Preceq row.1 X
  leaseCompatible : ∀ x ∈ rho.honest, ∀ (t : Time) (B : Block) (pc : PC p.n),
    t < SA.voteTime p.toParams (j + 1) → LiveLease (storeAt p c E rho x t) B →
    pc ∈ (storeAt p c E rho x t).pcs → Block.Compatible B pc.target
  recordOrigin : ∀ x ∈ rho.honest, ∀ t : Time, t < SA.voteTime p.toParams (j + 1) →
    (storeAt p c E rho x t).base.stableRecord = eraseFG (storeAt p c E rho x t).fg.F ∨
      ∃ (i : Slot) (X : Block), i ≤ j ∧ gateResultAt p c E rho x i = some (some X) ∧
        (storeAt p c E rho x t).base.stableRecord = X
  recordMono : ∀ x ∈ rho.honest, ∀ t t' : Time, t ≤ t' → t' < SA.voteTime p.toParams (j + 1) →
    Block.Preceq (storeAt p c E rho x t).base.stableRecord
      (storeAt p c E rho x t').base.stableRecord
  recordCompatible : ∀ x ∈ rho.honest, ∀ y ∈ rho.honest, ∀ t t' : Time,
    t < SA.voteTime p.toParams (j + 1) → t' < SA.voteTime p.toParams (j + 1) →
    Block.Compatible (storeAt p c E rho x t).base.stableRecord
      (storeAt p c E rho y t').base.stableRecord
  roots : ∀ x ∈ rho.honest, ∀ R : Block, liveRootAt p c E rho x (j + 1) = some R →
    (∀ y ∈ rho.honest, ∀ X, gateResultAt p c E rho y j = some (some X) →
      Block.Compatible R X) ∧
    (∀ y H, HonestHeadAt p c E rho y j H → Block.Compatible R H)

/-- [PC-SA claims, W0; pcsa34-r4 5.3 Claim] The formation conclusion at slot
`s` with the honest proposal `N` (`P = N.erase`): every honest HEAD at `v_s`
is `P`; `N_s(P) ≥ q_N` at every honest node at `e_s`; every honest node awake
at `e_s` acks `(s, P)`; `PC(s, P)` is stamped before `z_s` at every honest
node; if also `a < h_s`, every honest result at `d_s` is `P`. -/
def FormationConcl (s : Slot) (N : NamedProposal p.n) : Prop :=
  (∀ y H, HonestHeadAt p c E rho y s H → H = N.erase) ∧
  (∀ y ∈ rho.honest, ∃ nd, pcsa_postClock E rho y (SA.earlyTime p.toParams s) = some nd ∧
    holdsN p (actView nd.st) s N.erase = true) ∧
  (∀ y ∈ rho.honest, E.awake y (SA.earlyTime p.toParams s) = true →
    HonestAckAt p c E rho y s N.erase) ∧
  (∀ y ∈ rho.honest, PCStampedBefore p c E rho y (SA.freezeTime p.toParams s) s N.erase) ∧
  ((faulty rho).card < (awakeHonestLabel p c E rho s).card →
    ∀ y ∈ rho.honest, gateResultAt p c E rho y s = some (some N.erase))

theorem FormationConcl_def (s : Slot) (N : NamedProposal p.n) :
    FormationConcl p c E rho s N =
      ((∀ y H, HonestHeadAt p c E rho y s H → H = N.erase) ∧
      (∀ y ∈ rho.honest, ∃ nd, pcsa_postClock E rho y (SA.earlyTime p.toParams s) = some nd ∧
        holdsN p (actView nd.st) s N.erase = true) ∧
      (∀ y ∈ rho.honest, E.awake y (SA.earlyTime p.toParams s) = true →
        HonestAckAt p c E rho y s N.erase) ∧
      (∀ y ∈ rho.honest,
        PCStampedBefore p c E rho y (SA.freezeTime p.toParams s) s N.erase) ∧
      ((faulty rho).card < (awakeHonestLabel p c E rho s).card →
        ∀ y ∈ rho.honest, gateResultAt p c E rho y s = some (some N.erase))) := rfl

end Invariant

/-- [PC-SA claims, W0; pcsa34-r4 5.2.2 (CI), stage 1; plan C6] The joint clean
induction: in a run with a healthy prefix up to `b₀` (CLEAN(b₀): strict
delivery within `Δ`, rows `Δ_F`, `a < h_t`), `a < ⌈n/2⌉` (CL4 and
[pc-trumps §2] need `2q_N > n + a`) and the stage-1 frame, CI(j) holds for
every label `j` whose gate `d_j` is in the prefix. -/
def CleanInvariantClaim (p : Params) : Prop :=
  ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (pcsa p c)) (b₀ ΔF : Time),
    HealthyPrefix₂ p c E rho b₀ ΔF → FaultsBelowQA p c rho → StageOneFrame p c E rho →
    ∀ j : Slot, SA.gateTime p.toParams j ≤ b₀ → CleanInvariantAt p c E rho j

theorem CleanInvariantClaim_def (p : Params) : CleanInvariantClaim p =
    (∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
      (E : Generic.Env V) (rho : V2.D.Run V (pcsa p c)) (b₀ ΔF : Time),
      HealthyPrefix₂ p c E rho b₀ ΔF → FaultsBelowQA p c rho → StageOneFrame p c E rho →
      ∀ j : Slot, SA.gateTime p.toParams j ≤ b₀ → CleanInvariantAt p c E rho j) := by
  rw [CleanInvariantClaim]

/-- [PC-SA claims, W0; pcsa34-r4 5.3, PROVED under (F1)–(F7), a ≤ ⌊n/4⌋;
plan C7] Formation at a slot with an honest awake proposer: under the
premises (F1)–(F7) (`FormationPrem`, stage 1) the formation conclusion holds.
No CI premise: r4.3 discharges (F3), (F4) from CI in a clean run and from 5.6
in recovery. -/
def FormationClaim (p : Params) : Prop :=
  ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (pcsa p c)) (s : Slot) (N : NamedProposal p.n)
    (ΔF : Time),
    FormationPrem p c E rho s N ΔF → FormationConcl p c E rho s N

theorem FormationClaim_def (p : Params) : FormationClaim p =
    (∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
      (E : Generic.Env V) (rho : V2.D.Run V (pcsa p c)) (s : Slot) (N : NamedProposal p.n)
      (ΔF : Time),
      FormationPrem p c E rho s N ΔF → FormationConcl p c E rho s N) := by
  rw [FormationClaim]

/-- [PC-SA claims, W0; pcsa34-r4 5.2.3 Dissemination, stage 1; plan C14] An
honest ack `(s, B)` at `e_s` in a clean prefix gives every honest HEAD at
`v_{s+1}` `⪰ B` and every honest result at `d_{s+1}` `⪰ B`. Premises: CLEAN
up to `d_{s+1}`, `a < ⌈n/2⌉` ([pc-trumps §2]), stage-1 frame. -/
def CleanDisseminationClaim (p : Params) : Prop :=
  ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (pcsa p c)) (b₀ ΔF : Time),
    HealthyPrefix₂ p c E rho b₀ ΔF → FaultsBelowQA p c rho → StageOneFrame p c E rho →
    ∀ (s : Slot) (y : V) (B : Block), SA.gateTime p.toParams (s + 1) ≤ b₀ →
      HonestAckAt p c E rho y s B →
      (∀ x H, HonestHeadAt p c E rho x (s + 1) H → Block.Preceq B H) ∧
      (∀ x ∈ rho.honest, ∀ X, gateResultAt p c E rho x (s + 1) = some (some X) →
        Block.Preceq B X)

theorem CleanDisseminationClaim_def (p : Params) : CleanDisseminationClaim p =
    (∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
      (E : Generic.Env V) (rho : V2.D.Run V (pcsa p c)) (b₀ ΔF : Time),
      HealthyPrefix₂ p c E rho b₀ ΔF → FaultsBelowQA p c rho → StageOneFrame p c E rho →
      ∀ (s : Slot) (y : V) (B : Block), SA.gateTime p.toParams (s + 1) ≤ b₀ →
        HonestAckAt p c E rho y s B →
        (∀ x H, HonestHeadAt p c E rho x (s + 1) H → Block.Preceq B H) ∧
        (∀ x ∈ rho.honest, ∀ X, gateResultAt p c E rho x (s + 1) = some (some X) →
          Block.Preceq B X)) := by
  rw [CleanDisseminationClaim]

/-- [PC-SA claims, W0; pcsa34-r4 5.2.3 Clean safety, stage 1; plan C14] In a
clean prefix the honest available and strong reads are pairwise compatible
(across nodes and times) and monotone at each node (contract confirmedSafe,
stableSafe, monotone; nesting is `OutputNestingClaim`). Premises: CLEAN(b₀),
`a < ⌈n/2⌉`, stage-1 frame (r4.3: "PROVED modulo (vi) HAND for stage 2;
stage 1 has no (vi)"). -/
def PCSACleanSafetyClaim (p : Params) : Prop :=
  ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (pcsa p c)) (b₀ ΔF : Time),
    HealthyPrefix₂ p c E rho b₀ ΔF → FaultsBelowQA p c rho → StageOneFrame p c E rho →
    ∀ x ∈ rho.honest, ∀ y ∈ rho.honest, ∀ t t' : Time, 0 ≤ t → t ≤ b₀ → 0 ≤ t' → t' ≤ b₀ →
      Block.Compatible (confirmed (storeAt p c E rho x t)) (confirmed (storeAt p c E rho y t')) ∧
      Block.Compatible (strong (storeAt p c E rho x t)) (strong (storeAt p c E rho y t')) ∧
      (t ≤ t' →
        Block.Preceq (confirmed (storeAt p c E rho x t)) (confirmed (storeAt p c E rho x t')) ∧
        Block.Preceq (strong (storeAt p c E rho x t)) (strong (storeAt p c E rho x t')))

theorem PCSACleanSafetyClaim_def (p : Params) : PCSACleanSafetyClaim p =
    (∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
      (E : Generic.Env V) (rho : V2.D.Run V (pcsa p c)) (b₀ ΔF : Time),
      HealthyPrefix₂ p c E rho b₀ ΔF → FaultsBelowQA p c rho → StageOneFrame p c E rho →
      ∀ x ∈ rho.honest, ∀ y ∈ rho.honest, ∀ t t' : Time,
        0 ≤ t → t ≤ b₀ → 0 ≤ t' → t' ≤ b₀ →
        Block.Compatible (confirmed (storeAt p c E rho x t))
          (confirmed (storeAt p c E rho y t')) ∧
        Block.Compatible (strong (storeAt p c E rho x t)) (strong (storeAt p c E rho y t')) ∧
        (t ≤ t' →
          Block.Preceq (confirmed (storeAt p c E rho x t))
            (confirmed (storeAt p c E rho x t')) ∧
          Block.Preceq (strong (storeAt p c E rho x t)) (strong (storeAt p c E rho x t')))) := by
  rw [PCSACleanSafetyClaim]

/-- [PC-SA claims, W0; pcsa34-r4 5.2.3 Inclusion, D_c = 6Δ, stage 1; plan
C14] The honest proposal `P` of slot `u` (honest awake proposer) is below
every honest available read from the gate `d_u = t_u + 6Δ` to the end of the
clean prefix. Premises: CLEAN(b₀) with `d_u ≤ b₀`, `a < ⌈n/2⌉`, stage-1
frame. No `q_N` premise: inclusion in `S` needs `a < h_u` only. -/
def PCSACleanInclusionClaim (p : Params) : Prop :=
  ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (pcsa p c)) (b₀ ΔF : Time),
    HealthyPrefix₂ p c E rho b₀ ΔF → FaultsBelowQA p c rho → StageOneFrame p c E rho →
    ∀ (u : Slot) (P : Block),
      Gen.V2.Duty.HonestProposalAt E (pcsaInterface p c).toInterface rho u P →
      ∀ x ∈ rho.honest, ∀ t : Time, SA.gateTime p.toParams u ≤ t → t ≤ b₀ →
        Block.Preceq P (confirmed (storeAt p c E rho x t))

theorem PCSACleanInclusionClaim_def (p : Params) : PCSACleanInclusionClaim p =
    (∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
      (E : Generic.Env V) (rho : V2.D.Run V (pcsa p c)) (b₀ ΔF : Time),
      HealthyPrefix₂ p c E rho b₀ ΔF → FaultsBelowQA p c rho → StageOneFrame p c E rho →
      ∀ (u : Slot) (P : Block),
        Gen.V2.Duty.HonestProposalAt E (pcsaInterface p c).toInterface rho u P →
        ∀ x ∈ rho.honest, ∀ t : Time, SA.gateTime p.toParams u ≤ t → t ≤ b₀ →
          Block.Preceq P (confirmed (storeAt p c E rho x t))) := by
  rw [PCSACleanInclusionClaim]

/-- [PC-SA claims, W0; pcsa34-r4 5.2.3 Strong inclusion (3Δ), stage 1;
App. B strongIncluded; plan C9] The stage-1 form of the generic
`PCIncludedStatement` (`PCIncludedRegime` fields over `pcsa`): synchrony from
time 0 (`t_GST = 0`), an awake honest majority, full participation, the PC
fault cap `a ≤ ⌊n/4⌋`, and the stage-1 frame. Then every honest awake
proposal is in every honest strong read `3Δ` after its proposal time. The
generic instance without the frame premise is a stage-2 field. -/
def StrongIncludedClaim (p : Params) : Prop :=
  ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (pcsa p c)) (ΔF : Time),
    Base₂ p c E rho → Gen.V2.Duty.PartialSynchronyBy E rho (pcsaDelay p E.Δ ΔF) →
    E.Δ ≤ ΔF → E.t_GST = 0 →
    (∀ t, 0 ≤ t → t ≤ rho.horizon → Gen.V2.Duty.AwakeMajority E rho t) →
    Gen.V2.Duty.FullParticipation E rho 0 → QuarterCap p c rho → StageOneFrame p c E rho →
    Gen.V2.Duty.IncludedFrom E (pcsaInterface p c).toInterface rho (pcsaInterface p c).strong 0
      (3 * E.Δ)

theorem StrongIncludedClaim_def (p : Params) : StrongIncludedClaim p =
    (∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
      (E : Generic.Env V) (rho : V2.D.Run V (pcsa p c)) (ΔF : Time),
      Base₂ p c E rho → Gen.V2.Duty.PartialSynchronyBy E rho (pcsaDelay p E.Δ ΔF) →
      E.Δ ≤ ΔF → E.t_GST = 0 →
      (∀ t, 0 ≤ t → t ≤ rho.horizon → Gen.V2.Duty.AwakeMajority E rho t) →
      Gen.V2.Duty.FullParticipation E rho 0 → QuarterCap p c rho → StageOneFrame p c E rho →
      Gen.V2.Duty.IncludedFrom E (pcsaInterface p c).toInterface rho
        (pcsaInterface p c).strong 0 (3 * E.Δ)) := by
  rw [StrongIncludedClaim]

end AvailableChain.PCSA.Run

end
