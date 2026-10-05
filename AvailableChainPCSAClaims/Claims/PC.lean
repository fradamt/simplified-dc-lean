module
public import AvailableChainPCSAClaims.Statements.Reads
public import AvailableChainPCSAClaims.Statements.Regimes

@[expose] public section

/-! [PC-SA claims, M1] The Statements-layer claims of the PC path, as Props
with `_def` equations and no proofs (lead brief 2026-10-05). Each claim is
`∀ {V} [DecidableEq V] [Fintype V] {In} (c E rho), premise → conclusion`,
the FG-SA claim shape (`FGSAClaims/Claims/Foundations.lean`). The proof
phase proves them; the pure lemmas (`qN_head_unique`, `qA_honest`,
`preferPC_*`, `pcFloor_*`) are on the Generic PC branch. -/

namespace AvailableChain.PCSA.Run

open AvailableChain.SimplexFG

/-- [pcsa34-r3 5.1] PC uniqueness per slot: under fewer than `q_A` faults, two
PCs of one slot held by honest nodes at any times have one target. -/
def PCUniquenessClaim (p : Params) : Prop :=
  ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (pcsa p c)),
    Base₂ p c E rho → FaultsBelowQA p c rho →
    ∀ x ∈ rho.honest, ∀ y ∈ rho.honest, ∀ (t t' : Time),
      ∀ c₁ ∈ (storeAt p c E rho x t).pcs, ∀ c₂ ∈ (storeAt p c E rho y t').pcs,
        c₁.slot = c₂.slot → c₁.target = c₂.target

theorem PCUniquenessClaim_def (p : Params) : PCUniquenessClaim p =
    (∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
      (E : Generic.Env V) (rho : V2.D.Run V (pcsa p c)),
      Base₂ p c E rho → FaultsBelowQA p c rho →
      ∀ x ∈ rho.honest, ∀ y ∈ rho.honest, ∀ (t t' : Time),
        ∀ c₁ ∈ (storeAt p c E rho x t).pcs, ∀ c₂ ∈ (storeAt p c E rho y t').pcs,
          c₁.slot = c₂.slot → c₁.target = c₂.target) := by
  rw [PCUniquenessClaim]

/-- [pcsa34-r3 A6; lead ruling D1] One ack per seat per slot: an honest node
emits at most one ack object per slot and seat (one `ackAction s`, at `e_s`
only, one object per label and seat per tick). -/
def OneAckPerSlotClaim (p : Params) : Prop :=
  ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (pcsa p c)),
    V2.D.ExecutionValid E rho →
    ∀ x ∈ rho.honest, ∀ (s : Slot) (i : Fin p.n) (r r' : BlockId) (t t' : Time),
      V2.D.Run.emits E rho x (ackObj p s i r) t → V2.D.Run.emits E rho x (ackObj p s i r') t' →
      r = r' ∧ t = t' ∧ t = SA.earlyTime p.toParams s

theorem OneAckPerSlotClaim_def (p : Params) : OneAckPerSlotClaim p =
    (∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
      (E : Generic.Env V) (rho : V2.D.Run V (pcsa p c)),
      V2.D.ExecutionValid E rho →
      ∀ x ∈ rho.honest, ∀ (s : Slot) (i : Fin p.n) (r r' : BlockId) (t t' : Time),
        V2.D.Run.emits E rho x (ackObj p s i r) t →
        V2.D.Run.emits E rho x (ackObj p s i r') t' →
        r = r' ∧ t = t' ∧ t = SA.earlyTime p.toParams s) := by
  rw [OneAckPerSlotClaim]

/-- [pcsa34-r3 5.2, R4] PC dissemination before `z_s` under synchrony: when
`q_A` honest seats of slot `s` emit acks on one root at `e_s` and delivery is
healthy up to `z_s`, every honest node holds a PC of slot `s` on that root
after the ticks at `z_s` (so it is in every frozen view of slot `s + 1`).

Open premise (review 2026-10-06): `reconcile` drops a held PC whose target
conflicts with the new `F`, and `admitBlock` and `admitPC` only install a PC
whose target resolves in the node's tree. The claim therefore also needs the
PC target to stay `F`-compatible on every honest node up to `z_s`
(pcsa34-r3 5.4 states this as a premise). The statement below does not yet
carry that premise; whether it is derivable from `HealthyPrefix₂` or must be
added is open. -/
def PCDisseminationClaim (p : Params) : Prop :=
  ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (pcsa p c)) (b₀ ΔF : Time),
    HealthyPrefix₂ p c E rho b₀ ΔF → FaultsBelowQA p c rho →
    ∀ (s : Slot) (r : BlockId), SA.freezeTime p.toParams s ≤ b₀ →
      (∃ Q : Finset (Fin p.n), pcQuorum p.n ≤ Q.card ∧ ∀ i ∈ Q,
        rho.seatOf (.base (.ack s)) i ∈ rho.honest ∧
        V2.D.Run.emits E rho (rho.seatOf (.base (.ack s)) i) (ackObj p s i r)
          (SA.earlyTime p.toParams s)) →
      ∀ y ∈ rho.honest, ∃ c' ∈ (storeAfterTicks p c E rho y (SA.freezeTime p.toParams s)).pcs,
        c'.slot = s ∧ c'.target.root = r

theorem PCDisseminationClaim_def (p : Params) : PCDisseminationClaim p =
    (∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
      (E : Generic.Env V) (rho : V2.D.Run V (pcsa p c)) (b₀ ΔF : Time),
      HealthyPrefix₂ p c E rho b₀ ΔF → FaultsBelowQA p c rho →
      ∀ (s : Slot) (r : BlockId), SA.freezeTime p.toParams s ≤ b₀ →
        (∃ Q : Finset (Fin p.n), pcQuorum p.n ≤ Q.card ∧ ∀ i ∈ Q,
          rho.seatOf (.base (.ack s)) i ∈ rho.honest ∧
          V2.D.Run.emits E rho (rho.seatOf (.base (.ack s)) i) (ackObj p s i r)
            (SA.earlyTime p.toParams s)) →
        ∀ y ∈ rho.honest,
          ∃ c' ∈ (storeAfterTicks p c E rho y (SA.freezeTime p.toParams s)).pcs,
            c'.slot = s ∧ c'.target.root = r) := by
  rw [PCDisseminationClaim]

/-- [pcsa34-r3 3.2, R7] Output nesting at every honest node and time:
`strong ⪯ available` and `F ⪯ available` (erased). No fault premise. -/
def OutputNestingClaim (p : Params) : Prop :=
  ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (pcsa p c)),
    V2.D.ExecutionValid E rho →
    ∀ x ∈ rho.honest, ∀ t : Time,
      Block.Preceq (strong (storeAt p c E rho x t)) (confirmed (storeAt p c E rho x t)) ∧
      Block.Preceq (eraseFG (storeAt p c E rho x t).fg.F) (confirmed (storeAt p c E rho x t))

theorem OutputNestingClaim_def (p : Params) : OutputNestingClaim p =
    (∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
      (E : Generic.Env V) (rho : V2.D.Run V (pcsa p c)),
      V2.D.ExecutionValid E rho →
      ∀ x ∈ rho.honest, ∀ t : Time,
        Block.Preceq (strong (storeAt p c E rho x t)) (confirmed (storeAt p c E rho x t)) ∧
        Block.Preceq (eraseFG (storeAt p c E rho x t).fg.F)
          (confirmed (storeAt p c E rho x t))) := by
  rw [OutputNestingClaim]

/-- [pcsa34-r3 5.4, 5.8; SA clean safety] Available monotonicity on a healthy
prefix: at an honest node, the available output at `t ≤ t'` within the
prefix is below the available output at `t'`. -/
def AvailableMonotoneClaim (p : Params) : Prop :=
  ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (pcsa p c)) (b₀ ΔF : Time),
    HealthyPrefix₂ p c E rho b₀ ΔF → FaultsBelowQA p c rho →
    ∀ x ∈ rho.honest, ∀ (t t' : Time), 0 ≤ t → t ≤ t' → t' ≤ b₀ →
      Block.Preceq (confirmed (storeAt p c E rho x t)) (confirmed (storeAt p c E rho x t'))

theorem AvailableMonotoneClaim_def (p : Params) : AvailableMonotoneClaim p =
    (∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
      (E : Generic.Env V) (rho : V2.D.Run V (pcsa p c)) (b₀ ΔF : Time),
      HealthyPrefix₂ p c E rho b₀ ΔF → FaultsBelowQA p c rho →
      ∀ x ∈ rho.honest, ∀ (t t' : Time), 0 ≤ t → t ≤ t' → t' ≤ b₀ →
        Block.Preceq (confirmed (storeAt p c E rho x t))
          (confirmed (storeAt p c E rho x t'))) := by
  rw [AvailableMonotoneClaim]

/-- [PC-SA claims, M1] The five claims of the PC path, as one record. -/
structure PCSAPCClaims (p : Params) : Prop where
  pcUnique : PCUniquenessClaim p
  oneAck : OneAckPerSlotClaim p
  dissemination : PCDisseminationClaim p
  outputNesting : OutputNestingClaim p
  availableMonotone : AvailableMonotoneClaim p

end AvailableChain.PCSA.Run
end
