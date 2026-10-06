module
public import AvailableChainPCSAClaims.Statements.LaneReads
public import AvailableChainPCSAClaims.Statements.Regimes

@[expose] public section

/-! [PC-SA claims, W0] Premise packages that more than one lane reads: the
formation premises (F1)–(F7) of pcsa34-r4 5.3 (Clean formation and Finality
source transfer) and the arming premise ARM(s, B, j₀) of 5.0/5.4 with its
conclusion (Outage persistence and the stage-2 stub). Statements only. -/

namespace AvailableChain.PCSA.Run

open AvailableChain.SimplexFG
open Gen.V2.Duty (faulty awakeHonest)

variable (p : Params) {In : Type} (c : AppCodec In) {V : Type} [DecidableEq V] [Fintype V]
    (E : Generic.Env V) (rho : V2.D.Run V (pcsa p c))

/-- [PC-SA claims, W0; pcsa34-r4 1.4] A wire object that is not an FG row
(HEAD, proposal, ack, PC). These objects have delay `Δ`; rows have `Δ_F`. -/
def IsNonRow {p : Params} (o : Obj p) : Prop :=
  match o.payload with
  | .row _ => False
  | _ => True

theorem pcsa_IsNonRow_def {p : Params} (o : Obj p) :
    IsNonRow o = (match o.payload with | .row _ => False | _ => True) := rfl

omit [Fintype V] in
/-- [PC-SA claims, W0; pcsa34-r4 3.10, 5.3] The honest proposal of slot `s`
is the named proposal `N`: the proposer of `s` is honest and emits `N` at
`t_s` (so it is awake then). `N.erase` is `P`, `N.pc` the carried PC. -/
def HonestNamedProposal (s : Slot) (N : NamedProposal p.n) : Prop :=
  V2.D.proposerOf rho (pcsaInterface p c).toInterface s ∈ rho.honest ∧
    V2.D.Run.emits E rho (V2.D.proposerOf rho (pcsaInterface p c).toInterface s)
      ⟨.seat ((pcsaInterface p c).propLabel s)
        (V2.D.propSeat (pcsaInterface p c).toInterface s), .proposal N⟩
      (V2.D.proposalTime (pcsaInterface p c).toInterface s)

omit [Fintype V] in
theorem pcsa_HonestNamedProposal_def (s : Slot) (N : NamedProposal p.n) :
    HonestNamedProposal p c E rho s N =
      (V2.D.proposerOf rho (pcsaInterface p c).toInterface s ∈ rho.honest ∧
        V2.D.Run.emits E rho (V2.D.proposerOf rho (pcsaInterface p c).toInterface s)
          ⟨.seat ((pcsaInterface p c).propLabel s)
            (V2.D.propSeat (pcsaInterface p c).toInterface s), .proposal N⟩
          (V2.D.proposalTime (pcsaInterface p c).toInterface s)) := rfl

/-- [PC-SA claims, W0; pcsa34-r4 5.3 premises (F1)–(F7)] The formation
premises at slot `s` with the honest proposal `N` (`P = N.erase`), stage 1.
- (F1) `delivery`: every non-row object sent or accepted at `t` reaches every
  honest node before `max t z_{s−1} + Δ` (r4.3: "within Δ, strict (so
  z_{s−1} ≥ t_GST)"; an object of an earlier time is held by `t_s`), up to `d_s`.
- (F2) `participation`: `h_s ≥ q_N` honest nodes awake at `v_s` and `e_s`.
- (F3) `commonView`: every honest voter's `view(s)` has the target of the
  carried PC `N.pc` (both `⊥` when `N.pc = ⊥`).
- (F4) `leases`: every live lease at an honest voter that is deeper than the
  view target (or `Z` without a view) and compatible with it is `⪯ parent(P)`.
- (F5) is not a field: r4.3 derives it from (F1) (p accepted the visited
  blocks before `t_s`, so they reach every voter before `v_s`).
- (F6), (F7) `frame`: stage 1, vacuous (`StageOneFrame`).
The fault cap is `a ≤ ⌊n/4⌋` (r4.3 §1.1, 5.3). -/
structure FormationPrem (s : Slot) (N : NamedProposal p.n) (ΔF : Time) : Prop where
  base : Base₂ p c E rho
  quarterCap : QuarterCap p c rho
  frame : StageOneFrame p c E rho
  slotPos : 0 < s
  horizon : SA.gateTime p.toParams s ≤ rho.horizon
  deltaF : E.Δ ≤ ΔF
  proposal : HonestNamedProposal p c E rho s N
  delivery : Gen.V2.Duty.DeliveryWithinOn E rho IsNonRow
    (fun t => max t (SA.freezeTime p.toParams (s - 1)) + E.Δ) (SA.gateTime p.toParams s)
  participation : nQuorum p.n ≤ (awakeHonestLabel p c E rho s).card
  commonView : ∀ y ∈ rho.honest, E.awake y (SA.voteTime p.toParams s) = true →
    (viewAt p c E rho y s).map (Option.map PC.target) = some (N.pc.map PC.target)
  leases : ∀ y ∈ rho.honest, E.awake y (SA.voteTime p.toParams s) = true →
    ∀ nd, pcsa_postClock E rho y (SA.voteTime p.toParams s) = some nd →
    ∀ B, LiveLease nd.st B →
      Block.Compatible B ((N.pc.map PC.target).getD (eraseFG (controls p nd.st).Z)) →
      ((N.pc.map PC.target).getD (eraseFG (controls p nd.st).Z)).depth < B.depth →
      Block.Preceq B N.erase.parent

/-- [PC-SA claims, W0; pcsa34-r4 5.0, 5.4.1 ARM(s, B, j₀)] (a) `PC(s, B)` is
stamped before `z_{j₀−1}` at every honest node; (b) every honest ack of a slot
in `[s + 1, j₀)` has a target `⪰ B`. Delivery after `v_{j₀}` is arbitrary. -/
structure Arm (s : Slot) (B : Block) (j₀ : Slot) : Prop where
  stamped : ∀ y ∈ rho.honest,
    PCStampedBefore p c E rho y (SA.freezeTime p.toParams (j₀ - 1)) s B
  acks : ∀ y s' X, s + 1 ≤ s' → s' < j₀ → HonestAckAt p c E rho y s' X → Block.Preceq B X

omit [Fintype V] in
/-- [PC-SA claims, W0; pcsa34-r4 5.4.1 Theorem] The persistence conclusion:
every honest HEAD at `v_j` (`j ≥ j₀`) is `⪰ B`; every honest ack of a slot
`≥ j₀` (hence every PC of that slot, 5.1) has a target `⪰ B`; from the time an
honest node holds `PC(s, B)`, its strong and available outputs are `⪰ B`. -/
def ArmConcl (s : Slot) (B : Block) (j₀ : Slot) : Prop :=
  (∀ j x H, j₀ ≤ j → HonestHeadAt p c E rho x j H → Block.Preceq B H) ∧
  (∀ j x X, j₀ ≤ j → HonestAckAt p c E rho x j X → Block.Preceq B X) ∧
  (∀ w ∈ rho.honest, ∀ t t' : Time, t ≤ t' →
    (∃ pc ∈ (storeAt p c E rho w t).pcs, pc.slot = s ∧ pc.target = B) →
    Block.Preceq B (strong (storeAt p c E rho w t')) ∧
      Block.Preceq B (confirmed (storeAt p c E rho w t')))

omit [Fintype V] in
theorem pcsa_ArmConcl_def (s : Slot) (B : Block) (j₀ : Slot) :
    ArmConcl p c E rho s B j₀ =
      ((∀ j x H, j₀ ≤ j → HonestHeadAt p c E rho x j H → Block.Preceq B H) ∧
      (∀ j x X, j₀ ≤ j → HonestAckAt p c E rho x j X → Block.Preceq B X) ∧
      (∀ w ∈ rho.honest, ∀ t t' : Time, t ≤ t' →
        (∃ pc ∈ (storeAt p c E rho w t).pcs, pc.slot = s ∧ pc.target = B) →
        Block.Preceq B (strong (storeAt p c E rho w t')) ∧
          Block.Preceq B (confirmed (storeAt p c E rho w t')))) := rfl

end AvailableChain.PCSA.Run

end
