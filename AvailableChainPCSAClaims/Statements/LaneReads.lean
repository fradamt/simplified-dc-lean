module
public import AvailableChainPCSAClaims.Statements.Reads
public import AvailableChainGeneric.Statements.V2.Duty.Counts

@[expose] public section

/-! [PC-SA claims, W0] The run reads of the lane claims (pcsa-proof-plan §3).
Each read is a deterministic function of the run: a duty read is taken on the
post-clock state of the node's tick (`pcsa_postClock`), so it is defined also
for a node that is asleep at the duty time; a claim that is about a sent object
adds the awake premise. The copied generic reads stay in `Reads.lean` (the FG
lift replaces them there). -/

namespace AvailableChain.PCSA.Run

open AvailableChain.SimplexFG
open Gen.V2.Duty (awakeHonest)

variable (p : Params) {In : Type} (c : AppCodec In) {V : Type} [DecidableEq V]
    (E : Generic.Env V) (rho : V2.D.Run V (pcsa p c))

/-- [PC-SA claims, W0] The store of node `x` before event `i` (every event
state, also inside one time). -/
def storeBefore (i : Nat) (x : V) : State p.n :=
  (V2.D.Run.stateBefore E rho i x).st

theorem pcsa_storeBefore_def (i : Nat) (x : V) :
    storeBefore p c E rho i x = (V2.D.Run.stateBefore E rho i x).st := rfl

/-- [PC-SA claims, W0; pcsa34-r4 1.2, 3.10] The HEAD of node `x` at `v_s`:
`goldfish_vote` on the post-clock state of the tick at `v_s`. -/
def voteHeadAt (x : V) (s : Slot) : Option Block :=
  (pcsa_postClock E rho x (SA.voteTime p.toParams s)).map (fun nd => headVote p nd.st s)

theorem pcsa_voteHeadAt_def (x : V) (s : Slot) :
    voteHeadAt p c E rho x s =
      (pcsa_postClock E rho x (SA.voteTime p.toParams s)).map
        (fun nd => headVote p nd.st s) := rfl

/-- [PC-SA claims, W0; pcsa34-r4 3.3] `view(Σ, s)` of node `x`, read at `v_s`. -/
def viewAt (x : V) (s : Slot) : Option (Option (PC p.n)) :=
  (pcsa_postClock E rho x (SA.voteTime p.toParams s)).map (fun nd => voterPC p nd.st s)

theorem pcsa_viewAt_def (x : V) (s : Slot) :
    viewAt p c E rho x s =
      (pcsa_postClock E rho x (SA.voteTime p.toParams s)).map
        (fun nd => voterPC p nd.st s) := rfl

/-- [PC-SA claims, W0; pcsa34-r4 3.3 live_root] `live_root(Σ, s)` of node `x`,
read at `v_s` with the slot-`s` view. -/
def liveRootAt (x : V) (s : Slot) : Option Block :=
  (pcsa_postClock E rho x (SA.voteTime p.toParams s)).map
    (fun nd => liveRoot p nd.st (voterPC p nd.st s))

theorem pcsa_liveRootAt_def (x : V) (s : Slot) :
    liveRootAt p c E rho x s =
      (pcsa_postClock E rho x (SA.voteTime p.toParams s)).map
        (fun nd => liveRoot p nd.st (voterPC p nd.st s)) := rfl

/-- [PC-SA claims, W0; pcsa34-r4 3.4 A1] The N target of slot `s` at node `x`,
read at `e_s`. -/
def nTargetAt (x : V) (s : Slot) : Option (Option Block) :=
  (pcsa_postClock E rho x (SA.earlyTime p.toParams s)).map (fun nd => nTarget? p nd.st s)

theorem pcsa_nTargetAt_def (x : V) (s : Slot) :
    nTargetAt p c E rho x s =
      (pcsa_postClock E rho x (SA.earlyTime p.toParams s)).map
        (fun nd => nTarget? p nd.st s) := rfl

/-- [PC-SA claims, W0; pcsa34-r4 3.4, 3.8] The ack decision of node `x` at
`e_s` (A1 and A2; A6 is the duty schedule). The tick at `e_s` runs the gate of
`s − 1` first, so the read is after that gate. -/
def ackAt (x : V) (s : Slot) : Option (Option Block) :=
  (pcsa_postClock E rho x (SA.earlyTime p.toParams s)).map (fun nd => ackFor p nd.st s)

theorem pcsa_ackAt_def (x : V) (s : Slot) :
    ackAt p c E rho x s =
      (pcsa_postClock E rho x (SA.earlyTime p.toParams s)).map
        (fun nd => ackFor p nd.st s) := rfl

/-- [PC-SA claims, W0; pcsa34-r4 3.8] An honest ack `(s, B)`: node `x` is
honest, awake at `e_s`, and its ack decision is `B` (the ack duty then sends
`(i, s, B)` for its seat `i`). -/
def HonestAckAt (x : V) (s : Slot) (B : Block) : Prop :=
  x ∈ rho.honest ∧ E.awake x (SA.earlyTime p.toParams s) = true ∧
    ackAt p c E rho x s = some (some B)

theorem pcsa_HonestAckAt_def (x : V) (s : Slot) (B : Block) :
    HonestAckAt p c E rho x s B =
      (x ∈ rho.honest ∧ E.awake x (SA.earlyTime p.toParams s) = true ∧
        ackAt p c E rho x s = some (some B)) := rfl

/-- [PC-SA claims, W0; pcsa34-r4 1.2] An honest HEAD of label `s`: node `x` is
honest, awake at `v_s`, and its HEAD at `v_s` is `H`. -/
def HonestHeadAt (x : V) (s : Slot) (H : Block) : Prop :=
  x ∈ rho.honest ∧ E.awake x (SA.voteTime p.toParams s) = true ∧
    voteHeadAt p c E rho x s = some H

theorem pcsa_HonestHeadAt_def (x : V) (s : Slot) (H : Block) :
    HonestHeadAt p c E rho x s H =
      (x ∈ rho.honest ∧ E.awake x (SA.voteTime p.toParams s) = true ∧
        voteHeadAt p c E rho x s = some H) := rfl

/-- [PC-SA claims, W0; FG-SA gateIn] The gate input of label `s` at node `x`:
the clock steps before the gate at `d_s`. -/
def gateInAt (x : V) (s : Slot) : Option (State p.n) :=
  (pcsa_preTick E rho x (SA.gateTime p.toParams s)).map
    (fun nd => clockPre p nd.st (SA.gateTime p.toParams s))

theorem pcsa_gateInAt_def (x : V) (s : Slot) :
    gateInAt p c E rho x s =
      (pcsa_preTick E rho x (SA.gateTime p.toParams s)).map
        (fun nd => clockPre p nd.st (SA.gateTime p.toParams s)) := rfl

/-- [PC-SA claims, W0; pcsa34-r4 3.7, 5.0 R_u(j); FG-SA gateResult] The raw
gate result `R_x(s)` of label `s` at node `x`, before the guard: the walk from
`F` over the active view. `some none` is an empty result. -/
def gateResultAt (x : V) (s : Slot) : Option (Option Block) :=
  (gateInAt p c E rho x s).map (fun st =>
    SA.Root.confirmationFrom p.toParams (eraseFG st.fg.F) (actView st) s)

theorem pcsa_gateResultAt_def (x : V) (s : Slot) :
    gateResultAt p c E rho x s =
      (gateInAt p c E rho x s).map (fun st =>
        SA.Root.confirmationFrom p.toParams (eraseFG st.fg.F) (actView st) s) := rfl

/-- [PC-SA claims, W0; pcsa34-r4 1.4, 3.3] `PC(s, B)` is stamped before the
tick time `t` at node `y`: it is held after the ticks at `t`, before the
deliveries at `t` (an object accepted strictly before a tick time has a stamp
below it; the freeze at `t` reads exactly these PCs). -/
def PCStampedBefore (y : V) (t : Time) (s : Slot) (B : Block) : Prop :=
  ∃ c' ∈ (storeAfterTicks p c E rho y t).pcs, c'.slot = s ∧ c'.target = B

theorem pcsa_PCStampedBefore_def (y : V) (t : Time) (s : Slot) (B : Block) :
    PCStampedBefore p c E rho y t s B =
      (∃ c' ∈ (storeAfterTicks p c E rho y t).pcs, c'.slot = s ∧ c'.target = B) := rfl

/-- [PC-SA claims, W0; pcsa34-r4 3.9, R8′] The FG source `C_fg` of node `x` at
the action time `a_r` of round `r`. -/
def actionSourceAt (x : V) (r : Nat) : Option (Option (FGBlock (Fin p.n))) :=
  (pcsa_postClock E rho x (p.actionTime r)).map (fun nd => fgSource p nd.st)

theorem pcsa_actionSourceAt_def (x : V) (r : Nat) :
    actionSourceAt p c E rho x r =
      (pcsa_postClock E rho x (p.actionTime r)).map (fun nd => fgSource p nd.st) := rfl

/-- [PC-SA claims, W0; pcsa34-r4 5.0 h_j] The honest nodes awake at `v_s` and
at `e_s`. -/
def awakeHonestLabel (s : Slot) : Finset V :=
  awakeHonest E rho (SA.voteTime p.toParams s) ∩ awakeHonest E rho (SA.earlyTime p.toParams s)

theorem pcsa_awakeHonestLabel_def (s : Slot) :
    awakeHonestLabel p c E rho s =
      awakeHonest E rho (SA.voteTime p.toParams s) ∩
        awakeHonest E rho (SA.earlyTime p.toParams s) := rfl

end AvailableChain.PCSA.Run

namespace AvailableChain.PCSA

/-- [PC-SA claims, W0; pcsa34-r4 3.1, 3.7] A live lease on `B` in the store:
a lease row on `B` whose deadline is after the store time. -/
def LiveLease {n : Nat} (st : State n) (B : Block) : Prop :=
  ∃ row ∈ st.base.obligations, row.1 = B ∧ st.base.now < row.2.2

theorem pcsa_LiveLease_def {n : Nat} (st : State n) (B : Block) :
    LiveLease st B = (∃ row ∈ st.base.obligations, row.1 = B ∧ st.base.now < row.2.2) := rfl

end AvailableChain.PCSA

end
