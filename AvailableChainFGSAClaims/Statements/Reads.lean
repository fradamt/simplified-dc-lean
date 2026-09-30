module
public import AvailableChainGeneric.Statements.V2.Reads -- shake: keep (Claims import policy)

@[expose] public section

/-! Generic reads over the real v2 engine (P3 F0.1). -/

namespace AvailableChain.FGSA.Run

variable {V : Type} {In : Type} {P : V2.ProtocolSpec In}

/-- Include earlier events and the restarts and ticks at `t`, before deliveries. -/
def cutPred (t : Time) (e : V2.Event V P.Object) : Bool :=
  decide (e.key ≤ toLex (t, 1))

/-- The event index after all ticks at `t`. -/
def afterTicksIdx (rho : V2.Run V P) (t : Time) : Nat :=
  (rho.events.filter (cutPred t)).length

/-- Event states in the suffix that starts at the post-gate cut. -/
def SuffixIdx (rho : V2.Run V P) (t : Time) (i : Nat) : Prop :=
  afterTicksIdx rho t ≤ i ∧ i ≤ rho.events.length

/-- The inclusive event index at `t`. -/
def timeIdx (rho : V2.Run V P) (t : Time) : Nat :=
  (rho.events.filter (fun e => decide (e.time ≤ t))).length

variable [DecidableEq V]

/-- The world after all ticks at `t`, before its deliveries. -/
def afterTicks (E : Generic.Env V) (rho : V2.Run V P) (t : Time) : V2.World V P :=
  (rho.events.filter (cutPred t)).foldl (V2.World.step E rho) V2.World.init

/-- The local state before the node's tick, if that tick exists. -/
def preTick (E : Generic.Env V) (rho : V2.Run V P) (v : V) (t : Time) : Option P.State :=
  (V2.Run.tickIdx? rho v t).map (fun i => V2.Run.stateBefore E rho i v)

/-- The local state after the clock, before the own record. -/
def postClock (E : Generic.Env V) (rho : V2.Run V P) (v : V) (t : Time) : Option P.State :=
  (preTick E rho v t).map (fun nd => P.clock nd t)

/-- The local state after the node's complete tick, if that tick exists. -/
def postTick (E : Generic.Env V) (rho : V2.Run V P) (v : V) (t : Time) : Option P.State :=
  (V2.Run.tickIdx? rho v t).map (fun i => V2.Run.stateBefore E rho (i + 1) v)

end AvailableChain.FGSA.Run

end
