module
public import AvailableChainFGSARun.Proofs.ClockLaws
public import AvailableChainGeneric.Proofs.V2.Fields

public section
namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG
open AvailableChain.V2.Engine
variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

/-- The record fold includes all ticks before `i`, across restarts. -/
theorem ownRecord_fold_run (E : Generic.Env V) (rho : V2.Run V (fgsa p c))
    (i : Nat) (v : V) :
    (V2.Run.stateBefore E rho i v).record =
      (ownReleased E rho v 0 i).foldl (recordRow? p) Record.initial := by
  have h := Gen.V2.ownRecord_fold_restart (P := fgsa p c) Node.record (recordRow? p)
    clock_rec process_rec recordOwn_rec E rho (Nat.zero_le i) v
    (fun k _ _ _ _ => restore_rec (V2.Run.stateBefore E rho k v).record)
  exact h

/-- Exact HEAD emission at any tick. -/
theorem fgsa_emits_head (E : Generic.Env V) (rho : V2.Run V (fgsa p c))
    (nd : Node p) (v : V) (t : Time) (s : Slot) (j : Fin p.n) (b : Block) :
    (⟨.seat (.base (.head s)) j, .head b⟩ : Obj p) ∈ (V2.tick E rho nd v t).2 ↔
      E.awake v t = true ∧ SA.voteTime p.toParams s = t ∧
      rho.seatOf (.base (.head s)) j = v ∧ b = headVote p (FGSA.clock p nd.st t) s := by
  refine (mem_tick_seat_iff (P := fgsa p c) E rho nd v t (.base (.head s)) j (.head b)).trans ?_
  dsimp only [fgsa, act, actS]
  simp only [Option.some.injEq, Msg.head.injEq]
  exact and_congr_right fun _ => and_congr_right fun _ => and_congr_right fun _ => eq_comm

/-- Exact FG row emission, with its round and seat retained. -/
theorem fgsa_emits_row (E : Generic.Env V) (rho : V2.Run V (fgsa p c))
    (nd : Node p) (v : V) (t : Time) (r : Nat) (j : Fin p.n) (body : RowBody) :
    ofRow p ⟨.seat (.fg r) j, body⟩ ∈ (V2.tick E rho nd v t).2 ↔
      E.awake v t = true ∧ p.actionTime r = t ∧ rho.seatOf (.base (.fg r)) j = v ∧
      body = (attest p (FGSA.clock p nd.st t) nd.record ⟨0, p.nPos⟩).1 := by
  change (⟨.seat (.base (.fg r)) j, .row body⟩ : Obj p) ∈ _ ↔ _
  refine (mem_tick_seat_iff (P := fgsa p c) E rho nd v t (.base (.fg r)) j (.row body)).trans ?_
  dsimp only [fgsa, act]
  simp only [Option.some.injEq, Msg.row.injEq]
  exact and_congr_right fun _ => and_congr_right fun _ => and_congr_right fun _ => eq_comm

/-- Exact row emission at a tick event in the run. -/
theorem fgsa_emitsAt_row (E : Generic.Env V) (rho : V2.Run V (fgsa p c))
    (k : Nat) (v : V) (t : Time) (hk : rho.events[k]? = some (.tick v t))
    (r : Nat) (j : Fin p.n) (body : RowBody) :
    ofRow p ⟨.seat (.fg r) j, body⟩ ∈ V2.Run.emitsAt E rho k ↔
      E.awake v t = true ∧ p.actionTime r = t ∧ rho.seatOf (.base (.fg r)) j = v ∧
      body = (attest p (FGSA.clock p (V2.Run.stateBefore E rho k v).st t)
        (V2.Run.stateBefore E rho k v).record ⟨0, p.nPos⟩).1 := by
  have ht := (V2.Run.step_tick_eq E rho hk).2
  exact (congrArg (fun xs => ofRow p ⟨.seat (.fg r) j, body⟩ ∈ xs) ht).to_iff.trans
    (fgsa_emits_row E rho (V2.Run.stateBefore E rho k v) v t r j body)

/-- Exact proposal emission, including the application body. -/
theorem fgsa_emits_proposal (E : Generic.Env V) (rho : V2.Run V (fgsa p c))
    (nd : Node p) (v : V) (t : Time) (s : Slot) (m : Msg p.n) :
    (⟨.seat (.prop s) ⟨0, Nat.one_pos⟩, m⟩ : Obj p) ∈ (V2.tick E rho nd v t).2 ↔
      E.awake v t = true ∧ SA.proposalTime p.toParams s = t ∧
      rho.seatOf (.prop s) ⟨0, Nat.one_pos⟩ = v ∧
      (propose p (FGSA.clock p nd.st t) s).map (withApp (c.app (rho.input v t))) = some m :=
  mem_tick_seat_iff E rho nd v t (.prop s) ⟨0, Nat.one_pos⟩ m

/-- Sleep releases no object and keeps the record. -/
theorem fgsa_tick_asleep (E : Generic.Env V) (rho : V2.Run V (fgsa p c))
    (nd : Node p) (v : V) (t : Time) (h : E.awake v t = false) :
    (V2.tick E rho nd v t).2 = [] ∧ (V2.tick E rho nd v t).1.record = nd.record := by
  rw [V2.tick_asleep E rho nd h]
  exact ⟨rfl, rfl⟩

/-- The wire decoder recovers the client row with the actual seat. -/
theorem fgsa_attest_decode (st : State p.n) (Λ : Record) (r : Nat) (j : Fin p.n) :
    RowWire.toRow? (⟨.seat (.fg r) j, (attest p st Λ ⟨0, p.nPos⟩).1⟩ : RowWire p.n) =
      some (createRow p.E p.cfg Λ j (fgInputs p st).1 (fgInputs p st).2).1 := rfl

/-- A carried honest row has an earlier emission by its holder. -/
theorem fgsa_carried_row (E : Generic.Env V) (rho : V2.Run V (fgsa p c))
    (h : V2.UnforgeableSignatures E rho) (v u : V) (o : Obj p) (t : Time)
    (hp : V2.Run.processes rho v o t) (a : RowWire p.n)
    (hc : (fgsa p c).carries o (ofRow p a)) (hu : u ∈ rho.honest)
    (hh : V2.Run.holder rho (ofRow p a).auth = some u) :
    ∃ t', t' ≤ t ∧ V2.Run.emits E rho u (ofRow p a) t' :=
  h.carried v o t hp (ofRow p a) hc u hu hh

end AvailableChain.FGSA.Run
end
