module
public import AvailableChainFGSAProofs.Proofs.Shared.Channels
public import AvailableChainFGSAClaims.Statements.Regimes
public import AvailableChainFGSARun.Proofs.ClientTrace
public import AvailableChainFGSARun.Proofs.EmissionWellFormed
public import AvailableChainGeneric.Proofs.V2.Signatures

public section

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

variable (p : Params) {In V : Type} [DecidableEq V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.Run V (fgsa p c))

/-- bp.clientSafety.v1: T7.9 A, including runs with restarts.
The claim type is applied only at the Foundations export boundary (L42). -/
theorem fgsa_clientSafeAll (hL : V2.Linked (fgsaFamilies p c).linked rho) :
    ∀ x ∈ rho.honest, EmittedRowsNoSlash p c E rho x :=
  emittedRowsNoSlash E rho hL

private theorem row_at_seat {j : Nat} {x : V} {r : Nat} {a : RowWire p.n}
    (ha : HonestRowAt p c E rho j x r a) :
    ∃ i body, a = ⟨.seat (.fg r) i, body⟩ ∧
      rho.events[j]? = some (.tick x (p.actionTime r)) ∧
      rho.seatOf (.base (.fg r)) i = x ∧
      ofRow p a ∈ V2.Run.emitsAt E rho j := by
  rw [HonestRowAt_def] at ha
  obtain ⟨_, hr, t, hj, hem⟩ := ha
  rcases a with ⟨auth, body⟩
  cases auth with
  | none => cases hr
  | proposer s => cases hr
  | seat label i =>
    cases label with
    | head s => cases hr
    | fg r' =>
      have he : r' = r := Option.some.inj hr
      subst r'
      have hrow := (fgsa_emitsAt_row E rho j x t hj r i body).mp hem
      exact ⟨i, body, rfl, hrow.2.1 ▸ hj, hrow.2.2.1, hem⟩

-- The frozen BaseSet package takes Fintype, although its fields do not use it.
set_option linter.unusedFintypeInType false in
/-- P3 §6, 22 §1: one signed row per honest identity and round.
G12 gives signed-object uniqueness; T7.6 gives tick uniqueness and totality;
T7.9 B gives row validity. F0.8a supplies the row and signer channels. -/
theorem honest_one_row_per_round [Fintype V] (hb : BaseSet p c E rho) :
    ∀ x ∈ rho.honest, ∀ r : Nat,
      (∀ (j j' : Nat) (a a' : RowWire p.n), HonestRowAt p c E rho j x r a →
        HonestRowAt p c E rho j' x r a' → j = j' ∧ a = a') ∧
      (p.actionTime r ≤ rho.horizon → E.awake x (p.actionTime r) = true →
        ∃ (j : Nat) (a : RowWire p.n), HonestRowAt p c E rho j x r a ∧
          RowComplete p c rho x r a) := by
  intro x hx r
  have hseat := hb.linked.toCStar (.base (.fg r)) trivial
  constructor
  · intro j j' a a' ha ha'
    obtain ⟨i, body, he, hj, hi, hem⟩ := row_at_seat p c E rho ha
    obtain ⟨i', body', he', hj', hi', hem'⟩ := row_at_seat p c E rho ha'
    have hii : i' = i := hseat.1 (hi'.trans hi.symm)
    subst i'
    subst a
    subst a'
    have ho := Gen.V2.honest_unique_per_label E rho hb.valid.nodup
      hb.valid.toUnforgeableSignatures (fgsaHooks p c).handles_carries
      (.base (.fg r)) i (hi.symm ▸ hx)
      (ofRow p ⟨.seat (.fg r) i, body⟩) (ofRow p ⟨.seat (.fg r) i, body'⟩)
      rfl rfl (Or.inl ⟨p.actionTime r, hi.symm ▸ ⟨j, hj, hem⟩⟩)
      (Or.inl ⟨p.actionTime r, hi.symm ▸ ⟨j', hj', hem'⟩⟩)
    have hbodies : body = body' := Msg.row.inj (congrArg V2.Signed.payload ho)
    exact ⟨fgsa_tick_unique E rho hb.valid.toScheduleWellFormed hj hj',
      congrArg (fun b => (⟨.seat (.fg r) i, b⟩ : RowWire p.n)) hbodies⟩
  · intro hh hawake
    have ht : p.actionTime r = ((4 * (r * p.R) + 6 : Nat) : Time) * p.Δ := by
      change 4 * p.Δ * ((r * p.R : Nat) : Time) + 6 * p.Δ = _
      push_cast
      ring
    obtain ⟨j, hj, _⟩ := fgsa_tick_total E rho hb.valid.toScheduleWellFormed
      hb.delta x hx (4 * (r * p.R) + 6) (ht ▸ hh)
    rw [← ht] at hj
    obtain ⟨i, hi⟩ := hseat.2 x
    let body := (attest p (FGSA.clock p (V2.Run.stateBefore E rho j x).st
      (p.actionTime r)) (V2.Run.stateBefore E rho j x).record ⟨0, p.nPos⟩).1
    let a : RowWire p.n := ⟨.seat (.fg r) i, body⟩
    have hem : ofRow p a ∈ V2.Run.emitsAt E rho j :=
      (fgsa_emitsAt_row E rho j x (p.actionTime r) hj r i body).mpr
        ⟨hawake, rfl, hi, rfl⟩
    have hv := honest_emit_wellFormed E rho hb.valid.toDeliveryWellFormed
      hb.valid.toScheduleWellFormed j x (p.actionTime r) hj hx hawake (ofRow p a) hem
    have hvalid : a.valid = true := hv
    have hr : a.round? = some r := rfl
    have hsigner : RowSigner p c rho a x :=
      (rowSigner_iff_holder p c rho a x).mpr ⟨⟨r, i, rfl⟩, congrArg some hi⟩
    exact ⟨j, a, ⟨hx, hr, p.actionTime r, hj, hem⟩, hvalid, hr, hsigner⟩

end AvailableChain.FGSA.Run
end
