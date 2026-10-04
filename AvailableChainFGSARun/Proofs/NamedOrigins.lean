module
public import AvailableChainFGSARun.Proofs.NamedScope
public import AvailableChainFGSARun.Statements.Interface
public import AvailableChainFGSARun.Statements.Emission
public import AvailableChainGeneric.Statements.V2.Duty.DeliveryBy

public section

namespace AvailableChain.FGSA.Run
variable {p : Params} {In V : Type} {c : AppCodec In} [DecidableEq V]

/-- [ROOT-DIGEST-2 W1; DC NamedReceiptCalls] A proposal call is a direct delivery. -/
theorem proposal_handlesS_direct (st : State p.n) (parent o : Obj p)
    (s : Slot) (N : NamedProposal p.n)
    (hd : (toWire p o).decode = some (.block s N))
    (hh : handlesS p st parent o) : parent = o := by
  rcases hh with h | h
  · exact h
  · cases hp : (toWire p parent).decode with
    | none => simp only [hp] at h
    | some m =>
      cases m with
      | vote r i B => simp only [hp] at h
      | row i body => simp only [hp] at h
      | block r B =>
        rw [hp] at h
        rcases h.2 with hm | hm
        · obtain ⟨a, _, rfl⟩ := List.mem_map.mp hm
          rcases a with ⟨⟨(_ | _), _⟩ | _ | _, _⟩ <;> simp [toWire, ofHead, ofWire, ofAuth,
            toAuth, Wire.decode] at hd
        · obtain ⟨a, _, rfl⟩ := List.mem_map.mp hm
          rcases a with ⟨⟨(_ | _), _⟩ | _ | _, _⟩ <;> simp [toWire, ofRow, ofWire, ofAuth, toAuth,
            Wire.decode] at hd

/-- [ROOT-DIGEST-2 W1; DC NamedRun.blockInRun] A proposal handler scopes its body. -/
theorem proposal_handle_in_scope (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (o : Obj p) (s : Slot) (N : NamedProposal p.n)
    (ho : o = ofWire p ⟨.proposer s, .proposal N⟩)
    (j : Nat) (w : V) (t : Time) (hh : V2.D.Run.handlesAt E rho j w o t) :
    NamedProposalInRun p c E rho N := by
  obtain ⟨parent, hevent, hcall⟩ := hh
  have hd : (toWire p o).decode = some (.block s N) := by
    rw [ho]
    rfl
  have hp := proposal_handlesS_direct _ parent o s N hd hcall
  subst parent
  refine ⟨N, Or.inl ⟨w, o, t, ?_, ?_⟩, named_preceq_refl N⟩
  · exact List.mem_of_getElem? hevent
  · rw [ho]
    rfl

/-- [ROOT-DIGEST-2 W1; DC NamedReceiptCalls] Broadcast or source acceptance scopes a trigger.
This proof uses no root idealization or processed-to-body inference. -/
theorem proposal_trigger_in_scope
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (o : Obj p) (s : Slot) (N : NamedProposal p.n)
    (ho : o = ofWire p ⟨.proposer s, .proposal N⟩)
    (dl : Time → Time) (cut t : Time) (w : V)
    (hD : Gen.V2.Duty.DeliveryWithinOn E rho (fun o => ¬ isRowObject o) dl cut)
    (hT : Gen.V2.Duty.Trigger E rho o t) (hw : w ∈ rho.honest)
    (hcut : dl t ≤ cut)
    (hNX : (fgsa p c).excludes (V2.D.Run.stateBeforeTime E rho (dl t) w) o = false) :
    NamedProposalInRun p c E rho N := by
  rcases hT with ⟨v, hv, hemit⟩ | ⟨v, _, i, haccept⟩
  · have hQ : ¬ isRowObject o := by
      rw [ho]
      simp [isRowObject, ofWire]
    obtain ⟨t', _, _, j, hh⟩ := hD.broadcast v hv o hQ t hemit w hw hcut hNX
    exact proposal_handle_in_scope E rho o s N ho j w t' hh
  · exact proposal_handle_in_scope E rho o s N ho i v t haccept.1

/-- [ROOT-DIGEST-2 W1; DC NamedRun.blockInRun] Trigger scope retains the Block projection. -/
theorem proposal_trigger_in_root_scope
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (o : Obj p) (s : Slot) (N : NamedProposal p.n)
    (ho : o = ofWire p ⟨.proposer s, .proposal N⟩)
    (dl : Time → Time) (cut t : Time) (w : V)
    (hD : Gen.V2.Duty.DeliveryWithinOn E rho (fun o => ¬ isRowObject o) dl cut)
    (hT : Gen.V2.Duty.Trigger E rho o t) (hw : w ∈ rho.honest)
    (hcut : dl t ≤ cut)
    (hNX : (fgsa p c).excludes (V2.D.Run.stateBeforeTime E rho (dl t) w) o = false) :
    RootBlockInRun p c E rho N.erase :=
  ⟨N, proposal_trigger_in_scope E rho o s N ho dl cut t w hD hT hw hcut hNX, rfl⟩

/-- [ROOT-DIGEST-2 W1; DC NamedBlocks] Every emitted payload has its exact parent held. -/
theorem emitted_payload_parent_stored (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {x : V} {o : Obj p} {t : Time}
    {N : NamedProposal p.n}
    (hem : V2.D.Run.emits E rho x o t) (ho : o.payload = .proposal N) :
    ∃ i, N.parent ∈ (V2.D.Run.stateBefore E rho i x).st.namedBodies := by
  obtain ⟨i, hi, hemit⟩ := hem
  rw [(V2.D.Run.step_tick_eq E rho hi).2] at hemit
  change o ∈ (if E.awake x t then
    (duties p t).flatMap (fun d => (rho.ownSeats (RunDuty.signLabel d) x).filterMap
      (fun seat => ((fgsa p c).act ((fgsa p c).clock (rho.stateBefore E i x) t) d
        (rho.input x t)).map (fun m => ⟨.seat (RunDuty.signLabel d) seat, m⟩))) ++ []
    else []) at hemit
  split at hemit
  · rw [List.append_nil] at hemit
    obtain ⟨d, _, hpool⟩ := List.mem_flatMap.mp hemit
    obtain ⟨seat, _, hwire⟩ := List.mem_filterMap.mp hpool
    obtain ⟨m, hact, heq⟩ := Option.map_eq_some_iff.mp hwire
    subst o
    change m = .proposal N at ho
    subst m
    cases d with
    | headAction s => cases hact
    | fgAction r =>
      change (attest p _ _ _).1.map Msg.row = some (.proposal N) at hact
      obtain ⟨_, _, he⟩ := Option.map_eq_some_iff.mp hact
      cases he
    | propAction s =>
      change (propose p _ s).map (withApp p _) = some (.proposal N) at hact
      unfold propose at hact
      split at hact
      · cases hact
      · simp only [Option.map_map] at hact
        obtain ⟨P, hP, he⟩ := Option.map_eq_some_iff.mp hact
        have hparent : N.parent = P := by
          have hp := congrArg (fun m : Msg p.n =>
            match m with | .proposal M => M.parent | _ => .genesis) he
          exact hp.symm
        refine ⟨i, ?_⟩
        have hm := (namedByErase?_sound _ _ P hP).1
        change P ∈ (clock p (rho.stateBefore E i x).st t).namedBodies at hm
        rw [clock_namedBodies] at hm
        simpa only [hparent] using hm
  · exact (List.not_mem_nil hemit).elim

/-- [ROOT-DIGEST-2 W1; DC goldfish_vote] Emission supplies the actual selected body. -/
theorem headTargetAtEmission_exists (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {x : V} {o : Obj p} {t : Time} {r : BlockId}
    (hem : V2.D.Run.emits E rho x o t) (ho : o.payload = .head r) :
    ∃ H, HeadTargetAtEmission p c E rho x o t H := by
  obtain ⟨i, hi, hemit⟩ := hem
  have horiginal := hemit
  rw [(V2.D.Run.step_tick_eq E rho hi).2] at hemit
  change o ∈ (if E.awake x t then
    (duties p t).flatMap (fun d => (rho.ownSeats (RunDuty.signLabel d) x).filterMap
      (fun seat => ((fgsa p c).act ((fgsa p c).clock (rho.stateBefore E i x) t) d
        (rho.input x t)).map (fun m => ⟨.seat (RunDuty.signLabel d) seat, m⟩))) ++ []
    else []) at hemit
  split at hemit
  · rw [List.append_nil] at hemit
    obtain ⟨d, _, hpool⟩ := List.mem_flatMap.mp hemit
    obtain ⟨seat, _, hwire⟩ := List.mem_filterMap.mp hpool
    obtain ⟨m, hact, heq⟩ := Option.map_eq_some_iff.mp hwire
    subst o
    change m = .head r at ho
    subst m
    cases d with
    | headAction s =>
      have he := Option.some.inj hact
      refine ⟨headVote p (clock p (rho.stateBefore E i x).st t) s, i, s, seat,
        hi, horiginal, ?_, rfl⟩
      cases Msg.head.inj he
      rfl
    | fgAction r' =>
      change (attest p _ _ _).1.map Msg.row = some (.head r) at hact
      obtain ⟨_, _, he⟩ := Option.map_eq_some_iff.mp hact
      cases he
    | propAction s =>
      change (propose p _ s).map (withApp p _) = some (.head r) at hact
      unfold propose at hact
      split at hact
      · cases hact
      · simp only [Option.map_map] at hact
        obtain ⟨P, _, he⟩ := Option.map_eq_some_iff.mp hact
        cases he
  · exact (List.not_mem_nil hemit).elim

/-- [ROOT-DIGEST-2 W1; DC duty provenance] A scheduled occurrence has one selected body. -/
theorem headTargetAtEmission_unique (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hs : V2.D.ScheduleWellFormed E rho) {x : V} {o : Obj p} {t : Time} {H K : Block}
    (hH : HeadTargetAtEmission p c E rho x o t H)
    (hK : HeadTargetAtEmission p c E rho x o t K) : H = K := by
  obtain ⟨i, s, j, hi, _, ho, hH⟩ := hH
  obtain ⟨i', s', j', hi', _, ho', hK⟩ := hK
  obtain ⟨_, he⟩ := List.getElem?_eq_some_iff.mp hi
  obtain ⟨_, he'⟩ := List.getElem?_eq_some_iff.mp hi'
  have heq : i = i' := (List.Nodup.getElem_inj_iff hs.nodup).mp (he.trans he'.symm)
  subst i'
  have hslot : s = s' := by
    have ha := congrArg (fun (a : Obj p) => match a.auth with
      | .seat (.base (.head u)) _ => some u
      | _ => none) (ho.symm.trans ho')
    exact Option.some.inj ha
  subst s'
  exact hH.trans hK.symm

end AvailableChain.FGSA.Run
end
