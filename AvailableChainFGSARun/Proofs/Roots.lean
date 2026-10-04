module
public import AvailableChainFGSARun.Statements.Roots
public import AvailableChainFGSARun.Proofs.Reachable
public import AvailableChainFGSARun.Proofs.Emission
public import AvailableChainFGSA.Proofs.Carrier
public import AvailableChainFGSA.Proofs.CrossNode
public import AvailableChainFGSA.Proofs.Head
public import AvailableChainFGSARun.Statements.Interface
public import AvailableChainGeneric.Statements.V2.Duty.DeliveryBy

public section

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG

variable {p : Params} {In V : Type} {c : AppCodec In} [DecidableEq V]

/-- [ROOT-DIGEST W1; DC NamedReceiptCalls] A proposal call is a direct delivery. -/
theorem proposal_handlesS_direct (st : State p.n) (parent o : Obj p)
    (s : Slot) (b : Block) (raw sup : List (HeadWire p.n)) (rows : List (RowWire p.n))
    (hd : (toWire p o).decode = some (.block s b raw sup rows))
    (hh : handlesS p st parent o) : parent = o := by
  rcases hh with h | h
  · exact h
  · cases hp : (toWire p parent).decode with
    | none => simp only [hp] at h
    | some m =>
      cases m with
      | vote r i B => simp only [hp] at h
      | row i body => simp only [hp] at h
      | block r B raw' sup' rows' =>
        rw [hp] at h
        rcases h.2 with hm | hm
        · obtain ⟨a, _, rfl⟩ := List.mem_map.mp hm
          rcases a with ⟨⟨(_ | _), _⟩ | _ | _, _⟩ <;> simp [toWire, ofHead, ofWire, ofAuth,
            toAuth, Wire.decode] at hd
        · obtain ⟨a, _, rfl⟩ := List.mem_map.mp hm
          rcases a with ⟨⟨(_ | _), _⟩ | _ | _, _⟩ <;> simp [toWire, ofRow, ofWire, ofAuth, toAuth,
            Wire.decode] at hd

/-- [ROOT-DIGEST W1; DC NamedRun.blockInRun] A proposal handler scopes its body. -/
theorem proposal_handle_in_scope (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (o : Obj p) (s : Slot) (b : Block)
    (raw support : List (HeadWire p.n)) (rows : List (RowWire p.n))
    (ho : o = ofWire p ⟨.proposer s, .proposal b raw support rows⟩)
    (j : Nat) (w : V) (t : Time) (hh : V2.D.Run.handlesAt E rho j w o t) :
    RootBlockInRun p c E rho b := by
  obtain ⟨parent, hevent, hcall⟩ := hh
  have hd : (toWire p o).decode = some (.block s b raw support rows) := by
    rw [ho]
    rfl
  have hp := proposal_handlesS_direct _ parent o s b raw support rows hd hcall
  subst parent
  refine ⟨b, Or.inl ⟨w, o, t, raw, support, rows, ?_, ?_⟩, ?_⟩
  · exact List.mem_of_getElem? hevent
  · rw [ho]
    rfl
  · cases b <;> simp [Block.Preceq, Block.preceq]

/-- [ROOT-DIGEST W1; DC NamedReceiptCalls] Broadcast or source acceptance scopes a trigger.
This proof uses no root idealization or processed-to-body inference. -/
theorem proposal_trigger_in_scope
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (o : Obj p) (s : Slot) (b : Block)
    (raw support : List (HeadWire p.n)) (rows : List (RowWire p.n))
    (ho : o = ofWire p ⟨.proposer s, .proposal b raw support rows⟩)
    (dl : Time → Time) (cut t : Time) (w : V)
    (hD : Gen.V2.Duty.DeliveryWithinOn E rho (fun o => ¬ isRowObject o) dl cut)
    (hT : Gen.V2.Duty.Trigger E rho o t) (hw : w ∈ rho.honest)
    (hcut : dl t ≤ cut)
    (hNX : (fgsa p c).excludes (V2.D.Run.stateBeforeTime E rho (dl t) w) o = false) :
    RootBlockInRun p c E rho b := by
  rcases hT with ⟨v, hv, hemit⟩ | ⟨v, _, i, haccept⟩
  · have hQ : ¬ isRowObject o := by
      rw [ho]
      simp [isRowObject, ofWire]
    obtain ⟨t', _, _, j, hh⟩ := hD.broadcast v hv o hQ t hemit w hw hcut hNX
    exact proposal_handle_in_scope E rho o s b raw support rows ho j w t' hh
  · exact proposal_handle_in_scope E rho o s b raw support rows ho i v t haccept.1

/-- [ROOT-DIGEST W1; DC NamedRootCollisionFree] Stored content agrees on scoped roots.
Signed rows follow from BODY validity. This does not equate raw or support lists. -/
theorem stored_content_eq (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hr : NamedRootCollisionFree p c E rho)
    {b b' : Block} {raw support raw' support' : List (HeadWire p.n)}
    {rows rows' : List (RowWire p.n)}
    (hb : RootBlockInRun p c E rho b) (hb' : RootBlockInRun p c E rho b')
    (hc : contentOk p b raw support rows = true)
    (hc' : contentOk p b' raw' support' rows' = true)
    (he : b.root = b'.root) : b = b' ∧ rows = rows' := by
  have hbb := hr.root_injective b b' hb hb' b b'
    (Or.inl (block_preceq_refl b)) (Or.inr (block_preceq_refl b')) he
  subst b'
  exact ⟨rfl, rows_eq_of_rowsOk (contentOk_rowsOk hc) (contentOk_rowsOk hc')⟩

/-- [ROOT-DIGEST W1; DC NamedBlocks] An app update recomputes the full content digest. -/
theorem contentOk_withApp (H : Block) (s : Slot) (r : BlockId) (body app : Nat)
    (raw support : List (HeadWire p.n)) (rows : List (RowWire p.n)) :
    withApp p app (.proposal (.node H s r body) raw support rows) =
      .proposal (proposalBlock p H s app raw support rows) raw support rows ∧
    contentOk p (proposalBlock p H s app raw support rows) raw support rows = true :=
  ⟨rfl, contentOk_proposalBlock p H s app raw support rows⟩

/-- [ROOT-DIGEST W1; DC NamedBlocks] A zero app update preserves the zero-app proposal. -/
theorem withApp_zero_proposalBlock (H : Block) (s : Slot)
    (raw support : List (HeadWire p.n)) (rows : List (RowWire p.n)) :
    withApp p 0 (.proposal (proposalBlock p H s 0 raw support rows) raw support rows) =
      .proposal (proposalBlock p H s 0 raw support rows) raw support rows := rfl

/-- [ROOT-DIGEST W1; DC NamedBlocks] An app update preserves BODY validity. -/
theorem rowsOk_withApp_proposalBlock (H : Block) (s : Slot) (app : Nat)
    (raw support : List (HeadWire p.n)) (rows : List (RowWire p.n)) :
    rowsOk (proposalBlock p H s app raw support rows) rows = true :=
  contentOk_rowsOk (contentOk_proposalBlock p H s app raw support rows)

/-- ROOT-DIGEST W2. Direct delivery puts the proposal body in scope. -/
theorem rootBlockInRun_delivered (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {x : V} {o : Obj p} {t : Time} {b : Block}
    {raw sup : List (HeadWire p.n)} {rows : List (RowWire p.n)}
    (hd : V2.Event.deliver x o t ∈ rho.events)
    (ho : o.payload = .proposal b raw sup rows) : RootBlockInRun p c E rho b :=
  ⟨b, Or.inl ⟨x, o, t, raw, sup, rows, hd, ho⟩, block_preceq_refl b⟩

/-- ROOT-DIGEST W2. An honest prefix body is a direct scope seed. -/
theorem rootBlockInRun_held (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {x : V} (hx : x ∈ rho.honest) (i : Nat) {b : Block}
    (hb : b ∈ (V2.D.Run.stateBefore E rho i x).st.base.blocks) :
    RootBlockInRun p c E rho b :=
  ⟨b, Or.inr ⟨x, hx, i, hb⟩, block_preceq_refl b⟩

/-- ROOT-DIGEST W2. The body scope is closed under ancestors. -/
theorem rootBlockInRun_ancestor (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {A B : Block} (hB : RootBlockInRun p c E rho B) (hAB : Block.Preceq A B) :
    RootBlockInRun p c E rho A := by
  obtain ⟨C, hC, hBC⟩ := hB
  exact ⟨C, hC, block_preceq_trans hAB hBC⟩

/-- ROOT-DIGEST W2. Equal roots identify two independently scoped bodies. -/
theorem rootBlockInRun_eq (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hr : NamedRootCollisionFree p c E rho) {A B : Block}
    (hA : RootBlockInRun p c E rho A) (hB : RootBlockInRun p c E rho B)
    (he : A.root = B.root) : A = B :=
  hr.root_injective A B hA hB A B
    (Or.inl (block_preceq_refl A)) (Or.inr (block_preceq_refl B)) he

/-- ROOT-DIGEST W2. Body scope and structural erasure give a two-chain FG premise. -/
theorem rootInjectiveOn_run (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hr : NamedRootCollisionFree p c E rho) {K W : FGBlock (Fin p.n)}
    (hK : RootBlockInRun p c E rho (eraseFG K))
    (hW : RootBlockInRun p c E rho (eraseFG W)) : KitFG.RootInjectiveOn K W := by
  intro A B hA hB he
  apply eraseFG_injective
  exact hr.root_injective _ _ hK hW _ _ (hA.imp eraseFG_preceq eraseFG_preceq)
    (hB.imp eraseFG_preceq eraseFG_preceq) (by simpa only [eraseFG_root] using he)

/-- ROOT-DIGEST W2. Scope for each inserted-tree member supplies StoreStepRoots. -/
theorem storeStepRoots_run (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hr : NamedRootCollisionFree p c E rho) (st : Store (Fin p.n))
    (B : FGBlock (Fin p.n))
    (hs : ∀ W ∈ insert B st.TF, RootBlockInRun p c E rho (eraseFG W)) :
    KitFG.StoreStepRoots st B := by
  rintro A D ⟨K, hK, hAK⟩ ⟨W, hW, hDW⟩ he
  exact rootInjectiveOn_run E rho hr (hs K hK) (hs W hW)
    A D (Or.inl hAK) (Or.inr hDW) he

/-- ROOT-DIGEST W2. A stored non-genesis FG body has an earlier direct delivery.
This origin proof uses local invariants only, with no root premise or Base₂. -/
theorem stored_fg_body_delivery (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (i : Nat) (x : V) (W : FGBlock (Fin p.n))
    (hW : W ∈ (V2.D.Run.stateBefore E rho i x).st.fg.TF) (hne : W ≠ .genesis) :
    ∃ s raw sup rows, W.rows = rows.filterMap RowWire.toRow? ∧
      ∃ j o t, j < i ∧ rho.events[j]? = some (.deliver x o t) ∧
        o = ofWire p ⟨.proposer s, .proposal (eraseFG W) raw sup rows⟩ := by
  have hs := storeBundle_stateBefore E rho i x
  obtain ⟨s, raw, sup, rows, hw, hr⟩ :=
    stored_wire_of_block p _ hs.cstore hs.«meta» hW hne
  obtain ⟨j, o, t, hji, hd, ho, _, _⟩ := stored_proposal_delivered E rho i x _ hw
  refine ⟨s, raw, sup, rows, hr, j, o, t, hji, hd, ?_⟩
  apply toWire_injective
  rw [toWire_ofWire, ho]

/-- ROOT-DIGEST W2. Any stored non-genesis body is a directly delivered proposal. -/
theorem stored_body_delivery (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (i : Nat) (x : V) {b : Block}
    (hb : b ∈ (V2.D.Run.stateBefore E rho i x).st.base.blocks) (hne : b ≠ .genesis) :
    ∃ j o t raw sup rows, j < i ∧ rho.events[j]? = some (.deliver x o t) ∧
      o.payload = .proposal b raw sup rows := by
  obtain ⟨W, hW, rfl⟩ := (cstoreInv_stateBefore E rho i x).baseTree _ |>.mp hb
  have hWne : W ≠ .genesis := fun h => hne (by rw [h]; rfl)
  obtain ⟨s, raw, sup, rows, _, j, o, t, hj, hd, rfl⟩ :=
    stored_fg_body_delivery E rho i x W hW hWne
  exact ⟨j, _, t, raw, sup, rows, hj, hd, rfl⟩

/-- ROOT-DIGEST W2. Non-genesis bodies at arbitrary nodes have delivery scope. -/
theorem rootBlockInRun_stored (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (i : Nat) (x : V) {b : Block}
    (hb : b ∈ (V2.D.Run.stateBefore E rho i x).st.base.blocks) (hne : b ≠ .genesis) :
    RootBlockInRun p c E rho b := by
  obtain ⟨_, _, _, _, _, _, _, hd, ho⟩ := stored_body_delivery E rho i x hb hne
  exact rootBlockInRun_delivered E rho (List.mem_of_getElem? hd) ho

/-- ROOT-DIGEST W2. Every stored proposal body is in scope, at any node. -/
theorem rootBlockInRun_stored_proposal (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) (i : Nat) (x : V)
    {s : Slot} {b : Block} {raw sup : List (HeadWire p.n)} {rows : List (RowWire p.n)}
    (hw : (⟨.proposer s, .proposal b raw sup rows⟩ : Wire p.n) ∈
      (V2.D.Run.stateBefore E rho i x).st.proposals) : RootBlockInRun p c E rho b := by
  obtain ⟨_, o, _, _, hd, ho, _, _⟩ := stored_proposal_delivered E rho i x _ hw
  have he : o = ofWire p ⟨.proposer s, .proposal b raw sup rows⟩ := by
    apply toWire_injective
    rwa [toWire_ofWire]
  exact rootBlockInRun_delivered E rho (List.mem_of_getElem? hd) (by rw [he]; rfl)

/-- ROOT-DIGEST W2. Every ancestor of a prefix-held body is in that body store. -/
theorem stored_body_ancestor (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (i : Nat) (x : V) {A B : Block}
    (hB : B ∈ (V2.D.Run.stateBefore E rho i x).st.base.blocks)
    (hAB : Block.Preceq A B) : A ∈ (V2.D.Run.stateBefore E rho i x).st.base.blocks := by
  have hs := cstoreInv_stateBefore E rho i x
  obtain ⟨W, hW, rfl⟩ := (hs.baseTree B).mp hB
  obtain ⟨C, hC, he, _⟩ := eraseFG_ancestor_preceq hs.fg.closed hW hAB
  exact (hs.baseTree A).mpr ⟨C, hC, he⟩

/-- ROOT-DIGEST W2b. ROOT-DIGEST W2. An emitted proposal's parent was already in the emitter's
store.
The emitted tip itself need not be in the body scope. -/
theorem emitted_proposal_parent_stored (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) (i : Nat) (x : V) (t : Time) (s : Slot)
    (b : Block) (raw sup : List (HeadWire p.n)) (rows : List (RowWire p.n))
    (hi : rho.events[i]? = some (.tick x t))
    (hem : ofWire p ⟨.proposer s, .proposal b raw sup rows⟩ ∈ rho.emitsAt E i) :
    b.parent ∈ (V2.D.Run.stateBefore E rho i x).st.base.blocks := by
  rw [(V2.D.Run.step_tick_eq E rho hi).2] at hem
  have hp := (fgsa_emits_proposal E rho _ x t s _).mp hem |>.2.2.2
  unfold propose at hp
  split at hp
  · cases hp
  · change some (Msg.proposal _ _ _ _) = some (Msg.proposal b raw sup rows) at hp
    obtain ⟨rfl, _, _, _⟩ := Msg.proposal.inj (Option.some.inj hp)
    have hm := getHead_stored p _ (cstoreInv_clock p _ (cstoreInv_stateBefore E rho i x) t)
      (proposerVotes (clock p (rho.stateBefore E i x).st t) s)
      (proposerSupport (clock p (rho.stateBefore E i x).st t) s)
    rwa [clock_base_blocks] at hm

/-- ROOT-DIGEST W2b. Every emitted proposal payload has a stored parent. -/
theorem emitted_payload_parent_stored (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {x : V} {o : Obj p} {t : Time}
    {b : Block} {raw sup : List (HeadWire p.n)} {rows : List (RowWire p.n)}
    (hem : V2.D.Run.emits E rho x o t) (ho : o.payload = .proposal b raw sup rows) :
    ∃ i, b.parent ∈ (V2.D.Run.stateBefore E rho i x).st.base.blocks := by
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
    change m = .proposal b raw sup rows at ho
    subst m
    cases d with
    | headAction s => cases hact
    | fgAction r =>
      change (attest p _ _ _).1.map Msg.row = some (.proposal b raw sup rows) at hact
      obtain ⟨_, _, he⟩ := Option.map_eq_some_iff.mp hact
      cases he
    | propAction s =>
      change (propose p _ s).map (withApp p _) = some (.proposal b raw sup rows) at hact
      unfold propose at hact
      split at hact
      · cases hact
      · change some (Msg.proposal _ _ _ _) = some (Msg.proposal b raw sup rows) at hact
        obtain ⟨rfl, _, _, _⟩ := Msg.proposal.inj (Option.some.inj hact)
        refine ⟨i, ?_⟩
        have hhead := getHead_stored p _
          (cstoreInv_clock p _ (cstoreInv_stateBefore E rho i x) t)
          (proposerVotes (clock p (rho.stateBefore E i x).st t) s)
          (proposerSupport (clock p (rho.stateBefore E i x).st t) s)
        rwa [clock_base_blocks] at hhead
  · exact (List.not_mem_nil hemit).elim

/-- ROOT-DIGEST W2. An emitted proposal with a slot digest has that small root. -/
theorem emitted_proposal_slot_root (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hdigest : ∀ d, p.digest d = ⟨d.slot + 1⟩)
    (i : Nat) (x : V) (t : Time) (s : Slot)
    (b : Block) (raw sup : List (HeadWire p.n)) (rows : List (RowWire p.n))
    (hi : rho.events[i]? = some (.tick x t))
    (hem : ofWire p ⟨.proposer s, .proposal b raw sup rows⟩ ∈ rho.emitsAt E i) :
    b.root = ⟨b.slot + 1⟩ := by
  rw [(V2.D.Run.step_tick_eq E rho hi).2] at hem
  have hp := (fgsa_emits_proposal E rho _ x t s _).mp hem |>.2.2.2
  obtain ⟨H, raw', sup', rows', he, _, _⟩ := rowsOk_withApp _ _ _ hp
  obtain ⟨rfl, _, _, _⟩ := Msg.proposal.inj he.symm
  exact hdigest _

/-- ROOT-DIGEST W2. Delivery-parent origin closes the full body scope.
For NV, emitted_proposal_parent_stored supplies hparents. No root premise is used. -/
theorem rootBlockInRun_genesis_or_delivered (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c))
    (hparents : ∀ x o t b raw sup rows,
      V2.Event.deliver x o t ∈ rho.events → o.payload = .proposal b raw sup rows →
      ∃ i y, b.parent ∈ (V2.D.Run.stateBefore E rho i y).st.base.blocks)
    {A : Block} (hA : RootBlockInRun p c E rho A) :
    A = .genesis ∨ ∃ x o t raw sup rows,
      V2.Event.deliver x o t ∈ rho.events ∧ o.payload = .proposal A raw sup rows := by
  by_cases hg : A = .genesis
  · exact Or.inl hg
  apply Or.inr
  have held (i : Nat) (x : V)
      (hm : A ∈ (V2.D.Run.stateBefore E rho i x).st.base.blocks) :
      ∃ x o t raw sup rows,
        V2.Event.deliver x o t ∈ rho.events ∧ o.payload = .proposal A raw sup rows := by
    obtain ⟨j, o, t, raw, sup, rows, _, hd, ho⟩ := stored_body_delivery E rho i x hm hg
    exact ⟨x, o, t, raw, sup, rows, List.mem_of_getElem? hd, ho⟩
  obtain ⟨B, hd | ⟨x, _, i, hm⟩, hAB⟩ := hA
  · obtain ⟨x, o, t, raw, sup, rows, hd, ho⟩ := hd
    by_cases he : A = B
    · exact ⟨x, o, t, raw, sup, rows, hd, he ▸ ho⟩
    obtain ⟨i, y, hm⟩ := hparents x o t B raw sup rows hd ho
    apply held i y
    apply stored_body_ancestor E rho i y hm
    cases B with
    | genesis =>
      have : A = .genesis := by simpa [Block.Preceq, Block.preceq] using hAB
      exact (hg this).elim
    | node P s root body =>
      exact (Bool.or_eq_true_iff.mp hAB).resolve_left (by simpa using he)
  · exact held i x (stored_body_ancestor E rho i x hm hAB)

/-- ROOT-DIGEST W2. A predicate on genesis and delivered bodies covers the run scope.
NV can take Q to mean genesis or an actual fixture emission. -/
theorem rootBlockInRun_origin (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hparents : ∀ x o t b raw sup rows,
      V2.Event.deliver x o t ∈ rho.events → o.payload = .proposal b raw sup rows →
      ∃ i y, b.parent ∈ (V2.D.Run.stateBefore E rho i y).st.base.blocks)
    (Q : Block → Prop) (hgen : Q .genesis)
    (hdel : ∀ x o t b raw sup rows,
      V2.Event.deliver x o t ∈ rho.events → o.payload = .proposal b raw sup rows → Q b)
    {A : Block} (hA : RootBlockInRun p c E rho A) : Q A := by
  rcases rootBlockInRun_genesis_or_delivered E rho hparents hA with rfl | hd
  · exact hgen
  · obtain ⟨x, o, t, raw, sup, rows, hd, ho⟩ := hd
    exact hdel x o t A raw sup rows hd ho

end AvailableChain.FGSA.Run
end
