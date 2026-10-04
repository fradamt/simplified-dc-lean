module
public import AvailableChainFGSARun.Statements.Roots
public import AvailableChainFGSARun.Proofs.NamedOrigins
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




/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
[ROOT-DIGEST W1; DC NamedRootCollisionFree] Stored content agrees on scoped roots.
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

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
[ROOT-DIGEST W1; DC NamedBlocks] An app update recomputes the full content digest. -/
theorem contentOk_withApp (H : Block) (s : Slot) (r : BlockId) (body app : Nat)
    (raw support : List (HeadWire p.n)) (rows : List (RowWire p.n)) :
    withApp p app (.proposal (.node H s r body) raw support rows) =
      .proposal (proposalBlock p H s app raw support rows) raw support rows ∧
    contentOk p (proposalBlock p H s app raw support rows) raw support rows = true :=
  ⟨rfl, contentOk_proposalBlock p H s app raw support rows⟩

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
[ROOT-DIGEST W1; DC NamedBlocks] A zero app update preserves the zero-app proposal. -/
theorem withApp_zero_proposalBlock (H : Block) (s : Slot)
    (raw support : List (HeadWire p.n)) (rows : List (RowWire p.n)) :
    withApp p 0 (.proposal (proposalBlock p H s 0 raw support rows) raw support rows) =
      .proposal (proposalBlock p H s 0 raw support rows) raw support rows := rfl

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
[ROOT-DIGEST W1; DC NamedBlocks] An app update preserves BODY validity. -/
theorem rowsOk_withApp_proposalBlock (H : Block) (s : Slot) (app : Nat)
    (raw support : List (HeadWire p.n)) (rows : List (RowWire p.n)) :
    rowsOk (proposalBlock p H s app raw support rows) rows = true :=
  contentOk_rowsOk (contentOk_proposalBlock p H s app raw support rows)

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
ROOT-DIGEST W2. Direct delivery puts the proposal body in scope. -/
theorem rootBlockInRun_delivered (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {x : V} {o : Obj p} {t : Time} {b : Block}
    {raw sup : List (HeadWire p.n)} {rows : List (RowWire p.n)}
    (hd : V2.Event.deliver x o t ∈ rho.events)
    (ho : o.payload = .proposal b raw sup rows) : RootBlockInRun p c E rho b :=
  ⟨b, Or.inl ⟨x, o, t, raw, sup, rows, hd, ho⟩, block_preceq_refl b⟩

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
ROOT-DIGEST W2. An honest prefix body is a direct scope seed. -/
theorem rootBlockInRun_held (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {x : V} (hx : x ∈ rho.honest) (i : Nat) {b : Block}
    (hb : b ∈ (V2.D.Run.stateBefore E rho i x).st.base.blocks) :
    RootBlockInRun p c E rho b :=
  ⟨b, Or.inr ⟨x, hx, i, hb⟩, block_preceq_refl b⟩




/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
ROOT-DIGEST W2. Scope for each inserted-tree member supplies StoreStepRoots. -/
theorem storeStepRoots_run (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hr : NamedRootCollisionFree p c E rho) (st : Store (Fin p.n))
    (B : FGBlock (Fin p.n))
    (hs : ∀ W ∈ insert B st.TF, RootBlockInRun p c E rho (eraseFG W)) :
    KitFG.StoreStepRoots st B := by
  rintro A D ⟨K, hK, hAK⟩ ⟨W, hW, hDW⟩ he
  exact rootInjectiveOn_run E rho hr (hs K hK) (hs W hW)
    A D (Or.inl hAK) (Or.inr hDW) he

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
ROOT-DIGEST W2. A stored non-genesis FG body has an earlier direct delivery.
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

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
ROOT-DIGEST W2. Any stored non-genesis body is a directly delivered proposal. -/
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

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
ROOT-DIGEST W2. Non-genesis bodies at arbitrary nodes have delivery scope. -/
theorem rootBlockInRun_stored (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (i : Nat) (x : V) {b : Block}
    (hb : b ∈ (V2.D.Run.stateBefore E rho i x).st.base.blocks) (hne : b ≠ .genesis) :
    RootBlockInRun p c E rho b := by
  obtain ⟨_, _, _, _, _, _, _, hd, ho⟩ := stored_body_delivery E rho i x hb hne
  exact rootBlockInRun_delivered E rho (List.mem_of_getElem? hd) ho

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
ROOT-DIGEST W2. Every stored proposal body is in scope, at any node. -/
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

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
ROOT-DIGEST W2. Every ancestor of a prefix-held body is in that body store. -/
theorem stored_body_ancestor (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (i : Nat) (x : V) {A B : Block}
    (hB : B ∈ (V2.D.Run.stateBefore E rho i x).st.base.blocks)
    (hAB : Block.Preceq A B) : A ∈ (V2.D.Run.stateBefore E rho i x).st.base.blocks := by
  have hs := cstoreInv_stateBefore E rho i x
  obtain ⟨W, hW, rfl⟩ := (hs.baseTree B).mp hB
  obtain ⟨C, hC, he, _⟩ := eraseFG_ancestor_preceq hs.fg.closed hW hAB
  exact (hs.baseTree A).mpr ⟨C, hC, he⟩

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
ROOT-DIGEST W2b. ROOT-DIGEST W2. An emitted proposal's parent was already in the emitter's
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


/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
ROOT-DIGEST W2. An emitted proposal with a slot digest has that small root. -/
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

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
ROOT-DIGEST W2. Delivery-parent origin closes the full body scope.
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

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
ROOT-DIGEST W2. A predicate on genesis and delivered bodies covers the run scope.
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
