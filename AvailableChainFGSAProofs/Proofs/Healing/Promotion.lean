module
public import AvailableChainFGSAProofs.Proofs.Shared.GridSchedule
public import AvailableChainFGSAProofs.Proofs.Healing.FrameSource
public import AvailableChainFGSAClaims.Statements.Fold

public section

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG Gen.Pure

variable {p : Params} {In V : Type} [DecidableEq V] [Fintype V] {c : AppCodec In}

private theorem promotion_honest_nonempty (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : Recovery₂ p c E rho G ΔF) :
    rho.honest.Nonempty := by
  have hn : Fintype.card V = p.n :=
    (V2.D.CStar.seats_eq (ℓ := .base .fg) hrec.base.linked.toCStar trivial).symm
  by_contra h
  have he := Finset.not_nonempty_iff_eq_empty.mp h
  have hf := hrec.fault
  rw [Gen.V2.Duty.faulty_def, he, Finset.sdiff_empty, Finset.card_univ, hn] at hf
  have := p.nPos
  omega

omit [Fintype V] in
private theorem promotion_stored_parent_slot (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) (hv : V2.D.ExecutionValid E rho)
    (i : Nat) (x : V) (W : FGBlock (Fin p.n))
    (hW : W ∈ (storeAt p c E rho i x).fg.TF) (hne : W ≠ .genesis) :
    W.parent.slot < W.slot := by
  have hm := ((cstoreInv_stateBefore E rho i x).baseTree (eraseFG W)).mpr ⟨W, hW, rfl⟩
  obtain ⟨w, hw, hb, j, o, t, _, hd, ho, _⟩ :=
    fgsa_stored_block_origin E rho i x (eraseFG W) hm (by
      intro he; exact hne (eraseFG_eq_genesis.mp he))
  obtain ⟨s, Q, raw, sup, rows, rfl, _, _, _⟩ :=
    (metaInv_stateBefore E rho i x).wireTree w hw
  have hQ : Q = eraseFG W := Option.some.inj hb
  subst Q
  have hf := hv.wire j x o t hd
  change FGSA.wellFormed p (toWire p o) = true at hf
  rw [ho] at hf
  have hlt : (eraseFG W).parent.slot < (eraseFG W).slot := of_decide_eq_true
    (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp
      (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hf).1).1).1).1).2
  rwa [eraseFG_parent, eraseFG_slot, eraseFG_slot] at hlt

omit [Fintype V] in
private theorem promotion_stored_ancestor_slot (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) (hv : V2.D.ExecutionValid E rho)
    (i : Nat) (x : V) {U K : FGBlock (Fin p.n)}
    (hK : K ∈ (storeAt p c E rho i x).fg.TF) (hUK : FGBlock.Preceq U K) :
    U.slot ≤ K.slot := by
  induction K with
  | genesis => obtain rfl := KitFG.preceq_genesis.mp hUK; exact le_rfl
  | node P s body rows ih =>
      by_cases he : U = .node P s body rows
      · subst U; exact le_rfl
      · have hUP := KitFG.preceq_parent_of_preceq_node hUK he
        have hP := (cstoreInv_stateBefore E rho i x).fg.closed _ hK
        exact (ih hP hUP).trans
          (promotion_stored_parent_slot E rho hv i x _ hK (by intro h; cases h)).le

/-- Blueprint 21:1356–1384; plan §3.2 step 1.
DC: INTENTIONAL choose the starting action's SO-COV witnesses once.
The sources can differ. Their actual entries agree by root injectivity.
The source path, source slot and original send round remain in the result. -/
theorem healing_promotion_fixed_rows (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : Recovery₂ p c E rho G ΔF)
    {r height : Nat} {Q : Block} (hentry : OpeningEntry p c E rho r height)
    (hcovered : OpeningCovered p c E rho r Q) :
    ∃ U : FGBlock (Fin p.n), EntryAt p U height ∧
      ∀ x ∈ rho.honest, ∃ K nd j rSent a,
        postClock E rho x (p.actionTime r) = some nd ∧
        actionSourceFG p c E rho x r = some (some K) ∧ K ∈ FGSA.fullTree p nd.st ∧
        Block.Preceq Q (eraseFG K) ∧ FGBlock.Preceq U K ∧ K.slot ≤ r * p.R ∧
        (heightView p K).h = height ∧ (heightView p K).T_h = U ∧
        rSent ≤ r ∧ HonestRowAt p c E rho j x rSent a ∧
        NamesEntry p .progress a height U := by
  obtain ⟨e, he⟩ := hentry
  obtain ⟨x₀, hx₀⟩ := promotion_honest_nonempty E rho hrec
  obtain ⟨K₀, _, _, _, _, _, hK₀, _⟩ := hcovered x₀ hx₀
  obtain ⟨hh₀, hr₀⟩ := he x₀ K₀ hx₀ hK₀
  let U := (heightView p K₀).T_h
  refine ⟨U, ⟨((fgCertificateLaws p).height.entry_same_height K₀).trans hh₀,
    (fgCertificateLaws p).height.entry_idem K₀⟩, ?_⟩
  intro x hx
  obtain ⟨K, nd, j, rSent, a, hnd, hK, hmem, hQ, hr, ha, hn⟩ := hcovered x hx
  obtain ⟨hh, hroot⟩ := he x K hx hK
  have hU : (heightView p K).T_h = U := FGBlock.root_injective (hroot.trans hr₀.symm)
  refine ⟨K, nd, j, rSent, a, hnd, hK, hmem, hQ,
    hU ▸ (fgCertificateLaws p).height.entry_preceq K,
    healing_source_slot p c E rho hx hK, hh, hU, hr, ha, ?_⟩
  rw [hh, hU] at hn
  change ∃ timeout, a.payload.height_pair = .vote height U.root timeout
  cases hp : a.payload.height_pair with
  | empty => rw [hp] at hn; cases hn
  | vote h root timeout =>
    rw [hp] at hn
    have heq : (h, root) = (height, U.root) := Option.some.inj hn
    cases heq
    exact ⟨timeout, rfl⟩

/-- Blueprint 21:1356–1384; plan §3.2 steps 1 and 5.
DC: SAME the common entry's slot is at most the starting action label.
The equality is supplied by the fixed starting rows. -/
theorem healing_promotion_entry_slot (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : Recovery₂ p c E rho G ΔF)
    {x : V} {r : Nat} {K U : FGBlock (Fin p.n)} (hx : x ∈ rho.honest)
    (hK : actionSourceFG p c E rho x r = some (some K))
    (hU : (heightView p K).T_h = U) : U.slot ≤ r * p.R := by
  have hslot := healing_source_slot p c E rho hx hK
  have hUK : FGBlock.Preceq U K := hU ▸ (fgCertificateLaws p).height.entry_preceq K
  rw [actionSourceFG_def, postClock_def, preTick_def] at hK
  cases hi : V2.D.Run.tickIdx? rho x (p.actionTime r) with
  | none => simp only [hi, Option.map_none, reduceCtorEq] at hK
  | some i =>
    simp only [hi, Option.map_some, Option.some.injEq] at hK
    have hm := (Finset.mem_filter.mp (pickPair_some_spec _ _ hK).1).1
    have hs := ((KitFG.mem_filteredFromView _ _ _ _).mp hm).1
    change K ∈ (clock p (storeAt p c E rho i x) (p.actionTime r)).fg.TF at hs
    rw [clock_fg] at hs
    exact (promotion_stored_ancestor_slot E rho hrec.base.valid i x hs hUK).trans hslot

/-- Blueprint 21:1356–1384; plan §3.2 step 1.
DC: SAME the fixed batch keeps the common entry and its action-slot bound.
No starting row or source is replaced. -/
theorem healing_promotion_bounded_rows (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : Recovery₂ p c E rho G ΔF)
    {r height : Nat} {Q : Block} (hentry : OpeningEntry p c E rho r height)
    (hcovered : OpeningCovered p c E rho r Q) :
    ∃ U : FGBlock (Fin p.n), EntryAt p U height ∧ U.slot ≤ r * p.R ∧
      ∀ x ∈ rho.honest, ∃ K nd j rSent a,
        postClock E rho x (p.actionTime r) = some nd ∧
        actionSourceFG p c E rho x r = some (some K) ∧ K ∈ FGSA.fullTree p nd.st ∧
        Block.Preceq Q (eraseFG K) ∧ FGBlock.Preceq U K ∧ K.slot ≤ r * p.R ∧
        (heightView p K).h = height ∧ (heightView p K).T_h = U ∧
        rSent ≤ r ∧ HonestRowAt p c E rho j x rSent a ∧
        NamesEntry p .progress a height U := by
  obtain ⟨U, hU, hrows⟩ := healing_promotion_fixed_rows E rho hrec hentry hcovered
  obtain ⟨x, hx⟩ := promotion_honest_nonempty E rho hrec
  obtain ⟨K, _, _, _, _, _, hK, _, _, _, _, _, he, _⟩ := hrows x hx
  exact ⟨U, hU, healing_promotion_entry_slot E rho hrec hx hK he, hrows⟩

omit [Fintype V] in
/-- Blueprint 21:1385–1396; plan §3.2 step 4.
DC: SAME an actual starting source is a fast PhaseBody at its own opening.
No later source or row is selected. -/
theorem healing_promotion_source_body (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {x : V} {r : Nat} {K : FGBlock (Fin p.n)}
    (hx : x ∈ rho.honest) (hK : actionSourceFG p c E rho x r = some (some K)) :
    PhaseBody p c E rho (r * p.R) (eraseFG K) := by
  rw [actionSourceFG_def, postClock_def, preTick_def] at hK
  cases hi : V2.D.Run.tickIdx? rho x (p.actionTime r) with
  | none => simp only [hi, Option.map_none, reduceCtorEq] at hK
  | some i =>
    simp only [hi, Option.map_some, Option.some.injEq] at hK
    let nd := (fgsa p c).clock (rho.stateBefore E i x) (p.actionTime r)
    have hround : p.round (nd.st.slot p) = r := (fgsa_action_slot_round (c := c) _ r).2
    have hfw := (Finset.mem_filter.mp (pickPair_some_spec _ _ hK).1).2
    change (decide (eraseFG K ∈ (fastWriteAt nd.st (p.round (nd.st.slot p) * p.R)).getD []) &&
      _) = true at hfw
    have hmem := of_decide_eq_true (Bool.and_eq_true_iff.mp hfw).1
    rw [hround] at hmem
    refine ⟨x, hx, Or.inl ⟨nd, ?_, hmem⟩⟩
    rw [← fgsa_grid_action_gate, fgsa_grid_action_time, postClock_def, preTick_def, hi]
    rfl

omit [Fintype V] in
/-- Blueprint 21:1385–1396; plan §3.2 step 4.
DC: SAME TPerm transfers each fixed source to the new proposal's parent.
The phase premise includes the proposal read; service after phase termination
is not required. -/
theorem healing_promotion_source_parent (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) (perm : TPerm p c E rho)
    {u : Time} {m : Nat} {J : Option (FGBlock (Fin p.n))} {contested : Bool}
    {r : Nat} {s : Slot} {x : V} {K : FGBlock (Fin p.n)} {Q : Block}
    (hgst : E.t_GST ≤ u)
    (hphase : PhaseInterval p c E rho u (SA.proposalTime p.toParams s) m J contested)
    (hu : u ≤ SA.voteTime p.toParams (r * p.R))
    (hgate : p.actionTime r ≤ SA.proposalTime p.toParams s)
    (hx : x ∈ rho.honest) (hK : actionSourceFG p c E rho x r = some (some K))
    (hs : r * p.R + 2 ≤ s) (hQ : HonestProposal E rho (fgsaInterface p c) s Q) :
    Block.Preceq (eraseFG K) Q.parent := by
  have hg : SA.gateTime p.toParams (r * p.R) ≤ SA.proposalTime p.toParams s := by
    rwa [← fgsa_grid_action_gate, fgsa_grid_action_time]
  have ht := perm u _ m J contested (r * p.R) (eraseFG K) hgst hphase hu hg
    (healing_promotion_source_body E rho hx hK)
  exact ht.2.1 s Q hs le_rfl hQ

omit [Fintype V] in
/-- Blueprint 21:1410–1424; plan §3.2 step 6.
DC: SAME service is conditional on the old phase through the new gate.
This adapter uses the persistent RepairAfter premise of the frozen boundary. -/
theorem healing_promotion_continuing_service (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {u : Time} {m : Nat}
    {J : Option (FGBlock (Fin p.n))} {contested : Bool} {l s : Slot} {Q : Block}
    (hrepair : ∀ v, PhaseInterval p c E rho u v m J contested → RepairAfter p c E rho l v)
    (hafter : SA.proposalTime p.toParams l < SA.proposalTime p.toParams s)
    (hQ : HonestProposal E rho (fgsaInterface p c) s Q) :
    PhaseInterval p c E rho u (SA.gateTime p.toParams s) m J contested →
      ExactService p c E rho s Q := by
  intro hphase
  exact hrepair _ hphase s Q hafter le_rfl hQ

end AvailableChain.FGSA.Run
end
