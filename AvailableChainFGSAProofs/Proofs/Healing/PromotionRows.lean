module
public import AvailableChainFGSAProofs.Proofs.Healing.PromotionCarrier
public import AvailableChainFGSAProofs.Proofs.Healing.Promotion

public section

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

variable {p : Params} {In V : Type} [DecidableEq V] [Fintype V] {c : AppCodec In}

private theorem promotion_honest_row_decode (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : Recovery₂ p c E rho G ΔF)
    {j r : Nat} {x : V} {a : RowWire p.n} (ha : HonestRowAt p c E rho j x r a) :
    ∃ b, a.toRow? = some b ∧ b.height_pair = a.payload.height_pair := by
  have hawake : E.awake x (p.actionTime r) = true := by
    cases hw : E.awake x (p.actionTime r) with
    | true => rfl
    | false =>
      have hem := ha.2.2
      rw [(V2.D.Run.step_tick_eq E rho ha.2.1).2] at hem
      have hnil := (fgsa_tick_asleep (p := p) (c := c) E rho
        (V2.D.Run.stateBefore E rho j x) x (p.actionTime r) hw).1
      have hem : ofRow p a ∈ ([] : List (Obj p)) := hnil ▸ hem
      exact (List.not_mem_nil hem).elim
  have hv := honest_emit_wellFormed E rho hrec.base.valid.toDeliveryWellFormed
    hrec.base.valid.toScheduleWellFormed j x _ ha.2.1 ha.1 hawake (ofRow p a) ha.2.2
  cases a with
  | mk auth payload =>
    cases auth with
    | none => cases hv
    | proposer s => cases hv
    | seat label i =>
      cases label with
      | head s => cases hv
      | fg => exact ⟨_, rfl, rfl⟩

/-- Blueprint 21:1385–1410; plan §3.2 step 4, same-height branch.
DC: SAME the original progress row matches the current parent entry.
The path and equal height are local branch facts. They do not assert placement
of earlier matching rows. The row's finality pair can have any value. -/
private theorem promotion_same_row (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : Recovery₂ p c E rho G ΔF)
    {s : Slot} {X U : FGBlock (Fin p.n)} {height : Nat}
    (hQ : HonestProposal E rho (fgsaInterface p c) s (eraseFG X)) (hslot : X.slot = s)
    (hentry : EntryAt p U height) (hpath : FGBlock.Preceq U X.parent)
    (hheight : (heightView p X.parent).h = height)
    {j rSent : Nat} {x : V} {a : RowWire p.n}
    (ha : HonestRowAt p c E rho j x rSent a) (hn : NamesEntry p .progress a height U) :
    ValidForParent p c E rho X.slot (eraseFG X) a ∧
      HeightMatch p c E rho X.slot (eraseFG X) a := by
  obtain ⟨Y, he, _, _, st, hst, hlookup⟩ := healing_promotion_carrier E rho hrec hQ
  have hYX : Y = X := eraseFG_injective he
  subst Y
  have hT : (heightView p X.parent).T_h = U :=
    ((fgCertificateLaws p).height.entry_plateau hpath (hentry.1.trans hheight.symm)).symm.trans
      hentry.2
  have hh : (parentFoldState p s X.parent).h = height := hheight
  have ht : (parentFoldState p s X.parent).T_h = U := hT
  obtain ⟨b, hb, hpair⟩ := promotion_honest_row_decode E rho hrec ha
  obtain ⟨timeout, hn⟩ := hn
  have hm : Window.heightMatch (parentFoldState p s X.parent) b = true := by
    rw [Window.heightMatch_def, hpair, hn, hh, ht]
    change decide (height = height ∧ U.root = U.root) = true
    exact decide_eq_true ⟨rfl, rfl⟩
  have hv : Window.rowValidW (parentFoldState p s X.parent) a = true :=
    (Window.rowValidW_iff _ a).mpr ⟨b, hb, Or.inl hm⟩
  rw [hslot]
  refine ⟨⟨st, X.parent, hst, hlookup, hv⟩, st, X.parent, hst, hlookup, ?_⟩
  rw [hn]
  change some (height, U.root) = some ((parentFoldState p s X.parent).h,
    (parentFoldState p s X.parent).T_h.root)
  rw [hh, ht]

/-- ROOT-DIGEST W2b. Blueprint 21:1385–1410; plan §3.2 step 4, same-height branch.
DC: SAME source transfer puts the common entry on the new parent path.
The original fixed rows supply both validity fields when the parent has the
starting height. No above-entry occurrence premise is required. -/
theorem healing_promotion_same_rows (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : Recovery₂ p c E rho G ΔF)
    (perm : TPerm p c E rho) {u : Time} {m : Nat}
    {J : Option (FGBlock (Fin p.n))} {contested : Bool}
    {r height : Nat} {s : Slot} {Q : Block} {X : FGBlock (Fin p.n)}
    (hentry : OpeningEntry p c E rho r height) (hcovered : OpeningCovered p c E rho r Q)
    (hgst : E.t_GST ≤ u)
    (hphase : PhaseInterval p c E rho u (SA.proposalTime p.toParams s) m J contested)
    (hu : u ≤ SA.voteTime p.toParams (r * p.R))
    (hgate : p.actionTime r ≤ SA.proposalTime p.toParams s) (hs : r * p.R + 2 ≤ s)
    (hnew : HonestProposal E rho (fgsaInterface p c) s (eraseFG X)) (hslot : X.slot = s) :
    ∃ U : FGBlock (Fin p.n), EntryAt p U height ∧ U.slot ≤ r * p.R ∧
      FGBlock.Preceq U X.parent ∧
      ∀ x ∈ rho.honest, ∃ K nd j rSent a,
        postClock E rho x (p.actionTime r) = some nd ∧
        actionSourceFG p c E rho x r = some (some K) ∧ K ∈ FGSA.fullTree p nd.st ∧
        Block.Preceq Q (eraseFG K) ∧ FGBlock.Preceq U K ∧ K.slot ≤ r * p.R ∧
        (heightView p K).h = height ∧ (heightView p K).T_h = U ∧
        rSent ≤ r ∧ HonestRowAt p c E rho j x rSent a ∧
        NamesEntry p .progress a height U ∧
        ((heightView p X.parent).h = height →
          ValidForParent p c E rho X.slot (eraseFG X) a ∧
          HeightMatch p c E rho X.slot (eraseFG X) a) := by
  obtain ⟨U, hU, hUslot, hrows⟩ := healing_promotion_bounded_rows E rho hrec hentry hcovered
  have path : ∀ x ∈ rho.honest, ∀ K,
      actionSourceFG p c E rho x r = some (some K) →
      FGBlock.Preceq U K → FGBlock.Preceq U X.parent := by
    intro x hx K hK hUK
    have hparent := healing_promotion_source_parent E rho perm hgst hphase hu hgate hx hK hs hnew
    rw [eraseFG_parent] at hparent
    have hKX : FGBlock.Preceq K X.parent :=
      eraseFG_preceq_iff.mp hparent
    exact KitFG.preceq_trans hUK hKX
  have hUP : FGBlock.Preceq U X.parent := by
    obtain ⟨x, hx⟩ := (show rho.honest.Nonempty from by
      have hn : Fintype.card V = p.n :=
        (V2.D.CStar.seats_eq (ℓ := .base .fg) hrec.base.linked.toCStar trivial).symm
      by_contra h
      have he := Finset.not_nonempty_iff_eq_empty.mp h
      have hf := hrec.fault
      rw [Gen.V2.Duty.faulty_def, he, Finset.sdiff_empty, Finset.card_univ, hn] at hf
      have := p.nPos
      omega)
    obtain ⟨K, _, _, _, _, _, hK, _, _, hUK, _⟩ := hrows x hx
    exact path x hx K hK hUK
  refine ⟨U, hU, hUslot, hUP, ?_⟩
  intro x hx
  obtain ⟨K, nd, j, rSent, a, hnd, hK, hmem, hQ, hUK, hKslot, hKheight, hKU, hr, ha, hn⟩ :=
    hrows x hx
  exact ⟨K, nd, j, rSent, a, hnd, hK, hmem, hQ, hUK, hKslot, hKheight, hKU, hr, ha, hn,
    fun hh => promotion_same_row E rho hrec hnew hslot hU hUP hh ha hn⟩

/-- The promotion consumer uses the selected sources at its actual proposal read. -/
theorem healing_promotion_same_rows_on (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : Recovery₂ p c E rho G ΔF)
 {u : Time} {m : Nat}
    {J : Option (FGBlock (Fin p.n))} {contested : Bool}
    {r height : Nat} {s : Slot} {Q : Block} {X : FGBlock (Fin p.n)}
    (hentry : OpeningEntry p c E rho r height) (hcovered : OpeningCovered p c E rho r Q)
    (_hgst : E.t_GST ≤ u)
    (_hphase : PhaseInterval p c E rho u (SA.proposalTime p.toParams s) m J contested)
    (_hu : u ≤ SA.voteTime p.toParams (r * p.R))
    (_hgate : p.actionTime r ≤ SA.proposalTime p.toParams s) (_hs : r * p.R + 2 ≤ s)
    (hnew : HonestProposal E rho (fgsaInterface p c) s (eraseFG X)) (hslot : X.slot = s)
    (hParents : ∀ x ∈ rho.honest, ∀ K,
      actionSourceFG p c E rho x r = some (some K) →
      Block.Preceq (eraseFG K) (eraseFG X).parent) :
    ∃ U : FGBlock (Fin p.n), EntryAt p U height ∧ U.slot ≤ r * p.R ∧
      FGBlock.Preceq U X.parent ∧
      ∀ x ∈ rho.honest, ∃ K nd j rSent a,
        postClock E rho x (p.actionTime r) = some nd ∧
        actionSourceFG p c E rho x r = some (some K) ∧ K ∈ FGSA.fullTree p nd.st ∧
        Block.Preceq Q (eraseFG K) ∧ FGBlock.Preceq U K ∧ K.slot ≤ r * p.R ∧
        (heightView p K).h = height ∧ (heightView p K).T_h = U ∧
        rSent ≤ r ∧ HonestRowAt p c E rho j x rSent a ∧
        NamesEntry p .progress a height U ∧
        ((heightView p X.parent).h = height →
          ValidForParent p c E rho X.slot (eraseFG X) a ∧
          HeightMatch p c E rho X.slot (eraseFG X) a) := by
  obtain ⟨U, hU, hUslot, hrows⟩ := healing_promotion_bounded_rows E rho hrec hentry hcovered
  have path : ∀ x ∈ rho.honest, ∀ K,
      actionSourceFG p c E rho x r = some (some K) →
      FGBlock.Preceq U K → FGBlock.Preceq U X.parent := by
    intro x hx K hK hUK
    have hparent := hParents x hx K hK
    rw [eraseFG_parent] at hparent
    have hKX : FGBlock.Preceq K X.parent :=
      eraseFG_preceq_iff.mp hparent
    exact KitFG.preceq_trans hUK hKX
  have hUP : FGBlock.Preceq U X.parent := by
    obtain ⟨x, hx⟩ := (show rho.honest.Nonempty from by
      have hn : Fintype.card V = p.n :=
        (V2.D.CStar.seats_eq (ℓ := .base .fg) hrec.base.linked.toCStar trivial).symm
      by_contra h
      have he := Finset.not_nonempty_iff_eq_empty.mp h
      have hf := hrec.fault
      rw [Gen.V2.Duty.faulty_def, he, Finset.sdiff_empty, Finset.card_univ, hn] at hf
      have := p.nPos
      omega)
    obtain ⟨K, _, _, _, _, _, hK, _, _, hUK, _⟩ := hrows x hx
    exact path x hx K hK hUK
  refine ⟨U, hU, hUslot, hUP, ?_⟩
  intro x hx
  obtain ⟨K, nd, j, rSent, a, hnd, hK, hmem, hQ, hUK, hKslot, hKheight, hKU, hr, ha, hn⟩ :=
    hrows x hx
  exact ⟨K, nd, j, rSent, a, hnd, hK, hmem, hQ, hUK, hKslot, hKheight, hKU, hr, ha, hn,
    fun hh => promotion_same_row E rho hrec hnew hslot hU hUP hh ha hn⟩

end AvailableChain.FGSA.Run
end
