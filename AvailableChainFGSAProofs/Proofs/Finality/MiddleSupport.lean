module
public import AvailableChainFGSAProofs.Proofs.Shared.FGCompose
public import AvailableChainFGCompose.Proofs.SourceHead
public import AvailableChainFGSAProofs.Proofs.Finality.RecoveryScope
public import AvailableChainFGSAProofs.Proofs.Finality.TickRead
public import AvailableChainFGSAProofs.Proofs.Shared.OutputGrowthProposal
public import AvailableChainFGSAProofs.Proofs.Shared.ProposalRead
public import AvailableChainFGSAProofs.Proofs.Shared.BoundsW
public import AvailableChainFGSAProofs.Proofs.Shared.HonestQuorum
public import AvailableChainFGSAClaims.Statements.ComposeStmt
public import AvailableChainFGSAClaims.Statements.Phases
public import AvailableChainFGSARun.Proofs.Schedule
public import AvailableChainFGSA.Proofs.Head
public import AvailableChainFGSA.Proofs.WindowAdmissionInvariant
public import AvailableChainKitFG.CausalCapCore

public section

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG AvailableChain.KitFG

/-! ### Step group A: the round clock -/

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
FINAL 22:217–220. The action clock in slot units.
DC: INTENTIONAL: FG-SA action times use its fixed round grid. -/
theorem kmid_actionTime_eq (p : Params) (r : Nat) :
    p.actionTime r = 4 * p.Δ * ((r * p.R : Nat) : Time) + 6 * p.Δ := rfl

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
FINAL 22:217–220,923–944. Positive delay and round length order the actions.
DC: INTENTIONAL: FG-SA action times use its fixed round grid. -/
theorem kmid_action_strictMono (p : Params) : StrictMono p.actionTime := by
  intro m n hmn
  rw [kmid_actionTime_eq, kmid_actionTime_eq]
  have hR : 0 < p.R := by have h := p.RLarge; omega
  have hΔ : 0 < 4 * p.Δ := mul_pos (by decide) p.deltaPos
  have hmul : m * p.R < n * p.R := Nat.mul_lt_mul_of_pos_right hmn hR
  have hprod : 4 * p.Δ * ((m * p.R : Nat) : Int) <
      4 * p.Δ * ((n * p.R : Nat) : Int) :=
    mul_lt_mul_of_pos_left (Int.ofNat_lt.mpr hmul) hΔ
  exact Int.add_lt_add_right hprod _

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
FINAL 22:217–220. Slot times are monotone in the slot.
DC: INTENTIONAL: FG-SA slot times use the 4Δ grid. -/
theorem kmid_slot_scale_le (p : Params) {a b : Nat} (h : a ≤ b) :
    4 * p.Δ * (a : Time) ≤ 4 * p.Δ * (b : Time) := by
  have hd := p.deltaPos
  have hab : (a : Time) ≤ b := by exact_mod_cast h
  nlinarith

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
FINAL 22:217–220. Slot times are strictly monotone in the slot.
DC: INTENTIONAL: FG-SA slot times use the 4Δ grid. -/
theorem kmid_slot_scale_lt (p : Params) {a b : Nat} (h : a < b) :
    4 * p.Δ * (a : Time) < 4 * p.Δ * (b : Time) := by
  have hd := p.deltaPos
  have hab : (a : Time) < b := by exact_mod_cast h
  nlinarith

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
FINAL 22:217–220. The row delay fits in κ slots.
DC: INTENTIONAL: the row delay fixes κ. -/
theorem kmid_kappa_cover (p : Params) (ΔF : Time) (hF : 0 ≤ ΔF) :
    6 * p.Δ + ΔF ≤ 4 * p.Δ * (kappaF p ΔF : Time) := by
  have h := (kappaF_ceiling p ΔF hF).2
  linarith

/-! ### Step group A: the actual opening, middle and early proposals -/

variable (p : Params) {In V : Type} [DecidableEq V]
    (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. FINAL 22:1171–1180. A joined honest proposer at a positive slot emits its
block.
DC: INTENTIONAL: the FG-SA proposer duty always builds a block at a positive slot. -/
theorem kmid_honest_proposal_exists (hs : V2.D.ScheduleWellFormed E rho) (hΔ : E.Δ = p.Δ)
    (s : Slot) (hslot : Gen.V2.Duty.HonestSlot rho (fgsaInterface p c) s)
    (hjoined : joinedAt p E rho (V2.D.proposerOf rho (fgsaInterface p c) s) s
      (SA.proposalTime p.toParams s))
    (hh : SA.proposalTime p.toParams s ≤ rho.horizon) :
    ∃ b, HonestProposal E rho (fgsaInterface p c) s b := by
  obtain ⟨B, hB, _⟩ := fgsa_honestProposal_exists_of_awake_slot E rho hs hΔ hslot
    hjoined.1 hjoined.2.2 hh
  exact ⟨B, hB⟩

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. FINAL 22:1171–1180. The emitted proposal object and its post-clock proposer
read.
DC: INTENTIONAL: FG-SA reads the proposal tick of the actual signed wire. -/
theorem kmid_proposal_read (hs : V2.D.ScheduleWellFormed E rho) {s : Slot} {b : Block}
    (hp : HonestProposal E rho (fgsaInterface p c) s b) :
    ∃ j N, N.erase = b ∧ rho.events[j]? = some (.tick (V2.D.proposerOf rho (fgsaInterface p c) s)
        (SA.proposalTime p.toParams s)) ∧
      (⟨.seat (.prop s) ⟨0, Nat.one_pos⟩, .proposal N⟩ : Obj p) ∈
        V2.D.Run.emitsAt E rho j ∧
      let st := ((fgsa p c).clock
        (V2.D.Run.stateBefore E rho j (V2.D.proposerOf rho (fgsaInterface p c) s))
        (SA.proposalTime p.toParams s)).st
      proposalStateAt p c E rho s = some st ∧ st.slot p = s ∧
        b = proposalBlock p (proposerHead p st s) s (c.app (rho.input
          (V2.D.proposerOf rho (fgsaInterface p c) s) (SA.proposalTime p.toParams s))) N.raw
              N.support
            (proposalRows p st (proposerHead p st s)) ∧
        N.rows = proposalRows p st (proposerHead p st s) :=
  proposal_read_named p c E rho hs hp

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. FINAL 22:1171–1180,585–598. The FG block of an honest proposal, with its stored
parent.
DC: INTENTIONAL: the emitted wire, proposer read, parent and decoded rows give one block. -/
theorem kmid_opening_carrier (hs : V2.D.ScheduleWellFormed E rho) {s : Slot} {b : Block}
    (hp : HonestProposal E rho (fgsaInterface p c) s b) :
    ∃ Bfg : FGBlock (Fin p.n), eraseFG Bfg = b ∧ OpeningCarrier_W p c E rho s b Bfg ∧
      Bfg.slot = s ∧
      (∃ rows, HonestCarrier p c E rho s b rows ∧ Bfg.rows = rows.filterMap RowWire.toRow?) ∧
      ∃ st, proposalStateAt p c E rho s = some st ∧
        FGSA.fgBlockOf st b.parent = some Bfg.parent ∧ Bfg.parent ∈ st.fg.TF := by
  obtain ⟨j, N, heN, hj, hem, hst, _hslot, hb, _hrows⟩ := kmid_proposal_read p c E rho hs hp
  let v := V2.D.proposerOf rho (fgsaInterface p c) s
  let st := ((fgsa p c).clock (V2.D.Run.stateBefore E rho j v) (SA.proposalTime p.toParams s)).st
  have hinv : CStoreInv p st := (storeBundle_postClock E rho j v _).cstore
  have hhead : proposerHead p st s ∈ st.base.blocks := by
    rw [proposerHead_def]
    exact getHead_stored p st hinv _ _
  obtain ⟨P, hP, hPe⟩ := (hinv.baseTree _).mp hhead
  have hpar : b.parent = proposerHead p st s := by rw [hb]; rfl
  have hok : rowsOk b N.rows = true := by
    rw [hb, _hrows]
    exact rowsOk_node_packBody _ _ _ _ _
  have hne : b ≠ .genesis := by rw [hb]; intro h; cases h
  have hlook : FGSA.fgBlockOf st b.parent = some P :=
    (fgBlockOf_spec p st hinv _ P).mpr ⟨hP, hPe.trans hpar.symm⟩
  let o : Obj p := ⟨.seat (.prop s) ⟨0, Nat.one_pos⟩, .proposal N⟩
  have hemit : V2.D.Run.emits E rho v o (V2.D.proposalTime (fgsaInterface p c) s) :=
    ⟨j, hj, hem⟩
  refine ⟨fgBlock P b N.rows, eraseFG_fgBlock hne (hPe.trans hpar.symm) N.rows hok,
    (OpeningCarrier_W_def p c E rho s b _).mpr
      ⟨o, N, st, P, hemit, heN, rfl, hst, hlook, rfl⟩, ?_,
    ⟨N.rows, ⟨hp, o, N, hemit, rfl, heN, rfl⟩, rfl⟩, st, hst, hlook, hP⟩
  rw [fgBlock_slot, hb]
  rfl

/-! ### Step group A: erased identity and ancestry -/

omit [DecidableEq V] in
/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. FINAL 22:1188–1197. FG roots are content hashes; erasure is injective.
DC: INTENTIONAL: the flat FG wire keeps one erasure. -/
theorem kmid_eraseFG_inj {A B : FGBlock (Fin p.n)} (h : eraseFG A = eraseFG B) : A = B :=
  eraseFG_injective h

omit [DecidableEq V] in
/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. FINAL 22:1188–1197. Erased ancestry lifts to FG ancestry.
DC: INTENTIONAL: the flat FG wire keeps one erasure. -/
theorem kmid_lift_preceq {A B : FGBlock (Fin p.n)}
    (h : Block.Preceq (eraseFG A) (eraseFG B)) : FGBlock.Preceq A B :=
  eraseFG_preceq_iff.mp h

omit [DecidableEq V] in
/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. FINAL 22:1188–1197. A block's parent precedes it, also at genesis.
DC: SAME chain order. -/
theorem kmid_parent_preceq (B : FGBlock (Fin p.n)) : FGBlock.Preceq B.parent B := by
  cases B with
  | genesis => exact preceq_refl _
  | node P s root x rs => exact preceq_parent_node P s root x rs

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
FINAL 22:1188–1197. H3 at an action slot fixes the FG action source.
DC: INTENTIONAL: the erased H3 source lifts by root identity. -/
theorem kmid_source_of_exact {v : Slot} {X : FGBlock (Fin p.n)}
    (hex : ExactService p c E rho v (eraseFG X))
    (hh : SA.gateTime p.toParams v ≤ rho.horizon) (r : Nat) (hv : v = r * p.R) :
    ∀ x ∈ rho.honest,
      confirmedReaderAtIdx p c E rho x (afterTicksIdx rho (SA.gateTime p.toParams v))
        (SA.gateTime p.toParams v) →
      actionSourceFG p c E rho x r = some (some X) := by
  intro x hx hreader
  have hs := ((hex.2 hh x hx hreader).2.2.2.2) r hv
  change (actionSourceFG p c E rho x r).map (Option.map eraseFG) = some (some (eraseFG X)) at hs
  obtain ⟨o, ho, he⟩ := Option.map_eq_some_iff.mp hs
  obtain ⟨C, hC, hCe⟩ := Option.map_eq_some_iff.mp he
  rw [ho, hC, kmid_eraseFG_inj p hCe]

/-! ### Step group B: raw row heights -/

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
FINAL 22:946–956. The empty pair has no height; a height names an entry.
DC: INTENTIONAL: the wire height is optional for an empty pair. -/
theorem kmid_rowHeight_entry (a : RowWire p.n) (h : Nat) (hh : rowHeight a = some h) :
    ∃ e, namedEntry a.payload.height_pair = some (h, e) := by
  have hdef : rowHeight a =
      (match a.payload.height_pair with | .empty => none | .vote h _ _ => some h) := rowHeight_def a
  rw [hdef] at hh
  cases hp : a.payload.height_pair with
  | empty => rw [hp] at hh; cases hh
  | vote k e timeout =>
    rw [hp] at hh
    have hk : k = h := Option.some.inj hh
    subst k
    exact ⟨e, by rw [namedEntry_def]⟩

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
FINAL 22:946–956. An honest row height is its action source height.
DC: INTENTIONAL: the source-discipline name channel is an explicit input. -/
theorem kmid_row_source_height
    (hnames : ∀ j x r a e, HonestRowAt p c E rho j x r a →
      namedEntry a.payload.height_pair = some e →
      ∃ C, actionSourceFG p c E rho x r = some (some C) ∧
        e = ((heightView p C).h, (heightView p C).T_h.root))
    {j : Nat} {x : V} {r : Nat} {a : RowWire p.n} {h : Nat}
    (ha : HonestRowAt p c E rho j x r a) (hh : rowHeight a = some h) :
    ∃ C, actionSourceFG p c E rho x r = some (some C) ∧ h = (heightView p C).h := by
  obtain ⟨e, he⟩ := kmid_rowHeight_entry p a h hh
  obtain ⟨C, hC, hCe⟩ := hnames j x r a _ ha he
  exact ⟨C, hC, congrArg Prod.fst hCe⟩

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
FINAL 22:923–947. Rows before the opening action stay at or below its height.
DC: INTENTIONAL: H2 transfers every high earlier source below the opening parent. -/
theorem kmid_rows_below_opening (w : HealingWitness) (h2 : TCarrier p c E rho w)
    (hnames : ∀ j x r a e, HonestRowAt p c E rho j x r a →
      namedEntry a.payload.height_pair = some e →
      ∃ C, actionSourceFG p c E rho x r = some (some C) ∧
        e = ((heightView p C).h, (heightView p C).T_h.root))
    (q : Nat) (A₀ : FGBlock (Fin p.n))
    (hA : HonestProposal E rho (fgsaInterface p c) (q * p.R) (eraseFG A₀))
    (hhigh : w.M + 1 ≤ (heightView p A₀).h) :
    ∀ j x r a h, r < q → HonestRowAt p c E rho j x r a → rowHeight a = some h →
      h ≤ (heightView p A₀).h := by
  intro j x r a h hr ha hh
  obtain ⟨C, hC, rfl⟩ := kmid_row_source_height p c E rho hnames ha hh
  by_cases hc : w.M + 1 ≤ (heightView p C).h
  · have hR := p.RLarge
    have hslot : r * p.R + 2 ≤ q * p.R := by
      have := Nat.mul_le_mul_right p.R (Nat.succ_le_of_lt hr)
      rw [Nat.succ_mul] at this
      omega
    have hpre := h2 x r C (q * p.R) (eraseFG A₀) ((HonestRowAt_def p c E rho _ _ _ _).mp ha).1
      hC hc hA hslot
    rw [eraseFG_parent] at hpre
    have hCP := kmid_lift_preceq p hpre
    exact ((fgCertificateLaws p).height.h_mono hCP).trans
      ((fgCertificateLaws p).height.h_mono (kmid_parent_preceq p A₀))
  · omega

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
FINAL 22:946–956. Rows at an action with a fixed source have that source height.
DC: INTENTIONAL: the source-discipline name channel is an explicit input. -/
theorem kmid_rows_at_source
    (hnames : ∀ j x r a e, HonestRowAt p c E rho j x r a →
      namedEntry a.payload.height_pair = some e →
      ∃ C, actionSourceFG p c E rho x r = some (some C) ∧
        e = ((heightView p C).h, (heightView p C).T_h.root))
    (r : Nat) (X : FGBlock (Fin p.n))
    (hsrc : ∀ x ∈ rho.honest, actionSourceFG p c E rho x r = some (some X)) :
    ∀ j x a h, HonestRowAt p c E rho j x r a → rowHeight a = some h →
      h = (heightView p X).h := by
  intro j x a h ha hh
  obtain ⟨C, hC, rfl⟩ := kmid_row_source_height p c E rho hnames ha hh
  rw [hsrc x ((HonestRowAt_def p c E rho _ _ _ _).mp ha).1] at hC
  cases Option.some.inj (Option.some.inj hC)
  rfl

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. FINAL 22:946–956. An honest row is the client output of its action tick.
DC: INTENTIONAL: the run uses event-indexed emission. -/
theorem kmid_row_action {j : Nat} {x : V} {r : Nat} {a : RowWire p.n}
    (ha : HonestRowAt p c E rho j x r a) :
    rho.events[j]? = some (.tick x (p.actionTime r)) ∧
      (attest p
        ((fgsa p c).clock (V2.D.Run.stateBefore E rho j x) (p.actionTime r)).st
        (V2.D.Run.stateBefore E rho j x).record ⟨0, p.nPos⟩).1 = some a.payload := by
  obtain ⟨_, hj, hem⟩ := (HonestRowAt_def p c E rho _ _ _ _).mp ha
  refine ⟨hj, ?_⟩
  rw [(V2.D.Run.step_tick_eq E rho hj).2] at hem
  change ofRow p a ∈ (if E.awake x (p.actionTime r) then
    (duties p (p.actionTime r)).flatMap (fun d =>
      (rho.ownSeats (RunDuty.signLabel d) x).filterMap (fun i =>
        (act p c ((fgsa p c).clock (V2.D.Run.stateBefore E rho j x) (p.actionTime r))
          d (rho.input x (p.actionTime r))).map
            (fun m => (⟨.seat (RunDuty.signLabel d) i, m⟩ : Obj p)))) ++
      ([] : List (Obj p)) else []) at hem
  split at hem
  · rw [List.append_nil] at hem
    obtain ⟨d, _, hem⟩ := List.mem_flatMap.mp hem
    obtain ⟨i, _, hm⟩ := List.mem_filterMap.mp hem
    obtain ⟨m, hm, ho⟩ := Option.map_eq_some_iff.mp hm
    have hp : m = .row a.payload := congrArg V2.Signed.payload ho
    subst m
    cases d with
    | headAction s =>
      change (if joinedNow p _ then some (Msg.head _) else none) =
        some (Msg.row a.payload) at hm
      split at hm <;> cases hm
    | fgAction r' =>
      change (attest p _ _ _).1.map Msg.row = some (.row a.payload) at hm
      obtain ⟨payload, hb, he⟩ := Option.map_eq_some_iff.mp hm
      have heq : payload = a.payload := Msg.row.inj he
      subst payload
      dsimp only [fgsa] at hb ⊢
      exact hb
    | propAction s =>
      change (if joinedNow p _ then (propose p _ s).map (withApp p _) else none) =
        some (.row a.payload) at hm
      split at hm
      · obtain ⟨m, hm, he⟩ := Option.map_eq_some_iff.mp hm
        obtain ⟨_, _, _, _, heq, _, _⟩ := rowsOk_withApp _ _ _ (by rw [hm]; exact congrArg some he)
        cases heq
      · cases hm
  · exact (List.not_mem_nil hem).elim

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
FINAL 22:952–958. An honest row has a height, and its finality height is smaller.
DC: SAME client filter of the finality pair below the height pair. -/
theorem kmid_row_fin_lt {j : Nat} {x : V} {r : Nat} {a : RowWire p.n}
    (ha : HonestRowAt p c E rho j x r a) :
    ∃ h, rowHeight a = some h ∧ ∀ f, finHeight a = some f → f < h := by
  obtain ⟨_hj, hb⟩ := kmid_row_action p c E rho ha
  obtain ⟨row, hrow, hbody⟩ := Option.map_eq_some_iff.mp hb
  obtain ⟨h, T, tm, _hp, hroweq, _, _, _⟩ :=
    KitFG.createRowOnce_released p.E p.cfg _ ⟨0, p.nPos⟩ _ _ hrow
  subst hroweq
  refine ⟨h, ?_, ?_⟩
  · have hdef : rowHeight a =
        (match a.payload.height_pair with | .empty => none | .vote h _ _ => some h) :=
      rowHeight_def a
    rw [hdef, ← hbody]
    rfl
  · intro f hf
    have hdef : finHeight a = a.payload.finality_pair.map (·.height) := finHeight_def a
    rw [hdef, ← hbody] at hf
    change ((finality_pair _ _).filter (fun p => decide (p.height < h))).map (·.height) =
      some f at hf
    obtain ⟨fp, hfp, hfe⟩ := Option.map_eq_some_iff.mp hf
    have hlt := of_decide_eq_true (Option.filter_eq_some_iff.mp hfp).2
    rw [← hfe]
    exact hlt

variable [Fintype V]

/-! ### Step group E: held chains through the actual HEAD read -/

omit [DecidableEq V] [Fintype V] in
/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
FINAL 22:923–947. A tick at the cut time is before the read-phase cut.
DC: INTENTIONAL: event phases order ticks before same-time deliveries. -/
theorem kmid_tick_lt_afterTicks (hs : V2.D.ScheduleWellFormed E rho)
    {i : Nat} {v : V} {t' t : Time} (hi : rho.events[i]? = some (.tick v t')) (ht : t' ≤ t) :
    i < afterTicksIdx rho t := by
  have heq : afterTicksIdx rho t = FGCompose.afterTicksIdx rho t := rfl
  rw [heq]
  exact FGCompose.tick_lt_afterTicks E rho hs hi ht

omit [Fintype V] in
/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
FINAL 22:1226,954–956. The exact HEAD read holds its block at the tick index.
DC: INTENTIONAL: the stored HEAD target is the admitted FG block. -/
theorem kmid_head_held {v : Slot}
    {X : FGBlock (Fin p.n)} (hex : ExactService p c E rho v (eraseFG X))
    (hh : SA.voteTime p.toParams v ≤ rho.horizon) (x : V) (hx : x ∈ rho.honest)
    (hjoined : joinedAt p E rho x v (SA.voteTime p.toParams v)) :
    ∃ i, rho.events[i]? = some (.tick x (SA.voteTime p.toParams v)) ∧
      X ∈ (V2.D.Run.stateBefore E rho i x).st.fg.TF := by
  have hhead := hex.1 hh x hx hjoined
  change (postClock E rho x (SA.voteTime p.toParams v)).map
    (fun nd => FGSA.headVote p nd.st v) = some (eraseFG X) at hhead
  have hhead' : (FGCompose.postClock E rho x (SA.voteTime p.toParams v)).map
      (fun nd => (fgsaCoreReads p c).headVote nd v) = some ((fgsaCoreReads p c).erase X) := by
    rw [fgsaCoreReads_def, ← (fgsa_eventReads_eq_compose E rho x _).2.2.2.2.2.1]
    exact hhead
  have h := FGCompose.head_held (fgsaCoreReads p c) E rho (fgsaCoreLaws p c)
    (fgsaHeadLaws p c E rho) hhead'
  rw [fgsaCoreReads_def] at h
  exact h

omit [Fintype V] in
/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
FINAL 22:1265–1304. The FG action source is a stored block of the read state.
DC: INTENTIONAL: the joint source picks from the filtered stored tree. -/
theorem kmid_source_mem_TF {st : State p.n} {C : FGBlock (Fin p.n)}
    (h : FGSA.fgSource p st = some C) : C ∈ st.fg.TF := by
  have hsrc : (fgsaCoreReads p unitCodec).source ⟨st, RecordOnce.initial⟩ = some C := by
    rw [fgsaCoreReads_def]
    exact h
  have hm := FGCompose.source_mem_TF (fgsaCoreReads p unitCodec) (fgsaCoreLaws p unitCodec) hsrc
  rw [fgsaCoreReads_def] at hm
  exact hm

omit [Fintype V] in
/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
FINAL 22:1265–1304. An honest action source is held at its own action tick,
before the read-phase cut of that action. DC: INTENTIONAL: the run reads the source
at the post-clock state of the action tick. -/
theorem kmid_source_held_at_tick (hs : V2.D.ScheduleWellFormed E rho) {x : V} {r : Nat}
    {C : FGBlock (Fin p.n)} (hx : x ∈ rho.honest)
    (hsrc : actionSourceFG p c E rho x r = some (some C)) :
    ∃ i, rho.events[i]? = some (.tick x (p.actionTime r)) ∧
      i < afterTicksIdx rho (p.actionTime r) ∧ HeldAt p c E rho i x C := by
  rw [actionSourceFG_def, postClock_def, preTick_def] at hsrc
  cases hi : V2.D.Run.tickIdx? rho x (p.actionTime r) with
  | none => simp only [hi, Option.map_none] at hsrc; contradiction
  | some i =>
    simp only [hi, Option.map_some, Option.some.injEq] at hsrc
    have hj := V2.D.Run.tickIdx?_spec hi
    have hm := kmid_source_mem_TF p hsrc
    change C ∈ (FGSA.clock p _ _).fg.TF at hm
    rw [FGSA.clock_fg] at hm
    exact ⟨i, hj, kmid_tick_lt_afterTicks p c E rho hs hj le_rfl, hx, hm⟩

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
FINAL 22:954–956,1226. The exact HEAD read gives raw chain rows before a later cut.
DC: INTENTIONAL: an actual honest strict-before read holds every carrier. -/
theorem kmid_chainRows_of_head (hs : V2.D.ScheduleWellFormed E rho)
    {v : Slot} {X : FGBlock (Fin p.n)} (hex : ExactService p c E rho v (eraseFG X))
    (hh : SA.voteTime p.toParams v ≤ rho.horizon) (x : V) (hx : x ∈ rho.honest)
    (hjoined : joinedAt p E rho x v (SA.voteTime p.toParams v))
    (cut : Time) (hcut : SA.voteTime p.toParams v < cut) :
    ChainRowsBefore p c E rho X cut := by
  obtain ⟨i, hi, hX⟩ := kmid_head_held p c E rho hex hh x hx hjoined
  intro W hW _row _hrow
  refine ⟨x, SA.voteTime p.toParams v, hx, hcut, ?_⟩
  have hanc := KitFG.ancestor_closed_of_parent_closed _
    (cstoreInv_stateBefore E rho i x).fg.closed X hX W hW
  rw [Gen.V2.Duty.HoldsBefore_def]
  rw [← finality_joined_tick_read p c E rho hs hi hjoined]
  exact hanc

omit [Fintype V] in
/-- The joined HEAD target remains in durable storage at each later cut. -/
theorem kmid_head_held_from (hs : V2.D.ScheduleWellFormed E rho)
    {v : Slot} {X : FGBlock (Fin p.n)} (hex : ExactService p c E rho v (eraseFG X))
    (hh : SA.voteTime p.toParams v ≤ rho.horizon) (x : V) (hx : x ∈ rho.honest)
    (hjoined : joinedAt p E rho x v (SA.voteTime p.toParams v))
    (k : Nat) (t : Time) (ht : SA.voteTime p.toParams v ≤ t) (hk : afterTicksIdx rho t ≤ k) :
    X ∈ (storeAt p c E rho k x).fg.TF := by
  obtain ⟨i, hi, hX⟩ := kmid_head_held p c E rho hex hh x hx hjoined
  exact (fgsa_store_durable p c E rho
    ((kmid_tick_lt_afterTicks p c E rho hs hi ht).le.trans hk) x).1 hX

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
FINAL 22:948–958. Linked unit-weight seats bound the faulty weight.
DC: INTENTIONAL: FG-SA uses linked seats. -/
theorem kmid_faulty_weight (base : BaseSet p c E rho)
    (hQ : Gen.Pure.FaultQ p.n (Gen.V2.Duty.faulty rho).card) :
    p.E.weightOf (Finset.univ \ honestSeats p c rho) < p.E.q := by
  classical
  have hsub : (Finset.univ \ honestSeats p c rho).image (rho.seatOf (.base .fg)) ⊆
      Gen.V2.Duty.faulty rho := by
    intro z hz
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hz
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ?_⟩
    have hn := (Finset.mem_sdiff.mp hi).2
    exact fun hh => hn ((kmid_honestSeats_mem p c rho i).mpr hh)
  have hinj : Function.Injective (fun i : Fin p.n => rho.seatOf (.base .fg) i) :=
    (base.linked.toCStar (.base .fg) trivial).1
  have hc : (Finset.univ \ honestSeats p c rho).card ≤
      (Gen.V2.Duty.faulty rho).card :=
    (Finset.card_image_of_injective _ hinj).symm.trans_le (Finset.card_le_card hsub)
  have hw : p.E.weightOf (Finset.univ \ honestSeats p c rho) =
      (Finset.univ \ honestSeats p c rho).card := by
    change (∑ _ ∈ Finset.univ \ honestSeats p c rho, (1 : Nat)) = _
    simp
  have hq : p.E.q = Gen.Pure.qF p.n :=
    (toWeights_q p.E).symm.trans (unit_toWeights_q p.n)
  rw [hw, hq]
  exact hc.trans_lt hQ.lt

omit [Fintype V] in
/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
FINAL 22:948–958. A seat outside the faulty set is honest.
DC: INTENTIONAL: FG-SA uses linked seats. -/
theorem kmid_honest_seat (u : Row (Fin p.n))
    (hf : u.signer ∉ Finset.univ \ honestSeats p c rho) :
    rho.seatOf (.base .fg) u.signer ∈ rho.honest := by
  classical
  have hm : u.signer ∈ honestSeats p c rho := by
    by_contra hn
    exact hf (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hn⟩)
  exact (kmid_honestSeats_mem p c rho u.signer).mp hm

omit [DecidableEq V] [Fintype V] in
/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
FINAL 22:954–956. Decode the exact signed wire payload.
DC: INTENTIONAL: FG-SA uses seat-authenticated wires. -/
theorem kmid_wire_decode {a : RowWire p.n} {u : Row (Fin p.n)}
    (ha : a.toRow? = some u) :
    a = ⟨.seat .fg u.signer, .vote ⟨u.height_pair, u.finality_pair⟩⟩ := by
  rcases a with ⟨auth, ⟨⟨ah, af⟩⟩⟩
  cases auth with
  | none => cases ha
  | proposer s => cases ha
  | seat label k =>
    cases label with
    | head s => cases ha
    | fg =>
      have he : (⟨k, ah, af⟩ : Row (Fin p.n)) = u := Option.some.inj ha
      subst u
      rfl

omit [Fintype V] in
/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
FINAL 22:954–956. The emission tick gives its exact action time.
DC: INTENTIONAL: the run uses event-indexed emission. -/
theorem kmid_event_time {j r : Nat} {z : V} {a : RowWire p.n}
    (hj : HonestRowAt p c E rho j z r a) :
    eventTime rho j = some (p.actionTime r) := by
  have hdef : eventTime rho j = rho.events[j]?.map V2.Event.time := eventTime_def rho j
  rw [hdef, ((HonestRowAt_def p c E rho _ _ _ _).mp hj).2.1]
  rfl

omit [DecidableEq V] [Fintype V] in
/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
FINAL 22:954–956. A matching pair has the stated wire height.
DC: INTENTIONAL: the wire height is optional for an empty pair. -/
theorem kmid_matching_height {u : Row (Fin p.n)} {a : RowWire p.n}
    {y : Nat} {T : BlockId} (ha : a.toRow? = some u)
    (hm : u.height_pair.matchesEntry y T = true) : rowHeight a = some y := by
  rw [kmid_wire_decode p ha]
  have hdef : ∀ b : RowWire p.n, rowHeight b =
      (match b.payload.height_pair with | .empty => none | .vote h _ _ => some h) :=
    fun b => rowHeight_def b
  rw [hdef]
  cases hp : u.height_pair with
  | empty => simp only [hp, NamedHeightPair.matchesEntry] at hm; contradiction
  | vote h U timeout =>
    have hh : h = y := by
      simp only [hp, NamedHeightPair.matchesEntry, decide_eq_true_eq] at hm
      exact hm.1
    change some h = some y
    rw [hh]

omit [DecidableEq V] [Fintype V] in
/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
FINAL 22:923–947. Deliveries before the read-phase cut are strictly earlier.
DC: INTENTIONAL: event phases order ticks before same-time deliveries. -/
theorem kmid_delivery_before_afterTicks (hs : V2.D.ScheduleWellFormed E rho)
    {k : Nat} {t t' : Time} {x : V} {o : (fgsa p c).Object}
    (hk : k < afterTicksIdx rho t) (he : rho.events[k]? = some (.deliver x o t')) :
    t' < t := by
  have hf := V2.D.Engine.filter_eq_take hs (cutPred t) (fun e f hk hf =>
    decide_eq_true (hk.trans (of_decide_eq_true hf)))
  have hm : (V2.Event.deliver x o t' : V2.Event V (fgsa p c).Object) ∈
      rho.events.filter (cutPred t) := by
    rw [hf]
    apply List.mem_of_getElem? (i := k)
    change (rho.events.take (afterTicksIdx rho t))[k]? = some _
    rw [List.getElem?_take_of_lt hk]
    exact he
  have hkey : toLex (t', (2 : Nat)) ≤ toLex (t, (1 : Nat)) :=
    of_decide_eq_true (List.mem_filter.mp hm).2
  rcases Prod.Lex.toLex_le_toLex.mp hkey with h | ⟨_, h⟩
  · exact h
  · omega

variable (horigin : ∀ (i : Nat) (x : V) (B : FGBlock (Fin p.n)),
    HeldAt p c E rho i x B → ∀ u ∈ chainRows B,
      ∃ (a : RowWire p.n) (r : Nat),
        a.toRow? = some u ∧ a.auth = .seat .fg u.signer ∧
        ∃ k o t, k < i ∧ rho.events[k]? = some (.deliver x o t) ∧
          ∀ z : V, RowSigner p c rho a z → z ∈ rho.honest →
            HonestRowBefore p c E rho i z r a ∧ p.actionTime r ≤ t)

include horigin in
/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
FINAL 22:923–938. A held chain has no crossing above its honest row bound.
DC: INTENTIONAL: timed raw origin replaces a selected-pool bound. -/
theorem kmid_held_height_le (base : BaseSet p c E rho)
    (faultQ : Gen.Pure.FaultQ p.n (Gen.V2.Duty.faulty rho).card) (m : Nat) (cut : Time)
    (hrows : ∀ j z r a h t, HonestRowAt p c E rho j z r a →
      rowHeight a = some h → eventTime rho j = some t → t < cut → h ≤ m)
    (i : Nat) (x : V) (B : FGBlock (Fin p.n)) (hheld : HeldAt p c E rho i x B)
    (hbefore : ∀ k o t, k < i → rho.events[k]? = some (.deliver x o t) → t < cut) :
    (heightView p B).h ≤ m + 1 := by
  by_contra hn
  obtain ⟨C, _hCB, _hC, Q, hQ, hw⟩ := (fgCertificateLaws p).height.height_crossing
    B (m + 1) (by simp only [Height]; omega) (by simp only [Height] at *; omega)
  obtain ⟨seat, hs, hf⟩ := honest_in_quorum p.E (Finset.univ \ honestSeats p c rho)
    hQ (kmid_faulty_weight p c E rho base faultQ)
  obtain ⟨W, u, hWB, hu, hsign, hm⟩ := hw seat hs
  have hfu : u.signer ∉ Finset.univ \ honestSeats p c rho := hsign ▸ hf
  have hhonest := kmid_honest_seat p c rho u hfu
  obtain ⟨a, r, ha, har, k, o, t, hki, hk, he⟩ :=
    horigin i x B hheld u (mem_chainRows_of_carrier hWB hu)
  have hsigner : RowSigner p c rho a (rho.seatOf (.base .fg) u.signer) :=
    (RowSigner_def p c rho a _).mpr ⟨u.signer, har, rfl⟩
  obtain ⟨hb, hrt⟩ := he _ hsigner hhonest
  obtain ⟨j, _hji, hj⟩ := (HonestRowBefore_def p c E rho _ _ _ _).mp hb
  have ht := hrt.trans_lt (hbefore k o t hki hk)
  have bound := hrows j _ r a (m + 1) (p.actionTime r) hj
    (kmid_matching_height p ha hm) (kmid_event_time p c E rho hj) ht
  omega

include horigin in
/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
FINAL 22:923–947. The cap holds through the read phase of the cut, before deliveries.
DC: INTENTIONAL: event phases make same-time rows undeliverable before the read. -/
theorem kmid_held_cap_afterTicks (base : BaseSet p c E rho)
    (faultQ : Gen.Pure.FaultQ p.n (Gen.V2.Duty.faulty rho).card) (m : Nat) (cut : Time)
    (hrows : ∀ j z r a h t, HonestRowAt p c E rho j z r a →
      rowHeight a = some h → eventTime rho j = some t → t < cut → h ≤ m)
    (i : Nat) (x : V) (B : FGBlock (Fin p.n))
    (hcut : i ≤ afterTicksIdx rho cut) (hheld : HeldAt p c E rho i x B) :
    (heightView p B).h ≤ m + 1 :=
  kmid_held_height_le p c E rho horigin base faultQ m cut hrows i x B hheld
    (fun _ _ _ hki hk => kmid_delivery_before_afterTicks p c E rho
      base.valid.toScheduleWellFormed (hki.trans_le hcut) hk)

include horigin in
/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
FINAL 22:952–958,1224–1226. No held finality certificate at or above y before the cut.
DC: INTENTIONAL: the active W certificate supplies the exact finality height. -/
theorem kmid_held_finality_afterTicks (base : BaseSet p c E rho)
    (faultQ : Gen.Pure.FaultQ p.n (Gen.V2.Duty.faulty rho).card) (y : Nat) (cut : Time)
    (hy : 0 < y)
    (hrows : ∀ j z r a f t, HonestRowAt p c E rho j z r a →
      finHeight a = some f → eventTime rho j = some t → t < cut → f < y)
    (i : Nat) (x : V) (W : FGBlock (Fin p.n))
    (hcut : i ≤ afterTicksIdx rho cut) (hheld : HeldAt p c E rho i x W) :
    (finalityView p W).h_F < y := by
  by_contra hn
  have hF : y ≤ (finalityView p W).h_F := Nat.le_of_not_gt hn
  let R := fun u : Row (Fin p.n) => ∃ j z r a t,
    HonestRowAt p c E rho j z r a ∧ a.toRow? = some u ∧ eventTime rho j = some t ∧ t < cut
  obtain ⟨u, _hu, _hf, ho, hp⟩ := finalityCap_row_of_certificate p.E
    (heightView p) (finalityView p) (fgCertificateLaws p)
    (Finset.univ \ honestSeats p c rho) (kmid_faulty_weight p c E rho base faultQ)
    y W R (by
      intro u hu hf
      have hhonest := kmid_honest_seat p c rho u hf
      obtain ⟨a, r, ha, har, k, o, t, hki, hk, he⟩ := horigin i x W hheld u hu
      have hsigner : RowSigner p c rho a (rho.seatOf (.base .fg) u.signer) :=
        (RowSigner_def p c rho a _).mpr ⟨u.signer, har, rfl⟩
      obtain ⟨hb, hrt⟩ := he _ hsigner hhonest
      obtain ⟨j, _hji, hj⟩ := (HonestRowBefore_def p c E rho _ _ _ _).mp hb
      exact ⟨j, _, r, a, p.actionTime r, hj, ha, kmid_event_time p c E rho hj,
        hrt.trans_lt (kmid_delivery_before_afterTicks p c E rho
          base.valid.toScheduleWellFormed (hki.trans_le hcut) hk)⟩) hy hF
  obtain ⟨j, z, r, a, t, hj, ha, ht, hlt⟩ := ho
  have hfin : finHeight a = some (finalityView p W).h_F := by
    rw [kmid_wire_decode p ha]
    rw [finHeight_def]
    rw [hp]
    rfl
  exact (Nat.not_lt.mpr hF) (hrows j z r a _ t hj hfin ht hlt)

/-! ### Step group C: the height batch at a parent that stays -/

omit [DecidableEq V] [Fintype V] in
/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
FINAL 22:583–610. The parent fold state reads the parent's height entry.
DC: INTENTIONAL: R6W reads the window parent state with the child slot. -/
private theorem kmid_parentFold_eq (s : Slot) (H : FGBlock (Fin p.n)) :
    parentFoldState p s H = Window.parentState p p.K_W H s := rfl

omit [DecidableEq V] [Fintype V] in
/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
FINAL 22:583–610. The parent fold state has the height and entry of the height view.
DC: INTENTIONAL: R6W reads the window parent state with the child slot. -/
theorem kmid_parentFold_height (s : Slot) (H : FGBlock (Fin p.n)) :
    (parentFoldState p s H).h = (heightView p H).h ∧
      (parentFoldState p s H).T_h = (heightView p H).T_h := by
  rw [kmid_parentFold_eq, Window.parentState_def, heightView_def, Window.projectHeight_def]
  exact ⟨rfl, rfl⟩

omit [DecidableEq V] [Fintype V] in
/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
FINAL 22:583–610. The decoded row of a seat-authenticated wire.
DC: INTENTIONAL: FG-SA uses seat-authenticated wires. -/
theorem kmid_wire_toRow {a : RowWire p.n} {i : Fin p.n} (ha : a.auth = .seat .fg i) :
    a.toRow? = some ⟨i, a.payload.height_pair, a.payload.finality_pair⟩ := by
  rcases a with ⟨auth, ⟨body⟩⟩
  dsimp only at ha
  subst auth
  rfl

omit [Fintype V] in
/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
FINAL 22:583–603. A post-clock proposer read is reachable.
DC: INTENTIONAL: the proposer read is an indexed post-clock state. -/
theorem kmid_proposal_reachable {s : Slot} {st : State p.n}
    (hs : proposalStateAt p c E rho s = some st) : Reachable p st := by
  change (postClock E rho _ _).map (·.st) = some st at hs
  rw [postClock_def, preTick_def] at hs
  cases hk : V2.D.Run.tickIdx? rho (V2.D.proposerOf rho (fgsaInterface p c) s)
      (V2.D.proposalTime (fgsaInterface p c) s) with
  | none => rw [hk] at hs; cases hs
  | some k =>
      rw [hk] at hs
      rw [← Option.some.inj hs]
      exact reachable_postClock E rho k _ _

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. FINAL 22:583–610. Rows on a stored chain that name an entry lie above that
entry,
when the chain stays at the entry height. DC: INTENTIONAL: stored R6W validity. -/
theorem kmid_rows_above_entry (st : State p.n) (hr : Reachable p st)
    (k : RowKind) (y : Nat) (U P : FGBlock (Fin p.n)) (hP : P ∈ st.fg.TF)
    (hPh : (heightView p P).h = y) (hUP : FGBlock.Preceq U P) :
    ∀ i W, FGBlock.Preceq W P → (∃ row ∈ W.rows, RowNames p k row i y U) →
      FGBlock.Preceq U W.parent := by
  intro i W hWP ⟨row, hrow, hnames⟩
  have hinv := storeInvariant p st hr
  have hW : W ∈ st.fg.TF := ancestor_closed_of_parent_closed _ hinv.fg.closed P hP W hWP
  cases W with
  | genesis => exact (List.not_mem_nil hrow).elim
  | node Q t root x rs =>
  have hv := stored_r6wW p hr Q t root x rs hW row hrow
  have hpair : ∃ timeout, row.height_pair = .vote y U.root timeout := by
    obtain ⟨_, hk⟩ := hnames
    cases k with
    | target => exact ⟨_, hk⟩
    | progress => obtain ⟨timeout, ht⟩ := hk; exact ⟨timeout, ht⟩
  obtain ⟨timeout, hp⟩ := hpair
  have hQP : FGBlock.Preceq Q P := preceq_trans (preceq_parent_node Q t root x rs) hWP
  have hQh : (heightView p Q).h ≤ y := hPh ▸ (fgCertificateLaws p).height.h_mono hQP
  have hdh : (Window.derive p p.K_W Q).h = (heightView p Q).h := by
    rw [heightView_def, Window.projectHeight_def]
  have hdT : (Window.derive p p.K_W Q).T_h = (heightView p Q).T_h := by
    rw [heightView_def, Window.projectHeight_def]
  rw [Window.r6w_def] at hv
  rcases Bool.or_eq_true_iff.mp hv with hm | hm
  · rw [Window.heightMatch_def, hp] at hm
    simp only [NamedHeightPair.matchesEntry, decide_eq_true_eq] at hm
    have hroot : U.root = (heightView p Q).T_h.root := hdT ▸ hm.2
    have hU : U = (heightView p Q).T_h := viewRootInj_TF p st hinv _ _ ⟨P, hP, hUP⟩
      ⟨P, hP, preceq_trans ((fgCertificateLaws p).height.entry_preceq Q) hQP⟩ hroot
    change FGBlock.Preceq U Q
    rw [hU]
    exact (fgCertificateLaws p).height.entry_preceq Q
  · rw [Window.staleUseful_def, hp] at hm
    cases hf : row.finality_pair with
    | none => rw [hf] at hm; cases hm
    | some fp =>
      rw [hf] at hm
      have hb := (Bool.and_eq_true_iff.mp hm).1
      have hlt : y < (Window.derive p p.K_W Q).h := (of_decide_eq_true hb).2
      rw [hdh] at hlt
      simp only [Height] at *
      omega

/-! ### Step group D: slot chains of stored blocks -/

omit [Fintype V] in
/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
FINAL 22:43–54,1056–1059. A stored accepted block has a smaller parent slot.
DC: INTENTIONAL: accepted proposal validity supplies strict parent-slot growth. -/
theorem kmid_stored_parent_slot (hE : V2.D.ExecutionValid E rho)
    (i : Nat) (v : V) (C : Block)
    (hm : C ∈ (V2.D.Run.stateBefore E rho i v).st.base.blocks) (hg : C ≠ .genesis) :
    C.parent.slot < C.slot := by
  obtain ⟨w, hw, hb, j, o, t, -, hd, ho, -⟩ := fgsa_stored_block_origin E rho i v C hm hg
  obtain ⟨r, N, rfl, -⟩ := (metaInv_stateBefore E rho i v).wireTree w hw
  have hQ : N.erase = C := Option.some.inj hb
  rw [← hQ]
  have hf := hE.wire j v o t hd
  change FGSA.wellFormed p (toWire p o) = true at hf
  rw [ho] at hf
  exact of_decide_eq_true
    (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp
      (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hf).1).1).1).1).2

omit [Fintype V] in
/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
FINAL 22:43–54,1056–1059. A stored FG block has increasing slots along its chain.
DC: INTENTIONAL: accepted proposal validity supplies strict parent-slot growth. -/
theorem kmid_stored_slotChain (hE : V2.D.ExecutionValid E rho) (i : Nat) (v : V)
    (X : FGBlock (Fin p.n)) (hX : X ∈ (V2.D.Run.stateBefore E rho i v).st.fg.TF) :
    SlotChain X := by
  intro W hW hg
  have hinv := cstoreInv_stateBefore E rho i v
  have hWm := ancestor_closed_of_parent_closed _ hinv.fg.closed X hX W hW
  have hb : eraseFG W ∈ (V2.D.Run.stateBefore E rho i v).st.base.blocks :=
    (hinv.baseTree _).mpr ⟨W, hWm, rfl⟩
  have hlt := kmid_stored_parent_slot p c E rho hE i v (eraseFG W) hb
    (fun h => hg (eraseFG_eq_genesis.mp h))
  rwa [eraseFG_parent, eraseFG_slot, eraseFG_slot] at hlt

omit [DecidableEq V] [Fintype V] in
/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. FINAL 22:43–54. Slots do not decrease along a slot chain.
DC: INTENTIONAL: FG-SA height coverage has explicit chain-history inputs. -/
theorem kmid_slot_le_of_preceq {W X : FGBlock (Fin p.n)} (hX : SlotChain X)
    (hW : FGBlock.Preceq W X) : W.slot ≤ X.slot := by
  induction X with
  | genesis =>
    rw [preceq_genesis] at hW
    rw [hW]
  | node P s root x rs ih =>
    by_cases he : W = .node P s root x rs
    · rw [he]
    · have hWP := preceq_parent_of_preceq_node hW he
      have hP : SlotChain P := fun Z hZ hg =>
        hX Z (preceq_trans hZ (preceq_parent_node P s root x rs)) hg
      have hlt := hX (.node P s root x rs) (preceq_refl _) (by intro h; cases h)
      exact (ih hP hWP).trans (le_of_lt hlt)

omit [DecidableEq V] [Fintype V] in
/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. FINAL 22:43–54. A strict ancestor has a strictly smaller slot.
DC: INTENTIONAL: FG-SA height coverage has explicit chain-history inputs. -/
theorem kmid_slot_lt_of_strict {W X : FGBlock (Fin p.n)} (hX : SlotChain X)
    (hW : FGBlock.Preceq W X) (hne : W ≠ X) : W.slot < X.slot := by
  cases X with
  | genesis => exact (hne (preceq_genesis.mp hW)).elim
  | node P s root x rs =>
    have hWP := preceq_parent_of_preceq_node hW hne
    have hP : SlotChain P := fun Z hZ hg =>
      hX Z (preceq_trans hZ (preceq_parent_node P s root x rs)) hg
    have hlt := hX (.node P s root x rs) (preceq_refl _) (by intro h; cases h)
    exact (kmid_slot_le_of_preceq p hP hWP).trans_lt hlt

/-! ### Step group C: the honest batch of a stored parent -/

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. FINAL 22:583–610,886–915. Complete honest target rows at a stored parent form a
batch.
DC: SAME height coverage; INTENTIONAL: complete earlier-or-current send-once witnesses. -/
theorem kmid_batchPrem (ΔF : Time) (base : BaseSet p c E rho)
    (faultQ : Gen.Pure.FaultQ p.n (Gen.V2.Duty.faulty rho).card)
    (hfault : (Gen.V2.Duty.faulty rho).card ≤ (p.n - 1) / 3)
    (deltaF : E.Δ ≤ ΔF) (receipt : TRowsReceipt p c E rho ΔF)
    (q y : Nat) (U X : FGBlock (Fin p.n))
    (horizon : max (p.actionTime q) E.t_GST + ΔF ≤ SA.proposalTime p.toParams X.slot ∧
      SA.proposalTime p.toParams X.slot ≤ rho.horizon)
    (carrier : ∃ rows, HonestCarrier p c E rho X.slot (eraseFG X) rows ∧
      X.rows = rows.filterMap RowWire.toRow?)
    (st : State p.n) (hst : proposalStateAt p c E rho X.slot = some st)
    (hlook : FGSA.fgBlockOf st (eraseFG X).parent = some X.parent)
    (hparTF : X.parent ∈ st.fg.TF)
    (after : q * p.R + 2 ≤ X.slot) (entry : EntryAt p U y)
    (path : FGBlock.Preceq U X.parent) (hpar : (heightView p X.parent).h = y)
    (rows : ∀ x ∈ rho.honest, ∃ j r a, r ≤ q ∧ HonestRowAt p c E rho j x r a ∧
      RowComplete p c rho x a ∧ NamesEntry p .target a y U) :
    BatchPrem p c E rho ΔF .target q y U X := by
  have hinj : Function.Injective (rho.seatOf (.base .fg)) :=
    (base.linked.toCStar (.base .fg) trivial).1
  have hσ := kmid_parentFold_height p X.slot X.parent
  have hT : (heightView p X.parent).T_h = U :=
    ((fgCertificateLaws p).height.entry_plateau path (entry.1.trans hpar.symm)).symm.trans
      entry.2
  refine ⟨base, faultQ, deltaF, receipt, horizon, carrier, after, ?_, entry, path, ?_⟩
  · refine ⟨honestSeats p c rho, subset_rfl, kmid_honest_quorum p c rho base.linked hfault, ?_⟩
    intro i hi
    obtain ⟨j, r, a, hr, ha, hcomp, hnames⟩ :=
      rows _ ((kmid_honestSeats_mem p c rho i).mp hi)
    obtain ⟨i', hauth, hseat⟩ := (RowSigner_def p c rho a _).mp hcomp.2
    have hii : i' = i := hinj hseat
    subst i'
    have hpair : a.payload.height_pair = .vote y U.root false := hnames
    have hrow := kmid_wire_toRow p hauth
    refine ⟨j, r, a, p.actionTime r, hr, ha, hauth, hnames, kmid_event_time p c E rho ha, rfl,
      ?_, ?_⟩
    · refine (ValidForParent_def p c E rho _ _ a).mpr ⟨st, X.parent, hst, hlook, ?_⟩
      refine (Window.rowValidW_iff _ a).mpr ⟨_, hrow, Or.inl ?_⟩
      rw [Window.heightMatch_def]
      change (a.payload.height_pair).matchesEntry _ _ = true
      rw [hpair, hσ.1, hσ.2, hpar, hT]
      simp [NamedHeightPair.matchesEntry]
    · refine (HeightMatch_def p c E rho _ _ a).mpr ⟨st, X.parent, hst, hlook, ?_⟩
      rw [hpair, hσ.1, hσ.2, hpar, hT]
      rfl
  · intro i _ W hW hrow
    exact kmid_rows_above_entry p st (kmid_proposal_reachable p c E rho hst) .target y U X.parent
      hparTF hpar path i W hW hrow

/-! ### Step group A: kernel clock bounds -/

omit [DecidableEq V] [Fintype V] in
/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
FINAL 22:217–220. A round count of periods is the slot clock of its first slot.
DC: INTENTIONAL: FG-SA action times use its fixed round grid. -/
theorem kmid_period_eq (r : Nat) :
    (r : Time) * P p = 4 * p.Δ * ((r * p.R : Nat) : Time) := by
  change (r : Time) * (4 * (p.R : Time) * p.Δ) = _
  push_cast
  ring

variable {p c E rho} in
/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
FINAL 22:1173–1177,1199–1211. Kernel clock facts from the kernel premise.
DC: INTENTIONAL: the W kernel uses the row delay ΔF. -/
theorem kmid_kernel_bounds {G ΔF : Time} {pt : KernelPt}
    (hK : KernelPrem_W p c G ΔF E rho pt) :
    0 ≤ ΔF ∧ 2 ≤ kappaF p ΔF ∧ kappaF p ΔF ≤ p.R ∧ 2 ≤ p.R ∧
      pt.w.sStar + 2 ≤ pt.r * p.R ∧
      E.t_GST ≤ SA.proposalTime p.toParams (pt.r * p.R) ∧
      p.actionTime (pt.r + 2) ≤ rho.horizon := by
  have hΔ := p.deltaPos
  have hF0 : 0 ≤ ΔF := by
    have h1 := hK.set.deltaF
    have h2 := hK.set.base.delta
    linarith
  have hκ := kappaF_ge_two p ΔF hF0
  have hκR := hK.bound.kappa_le_R
  have hstart : SA.gateTime p.toParams pt.w.u ≤ (pt.r : Time) * P p := hK.start
  rw [kmid_period_eq] at hstart
  have hu : pt.w.u < pt.r * p.R := by
    by_contra hn
    have hle := kmid_slot_scale_le p (Nat.le_of_not_gt hn)
    change 4 * p.Δ * (pt.w.u : Time) + 6 * p.Δ ≤ _ at hstart
    linarith
  have hlow := hK.input.wit.proposal_lower
  refine ⟨hF0, hκ, hκR, hκ.trans hκR, le_of_lt (lt_of_le_of_lt hlow hu), ?_, ?_⟩
  · have h1 := hK.input.wit.after_gst
    change E.t_GST ≤ SA.gateTime p.toParams pt.w.u at h1
    exact h1.trans hstart
  · have hhor := hK.hhor
    rw [kernelDeadlineW_def, kmid_period_eq] at hhor
    have hb := (betaF_bounds p ΔF hF0).1
    rw [kmid_actionTime_eq]
    linarith

variable {p c E rho} in
/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
FINAL 22:1173–1177. Every slot read up to the window end is inside the run.
DC: INTENTIONAL: the W kernel horizon covers its window reads. -/
theorem kmid_slot_horizon {G ΔF : Time} {pt : KernelPt}
    (hK : KernelPrem_W p c G ΔF E rho pt) {s : Slot} (hs : s ≤ (pt.r + 2) * p.R) :
    SA.proposalTime p.toParams s ≤ rho.horizon ∧ SA.voteTime p.toParams s ≤ rho.horizon ∧
      SA.gateTime p.toParams s ≤ rho.horizon := by
  have hA := (kmid_kernel_bounds hK).2.2.2.2.2.2
  rw [kmid_actionTime_eq] at hA
  have hle := kmid_slot_scale_le p hs
  have hΔ := p.deltaPos
  change 4 * p.Δ * (s : Time) ≤ _ ∧ 4 * p.Δ * (s : Time) + p.Δ ≤ _ ∧
    4 * p.Δ * (s : Time) + 6 * p.Δ ≤ _
  refine ⟨?_, ?_, ?_⟩ <;> linarith

variable {p c E rho} in
/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
FINAL 22:1173–1177. Every slot read from the opening on is after GST.
DC: INTENTIONAL: the W kernel starts after GST. -/
theorem kmid_slot_gst {G ΔF : Time} {pt : KernelPt}
    (hK : KernelPrem_W p c G ΔF E rho pt) {s : Slot} (hs : pt.r * p.R ≤ s) :
    E.t_GST ≤ SA.proposalTime p.toParams s := by
  have hG := (kmid_kernel_bounds hK).2.2.2.2.2.1
  have hle := kmid_slot_scale_le p hs
  change E.t_GST ≤ 4 * p.Δ * (s : Time)
  change E.t_GST ≤ 4 * p.Δ * ((pt.r * p.R : Nat) : Time) at hG
  linarith

variable {p c E rho} in
/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
FINAL 22:1171–1180. An honest window slot has an actual honest proposal.
DC: INTENTIONAL: the FG-SA proposer duty always builds a block at a positive slot. -/
theorem kmid_window_proposal {G ΔF : Time} {pt : KernelPt}
    (hK : KernelPrem_W p c G ΔF E rho pt) {s : Slot}
    (hslot : Gen.V2.Duty.HonestSlot rho (fgsaInterface p c) s)
    (hlo : pt.r * p.R ≤ s) (hhi : s ≤ (pt.r + 2) * p.R) :
    ∃ b, HonestProposal E rho (fgsaInterface p c) s b := by
  have hh := (kmid_slot_horizon hK hhi).1
  have hcut : E.t_GST ≤ slotStartZ p ((s : Int) - 1) := by
    have hstart := hK.start
    rw [kmid_period_eq] at hstart
    have hlow : (pt.w.sStar : Int) + 2 ≤ (pt.w.u : Int) := by
      exact_mod_cast hK.input.wit.proposal_lower
    have hsync := hK.input.wit.synchronous
    have hle := kmid_slot_scale_le p hlo
    change 4 * p.Δ * (pt.w.u : Int) + 6 * p.Δ ≤ _ at hstart
    change E.t_GST ≤ 4 * p.Δ * (pt.w.sStar : Int) + p.Δ at hsync
    change E.t_GST ≤ 4 * p.Δ * ((s : Int) - 1)
    nlinarith [p.deltaPos]
  exact kmid_honest_proposal_exists p c E rho hK.set.base.valid.toScheduleWellFormed
    hK.set.base.delta s hslot
    (finality_recovery_joined p c E rho hK.set hslot.2 hcut (kmid_slot_gst hK hlo) hh) hh

variable {p c E rho} in
/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
FINAL 22:1188–1197. H3 serves every honest window proposal.
DC: INTENTIONAL: the healed AC service is an explicit input. -/
theorem kmid_window_exact {G ΔF : Time} {pt : KernelPt}
    (hK : KernelPrem_W p c G ΔF E rho pt) {s : Slot} {b : Block}
    (hb : HonestProposal E rho (fgsaInterface p c) s b) (hlo : pt.r * p.R ≤ s) :
    ExactService p c E rho s b :=
  hK.input.ac.h3 s b hb ((kmid_kernel_bounds hK).2.2.2.2.1.trans hlo)

/-! ### Step group B: raw cuts from round bounds -/

omit [Fintype V] in
/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
FINAL 22:923–947. A round-indexed row bound is a raw cut at the next action.
DC: INTENTIONAL: an honest row has the exact time of its action tick. -/
theorem kmid_rows_cut (m Q : Nat)
    (hrow : ∀ j x r a h, r ≤ Q → HonestRowAt p c E rho j x r a → rowHeight a = some h →
      h ≤ m) :
    (∀ j x r a h t, HonestRowAt p c E rho j x r a → rowHeight a = some h → m + 1 ≤ h →
      eventTime rho j = some t → p.actionTime (Q + 1) ≤ t) ∧
    (∀ j z r a h t, HonestRowAt p c E rho j z r a → rowHeight a = some h →
      eventTime rho j = some t → t < p.actionTime (Q + 1) → h ≤ m) := by
  have key : ∀ j z r a t, HonestRowAt p c E rho j z r a → eventTime rho j = some t →
      t < p.actionTime (Q + 1) → r ≤ Q := by
    intro j z r a t ha ht hlt
    rw [kmid_event_time p c E rho ha] at ht
    cases Option.some.inj ht
    exact Nat.le_of_lt_succ ((kmid_action_strictMono p).lt_iff_lt.mp hlt)
  refine ⟨?_, ?_⟩
  · intro j x r a h t ha hh hm ht
    by_contra hn
    have := hrow j x r a h (key j x r a t ha ht (lt_of_not_ge hn)) ha hh
    omega
  · intro j z r a h t ha hh ht hlt
    exact hrow j z r a h (key j z r a t ha ht hlt) ha hh

omit [Fintype V] in
/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
FINAL 22:952–958. A round-indexed row bound caps the finality heights below it.
DC: SAME client filter of the finality pair below the height pair. -/
theorem kmid_fin_cut (m Q : Nat)
    (hrow : ∀ j x r a h, r ≤ Q → HonestRowAt p c E rho j x r a → rowHeight a = some h →
      h ≤ m) :
    (∀ j x r a f t, HonestRowAt p c E rho j x r a → finHeight a = some f → m ≤ f →
      eventTime rho j = some t → p.actionTime (Q + 1) ≤ t) ∧
    (∀ j z r a f t, HonestRowAt p c E rho j z r a → finHeight a = some f →
      eventTime rho j = some t → t < p.actionTime (Q + 1) → f < m) := by
  have hcut := (kmid_rows_cut p c E rho m Q hrow).2
  have key : ∀ j z r a f t, HonestRowAt p c E rho j z r a → finHeight a = some f →
      eventTime rho j = some t → t < p.actionTime (Q + 1) → f < m := by
    intro j z r a f t ha hf ht hlt
    obtain ⟨h, hh, hlt'⟩ := kmid_row_fin_lt p c E rho ha
    exact (hlt' f hf).trans_le (hcut j z r a h t ha hh ht hlt)
  refine ⟨?_, key⟩
  intro j x r a f t ha hf hm ht
  by_contra hn
  have := key j x r a f t ha hf ht (lt_of_not_ge hn)
  omega

omit [DecidableEq V] [Fintype V] in
/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
FINAL 22:217–220. A HEAD read at or before a round's first slot precedes its action.
DC: INTENTIONAL: FG-SA action times use its fixed round grid. -/
theorem kmid_vote_lt_action {s : Slot} {r : Nat} (h : s ≤ r * p.R) :
    SA.voteTime p.toParams s < p.actionTime r := by
  have hle := kmid_slot_scale_le p h
  have hΔ := p.deltaPos
  rw [kmid_actionTime_eq]
  change 4 * p.Δ * (s : Time) + p.Δ < _
  linarith

omit [DecidableEq V] [Fintype V] in
/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
FINAL 22:217–220. A proposal at or before a round's first slot precedes its action.
DC: INTENTIONAL: FG-SA action times use its fixed round grid. -/
theorem kmid_proposal_le_action {s : Slot} {r : Nat} (h : s ≤ r * p.R) :
    SA.proposalTime p.toParams s ≤ p.actionTime r := by
  have hle := kmid_slot_scale_le p h
  have hΔ := p.deltaPos
  rw [kmid_actionTime_eq]
  change 4 * p.Δ * (s : Time) ≤ _
  linarith

variable {p c E rho} in
/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
FINAL 22:886–915,1199–1211. Rows of an action are received before a proposal κ slots later.
DC: INTENTIONAL: the W kernel uses the row delay ΔF. -/
theorem kmid_batch_horizon {G ΔF : Time} {pt : KernelPt}
    (hK : KernelPrem_W p c G ΔF E rho pt) {r : Nat} {s : Slot}
    (hG : E.t_GST ≤ p.actionTime r) (hs : r * p.R + kappaF p ΔF ≤ s)
    (hs' : s ≤ (pt.r + 2) * p.R) :
    max (p.actionTime r) E.t_GST + ΔF ≤ SA.proposalTime p.toParams s ∧
      SA.proposalTime p.toParams s ≤ rho.horizon := by
  refine ⟨?_, (kmid_slot_horizon hK hs').1⟩
  rw [max_eq_left hG, kmid_actionTime_eq]
  have hcov := kmid_kappa_cover p ΔF (kmid_kernel_bounds hK).1
  have hle := kmid_slot_scale_le p hs
  have hsplit : 4 * p.Δ * ((r * p.R + kappaF p ΔF : Nat) : Time) =
      4 * p.Δ * ((r * p.R : Nat) : Time) + 4 * p.Δ * (kappaF p ΔF : Time) := by
    push_cast
    ring
  change _ ≤ 4 * p.Δ * (s : Time)
  linarith

end AvailableChain.FGSA.Run
end
