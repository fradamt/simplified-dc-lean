module
public import AvailableChainFGSAProofs.Proofs.Foundations.Carrier
public import AvailableChainFGSAProofs.Proofs.Shared.Channels
public import AvailableChainFGSAProofs.Proofs.Shared.StoreRun
public import AvailableChainFGSARun.Proofs.Receipts
public import AvailableChainFGSA.Model.RowValidity
public import AvailableChainFGSAClaims.Statements.Fold

public section

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

variable (p : Params) {In V : Type} [DecidableEq V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. BP01:109–114: a height row in an actual held carrier sets its matching bit,
which persists forward while the key stays fixed. DC: ChainState/
MatchingProgress.lean:147 gives the converse witness.
INTENTIONAL: this FG-SA adapter uses the forward KitFG
laws and an explicit occurrence; a parent-chain row alone is insufficient.
The held premise records the occurrence in the run; the fold law is pure. -/
theorem fgsa_rowBitPersist (target : Bool) (i : Nat) (x : V)
    (parent B W : FGBlock (Fin p.n)) (s : Slot) (root : BlockId) (body : Nat)
    (rows : List (Row (Fin p.n))) (a : Row (Fin p.n))
    (_held : HeldAt p c E rho i x (.node parent s root body rows))
    (ha : a ∈ rows) (hCB : FGBlock.Preceq (.node parent s root body rows) B)
    (hm : if target then a.height_pair = .vote (heightView p parent).h
      (heightView p parent).T_h.root false else
      a.height_pair.matchesEntry (heightView p parent).h (heightView p parent).T_h.root = true)
    (hPB : (heightView p parent).h = (heightView p B).h ∧
      (heightView p parent).T_h.root = (heightView p B).T_h.root)
    (hBW : FGBlock.Preceq B W)
    (hstate : (heightView p B).h = (heightView p W).h ∧
      (heightView p B).T_h.root = (heightView p W).T_h.root) :
    a.signer ∈ (if target then (heightView p W).target_participation
      else (heightView p W).progress) :=
  row_bit_persist p target parent W s root body rows a ha (KitFG.preceq_trans hCB hBW) hm
    ⟨hPB.1.trans hstate.1, hPB.2.trans hstate.2⟩

private theorem rowService_receipt_on (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (_hDelta : E.Δ = p.Δ) (hExecution : V2.D.ExecutionValid E rho)
    (hNoRestart : V2.D.NoRestart rho) (dl : Time → Time) (cut : Time)
    (i : Fin p.n) (body : RowPayload) (t : Time) (w : V)
    (hD : Gen.V2.Duty.DeliveryWithinOn E rho isRowObject dl cut)
    (hT : Gen.V2.Duty.Trigger E rho (ofRow p ⟨.seat .fg i, body⟩) t)
    (hw : w ∈ rho.honest) (hcut : dl t ≤ cut) (hlt : t < dl t) :
    (⟨.seat .fg i, body⟩ : RowWire p.n) ∈
      (V2.D.Run.stateBeforeTime E rho (dl t) w).st.rowPool := by
  let o := ofRow p (⟨.seat .fg i, body⟩ : RowWire p.n)
  let C := fgsaTimelyClock p c
  have hS := hExecution.toScheduleWellFormed
  have htime : 0 ≤ t ∧ t ≤ rho.horizon := by
    rcases hT with ⟨v, _, k, he, _⟩ | ⟨v, _, k, ha⟩
    · exact hS.in_horizon _ (List.mem_of_getElem? he)
    · obtain ⟨parent, he, _⟩ := ha.1
      exact hS.in_horizon _ (List.mem_of_getElem? he)
  have hfloor0 : 0 ≤ Gen.V2.Duty.pubFloor E t :=
    mul_nonneg (Int.ediv_nonneg htime.1 (le_of_lt E.Δ_pos)) (le_of_lt E.Δ_pos)
  have hAdm : C.actTime o ≤ Gen.V2.Duty.pubFloor E t := by
    rw [fgsaTimelyClock_actTime p c o]
    exact hfloor0
  have hfloorpub : V2.PublicTime E (Gen.V2.Duty.pubFloor E t) := by
    refine ⟨(t / E.Δ).toNat, ?_⟩
    rw [Int.toNat_of_nonneg (Int.ediv_nonneg htime.1 (le_of_lt E.Δ_pos))]
    rfl
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp (hS.tick_total w hw _ hfloorpub hfloor0
    ((Gen.V2.Duty.pubFloor_le E t).trans htime.2))
  have hprocessed := Gen.V2.Duty.accepted_by_deadline_on E rho isRowObject dl cut
    o t w hD (by trivial) hT hw hcut hlt hS
    ((fgsaHooks p c).excludes_stable E rho hS) (processed_stable E rho hS)
    (fgsa_hReady_of_not_block (by intro s N h; cases h)
      (fgsa_hWF_of_delivery hExecution.wire))
    (fgsaAcceptance p c) C (fun k => cstoreInv_stateBefore E rho k w) hAdm j hj
    (hNoRestart.restartFree w j _) rfl
  exact of_decide_eq_true hprocessed

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Strict receipt for every emitted row, including pre-GST rows and sleepers.
DC: SAME max deadline and horizon; INTENTIONAL FG adapter with bound ΔF. -/
theorem fgsa_rowService_receipt (ΔF : Time) (hΔ : E.Δ = p.Δ)
    (hv : V2.D.ExecutionValid E rho) (hnr : V2.D.NoRestart rho)
    (hsync : Gen.V2.Duty.PartialSynchronyBy E rho (fgsaDelay E.Δ ΔF))
    (hΔF : E.Δ ≤ ΔF)
    {j : Nat} {y : V} {r : Nat} {a : RowWire p.n}
    (ha : HonestRowAt p c E rho j y r a)
    (hhor : max (p.actionTime r) E.t_GST + ΔF ≤ rho.horizon)
    (x : V) (hx : x ∈ rho.honest) :
    HeldBefore p c E rho x a (max (p.actionTime r) E.t_GST + ΔF) := by
  obtain ⟨i, hi⟩ := honestRow_auth p c rho E hv ha
  obtain ⟨auth, body⟩ := a
  dsimp only at hi
  subst auth
  have hD := Gen.V2.Duty.deliveryWithinOn_of_partialSynchronyBy E rho hsync
    isRowObject ΔF (by
      intro o ho
      cases o with
      | mk auth m => cases m <;> first | rfl | exact ho.elim)
  apply Or.inl
  exact rowService_receipt_on p c E rho hΔ hv hnr _ rho.horizon i body
    (p.actionTime r) x hD (Or.inl ⟨y, ha.1, j, ha.2⟩) hx hhor
    ((le_max_left _ _).trans_lt (lt_add_of_pos_right _ (E.Δ_pos.trans_le hΔF)))

private theorem rowService_carrier_read {s : Slot} {Q : Block} {rows : List (RowWire p.n)}
    (hs : V2.D.ScheduleWellFormed E rho) (hc : HonestCarrier p c E rho s Q rows) :
    ∃ j, rho.events[j]? = some (.tick (V2.D.proposerOf rho (fgsaInterface p c) s)
        (SA.proposalTime p.toParams s)) ∧
      let st := ((fgsa p c).clock
        (V2.D.Run.stateBefore E rho j (V2.D.proposerOf rho (fgsaInterface p c) s))
        (SA.proposalTime p.toParams s)).st
      proposalStateAt p c E rho s = some st ∧ st.slot p = s ∧
        rows = proposalRows p st Q.parent := by
  obtain ⟨hp, o, N, ⟨j, hj, hem⟩, hpay, heN, hrows⟩ := hc
  subst Q rows
  have hs0 : 0 < s := hp.1.1
  change rho.events[j]? = some (.tick _ (SA.proposalTime p.toParams s)) at hj
  rw [(V2.D.Run.step_tick_eq E rho hj).2] at hem
  obtain ⟨auth, m⟩ := o
  change m = _ at hpay
  subst m
  cases auth with
  | none =>
    change (⟨.none, _⟩ : Obj p) ∈ (if E.awake _ _ then
      (duties p _).flatMap (fun d => (rho.ownSeats (RunDuty.signLabel d) _).filterMap
        (fun i => ((fgsa p c).act ((fgsa p c).clock _ _) d (rho.input _ _)).map
          (fun m => ⟨.seat (RunDuty.signLabel d) i, m⟩))) ++ [] else []) at hem
    split at hem
    · rw [List.append_nil] at hem
      obtain ⟨d, _, hm⟩ := List.mem_flatMap.mp hem
      obtain ⟨i, _, hm⟩ := List.mem_filterMap.mp hm
      obtain ⟨m, _, he⟩ := Option.map_eq_some_iff.mp hm
      cases he
    · exact (List.not_mem_nil hem).elim
  | seat l seat =>
    obtain ⟨_, _, d, _, ht, hm⟩ :=
      (V2.D.Engine.mem_tick_seat_iff E rho _ _ _ l seat _).mp hem
    cases d with
    | headAction v => cases hm
    | fgAction r =>
      change (attest p _ _ _).1.map Msg.row = some (.proposal N) at hm
      obtain ⟨body, _, he⟩ := Option.map_eq_some_iff.mp hm
      cases he
    | propAction s' =>
      have hss : s' = s := by
        change 4 * p.Δ * (s' : Int) = 4 * p.Δ * (s : Int) at ht
        have hΔ : (0 : Int) < p.Δ := p.deltaPos
        have he : (s' : Int) = s := by nlinarith
        exact_mod_cast he
      subst s'
      let nd := V2.D.Run.stateBefore E rho j
        (V2.D.proposerOf rho (fgsaInterface p c) s)
      let st := ((fgsa p c).clock nd (SA.proposalTime p.toParams s)).st
      have htick : V2.D.Run.tickIdx? rho (V2.D.proposerOf rho (fgsaInterface p c) s)
          (SA.proposalTime p.toParams s) = some j := by
        obtain ⟨k, hk⟩ : ∃ k, V2.D.Run.tickIdx? rho
            (V2.D.proposerOf rho (fgsaInterface p c) s)
            (SA.proposalTime p.toParams s) = some k := by
          rw [V2.D.Run.tickIdx?, ← Option.isSome_iff_exists, List.findIdx?_isSome, List.any_eq_true]
          exact ⟨_, List.mem_of_getElem? hj, by simp⟩
        exact (fgsa_tick_unique E rho hs (V2.D.Run.tickIdx?_spec hk) hj) ▸ hk
      refine ⟨j, hj, ?_, fgsa_proposal_slot nd s, ?_⟩
      · change (postClock E rho _ _).map (·.st) = some st
        rw [proposalTime_fgsa p c s, postClock_def, preTick_def]
        change (((V2.D.Run.tickIdx? rho _ (SA.proposalTime p.toParams s)).map
          (fun k => V2.D.Run.stateBefore E rho k _)).map
          (fun nd : Node p => (fgsa p c).clock nd (SA.proposalTime p.toParams s))).map
          (fun nd : Node p => nd.st) = some st
        rw [htick]
        rfl
      · change (propose p st s).map (withApp p _) = some (.proposal N) at hm
        rw [propose_head p st s (Nat.ne_of_gt hs0)] at hm
        simp only [Option.map_map] at hm
        obtain ⟨P, hP, he⟩ := Option.map_eq_some_iff.mp hm
        cases Msg.proposal.inj he
        have hparent := (namedByErase?_sound st (proposerHead p st s) P hP).2
        change proposalRows p st (proposerHead p st s) = proposalRows p st P.erase
        rw [hparent]

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
R6W and a row height at least the parent height imply current-height matching.
The stale arm contradicts the height bound. -/
theorem validForParent_currentHeightMatch {s : Slot} {Q : Block} {a : RowWire p.n}
    (st : State p.n) (H : FGBlock (Fin p.n))
    (hs : proposalStateAt p c E rho s = some st)
    (hH : fgBlockOf st Q.parent = some H)
    (hv : Window.rowValidW (parentFoldState p s H) a = true)
    (h : Nat) (T : BlockId) (hn : namedEntry a.payload.height_pair = some (h, T))
    (hh : (parentFoldState p s H).h ≤ h) : HeightMatch p c E rho s Q a := by
  obtain ⟨b, hb, hm⟩ := (Window.rowValidW_iff _ a).mp hv
  have he : b.height_pair = a.payload.height_pair := by
    cases a with
    | mk auth body =>
      cases auth with
      | none => cases hb
      | proposer s => cases hb
      | seat l i => cases l with
        | head s => cases hb
        | fg => cases hb; rfl
  refine ⟨st, H, hs, hH, ?_⟩
  rw [← he] at hn ⊢
  cases hp : b.height_pair with
  | empty => rw [hp] at hn; cases hn
  | vote k U timeout =>
      rw [hp] at hn
      have hname : k = h ∧ U = T := Prod.mk.inj (Option.some.inj hn)
      rcases hm with hm | hm
      · have keys : k = (parentFoldState p s H).h ∧
            U = (parentFoldState p s H).T_h.root := by
          simpa [Window.heightMatch_def, hp, NamedHeightPair.matchesEntry] using hm
        exact congrArg some (Prod.ext keys.1 keys.2)
      · cases hf : b.finality_pair with
        | none => simp [Window.staleUseful_def, hp, hf] at hm
        | some fp =>
            have hlt : k < (parentFoldState p s H).h := by
              have hbounds : (fp.height < k ∧ k < (parentFoldState p s H).h) ∧
                  Window.windowMatch (parentFoldState p s H) b = true := by
                simpa only [Window.staleUseful_def, hp, hf, Bool.and_eq_true,
                  decide_eq_true_eq] using hm
              exact hbounds.1.2
            exact (Nat.not_lt_of_ge hh (hname.1 ▸ hlt)).elim

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Exact signed-row selection from the pool or stored blocks, with R6.
DC: INTENTIONAL FG-SA transport adapter; no quorum or row-count premise. -/
theorem fgsa_tRowsSelect (hv : V2.D.ExecutionValid E rho) : TRowsSelect p c E rho := by
  intro s Q rows j y r a hc _ha hvalid hheld
  obtain ⟨k, hk, hread, hslot, hrows⟩ := rowService_carrier_read p c E rho
    hv.toScheduleWellFormed hc
  obtain ⟨st, hs, hh⟩ := hheld
  have he := Option.some.inj (hs.symm.trans hread)
  subst st
  obtain ⟨st', H, hs', hH, hvalid⟩ := hvalid
  have he := Option.some.inj (hs'.symm.trans hread)
  subst st'
  let st := ((fgsa p c).clock
    (V2.D.Run.stateBefore E rho k (V2.D.proposerOf rho (fgsaInterface p c) s))
    (SA.proposalTime p.toParams s)).st
  by_cases hon : a ∈ chainWireRows st Q.parent
  · exact Or.inr ⟨_, hread, hon⟩
  · left
    rw [hrows]
    change a ∈ proposalRowsFor p _ _ Q.parent
    apply (mem_proposalRowsFor_iff p _ _ _ _).mpr
    exact ⟨H, hH, hh, hslot.symm ▸ hvalid, hon⟩

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Receipt transport to a later proposal uses no second delivery delay.
DC: SAME no-restart storage transport; INTENTIONAL exact FG wire selector. -/
theorem fgsa_rowsReceipt_carriage (hv : V2.D.ExecutionValid E rho)
    (hnr : V2.D.NoRestart rho) {s : Slot} {Q : Block} {rows : List (RowWire p.n)}
    {j : Nat} {y : V} {r : Nat} {a : RowWire p.n} {d : Time}
    (hc : HonestCarrier p c E rho s Q rows) (ha : HonestRowAt p c E rho j y r a)
    (hvalid : ValidForParent p c E rho s Q a)
    (hheld : HeldBefore p c E rho (V2.D.proposerOf rho (fgsaInterface p c) s) a d)
    (hd : d ≤ SA.proposalTime p.toParams s) :
    a ∈ rows ∨ onParentChain p c E rho s Q a := by
  obtain ⟨k, hk, hread, _hslot, _hrows⟩ := rowService_carrier_read p c E rho
    hv.toScheduleWellFormed hc
  let x := V2.D.proposerOf rho (fgsaInterface p c) s
  have hik : V2.D.Run.idxBefore rho d ≤ k := by
    by_contra hn
    have ht := (Gen.V2.Duty.index_lt_idxBefore_iff hv.toScheduleWellFormed hk d).mp
      (Nat.lt_of_not_ge hn)
    exact (not_lt.mpr hd) ht
  change rowHeld p (V2.D.Run.stateBeforeTime E rho d x).st a at hheld
  rw [← Gen.V2.Duty.stateBefore_idxBefore E rho d hv.toScheduleWellFormed] at hheld
  have hcumul := fgsa_store_cumulative p c E rho hnr hik x
  apply fgsa_tRowsSelect p c E rho hv s Q rows j y r a hc ha hvalid
  refine ⟨_, hread, ?_⟩
  rcases hheld with hp | hb
  · left
    change a ∈ (FGSA.clock p (V2.D.Run.stateBefore E rho k x).st _).rowPool
    rw [clock_rowPool]
    exact hcumul.2.2.2.2.2.subset hp
  · right
    change a ∈ allBlockRows _ at hb ⊢
    change a ∈ allBlockRows (FGSA.clock p (V2.D.Run.stateBefore E rho k x).st _)
    unfold allBlockRows at hb ⊢
    rw [clock_proposals]
    obtain ⟨xs, hxs, ha⟩ := List.mem_flatten.mp hb
    obtain ⟨w, hw, hdec⟩ := List.mem_filterMap.mp hxs
    exact List.mem_flatten.mpr ⟨xs,
      List.mem_filterMap.mpr ⟨w, hcumul.2.2.2.2.1.subset hw, hdec⟩, ha⟩

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
T-ROWS receipt under the bound row family, including pre-GST sends.
DC: SAME strict max deadline and finite horizon; INTENTIONAL row family. -/
theorem fgsa_tRowsReceipt (ΔF : Time) (hΔ : E.Δ = p.Δ)
    (hv : V2.D.ExecutionValid E rho) (hnr : V2.D.NoRestart rho)
    (hsync : Gen.V2.Duty.PartialSynchronyBy E rho (fgsaDelay E.Δ ΔF))
    (hΔF : E.Δ ≤ ΔF) : TRowsReceipt p c E rho ΔF := by
  intro j y r a ha hhor x hx
  exact fgsa_rowService_receipt p c E rho ΔF hΔ hv hnr hsync hΔF ha hhor x hx

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Post-GST receipt and carriage at one row delay.
DC: SAME strict receipt; INTENTIONAL R6 selector and independent row delay. -/
theorem fgsa_tRowsSync (ΔF : Time) (hΔ : E.Δ = p.Δ)
    (hv : V2.D.ExecutionValid E rho) (hnr : V2.D.NoRestart rho)
    (hsync : Gen.V2.Duty.PartialSynchronyBy E rho (fgsaDelay E.Δ ΔF))
    (hΔF : E.Δ ≤ ΔF) : TRowsSync p c E rho ΔF := by
  intro j y r a ha hg
  have receipt := fgsa_tRowsReceipt p c E rho ΔF hΔ hv hnr hsync hΔF j y r a ha
  rw [max_eq_left hg] at receipt
  refine ⟨receipt, ?_⟩
  intro s Q rows hc hvalid htime
  obtain ⟨k, hk, _⟩ := rowService_carrier_read p c E rho hv.toScheduleWellFormed hc
  have hhor := htime.trans (hv.toScheduleWellFormed.in_horizon _ (List.mem_of_getElem? hk)).2
  exact fgsa_rowsReceipt_carriage p c E rho hv hnr hc ha hvalid
    (receipt hhor _ hc.1.1.2) htime

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
The three T-ROWS clauses share one bound row family.
DC: INTENTIONAL FG transport adapter; SAME receipt and storage premises. -/
theorem fgsa_tRows (ΔF : Time) (hΔ : E.Δ = p.Δ)
    (hv : V2.D.ExecutionValid E rho) (hnr : V2.D.NoRestart rho)
    (hsync : Gen.V2.Duty.PartialSynchronyBy E rho (fgsaDelay E.Δ ΔF))
    (hΔF : E.Δ ≤ ΔF) : TRows p c E rho ΔF :=
  ⟨fgsa_tRowsSelect p c E rho hv, fgsa_tRowsSync p c E rho ΔF hΔ hv hnr hsync hΔF,
    fgsa_tRowsReceipt p c E rho ΔF hΔ hv hnr hsync hΔF⟩

private theorem rowService_chain_occurrence (st : State p.n) (hmeta : MetaInv p st)
    (H : FGBlock (Fin p.n)) (a : RowWire p.n) (b : Row (Fin p.n))
    (hd : a.toRow? = some b) (ha : a ∈ chainWireRows st (eraseFG H)) :
    ∃ W, FGBlock.Preceq W H ∧ b ∈ W.rows := by
  obtain ⟨rows, hrs, ha⟩ := List.mem_flatten.mp ha
  obtain ⟨o, ho, hrows⟩ := List.mem_filterMap.mp hrs
  obtain ⟨s, N, rfl, _hok, _hparent, _hdec, W, _hW, hWe, hWr⟩ :=
    hmeta.wireTree o ho
  change (if Block.preceq N.erase (eraseFG H) then some N.rows else none) = some rows at hrows
  split at hrows
  next hpath =>
    have he := Option.some.inj hrows
    subst rows
    refine ⟨W, (fgsa_carrier_geometry W H).2.1.mpr ?_, ?_⟩
    · rwa [hWe]
    · rw [hWr]
      exact List.mem_filterMap.mpr ⟨a, ha, hd⟩
  next hpath => cases hrows

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
The R6 invariant is available at the exact carrier read.
DC: INTENTIONAL immutable-parent validity of every stored proposal. -/
theorem fgsa_rowsValidStored_atProposal (hv : V2.D.ExecutionValid E rho)
    {s : Slot} {Q : Block} {rows : List (RowWire p.n)} {st : State p.n}
    (hc : HonestCarrier p c E rho s Q rows)
    (hs : proposalStateAt p c E rho s = some st) : RowsValidStored p st := by
  obtain ⟨i, _hi, hread, _⟩ := rowService_carrier_read p c E rho hv.toScheduleWellFormed hc
  have he := Option.some.inj (hs.symm.trans hread)
  subst st
  exact rowsValidStored_reachable p (reachable_postClock E rho i _ _)

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
The complete valid witnesses imply the raw batch witnesses. -/
theorem BatchPrem.batch_of_valid {p : Params} {V : Type} [DecidableEq V] [Fintype V] {In : Type}
    {c : AppCodec In} {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}
    {ΔF : Time} {k : RowKind} {q y : Nat} {U X : FGBlock (Fin p.n)}
    (h : BatchPrem p c E rho ΔF k q y U X) :
    ∃ S : Finset (Fin p.n), S ⊆ honestSeats p c rho ∧ p.E.q ≤ p.E.weightOf S ∧
      ∀ i ∈ S, ∃ j r a t, r ≤ q ∧
        HonestRowAt p c E rho j (rho.seatOf (.base .fg) i) r a ∧
        a.auth = .seat .fg i ∧ NamesEntry p k a y U ∧
        eventTime rho j = some t ∧ t = p.actionTime r := by
  rcases h.valid with ⟨S, hs, hq, hv⟩; exact ⟨S, hs, hq, by grind⟩

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. SO-COV chooses the same complete witness for validity, match, and receipt.
DC: SAME height coverage; INTENTIONAL cutoff q and pre-GST row transport. -/
theorem fgsa_batchCoverage (ΔF : Time) (kind : RowKind) : BatchCoverage p ΔF kind := by
  intro V _ _ In c E rho q y U X hb hheight
  rw [← KitFG.hOf_of_bridge p.E p.cfg (heightView p) (heightView_bridge p)] at hheight
  dsimp only [hOf] at hheight
  obtain ⟨rows, hc, hXrows⟩ := hb.carrier
  obtain ⟨S, hS, hquorum, hvalid⟩ := hb.valid
  refine ⟨S, hquorum, ?_⟩
  intro i hi
  obtain ⟨j, r, a, t, hr, ha, hauth, hname, _ht, _htime, hvalid, hmatch⟩ := hvalid i hi
  have htime : p.actionTime r ≤ p.actionTime q := by
    change 4 * p.Δ * ((r * p.R : Nat) : Int) + 6 * p.Δ ≤
      4 * p.Δ * ((q * p.R : Nat) : Int) + 6 * p.Δ
    have hR : (r * p.R : Nat) ≤ q * p.R := Nat.mul_le_mul_right p.R hr
    have hc : ((r * p.R : Nat) : Int) ≤ (q * p.R : Nat) := by exact_mod_cast hR
    have hΔ := p.deltaPos
    nlinarith
  have hdeadline : max (p.actionTime r) E.t_GST + ΔF ≤
      SA.proposalTime p.toParams X.slot := by
    have hmax := max_le_max_right E.t_GST htime
    exact (Int.add_le_add_right hmax ΔF).trans hb.horizon.1
  have hreceipt := hb.rowsReceipt j _ r a ha (hdeadline.trans hb.horizon.2)
    _ hc.1.1.2
  have hcarry := fgsa_rowsReceipt_carriage p c E rho hb.base.valid hb.base.noRestart
    hc ha hvalid hreceipt hdeadline
  let b : Row (Fin p.n) := a.payload.toRow i
  have hdecode : a.toRow? = some b := by
    obtain ⟨auth, body⟩ := a
    dsimp only at hauth
    subst auth
    rfl
  have hrow : RowNames p kind b i y U := ⟨rfl, hname⟩
  rcases hcarry with hcarry | hchain
  · right
    refine ⟨b, ?_, hrow⟩
    rw [hXrows]
    exact List.mem_filterMap.mpr ⟨a, hcarry, hdecode⟩
  · obtain ⟨st, hs, hchain⟩ := hchain
    obtain ⟨idx, _hidx, hread, _⟩ := rowService_carrier_read p c E rho
      hb.base.valid.toScheduleWellFormed hc
    have he := Option.some.inj (hs.symm.trans hread)
    have hmeta : MetaInv p st := he ▸ (storeBundle_postClock E rho idx _ _).meta
    rw [eraseFG_parent] at hchain
    obtain ⟨W, hWP, hbW⟩ := rowService_chain_occurrence p st hmeta X.parent a b hdecode hchain
    have hUW := hb.above i (hS hi) W hWP ⟨b, hbW, hrow⟩
    have hpar : FGBlock.Preceq W.parent X.parent := by
      cases W with
      | genesis => exact hWP
      | node P s root body rs =>
          exact KitFG.preceq_trans (KitFG.preceq_parent_node P s root body rs) hWP
    have hlow := KitFG.h_mono p.E p.cfg hUW
    have hhigh := KitFG.h_mono p.E p.cfg hpar
    have hentry : (heightView p U).h = y ∧ (heightView p U).T_h = U := hb.entry
    simp only [heightView_eq_simplex p,
      KitFG.simplexHeightView_def, KitFG.heightOf_def] at hentry
    have hh : (derive p.E p.cfg W.parent).h = y := by
      rw [hentry.1] at hlow
      rw [hheight] at hhigh
      exact Nat.le_antisymm hhigh hlow
    have hT : (derive p.E p.cfg W.parent).T_h = U :=
      (KitFG.entry_eq_on_plateau p.E p.cfg hUW (hentry.1.trans hh.symm)).symm.trans hentry.2
    have hsames : (derive p.E p.cfg W.parent).h = (derive p.E p.cfg X.parent).h ∧
        (derive p.E p.cfg W.parent).T_h.root = (derive p.E p.cfg X.parent).T_h.root :=
      ⟨hh.trans hheight.symm,
        congrArg FGBlock.root (KitFG.entry_eq_on_plateau p.E p.cfg hpar (hh.trans hheight.symm))⟩
    -- HeightMatch remains an explicit consumer input when the fold changes.
    obtain ⟨_st, _H, _hs, _hH, _hm⟩ := hmatch
    left
    cases W with
    | genesis => exact (List.not_mem_nil hbW).elim
    | node P s root body rs =>
      change (derive p.E p.cfg P).h = y at hh
      change (derive p.E p.cfg P).T_h = U at hT
      change (derive p.E p.cfg P).h = (derive p.E p.cfg X.parent).h ∧
        (derive p.E p.cfg P).T_h.root = (derive p.E p.cfg X.parent).T_h.root at hsames
      cases kind with
      | target =>
        have hm : b.height_pair = .vote (heightView p P).h (heightView p P).T_h.root false := by
          simp only [heightView_eq_simplex, KitFG.simplexHeightView_def, KitFG.heightOf_def]
          rw [hh, hT]
          exact hrow.2
        have hk : (heightView p P).h = (heightView p X.parent).h ∧
            (heightView p P).T_h.root = (heightView p X.parent).T_h.root := by
          simpa only [heightView_eq_simplex, KitFG.simplexHeightView_def, KitFG.heightOf_def]
            using hsames
        have ht := row_bit_persist p true P X.parent s root body rs b hbW hWP hm hk
        change b.signer ∈ (heightView p X.parent).target_participation at ht
        exact hrow.1 ▸ ht
      | progress =>
        have hm : b.height_pair.matchesEntry
            (heightView p P).h (heightView p P).T_h.root = true := by
          simp only [heightView_eq_simplex, KitFG.simplexHeightView_def, KitFG.heightOf_def]
          obtain ⟨timeout, hn⟩ := hrow.2
          rw [hh, hT, hn]
          cases timeout <;> simp [NamedHeightPair.matchesEntry]
        have hk : (heightView p P).h = (heightView p X.parent).h ∧
            (heightView p P).T_h.root = (heightView p X.parent).T_h.root := by
          simpa only [heightView_eq_simplex, KitFG.simplexHeightView_def, KitFG.heightOf_def]
            using hsames
        have ht := row_bit_persist p false P X.parent s root body rs b hbW hWP hm hk
        change b.signer ∈ (heightView p X.parent).progress at ht
        exact hrow.1 ▸ ht

end AvailableChain.FGSA.Run
end
