module
public import AvailableChainFGSAProofs.Statements.WeakContinuation
public import AvailableChainFGSAProofs.Proofs.Foundations.Export
public import AvailableChainFGSAProofs.Proofs.Shared.HonestQuorum
public import AvailableChainFGSARun.Proofs.Receipts

-- WC J1; DC handler order. B3 private matcher copy, with a checked equality.
namespace AvailableChain.FGSA
open AvailableChain.SimplexFG
/-- WC J1; DC finite event provenance: private replay or source-construction helper. -/
private def wc_admitBlock (p : Params) (st : State p.n) (s : Slot)
    (N : NamedProposal p.n) : State p.n :=
  if !namedParentHeld st N then st else
  match parentFG st N.erase with
  | none => st
  | some P =>
      if blockAccepted p st s N P then
        let st1 : State p.n := { st with
          base := GridCO.admitProposal p.toParams.engine st.base
            (baseProposal s N.erase N.raw N.support) N.erase (N.raw.map baseHead)
          fg := Window.on_block p p.K_W st.fg (fgBlock P N.erase N.rows)
          proposals := st.proposals ++ [⟨.proposer s, .proposal N⟩] }
        let st2 := if st1.fg.F = st.fg.F then st1 else reconcile st1
        N.rows.foldl (admitRow p) st2
      else st

/-- WC J1; DC finite event provenance: private replay or source-construction helper. -/
private theorem wc_admitBlock_eq : @admitBlock = @wc_admitBlock := rfl

end AvailableChain.FGSA

public section

/-! WC J1; DC bounded weak continuation: source seed and foundation discharge.
This module joins producers. The WC lane receives separate result premises. -/

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG KitFG

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}
    {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}

/-- WC J1; DC named scope: every honest-holder row has its original action index.
Rejected delivered proposals count. Emitted-only proposals do not supply scope. -/
theorem wc_scopedRowOrigins (hv : V2.D.ExecutionValid E rho)
    (D : FGBlock (Fin p.n)) (hD : RootBlockInRun p c E rho (eraseFG D))
    (a : Row (Fin p.n)) (ha : a ∈ chainRows D)
    (hh : rho.seatOf (.base .fg) a.signer ∈ rho.honest) :
    ∃ j r wire, HonestRowAt p c E rho j (rho.seatOf (.base .fg) a.signer) r wire ∧
      wire.toRow? = some a ∧ wire.auth = .seat .fg a.signer := by
  obtain ⟨N, ⟨M, hM, hNM⟩, hN⟩ := hD
  have hDM : Block.Preceq (eraseFG D) M.erase := by
    rw [← hN]
    exact named_preceq_erase hNM
  have carriage : FinalityCarriage p c E rho (chainRows D) := by
    rcases hM with ⟨x, o, t, hd, ho⟩ | ⟨x, hx, i, hm⟩
    · obtain ⟨j, hj⟩ := List.getElem?_of_mem hd
      exact delivered_runBlock_carriage p c E rho hv j x o t hj M ho D hDM
    · have hr := namedOrigin_reachable E rho i x
      have hb := ((reachable_named_store p hr).2.1 M.erase).mpr ⟨M, hm, rfl⟩
      obtain ⟨W, hW, he⟩ := (cstoreInv_stateBefore E rho i x).baseTree M.erase |>.mp hb
      have hDW : FGBlock.Preceq D W := eraseFG_preceq_iff.mp (he ▸ hDM)
      have hstored := KitFG.ancestor_closed_of_parent_closed _
        (cstoreInv_stateBefore E rho i x).fg.closed W hW D hDW
      rw [FinalityCarriage_def]
      exact held_chain_row_origin p c E rho hv.toUnforgeableSignatures i x D ⟨hx, hstored⟩
  rw [FinalityCarriage_def] at carriage
  obtain ⟨wire, _, hd, auth, origin⟩ := carriage a ha
  have signer : RowSigner p c rho wire (rho.seatOf (.base .fg) a.signer) :=
    ⟨a.signer, auth, rfl⟩
  obtain ⟨j, t, hj, hem⟩ := origin _ signer hh
  obtain ⟨au, body⟩ := wire
  dsimp only at auth
  subst au
  obtain ⟨_, _, r, ht, _⟩ := (fgsa_emitsAt_row E rho j _ t hj a.signer body).mp hem
  exact ⟨j, r, ⟨.seat .fg a.signer, body⟩, ⟨hh, ht ▸ hj, hem⟩, hd, rfl⟩

/-- WC J1; DC receipt replay: retain the original trigger and acceptance index. -/
theorem wc_receiptOrigins (i : Nat) (x : V) :
    WCReceiptOrigins p c E rho i x (storeAt p c E rho i x) := by
  constructor
  · exact fgsa_block_stamp_source E rho i x
  · exact fgsa_vote_stamp_source E rho i x

/-- WC J1; DC finite event provenance: private replay or source-construction helper. -/
private def wc_savedPairs (st : State p.n) : List (Slot × Block) :=
  st.base.genuine.filterMap (fun row => row.2.map (fun B => (row.1, B)))

/-- WC J1; DC finite event provenance: private replay or source-construction helper. -/
private theorem wc_savedPairs_mem (st : State p.n) (s : Slot) (B : Block) :
    (s, B) ∈ wc_savedPairs st ↔ (s, some B) ∈ st.base.genuine := by
  constructor
  · intro h
    obtain ⟨row, hr, hb⟩ := List.mem_filterMap.mp h
    obtain ⟨C, hc, he⟩ := Option.map_eq_some_iff.mp hb
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
    have hrow : row = (row.1, some C) := Prod.ext rfl hc
    rwa [hrow] at hr
  · intro h
    exact List.mem_filterMap.mpr ⟨(s, some B), h, rfl⟩

/-- WC J1; DC finite event provenance: private replay or source-construction helper. -/
private theorem wc_savedPairs_reconcile (st : State p.n) :
    wc_savedPairs (reconcile st) ⊆ wc_savedPairs st := by
  rintro ⟨s, B⟩ hm
  rw [wc_savedPairs_mem, reconcile_genuine] at hm
  obtain ⟨row, hr, he⟩ := List.mem_map.mp hm
  have hk := congrArg Prod.fst he
  have hb := (Option.filter_eq_some_iff.mp (congrArg Prod.snd he)).1
  rw [wc_savedPairs_mem]
  have hrow : row = (s, some B) := Prod.ext hk hb
  rwa [hrow] at hr

/-- WC J1; DC finite event provenance: private replay or source-construction helper. -/
private theorem wc_savedPairs_admitRows (rows : List (RowWire p.n)) (st : State p.n) :
    wc_savedPairs (rows.foldl (admitRow p) st) = wc_savedPairs st := by
  induction rows generalizing st with
  | nil => rfl
  | cons a rows ih =>
    rw [List.foldl_cons, ih]
    rcases admitRow_eq p st a with h | h
    · rw [h]
    · rw [h]
      rfl

-- WC J1; DC handler order. The upstream Schedule helper is private.
/-- WC J1; DC finite event provenance: private replay or source-construction helper. -/
private theorem wc_proposal_genuine (q : GridCO.Params) {n : Nat}
    (st : GridCO.State n .root) (o : GridCO.Wire n .root) (b : Block)
    (raw : List (GridCO.HeadWire n .root)) :
    (GridCO.admitProposal q st o b raw).genuine = st.genuine := by
  obtain ⟨auth, msg⟩ := o
  cases auth <;> unfold GridCO.admitProposal <;> dsimp only <;> split
  all_goals first | rfl | exact (foldVotes_fields q raw _).2.2.2.2.1

/-- WC J1; DC finite event provenance: private replay or source-construction helper. -/
private theorem wc_savedPairs_process (st : State p.n) (o : Wire p.n) :
    wc_savedPairs (process p st o) ⊆ wc_savedPairs st := by
  change wc_savedPairs (match o.decode with
    | some (.vote s i b) => admitHead p st s i b
    | some (.row _ body) => admitRow p st ⟨o.auth, body⟩
    | some (.block s N) => admitBlock p st s N
    | none => st) ⊆ wc_savedPairs st
  cases o.decode with
  | none => exact List.Subset.refl _
  | some a =>
    cases a <;> dsimp only
    case vote s i b =>
      unfold wc_savedPairs
      rw [admitHead_genuine]
    case row i body =>
      rcases admitRow_eq p st ⟨o.auth, body⟩ with h | h <;> rw [h]
      exact List.Subset.refl _
    case block s N =>
      cases hn : namedParentHeld st N with
      | false => rw [admitBlock_refused p st s N (Or.inl hn)]
      | true =>
        cases hp : parentFG st N.erase with
        | none => rw [admitBlock_refused p st s N (Or.inr (Or.inl hp))]
        | some P =>
          cases ha : blockAccepted p st s N P with
          | false =>
            rw [admitBlock_refused p st s N (Or.inr (Or.inr ⟨P, hp, ha⟩))]
          | true =>
            rw [wc_admitBlock_eq]
            unfold wc_admitBlock
            simp only [hn, Bool.not_true, Bool.false_eq_true, ite_false]
            rw [hp]
            dsimp only
            rw [ha, ite_eq_left rfl, wc_savedPairs_admitRows]
            split
            · unfold wc_savedPairs
              dsimp only
              rw [wc_proposal_genuine]
            · apply List.Subset.trans (wc_savedPairs_reconcile _)
              unfold wc_savedPairs
              dsimp only
              rw [wc_proposal_genuine]

/-- WC J1; DC finite event provenance: private replay or source-construction helper. -/
private theorem wc_savedPairs_clock (st : State p.n) (t : Time) (pair : Slot × Block)
    (hm : pair ∈ wc_savedPairs (clock p st t)) :
    pair ∈ wc_savedPairs st ∨
      (t = SA.gateTime p.toParams pair.1 ∧
       SA.Root.confirmationFrom p.toParams (eraseFG (clockPre p st t).fg.F)
         (actView (clockPre p st t)) pair.1 = some pair.2) := by
  change pair ∈ wc_savedPairs (if isGateTime p t then
    gateStep p (clockPre p st t) ((t - 6 * p.Δ) / (4 * p.Δ)).toNat
    else clockPre p st t) at hm
  have hpre : wc_savedPairs (clockPre p st t) = wc_savedPairs st := by
    unfold wc_savedPairs
    rw [clockPre_genuine]
  split at hm
  · rename_i ht
    let s := ((t - 6 * p.Δ) / (4 * p.Δ)).toNat
    let pre := clockPre p st t
    have htime : t = SA.gateTime p.toParams s :=
      beq_iff_eq.mp (Bool.and_eq_true_iff.mp ht).2
    cases hs : GridCO.savedGenuine pre.base s with
    | some saved =>
      rw [gateStep_saved p pre s (by rw [hs]; rfl)] at hm
      unfold wc_savedPairs at hm
      rw [normalizeS_fields] at hm
      exact Or.inl (hpre ▸ hm)
    | none =>
      have hg : (gateStep p pre s).base.genuine = pre.base.genuine ++
          [(s, SA.Root.confirmationFrom p.toParams (eraseFG pre.fg.F) (actView pre) s)] := by
        unfold gateStep
        rw [normalizeS_fields]
        simp only [hs, Option.isSome_none, Bool.false_eq_true, ite_false]
        exact saGate_genuine p.toParams (eraseFG pre.fg.F) (actView pre) s hs
      rcases pair with ⟨v, B⟩
      rw [wc_savedPairs_mem, hg, List.mem_append] at hm
      rcases hm with hm | hm
      · exact Or.inl (hpre ▸ (wc_savedPairs_mem pre v B).mpr hm)
      · have he := List.mem_singleton.mp hm
        obtain ⟨rfl, hC⟩ := Prod.mk.inj he
        exact Or.inr ⟨htime, hC.symm⟩
  · exact Or.inl (hpre ▸ hm)

/-- WC J1; DC actual saved origin: a retained value still has its original gate result. -/
theorem wc_savedOrigin (hs : V2.D.ScheduleWellFormed E rho)
    (i : Nat) (x : V) (s : Slot) (B : Block)
    (hb : GridCO.savedGenuine (storeAt p c E rho i x).base s = some (some B)) :
    ∃ j < i, IsGateTick p c rho j x s ∧ gateResultAt p c E rho j = some (some B) := by
  obtain ⟨row, hr, he⟩ := Option.map_eq_some_iff.mp hb
  have hk : row.1 = s := by simpa using List.find?_some hr
  have hm : (s, B) ∈ wc_savedPairs (storeAt p c E rho i x) := by
    rw [wc_savedPairs_mem]
    simpa only [← hk, ← he] using List.mem_of_find?_eq_some hr
  obtain ⟨j, hj, t, ht, htime, hC⟩ :=
    V2.D.Engine.clock_field_origin_of_subset (P := fgsa p c)
      (fun nd => wc_savedPairs nd.st) rfl
      (fun nd o pair h => wc_savedPairs_process nd.st (toWire p o) h)
      (fun _ _ _ h => h) (fgsa_hrestore_field p c wc_savedPairs rfl)
      (fun nd t pair => t = SA.gateTime p.toParams pair.1 ∧
        SA.Root.confirmationFrom p.toParams (eraseFG (clockPre p nd.st t).fg.F)
          (actView (clockPre p nd.st t)) pair.1 = some pair.2)
      (fun nd t pair h => wc_savedPairs_clock nd.st t pair h) E rho i x (s, B) hm
  change t = SA.gateTime p.toParams s at htime
  subst t
  refine ⟨j, hj, ht, ?_⟩
  rw [gateResultAt_eq_gateResult p c E rho hs ht, gateResult_def, gateIn_def, preTick_def,
    fgsa_tickIdx_of_event p c E rho hs ht]
  exact congrArg some hC

variable [Fintype V]

/-- WC J1; DC premise discharge: supply every separate lane input to its consumer.
The consumer telescope is the literal [L] expansion; no foundation bundle is passed. -/
theorem wc_dischargeL {ΔF : Time} {w : HealingWitness} {Result : Prop}
    (hb : Base₂ p c E rho)
    (hsync : Gen.V2.Duty.PartialSynchronyBy E rho (fgsaDelay E.Δ ΔF))
    (hdeltaF : E.Δ ≤ ΔF)
    (hfault : (Gen.V2.Duty.faulty rho).card ≤ (p.n - 1) / 3)
    (hpart : ∀ s, w.u + 1 ≤ s → SA.voteTime p.toParams s ≤ rho.horizon →
      (Gen.V2.Duty.faulty rho).card <
        (Gen.V2.Duty.awakeHonest E rho (SA.voteTime p.toParams s)).card)
    (consume : ∀
  (_hvalid : V2.D.ExecutionValid E rho)
  (_hlinked : V2.D.Linked (fgsaFamilies p c).linked rho)
  (_hcstar : V2.D.CStar (fgsaFamilies p c).fresh rho)
  (_hnr : V2.D.NoRestart rho)
  (_hdelta : E.Δ = p.Δ)
  (_hroots : NamedRootCollisionFree p c E rho)
  (_hsync : Gen.V2.Duty.PartialSynchronyBy E rho (fgsaDelay E.Δ ΔF))
  (_hdeltaF : E.Δ ≤ ΔF)
  (_hfault : (Gen.V2.Duty.faulty rho).card ≤ (p.n - 1) / 3)
  (_hfaultQ : Gen.Pure.FaultQ p.n (Gen.V2.Duty.faulty rho).card)
  (_hfaultX : Gen.Pure.FaultX p.n (Gen.V2.Duty.faulty rho).card)
  (_hpart : ∀ s, w.u + 1 ≤ s → SA.voteTime p.toParams s ≤ rho.horizon →
    (Gen.V2.Duty.faulty rho).card <
      (Gen.V2.Duty.awakeHonest E rho (SA.voteTime p.toParams s)).card)
  (_hstore : RStore p c E rho)
  (_hcumul : RStoreCumul p c E rho)
  (_hmono : RMono p c E rho)
  (_hactive : RActive p c E rho)
  (_hframe : RFrameExact p c E rho)
  (_hmeta : RFrame p c E rho)
  (_hrec : RRec p c E rho)
  (_hgeo : RGeo p c E rho)
  (_hcert : RCert p c E rho)
  (_hsrc : TSrc p c E rho)
  (_hlabel : LabelBound p c E rho)
  (_hqc : RQCOrigin p c E rho)
  (_hstrat : RStrat p c E rho)
  (_hnoslash : ∀ x ∈ rho.honest, EmittedRowsNoSlash p c E rho x)
  (_hemitted : ∀ j x r a e, HonestRowAt p c E rho j x r a →
    namedEntry a.payload.height_pair = some e →
    ∃ C B, actionSourceFG p c E rho x r = some (some C) ∧
      e = (hOf p.E p.cfg C, (derive p.E p.cfg C).T_h.root) ∧
      FGBlock.Preceq (derive p.E p.cfg C).T_h C ∧
      gateResult p c E rho x (r * p.R) = some (some B) ∧
      Block.Preceq (eraseFG C) B ∧ fastAt p c E rho x (r * p.R) (eraseFG C))
  (_htargets : ∀ i x row, row ∈ (storeAt p c E rho i x).base.obligations →
    Block.Preceq row.1 (storeAt p c E rho i x).base.stableRecord)
  (_hlease : ∀ i x row, row ∈ (storeAt p c E rho i x).base.obligations →
    ∃ j < i, ∃ s B, IsGateTick p c rho j x s ∧ gatePassedAt p c E rho j ∧
      gateResultAt p c E rho j = some (some B) ∧ Block.Preceq row.1 B ∧
      (row.1, row.2.1) ∈
      (let wcView := actView (clockPre p (storeAt p c E rho j x) (SA.gateTime p.toParams s));
        (wcView.blocks.filter (fun b => b != .genesis && Block.preceq b B)).flatMap
          (fun b => (@GridCO.admissionLevels GridCO.slowLeasePolicy
            p.toParams.engine p.n .root wcView s b).map (fun g => (b, g)))) ∧
      row.2.2 = SA.gateTime p.toParams s + SA.lifetime p.toParams ∧
      row.2.2 = SA.releaseTime p.toParams (s + p.k) ∧
      ∀ k w C, j < k → k < i → IsGateTick p c rho k x w →
        let pre := clockPre p (storeAt p c E rho k x) (SA.gateTime p.toParams w)
        GridCO.savedGenuine pre.base w = none →
        SA.Root.confirmationFrom p.toParams (eraseFG pre.fg.F) (actView pre) w = some C →
        (actView pre).obligations.any (fun r => !Block.compatible r.1 C) = false →
        (row.1, row.2.1) ∉ (let wcView := actView pre;
        (wcView.blocks.filter (fun b => b != .genesis && Block.preceq b C)).flatMap
          (fun b => (@GridCO.admissionLevels GridCO.slowLeasePolicy
            p.toParams.engine p.n .root wcView w b).map (fun g => (b, g)))))
  (_hfast : ∀ i x,
    ∀ s X, X ∈ (FGSA.fastWriteAt (storeAt p c E rho i x) s).getD [] →
      ∃ j < i, IsGateTick p c rho j x s ∧ gatePassedAt p c E rho j ∧
        ∃ B, gateResultAt p c E rho j = some (some B) ∧
          Block.Preceq X B ∧ fastAt p c E rho x s X)
  (_hdeadlines : ∀ i x,
    ∀ K g deadline, (K, g, deadline) ∈ (storeAt p c E rho i x).base.obligations →
      ∀ B, B ≠ .genesis → Block.Preceq B K →
        Gen.AC.Root.ProtectsUntil (storeAt p c E rho i x).base B g deadline)
  (_hheldRows : ∀ i x W, HeldAt p c E rho i x W → ∀ a ∈ chainRows W,
    ∃ (wire : RowWire p.n) (r : Nat), wire.toRow? = some a ∧
      wire.auth = .seat .fg a.signer ∧ ∃ k o t, k < i ∧
        rho.events[k]? = some (.deliver x o t) ∧
        ∀ z, RowSigner p c rho wire z → z ∈ rho.honest →
          HonestRowBefore p c E rho i z r wire ∧ p.actionTime r ≤ t)
  (_hscopeRows : ∀ D, RootBlockInRun p c E rho (eraseFG D) → ∀ a ∈ chainRows D,
    rho.seatOf (.base .fg) a.signer ∈ rho.honest → ∃ j r wire,
      HonestRowAt p c E rho j (rho.seatOf (.base .fg) a.signer) r wire ∧
      wire.toRow? = some a ∧ wire.auth = .seat .fg a.signer)
  (_hfinalHead : ∀ j z r a u, HonestRowAt p c E rho j z r a →
    RowSigner p c rho a z → a.toRow? = some u → ∀ fp,
    u.finality_pair = some fp → ∃ B, HeldAt p c E rho j z B ∧
      fp.height = (heightView p B).h_j ∧ fp.target = (heightView p B).J.root ∧
      TargetQCAt p.E B fp.height (heightView p B).J), Result) : Result := by
  have hq := fgsa_faultQ_of_count p hfault
  have hs := hb.valid.toScheduleWellFormed
  have hstore := fgsa_rStore p c E rho
  apply consume hb.valid hb.linked hb.cstar hb.noRestart hb.delta hb.idealization
    hsync hdeltaF hfault hq (fgsa_faultX_count_rec p hfault) hpart
    hstore (fgsa_rStoreCumul p c E rho) (fgsa_rMono p c E rho)
    (fgsa_rActive p c E rho) (fgsa_rFrameExact p c E rho) (fgsa_rFrame p c E rho)
    (fgsa_rRec p c E rho) (fgsa_rGeo p c E rho) (fgsa_rCert p c E rho)
    (sourceDiscipline_tSrc p c E rho hs) (sourceDiscipline_labelBound p c E rho hs)
    (sourceDiscipline_qcOrigin p c E rho (pt := ()) ⟨hb, hq⟩ hstore)
    (sourceDiscipline_strat p c E rho (pt := ()) ⟨hb, hq⟩ hstore)
    (fgsa_clientSafeAll p c E rho hb.linked)
  · intro j x r a e ha he
    exact sourceDiscipline_emittedName p c E rho hs ha he
  · intro i x row hr
    exact storedTargetsBelowOutput_target p _ (fgsa_storedTargetsBelowOutput p c E rho i x)
      row hr
  · exact fgsa_leaseOrigins_lastWrite p c E rho hs
  · exact fgsa_leaseOrigins_fastWrites p c E rho hs
  · exact fgsa_leaseOrigins_ancestorDeadlines p c E rho
  · exact held_chain_row_origin_before p c E rho hb.valid.toUnforgeableSignatures hs
  · exact wc_scopedRowOrigins hb.valid
  · intro j z r a u ha hsign hd fp hf
    exact cap_finality_head p c E rho ha hsign hd fp hf

/-- WC J1; DC fixed corruption: agreement transfers the source fault bound. -/
theorem wc_faultTransfer {E' : Generic.Env V} {source : V2.D.Run V (fgsa p c)}
    {G ΔF : Time} (hS : StrongRecoverySearchPrefix₂ p c E source G ΔF)
    (hc : CleanContinuation₂ p c E source E' rho ΔF) :
    (Gen.V2.Duty.faulty rho).card ≤ (p.n - 1) / 3 := by
  simpa only [Gen.V2.Duty.faulty_def, hc.agrees.honest] using hS.fault

/-- WC J1; DC weak duty: the split includes the endpoint and the first suffix batch. -/
theorem wc_participation {E' : Generic.Env V} {source : V2.D.Run V (fgsa p c)}
    {G ΔF : Time} {w : HealingWitness}
    (hS : StrongRecoverySearchPrefix₂ p c E source G ΔF)
    (hc : CleanContinuation₂ p c E source E' rho ΔF)
    (hfirst : E.t_GST ≤ SA.voteTime p.toParams (w.u + 1)) :
    ∀ s, w.u + 1 ≤ s → SA.voteTime p.toParams s ≤ rho.horizon →
      (Gen.V2.Duty.faulty rho).card <
        (Gen.V2.Duty.awakeHonest E' rho (SA.voteTime p.toParams s)).card := by
  intro s hs hhor
  by_cases hend : SA.voteTime p.toParams s ≤ source.horizon
  · have htime : E.t_GST ≤ SA.voteTime p.toParams s := by
      have hnat : (w.u + 1 : Int) ≤ (s : Int) := by exact_mod_cast hs
      have hd := p.deltaPos
      change E.t_GST ≤ 4 * p.Δ * (s : Int) + p.Δ
      change E.t_GST ≤ 4 * p.Δ * ((w.u : Int) + 1) + p.Δ at hfirst
      nlinarith
    have ha : Gen.V2.Duty.awakeHonest E' rho (SA.voteTime p.toParams s) = source.honest := by
      rw [Gen.V2.Duty.awakeHonest_def, hc.agrees.honest]
      apply Finset.filter_eq_self.mpr
      intro x hx
      rw [hc.agrees.awake x _ hend]
      exact hS.awake x hx _ htime hend
    rw [ha, Gen.V2.Duty.faulty_def, hc.agrees.honest]
    obtain ⟨equiv, _⟩ := fgsa_linked_seats source hS.base.linked
    have hn : Fintype.card V = p.n := by
      rw [← Fintype.card_congr equiv, Fintype.card_fin]
    have hsum : (Finset.univ \ source.honest).card + source.honest.card = p.n := by
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ]
      have hh := Finset.card_le_univ source.honest
      omega
    have hf := hS.fault
    rw [Gen.V2.Duty.faulty_def] at hf
    have hp := p.nPos
    omega
  · exact hc.participation _ (lt_of_not_ge hend) hhor

/-- WC J1; DC finite seed: each structural fact comes from its own producer. -/
theorem wc_finiteFacts (hb : Base₂ p c E rho)
    (hfault : (Gen.V2.Duty.faulty rho).card ≤ (p.n - 1) / 3) (i : Nat) :
    WCFiniteFacts p c E rho i := by
  have hs := hb.valid.toScheduleWellFormed
  refine ⟨fun x _ => cstoreInv_stateBefore E rho i x,
    fun x _ => nestOK_stateBefore E rho i x,
    fun x _ => metaInv_stateBefore E rho i x,
    fun x _ => wc_receiptOrigins i x,
    fun x _ row hr => ⟨fgsa_leaseOrigins_lastWrite p c E rho hs i x row hr⟩,
    fun x _ => fgsa_leaseOrigins_ancestorDeadlines p c E rho i x,
    fun x _ => fgsa_leaseOrigins_fastWrites p c E rho hs i x,
    fun x _ s C hc => wc_savedOrigin hs i x s C hc, ?_, ?_⟩
  · intro x hx W hW X hX hne
    have strat := sourceDiscipline_strat p c E rho
      (pt := ()) ⟨hb, fgsa_faultQ_of_count p hfault⟩ (fgsa_rStore p c E rho)
    obtain ⟨y, r, wire, ⟨j, hj, hrow⟩, hname⟩ := strat i x W hx hW X hX hne
    obtain ⟨K, B, hK, hpair, hentry, hB, hKB, _⟩ :=
      sourceDiscipline_emittedName p c E rho hs hrow hname
    have hXK : X = (derive p.E p.cfg K).T_h :=
      rootScope_eq hb.idealization
        (rootScope_ancestor (rootScope_store hx hW) (certified_preceq hX))
        (rootScope_ancestor (rootScope_source hrow.1 hK) hentry)
        (congrArg Prod.snd hpair)
    exact ⟨j, y, r, wire, K, B, hj, hrow, hname, hK, hXK ▸ hentry, hB, hKB⟩
  · intro j k x r r' a b u v _ _ ha hb' hu hv
    exact fgsa_clientSafeAll p c E rho hb.linked x ha.1 a b
      ⟨j, p.actionTime r, ha.2⟩ ⟨k, p.actionTime r', hb'.2⟩ u v hu hv

omit [DecidableEq V] [Fintype V] in
/-- WC J1; DC finite event provenance: private replay or source-construction helper. -/
private theorem wc_cut_downward (t : Time) :
    ∀ e f : V2.Event V (fgsa p c).Object, e.key ≤ f.key →
      cutPred t f = true → cutPred t e = true := by
  intro e f hef hf
  exact decide_eq_true (hef.trans (of_decide_eq_true hf))

omit [DecidableEq V] [Fintype V] in
/-- WC J1; DC finite event provenance: private replay or source-construction helper. -/
private theorem wc_tick_before_cut (hs : V2.D.ScheduleWellFormed E rho)
    {i : Nat} {x : V} {t d : Time} (he : rho.events[i]? = some (.tick x t))
    (ht : t ≤ d) : i < afterTicksIdx rho d := by
  by_contra h
  have hf := V2.D.Engine.filter_false_of_index_ge hs (cutPred d)
    (wc_cut_downward d) (Nat.le_of_not_gt h) he
  have hc : cutPred d (.tick x t : V2.Event V (fgsa p c).Object) = true := by
    apply decide_eq_true
    exact Prod.Lex.toLex_le_toLex.mpr (ht.lt_or_eq.imp id (fun h => ⟨h, le_rfl⟩))
  rw [hc] at hf
  cases hf

omit [DecidableEq V] [Fintype V] in
/-- WC J1; DC finite event provenance: private replay or source-construction helper. -/
private theorem wc_time_before_cut (hs : V2.D.ScheduleWellFormed E rho)
    {i : Nat} {e : V2.Event V (fgsa p c).Object} {d : Time}
    (he : rho.events[i]? = some e) (hi : i < afterTicksIdx rho d) : e.time ≤ d := by
  have hm : e ∈ rho.events.filter (cutPred d) := by
    rw [V2.D.Engine.filter_eq_take hs (cutPred d) (wc_cut_downward d)]
    apply List.mem_of_getElem? (i := i)
    change (rho.events.take (afterTicksIdx rho d))[i]? = some e
    rw [List.getElem?_take_of_lt hi]
    exact he
  have hkey := of_decide_eq_true (List.mem_filter.mp hm).2
  rcases Prod.Lex.toLex_le_toLex.mp hkey with h | ⟨h, _⟩
  · exact le_of_lt h
  · exact le_of_eq h

/-- WC J1; DC height seed: construct HS from the selected HealingInput and source regime.
The output cut alone is not used as a replacement for the source witness. -/
theorem wc_heightSeed {G ΔF : Time} {w : HealingWitness}
    (hS : StrongRecoverySearchPrefix₂ p c E rho G ΔF)
    (hinput : HealingInput p c E rho w ΔF) (hend : tstar p w < rho.horizon) :
    let i := afterTicksIdx rho (tstar p w)
    BoundedHealingCut₂ p c E rho w.u w.QStar i ΔF ∧ WCSeed p c E rho w i := by
  let i := afterTicksIdx rho (tstar p w)
  have hs := hS.base.valid.toScheduleWellFormed
  have hservice := hinput.ac.h3 w.u w.QStar hinput.wit.proposal hinput.wit.proposal_lower
  have hgate : SA.gateTime p.toParams w.u ≤ rho.horizon := le_of_lt hend
  have href : ∀ x ∈ rho.honest, S_at p c E rho i x = w.QStar := by
    intro x hx
    have h := hinput.ac.h4.1 x hx
    rw [afterTicks_eq_stateBefore E rho hs] at h
    exact h
  have hnext : SA.voteTime p.toParams (w.u + 1) ≤ SA.gateTime p.toParams w.u := by
    change 4 * p.Δ * ((w.u + 1 : Nat) : Int) + p.Δ ≤ 4 * p.Δ * (w.u : Int) + 6 * p.Δ
    push_cast
    have hd := p.deltaPos
    nlinarith
  have hfirst : E.t_GST ≤ SA.voteTime p.toParams (w.u + 1) := by
    have hstart := hinput.wit.synchronous
    have hslot : w.sStar + 2 ≤ w.u := hinput.wit.proposal_lower
    have hslot' : (w.sStar : Int) ≤ (w.u : Int) + 1 := by
      exact_mod_cast (Nat.le_trans (Nat.le_add_right w.sStar 2)
        (hslot.trans (Nat.le_succ w.u)))
    change E.t_GST ≤ 4 * p.Δ * (w.sStar : Int) + p.Δ at hstart
    change E.t_GST ≤ 4 * p.Δ * ((w.u + 1 : Nat) : Int) + p.Δ
    push_cast
    have hd := p.deltaPos
    nlinarith
  obtain ⟨j₀, y₀, a₀, WStar, hrow₀, _, hsrc₀, herase, hheight⟩ := hinput.wit.fresh
  have hstored : ∀ x ∈ rho.honest, WStar ∈ (storeAt p c E rho i x).fg.TF := by
    intro x hx
    have hc := cstoreInv_stateBefore E rho i x
    have hQ : w.QStar ∈ (storeAt p c E rho i x).base.blocks := by
      rw [← href x hx]
      exact hc.Smem
    obtain ⟨Qfg, hQfg, heQ⟩ := hc.baseTree w.QStar |>.mp hQ
    apply KitFG.ancestor_closed_of_parent_closed _ hc.fg.closed Qfg hQfg
    apply eraseFG_preceq_iff.mp
    rw [herase, heQ]
    exact hinput.wit.source_prefix
  have hscope := rootScope_source hrow₀.1 hsrc₀
  refine ⟨⟨hinput.wit.after_gst, hend, rfl, hinput.wit.proposal, href⟩,
    ⟨rfl, List.length_filter_le _ _, hinput.wit.after_gst, hfirst,
      ⟨WStar, herase, hheight, hscope, hstored⟩, hinput.wit.source_prefix,
      ?_, href, ?_, ?_, ?_, ?_, ?_, wc_finiteFacts hS.base hS.fault i⟩⟩
  · intro x hx
    obtain ⟨hraw, ⟨j, hj, hpass⟩, _⟩ := hservice.2 hgate x hx
    refine ⟨j, wc_tick_before_cut hs hj le_rfl, hj, ?_, hpass⟩
    rw [gateResultAt_eq_gateResult p c E rho hs hj]
    exact hraw
  · intro x hx
    have heq : ((4 * (w.u + 1) + 1 : Nat) : Time) * p.Δ =
        SA.voteTime p.toParams (w.u + 1) := by
      change _ = 4 * p.Δ * ((w.u + 1 : Nat) : Int) + p.Δ
      push_cast
      ring
    obtain ⟨k, hk, _⟩ := fgsa_tick_total E rho hs hS.base.delta x hx
      (4 * (w.u + 1) + 1) (heq ▸ hnext.trans hgate)
    rw [heq] at hk
    let st := FGSA.clock p (storeAt p c E rho k x) (SA.voteTime p.toParams (w.u + 1))
    have hread : headAtLabel p c E rho x (w.u + 1) = some (headVote p st (w.u + 1)) := by
      unfold headAtLabel
      rw [postClock_def, preTick_def, fgsa_tickIdx_of_event p c E rho hs hk]
      rfl
    have hraw := (hservice.2 hgate x hx).1
    have hsu : w.sStar ≤ w.u := le_trans (Nat.le_add_right _ _) hinput.wit.proposal_lower
    have hle := (hinput.ac.h5 x w.u w.QStar hx hsu hraw).2.1
      x (w.u + 1) (headVote p st (w.u + 1)) hx le_rfl hread
    have hinv := cstoreInv_clock p _ (cstoreInv_stateBefore E rho k x)
      (SA.voteTime p.toParams (w.u + 1))
    refine ⟨k, wc_tick_before_cut hs hk hnext, ⟨hk, ?_, ?_, ?_⟩⟩
    · unfold headAtIdx
      rw [hk]
      exact hle
    · intro A hA
      obtain ⟨H, hH, hHread⟩ := hinv.baseTree _ |>.mp (headVote_stored p st hinv (w.u + 1))
      obtain ⟨Afg, hAfg, heA⟩ := eraseFG_ancestor_mem hinv.fg.closed hH
        (hHread ▸ Gen.Pure.block_preceq_trans hA hle)
      exact hinv.baseTree A |>.mpr ⟨Afg, hAfg, heA⟩
    · have hr := wc_receiptOrigins (E := E) (rho := rho) k x
      constructor
      · simpa only [(clock_cumulative p _ _).2.2.1] using hr.blocks
      · simpa only [(clock_cumulative p _ _).2.2.2.1] using hr.votes
  · intro j x r a e hj ha he hhigh
    obtain ⟨K, B, hK, hpair, hentry, hB, hKB, _⟩ :=
      sourceDiscipline_emittedName p c E rho hs ha he
    refine ⟨K, B, hK, hpair, hentry, hB, hKB, ?_⟩
    have ht := wc_time_before_cut hs ha.2.1 hj
    have hlabel : r * p.R ≤ w.u := by
      change 4 * p.Δ * ((r * p.R : Nat) : Int) + 6 * p.Δ ≤
        4 * p.Δ * (w.u : Int) + 6 * p.Δ at ht
      have hd := p.deltaPos
      have hcast : ((r * p.R : Nat) : Int) ≤ (w.u : Int) := by nlinarith
      exact_mod_cast hcast
    rcases hlabel.lt_or_eq with hlt | heq
    · have hh : high p w K := by
        rw [high_def, heightView_eq_simplex]
        change w.M + 1 ≤ hOf p.E p.cfg K
        simpa only [hpair] using hhigh
      have hhead := hservice.1 (by
        change 4 * p.Δ * (w.u : Int) + p.Δ ≤ rho.horizon
        change 4 * p.Δ * (w.u : Int) + 6 * p.Δ ≤ rho.horizon at hgate
        have hd := p.deltaPos
        nlinarith) x ha.1
      exact (hinput.ac.h2A x r K ha.1 hK hh).1 x w.u w.QStar ha.1
        (Nat.succ_le_of_lt hlt) hhead
    · rw [heq] at hB
      have heB := Option.some.inj (Option.some.inj (hB.symm.trans (hservice.2 hgate x ha.1).1))
      exact heB ▸ hKB
  · intro x hx
    have hc := (cstoreInv_stateBefore E rho i x).fg
    change w.M + 1 ≤ (rho.stateBefore E i x).st.fg.h_max
    rw [hc.hmax]
    rw [← hheight]
    have hw : WStar ∈ (rho.stateBefore E i x).st.fg.TF := hstored x hx
    exact le_sup_of_le_left (Finset.le_sup (f := fun B => (heightView p B).h) hw)
  · intro x hx
    have hn := nestOK_stateBefore E rho i x
    change Block.Preceq (F_at p c E rho i x) (S_at p c E rho i x) at hn
    rwa [href x hx] at hn
  · intro x hx row hr _
    have ht := storedTargetsBelowOutput_target p _ (fgsa_storedTargetsBelowOutput p c E rho i x)
      row hr
    change Block.Preceq row.1 (S_at p c E rho i x) at ht
    rwa [href x hx] at ht

/-- WC J1; DC continuation assembly: all [L] inputs, including the first suffix batch.
The finite source seed is sufficient for the split at the inclusive source endpoint. -/
theorem wc_dischargeContinuation {E' : Generic.Env V} {source : V2.D.Run V (fgsa p c)}
    {G ΔF : Time} {w : HealingWitness} {iStar : Nat} {Result : Prop}
    (hS : StrongRecoverySearchPrefix₂ p c E source G ΔF)
    (hc : CleanContinuation₂ p c E source E' rho ΔF)
    (hs : WCSeed p c E source w iStar)
    (consume : ∀
  (_hvalid : V2.D.ExecutionValid E' rho)
  (_hlinked : V2.D.Linked (fgsaFamilies p c).linked rho)
  (_hcstar : V2.D.CStar (fgsaFamilies p c).fresh rho)
  (_hnr : V2.D.NoRestart rho)
  (_hdelta : E'.Δ = p.Δ)
  (_hroots : NamedRootCollisionFree p c E' rho)
  (_hsync : Gen.V2.Duty.PartialSynchronyBy E' rho (fgsaDelay E'.Δ ΔF))
  (_hdeltaF : E'.Δ ≤ ΔF)
  (_hfault : (Gen.V2.Duty.faulty rho).card ≤ (p.n - 1) / 3)
  (_hfaultQ : Gen.Pure.FaultQ p.n (Gen.V2.Duty.faulty rho).card)
  (_hfaultX : Gen.Pure.FaultX p.n (Gen.V2.Duty.faulty rho).card)
  (_hpart : ∀ s, w.u + 1 ≤ s → SA.voteTime p.toParams s ≤ rho.horizon →
    (Gen.V2.Duty.faulty rho).card <
      (Gen.V2.Duty.awakeHonest E' rho (SA.voteTime p.toParams s)).card)
  (_hstore : RStore p c E' rho)
  (_hcumul : RStoreCumul p c E' rho)
  (_hmono : RMono p c E' rho)
  (_hactive : RActive p c E' rho)
  (_hframe : RFrameExact p c E' rho)
  (_hmeta : RFrame p c E' rho)
  (_hrec : RRec p c E' rho)
  (_hgeo : RGeo p c E' rho)
  (_hcert : RCert p c E' rho)
  (_hsrc : TSrc p c E' rho)
  (_hlabel : LabelBound p c E' rho)
  (_hqc : RQCOrigin p c E' rho)
  (_hstrat : RStrat p c E' rho)
  (_hnoslash : ∀ x ∈ rho.honest, EmittedRowsNoSlash p c E' rho x)
  (_hemitted : ∀ j x r a e, HonestRowAt p c E' rho j x r a →
    namedEntry a.payload.height_pair = some e →
    ∃ C B, actionSourceFG p c E' rho x r = some (some C) ∧
      e = (hOf p.E p.cfg C, (derive p.E p.cfg C).T_h.root) ∧
      FGBlock.Preceq (derive p.E p.cfg C).T_h C ∧
      gateResult p c E' rho x (r * p.R) = some (some B) ∧
      Block.Preceq (eraseFG C) B ∧ fastAt p c E' rho x (r * p.R) (eraseFG C))
  (_htargets : ∀ i x row, row ∈ (storeAt p c E' rho i x).base.obligations →
    Block.Preceq row.1 (storeAt p c E' rho i x).base.stableRecord)
  (_hlease : ∀ i x row, row ∈ (storeAt p c E' rho i x).base.obligations →
    ∃ j < i, ∃ s B, IsGateTick p c rho j x s ∧ gatePassedAt p c E' rho j ∧
      gateResultAt p c E' rho j = some (some B) ∧ Block.Preceq row.1 B ∧
      (row.1, row.2.1) ∈
      (let wcView := actView (clockPre p (storeAt p c E' rho j x) (SA.gateTime p.toParams s));
        (wcView.blocks.filter (fun b => b != .genesis && Block.preceq b B)).flatMap
          (fun b => (@GridCO.admissionLevels GridCO.slowLeasePolicy
            p.toParams.engine p.n .root wcView s b).map (fun g => (b, g)))) ∧
      row.2.2 = SA.gateTime p.toParams s + SA.lifetime p.toParams ∧
      row.2.2 = SA.releaseTime p.toParams (s + p.k) ∧
      ∀ k w C, j < k → k < i → IsGateTick p c rho k x w →
        let pre := clockPre p (storeAt p c E' rho k x) (SA.gateTime p.toParams w)
        GridCO.savedGenuine pre.base w = none →
        SA.Root.confirmationFrom p.toParams (eraseFG pre.fg.F) (actView pre) w = some C →
        (actView pre).obligations.any (fun r => !Block.compatible r.1 C) = false →
        (row.1, row.2.1) ∉ (let wcView := actView pre;
        (wcView.blocks.filter (fun b => b != .genesis && Block.preceq b C)).flatMap
          (fun b => (@GridCO.admissionLevels GridCO.slowLeasePolicy
            p.toParams.engine p.n .root wcView w b).map (fun g => (b, g)))))
  (_hfast : ∀ i x,
    ∀ s X, X ∈ (FGSA.fastWriteAt (storeAt p c E' rho i x) s).getD [] →
      ∃ j < i, IsGateTick p c rho j x s ∧ gatePassedAt p c E' rho j ∧
        ∃ B, gateResultAt p c E' rho j = some (some B) ∧
          Block.Preceq X B ∧ fastAt p c E' rho x s X)
  (_hdeadlines : ∀ i x,
    ∀ K g deadline, (K, g, deadline) ∈ (storeAt p c E' rho i x).base.obligations →
      ∀ B, B ≠ .genesis → Block.Preceq B K →
        Gen.AC.Root.ProtectsUntil (storeAt p c E' rho i x).base B g deadline)
  (_hheldRows : ∀ i x W, HeldAt p c E' rho i x W → ∀ a ∈ chainRows W,
    ∃ (wire : RowWire p.n) (r : Nat), wire.toRow? = some a ∧
      wire.auth = .seat .fg a.signer ∧ ∃ k o t, k < i ∧
        rho.events[k]? = some (.deliver x o t) ∧
        ∀ z, RowSigner p c rho wire z → z ∈ rho.honest →
          HonestRowBefore p c E' rho i z r wire ∧ p.actionTime r ≤ t)
  (_hscopeRows : ∀ D, RootBlockInRun p c E' rho (eraseFG D) → ∀ a ∈ chainRows D,
    rho.seatOf (.base .fg) a.signer ∈ rho.honest → ∃ j r wire,
      HonestRowAt p c E' rho j (rho.seatOf (.base .fg) a.signer) r wire ∧
      wire.toRow? = some a ∧ wire.auth = .seat .fg a.signer)
  (_hfinalHead : ∀ j z r a u, HonestRowAt p c E' rho j z r a →
    RowSigner p c rho a z → a.toRow? = some u → ∀ fp,
    u.finality_pair = some fp → ∃ B, HeldAt p c E' rho j z B ∧
      fp.height = (heightView p B).h_j ∧ fp.target = (heightView p B).J.root ∧
      TargetQCAt p.E B fp.height (heightView p B).J), Result) : Result :=
  wc_dischargeL hc.base hc.sync hc.deltaF (wc_faultTransfer hS hc)
    (wc_participation hS hc hs.firstVoteAfterGST) consume

end AvailableChain.FGSA.Run
end
