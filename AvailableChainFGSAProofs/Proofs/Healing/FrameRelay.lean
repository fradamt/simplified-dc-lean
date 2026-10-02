module
public import AvailableChainFGSAClaims.Statements.ComposeStmt
public import AvailableChainFGSARun.Proofs.Receipts
public import AvailableChainFGSAProofs.Proofs.Shared.StoreRun
public import AvailableChainFGSAProofs.Proofs.Healing.PhaseFrame

public section

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

variable (p : Params) {In V : Type} [DecidableEq V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

omit [DecidableEq V] in
/-- Blueprint 21:749–783, 1148–1252; plan S30, H-FRAME/F2.
DC: SAME order of strict event cuts. -/
private theorem frame_idx_mono {a b : Time} (hab : a ≤ b) :
    V2.D.Run.idxBefore rho a ≤ V2.D.Run.idxBefore rho b := by
  rw [V2.D.Run.idxBefore_def, V2.D.Run.idxBefore_def,
    ← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
  exact List.countP_mono_left (fun e _ he =>
    decide_eq_true ((of_decide_eq_true he).trans_le hab))

/-- Blueprint 21:749–783, 1148–1252; plan S30, H-FRAME/F2.
DC: INTENTIONAL strict relay of an arbitrary held FG carrier, including old carriers.
The receiver ancestry is explicit at the deadline. Assembly supplies RMono.
Standalone rows use ΔF; this block object uses Δ. -/
theorem healing_held_block_receipt (mono : RMono p c E rho)
    (hvalid : V2.D.ExecutionValid E rho) (hnr : V2.D.NoRestart rho)
    (hdelta : E.Δ = p.Δ) {ΔF : Time}
    (hsync : Gen.V2.Duty.PartialSynchronyBy E rho (fgsaDelay E.Δ ΔF))
    {i : Nat} {x y : V} {t : Time} {W : FGBlock (Fin p.n)}
    (hi : rho.events[i]? = some (.tick x t))
    (hx : x ∈ rho.honest) (hy : y ∈ rho.honest)
    (hW : W ∈ (storeAt p c E rho i x).fg.TF)
    (hgst : E.t_GST ≤ t) (hhor : t + p.Δ ≤ rho.horizon)
    (hF : FGBlock.Preceq
      (storeAt p c E rho (V2.D.Run.idxBefore rho (t + p.Δ)) y).fg.F W) :
    Gen.V2.Duty.HoldsBefore E rho (fun nd => W ∈ nd.st.fg.TF) (t + p.Δ) y := by
  have hs := hvalid.toScheduleWellFormed
  change W ∈ (V2.D.Run.stateBeforeTime E rho (t + p.Δ) y).st.fg.TF
  rw [← Gen.V2.Duty.stateBefore_idxBefore E rho _ hs]
  by_cases hg : W = .genesis
  · exact hg ▸ (storeBundle_stateBefore E rho _ y).cstore.fg.gen
  have hb : eraseFG W ∈ (storeAt p c E rho i x).base.blocks :=
    (storeBundle_stateBefore E rho i x).cstore.baseTree _ |>.mpr ⟨W, hW, rfl⟩
  change eraseFG W ∈ (V2.D.Run.stateBefore E rho i x).st.base.blocks at hb
  rw [← (storeBundle_stateBefore E rho i x).«meta».stampKeys] at hb
  obtain ⟨⟨b, stamp⟩, hb, he⟩ := List.mem_map.mp hb
  dsimp only at he
  subst b
  rcases fgsa_block_stamp_source E rho i x (eraseFG W) stamp hb with
      hgen | ⟨k, hki, u, o, ho, ha, _⟩
  · exact (hg (eraseFG_eq_genesis.mp hgen.1)).elim
  obtain ⟨parent, hk, _⟩ := ha.1
  obtain ⟨hil, hie⟩ := List.getElem?_eq_some_iff.mp hi
  obtain ⟨hkl, hke⟩ := List.getElem?_eq_some_iff.mp hk
  have htime := (List.pairwise_iff_getElem.mp hs.sorted) k i hkl hil hki
  rw [hie, hke] at htime
  have hut : u ≤ t := V2.D.Engine.time_le_of_key_le _ _ htime
  let dl := fun u => max u E.t_GST + p.Δ
  have hd : dl u ≤ t + p.Δ := Int.add_le_add_right (max_le hut hgst) p.Δ
  have hidx := frame_idx_mono p c rho hd
  have hF' := (mono hnr _ _ y hy hidx).1
  have hcompat : Block.Compatible (eraseFG W)
      (eraseFG (V2.D.Run.stateBeforeTime E rho (dl u) y).st.fg.F) := by
    rw [← Gen.V2.Duty.stateBefore_idxBefore E rho _ hs]
    exact Bool.or_eq_true_iff.mpr (Or.inr
      (eraseFG_preceq (KitFG.preceq_trans hF' hF)))
  have delay (o : Obj p) (hn : ¬ isRowObject o) : fgsaDelay E.Δ ΔF o = p.Δ := by
    cases he : o.payload <;> simp only [fgsaDelay_def, he, hdelta]
    exact (hn (by change (match o.payload with | .row _ => True | _ => False)
                  rw [he]; trivial)).elim
  have hD := Gen.V2.Duty.deliveryWithinOn_of_partialSynchronyBy E rho hsync
    (fun o => ¬ isRowObject o) p.Δ delay
  have hu : u < dl u := (le_max_left u E.t_GST).trans_lt (lt_add_of_pos_right _ p.deltaPos)
  dsimp only [blockOf?] at ho
  cases hdec : (toWire p o).decode with
  | none => simp only [hdec, reduceCtorEq] at ho
  | some msg =>
    cases msg <;> simp only [hdec, reduceCtorEq, Option.some.injEq] at ho
    rename_i slot b raw sup rows
    subst b
    have he : o = ofWire p ⟨.proposer slot, .proposal (eraseFG W) raw sup rows⟩ := by
      apply toWire_injective
      rw [toWire_ofWire]
      exact decode_eq_block.mp hdec
    obtain ⟨Y, hY, hYW⟩ := fgsa_proposal_receipt E rho hdelta hvalid hnr dl rho.horizon
      slot (eraseFG W) raw sup rows u y hD (Or.inr ⟨x, hx, k, he ▸ ha⟩) hy
      (hd.trans hhor) hu hcompat
    have hYeq : Y = W := eraseFG_injective hYW
    rw [hYeq, ← Gen.V2.Duty.stateBefore_idxBefore E rho _ hs] at hY
    exact (fgsa_store_cumulative p c E rho hnr hidx y).1 hY

/-- Blueprint 21:749–783, 1148–1252; plan S30, H-FRAME/F2.
DC: INTENTIONAL receiver frames are required at the strict receipt cut.
RXing uses the accepted finality certificate and a witness held at that same cut.
Settlement only at the source HEAD does not supply the destination frames. -/
theorem healing_witness_relay (mono : RMono p c E rho) (crossing : RXing p c E rho)
    (hvalid : V2.D.ExecutionValid E rho) (hnr : V2.D.NoRestart rho)
    (hdelta : E.Δ = p.Δ) {ΔF : Time}
    (hsync : Gen.V2.Duty.PartialSynchronyBy E rho (fgsaDelay E.Δ ΔF))
    {i : Nat} {x : V} {s m : Nat} {J : Option (FGBlock (Fin p.n))} {contested : Bool}
    (hx : x ∈ rho.honest)
    (hi : rho.events[i]? = some (.tick x (SA.voteTime p.toParams s)))
    (hgst : E.t_GST ≤ SA.voteTime p.toParams s)
    (hhor : SA.voteTime p.toParams s + p.Δ ≤ rho.horizon)
    (W : FGBlock (Fin p.n)) (hW : W ∈ (storeAt p c E rho i x).fg.TF)
    (hsrc : SettledPhaseFrame p (storeAt p c E rho i x) m J contested)
    (hZW : FGBlock.Preceq (R_at p c E rho i x).Z W)
    (hlo : (R_at p c E rho i x).lo ≤ (heightView p W).h)
    (hdst : ∀ y ∈ rho.honest, SettledPhaseFrame p
      (storeAt p c E rho (V2.D.Run.idxBefore rho (SA.voteTime p.toParams s + p.Δ)) y)
      m J contested) :
    ∀ y ∈ rho.honest, Gen.V2.Duty.HoldsBefore E rho
      (fun nd => ∀ B, FGBlock.Preceq B W → B ∈ nd.st.fg.TF)
      (SA.voteTime p.toParams s + p.Δ) y := by
  let j := V2.D.Run.idxBefore rho (SA.voteTime p.toParams s + p.Δ)
  have hij : i < j := (Gen.V2.Duty.index_lt_idxBefore_iff hvalid.toScheduleWellFormed hi _).mpr
    (lt_add_of_pos_right _ p.deltaPos)
  have hWj := (fgsa_store_cumulative p c E rho hnr hij.le x).1 hW
  intro y hy
  have hd := hdst y hy
  have hF : FGBlock.Preceq (storeAt p c E rho j y).fg.F W := by
    cases J with
    | some B =>
      have hJB : (R_at p c E rho i x).Z = B := hsrc.2.2.2.1.2.2.1
      exact KitFG.preceq_trans hd.2.2.2.1.2.2.2.2.2 (hJB ▸ hZW)
    | none =>
      obtain ⟨K, hK, hKF, hKh⟩ := hd.2.2.2.1.2.2.1
      have hfloor : (R_at p c E rho j y).lo = (R_at p c E rho i x).lo :=
        hd.2.2.1.trans hsrc.2.2.1.symm
      exact crossing j j y x K W hy le_rfl hK hKF ⟨hx, hWj⟩
        (hKh.trans_le (hfloor ▸ hlo))
  have hreceipt := healing_held_block_receipt p c E rho mono hvalid hnr hdelta hsync
    hi hx hy hW hgst hhor hF
  change W ∈ (V2.D.Run.stateBeforeTime E rho _ y).st.fg.TF at hreceipt
  change ∀ B, FGBlock.Preceq B W → B ∈ (V2.D.Run.stateBeforeTime E rho _ y).st.fg.TF
  intro B hBW
  have hinv := (storeBundle_stateBeforeTime E rho (SA.voteTime p.toParams s + p.Δ) y).cstore
  obtain ⟨A, hA, he⟩ := eraseFG_ancestor_mem hinv.fg.closed hreceipt (eraseFG_preceq hBW)
  exact (eraseFG_injective he) ▸ hA

/-- Blueprint 21:749–783, 1148–1252; plan S30, H-FRAME/F2; owner B25/B26.
DC: INTENTIONAL the phase must include the strict receipt deadline.
The receiver frames come from healing_settled_frame. The lower-cut bridge is
kept in one place; it uses B25's strict PhaseInterval cut (idxBefore u). -/
theorem healing_witness_relay_phase (mono : RMono p c E rho) (crossing : RXing p c E rho)
    (hvalid : V2.D.ExecutionValid E rho) (hnr : V2.D.NoRestart rho)
    (hdelta : E.Δ = p.Δ) {ΔF : Time}
    (hsync : Gen.V2.Duty.PartialSynchronyBy E rho (fgsaDelay E.Δ ΔF))
    (u v : Time) (m : Nat) (J : Option (FGBlock (Fin p.n))) (contested : Bool)
    (hgst : E.t_GST ≤ u) (hphase : PhaseInterval p c E rho u v m J contested)
    {i : Nat} {x : V} {s : Slot} (hx : x ∈ rho.honest)
    (hi : rho.events[i]? = some (.tick x (SA.voteTime p.toParams s)))
    (hhead : u ≤ SA.voteTime p.toParams s)
    (hreceipt : SA.voteTime p.toParams s + p.Δ ≤ v)
    (hhor : SA.voteTime p.toParams s + p.Δ ≤ rho.horizon)
    (W : FGBlock (Fin p.n)) (hW : W ∈ (storeAt p c E rho i x).fg.TF)
    (hsrc : SettledPhaseFrame p (storeAt p c E rho i x) m J contested)
    (hZW : FGBlock.Preceq (R_at p c E rho i x).Z W)
    (hlo : (R_at p c E rho i x).lo ≤ (heightView p W).h) :
    ∀ y ∈ rho.honest, Gen.V2.Duty.HoldsBefore E rho
      (fun nd => ∀ B, FGBlock.Preceq B W → B ∈ nd.st.fg.TF)
      (SA.voteTime p.toParams s + p.Δ) y := by
  have hstrict : u < SA.voteTime p.toParams s + p.Δ :=
    hhead.trans_lt (lt_add_of_pos_right _ p.deltaPos)
  have hlow : timeIdx rho u ≤ V2.D.Run.idxBefore rho (SA.voteTime p.toParams s + p.Δ) := by
    change (rho.events.filter (fun e => decide (e.time ≤ u))).length ≤
      (rho.events.filter (fun e => decide (e.time < SA.voteTime p.toParams s + p.Δ))).length
    rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
    exact List.countP_mono_left (fun e _ he =>
      decide_eq_true ((of_decide_eq_true he).trans_lt hstrict))
  have hhigh : V2.D.Run.idxBefore rho (SA.voteTime p.toParams s + p.Δ) ≤ timeIdx rho v := by
    change (rho.events.filter (fun e => decide (e.time < SA.voteTime p.toParams s + p.Δ))).length ≤
      (rho.events.filter (fun e => decide (e.time ≤ v))).length
    rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
    exact List.countP_mono_left (fun e _ he =>
      decide_eq_true ((of_decide_eq_true he).le.trans hreceipt))
  apply healing_witness_relay p c E rho mono crossing hvalid hnr hdelta hsync hx hi
    (hgst.trans hhead) hhor W hW hsrc hZW hlo
  intro y hy
  exact healing_settled_frame p c E rho crossing u v m J contested hgst hphase _ y hlow hhigh hy

end AvailableChain.FGSA.Run
end
