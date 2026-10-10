module
public import AvailableChainFGSAProofs.Proofs.Healing.FrameRelay
public import AvailableChainFGSAProofs.Proofs.Healing.FrameZero
public import AvailableChainFGSAProofs.Proofs.Healing.PhaseRelay

public section

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

variable (p : Params) {In V : Type} [DecidableEq V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

/-- Blueprint 21:749–783, 1153–1162; plan H-SUPPORT S0 (H-FRAME review F1); ruling B25.
DC: INTENTIONAL the settled frame is read at the strict PhaseInterval cut idxBefore u.
A HEAD tick at u = v_s reads a state inside this cut. No GST premise is used. -/
theorem healing_settled_frame_strict (crossing : RXing p c E rho)
    (u v : Time) (m : Nat) (J : Option (FGBlock (Fin p.n))) (contested : Bool)
    (hp : PhaseInterval p c E rho u v m J contested)
    (i : Nat) (x : V) (hui : V2.D.Run.idxBefore rho u ≤ i) (hiv : i ≤ timeIdx rho v)
    (hx : x ∈ rho.honest) :
    SettledPhaseFrame p (storeAt p c E rho i x) m J contested := by
  obtain ⟨hH, hc, hr⟩ := hp.2.2.2 i x hui hiv hx
  exact healing_phase_frame p c E rho crossing hx hp.2.2.1 hH hc hr

omit [DecidableEq V] in
/-- Blueprint 21:749–783, 1153–1162; plan H-SUPPORT S0; ruling B25.
DC: SAME an event at or after u is not before the strict cut at u. -/
theorem healing_support_idxBefore_le (hs : V2.D.ScheduleWellFormed E rho)
    {i : Nat} {e : V2.Event V (Obj p)} (hi : rho.events[i]? = some e) {u : Time}
    (hu : u ≤ e.time) : V2.D.Run.idxBefore rho u ≤ i := by
  by_contra hn
  have hlt := (Gen.V2.Duty.index_lt_idxBefore_iff hs hi u).mp (Nat.lt_of_not_ge hn)
  exact (not_lt.mpr hu) hlt

/-- ROOT-DIGEST W2b. Blueprint 21:749–783, 1148–1252; plan H-SUPPORT S0 (H-FRAME review F1); B25,
B26.
DC: INTENTIONAL the source frame comes from the phase at the strict cut, so the
hsrc premise of healing_witness_relay_phase is derived. The HEAD may be at u = v_s.
The finite horizon follows from the phase end. -/
theorem healing_witness_relay_settled (mono : RMono p c E rho) (crossing : RXing p c E rho)
    (hvalid : V2.D.ExecutionValid E rho) (hnr : V2.D.NoRestart rho)
    (hdelta : E.Δ = p.Δ) {ΔF : Time}
    (hsync : Gen.V2.Duty.PartialSynchronyBy E rho (fgsaDelay E.Δ ΔF))
    (u v : Time) (m : Nat) (J : Option (FGBlock (Fin p.n))) (contested : Bool)
    (hgst : E.t_GST ≤ u) (hphase : PhaseInterval p c E rho u v m J contested)
    {i : Nat} {x : V} {s : Slot} (hx : x ∈ rho.honest)
    (hi : rho.events[i]? = some (.tick x (SA.voteTime p.toParams s)))
    (hhead : u ≤ SA.voteTime p.toParams s)
    (hreceipt : SA.voteTime p.toParams s + p.Δ ≤ v)
    (W : FGBlock (Fin p.n)) (hW : W ∈ (storeAt p c E rho i x).fg.TF)
    (hZW : FGBlock.Preceq (R_at p c E rho i x).Z W)
    (hlo : (R_at p c E rho i x).lo ≤ (heightView p W).h)
    (hroots : NamedReceiptRootCollisionFree p c E rho) :
    ∀ y ∈ rho.honest, E.awake y (SA.voteTime p.toParams s + p.Δ) = true →
          Gen.V2.Duty.HoldsBefore E rho
      (fun nd => ∀ B, FGBlock.Preceq B W → B ∈ nd.st.fg.TF)
      (SA.voteTime p.toParams s + p.Δ) y := by
  have hs := hvalid.toScheduleWellFormed
  have hui := healing_support_idxBefore_le p c E rho hs hi hhead
  have hiv : i ≤ timeIdx rho v := (healing_phase_lt_timeIdx p c E rho hs hi
    ((le_add_of_nonneg_right p.deltaPos.le).trans hreceipt)).le
  exact healing_witness_relay_phase (hroots := hroots)
    p c E rho mono crossing hvalid hnr hdelta hsync
    u v m J contested hgst hphase hx hi hhead hreceipt (hreceipt.trans hphase.2.1) W hW
    (healing_settled_frame_strict p c E rho crossing u v m J contested hphase i x hui hiv hx)
    hZW hlo

/-- ROOT-DIGEST W2b. Blueprint 21:749–783, 1148–1252; plan H-SUPPORT S0 and §4 step 3 (F1 + F2).
DC: INTENTIONAL the HEAD of an honest node in the phase has a full-domain witness K
and a height witness W above K; all ancestors of W reach every honest store
strictly before v_s + Δ. The HEAD itself need not be in its frozen domain. -/
theorem healing_head_witness_relay (mono : RMono p c E rho) (crossing : RXing p c E rho)
    (hvalid : V2.D.ExecutionValid E rho) (hnr : V2.D.NoRestart rho)
    (hdelta : E.Δ = p.Δ) {ΔF : Time}
    (hsync : Gen.V2.Duty.PartialSynchronyBy E rho (fgsaDelay E.Δ ΔF))
    (u v : Time) (m : Nat) (J : Option (FGBlock (Fin p.n))) (contested : Bool)
    (hgst : E.t_GST ≤ u) (hphase : PhaseInterval p c E rho u v m J contested)
    {i : Nat} {x : V} {s : Slot} (hx : x ∈ rho.honest)
    (hi : rho.events[i]? = some (.tick x (SA.voteTime p.toParams s)))
    (hhead : u ≤ SA.voteTime p.toParams s)
    (hreceipt : SA.voteTime p.toParams s + p.Δ ≤ v)
    (hroots : NamedReceiptRootCollisionFree p c E rho) :
    let st := ((fgsa p c).clock (rho.stateBefore E i x) (SA.voteTime p.toParams s)).st
    ∃ K ∈ fullTree p st, eraseFG K = headVote p st s ∧
      ∃ W ∈ st.fg.TF, FGBlock.Preceq K W ∧ (controls p st).lo ≤ (heightView p W).h ∧
        ∀ y ∈ rho.honest, E.awake y (SA.voteTime p.toParams s + p.Δ) = true →
          Gen.V2.Duty.HoldsBefore E rho
          (fun nd => ∀ B, FGBlock.Preceq B W → B ∈ nd.st.fg.TF)
          (SA.voteTime p.toParams s + p.Δ) y := by
  intro st
  have hs := hvalid.toScheduleWellFormed
  obtain ⟨K, hK, hk, W, hW, hKW, hlo⟩ :=
    healing_full_witness_all p c E rho hs crossing hx hi
  have hfg : st.fg = (storeAt p c E rho i x).fg := clock_fg p _ _
  have hZK : FGBlock.Preceq (controls p st).Z K :=
    ((KitFG.mem_filteredFromView _ _ _ _).mp hK).2.2.1
  have hR : controls p st = R_at p c E rho i x := by
    change KitFG.treeStoreControlsView (heightView p) st.fg =
      KitFG.treeStoreControlsView (heightView p) (storeAt p c E rho i x).fg
    rw [hfg]
  refine ⟨K, hK, hk, W, hW, hKW, hlo, ?_⟩
  apply healing_witness_relay_settled (hroots := hroots)
    p c E rho mono crossing hvalid hnr hdelta hsync
    u v m J contested hgst hphase hx hi hhead hreceipt W (hfg ▸ hW)
  · exact hR ▸ KitFG.preceq_trans hZK hKW
  · exact hR ▸ hlo

end AvailableChain.FGSA.Run
end
