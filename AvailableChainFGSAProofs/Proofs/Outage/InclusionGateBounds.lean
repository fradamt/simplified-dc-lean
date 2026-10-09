module
public import AvailableChainFGSAProofs.Proofs.Outage.InclusionGate

public section

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG
open Gen.Pure

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

private theorem igate_saved_of_mem (st : State p.n) (hinv : CStoreInv p st)
    {r : Slot} {C : Block} (hm : (r, some C) ∈ st.base.genuine) :
    GridCO.savedGenuine st.base r = some (some C) := by
  cases hf : st.base.genuine.find? (fun row => row.1 == r) with
  | none =>
    have hn := List.find?_eq_none.mp hf _ hm
    simp at hn
  | some row =>
    have he : row.1 = r := by simpa using List.find?_some hf
    have hr := List.inj_on_of_nodup_map hinv.genuineKeys
      (List.mem_of_find?_eq_some hf) hm he
    change (st.base.genuine.find? _).map Prod.snd = _
    rw [hf, hr]
    rfl

private theorem igate_process_saved (st : State p.n) (hinv : CStoreInv p st)
    (w : Wire p.n) (P : Block)
    (hb : ∀ r C, (r, some C) ∈ st.base.genuine → Block.Preceq C P) :
    ∀ r C, (r, some C) ∈ (process p st w).base.genuine → Block.Preceq C P := by
  intro r C hm
  unfold process at hm
  cases hd : w.decode with
  | none => rw [hd] at hm; exact hb r C hm
  | some input =>
    rw [hd] at hm
    cases input with
    | vote s q B => rw [admitHead_genuine] at hm; exact hb r C hm
    | row q body =>
      dsimp only at hm
      rcases admitRow_eq p st ⟨w.auth, body⟩ with he | he <;>
        rw [he] at hm <;> exact hb r C hm
    | block s N =>
      dsimp only at hm
      cases hn : namedParentHeld st N with
      | false =>
        rw [admitBlock_refused p st s N (Or.inl hn)] at hm
        exact hb r C hm
      | true =>
        cases hp : parentFG st N.erase with
        | none =>
          rw [admitBlock_refused p st s N (Or.inr (Or.inl hp))] at hm
          exact hb r C hm
        | some D =>
          cases ha : blockAccepted p st s N D with
          | false =>
            rw [admitBlock_refused p st s N (Or.inr (Or.inr ⟨D, hp, ha⟩))] at hm
            exact hb r C hm
          | true =>
            obtain ⟨pool, he, _⟩ := admitBlock_accepted_eq p st s N D hn hp ha
            obtain ⟨_, _, _, _, hgen, _, _⟩ :=
              base_admitProposal_accepts p st hinv.toInv0 s N D hp ha
            rw [he] at hm
            dsimp only at hm
            split at hm
            · rw [hgen] at hm
              exact hb r C hm
            · rw [reconcile_genuine, List.mem_map] at hm
              obtain ⟨row, hrow, hroweq⟩ := hm
              have hval := (Prod.mk.inj hroweq).2
              have hsome := (Option.filter_eq_some_iff.mp hval).1
              have hkey := (Prod.mk.inj hroweq).1
              rw [hgen] at hrow
              exact hb r C (by simpa only [← hkey, ← hsome] using hrow)

private theorem igate_below_at_cut
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (d : Time) (P : Block)
    (hresults : ∀ r B, (r, B) ∈ cleanResults p c E rho (V2.D.Run.idxBefore rho d) →
      Block.Preceq B P)
    {k : Nat} (hk : k ≤ V2.D.Run.idxBefore rho d) {r : Slot} {X : Block}
    (hb : BelowLabel p c E rho k r X) : Block.Preceq X P := by
  rcases hb with rfl | ⟨q, B, ⟨j, hj, x, ht, hB⟩, _, hXB⟩
  · exact block_genesis_preceq _
  · exact block_preceq_trans hXB (hresults q B ⟨j, lt_of_lt_of_le hj hk, x, ht, hB⟩)

private theorem igate_frame_at_cut
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hstrat : RStrat p c E rho) (hstore : RStore p c E rho)
    (hroots : NamedRootCollisionFree p c E rho)
    (_hsrc : SrcFrameAboveStmt p c E rho)
    (hrows : ∀ i j x r (a : RowWire p.n) e, i ≤ timeIdx rho rho.horizon → j < i →
      HonestRowAt p c E rho j x r a → namedEntry a.payload.height_pair = some e →
      ∃ C, actionSourceFG p c E rho x r = some (some C) ∧ EntryBelow p e C ∧
        BelowLabel p c E rho i (labelBoundAt p c rho j) (eraseFG C))
    (d : Time) (P : Block) (hcut : V2.D.Run.idxBefore rho d ≤ timeIdx rho rho.horizon)
    (hresults : ∀ r B, (r, B) ∈ cleanResults p c E rho (V2.D.Run.idxBefore rho d) →
      Block.Preceq B P)
    {k : Nat} (hk : k ≤ V2.D.Run.idxBefore rho d) {x : V} (hx : x ∈ rho.honest) :
    Block.Preceq (F_at p c E rho k x) P ∧ Block.Preceq (J_at p c E rho k x) P := by
  let Φ := fun X : FGBlock (Fin p.n) => Block.Preceq (eraseFG X) P
  have hac : AncestorClosed p Φ :=
    ⟨fun _ _ hXY hY => block_preceq_trans (eraseFG_preceq hXY) hY⟩
  have hf := (srcFrameAbove_scoped p c E rho hstore hstrat Φ 0 hac (fun _ => block_genesis_preceq
    P) k x hx ?_).2
  · exact ⟨hf.1 (Nat.zero_le _), hf.2.1 (Nat.zero_le _)⟩
  · intro y r a X hrow hname hScope _
    obtain ⟨j, hj, ha⟩ := hrow
    obtain ⟨C, hSource, ⟨Y, hYC, he⟩, hb⟩ := hrows k j y r a _ (hk.trans hcut) hj ha hname
    have hYX : Y = X := rootScope_eq hroots (rootScope_ancestor (rootScope_source ha.1 hSource) hYC)
      hScope (congrArg Prod.snd he)
    subst Y
    exact block_preceq_trans (eraseFG_preceq hYC)
      (igate_below_at_cut E rho d P hresults hk hb)

private theorem igate_raw_at_tick
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hs : V2.D.ScheduleWellFormed E rho) {j : Nat} {x : V} {r : Slot}
    (ht : IsGateTick p c rho j x r) :
    gateResultAt p c E rho j = some ((fgsaAC E rho).raw j r x) := by
  rw [gateResultAt_eq_gateResult p c E rho hs ht, gateResult_def, gateIn_def, preTick_def,
    fgsa_tickIdx_of_event p c E rho hs ht]
  dsimp only [Option.map_some]
  have hv := fgsa_clockPre_gateView p (storeAt p c E rho j x) r
  have he := congrArg (fun v => SA.Root.confirmationFrom p.toParams
    (eraseFG (storeAt p c E rho j x).fg.F) v r) hv
  rw [clockPre_fg]
  exact congrArg some he

private theorem igate_normal_below {F S P : Block}
    (hF : Block.Preceq F P) (hS : Block.Preceq S P) :
    Block.Preceq (Gen.AC.normalizeOutput F S) P := by
  rw [Gen.AC.normalizeOutput_def]
  split <;> assumption

private theorem igate_state_at_cut
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hs : V2.D.ScheduleWellFormed E rho)
    (hnonempty : ∀ j x s, j < timeIdx rho rho.horizon → x ∈ rho.honest →
      IsGateTick p c rho j x s →
      ∃ B, gateResultAt p c E rho j = some (some B) ∧ (s = 0 → B = .genesis))
    (d : Time) (P : Block) (hcut : V2.D.Run.idxBefore rho d ≤ timeIdx rho rho.horizon)
    (hresults : ∀ r B, (r, B) ∈ cleanResults p c E rho (V2.D.Run.idxBefore rho d) →
      Block.Preceq B P)
    (hF : ∀ k, k ≤ V2.D.Run.idxBefore rho d → ∀ x ∈ rho.honest,
      Block.Preceq (F_at p c E rho k x) P) :
    ∀ k, k ≤ V2.D.Run.idxBefore rho d → ∀ x ∈ rho.honest,
      Block.Preceq (S_at p c E rho k x) P ∧
        ∀ r C, GridCO.savedGenuine (storeAt p c E rho k x).base r = some (some C) →
          Block.Preceq C P := by
  classical
  intro k
  induction k with
  | zero =>
    intro _ x _
    refine ⟨block_genesis_preceq _, ?_⟩
    intro r C hC
    cases hC
  | succ k ih =>
    intro hk x hx
    have hk' : k ≤ V2.D.Run.idxBefore rho d := (Nat.le_succ k).trans hk
    obtain ⟨hS, hsaved⟩ := ih hk' x hx
    have hmem : ∀ r C, (r, some C) ∈ (storeAt p c E rho k x).base.genuine →
        Block.Preceq C P := fun r C hm =>
      hsaved r C (igate_saved_of_mem _ (cstoreInv_stateBefore E rho k x) hm)
    have hout : Block.Preceq (S_at p c E rho (k + 1) x) P := by
      rcases fgsaAC_output_step E rho k x with he | ⟨r, ht⟩ | ⟨o, t, B, ht, hb, ha, he⟩ |
        ⟨t, ht, he⟩
      · rw [show S_at p c E rho (k + 1) x = S_at p c E rho k x from
          by rw [S_at_def, S_at_def]; exact he]
        exact hS
      · obtain ⟨C, hC, _⟩ := hnonempty k x r (lt_of_lt_of_le (by omega) hcut) hx ht
        have hraw : (fgsaAC E rho).raw k r x = some C := by
          exact Option.some.inj ((igate_raw_at_tick E rho hs ht).symm.trans hC)
        have hCP := hresults r C ⟨k, by omega, x, ht, hC⟩
        rcases (fgsaAC_gate_write E rho k r x ht).effects with hskip | hrun
        · rw [show S_at p c E rho (k + 1) x = S_at p c E rho k x from
            by rw [S_at_def, S_at_def]; exact hskip.2.1]
          exact hS
        · by_cases hg : ∀ lease ∈ ((fgsaAC E rho).gateView k x r).obligations,
              Block.Compatible (Gen.AC.Lease.target lease) C
          · have he := (hrun.accept C hraw hg).1
            rw [S_at_def]
            change Block.Preceq ((fgsaAC E rho).output (k + 1) x) P
            rw [he]
            apply igate_normal_below (hF k hk' x hx)
            unfold GridCO.advance
            split <;> assumption
          · have hveto : ∃ lease ∈ ((fgsaAC E rho).gateView k x r).obligations,
                ¬ Block.Compatible (Gen.AC.Lease.target lease) C := by
              simpa only [not_forall, exists_prop] using hg
            rw [show S_at p c E rho (k + 1) x = S_at p c E rho k x from
              by rw [S_at_def, S_at_def]; exact (hrun.veto C hraw hveto).1]
            exact hS
      · rw [S_at_def]
        change Block.Preceq ((fgsaAC E rho).output (k + 1) x) P
        rw [he]
        exact igate_normal_below (hF (k + 1) hk x hx) hS
      · rw [show S_at p c E rho (k + 1) x = S_at p c E rho 0 x from
          by rw [S_at_def, S_at_def]; exact he]
        exact block_genesis_preceq _
    refine ⟨hout, ?_⟩
    intro r C hC
    cases he : rho.events[k]? with
    | none =>
      have heq : storeAt p c E rho (k + 1) x = storeAt p c E rho k x := by
        unfold storeAt V2.D.Run.stateBefore
        rw [List.take_add_one, he]
        simp only [Option.toList_none, List.append_nil]
      rw [heq] at hC
      exact hsaved r C hC
    | some e =>
      by_cases hx' : e.node = x
      · cases e with
        | restart y t =>
          change y = x at hx'
          subst y
          change GridCO.savedGenuine
            (V2.D.Run.stateBefore E rho (k + 1) x).st.base r = _ at hC
          rw [V2.D.Run.stateBefore_succ E rho he] at hC
          simp only [V2.D.World.step, Function.update_self] at hC
          cases hC
        | deliver y o t =>
          change y = x at hx'
          subst y
          have hp : storeAt p c E rho (k + 1) x =
              process p (storeAt p c E rho k x) (toWire p o) := by
            unfold storeAt
            rw [V2.D.Run.stateBefore_succ E rho he]
            simp only [V2.D.World.step, Function.update_self]
            rfl
          rw [hp] at hC
          exact igate_process_saved _ (cstoreInv_stateBefore E rho k x) _ P hmem
            r C (mem_genuine_of_saved hC)
        | tick y t =>
          change y = x at hx'
          subst y
          by_cases hg : ∃ q, t = SA.gateTime p.toParams q
          · obtain ⟨q, rfl⟩ := hg
            have hw := fgsaAC_gate_write E rho k q x he
            change (fgsaAC E rho).saved (k + 1) x r = some (some C) at hC
            by_cases hr : r = q
            · subst r
              rw [hw.fresh (fgsa_gate_fresh E rho hs he)] at hC
              have hraw := Option.some.inj hC
              have hres := (igate_raw_at_tick E rho hs he).trans (congrArg some hraw)
              exact hresults q C ⟨k, by omega, x, he, hres⟩
            · rw [hw.saved_other r hr] at hC
              exact hsaved r C hC
          · have hc := inclusion_clock_offGate p (storeAt p c E rho k x) t
              (fun q hq => hg ⟨q, hq.symm⟩)
            have hp : storeAt p c E rho (k + 1) x = clockPre p (storeAt p c E rho k x) t := by
              unfold storeAt
              rw [V2.D.Run.stateBefore_succ E rho he]
              simp only [V2.D.World.step, Function.update_self]
              exact (tick_st (c := c) E rho _ x t).trans hc
            rw [hp, savedGenuine_congr (clockPre_genuine p _ _) r] at hC
            exact hsaved r C hC
      · have hp : storeAt p c E rho (k + 1) x = storeAt p c E rho k x := by
          unfold storeAt
          rw [V2.D.Run.stateBefore_succ E rho he, V2.D.World.step_apply_of_node_ne E rho _ hx']
        rw [hp] at hC
        exact hsaved r C hC

private theorem igate_slot_pos (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (_hE : V2.D.ExecutionValid E rho) (pt : PtSP)
    (hprop : HonestProposal E rho (fgsaInterface p c) pt.s pt.P) : 0 < pt.s := hprop.1.1

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. Blueprint 03:418–458; spec 683–694; plan I-GATE, G3. Class (iii).
DC: INTENTIONAL; all origins are bounded at the strict cut idxBefore d.
Other nodes' gate ticks at d do not enter this cut. The local gate input
has the same store. ClockPre keeps F, J, S and bodies, and deletes leases. -/
theorem inclusion_preGate_bounds [Fintype V]
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (ΔF : Time)
    (hset : CleanSet p c E rho ΔF)
    (hstore : RStore p c E rho) (hframe : RFrameExactNext p c E rho)
    (hsrc : SrcFrameAboveStmt p c E rho)
    (hordered : ∀ x y r s B C, x ∈ rho.honest → y ∈ rho.honest →
      SA.gateTime p.toParams r ≤ rho.horizon → SA.gateTime p.toParams s ≤ rho.horizon →
      gateResult p c E rho x r = some (some B) →
      gateResult p c E rho y s = some (some C) →
      (r < s → Block.Preceq B C) ∧ (r = s → Block.Compatible B C))
    (hnonempty : ∀ j x s, j < timeIdx rho rho.horizon → x ∈ rho.honest →
      IsGateTick p c rho j x s →
      ∃ B, gateResultAt p c E rho j = some (some B) ∧ (s = 0 → B = .genesis))
    (htransfer : ∀ x y s B H, x ∈ rho.honest → y ∈ rho.honest →
      SA.gateTime p.toParams s ≤ rho.horizon → gateResult p c E rho x s = some (some B) →
      vHead p c E rho y s = some H → Block.Preceq B H)
    (hleases : ∀ i v, i ≤ timeIdx rho rho.horizon → v ∈ rho.honest →
      ∀ row ∈ (storeAt p c E rho i v).base.obligations,
        BelowLabel p c E rho i (labelBoundAt p c rho i) row.1)
    (hrows : ∀ i j x r (a : RowWire p.n) e, i ≤ timeIdx rho rho.horizon → j < i →
      HonestRowAt p c E rho j x r a → namedEntry a.payload.height_pair = some e →
      ∃ C, actionSourceFG p c E rho x r = some (some C) ∧ EntryBelow p e C ∧
        BelowLabel p c E rho i (labelBoundAt p c rho j) (eraseFG C))
    (pt : PtSP) (hprop : HonestProposal E rho (fgsaInterface p c) pt.s pt.P)
    (hhor : SA.gateTime p.toParams pt.s ≤ rho.horizon)
    {i : Nat} {x : V} (hx : x ∈ rho.honest) (ht : IsGateTick p c rho i x pt.s)
    (hstrat : RStrat p c E rho) :
    let pre := clockPre p (storeAt p c E rho i x) (SA.gateTime p.toParams pt.s)
    Block.Preceq (eraseFG pre.fg.F) pt.P ∧ Block.Preceq (eraseFG pre.fg.J) pt.P ∧
      Block.Preceq (S_at p c E rho i x) pt.P ∧
      (∀ row ∈ pre.base.obligations, Block.Preceq row.1 pt.P) ∧
      (∀ r C, GridCO.savedGenuine pre.base r = some (some C) → Block.Preceq C pt.P) ∧
      (∀ r X, X ∈ (fastWriteAt pre r).getD [] → Block.Preceq X pt.P) := by
  let d := SA.gateTime p.toParams pt.s
  let k := V2.D.Run.idxBefore rho d
  let pre := clockPre p (storeAt p c E rho i x) d
  have hs := hset.pre.base.valid.toScheduleWellFormed
  have hhead := inclusion_headAtLabel (hstrat := hstrat) E rho ΔF hset hstore hframe hsrc hordered
    hnonempty
    htransfer hleases hrows pt hprop hhor
  have hpos := igate_slot_pos E rho hset.pre.base.valid pt hprop
  have hresults := inclusion_prior_results_below E rho hs hset.pre.base.delta hordered
    hnonempty htransfer pt.s pt.P hpos hhor hhead hx
  have hcut : k ≤ timeIdx rho rho.horizon := inclusion_idxBefore_le_timeIdx rho hhor
  have hframeCut {j : Nat} (hj : j ≤ k) {y : V} (hy : y ∈ rho.honest) :=
    igate_frame_at_cut (hroots := hset.pre.base.idealization) (hstrat := hstrat) (hstore := hstore)
       E rho hsrc hrows d pt.P hcut hresults hj hy
  have hF : ∀ j, j ≤ k → ∀ y ∈ rho.honest, Block.Preceq (F_at p c E rho j y) pt.P :=
    fun j hj y hy => (hframeCut hj hy).1
  obtain ⟨hS, hsaved⟩ := igate_state_at_cut E rho hs hnonempty d pt.P hcut hresults hF k le_rfl x hx
  have hfj := hframeCut (Nat.le_refl k) hx
  have heq : storeAt p c E rho i x = storeAt p c E rho k x := by
    unfold storeAt
    rw [fgsa_preTick_eq_timeRead E rho hs hset.pre.base.noRestart ht,
      ← Gen.V2.Duty.stateBefore_idxBefore E rho d hs]
  have hfpre : Block.Preceq (eraseFG pre.fg.F) pt.P := by
    dsimp only [pre]
    rw [clockPre_fg, heq]
    exact hfj.1
  have hjpre : Block.Preceq (eraseFG pre.fg.J) pt.P := by
    dsimp only [pre]
    rw [clockPre_fg, heq]
    exact hfj.2
  have hsavepre : ∀ r C, GridCO.savedGenuine pre.base r = some (some C) → Block.Preceq C pt.P := by
    intro r C hC
    dsimp only [pre] at hC
    rw [savedGenuine_congr (clockPre_genuine p _ d) r, heq] at hC
    exact hsaved r C hC
  refine ⟨hfpre, hjpre, ?_, ?_, hsavepre, ?_⟩
  · rw [S_at_def]
    rw [heq]
    exact hS
  · intro row hr
    have hm := (clockPre_obligations_sublist p (storeAt p c E rho i x) d).subset hr
    rw [heq] at hm
    exact igate_below_at_cut E rho d pt.P hresults le_rfl (hleases k x hcut hx row hm)
  · intro r X hX
    have hinv : CStoreInv p pre := cstoreInv_clockPre p _ (cstoreInv_stateBefore E rho i x) d
    cases hf : pre.fastWrite.find? (fun row => row.1 == r) with
    | none =>
      change X ∈ ((pre.fastWrite.find? _).map Prod.snd).getD [] at hX
      simp only [hf, Option.map_none, Option.getD_none, List.not_mem_nil] at hX
    | some row =>
      have hm := List.mem_of_find?_eq_some hf
      change X ∈ ((pre.fastWrite.find? _).map Prod.snd).getD [] at hX
      simp only [hf, Option.map_some, Option.getD_some] at hX
      rcases hinv.fastOrigin row hm X hX with ⟨C, hC, hXC⟩ | hXF
      · exact block_preceq_trans hXC (hsavepre row.1 C hC)
      · exact block_preceq_trans hXF hfpre

end AvailableChain.FGSA.Run
end
