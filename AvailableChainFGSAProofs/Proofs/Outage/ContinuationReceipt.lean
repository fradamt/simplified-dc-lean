module
public import AvailableChainFGSARun.Proofs.ReceiptCoverage
public import AvailableChainFGSAProofs.Proofs.Outage.ContinuationFrame
public import AvailableChainFGSAProofs.Proofs.Outage.ContinuationTiming
public import AvailableChainFGSAProofs.Proofs.Outage.ArmingDuty
public import AvailableChainFGSAProofs.Proofs.Outage.PersistenceDefs

public section

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG AvailableChain.KitFG Gen.Pure

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}
    {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}

/-- OUTPUT-DIRECT §§3,6. DC: INTENTIONAL; each ancestor of a held block
has its own earlier acceptance trigger. The source cutoff is inclusive. -/
theorem outageV_source_path (hsch : V2.D.ScheduleWellFormed E rho)
    {k : Nat} {y : V} {K : Block} {u : Time}
    (hK : K ∈ (storeAt p c E rho k y).base.blocks)
    (hcut : ∀ l < k, ∀ e, rho.events[l]? = some e → e.time ≤ u) :
    ∀ b, Block.Preceq b K → b ≠ .genesis →
      ∃ l < k, ∃ t o, blockOf? p o = some b ∧
        V2.D.Run.acceptsAt E rho l y o t ∧ 0 ≤ t ∧ t ≤ u := by
  intro b hb hne
  have hc := (storeBundle_stateBefore E rho k y).cstore
  obtain ⟨Kfg, hKfg, he⟩ := (hc.baseTree K).mp hK
  rw [← he] at hb
  obtain ⟨Bfg, hBfg, heB⟩ := eraseFG_ancestor_mem hc.fg.closed hKfg hb
  have hbm := (hc.baseTree b).mpr ⟨Bfg, hBfg, heB⟩
  rw [← (storeBundle_stateBefore E rho k y).«meta».stampKeys] at hbm
  obtain ⟨⟨b', stamp⟩, hstamp, he'⟩ := List.mem_map.mp hbm
  dsimp only at he'
  subst b'
  rcases fgsa_block_stamp_source E rho k y b stamp hstamp with hg | ⟨l, hl, t, o, ho, ha, _⟩
  · exact (hne hg.1).elim
  · obtain ⟨parent, hd, _⟩ := ha.1
    exact ⟨l, hl, t, o, ho, ha, (hsch.in_horizon _ (List.mem_of_getElem? hd)).1,
      hcut l hl _ hd⟩

/-- OUTPUT-DIRECT §§3,6. DC: INTENTIONAL; full-run relay gives path
coverage at any deadline after max(source cutoff,GST)+delta. This generalizes
the private gate_path_coverage construction in WeakContinuation/StepGateBatch.
It includes acceptances before GST and uses compatibility with F. -/
theorem outageV_path_coverage (hE : V2.D.ExecutionValid E rho) (hDelta : E.Δ = p.Δ)
    {ΔF : Time} (hsync : Gen.V2.Duty.PartialSynchronyBy E rho (fgsaDelay E.Δ ΔF))
    {k : Nat} {x y : V} {K : Block} {u D : Time}
    (hy : y ∈ rho.honest) (hK : K ∈ (storeAt p c E rho k y).base.blocks)
    (hcut : ∀ l < k, ∀ e, rho.events[l]? = some e → e.time ≤ u)
    (hdeadline : max u E.t_GST + p.Δ ≤ D) (hhor : D ≤ rho.horizon)
    (hF : ∀ j, j ≤ V2.D.Run.idxBefore rho D → Block.Compatible K (F_at p c E rho j x)) :
    ∃ required paths,
      ReceiptCoveragePremises E rho (fun t => max t E.t_GST + p.Δ) rho.horizon
        D 0 x K required paths ∧ paths K D := by
  let required := fun o t => ∃ l < k, V2.D.Run.acceptsAt E rho l y o t ∧
    ∃ b, blockOf? p o = some b ∧ Block.Preceq b K
  let paths := fun B d => B = K ∧ d = D
  have htime : ∀ o t, required o t → 0 ≤ t ∧ t ≤ u := by
    rintro o t ⟨l, hl, ha, _⟩
    obtain ⟨parent, hd, _⟩ := ha.1
    exact ⟨(hE.toScheduleWellFormed.in_horizon _ (List.mem_of_getElem? hd)).1, hcut l hl _ hd⟩
  have hbound : ∀ t, t ≤ u → max t E.t_GST + p.Δ ≤ D := by
    intro t ht
    exact (add_le_add (max_le_max ht le_rfl) le_rfl).trans hdeadline
  refine ⟨required, paths, ?_, rfl, rfl⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [hDelta] using Gen.V2.Duty.deliveryWithinOn_of_partialSynchronyBy E rho hsync
      (fun o => ¬ isRowObject o) E.Δ (fgsaDelay_nonrow E.Δ _)
  · intro o t hr
    obtain ⟨l, _, ha, b, hb, _⟩ := hr
    obtain ⟨parent, he, hh⟩ := ha.1
    refine ⟨Or.inr ⟨y, hy, l, ha⟩,
      handles_wellFormed p c _ parent o hh (hE.wire l y parent t he), ?_⟩
    intro r a B hv
    have hn : blockOf? p o = none := by
      change (match (toWire p o).decode with | some (.block _ N) => some N.erase | _ => none) = _
      rw [hv]
    rw [hn] at hb
    contradiction
  · intro j _ hj
    exact hF j hj
  · refine ⟨fun _ _ hab => add_le_add (max_le_max hab le_rfl) le_rfl,
      hhor, le_rfl, Nat.zero_le _, ?_, ?_, ?_⟩
    · intro o t hr
      exact ⟨Nat.zero_le _, (htime o t hr).1,
        (le_max_left _ _).trans_lt (lt_add_of_pos_right _ p.deltaPos),
        hbound t (htime o t hr).2⟩
    · rintro B d ⟨hBK, hdD⟩
      subst B
      subst d
      refine ⟨block_preceq_refl K, le_rfl, ?_⟩
      intro b hb hne
      obtain ⟨l, hl, t, o, ho, ha, _, ht⟩ :=
        outageV_source_path hE.toScheduleWellFormed hK hcut b hb hne
      have hdecode : ∃ r N, N.erase = b ∧ (toWire p o).decode = some (.block r N) := by
        change (match (toWire p o).decode with
          | some (.block _ N) => some N.erase | _ => none) = _ at ho
        cases he : (toWire p o).decode with
        | none => rw [he] at ho; contradiction
        | some m =>
          cases m <;> simp only [he, reduceCtorEq, Option.some.injEq] at ho
          exact ⟨_, _, ho, rfl⟩
      obtain ⟨r, N, heN, hdec⟩ := hdecode
      exact ⟨o, t, r, N, heN, ⟨l, hl, ha, b, ho, hb⟩, hdec, hbound t ht⟩
    · intro o t r N hr hdec
      obtain ⟨l, hl, ha, b', hb', hBK⟩ := hr
      have hb : blockOf? p o = some N.erase := by
        change (match (toWire p o).decode with | some (.block _ N) => some N.erase | _ => none) = _
        rw [hdec]
      have heq := Option.some.inj (hb'.symm.trans hb)
      subst b'
      exact ⟨K, D, ⟨rfl, rfl⟩, hBK⟩

/-- OUTPUT-DIRECT §7. DC: INTENTIONAL; a received compatible HEAD path
is active even when its target is a strict ancestor of the receiver's F. -/
theorem outageV_active_path_of_coverage (hE : V2.D.ExecutionValid E rho)
    (hN : V2.D.NoRestart rho) (hDelta : E.Δ = p.Δ)
    (dl : Time → Time) (cut D : Time) (first : Nat) (x : V) (K : Block)
    (required : Obj p → Time → Prop) (paths : Block → Time → Prop)
    (hx : x ∈ rho.honest)
    (hcov : ReceiptCoveragePremises E rho dl cut D first x K required paths)
    (hpath : paths K D)
    (hKF : Block.Compatible K (eraseFG (V2.D.Run.stateBeforeTime E rho D x).st.fg.F))
    (hroots : NamedRootCollisionFree p c E rho) :
    ∀ X, Block.Preceq X K → X ∈ (actView (V2.D.Run.stateBeforeTime E rho D x).st).blocks := by
  let st := (V2.D.Run.stateBeforeTime E rho D x).st
  have hc := (fgsa_receiptCoverage E rho dl cut D first x K required paths
    hroots hDelta hE hN hx hcov).1
  have hb := (storeBundle_stateBeforeTime E rho D x).cstore
  have hK : K ∈ (actView st).blocks := by
    rcases hc with ⟨hbelow, _⟩ | ⟨_, _, hpaths⟩
    · exact actView_ancestor_closed p st hb ((actView_genesis_F p st hb).2) hbelow
    · obtain ⟨Y, hY, hYK⟩ := hpaths K D hpath K (block_preceq_refl K)
      exact (actView_blocks st K).mpr ⟨(hb.baseTree K).mpr ⟨Y, hY, hYK⟩, hKF⟩
  intro X hX
  exact actView_ancestor_closed p st hb hK hX

/-- OUTPUT-DIRECT §6. DC: INTENTIONAL; relay keeps the exact FG carrier,
not only its erased path. The alternative is finality above B. Monotonic F
reduces every earlier exclusion check to compatibility at the receipt cut. -/
theorem outageV_exact_carrier_receipt (hE : V2.D.ExecutionValid E rho)
    (hN : V2.D.NoRestart rho) (hDelta : E.Δ = p.Δ)
    {ΔF : Time} (hsync : Gen.V2.Duty.PartialSynchronyBy E rho (fgsaDelay E.Δ ΔF))
    (hroots : NamedRootCollisionFree p c E rho)
    {k : Nat} {x y : V} {B P : FGBlock (Fin p.n)} {u D : Time}
    (hx : x ∈ rho.honest) (hy : y ∈ rho.honest)
    (hP : P ∈ (storeAt p c E rho k y).fg.TF)
    (hBP : FGBlock.Preceq B P)
    (hBJ : FGBlock.Preceq B (heightView p P).J)
    (hcut : ∀ l < k, ∀ e, rho.events[l]? = some e → e.time ≤ u)
    (hdeadline : max u E.t_GST + p.Δ ≤ D) (hhor : D ≤ rho.horizon)
    (hF : Block.Compatible (eraseFG B) (F_at p c E rho (V2.D.Run.idxBefore rho D) x)) :
    let dst := (V2.D.Run.stateBeforeTime E rho D x).st
    Block.Preceq (eraseFG B) (eraseFG dst.fg.F) ∨
      P ∈ dst.fg.TF ∧ (heightView p P).h_j ≤ dst.fg.h_j := by
  intro dst
  have hread : F_at p c E rho (V2.D.Run.idxBefore rho D) x = eraseFG dst.fg.F := by
    change eraseFG (V2.D.Run.stateBefore E rho (V2.D.Run.idxBefore rho D) x).st.fg.F = _
    rw [Gen.V2.Duty.stateBefore_idxBefore E rho D hE.toScheduleWellFormed]
  rw [hread] at hF
  by_cases hBF : Block.Preceq (eraseFG B) (eraseFG dst.fg.F)
  · exact Or.inl hBF
  have hFB : Block.Preceq (eraseFG dst.fg.F) (eraseFG B) := by
    rcases Bool.or_eq_true_iff.mp hF with h | h
    · exact (hBF h).elim
    · exact h
  have hhistory : ∀ j, j ≤ V2.D.Run.idxBefore rho D →
      Block.Compatible (eraseFG P) (F_at p c E rho j x) := by
    intro j hj
    have hm := arming_F_mono (E := E) hN hj x
    rw [hread] at hm
    exact Bool.or_eq_true_iff.mpr (Or.inr (block_preceq_trans
      hm (block_preceq_trans hFB (eraseFG_preceq hBP))))
  have hPb := ((storeBundle_stateBefore E rho k y).cstore.baseTree _).mpr ⟨P, hP, rfl⟩
  obtain ⟨required, paths, hcov, hpath⟩ := outageV_path_coverage hE hDelta hsync
    hy hPb hcut hdeadline hhor hhistory
  have hc := (fgsa_receiptCoverage E rho (fun t => max t E.t_GST + p.Δ)
    rho.horizon D 0 x (eraseFG P) required paths hroots hDelta hE hN hx hcov).1
  have hmem : P ∈ dst.fg.TF := by
    rcases hc with ⟨hPF, _⟩ | ⟨_, _, hp⟩
    · exact (hBF (block_preceq_trans (eraseFG_preceq hBP) hPF)).elim
    · obtain ⟨Y, hY, heY⟩ := hp _ D hpath _ (block_preceq_refl _)
      exact eraseFG_injective heY ▸ hY
  exact Or.inr ⟨hmem, outageV_received_height p dst
    (storeBundle_stateBeforeTime E rho D x).cstore hmem
    (eraseFG_preceq_iff.mp (block_preceq_trans hFB (eraseFG_preceq hBJ)))⟩

/-- OUTPUT-DIRECT §6. DC: INTENTIONAL; instantiate exact-carrier relay
at an actual first-regression HEAD cut. The F fact is required only at the
old-label gate deadline, before a gate can consume the regressed batch. -/
theorem outageV_regression_receipt (hE : V2.D.ExecutionValid E rho)
    (hN : V2.D.NoRestart rho) (hDelta : E.Δ = p.Δ)
    {ΔF : Time} (hsync : Gen.V2.Duty.PartialSynchronyBy E rho (fgsaDelay E.Δ ΔF))
    (hroots : NamedRootCollisionFree p c E rho)
    {k : Nat} {x y : V} {B P : FGBlock (Fin p.n)} {s : Slot}
    (hk : rho.events[k]? = some (.tick y (SA.voteTime p.toParams s)))
    (hx : x ∈ rho.honest) (hy : y ∈ rho.honest)
    (hP : P ∈ (storeAt p c E rho k y).fg.TF)
    (hBP : FGBlock.Preceq B P) (hBJ : FGBlock.Preceq B (heightView p P).J)
    (hgst : E.t_GST ≤ SA.voteTime p.toParams s)
    (hhor : SA.voteTime p.toParams s + p.Δ ≤ rho.horizon)
    (hF : Block.Compatible (eraseFG B)
      (F_at p c E rho (V2.D.Run.idxBefore rho (SA.voteTime p.toParams s + p.Δ)) x)) :
    let dst := (V2.D.Run.stateBeforeTime E rho (SA.voteTime p.toParams s + p.Δ) x).st
    Block.Preceq (eraseFG B) (eraseFG dst.fg.F) ∨
      P ∈ dst.fg.TF ∧ (heightView p P).h_j ≤ dst.fg.h_j := by
  apply outageV_exact_carrier_receipt hE hN hDelta hsync hroots hx hy hP hBP hBJ
    (u := SA.voteTime p.toParams s) ?_ ?_ hhor hF
  · intro l hl e he
    by_contra hn
    have := V2.D.Engine.eventIndex_lt_of_time_lt hE.toScheduleWellFormed hk he
      (lt_of_not_ge hn)
    omega
  · exact (outageV_regression_relay_bound p s _ _ le_rfl hgst).1

/-- OUTPUT-DIRECT §6. DC: INTENTIONAL; a horizon before the relay deadline
also excludes the next HEAD and the gate that consumes regressed HEADs. -/
theorem outageV_short_horizon (p : Params) (s : Slot) (horizon : Time)
    (h : horizon < SA.voteTime p.toParams s + p.Δ) :
    horizon < SA.voteTime p.toParams (s + 1) ∧ horizon < SA.gateTime p.toParams s := by
  rw [arming_vote_eq] at h
  rw [arming_vote_eq, arming_gate_eq]
  push_cast
  have := p.deltaPos
  constructor <;> nlinarith
/-- OUTPUT-DIRECT §6. DC: INTENTIONAL; every gate through the relay
cut uses an earlier label. No regressed HEAD can justify its own receipt. -/
theorem outageV_gate_through_relay (p : Params) (s q : Slot)
    (h : SA.gateTime p.toParams q ≤ SA.voteTime p.toParams s + p.Δ) : q < s := by
  rw [arming_gate_eq, arming_vote_eq] at h
  by_contra hn
  have hsq : (s : Int) ≤ (q : Int) := by exact_mod_cast (Nat.le_of_not_gt hn)
  have := p.deltaPos
  nlinarith

/-- OUTPUT-DIRECT §3. DC: INTENTIONAL; any source gate no later than
this HEAD lies at or before the previous label's early boundary. The
endpoint is inclusive, as required for the old-source relay witness. -/
theorem outageV_source_gate_cutoff (p : Params) (s q : Slot)
    (h : SA.gateTime p.toParams q ≤ SA.voteTime p.toParams (s + 1)) :
    SA.gateTime p.toParams q ≤ SA.earlyTime p.toParams s := by
  rw [arming_gate_eq, arming_vote_eq] at h
  rw [arming_gate_eq, arming_early_eq]
  push_cast at h
  have hd := p.deltaPos
  have hqs : q < s := by
    by_contra hn
    have hsq : (s : Int) ≤ (q : Int) := by exact_mod_cast (Nat.le_of_not_gt hn)
    nlinarith
  have hcast : (q : Int) + 1 ≤ (s : Int) := by exact_mod_cast (Nat.succ_le_of_lt hqs)
  nlinarith


/-- OUTPUT-DIRECT §§3,7. DC: INTENTIONAL; a block held before a positive
tick has a strict earlier stamp, including an old acceptance. -/
theorem outageV_block_stamp_lt (hsch : V2.D.ScheduleWellFormed E rho)
    (hn : V2.D.NoRestart rho) {j : Nat} {x : V} {t : Time}
    (hj : rho.events[j]? = some (.tick x t)) (ht : 0 < t)
    (B : Block) (hB : B ∈ (storeAt p c E rho j x).base.blocks) :
    GridCO.stampBlock (storeAt p c E rho j x).base B < t := by
  have hbm : B ∈ (V2.D.Run.stateBefore E rho j x).st.base.blockStamp.map Prod.fst := by
    rw [(storeBundle_stateBefore E rho j x).«meta».stampKeys]
    exact hB
  change (((V2.D.Run.stateBefore E rho j x).st.base.blockStamp.find? _).map Prod.snd).getD _ < t
  cases he : (V2.D.Run.stateBefore E rho j x).st.base.blockStamp.find? (fun row => row.1 == B) with
  | none =>
    obtain ⟨row, hr, hb⟩ := List.mem_map.mp hbm
    have hno := List.find?_eq_none.mp he row hr
    rw [hb, beq_self_eq_true] at hno
    contradiction
  | some row =>
    change row.2 < t
    have hmem := List.mem_of_find?_eq_some he
    rcases fgsa_block_stamp_source E rho j x row.1 row.2 hmem with hg | ⟨l, hl, _, _, _, _, hs⟩
    · rw [hg.2]
      exact ht
    · rw [hs]
      have hm := V2.D.Engine.stateBefore_now_mono_noRestart (fgsaClock p c) E rho hsch hn
        (Nat.le_of_lt hl) x
      rw [fgsa_clock_now p c (V2.D.Run.stateBefore E rho l x),
        fgsa_clock_now p c (V2.D.Run.stateBefore E rho j x)] at hm
      exact hm.trans_lt (fgsa_preTick_now_lt E rho hsch hj ht)

/-- OUTPUT-DIRECT §3. DC: INTENTIONAL; a carrier held before the freeze
remains in the actual later frozen voter set, with its original stamp. -/
theorem outageV_frozen_of_receipt (hsch : V2.D.ScheduleWellFormed E rho)
    (hn : V2.D.NoRestart rho) (hcumul : RStoreCumul p c E rho)
    {j i : Nat} {x : V} {t : Time} {s : Slot} {P : FGBlock (Fin p.n)}
    (hx : x ∈ rho.honest) (hj : rho.events[j]? = some (.tick x t))
    (ht : 0 < t) (hfreeze : t ≤ SA.freezeTime p.toParams (s - 1))
    (hji : j ≤ i) (hi : i ≤ rho.events.length)
    (hP : P ∈ (storeAt p c E rho j x).fg.TF) :
    P ∈ voterBlocks p (clock p (storeAt p c E rho i x) (SA.voteTime p.toParams s)) s := by
  let src := storeAt p c E rho j x
  let dst := clock p (storeAt p c E rho i x) (SA.voteTime p.toParams s)
  have hc := hcumul hn j i x hx hji hi
  have hPb : eraseFG P ∈ src.base.blocks :=
    ((storeBundle_stateBefore E rho j x).cstore.baseTree _).mpr ⟨P, hP, rfl⟩
  have hkey : eraseFG P ∈ src.base.blockStamp.map Prod.fst := by
    change eraseFG P ∈ (V2.D.Run.stateBefore E rho j x).st.base.blockStamp.map Prod.fst
    rw [(storeBundle_stateBefore E rho j x).«meta».stampKeys]
    exact hPb
  have hkey' : eraseFG P ∈ (storeAt p c E rho i x).base.blockStamp.map Prod.fst := by
    obtain ⟨row, hr, he⟩ := List.mem_map.mp hkey
    exact List.mem_map.mpr ⟨row, hc.2.2.1.subset hr, he⟩
  have hstamp : GridCO.stampBlock dst.base (eraseFG P) =
      GridCO.stampBlock src.base (eraseFG P) := by
    have hcstamp := inclusion_stampBlock_of_prefix (K := eraseFG P)
      (show (storeAt p c E rho i x).base.blockStamp <+: dst.base.blockStamp by
        rw [(clock_cumulative p _ _).2.2.1]) hkey'
    exact hcstamp.trans (inclusion_stampBlock_of_prefix hc.2.2.1 hkey)
  have hm : P ∈ dst.fg.TF := by
    change P ∈ (clock p (storeAt p c E rho i x) _).fg.TF
    rw [clock_fg]
    exact hc.1 hP
  apply Finset.mem_filter.mpr
  refine ⟨hm, Bool.or_eq_true_iff.mpr (Or.inl (decide_eq_true ?_))⟩
  rw [hstamp]
  exact (outageV_block_stamp_lt hsch hn hj ht _ hPb).trans_le hfreeze


/-- OUTPUT-DIRECT §3. DC: INTENTIONAL; clock processing admits no FG
blocks. Thus the actual action source was held before its emission tick. -/
theorem outageV_source_held (hsch : V2.D.ScheduleWellFormed E rho)
    {k : Nat} {y : V} {r : Nat} {C : FGBlock (Fin p.n)}
    (hk : rho.events[k]? = some (.tick y (p.actionTime r)))
    (hC : actionSourceFG p c E rho y r = some (some C)) :
    C ∈ (storeAt p c E rho k y).fg.TF := by
  rw [actionSourceFG_def, postClock_def, preTick_def] at hC
  cases hl : V2.D.Run.tickIdx? rho y (p.actionTime r) with
  | none => simp only [hl, Option.map_none] at hC; contradiction
  | some l =>
    have he := fgsa_tick_unique E rho hsch (V2.D.Run.tickIdx?_spec hl) hk
    subst l
    simp only [hl, Option.map_some, Option.some.injEq] at hC
    have hm := (Finset.mem_filter.mp (pickPair_some_spec _ _ hC).1).1
    have ht := (KitFG.mem_filteredFromView _ _ _ _).mp hm |>.1
    change C ∈ (clock p (storeAt p c E rho k y) (p.actionTime r)).fg.TF at ht
    rw [clock_fg] at ht
    exact ht

/-- OUTPUT-DIRECT §3. DC: INTENTIONAL; crossing a held carrier gives an
original honest source of the exact crossed height. Its action precedes the
inclusive previous early boundary, and its full body was held at that action. -/
theorem outageV_crossing_source (hsch : V2.D.ScheduleWellFormed E rho)
    (origin : RQCOrigin p c E rho) {i : Nat} {x : V} {s m : Nat}
    {W B : FGBlock (Fin p.n)} (hx : x ∈ rho.honest)
    (hi : rho.events[i]? = some (.tick x (SA.voteTime p.toParams (s + 1))))
    (hW : W ∈ (storeAt p c E rho i x).fg.TF)
    (hm : 1 ≤ m) (hmW : m < (heightView p W).h)
    (hist : OutageSourceHistory p c E rho (eraseFG B) i) :
    ∃ k, k < i ∧ ∃ y r, ∃ (wire : RowWire p.n) (C : FGBlock (Fin p.n)),
      HonestRowAt p c E rho k y r wire ∧
      actionSourceFG p c E rho y r = some (some C) ∧
      (heightView p C).h = m ∧ Block.Compatible (eraseFG C) (eraseFG B) ∧
      C ∈ (storeAt p c E rho k y).fg.TF ∧
      p.actionTime r ≤ SA.earlyTime p.toParams s := by
  classical
  obtain ⟨Y, hYW, hYm, Q, hQ, hrows⟩ :=
    (fgCertificateLaws p).height.height_crossing W m hm hmW
  let rows : Fin p.n → FGBlock (Fin p.n) × Row (Fin p.n) := fun k =>
    if hk : k ∈ Q then
      (Classical.choose (hrows k hk), Classical.choose (Classical.choose_spec (hrows k hk)))
    else (.genesis, ⟨k, .empty, none⟩)
  have hr : ∀ k ∈ Q, FGBlock.Preceq (rows k).1 W ∧
      (rows k).2 ∈ (rows k).1.rows ∧ (rows k).2.signer = k ∧
      (rows k).2.height_pair.matchesEntry m Y.root = true := fun k hk => by
    simpa only [rows, hk, ↓reduceDIte] using
      Classical.choose_spec (Classical.choose_spec (hrows k hk))
  obtain ⟨q, hq, y, r, wire, ⟨k, hk, hrow⟩, _, _, C, G, hC, hn, _⟩ :=
    (origin i x W hx hW).1 m Y Q rows hm hmW hYW hYm hQ hr
  have hheight : (heightView p C).h = m := by
    have hmatch := (hr q hq).2.2.2
    cases hp : (rows q).2.height_pair with
    | empty => rw [hp] at hmatch; contradiction
    | vote h e tm =>
      rw [hp] at hmatch hn
      have he : h = m ∧ e = Y.root := of_decide_eq_true hmatch
      exact (Prod.mk.inj (Option.some.inj hn)).1.symm.trans he.1
  have hsource : actionSource p c E rho y r = some (some (eraseFG C)) := by
    change (actionSourceFG p c E rho y r).map (Option.map eraseFG) = _
    rw [hC]
    rfl
  have htime : p.actionTime r ≤ SA.voteTime p.toParams (s + 1) := by
    by_contra hn
    have := V2.D.Engine.eventIndex_lt_of_time_lt hsch hi hrow.2.1 (lt_of_not_ge hn)
    omega
  refine ⟨k, hk, y, r, wire, C, hrow, hC, hheight,
    hist.history k y r _ hk hrow.1 hrow.2.1 hsource,
    outageV_source_held hsch hrow.2.1 hC, ?_⟩
  rw [fgsa_action_gate_time] at htime ⊢
  exact outageV_source_gate_cutoff p s (r * p.R) htime

/-- OUTPUT-DIRECT §7. DC: INTENTIONAL; full-run relay supplies the actual
compatible honest HEAD batch and its strict stamps. Targets may lie below F.
The explicit F history will be supplied by the joint event invariant. -/
theorem outageV_compatible_head_receipts
    {ΔF : Time} (hvalid : V2.D.ExecutionValid E rho) (hnr : V2.D.NoRestart rho) (hdelta : E.Δ = p.Δ)
    (hcstar : V2.D.CStar (fgsaFamilies p c).fresh rho)
    (hroots : NamedRootCollisionFree p c E rho)
    (hsync : Gen.V2.Duty.PartialSynchronyBy E rho (fgsaDelay E.Δ ΔF))
    {i : Nat} {x : V} {s : Slot}
    (ht : IsGateTick p c rho i x s) (hGST : E.t_GST ≤ SA.voteTime p.toParams s)
    (hfinal : ∀ k y, rho.events[k]? = some (.tick y (SA.voteTime p.toParams s)) →
      ∀ j, j ≤ i → Block.Compatible
        (headVote p (clock p (storeAt p c E rho k y) (SA.voteTime p.toParams s)) s)
        (F_at p c E rho j x))
    (B : Block)
    (hB : ∀ k y, rho.events[k]? = some (.tick y (SA.voteTime p.toParams s)) →
      Block.Compatible
        (headVote p (clock p (storeAt p c E rho k y) (SA.voteTime p.toParams s)) s) B) :
    ∀ q : Fin p.n, rho.seatOf (.base (.head s)) q ∈ rho.honest →
      E.awake (rho.seatOf (.base (.head s)) q) (SA.voteTime p.toParams s) = true →
      ∃ K t,
        rho.seatOf (.base (.head s)) q ∈ rho.honest ∧
        V2.D.Run.emits E rho (rho.seatOf (.base (.head s)) q)
          (ofHead p ⟨.seat (.head s) q, K.root⟩) t ∧
        baseVote (⟨.seat (.head s) q, K.root⟩ : HeadWire p.n) ∈
          (storeAt p c E rho i x).base.votes ∧
        K ∈ (actView (clockPre p (storeAt p c E rho i x)
          (SA.gateTime p.toParams s))).blocks ∧
        K.slot ≤ s ∧
        GridCO.stampVote (actView (clockPre p (storeAt p c E rho i x)
          (SA.gateTime p.toParams s)))
          (baseVote (⟨.seat (.head s) q, K.root⟩ : HeadWire p.n)) <
            GridCO.earlyTime p.toParams.engine s ∧
        GridCO.stampBlock (actView (clockPre p (storeAt p c E rho i x)
          (SA.gateTime p.toParams s))) K < GridCO.earlyTime p.toParams.engine s ∧
        Block.Compatible K B := by
  intro q hy hawake
  let y := rho.seatOf (.base (.head s)) q
  have hsch := hvalid.toScheduleWellFormed
  have hd : (0 : Int) < p.Δ := p.deltaPos
  have hx : x ∈ rho.honest := hsch.honest_only _ (List.mem_of_getElem? ht)
  have hcut : SA.gateTime p.toParams s ≤ rho.horizon :=
    (hvalid.in_horizon _ (List.mem_of_getElem? ht)).2
  have htimes : max (SA.voteTime p.toParams s) E.t_GST + p.Δ =
      SA.earlyTime p.toParams s := by
    rw [max_eq_left hGST]
    change 4 * p.Δ * ((s : Nat) : Int) + p.Δ + p.Δ =
      4 * p.Δ * ((s : Nat) : Int) + 2 * p.Δ
    ring
  have hearly : SA.earlyTime p.toParams s < SA.gateTime p.toParams s := by
    change 4 * p.Δ * ((s : Nat) : Int) + 2 * p.Δ <
      4 * p.Δ * ((s : Nat) : Int) + 6 * p.Δ
    linarith
  have hvote : SA.voteTime p.toParams s < SA.earlyTime p.toParams s := by
    rw [← htimes]
    exact (le_max_left _ _).trans_lt (lt_add_of_pos_right _ hd)
  have hvt : ((4 * s + 1 : Nat) : Time) * p.Δ = SA.voteTime p.toParams s := by
    change ((4 * s + 1 : Nat) : Int) * p.Δ = 4 * p.Δ * ((s : Nat) : Int) + p.Δ
    push_cast
    ring
  have het : ((4 * s + 2 : Nat) : Time) * p.Δ = SA.earlyTime p.toParams s := by
    change ((4 * s + 2 : Nat) : Int) * p.Δ = 4 * p.Δ * ((s : Nat) : Int) + 2 * p.Δ
    push_cast
    ring
  obtain ⟨k, hk, _⟩ := fgsa_tick_total E rho hsch hdelta y hy (4 * s + 1)
    (hvt ▸ (hvote.le.trans (hearly.le.trans hcut)))
  rw [hvt] at hk
  obtain ⟨j, hj, _⟩ := fgsa_tick_total E rho hsch hdelta x hx (4 * s + 2)
    (het ▸ (hearly.le.trans hcut))
  rw [het] at hj
  have hji := V2.D.Engine.eventIndex_lt_of_time_lt hsch hj ht hearly
  have hjread := fgsa_preTick_eq_timeRead E rho hsch hnr hj
  let K := headVote p (clock p (storeAt p c E rho k y) (SA.voteTime p.toParams s)) s
  have hKeq : K = headVote p ((fgsa p c).clock (V2.D.Run.stateBefore E rho k y)
      (SA.voteTime p.toParams s)).st s := rfl
  have hKsource : K ∈ (storeAt p c E rho k y).base.blocks := by
    have hm := headVote_stored p _ (storeBundle_postClock E rho k y
      (SA.voteTime p.toParams s)).cstore s
    rw [← hKeq] at hm
    change K ∈ (clock p (storeAt p c E rho k y) _).base.blocks at hm
    rwa [(clock_cumulative p _ _).2.1] at hm
  have hem : V2.D.Run.emits E rho y (ofHead p ⟨.seat (.head s) q, K.root⟩)
      (SA.voteTime p.toParams s) := by
    refine ⟨k, hk, ?_⟩
    rw [(V2.D.Run.step_tick_eq E rho hk).2]
    exact (fgsa_emits_head E rho _ y _ s q K.root).mpr ⟨hawake, rfl, rfl, congrArg
        Block.root hKeq⟩
  have hprefix := hfinal k y hk
  have hidx : V2.D.Run.idxBefore rho (SA.earlyTime p.toParams s) ≤ i := by
    by_contra hn
    exact (not_lt.mpr hearly.le)
      ((Gen.V2.Duty.index_lt_idxBefore_iff hsch ht _).mp (Nat.lt_of_not_ge hn))
  obtain ⟨required, paths, hcov, hp⟩ := outageV_path_coverage hvalid hdelta hsync
    (u := SA.voteTime p.toParams s) hy hKsource (by
      intro l hl e he
      by_contra hn
      have := V2.D.Engine.eventIndex_lt_of_time_lt hsch hk he (lt_of_not_ge hn)
      omega) htimes.le (hearly.le.trans hcut) (fun j hj => hprefix j (hj.trans hidx))
  have hFearly : Block.Compatible K (eraseFG (V2.D.Run.stateBeforeTime E rho
      (SA.earlyTime p.toParams s) x).st.fg.F) := by
    rw [← Gen.V2.Duty.stateBefore_idxBefore E rho _ hsch]
    exact hprefix _ hidx
  have hpath := outageV_active_path_of_coverage (hroots := hroots)
    hvalid hnr hdelta
    (fun t => max t E.t_GST + p.Δ) rho.horizon (SA.earlyTime p.toParams s) 0 x K
    required paths hx hcov hp hFearly
  have hKearly : K ∈ (storeAt p c E rho j x).base.blocks := by
    have hm := (actView_blocks _ K).mp (hpath K (block_preceq_refl K))
    rw [← hjread] at hm
    exact hm.1
  have hwindow : (V2.D.Run.stateBeforeTime E rho (SA.earlyTime p.toParams s) x).st.slot p ≤
      s + 1 := by
    rw [← hjread]
    have hn := V2.D.Engine.stateBefore_now_le_event (fgsaClock p c) (fgsa_hrestore_now p c)
      E rho hsch hj x
    rw [fgsa_clock_now p c (V2.D.Run.stateBefore E rho j x)] at hn
    have he := slotOf_offset p s (2 * p.Δ) (by omega) (by omega)
    exact ((Internal.slotOf_mono (p := p) hn).trans_eq he).trans (Nat.le_succ _)
  have hr := fgsa_honest_head_receipt E rho hdelta hvalid hnr
    hcstar (fun t => max t E.t_GST + p.Δ) rho.horizon s q K.root (SA.voteTime p.toParams s) y x
    (by
      simpa only [hdelta] using
        Gen.V2.Duty.deliveryWithinOn_of_partialSynchronyBy E rho hsync
            (fun o => ¬ isRowObject o) E.Δ (fgsaDelay_nonrow E.Δ _))
    hy hem hx (by rw [htimes]; exact hearly.le.trans hcut)
    ((le_max_left _ _).trans_lt (lt_add_of_pos_right _ hd))
    (by rw [htimes]; exact hwindow)
  dsimp only at hr
  rw [htimes, ← hjread] at hr
  obtain ⟨hvoteI, hblockI, hvsI, hbsI⟩ :=
    inclusion_stamps_kept E rho hnr hji.le x _ K hr.1 hKearly
  let pre := clockPre p (storeAt p c E rho i x) (SA.gateTime p.toParams s)
  let v := actView pre
  have hvsKey : baseVote (⟨.seat (.head s) q, K.root⟩ : HeadWire p.n) ∈
      (storeAt p c E rho i x).base.voteStamp.map Prod.fst := by
    change _ ∈ (V2.D.Run.stateBefore E rho i x).st.base.voteStamp.map Prod.fst
    rw [fgsa_vote_stamp_keys E rho i x]
    exact hvoteI
  have hbsKey : K ∈ (storeAt p c E rho i x).base.blockStamp.map Prod.fst := by
    change K ∈ (V2.D.Run.stateBefore E rho i x).st.base.blockStamp.map Prod.fst
    rw [(storeBundle_stateBefore E rho i x).«meta».stampKeys]
    exact hblockI
  have hvs : GridCO.stampVote v (baseVote (⟨.seat (.head s) q, K.root⟩ : HeadWire p.n)) =
      GridCO.stampVote (storeAt p c E rho j x).base
        (baseVote (⟨.seat (.head s) q, K.root⟩ : HeadWire p.n)) := by
    apply Eq.trans (inclusion_stampVote_of_prefix (st' := v) ?_ hvsKey) hvsI
    change _ <+: (clockPre p _ _).base.voteStamp
    rw [(clockPre_stamps p _ _).2]
  have hbs : GridCO.stampBlock v K = GridCO.stampBlock (storeAt p c E rho j x).base K := by
    apply Eq.trans (inclusion_stampBlock_of_prefix (st' := v) ?_ hbsKey) hbsI
    change _ <+: (clockPre p _ _).base.blockStamp
    rw [(clockPre_stamps p _ _).1]
  have hKg : K ∈ v.blocks := by
    apply (actView_blocks _ K).mpr
    rw [(clockPre_fields p _ _).2.1, clockPre_fg]
    exact ⟨hblockI, hprefix i le_rfl⟩
  have hslot : K.slot ≤ s := by
    have hm := (fgsa_stateBefore_bounds E rho hsch k y).1 K hKsource
    have hn := V2.D.Engine.stateBefore_now_le_event (fgsaClock p c) (fgsa_hrestore_now p c)
      E rho hsch hk y
    rw [fgsa_clock_now p c (V2.D.Run.stateBefore E rho k y)] at hn
    exact hm.trans ((Internal.slotOf_mono (p := p) hn).trans_eq
      (slotOf_offset p s p.Δ hd.le (by omega)))
  have hpos : 0 < SA.earlyTime p.toParams s := by
    change 0 < 4 * p.Δ * ((s : Nat) : Int) + 2 * p.Δ
    positivity
  refine ⟨K, SA.voteTime p.toParams s, hy, hem, hvoteI, hKg, hslot, ?_, ?_, hB k y hk⟩
  · rw [hvs]
    exact hr.2
  · rw [hbs]
    exact outageV_block_stamp_lt hsch hnr hj hpos K hKearly

/-- OUTPUT-DIRECT §3. DC: INTENTIONAL; covering HEADs arrive before the
previous early boundary. Their paths are frozen at the next scheduled HEAD,
and their authentic votes remain in its actual merged support pool. -/
theorem outageV_covering_head_receipts
    {ΔF : Time} (hvalid : V2.D.ExecutionValid E rho) (hnr : V2.D.NoRestart rho)
    (hdelta : E.Δ = p.Δ) (hcstar : V2.D.CStar (fgsaFamilies p c).fresh rho)
    (hcumul : RStoreCumul p c E rho) (hroots : NamedRootCollisionFree p c E rho)
    (hsync : Gen.V2.Duty.PartialSynchronyBy E rho (fgsaDelay E.Δ ΔF))
    {i : Nat} {x : V} {s : Slot}
    (ht : rho.events[i]? = some (.tick x (SA.voteTime p.toParams (s + 1))))
    (hGST : E.t_GST ≤ SA.voteTime p.toParams s) (B : Block)
    (hF : Block.Preceq (F_at p c E rho i x) B)
    (hB : ∀ k y, y ∈ rho.honest →
      rho.events[k]? = some (.tick y (SA.voteTime p.toParams s)) →
      Block.Preceq B
        (headVote p (clock p (storeAt p c E rho k y) (SA.voteTime p.toParams s)) s)) :
    let dst := clock p (storeAt p c E rho i x) (SA.voteTime p.toParams (s + 1))
    ∀ q : Fin p.n, rho.seatOf (.base (.head s)) q ∈ rho.honest →
      E.awake (rho.seatOf (.base (.head s)) q) (SA.voteTime p.toParams s) = true →
      ∃ K t, V2.D.Run.emits E rho (rho.seatOf (.base (.head s)) q)
        (ofHead p ⟨.seat (.head s) q, K.root⟩) t ∧
      baseVote (⟨.seat (.head s) q, K.root⟩ : HeadWire p.n) ∈ headSupport p dst (s + 1) ∧
      K ∈ dst.base.blocks ∧ K.slot ≤ s ∧ Block.Preceq B K ∧
      ∀ X : FGBlock (Fin p.n), Block.Preceq (eraseFG X) K →
        X ∈ voterBlocks p dst (s + 1) := by
  intro dst q hy hawake
  let y := rho.seatOf (.base (.head s)) q
  have hsch := hvalid.toScheduleWellFormed
  have hd : (0 : Int) < p.Δ := p.deltaPos
  have hx : x ∈ rho.honest := hsch.honest_only _ (List.mem_of_getElem? ht)
  have hcut : SA.voteTime p.toParams (s + 1) ≤ rho.horizon :=
    (hvalid.in_horizon _ (List.mem_of_getElem? ht)).2
  have htimes : max (SA.voteTime p.toParams s) E.t_GST + p.Δ =
      SA.earlyTime p.toParams s := by
    rw [max_eq_left hGST]
    change 4 * p.Δ * ((s : Nat) : Int) + p.Δ + p.Δ =
      4 * p.Δ * ((s : Nat) : Int) + 2 * p.Δ
    ring
  have hearly : SA.earlyTime p.toParams s < SA.voteTime p.toParams (s + 1) := by
    rw [arming_early_eq, arming_vote_eq]
    push_cast
    nlinarith
  have hvote : SA.voteTime p.toParams s < SA.earlyTime p.toParams s := by
    rw [← htimes]
    exact (le_max_left _ _).trans_lt (lt_add_of_pos_right _ hd)
  have hvt : ((4 * s + 1 : Nat) : Time) * p.Δ = SA.voteTime p.toParams s := by
    change ((4 * s + 1 : Nat) : Int) * p.Δ = 4 * p.Δ * ((s : Nat) : Int) + p.Δ
    push_cast
    ring
  have het : ((4 * s + 2 : Nat) : Time) * p.Δ = SA.earlyTime p.toParams s := by
    change ((4 * s + 2 : Nat) : Int) * p.Δ = 4 * p.Δ * ((s : Nat) : Int) + 2 * p.Δ
    push_cast
    ring
  obtain ⟨k, hk, _⟩ := fgsa_tick_total E rho hsch hdelta y hy (4 * s + 1)
    (hvt ▸ (hvote.le.trans (hearly.le.trans hcut)))
  rw [hvt] at hk
  obtain ⟨j, hj, _⟩ := fgsa_tick_total E rho hsch hdelta x hx (4 * s + 2)
    (het ▸ (hearly.le.trans hcut))
  rw [het] at hj
  have hji := V2.D.Engine.eventIndex_lt_of_time_lt hsch hj ht hearly
  have hjread := fgsa_preTick_eq_timeRead E rho hsch hnr hj
  let K := headVote p (clock p (storeAt p c E rho k y) (SA.voteTime p.toParams s)) s
  have hKeq : K = headVote p ((fgsa p c).clock (V2.D.Run.stateBefore E rho k y)
      (SA.voteTime p.toParams s)).st s := rfl
  have hKsource : K ∈ (storeAt p c E rho k y).base.blocks := by
    have hm := headVote_stored p _ (storeBundle_postClock E rho k y
      (SA.voteTime p.toParams s)).cstore s
    rw [← hKeq] at hm
    change K ∈ (clock p (storeAt p c E rho k y) _).base.blocks at hm
    rwa [(clock_cumulative p _ _).2.1] at hm
  have hem : V2.D.Run.emits E rho y (ofHead p ⟨.seat (.head s) q, K.root⟩)
      (SA.voteTime p.toParams s) := by
    refine ⟨k, hk, ?_⟩
    rw [(V2.D.Run.step_tick_eq E rho hk).2]
    exact (fgsa_emits_head E rho _ y _ s q K.root).mpr ⟨hawake, rfl, rfl, congrArg
        Block.root hKeq⟩
  have hBK := hB k y hy hk
  have hprefix : ∀ j, j ≤ i → Block.Compatible K (F_at p c E rho j x) := by
    intro j hj
    exact Bool.or_eq_true_iff.mpr (Or.inr (block_preceq_trans
      (arming_F_mono (E := E) hnr hj x) (block_preceq_trans hF hBK)))
  have hidx : V2.D.Run.idxBefore rho (SA.earlyTime p.toParams s) ≤ i := by
    by_contra hn
    exact (not_lt.mpr hearly.le)
      ((Gen.V2.Duty.index_lt_idxBefore_iff hsch ht _).mp (Nat.lt_of_not_ge hn))
  obtain ⟨required, paths, hcov, hp⟩ := outageV_path_coverage hvalid hdelta hsync
    (u := SA.voteTime p.toParams s) hy hKsource (by
      intro l hl e he
      by_contra hn
      have := V2.D.Engine.eventIndex_lt_of_time_lt hsch hk he (lt_of_not_ge hn)
      omega) htimes.le (hearly.le.trans hcut) (fun j hj => hprefix j (hj.trans hidx))
  have hFearly : Block.Compatible K (eraseFG (V2.D.Run.stateBeforeTime E rho
      (SA.earlyTime p.toParams s) x).st.fg.F) := by
    rw [← Gen.V2.Duty.stateBefore_idxBefore E rho _ hsch]
    exact hprefix _ hidx
  have hpath := outageV_active_path_of_coverage (hroots := hroots)
    hvalid hnr hdelta
    (fun t => max t E.t_GST + p.Δ) rho.horizon (SA.earlyTime p.toParams s) 0 x K
    required paths hx hcov hp hFearly
  have hKearly : K ∈ (storeAt p c E rho j x).base.blocks := by
    have hm := (actView_blocks _ K).mp (hpath K (block_preceq_refl K))
    rw [← hjread] at hm
    exact hm.1
  have hwindow : (V2.D.Run.stateBeforeTime E rho (SA.earlyTime p.toParams s) x).st.slot p ≤
      s + 1 := by
    rw [← hjread]
    have hn := V2.D.Engine.stateBefore_now_le_event (fgsaClock p c) (fgsa_hrestore_now p c)
      E rho hsch hj x
    rw [fgsa_clock_now p c (V2.D.Run.stateBefore E rho j x)] at hn
    have he := slotOf_offset p s (2 * p.Δ) (by omega) (by omega)
    exact ((Internal.slotOf_mono (p := p) hn).trans_eq he).trans (Nat.le_succ _)
  have hr := fgsa_honest_head_receipt E rho hdelta hvalid hnr
    hcstar (fun t => max t E.t_GST + p.Δ) rho.horizon s q K.root (SA.voteTime p.toParams s) y x
    (by
      simpa only [hdelta] using
        Gen.V2.Duty.deliveryWithinOn_of_partialSynchronyBy E rho hsync
            (fun o => ¬ isRowObject o) E.Δ (fgsaDelay_nonrow E.Δ _))
    hy hem hx (by rw [htimes]; exact hearly.le.trans hcut)
    ((le_max_left _ _).trans_lt (lt_add_of_pos_right _ hd))
    (by rw [htimes]; exact hwindow)
  dsimp only at hr
  rw [htimes, ← hjread] at hr
  obtain ⟨hvoteI, hblockI, hvsI, hbsI⟩ :=
    inclusion_stamps_kept E rho hnr hji.le x _ K hr.1 hKearly
  let pre := clock p (storeAt p c E rho i x) (SA.voteTime p.toParams (s + 1))
  let v := actView pre
  have hvsKey : baseVote (⟨.seat (.head s) q, K.root⟩ : HeadWire p.n) ∈
      (storeAt p c E rho i x).base.voteStamp.map Prod.fst := by
    change _ ∈ (V2.D.Run.stateBefore E rho i x).st.base.voteStamp.map Prod.fst
    rw [fgsa_vote_stamp_keys E rho i x]
    exact hvoteI
  have hbsKey : K ∈ (storeAt p c E rho i x).base.blockStamp.map Prod.fst := by
    change K ∈ (V2.D.Run.stateBefore E rho i x).st.base.blockStamp.map Prod.fst
    rw [(storeBundle_stateBefore E rho i x).«meta».stampKeys]
    exact hblockI
  have hvs : GridCO.stampVote v (baseVote (⟨.seat (.head s) q, K.root⟩ : HeadWire p.n)) =
      GridCO.stampVote (storeAt p c E rho j x).base
        (baseVote (⟨.seat (.head s) q, K.root⟩ : HeadWire p.n)) := by
    apply Eq.trans (inclusion_stampVote_of_prefix (st' := v) ?_ hvsKey) hvsI
    change _ <+: (clock p _ _).base.voteStamp
    rw [(clock_cumulative p _ _).2.2.2.1]
  have hbs : GridCO.stampBlock v K = GridCO.stampBlock (storeAt p c E rho j x).base K := by
    apply Eq.trans (inclusion_stampBlock_of_prefix (st' := v) ?_ hbsKey) hbsI
    change _ <+: (clock p _ _).base.blockStamp
    rw [(clock_cumulative p _ _).2.2.1]
  have hKg : K ∈ v.blocks := by
    apply (actView_blocks _ K).mpr
    rw [clock_base_blocks, clock_fg]
    exact ⟨hblockI, hprefix i le_rfl⟩
  have hslot : K.slot ≤ s := by
    have hm := (fgsa_stateBefore_bounds E rho hsch k y).1 K hKsource
    have hn := V2.D.Engine.stateBefore_now_le_event (fgsaClock p c) (fgsa_hrestore_now p c)
      E rho hsch hk y
    rw [fgsa_clock_now p c (V2.D.Run.stateBefore E rho k y)] at hn
    exact hm.trans ((Internal.slotOf_mono (p := p) hn).trans_eq
      (slotOf_offset p s p.Δ hd.le (by omega)))
  have hpos : 0 < SA.earlyTime p.toParams s := by
    change 0 < 4 * p.Δ * ((s : Nat) : Int) + 2 * p.Δ
    positivity
  have hfreeze : SA.earlyTime p.toParams s < SA.freezeTime p.toParams s := by
    rw [arming_early_eq, arming_freeze_eq]
    linarith
  have hvsf : GridCO.stampVote v
      (baseVote (⟨.seat (.head s) q, K.root⟩ : HeadWire p.n)) <
        SA.freezeTime p.toParams s := by
    rw [hvs]
    exact hr.2.trans hfreeze
  have hbsf : GridCO.stampBlock v K < SA.freezeTime p.toParams s := by
    rw [hbs]
    exact (outageV_block_stamp_lt hsch hnr hj hpos K hKearly).trans hfreeze
  have hvd : baseVote (⟨.seat (.head s) q, K.root⟩ : HeadWire p.n) ∈ pre.base.votes := by
    rw [(clock_vn _ _).1]
    exact hvoteI
  have hKd : K ∈ pre.base.blocks := by
    rw [clock_base_blocks]
    exact hblockI
  have hsup : baseVote (⟨.seat (.head s) q, K.root⟩ : HeadWire p.n) ∈
      headSupport p pre (s + 1) := by
    change _ ∈ List.eraseDups (α := GridCO.Wire p.n .root) (_ ++ _)
    rw [List.mem_eraseDups]
    apply List.mem_append_left
    apply List.mem_filter.mpr
    refine ⟨List.mem_filter.mpr ⟨hvd, beq_self_eq_true _⟩, ?_⟩
    have hres := actView_resolve_target p pre
      (cstoreInv_clock p _ (cstoreInv_stateBefore E rho i x) _)
      (base_headDomain_none p (Reachable.tick _ (reachable_stateBefore E rho i x)))
      (baseVote (⟨.seat (.head s) q, K.root⟩ : HeadWire p.n)) hKg rfl
    rw [Nat.add_sub_cancel]
    change (match GridCO.resolvedHead? v
        (baseVote (⟨.seat (.head s) q, K.root⟩ : HeadWire p.n)) with
      | none => false
      | some H => decide (H.slot ≤ (GridCO.headLabel?
          (baseVote (⟨.seat (.head s) q, K.root⟩ : HeadWire p.n))).getD 0) &&
          decide (GridCO.stampVote v
            (baseVote (⟨.seat (.head s) q, K.root⟩ : HeadWire p.n)) < SA.freezeTime p.toParams s) &&
          decide (GridCO.stampBlock v H < SA.freezeTime p.toParams s)) = true
    rw [hres]
    change (decide (K.slot ≤ s) && decide (GridCO.stampVote v
      (baseVote (⟨.seat (.head s) q, K.root⟩ : HeadWire p.n)) < SA.freezeTime p.toParams s) &&
      decide (GridCO.stampBlock v K < SA.freezeTime p.toParams s)) = true
    exact Bool.and_eq_true_iff.mpr
      ⟨Bool.and_eq_true_iff.mpr ⟨decide_eq_true hslot, decide_eq_true hvsf⟩,
        decide_eq_true hbsf⟩
  refine ⟨K, SA.voteTime p.toParams s, hem, hsup, hKd, hslot, hBK, ?_⟩
  intro X hXK
  have hXe : eraseFG X ∈ (storeAt p c E rho j x).base.blocks := by
    have hm := (actView_blocks _ _).mp (hpath _ hXK)
    rw [← hjread] at hm
    exact hm.1
  obtain ⟨Y, hY, heY⟩ := ((storeBundle_stateBefore E rho j x).cstore.baseTree _).mp hXe
  have hX : X ∈ (storeAt p c E rho j x).fg.TF := eraseFG_injective heY ▸ hY
  exact outageV_frozen_of_receipt hsch hnr hcumul hx hj hpos
    (by simpa only [Nat.add_sub_cancel] using hfreeze.le) hji.le
    (Nat.le_of_lt (List.getElem?_eq_some_iff.mp ht).1) hX

/-- OUTPUT-DIRECT §3. DC: INTENTIONAL; an old held path relays before
freeze even when its source cutoff equals the previous early boundary.
Current F below the path supplies all prior exclusion checks. -/
theorem outageV_frozen_path_receipt
    {ΔF : Time} (hvalid : V2.D.ExecutionValid E rho) (hnr : V2.D.NoRestart rho)
    (hdelta : E.Δ = p.Δ) (hcumul : RStoreCumul p c E rho)
    (hroots : NamedRootCollisionFree p c E rho)
    (hsync : Gen.V2.Duty.PartialSynchronyBy E rho (fgsaDelay E.Δ ΔF))
    {i k : Nat} {x y : V} {s : Slot} {U : FGBlock (Fin p.n)}
    (ht : rho.events[i]? = some (.tick x (SA.voteTime p.toParams (s + 1))))
    (hy : y ∈ rho.honest) (hU : U ∈ (storeAt p c E rho k y).fg.TF)
    (hcut : ∀ l < k, ∀ e, rho.events[l]? = some e → e.time ≤ SA.earlyTime p.toParams s)
    (hGST : E.t_GST ≤ SA.voteTime p.toParams s)
    (hF : Block.Preceq (F_at p c E rho i x) (eraseFG U)) :
    ∀ X, FGBlock.Preceq X U → X ∈ voterBlocks p
      (clock p (storeAt p c E rho i x) (SA.voteTime p.toParams (s + 1))) (s + 1) := by
  have hsch := hvalid.toScheduleWellFormed
  have hx := hsch.honest_only _ (List.mem_of_getElem? ht)
  have hfreeze : SA.freezeTime p.toParams s < SA.voteTime p.toParams (s + 1) := by
    rw [arming_freeze_eq, arming_vote_eq]
    push_cast
    have := p.deltaPos
    nlinarith
  have hhor : SA.freezeTime p.toParams s ≤ rho.horizon :=
    hfreeze.le.trans (hsch.in_horizon _ (List.mem_of_getElem? ht)).2
  have hft : ((4 * s + 3 : Nat) : Time) * p.Δ = SA.freezeTime p.toParams s := by
    rw [arming_freeze_eq]
    push_cast
    ring
  obtain ⟨j, hj, _⟩ := fgsa_tick_total E rho hsch hdelta x hx (4 * s + 3) (hft ▸ hhor)
  rw [hft] at hj
  have hji := V2.D.Engine.eventIndex_lt_of_time_lt hsch hj ht hfreeze
  have hjread := fgsa_preTick_eq_timeRead E rho hsch hnr hj
  have hidx : V2.D.Run.idxBefore rho (SA.freezeTime p.toParams s) ≤ i := by
    by_contra hn
    exact (not_lt.mpr hfreeze.le)
      ((Gen.V2.Duty.index_lt_idxBefore_iff hsch ht _).mp (Nat.lt_of_not_ge hn))
  have hhistory : ∀ l, l ≤ i → Block.Compatible (eraseFG U) (F_at p c E rho l x) := by
    intro l hl
    exact Bool.or_eq_true_iff.mpr (Or.inr
      (block_preceq_trans (arming_F_mono (E := E) hnr hl x) hF))
  have hUb := ((storeBundle_stateBefore E rho k y).cstore.baseTree _).mpr ⟨U, hU, rfl⟩
  obtain ⟨required, paths, hcov, hp⟩ := outageV_path_coverage hvalid hdelta hsync hy hUb
    hcut (outageV_source_relay_before_freeze p s _ _ le_rfl hGST) hhor
    (fun l hl => hhistory l (hl.trans hidx))
  have hFcut : Block.Compatible (eraseFG U)
      (eraseFG (V2.D.Run.stateBeforeTime E rho (SA.freezeTime p.toParams s) x).st.fg.F) := by
    rw [← Gen.V2.Duty.stateBefore_idxBefore E rho _ hsch]
    exact hhistory _ hidx
  have hpath := outageV_active_path_of_coverage (hroots := hroots) hvalid hnr hdelta
    (fun t => max t E.t_GST + p.Δ) rho.horizon (SA.freezeTime p.toParams s) 0 x
    (eraseFG U) required paths hx hcov hp hFcut
  intro X hXU
  have hXe := (actView_blocks _ _).mp (hpath _ (eraseFG_preceq hXU)) |>.1
  rw [← hjread] at hXe
  obtain ⟨Y, hY, heY⟩ := ((storeBundle_stateBefore E rho j x).cstore.baseTree _).mp hXe
  have hX : X ∈ (storeAt p c E rho j x).fg.TF := eraseFG_injective heY ▸ hY
  have hpos : 0 < SA.freezeTime p.toParams s := by
    rw [arming_freeze_eq]
    have := p.deltaPos
    positivity
  exact outageV_frozen_of_receipt hsch hnr hcumul hx hj hpos
    (by simp only [Nat.add_sub_cancel]; exact le_rfl) hji.le
    (Nat.le_of_lt (List.getElem?_eq_some_iff.mp ht).1) hX

/-- OUTPUT-DIRECT §3. DC: INTENTIONAL; instantiate the uncontested HEAD
with authentic covering receipts and frozen crossing-source witnesses.
Only causal source history, prior HEAD coverage, and live-root compatibility
remain as induction inputs. No full-store witness substitutes for a frozen one. -/
theorem outageV_uncontested_head [Fintype V]
    {ΔF : Time} (hvalid : V2.D.ExecutionValid E rho) (hnr : V2.D.NoRestart rho)
    (hdelta : E.Δ = p.Δ) (hcstar : V2.D.CStar (fgsaFamilies p c).fresh rho)
    (hcumul : RStoreCumul p c E rho) (hroots : NamedRootCollisionFree p c E rho)
    (origin : RQCOrigin p c E rho)
    (hsync : Gen.V2.Duty.PartialSynchronyBy E rho (fgsaDelay E.Δ ΔF))
    {i : Nat} {x : V} {s : Slot} (B : FGBlock (Fin p.n))
    (ht : rho.events[i]? = some (.tick x (SA.voteTime p.toParams (s + 1))))
    (hGST : E.t_GST ≤ SA.voteTime p.toParams s)
    (hpart : (Gen.V2.Duty.faulty rho).card <
      (Gen.V2.Duty.awakeHonest E rho (SA.voteTime p.toParams s)).card)
    (hist : OutageSourceHistory p c E rho (eraseFG B) i)
    (hB : ∀ k y, y ∈ rho.honest →
      rho.events[k]? = some (.tick y (SA.voteTime p.toParams s)) →
      Block.Preceq (eraseFG B)
        (headVote p (clock p (storeAt p c E rho k y) (SA.voteTime p.toParams s)) s))
    (hroot : Block.Compatible (liveRoot p
      (clock p (storeAt p c E rho i x) (SA.voteTime p.toParams (s + 1)))) (eraseFG B))
    (hnt : (controls p (clock p (storeAt p c E rho i x)
      (SA.voteTime p.toParams (s + 1)))).contest = false) :
    Block.Preceq (eraseFG B) (headVote p
      (clock p (storeAt p c E rho i x) (SA.voteTime p.toParams (s + 1))) (s + 1)) := by
  let dst := clock p (storeAt p c E rho i x) (SA.voteTime p.toParams (s + 1))
  have hinv := cstoreInv_clock p _ (cstoreInv_stateBefore E rho i x)
    (SA.voteTime p.toParams (s + 1))
  by_cases hBA : Block.Preceq (eraseFG B) (liveRoot p dst)
  · change Block.Preceq _ (if s + 1 = 0 then .genesis else headInTree p dst _ _ _)
    rw [ite_eq_right (Nat.succ_ne_zero s)]
    exact block_preceq_trans hBA (liveRoot_preceq_headInTree p dst _ _ _)
  have hAB : Block.Preceq (liveRoot p dst) (eraseFG B) := by
    rcases Bool.or_eq_true_iff.mp hroot with h | h
    · exact h
    · exact (hBA h).elim
  have hF : Block.Preceq (F_at p c E rho i x) (eraseFG B) := by
    have hf := block_preceq_trans (F_preceq_liveRoot p dst hinv) hAB
    change Block.Preceq (eraseFG (clock p _ _).fg.F) _ at hf
    rwa [clock_fg] at hf
  have hrec := outageV_covering_head_receipts hvalid hnr hdelta hcstar hcumul hroots
    hsync ht hGST (eraseFG B) hF hB
  obtain ⟨H, hH, hbatch⟩ := inclusion_head_seats E rho hcstar s ⟨hpart⟩
  obtain ⟨q, hq⟩ := Finset.card_pos.mp (lt_of_le_of_lt (Nat.zero_le _) hbatch.lt)
  obtain ⟨K, _, _, _, _, _, hBK, hpathK⟩ := hrec q ((hH q).mp hq).1 ((hH q).mp hq).2
  have hpathB : ∀ X, FGBlock.Preceq X B → X ∈ voterBlocks p dst (s + 1) := by
    intro X hXB
    exact hpathK X (block_preceq_trans (eraseFG_preceq hXB) hBK)
  have hBm := hpathB B (preceq_refl B)
  have hlo : (controls p dst).lo = dst.fg.h_max - 1 := by
    change (if (controls p dst).contest then dst.fg.h_max else dst.fg.h_max - 1) = _
    rw [hnt]
    rfl
  have hwitness : ∃ W ∈ voterBlocks p dst (s + 1), FGBlock.Preceq B W ∧
      (controls p dst).lo ≤ (heightView p W).h := by
    by_cases hlow : dst.fg.h_max - 1 ≤ (heightView p B).h
    · exact ⟨B, hBm, preceq_refl B, hlo ▸ hlow⟩
    obtain ⟨W, hW, hWh⟩ := KitFG.store_frontier_witness p.E (heightView p) (finalityView p)
      (fgCertificateLaws p) dst.fg hinv.fg
    have hWpre : W ∈ (storeAt p c E rho i x).fg.TF := by
      change W ∈ (clock p _ _).fg.TF at hW
      rwa [clock_fg] at hW
    have hBpos := (fgCertificateLaws p).height.one_le_h B
    change ¬ ((_ : Nat) ≤ _) at hlow
    change (1 : Nat) ≤ _ at hBpos
    change (_ : Nat) = _ at hWh
    have hm : 1 ≤ dst.fg.h_max - 1 := by
      change (1 : Nat) ≤ _
      omega
    have hmW : dst.fg.h_max - 1 < (heightView p W).h := by
      change (_ : Nat) < _
      omega
    obtain ⟨k, hk, y, r, wire, U, hrow, _, hUh, hUB, hU, htime⟩ :=
      outageV_crossing_source hvalid.toScheduleWellFormed origin
        (hvalid.honest_only _ (List.mem_of_getElem? ht)) ht hWpre hm hmW hist
    have hBU : FGBlock.Preceq B U := by
      rcases Bool.or_eq_true_iff.mp hUB with h | h
      · have hmono := (fgCertificateLaws p).height.h_mono (eraseFG_preceq_iff.mp h)
        rw [hUh] at hmono
        exact (hlow hmono).elim
      · exact eraseFG_preceq_iff.mp h
    have hfU := block_preceq_trans hF (eraseFG_preceq hBU)
    have hfreeze := outageV_frozen_path_receipt hvalid hnr hdelta hcumul hroots hsync
      ht hrow.1 hU (fun l hl e he => by
        have hle : e.time ≤ p.actionTime r := by
          by_contra hn
          have := V2.D.Engine.eventIndex_lt_of_time_lt hvalid.toScheduleWellFormed
            hrow.2.1 he (lt_of_not_ge hn)
          omega
        exact hle.trans htime) hGST hfU
    exact ⟨U, hfreeze U (preceq_refl U), hBU, by rw [hlo, hUh]⟩
  obtain ⟨W, hW, hBW, hWh⟩ := hwitness
  apply outageV_head_covers_from_batch E rho hvalid hnr hcstar s (eraseFG B) ht hpart hroot
  · intro C _ hCB
    obtain ⟨X, _, heX⟩ := eraseFG_ancestor_mem hinv.fg.closed
      (Finset.mem_filter.mp hBm).1 hCB
    have hXB := eraseFG_preceq_iff.mp (heX ▸ hCB)
    exact ⟨X, hpathB X hXB, heX, W, hW, preceq_trans hXB hBW, hWh⟩
  · intro q hh ha
    obtain ⟨K, t, hem, hs, hm, hslot, hBK, _⟩ := hrec q hh ha
    exact ⟨K, t, hem, hs, hm, hslot, hBK⟩

end AvailableChain.FGSA.Run
end
