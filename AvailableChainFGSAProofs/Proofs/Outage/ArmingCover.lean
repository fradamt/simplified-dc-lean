module
public import AvailableChainFGSAProofs.Proofs.Outage.ArmingDuty
public import AvailableChainFGSAProofs.Proofs.Outage.ArmingPrefix
public import AvailableChainFGSA.Proofs.Head.Transfer

public section

/-! Plan O-ARM §6.2 step 6. The label-`(l + 2)` HEAD and proposal reads cover
`D`. Every honest awake label-`(l + 1)` HEAD extends `D` and is in the read
pools with stamps before e(l + 1) < z(l + 1). The live root is below `D`, the
path to `D` is in the read domain, and the batch majority gives the walk. -/

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG
open Gen.Pure

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

/-- Plan O-ARM §6.2 step 6. Class (iii). DC: INTENTIONAL; a strict ancestor
relation is an order relation between distinct blocks. -/
theorem arming_prec {A C : Block} (h : Block.Prec A C) : A ≠ C ∧ Block.Preceq A C := by
  change ((!decide (A = C)) && Block.preceq A C) = true at h
  simpa only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
    Block.Preceq] using h

/-- Plan O-ARM §6.2 step 6. Class (iii). DC: INTENTIONAL; a strict descendant
of a block is not genesis. -/
theorem arming_prec_ne_genesis {A C : Block} (h : Block.Prec A C) : C ≠ .genesis := by
  intro hC
  subst hC
  obtain ⟨hne, hle⟩ := arming_prec h
  exact hne (block_preceq_antisymm hle (block_genesis_preceq A))

/-- Plan O-ARM §4 field 5, §6.2 step 6. Class (iii). DC: INTENTIONAL; the
field 5 premise form, used by the duty proofs. -/
abbrev ArmingPrefixState (p : Params) {In V : Type} (c : AppCodec In) [DecidableEq V]
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (l : Slot) (D : Block)
    (Dh : FGBlock (Fin p.n)) : Prop :=
  ∀ i y, i ≤ V2.D.Run.idxBefore rho (SA.gateTime p.toParams (l + 1)) →
    i ≤ rho.events.length → y ∈ rho.honest →
    Block.Preceq (F_at p c E rho i y) D ∧ Block.Preceq (J_at p c E rho i y) D ∧
    Block.Preceq (eraseFG (FGSA.controls p (storeAt p c E rho i y)).Z) D ∧
    (FGSA.controls p (storeAt p c E rho i y)).contest = false ∧
    (FGSA.controls p (storeAt p c E rho i y)).lo ≤ (heightView p Dh).h ∧
    ∀ row ∈ (storeAt p c E rho i y).base.obligations, Block.Preceq row.1 D

/-- Plan O-ARM §4 field 6, §6.2 step 6. Class (iii). DC: INTENTIONAL; the
field 6 premise form, used by the duty proofs. -/
abbrev ArmingBatchState (p : Params) {In V : Type} (c : AppCodec In) [DecidableEq V]
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (l : Slot) (D : Block) : Prop :=
  ∀ y (q : Fin p.n), y ∈ rho.honest →
    rho.seatOf (.base (.head (l + 1))) q ∈ rho.honest →
    E.awake (rho.seatOf (.base (.head (l + 1))) q) (SA.voteTime p.toParams (l + 1)) = true →
    ∃ K k, rho.events[k]? = some (.tick y (SA.earlyTime p.toParams (l + 1))) ∧
      V2.D.Run.emits E rho (rho.seatOf (.base (.head (l + 1))) q)
        (ofHead p ⟨.seat (.head (l + 1)) q, K⟩) (SA.voteTime p.toParams (l + 1)) ∧
      Block.Preceq D K ∧ K.slot ≤ l + 1 ∧
      baseVote (⟨.seat (.head (l + 1)) q, K⟩ : HeadWire p.n) ∈
        (storeAt p c E rho k y).base.votes ∧
      K ∈ (storeAt p c E rho k y).base.blocks ∧
      GridCO.stampVote (storeAt p c E rho k y).base
        (baseVote (⟨.seat (.head (l + 1)) q, K⟩ : HeadWire p.n)) <
        SA.earlyTime p.toParams (l + 1) ∧
      GridCO.stampBlock (storeAt p c E rho k y).base K < SA.earlyTime p.toParams (l + 1)

/-- Plan O-ARM §6.2 step 6. Class (iii). DC: INTENTIONAL; the batch at a later
read tick of `y` before the pending gate: each HEAD is still stored with its
original stamps. -/
theorem arming_batch_at {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}
    (hs : V2.D.ScheduleWellFormed E rho) (hN : V2.D.NoRestart rho) {l : Slot} {D : Block}
    (hbatchF : ArmingBatchState p c E rho l D) {y : V} (hy : y ∈ rho.honest) {i : Nat}
    {t : Time} (hi : rho.events[i]? = some (.tick y t))
    (ht : SA.earlyTime p.toParams (l + 1) < t) (q : Fin p.n)
    (hq : rho.seatOf (.base (.head (l + 1))) q ∈ rho.honest)
    (haw : E.awake (rho.seatOf (.base (.head (l + 1))) q) (SA.voteTime p.toParams (l + 1)) =
      true) :
    ∃ K k, rho.events[k]? = some (.tick y (SA.earlyTime p.toParams (l + 1))) ∧ k < i ∧
      V2.D.Run.emits E rho (rho.seatOf (.base (.head (l + 1))) q)
        (ofHead p ⟨.seat (.head (l + 1)) q, K⟩) (SA.voteTime p.toParams (l + 1)) ∧
      Block.Preceq D K ∧ K.slot ≤ l + 1 ∧
      baseVote (⟨.seat (.head (l + 1)) q, K⟩ : HeadWire p.n) ∈
        (storeAt p c E rho k y).base.votes ∧
      baseVote (⟨.seat (.head (l + 1)) q, K⟩ : HeadWire p.n) ∈
        (storeAt p c E rho i y).base.votes ∧
      K ∈ (storeAt p c E rho i y).base.blocks ∧
      GridCO.stampVote (storeAt p c E rho i y).base
        (baseVote (⟨.seat (.head (l + 1)) q, K⟩ : HeadWire p.n)) <
        SA.earlyTime p.toParams (l + 1) ∧
      GridCO.stampBlock (storeAt p c E rho i y).base K < SA.earlyTime p.toParams (l + 1) := by
  obtain ⟨K, k, hk, hem, hDK, hslot, hv, hKb, hvs, hbs⟩ := hbatchF y q hy hq haw
  have hki : k < i := V2.D.Engine.eventIndex_lt_of_time_lt hs hk hi ht
  obtain ⟨hv', hK', hvs', hbs'⟩ := inclusion_stamps_kept E rho hN hki.le y _ K hv hKb
  exact ⟨K, k, hk, hki, hem, hDK, hslot, hv, hv', hK', hvs' ▸ hvs, hbs' ▸ hbs⟩

/-- Plan O-ARM §6.2 step 6. Class (iii). DC: INTENTIONAL; at a non-gate tick
strictly before the pending gate the clocked read has F, Z, floor and live
root below `D`. -/
theorem arming_read_bounds {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}
    (hs : V2.D.ScheduleWellFormed E rho) {l : Slot} {D : Block} {Dh : FGBlock (Fin p.n)}
    (hprefix : ArmingPrefixState p c E rho l D Dh) {y : V} (hy : y ∈ rho.honest)
    {i : Nat} {t : Time} (hi : rho.events[i]? = some (.tick y t))
    (ht : t < SA.gateTime p.toParams (l + 1)) (hoff : ∀ r : Slot, SA.gateTime p.toParams r ≠ t) :
    i ≤ V2.D.Run.idxBefore rho (SA.gateTime p.toParams (l + 1)) ∧
      Block.Preceq (eraseFG (clock p (storeAt p c E rho i y) t).fg.F) D ∧
      (controls p (clock p (storeAt p c E rho i y) t)).lo ≤ (heightView p Dh).h ∧
      Block.Preceq (liveRoot p (clock p (storeAt p c E rho i y) t)) D := by
  have hiI : i ≤ V2.D.Run.idxBefore rho (SA.gateTime p.toParams (l + 1)) :=
    ((Gen.V2.Duty.index_lt_idxBefore_iff hs hi _).mpr ht).le
  obtain ⟨hF, -, hZ, -, hlo, hobl⟩ := hprefix i y hiI
    (hiI.trans (arming_idxBefore_le_length rho _)) hy
  have hctrl : controls p (clock p (storeAt p c E rho i y) t) =
      controls p (storeAt p c E rho i y) :=
    congrArg (KitFG.storeControlsView (heightView p)) (clock_fg p _ _)
  have hsub := (arming_clock_offGate_fields p (storeAt p c E rho i y) t hoff).2.2.2
  refine ⟨hiI, ?_, by rw [hctrl]; exact hlo, ?_⟩
  · rw [clock_fg]
    exact hF
  · exact inclusion_liveRoot_le p _ D (by rw [hctrl]; exact hZ)
      (fun row hrow => hobl row (hsub.subset hrow))

/-- Plan O-ARM §6.2 step 6. Class (iii). DC: INTENTIONAL; the label-`(l + 2)`
HEAD of every honest node reads the batch and covers `D`. The frozen block
arm holds every ancestor of `D` above the live root: each was stored before
e(l + 1) < z(l + 1). -/
theorem arming_head_covers [Fintype V] {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}
    (hE : V2.D.ExecutionValid E rho) (hN : V2.D.NoRestart rho) (hDelta : E.Δ = p.Δ)
    (hC : V2.D.CStar (fgsaFamilies p c).fresh rho)
    {l : Slot} {D : Block} {Dh : FGBlock (Fin p.n)} (hDh : eraseFG Dh = D)
    (hDne : D ≠ .genesis)
    (hSync : Gen.V2.Duty.LabelSyncOn E rho (fun o => ¬ isRowObject o)
      (SA.voteTime p.toParams (l + 1)) (SA.earlyTime p.toParams (l + 1)))
    (hpartv : Gen.Pure.Batch
      (Gen.V2.Duty.awakeHonest E rho (SA.voteTime p.toParams (l + 1))).card
      (Gen.V2.Duty.faulty rho).card)
    (hprefix : ArmingPrefixState p c E rho l D Dh)
    (hbatchF : ArmingBatchState p c E rho l D)
    {y : V} (hy : y ∈ rho.honest) {ih : Nat}
    (hih : rho.events[ih]? = some (.tick y (SA.voteTime p.toParams (l + 2)))) :
    Block.Preceq D (headVote p (clock p (V2.D.Run.stateBefore E rho ih y).st
      (SA.voteTime p.toParams (l + 2))) (l + 2)) := by
  classical
  have hs := hE.toScheduleWellFormed
  let dst := clock p (V2.D.Run.stateBefore E rho ih y).st (SA.voteTime p.toParams (l + 2))
  have hinv : CStoreInv p dst := cstoreInv_clock p _ (cstoreInv_stateBefore E rho ih y) _
  obtain ⟨_, htv, hvd, het⟩ := arming_duty_window p l
  obtain ⟨hihI, hFd, hlod, hlive⟩ := arming_read_bounds hs hprefix hy hih hvd
    (fun r => arming_gate_ne_vote p r (l + 2))
  change Block.Preceq (eraseFG dst.fg.F) D at hFd
  change (controls p dst).lo ≤ (heightView p Dh).h at hlod
  change Block.Preceq (liveRoot p dst) D at hlive
  obtain ⟨H, hH, hbatch⟩ := inclusion_head_seats E rho hC (l + 1) hpartv
  have hfr := (arming_vote_lt_early p (l + 1)).2
  have hstampDst : ∀ X, X ∈ (storeAt p c E rho ih y).base.blocks →
      GridCO.stampBlock dst.base X = GridCO.stampBlock (storeAt p c E rho ih y).base X := by
    intro X hX
    change GridCO.stampBlock (clock p (storeAt p c E rho ih y) _).base X = _
    have hkey : X ∈ (storeAt p c E rho ih y).base.blockStamp.map Prod.fst := by
      change X ∈ (V2.D.Run.stateBefore E rho ih y).st.base.blockStamp.map Prod.fst
      rw [(storeBundle_stateBefore E rho ih y).«meta».stampKeys]
      exact hX
    exact inclusion_stampBlock_of_prefix (by rw [(clock_cumulative p _ _).2.2.1]) hkey
  have hrecR : ∀ w ∈ H, ∃ K t, V2.D.Run.emits E rho (rho.seatOf (.base (.head (l + 1))) w)
        (ofHead p ⟨.seat (.head (l + 1)) w, K⟩) t ∧
      baseVote (⟨.seat (.head (l + 1)) w, K⟩ : HeadWire p.n) ∈ headSupport p dst (l + 1 + 1) ∧
      K ∈ dst.base.blocks ∧ K.slot ≤ l + 1 ∧ Block.Preceq D K := by
    intro w hw
    obtain ⟨hyw, haw⟩ := (hH w).mp hw
    obtain ⟨K, _, _, _, hem, hDK, hslot, _, hv, hKb, hvs, hbs⟩ :=
      arming_batch_at hs hN hbatchF hy hih (het.trans htv) w hyw haw
    let o := baseVote (⟨.seat (.head (l + 1)) w, K⟩ : HeadWire p.n)
    have hvd : o ∈ dst.base.votes := by
      change _ ∈ (clock p (storeAt p c E rho ih y) _).base.votes
      rw [(clock_vn _ _).1]
      exact hv
    have hKd : K ∈ dst.base.blocks := by
      change K ∈ (clock p (storeAt p c E rho ih y) _).base.blocks
      rw [clock_base_blocks]
      exact hKb
    have hvsd : GridCO.stampVote (actView dst) o < SA.freezeTime p.toParams (l + 1) := by
      change GridCO.stampVote (clock p (storeAt p c E rho ih y) _).base o < _
      have hkey : o ∈ (storeAt p c E rho ih y).base.voteStamp.map Prod.fst := by
        change o ∈ (V2.D.Run.stateBefore E rho ih y).st.base.voteStamp.map Prod.fst
        rw [fgsa_vote_stamp_keys E rho ih y]
        exact hv
      rw [inclusion_stampVote_of_prefix (by rw [(clock_cumulative p _ _).2.2.2.1]) hkey]
      exact hvs.trans hfr
    have hbsd : GridCO.stampBlock (actView dst) K < SA.freezeTime p.toParams (l + 1) := by
      change GridCO.stampBlock dst.base K < _
      rw [hstampDst K hKb]
      exact hbs.trans hfr
    have hKa : GridCO.blockKnown (actView dst) K = true := by
      apply decide_eq_true
      apply (actView_blocks dst K).mpr
      exact ⟨hKd, block_compatible_of_common (block_preceq_refl K)
        (block_preceq_trans hFd hDK)⟩
    refine ⟨K, _, hem, ?_, hKd, hslot, hDK⟩
    unfold headSupport
    dsimp only
    rw [List.mem_eraseDups]
    apply List.mem_append_left
    apply List.mem_filter.mpr
    refine ⟨List.mem_filter.mpr ⟨hvd, beq_self_eq_true _⟩, ?_⟩
    change (GridCO.blockKnown (actView dst) K && decide (K.slot ≤ l + 1) &&
      decide (GridCO.stampVote (actView dst) o < SA.freezeTime p.toParams (l + 1)) &&
      decide (GridCO.stampBlock (actView dst) K < SA.freezeTime p.toParams (l + 1))) = true
    simp only [hKa, hslot, hvsd, hbsd, decide_true, Bool.and_self]
  have hRS := inclusion_reader_scores E rho hE hN hC (l + 1) hih H hH hbatch D hrecR
  -- One batch HEAD fixes the reader e(l + 1) tick and an honest holder.
  obtain ⟨w0, hw0⟩ := Finset.card_pos.mp (lt_of_le_of_lt (Nat.zero_le _) hbatch.lt)
  obtain ⟨hyw0, haw0⟩ := (hH w0).mp hw0
  obtain ⟨K0, k0, hk0, hk0ih, hem0, hDK0, _, hv0, _, _, _, _⟩ :=
    arming_batch_at hs hN hbatchF hy hih (het.trans htv) w0 hyw0 haw0
  have hk0I := hk0ih.le.trans hihI
  have hF0 : Block.Preceq (F_at p c E rho k0 y) D :=
    (hprefix k0 y hk0I (hk0I.trans (arming_idxBefore_le_length rho _)) hy).1
  have hFk0 : Block.Preceq (F_at p c E rho k0 y) (eraseFG dst.fg.F) := by
    have h := arming_F_mono (E := E) hN hk0ih.le y
    change Block.Preceq _ (eraseFG (storeAt p c E rho ih y).fg.F) at h
    change Block.Preceq _ (eraseFG (clock p (storeAt p c E rho ih y) _).fg.F)
    rw [clock_fg]
    exact h
  have hvoter : ∀ X, X ≠ .genesis → Block.Preceq X D →
      Block.Preceq (F_at p c E rho k0 y) X →
      ∃ Xh ∈ voterBlocks p dst (l + 1 + 1), eraseFG Xh = X := by
    intro X hne hXD hFX
    obtain ⟨hXm, hXs⟩ := arming_ancestor_stamp hE hN hDelta hSync hk0 hyw0 hem0 hDK0
      hk0ih.le _ hv0 X hne hXD hFX
    have hXd : X ∈ dst.base.blocks := by
      change X ∈ (clock p (storeAt p c E rho ih y) _).base.blocks
      rw [clock_base_blocks]
      exact hXm
    obtain ⟨Xh, hXh, hXe⟩ := (hinv.baseTree X).1 hXd
    have hlt : GridCO.stampBlock dst.base (eraseFG Xh) <
        SA.freezeTime p.toParams (l + 1 + 1 - 1) := by
      rw [hXe, hstampDst X hXm]
      exact hXs.trans hfr
    exact ⟨Xh, Finset.mem_filter.mpr ⟨hXh, Bool.or_eq_true_iff.mpr
      (Or.inl (decide_eq_true hlt))⟩, hXe⟩
  obtain ⟨Dh', hDh'V, hDe⟩ := hvoter D hDne (block_preceq_refl D) hF0
  have hDhV : Dh ∈ voterBlocks p dst (l + 1 + 1) := by
    rw [← eraseFG_injective (hDe.trans hDh.symm)]
    exact hDh'V
  have hpath : ∀ C, Block.Prec (liveRoot p dst) C → Block.Preceq C D →
      C ∈ erasedList dst (storeFrame p.E p.cfg dst.fg (voterBlocks p dst (l + 1 + 1))) := by
    intro C hr hCD
    have hlC := (arming_prec hr).2
    have hFC : Block.Preceq (eraseFG dst.fg.F) C :=
      block_preceq_trans (F_preceq_liveRoot p dst hinv) hlC
    obtain ⟨Ch, hChV, hCe⟩ := hvoter C (arming_prec_ne_genesis hr) hCD
      (block_preceq_trans hFk0 hFC)
    have hm := fgsa_walk_domain_of_witness p dst (voterBlocks p dst (l + 1 + 1)) Ch Dh
      (fun B hB => (hinv.baseTree _).2 ⟨B, hB, rfl⟩) (Finset.filter_subset _ _) hChV hDhV
      (arming_lift (hCe ▸ hFC))
      (arming_lift (hCe ▸ block_preceq_trans (fgsa_Z_preceq_liveRoot p dst) hlC))
      (arming_lift (hCe ▸ hDh ▸ hCD)) hlod
    rw [domainR_eq_storeFrame, hCe] at hm
    exact hm
  have hD := hRS D (block_preceq_refl D)
  exact fgsa_headVote_covers_of_transfer p dst (l + 1) D
    (block_compatible_of_common hlive (block_preceq_refl D)) hpath hD.majority
    (fun X hX => by
      have h₁ := hD.rivals X hX
      have h₂ := hD.majority
      change 2 * RetainedWalk.ts p dst (l + 1 + 1) X ≤ _ at h₁
      change _ < 2 * RetainedWalk.ts p dst (l + 1 + 1) D at h₂
      change RetainedWalk.ts p dst (l + 1 + 1) X < RetainedWalk.ts p dst (l + 1 + 1) D
      omega)

/-- Plan O-ARM §6.2 step 6. Class (iii). DC: INTENTIONAL; the label-`(l + 2)`
proposer head of every honest proposer reads the full current previous-label
pool, which holds the batch, and covers `D`. -/
theorem arming_proposal_covers [Fintype V] {E : Generic.Env V}
    {rho : V2.D.Run V (fgsa p c)}
    (hE : V2.D.ExecutionValid E rho) (hN : V2.D.NoRestart rho)
    (hC : V2.D.CStar (fgsaFamilies p c).fresh rho)
    {l : Slot} {D : Block} {Dh : FGBlock (Fin p.n)} (hDh : eraseFG Dh = D)
    (hpartv : Gen.Pure.Batch
      (Gen.V2.Duty.awakeHonest E rho (SA.voteTime p.toParams (l + 1))).card
      (Gen.V2.Duty.faulty rho).card)
    (hprefix : ArmingPrefixState p c E rho l D Dh)
    (hbatchF : ArmingBatchState p c E rho l D)
    {y : V} (hy : y ∈ rho.honest) {ip : Nat}
    (hip : rho.events[ip]? = some (.tick y (SA.proposalTime p.toParams (l + 2)))) :
    Block.Preceq D (proposerHead p (clock p (V2.D.Run.stateBefore E rho ip y).st
      (SA.proposalTime p.toParams (l + 2))) (l + 2)) := by
  classical
  have hs := hE.toScheduleWellFormed
  let src := clock p (V2.D.Run.stateBefore E rho ip y).st (SA.proposalTime p.toParams (l + 2))
  have hinv : CStoreInv p src := cstoreInv_clock p _ (cstoreInv_stateBefore E rho ip y) _
  obtain ⟨_, htv, hvd, het⟩ := arming_duty_window p l
  obtain ⟨_, hFs, hlos, hlive⟩ := arming_read_bounds hs hprefix hy hip (htv.trans hvd)
    (fun r => arming_gate_ne_proposal p r (l + 2))
  change Block.Preceq (eraseFG src.fg.F) D at hFs
  change (controls p src).lo ≤ (heightView p Dh).h at hlos
  change Block.Preceq (liveRoot p src) D at hlive
  obtain ⟨H, hH, hbatch⟩ := inclusion_head_seats E rho hC (l + 1) hpartv
  have hrecP : ∀ w ∈ H, ∃ K t, V2.D.Run.emits E rho (rho.seatOf (.base (.head (l + 2 - 1))) w)
        (ofHead p ⟨.seat (.head (l + 2 - 1)) w, K⟩) t ∧
      baseVote (⟨.seat (.head (l + 2 - 1)) w, K⟩ : HeadWire p.n) ∈ src.base.votes ∧
      K ∈ (actView src).blocks ∧ K.slot ≤ l + 2 - 1 ∧ Block.Preceq D K := by
    intro w hw
    obtain ⟨hyw, haw⟩ := (hH w).mp hw
    obtain ⟨K, _, _, _, hem, hDK, hslot, _, hv, hKb, _, _⟩ :=
      arming_batch_at hs hN hbatchF hy hip het w hyw haw
    refine ⟨K, _, hem, ?_, ?_, hslot, hDK⟩
    · change _ ∈ (clock p (storeAt p c E rho ip y) _).base.votes
      rw [(clock_vn _ _).1]
      exact hv
    · apply (actView_blocks src K).mpr
      refine ⟨?_, block_compatible_of_common (block_preceq_refl K)
        (block_preceq_trans hFs hDK)⟩
      change K ∈ (clock p (storeAt p c E rho ip y) _).base.blocks
      rw [clock_base_blocks]
      exact hKb
  have hPP := inclusion_proposer_prior E rho hE hC (l + 2) ip y src (by
      change (clock p (storeAt p c E rho ip y) _).base.votes = _
      exact (clock_vn _ _).1) H hH hbatch D hrecP
  have hDsrc : Dh ∈ src.fg.TF := by
    obtain ⟨w, hw⟩ := Finset.card_pos.mp (lt_of_le_of_lt (Nat.zero_le _) hbatch.lt)
    obtain ⟨K, _, _, _, hK, _, hDK⟩ := hrecP w hw
    obtain ⟨A, hA, hAe⟩ := arming_lift_mem hinv ((actView_blocks src K).mp hK).1 hDK
    rwa [eraseFG_injective (hAe.trans hDh.symm)] at hA
  have hpath : ∀ C, Block.Prec (liveRoot p src) C → Block.Preceq C D →
      C ∈ erasedList src (fullTree p src) := by
    intro C hr hCD
    have hlC := (arming_prec hr).2
    have hFC : Block.Preceq (eraseFG src.fg.F) C :=
      block_preceq_trans (F_preceq_liveRoot p src hinv) hlC
    obtain ⟨Ch, hCh, hCe⟩ := arming_lift_mem hinv
      ((hinv.baseTree D).2 ⟨Dh, hDsrc, hDh⟩) hCD
    have hm := fgsa_walk_domain_of_witness p src src.fg.TF Ch Dh
      (fun B hB => (hinv.baseTree _).2 ⟨B, hB, rfl⟩) (subset_refl _) hCh hDsrc
      (arming_lift (hCe ▸ hFC))
      (arming_lift (hCe ▸ block_preceq_trans (fgsa_Z_preceq_liveRoot p src) hlC))
      (arming_lift (hCe ▸ hDh ▸ hCD)) hlos
    rw [domainR_eq_storeFrame, hCe, ← fullTree_eq] at hm
    exact hm
  obtain ⟨hmaj, hdom⟩ := hPP D (block_preceq_refl D)
  rw [proposerHead_def]
  exact fgsa_headInTree_covers_of_transfer p src _ _ _ D
    (block_compatible_of_common hlive (block_preceq_refl D)) hpath hmaj hdom

end AvailableChain.FGSA.Run
end
