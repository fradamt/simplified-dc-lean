module
-- L42: access the frozen conclusions through the allowed Shared module.
public import AvailableChainFGSAProofs.Proofs.Shared.Claims -- shake: keep
public import AvailableChainFGSAProofs.Proofs.Shared.Reads
public import AvailableChainFGSAProofs.Proofs.Shared.Channels
public import AvailableChainKitFG.Provenance
public import AvailableChainFGSARun.Proofs.ClientTrace

public section

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

variable (p : Params) {In V : Type} [DecidableEq V]
    (c : AppCodec In) (E : Generic.Env V) (rho : V2.Run V (fgsa p c))

private theorem source_tick_read (x : V) (r : Nat) (C : FGBlock (Fin p.n))
    (hc : actionSourceFG p c E rho x r = some (some C)) :
    ∃ i, rho.events[i]? = some (.tick x (p.actionTime r)) ∧
      let st := ((fgsa p c).clock (V2.Run.stateBefore E rho i x) (p.actionTime r)).st
      fgSource p st = some C ∧
      postClock E rho x (p.actionTime r) =
        some ((fgsa p c).clock (V2.Run.stateBefore E rho i x) (p.actionTime r)) := by
  rw [actionSourceFG_def, postClock_def, preTick_def] at hc
  cases hi : V2.Run.tickIdx? rho x (p.actionTime r) with
  | none => simp only [hi, Option.map_none] at hc; contradiction
  | some i =>
    simp only [hi, Option.map_some, Option.some.injEq] at hc
    refine ⟨i, V2.Run.tickIdx?_spec hi, hc, ?_⟩
    rw [postClock_def, preTick_def, hi]
    rfl

/-- The action's candidates have a passed gate origin (F1.3 supplies lease origins). -/
theorem sourceDiscipline_tSrc (hs : V2.ScheduleWellFormed E rho)
    (hL : LeaseOriginsAt p c E rho) : TSrc p c E rho := by
  intro x r C hx hc
  change Option.map (Option.map eraseFG) (actionSourceFG p c E rho x r) = _ at hc
  cases hf : actionSourceFG p c E rho x r with
  | none => simp only [hf, Option.map_none] at hc; contradiction
  | some src =>
    cases src with
    | none =>
      simp only [hf, Option.map_some, Option.map_none, Option.some.injEq] at hc
      contradiction
    | some B =>
      have he : eraseFG B = C := by simpa only [hf, Option.map_some, Option.some.injEq] using hc
      subst C
      obtain ⟨i, hi, hsrc, hread⟩ := source_tick_read p c E rho x r B hf
      let st := ((fgsa p c).clock (V2.Run.stateBefore E rho i x) (p.actionTime r)).st
      have hst : storeAt p c E rho (i + 1) x = st := by
        change (V2.Run.stateBefore E rho (i + 1) x).st = st
        rw [(V2.Run.step_tick_eq E rho hi).1]
        exact tick_st (p := p) (c := c) E rho _ _ _
      have hlen : i + 1 ≤ rho.events.length := Nat.succ_le_of_lt (List.getElem?_eq_some_iff.mp hi).1
      have horig := (hL (i + 1) x hlen hx).2.2.2
      rw [hst] at horig
      have hround : p.round (st.slot p) = r := (fgsa_action_slot_round (c := c) _ r).2
      have hmem : eraseFG B ∈ sourceCandidates p st := by
        rw [fgSource_eq_jointSource] at hsrc
        exact (Finset.mem_filter.mp (FGSA.pickPair_some_spec _ _ hsrc).1).2 |> of_decide_eq_true
      have hfw : ∀ D ∈ sourceCandidates p st, D ∈ (fastWriteAt st (r * p.R)).getD [] := by
        intro D hD
        rw [sourceCandidates_def] at hD
        have hm := (Finset.mem_filter.mp hD).1
        rw [hround] at hm
        exact List.mem_toFinset.mp hm
      obtain ⟨j, hj, hjgate, hjpass, G, hjG, hBG, hfast⟩ := horig (r * p.R) _ (hfw _ hmem)
      have hG := (gateResultAt_eq_gateResult p c E rho hs hjgate).symm.trans hjG
      refine ⟨sourceCandidates p st, G, ?_, hmem, hG, ?_, ?_, j, hjgate, hjpass⟩
      · change Option.map _ (postClock E rho x (p.actionTime r)) = _
        rw [hread]; rfl
      · intro D hD
        obtain ⟨k, hk, hkgate, hkpass, G', hkG, hDG, _⟩ := horig (r * p.R) D (hfw D hD)
        have hG' := (gateResultAt_eq_gateResult p c E rho hs hkgate).symm.trans hkG
        have heq : G' = G := Option.some.inj (Option.some.inj (hG'.symm.trans hG))
        exact heq ▸ hDG
      · intro D hD
        obtain ⟨k, hk, hkgate, hkpass, G', hkG, hDG, hfastD⟩ := horig (r * p.R) D (hfw D hD)
        exact hfastD

private theorem source_row_action {j : Nat} {x : V} {r : Nat} {a : RowWire p.n}
    (ha : HonestRowAt p c E rho j x r a) :
    rho.events[j]? = some (.tick x (p.actionTime r)) ∧
      a.payload = (attest p
        ((fgsa p c).clock (V2.Run.stateBefore E rho j x) (p.actionTime r)).st
        (V2.Run.stateBefore E rho j x).record ⟨0, p.nPos⟩).1 := by
  obtain ⟨hx, hr, t, hj, hem⟩ := ha
  rcases a with ⟨auth, body⟩
  cases auth with
  | none => cases hr
  | proposer s => cases hr
  | seat label seat =>
    cases label with
    | head s => cases hr
    | fg r' =>
      have hrr : r' = r := Option.some.inj hr
      subst r'
      obtain ⟨_, ht, _, hb⟩ := (fgsa_emitsAt_row E rho j x t hj r seat body).mp hem
      subst t
      exact ⟨hj, hb⟩

/-- Earlier row emissions bound their source gate labels. -/
theorem sourceDiscipline_labelBound (hs : V2.ScheduleWellFormed E rho) :
    LabelBound p c E rho := by
  intro i x y r a t hx hi ha
  obtain ⟨j, hji, hrow⟩ := ha
  have hj := (source_row_action p c E rho hrow).1
  obtain ⟨hil, hie⟩ := List.getElem?_eq_some_iff.mp hi
  obtain ⟨hjl, hje⟩ := List.getElem?_eq_some_iff.mp hj
  have hk := (List.pairwise_iff_getElem.mp hs.sorted) j i hjl hil hji
  rw [hie, hje] at hk
  have ht : p.actionTime r ≤ t := V2.Engine.time_le_of_key_le _ _ hk
  have hd : (0 : Int) < p.Δ := p.deltaPos
  have htime : (4 : Int) * p.Δ * (r * p.R : Nat) + 6 * p.Δ ≤ t := ht
  refine ⟨?_, ?_, ?_⟩
  · dsimp only [labelBoundAt]
    rw [hi]
    dsimp only [V2.Event.time]
    have hdiv : (r * p.R : Nat) ≤ (t - 6 * p.Δ) / (4 * p.Δ) := by
      apply (Int.le_ediv_iff_mul_le (by omega)).mpr
      nlinarith
    exact_mod_cast Int.toNat_le_toNat hdiv
  · intro s ht'
    rw [ht'] at htime
    change 4 * p.Δ * (r * p.R : Nat) + 6 * p.Δ ≤ 4 * p.Δ * (s : Int) + 5 * p.Δ at htime
    have : (r * p.R : Nat) < (s : Int) := by nlinarith
    omega
  · intro s hspos ht'
    rcases ht' with ht' | ht' <;> rw [ht'] at htime
    · change 4 * p.Δ * (r * p.R : Nat) + 6 * p.Δ ≤ 4 * p.Δ * (s : Int) at htime
      have : (r * p.R : Nat) + 1 < (s : Int) := by nlinarith
      omega
    · change 4 * p.Δ * (r * p.R : Nat) + 6 * p.Δ ≤ 4 * p.Δ * (s : Int) + p.Δ at htime
      have : (r * p.R : Nat) + 1 < (s : Int) := by nlinarith
      omega

/-- A nonempty emitted name comes from the actual FG action source. -/
theorem sourceDiscipline_emittedName (hs : V2.ScheduleWellFormed E rho)
    (hL : LeaseOriginsAt p c E rho) {j : Nat} {x : V} {r : Nat}
    {a : RowWire p.n} {e : Height × BlockId}
    (ha : HonestRowAt p c E rho j x r a)
    (he : namedEntry a.payload.height_pair = some e) :
    ∃ C G, actionSourceFG p c E rho x r = some (some C) ∧
      e = (hOf p.E p.cfg C, (derive p.E p.cfg C).T_h.root) ∧
      FGBlock.Preceq (derive p.E p.cfg C).T_h C ∧
      gateResult p c E rho x (r * p.R) = some (some G) ∧
      Block.Preceq (eraseFG C) G ∧ fastAt p c E rho x (r * p.R) (eraseFG C) := by
  have hx := ha.1
  obtain ⟨hj, hb⟩ := source_row_action p c E rho ha
  let nd := V2.Run.stateBefore E rho j x
  let st := ((fgsa p c).clock nd (p.actionTime r)).st
  have hn : namedEntry (attest p st nd.record ⟨0, p.nPos⟩).1.height_pair = some e := by
    rw [hb] at he
    exact he
  obtain ⟨h, root, tm, hp⟩ : ∃ h root tm,
      (attest p st nd.record ⟨0, p.nPos⟩).1.height_pair = .vote h root tm := by
    cases hh : (attest p st nd.record ⟨0, p.nPos⟩).1.height_pair with
    | empty => rw [hh] at hn; cases hn
    | vote h root tm => exact ⟨h, root, tm, rfl⟩
  have hfields := KitFG.height_pair_vote_fields hp
  change Option.map (fun C => ((derive p.E p.cfg C).h, (derive p.E p.cfg C).T_h.root))
    (fgSource p st) = some (h, root) at hfields
  cases hsrc : fgSource p st with
  | none => rw [hsrc] at hfields; cases hfields
  | some C =>
    have hpair : ((derive p.E p.cfg C).h, (derive p.E p.cfg C).T_h.root) = (h, root) := by
      exact Option.some.inj (by simpa only [hsrc, Option.map_some] using hfields)
    have heq : e = (hOf p.E p.cfg C, (derive p.E p.cfg C).T_h.root) := by
      rw [hp] at hn
      exact (Option.some.inj hn).symm.trans hpair.symm
    have hread : actionSourceFG p c E rho x r = some (some C) := by
      rw [actionSourceFG_eq_round p c E rho hs hj]
      have hr := (fgsa_action_slot_round (p := p) (c := c) nd r).2
      change fgSource p st = some C at hsrc
      change some (deepest _) = some (some C)
      change deepest _ = some C at hsrc
      rw [hr] at hsrc
      exact congrArg some hsrc
    have herase : actionSource p c E rho x r = some (some (eraseFG C)) := by
      change Option.map (Option.map eraseFG) _ = _
      rw [hread]; rfl
    obtain ⟨X, G, hX, hCX, hG, hbelow, hfast, _⟩ :=
      sourceDiscipline_tSrc p c E rho hs hL x r _ hx herase
    exact ⟨C, G, hread, heq, KitFG.entry_preceq p.E p.cfg C, hG,
      hbelow _ hCX, hfast _ hCX⟩

/-- Source discipline without the quorum clauses, with the frozen F1.3 input. -/
theorem sourceDiscipline_base {Pt : Type} {pt : Pt}
    (hb : BasePrem p c E rho pt) (hL : LeaseOriginsAt p c E rho) :
    SourceDisciplineBaseAt p c E rho := by
  have hs := hb.set.valid.toScheduleWellFormed
  exact ⟨sourceDiscipline_tSrc p c E rho hs hL,
    sourceDiscipline_labelBound p c E rho hs,
    fun _ _ _ _ _ ha he => sourceDiscipline_emittedName p c E rho hs hL ha he⟩

private theorem source_stored_row (hv : V2.ExecutionValid E rho)
    (e : Fin p.n ≃ V)
    (he : ∀ r j, rho.seatOf (.base (.fg r)) j = e j)
    (hS : RStore p c E rho) {i : Nat} {x : V} {B : FGBlock (Fin p.n)}
    {a : Row (Fin p.n)} (hx : x ∈ rho.honest)
    (hB : B ∈ (storeAt p c E rho i x).fg.TF) (ha : a ∈ B.rows)
    (hh : e a.signer ∈ rho.honest) :
    ∃ r, ∃ wire : RowWire p.n,
      HonestRowBefore p c E rho i (e a.signer) r wire ∧
      wire.toRow? = some a ∧ wire.payload.height_pair = a.height_pair ∧
      ∃ s raw sup rows,
        (⟨.proposer s, .proposal (eraseFG B) raw sup rows⟩ : Wire p.n) ∈
          (storeAt p c E rho i x).proposals ∧ wire ∈ rows := by
  have hg : B ≠ .genesis := by intro h; subst B; cases ha
  obtain ⟨s, raw, sup, rows, hw, hrows⟩ :=
    stored_wire_of_block p _ (hS i x hx).1 (metaInv_stateBefore E rho i x) hB hg
  rw [hrows] at ha
  obtain ⟨wire, hwire, hdecode⟩ := List.mem_filterMap.mp ha
  obtain ⟨k, o, t, hki, hk, ho, hop, _⟩ := stored_proposal_delivered E rho i x _ hw
  have hopayload : o.payload = .proposal (eraseFG B) raw sup rows := by
    have := congrArg Signed.payload ho
    exact this
  have hcarry : (fgsa p c).carries o (ofRow p wire) := by
    rcases o with ⟨auth, payload⟩
    cases hopayload
    exact Or.inr (Or.inr (List.mem_map.mpr ⟨wire, hwire, rfl⟩))
  rcases wire with ⟨auth, body⟩
  cases auth with
  | none => cases hdecode
  | proposer s => cases hdecode
  | seat label seat =>
    cases label with
    | head s => cases hdecode
    | fg r =>
      have haeq : (⟨seat, body.height_pair, body.finality_pair⟩ : Row (Fin p.n)) = a :=
        Option.some.inj hdecode
      subst a
      have hholder : V2.Run.holder rho (ofRow p ⟨.seat (.fg r) seat, body⟩).auth =
          some (e seat) := congrArg some (he r seat)
      obtain ⟨t', htt, j, hj, hem⟩ :=
        hv.carried x o t ⟨k, hk⟩ _ hcarry (e seat) hh hholder
      have hjk := V2.Engine.tick_index_lt_delivery E rho hv.toScheduleWellFormed hj hk htt
      exact ⟨r, ⟨.seat (.fg r) seat, body⟩,
        ⟨j, Nat.lt_trans hjk hki, hh, rfl, t', hj, hem⟩, rfl, rfl,
        s, raw, sup, rows, hw, hwire⟩

private theorem source_quorum_honest [Fintype V]
    (e : Fin p.n ≃ V) (hq : Gen.Pure.FaultQ p.n (Gen.V2.faulty rho).card)
    {Q : Finset (Fin p.n)} (hQ : p.E.IsQuorum Q) :
    ∃ k ∈ Q, e k ∈ rho.honest := by
  classical
  let F := (Gen.V2.faulty rho).map e.symm.toEmbedding
  have hcap : p.E.toWeights.weightOf F < p.E.toWeights.q := by
    have hqeq : p.E.toWeights.q = Gen.Pure.qF p.n := KitFG.unit_toWeights_q p.n
    rw [hqeq]
    have hcard : p.E.toWeights.weightOf F = (Gen.V2.faulty rho).card := by
      rw [KitFG.toWeights_weightOf]
      change (∑ _ ∈ F, (1 : Nat)) = (Gen.V2.faulty rho).card
      simp only [Finset.sum_const, smul_eq_mul, mul_one, Finset.card_map, F]
    rw [hcard]
    exact hq.lt
  obtain ⟨k, hk, hf⟩ := Gen.Pure.quorum_honest p.E.toWeights F
    ((KitFG.isQuorum_toWeights_iff p.E Q).mpr hQ) hcap
  refine ⟨k, hk, ?_⟩
  by_contra hn
  apply hf
  exact Finset.mem_map.mpr ⟨e k, by simpa [Gen.V2.faulty] using hn, e.symm_apply_apply k⟩

/-- Every selected progress or target QC has an earlier honest source.
Finalization uses the target QC of its prior justification. -/
theorem sourceDiscipline_qcOrigin [Fintype V] {Pt : Type} {pt : Pt}
    (hb : SourceDisciplinePrem p c E rho pt)
    (hS : RStore p c E rho) (hL : LeaseOriginsAt p c E rho) :
    RQCOrigin p c E rho := by
  classical
  obtain ⟨e, he⟩ := fgsa_linked_seats rho hb.set.linked
  intro i x W hx hW
  dsimp only
  have origin (Q : Finset (Fin p.n))
      (rows : Fin p.n → FGBlock (Fin p.n) × Row (Fin p.n))
      (hQ : p.E.IsQuorum Q)
      (hr : ∀ k ∈ Q, FGBlock.Preceq (rows k).1 W ∧
        (rows k).2 ∈ (rows k).1.rows ∧ (rows k).2.signer = k ∧
        (rows k).2.height_pair ≠ .empty) :
      ∃ k ∈ Q, ∃ y r, ∃ wire : RowWire p.n,
        HonestRowBefore p c E rho i y r wire ∧ wire.toRow? = some (rows k).2 ∧
        (∃ s raw sup ws,
          (⟨.proposer s, .proposal (eraseFG (rows k).1) raw sup ws⟩ : Wire p.n) ∈
            (storeAt p c E rho i x).proposals ∧ wire ∈ ws) ∧
        ∃ C G, actionSourceFG p c E rho y r = some (some C) ∧
          namedEntry (rows k).2.height_pair =
            some (hOf p.E p.cfg C, (derive p.E p.cfg C).T_h.root) ∧
          FGBlock.Preceq (derive p.E p.cfg C).T_h C ∧
          gateResult p c E rho y (r * p.R) = some (some G) ∧
          Block.Preceq (eraseFG C) G ∧ fastAt p c E rho y (r * p.R) (eraseFG C) := by
    obtain ⟨k, hk, hhon⟩ := source_quorum_honest p c rho e hb.quorum hQ
    obtain ⟨hc, ha, hsign, hne⟩ := hr k hk
    have hcstore := KitFG.ancestor_closed_of_parent_closed _
      (hS i x hx).1.fg.closed W hW _ hc
    have hhon' : e (rows k).2.signer ∈ rho.honest := by rw [hsign]; exact hhon
    obtain ⟨r, wire, hbefore, hdecode, hheight, hwire⟩ :=
      source_stored_row p c E rho hb.set.valid e he hS hx hcstore ha hhon'
    obtain ⟨pair, hp⟩ : ∃ pair, namedEntry (rows k).2.height_pair = some pair := by
      cases hh : (rows k).2.height_pair with
      | empty => exact (hne hh).elim
      | vote h root tm => exact ⟨(h, root), rfl⟩
    have hwname : namedEntry wire.payload.height_pair = some pair := hheight ▸ hp
    obtain ⟨j, hj, hemit⟩ := hbefore
    obtain ⟨C, G, hsrc, hpair, hpre, hgate, hbelow, hfast⟩ :=
      sourceDiscipline_emittedName p c E rho hb.set.valid.toScheduleWellFormed hL hemit hwname
    exact ⟨k, hk, e (rows k).2.signer, r, wire, ⟨j, hj, hemit⟩,
      hdecode, hwire, C, G, hsrc, hp.trans (congrArg some hpair), hpre, hgate, hbelow, hfast⟩
  refine ⟨?_, ?_, ?_⟩
  · intro m X Q rows hm hlt hX hheight hQ hr
    apply origin Q rows hQ
    intro k hk
    obtain ⟨hc, ha, hs, hp⟩ := hr k hk
    refine ⟨hc, ha, hs, ?_⟩
    intro hempty
    rw [hempty] at hp
    cases hp
  · intro Q rows hnz hQ hr
    apply origin Q rows hQ
    intro k hk
    obtain ⟨hc, ha, hs, hp⟩ := hr k hk
    exact ⟨hc, ha, hs, by rw [hp]; exact NamedHeightPair.noConfusion⟩
  · intro hF
    have hnz : (derive p.E p.cfg W).h_F ≠ 0 :=
      fun h => hF (KitFG.finalized_zero_is_genesis p.E p.cfg W h)
    obtain ⟨C, hCW, hCJ, hCh⟩ := KitFG.provenance_finality p.E p.cfg W hnz
    obtain ⟨Q, hQ, hr⟩ := KitFG.justification_certificate p.E p.cfg C
      (fun h => hnz (hCh.symm.trans h))
    choose carrier a hc ha hs hp using fun k hk => hr k hk
    let rows : Fin p.n → FGBlock (Fin p.n) × Row (Fin p.n) :=
      fun k => if hk : k ∈ Q then (carrier k hk, a k hk) else
        (.genesis, ⟨k, .empty, none⟩)
    have hrows : ∀ k ∈ Q, FGBlock.Preceq (rows k).1 C ∧
        (rows k).2 ∈ (rows k).1.rows ∧ (rows k).2.signer = k ∧
        (rows k).2.height_pair =
          .vote (derive p.E p.cfg C).h_j (derive p.E p.cfg C).J.root false := by
      intro k hk
      simp only [rows, dite_eq_left hk]
      exact ⟨hc k hk, ha k hk, hs k hk, hp k hk⟩
    refine ⟨C, hCW, hCJ, hCh, Q, rows, hQ, hrows, ?_⟩
    apply origin Q rows hQ
    intro k hk
    obtain ⟨hc', ha', hs', hp'⟩ := hrows k hk
    exact ⟨KitFG.preceq_trans hc' hCW, ha', hs',
      by rw [hp']; exact NamedHeightPair.noConfusion⟩

private theorem source_named_quorum [Fintype V] {Pt : Type} {pt : Pt}
    (hb : SourceDisciplinePrem p c E rho pt) (hS : RStore p c E rho)
    {i : Nat} {x : V} {W : FGBlock (Fin p.n)} (hx : x ∈ rho.honest)
    (hW : W ∈ (storeAt p c E rho i x).fg.TF) (m : Nat) (root : BlockId)
    (Q : Finset (Fin p.n)) (hQ : p.E.IsQuorum Q)
    (hr : ∀ k ∈ Q, ∃ carrier a, FGBlock.Preceq carrier W ∧
      a ∈ carrier.rows ∧ a.signer = k ∧ namedEntry a.height_pair = some (m, root)) :
    ∃ y r, ∃ wire : RowWire p.n, HonestRowBefore p c E rho i y r wire ∧
      namedEntry wire.payload.height_pair = some (m, root) := by
  obtain ⟨e, he⟩ := fgsa_linked_seats rho hb.set.linked
  obtain ⟨k, hk, hhon⟩ := source_quorum_honest p c rho e hb.quorum hQ
  obtain ⟨carrier, a, hc, ha, hsign, hp⟩ := hr k hk
  have hcstore := KitFG.ancestor_closed_of_parent_closed _
    (hS i x hx).1.fg.closed W hW _ hc
  have hhon' : e a.signer ∈ rho.honest := by rw [hsign]; exact hhon
  obtain ⟨r, wire, hbefore, _, hheight, _⟩ :=
    source_stored_row p c E rho hb.set.valid e he hS hx hcstore ha hhon'
  exact ⟨e a.signer, r, wire, hbefore, hheight ▸ hp⟩

/-- Each non-genesis certified entry has an earlier honest name. -/
theorem sourceDiscipline_strat [Fintype V] {Pt : Type} {pt : Pt}
    (hb : SourceDisciplinePrem p c E rho pt)
    (hS : RStore p c E rho) (hL : LeaseOriginsAt p c E rho) : RStrat p c E rho := by
  intro i x W hx hW e he hne
  obtain ⟨U, hUW, hentry⟩ := he
  have just (D : FGBlock (Fin p.n)) (hDW : FGBlock.Preceq D W)
      (hne : (derive p.E p.cfg D).J ≠ .genesis) :
      ∃ y r, ∃ wire : RowWire p.n, HonestRowBefore p c E rho i y r wire ∧
        namedEntry wire.payload.height_pair =
          some (hOf p.E p.cfg (derive p.E p.cfg D).J, (derive p.E p.cfg D).J.root) := by
    have hnz : (derive p.E p.cfg D).h_j ≠ 0 :=
      fun h => hne (KitFG.justified_zero_is_genesis p.E p.cfg D h)
    obtain ⟨Q, hQ, hr⟩ := KitFG.justification_certificate p.E p.cfg D hnz
    have hh := KitFG.entry_height p.E p.cfg D hnz
    apply source_named_quorum p c E rho hb hS hx hW _ _ Q hQ
    intro k hk
    obtain ⟨carrier, a, hc, ha, hs, hp⟩ := hr k hk
    refine ⟨carrier, a, KitFG.preceq_trans hc hDW, ha, hs, ?_⟩
    rw [hp]
    change some (_, _) = some (_, _)
    rw [show hOf p.E p.cfg (derive p.E p.cfg D).J = _ from hh]
  rcases hentry with hJ | hF | ⟨hT, hlt⟩
  · subst e
    exact just U hUW hne
  · subst e
    have hnz : (derive p.E p.cfg U).h_F ≠ 0 :=
      fun h => hne (KitFG.finalized_zero_is_genesis p.E p.cfg U h)
    obtain ⟨D, hDU, hDJ, _⟩ := KitFG.provenance_finality p.E p.cfg U hnz
    rw [← hDJ] at hne ⊢
    exact just D (KitFG.preceq_trans hDU hUW) hne
  · subst e
    obtain ⟨X, hXW, hXh, Q, hQ, hr⟩ := KitFG.height_crossing p.E p.cfg W
      (derive p.E p.cfg U).h (KitFG.one_le_h p.E p.cfg U) hlt
    obtain ⟨y, r, wire, hbefore, hname⟩ :=
      source_named_quorum p c E rho hb hS hx hW (derive p.E p.cfg U).h X.root Q hQ
        (by
          intro k hk
          obtain ⟨carrier, a, hc, ha, hs, hp⟩ := hr k hk
          refine ⟨carrier, a, hc, ha, hs, ?_⟩
          cases hh : a.height_pair with
          | empty => rw [hh] at hp; cases hp
          | vote m root tm =>
            rw [hh] at hp
            have hp' : m = (derive p.E p.cfg U).h ∧ root = X.root := by
              simpa only [NamedHeightPair.matchesEntry, Bool.and_eq_true, beq_iff_eq,
                decide_eq_true_eq] using hp
            exact congrArg some (Prod.ext hp'.1 hp'.2))
    obtain ⟨j, hj, hem⟩ := hbefore
    obtain ⟨C, G, _, hpair, _, _, _, _⟩ :=
      sourceDiscipline_emittedName p c E rho hb.set.valid.toScheduleWellFormed hL hem hname
    have hXC : X = (derive p.E p.cfg C).T_h :=
      FGBlock.root_injective (congrArg Prod.snd hpair)
    have hXentry : (derive p.E p.cfg X).T_h = X := by
      rw [hXC]
      exact KitFG.entry_idem p.E p.cfg C
    have hTX : (derive p.E p.cfg U).T_h = X := by
      rcases KitFG.preceq_total_of_common hUW hXW with hUX | hXU
      · exact (KitFG.entry_eq_on_plateau p.E p.cfg hUX hXh.symm).trans hXentry
      · exact (KitFG.entry_eq_on_plateau p.E p.cfg hXU hXh).symm.trans hXentry
    refine ⟨y, r, wire, ⟨j, hj, hem⟩, ?_⟩
    rw [hTX]
    change namedEntry wire.payload.height_pair = some ((derive p.E p.cfg X).h, X.root)
    rw [hXh]
    exact hname

/-- The source-discipline conclusion, with the frozen F1.1 and F1.3 inputs. -/
theorem sourceDiscipline_at [Fintype V] {Pt : Type} {pt : Pt}
    (hb : SourceDisciplinePrem p c E rho pt)
    (hS : RStore p c E rho) (hL : LeaseOriginsAt p c E rho) :
    SourceDisciplineAt p c E rho :=
  ⟨sourceDiscipline_base p c E rho (pt := pt) ⟨hb.set⟩ hL,
    sourceDiscipline_strat p c E rho hb hS hL,
    sourceDiscipline_qcOrigin p c E rho hb hS hL⟩

/-- The G1 genesis premise and exact earlier names give the source frame. -/
theorem sourceDiscipline_srcFrameAbove [Fintype V] {Pt : Type} {pt : Pt}
    (hb : SourceDisciplinePrem p c E rho pt)
    (hS : RStore p c E rho) (hL : LeaseOriginsAt p c E rho) :
    SrcFrameAboveStmt p c E rho := by
  have hstrat := sourceDiscipline_strat p c E rho hb hS hL
  intro Φ c₀ hclosed hg i x hx hrows
  have hcert : ∀ W ∈ (storeAt p c E rho i x).fg.TF,
      ∀ e ∈ certified p W, c₀ ≤ hOf p.E p.cfg e → Φ e := by
    intro W hW e he hheight
    by_cases hgen : e = .genesis
    · subst e; exact hg hheight
    · obtain ⟨y, r, a, ha, hname⟩ := hstrat i x W hx hW e he hgen
      exact hrows y r a e ha hname hheight
  refine ⟨hcert, ?_⟩
  let st := storeAt p c E rho i x
  have hinv := (hS i x hx).1.fg
  obtain ⟨K, hK, hKF⟩ := hinv.Fcar
  have hF : c₀ ≤ hOf p.E p.cfg st.fg.F → Φ st.fg.F := by
    intro hh
    apply hcert K hK st.fg.F
    · exact ⟨K, KitFG.preceq_refl K, Or.inr (Or.inl hKF.symm)⟩
    · exact hh
  have hFK : FGBlock.Preceq st.fg.F (derive p.E p.cfg K).J := by
    rw [← hKF]
    exact (KitFG.chainOrder_derive p.E p.cfg K).finalized_preceq_justified
  obtain ⟨D, hD, _, hpair, _⟩ := KitFG.lexMax_spec p.E p.cfg st.fg.F st.fg.TF
    (fun X Y _ _ hroot => FGBlock.root_injective hroot) ⟨K, hK, hFK⟩
  have hJ : st.fg.J = (derive p.E p.cfg D).J := congrArg Prod.snd (hinv.pair.trans hpair)
  have hj : c₀ ≤ hOf p.E p.cfg st.fg.J → Φ st.fg.J := by
    intro hh
    apply hcert D hD st.fg.J
    · exact ⟨D, KitFG.preceq_refl D, Or.inl hJ⟩
    · exact hh
  change FrameBelow p Φ c₀ (storeControls p.E p.cfg st.fg)
  refine ⟨hF, hj, ?_⟩
  change c₀ ≤ hOf p.E p.cfg (if (storeControls p.E p.cfg st.fg).rootIsJ then
      st.fg.J else st.fg.F) → Φ (if (storeControls p.E p.cfg st.fg).rootIsJ then
      st.fg.J else st.fg.F)
  cases (storeControls p.E p.cfg st.fg).rootIsJ <;> assumption

end AvailableChain.FGSA.Run
end
