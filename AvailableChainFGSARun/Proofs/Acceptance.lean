module
public import AvailableChainFGSARun.Statements.Acceptance
public import AvailableChainFGSARun.Proofs.Hooks
public import AvailableChainFGSA.Proofs.CrossNode

public section

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG

variable {p : Params} {In : Type} {c : AppCodec In}

/-- Slot admission is equivalent to reaching the slot threshold. -/
theorem fgsa_slot_threshold_iff (p : Params) (t : Time) (ht : 0 ≤ t) (s : Nat) :
    s ≤ p.slotOf t ↔ 4 * p.Δ * (s : Int) ≤ t := by
  have hd : (0 : Int) < 4 * p.Δ := mul_pos (by decide) p.deltaPos
  have hdiv : 0 ≤ t / (4 * p.Δ) := Int.ediv_nonneg ht (le_of_lt hd)
  change s ≤ (t / (4 * p.Δ)).toNat ↔ _
  rw [← Int.ofNat_le, Int.toNat_of_nonneg hdiv]
  simpa only [Int.mul_comm] using (Int.le_ediv_iff_mul_le hd (a := (s : Int)) (b := t))

/-- Row admission is equivalent to reaching the round threshold. -/
theorem fgsa_round_threshold_iff (p : Params) (t : Time) (ht : 0 ≤ t) (r : Nat) :
    r ≤ p.round (p.slotOf t) ↔ 4 * p.Δ * ((r * p.R : Nat) : Int) ≤ t := by
  have hR : 0 < p.R := by have := p.RLarge; omega
  change r ≤ p.slotOf t / p.R ↔ _
  rw [Nat.le_div_iff_mul_le hR, fgsa_slot_threshold_iff p t ht]

/-- The threshold clock for the generic receipt laws. -/
def fgsaTimelyClock (p : Params) (c : AppCodec In) :
    Gen.V2.Duty.TimelyClock (fgsa p c) (fgsaTimely p) where
  actTime := fgsaAdmissionTime p
  clockOf nd := nd.st.base.now
  timely_iff _ _ := Iff.rfl
  clock := fgsaClock p c
  clockOf_eq nd := (fgsa_clock_now p c nd).symm

private theorem t77_time_nonneg (p : Params) (o : Obj p) : 0 ≤ fgsaAdmissionTime p o := by
  have h : 0 < p.Δ := p.deltaPos
  obtain ⟨auth, payload⟩ := o
  rcases auth with ⟨((_ | _) | _), _⟩ | _ <;>
    dsimp only [fgsaAdmissionTime] <;> positivity

private theorem t77_vote_timely {nd : Node p} {o : Obj p} {s : Slot} {i : Fin p.n} {b : Block}
    (hd : (toWire p o).decode = some (.vote s i b)) (ht : fgsaTimely p nd o) :
    s ≤ nd.st.slot p := by
  have ho : o = ofWire p ⟨.seat (.head s) i, .head b⟩ := by
    apply toWire_injective
    simpa using decode_eq_vote.mp hd
  have ht' : 4 * p.Δ * (s : Int) ≤ nd.st.base.now := by
    rw [ho] at ht
    exact ht
  exact (fgsa_slot_threshold_iff p _ ((t77_time_nonneg p o).trans ht) s).2 ht'

private theorem t77_block_timely {nd : Node p} {o : Obj p} {s : Slot} {b : Block}
    {raw sup : List (HeadWire p.n)} {rows : List (RowWire p.n)}
    (hd : (toWire p o).decode = some (.block s b raw sup rows)) (ht : fgsaTimely p nd o) :
    s ≤ nd.st.slot p := by
  have ho : o = ofWire p ⟨.proposer s, .proposal b raw sup rows⟩ := by
    apply toWire_injective
    simpa using decode_eq_block.mp hd
  have ht' : 4 * p.Δ * (s : Int) ≤ nd.st.base.now := by
    rw [ho] at ht
    exact ht
  exact (fgsa_slot_threshold_iff p _ ((t77_time_nonneg p o).trans ht) s).2 ht'

private theorem t77_grid_partition (st : GridCO.State p.n) (s : Slot) (i : Fin p.n) (b : Block)
    (ht : s ≤ (st.now / (4 * p.Δ)).toNat) :
    let w : GridCO.Wire p.n := ⟨.seat s i, .head b⟩
    w ∈ (GridCO.admitVote p.toParams.engine st w).votes ∨
      GridCO.excludes p.toParams.engine (GridCO.admitVote p.toParams.engine st w) w = true := by
  intro w
  by_cases hm : w ∈ st.votes
  · exact Or.inl (Internal.grid_admitVote_votes_subset st w hm)
  · by_cases hx : GridCO.excludes p.toParams.engine st w = true
    · exact Or.inr (Internal.grid_admitVote_keeps st w w hx)
    · have h := (Internal.grid_excludes_head_iff st s i b).not.mp hx
      change ¬ (w ∉ st.votes ∧ (s + 1 < (st.now / (4 * p.Δ)).toNat ∨
        GridCO.equivocates (GridCO.votesAt st s) i = true)) at h
      have hold : ¬ s < (st.now / (4 * p.Δ)).toNat - 1 := by
        intro he
        apply h
        exact ⟨hm, Or.inl (Internal.lt_sub_one_iff_add_one_lt _ _ |>.mp he)⟩
      have heq : GridCO.equivocates (GridCO.votesAt st s) i = false := by
        cases he : GridCO.equivocates (GridCO.votesAt st s) i
        · rfl
        · exact (h ⟨hm, Or.inr he⟩).elim
      left
      unfold GridCO.admitVote
      change w ∈ (if s < (st.now / (4 * p.Δ)).toNat - 1 ||
          (st.now / (4 * p.Δ)).toNat < s || decide (w ∈ st.votes) ||
          GridCO.equivocates (GridCO.votesAt st s) i then st else
        { st with votes := st.votes ++ [w], voteStamp := st.voteStamp ++ [(w, st.now)] }).votes
      simp [hold, Nat.not_lt.mpr ht, hm, heq]

private theorem t77_row_partition (st : State p.n) (i : Fin p.n) (body : RowPayload) :
    let a : RowWire p.n := ⟨.seat .fg i, body⟩
    a ∈ (admitRow p st a).rowPool := by
  dsimp only
  by_cases hm : (⟨.seat .fg i, body⟩ : RowWire p.n) ∈ st.rowPool
  · simpa only [admitRow, RowWire.decode?, ite_eq_left hm] using hm
  · simp [admitRow, RowWire.decode?, hm]

private theorem t77_grid_settled_fold (raw : List (GridCO.HeadWire p.n))
    (st : GridCO.State p.n) (w : GridCO.Wire p.n)
    (h : w ∈ st.votes ∨ GridCO.excludes p.toParams.engine st w = true) :
    w ∈ (raw.foldl (fun v h => GridCO.admitVote p.toParams.engine v (GridCO.fromHead h)) st).votes ∨
      GridCO.excludes p.toParams.engine
        (raw.foldl (fun v h => GridCO.admitVote p.toParams.engine v
          (GridCO.fromHead h)) st) w = true := by
  exact h.imp (fun hm => Internal.grid_fold_votes_subset raw st hm)
    (Internal.grid_fold_keeps raw st w)

private theorem t77_head_fold_partition (raw : List (HeadWire p.n))
    (st : GridCO.State p.n) (s : Slot) (i : Fin p.n) (b : Block)
    (hm : (⟨.seat (.head s) i, b⟩ : HeadWire p.n) ∈ raw)
    (ht : s ≤ (st.now / (4 * p.Δ)).toNat) :
    let W := (raw.map baseHead).foldl
      (fun v h => GridCO.admitVote p.toParams.engine v (GridCO.fromHead h)) st
    (⟨.seat s i, .head b⟩ : GridCO.Wire p.n) ∈ W.votes ∨
      GridCO.excludes p.toParams.engine W ⟨.seat s i, .head b⟩ = true := by
  induction raw generalizing st with
  | nil => simp at hm
  | cons h raw ih =>
    simp only [List.mem_cons] at hm
    simp only [List.map_cons, List.foldl_cons]
    rcases hm with he | hm
    · subst h
      exact t77_grid_settled_fold (raw.map baseHead) _ _ (t77_grid_partition st s i b ht)
    · apply ih _ hm
      rw [Internal.grid_admitVote_now]
      exact ht

private theorem t77_row_settled_fold (rows : List (RowWire p.n)) (st : State p.n)
    (i : Fin p.n) (body : RowPayload)
    (h : (⟨.seat .fg i, body⟩ : RowWire p.n) ∈ st.rowPool) :
    (⟨.seat .fg i, body⟩ : RowWire p.n) ∈ (rows.foldl (admitRow p) st).rowPool := by
  obtain ⟨pool, he, hp⟩ := foldl_admitRow_eq p rows st
  rw [he]
  exact hp.subset h

private theorem t77_row_fold_partition (rows : List (RowWire p.n)) (st : State p.n)
    (i : Fin p.n) (body : RowPayload)
    (hm : (⟨.seat .fg i, body⟩ : RowWire p.n) ∈ rows) :
    (⟨.seat .fg i, body⟩ : RowWire p.n) ∈ (rows.foldl (admitRow p) st).rowPool := by
  induction rows generalizing st with
  | nil => simp at hm
  | cons a rows ih =>
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hm with he | hm
    · subst a
      exact t77_row_settled_fold rows _ i body (t77_row_partition st i body)
    · exact ih _ hm

private theorem t77_self_accepts (nd : Node p) (o : Obj p) (hInv : CStoreInv p nd.st)
    (hw : FGSA.wellFormed p (toWire p o) = true) (hd : depsS p nd.st o = true)
    (ht : fgsaTimely p nd o) :
    processedS p (FGSA.process p nd.st (toWire p o)) o = true ∨
      excludesS p (FGSA.process p nd.st (toWire p o)) o = true := by
  cases he : (toWire p o).decode with
  | none =>
    dsimp only [FGSA.wellFormed] at hw
    rw [he] at hw
    contradiction
  | some m =>
    cases m with
    | vote s i b =>
      have ht' := t77_vote_timely he ht
      have ha := t77_grid_partition nd.st.base s i b ht'
      dsimp only [FGSA.process, processedS, excludesS]
      rw [he]
      change decide (_ ∈ _) = true ∨ _ = true
      exact ha.imp decide_eq_true id
    | row i body =>
      have ha := t77_row_partition nd.st i body
      have hw' := decode_eq_row.mp he
      left
      dsimp only [FGSA.process, processedS]
      rw [he, hw']
      exact decide_eq_true ha
    | block s b raw sup rows =>
      have hw' := decode_eq_block.mp he
      have wf : FGSA.wellFormed p ⟨.proposer s, .proposal b raw sup rows⟩ = true := hw' ▸ hw
      dsimp only [FGSA.wellFormed, Wire.decode] at wf
      have hs : s = b.slot := by
        exact beq_iff_eq.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp
          (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp
            (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp wf).1).1).1).1).1).2
      have hslot : b.slot ≤ nd.st.slot p := hs ▸ t77_block_timely he ht
      have hdep : (parentFG nd.st b).isSome = true := by
        have ho : o = ofWire p ⟨.proposer s, .proposal b raw sup rows⟩ := by
          apply toWire_injective
          simpa only [toWire_ofWire] using hw'
        rw [ho] at hd
        exact hd
      obtain ⟨P, hP⟩ := Option.isSome_iff_exists.mp hdep
      have hPe := ((parentFG_spec nd.st hInv.rootInj b P).1 hP).2
      by_cases hv : rowsValidForParent p P b.slot rows = true
      · by_cases hm : ∃ Y ∈ nd.st.fg.TF, Y.root = b.root
        · left
          obtain ⟨Y, hY, hr⟩ := hm
          dsimp only [processedS]
          rw [he]
          simp only [decide_eq_true_eq]
          exact ⟨Y, (process_cumulative p nd.st (toWire p o)).1 hY, hr⟩
        · by_cases hc : Block.Compatible (eraseFG nd.st.fg.F) b
          · change _ = true at hc
            simp only [Block.compatible, Bool.or_eq_true] at hc
            rcases hc with hc | hc
            · have hpar : b.parent ∈ nd.st.base.blocks :=
                (hInv.baseTree _).2 ⟨P, ((parentFG_spec nd.st hInv.rootInj b P).1 hP).1, hPe⟩
              have hfresh : ∀ c ∈ nd.st.base.blocks, c.root ≠ b.root := by
                intro c hC hr
                obtain ⟨Y, hY, rfl⟩ := (hInv.baseTree c).1 hC
                exact hm ⟨Y, hY, (eraseFG_root Y).symm.trans hr⟩
              obtain ⟨_, Q, hQ, hmem⟩ := admitBlock_sufficient p nd.st hInv s b raw sup rows
                wf hpar hslot hfresh hc (fun Q hQ => by
                  have heq := Option.some.inj (hQ.symm.trans hP)
                  subst Q
                  exact hv)
              left
              dsimp only [processedS]
              rw [he]
              simp only [decide_eq_true_eq]
              rw [hw']
              refine ⟨fgBlock Q b rows, hmem, ?_⟩
              exact fgBlock_root Q b rows
                (by intro hg
                    have hb := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp
                      (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp
                        (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp wf).1).1).1).1).1).1
                    exact (bne_iff_ne.mp hb) hg)
                ((parentFG_spec nd.st hInv.rootInj b Q).1 hQ).2
                (Bool.and_eq_true_iff.mp wf).2
            · obtain ⟨Y, hY, heY, _⟩ := eraseFG_ancestor_preceq hInv.fg.closed hInv.fg.Fmem hc
              exact (hm ⟨Y, hY, by rw [← eraseFG_root, heY]⟩).elim
          · right
            apply excludesS_process nd.st (toWire p o) o
            rw [excludesS_of_block nd.st he]
            have hb : blockExcluded nd.st b = true := by
              simpa [blockExcluded, activeCompatible, Block.Compatible,
                Block.compatible, Bool.or_comm] using hc
            simp [hb]
      · right
        apply excludesS_process nd.st (toWire p o) o
        rw [excludesS_of_block nd.st he]
        simp [invalidForParent, hP, hv]

/-- Every timely, ready handled object is processed or excluded after delivery. -/
theorem fgsaAcceptance (p : Params) (c : AppCodec In) :
    Gen.V2.Duty.AcceptanceLaw (fgsa p c) (fgsaTimely p) (fgsaAcceptanceInv p) where
  accepts nd o' o hInv hh hw hd ht := by
    change CStoreInv p nd.st at hInv
    change handlesS p nd.st o' o at hh
    change FGSA.wellFormed p (toWire p o) = true at hw
    change depsS p nd.st o = true at hd
    change processedS p (FGSA.process p nd.st (toWire p o')) o = true ∨
      excludesS p (FGSA.process p nd.st (toWire p o')) o = true
    rcases hh with he | hh
    · subst o'
      exact t77_self_accepts nd o hInv hw hd ht
    · generalize hdecode : (toWire p o').decode = d at hh
      cases d with
      | none => exact hh.elim
      | some m =>
        cases m with
        | vote s i b => exact hh.elim
        | row i body => exact hh.elim
        | block s b raw sup rows =>
          obtain ⟨⟨P, hP, hacc⟩, hm⟩ := hh
          let st1 : State p.n := { nd.st with
            base := GridCO.admitProposal p.toParams.engine nd.st.base (baseProposal s b raw sup) b
              (raw.map baseHead)
            fg := on_block p.E p.cfg nd.st.fg (fgBlock P b rows)
            proposals := nd.st.proposals ++ [⟨.proposer s, .proposal b raw sup rows⟩] }
          let st2 := if st1.fg.F = nd.st.fg.F then st1 else reconcile st1
          have hp : FGSA.process p nd.st (toWire p o') = rows.foldl (admitRow p) st2 := by
            dsimp only [FGSA.process]
            rw [hdecode]
            dsimp only [admitBlock]
            rw [hP]
            simp only [hacc, ite_true]
            rfl
          have hn : st2.base.now = nd.st.base.now :=
            (Internal.ite_reconcile st1 nd.st).2.1.trans
              (Internal.grid_admitProposal_now nd.st.base _ b (raw.map baseHead))
          rw [hp]
          rcases hm with hm | hm
          · obtain ⟨h, hmem, rfl⟩ := List.mem_map.mp hm
            obtain ⟨auth, x⟩ := h
            rcases auth with ⟨(_ | _), i⟩ | s' | _
            · rename_i r
              have hdt : (toWire p (ofHead p ⟨.seat (.head r) i, x⟩)).decode =
                  some (.vote r i x) := by rw [toWire_ofHead]; rfl
              have ht' := t77_vote_timely hdt ht
              let seed : GridCO.State p.n := { nd.st.base with
                blocks := nd.st.base.blocks ++ [b]
                blockStamp := nd.st.base.blockStamp ++ [(b, nd.st.base.now)]
                proposals := nd.st.base.proposals ++ [baseProposal s b raw sup] }
              let W := (raw.map baseHead).foldl
                (fun v h => GridCO.admitVote p.toParams.engine v (GridCO.fromHead h)) seed
              have hbase :=
                (admitProposal_base_view p nd.st hInv.toInv0 s b raw sup P rows hP hacc).1
              have hv : st2.base.votes = W.votes :=
                (Internal.ite_reconcile st1 nd.st).1.trans (congrArg GridCO.State.votes hbase)
              have hnW : st2.base.now = W.now := hn.trans (Internal.grid_fold_now _ seed).symm
              have ha := t77_head_fold_partition raw seed r i x hmem ht'
              change _ ∈ W.votes ∨ GridCO.excludes p.toParams.engine W _ = true at ha
              dsimp only [processedS, excludesS]
              rw [toWire_ofHead]
              dsimp only [Wire.decode, baseVote, baseHead, HeadWire.decode?, GridCO.fromHead]
              rw [Internal.foldl_admitRow_base, hv,
                Internal.grid_excludes_congr hv hnW]
              exact ha.imp (fun hm => decide_eq_true hm) id
            · (dsimp only [FGSA.wellFormed] at hw;
                rw [toWire_ofHead] at hw;
                contradiction)
            · (dsimp only [FGSA.wellFormed] at hw;
                rw [toWire_ofHead] at hw;
                contradiction)
            · (dsimp only [FGSA.wellFormed] at hw;
                rw [toWire_ofHead] at hw;
                contradiction)
          · obtain ⟨a, hmem, rfl⟩ := List.mem_map.mp hm
            obtain ⟨auth, body⟩ := a
            rcases auth with ⟨(_ | _), i⟩ | s' | _
            · (dsimp only [FGSA.wellFormed] at hw;
                rw [toWire_ofRow] at hw;
                contradiction)
            · left
              dsimp only [processedS]
              rw [toWire_ofRow]
              exact decide_eq_true (t77_row_fold_partition rows st2 i body hmem)
            · (dsimp only [FGSA.wellFormed] at hw;
                rw [toWire_ofRow] at hw;
                contradiction)
            · (dsimp only [FGSA.wellFormed] at hw;
                rw [toWire_ofRow] at hw;
                contradiction)

private theorem t77_grid_future_absent (st : GridCO.State p.n) (r : Slot) (i : Fin p.n)
    (b : Block) (o : GridCO.Wire p.n) (hf : (st.now / (4 * p.Δ)).toNat < r)
    (hm : (⟨.seat r i, .head b⟩ : GridCO.Wire p.n) ∉ st.votes) :
    (⟨.seat r i, .head b⟩ : GridCO.Wire p.n) ∉
      (GridCO.admitVote p.toParams.engine st o).votes := by
  by_cases ho : o = ⟨.seat r i, .head b⟩
  · subst o
    unfold GridCO.admitVote
    change _ ∉ (if r < (st.now / (4 * p.Δ)).toNat - 1 ||
        (st.now / (4 * p.Δ)).toNat < r || decide (_ ∈ st.votes) ||
        GridCO.equivocates (GridCO.votesAt st r) i then st else _).votes
    simp [hf, hm]
  · obtain ⟨auth, payload⟩ := o
    cases auth <;> cases payload <;> dsimp only [GridCO.admitVote]
    all_goals first
      | exact hm
      | split_ifs
        · exact hm
        · simp only [List.mem_append, List.mem_singleton, not_or]
          exact ⟨hm, fun he => ho he.symm⟩

private theorem t77_grid_future_fold (raw : List (GridCO.HeadWire p.n))
    (st : GridCO.State p.n) (r : Slot) (i : Fin p.n) (b : Block)
    (hf : (st.now / (4 * p.Δ)).toNat < r)
    (hm : (⟨.seat r i, .head b⟩ : GridCO.Wire p.n) ∉ st.votes) :
    (⟨.seat r i, .head b⟩ : GridCO.Wire p.n) ∉
      (raw.foldl (fun v h => GridCO.admitVote p.toParams.engine v
        (GridCO.fromHead h)) st).votes := by
  induction raw generalizing st with
  | nil => exact hm
  | cons h raw ih =>
    apply ih _ _ (t77_grid_future_absent st r i b _ hf hm)
    rwa [Internal.grid_admitVote_now]

private theorem t77_grid_future_proposal (st : GridCO.State p.n) (r : Slot) (i : Fin p.n)
    (b : Block) (o : GridCO.Wire p.n) (B : Block) (raw : List (GridCO.HeadWire p.n))
    (hf : (st.now / (4 * p.Δ)).toNat < r)
    (hm : (⟨.seat r i, .head b⟩ : GridCO.Wire p.n) ∉ st.votes) :
    (⟨.seat r i, .head b⟩ : GridCO.Wire p.n) ∉
      (GridCO.admitProposal p.toParams.engine st o B raw).votes := by
  unfold GridCO.admitProposal
  dsimp only
  split_ifs
  · exact hm
  · exact t77_grid_future_fold raw _ r i b hf hm

private theorem t77_future_head_process (st : State p.n) (r : Slot) (i : Fin p.n)
    (b : Block) (o : Wire p.n) (hf : st.slot p < r)
    (hm : (⟨.seat r i, .head b⟩ : GridCO.Wire p.n) ∉ st.base.votes) :
    (⟨.seat r i, .head b⟩ : GridCO.Wire p.n) ∉ (FGSA.process p st o).base.votes := by
  dsimp only [FGSA.process]
  cases hd : o.decode with
  | none => exact hm
  | some m =>
    cases m with
    | vote s j B => exact t77_grid_future_absent st.base r i b _ hf hm
    | row j B => rwa [Internal.admitRow_base]
    | block s B raw sup rows =>
      dsimp only [admitBlock]
      cases hP : parentFG st B with
      | none => exact hm
      | some P =>
        let st1 : State p.n := { st with
          base := GridCO.admitProposal p.toParams.engine st.base (baseProposal s B raw sup) B
            (raw.map baseHead)
          fg := on_block p.E p.cfg st.fg (fgBlock P B rows)
          proposals := st.proposals ++ [⟨.proposer s, .proposal B raw sup rows⟩] }
        dsimp only
        split
        · rw [Internal.foldl_admitRow_base, (Internal.ite_reconcile st1 st).1]
          exact t77_grid_future_proposal st.base r i b _ _ _ hf hm
        · exact hm

/-- A newly processed handled object has reached its admission threshold. -/
theorem fgsaAdmitSound (p : Params) (c : AppCodec In) :
    Gen.V2.Duty.AdmitSound (fgsa p c) (fgsaTimelyClock p c) where
  timely nd o' o hn hpre hpost hh := by
    change 0 ≤ nd.st.base.now at hn
    change processedS p nd.st o = false at hpre
    change processedS p (FGSA.process p nd.st (toWire p o')) o = true at hpost
    change handlesS p nd.st o' o at hh
    cases he : (toWire p o).decode with
    | none =>
      dsimp only [processedS] at hpost
      rw [he] at hpost
      contradiction
    | some m =>
      cases m with
      | vote s i b =>
        have ho : o = ofWire p ⟨.seat (.head s) i, .head b⟩ := by
          apply toWire_injective
          simpa using decode_eq_vote.mp he
        have hs : s ≤ nd.st.slot p := by
          by_contra hs
          have hf : nd.st.slot p < s := Nat.lt_of_not_ge hs
          have hm := t77_future_head_process nd.st s i b (toWire p o') hf
          dsimp only [processedS] at hpre hpost
          rw [he] at hpre hpost
          change decide (_ ∈ nd.st.base.votes) = false at hpre
          change decide (_ ∈ (FGSA.process p nd.st (toWire p o')).base.votes) = true at hpost
          exact hm (decide_eq_false_iff_not.mp hpre) (of_decide_eq_true hpost)
        rw [ho]
        exact (fgsa_slot_threshold_iff p _ hn s).1 hs
      | row i body =>
        have ho : o = ofWire p ⟨.seat .fg i, .row body⟩ := by
          apply toWire_injective
          simpa using decode_eq_row.mp he
        rw [ho]
        exact hn
      | block s b raw sup rows =>
        have heq : o' = o := by
          rcases hh with hh | hh
          · exact hh
          · generalize hd' : (toWire p o').decode = d at hh
            cases d with
            | none => exact hh.elim
            | some m =>
              cases m with
              | vote s i b => exact hh.elim
              | row i body => exact hh.elim
              | block s b raw sup rows =>
                rcases hh.2 with hm | hm
                · obtain ⟨h, _, rfl⟩ := List.mem_map.mp hm
                  rw [toWire_ofHead] at he
                  obtain ⟨auth, payload⟩ := h
                  rcases auth with ⟨(_ | _), _⟩ | _ | _ <;>
                    dsimp only [Wire.decode] at he <;> cases he
                · obtain ⟨a, _, rfl⟩ := List.mem_map.mp hm
                  rw [toWire_ofRow] at he
                  obtain ⟨auth, payload⟩ := a
                  rcases auth with ⟨(_ | _), _⟩ | _ | _ <;>
                    dsimp only [Wire.decode] at he <;> cases he
        subst o'
        have hw := decode_eq_block.mp he
        have ho : o = ofWire p ⟨.proposer s, .proposal b raw sup rows⟩ := by
          apply toWire_injective
          simpa using hw
        dsimp only [FGSA.process] at hpost
        rw [he] at hpost
        dsimp only [admitBlock] at hpost
        cases hP : parentFG nd.st b with
        | none =>
          rw [hP] at hpost
          cases hpre.symm.trans hpost
        | some P =>
          rw [hP] at hpost
          dsimp only at hpost
          split at hpost
          · rename_i hacc
            obtain ⟨_, hslot, _, _, _, hs⟩ := blockAccepted_facts hacc
            have hs' : s ≤ nd.st.slot p := hs ▸ hslot
            rw [ho]
            exact (fgsa_slot_threshold_iff p _ hn s).1 hs'
          · cases hpre.symm.trans hpost

/-- The receipt clock reads the base store clock. -/
theorem fgsaTimelyClock_clockOf (p : Params) (c : AppCodec In) (nd : Node p) :
    (fgsaTimelyClock p c).clockOf nd = nd.st.base.now := by
  change nd.st.base.now = nd.st.base.now
  rfl

/-- The receipt clock uses the admission threshold. -/
theorem fgsaTimelyClock_actTime (p : Params) (c : AppCodec In) (o : Obj p) :
    (fgsaTimelyClock p c).actTime o = fgsaAdmissionTime p o := by
  change fgsaAdmissionTime p o = fgsaAdmissionTime p o
  rfl

/-- The FG-SA trigger is the generic honest emission or acceptance trigger. -/
theorem fgsaTrigger_def (p : Params) (c : AppCodec In) {V : Type} [DecidableEq V]
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (o : Obj p) (t : Time) :
    fgsaTrigger p c E rho o t ↔
      (∃ v ∈ rho.honest, V2.D.Run.emits E rho v o t) ∨
      (∃ v ∈ rho.honest, ∃ i, V2.D.Run.acceptsAt E rho i v o t) := Iff.rfl

/-- An honest emission produces an FG-SA trigger. -/
theorem fgsa_trigger_of_emit (p : Params) (c : AppCodec In) {V : Type} [DecidableEq V]
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) {v : V} {o : Obj p} {t : Time}
    (hv : v ∈ rho.honest) (he : V2.D.Run.emits E rho v o t) :
    fgsaTrigger p c E rho o t := Or.inl ⟨v, hv, he⟩

/-- An honest acceptance produces an FG-SA trigger. -/
theorem fgsa_trigger_of_accept (p : Params) (c : AppCodec In) {V : Type} [DecidableEq V]
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) {v : V} {o : Obj p} {t : Time} {i : Nat}
    (hv : v ∈ rho.honest) (ha : V2.D.Run.acceptsAt E rho i v o t) :
    fgsaTrigger p c E rho o t := Or.inr ⟨v, hv, i, ha⟩

end AvailableChain.FGSA.Run
end
