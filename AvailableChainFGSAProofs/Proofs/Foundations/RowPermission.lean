module
public import AvailableChainFGSAProofs.Proofs.Foundations.Accountable
public import AvailableChainFGSAProofs.Proofs.Foundations.Counts
public import AvailableChainFGSAProofs.Proofs.Shared.StoreRun
public import AvailableChainKitFG.ProvenanceCore
public import AvailableChainFGSAClaims.Statements.Packages.Healing

public section

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

variable {p : Params}

private theorem rowPermission_noEvidence_mono
    {A B A' B' : Finset (Row (Fin p.n))}
    (hA : A ⊆ A') (hB : B ⊆ B')
    (hn : ¬ HasSlashableWeightBetween p.E A' B') :
    ¬ HasSlashableWeightBetween p.E A B := by
  rintro ⟨S, hw, hs⟩
  apply hn
  refine ⟨S, hw, ?_⟩
  intro i hi
  obtain ⟨a, ha, b, hb, hai, hbi, he⟩ := hs i hi
  exact ⟨a, hA ha, b, hB hb, hai, hbi, he⟩

private theorem rowPermission_height_bound (st : State p.n) (hs : CStoreInv p st)
    (B : FGBlock (Fin p.n)) (hB : B ∈ st.fg.TF) : (heightView p B).h ≤ st.fg.h_max := by
  rw [hs.fg.hmax]
  exact (Finset.le_sup (f := fun B => (heightView p B).h) hB).trans (le_max_left _ _)

private theorem rowPermission_carrier_entry (st : State p.n) (hs : CStoreInv p st)
    (C K : FGBlock (Fin p.n)) (hC : C ∈ FGSA.fullTree p st)
    (hband : (FGSA.controls p st).lo ≤ (heightView p C).h)
    (hK : K ∈ st.fg.TF) (hk : (heightView p K).h_j = (heightView p C).h)
    (hno : ∀ A ∈ st.fg.TF, ∀ B ∈ st.fg.TF,
      ¬ HasSlashableWeightBetween p.E (chainRows A) (chainRows B)) :
    (heightView p C).T_h = (heightView p K).J := by
  have hc := (KitFG.mem_filteredFromView (heightView p) (FGSA.controls p st) st.fg.TF C).mp hC
  have hcap := rowPermission_height_bound st hs K hK
  have hlow := KitFG.Controls.H_sub_one_le_lo (FGSA.controls p st)
  have hhK := (fgCertificateLaws p).height.justified_below_height K
  have hpos := (fgCertificateLaws p).height.one_le_h C
  have hh : st.fg.h_max ≤ (heightView p C).h + 1 := by
    change st.fg.h_max - 1 ≤ _ at hlow
    simp only [Height] at *; omega
  obtain ⟨D, hD, hDF⟩ := hs.fg.Fcar
  have hDh := rowPermission_height_bound st hs D hD
  have hfbelow := (fgCertificateLaws p).heights_ordered D
  have hdj := (fgCertificateLaws p).height.justified_below_height D
  have hf : (finalityView p D).h_F ≤ (heightView p C).h := by simp only [Height] at *; omega
  have hFJ : FGBlock.Preceq st.fg.F (heightView p K).J := by
    rcases Nat.lt_or_eq_of_le hf with hlt | heq
    · have hentry := (fgJustificationLaws p).J_height K (by simp only [Height] at *; omega)
      have hJK := KitFG.preceq_trans ((fgCertificateLaws p).height.justified_preceq_entry K)
        ((fgCertificateLaws p).height.entry_preceq K)
      have hlock := KitFG.slashableWeight_or_finalized_preceq_of_certificate
        p.E (heightView p) (finalityView p) (fgCertificateLaws p) D (heightView p K).J
      have hheight : (finalityView p D).h_F < (heightView p (heightView p K).J).h := by
        rw [hentry, hk]
        exact hlt
      have hn := rowPermission_noEvidence_mono (p := p) (Finset.Subset.refl _)
        (KitFG.chainRows_mono hJK) (hno D hD K hK)
      rw [← hDF]
      exact (hlock hheight).resolve_left hn
    · obtain ⟨U, hUD, hUF, hu⟩ := KitFG.provenance_finality_of_certificate
        p.E (heightView p) (finalityView p) (fgCertificateLaws p) D
        (by simp only [Height] at *; omega)
      have huK : (heightView p U).h_j = (heightView p K).h_j := by simp only [Height] at *; omega
      have hn := rowPermission_noEvidence_mono (p := p) (KitFG.chainRows_mono hUD)
        (Finset.Subset.refl _) (hno D hD K hK)
      have he := (KitFG.slashableWeight_or_justified_eq_of_certificate
        p.E (heightView p) (finalityView p) (fgCertificateLaws p) U K huK).resolve_left hn
      rw [← he, hUF, hDF]
      exact KitFG.preceq_refl _
  have hmax := hs.fg.pair.2 K hK hFJ
  have hjle := KitFG.fst_le_of_lexKey_le hmax
  obtain ⟨L, hL, _, hj, hJ⟩ := hs.fg.pair.1
  have hLcap := rowPermission_height_bound st hs L hL
  have hLj := (fgCertificateLaws p).height.justified_below_height L
  have hjK : (heightView p L).h_j = (heightView p K).h_j := by simp only [Height] at *; omega
  have hsame := (KitFG.slashableWeight_or_justified_eq_of_certificate
    p.E (heightView p) (finalityView p) (fgCertificateLaws p) L K hjK).resolve_left
      (hno L hL K hK)
  have hnc : (FGSA.controls p st).contest = false := by
    cases he : (FGSA.controls p st).contest
    · rfl
    · have hlo : (FGSA.controls p st).lo = st.fg.h_max := by
        change (if (FGSA.controls p st).contest then _ else _) = _
        rw [he]; rfl
      rw [hlo] at hband
      simp only [Height] at *; omega
  have hr : (FGSA.controls p st).rootIsJ = true := by
    change (decide (st.fg.h_max = st.fg.h_j + 1) && !(FGSA.controls p st).contest) = true
    rw [hnc]
    simp only [Bool.not_false, Bool.and_true, decide_eq_true_eq]
    simp only [Height] at *; omega
  have hz : (FGSA.controls p st).Z = (heightView p K).J := by
    change (if (FGSA.controls p st).rootIsJ then st.fg.J else st.fg.F) = _
    simp only [hr, ite_true, hJ, hsame]
  have hsrc := hc.2.2.1
  rw [hz] at hsrc
  exact ((fgCertificateLaws p).height.entry_plateau hsrc
    (((fgJustificationLaws p).J_height K (by simp only [Height] at *; omega)).trans hk)).symm.trans
      ((fgJustificationLaws p).J_entry K)

private theorem rowPermission_write_lock (Λ : RecordOnce) (o : Obj p)
    (h : Height) (T : BlockId) (hl : (recordRow? p Λ o).lock h = some T) :
    Λ.lock h = some T ∨ ∃ seat body,
      o = ofRow p ⟨.seat .fg seat, body⟩ ∧ body.finality_pair = some ⟨h, T⟩ := by
  rcases o with ⟨auth, msg⟩
  cases auth with
  | none => exact Or.inl hl
  | seat label seat =>
    cases label with
    | prop s => exact Or.inl hl
    | base label =>
      cases label with
      | head s => exact Or.inl hl
      | fg =>
        cases msg with
        | head B => exact Or.inl hl
        | proposal B raw sup rows => exact Or.inl hl
        | row body =>
          change (record_row Λ.toRecord (body.toRow seat)).lock h = some T at hl
          rw [KitFG.record_row_lock] at hl
          change own_lock Λ.toRecord h body.finality_pair = some T at hl
          cases hf : body.finality_pair with
          | none => exact Or.inl (by simpa only [own_lock, hf] using hl)
          | some fp =>
            by_cases hh : fp.height = h
            · have ht : fp.target = T := by simpa only [own_lock, hf, hh, ite_true,
                Option.some.injEq] using hl
              exact Or.inr ⟨seat, body, rfl, hf.trans (congrArg some (by cases fp; simp_all))⟩
            · exact Or.inl (by simpa only [own_lock, hf, hh, ite_false] using hl)

private theorem rowPermission_fold_lock (ls : List (Obj p)) (Λ : RecordOnce)
    (h : Height) (T : BlockId) (hl : (ls.foldl (recordRow? p) Λ).lock h = some T) :
    Λ.lock h = some T ∨ ∃ seat body,
      ofRow p ⟨.seat .fg seat, body⟩ ∈ ls ∧ body.finality_pair = some ⟨h, T⟩ := by
  induction ls generalizing Λ with
  | nil => exact Or.inl hl
  | cons o ls ih =>
    rcases ih (recordRow? p Λ o) hl with hold | ⟨seat, body, hm, hf⟩
    · rcases rowPermission_write_lock Λ o h T hold with h | ⟨seat, body, rfl, hf⟩
      · exact Or.inl h
      · exact Or.inr ⟨seat, body, List.mem_cons_self, hf⟩
    · exact Or.inr ⟨seat, body, List.mem_cons_of_mem _ hm, hf⟩

private theorem rowPermission_head_carrier (st : State p.n) (hs : CStoreInv p st)
    (Λ : Record) (fp : FinalityPair)
    (hf : finality_pair Λ (fgInputs p st).2 = some fp) :
    ∃ K ∈ st.fg.TF, (heightView p K).h_j = fp.height ∧
      (heightView p K).J.root = fp.target := by
  cases hh : fgBlockOf st (fgHead p st) with
  | none =>
    have hhf : (fgInputs p st).2 = ⟨0, genesisRoot, 0⟩ := by
      change (match fgBlockOf st (fgHead p st) with
        | some H => Window.headFields p p.K_W H | none => ⟨0, genesisRoot, 0⟩) = _
      rw [hh]
    rw [hhf] at hf
    delta finality_pair at hf
    simp only [Nat.lt_irrefl, false_and, ite_false] at hf
    cases hf
  | some K =>
    have hhf : (fgInputs p st).2 =
        KitFG.certificateHeadFields (heightView p) (finalityView p) K := by
      change (match fgBlockOf st (fgHead p st) with
        | some H => Window.headFields p p.K_W H | none => ⟨0, genesisRoot, 0⟩) = _
      rw [hh]; rfl
    rw [hhf] at hf
    have hp := KitFG.provenance_finalityRow_of_heightLaws p.E
      (heightView p) (finalityView p) (fgCertificateLaws p).height Λ K fp hf
    exact ⟨K, ((fgBlockOf_spec p st hs _ K).mp hh).1, hp.1.symm, hp.2.1.symm⟩

variable {In V : Type} {c : AppCodec In} [DecidableEq V]
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

private theorem rowPermission_released_origin (i : Nat) (x : V)
    (seat : Fin p.n) (body : RowPayload)
    (hm : ofRow p ⟨.seat .fg seat, body⟩ ∈ V2.D.Engine.ownReleased E rho x 0 i) :
    ∃ j r, j < i ∧ rho.events[j]? = some (.tick x (p.actionTime r)) ∧
      ofRow p ⟨.seat .fg seat, body⟩ ∈ V2.D.Run.emitsAt E rho j := by
  rw [V2.D.Engine.ownReleased_def] at hm
  obtain ⟨j, hj, hm⟩ := List.mem_flatMap.mp hm
  have hji : j < i := by simpa using hj
  rw [V2.D.Engine.ownReleasedAt_def] at hm
  split at hm
  · rename_i hx
    have hem := (List.mem_filter.mp hm).1
    cases he : rho.events[j]? with
    | none => simp only [V2.D.Run.emitsAt, he] at hem; cases hem
    | some ev =>
      cases ev with
      | restart y t => simp only [V2.D.Run.emitsAt, he] at hem; cases hem
      | deliver y o t => simp only [V2.D.Run.emitsAt, he] at hem; cases hem
      | tick y t =>
        have hy : y = x := by simpa only [he, Option.map_some, V2.Event.node,
          Option.some.injEq] using hx
        subst y
        obtain ⟨_, _, r, hr, _⟩ := (fgsa_emitsAt_row E rho j x t he seat body).mp hem
        exact ⟨j, r, hji, hr ▸ he, hem⟩
  · cases hm

private theorem rowPermission_record_carrier
    (hnr : V2.D.NoRestart rho) (i : Nat) (x : V) (h : Height) (T : BlockId)
    (hl : (V2.D.Run.stateBefore E rho i x).record.lock h = some T) :
    ∃ K ∈ (storeAt p c E rho i x).fg.TF,
      (derive p.E p.cfg K).h_j = h ∧ (derive p.E p.cfg K).J.root = T := by
  rw [ownRecord_fold_run] at hl
  rcases rowPermission_fold_lock _ RecordOnce.initial h T hl with hinit | ⟨seat, body, hm, hf⟩
  · cases hinit
  obtain ⟨j, r, hji, hj, hem⟩ := rowPermission_released_origin E rho i x seat body hm
  obtain ⟨_, _, _, _, he⟩ := (fgsa_emitsAt_row E rho j x _ hj seat body).mp hem
  let st := FGSA.clock p (V2.D.Run.stateBefore E rho j x).st (p.actionTime r)
  let Λ := (V2.D.Run.stateBefore E rho j x).record
  have ha : (createRowOnce p.E p.cfg Λ seat (fgInputs p st).1 (fgInputs p st).2).1 =
      some (body.toRow seat) := (fgsa_attest_decode st Λ seat body he).symm
  obtain ⟨height, target, timeout, _, heq, _, _, _⟩ :=
    KitFG.createRowOnce_released p.E p.cfg Λ seat (fgInputs p st).1 (fgInputs p st).2 ha
  have hfp := congrArg Row.finality_pair heq
  change body.finality_pair = _ at hfp
  rw [hf] at hfp
  have hfinal := (Option.filter_eq_some_iff.mp hfp.symm).1
  obtain ⟨K, hK, hk, ht⟩ := rowPermission_head_carrier st
    (cstoreInv_clock p _ (cstoreInv_stateBefore E rho j x) _) Λ.toRecord ⟨h, T⟩ hfinal
  rw [heightView_bridge p K] at hk ht
  change K ∈ (FGSA.clock p _ _).fg.TF at hK
  rw [FGSA.clock_fg] at hK
  exact ⟨K, (fgsa_store_cumulative p c E rho hnr hji.le x).1 hK, hk, ht⟩

/-- IF.3(b), blueprint 21:1115–1137: the actual post-clock lock cannot name
another entry of an in-band source. The current pair uses the W head fields.
The Base₂ and fault premises are fields of HealingPrem. PhaseInterval supplies
no extra record assumption; the result holds at every such post-clock read.
DC: INTENTIONAL, fixedRootWindowRows_of_source uses a fixed-root witness;
this proof uses the live band and the W certificate laws. -/
theorem rowPermission_own_lock [Fintype V]
    (hb : Base₂ p c E rho) (hf : (Gen.V2.Duty.faulty rho).card ≤ (p.n - 1) / 3)
    (x : V) (hx : x ∈ rho.honest) (t : Time) (nd : Node p)
    (hnd : postClock E rho x t = some nd) (C : FGBlock (Fin p.n))
    (hC : C ∈ FGSA.fullTree p nd.st) (hband : (FGSA.controls p nd.st).lo ≤ hOf p.E p.cfg C) :
    own_lock nd.record.toRecord (hOf p.E p.cfg C)
        (finality_pair nd.record.toRecord (fgInputs p nd.st).2) = none ∨
      own_lock nd.record.toRecord (hOf p.E p.cfg C)
        (finality_pair nd.record.toRecord (fgInputs p nd.st).2) =
          some (derive p.E p.cfg C).T_h.root := by
  rw [postClock_def, preTick_def] at hnd
  cases hi : V2.D.Run.tickIdx? rho x t with
  | none => simp only [hi, Option.map_none] at hnd; contradiction
  | some i =>
    simp only [hi, Option.map_some] at hnd
    have hnd := Option.some.inj hnd
    subst nd
    let st := FGSA.clock p (V2.D.Run.stateBefore E rho i x).st t
    let Λ := (V2.D.Run.stateBefore E rho i x).record
    change own_lock Λ.toRecord (hOf p.E p.cfg C)
        (finality_pair Λ.toRecord (fgInputs p st).2) = none ∨
      own_lock Λ.toRecord (hOf p.E p.cfg C) (finality_pair Λ.toRecord (fgInputs p st).2) =
        some (derive p.E p.cfg C).T_h.root
    have hst := cstoreInv_clock p _ (cstoreInv_stateBefore E rho i x) t
    have hno : ∀ A ∈ st.fg.TF, ∀ B ∈ st.fg.TF,
        ¬ HasSlashableWeightBetween p.E (chainRows A) (chainRows B) := by
      intro A hA B hB hev
      change A ∈ (FGSA.clock p _ _).fg.TF at hA
      change B ∈ (FGSA.clock p _ _).fg.TF at hB
      rw [FGSA.clock_fg] at hA hB
      have hn := fgsa_slashable_faulty_count p c E rho hb.linked
        hb.valid.toUnforgeableSignatures i i x x A B ⟨hx, hA⟩ ⟨hx, hB⟩ hev
      have hlt := (fgsa_faultX_count_rec p hf).lt
      omega
    have hmatch : ∀ T,
        own_lock Λ.toRecord (hOf p.E p.cfg C)
          (finality_pair Λ.toRecord (fgInputs p st).2) = some T →
        T = (derive p.E p.cfg C).T_h.root := by
      intro T hl
      have hcarr : ∃ K ∈ st.fg.TF, (derive p.E p.cfg K).h_j = hOf p.E p.cfg C ∧
          (derive p.E p.cfg K).J.root = T := by
        have old (hl : Λ.lock (hOf p.E p.cfg C) = some T) :=
          rowPermission_record_carrier E rho hb.noRestart i x (hOf p.E p.cfg C) T hl
        cases hp : finality_pair Λ.toRecord (fgInputs p st).2 with
        | none =>
          obtain ⟨K, hK, hk, ht⟩ := old (by simpa only [own_lock, hp] using hl)
          exact ⟨K, by
              change K ∈ (FGSA.clock p _ _).fg.TF
              rw [FGSA.clock_fg]
              exact hK, hk, ht⟩
        | some fp =>
          by_cases hh : fp.height = hOf p.E p.cfg C
          · have ht : fp.target = T := by simpa only [own_lock, hp, hh, ite_true,
              Option.some.injEq] using hl
            obtain ⟨K, hK, hk, hT⟩ := rowPermission_head_carrier st hst Λ.toRecord fp hp
            rw [heightView_bridge p K] at hk hT
            exact ⟨K, hK, hk.trans hh, hT.trans ht⟩
          · obtain ⟨K, hK, hk, ht⟩ := old (by simpa only [own_lock, hp, hh, ite_false] using hl)
            exact ⟨K, by
              change K ∈ (FGSA.clock p _ _).fg.TF
              rw [FGSA.clock_fg]
              exact hK, hk, ht⟩
      obtain ⟨K, hK, hk, ht⟩ := hcarr
      have hentry := rowPermission_carrier_entry st hst C K hC
        (by rwa [← KitFG.hOf_of_bridge p.E p.cfg (heightView p) (heightView_bridge p)]) hK
        (by rw [heightView_bridge p K, heightView_bridge p C]; exact hk) hno
      rw [heightView_bridge p C, heightView_bridge p K] at hentry
      exact ht.symm.trans (congrArg FGBlock.root hentry).symm
    cases hl : own_lock Λ.toRecord (hOf p.E p.cfg C)
        (finality_pair Λ.toRecord (fgInputs p st).2) with
    | none => exact Or.inl rfl
    | some T => exact Or.inr (congrArg some (hmatch T hl))

private theorem rowPermission_pair_of_lock (Λ : Record) (h : Height) (T : BlockId)
    (fp : Option FinalityPair) (hl : own_lock Λ h fp = none ∨ own_lock Λ h fp = some T) :
    namedEntry (height_pair Λ (some (h, T)) fp) = some (h, T) := by
  change namedEntry (if Λ.timeout h then .vote h T true else
    match own_lock Λ h fp with
    | some locked => if locked = T then .vote h T false else .empty
    | none => match Λ.target h with
      | some recorded => if recorded = T then .vote h T false else .vote h T true
      | none => .vote h T false) = _
  by_cases ht : Λ.timeout h = true
  · rw [ht]; rfl
  · have ht' : Λ.timeout h = false := Bool.eq_false_of_not_eq_true ht
    rw [ht']
    rcases hl with hn | he
    · rw [hn]
      cases Λ.target h with
      | none => rfl
      | some recorded => by_cases he : recorded = T <;> simp only [he, ite_true, ite_false] <;> rfl
    · rw [he]
      simp only [Bool.false_eq_true, ite_false, ite_true]
      rfl

/-- The IF.3(b) permission conclusion for the selected action source.
DC: INTENTIONAL W head fields and the actual post-clock record; SAME computed
height-pair conclusion as fixedRootWindowRows_of_source (DC:879).
Blueprint 21:1120–1137; spec client height_pair. This theorem makes no claim
of a fresh emission. -/
theorem rowPermission_pair [Fintype V]
    (hb : Base₂ p c E rho) (hf : (Gen.V2.Duty.faulty rho).card ≤ (p.n - 1) / 3)
    (x : V) (hx : x ∈ rho.honest) (r : Nat) (nd : Node p)
    (hnd : postClock E rho x (p.actionTime r) = some nd) (C : FGBlock (Fin p.n))
    (hsource : actionSourceFG p c E rho x r = some (some C))
    (hC : C ∈ FGSA.fullTree p nd.st) (hband : (FGSA.controls p nd.st).lo ≤ hOf p.E p.cfg C) :
    namedEntry (height_pair nd.record.toRecord
      ((FGSA.fgSource p nd.st).map (fun C => (hOf p.E p.cfg C, (derive p.E p.cfg C).T_h.root)))
      (finality_pair nd.record.toRecord (fgInputs p nd.st).2)) =
        some (hOf p.E p.cfg C, (derive p.E p.cfg C).T_h.root) := by
  have hl := rowPermission_own_lock E rho hb hf x hx _ nd hnd C hC hband
  rw [actionSourceFG_def, hnd] at hsource
  have hc : FGSA.fgSource p nd.st = some C := Option.some.inj hsource
  rw [hc]
  exact rowPermission_pair_of_lock nd.record.toRecord _ _ _ hl

private theorem rowPermission_decode_write (Λ : RecordOnce) (o : Obj p) :
    recordRow? p Λ o = ((decodeRowObject p o).map (record_row_once Λ)).getD Λ := by
  rcases o with ⟨auth, msg⟩
  cases auth with
  | none => cases msg <;> rfl
  | seat label seat =>
    cases label with
    | prop s => cases msg <;> rfl
    | base label => cases label <;> cases msg <;> rfl

private theorem rowPermission_decode_fold (ls : List (Obj p)) (Λ : RecordOnce) :
    ls.foldl (recordRow? p) Λ = (ls.filterMap (decodeRowObject p)).foldl record_row_once Λ := by
  induction ls generalizing Λ with
  | nil => rfl
  | cons o ls ih =>
    rw [List.foldl_cons, ih, rowPermission_decode_write]
    cases hd : decodeRowObject p o <;> simp [hd]

private theorem rowPermission_client_record (seat : Fin p.n)
    (inputs : List (Option (FGBlock (Fin p.n)) × HeadFields)) (Λ : RecordOnce) :
    (clientRunOnce p.E p.cfg seat Λ inputs).foldl record_row_once Λ =
      clientRecordOnce p.E p.cfg seat Λ inputs := by
  induction inputs generalizing Λ with
  | nil => rfl
  | cons input rest ih =>
    rcases input with ⟨src, hd⟩
    change (clientRunOnce p.E p.cfg seat Λ ([(src, hd)] ++ rest)).foldl record_row_once Λ =
      clientRecordOnce p.E p.cfg seat Λ ([(src, hd)] ++ rest)
    rw [KitFG.clientRunOnce_append, KitFG.clientRecordOnce_append, List.foldl_append]
    have hr : clientRecordOnce p.E p.cfg seat Λ [(src, hd)] =
        (createRowOnce p.E p.cfg Λ seat src hd).2 := rfl
    have hu : clientRunOnce p.E p.cfg seat Λ [(src, hd)] =
        (createRowOnce p.E p.cfg Λ seat src hd).1.toList := by
      delta clientRunOnce
      dsimp only [List.brecOn, List.below]
      delta clientRunOnce._f
      dsimp only
      cases ha : (createRowOnce p.E p.cfg Λ seat src hd).1 <;> rfl
    rw [hr, hu]
    cases ha : (createRowOnce p.E p.cfg Λ seat src hd).1 with
    | none =>
      rw [KitFG.createRowOnce_none p.E p.cfg Λ seat src hd ha]
      exact ih Λ
    | some a =>
      obtain ⟨_, _, _, _, _, _, _, hw⟩ := KitFG.createRowOnce_released p.E p.cfg Λ seat src hd ha
      rw [hw]
      exact ih _

private theorem rowPermission_record_history
    (hL : V2.D.Linked (fgsaFamilies p c).linked rho) (i : Nat) (x : V) :
    let Λ := (V2.D.Run.stateBefore E rho i x).record
    KitFG.RecordInv Λ.toRecord ∧
      ∀ h T timeout fp, (.vote h T timeout, fp) ∈ Λ.sent →
        (timeout = false → Λ.target h = some T) ∧ (timeout = true → Λ.timeout h = true) := by
  obtain ⟨e, he⟩ := fgsa_linked_seats rho hL
  let inputs := (fgClientEvents p c E rho x i).map (fun ev => ev.2.2.2)
  have hr : (V2.D.Run.stateBefore E rho i x).record =
      clientRecordOnce p.E p.cfg (e.symm x) RecordOnce.initial inputs := by
    exact (ownRecord_fold_run E rho i x).trans
      ((rowPermission_decode_fold (p := p) _ _).trans
        ((congrArg (fun rows : List (Row (Fin p.n)) =>
          rows.foldl record_row_once RecordOnce.initial)
          (fgsa_client_trace_of_seats E rho e he x i)).trans
            (rowPermission_client_record (e.symm x) inputs RecordOnce.initial)))
  dsimp only
  rw [hr]
  have hc := KitFG.clientRunOnce_covers p.E p.cfg (e.symm x) inputs RecordOnce.initial
    KitFG.recordInv_initial
  refine ⟨hc.1, ?_⟩
  intro h T timeout fp hm
  rw [KitFG.clientRecordOnce_sent] at hm
  change (.vote h T timeout, fp) ∈
    ((clientRunOnce p.E p.cfg (e.symm x) RecordOnce.initial inputs).map
      Row.onceKey).reverse ++ [] at hm
  simp only [List.append_nil, List.mem_reverse, List.mem_map] at hm
  obtain ⟨a, ha, hk⟩ := hm
  have hh := congrArg Prod.fst hk
  change a.height_pair = .vote h T timeout at hh
  exact ⟨fun ht => (hc.2.2 a ha).1 h T (ht ▸ hh),
    fun ht => (hc.2.2 a ha).2.1 h T (ht ▸ hh)⟩

private theorem rowPermission_once_coverage (Λ : RecordOnce) (seat : Fin p.n)
    (src : Option (FGBlock (Fin p.n))) (hd : HeadFields) (h : Height) (T : BlockId)
    (hInv : KitFG.RecordInv Λ.toRecord)
    (hHist : ∀ g U timeout fp, (.vote g U timeout, fp) ∈ Λ.sent →
      (timeout = false → Λ.target g = some U) ∧ (timeout = true → Λ.timeout g = true))
    (hp : namedEntry (height_pair Λ.toRecord
      (src.map (fun C => ((derive p.E p.cfg C).h, (derive p.E p.cfg C).T_h.root)))
      (finality_pair Λ.toRecord hd)) = some (h, T)) :
    (∃ a, (createRowOnce p.E p.cfg Λ seat src hd).1 = some a ∧
      namedEntry a.height_pair = some (h, T)) ∨
    ∃ b ∈ Λ.sent, namedEntry b.1 = some (h, T) := by
  cases hpair : height_pair Λ.toRecord
      (src.map (fun C => ((derive p.E p.cfg C).h, (derive p.E p.cfg C).T_h.root)))
      (finality_pair Λ.toRecord hd) with
  | empty => rw [hpair] at hp; cases hp
  | vote g U timeout =>
    rw [hpair] at hp
    change some (g, U) = some (h, T) at hp
    have he := Option.some.inj hp
    have hg : g = h := congrArg Prod.fst he
    have hU : U = T := congrArg Prod.snd he
    subst h
    subst T
    by_cases hs : sameHeightOnce Λ g U timeout = true
    · right
      obtain ⟨⟨pair, fp⟩, hm, hg⟩ := List.any_eq_true.mp hs
      cases pair with
      | empty => cases hg
      | vote k W oldTimeout =>
        change (decide (k = g) && (!timeout || decide (W = U))) = true at hg
        obtain ⟨hk, he⟩ := Bool.and_eq_true_iff.mp hg
        have hk : k = g := of_decide_eq_true hk
        subst k
        have hWU : W = U := by
          cases timeout with
          | true => simpa using he
          | false =>
            have old := hHist g W oldTimeout fp hm
            cases oldTimeout with
            | true =>
              have ht := old.2 rfl
              have fields := KitFG.height_pair_vote_fields hpair
              rw [fields] at hpair
              change (if Λ.timeout g then NamedHeightPair.vote g U true else _) = _ at hpair
              rw [ht] at hpair
              cases hpair
            | false =>
              have ht := old.1 rfl
              rcases KitFG.height_pair_target_compat hInv hpair with hn | he
              · rw [ht] at hn; cases hn
              · exact Option.some.inj (ht.symm.trans he)
        subst W
        exact ⟨(.vote g U oldTimeout, fp), hm, rfl⟩
    · let a : Row (Fin p.n) := ⟨seat, .vote g U timeout,
        (finality_pair Λ.toRecord hd).filter (fun fp => decide (fp.height < g))⟩
      by_cases hm : a.onceKey ∈ Λ.sent
      · exact Or.inr ⟨a.onceKey, hm, rfl⟩
      · left
        refine ⟨a, ?_, rfl⟩
        rw [createRowOnce_def]
        dsimp only
        rw [hpair]
        simp only [hs, Bool.false_eq_true, ite_false]
        change (if a.onceKey ∈ Λ.sent then (none, Λ) else (some a, record_row_once Λ a)).1 = some a
        rw [ite_eq_right hm]

private theorem rowPermission_sent_origin (ls : List (Obj p)) (Λ : RecordOnce)
    (b : NamedHeightPair × Option FinalityPair)
    (hm : b ∈ (ls.foldl (recordRow? p) Λ).sent) :
    b ∈ Λ.sent ∨ ∃ seat body,
      ofRow p ⟨.seat .fg seat, body⟩ ∈ ls ∧ (body.height_pair, body.finality_pair) = b := by
  induction ls generalizing Λ with
  | nil => exact Or.inl hm
  | cons o ls ih =>
    rcases ih (recordRow? p Λ o) hm with hold | ⟨seat, body, hm, hb⟩
    · rcases o with ⟨auth, msg⟩
      cases auth with
      | none => exact Or.inl hold
      | seat label seat =>
        cases label with
        | prop s => exact Or.inl hold
        | base label =>
          cases label with
          | head s => exact Or.inl hold
          | fg =>
            cases msg with
            | head B => exact Or.inl hold
            | proposal B raw sup rows => exact Or.inl hold
            | row body =>
              rcases List.mem_cons.mp hold with he | hm
              · exact Or.inr ⟨seat, body, List.mem_cons_self, he.symm⟩
              · exact Or.inl hm
    · exact Or.inr ⟨seat, body, List.mem_cons_of_mem _ hm, hb⟩

/-- SO-COV at one awake action: the in-band source has a complete matching
emission at this action or an earlier one. The permission is derived from
Base₂ and the recovery fault bound. Blueprint 21:1120–1137 and 22 SO-COV;
spec client:1672–1679. DC: INTENTIONAL earlier-or-current coverage under the
send-once client, rather than a fresh-row conclusion. -/
theorem rowPermission_covered [Fintype V]
    (hb : Base₂ p c E rho) (hf : (Gen.V2.Duty.faulty rho).card ≤ (p.n - 1) / 3)
    (x : V) (hx : x ∈ rho.honest) (r : Nat) (nd : Node p)
    (hnd : postClock E rho x (p.actionTime r) = some nd) (C : FGBlock (Fin p.n))
    (hsource : actionSourceFG p c E rho x r = some (some C))
    (hC : C ∈ FGSA.fullTree p nd.st) (hband : (FGSA.controls p nd.st).lo ≤ hOf p.E p.cfg C)
    (hawake : E.awake x (p.actionTime r) = true) :
    ∃ j rSent a, rSent ≤ r ∧ HonestRowAt p c E rho j x rSent a ∧
      namedEntry a.payload.height_pair =
          some (hOf p.E p.cfg C, (derive p.E p.cfg C).T_h.root) := by
  have hp := rowPermission_pair E rho hb hf x hx r nd hnd C hsource hC hband
  rw [postClock_def, preTick_def] at hnd
  cases hi : V2.D.Run.tickIdx? rho x (p.actionTime r) with
  | none => simp only [hi, Option.map_none] at hnd; contradiction
  | some i =>
    simp only [hi, Option.map_some] at hnd
    have hnd := Option.some.inj hnd
    subst nd
    have ht := V2.D.Run.tickIdx?_spec hi
    let st := FGSA.clock p (V2.D.Run.stateBefore E rho i x).st (p.actionTime r)
    let Λ := (V2.D.Run.stateBefore E rho i x).record
    have hist := rowPermission_record_history E rho hb.linked i x
    have cov := rowPermission_once_coverage Λ ⟨0, p.nPos⟩ (fgInputs p st).1
      (fgInputs p st).2 (hOf p.E p.cfg C) (derive p.E p.cfg C).T_h.root hist.1 hist.2
    rcases cov hp with ⟨a, ha, hn⟩ | ⟨b, hbSent, hn⟩
    · let body := RowPayload.vote (RowBody.ofRow a)
      have hattest : (attest p st Λ ⟨0, p.nPos⟩).1 = some body := by
        change Option.map (fun a => RowPayload.vote (RowBody.ofRow a))
          (createRowOnce p.E p.cfg Λ ⟨0, p.nPos⟩ (fgInputs p st).1 (fgInputs p st).2).1 = _
        rw [ha]; rfl
      obtain ⟨seat, hs⟩ := (hb.linked.toCStar (.base .fg) trivial).2 x
      let wire : RowWire p.n := ⟨.seat .fg seat, body⟩
      refine ⟨i, r, wire, le_rfl, ⟨hx, ht, ?_⟩, hn⟩
      exact (fgsa_emitsAt_row E rho i x _ ht seat body).mpr ⟨hawake, hs, r, rfl, hattest⟩
    · change b ∈ (V2.D.Run.stateBefore E rho i x).record.sent at hbSent
      rw [ownRecord_fold_run] at hbSent
      rcases rowPermission_sent_origin _ RecordOnce.initial b hbSent with hn | ⟨seat, body, hm, he⟩
      · cases hn
      obtain ⟨j, rSent, hji, hj, hem⟩ := rowPermission_released_origin E rho i x seat body hm
      have htime := fgsa_tick_time_strict E rho hb.valid.toScheduleWellFormed hj ht hji
      have hr : rSent ≤ r := by
        by_contra h
        have hcast : ((r * p.R : Nat) : Time) < ((rSent * p.R : Nat) : Time) := by
          exact_mod_cast (Nat.mul_lt_mul_of_pos_right (show r < rSent by omega)
            (show 0 < p.R by have := p.RLarge; omega))
        change 4 * p.Δ * ((rSent * p.R : Nat) : Time) + 6 * p.Δ <
          4 * p.Δ * ((r * p.R : Nat) : Time) + 6 * p.Δ at htime
        have := p.deltaPos
        nlinarith
      refine ⟨j, rSent, ⟨.seat .fg seat, body⟩, hr, ⟨hx, hj, hem⟩, ?_⟩
      exact (congrArg (fun b => namedEntry b.1) he).trans hn

/-- RowPermissionAt in heightView form under HealingPrem. No client permission
premise is added. The phase is needed only for its horizon bound; the live
in-band theorem gives the stronger local result. Blueprint 21 H.7 / H.9,
IF.3(b), SO-COV. DC: INTENTIONAL live W execution and send-once coverage.
The body is stated here without a Claims import, as required by L42. -/
theorem rowPermission_at [Fintype V] (G ΔF : Time) (pt : Unit)
    (h : HealingPrem p c G ΔF E rho pt) :
    ∀ u v m J contested r x C nd,
      E.t_GST ≤ u → PhaseInterval p c E rho u v m J contested →
      u ≤ p.actionTime r → p.actionTime r ≤ v → x ∈ rho.honest →
      postClock E rho x (p.actionTime r) = some nd →
      actionSourceFG p c E rho x r = some (some C) →
      C ∈ FGSA.fullTree p nd.st →
      (FGSA.controls p nd.st).lo ≤ (heightView p C).h → (heightView p C).h ≤ m →
      ∃ j rSent a, rSent ≤ r ∧ HonestRowAt p c E rho j x rSent a ∧
        namedEntry a.payload.height_pair =
          some ((heightView p C).h, (heightView p C).T_h.root) := by
  intro u v m J contested r x C nd hGST hphase hu hv hx hnd hsrc hC hlo _
  have old := rowPermission_covered E rho h.set.base h.set.fault x hx r nd hnd C hsrc hC
    (by simpa only [heightView_eq_simplex p, KitFG.simplexHeightView_def,
      KitFG.heightOf_def, hOf] using hlo)
    (h.set.awake x hx _ (hGST.trans hu) (hv.trans hphase.2.1))
  simpa only [heightView_eq_simplex p, KitFG.simplexHeightView_def,
    KitFG.heightOf_def, hOf] using old

end AvailableChain.FGSA.Run
