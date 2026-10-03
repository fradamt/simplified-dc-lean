module
public import AvailableChainFGSAClaims.Statements.Fold
public import AvailableChainFGSARun.Proofs.ClientTrace
public import AvailableChainFGSARun.Proofs.Schedule
public import AvailableChainKitFG.ProvenanceCore
public import AvailableChainFGSA.Proofs.EmissionFields
public import AvailableChainFGSAClaims.Statements.ComposeStmt

public section

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

variable (p : Params) {In V : Type} [DecidableEq V]
    (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

/-- Paper 22:841–879: high honest sources at one height have one entry.
DC: INTENTIONAL: H1 supplies compatibility; height plateau supplies the entry. -/
theorem high_source_entry_eq (w : HealingWitness) (hhigh : THigh p c E rho w)
    (x z : V) (r s : Nat) (C D : FGBlock (Fin p.n))
    (hx : x ∈ rho.honest) (hz : z ∈ rho.honest)
    (hC : actionSourceFG p c E rho x r = some (some C))
    (hD : actionSourceFG p c E rho z s = some (some D))
    (hc : high p w C) (hd : high p w D)
    (heq : (heightView p C).h = (heightView p D).h) :
    (heightView p C).T_h = (heightView p D).T_h := by
  have hcompat := (hhigh x z r s C D hx hz hC hD hc hd).1
  change ((eraseFG C).preceq (eraseFG D) || (eraseFG D).preceq (eraseFG C)) = true at hcompat
  rw [Bool.or_eq_true] at hcompat
  have lift (A B : FGBlock (Fin p.n)) (hab : Block.Preceq (eraseFG A) (eraseFG B)) :
      FGBlock.Preceq A B :=
    preceq_of_eraseFG_preceq (Vw := ({A, B} : Finset (FGBlock (Fin p.n))))
      (fun _ _ _ _ h => FGBlock.root_injective h)
      ⟨A, by simp, KitFG.preceq_refl A⟩ ⟨B, by simp, KitFG.preceq_refl B⟩ hab
  rcases hcompat with h | h
  · exact (fgCertificateLaws p).height.entry_plateau (lift C D h) heq
  · exact ((fgCertificateLaws p).height.entry_plateau (lift D C h) heq.symm).symm

private noncomputable def recordInv_entry (y : Nat) : BlockId := by
  classical
  exact if h : ∃ x r C, x ∈ rho.honest ∧
      actionSourceFG p c E rho x r = some (some C) ∧ (heightView p C).h = y
    then (heightView p (Classical.choose (Classical.choose_spec
      (Classical.choose_spec h)))).T_h.root else genesisRoot

private theorem recordInv_entry_source (w : HealingWitness) (hh : THigh p c E rho w)
    (x : V) (r : Nat) (C : FGBlock (Fin p.n)) (hx : x ∈ rho.honest)
    (hs : actionSourceFG p c E rho x r = some (some C)) (hc : high p w C) :
    recordInv_entry p c E rho (heightView p C).h = (heightView p C).T_h.root := by
  classical
  unfold recordInv_entry
  split_ifs with h
  · obtain ⟨hz, hD, heq⟩ := Classical.choose_spec
      (Classical.choose_spec (Classical.choose_spec h))
    exact congrArg FGBlock.root (high_source_entry_eq p c E rho w hh _ x _ r _ C
      hz hx hD hs (by simpa only [high_def, heq] using hc) hc heq)
  · exact (h ⟨x, r, C, hx, hs, rfl⟩).elim

private theorem recordInv_height_pair_some_def (Λ : Record) (y : Nat) (T : BlockId)
    (fp : Option FinalityPair) : height_pair Λ (some (y, T)) fp =
      if Λ.timeout y then .vote y T true else
        match own_lock Λ y fp with
        | some locked => if locked = T then .vote y T false else .empty
        | none => match Λ.target y with
          | some recorded => if recorded = T then .vote y T false else .vote y T true
          | none => .vote y T false := rfl

/-- Paper 22:841–879: the three record guards give a target, including the own lock.
DC: Protocol/ValidatorClient.lean:216–229, height-pair branches. -/
theorem high_record_target_choice (Λ : Record) (y : Nat) (T : BlockId)
    (fp : Option FinalityPair)
    (ht : Λ.target y = none ∨ Λ.target y = some T)
    (hn : Λ.timeout y = false)
    (hl : Λ.lock y = none ∨ Λ.lock y = some T)
    (hf : ∀ f, fp = some f → f.height = y → f.target = T) :
    height_pair Λ (some (y, T)) fp = .vote y T false := by
  have hol : own_lock Λ y fp = none ∨ own_lock Λ y fp = some T := by
    cases hp : fp with
    | none => simpa only [own_lock, hp] using hl
    | some f =>
      by_cases hy : f.height = y
      · right; simp only [own_lock, hy, ite_true, hf f hp hy]
      · simpa only [own_lock, hp, hy, ite_false] using hl
  rw [recordInv_height_pair_some_def]
  simp only [hn, Bool.false_eq_true, ite_false]
  rcases hol with hol | hol
  · rw [hol]
    rcases ht with ht | ht <;> simp [ht]
  · simp [hol]

private def recordInv_good (M : Nat) (entry : Nat → BlockId) (Λ : RecordOnce) : Prop :=
  ∀ y, M + 1 ≤ y →
    (Λ.target y = none ∨ Λ.target y = some (entry y)) ∧ Λ.timeout y = false ∧
    (Λ.lock y = none ∨ Λ.lock y = some (entry y)) ∧
    ∀ b ∈ Λ.sent, ∀ T timeout, b.1 = .vote y T timeout → T = entry y ∧ timeout = false

private theorem recordInv_finality_source (w : HealingWitness)
    (hh : THigh p c E rho w) (hqc : RQCOrigin p c E rho)
    (i : Nat) (x : V) (t : Time) (Λ : Record) (fp : FinalityPair)
    (hx : x ∈ rho.honest)
    (hf : finality_pair Λ (fgInputs p
      (FGSA.clock p (V2.D.Run.stateBefore E rho i x).st t)).2 = some fp)
    (hy : w.M + 1 ≤ fp.height) :
    fp.target = recordInv_entry p c E rho fp.height := by
  classical
  let st := FGSA.clock p (V2.D.Run.stateBefore E rho i x).st t
  have hs := cstoreInv_clock p _ (cstoreInv_stateBefore E rho i x) t
  cases hk : fgBlockOf st (fgHead p st) with
  | none =>
    have hfields : (fgInputs p st).2 = ⟨0, genesisRoot, 0⟩ := by
      change (match fgBlockOf st (fgHead p st) with
        | some H => Window.headFields p p.K_W H | none => ⟨0, genesisRoot, 0⟩) = _
      rw [hk]
    change finality_pair Λ (fgInputs p st).2 = some fp at hf
    rw [hfields] at hf
    delta finality_pair at hf
    simp only [Nat.lt_irrefl, false_and, ite_false] at hf
    cases hf
  | some K =>
    change finality_pair Λ (fgInputs p st).2 = some fp at hf
    rw [FGSA.fgInputs_headFields p st K hk] at hf
    obtain ⟨hheight, hroot, _, _⟩ := KitFG.provenance_finalityRow_of_heightLaws p.E
      (heightView p) (finalityView p) (fgCertificateLaws p).height Λ K fp hf
    have hK := ((fgBlockOf_spec p st hs _ K).mp hk).1
    change K ∈ (FGSA.clock p _ _).fg.TF at hK
    rw [FGSA.clock_fg] at hK
    have hnz : (heightView p K).h_j ≠ 0 := by simp only [Height] at *; omega
    obtain ⟨Q, hQ, hw⟩ := (fgCertificateLaws p).height.justification_certificate K hnz
    have hw' : ∀ k, ∃ W a, k ∈ Q → FGBlock.Preceq W K ∧ a ∈ W.rows ∧
        a.signer = k ∧ a.height_pair = .vote (heightView p K).h_j
          (heightView p K).J.root false := by
      intro k
      by_cases h : k ∈ Q
      · obtain ⟨W, a, ha⟩ := hw k h
        exact ⟨W, a, fun _ => ha⟩
      · exact ⟨.genesis, ⟨k, .empty, none⟩, fun hk => (h hk).elim⟩
    choose W a ha using hw'
    obtain ⟨k, hkQ, z, r, wire, hb, hd, _, C, G, hC, hn, _⟩ :=
      (hqc i x K hx hK).2.1 Q (fun k => (W k, a k)) hnz hQ ha
    have hname : namedEntry (a k).height_pair =
        some ((heightView p K).h_j, (heightView p K).J.root) := by
      rw [(ha k hkQ).2.2.2]; rfl
    rw [hname] at hn
    have heq := Option.some.inj hn
    have hyC : (heightView p C).h = fp.height :=
      (congrArg Prod.fst heq).symm.trans hheight.symm
    have hTC : (heightView p K).J.root = (heightView p C).T_h.root :=
      congrArg Prod.snd heq
    obtain ⟨j, _, hj⟩ := hb
    have hentry := recordInv_entry_source p c E rho w hh z r C hj.1 hC
      (by rw [high_def, hyC]; exact hy)
    rw [hyC] at hentry
    exact hroot.trans (hTC.trans hentry.symm)

private theorem recordInv_write (M : Nat) (entry : Nat → BlockId) (Λ : RecordOnce)
    (a : Row (Fin p.n)) (hg : recordInv_good M entry Λ)
    (hh : ∀ y T timeout, a.height_pair = .vote y T timeout → M + 1 ≤ y →
      T = entry y ∧ timeout = false)
    (hf : ∀ f, a.finality_pair = some f → M + 1 ≤ f.height → f.target = entry f.height) :
    recordInv_good M entry (record_row_once Λ a) := by
  intro y hy
  obtain ⟨ht, hn, hl, hb⟩ := hg y hy
  have hf' : ∀ f, a.finality_pair = some f → f.height = y → f.target = entry y := by
    intro f hfp hfy
    simpa only [hfy] using hf f hfp (hfy ▸ hy)
  have hlock : own_lock Λ.toRecord y a.finality_pair = none ∨
      own_lock Λ.toRecord y a.finality_pair = some (entry y) := by
    cases hp : a.finality_pair with
    | none => simpa only [own_lock, hp] using hl
    | some f =>
      by_cases he : f.height = y
      · right; simp only [own_lock, he, ite_true, hf' f hp he]
      · simpa only [own_lock, hp, he, ite_false] using hl
  refine ⟨?_, ?_, ?_, ?_⟩
  · change (record_row Λ.toRecord a).target y = none ∨
      (record_row Λ.toRecord a).target y = some (entry y)
    rcases a with ⟨seat, pair, fp⟩
    cases pair with
    | empty => cases fp <;> simpa [record_row, Record.with_lock] using ht
    | vote g T timeout =>
      by_cases he : y = g
      · subst g
        obtain ⟨rfl, rfl⟩ := hh y T timeout rfl hy
        cases fp <;> simp only [record_row, Record.with_lock]
        all_goals
          by_cases htarget : Λ.target y = none
          · simp [htarget, Record.with_target]
          · simpa [htarget] using ht
      · cases timeout <;> cases fp <;> simp only [record_row] <;>
          (try split) <;> simpa [Record.with_lock, Record.with_timeout,
            Record.with_target, he] using ht
  · change (record_row Λ.toRecord a).timeout y = false
    apply KitFG.record_row_timeout_false_of_ne _ _ hn
    intro T hp
    have := (hh y T true hp hy).2
    cases this
  · exact (KitFG.record_row_lock Λ.toRecord a y) ▸ hlock
  · intro b hmem T timeout hpair
    rcases List.mem_cons.mp hmem with rfl | hmem
    · exact hh y T timeout hpair hy
    · exact hb b hmem T timeout hpair

private theorem recordInv_released_pair (w : HealingWitness)
    (hh : THigh p c E rho w) (hqc : RQCOrigin p c E rho)
    (i : Nat) (x : V) (r : Nat) (seat : Fin p.n) (body : RowPayload)
    (hx : x ∈ rho.honest)
    (ha : (attest p (FGSA.clock p (V2.D.Run.stateBefore E rho i x).st (p.actionTime r))
      (V2.D.Run.stateBefore E rho i x).record ⟨0, p.nPos⟩).1 = some body)
    (hg : recordInv_good w.M (recordInv_entry p c E rho)
      (V2.D.Run.stateBefore E rho i x).record)
    (y : Nat) (T : BlockId) (timeout : Bool)
    (hp : body.height_pair = .vote y T timeout) (hy : w.M + 1 ≤ y)
    (hsource : ∃ C, actionSourceFG p c E rho x r = some (some C) ∧
      (heightView p C).h = y ∧ (heightView p C).T_h.root = T) :
    T = recordInv_entry p c E rho y ∧ timeout = false := by
  let st := FGSA.clock p (V2.D.Run.stateBefore E rho i x).st (p.actionTime r)
  let Λ := (V2.D.Run.stateBefore E rho i x).record
  have hd := (fgsa_attest_decode st Λ seat body ha).symm
  change (createRowOnce p.E p.cfg Λ seat (fgInputs p st).1 (fgInputs p st).2).1 =
    some (body.toRow seat) at hd
  obtain ⟨g, U, tm, hpair, he, _, _, _⟩ :=
    KitFG.createRowOnce_released p.E p.cfg Λ seat (fgInputs p st).1 (fgInputs p st).2 hd
  have hhp := congrArg Row.height_pair he
  change body.height_pair = .vote g U tm at hhp
  rw [hp] at hhp
  cases hhp
  rw [FGSA.attest_source_heightView] at hpair
  have hfields := KitFG.height_pair_vote_fields hpair
  rw [hfields] at hpair
  obtain ⟨C, hs, hc, ht⟩ := hsource
  have hentry := recordInv_entry_source p c E rho w hh x r C hx hs
    (by rw [high_def, hc]; exact hy)
  rw [hc, ht] at hentry
  obtain ⟨htr, hto, hlock, _⟩ := hg y hy
  have hchoice := high_record_target_choice Λ.toRecord y T
    (finality_pair Λ.toRecord (fgInputs p st).2)
    (by simpa only [hentry] using htr) hto (by simpa only [hentry] using hlock)
    (by
      intro fp hf hfy
      have hfroot := recordInv_finality_source p c E rho w hh hqc i x (p.actionTime r)
        Λ.toRecord fp hx hf (hfy ▸ hy)
      rw [hfy, hentry] at hfroot
      exact hfroot)
  rw [hchoice] at hpair
  cases hpair
  exact ⟨hentry.symm, rfl⟩

private theorem recordInv_released_finality (w : HealingWitness)
    (hh : THigh p c E rho w) (hqc : RQCOrigin p c E rho)
    (i : Nat) (x : V) (r : Nat) (seat : Fin p.n) (body : RowPayload)
    (hx : x ∈ rho.honest)
    (ha : (attest p (FGSA.clock p (V2.D.Run.stateBefore E rho i x).st (p.actionTime r))
      (V2.D.Run.stateBefore E rho i x).record ⟨0, p.nPos⟩).1 = some body)
    (f : FinalityPair) (hf : body.finality_pair = some f) (hy : w.M + 1 ≤ f.height) :
    f.target = recordInv_entry p c E rho f.height := by
  let st := FGSA.clock p (V2.D.Run.stateBefore E rho i x).st (p.actionTime r)
  let Λ := (V2.D.Run.stateBefore E rho i x).record
  have hd := (fgsa_attest_decode st Λ seat body ha).symm
  change (createRowOnce p.E p.cfg Λ seat (fgInputs p st).1 (fgInputs p st).2).1 =
    some (body.toRow seat) at hd
  obtain ⟨_, _, _, _, he, _, _, _⟩ :=
    KitFG.createRowOnce_released p.E p.cfg Λ seat (fgInputs p st).1 (fgInputs p st).2 hd
  have hfp := congrArg Row.finality_pair he
  change body.finality_pair = _ at hfp
  rw [hf] at hfp
  exact recordInv_finality_source p c E rho w hh hqc i x (p.actionTime r) Λ.toRecord f
    hx (Option.filter_eq_some_iff.mp hfp.symm).1 hy

private theorem recordInv_own_row (i : Nat) (x : V) (seat : Fin p.n) (body : RowPayload)
    (ho : ofRow p ⟨.seat .fg seat, body⟩ ∈ V2.D.Engine.ownReleasedAt E rho x i) :
    ∃ r, rho.events[i]? = some (.tick x (p.actionTime r)) ∧
      ofRow p ⟨.seat .fg seat, body⟩ ∈ V2.D.Run.emitsAt E rho i ∧
      (attest p (FGSA.clock p (V2.D.Run.stateBefore E rho i x).st (p.actionTime r))
        (V2.D.Run.stateBefore E rho i x).record ⟨0, p.nPos⟩).1 = some body := by
  rw [V2.D.Engine.ownReleasedAt_def] at ho
  split at ho
  · rename_i hnode
    have hem := (List.mem_filter.mp ho).1
    cases hi : rho.events[i]? with
    | none => simp only [V2.D.Run.emitsAt, hi] at hem; cases hem
    | some ev =>
      cases ev with
      | restart z t => simp only [V2.D.Run.emitsAt, hi] at hem; cases hem
      | deliver z o t => simp only [V2.D.Run.emitsAt, hi] at hem; cases hem
      | tick z t =>
        have hz : z = x := by simpa only [hi, Option.map_some, V2.Event.node,
          Option.some.injEq] using hnode
        subst z
        obtain ⟨_, _, r, hr, ha⟩ := (fgsa_emitsAt_row E rho i x t hi seat body).mp hem
        exact ⟨r, by simp only [hr], hem, hr ▸ ha⟩
  · cases ho

private theorem recordInv_all (w : HealingWitness)
    (hh : THigh p c E rho w) (hqc : RQCOrigin p c E rho)
    (hnames : ∀ j x r a e, HonestRowAt p c E rho j x r a →
      namedEntry a.payload.height_pair = some e →
      ∃ C, actionSourceFG p c E rho x r = some (some C) ∧
        e = ((heightView p C).h, (heightView p C).T_h.root))
    (i : Nat) (x : V) (hx : x ∈ rho.honest) :
    recordInv_good w.M (recordInv_entry p c E rho)
      (V2.D.Run.stateBefore E rho i x).record := by
  induction i with
  | zero =>
    rw [ownRecord_fold_run]
    simp only [V2.D.Engine.ownReleased_self]
    change recordInv_good w.M (recordInv_entry p c E rho) RecordOnce.initial
    intro y _
    exact ⟨Or.inl rfl, rfl, Or.inl rfl, fun _ h => (List.not_mem_nil h).elim⟩
  | succ i ih =>
    have hstep : (V2.D.Run.stateBefore E rho (i + 1) x).record =
        (V2.D.Engine.ownReleasedAt E rho x i).foldl (recordRow? p)
          (V2.D.Run.stateBefore E rho i x).record := by
      have hls : V2.D.Engine.ownReleased E rho x 0 (i + 1) =
          V2.D.Engine.ownReleased E rho x 0 i ++ V2.D.Engine.ownReleasedAt E rho x i :=
        V2.D.Engine.ownReleased_succ E rho x (Nat.zero_le i)
      calc
        _ = (V2.D.Engine.ownReleased E rho x 0 (i + 1)).foldl
            (recordRow? p) RecordOnce.initial := ownRecord_fold_run E rho (i + 1) x
        _ = (V2.D.Engine.ownReleased E rho x 0 i ++ V2.D.Engine.ownReleasedAt E rho x i).foldl
            (recordRow? p) RecordOnce.initial := congrArg
              (fun ls : List (Obj p) => ls.foldl (recordRow? p) RecordOnce.initial) hls
        _ = (V2.D.Engine.ownReleasedAt E rho x i).foldl (recordRow? p)
            ((V2.D.Engine.ownReleased E rho x 0 i).foldl (recordRow? p) RecordOnce.initial) :=
          List.foldl_append
        _ = _ := congrArg (fun Λ => (V2.D.Engine.ownReleasedAt E rho x i).foldl
          (recordRow? p) Λ) (ownRecord_fold_run E rho i x).symm
    rw [hstep]
    have preserve : ∀ o ∈ V2.D.Engine.ownReleasedAt E rho x i, ∀ Λ,
        recordInv_good w.M (recordInv_entry p c E rho) Λ →
        recordInv_good w.M (recordInv_entry p c E rho) (recordRow? p Λ o) := by
      intro o ho Λ hg
      rcases o with ⟨auth, msg⟩
      cases auth with
      | none => exact hg
      | seat label seat =>
        cases label with
        | prop s => exact hg
        | base label =>
          cases label with
          | head s => exact hg
          | fg =>
            cases msg with
            | head B => exact hg
            | proposal B raw support rows => exact hg
            | row body =>
              obtain ⟨r, hj, hem, ha⟩ := recordInv_own_row p c E rho i x seat body ho
              apply recordInv_write p _ _ Λ (body.toRow seat) hg
              · intro y T timeout hp hy
                change body.height_pair = .vote y T timeout at hp
                have hn : namedEntry body.height_pair = some (y, T) := by rw [namedEntry_def, hp]
                obtain ⟨C, hs, heq⟩ := hnames i x r _ _ ⟨hx, hj, hem⟩ hn
                have hc := (congrArg Prod.fst heq).symm
                have ht := (congrArg Prod.snd heq).symm
                exact recordInv_released_pair p c E rho w hh hqc i x r seat body hx ha ih
                  y T timeout hp hy ⟨C, hs, hc, ht⟩
              · exact recordInv_released_finality p c E rho w hh hqc i x r seat body hx ha
    have foldGood (ls : List (Obj p)) (hls : ls ⊆ V2.D.Engine.ownReleasedAt E rho x i)
        (Λ : RecordOnce) (hg : recordInv_good w.M (recordInv_entry p c E rho) Λ) :
        recordInv_good w.M (recordInv_entry p c E rho) (ls.foldl (recordRow? p) Λ) := by
      induction ls generalizing Λ with
      | nil => exact hg
      | cons o ls ih =>
        exact ih (fun _ h => hls (List.mem_cons_of_mem _ h)) _
          (preserve o (hls List.mem_cons_self) Λ hg)
    exact foldGood _ (List.Subset.refl _) _ ih

/-- Paper 22:841–879 (FF2): all actual writes preserve the high-entry guards.
DC: INTENTIONAL: H1 and QC origin replace a fixed-root window premise.
Old records rest on THigh .1 over all rounds, not on H0.
The prefix starts at the initial durable record and includes pre-GST writes. -/
theorem high_entry_record_invariant (w : HealingWitness)
    (hh : THigh p c E rho w) (hqc : RQCOrigin p c E rho)
    (hnames : ∀ j x r a e, HonestRowAt p c E rho j x r a →
      namedEntry a.payload.height_pair = some e →
      ∃ C, actionSourceFG p c E rho x r = some (some C) ∧
        e = ((heightView p C).h, (heightView p C).T_h.root)) :
    ∃ entry : Nat → BlockId,
      (∀ x r C, x ∈ rho.honest →
        actionSourceFG p c E rho x r = some (some C) → high p w C →
        entry (heightView p C).h = (heightView p C).T_h.root) ∧
      (∀ i x y, x ∈ rho.honest → w.M + 1 ≤ y →
        let Λ := (V2.D.Run.stateBefore E rho i x).record
        (Λ.target y = none ∨ Λ.target y = some (entry y)) ∧ Λ.timeout y = false ∧
        (Λ.lock y = none ∨ Λ.lock y = some (entry y)) ∧
        ∀ b ∈ Λ.sent, ∀ T timeout, b.1 = .vote y T timeout →
          T = entry y ∧ timeout = false) := by
  refine ⟨recordInv_entry p c E rho, ?_, ?_⟩
  · exact recordInv_entry_source p c E rho w hh
  · intro i x y hx hy
    exact recordInv_all p c E rho w hh hqc hnames i x hx y hy

private def recordInv_fresh (y : Nat) (Λ : RecordOnce) : Prop :=
  Λ.target y = none ∧ Λ.timeout y = false ∧ Λ.lock y = none ∧
    ∀ b ∈ Λ.sent, ∀ T timeout, b.1 ≠ .vote y T timeout

private theorem recordInv_fresh_write (y : Nat) (Λ : RecordOnce)
    (a : Row (Fin p.n)) (hg : recordInv_fresh y Λ)
    (hh : ∃ g T timeout, a.height_pair = .vote g T timeout ∧ g < y)
    (hf : ∀ f, a.finality_pair = some f → f.height < y) :
    recordInv_fresh y (record_row_once Λ a) := by
  obtain ⟨g, T, timeout, hp, hgy⟩ := hh
  rcases a with ⟨seat, pair, fp⟩
  dsimp only at hp
  subst pair
  obtain ⟨ht, hn, hl, hb⟩ := hg
  have hne : y ≠ g := by simp only [Height] at *; omega
  have hlock : own_lock Λ.toRecord y fp = none := by
    cases fp with
    | none => exact hl
    | some f =>
      have hfy : f.height ≠ y := by have := hf f rfl; simp only [Height] at *; omega
      change (if f.height = y then some f.target else Λ.lock y) = none
      rw [ite_eq_right hfy]
      exact hl
  refine ⟨?_, ?_, ?_, ?_⟩
  · change (record_row Λ.toRecord ⟨seat, .vote g T timeout, fp⟩).target y = none
    cases fp <;> cases timeout <;> simp only [record_row] <;>
      (try split) <;> simpa [Record.with_lock, Record.with_target,
        Record.with_timeout, hne] using ht
  · change (record_row Λ.toRecord ⟨seat, .vote g T timeout, fp⟩).timeout y = false
    cases fp <;> cases timeout <;> simp only [record_row] <;>
      (try split) <;> simpa [Record.with_lock, Record.with_target,
        Record.with_timeout, hne] using hn
  · change (record_row Λ.toRecord ⟨seat, .vote g T timeout, fp⟩).lock y = none
    rw [KitFG.record_row_lock]
    exact hlock
  · intro b hm U tm he
    rcases List.mem_cons.mp hm with rfl | hm
    · have := (NamedHeightPair.vote.inj he).1
      simp only [Height] at *; omega
    · exact hb b hm U tm he

private theorem recordInv_own_origin (i : Nat) (x : V) (seat : Fin p.n) (body : RowPayload)
    (ho : ofRow p ⟨.seat .fg seat, body⟩ ∈ V2.D.Engine.ownReleased E rho x 0 i) :
    ∃ j r, j < i ∧ rho.events[j]? = some (.tick x (p.actionTime r)) ∧
      ofRow p ⟨.seat .fg seat, body⟩ ∈ V2.D.Run.emitsAt E rho j ∧
      (attest p (FGSA.clock p (V2.D.Run.stateBefore E rho j x).st (p.actionTime r))
        (V2.D.Run.stateBefore E rho j x).record ⟨0, p.nPos⟩).1 = some body := by
  rw [V2.D.Engine.ownReleased_def] at ho
  obtain ⟨j, hj, ho⟩ := List.mem_flatMap.mp ho
  have hji : j < i := by simpa using hj
  obtain ⟨r, hr, hem, ha⟩ := recordInv_own_row p c E rho j x seat body ho
  exact ⟨j, r, hji, hr, hem, ha⟩

private theorem recordInv_rowHeight_def (a : RowWire p.n) : rowHeight a =
    NamedHeightPair.casesOn (motive := fun _ => Option Nat) a.payload.height_pair
      none (fun h _ _ => some h) := by
  rw [rowHeight_def]
  cases a.payload.height_pair <;> rfl

/-- Paper 22:886–909,1228–1254: no earlier row at or above y leaves y fresh.
DC: INTENTIONAL: durable actual-write history, including restart and suppression. -/
theorem high_record_fresh_at_cut (i : Nat) (x : V) (y : Nat) (hx : x ∈ rho.honest)
    (hbefore : ∀ j r a h, j < i → HonestRowAt p c E rho j x r a →
      rowHeight a = some h → h < y) :
    let Λ := (V2.D.Run.stateBefore E rho i x).record
    Λ.target y = none ∧ Λ.timeout y = false ∧ Λ.lock y = none ∧
      ∀ b ∈ Λ.sent, ∀ T timeout, b.1 ≠ .vote y T timeout := by
  change recordInv_fresh y (V2.D.Run.stateBefore E rho i x).record
  rw [ownRecord_fold_run]
  have preserve : ∀ o ∈ V2.D.Engine.ownReleased E rho x 0 i, ∀ Λ,
      recordInv_fresh y Λ → recordInv_fresh y (recordRow? p Λ o) := by
    intro o ho Λ hg
    rcases o with ⟨auth, msg⟩
    cases auth with
    | none => exact hg
    | seat label seat =>
      cases label with
      | prop s => exact hg
      | base label =>
        cases label with
        | head s => exact hg
        | fg =>
          cases msg with
          | head B => exact hg
          | proposal B raw support rows => exact hg
          | row body =>
            obtain ⟨j, r, hji, hj, hem, ha⟩ := recordInv_own_origin p c E rho i x seat body ho
            let st := FGSA.clock p (V2.D.Run.stateBefore E rho j x).st (p.actionTime r)
            let prior := (V2.D.Run.stateBefore E rho j x).record
            have hd := (fgsa_attest_decode st prior seat body ha).symm
            change (createRowOnce p.E p.cfg prior seat (fgInputs p st).1 (fgInputs p st).2).1 =
              some (body.toRow seat) at hd
            obtain ⟨g, T, timeout, _, he, _, _, _⟩ :=
              KitFG.createRowOnce_released p.E p.cfg prior seat (fgInputs p st).1
                (fgInputs p st).2 hd
            have hp := congrArg Row.height_pair he
            change body.height_pair = .vote g T timeout at hp
            have hrow : rowHeight (⟨.seat .fg seat, body⟩ : RowWire p.n) = some g := by
              rw [recordInv_rowHeight_def]
              change NamedHeightPair.casesOn (motive := fun _ => Option Nat)
                body.height_pair none (fun h _ _ => some h) = _
              rw [hp]
            have hgy := hbefore j r _ g hji ⟨hx, hj, hem⟩ hrow
            apply recordInv_fresh_write p y Λ (body.toRow seat) hg
            · exact ⟨g, T, timeout, hp, hgy⟩
            · intro f hf
              have hfp := congrArg Row.finality_pair he
              change body.finality_pair = _ at hfp
              change body.finality_pair = some f at hf
              rw [hf] at hfp
              have hfg := of_decide_eq_true (Option.filter_eq_some_iff.mp hfp.symm).2
              exact hfg.trans hgy
  have foldFresh (ls : List (Obj p)) (hls : ls ⊆ V2.D.Engine.ownReleased E rho x 0 i)
      (Λ : RecordOnce) (hg : recordInv_fresh y Λ) :
      recordInv_fresh y (ls.foldl (recordRow? p) Λ) := by
    induction ls generalizing Λ with
    | nil => exact hg
    | cons o ls ih =>
      exact ih (fun _ h => hls (List.mem_cons_of_mem _ h)) _
        (preserve o (hls List.mem_cons_self) Λ hg)
  exact foldFresh _ (List.Subset.refl _) RecordOnce.initial
    ⟨rfl, rfl, rfl, fun _ h => (List.not_mem_nil h).elim⟩

private theorem recordInv_once_target (st : State p.n) (Λ : RecordOnce)
    (seat : Fin p.n) (y : Nat) (T : BlockId)
    (hp : height_pair Λ.toRecord
      ((fgInputs p st).1.map (fun C => ((heightView p C).h, (heightView p C).T_h.root)))
      (finality_pair Λ.toRecord (fgInputs p st).2) = .vote y T false)
    (hsent : ∀ b ∈ Λ.sent, ∀ U timeout, b.1 = .vote y U timeout → U = T ∧ timeout = false) :
    (∃ body, (attest p st Λ seat).1 = some body ∧ body.height_pair = .vote y T false) ∨
      ∃ b ∈ Λ.sent, b.1 = .vote y T false := by
  by_cases hs : sameHeightOnce Λ y T false = true
  · right
    obtain ⟨⟨pair, fp⟩, hm, hpair⟩ := List.any_eq_true.mp hs
    cases pair with
    | empty => cases hpair
    | vote g U timeout =>
      change (decide (g = y) && (!false || decide (U = T))) = true at hpair
      have hg : g = y := of_decide_eq_true (Bool.and_eq_true_iff.mp hpair).1
      subst g
      obtain ⟨rfl, rfl⟩ := hsent _ hm U timeout rfl
      exact ⟨_, hm, rfl⟩
  · let a : Row (Fin p.n) := ⟨seat, .vote y T false,
      (finality_pair Λ.toRecord (fgInputs p st).2).filter (fun fp => decide (fp.height < y))⟩
    by_cases hm : a.onceKey ∈ Λ.sent
    · exact Or.inr ⟨a.onceKey, hm, rfl⟩
    · left
      refine ⟨.vote (RowBody.ofRow a), ?_, rfl⟩
      have ha : (createRowOnce p.E p.cfg Λ seat (fgInputs p st).1 (fgInputs p st).2).1 =
          some a := by
        rw [createRowOnce_def]
        dsimp only
        rw [FGSA.attest_source_heightView, hp]
        simp only [hs, Bool.false_eq_true, ite_false]
        change (if a.onceKey ∈ Λ.sent then (none, Λ) else
          (some a, record_row_once Λ a)).1 = some a
        rw [ite_eq_right hm]
      change Option.map (fun a => RowPayload.vote (RowBody.ofRow a))
        (createRowOnce p.E p.cfg Λ seat (fgInputs p st).1 (fgInputs p st).2).1 = _
      rw [ha]; rfl

private theorem recordInv_sent_origin (ls : List (Obj p)) (Λ : RecordOnce)
    (b : NamedHeightPair × Option FinalityPair) (hm : b ∈ (ls.foldl (recordRow? p) Λ).sent) :
    b ∈ Λ.sent ∨ ∃ seat body, ofRow p ⟨.seat .fg seat, body⟩ ∈ ls ∧
      (body.height_pair, body.finality_pair) = b := by
  induction ls generalizing Λ with
  | nil => exact Or.inl hm
  | cons o ls ih =>
    rcases ih (recordRow? p Λ o) hm with hold | ⟨seat, body, hm, he⟩
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
            | proposal B raw support rows => exact Or.inl hold
            | row body =>
              rcases List.mem_cons.mp hold with he | hold
              · exact Or.inr ⟨seat, body, List.mem_cons_self, he.symm⟩
              · exact Or.inl hold
    · exact Or.inr ⟨seat, body, List.mem_cons_of_mem _ hm, he⟩

private theorem recordInv_complete (i : Nat) (x : V) (r : Nat)
    (seat : Fin p.n) (body : RowPayload)
    (hj : rho.events[i]? = some (.tick x (p.actionTime r)))
    (hem : ofRow p ⟨.seat .fg seat, body⟩ ∈ V2.D.Run.emitsAt E rho i) :
    RowComplete p c rho x ⟨.seat .fg seat, body⟩ := by
  obtain ⟨_, hseat, _, _, hb⟩ := (fgsa_emitsAt_row E rho i x _ hj seat body).mp hem
  refine ⟨?_, ?_⟩
  · obtain ⟨a, ha, hbody⟩ := Option.map_eq_some_iff.mp hb
    obtain ⟨h, T, timeout, hp, he, _, _, _⟩ :=
      KitFG.createRowOnce_released p.E p.cfg _ ⟨0, p.nPos⟩ _ _ ha
    rw [FGSA.attest_source_heightView] at hp
    have hf := KitFG.height_pair_vote_fields hp
    obtain ⟨C, _, hc⟩ := Option.map_eq_some_iff.mp hf
    have heh := congrArg Prod.fst hc
    change (heightView p C).h = h at heh
    have hpos : 1 ≤ h := heh ▸ (fgCertificateLaws p).height.one_le_h C
    rw [← hbody, he]
    change (decide (1 ≤ h) &&
      ((finality_pair _ _).filter (fun fp => decide (fp.height < h))
        |>.map (fun fp => decide (fp.height < h))).getD true) = true
    cases hfp : finality_pair _ _ with
    | none => simp [hpos, Option.filter]
    | some fp => by_cases hlt : fp.height < h <;> simp [hpos, Option.filter, hlt]
  · rw [RowSigner_def]
    exact ⟨seat, rfl, hseat⟩

/-- Paper 22:886–915 (SO-COV): an earlier or current complete target covers the action.
DC: INTENTIONAL: FF2 proves the target bit; both send-once checks use durable content. -/
theorem high_target_row_covered (w : HealingWitness)
    (hh : THigh p c E rho w) (hqc : RQCOrigin p c E rho)
    (hnames : ∀ j x r a e, HonestRowAt p c E rho j x r a →
      namedEntry a.payload.height_pair = some e →
      ∃ C, actionSourceFG p c E rho x r = some (some C) ∧
        e = ((heightView p C).h, (heightView p C).T_h.root))
    (hL : V2.D.Linked (fgsaFamilies p c).linked rho)
    (hS : V2.D.ScheduleWellFormed E rho)
    (x : V) (hx : x ∈ rho.honest) (r : Nat) (C : FGBlock (Fin p.n))
    (hsource : actionSourceFG p c E rho x r = some (some C))
    (hhigh : high p w C) (hawake : E.awake x (p.actionTime r) = true) :
    ∃ j rSent a, rSent ≤ r ∧ HonestRowAt p c E rho j x rSent a ∧
      RowComplete p c rho x a ∧
      a.payload.height_pair = .vote (heightView p C).h (heightView p C).T_h.root false := by
  classical
  rw [actionSourceFG_def, postClock_def, preTick_def] at hsource
  cases hi : V2.D.Run.tickIdx? rho x (p.actionTime r) with
  | none => simp only [hi, Option.map_none] at hsource; contradiction
  | some i =>
    simp only [hi, Option.map_some, Option.some.injEq] at hsource
    have hj := V2.D.Run.tickIdx?_spec hi
    let st := FGSA.clock p (V2.D.Run.stateBefore E rho i x).st (p.actionTime r)
    let Λ := (V2.D.Run.stateBefore E rho i x).record
    have hs : actionSourceFG p c E rho x r = some (some C) := by
      rw [actionSourceFG_def, postClock_def, preTick_def, hi]
      exact congrArg some hsource
    have hentry := recordInv_entry_source p c E rho w hh x r C hx hs hhigh
    have hg := recordInv_all p c E rho w hh hqc hnames i x hx (heightView p C).h hhigh
    obtain ⟨ht, hn, hl, hsent⟩ := hg
    have hp := high_record_target_choice Λ.toRecord (heightView p C).h
      (heightView p C).T_h.root (finality_pair Λ.toRecord (fgInputs p st).2)
      (by simpa only [hentry] using ht) hn (by simpa only [hentry] using hl)
      (by
        intro fp hf hfy
        have hr := recordInv_finality_source p c E rho w hh hqc i x (p.actionTime r)
          Λ.toRecord fp hx hf (hfy ▸ hhigh)
        simpa only [hfy, hentry] using hr)
    have hpair : height_pair Λ.toRecord
        ((fgInputs p st).1.map (fun C => ((heightView p C).h, (heightView p C).T_h.root)))
        (finality_pair Λ.toRecord (fgInputs p st).2) =
          .vote (heightView p C).h (heightView p C).T_h.root false := by
      change height_pair _ ((fgSource p st).map _) _ = _
      change fgSource p st = some C at hsource
      rw [hsource]
      exact hp
    obtain ⟨seat, hseat⟩ := (hL.toCStar (.base .fg) trivial).2 x
    rcases recordInv_once_target p st Λ seat _ _ hpair
      (by simpa only [hentry] using hsent) with ⟨body, hattest, htarget⟩ | ⟨b, hb, htarget⟩
    · have hem : ofRow p ⟨.seat .fg seat, body⟩ ∈ V2.D.Run.emitsAt E rho i :=
        (fgsa_emitsAt_row E rho i x _ hj seat body).mpr
          ⟨hawake, hseat, r, rfl, by rwa [attest_signer_irrel st Λ seat ⟨0, p.nPos⟩] at hattest⟩
      exact ⟨i, r, ⟨.seat .fg seat, body⟩, le_rfl, ⟨hx, hj, hem⟩,
        recordInv_complete p c E rho i x r seat body hj hem, htarget⟩
    · change b ∈ (V2.D.Run.stateBefore E rho i x).record.sent at hb
      rw [ownRecord_fold_run] at hb
      rcases recordInv_sent_origin p _ RecordOnce.initial b hb with hb | ⟨seat, body, hm, he⟩
      · cases hb
      obtain ⟨j, rSent, hji, hjs, hem, _⟩ := recordInv_own_origin p c E rho i x seat body hm
      have htime := fgsa_tick_time_strict E rho hS hjs hj hji
      have hr : rSent ≤ r := by
        by_contra h
        have hcast : ((r * p.R : Nat) : Time) < ((rSent * p.R : Nat) : Time) := by
          exact_mod_cast (Nat.mul_lt_mul_of_pos_right (show r < rSent by omega)
            (show 0 < p.R by have := p.RLarge; omega))
        change 4 * p.Δ * ((rSent * p.R : Nat) : Time) + 6 * p.Δ <
          4 * p.Δ * ((r * p.R : Nat) : Time) + 6 * p.Δ at htime
        have := p.deltaPos
        nlinarith
      exact ⟨j, rSent, ⟨.seat .fg seat, body⟩, hr, ⟨hx, hjs, hem⟩,
        recordInv_complete p c E rho j x rSent seat body hjs hem,
        (congrArg Prod.fst he).trans htarget⟩

/-- Paper 22:841–879: the raw H0 cut has no high target, timeout, lock, or sent row.
DC: INTENTIONAL: the inclusive raw cut uses H0's emission cap, including old sends. -/
theorem high_record_reset_fresh (w : HealingWitness) (h0 : H0Reset p c E rho w)
    (hs : V2.D.ScheduleWellFormed E rho) (x : V) (hx : x ∈ rho.honest)
    (y : Nat) (hy : w.M + 1 ≤ y) :
    let Λ := (V2.D.Run.stateBefore E rho (afterTicksIdx rho w.u₀) x).record
    Λ.target y = none ∧ Λ.timeout y = false ∧ Λ.lock y = none ∧
      ∀ b ∈ Λ.sent, ∀ T timeout, b.1 ≠ .vote y T timeout := by
  apply high_record_fresh_at_cut p c E rho _ x y hx
  intro j r a h hj ha hh
  have hf := V2.D.Engine.filter_eq_take hs (cutPred w.u₀) (by
    intro e f hk hmem
    exact decide_eq_true (hk.trans (of_decide_eq_true hmem)))
  have hm : (.tick x (p.actionTime r) : V2.Event V (fgsa p c).Object) ∈
      rho.events.filter (cutPred w.u₀) := by
    rw [hf]
    apply List.mem_of_getElem? (i := j)
    change j < (rho.events.filter (cutPred w.u₀)).length at hj
    rw [List.getElem?_take_of_lt hj]
    exact ha.2.1
  have hkey := of_decide_eq_true (List.mem_filter.mp hm).2
  have ht : p.actionTime r ≤ w.u₀ := by
    change toLex (p.actionTime r, (1 : Nat)) ≤ toLex (w.u₀, 1) at hkey
    rcases Prod.Lex.toLex_le_toLex.mp hkey with h | ⟨h, _⟩
    · exact h.le
    · exact h.le
  rw [recordInv_rowHeight_def] at hh
  cases hp : a.payload.height_pair with
  | empty => rw [hp] at hh; cases hh
  | vote g T timeout =>
    have hgh : g = h := by
      rw [hp] at hh
      exact Option.some.inj hh
    have hcap := h0.rowCap j x r a g T (p.actionTime r) ha ha.2.1 ht (by rw [namedEntry_def, hp])
    simp only [Height] at *
    omega

/-- Paper 22:841–879,1228–1254: the exact K-ROWS record premise at a prefix cut.
DC: INTENTIONAL: FF2 at y and durable freshness at y+1 share the actual record. -/
theorem high_record_guards_and_fresh (w : HealingWitness)
    (hh : THigh p c E rho w) (hqc : RQCOrigin p c E rho)
    (hnames : ∀ j x r a e, HonestRowAt p c E rho j x r a →
      namedEntry a.payload.height_pair = some e →
      ∃ C, actionSourceFG p c E rho x r = some (some C) ∧
        e = ((heightView p C).h, (heightView p C).T_h.root))
    (z : V) (r : Nat) (C : FGBlock (Fin p.n)) (hz : z ∈ rho.honest)
    (hsource : actionSourceFG p c E rho z r = some (some C))
    (y : Nat) (hheight : (heightView p C).h = y) (hy : w.M + 1 ≤ y)
    (i : Nat) (x : V) (hx : x ∈ rho.honest)
    (hbefore : ∀ j r a h, j < i → HonestRowAt p c E rho j x r a →
      rowHeight a = some h → h < y + 1) :
    let Λ := (V2.D.Run.stateBefore E rho i x).record
    (Λ.target y = none ∨ Λ.target y = some (heightView p C).T_h.root) ∧
      Λ.timeout y = false ∧
      (Λ.lock y = none ∨ Λ.lock y = some (heightView p C).T_h.root) ∧
      Λ.target (y + 1) = none ∧ Λ.timeout (y + 1) = false ∧ Λ.lock (y + 1) = none ∧
      ∀ b ∈ Λ.sent, ∀ T timeout, b.1 ≠ .vote (y + 1) T timeout := by
  have hentry := recordInv_entry_source p c E rho w hh z r C hz hsource
    (by rw [high_def, hheight]; exact hy)
  rw [hheight] at hentry
  obtain ⟨ht, hn, hl, _⟩ := recordInv_all p c E rho w hh hqc hnames i x hx y hy
  rw [hentry] at ht hl
  exact ⟨ht, hn, hl, high_record_fresh_at_cut p c E rho i x (y + 1) hx hbefore⟩

/-- Paper 22:886–909,1208–1211: the first high target cannot be suppressed.
DC: INTENTIONAL: an earlier covering send contradicts the strict raw height cap. -/
theorem high_target_first_row (w : HealingWitness)
    (hh : THigh p c E rho w) (hqc : RQCOrigin p c E rho)
    (hnames : ∀ j x r a e, HonestRowAt p c E rho j x r a →
      namedEntry a.payload.height_pair = some e →
      ∃ C, actionSourceFG p c E rho x r = some (some C) ∧
        e = ((heightView p C).h, (heightView p C).T_h.root))
    (hL : V2.D.Linked (fgsaFamilies p c).linked rho)
    (hS : V2.D.ScheduleWellFormed E rho)
    (x : V) (hx : x ∈ rho.honest) (r : Nat) (C : FGBlock (Fin p.n))
    (hsource : actionSourceFG p c E rho x r = some (some C))
    (hhigh : high p w C) (hawake : E.awake x (p.actionTime r) = true)
    (hbefore : ∀ j q a h, q < r → HonestRowAt p c E rho j x q a →
      rowHeight a = some h → h < (heightView p C).h) :
    ∃ j a, HonestRowAt p c E rho j x r a ∧ RowComplete p c rho x a ∧
      a.payload.height_pair = .vote (heightView p C).h (heightView p C).T_h.root false := by
  obtain ⟨j, q, a, hqr, ha, hc, hp⟩ := high_target_row_covered p c E rho w hh hqc hnames
    hL hS x hx r C hsource hhigh hawake
  have hq : q = r := by
    by_contra hne
    have hlt := hbefore j q a _ (lt_of_le_of_ne hqr hne) ha (by
      rw [recordInv_rowHeight_def]
      rw [hp])
    exact (Nat.lt_irrefl _ hlt).elim
  subst q
  exact ⟨j, a, ha, hc, hp⟩

private theorem recordInv_honestSeats_def : honestSeats p c rho =
    @Finset.filter (Fin p.n) (fun i => rho.seatOf (.base .fg) i ∈ rho.honest)
      (fun i => Classical.propDecidable (rho.seatOf (.base .fg) i ∈ rho.honest)) Finset.univ :=
  honestSeats_def p c rho

private theorem recordInv_honestSeats_mem (i : Fin p.n) :
    i ∈ honestSeats p c rho ↔ rho.seatOf (.base .fg) i ∈ rho.honest := by
  rw [recordInv_honestSeats_def p c rho]
  simpa only [Finset.mem_univ, true_and] using
    (@Finset.mem_filter (Fin p.n) (fun k => rho.seatOf (.base .fg) k ∈ rho.honest)
      (fun k => Classical.propDecidable (rho.seatOf (.base .fg) k ∈ rho.honest)) Finset.univ i)

/-- Paper 22:886–915: the Recovery fault bound supplies an honest unit-weight quorum.
DC: INTENTIONAL: linked fixed FG seats transport honest identity cardinality. -/
theorem high_target_honest_quorum [Fintype V]
    (hL : V2.D.Linked (fgsaFamilies p c).linked rho)
    (hf : (Gen.V2.Duty.faulty rho).card ≤ (p.n - 1) / 3) :
    p.E.IsQuorum (honestSeats p c rho) := by
  classical
  obtain ⟨e, he⟩ := fgsa_linked_seats rho hL
  have he' : ∀ j : Fin p.n, rho.seatOf (.base .fg) j = e j := he
  let seatOf : Fin p.n → V := rho.seatOf (.base .fg)
  have himage : (honestSeats p c rho).image seatOf = rho.honest := by
    ext x
    constructor
    · rintro hx
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
      exact (recordInv_honestSeats_mem p c rho i).mp hi
    · intro hx
      refine Finset.mem_image.mpr ⟨e.symm x, ?_, ?_⟩
      · apply (recordInv_honestSeats_mem p c rho _).mpr
        rw [he', Equiv.apply_symm_apply]
        exact hx
      · exact (he' _).trans (e.apply_symm_apply x)
  have hinj : Function.Injective seatOf := by
    intro k l h
    exact e.injective ((he' k).symm.trans (h.trans (he' l)))
  have hcard : (honestSeats p c rho).card = rho.honest.card := by
    exact (Finset.card_image_of_injective _ hinj).symm.trans (congrArg Finset.card himage)
  have hn : Fintype.card V = p.n := by
    rw [← Fintype.card_congr e, Fintype.card_fin]
  have hbound := Finset.card_le_univ rho.honest
  rw [hn] at hbound
  have hsum : (Gen.V2.Duty.faulty rho).card + rho.honest.card = p.n := by
    rw [Gen.V2.Duty.faulty_def, Finset.card_sdiff_of_subset (Finset.subset_univ _),
      Finset.card_univ, hn]
    omega
  have hq : p.E.q = Gen.Pure.qF p.n :=
    (KitFG.toWeights_q p.E).symm.trans (KitFG.unit_toWeights_q p.n)
  change p.E.q ≤ p.E.weightOf (honestSeats p c rho)
  have hw : p.E.weightOf (honestSeats p c rho) = (honestSeats p c rho).card := by
    change (∑ _ ∈ honestSeats p c rho, (1 : Nat)) = _
    simp
  rw [hq, hw, hcard, Gen.Pure.qF_def]
  have := p.nPos
  omega

/-- Paper 22:886–915: each honest quorum seat has a complete target and its exact receipt.
DC: INTENTIONAL: strict max(emission,GST)+ΔF receipt includes old suppressed sends. -/
theorem high_target_quorum_covered [Fintype V] (G ΔF : Time)
    (hrec : Recovery₂ p c E rho G ΔF) (w : HealingWitness)
    (hh : THigh p c E rho w) (hqc : RQCOrigin p c E rho)
    (hnames : ∀ j x r a e, HonestRowAt p c E rho j x r a →
      namedEntry a.payload.height_pair = some e →
      ∃ C, actionSourceFG p c E rho x r = some (some C) ∧
        e = ((heightView p C).h, (heightView p C).T_h.root))
    (hreceipt : TRowsReceipt p c E rho ΔF)
    (r : Nat) (C : FGBlock (Fin p.n)) (hhigh : high p w C)
    (hsource : ∀ x ∈ rho.honest, actionSourceFG p c E rho x r = some (some C))
    (hGST : E.t_GST ≤ p.actionTime r)
    (hhor : p.actionTime r + ΔF ≤ rho.horizon) :
    p.E.IsQuorum (honestSeats p c rho) ∧
      ∃ rows : Fin p.n → RowWire p.n, ∀ i ∈ honestSeats p c rho, ∃ j rSent,
        rSent ≤ r ∧
        HonestRowAt p c E rho j (rho.seatOf (.base .fg) i) rSent (rows i) ∧
        RowComplete p c rho (rho.seatOf (.base .fg) i) (rows i) ∧
        (rows i).auth = .seat .fg i ∧
        (rows i).payload.height_pair =
          .vote (heightView p C).h (heightView p C).T_h.root false ∧
        ∀ x ∈ rho.honest, HeldBefore p c E rho x (rows i)
          (max (p.actionTime rSent) E.t_GST + ΔF) := by
  classical
  refine ⟨high_target_honest_quorum p c rho hrec.base.linked hrec.fault, ?_⟩
  have haction : p.actionTime r ≤ rho.horizon := by
    have := E.Δ_pos.trans_le hrec.deltaF
    linarith
  have hseat : ∀ i : Fin p.n, ∃ a, i ∈ honestSeats p c rho → ∃ j rSent,
      rSent ≤ r ∧ HonestRowAt p c E rho j (rho.seatOf (.base .fg) i) rSent a ∧
      RowComplete p c rho (rho.seatOf (.base .fg) i) a ∧ a.auth = .seat .fg i ∧
      a.payload.height_pair = .vote (heightView p C).h (heightView p C).T_h.root false ∧
      ∀ x ∈ rho.honest, HeldBefore p c E rho x a
        (max (p.actionTime rSent) E.t_GST + ΔF) := by
    intro i
    by_cases hi : i ∈ honestSeats p c rho
    · have hx := (recordInv_honestSeats_mem p c rho i).mp hi
      obtain ⟨j, rSent, a, hr, ha, hc, hp⟩ := high_target_row_covered p c E rho w hh hqc
        hnames hrec.base.linked hrec.base.valid.toScheduleWellFormed _ hx r C
        (hsource _ hx) hhigh (hrec.awake _ hx _ hGST haction)
      have hauth : a.auth = .seat .fg i := by
        obtain ⟨k, hk, hki⟩ := hc.2
        have hinj := (hrec.base.linked.toCStar (.base .fg) trivial).1
        exact hk.trans (congrArg (fun k => Auth.seat Label.fg k) (hinj hki))
      have htime : p.actionTime rSent ≤ p.actionTime r := by
        have hmul : rSent * p.R ≤ r * p.R := Nat.mul_le_mul_right p.R hr
        have hcast : ((rSent * p.R : Nat) : Time) ≤ ((r * p.R : Nat) : Time) :=
          by exact_mod_cast hmul
        change 4 * p.Δ * ((rSent * p.R : Nat) : Time) + 6 * p.Δ ≤
          4 * p.Δ * ((r * p.R : Nat) : Time) + 6 * p.Δ
        have := p.deltaPos
        nlinarith
      have hdeadline : max (p.actionTime rSent) E.t_GST + ΔF ≤ rho.horizon := by
        have := max_le htime hGST
        linarith
      exact ⟨a, fun _ => ⟨j, rSent, hr, ha, hc, hauth, hp, hreceipt j _ rSent a ha hdeadline⟩⟩
    · exact ⟨⟨.seat .fg i, .vote ⟨.empty, none⟩⟩, fun h => (hi h).elim⟩
  choose rows hrows using hseat
  exact ⟨rows, hrows⟩

/-- Paper 22:841–879: FF2 selects a high target with the actual head's own lock.
DC: Protocol/ValidatorClient.lean:216–229; the head target QC fixes its lock. -/
theorem high_action_target_choice (w : HealingWitness)
    (hh : THigh p c E rho w) (hqc : RQCOrigin p c E rho)
    (hnames : ∀ j x r a e, HonestRowAt p c E rho j x r a →
      namedEntry a.payload.height_pair = some e →
      ∃ C, actionSourceFG p c E rho x r = some (some C) ∧
        e = ((heightView p C).h, (heightView p C).T_h.root))
    (z : V) (r : Nat) (C : FGBlock (Fin p.n)) (hz : z ∈ rho.honest)
    (hsource : actionSourceFG p c E rho z r = some (some C)) (hhigh : high p w C)
    (i : Nat) (x : V) (t : Time) (hx : x ∈ rho.honest) :
    let Λ := (V2.D.Run.stateBefore E rho i x).record
    let st := FGSA.clock p (V2.D.Run.stateBefore E rho i x).st t
    height_pair Λ.toRecord (some ((heightView p C).h, (heightView p C).T_h.root))
      (finality_pair Λ.toRecord (FGSA.fgInputs p st).2) =
      .vote (heightView p C).h (heightView p C).T_h.root false := by
  have hentry := recordInv_entry_source p c E rho w hh z r C hz hsource hhigh
  obtain ⟨ht, hn, hl, _⟩ := recordInv_all p c E rho w hh hqc hnames i x hx
    (heightView p C).h hhigh
  apply high_record_target_choice
  · simpa only [hentry] using ht
  · exact hn
  · simpa only [hentry] using hl
  · intro fp hf hfy
    have hr := recordInv_finality_source p c E rho w hh hqc i x t
      (V2.D.Run.stateBefore E rho i x).record.toRecord fp hx hf (hfy ▸ hhigh)
    simpa only [hfy, hentry] using hr

/-- Paper 22:841–879,1256–1263: the K-ROWS record guards at the actual action read.
DC: INTENTIONAL: the round cut becomes a prefix cut by strict tick time;
clock_rec transports all seven fields to the postClock record. -/
theorem high_record_guards_and_fresh_at_action (w : HealingWitness)
    (hh : THigh p c E rho w) (hqc : RQCOrigin p c E rho)
    (hnames : ∀ j x r a e, HonestRowAt p c E rho j x r a →
      namedEntry a.payload.height_pair = some e →
      ∃ C, actionSourceFG p c E rho x r = some (some C) ∧
        e = ((heightView p C).h, (heightView p C).T_h.root))
    (hs : V2.D.ScheduleWellFormed E rho)
    (z : V) (r : Nat) (C : FGBlock (Fin p.n)) (hz : z ∈ rho.honest)
    (hsource : actionSourceFG p c E rho z r = some (some C))
    (y : Nat) (hheight : (heightView p C).h = y) (hy : w.M + 1 ≤ y)
    (q : Nat) (x : V) (hx : x ∈ rho.honest)
    (hbefore : ∀ j r a h, r < q → HonestRowAt p c E rho j x r a →
      rowHeight a = some h → h < y + 1) :
    ∀ nd, postClock E rho x (p.actionTime q) = some nd →
      (nd.record.target y = none ∨ nd.record.target y = some (heightView p C).T_h.root) ∧
      nd.record.timeout y = false ∧
      (nd.record.lock y = none ∨ nd.record.lock y = some (heightView p C).T_h.root) ∧
      nd.record.target (y + 1) = none ∧ nd.record.timeout (y + 1) = false ∧
      nd.record.lock (y + 1) = none ∧
      ∀ b ∈ nd.record.sent, ∀ T timeout, b.1 ≠ .vote (y + 1) T timeout := by
  intro nd hnd
  rw [postClock_def, preTick_def] at hnd
  cases hi : V2.D.Run.tickIdx? rho x (p.actionTime q) with
  | none => simp only [hi, Option.map_none] at hnd; contradiction
  | some i =>
    simp only [hi, Option.map_some, Option.some.injEq] at hnd
    have hj := V2.D.Run.tickIdx?_spec hi
    have hr : (V2.D.Run.stateBefore E rho i x).record = nd.record :=
      (clock_rec (c := c) (V2.D.Run.stateBefore E rho i x) (p.actionTime q)).symm.trans
        (congrArg Node.record hnd)
    have hg := high_record_guards_and_fresh p c E rho w hh hqc hnames z r C hz hsource
      y hheight hy i x hx (by
        intro j r a h hji ha hah
        have ht := fgsa_tick_time_strict E rho hs ha.2.1 hj hji
        have hrq : r < q := by
          by_contra hn
          have hmul : ((q * p.R : Nat) : Time) ≤ ((r * p.R : Nat) : Time) := by
            exact_mod_cast Nat.mul_le_mul_right p.R (show q ≤ r by omega)
          change 4 * p.Δ * ((r * p.R : Nat) : Time) + 6 * p.Δ <
            4 * p.Δ * ((q * p.R : Nat) : Time) + 6 * p.Δ at ht
          have := p.deltaPos
          nlinarith
        exact hbefore j r a h hrq ha hah)
    change (let Λ := (V2.D.Run.stateBefore E rho i x).record; _) at hg
    simpa only [hr] using hg

private theorem recordInv_honest_pair (w : HealingWitness)
    (hh : THigh p c E rho w) (hqc : RQCOrigin p c E rho)
    (hnames : ∀ j x r a e, HonestRowAt p c E rho j x r a →
      namedEntry a.payload.height_pair = some e →
      ∃ C, actionSourceFG p c E rho x r = some (some C) ∧
        e = ((heightView p C).h, (heightView p C).T_h.root))
    (j : Nat) (x : V) (r : Nat) (wire : RowWire p.n) (a : Row (Fin p.n))
    (ha : HonestRowAt p c E rho j x r wire) (hd : wire.toRow? = some a)
    (y : Nat) (T : BlockId) (hn : namedEntry a.height_pair = some (y, T))
    (hy : w.M + 1 ≤ y) :
    a.height_pair = .vote y (recordInv_entry p c E rho y) false := by
  cases hp : a.height_pair with
  | empty => rw [hp] at hn; cases hn
  | vote g U timeout =>
    rw [hp] at hn
    rw [namedEntry_def] at hn
    have he : (g, U) = (y, T) := Option.some.inj hn
    cases he
    rcases wire with ⟨auth, body⟩
    cases auth with
    | none => cases hd
    | proposer s => cases hd
    | seat label seat =>
      cases label with
      | head s => cases hd
      | fg =>
        have he := Option.some.inj hd
        have hb : body.height_pair = .vote y T timeout :=
          (congrArg Row.height_pair he).trans hp
        obtain ⟨_, _, _, _, hsend⟩ :=
          (fgsa_emitsAt_row E rho j x (p.actionTime r) ha.2.1 seat body).mp ha.2.2
        have hnwire : namedEntry body.height_pair = some (y, T) := by rw [namedEntry_def, hb]
        obtain ⟨C, hs, hc⟩ := hnames j x r _ _ ha hnwire
        obtain ⟨hroot, htimeout⟩ := recordInv_released_pair p c E rho w hh hqc j x r
          seat body ha.1 hsend (recordInv_all p c E rho w hh hqc hnames j x ha.1)
          y T timeout hb hy ⟨C, hs, (congrArg Prod.fst hc).symm,
            (congrArg Prod.snd hc).symm⟩
        rw [hroot, htimeout]

private theorem recordInv_qc_source (w : HealingWitness) (hh : THigh p c E rho w)
    (i : Nat) (z : V) (r : Nat) (wire : RowWire p.n) (a : Row (Fin p.n))
    (C : FGBlock (Fin p.n)) (y : Nat) (T : BlockId)
    (hb : HonestRowBefore p c E rho i z r wire)
    (hs : actionSourceFG p c E rho z r = some (some C))
    (hn : namedEntry a.height_pair = some ((heightView p C).h, (heightView p C).T_h.root))
    (hp : namedEntry a.height_pair = some (y, T)) (hy : w.M + 1 ≤ y) :
    z ∈ rho.honest ∧ high p w C ∧ (heightView p C).h = y ∧
      T = (heightView p C).T_h.root ∧ T = recordInv_entry p c E rho y := by
  obtain ⟨j, _, ha⟩ := hb
  have he := Option.some.inj (hn.symm.trans hp)
  have hc : (heightView p C).h = y := congrArg Prod.fst he
  have ht : T = (heightView p C).T_h.root := (congrArg Prod.snd he).symm
  have hhigh : high p w C := by rw [high_def, hc]; exact hy
  have hentry := recordInv_entry_source p c E rho w hh z r C ha.1 hs hhigh
  rw [hc] at hentry
  exact ⟨ha.1, hhigh, hc, ht, ht.trans hentry.symm⟩

private theorem recordInv_quorum_honest [Fintype V]
    (hL : V2.D.Linked (fgsaFamilies p c).linked rho)
    (hf : Gen.Pure.FaultQ p.n (Gen.V2.Duty.faulty rho).card)
    (Q : Finset (Fin p.n)) (hQ : p.E.IsQuorum Q) :
    ∃ k ∈ Q, rho.seatOf (.base .fg) k ∈ rho.honest := by
  classical
  obtain ⟨e, he⟩ := fgsa_linked_seats rho hL
  have he' : ∀ j : Fin p.n, rho.seatOf (.base .fg) j = e j := he
  let F := (Gen.V2.Duty.faulty rho).map e.symm.toEmbedding
  have hcap : p.E.toWeights.weightOf F < p.E.toWeights.q := by
    have hq : p.E.toWeights.q = Gen.Pure.qF p.n := KitFG.unit_toWeights_q p.n
    rw [hq]
    have hc : p.E.toWeights.weightOf F = (Gen.V2.Duty.faulty rho).card := by
      rw [KitFG.toWeights_weightOf]
      change (∑ _ ∈ F, (1 : Nat)) = _
      simp only [Finset.sum_const, smul_eq_mul, mul_one, Finset.card_map, F]
    rw [hc]
    exact hf.lt
  obtain ⟨k, hk, hn⟩ := Gen.Pure.quorum_honest p.E.toWeights F
    ((KitFG.isQuorum_toWeights_iff p.E Q).mpr hQ) hcap
  refine ⟨k, hk, ?_⟩
  rw [he']
  by_contra hh
  apply hn
  exact Finset.mem_map.mpr ⟨e k, by simpa [Gen.V2.Duty.faulty_def] using hh,
    e.symm_apply_apply k⟩

private theorem recordInv_decoded_height (wire : RowWire p.n) (a : Row (Fin p.n))
    (hd : wire.toRow? = some a) : wire.payload.height_pair = a.height_pair := by
  rcases wire with ⟨auth, body⟩
  cases auth with
  | none => cases hd
  | proposer s => cases hd
  | seat label seat =>
    cases label with
    | head s => cases hd
    | fg => exact congrArg Row.height_pair (Option.some.inj hd)

private theorem recordInv_honest_finality (w : HealingWitness)
    (hh : THigh p c E rho w) (hqc : RQCOrigin p c E rho)
    (j : Nat) (x : V) (r : Nat) (wire : RowWire p.n) (a : Row (Fin p.n))
    (ha : HonestRowAt p c E rho j x r wire) (hd : wire.toRow? = some a)
    (fp : FinalityPair) (hf : a.finality_pair = some fp) (hy : w.M + 1 ≤ fp.height) :
    fp.target = recordInv_entry p c E rho fp.height := by
  rcases wire with ⟨auth, body⟩
  cases auth with
  | none => cases hd
  | proposer s => cases hd
  | seat label seat =>
    cases label with
    | head s => cases hd
    | fg =>
      have hbody : body.finality_pair = some fp :=
        (congrArg Row.finality_pair (Option.some.inj hd)).trans hf
      obtain ⟨_, _, _, _, hsend⟩ :=
        (fgsa_emitsAt_row E rho j x (p.actionTime r) ha.2.1 seat body).mp ha.2.2
      exact recordInv_released_finality p c E rho w hh hqc j x r seat body ha.1
        hsend fp hbody hy

/-- Paper 22:876–879: every high target, progress, or finality QC in cumulative TF has one identity.
DC: INTENTIONAL: honest row origins include delayed disclosures and pre-GST writes.
There is no carrier-height guard; matchesEntry permits either timeout bit. -/
theorem ff2_stored_high_qc_identity [Fintype V] (w : HealingWitness)
    (hh : THigh p c E rho w) (hqc : RQCOrigin p c E rho)
    (hnames : ∀ j x r a e, HonestRowAt p c E rho j x r a →
      namedEntry a.payload.height_pair = some e →
      ∃ C, actionSourceFG p c E rho x r = some (some C) ∧
        e = ((heightView p C).h, (heightView p C).T_h.root))
    (hL : V2.D.Linked (fgsaFamilies p c).linked rho)
    (hf : Gen.Pure.FaultQ p.n (Gen.V2.Duty.faulty rho).card)
    (hOrigin : ∀ i x W, HeldAt p c E rho i x W → ∀ a ∈ chainRows W,
      ∃ (wire : RowWire p.n) (r : Nat), wire.toRow? = some a ∧
        wire.auth = .seat .fg a.signer ∧
        ∀ z, RowSigner p c rho wire z → z ∈ rho.honest →
          HonestRowBefore p c E rho i z r wire) :
    ∃ entry : Nat → BlockId,
      (∀ z r C, z ∈ rho.honest →
        actionSourceFG p c E rho z r = some (some C) → high p w C →
        entry (heightView p C).h = (heightView p C).T_h.root) ∧
      ∀ i x W, HeldAt p c E rho i x W →
        (∀ y T (Q : Finset (Fin p.n)),
          w.M + 1 ≤ y → p.E.IsQuorum Q →
          (∀ k ∈ Q, ∃ a ∈ chainRows W, a.signer = k ∧
            a.height_pair.matchesEntry y T = true) →
          T = entry y ∧ ∃ z r C, z ∈ rho.honest ∧
            actionSourceFG p c E rho z r = some (some C) ∧ high p w C ∧
            (heightView p C).h = y ∧ T = (heightView p C).T_h.root ∧
            ∃ k ∈ Q, ∃ a ∈ chainRows W, a.signer = k ∧
              a.height_pair = .vote y (entry y) false) ∧
        (∀ fp (Q : Finset (Fin p.n)), w.M + 1 ≤ fp.height → p.E.IsQuorum Q →
          (∀ k ∈ Q, ∃ a ∈ chainRows W, a.signer = k ∧ a.finality_pair = some fp) →
          fp.target = entry fp.height) := by
  classical
  refine ⟨recordInv_entry p c E rho, recordInv_entry_source p c E rho w hh, ?_⟩
  intro i x W hW
  refine ⟨?_, ?_⟩
  · intro y T Q hy hQ hrows
    obtain ⟨k, hk, hz⟩ := recordInv_quorum_honest p c rho hL hf Q hQ
    obtain ⟨a, ha, hs, hm⟩ := hrows k hk
    obtain ⟨wire, r, hd, hauth, ho⟩ := hOrigin i x W hW a ha
    have hsign : RowSigner p c rho wire (rho.seatOf (.base .fg) k) := by
      rw [RowSigner_def]
      exact ⟨k, by rw [hauth, hs], rfl⟩
    obtain ⟨j, hji, hem⟩ := ho _ hsign hz
    have hn : namedEntry a.height_pair = some (y, T) := by
      cases hp : a.height_pair with
      | empty => rw [hp] at hm; cases hm
      | vote g U timeout =>
        rw [hp] at hm
        have he : g = y ∧ U = T := of_decide_eq_true hm
        rw [he.1, he.2]; rfl
    have hnwire : namedEntry wire.payload.height_pair = some (y, T) := by
      rw [recordInv_decoded_height p wire a hd]; exact hn
    obtain ⟨C, hsource, hc⟩ := hnames j _ r wire _ hem hnwire
    obtain ⟨hz', hhigh, hhC, ht, he⟩ := recordInv_qc_source p c E rho w hh i _ r wire
      a C y T ⟨j, hji, hem⟩ hsource (by rw [hn, hc]) hn hy
    exact ⟨he, _, r, C, hz', hsource, hhigh, hhC, ht, k, hk, a, ha, hs,
      recordInv_honest_pair p c E rho w hh hqc hnames j _ r wire a hem hd y T hn hy⟩
  · intro fp Q hy hQ hrows
    obtain ⟨k, hk, hz⟩ := recordInv_quorum_honest p c rho hL hf Q hQ
    obtain ⟨a, ha, hs, hfp⟩ := hrows k hk
    obtain ⟨wire, r, hd, hauth, ho⟩ := hOrigin i x W hW a ha
    have hsign : RowSigner p c rho wire (rho.seatOf (.base .fg) k) := by
      rw [RowSigner_def]
      exact ⟨k, by rw [hauth, hs], rfl⟩
    obtain ⟨j, _, hem⟩ := ho _ hsign hz
    exact recordInv_honest_finality p c E rho w hh hqc j _ r wire a hem hd fp hfp hy

/-- Paper 22:876–879: selected high progress, target, and finality QCs have one identity.
DC: INTENTIONAL: the earlier target QC supplies the finality identity.
All prefixes and all cumulative TF blocks are included; the record induction
also makes the selected honest progress witness a target. -/
theorem ff2_high_qc_identity (w : HealingWitness)
    (hh : THigh p c E rho w) (hqc : RQCOrigin p c E rho)
    (hnames : ∀ j x r a e, HonestRowAt p c E rho j x r a →
      namedEntry a.payload.height_pair = some e →
      ∃ C, actionSourceFG p c E rho x r = some (some C) ∧
        e = ((heightView p C).h, (heightView p C).T_h.root)) :
    ∃ entry : Nat → BlockId,
      (∀ z r C, z ∈ rho.honest →
        actionSourceFG p c E rho z r = some (some C) → high p w C →
        entry (heightView p C).h = (heightView p C).T_h.root) ∧
      ∀ i x W, x ∈ rho.honest → W ∈ (storeAt p c E rho i x).fg.TF →
        (∀ y X (Q : Finset (Fin p.n))
            (rows : Fin p.n → FGBlock (Fin p.n) × Row (Fin p.n)),
          w.M + 1 ≤ y → y < (heightView p W).h →
          FGBlock.Preceq X W → (heightView p X).h = y → p.E.IsQuorum Q →
          (∀ k ∈ Q, FGBlock.Preceq (rows k).1 W ∧ (rows k).2 ∈ (rows k).1.rows ∧
            (rows k).2.signer = k ∧
            (rows k).2.height_pair.matchesEntry y X.root = true) →
          X.root = entry y ∧ ∃ z r C, z ∈ rho.honest ∧
            actionSourceFG p c E rho z r = some (some C) ∧ high p w C ∧
            (heightView p C).h = y ∧ X.root = (heightView p C).T_h.root ∧
            ∃ k ∈ Q, (rows k).2.height_pair = .vote y (entry y) false) ∧
        (w.M + 1 ≤ (heightView p W).h_j →
          (heightView p W).J.root = entry (heightView p W).h_j ∧
          ∃ z r C, z ∈ rho.honest ∧
            actionSourceFG p c E rho z r = some (some C) ∧ high p w C ∧
            (heightView p C).h = (heightView p W).h_j ∧
            (heightView p W).J.root = (heightView p C).T_h.root) ∧
        (w.M + 1 ≤ (finalityView p W).h_F →
          (finalityView p W).F.root = entry (finalityView p W).h_F ∧
          ∃ z r C, z ∈ rho.honest ∧
            actionSourceFG p c E rho z r = some (some C) ∧ high p w C ∧
            (heightView p C).h = (finalityView p W).h_F ∧
            (finalityView p W).F.root = (heightView p C).T_h.root) := by
  classical
  refine ⟨recordInv_entry p c E rho, recordInv_entry_source p c E rho w hh, ?_⟩
  intro i x W hx hW
  have ho := hqc
  rw [RQCOrigin_def] at ho
  have hoW := ho i x W hx hW
  refine ⟨?_, ?_, ?_⟩
  · intro y X Q rows hy hlt hX hheight hQ hrows
    obtain ⟨k, hk, z, r, wire, hb, hd, _, C, G, hs, hn, _⟩ :=
      hoW.1 y X Q rows (by simp only [Height] at *; omega) hlt hX hheight hQ hrows
    have hp : namedEntry (rows k).2.height_pair = some (y, X.root) := by
      cases he : (rows k).2.height_pair with
      | empty => have hm := (hrows k hk).2.2.2; rw [he] at hm; cases hm
      | vote g U timeout =>
        have hm := (hrows k hk).2.2.2
        rw [he] at hm
        have hgu : g = y ∧ U = X.root := of_decide_eq_true hm
        rw [hgu.1, hgu.2]; rfl
    obtain ⟨hz, hc, hhC, ht, he⟩ := recordInv_qc_source p c E rho w hh i z r wire
      (rows k).2 C y X.root hb hs hn hp hy
    obtain ⟨j, _, ha⟩ := hb
    exact ⟨he, z, r, C, hz, hs, hc, hhC, ht, k, hk,
      recordInv_honest_pair p c E rho w hh hqc hnames j z r wire (rows k).2 ha hd
        y X.root hp hy⟩
  · intro hy
    have hnz : (heightView p W).h_j ≠ 0 := by simp only [Height] at *; omega
    obtain ⟨Q, hQ, hw⟩ := (fgCertificateLaws p).height.justification_certificate W hnz
    have hw' : ∀ k, ∃ B a, k ∈ Q → FGBlock.Preceq B W ∧ a ∈ B.rows ∧
        a.signer = k ∧
        a.height_pair = .vote (heightView p W).h_j (heightView p W).J.root false := by
      intro k
      by_cases hk : k ∈ Q
      · obtain ⟨B, a, ha⟩ := hw k hk
        exact ⟨B, a, fun _ => ha⟩
      · exact ⟨.genesis, ⟨k, .empty, none⟩, fun h => (hk h).elim⟩
    choose B a ha using hw'
    obtain ⟨k, hk, z, r, wire, hb, _, _, C, G, hs, hn, _⟩ :=
      hoW.2.1 Q (fun k => (B k, a k)) hnz hQ ha
    have hp : namedEntry (a k).height_pair =
        some ((heightView p W).h_j, (heightView p W).J.root) := by
      rw [(ha k hk).2.2.2]; rfl
    obtain ⟨hz, hc, hhC, ht, he⟩ := recordInv_qc_source p c E rho w hh i z r wire
      (a k) C _ _ hb hs hn hp hy
    exact ⟨he, z, r, C, hz, hs, hc, hhC, ht⟩
  · intro hy
    obtain ⟨B, hBW, hBJ, hj⟩ := KitFG.provenance_finality_of_certificate p.E
      (heightView p) (finalityView p) (fgCertificateLaws p) W (by simp only [Height] at *; omega)
    have hB := KitFG.ancestor_closed_of_parent_closed _
      (cstoreInv_stateBefore E rho i x).fg.closed W hW B hBW
    have hnz : (heightView p B).h_j ≠ 0 := by rw [hj]; simp only [Height] at *; omega
    obtain ⟨Q, hQ, hw⟩ := (fgCertificateLaws p).height.justification_certificate B hnz
    have hw' : ∀ k, ∃ D a, k ∈ Q → FGBlock.Preceq D B ∧ a ∈ D.rows ∧
        a.signer = k ∧
        a.height_pair = .vote (heightView p B).h_j (heightView p B).J.root false := by
      intro k
      by_cases hk : k ∈ Q
      · obtain ⟨D, a, ha⟩ := hw k hk
        exact ⟨D, a, fun _ => ha⟩
      · exact ⟨.genesis, ⟨k, .empty, none⟩, fun h => (hk h).elim⟩
    choose D a ha using hw'
    obtain ⟨k, hk, z, r, wire, hb, _, _, C, G, hs, hn, _⟩ :=
      (ho i x B hx hB).2.1 Q (fun k => (D k, a k)) hnz hQ ha
    have hp : namedEntry (a k).height_pair =
        some ((finalityView p W).h_F, (finalityView p W).F.root) := by
      rw [(ha k hk).2.2.2, hj, hBJ]; rfl
    obtain ⟨hz, hc, hhC, ht, he⟩ := recordInv_qc_source p c E rho w hh i z r wire
      (a k) C _ _ hb hs hn hp hy
    exact ⟨he, z, r, C, hz, hs, hc, hhC, ht⟩


/-- Paper 22:876–879,917–921: a high contest is impossible at every honest prefix.
DC: INTENTIONAL: QC identity covers every stored contest witness, including
blocks disclosed late in cumulative TF. -/
theorem ff2_no_high_contest (w : HealingWitness)
    (hh : THigh p c E rho w) (hqc : RQCOrigin p c E rho)
    (hnames : ∀ j x r a e, HonestRowAt p c E rho j x r a →
      namedEntry a.payload.height_pair = some e →
      ∃ C, actionSourceFG p c E rho x r = some (some C) ∧
        e = ((heightView p C).h, (heightView p C).T_h.root)) :
    ∀ i x, i ≤ rho.events.length → x ∈ rho.honest →
      let R := FGSA.controls p (storeAt p c E rho i x)
      R.contest = true → R.H ≤ w.M + 1 := by
  classical
  obtain ⟨entry, _, hidentity⟩ := ff2_high_qc_identity p c E rho w hh hqc hnames
  intro i x _hi hx
  let st := storeAt p c E rho i x
  change (FGSA.controls p st).contest = true → (FGSA.controls p st).H ≤ w.M + 1
  unfold FGSA.controls
  rw [KitFG.storeControlsView_def]
  intro ht
  change (decide (st.fg.h_max = st.fg.h_j + 1) &&
    decide (∃ W ∈ st.fg.TF, (heightView p W).h = st.fg.h_max ∧
      ¬ FGBlock.Preceq st.fg.J W)) = true at ht
  rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at ht
  obtain ⟨htop, W, hW, hw, hbad⟩ := ht
  change st.fg.h_max ≤ w.M + 1
  by_contra hlarge
  have hjhigh : w.M + 1 ≤ st.fg.h_j := by simp only [Height] at *; omega
  have hI : KitFG.FGStoreInvariant (heightView p) (finalityView p) st.fg :=
    (cstoreInv_stateBefore E rho i x).fg
  obtain ⟨K, hK, _, hjK, hJK⟩ := hI.pair.1
  have hJroot : st.fg.J.root = entry st.fg.h_j := by
    rw [hJK, hjK]
    exact ((hidentity i x K hx hK).2.1 (hjK ▸ hjhigh)).1
  have allWitnesses : ∀ D ∈ st.fg.TF, (heightView p D).h = st.fg.h_max →
      FGBlock.Preceq st.fg.J D := by
    intro D hD hd
    obtain ⟨X, hXD, hXheight, Q, hQ, hwit⟩ :=
      (fgCertificateLaws p).height.height_crossing D st.fg.h_j
        (by simp only [Height] at *; omega)
        (by rw [hd, htop]; exact Nat.lt_succ_self _)
    have hwit' : ∀ k, ∃ B a, k ∈ Q → FGBlock.Preceq B D ∧ a ∈ B.rows ∧
        a.signer = k ∧ a.height_pair.matchesEntry st.fg.h_j X.root = true := by
      intro k
      by_cases hk : k ∈ Q
      · obtain ⟨B, a, ha⟩ := hwit k hk
        exact ⟨B, a, fun _ => ha⟩
      · exact ⟨.genesis, ⟨k, .empty, none⟩, fun h => (hk h).elim⟩
    choose B a ha using hwit'
    have hXroot := ((hidentity i x D hx hD).1 st.fg.h_j X Q
      (fun k => (B k, a k)) hjhigh
      (by rw [hd, htop]; exact Nat.lt_succ_self _) hXD hXheight hQ ha).1
    have he : st.fg.J = X := FGBlock.root_injective (hJroot.trans hXroot.symm)
    exact he ▸ hXD
  exact hbad (allWitnesses W hW hw)

/-- Paper 22:841–879: the three high record guards used by K-MID and K-ROWS.
DC: INTENTIONAL: this predicate only names the proved record fields. -/
abbrev HighRecordGuard_W {n : Nat} (Λ : RecordOnce) (y : Nat) (U : FGBlock (Fin n)) : Prop :=
  (Λ.target y = none ∨ Λ.target y = some U.root) ∧ Λ.timeout y = false ∧
    (Λ.lock y = none ∨ Λ.lock y = some U.root)

/-- Paper 22:841–879: the equation for the high record guard.
DC: INTENTIONAL: the three durable record fields. -/
theorem HighRecordGuard_W_def {n : Nat} (Λ : RecordOnce) (y : Nat) (U : FGBlock (Fin n)) :
    HighRecordGuard_W Λ y U =
      ((Λ.target y = none ∨ Λ.target y = some U.root) ∧ Λ.timeout y = false ∧
        (Λ.lock y = none ∨ Λ.lock y = some U.root)) := rfl

/-- Paper 22:841–879: FF2 through the K-ROWS plan's common telescope, without A or m.
DC: INTENTIONAL: the thin adapter uses H1 over all rounds and QC origin. -/
theorem ff2_high_record_guards [Fintype V] (G ΔF : Time) (pt : KernelPt)
    (_hδ : p.δt = 2 * p.R) (hK : KernelPrem_W p c G ΔF E rho pt)
    (_hFG : FGFoundation p c E rho) (_hCert : RCert p c E rho)
    (hQC : RQCOrigin p c E rho) (_hXing : RXing p c E rho)
    (_hTiming : TimingContract p c E rho)
    (hNames : ∀ j x r a, HonestRowAt p c E rho j x r a →
      ∃ e C H, namedEntry a.payload.height_pair = some e ∧
        actionSourceFG p c E rho x r = some (some C) ∧
        e = ((heightView p C).h, (heightView p C).T_h.root) ∧
        FGBlock.Preceq (heightView p C).T_h C ∧
        gateResult p c E rho x (r * p.R) = some (some H) ∧
        Block.Preceq (eraseFG C) H ∧ fastAt p c E rho x (r * p.R) (eraseFG C)) :
    ∀ a r C, a ∈ rho.honest → actionSourceFG p c E rho a r = some (some C) →
      high p pt.w C → ∀ i x, i ≤ rho.events.length → x ∈ rho.honest →
        HighRecordGuard_W (V2.D.Run.stateBefore E rho i x).record
          (heightView p C).h (heightView p C).T_h := by
  have hnames : ∀ j x r a e, HonestRowAt p c E rho j x r a →
      namedEntry a.payload.height_pair = some e →
      ∃ C, actionSourceFG p c E rho x r = some (some C) ∧
        e = ((heightView p C).h, (heightView p C).T_h.root) := by
    intro j x r a e ha he
    obtain ⟨e', C, H, he', hs, hc, _⟩ := hNames j x r a ha
    have heq := Option.some.inj (he.symm.trans he')
    exact ⟨C, hs, heq.trans hc⟩
  intro a r C ha hs hc i x _hi hx
  rw [HighRecordGuard_W_def]
  have hentry := recordInv_entry_source p c E rho pt.w hK.input.t.h1 a r C ha hs hc
  obtain ⟨ht, hn, hl, _⟩ := recordInv_all p c E rho pt.w hK.input.t.h1 hQC hnames
    i x hx (heightView p C).h hc
  simpa only [hentry] using And.intro ht (And.intro hn hl)

end AvailableChain.FGSA.Run
