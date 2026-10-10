module
public import AvailableChainFGSAProofs.Proofs.Healing.SupportProposal
public import AvailableChainFGSAProofs.Proofs.Healing.SupportSaved

public section

/-! H-SUPPORT S2 (plan §5; G3 slow): the synchronous-window slow body. The saved window
results of the source gate cover B. Every lease that can be live at q_(s+1) has its last
write inside the window, so same-label compatibility replaces the fast release bound. -/

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG
open Gen.AC

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

omit [DecidableEq V] in
private theorem slow_idx_lt (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hs : V2.D.ScheduleWellFormed E rho) {a b : Nat} {y : V} {ta tb : Time}
    (ha : rho.events[a]? = some (.tick y ta)) (hb : rho.events[b]? = some (.tick y tb))
    (hlt : ta < tb) : a < b := by
  rcases lt_trichotomy a b with h | h | h
  · exact h
  · subst h
    have he := Option.some.inj (ha.symm.trans hb)
    injection he with _ ht
    exact absurd ht (ne_of_lt hlt)
  · exact absurd (fgsa_tick_time_strict E rho hs hb ha h) (not_lt.mpr hlt.le)

private theorem slow_gate_label (s : Slot) :
    ((SA.gateTime p.toParams s - 6 * p.Δ) / (4 * p.Δ)).toNat = s := by
  have he : SA.gateTime p.toParams s - 6 * p.Δ = 4 * p.Δ * (s : Int) := by
    change 4 * p.Δ * (s : Int) + 6 * p.Δ - 6 * p.Δ = _
    ring
  have hDelta : (0 : Int) < p.Δ := p.deltaPos
  rw [he, Int.mul_ediv_cancel_left _ (by omega), Int.toNat_natCast]

private theorem slow_gate_result (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {j : Nat} {x : V} {s : Slot} {B : Block}
    (ht : rho.events[j]? = some (.tick x (SA.gateTime p.toParams s)))
    (hc : SA.Root.confirmationFrom p.toParams
      (eraseFG (clockPre p (V2.D.Run.stateBefore E rho j x).st (SA.gateTime p.toParams s)).fg.F)
      (actView (clockPre p (V2.D.Run.stateBefore E rho j x).st
        (SA.gateTime p.toParams s))) s = some B) :
    gateResultAt p c E rho j = some (some B) := by
  delta gateResultAt
  rw [ht]
  dsimp only
  have htest := (isGateTime_iff p (SA.gateTime p.toParams s)).mpr ⟨s, rfl⟩
  rw [htest, ite_eq_left rfl]
  rw [slow_gate_label s, hc]

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21:689–699; plan H-SUPPORT §3.
DC: SAME a clock step at a time that is not a gate time is the pre-gate clock. -/
theorem healing_clock_nongate (st : State p.n) (t : Time)
    (ht : ∀ w : Slot, t ≠ SA.gateTime p.toParams w) : FGSA.clock p st t = clockPre p st t := by
  unfold FGSA.clock
  dsimp only
  split
  · rename_i hg
    exact absurd (beq_iff_eq.mp (Bool.and_eq_true_iff.mp hg).2) (ht _)
  · rfl

private theorem slow_vote_nongate (i : Slot) (w : Slot) :
    SA.voteTime p.toParams i ≠ SA.gateTime p.toParams w := by
  intro h
  have hd := p.deltaPos
  have h1 : (4 * (i : Int) + 1) * p.Δ = (4 * (w : Int) + 6) * p.Δ := by
    change 4 * p.Δ * (i : Int) + p.Δ = 4 * p.Δ * (w : Int) + 6 * p.Δ at h
    linarith
  have h2 := Int.eq_of_mul_eq_mul_right (ne_of_gt hd) h1
  omega

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21:650–680 (H.4-S window); plan H-SUPPORT §5 step 1, G3.
DC: INTENTIONAL every window label w with s+1-k ≤ w < s has a raw result of the slow
source node that covers B: slow eligibility reads the saved window results, and a
saved non-empty result is the raw gate result (`healing_saved_origin`). -/
theorem healing_slow_window (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hs : V2.D.ScheduleWellFormed E rho) (hN : V2.D.NoRestart rho)
    {s : Slot} {B : Block} {x : V} {st : State p.n}
    (hst : gateIn p c E rho x s = some st)
    (hel : GridCO.slowEligible p.toParams.engine (actView st) s B = true)
    {w : Slot} (hw1 : s + 1 - p.k ≤ w) (hw2 : w + 1 ≤ s) :
    ∃ C, gateResult p c E rho x w = some (some C) ∧ Block.Preceq B C := by
  rw [gateIn_def, preTick_def] at hst
  cases hj' : V2.D.Run.tickIdx? rho x (SA.gateTime p.toParams s) with
  | none => rw [hj'] at hst; cases hst
  | some j =>
  rw [hj'] at hst
  have hst' : clockPre p (storeAt p c E rho j x) (SA.gateTime p.toParams s) = st :=
    Option.some.inj hst
  subst hst'
  unfold GridCO.slowEligible at hel
  obtain ⟨_, hall⟩ := Bool.and_eq_true_iff.mp hel
  have hm : p.toParams.engine.m = p.k := rfl
  rw [hm] at hall
  have key1 : ∀ a b k : Nat, a + 1 - k ≤ b → b + 1 ≤ a → a - b - 1 < k - 1 := by
    intro a b k h1 h2
    omega
  have key2 : ∀ a b : Nat, b + 1 ≤ a → a - (a - b - 1 + 1) = b := by
    intro a b h
    omega
  have hjj : (s : Nat) - w - 1 ∈ List.range (p.k - 1) :=
    List.mem_range.mpr (key1 s w p.k hw1 hw2)
  have h := List.all_eq_true.mp hall _ hjj
  have hsw : (s : Nat) - ((s : Nat) - w - 1 + 1) = w := key2 s w hw2
  rw [hsw] at h
  have hsave : GridCO.savedGenuine (actView (clockPre p (storeAt p c E rho j x)
      (SA.gateTime p.toParams s))) w =
      GridCO.savedGenuine (storeAt p c E rho j x).base w :=
    savedGenuine_congr (clockPre_genuine p _ _) w
  rw [hsave] at h
  cases hsg : GridCO.savedGenuine (storeAt p c E rho j x).base w with
  | none => rw [hsg] at h; cases h
  | some r =>
    cases r with
    | none => rw [hsg] at h; cases h
    | some C =>
      rw [hsg] at h
      obtain ⟨_, _, _, hres⟩ := healing_saved_origin E rho hs hN hsg
      exact ⟨C, hres, h⟩

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21:650–680 (H.4-S); plan H-SUPPORT §5 step 2.
DC: SAME the slow source result is a strict late majority, and so is B ⪯ C. -/
theorem healing_slow_majority (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hs : V2.D.ScheduleWellFormed E rho) {s : Slot} {B C : Block} {j : Nat} {x : V}
    (ht : IsGateTick p c rho j x s) (hres : gateResult p c E rho x s = some (some C))
    (hBC : Block.Preceq B C) :
    let src := actView (clockPre p (storeAt p c E rho j x) (SA.gateTime p.toParams s))
    GridCO.voterCount (GridCO.lateVotes p.toParams.engine src s) <
      2 * GridCO.goldfishScore src.blocks (GridCO.cleanSupport p.toParams.engine src s)
        (GridCO.cleanSupport p.toParams.engine src s) B := by
  intro src
  rw [gateResult_def, gateIn_def, preTick_def, fgsa_tickIdx_of_event p c E rho hs ht] at hres
  simp only [Option.map_some, Option.some.injEq] at hres
  have hh : GridCO.voterCount (GridCO.lateVotes p.toParams.engine src s) <
      2 * GridCO.goldfishScore src.blocks (GridCO.cleanSupport p.toParams.engine src s)
        (GridCO.cleanSupport p.toParams.engine src s) C := by
    change (if _ then some _ else none) = some C at hres
    split at hres
    · have he := Option.some.inj hres
      subst C
      have heq (D : Block) :
          GridCO.goldfishScoreOn (GridCO.resolutionTree src) src.blocks
            (GridCO.cleanSupport p.toParams.engine src s)
            (GridCO.cleanSupport p.toParams.engine src s) D =
          GridCO.goldfishScore src.blocks (GridCO.cleanSupport p.toParams.engine src s)
            (GridCO.cleanSupport p.toParams.engine src s) D :=
        actView_score p (clockPre p (storeAt p c E rho j x) (SA.gateTime p.toParams s))
          (cstoreInv_clockPre p _ (cstoreInv_stateBefore E rho j x) _)
          (by rw [clockPre_headDomain];
              exact base_headDomain_none p (reachable_stateBefore E rho j x)) _ _ D
      rw [← heq _]
      assumption
    · contradiction
  have ha := Gen.AC.Root.goldfishScore_antitone src.blocks
    (GridCO.cleanSupport p.toParams.engine src s)
    (GridCO.cleanSupport p.toParams.engine src s) B C hBC
  omega

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21:673–689 (late receipt), 02 §2.1; plan H-SUPPORT §5 step 2, G3.
DC: SAME every honest label-s HEAD reaches an honest gate d_s in its late pool. -/
theorem healing_support_honest_late [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : Recovery₂ p c E rho G ΔF)
    {s : Slot} (hgst : E.t_GST ≤ SA.voteTime p.toParams s)
    (hhor : SA.gateTime p.toParams s ≤ rho.horizon)
    {j : Nat} {x : V} (hx : x ∈ rho.honest)
    (ht : rho.events[j]? = some (.tick x (SA.gateTime p.toParams s)))
    (k : Fin p.n) (hk : rho.seatOf (.base (.head s)) k ∈ rho.honest) :
    k ∈ (GridCO.seats p.n (GridCO.lateVotes p.toParams.engine
      (actView (clockPre p (storeAt p c E rho j x) (SA.gateTime p.toParams s))) s)).toFinset := by
  have hE := hrec.base.valid
  have hS := hE.toScheduleWellFormed
  have hN := hrec.base.noRestart
  have hDelta := hrec.base.delta
  have hd := p.deltaPos
  let z := rho.seatOf (.base (.head s)) k
  have hvg : SA.voteTime p.toParams s + p.Δ ≤ SA.gateTime p.toParams s := by
    change 4 * p.Δ * (s : Int) + p.Δ + p.Δ ≤ 4 * p.Δ * (s : Int) + 6 * p.Δ
    linarith
  have hvh : SA.voteTime p.toParams s ≤ rho.horizon :=
    ((le_add_of_nonneg_right hd.le).trans hvg).trans hhor
  have hawake := hrec.awake z hk _ hgst hvh
  obtain ⟨jz, hjz⟩ := healing_support_vote_tick E rho hS hDelta hk s hvh hawake
  obtain ⟨hem, _⟩ := healing_support_honest_emits (c := c) E rho hS hjz hawake
  let K := headVote p (FGSA.clock p (V2.D.Run.stateBefore E rho jz z).st
    (SA.voteTime p.toParams s)) s
  have hvd : SA.voteTime p.toParams s + E.Δ ≤ SA.voteTime p.toParams s + E.Δ := le_rfl
  have hdt : SA.voteTime p.toParams s + E.Δ ≤ rho.horizon := by
    rw [hDelta]
    exact hvg.trans hhor
  obtain ⟨dl, cut, hD, _, hlt, hdl, _, hdcut, _⟩ :=
    Gen.V2.Duty.LabelSyncOn.of_recoveryBy E rho (fun o => ¬ isRowObject o) _ _ hrec.sync
      (fgsaDelay_nonrow E.Δ _) hgst hvd hdt
  have hdle : dl (SA.voteTime p.toParams s) ≤ SA.voteTime p.toParams s + p.Δ := by
    have h := hdl (SA.voteTime p.toParams s)
    rwa [max_self, hDelta] at h
  have hwindow : (V2.D.Run.stateBeforeTime E rho (dl (SA.voteTime p.toParams s)) x).st.slot p ≤
      s + 1 := by
    have h := healing_support_read_window E rho hS hN ht _ (hdle.trans hvg)
    have he : p.slotOf (SA.gateTime p.toParams s) = s + 1 :=
      (fgsa_postClock_slot (c := c) (V2.D.Run.stateBefore E rho j x) _).2.symm.trans
        (fgsa_gate_slot (c := c) _ s)
    exact h.trans_eq he
  have hcut : dl (SA.voteTime p.toParams s) ≤ cut := by
    refine hdle.trans (le_trans ?_ hdcut)
    rw [hDelta]
  obtain ⟨hom, hos⟩ := fgsa_honest_head_receipt E rho hDelta hE hN hrec.base.cstar dl cut s k K.root
    (SA.voteTime p.toParams s) z x hD hk hem hx hcut (hlt _) hwindow
  let o := baseVote (⟨.seat (.head s) k, K.root⟩ : HeadWire p.n)
  have hidx : V2.D.Run.idxBefore rho (dl (SA.voteTime p.toParams s)) ≤ j :=
    healing_support_idxBefore_le p c E rho hS ht (hdle.trans hvg)
  have hom' : o ∈ (storeAt p c E rho (V2.D.Run.idxBefore rho
      (dl (SA.voteTime p.toParams s))) x).base.votes := by
    change o ∈ (V2.D.Run.stateBefore E rho _ x).st.base.votes
    rw [Gen.V2.Duty.stateBefore_idxBefore E rho _ hS]
    exact hom
  obtain ⟨hod, hods⟩ := healing_support_vote_kept E rho hN hidx x
    (SA.gateTime p.toParams s) o hom'
  have hvc : (actView (clockPre p (storeAt p c E rho j x)
      (SA.gateTime p.toParams s))).votes = (storeAt p c E rho j x).base.votes :=
    (Internal.clockPre_vn (storeAt p c E rho j x) _).1
  have hstamp : GridCO.stampVote (actView (clockPre p (storeAt p c E rho j x)
      (SA.gateTime p.toParams s))) o = GridCO.stampVote (storeAt p c E rho
        (V2.D.Run.idxBefore rho (dl (SA.voteTime p.toParams s))) x).base o := by
    rw [← hods]
    change ((((clockPre p _ _).base.voteStamp).find? _).map Prod.snd).getD _ =
      ((((FGSA.clock p _ _).base.voteStamp).find? _).map Prod.snd).getD _
    rw [(clockPre_stamps p _ _).2, (clock_cumulative p _ _).2.2.2.1]
    congr 1
    exact (Internal.clockPre_vn _ _).2.trans (clock_vn _ _).2.symm
  have hlate : o ∈ GridCO.lateVotes p.toParams.engine
      (actView (clockPre p (storeAt p c E rho j x) (SA.gateTime p.toParams s))) s := by
    apply List.mem_filter.mpr
    refine ⟨List.mem_filter.mpr ⟨?_, beq_self_eq_true _⟩, ?_⟩
    · rw [hvc, ← (clock_vn (storeAt p c E rho j x) (SA.gateTime p.toParams s)).1]
      exact hod
    · apply decide_eq_true
      rw [hstamp]
      change GridCO.stampVote (V2.D.Run.stateBefore E rho _ x).st.base o < _
      rw [Gen.V2.Duty.stateBefore_idxBefore E rho _ hS]
      exact lt_of_lt_of_le hos (hdle.trans hvg)
  exact (Gen.AC.Root.vote_pool_mem_seats _ k).mpr ⟨o, hlate, rfl⟩

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21:650–680 (H.4-S); plan H-SUPPORT §5 step 2, G3.
DC: INTENTIONAL a strict late majority for B at an honest gate in the synchronous
window has an honest clean supporter: all honest seats are late voters there, and the
other late voters are faulty seats, fewer than the honest ones. -/
theorem healing_slow_honest_seat [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : Recovery₂ p c E rho G ΔF)
    {s : Slot} (hgst : E.t_GST ≤ SA.voteTime p.toParams s)
    (hhor : SA.gateTime p.toParams s ≤ rho.horizon)
    {j : Nat} {x : V} (hx : x ∈ rho.honest)
    (ht : rho.events[j]? = some (.tick x (SA.gateTime p.toParams s))) {B : Block}
    (hmaj : let src := actView (clockPre p (storeAt p c E rho j x) (SA.gateTime p.toParams s))
      GridCO.voterCount (GridCO.lateVotes p.toParams.engine src s) <
        2 * GridCO.goldfishScore src.blocks (GridCO.cleanSupport p.toParams.engine src s)
          (GridCO.cleanSupport p.toParams.engine src s) B) :
    let src := actView (clockPre p (storeAt p c E rho j x) (SA.gateTime p.toParams s))
    ∃ k o, rho.seatOf (.base (.head s)) k ∈ rho.honest ∧
      o ∈ GridCO.cleanSupport p.toParams.engine src s ∧ GridCO.headSeat? o = some k ∧
      Gen.AC.Root.voteSupports src.blocks B o = true := by
  classical
  intro src
  have hC := hrec.base.cstar
  have hd := p.deltaPos
  let P := GridCO.cleanSupport p.toParams.engine src s
  let L := (GridCO.seats p.n (GridCO.lateVotes p.toParams.engine src s)).toFinset
  let T := (GridCO.seats p.n P).toFinset.filter
    (fun i => Gen.AC.Root.poolSupports src.blocks P i B = true)
  let Hon : Finset (Fin p.n) := Finset.univ.filter
    (fun k => rho.seatOf (.base (.head s)) k ∈ rho.honest)
  have hHmem (k : Fin p.n) : k ∈ Hon ↔ rho.seatOf (.base (.head s)) k ∈ rho.honest := by
    simp only [Hon, Finset.mem_filter, Finset.mem_univ, true_and]
  have hscore : GridCO.goldfishScore src.blocks P P B = T.card := by
    rw [Gen.AC.Root.vote_pool_score_card]
    apply congrArg Finset.card
    apply Finset.filter_congr
    intro i _
    rw [show GridCO.equivocates P i = false from
      fgsa_cleanSupport_no_equivocation p src s i, Bool.false_or]
  have hcount : GridCO.voterCount (GridCO.lateVotes p.toParams.engine src s) = L.card := by
    unfold GridCO.voterCount
    exact (List.toFinset_card_of_nodup (List.nodup_dedup _)).symm
  by_contra hn
  have hTH : Disjoint T Hon := by
    rw [Finset.disjoint_left]
    intro k hkT hkH
    obtain ⟨_, hs⟩ := Finset.mem_filter.mp hkT
    obtain ⟨o, ho, hk', hsup⟩ := (Gen.AC.Root.vote_pool_support_witness _ _ k B).mp hs
    exact hn ⟨k, o, (hHmem k).mp hkH, ho, hk', hsup⟩
  have hTL : T ⊆ L := fun k hk =>
    fgsa_cleanSupport_seats_subset_late p src s (Finset.mem_filter.mp hk).1
  have hHL : Hon ⊆ L := fun k hk =>
    healing_support_honest_late E rho hrec hgst hhor hx ht k ((hHmem k).mp hk)
  have hTf : T.card ≤ (Gen.V2.Duty.faulty rho).card := by
    apply Finset.card_le_card_of_injOn (rho.seatOf (.base (.head s)))
    · intro k hk
      rw [Finset.mem_coe, Gen.V2.Duty.faulty_def]
      refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ?_⟩
      intro hh
      exact Finset.disjoint_left.mp hTH hk ((hHmem k).mpr hh)
    · intro k _ i _ he
      exact (hC (.base (.head s)) trivial).injective he
  have hbij : Function.Bijective (fun k : Fin p.n => rho.seatOf (.base (.head s)) k) :=
    hC (.base (.head s)) trivial
  have hHon : Hon.card = rho.honest.card := by
    rw [← Finset.card_image_of_injective Hon hbij.1]
    congr 1
    ext z
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact (hHmem k).mp hk
    · intro hz
      obtain ⟨k, rfl⟩ := hbij.2 z
      exact ⟨k, (hHmem k).mpr hz, rfl⟩
  have hvh : SA.voteTime p.toParams s ≤ rho.horizon := by
    refine le_trans ?_ hhor
    change 4 * p.Δ * (s : Int) + p.Δ ≤ 4 * p.Δ * (s : Int) + 6 * p.Δ
    linarith
  have hawk : Gen.V2.Duty.awakeHonest E rho (SA.voteTime p.toParams s) = rho.honest := by
    rw [Gen.V2.Duty.awakeHonest_def]
    exact Finset.filter_eq_self.mpr (fun z hz => hrec.awake z hz _ hgst hvh)
  have hb : (Gen.V2.Duty.faulty rho).card < Hon.card := by
    have h := (hrec.batch hgst hvh).lt
    rw [hawk] at h
    rw [hHon]
    exact h
  have hunion : T.card + Hon.card ≤ L.card := by
    rw [← Finset.card_union_of_disjoint hTH]
    exact Finset.card_le_card (Finset.union_subset hTL hHL)
  have hm : GridCO.voterCount (GridCO.lateVotes p.toParams.engine src s) <
      2 * GridCO.goldfishScore src.blocks P P B := hmaj
  rw [hscore, hcount] at hm
  omega

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21:650–699 (H.4-S lease window), IF.1, IF.6; plan H-SUPPORT §5 steps 3–5.
DC: INTENTIONAL a lease written by an honest gate at a window label w (s+1-k ≤ w ≤ s)
is compatible with a slow-body B: the slow source result at w covers B, and two honest
raw results of one synchronized label are compatible (`fgsa_sameLabel`). -/
theorem healing_slow_lease_window [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : Recovery₂ p c E rho G ΔF)
    {s : Slot} {B : Block} {x : V} (hx : x ∈ rho.honest) {st : State p.n}
    (hgw : E.t_GST ≤ SA.voteTime p.toParams (s + 1 - p.k))
    (hgs : SA.gateTime p.toParams s ≤ rho.horizon)
    (hst : gateIn p c E rho x s = some st) {C : Block}
    (hres : gateResult p c E rho x s = some (some C)) (hBC : Block.Preceq B C)
    (hel : GridCO.slowEligible p.toParams.engine (actView st) s B = true)
    {j : Nat} {y : V} {w : Slot} {D A : Block} (hy : y ∈ rho.honest)
    (ht : IsGateTick p c rho j y w) (hD : gateResultAt p c E rho j = some (some D))
    (hAD : Block.Preceq A D) (hw1 : s + 1 - p.k ≤ w) (hw2 : w ≤ s) :
    Block.Compatible A B := by
  have hE := hrec.base.valid
  have hS := hE.toScheduleWellFormed
  have hN := hrec.base.noRestart
  have hDelta := hrec.base.delta
  have hd := p.deltaPos
  obtain ⟨Cw, hxw, hBw⟩ : ∃ Cw, gateResult p c E rho x w = some (some Cw) ∧
      Block.Preceq B Cw := by
    rcases Nat.lt_or_ge (w : Nat) (s : Nat) with hlt | hge
    · exact healing_slow_window E rho hS hN hst hel hw1 hlt
    · have hws : w = s := le_antisymm hw2 hge
      subst hws
      exact ⟨C, hres, hBC⟩
  have hgww : E.t_GST ≤ SA.voteTime p.toParams w := by
    refine hgw.trans ?_
    change 4 * p.Δ * ((s + 1 - p.k : Nat) : Int) + p.Δ ≤ 4 * p.Δ * (w : Int) + p.Δ
    have : ((s + 1 - p.k : Nat) : Int) ≤ (w : Int) := by exact_mod_cast hw1
    nlinarith
  have hgsw : SA.gateTime p.toParams w ≤ rho.horizon := by
    refine le_trans ?_ hgs
    change 4 * p.Δ * (w : Int) + 6 * p.Δ ≤ 4 * p.Δ * (s : Int) + 6 * p.Δ
    have : (w : Int) ≤ (s : Int) := by exact_mod_cast hw2
    nlinarith
  have hvd : SA.voteTime p.toParams w + E.Δ ≤ SA.gateTime p.toParams w := by
    rw [hDelta]
    change 4 * p.Δ * (w : Int) + p.Δ + p.Δ ≤ 4 * p.Δ * (w : Int) + 6 * p.Δ
    linarith
  have hSync := Gen.V2.Duty.LabelSyncOn.of_recoveryBy E rho (fun o => ¬ isRowObject o) _ _
    hrec.sync (fgsaDelay_nonrow E.Δ _) hgww hvd hgsw
  have hyD : gateResult p c E rho y w = some (some D) :=
    (gateResultAt_eq_gateResult p c E rho hS ht).symm.trans hD
  have hCD := fgsa_sameLabel (hroots := hrec.base.idealization) p c E rho hE hN hDelta w hSync x
      y Cw D hx hy hxw hyD
  have hDB : Block.Compatible D B := by
    rcases Bool.or_eq_true_iff.mp hCD with hh | hh
    · exact Bool.or_eq_true_iff.mpr (Or.inr (Gen.Pure.block_preceq_trans hBw hh))
    · exact Gen.Pure.block_compatible_of_common hh hBw
  rcases Bool.or_eq_true_iff.mp hDB with h | h
  · exact Bool.or_eq_true_iff.mpr (Or.inl (Gen.Pure.block_preceq_trans hAD h))
  · exact Gen.Pure.block_compatible_of_common hAD h

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21:650–699 (H.4-S lease bound), IF.1, IF.6; plan H-SUPPORT §5 steps 3–5, G5.
DC: INTENTIONAL every lease row read at or after q_(s+1) is compatible with a slow-body B.
A row with gate label w ≤ s-k expires at r_(w+k) ≤ q_(s+1) (G5); a window label uses
`healing_slow_lease_window`; a later label uses the honest batch cover of that label. -/
theorem healing_slow_lease_at [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : Recovery₂ p c E rho G ΔF)
    (mono : RMono p c E rho)
    (writes : ∀ i x (row : Block × Nat × Time),
      row ∈ (storeAt p c E rho i x).base.obligations →
      ∃ j < i, ∃ s B, IsGateTick p c rho j x s ∧ gatePassedAt p c E rho j ∧
        gateResultAt p c E rho j = some (some B) ∧ Block.Preceq row.1 B ∧
        (row.1, row.2.1) ∈ @GridCO.gateWriteKeys GridCO.slowLeasePolicy .root p.toParams.engine p.n
          (actView (clockPre p (storeAt p c E rho j x) (SA.gateTime p.toParams s))) s B ∧
        row.2.2 = SA.gateTime p.toParams s + SA.lifetime p.toParams ∧
        row.2.2 = SA.releaseTime p.toParams (s + p.k) ∧
        ∀ k w C, j < k → k < i → IsGateTick p c rho k x w →
          let pre := clockPre p (storeAt p c E rho k x) (SA.gateTime p.toParams w)
          GridCO.savedGenuine pre.base w = none →
          SA.Root.confirmationFrom p.toParams (eraseFG pre.fg.F) (actView pre) w = some C →
          (actView pre).obligations.any (fun r => !Block.compatible r.1 C) = false →
          (row.1, row.2.1) ∉ @GridCO.gateWriteKeys GridCO.slowLeasePolicy .root
              p.toParams.engine p.n
            (actView pre) w C)
    {s : Slot} {B : Block} (hgst : E.t_GST ≤ SA.voteTime p.toParams s)
    (hgs : SA.gateTime p.toParams s ≤ rho.horizon)
    {x : V} (hx : x ∈ rho.honest)
    (hgw : E.t_GST ≤ SA.voteTime p.toParams (s + 1 - p.k)) {st : State p.n}
    (hst : gateIn p c E rho x s = some st) {C : Block}
    (hres : gateResult p c E rho x s = some (some C)) (hBC : Block.Preceq B C)
    (hel : GridCO.slowEligible p.toParams.engine (actView st) s B = true)
    {T : Time} (hTh : T ≤ rho.horizon)
    (hcov : ∀ w, s + 1 ≤ w → SA.gateTime p.toParams w ≤ T → ∀ z ∈ rho.honest, ∀ K,
      headAtLabel p c E rho z w = some K → Block.Preceq B K)
    {a iq : Nat} {y : V} (hy : y ∈ rho.honest)
    (hiq : rho.events[iq]? = some (.tick y (SA.voteTime p.toParams (s + 1))))
    (hqa : iq < a)
    (hT : ∀ j t, j < a → rho.events[j]? = some (.tick y t) → t ≤ T)
    (hFB : Block.Preceq (eraseFG (storeAt p c E rho a y).fg.F) B) :
    ∀ row ∈ (storeAt p c E rho a y).base.obligations, Block.Compatible row.1 B := by
  have hE := hrec.base.valid
  have hS := hE.toScheduleWellFormed
  have hN := hrec.base.noRestart
  have hd := p.deltaPos
  have hFmono {a b : Nat} (hab : a ≤ b) (hFb : Block.Preceq
      (eraseFG (storeAt p c E rho b y).fg.F) B) :
      Block.Preceq (eraseFG (storeAt p c E rho a y).fg.F) B :=
    Gen.Pure.block_preceq_trans (eraseFG_preceq (mono hN a b y hy hab).1) hFb
  have hcompat {A D : Block} (hAD : Block.Preceq A D) (hDB : Block.Compatible D B) :
      Block.Compatible A B := by
    rcases Bool.or_eq_true_iff.mp hDB with h | h
    · exact Bool.or_eq_true_iff.mpr (Or.inl (Gen.Pure.block_preceq_trans hAD h))
    · exact Gen.Pure.block_compatible_of_common hAD h
  have key : ∀ a b k : Nat, ¬ b + k ≤ a → a + 1 - k ≤ b := by
    intro a b k h
    omega
  intro row hr0
  obtain ⟨j, hj, w, D, ht, _, hres', hrowD, _, _, hdl, _⟩ := writes a y row hr0
  by_cases hold : (w : Nat) + p.k ≤ (s : Nat)
  · -- An old lease expires by q_(s+1) (G5).
    exfalso
    have hwk : (w : Int) + p.k ≤ (s : Int) := by exact_mod_cast hold
    have hjq : j < iq := slow_idx_lt E rho hS ht hiq (by
      change 4 * p.Δ * (w : Int) + 6 * p.Δ < 4 * p.Δ * ((s + 1 : Nat) : Int) + p.Δ
      have : (w : Int) + 1 ≤ (s : Int) := by
        have := p.kLarge
        omega
      push_cast
      nlinarith)
    have hlife : row.2.2 = SA.gateTime p.toParams w + SA.lifetime p.toParams := by
      rw [hdl]
      change 4 * p.Δ * ((w + p.k : Nat) : Int) + 5 * p.Δ =
        4 * p.Δ * (w : Int) + 6 * p.Δ + (4 * (p.k : Int) - 1) * p.Δ
      push_cast
      ring
    have hkeep := healing_lease_persist E rho hS ht (Nat.lt_succ_of_lt hjq) hqa row hlife hr0
    have hpost : storeAt p c E rho (iq + 1) y =
        clockPre p (storeAt p c E rho iq y) (SA.voteTime p.toParams (s + 1)) := by
      change (V2.D.Run.stateBefore E rho (iq + 1) y).st = _
      rw [V2.D.Run.stateBefore_succ E rho hiq]
      simp only [V2.D.World.step, Function.update_self]
      rw [← healing_clock_nongate _ _ (slow_vote_nongate (p := p) (s + 1))]
      exact tick_st (c := c) E rho _ y _
    rw [hpost] at hkeep
    have hlive := healing_clockPre_live _ _ row hkeep
    rw [hdl] at hlive
    change 4 * p.Δ * ((s + 1 : Nat) : Int) + p.Δ < 4 * p.Δ * ((w + p.k : Nat) : Int) + 5 * p.Δ
      at hlive
    push_cast at hlive
    nlinarith
  have hw1 : s + 1 - p.k ≤ w := key s w p.k hold
  rcases Nat.lt_or_ge (s : Nat) (w : Nat) with hws | hws
  · -- A later label: the honest batch of label w makes the gate result cover B.
    have hgw' : E.t_GST ≤ SA.voteTime p.toParams w := by
      refine hgst.trans ?_
      change 4 * p.Δ * (s : Int) + p.Δ ≤ 4 * p.Δ * (w : Int) + p.Δ
      have : (s : Int) ≤ (w : Int) := by exact_mod_cast hws.le
      nlinarith
    have hwT := hT j _ hj ht
    have hFw : Block.Preceq (eraseFG (clockPre p (storeAt p c E rho j y)
        (SA.gateTime p.toParams w)).fg.F) B := by
      rw [clockPre_fg]
      exact hFmono hj.le hFB
    obtain ⟨C', hC', hBC'⟩ := healing_support_gate_cover E rho hrec hgw' (hwT.trans hTh)
      (hcov w hws hwT) ht hFw
    have hDC : D = C' := by
      have h2 := slow_gate_result (c := c) E rho ht hC'
      rw [hres'] at h2
      exact Option.some.inj (Option.some.inj h2)
    subst hDC
    exact hcompat hrowD (Bool.or_eq_true_iff.mpr (Or.inr hBC'))
  · exact healing_slow_lease_window E rho hrec hx hgw hgs hst hres hBC hel hy ht hres' hrowD
      hw1 hws

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21:689–715 (H.2 lease premise, slow arm); plan H-SUPPORT §5 steps 3–5.
DC: INTENTIONAL the lease premise of a HEAD at q_(i+1), i ≥ s, for a slow body:
`healing_slow_lease_at` at the post-tick index with the bound q_(i+1). -/
theorem healing_slow_lease [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : Recovery₂ p c E rho G ΔF)
    (mono : RMono p c E rho)
    (writes : ∀ i x (row : Block × Nat × Time),
      row ∈ (storeAt p c E rho i x).base.obligations →
      ∃ j < i, ∃ s B, IsGateTick p c rho j x s ∧ gatePassedAt p c E rho j ∧
        gateResultAt p c E rho j = some (some B) ∧ Block.Preceq row.1 B ∧
        (row.1, row.2.1) ∈ @GridCO.gateWriteKeys GridCO.slowLeasePolicy .root p.toParams.engine p.n
          (actView (clockPre p (storeAt p c E rho j x) (SA.gateTime p.toParams s))) s B ∧
        row.2.2 = SA.gateTime p.toParams s + SA.lifetime p.toParams ∧
        row.2.2 = SA.releaseTime p.toParams (s + p.k) ∧
        ∀ k w C, j < k → k < i → IsGateTick p c rho k x w →
          let pre := clockPre p (storeAt p c E rho k x) (SA.gateTime p.toParams w)
          GridCO.savedGenuine pre.base w = none →
          SA.Root.confirmationFrom p.toParams (eraseFG pre.fg.F) (actView pre) w = some C →
          (actView pre).obligations.any (fun r => !Block.compatible r.1 C) = false →
          (row.1, row.2.1) ∉ @GridCO.gateWriteKeys GridCO.slowLeasePolicy .root
              p.toParams.engine p.n
            (actView pre) w C)
    {s : Slot} {B : Block} (hgst : E.t_GST ≤ SA.voteTime p.toParams s)
    (hgs : SA.gateTime p.toParams s ≤ rho.horizon)
    {x : V} (hx : x ∈ rho.honest)
    (hgw : E.t_GST ≤ SA.voteTime p.toParams (s + 1 - p.k)) {st : State p.n}
    (hst : gateIn p c E rho x s = some st) {C : Block}
    (hres : gateResult p c E rho x s = some (some C)) (hBC : Block.Preceq B C)
    (hel : GridCO.slowEligible p.toParams.engine (actView st) s B = true)
    {i : Slot} (hi : s ≤ i) (hvh : SA.voteTime p.toParams (i + 1) ≤ rho.horizon)
    (hcov : ∀ w, s + 1 ≤ w → w ≤ i → ∀ z ∈ rho.honest, ∀ K,
      headAtLabel p c E rho z w = some K → Block.Preceq B K)
    {iy : Nat} {y : V} (hy : y ∈ rho.honest)
    (hiy : rho.events[iy]? = some (.tick y (SA.voteTime p.toParams (i + 1))))
    (hFB : Block.Preceq (eraseFG (storeAt p c E rho iy y).fg.F) B) :
    ∀ row ∈ (FGSA.clock p (storeAt p c E rho iy y)
      (SA.voteTime p.toParams (i + 1))).base.obligations, Block.Compatible row.1 B := by
  have hS := hrec.base.valid.toScheduleWellFormed
  have hDelta := hrec.base.delta
  have hd := p.deltaPos
  have hiI : (s : Int) ≤ (i : Int) := by exact_mod_cast hi
  have hqq : SA.voteTime p.toParams (s + 1) ≤ SA.voteTime p.toParams (i + 1) := by
    change 4 * p.Δ * ((s + 1 : Nat) : Int) + p.Δ ≤ 4 * p.Δ * ((i + 1 : Nat) : Int) + p.Δ
    push_cast
    nlinarith
  obtain ⟨iq, hiq⟩ := healing_support_vote_tick E rho hS hDelta hy (s + 1) (hqq.trans hvh)
  have hqa : iq < iy + 1 := by
    rcases Nat.lt_or_ge iy iq with h | h
    · exact absurd (fgsa_tick_time_strict E rho hS hiy hiq h) (not_lt.mpr hqq)
    · exact Nat.lt_succ_of_le h
  have hpost : storeAt p c E rho (iy + 1) y =
      FGSA.clock p (storeAt p c E rho iy y) (SA.voteTime p.toParams (i + 1)) := by
    change (V2.D.Run.stateBefore E rho (iy + 1) y).st = _
    rw [V2.D.Run.stateBefore_succ E rho hiy]
    simp only [V2.D.World.step, Function.update_self]
    exact tick_st (c := c) E rho _ y _
  rw [← hpost]
  refine healing_slow_lease_at E rho hrec mono writes hgst hgs hx hgw hst hres hBC hel hvh ?_
    hy hiq hqa ?_ ?_
  · intro w hw hwT
    refine hcov w hw ?_
    have h : (4 * (w : Int) + 6) * p.Δ ≤ (4 * ((i + 1 : Nat) : Int) + 1) * p.Δ := by
      change 4 * p.Δ * (w : Int) + 6 * p.Δ ≤ 4 * p.Δ * ((i + 1 : Nat) : Int) + p.Δ at hwT
      linarith
    have h2 : 4 * (w : Int) + 6 ≤ 4 * ((i + 1 : Nat) : Int) + 1 := le_of_mul_le_mul_right h hd
    push_cast at h2
    exact_mod_cast (show (w : Int) ≤ i by omega)
  · intro j t hj ht
    rcases Nat.lt_or_ge j iy with h | h
    · exact (fgsa_tick_time_strict E rho hS ht hiy h).le
    · have hje : j = iy := by omega
      subst hje
      have he := Option.some.inj (ht.symm.trans hiy)
      injection he with _ htt
      exact htt.le
  · rw [hpost, clock_fg]
    exact hFB

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. Blueprint 21:650–699 (H.1 at s+1, slow arm); plan H-SUPPORT §5 steps 2–5, G3.
DC: INTENTIONAL the first HEAD transfer at s+1 for a synchronous-window slow body.
The slow source result is a strict late majority with an honest clean supporter. -/
theorem healing_slow_first_transfer [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : Recovery₂ p c E rho G ΔF)
    (mono : RMono p c E rho) (crossing : RXing p c E rho)
    (writes : ∀ i x (row : Block × Nat × Time),
      row ∈ (storeAt p c E rho i x).base.obligations →
      ∃ j < i, ∃ s B, IsGateTick p c rho j x s ∧ gatePassedAt p c E rho j ∧
        gateResultAt p c E rho j = some (some B) ∧ Block.Preceq row.1 B ∧
        (row.1, row.2.1) ∈ @GridCO.gateWriteKeys GridCO.slowLeasePolicy .root p.toParams.engine p.n
          (actView (clockPre p (storeAt p c E rho j x) (SA.gateTime p.toParams s))) s B ∧
        row.2.2 = SA.gateTime p.toParams s + SA.lifetime p.toParams ∧
        row.2.2 = SA.releaseTime p.toParams (s + p.k) ∧
        ∀ k w C, j < k → k < i → IsGateTick p c rho k x w →
          let pre := clockPre p (storeAt p c E rho k x) (SA.gateTime p.toParams w)
          GridCO.savedGenuine pre.base w = none →
          SA.Root.confirmationFrom p.toParams (eraseFG pre.fg.F) (actView pre) w = some C →
          (actView pre).obligations.any (fun r => !Block.compatible r.1 C) = false →
          (row.1, row.2.1) ∉ @GridCO.gateWriteKeys GridCO.slowLeasePolicy .root
              p.toParams.engine p.n
            (actView pre) w C)
    {u v : Time} {m : Nat} {J : Option (FGBlock (Fin p.n))} {contested : Bool}
    (hgst : E.t_GST ≤ u) (hphase : PhaseInterval p c E rho u v m J contested)
    {s : Slot} {B : Block} (hhead : u ≤ SA.voteTime p.toParams s)
    (hgate : SA.gateTime p.toParams s ≤ v)
    {x : V} (hx : x ∈ rho.honest)
    (hgw : E.t_GST ≤ SA.voteTime p.toParams (s + 1 - p.k)) {st : State p.n}
    (hst : gateIn p c E rho x s = some st) {C : Block}
    (hres : gateResult p c E rho x s = some (some C)) (hBC : Block.Preceq B C)
    (hel : GridCO.slowEligible p.toParams.engine (actView st) s B = true)
    {jx : Nat} (hjx : IsGateTick p c rho jx x s)
    {y : V} (hy : y ∈ rho.honest) (hv : SA.voteTime p.toParams (s + 1) ≤ v)
    {H : Block} (hH : headAtLabel p c E rho y (s + 1) = some H) :
    Block.Preceq B H := by
  have hE := hrec.base.valid
  have hS := hE.toScheduleWellFormed
  have hN := hrec.base.noRestart
  have hDelta := hrec.base.delta
  have hhor : SA.gateTime p.toParams s ≤ rho.horizon := hgate.trans hphase.2.1
  have hmaj := healing_slow_majority E rho hS hjx hres hBC
  obtain ⟨k, o, hkh, ho, hko, hsup⟩ :=
    healing_slow_honest_seat E rho hrec (hgst.trans hhead) hhor hx hjx hmaj
  unfold headAtLabel at hH
  rw [postClock_def, preTick_def] at hH
  cases hiy' : V2.D.Run.tickIdx? rho y (SA.voteTime p.toParams (s + 1)) with
  | none => rw [hiy'] at hH; cases hH
  | some iy =>
  rw [hiy'] at hH
  have hiy := V2.D.Run.tickIdx?_spec hiy'
  have hHeq := Option.some.inj hH
  subst hHeq
  obtain ⟨K, hK, _⟩ := healing_support_clean_target E rho o ho
  have hsupD := actView_support_in_domain p _
    (cstoreInv_clockPre p _ (cstoreInv_stateBefore E rho jx x) _) o hK hsup
  exact healing_first_transfer_core (hroots := hrec.base.idealization)
    E rho mono crossing hE hN hDelta hrec.sync hgst hphase
    hhead hgate hx hjx hkh ho hko hsupD hmaj hy hiy hv
    (healing_slow_lease E rho hrec mono writes (hgst.trans hhead) hhor hx hgw hst hres hBC
      hel le_rfl (hv.trans hphase.2.1)
      (fun w hw1 hw2 => absurd (hw1.trans hw2) (Nat.not_succ_le_self s)) hy hiy)

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21:650–715 (H.1 + H.2 S1, slow arm); plan H-SUPPORT §5.
DC: INTENTIONAL the S1 HEAD clause of Transfers for a synchronous-window slow body. -/
theorem healing_slow_heads [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : Recovery₂ p c E rho G ΔF)
    (mono : RMono p c E rho) (crossing : RXing p c E rho)
    (writes : ∀ i x (row : Block × Nat × Time),
      row ∈ (storeAt p c E rho i x).base.obligations →
      ∃ j < i, ∃ s B, IsGateTick p c rho j x s ∧ gatePassedAt p c E rho j ∧
        gateResultAt p c E rho j = some (some B) ∧ Block.Preceq row.1 B ∧
        (row.1, row.2.1) ∈ @GridCO.gateWriteKeys GridCO.slowLeasePolicy .root p.toParams.engine p.n
          (actView (clockPre p (storeAt p c E rho j x) (SA.gateTime p.toParams s))) s B ∧
        row.2.2 = SA.gateTime p.toParams s + SA.lifetime p.toParams ∧
        row.2.2 = SA.releaseTime p.toParams (s + p.k) ∧
        ∀ k w C, j < k → k < i → IsGateTick p c rho k x w →
          let pre := clockPre p (storeAt p c E rho k x) (SA.gateTime p.toParams w)
          GridCO.savedGenuine pre.base w = none →
          SA.Root.confirmationFrom p.toParams (eraseFG pre.fg.F) (actView pre) w = some C →
          (actView pre).obligations.any (fun r => !Block.compatible r.1 C) = false →
          (row.1, row.2.1) ∉ @GridCO.gateWriteKeys GridCO.slowLeasePolicy .root
              p.toParams.engine p.n
            (actView pre) w C)
    {u v : Time} {m : Nat} {J : Option (FGBlock (Fin p.n))} {contested : Bool}
    (hgst : E.t_GST ≤ u) (hphase : PhaseInterval p c E rho u v m J contested)
    {s : Slot} {B : Block} (hhead : u ≤ SA.voteTime p.toParams s)
    (hgate : SA.gateTime p.toParams s ≤ v)
    {x : V} (hx : x ∈ rho.honest)
    (hgw : E.t_GST ≤ SA.voteTime p.toParams (s + 1 - p.k)) {st : State p.n}
    (hst : gateIn p c E rho x s = some st) {C : Block}
    (hres : gateResult p c E rho x s = some (some C)) (hBC : Block.Preceq B C)
    (hel : GridCO.slowEligible p.toParams.engine (actView st) s B = true)
    {jx : Nat} (hjx : IsGateTick p c rho jx x s)
 :
    ∀ i, s + 1 ≤ i → SA.voteTime p.toParams i ≤ v →
      ∀ z ∈ rho.honest, ∀ K, headAtLabel p c E rho z i = some K → Block.Preceq B K := by
  have hd := p.deltaPos
  have hvmono {a b : Slot} (hab : a ≤ b) :
      SA.voteTime p.toParams a ≤ SA.voteTime p.toParams b := by
    have h : (a : Int) ≤ (b : Int) := by exact_mod_cast hab
    change 4 * p.Δ * (a : Int) + p.Δ ≤ 4 * p.Δ * (b : Int) + p.Δ
    nlinarith
  suffices h : ∀ i, s + 1 ≤ i → SA.voteTime p.toParams i ≤ v → ∀ w, s + 1 ≤ w → w ≤ i →
      ∀ z ∈ rho.honest, ∀ K, headAtLabel p c E rho z w = some K → Block.Preceq B K by
    intro i hi hv
    exact h i hi hv i hi le_rfl
  intro i hi
  induction i, hi using Nat.le_induction with
  | base =>
    intro hv w hw1 hw2
    have hw : w = s + 1 := le_antisymm hw2 hw1
    subst hw
    intro z hz K hK
    exact healing_slow_first_transfer E rho hrec mono crossing writes hgst hphase hhead hgate
      hx hgw hst hres hBC hel hjx hz hv hK
  | succ i hi ih =>
    intro hv w hw1 hw2
    have hvi : SA.voteTime p.toParams i ≤ v := (hvmono (Nat.le_succ i)).trans hv
    by_cases hwi : w ≤ i
    · exact ih hvi w hw1 hwi
    have hw : w = i + 1 := le_antisymm hw2 (Nat.succ_le_of_lt (Nat.lt_of_not_le hwi))
    subst hw
    intro z hz K hK
    unfold headAtLabel at hK
    rw [postClock_def, preTick_def] at hK
    cases hiz' : V2.D.Run.tickIdx? rho z (SA.voteTime p.toParams (i + 1)) with
    | none => rw [hiz'] at hK; cases hK
    | some iz =>
    rw [hiz'] at hK
    have hiz := V2.D.Run.tickIdx?_spec hiz'
    have hKeq := Option.some.inj hK
    subst hKeq
    have hsi : SA.voteTime p.toParams s ≤ SA.voteTime p.toParams i :=
      hvmono ((Nat.le_succ s).trans hi)
    exact healing_next_transfer_core E rho hrec mono crossing hgst hphase (hhead.trans hsi)
      (ih hvi i hi le_rfl) hz hiz hv
      (healing_slow_lease E rho hrec mono writes (hgst.trans hhead) (hgate.trans hphase.2.1)
        hx hgw hst hres hBC hel ((Nat.le_succ s).trans hi) (hv.trans hphase.2.1) (ih hvi) hz hiz)

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21:650–715 (H.1 + H.2 S2, slow arm); plan H-SUPPORT §5.
DC: INTENTIONAL the S2 proposal clause of Transfers for a synchronous-window slow body. -/
theorem healing_slow_proposals [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : Recovery₂ p c E rho G ΔF)
    (mono : RMono p c E rho) (crossing : RXing p c E rho)
    (writes : ∀ i x (row : Block × Nat × Time),
      row ∈ (storeAt p c E rho i x).base.obligations →
      ∃ j < i, ∃ s B, IsGateTick p c rho j x s ∧ gatePassedAt p c E rho j ∧
        gateResultAt p c E rho j = some (some B) ∧ Block.Preceq row.1 B ∧
        (row.1, row.2.1) ∈ @GridCO.gateWriteKeys GridCO.slowLeasePolicy .root p.toParams.engine p.n
          (actView (clockPre p (storeAt p c E rho j x) (SA.gateTime p.toParams s))) s B ∧
        row.2.2 = SA.gateTime p.toParams s + SA.lifetime p.toParams ∧
        row.2.2 = SA.releaseTime p.toParams (s + p.k) ∧
        ∀ k w C, j < k → k < i → IsGateTick p c rho k x w →
          let pre := clockPre p (storeAt p c E rho k x) (SA.gateTime p.toParams w)
          GridCO.savedGenuine pre.base w = none →
          SA.Root.confirmationFrom p.toParams (eraseFG pre.fg.F) (actView pre) w = some C →
          (actView pre).obligations.any (fun r => !Block.compatible r.1 C) = false →
          (row.1, row.2.1) ∉ @GridCO.gateWriteKeys GridCO.slowLeasePolicy .root
              p.toParams.engine p.n
            (actView pre) w C)
    {u v : Time} {m : Nat} {J : Option (FGBlock (Fin p.n))} {contested : Bool}
    (hgst : E.t_GST ≤ u) (hphase : PhaseInterval p c E rho u v m J contested)
    {s : Slot} {B : Block} (hhead : u ≤ SA.voteTime p.toParams s)
    (hgate : SA.gateTime p.toParams s ≤ v)
    {x : V} (hx : x ∈ rho.honest)
    (hgw : E.t_GST ≤ SA.voteTime p.toParams (s + 1 - p.k)) {st : State p.n}
    (hst : gateIn p c E rho x s = some st) {C : Block}
    (hres : gateResult p c E rho x s = some (some C)) (hBC : Block.Preceq B C)
    (hel : GridCO.slowEligible p.toParams.engine (actView st) s B = true)
    {jx : Nat} (hjx : IsGateTick p c rho jx x s)
 :
    ∀ i Q, s + 2 ≤ i → SA.proposalTime p.toParams i ≤ v →
      HonestProposal E rho (fgsaInterface p c) i Q → Block.Preceq B Q.parent := by
  have hS := hrec.base.valid.toScheduleWellFormed
  have hDelta := hrec.base.delta
  have hd := p.deltaPos
  have hheads := healing_slow_heads E rho hrec mono crossing writes hgst hphase hhead hgate
    hx hgw hst hres hBC hel hjx
  refine healing_proposals_cover E rho hrec mono crossing hgst hphase hhead hheads ?_
  intro i hi hv ip y hy hip hFB
  have hiI : (s : Int) + 2 ≤ (i : Int) := by exact_mod_cast hi
  have hq : SA.voteTime p.toParams (s + 1) < SA.proposalTime p.toParams i := by
    change 4 * p.Δ * ((s + 1 : Nat) : Int) + p.Δ < 4 * p.Δ * (i : Int)
    push_cast
    nlinarith
  obtain ⟨iq, hiq⟩ := healing_support_vote_tick E rho hS hDelta hy (s + 1)
    ((hq.le.trans hv).trans hphase.2.1)
  have hqa : iq < ip := slow_idx_lt E rho hS hiq hip hq
  refine healing_slow_lease_at E rho hrec mono writes (hgst.trans hhead)
    (hgate.trans hphase.2.1) hx hgw hst hres hBC hel hphase.2.1 ?_ hy hiq hqa ?_ hFB
  · intro w hw hwT
    refine hheads w hw (le_trans ?_ hwT)
    change 4 * p.Δ * (w : Int) + p.Δ ≤ 4 * p.Δ * (w : Int) + 6 * p.Δ
    linarith
  · intro j' t hj' ht'
    exact ((fgsa_tick_time_strict E rho hS ht' hip hj').le).trans hv

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21:650–715 (H.1 + H.2 S3, slow arm); plan H-SUPPORT §5; ruling B31.
DC: INTENTIONAL the guarded S3 output clause of Transfers for a synchronous-window slow
body. The guard d_s + 4Δ ≤ v is the B31 premise of the output clause. -/
theorem healing_slow_output [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : Recovery₂ p c E rho G ΔF)
    (mono : RMono p c E rho) (crossing : RXing p c E rho)
    (writes : ∀ i x (row : Block × Nat × Time),
      row ∈ (storeAt p c E rho i x).base.obligations →
      ∃ j < i, ∃ s B, IsGateTick p c rho j x s ∧ gatePassedAt p c E rho j ∧
        gateResultAt p c E rho j = some (some B) ∧ Block.Preceq row.1 B ∧
        (row.1, row.2.1) ∈ @GridCO.gateWriteKeys GridCO.slowLeasePolicy .root p.toParams.engine p.n
          (actView (clockPre p (storeAt p c E rho j x) (SA.gateTime p.toParams s))) s B ∧
        row.2.2 = SA.gateTime p.toParams s + SA.lifetime p.toParams ∧
        row.2.2 = SA.releaseTime p.toParams (s + p.k) ∧
        ∀ k w C, j < k → k < i → IsGateTick p c rho k x w →
          let pre := clockPre p (storeAt p c E rho k x) (SA.gateTime p.toParams w)
          GridCO.savedGenuine pre.base w = none →
          SA.Root.confirmationFrom p.toParams (eraseFG pre.fg.F) (actView pre) w = some C →
          (actView pre).obligations.any (fun r => !Block.compatible r.1 C) = false →
          (row.1, row.2.1) ∉ @GridCO.gateWriteKeys GridCO.slowLeasePolicy .root
              p.toParams.engine p.n
            (actView pre) w C)
    {u v : Time} {m : Nat} {J : Option (FGBlock (Fin p.n))} {contested : Bool}
    (hgst : E.t_GST ≤ u) (hphase : PhaseInterval p c E rho u v m J contested)
    {s : Slot} {B : Block} (hhead : u ≤ SA.voteTime p.toParams s)
    (hgate : SA.gateTime p.toParams s ≤ v)
    (hguard : SA.gateTime p.toParams s + 4 * p.Δ ≤ v)
    {x : V} (hx : x ∈ rho.honest)
    (hgw : E.t_GST ≤ SA.voteTime p.toParams (s + 1 - p.k)) {st : State p.n}
    (hst : gateIn p c E rho x s = some st) {C : Block}
    (hres : gateResult p c E rho x s = some (some C)) (hBC : Block.Preceq B C)
    (hel : GridCO.slowEligible p.toParams.engine (actView st) s B = true)
    {jx : Nat} (hjx : IsGateTick p c rho jx x s)
 :
    ∀ i y, y ∈ rho.honest → afterTicksIdx rho (SA.gateTime p.toParams s + 4 * p.Δ) ≤ i →
      i ≤ timeIdx rho v → Block.Preceq B (S_at p c E rho i y) := by
  have hS := hrec.base.valid.toScheduleWellFormed
  have hDelta := hrec.base.delta
  have hd := p.deltaPos
  have hheads := healing_slow_heads E rho hrec mono crossing writes hgst hphase hhead hgate
    hx hgw hst hres hBC hel hjx
  refine healing_output_cover E rho hrec mono crossing hgst hphase hhead hguard hheads ?_
  intro j y hy ht hFB
  have hq : SA.voteTime p.toParams (s + 1) < SA.gateTime p.toParams (s + 1) := by
    change 4 * p.Δ * ((s + 1 : Nat) : Int) + p.Δ < 4 * p.Δ * ((s + 1 : Nat) : Int) + 6 * p.Δ
    linarith
  have hgv : SA.gateTime p.toParams (s + 1) ≤ v := by
    refine le_trans (le_of_eq ?_) hguard
    change 4 * p.Δ * ((s + 1 : Nat) : Int) + 6 * p.Δ = 4 * p.Δ * (s : Int) + 6 * p.Δ + 4 * p.Δ
    push_cast
    ring
  obtain ⟨iq, hiq⟩ := healing_support_vote_tick E rho hS hDelta hy (s + 1)
    ((hq.le.trans hgv).trans hphase.2.1)
  have hqa : iq < j := slow_idx_lt E rho hS hiq ht hq
  refine healing_slow_lease_at E rho hrec mono writes (hgst.trans hhead)
    (hgate.trans hphase.2.1) hx hgw hst hres hBC hel hphase.2.1 ?_ hy hiq hqa ?_ hFB
  · intro w hw hwT
    refine hheads w hw (le_trans ?_ hwT)
    change 4 * p.Δ * (w : Int) + p.Δ ≤ 4 * p.Δ * (w : Int) + 6 * p.Δ
    linarith
  · intro j' t hj' ht'
    exact ((fgsa_tick_time_strict E rho hS ht' ht hj').le).trans hgv

end AvailableChain.FGSA.Run
end
