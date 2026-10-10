module
public import AvailableChainFGSAProofs.Proofs.WeakContinuationGrowth.Epoch
public import AvailableChainFGSAProofs.Proofs.WeakContinuationGrowth.StepInit
public import AvailableChainFGSAProofs.Proofs.WeakContinuationGrowth.Frame
public import AvailableChainFGSAProofs.Proofs.Shared.Roots
public import AvailableChainFGSAProofs.Proofs.Shared.Reads
public import AvailableChainFGSARun.Proofs.Receipts
public import AvailableChainFGSARun.Proofs.AC
public import AvailableChainFGSAProofs.Proofs.Shared.Count
public import AvailableChainFGSAProofs.Proofs.Shared.SameLabel
public import AvailableChainFGSAProofs.Proofs.Shared.Relay
public import AvailableChainFGSA.Proofs.Head.Transfer -- shake: keep (fgsa_headInTree_covers_of_transfer proof reference)

namespace AvailableChain.GridCO

private def growth_advance (old candidate : Block) : Block :=
  if Block.preceq candidate old then old else candidate
private theorem growth_advance_eq : @advance = @growth_advance := rfl

private def growth_stampBlock {n : Nat} {mode : HeadMode} (st : State n mode) (b : Block) : Time :=
  ((st.blockStamp.find? (fun row => row.1 == b)).map Prod.snd).getD st.now
private theorem growth_stampBlock_eq : @stampBlock = @growth_stampBlock := rfl

private def growth_stampVote {n : Nat} {mode : HeadMode} (st : State n mode) (o : Wire n mode)
  : Time :=
  ((st.voteStamp.find? (fun row => row.1 == o)).map Prod.snd).getD st.now
private theorem growth_stampVote_eq : @stampVote = @growth_stampVote := rfl

private def growth_admitProposal (p : Params) {n : Nat} {mode : HeadMode} (st : State n mode)
  (o : Wire n mode)
    (b : Block) (raw : List (HeadWire n mode)) : State n mode :=
  let current := (st.now / (4 * p.Δ)).toNat
  let correctProposer := match o.auth with
    | .proposer s => s == b.slot
    | _ => false
  if b.slot > current || !blockKnown st b.parent || b ∈ st.blocks ||
      !(b.parent.slot < b.slot) || !correctProposer then st else
    let st' := { st with
      blocks := st.blocks ++ [b]
      blockStamp := st.blockStamp ++ [(b, st.now)]
      proposals := st.proposals ++ [o] }
    raw.foldl (fun acc row => admitVote p acc (fromHead row)) st'
private theorem growth_admitProposal_eq : @admitProposal = @growth_admitProposal := rfl

private def growth_resolvedBefore {n : Nat} {mode : HeadMode}
    (st : State n mode) (o : Wire n mode) (cutoff : Time) : Bool :=
  match resolvedHead? st o with
  | none => false
  | some B => decide (B.slot ≤ (headLabel? o).getD 0) &&
      decide (stampVote st o < cutoff) && decide (stampBlock st B < cutoff)
private theorem growth_resolvedBefore_eq : @resolvedBefore = @growth_resolvedBefore := rfl

end AvailableChain.GridCO

namespace AvailableChain.FGSA

private def growth_gateStep (p : Params) (st : State p.n) (s : Slot) : State p.n :=
  let a := eraseFG st.fg.F
  let st := if (GridCO.savedGenuine st.base s).isSome then st else
    { onView (fun v => SA.Root.gateFrom p.toParams a v s) st with
      fastWrite := st.fastWrite ++ [(s, fastSet p a (actView st) s)] }
  normalizeS st
private theorem growth_gateStep_eq : @gateStep = @growth_gateStep := rfl

end AvailableChain.FGSA

namespace AvailableChain.FGSA.Run
private def growth_headAtIdx (p : Params) {In : Type} (c : AppCodec In) {V : Type} [DecidableEq V]
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (k : Nat) (s : Slot) : Block :=
  match rho.events[k]? with
  | some (.tick y t) => FGSA.headVote p ((fgsa p c).clock (V2.D.Run.stateBefore E rho k y) t).st s
  | _ => .genesis
private theorem growth_headAtIdx_eq : @headAtIdx = @growth_headAtIdx := rfl

private def growth_blockOf (p : Params) (o : Obj p) : Option Block :=
  match (toWire p o).decode with
  | some (.block _ N) => some N.erase
  | _ => none
private theorem growth_blockOf_eq : @blockOf? = @growth_blockOf := rfl
end AvailableChain.FGSA.Run

public section

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG KitFG Gen.Pure

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}
    {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}
    {w : HealingWitness} {iStar : Nat}

/-- WC plan §6.7; DC completed result evidence persists in a longer history. -/
private theorem result_mono {i k j : Nat} {x : V} {s : Slot} {B : Block}
    (h : WCResult p c E rho w iStar i j x s B) (hik : i ≤ k) :
    WCResult p c E rho w iStar k j x s B :=
  { h with completed := h.completed.trans_le hik }

/-- WC plan §6.7; DC prefix origins persist in a longer history. -/
private theorem history_mono {i k : Nat} {B : Block}
    (h : WCBelowHistory p c E rho w iStar i B) (hik : i ≤ k) :
    WCBelowHistory p c E rho w iStar k B := by
  rcases h.origin with h | ⟨j, x, s, C, hr, hb⟩
  · exact ⟨Or.inl h⟩
  · exact ⟨Or.inr ⟨j, x, s, C, result_mono hr hik, hb⟩⟩

/-- WC plan §6.7; DC cached finality has a low or a high historical origin. -/
theorem wcg_finalHistoryAt {i k : Nat} {x : V}
    (hs : WCSeed p c E rho w iStar) (hi : WCInv p c E rho w iStar i)
    (hlo : iStar ≤ k) (hki : k ≤ i) (hx : x ∈ rho.honest) :
    WCBelowHistory p c E rho w iStar k (F_at p c E rho k x) := by
  obtain ⟨D, hD, hF⟩ := ((hi.finite k hlo hki).store x hx).fg.Fcar
  by_cases hX : (finalityView p D).F = .genesis
  · have he : F_at p c E rho k x = .genesis := by
      change eraseFG (storeAt p c E rho k x).fg.F = _
      rw [← hF, hX]
      rfl
    rw [he]
    exact ⟨Or.inl (block_genesis_preceq _)⟩
  by_cases hlow : (finalityView p D).h_F ≤ w.M
  · exact ⟨Or.inl (block_preceq_trans
      (hi.lowFinalized k x D _ _ hlo hki ⟨hx, hD⟩ hF rfl hlow) hs.sourcePrefix)⟩
  · have hn : (finalityView p D).h_F ≠ 0 := by
      simp only [Height] at *
      omega
    obtain ⟨C, D₀, _, _, hbirth, _⟩ := (fgCertificateLaws p).finality_origin D hn
    have hheight : (heightView p (finalityView p D).F).h = (finalityView p D).h_F := by
      rw [← hbirth.2.2.1, (fgCertificateLaws p).height.entry_same_height, hbirth.2.1]
    have hcert : (finalityView p D).F ∈ certified p D :=
      ⟨D, preceq_refl D, Or.inr (Or.inl rfl)⟩
    have hh : w.M + 1 ≤ (heightView p (finalityView p D).F).h := by
      rw [hheight]
      simp only [Height] at *
      omega
    have ho := (hi.highCertificates k x D _ hlo hki hx hD hcert hX hh).2
    rw [hF] at ho
    exact ho

/-- WC plan §6.7; DC the output origin keeps its own finite history bound. -/
theorem wcg_outputHistoryAt {i k : Nat} {x : V}
    (hs : WCSeed p c E rho w iStar) (hi : WCInv p c E rho w iStar i)
    (hlo : iStar ≤ k) (hki : k ≤ i) (hx : x ∈ rho.honest) :
    WCBelowHistory p c E rho w iStar k (S_at p c E rho k x) := by
  rcases hi.outputOrigin k x hlo hki hx with hq | ⟨j, y, s, hr⟩ | ⟨l, hl, hlk, he, _⟩
  · exact ⟨Or.inl (hq ▸ block_preceq_refl w.QStar)⟩
  · exact ⟨Or.inr ⟨j, y, s, _, hr, block_preceq_refl _⟩⟩
  · rw [he]
    exact history_mono (wcg_finalHistoryAt hs hi hl (hlk.trans hki) hx) hlk

/-- WC plan §6.7; DC result and output origins are compatible within the proved history. -/
theorem wcg_result_output_compatible {i k j : Nat} {x y : V} {s : Slot} {B : Block}
    (hi : WCInv p c E rho w iStar i) (hr : WCResult p c E rho w iStar i j y s B)
    (hlo : iStar ≤ k) (hki : k ≤ i) (hx : x ∈ rho.honest) :
    Block.Compatible (S_at p c E rho k x) B := by
  rcases hi.outputOrigin k x hlo hki hx with hq | ⟨l, z, r, ho⟩ | ⟨l, _, _, he, hc⟩
  · obtain ⟨C, hC, hqC, _⟩ :=
      hi.nonempty j y s hr.afterCut hr.completed hr.honest hr.event hr.label
    have he : C = B := Option.some.inj (Option.some.inj (hC.symm.trans hr.value))
    rw [hq]
    exact block_compatible_of_common (he ▸ hqC) (block_preceq_refl B)
  · have ho' := result_mono ho hki
    rcases lt_trichotomy r s with h | h | h
    · exact block_compatible_of_common (hi.ordered l j z y r s _ B ho' hr h)
        (block_preceq_refl B)
    · subst r
      exact hi.sameLabel l j z y s _ B ho' hr
    · exact block_compatible_of_common (block_preceq_refl _)
        (hi.ordered j l y z s r B _ hr ho' h)
  · rw [he]
    exact hc j y s B hr

end AvailableChain.FGSA.Run


/-! Companion event induction. The source WC modules stay unchanged.
One-quorum causality and invariant-to-safety use the existing lane Export.
Low finality uses whole-run accountability in place of FaultX. -/


namespace AvailableChain.FGSA
open AvailableChain.SimplexFG
/-- WC plan §6.5; DC finite event provenance: private replay or source-construction helper. -/
private def growthStepFacts_step_admitBlock (p : Params) (st : State p.n) (s : Slot)
    (N : NamedProposal p.n) : State p.n :=
  if !namedParentHeld st N then st else
  match parentFG st N.erase with
  | none => st
  | some P =>
      if blockAccepted p st s N P then
        let st1 : State p.n := { st with
          base := GridCO.admitProposal p.toParams.engine st.base
            (baseProposal s N.erase N.raw N.support) N.erase (N.raw.map baseHead)
          fg := Window.on_block p p.K_W st.fg (fgBlock P N.erase N.rows)
          proposals := st.proposals ++ [⟨.proposer s, .proposal N⟩] }
        let st2 := if st1.fg.F = st.fg.F then st1 else reconcile st1
        N.rows.foldl (admitRow p) st2
      else st

/-- WC plan §6.5; DC finite event provenance: private replay or source-construction helper. -/
private theorem growthStepFacts_step_admitBlock_eq : @admitBlock =
  @growthStepFacts_step_admitBlock := rfl

end AvailableChain.FGSA


/-! WC plan §6.5; DC original saved-result and certificate events persist in each finite read. -/

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG KitFG

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}
    {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}

/-- WC plan §6.5; DC receipt replay: retain the original trigger and acceptance index. -/
private theorem growthStepFacts_step_receiptOrigins (i : Nat) (x : V) :
    WCReceiptOrigins p c E rho i x (storeAt p c E rho i x) := by
  constructor
  · exact fgsa_block_stamp_source E rho i x
  · exact fgsa_vote_stamp_source E rho i x

/-- WC plan §6.5; DC finite event provenance: private replay or source-construction helper. -/
private def growthStepFacts_step_savedPairs (st : State p.n) : List (Slot × Block) :=
  st.base.genuine.filterMap (fun row => row.2.map (fun B => (row.1, B)))

/-- WC plan §6.5; DC finite event provenance: private replay or source-construction helper. -/
private theorem growthStepFacts_step_savedPairs_mem (st : State p.n) (s : Slot) (B : Block) :
    (s, B) ∈ growthStepFacts_step_savedPairs st ↔ (s, some B) ∈ st.base.genuine := by
  constructor
  · intro h
    obtain ⟨row, hr, hb⟩ := List.mem_filterMap.mp h
    obtain ⟨C, hc, he⟩ := Option.map_eq_some_iff.mp hb
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
    have hrow : row = (row.1, some C) := Prod.ext rfl hc
    rwa [hrow] at hr
  · intro h
    exact List.mem_filterMap.mpr ⟨(s, some B), h, rfl⟩

/-- WC plan §6.5; DC finite event provenance: private replay or source-construction helper. -/
private theorem growthStepFacts_step_savedPairs_reconcile (st : State p.n) :
    growthStepFacts_step_savedPairs (reconcile st) ⊆ growthStepFacts_step_savedPairs st := by
  rintro ⟨s, B⟩ hm
  rw [growthStepFacts_step_savedPairs_mem, reconcile_genuine] at hm
  obtain ⟨row, hr, he⟩ := List.mem_map.mp hm
  have hk := congrArg Prod.fst he
  have hb := (Option.filter_eq_some_iff.mp (congrArg Prod.snd he)).1
  rw [growthStepFacts_step_savedPairs_mem]
  have hrow : row = (s, some B) := Prod.ext hk hb
  rwa [hrow] at hr

/-- WC plan §6.5; DC finite event provenance: private replay or source-construction helper. -/
private theorem growthStepFacts_step_savedPairs_admitRows (rows : List (RowWire p.n)) (st :
  State p.n) :
    growthStepFacts_step_savedPairs (rows.foldl (admitRow p) st) =
      growthStepFacts_step_savedPairs st := by
  induction rows generalizing st with
  | nil => rfl
  | cons a rows ih =>
    rw [List.foldl_cons, ih]
    rcases admitRow_eq p st a with h | h
    · rw [h]
    · rw [h]
      rfl

-- WC plan §6.5; DC handler order. The upstream Schedule helper is private.
/-- WC plan §6.5; DC finite event provenance: private replay or source-construction helper. -/
private theorem growthStepFacts_step_proposal_genuine (q : GridCO.Params) {n : Nat}
    (st : GridCO.State n .root) (o : GridCO.Wire n .root) (b : Block)
    (raw : List (GridCO.HeadWire n .root)) :
    (GridCO.admitProposal q st o b raw).genuine = st.genuine := by
  obtain ⟨auth, msg⟩ := o
  cases auth <;> rw [GridCO.growth_admitProposal_eq]
  all_goals unfold GridCO.growth_admitProposal
  all_goals dsimp only
  all_goals split
  all_goals first | rfl | exact (foldVotes_fields q raw _).2.2.2.2.1

/-- WC plan §6.5; DC finite event provenance: private replay or source-construction helper. -/
private theorem growthStepFacts_step_savedPairs_process (st : State p.n) (o : Wire p.n) :
    growthStepFacts_step_savedPairs (process p st o) ⊆ growthStepFacts_step_savedPairs st := by
  change growthStepFacts_step_savedPairs (match o.decode with
    | some (.vote s i b) => admitHead p st s i b
    | some (.row _ body) => admitRow p st ⟨o.auth, body⟩
    | some (.block s N) => admitBlock p st s N
    | none => st) ⊆ growthStepFacts_step_savedPairs st
  cases o.decode with
  | none => exact List.Subset.refl _
  | some a =>
    cases a <;> dsimp only
    case vote s i b =>
      unfold growthStepFacts_step_savedPairs
      rw [admitHead_genuine]
    case row i body =>
      rcases admitRow_eq p st ⟨o.auth, body⟩ with h | h <;> rw [h]
      exact List.Subset.refl _
    case block s N =>
      cases hn : namedParentHeld st N with
      | false => rw [admitBlock_refused p st s N (Or.inl hn)]
      | true =>
        cases hp : parentFG st N.erase with
        | none => rw [admitBlock_refused p st s N (Or.inr (Or.inl hp))]
        | some P =>
          cases ha : blockAccepted p st s N P with
          | false =>
            rw [admitBlock_refused p st s N (Or.inr (Or.inr ⟨P, hp, ha⟩))]
          | true =>
            rw [growthStepFacts_step_admitBlock_eq]
            unfold growthStepFacts_step_admitBlock
            simp only [hn, Bool.not_true, Bool.false_eq_true, ite_false]
            rw [hp]
            dsimp only
            rw [ha, ite_eq_left rfl, growthStepFacts_step_savedPairs_admitRows]
            split
            · unfold growthStepFacts_step_savedPairs
              dsimp only
              rw [growthStepFacts_step_proposal_genuine]
            · apply List.Subset.trans (growthStepFacts_step_savedPairs_reconcile _)
              unfold growthStepFacts_step_savedPairs
              dsimp only
              rw [growthStepFacts_step_proposal_genuine]

/-- WC plan §6.5; DC finite event provenance: private replay or source-construction helper. -/
private theorem growthStepFacts_step_savedPairs_clock (st : State p.n) (t : Time) (pair : Slot
  × Block)
    (hm : pair ∈ growthStepFacts_step_savedPairs (clock p st t)) :
    pair ∈ growthStepFacts_step_savedPairs st ∨
      (t = SA.gateTime p.toParams pair.1 ∧
       SA.Root.confirmationFrom p.toParams (eraseFG (clockPre p st t).fg.F)
         (actView (clockPre p st t)) pair.1 = some pair.2) := by
  change pair ∈ growthStepFacts_step_savedPairs (if isGateTime p t then
    gateStep p (clockPre p st t) ((t - 6 * p.Δ) / (4 * p.Δ)).toNat
    else clockPre p st t) at hm
  have hpre : growthStepFacts_step_savedPairs (clockPre p st t) =
    growthStepFacts_step_savedPairs st := by
    unfold growthStepFacts_step_savedPairs
    rw [clockPre_genuine]
  split at hm
  · rename_i ht
    let s := ((t - 6 * p.Δ) / (4 * p.Δ)).toNat
    let pre := clockPre p st t
    have htime : t = SA.gateTime p.toParams s :=
      beq_iff_eq.mp (Bool.and_eq_true_iff.mp ht).2
    cases hs : GridCO.savedGenuine pre.base s with
    | some saved =>
      rw [gateStep_saved p pre s (by rw [hs]; rfl)] at hm
      unfold growthStepFacts_step_savedPairs at hm
      rw [normalizeS_fields] at hm
      exact Or.inl (hpre ▸ hm)
    | none =>
      have hg : (gateStep p pre s).base.genuine = pre.base.genuine ++
          [(s, SA.Root.confirmationFrom p.toParams (eraseFG pre.fg.F) (actView pre) s)] := by
        rw [FGSA.growth_gateStep_eq]
        unfold FGSA.growth_gateStep
        rw [normalizeS_fields]
        simp only [hs, Option.isSome_none, Bool.false_eq_true, ite_false]
        exact saGate_genuine p.toParams (eraseFG pre.fg.F) (actView pre) s hs
      rcases pair with ⟨v, B⟩
      rw [growthStepFacts_step_savedPairs_mem, hg, List.mem_append] at hm
      rcases hm with hm | hm
      · exact Or.inl (hpre ▸ (growthStepFacts_step_savedPairs_mem pre v B).mpr hm)
      · have he := List.mem_singleton.mp hm
        obtain ⟨rfl, hC⟩ := Prod.mk.inj he
        exact Or.inr ⟨htime, hC.symm⟩
  · exact Or.inl (hpre ▸ hm)

/-- WC plan §6.5; DC actual saved origin: a retained value still has its original gate result. -/
private theorem growthStepFacts_step_savedOrigin (hs : V2.D.ScheduleWellFormed E rho)
    (i : Nat) (x : V) (s : Slot) (B : Block)
    (hb : GridCO.savedGenuine (storeAt p c E rho i x).base s = some (some B)) :
    ∃ j < i, IsGateTick p c rho j x s ∧ gateResultAt p c E rho j = some (some B) := by
  obtain ⟨row, hr, he⟩ := Option.map_eq_some_iff.mp hb
  have hk : row.1 = s := by simpa using List.find?_some hr
  have hm : (s, B) ∈ growthStepFacts_step_savedPairs (storeAt p c E rho i x) := by
    rw [growthStepFacts_step_savedPairs_mem]
    simpa only [← hk, ← he] using List.mem_of_find?_eq_some hr
  obtain ⟨j, hj, t, ht, htime, hC⟩ :=
    V2.D.Engine.clock_field_origin_of_subset (P := fgsa p c)
      (fun nd => growthStepFacts_step_savedPairs nd.st) rfl
      (fun nd o pair h => growthStepFacts_step_savedPairs_process nd.st (toWire p o) h)
      (fun _ _ _ h => h)
        (fgsa_hrestore_field_retained p c growthStepFacts_step_savedPairs (fun _ => rfl))
      (fun nd t pair => t = SA.gateTime p.toParams pair.1 ∧
        SA.Root.confirmationFrom p.toParams (eraseFG (clockPre p nd.st t).fg.F)
          (actView (clockPre p nd.st t)) pair.1 = some pair.2)
      (fun nd t pair h => growthStepFacts_step_savedPairs_clock nd.st t pair h) E rho i x (s, B) hm
  change t = SA.gateTime p.toParams s at htime
  subst t
  refine ⟨j, hj, ht, ?_⟩
  rw [gateResultAt_eq_gateResult p c E rho hs ht, gateResult_def, gateIn_def, preTick_def,
    fgsa_tickIdx_of_event p c E rho hs ht]
  exact congrArg some hC

/-- WC plan §6.5; DC a gate is after the completed cut exactly when its label is later. -/
theorem wcg_gate_cut_iff (hsch : V2.D.ScheduleWellFormed E rho)
    {w : HealingWitness} {iStar j : Nat} {x : V} {s : Slot}
    (hs : WCSeed p c E rho w iStar) (ht : IsGateTick p c rho j x s) :
    iStar ≤ j ↔ w.u < s := by
  have hc := V2.D.Engine.filter_eq_take hsch (cutPred (SA.gateTime p.toParams w.u)) (by
    intro e f hle hf
    exact decide_eq_true (hle.trans (of_decide_eq_true hf)))
  constructor
  · intro hj
    by_contra hn
    have hle : (s : Int) ≤ w.u := Int.ofNat_le.mpr (Nat.le_of_not_gt hn)
    have htime : SA.gateTime p.toParams s ≤ SA.gateTime p.toParams w.u := by
      change 4 * p.Δ * (s : Int) + 6 * p.Δ ≤ 4 * p.Δ * (w.u : Int) + 6 * p.Δ
      nlinarith [p.deltaPos]
    have hf := V2.D.Engine.filter_false_of_index_ge hsch
      (cutPred (SA.gateTime p.toParams w.u)) (by
        intro e f hle hf
        exact decide_eq_true (hle.trans (of_decide_eq_true hf)))
      (show afterTicksIdx rho (SA.gateTime p.toParams w.u) ≤ j from hs.cut ▸ hj) ht
    have hh : cutPred (SA.gateTime p.toParams w.u)
        (.tick x (SA.gateTime p.toParams s) : V2.Event V (fgsa p c).Object) = true :=
      decide_eq_true (Prod.Lex.toLex_le_toLex.mpr
        (htime.lt_or_eq.imp id (fun he => ⟨he, le_rfl⟩)))
    rw [hh] at hf
    cases hf
  · intro hslabel
    by_contra hn
    have hj : j < afterTicksIdx rho (SA.gateTime p.toParams w.u) :=
      hs.cut ▸ Nat.lt_of_not_ge hn
    have hm : V2.Event.tick x (SA.gateTime p.toParams s) ∈
        rho.events.filter (cutPred (SA.gateTime p.toParams w.u)) := by
      rw [hc]
      apply List.mem_of_getElem? (i := j)
      change (rho.events.take (afterTicksIdx rho (SA.gateTime p.toParams w.u)))[j]? = _
      rw [List.getElem?_take_of_lt hj]
      exact ht
    have hk := of_decide_eq_true (List.mem_filter.mp hm).2
    have hh : SA.gateTime p.toParams s ≤ SA.gateTime p.toParams w.u := by
      rcases Prod.Lex.toLex_le_toLex.mp hk with h | ⟨h, _⟩
      · exact h.le
      · exact h.le
    have hcast : (w.u : Int) < s := Int.ofNat_lt.mpr hslabel
    change 4 * p.Δ * (s : Int) + 6 * p.Δ ≤ 4 * p.Δ * (w.u : Int) + 6 * p.Δ at hh
    nlinarith [p.deltaPos]

/-- Finite seed facts follow from continuation producers at any index.
No seed, suffix invariant, one-third cap, or FaultX premise is needed. -/
theorem wcg_finiteFacts :
  ∀
  (_hvalid : V2.D.ExecutionValid E rho)
  (_hroots : NamedRootCollisionFree p c E rho)
  (_hstrat : RStrat p c E rho)
  (_hnoslash : ∀ x ∈ rho.honest, EmittedRowsNoSlash p c E rho x)
  (_hemitted : ∀ j x r a e, HonestRowAt p c E rho j x r a →
    namedEntry a.payload.height_pair = some e →
    ∃ C B, actionSourceFG p c E rho x r = some (some C) ∧
      e = (hOf p.E p.cfg C, (derive p.E p.cfg C).T_h.root) ∧
      FGBlock.Preceq (derive p.E p.cfg C).T_h C ∧
      gateResult p c E rho x (r * p.R) = some (some B) ∧
      Block.Preceq (eraseFG C) B ∧ fastAt p c E rho x (r * p.R) (eraseFG C))
  (_hlease : ∀ i x row, row ∈ (storeAt p c E rho i x).base.obligations →
    ∃ j < i, ∃ s B, IsGateTick p c rho j x s ∧ gatePassedAt p c E rho j ∧
      gateResultAt p c E rho j = some (some B) ∧ Block.Preceq row.1 B ∧
      (row.1, row.2.1) ∈
      (let wcView := actView (clockPre p (storeAt p c E rho j x) (SA.gateTime p.toParams s));
        (wcView.blocks.filter (fun b => b != .genesis && Block.preceq b B)).flatMap
          (fun b => (@GridCO.admissionLevels GridCO.slowLeasePolicy
            p.toParams.engine p.n .root wcView s b).map (fun g => (b, g)))) ∧
      row.2.2 = SA.gateTime p.toParams s + SA.lifetime p.toParams ∧
      row.2.2 = SA.releaseTime p.toParams (s + p.k) ∧
      ∀ k w C, j < k → k < i → IsGateTick p c rho k x w →
        let pre := clockPre p (storeAt p c E rho k x) (SA.gateTime p.toParams w)
        GridCO.savedGenuine pre.base w = none →
        SA.Root.confirmationFrom p.toParams (eraseFG pre.fg.F) (actView pre) w = some C →
        (actView pre).obligations.any (fun r => !Block.compatible r.1 C) = false →
        (row.1, row.2.1) ∉ (let wcView := actView pre;
        (wcView.blocks.filter (fun b => b != .genesis && Block.preceq b C)).flatMap
          (fun b => (@GridCO.admissionLevels GridCO.slowLeasePolicy
            p.toParams.engine p.n .root wcView w b).map (fun g => (b, g)))))
  (_hfast : ∀ i x,
    ∀ s X, X ∈ (FGSA.fastWriteAt (storeAt p c E rho i x) s).getD [] →
      ∃ j < i, IsGateTick p c rho j x s ∧ gatePassedAt p c E rho j ∧
        ∃ B, gateResultAt p c E rho j = some (some B) ∧
          Block.Preceq X B ∧ fastAt p c E rho x s X)
  (_hdeadlines : ∀ i x,
    ∀ K g deadline, (K, g, deadline) ∈ (storeAt p c E rho i x).base.obligations →
      ∀ B, B ≠ .genesis → Block.Preceq B K →
        Gen.AC.Root.ProtectsUntil (storeAt p c E rho i x).base B g deadline),
  ∀ n, WCFiniteFacts p c E rho n := by
  intro hvalid hroots hstrat hnoslash hemitted hlease hfast hdeadlines n
  refine ⟨fun x _ => cstoreInv_stateBefore E rho n x,
    fun x _ => nestOK_stateBefore E rho n x,
    fun x _ => metaInv_stateBefore E rho n x,
    fun x _ => growthStepFacts_step_receiptOrigins n x,
    fun x _ row hr => ⟨hlease n x row hr⟩,
    fun x _ => hdeadlines n x,
    fun x _ => hfast n x,
    fun x _ s C hc => growthStepFacts_step_savedOrigin hvalid.toScheduleWellFormed n x s C hc,
      ?_, ?_⟩
  · intro x hx W hW X hX hne
    obtain ⟨y, r, wire, ⟨j, hj, hrow⟩, hname⟩ := hstrat n x W hx hW X hX hne
    obtain ⟨K, B, hK, hpair, hentry, hB, hKB, _⟩ := hemitted j y r wire _ hrow hname
    have hXK : X = (derive p.E p.cfg K).T_h := rootScope_eq hroots
      (rootScope_ancestor (rootScope_store hx hW) (certified_preceq hX))
      (rootScope_ancestor (rootScope_source hrow.1 hK) hentry) (congrArg Prod.snd hpair)
    exact ⟨j, y, r, wire, K, B, hj, hrow, hname, hK, hXK ▸ hentry, hB, hKB⟩
  · intro j k x r r' a b u v _ _ ha hb hu hv
    exact hnoslash x ha.1 a b ⟨j, p.actionTime r, ha.2⟩ ⟨k, p.actionTime r', hb.2⟩ u v hu hv


variable [Fintype V]

/-- WC plan §6.5; DC each event's finite facts retain actual origins and deadlines. -/
theorem wcg_finiteStep (ΔF : Time) (w : HealingWitness) (iStar : Nat) :
  ∀
  (_hvalid : V2.D.ExecutionValid E rho)
  (_hlinked : V2.D.Linked (fgsaFamilies p c).linked rho)
  (_hcstar : V2.D.CStar (fgsaFamilies p c).fresh rho)
  (_hnr : V2.D.NoRestart rho)
  (_hdelta : E.Δ = p.Δ)
  (_hroots : NamedRootCollisionFree p c E rho)
  (_hsync : Gen.V2.Duty.PartialSynchronyBy E rho (fgsaDelay E.Δ ΔF))
  (_hdeltaF : E.Δ ≤ ΔF)
  (_hfaultQ : Gen.Pure.FaultQ p.n (Gen.V2.Duty.faulty rho).card)
  (_haccountable : FinalitySlashableBound p c E rho)
  (_hpart : ∀ s, w.u + 1 ≤ s → SA.voteTime p.toParams s ≤ rho.horizon →
    (Gen.V2.Duty.faulty rho).card <
      (Gen.V2.Duty.awakeHonest E rho (SA.voteTime p.toParams s)).card)
  (_hstore : RStore p c E rho)
  (_hcumul : RStoreCumul p c E rho)
  (_hmono : RMono p c E rho)
  (_hactive : RActive p c E rho)
  (_hframe : RFrameExactNext p c E rho)
  (_hmeta : RFrameNext p c E rho)
  (_hrec : RRec p c E rho)
  (_hgeo : RGeo p c E rho)
  (_hcert : RCert p c E rho)
  (_hsrc : TSrc p c E rho)
  (_hlabel : LabelBound p c E rho)
  (_hqc : RQCOrigin p c E rho)
  (_hstrat : RStrat p c E rho)
  (_hnoslash : ∀ x ∈ rho.honest, EmittedRowsNoSlash p c E rho x)
  (_hemitted : ∀ j x r a e, HonestRowAt p c E rho j x r a →
    namedEntry a.payload.height_pair = some e →
    ∃ C B, actionSourceFG p c E rho x r = some (some C) ∧
      e = (hOf p.E p.cfg C, (derive p.E p.cfg C).T_h.root) ∧
      FGBlock.Preceq (derive p.E p.cfg C).T_h C ∧
      gateResult p c E rho x (r * p.R) = some (some B) ∧
      Block.Preceq (eraseFG C) B ∧ fastAt p c E rho x (r * p.R) (eraseFG C))
  (_htargets : ∀ i x row, row ∈ (storeAt p c E rho i x).base.obligations →
    Block.Preceq row.1 (storeAt p c E rho i x).base.stableRecord)
  (_hlease : ∀ i x row, row ∈ (storeAt p c E rho i x).base.obligations →
    ∃ j < i, ∃ s B, IsGateTick p c rho j x s ∧ gatePassedAt p c E rho j ∧
      gateResultAt p c E rho j = some (some B) ∧ Block.Preceq row.1 B ∧
      (row.1, row.2.1) ∈
      (let wcView := actView (clockPre p (storeAt p c E rho j x) (SA.gateTime p.toParams s));
        (wcView.blocks.filter (fun b => b != .genesis && Block.preceq b B)).flatMap
          (fun b => (@GridCO.admissionLevels GridCO.slowLeasePolicy
            p.toParams.engine p.n .root wcView s b).map (fun g => (b, g)))) ∧
      row.2.2 = SA.gateTime p.toParams s + SA.lifetime p.toParams ∧
      row.2.2 = SA.releaseTime p.toParams (s + p.k) ∧
      ∀ k w C, j < k → k < i → IsGateTick p c rho k x w →
        let pre := clockPre p (storeAt p c E rho k x) (SA.gateTime p.toParams w)
        GridCO.savedGenuine pre.base w = none →
        SA.Root.confirmationFrom p.toParams (eraseFG pre.fg.F) (actView pre) w = some C →
        (actView pre).obligations.any (fun r => !Block.compatible r.1 C) = false →
        (row.1, row.2.1) ∉ (let wcView := actView pre;
        (wcView.blocks.filter (fun b => b != .genesis && Block.preceq b C)).flatMap
          (fun b => (@GridCO.admissionLevels GridCO.slowLeasePolicy
            p.toParams.engine p.n .root wcView w b).map (fun g => (b, g)))))
  (_hfast : ∀ i x,
    ∀ s X, X ∈ (FGSA.fastWriteAt (storeAt p c E rho i x) s).getD [] →
      ∃ j < i, IsGateTick p c rho j x s ∧ gatePassedAt p c E rho j ∧
        ∃ B, gateResultAt p c E rho j = some (some B) ∧
          Block.Preceq X B ∧ fastAt p c E rho x s X)
  (_hdeadlines : ∀ i x,
    ∀ K g deadline, (K, g, deadline) ∈ (storeAt p c E rho i x).base.obligations →
      ∀ B, B ≠ .genesis → Block.Preceq B K →
        Gen.AC.Root.ProtectsUntil (storeAt p c E rho i x).base B g deadline)
  (_hheldRows : ∀ i x W, HeldAt p c E rho i x W → ∀ a ∈ chainRows W,
    ∃ (wire : RowWire p.n) (r : Nat), wire.toRow? = some a ∧
      wire.auth = .seat .fg a.signer ∧ ∃ k o t, k < i ∧
        rho.events[k]? = some (.deliver x o t) ∧
        ∀ z, RowSigner p c rho wire z → z ∈ rho.honest →
          HonestRowBefore p c E rho i z r wire ∧ p.actionTime r ≤ t)
  (_hscopeRows : ∀ D, RootBlockInRun p c E rho (eraseFG D) → ∀ a ∈ chainRows D,
    rho.seatOf (.base .fg) a.signer ∈ rho.honest → ∃ j r wire,
      HonestRowAt p c E rho j (rho.seatOf (.base .fg) a.signer) r wire ∧
      wire.toRow? = some a ∧ wire.auth = .seat .fg a.signer)
  (_hfinalHead : ∀ j z r a u, HonestRowAt p c E rho j z r a →
    RowSigner p c rho a z → a.toRow? = some u → ∀ fp,
    u.finality_pair = some fp → ∃ B, HeldAt p c E rho j z B ∧
      fp.height = (heightView p B).h_j ∧ fp.target = (heightView p B).J.root ∧
      TargetQCAt p.E B fp.height (heightView p B).J),
  WCSeed p c E rho w iStar → ∀ i, iStar ≤ i → i < rho.events.length →
    WCInv p c E rho w iStar i → ∀ e, rho.events[i]? = some e →
      WCFiniteFacts p c E rho (i + 1) := by
  intro hvalid _hlinked _hcstar _hnr _hdelta hroots _hsync _hdeltaF _hfaultQ
    _haccountable _hpart _hstore _hcumul _hmono _hactive _hframe _hmeta _hrec _hgeo _hcert
    _hsrc _hlabel _hqc hstrat hnoslash hemitted _htargets hlease hfast hdeadlines
    _hheldRows _hscopeRows _hfinalHead _hs i _hi _hilen _inv _e _he
  let n := i + 1
  refine ⟨fun x _ => cstoreInv_stateBefore E rho n x,
    fun x _ => nestOK_stateBefore E rho n x,
    fun x _ => metaInv_stateBefore E rho n x,
    fun x _ => growthStepFacts_step_receiptOrigins n x,
    fun x _ row hr => ⟨hlease n x row hr⟩,
    fun x _ => hdeadlines n x,
    fun x _ => hfast n x,
    fun x _ s C hc => growthStepFacts_step_savedOrigin hvalid.toScheduleWellFormed n x s C hc,
      ?_, ?_⟩
  · intro x hx W hW X hX hne
    obtain ⟨y, r, wire, ⟨j, hj, hrow⟩, hname⟩ := hstrat n x W hx hW X hX hne
    obtain ⟨K, B, hK, hpair, hentry, hB, hKB, _⟩ := hemitted j y r wire _ hrow hname
    have hXK : X = (derive p.E p.cfg K).T_h := rootScope_eq hroots
      (rootScope_ancestor (rootScope_store hx hW) (certified_preceq hX))
      (rootScope_ancestor (rootScope_source hrow.1 hK) hentry) (congrArg Prod.snd hpair)
    exact ⟨j, y, r, wire, K, B, hj, hrow, hname, hK, hXK ▸ hentry, hB, hKB⟩
  · intro j k x r r' a b u v _ _ ha hb hu hv
    exact hnoslash x ha.1 a b ⟨j, p.actionTime r, ha.2⟩ ⟨k, p.actionTime r', hb.2⟩ u v hu hv

end AvailableChain.FGSA.Run



/-! WC plan §6.6; DC finite service follows the proved joint history. -/

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG KitFG Gen.Pure

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}
    {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}
    {w : HealingWitness} {iStar : Nat}

/-- WC plan §6.6; DC a completed guard writes its result into the local output. -/
private theorem growthStepService_gate_served {i j : Nat} {x : V} {s : Slot} {B : Block}
    (hsch : V2.D.ScheduleWellFormed E rho) (hi : WCInv p c E rho w iStar i)
    (hr : WCResult p c E rho w iStar i j x s B) :
    Block.Preceq B (S_at p c E rho (j + 1) x) := by
  obtain ⟨C, hC, _, hpass⟩ := hi.nonempty j x s hr.afterCut hr.completed
    hr.honest (wcg_gate_enabled_of_result hsch hr.event hr.value) hr.label
  have hrawAt : gateResultAt p c E rho j = some (SA.Root.confirmationFrom p.toParams
      (eraseFG (clockPre p (storeAt p c E rho j x) (SA.gateTime p.toParams s)).fg.F)
      (actView (clockPre p (storeAt p c E rho j x) (SA.gateTime p.toParams s))) s) := by
    rw [gateResultAt_eq_gateResult p c E rho hsch hr.event,
      gateResult_eq_saved p c E rho hsch hr.event, clockPre_fg]
    exact fgsa_gate_saved_result E rho hsch hr.event
      (fgsa_gate_joined_of_enabled E rho (wcg_gate_enabled_of_result hsch hr.event hr.value))
  have hraw := Option.some.inj (hrawAt.symm.trans hr.value)
  obtain ⟨y, r, he, _, G, hG, hguard⟩ := hpass
  have hevent := V2.Event.tick.inj (Option.some.inj (he.symm.trans hr.event))
  have hlabel : r = s := by
    have ht := hevent.2
    change 4 * p.Δ * (r : Int) + 6 * p.Δ = 4 * p.Δ * (s : Int) + 6 * p.Δ at ht
    have hcast : (r : Int) = s := by nlinarith [p.deltaPos]
    exact Int.ofNat_inj.mp hcast
  have hxy := hevent.1
  subst y
  subst r
  have heq : G = B := Option.some.inj (hG.symm.trans hraw)
  subst G
  have hview := fgsa_clockPre_gateView p (storeAt p c E rho j x) s
  have hraw' : (fgsaAC E rho).raw j s x = some B := by
    rw [clockPre_fg] at hraw
    have he := congrArg (fun v => SA.Root.confirmationFrom p.toParams
      (eraseFG (storeAt p c E rho j x).fg.F) v s) hview
    exact he.symm.trans hraw
  have hguard' : ∀ lease ∈ ((fgsaAC E rho).gateView j x s).obligations,
      Block.Compatible (Gen.AC.Lease.target lease) B := by
    intro lease hm
    have he : (clockPre p (storeAt p c E rho j x) (SA.gateTime p.toParams s)).base.obligations =
        ((fgsaAC E rho).gateView j x s).obligations := by
      have he' := congrArg GridCO.State.obligations hview
      exact he'
    rw [← he] at hm
    have hg := List.any_eq_false.mp hguard lease hm
    change Block.compatible lease.1 B = true
    simpa only [Bool.not_eq_true', Bool.not_eq_false] using hg
  have hc := wcg_result_output_compatible hi hr hr.afterCut (Nat.le_of_lt hr.completed)
    hr.honest
  have hadv : Block.Preceq (S_at p c E rho j x) (GridCO.advance (S_at p c E rho j x) B) := by
    rw [GridCO.growth_advance_eq]
    unfold GridCO.growth_advance
    split
    · exact block_preceq_refl _
    · next hn =>
      rcases Bool.or_eq_true_iff.mp hc with h | h
      · exact h
      · exact (hn h).elim
  have hb : Block.Preceq B (GridCO.advance (S_at p c E rho j x) B) := by
    rw [GridCO.growth_advance_eq]
    unfold GridCO.growth_advance
    split
    · assumption
    · exact block_preceq_refl _
  rcases (fgsaAC_gate_write E rho j s x
    (wcg_gate_pre_joined (wcg_gate_enabled_of_result hsch hr.event hr.value))
    hr.event).effects with hskip | hrun
  · obtain ⟨result, hsaved⟩ := hskip.1
    have hfresh := fgsa_gate_fresh E rho hsch hr.event
    change GridCO.savedGenuine (storeAt p c E rho j x).base s = some result at hsaved
    change GridCO.savedGenuine (storeAt p c E rho j x).base s = none at hfresh
    rw [hfresh] at hsaved
    cases hsaved
  · have hw := (hrun.accept B hraw' hguard').1
    change S_at p c E rho (j + 1) x = Gen.AC.normalizeOutput (F_at p c E rho j x)
      (GridCO.advance (S_at p c E rho j x) B) at hw
    have hn : Block.preceq (F_at p c E rho j x)
        (GridCO.advance (S_at p c E rho j x) B) = true :=
      block_preceq_trans (nestOK_stateBefore E rho j x) hadv
    rwa [hw, Gen.AC.normalizeOutput_def, ite_eq_left hn]

variable [Fintype V] {ΔF : Time}

/-- WC plan §6.6; DC finite service needs only history through the requested read. -/
theorem wcg_service4_prefix :
  ∀
  (_hvalid : V2.D.ExecutionValid E rho)
  (_hlinked : V2.D.Linked (fgsaFamilies p c).linked rho)
  (_hcstar : V2.D.CStar (fgsaFamilies p c).fresh rho)
  (_hnr : V2.D.NoRestart rho)
  (_hdelta : E.Δ = p.Δ)
  (_hroots : NamedRootCollisionFree p c E rho)
  (_hsync : Gen.V2.Duty.PartialSynchronyBy E rho (fgsaDelay E.Δ ΔF))
  (_hdeltaF : E.Δ ≤ ΔF)
  (_hfaultQ : Gen.Pure.FaultQ p.n (Gen.V2.Duty.faulty rho).card)
  (_haccountable : FinalitySlashableBound p c E rho)
  (_hpart : ∀ s, w.u + 1 ≤ s → SA.voteTime p.toParams s ≤ rho.horizon →
    (Gen.V2.Duty.faulty rho).card <
      (Gen.V2.Duty.awakeHonest E rho (SA.voteTime p.toParams s)).card)
  (_hstore : RStore p c E rho)
  (_hcumul : RStoreCumul p c E rho)
  (_hmono : RMono p c E rho)
  (_hactive : RActive p c E rho)
  (_hframe : RFrameExactNext p c E rho)
  (_hmeta : RFrameNext p c E rho)
  (_hrec : RRec p c E rho)
  (_hgeo : RGeo p c E rho)
  (_hcert : RCert p c E rho)
  (_hsrc : TSrc p c E rho)
  (_hlabel : LabelBound p c E rho)
  (_hqc : RQCOrigin p c E rho)
  (_hstrat : RStrat p c E rho)
  (_hnoslash : ∀ x ∈ rho.honest, EmittedRowsNoSlash p c E rho x)
  (_hemitted : ∀ j x r a e, HonestRowAt p c E rho j x r a →
    namedEntry a.payload.height_pair = some e →
    ∃ C B, actionSourceFG p c E rho x r = some (some C) ∧
      e = (hOf p.E p.cfg C, (derive p.E p.cfg C).T_h.root) ∧
      FGBlock.Preceq (derive p.E p.cfg C).T_h C ∧
      gateResult p c E rho x (r * p.R) = some (some B) ∧
      Block.Preceq (eraseFG C) B ∧ fastAt p c E rho x (r * p.R) (eraseFG C))
  (_htargets : ∀ i x row, row ∈ (storeAt p c E rho i x).base.obligations →
    Block.Preceq row.1 (storeAt p c E rho i x).base.stableRecord)
  (_hlease : ∀ i x row, row ∈ (storeAt p c E rho i x).base.obligations →
    ∃ j < i, ∃ s B, IsGateTick p c rho j x s ∧ gatePassedAt p c E rho j ∧
      gateResultAt p c E rho j = some (some B) ∧ Block.Preceq row.1 B ∧
      (row.1, row.2.1) ∈
      (let wcView := actView (clockPre p (storeAt p c E rho j x) (SA.gateTime p.toParams s));
        (wcView.blocks.filter (fun b => b != .genesis && Block.preceq b B)).flatMap
          (fun b => (@GridCO.admissionLevels GridCO.slowLeasePolicy
            p.toParams.engine p.n .root wcView s b).map (fun g => (b, g)))) ∧
      row.2.2 = SA.gateTime p.toParams s + SA.lifetime p.toParams ∧
      row.2.2 = SA.releaseTime p.toParams (s + p.k) ∧
      ∀ k w C, j < k → k < i → IsGateTick p c rho k x w →
        let pre := clockPre p (storeAt p c E rho k x) (SA.gateTime p.toParams w)
        GridCO.savedGenuine pre.base w = none →
        SA.Root.confirmationFrom p.toParams (eraseFG pre.fg.F) (actView pre) w = some C →
        (actView pre).obligations.any (fun r => !Block.compatible r.1 C) = false →
        (row.1, row.2.1) ∉ (let wcView := actView pre;
        (wcView.blocks.filter (fun b => b != .genesis && Block.preceq b C)).flatMap
          (fun b => (@GridCO.admissionLevels GridCO.slowLeasePolicy
            p.toParams.engine p.n .root wcView w b).map (fun g => (b, g)))))
  (_hfast : ∀ i x,
    ∀ s X, X ∈ (FGSA.fastWriteAt (storeAt p c E rho i x) s).getD [] →
      ∃ j < i, IsGateTick p c rho j x s ∧ gatePassedAt p c E rho j ∧
        ∃ B, gateResultAt p c E rho j = some (some B) ∧
          Block.Preceq X B ∧ fastAt p c E rho x s X)
  (_hdeadlines : ∀ i x,
    ∀ K g deadline, (K, g, deadline) ∈ (storeAt p c E rho i x).base.obligations →
      ∀ B, B ≠ .genesis → Block.Preceq B K →
        Gen.AC.Root.ProtectsUntil (storeAt p c E rho i x).base B g deadline)
  (_hheldRows : ∀ i x W, HeldAt p c E rho i x W → ∀ a ∈ chainRows W,
    ∃ (wire : RowWire p.n) (r : Nat), wire.toRow? = some a ∧
      wire.auth = .seat .fg a.signer ∧ ∃ k o t, k < i ∧
        rho.events[k]? = some (.deliver x o t) ∧
        ∀ z, RowSigner p c rho wire z → z ∈ rho.honest →
          HonestRowBefore p c E rho i z r wire ∧ p.actionTime r ≤ t)
  (_hscopeRows : ∀ D, RootBlockInRun p c E rho (eraseFG D) → ∀ a ∈ chainRows D,
    rho.seatOf (.base .fg) a.signer ∈ rho.honest → ∃ j r wire,
      HonestRowAt p c E rho j (rho.seatOf (.base .fg) a.signer) r wire ∧
      wire.toRow? = some a ∧ wire.auth = .seat .fg a.signer)
  (_hfinalHead : ∀ j z r a u, HonestRowAt p c E rho j z r a →
    RowSigner p c rho a z → a.toRow? = some u → ∀ fp,
    u.finality_pair = some fp → ∃ B, HeldAt p c E rho j z B ∧
      fp.height = (heightView p B).h_j ∧ fp.target = (heightView p B).J.root ∧
      TargetQCAt p.E B fp.height (heightView p B).J),
  WCSeed p c E rho w iStar → ∀ n, WCInv p c E rho w iStar n →
    ∀ j x s B, WCResult p c E rho w iStar n j x s B →
    SA.gateTime p.toParams s + 4 * p.Δ ≤ rho.horizon →
    ∀ i y, afterTicksIdx rho (SA.gateTime p.toParams s + 4 * p.Δ) ≤ i → i ≤ n →
      y ∈ rho.honest → Block.Preceq B (S_at p c E rho i y) := by
  intro hvalid _hlinked _hcstar _hnr hdelta _hroots _hsync _hdeltaF _hfaultQ
    _haccountable _hpart _hstore _hcumul _hmono _hactive _hframe _hmeta _hrec _hgeo _hcert
    _hsrc _hlabel _hqc _hstrat _hnoslash _hemitted _htargets _hlease _hfast _hdeadlines
    _hheldRows _hscopeRows _hfinalHead _hs n inv j x s B hr hhor i y hcut hin hy
  have hsch := hvalid.toScheduleWellFormed
  have hi := inv
  have hj := hr.afterCut
  have ht := hr.event
  have hlabel := hr.label
  have hnext : SA.gateTime p.toParams (s + 1) = SA.gateTime p.toParams s + 4 * p.Δ := by
    change 4 * p.Δ * ((s + 1 : Nat) : Int) + 6 * p.Δ =
      (4 * p.Δ * (s : Int) + 6 * p.Δ) + 4 * p.Δ
    push_cast
    ring
  have hclock : ((4 * (s + 1) + 6 : Nat) : Time) * p.Δ =
      SA.gateTime p.toParams (s + 1) := by
    change ((4 * (s + 1) + 6 : Nat) : Int) * p.Δ =
      4 * p.Δ * ((s + 1 : Nat) : Int) + 6 * p.Δ
    push_cast
    ring
  obtain ⟨k, hk, _⟩ := fgsa_tick_total E rho hsch hdelta y hy (4 * (s + 1) + 6)
    (by rw [hclock, hnext]; exact hhor)
  rw [hclock] at hk
  have hjk : j < k := V2.D.Engine.eventIndex_lt_of_time_lt hsch ht hk
    (by
      change SA.gateTime p.toParams s < SA.gateTime p.toParams (s + 1)
      rw [hnext]
      exact lt_add_of_pos_right _ (by linarith [p.deltaPos]))
  have hkc : k < afterTicksIdx rho (SA.gateTime p.toParams (s + 1)) := by
    by_contra hn
    have hf := V2.D.Engine.filter_false_of_index_ge hsch
      (cutPred (SA.gateTime p.toParams (s + 1))) (by
        intro e f hle hf
        exact decide_eq_true (hle.trans (of_decide_eq_true hf)))
      (Nat.le_of_not_gt hn) hk
    have hc : cutPred (SA.gateTime p.toParams (s + 1))
        (.tick y (SA.gateTime p.toParams (s + 1)) : V2.Event V (fgsa p c).Object) = true :=
      decide_eq_true le_rfl
    rw [hc] at hf
    cases hf
  have hki : k + 1 ≤ i := (Nat.succ_le_of_lt hkc).trans (hnext ▸ hcut)
  have hklen : k < n := (Nat.lt_succ_self k).trans_le (hki.trans hin)
  have hik : iStar ≤ k := hj.trans (Nat.le_of_lt hjk)
  obtain ⟨C, hC, _, _⟩ :=
    hi.nonempty k y (s + 1) hik hklen hy hk (hlabel.trans (Nat.lt_succ_self s))
  have hrC : WCResult p c E rho w iStar n k y (s + 1) C :=
    ⟨hy, hik, hklen, hlabel.trans (Nat.lt_succ_self s), hk, hC⟩
  have hBC := hi.ordered j k x y s (s + 1) B C hr hrC (Nat.lt_succ_self s)
  have hCout := growthStepService_gate_served hsch hi hrC
  have mono : ∀ l, k + 1 ≤ l → l ≤ n →
      Block.Preceq (S_at p c E rho (k + 1) y) (S_at p c E rho l y) := by
    intro l hl
    induction l, hl using Nat.le_induction with
    | base => intro _; exact block_preceq_refl _
    | succ l hkl ih =>
      intro hln
      exact block_preceq_trans (ih (by omega))
        (hi.transitions l y (hik.trans (by omega)) (by omega) hy)
  exact block_preceq_trans hBC (block_preceq_trans hCout (mono i hki hin))

/-- WC plan §6.6; DC the next covered gate serves the result at every honest reader. -/
theorem wcg_service4 : WCGService4Statement p c E rho ΔF w iStar := by
  intro hvalid hlinked hcstar hnr hdelta hroots hsync hdeltaF
    hfaultQ haccountable hpart hstore hcumul hmono hactive hframe hmeta hrec hgeo hcert
    hsrc hlabel hqc hstrat hnoslash hemitted htargets hlease hfast hdeadlines hheldRows
    hscopeRows hfinalHead hs hinv j x s B hx hj ht hlabel' hB hhor i y hcut hilen hy
  exact wcg_service4_prefix hvalid hlinked hcstar hnr hdelta hroots hsync hdeltaF
    hfaultQ haccountable hpart hstore hcumul hmono hactive hframe hmeta hrec hgeo hcert
    hsrc hlabel hqc hstrat hnoslash hemitted htargets hlease hfast hdeadlines hheldRows
    hscopeRows hfinalHead hs rho.events.length (hinv rho.events.length ⟨hs.within, le_rfl⟩)
    j x s B ⟨hx, hj, (List.getElem?_eq_some_iff.mp ht).1, hlabel', ht, hB⟩
    hhor i y hcut hilen hy

end AvailableChain.FGSA.Run



/-! WC plan §6.5; DC old results cover the current honest HEAD inputs. -/

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG KitFG Gen.Pure

variable {p : Params} {In V : Type} [DecidableEq V] [Fintype V] {c : AppCodec In}
    {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}

omit [DecidableEq V] [Fintype V] in
/-- WC plan §6.5; DC every event strictly after the cut has a later key. -/
private theorem growthStepInputs_time_before_cut (hsch : V2.D.ScheduleWellFormed E rho)
    {i : Nat} {e : V2.Event V (fgsa p c).Object} {t : Time}
    (he : rho.events[i]? = some e) (hi : i < afterTicksIdx rho t) : e.time ≤ t := by
  have hm : e ∈ rho.events.filter (cutPred t) := by
    rw [V2.D.Engine.filter_eq_take hsch (cutPred t) (by
      intro e f hk hf
      exact decide_eq_true (hk.trans (of_decide_eq_true hf)))]
    apply List.mem_of_getElem? (i := i)
    change (rho.events.take (afterTicksIdx rho t))[i]? = some e
    rw [List.getElem?_take_of_lt hi]
    exact he
  have hk := of_decide_eq_true (List.mem_filter.mp hm).2
  rcases Prod.Lex.toLex_le_toLex.mp hk with h | ⟨h, _⟩
  · exact h.le
  · exact h.le

/-- WC plan §6.5; DC retrospective results supply the current batch, including sleepers. -/
theorem wcg_gateHeads (ΔF : Time) (w : HealingWitness) (iStar : Nat) :
  ∀
  (_hvalid : V2.D.ExecutionValid E rho)
  (_hlinked : V2.D.Linked (fgsaFamilies p c).linked rho)
  (_hcstar : V2.D.CStar (fgsaFamilies p c).fresh rho)
  (_hnr : V2.D.NoRestart rho)
  (_hdelta : E.Δ = p.Δ)
  (_hroots : NamedRootCollisionFree p c E rho)
  (_hsync : Gen.V2.Duty.PartialSynchronyBy E rho (fgsaDelay E.Δ ΔF))
  (_hdeltaF : E.Δ ≤ ΔF)
  (_hfaultQ : Gen.Pure.FaultQ p.n (Gen.V2.Duty.faulty rho).card)
  (_haccountable : FinalitySlashableBound p c E rho)
  (_hpart : ∀ s, w.u + 1 ≤ s → SA.voteTime p.toParams s ≤ rho.horizon →
    (Gen.V2.Duty.faulty rho).card <
      (Gen.V2.Duty.awakeHonest E rho (SA.voteTime p.toParams s)).card)
  (_hstore : RStore p c E rho)
  (_hcumul : RStoreCumul p c E rho)
  (_hmono : RMono p c E rho)
  (_hactive : RActive p c E rho)
  (_hframe : RFrameExactNext p c E rho)
  (_hmeta : RFrameNext p c E rho)
  (_hrec : RRec p c E rho)
  (_hgeo : RGeo p c E rho)
  (_hcert : RCert p c E rho)
  (_hsrc : TSrc p c E rho)
  (_hlabel : LabelBound p c E rho)
  (_hqc : RQCOrigin p c E rho)
  (_hstrat : RStrat p c E rho)
  (_hnoslash : ∀ x ∈ rho.honest, EmittedRowsNoSlash p c E rho x)
  (_hemitted : ∀ j x r a e, HonestRowAt p c E rho j x r a →
    namedEntry a.payload.height_pair = some e →
    ∃ C B, actionSourceFG p c E rho x r = some (some C) ∧
      e = (hOf p.E p.cfg C, (derive p.E p.cfg C).T_h.root) ∧
      FGBlock.Preceq (derive p.E p.cfg C).T_h C ∧
      gateResult p c E rho x (r * p.R) = some (some B) ∧
      Block.Preceq (eraseFG C) B ∧ fastAt p c E rho x (r * p.R) (eraseFG C))
  (_htargets : ∀ i x row, row ∈ (storeAt p c E rho i x).base.obligations →
    Block.Preceq row.1 (storeAt p c E rho i x).base.stableRecord)
  (_hlease : ∀ i x row, row ∈ (storeAt p c E rho i x).base.obligations →
    ∃ j < i, ∃ s B, IsGateTick p c rho j x s ∧ gatePassedAt p c E rho j ∧
      gateResultAt p c E rho j = some (some B) ∧ Block.Preceq row.1 B ∧
      (row.1, row.2.1) ∈
      (let wcView := actView (clockPre p (storeAt p c E rho j x) (SA.gateTime p.toParams s));
        (wcView.blocks.filter (fun b => b != .genesis && Block.preceq b B)).flatMap
          (fun b => (@GridCO.admissionLevels GridCO.slowLeasePolicy
            p.toParams.engine p.n .root wcView s b).map (fun g => (b, g)))) ∧
      row.2.2 = SA.gateTime p.toParams s + SA.lifetime p.toParams ∧
      row.2.2 = SA.releaseTime p.toParams (s + p.k) ∧
      ∀ k w C, j < k → k < i → IsGateTick p c rho k x w →
        let pre := clockPre p (storeAt p c E rho k x) (SA.gateTime p.toParams w)
        GridCO.savedGenuine pre.base w = none →
        SA.Root.confirmationFrom p.toParams (eraseFG pre.fg.F) (actView pre) w = some C →
        (actView pre).obligations.any (fun r => !Block.compatible r.1 C) = false →
        (row.1, row.2.1) ∉ (let wcView := actView pre;
        (wcView.blocks.filter (fun b => b != .genesis && Block.preceq b C)).flatMap
          (fun b => (@GridCO.admissionLevels GridCO.slowLeasePolicy
            p.toParams.engine p.n .root wcView w b).map (fun g => (b, g)))))
  (_hfast : ∀ i x,
    ∀ s X, X ∈ (FGSA.fastWriteAt (storeAt p c E rho i x) s).getD [] →
      ∃ j < i, IsGateTick p c rho j x s ∧ gatePassedAt p c E rho j ∧
        ∃ B, gateResultAt p c E rho j = some (some B) ∧
          Block.Preceq X B ∧ fastAt p c E rho x s X)
  (_hdeadlines : ∀ i x,
    ∀ K g deadline, (K, g, deadline) ∈ (storeAt p c E rho i x).base.obligations →
      ∀ B, B ≠ .genesis → Block.Preceq B K →
        Gen.AC.Root.ProtectsUntil (storeAt p c E rho i x).base B g deadline)
  (_hheldRows : ∀ i x W, HeldAt p c E rho i x W → ∀ a ∈ chainRows W,
    ∃ (wire : RowWire p.n) (r : Nat), wire.toRow? = some a ∧
      wire.auth = .seat .fg a.signer ∧ ∃ k o t, k < i ∧
        rho.events[k]? = some (.deliver x o t) ∧
        ∀ z, RowSigner p c rho wire z → z ∈ rho.honest →
          HonestRowBefore p c E rho i z r wire ∧ p.actionTime r ≤ t)
  (_hscopeRows : ∀ D, RootBlockInRun p c E rho (eraseFG D) → ∀ a ∈ chainRows D,
    rho.seatOf (.base .fg) a.signer ∈ rho.honest → ∃ j r wire,
      HonestRowAt p c E rho j (rho.seatOf (.base .fg) a.signer) r wire ∧
      wire.toRow? = some a ∧ wire.auth = .seat .fg a.signer)
  (_hfinalHead : ∀ j z r a u, HonestRowAt p c E rho j z r a →
    RowSigner p c rho a z → a.toRow? = some u → ∀ fp,
    u.finality_pair = some fp → ∃ B, HeldAt p c E rho j z B ∧
      fp.height = (heightView p B).h_j ∧ fp.target = (heightView p B).J.root ∧
      TargetQCAt p.E B fp.height (heightView p B).J),
  WCSeed p c E rho w iStar → ∀ i x s, iStar ≤ i → i < rho.events.length →
    WCInv p c E rho w iStar i → IsGateTick p c rho i x s → w.u < s →
    ∀ k y, y ∈ rho.honest → rho.events[k]? = some (.tick y (SA.voteTime p.toParams s)) →
      Block.Preceq w.QStar (headAtIdx p c E rho k s) ∧
      ∀ j z r B, WCResult p c E rho w iStar i j z r B → r < s →
        Block.Preceq B (headAtIdx p c E rho k s) := by
  intro hvalid _hlinked _hcstar _hnr hdelta _hroots _hsync _hdeltaF _hfaultQ
    _haccountable _hpart _hstore _hcumul _hmono _hactive _hframe _hmeta _hrec _hgeo _hcert
    _hsrc _hlabel _hqc _hstrat _hnoslash _hemitted _htargets _hlease _hfast _hdeadlines
    _hheldRows _hscopeRows _hfinalHead hs i x s _hi _hilen inv ht hlabel k y hy hk
  have hsch := hvalid.toScheduleWellFormed
  by_cases hfirst : s = w.u + 1
  · subst s
    obtain ⟨l, _, hhead⟩ := hs.nextHeads y hy
    have he : l = k := fgsa_tick_unique E rho hsch hhead.event hk
    refine ⟨he ▸ hhead.covers, ?_⟩
    intro j z r B hr hlt
    have hh := hr.label
    exact ((Nat.not_lt_of_ge (Nat.succ_le_of_lt hh)) hlt).elim
  have hsuc : s - 1 + 1 = s := Nat.sub_add_cancel
    (Nat.succ_le_of_lt ((Nat.zero_le w.u).trans_lt hlabel))
  have hprev : w.u < s - 1 := by
    simp only [Slot] at hlabel hfirst ⊢
    omega
  have hclock : ((4 * (s - 1) + 6 : Nat) : Time) * p.Δ =
      SA.gateTime p.toParams (s - 1) := by
    change ((4 * (s - 1) + 6 : Nat) : Int) * p.Δ =
      4 * p.Δ * ((s - 1 : Nat) : Int) + 6 * p.Δ
    push_cast
    ring
  have hlt : SA.gateTime p.toParams (s - 1) < SA.gateTime p.toParams s := by
    have hh : ((s - 1 : Nat) : Int) < s := by
      exact_mod_cast Nat.sub_lt ((Nat.zero_le w.u).trans_lt hlabel) (by decide : 0 < 1)
    change 4 * p.Δ * ((s - 1 : Nat) : Int) + 6 * p.Δ <
      4 * p.Δ * (s : Int) + 6 * p.Δ
    nlinarith [p.deltaPos]
  have hhor : SA.gateTime p.toParams (s - 1) ≤ rho.horizon :=
    hlt.le.trans (hvalid.in_horizon _ (List.mem_of_getElem? ht)).2
  obtain ⟨l, hl, _⟩ := fgsa_tick_total E rho hsch hdelta y hy (4 * (s - 1) + 6)
    (hclock ▸ hhor)
  rw [hclock] at hl
  have hli : l < i := V2.D.Engine.eventIndex_lt_of_time_lt hsch hl ht hlt
  have hafter : iStar ≤ l := by
    by_contra hn
    have hh := growthStepInputs_time_before_cut hsch hl (hs.cut ▸ (Nat.lt_of_not_ge hn))
    change SA.gateTime p.toParams (s - 1) ≤ SA.gateTime p.toParams w.u at hh
    have hp : (w.u : Int) < (s - 1 : Nat) := Int.ofNat_lt.mpr hprev
    change 4 * p.Δ * ((s - 1 : Nat) : Int) + 6 * p.Δ ≤
      4 * p.Δ * (w.u : Int) + 6 * p.Δ at hh
    nlinarith [p.deltaPos]
  obtain ⟨C, hC, hQC, _⟩ := inv.nonempty l y (s - 1) hafter hli hy hl hprev
  have hresult : WCResult p c E rho w iStar i l y (s - 1) C :=
    ⟨hy, hafter, hli, hprev, hl, hC⟩
  have covers (j : Nat) (z : V) (B : Block)
      (hr : WCResult p c E rho w iStar i j z (s - 1) B) :
      Block.Preceq B (headAtIdx p c E rho k s) := by
    obtain ⟨q, _, hhead⟩ := inv.retrospective j z (s - 1) B hr y hy
    rw [hsuc] at hhead
    exact (fgsa_tick_unique E rho hsch hhead.event hk) ▸ hhead.covers
  have hCH := covers l y C hresult
  refine ⟨block_preceq_trans hQC hCH, ?_⟩
  intro j z r B hr hrs
  rcases lt_or_eq_of_le (Nat.le_sub_one_of_lt hrs) with hlt | heq
  · exact block_preceq_trans (inv.ordered j l z y r (s - 1) B C hr hresult hlt) hCH
  · subst r
    exact covers j z B hr

/-- WC plan §6.5; DC the gate anchor comes from the seed or a strictly earlier result. -/
theorem wcg_gateFinalOrigin (hcausal : WCFinalityTargetEarlierStatement p c E rho) (ΔF : Time)
  (w : HealingWitness) (iStar : Nat) :
  ∀
  (_hvalid : V2.D.ExecutionValid E rho)
  (_hlinked : V2.D.Linked (fgsaFamilies p c).linked rho)
  (_hcstar : V2.D.CStar (fgsaFamilies p c).fresh rho)
  (_hnr : V2.D.NoRestart rho)
  (_hdelta : E.Δ = p.Δ)
  (_hroots : NamedRootCollisionFree p c E rho)
  (_hsync : Gen.V2.Duty.PartialSynchronyBy E rho (fgsaDelay E.Δ ΔF))
  (_hdeltaF : E.Δ ≤ ΔF)
  (_hfaultQ : Gen.Pure.FaultQ p.n (Gen.V2.Duty.faulty rho).card)
  (_haccountable : FinalitySlashableBound p c E rho)
  (_hpart : ∀ s, w.u + 1 ≤ s → SA.voteTime p.toParams s ≤ rho.horizon →
    (Gen.V2.Duty.faulty rho).card <
      (Gen.V2.Duty.awakeHonest E rho (SA.voteTime p.toParams s)).card)
  (_hstore : RStore p c E rho)
  (_hcumul : RStoreCumul p c E rho)
  (_hmono : RMono p c E rho)
  (_hactive : RActive p c E rho)
  (_hframe : RFrameExactNext p c E rho)
  (_hmeta : RFrameNext p c E rho)
  (_hrec : RRec p c E rho)
  (_hgeo : RGeo p c E rho)
  (_hcert : RCert p c E rho)
  (_hsrc : TSrc p c E rho)
  (_hlabel : LabelBound p c E rho)
  (_hqc : RQCOrigin p c E rho)
  (_hstrat : RStrat p c E rho)
  (_hnoslash : ∀ x ∈ rho.honest, EmittedRowsNoSlash p c E rho x)
  (_hemitted : ∀ j x r a e, HonestRowAt p c E rho j x r a →
    namedEntry a.payload.height_pair = some e →
    ∃ C B, actionSourceFG p c E rho x r = some (some C) ∧
      e = (hOf p.E p.cfg C, (derive p.E p.cfg C).T_h.root) ∧
      FGBlock.Preceq (derive p.E p.cfg C).T_h C ∧
      gateResult p c E rho x (r * p.R) = some (some B) ∧
      Block.Preceq (eraseFG C) B ∧ fastAt p c E rho x (r * p.R) (eraseFG C))
  (_htargets : ∀ i x row, row ∈ (storeAt p c E rho i x).base.obligations →
    Block.Preceq row.1 (storeAt p c E rho i x).base.stableRecord)
  (_hlease : ∀ i x row, row ∈ (storeAt p c E rho i x).base.obligations →
    ∃ j < i, ∃ s B, IsGateTick p c rho j x s ∧ gatePassedAt p c E rho j ∧
      gateResultAt p c E rho j = some (some B) ∧ Block.Preceq row.1 B ∧
      (row.1, row.2.1) ∈
      (let wcView := actView (clockPre p (storeAt p c E rho j x) (SA.gateTime p.toParams s));
        (wcView.blocks.filter (fun b => b != .genesis && Block.preceq b B)).flatMap
          (fun b => (@GridCO.admissionLevels GridCO.slowLeasePolicy
            p.toParams.engine p.n .root wcView s b).map (fun g => (b, g)))) ∧
      row.2.2 = SA.gateTime p.toParams s + SA.lifetime p.toParams ∧
      row.2.2 = SA.releaseTime p.toParams (s + p.k) ∧
      ∀ k w C, j < k → k < i → IsGateTick p c rho k x w →
        let pre := clockPre p (storeAt p c E rho k x) (SA.gateTime p.toParams w)
        GridCO.savedGenuine pre.base w = none →
        SA.Root.confirmationFrom p.toParams (eraseFG pre.fg.F) (actView pre) w = some C →
        (actView pre).obligations.any (fun r => !Block.compatible r.1 C) = false →
        (row.1, row.2.1) ∉ (let wcView := actView pre;
        (wcView.blocks.filter (fun b => b != .genesis && Block.preceq b C)).flatMap
          (fun b => (@GridCO.admissionLevels GridCO.slowLeasePolicy
            p.toParams.engine p.n .root wcView w b).map (fun g => (b, g)))))
  (_hfast : ∀ i x,
    ∀ s X, X ∈ (FGSA.fastWriteAt (storeAt p c E rho i x) s).getD [] →
      ∃ j < i, IsGateTick p c rho j x s ∧ gatePassedAt p c E rho j ∧
        ∃ B, gateResultAt p c E rho j = some (some B) ∧
          Block.Preceq X B ∧ fastAt p c E rho x s X)
  (_hdeadlines : ∀ i x,
    ∀ K g deadline, (K, g, deadline) ∈ (storeAt p c E rho i x).base.obligations →
      ∀ B, B ≠ .genesis → Block.Preceq B K →
        Gen.AC.Root.ProtectsUntil (storeAt p c E rho i x).base B g deadline)
  (_hheldRows : ∀ i x W, HeldAt p c E rho i x W → ∀ a ∈ chainRows W,
    ∃ (wire : RowWire p.n) (r : Nat), wire.toRow? = some a ∧
      wire.auth = .seat .fg a.signer ∧ ∃ k o t, k < i ∧
        rho.events[k]? = some (.deliver x o t) ∧
        ∀ z, RowSigner p c rho wire z → z ∈ rho.honest →
          HonestRowBefore p c E rho i z r wire ∧ p.actionTime r ≤ t)
  (_hscopeRows : ∀ D, RootBlockInRun p c E rho (eraseFG D) → ∀ a ∈ chainRows D,
    rho.seatOf (.base .fg) a.signer ∈ rho.honest → ∃ j r wire,
      HonestRowAt p c E rho j (rho.seatOf (.base .fg) a.signer) r wire ∧
      wire.toRow? = some a ∧ wire.auth = .seat .fg a.signer)
  (_hfinalHead : ∀ j z r a u, HonestRowAt p c E rho j z r a →
    RowSigner p c rho a z → a.toRow? = some u → ∀ fp,
    u.finality_pair = some fp → ∃ B, HeldAt p c E rho j z B ∧
      fp.height = (heightView p B).h_j ∧ fp.target = (heightView p B).J.root ∧
      TargetQCAt p.E B fp.height (heightView p B).J),
  WCSeed p c E rho w iStar → ∀ i x s, iStar ≤ i → i < rho.events.length →
    WCInv p c E rho w iStar i → IsGateTick p c rho i x s → w.u < s →
      Block.Preceq (F_at p c E rho i x) w.QStar ∨
      ∃ j y r B, WCResult p c E rho w iStar i j y r B ∧ r < s ∧
        Block.Preceq (F_at p c E rho i x) B := by
  intro hvalid hlinked _hcstar _hnr _hdelta hroots _hsync _hdeltaF hfaultQ
    _haccountable _hpart _hstore _hcumul _hmono _hactive _hframe _hmeta _hrec _hgeo _hcert
    _hsrc _hlabel hqc _hstrat _hnoslash hemitted _htargets _hlease _hfast _hdeadlines
    hheldRows _hscopeRows hfinalHead hs i x s hi _hilen inv ht _hlabel
  have hx := hvalid.honest_only _ (List.mem_of_getElem? ht)
  obtain ⟨D, hD, hF⟩ := ((inv.finite i hi le_rfl).store x hx).fg.Fcar
  by_cases hlo : (finalityView p D).h_F ≤ w.M
  · exact Or.inl (block_preceq_trans
      (inv.lowFinalized i x D _ _ hi le_rfl ⟨hx, hD⟩ hF rfl hlo) hs.sourcePrefix)
  have hpos : 0 < (finalityView p D).h_F := by simp only [Height] at hlo ⊢; omega
  have hhigh : w.M + 1 ≤ (finalityView p D).h_F := by simp only [Height] at hlo ⊢; omega
  obtain ⟨jf, z, rf, af, uf, H, jt, v, rt, aT, ut, K, B, hjf, haf, _, _, _, _,
      _, _, _, _, hjt, haT, hdecode, _, htarget, hK, hXK, _hgate, _hKB, hgap⟩ :=
    (hcausal hvalid hlinked hfaultQ hroots hheldRows hfinalHead hqc
      hemitted i x D _ _ ⟨hx, hD⟩ hpos hF rfl).finalityRow
  have hfields : aT.payload.height_pair = ut.height_pair := by
    rcases aT with ⟨auth, body⟩
    cases auth with
    | none => cases hdecode
    | proposer s => cases hdecode
    | seat label k =>
      cases label with
      | head s => cases hdecode
      | fg => exact congrArg Row.height_pair (Option.some.inj hdecode)
  have hname : namedEntry aT.payload.height_pair =
      some ((finalityView p D).h_F, (storeAt p c E rho i x).fg.F.root) := by
    rw [hfields, htarget]
    rfl
  by_cases hbefore : jt < iStar
  · obtain ⟨K', B', hK', _, _, _, _, hbelow⟩ :=
      hs.highSources jt v rt aT _ hbefore haT hname hhigh
    have heq : K = K' := Option.some.inj (Option.some.inj (hK.symm.trans hK'))
    exact Or.inl (block_preceq_trans (eraseFG_preceq hXK) (heq ▸ hbelow))
  have hafter : iStar ≤ jt := Nat.le_of_not_gt hbefore
  obtain ⟨C, hC, hKC⟩ := inv.suffixSources jt v rt K hafter (hjt.trans hjf) haT.1 haT.2.1 hK
  have htime : p.actionTime rf ≤ SA.gateTime p.toParams s := by
    obtain ⟨hfl, hfe⟩ := List.getElem?_eq_some_iff.mp haf.2.1
    obtain ⟨hil, hie⟩ := List.getElem?_eq_some_iff.mp ht
    have hk := (List.pairwise_iff_getElem.mp hvalid.sorted) jf i hfl hil hjf
    rw [hfe, hie] at hk
    exact V2.D.Engine.time_le_of_key_le _ _ hk
  have hlt : rt * p.R < s := by
    have hh : SA.gateTime p.toParams (rt * p.R) + 4 * p.Δ < SA.gateTime p.toParams s :=
      hgap.trans_le htime
    change 4 * p.Δ * (rt * p.R : Nat) + 6 * p.Δ + 4 * p.Δ <
      4 * p.Δ * (s : Int) + 6 * p.Δ at hh
    have hcast : ((rt * p.R : Nat) : Int) < s := by nlinarith [p.deltaPos]
    exact Int.ofNat_lt.mp hcast
  exact Or.inr ⟨jt, v, rt * p.R, C, hC, hlt, block_preceq_trans (eraseFG_preceq hXK) hKC⟩

end AvailableChain.FGSA.Run



/-! WC plan §6.5; DC the honest batch retains its original receipt deadlines. -/

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG KitFG Gen.Pure

variable {p : Params} {In V : Type} {c : AppCodec In} [DecidableEq V]
    {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)} {ΔF : Time}

/-- WC plan §6.5; DC cumulative stamps retain their first receipt. -/
private theorem growthStepGateBatch_stamp_find_kept {α : Type} [BEq α] [LawfulBEq α]
    {xs ys : List (α × Time)} (hp : xs <+: ys) (a : α)
    (hm : a ∈ xs.map Prod.fst) :
    ys.find? (fun row => row.1 == a) = xs.find? (fun row => row.1 == a) := by
  obtain ⟨tail, he⟩ := hp
  rw [← he, List.find?_append]
  cases hf : xs.find? (fun row => row.1 == a) with
  | none =>
    obtain ⟨⟨b, t⟩, ht, hb⟩ := List.mem_map.mp hm
    dsimp only at hb
    subst b
    have hn := List.find?_eq_none.mp hf (a, t) ht
    simp only [beq_self_eq_true] at hn
    exact (hn trivial).elim
  | some row => rfl


/-- WC plan §6.5; DC gate inputs retain the original stored stamps. -/
private theorem growthStepGateBatch_gate_stamps (hcumul : RStoreCumul p c E rho) (hn :
  V2.D.NoRestart rho)
    {j i : Nat} {x : V} {s : Slot} (hx : x ∈ rho.honest)
    (hji : j ≤ i) (hi : i ≤ rho.events.length)
    (o : GridCO.Wire p.n .root) (B : Block)
    (ho : o ∈ (storeAt p c E rho j x).base.votes)
    (hB : B ∈ (storeAt p c E rho j x).base.blocks) :
    let v := actView (clockPre p (storeAt p c E rho i x) (SA.gateTime p.toParams s))
    o ∈ (storeAt p c E rho i x).base.votes ∧
      GridCO.stampVote v o = GridCO.stampVote (storeAt p c E rho j x).base o ∧
      GridCO.stampBlock v B = GridCO.stampBlock (storeAt p c E rho j x).base B := by
  intro v
  have hc := hcumul hn j i x hx hji hi
  have hv : o ∈ (storeAt p c E rho j x).base.voteStamp.map Prod.fst := by
    change o ∈ (V2.D.Run.stateBefore E rho j x).st.base.voteStamp.map Prod.fst
    rw [fgsa_vote_stamp_keys E rho j x]
    exact ho
  have hb : B ∈ (storeAt p c E rho j x).base.blockStamp.map Prod.fst := by
    change B ∈ (V2.D.Run.stateBefore E rho j x).st.base.blockStamp.map Prod.fst
    rw [(storeBundle_stateBefore E rho j x).«meta».stampKeys]
    exact hB
  have hev := growthStepGateBatch_stamp_find_kept hc.2.2.2 o hv
  have heb := growthStepGateBatch_stamp_find_kept hc.2.2.1 B hb
  refine ⟨?_, ?_, ?_⟩
  · change o ∈ (V2.D.Run.stateBefore E rho i x).st.base.votes
    rw [← fgsa_vote_stamp_keys E rho i x]
    obtain ⟨row, hr, he⟩ := List.mem_map.mp hv
    exact List.mem_map.mpr ⟨row, hc.2.2.2.subset hr, he⟩
  · change (((clockPre p _ _).base.voteStamp.find? _).map Prod.snd).getD _ = _
    rw [(clockPre_stamps p _ _).2, hev]
    rw [GridCO.growth_stampVote_eq]
    unfold GridCO.growth_stampVote
    cases he : (storeAt p c E rho j x).base.voteStamp.find? (fun row => row.1 == o) with
    | none =>
      obtain ⟨row, hr, ho⟩ := List.mem_map.mp hv
      have hn := List.find?_eq_none.mp he row hr
      rw [ho, beq_self_eq_true] at hn
      contradiction
    | some row => rfl
  · change (((clockPre p _ _).base.blockStamp.find? _).map Prod.snd).getD _ = _
    rw [(clockPre_stamps p _ _).1, heb]
    rw [GridCO.growth_stampBlock_eq]
    unfold GridCO.growth_stampBlock
    cases he : (storeAt p c E rho j x).base.blockStamp.find? (fun row => row.1 == B) with
    | none =>
      obtain ⟨row, hr, ho⟩ := List.mem_map.mp hb
      have hn := List.find?_eq_none.mp he row hr
      rw [ho, beq_self_eq_true] at hn
      contradiction
    | some row => rfl
/-- WC plan §6.5; DC a HEAD path has actual earlier receipt origins. -/
private theorem growthStepGateBatch_gate_source_path (hsch : V2.D.ScheduleWellFormed E rho)
    {k : Nat} {y : V} {s : Slot} {K : Block}
    (hk : rho.events[k]? = some (.tick y (SA.voteTime p.toParams s)))
    (hK : K ∈ (storeAt p c E rho k y).base.blocks) :
    ∀ b, Block.Preceq b K → b ≠ .genesis →
      ∃ l < k, ∃ t o, blockOf? p o = some b ∧
        V2.D.Run.acceptsAt E rho l y o t ∧ 0 ≤ t ∧ t < SA.voteTime p.toParams s := by
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
  · refine ⟨l, hl, t, o, ho, ha, ?_, ?_⟩
    · obtain ⟨parent, hd, _⟩ := ha.1
      exact (hsch.in_horizon _ (List.mem_of_getElem? hd)).1
    · obtain ⟨parent, hd, _⟩ := ha.1
      obtain ⟨hll, hle⟩ := List.getElem?_eq_some_iff.mp hd
      obtain ⟨hkl, hke⟩ := List.getElem?_eq_some_iff.mp hk
      have hkey := (List.pairwise_iff_getElem.mp hsch.sorted) l k hll hkl hl
      rw [hle, hke] at hkey
      change toLex (t, (2 : Nat)) ≤ toLex (SA.voteTime p.toParams s, 1) at hkey
      rcases Prod.Lex.toLex_le_toLex.mp hkey with hlt | ⟨_, hphase⟩
      · exact hlt
      · omega

/-- WC plan §6.5; DC path coverage uses each acceptance time and the inherited GST. -/
private theorem growthStepGateBatch_gate_path_coverage (hE : V2.D.ExecutionValid E rho)
    (_hn : V2.D.NoRestart rho) (hDelta : E.Δ = p.Δ)
    (hsync : Gen.V2.Duty.PartialSynchronyBy E rho (fgsaDelay E.Δ ΔF))
    {i k : Nat} {x y : V} {s : Slot} {K : Block}
    (hGST : E.t_GST ≤ SA.voteTime p.toParams s)
    (ht : IsGateTick p c rho i x s) (hcut : SA.gateTime p.toParams s ≤ rho.horizon)
    (hy : y ∈ rho.honest)
    (hk : rho.events[k]? = some (.tick y (SA.voteTime p.toParams s)))
    (hK : K ∈ (storeAt p c E rho k y).base.blocks)
    (hF : ∀ j, j ≤ i → Block.Preceq (F_at p c E rho j x) K) :
    ∃ required paths,
      ReceiptCoveragePremises E rho (fun t => max t E.t_GST + p.Δ) rho.horizon
        (SA.earlyTime p.toParams s) 0 x K required paths ∧
      paths K (SA.earlyTime p.toParams s) := by
  let required := fun o t => ∃ l < k, V2.D.Run.acceptsAt E rho l y o t ∧
    ∃ b, blockOf? p o = some b ∧ Block.Preceq b K
  let paths := fun B d => B = K ∧ d = SA.earlyTime p.toParams s
  have hsch := hE.toScheduleWellFormed
  have hD : SA.earlyTime p.toParams s ≤ SA.gateTime p.toParams s := by
    change 4 * p.Δ * (s : Int) + 2 * p.Δ ≤ 4 * p.Δ * (s : Int) + 6 * p.Δ
    have hd : (0 : Int) < p.Δ := p.deltaPos
    linarith
  have hidx : V2.D.Run.idxBefore rho (SA.earlyTime p.toParams s) ≤ i := by
    by_contra hh
    have hlt := (Gen.V2.Duty.index_lt_idxBefore_iff hsch ht (SA.earlyTime p.toParams s)).mp
      (Nat.lt_of_not_ge hh)
    exact (not_lt.mpr hD) hlt
  have htime : ∀ o t, required o t → 0 ≤ t ∧ t < SA.voteTime p.toParams s := by
    rintro o t ⟨l, hl, ha, _⟩
    obtain ⟨parent, hd, _⟩ := ha.1
    refine ⟨(hsch.in_horizon _ (List.mem_of_getElem? hd)).1, ?_⟩
    obtain ⟨hll, hle⟩ := List.getElem?_eq_some_iff.mp hd
    obtain ⟨hkl, hke⟩ := List.getElem?_eq_some_iff.mp hk
    have hkey := (List.pairwise_iff_getElem.mp hsch.sorted) l k hll hkl hl
    rw [hle, hke] at hkey
    change toLex (t, (2 : Nat)) ≤ toLex (SA.voteTime p.toParams s, 1) at hkey
    rcases Prod.Lex.toLex_le_toLex.mp hkey with hh | ⟨_, hh⟩
    · exact hh
    · omega
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
    have hh : blockOf? p o = none := by
      change (match (toWire p o).decode with | some (.block _ N) => some N.erase | _ => none) = _
      rw [hv]
    rw [hh] at hb
    contradiction
  · intro j _ hj
    exact block_compatible_of_common (block_preceq_refl K) (hF j (hj.trans hidx))
  · refine ⟨fun _ _ hab => add_le_add (max_le_max hab le_rfl) le_rfl,
      hD.trans hcut, le_rfl, Nat.zero_le _, ?_, ?_, ?_⟩
    · intro o t hr
      have htt := htime o t hr
      refine ⟨Nat.zero_le _, htt.1,
        (le_max_left _ _).trans_lt (lt_add_of_pos_right _ p.deltaPos), ?_⟩
      have hv := htt.2
      change t < 4 * p.Δ * (s : Int) + p.Δ at hv
      have hm : max t E.t_GST ≤ SA.voteTime p.toParams s := max_le hv.le hGST
      change max t E.t_GST + p.Δ ≤ 4 * p.Δ * (s : Int) + 2 * p.Δ
      change max t E.t_GST ≤ 4 * p.Δ * (s : Int) + p.Δ at hm
      linarith
    · rintro B d ⟨hBK, hdD⟩
      subst B
      subst d
      refine ⟨block_preceq_refl K, le_rfl, ?_⟩
      intro b hb hne
      obtain ⟨l, hl, t, o, ho, ha, _, ht'⟩ := growthStepGateBatch_gate_source_path hsch hk hK b
        hb hne
      have hdecode : ∃ r N, N.erase = b ∧ (toWire p o).decode = some (.block r N) := by
        change (match (toWire p o).decode with
          | some (.block _ N) => some N.erase | _ => none) = _ at ho
        cases he : (toWire p o).decode with
        | none => rw [he] at ho; contradiction
        | some m =>
          cases m <;> simp only [he, reduceCtorEq, Option.some.injEq] at ho
          exact ⟨_, _, ho, rfl⟩
      obtain ⟨r, N, heN, hdec⟩ := hdecode
      refine ⟨o, t, r, N, heN, ⟨l, hl, ha, b, ho, hb⟩, hdec, ?_⟩
      change t < 4 * p.Δ * (s : Int) + p.Δ at ht'
      have hm : max t E.t_GST ≤ SA.voteTime p.toParams s := max_le ht'.le hGST
      change max t E.t_GST + p.Δ ≤ 4 * p.Δ * (s : Int) + 2 * p.Δ
      change max t E.t_GST ≤ 4 * p.Δ * (s : Int) + p.Δ at hm
      linarith
    · intro o t r N hr hdec
      obtain ⟨l, hl, ha, b', hb', hBK⟩ := hr
      have hb : blockOf? p o = some N.erase := by
        change (match (toWire p o).decode with | some (.block _ N) => some N.erase | _ => none) = _
        rw [hdec]
      have heq := Option.some.inj (hb'.symm.trans hb)
      subst b'
      exact ⟨K, SA.earlyTime p.toParams s, ⟨rfl, rfl⟩, hBK⟩


/-- WC plan §6.5; DC receipts before a tick have strictly earlier stamps. -/
private theorem growthStepGateBatch_gate_block_stamp_lt (hsch : V2.D.ScheduleWellFormed E rho)
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

/-- WC plan §6.5; DC an awake honest HEAD and its path arrive before the early tick. -/
private theorem growthStepGateBatch_gate_active_heads
    (hvalid : V2.D.ExecutionValid E rho) (hnr : V2.D.NoRestart rho) (hdelta : E.Δ = p.Δ)
    (hcstar : V2.D.CStar (fgsaFamilies p c).fresh rho)
    (hroots : NamedRootCollisionFree p c E rho)
    (hsync : Gen.V2.Duty.PartialSynchronyBy E rho (fgsaDelay E.Δ ΔF))
    (hcumul : RStoreCumul p c E rho) {i : Nat} {x : V} {s : Slot}
    (ht : IsGateTick p c rho i x s) (hGST : E.t_GST ≤ SA.voteTime p.toParams s)
    (hfinal : ∀ k y, rho.events[k]? = some (.tick y (SA.voteTime p.toParams s)) →
      ∀ j, j ≤ i → Block.Preceq (F_at p c E rho j x) (headAtIdx p c E rho k s))
    (B : Block)
    (hB : ∀ k y, rho.events[k]? = some (.tick y (SA.voteTime p.toParams s)) →
      Block.Preceq B (headAtIdx p c E rho k s)) :
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
        Block.Preceq (eraseFG (clockPre p (storeAt p c E rho i x)
          (SA.gateTime p.toParams s)).fg.F) K ∧ Block.Preceq B K := by
  intro q hy hawake
  let y := rho.seatOf (.base (.head s)) q
  have hsch := hvalid.toScheduleWellFormed
  have hd : (0 : Int) < p.Δ := p.deltaPos
  have hx : x ∈ rho.honest := hsch.honest_only _ (List.mem_of_getElem? ht)
  have hil := Nat.le_of_lt (List.getElem?_eq_some_iff.mp ht).1
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
  let K := headAtIdx p c E rho k s
  have hKeq : K = headVote p ((fgsa p c).clock (V2.D.Run.stateBefore E rho k y)
      (SA.voteTime p.toParams s)).st s := by
    change headAtIdx p c E rho k s = _
    rw [growth_headAtIdx_eq]
    unfold growth_headAtIdx
    rw [hk]
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
  obtain ⟨required, paths, hcov, hp⟩ :=
    growthStepGateBatch_gate_path_coverage hvalid hnr hdelta hsync hGST ht hcut hy hk hKsource
      hprefix
  have hidx : V2.D.Run.idxBefore rho (SA.earlyTime p.toParams s) ≤ i := by
    by_contra hn
    exact (not_lt.mpr hearly.le)
      ((Gen.V2.Duty.index_lt_idxBefore_iff hsch ht _).mp (Nat.lt_of_not_ge hn))
  have hFearly : Block.Preceq (eraseFG (V2.D.Run.stateBeforeTime E rho
      (SA.earlyTime p.toParams s) x).st.fg.F) K := by
    rw [← Gen.V2.Duty.stateBefore_idxBefore E rho _ hsch]
    exact hprefix _ hidx
  have hpath := fgsa_active_path_of_coverage (hroots := hroots)
    E rho hvalid hnr hdelta
    (fun t => max t E.t_GST + p.Δ) rho.horizon (SA.earlyTime p.toParams s) 0 x K
    required paths hx hcov hp hFearly
  have hKearly : K ∈ (storeAt p c E rho j x).base.blocks := by
    have hm := (actView_blocks _ K).mp (hpath K (block_preceq_refl K))
    rw [← hjread] at hm
    exact hm.1
  have hwindow : (V2.D.Run.stateBeforeTime E rho (SA.earlyTime p.toParams s) x).st.slot p ≤
      s + 1 := by
    rw [← hjread]
    have hn := stateBefore_now_le_event_retained (fgsaClock p c)
      (fgsa_hrestore_now_retained p c)
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
  have htrans := growthStepGateBatch_gate_stamps hcumul hnr (s := s) hx
    (Nat.le_of_lt hji) hil _ K hr.1 hKearly
  have hKg : K ∈ (actView (clockPre p (storeAt p c E rho i x)
      (SA.gateTime p.toParams s))).blocks := by
    apply (actView_blocks _ K).mpr
    rw [(clockPre_fields p _ _).2.1, clockPre_fg]
    exact ⟨(hcumul hnr j i x hx (Nat.le_of_lt hji) hil).2.1.subset hKearly,
      block_compatible_of_common (block_preceq_refl K) (hprefix i le_rfl)⟩
  have hslot : K.slot ≤ s := by
    have hm := (fgsa_stateBefore_bounds E rho hsch k y).1 K hKsource
    have hn := stateBefore_now_le_event_retained (fgsaClock p c)
      (fgsa_hrestore_now_retained p c)
      E rho hsch hk y
    rw [fgsa_clock_now p c (V2.D.Run.stateBefore E rho k y)] at hn
    exact hm.trans ((Internal.slotOf_mono (p := p) hn).trans_eq
      (slotOf_offset p s p.Δ hd.le (by omega)))
  have hpos : 0 < SA.earlyTime p.toParams s := by
    change 0 < 4 * p.Δ * ((s : Nat) : Int) + 2 * p.Δ
    positivity
  refine ⟨K, SA.voteTime p.toParams s, hy, hem, htrans.1, hKg, hslot, ?_, ?_, ?_, hB k y hk⟩
  · rw [htrans.2.1]
    exact hr.2
  · rw [htrans.2.2]
    exact growthStepGateBatch_gate_block_stamp_lt hsch hnr hj hpos K hKearly
  · rw [clockPre_fg]
    exact hprefix i le_rfl


/-- WC plan §6.5; DC the actual awake batch gives both anchor and target majorities. -/
theorem wcg_gateBatch [Fintype V] (hcausal : WCFinalityTargetEarlierStatement p c E rho) (ΔF :
  Time) (w : HealingWitness) (iStar : Nat) :
  ∀
  (_hvalid : V2.D.ExecutionValid E rho)
  (_hlinked : V2.D.Linked (fgsaFamilies p c).linked rho)
  (_hcstar : V2.D.CStar (fgsaFamilies p c).fresh rho)
  (_hnr : V2.D.NoRestart rho)
  (_hdelta : E.Δ = p.Δ)
  (_hroots : NamedRootCollisionFree p c E rho)
  (_hsync : Gen.V2.Duty.PartialSynchronyBy E rho (fgsaDelay E.Δ ΔF))
  (_hdeltaF : E.Δ ≤ ΔF)
  (_hfaultQ : Gen.Pure.FaultQ p.n (Gen.V2.Duty.faulty rho).card)
  (_haccountable : FinalitySlashableBound p c E rho)
  (_hpart : ∀ s, w.u + 1 ≤ s → SA.voteTime p.toParams s ≤ rho.horizon →
    (Gen.V2.Duty.faulty rho).card <
      (Gen.V2.Duty.awakeHonest E rho (SA.voteTime p.toParams s)).card)
  (_hstore : RStore p c E rho)
  (_hcumul : RStoreCumul p c E rho)
  (_hmono : RMono p c E rho)
  (_hactive : RActive p c E rho)
  (_hframe : RFrameExactNext p c E rho)
  (_hmeta : RFrameNext p c E rho)
  (_hrec : RRec p c E rho)
  (_hgeo : RGeo p c E rho)
  (_hcert : RCert p c E rho)
  (_hsrc : TSrc p c E rho)
  (_hlabel : LabelBound p c E rho)
  (_hqc : RQCOrigin p c E rho)
  (_hstrat : RStrat p c E rho)
  (_hnoslash : ∀ x ∈ rho.honest, EmittedRowsNoSlash p c E rho x)
  (_hemitted : ∀ j x r a e, HonestRowAt p c E rho j x r a →
    namedEntry a.payload.height_pair = some e →
    ∃ C B, actionSourceFG p c E rho x r = some (some C) ∧
      e = (hOf p.E p.cfg C, (derive p.E p.cfg C).T_h.root) ∧
      FGBlock.Preceq (derive p.E p.cfg C).T_h C ∧
      gateResult p c E rho x (r * p.R) = some (some B) ∧
      Block.Preceq (eraseFG C) B ∧ fastAt p c E rho x (r * p.R) (eraseFG C))
  (_htargets : ∀ i x row, row ∈ (storeAt p c E rho i x).base.obligations →
    Block.Preceq row.1 (storeAt p c E rho i x).base.stableRecord)
  (_hlease : ∀ i x row, row ∈ (storeAt p c E rho i x).base.obligations →
    ∃ j < i, ∃ s B, IsGateTick p c rho j x s ∧ gatePassedAt p c E rho j ∧
      gateResultAt p c E rho j = some (some B) ∧ Block.Preceq row.1 B ∧
      (row.1, row.2.1) ∈
      (let wcView := actView (clockPre p (storeAt p c E rho j x) (SA.gateTime p.toParams s));
        (wcView.blocks.filter (fun b => b != .genesis && Block.preceq b B)).flatMap
          (fun b => (@GridCO.admissionLevels GridCO.slowLeasePolicy
            p.toParams.engine p.n .root wcView s b).map (fun g => (b, g)))) ∧
      row.2.2 = SA.gateTime p.toParams s + SA.lifetime p.toParams ∧
      row.2.2 = SA.releaseTime p.toParams (s + p.k) ∧
      ∀ k w C, j < k → k < i → IsGateTick p c rho k x w →
        let pre := clockPre p (storeAt p c E rho k x) (SA.gateTime p.toParams w)
        GridCO.savedGenuine pre.base w = none →
        SA.Root.confirmationFrom p.toParams (eraseFG pre.fg.F) (actView pre) w = some C →
        (actView pre).obligations.any (fun r => !Block.compatible r.1 C) = false →
        (row.1, row.2.1) ∉ (let wcView := actView pre;
        (wcView.blocks.filter (fun b => b != .genesis && Block.preceq b C)).flatMap
          (fun b => (@GridCO.admissionLevels GridCO.slowLeasePolicy
            p.toParams.engine p.n .root wcView w b).map (fun g => (b, g)))))
  (_hfast : ∀ i x,
    ∀ s X, X ∈ (FGSA.fastWriteAt (storeAt p c E rho i x) s).getD [] →
      ∃ j < i, IsGateTick p c rho j x s ∧ gatePassedAt p c E rho j ∧
        ∃ B, gateResultAt p c E rho j = some (some B) ∧
          Block.Preceq X B ∧ fastAt p c E rho x s X)
  (_hdeadlines : ∀ i x,
    ∀ K g deadline, (K, g, deadline) ∈ (storeAt p c E rho i x).base.obligations →
      ∀ B, B ≠ .genesis → Block.Preceq B K →
        Gen.AC.Root.ProtectsUntil (storeAt p c E rho i x).base B g deadline)
  (_hheldRows : ∀ i x W, HeldAt p c E rho i x W → ∀ a ∈ chainRows W,
    ∃ (wire : RowWire p.n) (r : Nat), wire.toRow? = some a ∧
      wire.auth = .seat .fg a.signer ∧ ∃ k o t, k < i ∧
        rho.events[k]? = some (.deliver x o t) ∧
        ∀ z, RowSigner p c rho wire z → z ∈ rho.honest →
          HonestRowBefore p c E rho i z r wire ∧ p.actionTime r ≤ t)
  (_hscopeRows : ∀ D, RootBlockInRun p c E rho (eraseFG D) → ∀ a ∈ chainRows D,
    rho.seatOf (.base .fg) a.signer ∈ rho.honest → ∃ j r wire,
      HonestRowAt p c E rho j (rho.seatOf (.base .fg) a.signer) r wire ∧
      wire.toRow? = some a ∧ wire.auth = .seat .fg a.signer)
  (_hfinalHead : ∀ j z r a u, HonestRowAt p c E rho j z r a →
    RowSigner p c rho a z → a.toRow? = some u → ∀ fp,
    u.finality_pair = some fp → ∃ B, HeldAt p c E rho j z B ∧
      fp.height = (heightView p B).h_j ∧ fp.target = (heightView p B).J.root ∧
      TargetQCAt p.E B fp.height (heightView p B).J),
  WCSeed p c E rho w iStar → ∀ i x s, iStar ≤ i → i < rho.events.length →
    WCInv p c E rho w iStar i → IsGateTick p c rho i x s → w.u < s → ∀ B,
    (∀ k y, rho.events[k]? = some (.tick y (SA.voteTime p.toParams s)) →
      Block.Preceq B (headAtIdx p c E rho k s)) →
    let pre := clockPre p (storeAt p c E rho i x) (SA.gateTime p.toParams s)
    let v := actView pre
    let a := eraseFG pre.fg.F
    GridCO.voterCount (GridCO.lateVotes p.toParams.engine v s) <
      2 * SA.Root.prefixSupport p.toParams v s a ∧
    GridCO.voterCount (GridCO.lateVotes p.toParams.engine v s) <
      2 * SA.Root.prefixSupport p.toParams v s B ∧
    (∀ X, Block.Preceq a X → Block.Preceq X B → X ≠ a → X ∈ v.blocks) := by
  classical
  intro hvalid hlinked hcstar hnr hdelta hroots hsync hdeltaF
    hfaultQ haccountable hpart hstore hcumul hmono hactive hframe hmeta hrec hgeo hcert
    hsrc hlabel hqc hstrat
    hnoslash hemitted htargets hlease hfast hdeadlines hheldRows hscopeRows hfinalHead
    hs i x s hi hilen inv ht hslabel B hB
  have hsch := hvalid.toScheduleWellFormed
  have hx := hvalid.honest_only _ (List.mem_of_getElem? ht)
  have hcut : SA.gateTime p.toParams s ≤ rho.horizon :=
    (hvalid.in_horizon _ (List.mem_of_getElem? ht)).2
  have hGST : E.t_GST ≤ SA.voteTime p.toParams s := by
    apply hs.firstVoteAfterGST.trans
    have hc : ((w.u + 1 : Nat) : Int) ≤ s := Int.ofNat_le.mpr (Nat.succ_le_of_lt hslabel)
    change 4 * p.Δ * ((w.u + 1 : Nat) : Int) + p.Δ ≤ 4 * p.Δ * (s : Int) + p.Δ
    nlinarith [p.deltaPos]
  have hhead := wcg_gateHeads ΔF w iStar hvalid hlinked hcstar hnr hdelta hroots hsync hdeltaF
    hfaultQ haccountable hpart hstore hcumul hmono hactive hframe hmeta hrec hgeo hcert
    hsrc hlabel hqc hstrat
    hnoslash hemitted htargets hlease hfast hdeadlines hheldRows hscopeRows hfinalHead
    hs i x s hi hilen inv ht hslabel
  have hF := (wcg_gateFinalOrigin hcausal) ΔF w iStar hvalid hlinked hcstar hnr hdelta hroots
    hsync hdeltaF
    hfaultQ haccountable hpart hstore hcumul hmono hactive hframe hmeta hrec hgeo hcert
    hsrc hlabel hqc hstrat
    hnoslash hemitted htargets hlease hfast hdeadlines hheldRows hscopeRows hfinalHead
    hs i x s hi hilen inv ht hslabel
  have hfinal : ∀ k y, rho.events[k]? = some (.tick y (SA.voteTime p.toParams s)) →
      ∀ j, j ≤ i → Block.Preceq (F_at p c E rho j x) (headAtIdx p c E rho k s) := by
    intro k y hk j hji
    have hh := hhead k y (hvalid.honest_only _ (List.mem_of_getElem? hk)) hk
    apply block_preceq_trans (eraseFG_preceq (hmono hnr j i x hx hji).1)
    rcases hF with hF | ⟨l, z, r, C, hr, hrs, hFC⟩
    · exact block_preceq_trans hF hh.1
    · exact block_preceq_trans hFC (hh.2 l z r C hr hrs)
  let A := Gen.V2.Duty.awakeHonest E rho (SA.voteTime p.toParams s)
  let e : Fin p.n ≃ V := Equiv.ofBijective _ (hcstar (.base (.head s)) trivial)
  let H := A.image e.symm
  have hH : ∀ k, k ∈ H ↔ rho.seatOf (.base (.head s)) k ∈ rho.honest ∧
      E.awake (rho.seatOf (.base (.head s)) k) (SA.voteTime p.toParams s) = true := by
    intro k
    have he : k ∈ H ↔ e k ∈ A := by
      change k ∈ A.image e.symm ↔ e k ∈ A
      simp only [Finset.mem_image, e.symm_apply_eq]
      exact ⟨fun ⟨_, hy, he⟩ => he ▸ hy, fun hk => ⟨e k, hk, rfl⟩⟩
    rw [he]
    change rho.seatOf (.base (.head s)) k ∈
      Gen.V2.Duty.awakeHonest E rho (SA.voteTime p.toParams s) ↔ _
    rw [Gen.V2.Duty.awakeHonest_def]
    exact Finset.mem_filter
  have hv : SA.voteTime p.toParams s ≤ rho.horizon := by
    apply le_trans (b := SA.gateTime p.toParams s) _ hcut
    change 4 * p.Δ * (s : Int) + p.Δ ≤ 4 * p.Δ * (s : Int) + 6 * p.Δ
    linarith [p.deltaPos]
  have hcard : H.card = A.card := Finset.card_image_of_injective A e.symm.injective
  have hb : Gen.Pure.Batch H.card (Gen.V2.Duty.faulty rho).card :=
    ⟨hcard ▸ hpart s (Nat.succ_le_of_lt hslabel) hv⟩
  apply fgsa_gate_batch_premises E rho hvalid hcstar i x s B H hb
    (fun k hk ha => (hH k).mpr ⟨hk, ha⟩)
  intro k hk
  exact growthStepGateBatch_gate_active_heads hvalid hnr hdelta hcstar hroots hsync hcumul ht
    hGST hfinal B hB
    k ((hH k).mp hk).1 ((hH k).mp hk).2

end AvailableChain.FGSA.Run



/-! WC plan §6.5; DC gate order and the guard precede retrospective transfer. -/

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG KitFG Gen.Pure

variable {p : Params} {In V : Type} {c : AppCodec In} [DecidableEq V] [Fintype V]
    {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}

/-- WC plan §6.5; DC the new gate extends the seed and all results at earlier labels. -/
theorem wcg_gateResult (hcausal : WCFinalityTargetEarlierStatement p c E rho) (ΔF : Time) (w :
  HealingWitness) (iStar : Nat) :
  ∀
  (_hvalid : V2.D.ExecutionValid E rho)
  (_hlinked : V2.D.Linked (fgsaFamilies p c).linked rho)
  (_hcstar : V2.D.CStar (fgsaFamilies p c).fresh rho)
  (_hnr : V2.D.NoRestart rho)
  (_hdelta : E.Δ = p.Δ)
  (_hroots : NamedRootCollisionFree p c E rho)
  (_hsync : Gen.V2.Duty.PartialSynchronyBy E rho (fgsaDelay E.Δ ΔF))
  (_hdeltaF : E.Δ ≤ ΔF)
  (_hfaultQ : Gen.Pure.FaultQ p.n (Gen.V2.Duty.faulty rho).card)
  (_haccountable : FinalitySlashableBound p c E rho)
  (_hpart : ∀ s, w.u + 1 ≤ s → SA.voteTime p.toParams s ≤ rho.horizon →
    (Gen.V2.Duty.faulty rho).card <
      (Gen.V2.Duty.awakeHonest E rho (SA.voteTime p.toParams s)).card)
  (_hstore : RStore p c E rho)
  (_hcumul : RStoreCumul p c E rho)
  (_hmono : RMono p c E rho)
  (_hactive : RActive p c E rho)
  (_hframe : RFrameExactNext p c E rho)
  (_hmeta : RFrameNext p c E rho)
  (_hrec : RRec p c E rho)
  (_hgeo : RGeo p c E rho)
  (_hcert : RCert p c E rho)
  (_hsrc : TSrc p c E rho)
  (_hlabel : LabelBound p c E rho)
  (_hqc : RQCOrigin p c E rho)
  (_hstrat : RStrat p c E rho)
  (_hnoslash : ∀ x ∈ rho.honest, EmittedRowsNoSlash p c E rho x)
  (_hemitted : ∀ j x r a e, HonestRowAt p c E rho j x r a →
    namedEntry a.payload.height_pair = some e →
    ∃ C B, actionSourceFG p c E rho x r = some (some C) ∧
      e = (hOf p.E p.cfg C, (derive p.E p.cfg C).T_h.root) ∧
      FGBlock.Preceq (derive p.E p.cfg C).T_h C ∧
      gateResult p c E rho x (r * p.R) = some (some B) ∧
      Block.Preceq (eraseFG C) B ∧ fastAt p c E rho x (r * p.R) (eraseFG C))
  (_htargets : ∀ i x row, row ∈ (storeAt p c E rho i x).base.obligations →
    Block.Preceq row.1 (storeAt p c E rho i x).base.stableRecord)
  (_hlease : ∀ i x row, row ∈ (storeAt p c E rho i x).base.obligations →
    ∃ j < i, ∃ s B, IsGateTick p c rho j x s ∧ gatePassedAt p c E rho j ∧
      gateResultAt p c E rho j = some (some B) ∧ Block.Preceq row.1 B ∧
      (row.1, row.2.1) ∈
      (let wcView := actView (clockPre p (storeAt p c E rho j x) (SA.gateTime p.toParams s));
        (wcView.blocks.filter (fun b => b != .genesis && Block.preceq b B)).flatMap
          (fun b => (@GridCO.admissionLevels GridCO.slowLeasePolicy
            p.toParams.engine p.n .root wcView s b).map (fun g => (b, g)))) ∧
      row.2.2 = SA.gateTime p.toParams s + SA.lifetime p.toParams ∧
      row.2.2 = SA.releaseTime p.toParams (s + p.k) ∧
      ∀ k w C, j < k → k < i → IsGateTick p c rho k x w →
        let pre := clockPre p (storeAt p c E rho k x) (SA.gateTime p.toParams w)
        GridCO.savedGenuine pre.base w = none →
        SA.Root.confirmationFrom p.toParams (eraseFG pre.fg.F) (actView pre) w = some C →
        (actView pre).obligations.any (fun r => !Block.compatible r.1 C) = false →
        (row.1, row.2.1) ∉ (let wcView := actView pre;
        (wcView.blocks.filter (fun b => b != .genesis && Block.preceq b C)).flatMap
          (fun b => (@GridCO.admissionLevels GridCO.slowLeasePolicy
            p.toParams.engine p.n .root wcView w b).map (fun g => (b, g)))))
  (_hfast : ∀ i x,
    ∀ s X, X ∈ (FGSA.fastWriteAt (storeAt p c E rho i x) s).getD [] →
      ∃ j < i, IsGateTick p c rho j x s ∧ gatePassedAt p c E rho j ∧
        ∃ B, gateResultAt p c E rho j = some (some B) ∧
          Block.Preceq X B ∧ fastAt p c E rho x s X)
  (_hdeadlines : ∀ i x,
    ∀ K g deadline, (K, g, deadline) ∈ (storeAt p c E rho i x).base.obligations →
      ∀ B, B ≠ .genesis → Block.Preceq B K →
        Gen.AC.Root.ProtectsUntil (storeAt p c E rho i x).base B g deadline)
  (_hheldRows : ∀ i x W, HeldAt p c E rho i x W → ∀ a ∈ chainRows W,
    ∃ (wire : RowWire p.n) (r : Nat), wire.toRow? = some a ∧
      wire.auth = .seat .fg a.signer ∧ ∃ k o t, k < i ∧
        rho.events[k]? = some (.deliver x o t) ∧
        ∀ z, RowSigner p c rho wire z → z ∈ rho.honest →
          HonestRowBefore p c E rho i z r wire ∧ p.actionTime r ≤ t)
  (_hscopeRows : ∀ D, RootBlockInRun p c E rho (eraseFG D) → ∀ a ∈ chainRows D,
    rho.seatOf (.base .fg) a.signer ∈ rho.honest → ∃ j r wire,
      HonestRowAt p c E rho j (rho.seatOf (.base .fg) a.signer) r wire ∧
      wire.toRow? = some a ∧ wire.auth = .seat .fg a.signer)
  (_hfinalHead : ∀ j z r a u, HonestRowAt p c E rho j z r a →
    RowSigner p c rho a z → a.toRow? = some u → ∀ fp,
    u.finality_pair = some fp → ∃ B, HeldAt p c E rho j z B ∧
      fp.height = (heightView p B).h_j ∧ fp.target = (heightView p B).J.root ∧
      TargetQCAt p.E B fp.height (heightView p B).J),
  WCSeed p c E rho w iStar → ∀ i x s, iStar ≤ i → i < rho.events.length →
    WCInv p c E rho w iStar i → enabledGateAt p c E rho i x s → w.u < s →
    ∃ B, gateResultAt p c E rho i = some (some B) ∧ gatePassedAt p c E rho i ∧
      Block.Preceq w.QStar B ∧
      (∀ j y r C, WCResult p c E rho w iStar i j y r C → r < s → Block.Preceq C B) ∧
      (∀ j y r C, WCResult p c E rho w iStar i j y r C → Block.Compatible C B) ∧
      Block.Compatible (S_at p c E rho i x) B := by
  intro hvalid hlinked hcstar hnr hdelta hroots hsync hdeltaF
    hfaultQ haccountable hpart hstore hcumul hmono hactive hframe hmeta hrec hgeo hcert
    hsrc hlabel hqc hstrat hnoslash hemitted htargets hlease hfast hdeadlines hheldRows
    hscopeRows hfinalHead hs i x s hi hilen inv hEnabled hslabel
  have ht := hEnabled.1
  have hsch := hvalid.toScheduleWellFormed
  have hx := hvalid.honest_only _ (List.mem_of_getElem? ht)
  have hhead := wcg_gateHeads ΔF w iStar hvalid hlinked hcstar hnr hdelta hroots hsync hdeltaF
    hfaultQ haccountable hpart hstore hcumul hmono hactive hframe hmeta hrec hgeo hcert
    hsrc hlabel hqc hstrat hnoslash hemitted htargets hlease hfast hdeadlines hheldRows
    hscopeRows hfinalHead hs i x s hi hilen inv ht hslabel
  have batch := (wcg_gateBatch hcausal) ΔF w iStar hvalid hlinked hcstar hnr hdelta hroots
    hsync hdeltaF
    hfaultQ haccountable hpart hstore hcumul hmono hactive hframe hmeta hrec hgeo hcert
    hsrc hlabel hqc hstrat hnoslash hemitted htargets hlease hfast hdeadlines hheldRows
    hscopeRows hfinalHead hs i x s hi hilen inv ht hslabel
  let pre := clockPre p (storeAt p c E rho i x) (SA.gateTime p.toParams s)
  have hFS : Block.Preceq (eraseFG pre.fg.F) (S_at p c E rho i x) := by
    change Block.Preceq (eraseFG (clockPre p _ _).fg.F) _
    rw [clockPre_fg]
    exact nestOK_stateBefore E rho i x
  have hFQ : Block.Compatible (eraseFG pre.fg.F) w.QStar :=
    block_compatible_of_common hFS (inv.served i x hi le_rfl hx)
  have hbatchQ := batch w.QStar (fun k y hk =>
    (hhead k y (hvalid.honest_only _ (List.mem_of_getElem? hk)) hk).1)
  obtain ⟨B, hraw, hQB⟩ := fgsa_confirmationFrom_covers_majority p (actView pre)
    (eraseFG pre.fg.F) w.QStar s w.QStar.root hFQ hbatchQ.1 hbatchQ.2.1 hbatchQ.2.2
  have hrawAt : gateResultAt p c E rho i = some (SA.Root.confirmationFrom p.toParams
      (eraseFG pre.fg.F) (actView pre) s) := by
    rw [gateResultAt_eq_gateResult p c E rho hsch ht,
      gateResult_eq_saved p c E rho hsch ht]
    change _ = some (SA.Root.confirmationFrom p.toParams
      (eraseFG (clockPre p (storeAt p c E rho i x) _).fg.F) _ s)
    rw [clockPre_fg]
    exact fgsa_gate_saved_result E rho hsch ht
      (fgsa_gate_joined_of_enabled E rho hEnabled)
  have hB : gateResultAt p c E rho i = some (some B) := hrawAt.trans (congrArg some hraw)
  have ordered : ∀ j y r C, WCResult p c E rho w iStar i j y r C → r < s →
      Block.Preceq C B := by
    intro j y r C hr hrs
    have hc := block_compatible_of_preceq_compatible hFS
      (wcg_result_output_compatible inv hr hi le_rfl hx)
    have hb := batch C (fun k z hk =>
      (hhead k z (hvalid.honest_only _ (List.mem_of_getElem? hk)) hk).2 j y r C hr hrs)
    obtain ⟨D, hD, hCD⟩ := fgsa_confirmationFrom_covers_majority p (actView pre)
      (eraseFG pre.fg.F) C s C.root hc hb.1 hb.2.1 hb.2.2
    exact (Option.some.inj (hD.symm.trans hraw)) ▸ hCD
  have hGST : E.t_GST ≤ SA.voteTime p.toParams s := by
    apply hs.firstVoteAfterGST.trans
    have hc : ((w.u + 1 : Nat) : Int) ≤ s := Int.ofNat_le.mpr (Nat.succ_le_of_lt hslabel)
    change 4 * p.Δ * ((w.u + 1 : Nat) : Int) + p.Δ ≤ 4 * p.Δ * (s : Int) + p.Δ
    nlinarith [p.deltaPos]
  have hsyncLabel := Gen.V2.Duty.LabelSyncOn.of_recoveryBy E rho
    (fun o => ¬ isRowObject o) (SA.voteTime p.toParams s) (SA.gateTime p.toParams s)
    hsync (fgsaDelay_nonrow E.Δ _) hGST (by
      rw [hdelta]
      change 4 * p.Δ * (s : Int) + p.Δ + p.Δ ≤ 4 * p.Δ * (s : Int) + 6 * p.Δ
      linarith [p.deltaPos]) (hvalid.in_horizon _ (List.mem_of_getElem? ht)).2
  have compatible : ∀ j y r C, WCResult p c E rho w iStar i j y r C →
      Block.Compatible C B := by
    intro j y r C hr
    have hle : r ≤ s := by
      obtain ⟨hjl, hje⟩ := List.getElem?_eq_some_iff.mp hr.event
      obtain ⟨hil, hie⟩ := List.getElem?_eq_some_iff.mp ht
      have hk := (List.pairwise_iff_getElem.mp hsch.sorted) j i hjl hil hr.completed
      rw [hje, hie] at hk
      have ht := V2.D.Engine.time_le_of_key_le _ _ hk
      change 4 * p.Δ * (r : Int) + 6 * p.Δ ≤ 4 * p.Δ * (s : Int) + 6 * p.Δ at ht
      have hc : (r : Int) ≤ s := by nlinarith [p.deltaPos]
      exact Int.ofNat_le.mp hc
    rcases hle.lt_or_eq with hlt | heq
    · exact block_compatible_of_common (ordered j y r C hr hlt) (block_preceq_refl B)
    · subst r
      exact fgsa_sameLabel (hroots := hroots) p c E rho hvalid hnr hdelta s hsyncLabel
        y x C B hr.honest hx
        ((gateResultAt_eq_gateResult p c E rho hsch hr.event).symm.trans hr.value)
        ((gateResultAt_eq_gateResult p c E rho hsch ht).symm.trans hB)
  have hFB : Block.Preceq (eraseFG pre.fg.F) B := by
    change (if _ then some _ else none) = some B at hraw
    split at hraw
    · cases hraw
      apply walk_covers_of_dominated_suffix _ _ _ _ _
      · exact block_compatible_of_common (block_preceq_refl _) (block_preceq_refl _)
      · intro C hAC hCA
        change (!decide (_ = C) && Block.preceq _ C) = true at hAC
        have heq := block_preceq_antisymm (Bool.and_eq_true_iff.mp hAC).2 hCA
        simp only [heq, decide_true, Bool.not_true, Bool.false_and, Bool.false_eq_true] at hAC
    · contradiction
  have hSB : Block.Compatible (S_at p c E rho i x) B := by
    rcases inv.outputOrigin i x hi le_rfl hx with hq | ⟨j, y, r, hr⟩ | ⟨l, _, hli, he, _⟩
    · rw [hq]
      exact block_compatible_of_common hQB (block_preceq_refl B)
    · exact compatible j y r _ hr
    · rw [he]
      have hFi : Block.Preceq (F_at p c E rho i x) B := by
        change Block.Preceq (eraseFG (clockPre p _ _).fg.F) B at hFB
        rwa [clockPre_fg] at hFB
      exact block_compatible_of_common
        (block_preceq_trans (eraseFG_preceq (hmono hnr l i x hx hli).1) hFi)
        (block_preceq_refl B)
  refine ⟨B, hB, ?_, hQB, ordered, compatible, hSB⟩
  refine ⟨x, s, ht, ?_, B, hraw, ?_⟩
  · change ((clockPre p (storeAt p c E rho i x) _).base.genuine.find? _).map _ = none
    rw [clockPre_genuine]
    exact fgsa_gate_fresh E rho hsch ht
  · apply List.any_eq_false.mpr
    intro row hr
    have hold := (clockPre_obligations_sublist p (storeAt p c E rho i x)
      (SA.gateTime p.toParams s)).subset hr
    have hb := htargets i x row hold
    have hc := block_compatible_of_preceq_compatible hb hSB
    change Block.compatible row.1 B = true at hc
    simpa only [Bool.not_eq_true', Bool.not_eq_false] using hc

end AvailableChain.FGSA.Run



/-! WC plan §6.5; DC a received finalization was served before its acceptance. -/

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG KitFG Gen.Pure

variable {p : Params} {In V : Type} {c : AppCodec In} [DecidableEq V] [Fintype V]
    {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}

/-- WC plan §6.5; DC finality at a delivery cannot overtake the preceding honest outputs. -/
theorem wcg_reconcileBound (hcausal : WCFinalityTargetEarlierStatement p c E rho) (ΔF : Time)
  (w : HealingWitness) (iStar : Nat) :
  ∀
  (_hvalid : V2.D.ExecutionValid E rho)
  (_hlinked : V2.D.Linked (fgsaFamilies p c).linked rho)
  (_hcstar : V2.D.CStar (fgsaFamilies p c).fresh rho)
  (_hnr : V2.D.NoRestart rho)
  (_hdelta : E.Δ = p.Δ)
  (_hroots : NamedRootCollisionFree p c E rho)
  (_hsync : Gen.V2.Duty.PartialSynchronyBy E rho (fgsaDelay E.Δ ΔF))
  (_hdeltaF : E.Δ ≤ ΔF)
  (_hfaultQ : Gen.Pure.FaultQ p.n (Gen.V2.Duty.faulty rho).card)
  (_haccountable : FinalitySlashableBound p c E rho)
  (_hpart : ∀ s, w.u + 1 ≤ s → SA.voteTime p.toParams s ≤ rho.horizon →
    (Gen.V2.Duty.faulty rho).card <
      (Gen.V2.Duty.awakeHonest E rho (SA.voteTime p.toParams s)).card)
  (_hstore : RStore p c E rho)
  (_hcumul : RStoreCumul p c E rho)
  (_hmono : RMono p c E rho)
  (_hactive : RActive p c E rho)
  (_hframe : RFrameExactNext p c E rho)
  (_hmeta : RFrameNext p c E rho)
  (_hrec : RRec p c E rho)
  (_hgeo : RGeo p c E rho)
  (_hcert : RCert p c E rho)
  (_hsrc : TSrc p c E rho)
  (_hlabel : LabelBound p c E rho)
  (_hqc : RQCOrigin p c E rho)
  (_hstrat : RStrat p c E rho)
  (_hnoslash : ∀ x ∈ rho.honest, EmittedRowsNoSlash p c E rho x)
  (_hemitted : ∀ j x r a e, HonestRowAt p c E rho j x r a →
    namedEntry a.payload.height_pair = some e →
    ∃ C B, actionSourceFG p c E rho x r = some (some C) ∧
      e = (hOf p.E p.cfg C, (derive p.E p.cfg C).T_h.root) ∧
      FGBlock.Preceq (derive p.E p.cfg C).T_h C ∧
      gateResult p c E rho x (r * p.R) = some (some B) ∧
      Block.Preceq (eraseFG C) B ∧ fastAt p c E rho x (r * p.R) (eraseFG C))
  (_htargets : ∀ i x row, row ∈ (storeAt p c E rho i x).base.obligations →
    Block.Preceq row.1 (storeAt p c E rho i x).base.stableRecord)
  (_hlease : ∀ i x row, row ∈ (storeAt p c E rho i x).base.obligations →
    ∃ j < i, ∃ s B, IsGateTick p c rho j x s ∧ gatePassedAt p c E rho j ∧
      gateResultAt p c E rho j = some (some B) ∧ Block.Preceq row.1 B ∧
      (row.1, row.2.1) ∈
      (let wcView := actView (clockPre p (storeAt p c E rho j x) (SA.gateTime p.toParams s));
        (wcView.blocks.filter (fun b => b != .genesis && Block.preceq b B)).flatMap
          (fun b => (@GridCO.admissionLevels GridCO.slowLeasePolicy
            p.toParams.engine p.n .root wcView s b).map (fun g => (b, g)))) ∧
      row.2.2 = SA.gateTime p.toParams s + SA.lifetime p.toParams ∧
      row.2.2 = SA.releaseTime p.toParams (s + p.k) ∧
      ∀ k w C, j < k → k < i → IsGateTick p c rho k x w →
        let pre := clockPre p (storeAt p c E rho k x) (SA.gateTime p.toParams w)
        GridCO.savedGenuine pre.base w = none →
        SA.Root.confirmationFrom p.toParams (eraseFG pre.fg.F) (actView pre) w = some C →
        (actView pre).obligations.any (fun r => !Block.compatible r.1 C) = false →
        (row.1, row.2.1) ∉ (let wcView := actView pre;
        (wcView.blocks.filter (fun b => b != .genesis && Block.preceq b C)).flatMap
          (fun b => (@GridCO.admissionLevels GridCO.slowLeasePolicy
            p.toParams.engine p.n .root wcView w b).map (fun g => (b, g)))))
  (_hfast : ∀ i x,
    ∀ s X, X ∈ (FGSA.fastWriteAt (storeAt p c E rho i x) s).getD [] →
      ∃ j < i, IsGateTick p c rho j x s ∧ gatePassedAt p c E rho j ∧
        ∃ B, gateResultAt p c E rho j = some (some B) ∧
          Block.Preceq X B ∧ fastAt p c E rho x s X)
  (_hdeadlines : ∀ i x,
    ∀ K g deadline, (K, g, deadline) ∈ (storeAt p c E rho i x).base.obligations →
      ∀ B, B ≠ .genesis → Block.Preceq B K →
        Gen.AC.Root.ProtectsUntil (storeAt p c E rho i x).base B g deadline)
  (_hheldRows : ∀ i x W, HeldAt p c E rho i x W → ∀ a ∈ chainRows W,
    ∃ (wire : RowWire p.n) (r : Nat), wire.toRow? = some a ∧
      wire.auth = .seat .fg a.signer ∧ ∃ k o t, k < i ∧
        rho.events[k]? = some (.deliver x o t) ∧
        ∀ z, RowSigner p c rho wire z → z ∈ rho.honest →
          HonestRowBefore p c E rho i z r wire ∧ p.actionTime r ≤ t)
  (_hscopeRows : ∀ D, RootBlockInRun p c E rho (eraseFG D) → ∀ a ∈ chainRows D,
    rho.seatOf (.base .fg) a.signer ∈ rho.honest → ∃ j r wire,
      HonestRowAt p c E rho j (rho.seatOf (.base .fg) a.signer) r wire ∧
      wire.toRow? = some a ∧ wire.auth = .seat .fg a.signer)
  (_hfinalHead : ∀ j z r a u, HonestRowAt p c E rho j z r a →
    RowSigner p c rho a z → a.toRow? = some u → ∀ fp,
    u.finality_pair = some fp → ∃ B, HeldAt p c E rho j z B ∧
      fp.height = (heightView p B).h_j ∧ fp.target = (heightView p B).J.root ∧
      TargetQCAt p.E B fp.height (heightView p B).J),
  WCSeed p c E rho w iStar → ∀ i, iStar ≤ i → i < rho.events.length →
    WCInv p c E rho w iStar i → ∀ v o t, rho.events[i]? = some (.deliver v o t) →
    ∀ x y, x ∈ rho.honest → y ∈ rho.honest →
      Block.Preceq (F_at p c E rho (i + 1) x) (S_at p c E rho i y) := by
  intro hvalid hlinked hcstar hnr hdelta hroots hsync hdeltaF
    hfaultQ haccountable hpart hstore hcumul hmono hactive hframe hmeta hrec hgeo hcert
    hsrc hlabel hqc hstrat hnoslash hemitted htargets hlease hfast hdeadlines hheldRows
    hscopeRows hfinalHead hs i hi _hilen inv v o t he x y hx hy
  obtain ⟨D, hD, hF⟩ := (hstore (i + 1) x hx).1.fg.Fcar
  by_cases hlo : (finalityView p D).h_F ≤ w.M
  · have hbelow := (wcg_lowFinalized hroots haccountable hs
      D _ _ (wcg_finalizedOccurrence hscopeRows hnoslash D _ _
        (rootScope_store hx hD) hF rfl) hlo).2
    exact block_preceq_trans hbelow (inv.served i y hi le_rfl hy)
  have hpos : 0 < (finalityView p D).h_F := by simp only [Height] at hlo ⊢; omega
  have hhigh : w.M + 1 ≤ (finalityView p D).h_F := by simp only [Height] at hlo ⊢; omega
  obtain ⟨jf, z, rf, af, uf, H, jt, q, rt, aT, ut, K, B, hjf, haf, _, _, _, _,
      _, _, _, _, hjt, haT, hdecode, _, htarget, hK, hXK, _hgate, _hKB, hgap⟩ :=
    (hcausal hvalid hlinked hfaultQ hroots hheldRows hfinalHead hqc
      hemitted (i + 1) x D _ _ ⟨hx, hD⟩ hpos hF rfl).finalityRow
  have hfi : jf < i := by
    rcases (Nat.le_of_lt_succ hjf).lt_or_eq with h | h
    · exact h
    · subst jf
      have hf := haf.2.1
      rw [he] at hf
      cases hf
  have hfields : aT.payload.height_pair = ut.height_pair := by
    rcases aT with ⟨auth, body⟩
    cases auth with
    | none => cases hdecode
    | proposer s => cases hdecode
    | seat label k =>
      cases label with
      | head s => cases hdecode
      | fg => exact congrArg Row.height_pair (Option.some.inj hdecode)
  have hname : namedEntry aT.payload.height_pair =
      some ((finalityView p D).h_F, (storeAt p c E rho (i + 1) x).fg.F.root) := by
    rw [hfields, htarget]
    rfl
  by_cases hbefore : jt < iStar
  · obtain ⟨K', B', hK', _, _, _, _, hbelow⟩ :=
      hs.highSources jt q rt aT _ hbefore haT hname hhigh
    have heq : K = K' := Option.some.inj (Option.some.inj (hK.symm.trans hK'))
    exact block_preceq_trans (eraseFG_preceq hXK)
      (block_preceq_trans (heq ▸ hbelow) (inv.served i y hi le_rfl hy))
  obtain ⟨C, hr, hKC⟩ := inv.suffixSources jt q rt K (Nat.le_of_not_gt hbefore)
    (hjt.trans hfi) haT.1 haT.2.1 hK
  have hhor : SA.gateTime p.toParams (rt * p.R) + 4 * p.Δ ≤ rho.horizon :=
    hgap.le.trans (hvalid.in_horizon _ (List.mem_of_getElem? haf.2.1)).2
  have hcut : afterTicksIdx rho (SA.gateTime p.toParams (rt * p.R) + 4 * p.Δ) ≤ i := by
    apply le_trans (b := jf) _ (Nat.le_of_lt hfi)
    by_contra hn
    have hlt := Nat.lt_of_not_ge hn
    have hm : V2.Event.tick z (p.actionTime rf) ∈ rho.events.filter
        (cutPred (SA.gateTime p.toParams (rt * p.R) + 4 * p.Δ)) := by
      rw [V2.D.Engine.filter_eq_take hvalid.toScheduleWellFormed _ (by
        intro e f hk hf
        exact decide_eq_true (hk.trans (of_decide_eq_true hf)))]
      apply List.mem_of_getElem? (i := jf)
      change (rho.events.take (afterTicksIdx rho
        (SA.gateTime p.toParams (rt * p.R) + 4 * p.Δ)))[jf]? = _
      rw [List.getElem?_take_of_lt hlt]
      exact haf.2.1
    have hk := of_decide_eq_true (List.mem_filter.mp hm).2
    have ht : p.actionTime rf ≤ SA.gateTime p.toParams (rt * p.R) + 4 * p.Δ := by
      rcases Prod.Lex.toLex_le_toLex.mp hk with h | ⟨h, _⟩
      · exact h.le
      · exact h.le
    exact (not_lt.mpr ht) hgap
  have hserved := wcg_service4_prefix hvalid hlinked hcstar hnr hdelta hroots hsync hdeltaF
    hfaultQ haccountable hpart hstore hcumul hmono hactive hframe hmeta hrec hgeo hcert
    hsrc hlabel hqc hstrat hnoslash hemitted htargets hlease hfast hdeadlines hheldRows
    hscopeRows hfinalHead hs i inv jt q (rt * p.R) C hr hhor i y hcut le_rfl hy
  exact block_preceq_trans (eraseFG_preceq hXK) (block_preceq_trans hKC hserved)

end AvailableChain.FGSA.Run



/-! WC plan §6.5; DC the ordered handler cases preserve and identify the output. -/

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG KitFG Gen.Pure

variable {p : Params} {In V : Type} {c : AppCodec In} [DecidableEq V]
    {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}

/-- WC plan §6.5; DC a fresh accepted gate normalizes an already compatible output. -/
private theorem growthStepOutput_gate_output {j : Nat} {x : V} {s : Slot} {B : Block}
    (hsch : V2.D.ScheduleWellFormed E rho) (ht : IsGateTick p c rho j x s)
    (hB : gateResultAt p c E rho j = some (some B)) (hpass : gatePassedAt p c E rho j)
    (hcompat : Block.Compatible (S_at p c E rho j x) B) :
    S_at p c E rho (j + 1) x = GridCO.advance (S_at p c E rho j x) B ∧
      Block.Preceq (S_at p c E rho j x) (S_at p c E rho (j + 1) x) := by
  have hrawAt : gateResultAt p c E rho j = some (SA.Root.confirmationFrom p.toParams
      (eraseFG (clockPre p (storeAt p c E rho j x) (SA.gateTime p.toParams s)).fg.F)
      (actView (clockPre p (storeAt p c E rho j x) (SA.gateTime p.toParams s))) s) := by
    rw [gateResultAt_eq_gateResult p c E rho hsch ht,
      gateResult_eq_saved p c E rho hsch ht, clockPre_fg]
    exact fgsa_gate_saved_result E rho hsch ht
      (fgsa_gate_joined_of_enabled E rho (wcg_gate_enabled_of_result hsch ht hB))
  have hraw := Option.some.inj (hrawAt.symm.trans hB)
  obtain ⟨y, r, he, _, G, hG, hguard⟩ := hpass
  have hevent := V2.Event.tick.inj (Option.some.inj (he.symm.trans ht))
  have hlabel : r = s := by
    have ht := hevent.2
    change 4 * p.Δ * (r : Int) + 6 * p.Δ = 4 * p.Δ * (s : Int) + 6 * p.Δ at ht
    have hcast : (r : Int) = s := by nlinarith [p.deltaPos]
    exact Int.ofNat_inj.mp hcast
  have hxy := hevent.1
  subst y
  subst r
  have heq : G = B := Option.some.inj (hG.symm.trans hraw)
  subst G
  have hview := fgsa_clockPre_gateView p (storeAt p c E rho j x) s
  have hraw' : (fgsaAC E rho).raw j s x = some B := by
    rw [clockPre_fg] at hraw
    have he := congrArg (fun v => SA.Root.confirmationFrom p.toParams
      (eraseFG (storeAt p c E rho j x).fg.F) v s) hview
    exact he.symm.trans hraw
  have hguard' : ∀ lease ∈ ((fgsaAC E rho).gateView j x s).obligations,
      Block.Compatible (Gen.AC.Lease.target lease) B := by
    intro lease hm
    have he : (clockPre p (storeAt p c E rho j x) (SA.gateTime p.toParams s)).base.obligations =
        ((fgsaAC E rho).gateView j x s).obligations := by
      have he' := congrArg GridCO.State.obligations hview
      exact he'
    rw [← he] at hm
    have hg := List.any_eq_false.mp hguard lease hm
    change Block.compatible lease.1 B = true
    simpa only [Bool.not_eq_true', Bool.not_eq_false] using hg
  have hc := hcompat
  have hadv : Block.Preceq (S_at p c E rho j x) (GridCO.advance (S_at p c E rho j x) B) := by
    rw [GridCO.growth_advance_eq]
    unfold GridCO.growth_advance
    split
    · exact block_preceq_refl _
    · next hn =>
      rcases Bool.or_eq_true_iff.mp hc with h | h
      · exact h
      · exact (hn h).elim
  rcases (fgsaAC_gate_write E rho j s x
      (wcg_gate_pre_joined (wcg_gate_enabled_of_result hsch ht hB)) ht).effects with hskip | hrun
  · obtain ⟨result, hsaved⟩ := hskip.1
    have hfresh := fgsa_gate_fresh E rho hsch ht
    change GridCO.savedGenuine (storeAt p c E rho j x).base s = some result at hsaved
    change GridCO.savedGenuine (storeAt p c E rho j x).base s = none at hfresh
    rw [hfresh] at hsaved
    cases hsaved
  · have hw := (hrun.accept B hraw' hguard').1
    change S_at p c E rho (j + 1) x = Gen.AC.normalizeOutput (F_at p c E rho j x)
      (GridCO.advance (S_at p c E rho j x) B) at hw
    have hn : Block.preceq (F_at p c E rho j x)
        (GridCO.advance (S_at p c E rho j x) B) = true :=
      block_preceq_trans (nestOK_stateBefore E rho j x) hadv
    rw [Gen.AC.normalizeOutput_def, ite_eq_left hn] at hw
    exact ⟨hw, hw ▸ hadv⟩

/-- WC plan §6.5; DC expiry, duties, delivery and reconciliation keep S or take this gate. -/
theorem wcg_outputStep [Fintype V] (hcausal : WCFinalityTargetEarlierStatement p c E rho) (ΔF :
  Time) (w : HealingWitness) (iStar : Nat) :
  ∀
  (_hvalid : V2.D.ExecutionValid E rho)
  (_hlinked : V2.D.Linked (fgsaFamilies p c).linked rho)
  (_hcstar : V2.D.CStar (fgsaFamilies p c).fresh rho)
  (_hnr : V2.D.NoRestart rho)
  (_hdelta : E.Δ = p.Δ)
  (_hroots : NamedRootCollisionFree p c E rho)
  (_hsync : Gen.V2.Duty.PartialSynchronyBy E rho (fgsaDelay E.Δ ΔF))
  (_hdeltaF : E.Δ ≤ ΔF)
  (_hfaultQ : Gen.Pure.FaultQ p.n (Gen.V2.Duty.faulty rho).card)
  (_haccountable : FinalitySlashableBound p c E rho)
  (_hpart : ∀ s, w.u + 1 ≤ s → SA.voteTime p.toParams s ≤ rho.horizon →
    (Gen.V2.Duty.faulty rho).card <
      (Gen.V2.Duty.awakeHonest E rho (SA.voteTime p.toParams s)).card)
  (_hstore : RStore p c E rho)
  (_hcumul : RStoreCumul p c E rho)
  (_hmono : RMono p c E rho)
  (_hactive : RActive p c E rho)
  (_hframe : RFrameExactNext p c E rho)
  (_hmeta : RFrameNext p c E rho)
  (_hrec : RRec p c E rho)
  (_hgeo : RGeo p c E rho)
  (_hcert : RCert p c E rho)
  (_hsrc : TSrc p c E rho)
  (_hlabel : LabelBound p c E rho)
  (_hqc : RQCOrigin p c E rho)
  (_hstrat : RStrat p c E rho)
  (_hnoslash : ∀ x ∈ rho.honest, EmittedRowsNoSlash p c E rho x)
  (_hemitted : ∀ j x r a e, HonestRowAt p c E rho j x r a →
    namedEntry a.payload.height_pair = some e →
    ∃ C B, actionSourceFG p c E rho x r = some (some C) ∧
      e = (hOf p.E p.cfg C, (derive p.E p.cfg C).T_h.root) ∧
      FGBlock.Preceq (derive p.E p.cfg C).T_h C ∧
      gateResult p c E rho x (r * p.R) = some (some B) ∧
      Block.Preceq (eraseFG C) B ∧ fastAt p c E rho x (r * p.R) (eraseFG C))
  (_htargets : ∀ i x row, row ∈ (storeAt p c E rho i x).base.obligations →
    Block.Preceq row.1 (storeAt p c E rho i x).base.stableRecord)
  (_hlease : ∀ i x row, row ∈ (storeAt p c E rho i x).base.obligations →
    ∃ j < i, ∃ s B, IsGateTick p c rho j x s ∧ gatePassedAt p c E rho j ∧
      gateResultAt p c E rho j = some (some B) ∧ Block.Preceq row.1 B ∧
      (row.1, row.2.1) ∈
      (let wcView := actView (clockPre p (storeAt p c E rho j x) (SA.gateTime p.toParams s));
        (wcView.blocks.filter (fun b => b != .genesis && Block.preceq b B)).flatMap
          (fun b => (@GridCO.admissionLevels GridCO.slowLeasePolicy
            p.toParams.engine p.n .root wcView s b).map (fun g => (b, g)))) ∧
      row.2.2 = SA.gateTime p.toParams s + SA.lifetime p.toParams ∧
      row.2.2 = SA.releaseTime p.toParams (s + p.k) ∧
      ∀ k w C, j < k → k < i → IsGateTick p c rho k x w →
        let pre := clockPre p (storeAt p c E rho k x) (SA.gateTime p.toParams w)
        GridCO.savedGenuine pre.base w = none →
        SA.Root.confirmationFrom p.toParams (eraseFG pre.fg.F) (actView pre) w = some C →
        (actView pre).obligations.any (fun r => !Block.compatible r.1 C) = false →
        (row.1, row.2.1) ∉ (let wcView := actView pre;
        (wcView.blocks.filter (fun b => b != .genesis && Block.preceq b C)).flatMap
          (fun b => (@GridCO.admissionLevels GridCO.slowLeasePolicy
            p.toParams.engine p.n .root wcView w b).map (fun g => (b, g)))))
  (_hfast : ∀ i x,
    ∀ s X, X ∈ (FGSA.fastWriteAt (storeAt p c E rho i x) s).getD [] →
      ∃ j < i, IsGateTick p c rho j x s ∧ gatePassedAt p c E rho j ∧
        ∃ B, gateResultAt p c E rho j = some (some B) ∧
          Block.Preceq X B ∧ fastAt p c E rho x s X)
  (_hdeadlines : ∀ i x,
    ∀ K g deadline, (K, g, deadline) ∈ (storeAt p c E rho i x).base.obligations →
      ∀ B, B ≠ .genesis → Block.Preceq B K →
        Gen.AC.Root.ProtectsUntil (storeAt p c E rho i x).base B g deadline)
  (_hheldRows : ∀ i x W, HeldAt p c E rho i x W → ∀ a ∈ chainRows W,
    ∃ (wire : RowWire p.n) (r : Nat), wire.toRow? = some a ∧
      wire.auth = .seat .fg a.signer ∧ ∃ k o t, k < i ∧
        rho.events[k]? = some (.deliver x o t) ∧
        ∀ z, RowSigner p c rho wire z → z ∈ rho.honest →
          HonestRowBefore p c E rho i z r wire ∧ p.actionTime r ≤ t)
  (_hscopeRows : ∀ D, RootBlockInRun p c E rho (eraseFG D) → ∀ a ∈ chainRows D,
    rho.seatOf (.base .fg) a.signer ∈ rho.honest → ∃ j r wire,
      HonestRowAt p c E rho j (rho.seatOf (.base .fg) a.signer) r wire ∧
      wire.toRow? = some a ∧ wire.auth = .seat .fg a.signer)
  (_hfinalHead : ∀ j z r a u, HonestRowAt p c E rho j z r a →
    RowSigner p c rho a z → a.toRow? = some u → ∀ fp,
    u.finality_pair = some fp → ∃ B, HeldAt p c E rho j z B ∧
      fp.height = (heightView p B).h_j ∧ fp.target = (heightView p B).J.root ∧
      TargetQCAt p.E B fp.height (heightView p B).J),
  WCSeed p c E rho w iStar → ∀ i, iStar ≤ i → i < rho.events.length →
    WCInv p c E rho w iStar i → ∀ e, rho.events[i]? = some e →
    ∀ x ∈ rho.honest,
      Block.Preceq (S_at p c E rho i x) (S_at p c E rho (i + 1) x) ∧
      (S_at p c E rho (i + 1) x = S_at p c E rho i x ∨
        ∃ s, IsGateTick p c rho i x s ∧ w.u < s ∧
          gateResultAt p c E rho i = some (some (S_at p c E rho (i + 1) x))) := by
  intro hvalid hlinked hcstar hnr hdelta hroots hsync hdeltaF
    hfaultQ haccountable hpart hstore hcumul hmono hactive hframe hmeta hrec hgeo hcert
    hsrc hlabel hqc hstrat hnoslash hemitted htargets hlease hfast hdeadlines hheldRows
    hscopeRows hfinalHead hs i hi hilen inv _e _he x hx
  have keep (heq : S_at p c E rho (i + 1) x = S_at p c E rho i x) :
      Block.Preceq (S_at p c E rho i x) (S_at p c E rho (i + 1) x) ∧
      (S_at p c E rho (i + 1) x = S_at p c E rho i x ∨
        ∃ s, IsGateTick p c rho i x s ∧ w.u < s ∧
          gateResultAt p c E rho i = some (some (S_at p c E rho (i + 1) x))) := by
    exact ⟨heq ▸ block_preceq_refl _, Or.inl heq⟩
  rcases fgsaAC_output_step E rho i x with hsame | ⟨s, ht⟩ | hrc | ⟨t, hr, _⟩
  · exact keep hsame
  · have hslabel := (wcg_gate_cut_iff hvalid.toScheduleWellFormed hs ht).mp hi
    obtain ⟨B, hB, hpass, _, _, _, hcompat⟩ := (wcg_gateResult hcausal) ΔF w iStar hvalid hlinked
      hcstar hnr hdelta hroots hsync hdeltaF
      hfaultQ haccountable hpart hstore hcumul hmono hactive hframe hmeta hrec hgeo hcert
      hsrc hlabel hqc hstrat hnoslash hemitted htargets hlease hfast hdeadlines hheldRows
      hscopeRows hfinalHead
      hs i x s hi hilen inv ht hslabel
    obtain ⟨heq, hmono⟩ := growthStepOutput_gate_output hvalid.toScheduleWellFormed ht hB hpass
      hcompat
    refine ⟨hmono, ?_⟩
    rw [GridCO.growth_advance_eq] at heq
    unfold GridCO.growth_advance at heq
    split at heq
    · exact Or.inl heq
    · exact Or.inr ⟨s, ht, hslabel, heq ▸ hB⟩
  · obtain ⟨o, t, B, he, _, _, hout⟩ := hrc
    have hbelow := (wcg_reconcileBound hcausal) ΔF w iStar hvalid hlinked hcstar hnr hdelta hroots
      hsync hdeltaF
      hfaultQ haccountable hpart hstore hcumul hmono hactive hframe hmeta hrec hgeo hcert
      hsrc hlabel hqc hstrat hnoslash hemitted htargets hlease hfast hdeadlines hheldRows
      hscopeRows hfinalHead hs i hi hilen inv x o t he x x hx hx
    change S_at p c E rho (i + 1) x = Gen.AC.normalizeOutput
      (F_at p c E rho (i + 1) x) (S_at p c E rho i x) at hout
    change Block.preceq (F_at p c E rho (i + 1) x) (S_at p c E rho i x) = true at hbelow
    rw [Gen.AC.normalizeOutput_def, ite_eq_left hbelow] at hout
    exact keep hout
  · exact (hnr i x t hr).elim

end AvailableChain.FGSA.Run



/-! WC plan §6.5; DC retrospective frame bounds use only earlier result labels. -/

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG KitFG Gen.Pure

variable {p : Params} {In V : Type} {c : AppCodec In} [DecidableEq V] [Fintype V]
    {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}

/-- WC plan §6.5; DC the next HEAD clock runs no gate. -/
private theorem growthStepTransferFrame_transfer_vote_clock (st : State p.n) (s : Slot) :
    FGSA.clock p st (SA.voteTime p.toParams (s + 1)) =
      clockPre p st (SA.voteTime p.toParams (s + 1)) := by
  have hn : isGateTime p (SA.voteTime p.toParams (s + 1)) ≠ true := by
    intro hh
    obtain ⟨r, hr⟩ := (isGateTime_iff p _).mp hh
    symm at hr
    change 4 * p.Δ * ((s + 1 : Nat) : Int) + p.Δ =
      4 * p.Δ * (r : Int) + 6 * p.Δ at hr
    push_cast at hr
    have hd := p.deltaPos
    rcases Nat.lt_or_ge r s with hrs | hsr
    · have hi : (r : Int) + 1 ≤ (s : Int) := by exact_mod_cast hrs
      nlinarith
    · have hi : (s : Int) ≤ (r : Int) := by exact_mod_cast hsr
      nlinarith
  change (if isGateTime p _ then _ else _) = _
  rw [ite_eq_right hn]

/-- WC plan §6.5; DC the earlier HEAD frame is bounded by the newly ordered result. -/
theorem wcg_retrospectiveFrame (ΔF : Time) (w : HealingWitness) (iStar : Nat) :
  ∀
  (_hvalid : V2.D.ExecutionValid E rho)
  (_hlinked : V2.D.Linked (fgsaFamilies p c).linked rho)
  (_hcstar : V2.D.CStar (fgsaFamilies p c).fresh rho)
  (_hnr : V2.D.NoRestart rho)
  (_hdelta : E.Δ = p.Δ)
  (_hroots : NamedRootCollisionFree p c E rho)
  (_hsync : Gen.V2.Duty.PartialSynchronyBy E rho (fgsaDelay E.Δ ΔF))
  (_hdeltaF : E.Δ ≤ ΔF)
  (_hfaultQ : Gen.Pure.FaultQ p.n (Gen.V2.Duty.faulty rho).card)
  (_haccountable : FinalitySlashableBound p c E rho)
  (_hpart : ∀ s, w.u + 1 ≤ s → SA.voteTime p.toParams s ≤ rho.horizon →
    (Gen.V2.Duty.faulty rho).card <
      (Gen.V2.Duty.awakeHonest E rho (SA.voteTime p.toParams s)).card)
  (_hstore : RStore p c E rho)
  (_hcumul : RStoreCumul p c E rho)
  (_hmono : RMono p c E rho)
  (_hactive : RActive p c E rho)
  (_hframe : RFrameExactNext p c E rho)
  (_hmeta : RFrameNext p c E rho)
  (_hrec : RRec p c E rho)
  (_hgeo : RGeo p c E rho)
  (_hcert : RCert p c E rho)
  (_hsrc : TSrc p c E rho)
  (_hlabel : LabelBound p c E rho)
  (_hqc : RQCOrigin p c E rho)
  (_hstrat : RStrat p c E rho)
  (_hnoslash : ∀ x ∈ rho.honest, EmittedRowsNoSlash p c E rho x)
  (_hemitted : ∀ j x r a e, HonestRowAt p c E rho j x r a →
    namedEntry a.payload.height_pair = some e →
    ∃ C B, actionSourceFG p c E rho x r = some (some C) ∧
      e = (hOf p.E p.cfg C, (derive p.E p.cfg C).T_h.root) ∧
      FGBlock.Preceq (derive p.E p.cfg C).T_h C ∧
      gateResult p c E rho x (r * p.R) = some (some B) ∧
      Block.Preceq (eraseFG C) B ∧ fastAt p c E rho x (r * p.R) (eraseFG C))
  (_htargets : ∀ i x row, row ∈ (storeAt p c E rho i x).base.obligations →
    Block.Preceq row.1 (storeAt p c E rho i x).base.stableRecord)
  (_hlease : ∀ i x row, row ∈ (storeAt p c E rho i x).base.obligations →
    ∃ j < i, ∃ s B, IsGateTick p c rho j x s ∧ gatePassedAt p c E rho j ∧
      gateResultAt p c E rho j = some (some B) ∧ Block.Preceq row.1 B ∧
      (row.1, row.2.1) ∈
      (let wcView := actView (clockPre p (storeAt p c E rho j x) (SA.gateTime p.toParams s));
        (wcView.blocks.filter (fun b => b != .genesis && Block.preceq b B)).flatMap
          (fun b => (@GridCO.admissionLevels GridCO.slowLeasePolicy
            p.toParams.engine p.n .root wcView s b).map (fun g => (b, g)))) ∧
      row.2.2 = SA.gateTime p.toParams s + SA.lifetime p.toParams ∧
      row.2.2 = SA.releaseTime p.toParams (s + p.k) ∧
      ∀ k w C, j < k → k < i → IsGateTick p c rho k x w →
        let pre := clockPre p (storeAt p c E rho k x) (SA.gateTime p.toParams w)
        GridCO.savedGenuine pre.base w = none →
        SA.Root.confirmationFrom p.toParams (eraseFG pre.fg.F) (actView pre) w = some C →
        (actView pre).obligations.any (fun r => !Block.compatible r.1 C) = false →
        (row.1, row.2.1) ∉ (let wcView := actView pre;
        (wcView.blocks.filter (fun b => b != .genesis && Block.preceq b C)).flatMap
          (fun b => (@GridCO.admissionLevels GridCO.slowLeasePolicy
            p.toParams.engine p.n .root wcView w b).map (fun g => (b, g)))))
  (_hfast : ∀ i x,
    ∀ s X, X ∈ (FGSA.fastWriteAt (storeAt p c E rho i x) s).getD [] →
      ∃ j < i, IsGateTick p c rho j x s ∧ gatePassedAt p c E rho j ∧
        ∃ B, gateResultAt p c E rho j = some (some B) ∧
          Block.Preceq X B ∧ fastAt p c E rho x s X)
  (_hdeadlines : ∀ i x,
    ∀ K g deadline, (K, g, deadline) ∈ (storeAt p c E rho i x).base.obligations →
      ∀ B, B ≠ .genesis → Block.Preceq B K →
        Gen.AC.Root.ProtectsUntil (storeAt p c E rho i x).base B g deadline)
  (_hheldRows : ∀ i x W, HeldAt p c E rho i x W → ∀ a ∈ chainRows W,
    ∃ (wire : RowWire p.n) (r : Nat), wire.toRow? = some a ∧
      wire.auth = .seat .fg a.signer ∧ ∃ k o t, k < i ∧
        rho.events[k]? = some (.deliver x o t) ∧
        ∀ z, RowSigner p c rho wire z → z ∈ rho.honest →
          HonestRowBefore p c E rho i z r wire ∧ p.actionTime r ≤ t)
  (_hscopeRows : ∀ D, RootBlockInRun p c E rho (eraseFG D) → ∀ a ∈ chainRows D,
    rho.seatOf (.base .fg) a.signer ∈ rho.honest → ∃ j r wire,
      HonestRowAt p c E rho j (rho.seatOf (.base .fg) a.signer) r wire ∧
      wire.toRow? = some a ∧ wire.auth = .seat .fg a.signer)
  (_hfinalHead : ∀ j z r a u, HonestRowAt p c E rho j z r a →
    RowSigner p c rho a z → a.toRow? = some u → ∀ fp,
    u.finality_pair = some fp → ∃ B, HeldAt p c E rho j z B ∧
      fp.height = (heightView p B).h_j ∧ fp.target = (heightView p B).J.root ∧
      TargetQCAt p.E B fp.height (heightView p B).J),
  WCSeed p c E rho w iStar → ∀ i k x y s (Bfg : FGBlock (Fin p.n)),
    iStar ≤ i → i < rho.events.length → WCInv p c E rho w iStar i →
    IsGateTick p c rho i x s → w.u < s → k < i →
    rho.events[k]? = some (.tick y (SA.voteTime p.toParams (s + 1))) →
    Block.Preceq w.QStar (eraseFG Bfg) →
    (∀ j z r C, WCResult p c E rho w iStar i j z r C → r < s →
      Block.Preceq C (eraseFG Bfg)) →
    let st := FGSA.clock p (storeAt p c E rho k y) (SA.voteTime p.toParams (s + 1))
    WCFrameLiveBelow p st (.head (s + 1)) Bfg (voterBlocks p st (s + 1)) := by
  intro hvalid hlinked hcstar hnr hdelta hroots hsync hdeltaF
    hfaultQ haccountable hpart hstore hcumul hmono hactive hframe hmeta hrec hgeo hcert
    hsrc hlabel hqc hstrat hnoslash hemitted htargets hlease hfast hdeadlines hheldRows
    hscopeRows hfinalHead hs i k x y s Bfg _hi _hilen inv _ht hslabel hki hk hQB hord st
  have hy := hvalid.honest_only _ (List.mem_of_getElem? hk)
  have hsch := hvalid.toScheduleWellFormed
  have hafter : iStar ≤ k := by
    by_contra hn
    have hlt : k < afterTicksIdx rho (SA.gateTime p.toParams w.u) :=
      hs.cut ▸ (Nat.lt_of_not_ge hn)
    have hm : V2.Event.tick y (SA.voteTime p.toParams (s + 1)) ∈
        rho.events.filter (cutPred (SA.gateTime p.toParams w.u)) := by
      rw [V2.D.Engine.filter_eq_take hsch _ (by
        intro e f hle hf
        exact decide_eq_true (hle.trans (of_decide_eq_true hf)))]
      apply List.mem_of_getElem? (i := k)
      change (rho.events.take (afterTicksIdx rho (SA.gateTime p.toParams w.u)))[k]? = _
      rw [List.getElem?_take_of_lt hlt]
      exact hk
    have hkey := of_decide_eq_true (List.mem_filter.mp hm).2
    have ht : SA.voteTime p.toParams (s + 1) ≤ SA.gateTime p.toParams w.u := by
      rcases Prod.Lex.toLex_le_toLex.mp hkey with h | ⟨h, _⟩
      · exact h.le
      · exact h.le
    change 4 * p.Δ * ((s + 1 : Nat) : Int) + p.Δ ≤
      4 * p.Δ * (w.u : Int) + 6 * p.Δ at ht
    have hc : (w.u : Int) + 1 ≤ s := by exact_mod_cast hslabel
    push_cast at ht
    nlinarith [p.deltaPos]
  have hstate : Block.Preceq (S_at p c E rho k y) (eraseFG Bfg) := by
    rcases (wcg_outputHistoryAt hs inv hafter (Nat.le_of_lt hki) hy).origin with
      h | ⟨j, z, r, C, hr, hSC⟩
    · exact block_preceq_trans h hQB
    · have ht : SA.gateTime p.toParams r ≤ SA.voteTime p.toParams (s + 1) := by
        obtain ⟨hjl, hje⟩ := List.getElem?_eq_some_iff.mp hr.event
        obtain ⟨hkl, hke⟩ := List.getElem?_eq_some_iff.mp hk
        have hh := (List.pairwise_iff_getElem.mp hsch.sorted) j k hjl hkl hr.completed
        rw [hje, hke] at hh
        exact V2.D.Engine.time_le_of_key_le _ _ hh
      have hrs : r < s := by
        change 4 * p.Δ * (r : Int) + 6 * p.Δ ≤
          4 * p.Δ * ((s + 1 : Nat) : Int) + p.Δ at ht
        push_cast at ht
        have hh : (r : Int) < s := by nlinarith [p.deltaPos]
        exact Int.ofNat_lt.mp hh
      exact block_preceq_trans hSC (hord j z r C
        { hr with completed := hr.completed.trans hki } hrs)
  have hhigh : WCUsableHighSourcesBelow p c E rho w k y st (eraseFG Bfg) := by
    refine ⟨hy, ?_⟩
    intro a _ha j z r wire e K hj hrow _hdecode hname hhigh hK
    by_cases hpre : j < iStar
    · obtain ⟨K', G, hK', _, _, _, _, hbelow⟩ :=
        hs.highSources j z r wire e hpre hrow hname hhigh
      have heq : K = K' := Option.some.inj (Option.some.inj (hK.symm.trans hK'))
      exact block_preceq_trans (heq ▸ hbelow) hQB
    · obtain ⟨C, hr, hKC⟩ := inv.suffixSources j z r K (Nat.le_of_not_gt hpre)
        (hj.trans hki) hrow.1 hrow.2.1 hK
      have hbound := (hlabel k y z r wire _ hy hk ⟨j, hj, hrow⟩).2.2 (s + 1)
        (Nat.succ_le_succ (Nat.zero_le s)) (Or.inr rfl)
      have hrs : r * p.R < s := by
        simp only [Slot] at hbound hslabel ⊢
        omega
      exact block_preceq_trans hKC (hord j z (r * p.R) C hr hrs)
  obtain ⟨W, hW, hh, hmem⟩ := inv.carrier
  have hWst : W ∈ st.fg.TF := by
    change W ∈ (FGSA.clock p _ _).fg.TF
    rw [clock_fg]
    exact hmem k y hafter (Nat.le_of_lt hki) hy
  have hd : WCDutyInput p c E rho k y (.head (s + 1)) st :=
    ⟨(List.getElem?_eq_some_iff.mp hk).1, _, hk, Or.inr (Or.inl ⟨s + 1, rfl, rfl, rfl⟩)⟩
  have htarget : ∀ row ∈ st.base.obligations, st.base.now < row.2.2 →
      Block.Preceq row.1 (eraseFG Bfg) := by
    intro row hr _
    change row ∈ (FGSA.clock p _ _).base.obligations at hr
    rw [growthStepTransferFrame_transfer_vote_clock] at hr
    exact block_preceq_trans (htargets k y row
      ((clockPre_obligations_sublist p _ _).subset hr)) hstate
  exact wcg_seededFrameLive hvalid hlinked hcstar hnr hdelta hroots hsync hdeltaF
    hfaultQ haccountable hpart hstore hcumul hmono hactive hframe hmeta hrec hgeo hcert
    hsrc hlabel hqc hstrat hnoslash hemitted htargets hlease hfast hdeadlines hheldRows
    hscopeRows hfinalHead hs k y (.head (s + 1)) st W Bfg hd hy hafter
    hWst hW hh hQB hhigh htarget (voterBlocks p st (s + 1))
    ⟨Or.inl ⟨s + 1, rfl, rfl⟩⟩ (fun _ h => (Finset.mem_filter.mp (Finset.mem_filter.mp h).1).1)

end AvailableChain.FGSA.Run



/-! WC plan §6.5; DC retrospective paths retain the original per-body receipt times. -/

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG KitFG Gen.Pure

variable (p : Params) {In V : Type} (c : AppCodec In) [DecidableEq V]
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) {ΔF : Time}

/-- WC plan §6.5; DC preserve named receipt provenance and the strict freeze cutoff. -/
private theorem growthStepTransferReceipts_transfer_decode {o : Obj p} {b : Block} (h :
  blockOf? p o = some b) :
    ∃ u N, N.erase = b ∧ (toWire p o).decode = some (.block u N) := by
  rw [growth_blockOf_eq] at h
  unfold growth_blockOf at h
  cases hd : (toWire p o).decode with
  | none => simp only [hd, reduceCtorEq] at h
  | some m =>
    cases m <;> simp only [hd, reduceCtorEq, Option.some.injEq] at h
    exact ⟨_, _, h, rfl⟩

/-- WC plan §6.5; DC preserve named receipt provenance and the strict freeze cutoff. -/
private theorem growthStepTransferReceipts_transfer_source_acceptances
    (hroots : NamedRootCollisionFree p c E rho)
    (hsch : V2.D.ScheduleWellFormed E rho) (hDelta : E.Δ = p.Δ)
    {i : Nat} {x : V} {s : Slot} {K B : Block}
    (hK : K ∈ (storeAt p c E rho i x).base.blocks)
    (hstamp : GridCO.stampBlock (storeAt p c E rho i x).base K <
      SA.earlyTime p.toParams s)
    (hBK : Block.Preceq B K) :
    ∀ b, Block.Preceq b B → b ≠ .genesis →
      ∃ l < i, ∃ t o u N, N.erase = b ∧
        (toWire p o).decode = some (.block u N) ∧
        V2.D.Run.acceptsAt E rho l x o t ∧ 0 ≤ t ∧ t < SA.earlyTime p.toParams s := by
  intro b hb hne
  have hbK := block_preceq_trans hb hBK
  have hKg : K ≠ .genesis := by
    intro he
    rw [he] at hbK
    exact hne (Gen.Pure.block_preceq_antisymm hbK (block_genesis_preceq b))
  have hpub : V2.PublicTime E (SA.earlyTime p.toParams s) := by
    refine ⟨4 * s + 2, ?_⟩
    rw [hDelta]
    change 4 * p.Δ * (s : Int) + 2 * p.Δ = _
    push_cast
    ring
  have hz : 0 ≤ SA.earlyTime p.toParams s := by
    change 0 ≤ 4 * p.Δ * (s : Int) + 2 * p.Δ
    have hd := p.deltaPos
    positivity
  obtain ⟨j, hji, t, o, ho, ha, ht⟩ :=
    fgsa_block_accepted_before E rho hsch i x K _ hKg hpub hz hK hstamp
  obtain ⟨u, N, heN, hdec⟩ := growthStepTransferReceipts_transfer_decode p ho
  have hpost := ha.2.2
  change processedS p (V2.D.Run.stateBefore E rho (j + 1) x).st o = true at hpost
  dsimp only [processedS] at hpost
  rw [hdec] at hpost
  obtain ⟨Kfg, hKfg, hroot⟩ := of_decide_eq_true hpost
  obtain ⟨envelope, hdelivery, _⟩ := ha.1
  have hx := hsch.honest_only _ (List.mem_of_getElem? hdelivery)
  have heK : eraseFG Kfg = K := rootBlockInRun_eq E rho hroots
    (rootScope_store hx hKfg) (rootBlockInRun_held E rho hx i hK)
    (by simpa only [← named_erase_root, heN] using (eraseFG_root Kfg).trans hroot)
  have hc := (storeBundle_stateBefore E rho (j + 1) x).cstore
  obtain ⟨A, hA, heA⟩ := eraseFG_ancestor_mem hc.fg.closed hKfg (heK ▸ hbK)
  have hbm := (hc.baseTree b).mpr ⟨A, hA, heA⟩
  rw [← (storeBundle_stateBefore E rho (j + 1) x).«meta».stampKeys] at hbm
  obtain ⟨⟨b', stamp⟩, hmem, he⟩ := List.mem_map.mp hbm
  dsimp only at he
  subst b'
  rcases fgsa_block_stamp_source E rho (j + 1) x b stamp hmem with hg | ⟨l, hl, t', o', ho', ha', _⟩
  · exact (hne hg.1).elim
  obtain ⟨u', M, heM, hd'⟩ := growthStepTransferReceipts_transfer_decode p ho'
  obtain ⟨parent, hd, _⟩ := ha.1
  obtain ⟨parent', hd'', _⟩ := ha'.1
  refine ⟨l, by omega, t', o', u', M, heM, hd', ha',
    (hsch.in_horizon _ (List.mem_of_getElem? hd'')).1, ?_⟩
  have htime : t' ≤ t := by
    by_cases heq : l = j
    · subst l
      rw [hd] at hd''
      cases hd''
      exact le_rfl
    · obtain ⟨hll, hle⟩ := List.getElem?_eq_some_iff.mp hd''
      obtain ⟨hjl, hje⟩ := List.getElem?_eq_some_iff.mp hd
      have hkey := (List.pairwise_iff_getElem.mp hsch.sorted) l j hll hjl (by omega)
      rw [hle, hje] at hkey
      change toLex (t', (2 : Nat)) ≤ toLex (t, 2) at hkey
      rcases Prod.Lex.toLex_le_toLex.mp hkey with hlt | ⟨heq, _⟩
      · exact le_of_lt hlt
      · exact le_of_eq heq
  exact htime.trans_lt ht

/-- WC plan §6.5; DC preserve named receipt provenance and the strict freeze cutoff. -/
private theorem growthStepTransferReceipts_transfer_coverage
    (hE : V2.D.ExecutionValid E rho) (hDelta : E.Δ = p.Δ)
    (hsync : Gen.V2.Duty.PartialSynchronyBy E rho (fgsaDelay E.Δ ΔF))
    {i : Nat} {x y : V} {s : Slot} {B : Block}
    (hx : x ∈ rho.honest) (hcut : SA.freezeTime p.toParams s ≤ rho.horizon)
    (hGST : E.t_GST ≤ SA.voteTime p.toParams s)
    (hpath : ∀ b, Block.Preceq b B → b ≠ .genesis →
      ∃ l < i, ∃ t o u N, N.erase = b ∧
        (toWire p o).decode = some (.block u N) ∧
        V2.D.Run.acceptsAt E rho l x o t ∧ 0 ≤ t ∧ t < SA.earlyTime p.toParams s)
    (hF : ∀ j, j ≤ V2.D.Run.idxBefore rho (SA.freezeTime p.toParams s) →
      Block.Preceq (F_at p c E rho j y) B) :
    ∃ required,
      ReceiptCoveragePremises E rho (fun t => max t E.t_GST + p.Δ) rho.horizon
        (SA.freezeTime p.toParams s) 0 y B required
        (fun L d => L = B ∧ d = SA.freezeTime p.toParams s) := by
  let required := fun o t => 0 ≤ t ∧ t < SA.earlyTime p.toParams s ∧
    ∃ l < i, V2.D.Run.acceptsAt E rho l x o t ∧
      ∃ b, blockOf? p o = some b ∧ Block.Preceq b B
  refine ⟨required, ?_, ?_, ?_, ?_⟩
  · simpa only [hDelta] using Gen.V2.Duty.deliveryWithinOn_of_partialSynchronyBy E rho hsync
          (fun o => ¬ isRowObject o) E.Δ (fgsaDelay_nonrow E.Δ _)
  · intro o t hr
    obtain ⟨_, _, l, _, ha, b, hb, _⟩ := hr
    obtain ⟨parent, he, hh⟩ := ha.1
    refine ⟨Or.inr ⟨x, hx, l, ha⟩,
      handles_wellFormed p c _ parent o hh (hE.wire l x parent t he), ?_⟩
    intro r a K hv
    have hn : blockOf? p o = none := by
      change (match (toWire p o).decode with | some (.block _ N) => some N.erase | _ => none) = _
      rw [hv]
    rw [hn] at hb
    contradiction
  · intro j _ hj
    exact block_compatible_of_common (block_preceq_refl B) (hF j hj)
  · refine ⟨fun _ _ hab => add_le_add (max_le_max hab le_rfl) le_rfl,
      hcut, le_rfl, Nat.zero_le _, ?_, ?_, ?_⟩
    · intro o t hr
      refine ⟨Nat.zero_le _, hr.1,
        (le_max_left _ _).trans_lt (lt_add_of_pos_right _ p.deltaPos), ?_⟩
      have ht := hr.2.1
      change t < 4 * p.Δ * (s : Int) + 2 * p.Δ at ht
      have hg : E.t_GST < 4 * p.Δ * (s : Int) + 2 * p.Δ := by
        change E.t_GST ≤ 4 * p.Δ * (s : Int) + p.Δ at hGST
        linarith [p.deltaPos]
      have hm := max_lt ht hg
      change max t E.t_GST + p.Δ ≤ 4 * p.Δ * (s : Int) + 3 * p.Δ
      linarith
    · rintro K d ⟨hKB, hdD⟩
      subst K d
      refine ⟨block_preceq_refl B, le_rfl, ?_⟩
      intro b hb hne
      obtain ⟨l, hl, t, o, u, N, heN, hd, ha, hz, ht⟩ := hpath b hb hne
      have ho : blockOf? p o = some b := by
        change (match (toWire p o).decode with | some (.block _ N) => some N.erase | _ => none) = _
        rw [hd]
        exact congrArg some heN
      refine ⟨o, t, u, N, heN, ⟨hz, ht, l, hl, ha, b, ho, hb⟩, hd, ?_⟩
      change t < 4 * p.Δ * (s : Int) + 2 * p.Δ at ht
      have hg : E.t_GST < 4 * p.Δ * (s : Int) + 2 * p.Δ := by
        change E.t_GST ≤ 4 * p.Δ * (s : Int) + p.Δ at hGST
        linarith [p.deltaPos]
      have hm := max_lt ht hg
      change max t E.t_GST + p.Δ ≤ 4 * p.Δ * (s : Int) + 3 * p.Δ
      linarith
    · intro o t u N hr hd
      obtain ⟨_, _, l, hl, ha, b', hb', hBK⟩ := hr
      have hb : blockOf? p o = some N.erase := by
        change (match (toWire p o).decode with | some (.block _ N) => some N.erase | _ => none) = _
        rw [hd]
      have heq := Option.some.inj (hb'.symm.trans hb)
      subst b'
      exact ⟨B, SA.freezeTime p.toParams s, ⟨rfl, rfl⟩, hBK⟩

/-- WC plan §6.5; DC preserve named receipt provenance and the strict freeze cutoff. -/
private theorem growthStepTransferReceipts_transfer_read_stamp (hsch : V2.D.ScheduleWellFormed
  E rho)
    (y : V) (D : Time) (hD : 0 < D) (b : Block)
    (hb : b ∈ (V2.D.Run.stateBeforeTime E rho D y).st.base.blocks) :
    GridCO.stampBlock (V2.D.Run.stateBeforeTime E rho D y).st.base b < D := by
  rw [← Gen.V2.Duty.stateBefore_idxBefore E rho D hsch] at hb ⊢
  have hkeys : b ∈
      ((V2.D.Run.stateBefore E rho (V2.D.Run.idxBefore rho D) y).st.base.blockStamp.map
        Prod.fst) := by
    rw [(storeBundle_stateBefore E rho (V2.D.Run.idxBefore rho D) y).«meta».stampKeys]
    exact hb
  change (((V2.D.Run.stateBefore E rho (V2.D.Run.idxBefore rho D) y).st.base.blockStamp.find? _).map
    Prod.snd).getD _ < D
  cases he : (V2.D.Run.stateBefore E rho (V2.D.Run.idxBefore rho D) y).st.base.blockStamp.find?
      (fun row => row.1 == b) with
  | none =>
    obtain ⟨row, hr, hh⟩ := List.mem_map.mp hkeys
    have hn := List.find?_eq_none.mp he row hr
    rw [hh, beq_self_eq_true] at hn
    contradiction
  | some row =>
    change row.2 < D
    rcases fgsa_block_stamp_source E rho _ y row.1 row.2 (List.mem_of_find?_eq_some he) with
      hg | ⟨l, hl, t, o, _, ha, hs⟩
    · rw [hg.2]; exact hD
    · obtain ⟨parent, hd, _⟩ := ha.1
      have ht := (Gen.V2.Duty.index_lt_idxBefore_iff hsch hd D).mp hl
      have hc := stateBefore_now_le_event_retained (fgsaClock p c)
        (fgsa_hrestore_now_retained p c) E rho hsch hd y
      rw [fgsa_clock_now p c (V2.D.Run.stateBefore E rho l y)] at hc
      rw [hs]
      exact hc.trans_lt ht

/-- WC plan §6.5; DC preserve named receipt provenance and the strict freeze cutoff. -/
private theorem growthStepTransferReceipts_transfer_stamp_kept {α : Type} [BEq α] [LawfulBEq α]
    {xs ys : List (α × Time)} (hp : xs <+: ys) (a : α)
    (hm : a ∈ xs.map Prod.fst) :
    ys.find? (fun row => row.1 == a) = xs.find? (fun row => row.1 == a) := by
  obtain ⟨tail, he⟩ := hp
  rw [← he, List.find?_append]
  cases hf : xs.find? (fun row => row.1 == a) with
  | none =>
    obtain ⟨row, hr, hh⟩ := List.mem_map.mp hm
    have hn := List.find?_eq_none.mp hf row hr
    rw [hh, beq_self_eq_true] at hn
    contradiction
  | some row => rfl

/-- WC plan §6.5; DC each support path is retained at the next HEAD with its freeze stamps. -/
private theorem growthStepTransferReceipts_prefreeze_path
    (hvalid : V2.D.ExecutionValid E rho) (hnr : V2.D.NoRestart rho) (hdelta : E.Δ = p.Δ)
    (hroots : NamedRootCollisionFree p c E rho)
    (hsync : Gen.V2.Duty.PartialSynchronyBy E rho (fgsaDelay E.Δ ΔF))
    (hcumul : RStoreCumul p c E rho) (hmono : RMono p c E rho)
    {i k : Nat} {x y : V} {s : Slot} {K : Block} (hx : x ∈ rho.honest)
    (hk : rho.events[k]? = some (.tick y (SA.voteTime p.toParams (s + 1))))
    (hGST : E.t_GST ≤ SA.voteTime p.toParams s)
    (hcut : SA.freezeTime p.toParams s ≤ rho.horizon)
    (hK : K ∈ (storeAt p c E rho i x).base.blocks)
    (hstamp : GridCO.stampBlock (storeAt p c E rho i x).base K < SA.earlyTime p.toParams s)
    (hFK : Block.Preceq (F_at p c E rho k y) K) :
    let st := FGSA.clock p (storeAt p c E rho k y) (SA.voteTime p.toParams (s + 1))
    ∃ Kfg : FGBlock (Fin p.n), eraseFG Kfg = K ∧
      ∀ A : FGBlock (Fin p.n), FGBlock.Preceq A Kfg → A ∈ st.fg.TF ∧
        GridCO.stampBlock st.base (eraseFG A) < SA.freezeTime p.toParams s := by
  intro st
  have hsch := hvalid.toScheduleWellFormed
  have hy := hvalid.honest_only _ (List.mem_of_getElem? hk)
  let D := SA.freezeTime p.toParams s
  let j := V2.D.Run.idxBefore rho D
  have hjk : j ≤ k := by
    by_contra hn
    have ht := (Gen.V2.Duty.index_lt_idxBefore_iff hsch hk D).mp (Nat.lt_of_not_ge hn)
    change 4 * p.Δ * ((s + 1 : Nat) : Int) + p.Δ <
      4 * p.Δ * (s : Int) + 3 * p.Δ at ht
    push_cast at ht
    nlinarith [p.deltaPos]
  have hF : ∀ l, l ≤ j → Block.Preceq (F_at p c E rho l y) K := by
    intro l hl
    exact block_preceq_trans (eraseFG_preceq (hmono hnr l k y hy (hl.trans hjk)).1) hFK
  have haccept := growthStepTransferReceipts_transfer_source_acceptances p c E rho hroots hsch
    hdelta hK hstamp
    (block_preceq_refl K)
  obtain ⟨required, hcov⟩ := growthStepTransferReceipts_transfer_coverage p c E rho hvalid
    hdelta hsync hx hcut hGST
    haccept hF
  have hpath : ∀ b, Block.Preceq b K →
      b ∈ (actView (V2.D.Run.stateBeforeTime E rho D y).st).blocks := by
    apply fgsa_active_path_of_coverage (hroots := hroots) E rho hvalid hnr hdelta
      (fun t => max t E.t_GST + p.Δ) rho.horizon D 0 y K required
      (fun L d => L = K ∧ d = D) hy hcov ⟨rfl, rfl⟩
    have hh := hF j le_rfl
    change Block.Preceq (eraseFG (V2.D.Run.stateBefore E rho (V2.D.Run.idxBefore rho D)
      y).st.fg.F) K at hh
    rw [Gen.V2.Duty.stateBefore_idxBefore E rho D hsch] at hh
    exact hh
  have hklen : k ≤ rho.events.length := Nat.le_of_lt (List.getElem?_eq_some_iff.mp hk).1
  have hc := hcumul hnr j k y hy hjk hklen
  have hread : storeAt p c E rho j y = (V2.D.Run.stateBeforeTime E rho D y).st := by
    change (V2.D.Run.stateBefore E rho (V2.D.Run.idxBefore rho D) y).st = _
    rw [Gen.V2.Duty.stateBefore_idxBefore E rho D hsch]
  have hKmem := ((actView_blocks _ K).mp (hpath K (block_preceq_refl K))).1
  obtain ⟨Kfg, hKfg, he⟩ := ((storeBundle_stateBeforeTime E rho D y).cstore.baseTree K).mp hKmem
  refine ⟨Kfg, he, ?_⟩
  intro A hA
  have hAm := KitFG.ancestor_closed_of_parent_closed _
    (storeBundle_stateBeforeTime E rho D y).cstore.fg.closed Kfg hKfg A hA
  have hAb := ((storeBundle_stateBeforeTime E rho D y).cstore.baseTree (eraseFG A)).mpr
    ⟨A, hAm, rfl⟩
  have hAstamp := growthStepTransferReceipts_transfer_read_stamp p c E rho hsch y D (by
    change 0 < 4 * p.Δ * (s : Int) + 3 * p.Δ
    have hd := p.deltaPos
    positivity) (eraseFG A) hAb
  rw [← hread] at hAm hAb hAstamp
  have hkeys : eraseFG A ∈ (storeAt p c E rho j y).base.blockStamp.map Prod.fst := by
    change eraseFG A ∈ (V2.D.Run.stateBefore E rho j y).st.base.blockStamp.map Prod.fst
    rw [(storeBundle_stateBefore E rho j y).«meta».stampKeys]
    exact hAb
  constructor
  · change A ∈ (FGSA.clock p (storeAt p c E rho k y) _).fg.TF
    rw [(clock_cumulative p _ _).1]
    exact hc.1 hAm
  · have heq := growthStepTransferReceipts_transfer_stamp_kept hc.2.2.1 (eraseFG A) hkeys
    change (((FGSA.clock p (storeAt p c E rho k y) _).base.blockStamp.find? _).map
      Prod.snd).getD _ < D
    rw [(clock_cumulative p _ _).2.2.1, heq]
    rw [GridCO.growth_stampBlock_eq] at hAstamp
    unfold GridCO.growth_stampBlock at hAstamp
    cases hfind : (storeAt p c E rho j y).base.blockStamp.find?
        (fun row => row.1 == eraseFG A) with
    | none =>
      obtain ⟨row, hr, hh⟩ := List.mem_map.mp hkeys
      have hn := List.find?_eq_none.mp hfind row hr
      rw [hh, beq_self_eq_true] at hn
      contradiction
    | some row => simpa only [hfind, Option.map_some, Option.getD_some] using hAstamp

/-- WC plan §6.5; DC every support path keeps its actual frozen receipt evidence. -/
theorem wcg_retrospectivePaths [Fintype V] (ΔF : Time) (w : HealingWitness) (iStar : Nat) :
  ∀
  (_hvalid : V2.D.ExecutionValid E rho)
  (_hlinked : V2.D.Linked (fgsaFamilies p c).linked rho)
  (_hcstar : V2.D.CStar (fgsaFamilies p c).fresh rho)
  (_hnr : V2.D.NoRestart rho)
  (_hdelta : E.Δ = p.Δ)
  (_hroots : NamedRootCollisionFree p c E rho)
  (_hsync : Gen.V2.Duty.PartialSynchronyBy E rho (fgsaDelay E.Δ ΔF))
  (_hdeltaF : E.Δ ≤ ΔF)
  (_hfaultQ : Gen.Pure.FaultQ p.n (Gen.V2.Duty.faulty rho).card)
  (_haccountable : FinalitySlashableBound p c E rho)
  (_hpart : ∀ s, w.u + 1 ≤ s → SA.voteTime p.toParams s ≤ rho.horizon →
    (Gen.V2.Duty.faulty rho).card <
      (Gen.V2.Duty.awakeHonest E rho (SA.voteTime p.toParams s)).card)
  (_hstore : RStore p c E rho)
  (_hcumul : RStoreCumul p c E rho)
  (_hmono : RMono p c E rho)
  (_hactive : RActive p c E rho)
  (_hframe : RFrameExactNext p c E rho)
  (_hmeta : RFrameNext p c E rho)
  (_hrec : RRec p c E rho)
  (_hgeo : RGeo p c E rho)
  (_hcert : RCert p c E rho)
  (_hsrc : TSrc p c E rho)
  (_hlabel : LabelBound p c E rho)
  (_hqc : RQCOrigin p c E rho)
  (_hstrat : RStrat p c E rho)
  (_hnoslash : ∀ x ∈ rho.honest, EmittedRowsNoSlash p c E rho x)
  (_hemitted : ∀ j x r a e, HonestRowAt p c E rho j x r a →
    namedEntry a.payload.height_pair = some e →
    ∃ C B, actionSourceFG p c E rho x r = some (some C) ∧
      e = (hOf p.E p.cfg C, (derive p.E p.cfg C).T_h.root) ∧
      FGBlock.Preceq (derive p.E p.cfg C).T_h C ∧
      gateResult p c E rho x (r * p.R) = some (some B) ∧
      Block.Preceq (eraseFG C) B ∧ fastAt p c E rho x (r * p.R) (eraseFG C))
  (_htargets : ∀ i x row, row ∈ (storeAt p c E rho i x).base.obligations →
    Block.Preceq row.1 (storeAt p c E rho i x).base.stableRecord)
  (_hlease : ∀ i x row, row ∈ (storeAt p c E rho i x).base.obligations →
    ∃ j < i, ∃ s B, IsGateTick p c rho j x s ∧ gatePassedAt p c E rho j ∧
      gateResultAt p c E rho j = some (some B) ∧ Block.Preceq row.1 B ∧
      (row.1, row.2.1) ∈
      (let wcView := actView (clockPre p (storeAt p c E rho j x) (SA.gateTime p.toParams s));
        (wcView.blocks.filter (fun b => b != .genesis && Block.preceq b B)).flatMap
          (fun b => (@GridCO.admissionLevels GridCO.slowLeasePolicy
            p.toParams.engine p.n .root wcView s b).map (fun g => (b, g)))) ∧
      row.2.2 = SA.gateTime p.toParams s + SA.lifetime p.toParams ∧
      row.2.2 = SA.releaseTime p.toParams (s + p.k) ∧
      ∀ k w C, j < k → k < i → IsGateTick p c rho k x w →
        let pre := clockPre p (storeAt p c E rho k x) (SA.gateTime p.toParams w)
        GridCO.savedGenuine pre.base w = none →
        SA.Root.confirmationFrom p.toParams (eraseFG pre.fg.F) (actView pre) w = some C →
        (actView pre).obligations.any (fun r => !Block.compatible r.1 C) = false →
        (row.1, row.2.1) ∉ (let wcView := actView pre;
        (wcView.blocks.filter (fun b => b != .genesis && Block.preceq b C)).flatMap
          (fun b => (@GridCO.admissionLevels GridCO.slowLeasePolicy
            p.toParams.engine p.n .root wcView w b).map (fun g => (b, g)))))
  (_hfast : ∀ i x,
    ∀ s X, X ∈ (FGSA.fastWriteAt (storeAt p c E rho i x) s).getD [] →
      ∃ j < i, IsGateTick p c rho j x s ∧ gatePassedAt p c E rho j ∧
        ∃ B, gateResultAt p c E rho j = some (some B) ∧
          Block.Preceq X B ∧ fastAt p c E rho x s X)
  (_hdeadlines : ∀ i x,
    ∀ K g deadline, (K, g, deadline) ∈ (storeAt p c E rho i x).base.obligations →
      ∀ B, B ≠ .genesis → Block.Preceq B K →
        Gen.AC.Root.ProtectsUntil (storeAt p c E rho i x).base B g deadline)
  (_hheldRows : ∀ i x W, HeldAt p c E rho i x W → ∀ a ∈ chainRows W,
    ∃ (wire : RowWire p.n) (r : Nat), wire.toRow? = some a ∧
      wire.auth = .seat .fg a.signer ∧ ∃ k o t, k < i ∧
        rho.events[k]? = some (.deliver x o t) ∧
        ∀ z, RowSigner p c rho wire z → z ∈ rho.honest →
          HonestRowBefore p c E rho i z r wire ∧ p.actionTime r ≤ t)
  (_hscopeRows : ∀ D, RootBlockInRun p c E rho (eraseFG D) → ∀ a ∈ chainRows D,
    rho.seatOf (.base .fg) a.signer ∈ rho.honest → ∃ j r wire,
      HonestRowAt p c E rho j (rho.seatOf (.base .fg) a.signer) r wire ∧
      wire.toRow? = some a ∧ wire.auth = .seat .fg a.signer)
  (_hfinalHead : ∀ j z r a u, HonestRowAt p c E rho j z r a →
    RowSigner p c rho a z → a.toRow? = some u → ∀ fp,
    u.finality_pair = some fp → ∃ B, HeldAt p c E rho j z B ∧
      fp.height = (heightView p B).h_j ∧ fp.target = (heightView p B).J.root ∧
      TargetQCAt p.E B fp.height (heightView p B).J),
  WCSeed p c E rho w iStar → ∀ i k x y s B, iStar ≤ i → i < rho.events.length →
    WCInv p c E rho w iStar i → IsGateTick p c rho i x s → w.u < s → k < i →
    rho.events[k]? = some (.tick y (SA.voteTime p.toParams (s + 1))) →
    gateResultAt p c E rho i = some (some B) → Block.Preceq w.QStar B →
    (∀ j z r C, WCResult p c E rho w iStar i j z r C → r < s → Block.Preceq C B) →
    let st := FGSA.clock p (storeAt p c E rho k y) (SA.voteTime p.toParams (s + 1))
    let src := actView (clockPre p (storeAt p c E rho i x) (SA.gateTime p.toParams s))
    ∃ Bfg, eraseFG Bfg = B ∧ WCFrameLiveBelow p st (.head (s + 1)) Bfg
      (voterBlocks p st (s + 1)) ∧
      (∀ A, FGBlock.Preceq A Bfg → A ∈ st.fg.TF ∧
        GridCO.stampBlock st.base (eraseFG A) < SA.freezeTime p.toParams s) ∧
      ∀ o ∈ GridCO.cleanSupport p.toParams.engine src s, ∀ K,
        GridCO.resolvedHead? src o = some K → Block.Preceq B K →
        ∃ Kfg, eraseFG Kfg = K ∧ ∀ A, FGBlock.Preceq A Kfg → A ∈ st.fg.TF ∧
          GridCO.stampBlock st.base (eraseFG A) < SA.freezeTime p.toParams s := by
  intro hvalid hlinked hcstar hnr hdelta hroots hsync hdeltaF
    hfaultQ haccountable hpart hstore hcumul hmono hactive hframe hmeta hrec hgeo hcert
    hsrc hlabel hqc hstrat hnoslash hemitted htargets hlease hfast hdeadlines hheldRows
    hscopeRows hfinalHead hs i k x y s B hi hilen inv ht hslabel hki hk hB hQB hord st src
  have hsch := hvalid.toScheduleWellFormed
  have hx := hvalid.honest_only _ (List.mem_of_getElem? ht)
  have hrawAt : gateResultAt p c E rho i = some (SA.Root.confirmationFrom p.toParams
      (eraseFG (clockPre p (storeAt p c E rho i x) (SA.gateTime p.toParams s)).fg.F) src s) := by
    rw [gateResultAt_eq_gateResult p c E rho hsch ht,
      gateResult_eq_saved p c E rho hsch ht, clockPre_fg]
    exact fgsa_gate_saved_result E rho hsch ht
      (fgsa_gate_joined_of_enabled E rho (wcg_gate_enabled_of_result hsch ht hB))
  have hraw := Option.some.inj (hrawAt.symm.trans hB)
  have hc := cstoreInv_clockPre p _ (storeBundle_stateBefore E rho i x).cstore
    (SA.gateTime p.toParams s)
  obtain ⟨_, hm⟩ := compat_of_confirmation p _ hc hraw
  obtain ⟨Bfg, _, he⟩ := (hc.baseTree B).mp hm
  have hframe := wcg_retrospectiveFrame ΔF w iStar hvalid hlinked hcstar hnr hdelta hroots
    hsync hdeltaF
    hfaultQ haccountable hpart hstore hcumul hmono hactive hframe hmeta hrec hgeo hcert
    hsrc hlabel hqc hstrat hnoslash hemitted htargets hlease hfast hdeadlines hheldRows
    hscopeRows hfinalHead
    hs i k x y s Bfg hi hilen inv ht hslabel hki hk (he ▸ hQB)
    (fun j z r C hr hrs => he ▸ hord j z r C hr hrs)
  have hFB : Block.Preceq (F_at p c E rho k y) B := by
    have hF := block_preceq_trans hframe.frame.finalRoot hframe.frame.rootBelow
    change Block.Preceq (eraseFG (FGSA.clock p _ _).fg.F) _ at hF
    rw [clock_fg, he] at hF
    exact hF
  have hcut : SA.freezeTime p.toParams s ≤ rho.horizon := by
    have ht := (hvalid.in_horizon _ (List.mem_of_getElem? ht)).2
    change 4 * p.Δ * (s : Int) + 6 * p.Δ ≤ rho.horizon at ht
    change 4 * p.Δ * (s : Int) + 3 * p.Δ ≤ rho.horizon
    linarith [p.deltaPos]
  have hGST : E.t_GST ≤ SA.voteTime p.toParams s := by
    apply hs.firstVoteAfterGST.trans
    have hh : ((w.u + 1 : Nat) : Int) ≤ s := Int.ofNat_le.mpr (Nat.succ_le_of_lt hslabel)
    change 4 * p.Δ * ((w.u + 1 : Nat) : Int) + p.Δ ≤ 4 * p.Δ * (s : Int) + p.Δ
    nlinarith [p.deltaPos]
  have paths : ∀ o ∈ GridCO.cleanSupport p.toParams.engine src s, ∀ K,
      GridCO.resolvedHead? src o = some K → Block.Preceq B K →
      ∃ Kfg, eraseFG Kfg = K ∧ ∀ A, FGBlock.Preceq A Kfg → A ∈ st.fg.TF ∧
        GridCO.stampBlock st.base (eraseFG A) < SA.freezeTime p.toParams s := by
    intro o ho K hK hBK
    have hres := (List.mem_filter.mp (List.mem_filter.mp ho).1).2
    change GridCO.resolvedBefore _ o _ = true at hres
    rw [GridCO.growth_resolvedBefore_eq] at hres
    unfold GridCO.growth_resolvedBefore at hres
    rw [hK] at hres
    have hKm := resolvedHead_mem _ o hK
    have hstamp := of_decide_eq_true (Bool.and_eq_true_iff.mp hres).2
    have hmem := ((actView_blocks _ K).mp hKm).1
    rw [(clockPre_fields p _ _).2.1] at hmem
    have heq : GridCO.stampBlock src K = GridCO.stampBlock
        (storeAt p c E rho i x).base K := by
      change (((clockPre p _ _).base.blockStamp.find? _).map Prod.snd).getD _ = _
      rw [(clockPre_stamps p _ _).1]
      have hkeys : K ∈ (storeAt p c E rho i x).base.blockStamp.map Prod.fst := by
        change K ∈ (V2.D.Run.stateBefore E rho i x).st.base.blockStamp.map Prod.fst
        rw [(metaInv_stateBefore E rho i x).stampKeys]
        exact hmem
      rw [GridCO.growth_stampBlock_eq]
      unfold GridCO.growth_stampBlock
      cases he : (storeAt p c E rho i x).base.blockStamp.find? (fun row => row.1 == K) with
      | none =>
        obtain ⟨row, hr, hh⟩ := List.mem_map.mp hkeys
        have hn := List.find?_eq_none.mp he row hr
        rw [hh, beq_self_eq_true] at hn
        contradiction
      | some row => rfl
    rw [heq] at hstamp
    exact growthStepTransferReceipts_prefreeze_path p c E rho hvalid hnr hdelta hroots hsync
      hcumul hmono
      hx hk hGST hcut hmem hstamp (block_preceq_trans hFB hBK)
  obtain ⟨o, K, ho, hK, _, _, hBK, _⟩ := confirmation_support_body p src s _ B hraw
  obtain ⟨Kfg, hKeq, hpath⟩ := paths o ho K hK hBK
  have hBpre : FGBlock.Preceq Bfg Kfg := eraseFG_preceq_iff.mp (by rwa [he, hKeq])
  exact ⟨Bfg, he, hframe, (fun A hA => hpath A (preceq_trans hA hBpre)), paths⟩

end AvailableChain.FGSA.Run



/-! WC plan §6.5; DC retrospective HEAD transfer precedes exact proposal adoption. -/

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG KitFG Gen.Pure

variable {p : Params} {In V : Type} {c : AppCodec In} [DecidableEq V] [Fintype V]
    {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}
    {ΔF : Time} {w : HealingWitness} {iStar : Nat}

/-- WC plan §6.5; DC raw pools, carried support and original receipts give the earlier HEAD. -/
theorem wcg_retrospective (hcausal : WCFinalityTargetEarlierStatement p c E rho) :
  WCGRetrospectiveStatement p c E rho ΔF w iStar := by
  intro hvalid hlinked hcstar hnr hdelta hroots hsync hdeltaF
    hfaultQ haccountable hpart hstore hcumul hmono hactive hframe hmeta hrec hgeo hcert
    hsrc hlabel hqc hstrat hnoslash hemitted htargets hlease hfast hdeadlines hheldRows
    hscopeRows hfinalHead hs i hi hilen inv x s B hx ht hslabel hB y hy
  obtain ⟨C, hC, _, hQC, hord, _, _⟩ := (wcg_gateResult hcausal) ΔF w iStar hvalid hlinked
    hcstar hnr
    hdelta hroots hsync hdeltaF
    hfaultQ haccountable hpart hstore hcumul hmono hactive hframe hmeta hrec hgeo hcert
    hsrc hlabel hqc hstrat hnoslash hemitted htargets hlease hfast hdeadlines hheldRows
    hscopeRows hfinalHead
    hs i x s hi hilen inv ht hslabel
  have he : C = B := Option.some.inj (Option.some.inj (hC.symm.trans hB))
  subst C
  have hsch := hvalid.toScheduleWellFormed
  have htime : SA.voteTime p.toParams (s + 1) < SA.gateTime p.toParams s := by
    change 4 * p.Δ * ((s + 1 : Nat) : Int) + p.Δ < 4 * p.Δ * (s : Int) + 6 * p.Δ
    push_cast
    linarith [p.deltaPos]
  have hclock : ((4 * (s + 1) + 1 : Nat) : Time) * p.Δ =
      SA.voteTime p.toParams (s + 1) := by
    change ((4 * (s + 1) + 1 : Nat) : Int) * p.Δ =
      4 * p.Δ * ((s + 1 : Nat) : Int) + p.Δ
    push_cast
    ring
  obtain ⟨k, hk, _⟩ := fgsa_tick_total E rho hsch hdelta y hy (4 * (s + 1) + 1)
    (hclock ▸ htime.le.trans (hvalid.in_horizon _ (List.mem_of_getElem? ht)).2)
  rw [hclock] at hk
  have hki := V2.D.Engine.eventIndex_lt_of_time_lt hsch hk ht htime
  let src := actView (clockPre p (storeAt p c E rho i x) (SA.gateTime p.toParams s))
  let dst := FGSA.clock p (storeAt p c E rho k y) (SA.voteTime p.toParams (s + 1))
  obtain ⟨Bfg, he, hframe, hpathB, hpaths⟩ := wcg_retrospectivePaths p c E rho ΔF w iStar
    hvalid hlinked hcstar hnr hdelta hroots hsync hdeltaF
    hfaultQ haccountable hpart hstore hcumul hmono hactive hframe hmeta hrec hgeo hcert
    hsrc hlabel hqc hstrat hnoslash hemitted htargets hlease hfast hdeadlines hheldRows
    hscopeRows hfinalHead hs i k x y s B hi hilen inv ht hslabel hki hk hB hQC hord
  have hGST : E.t_GST ≤ SA.voteTime p.toParams s := by
    apply hs.firstVoteAfterGST.trans
    have hh : ((w.u + 1 : Nat) : Int) ≤ s := Int.ofNat_le.mpr (Nat.succ_le_of_lt hslabel)
    change 4 * p.Δ * ((w.u + 1 : Nat) : Int) + p.Δ ≤ 4 * p.Δ * (s : Int) + p.Δ
    nlinarith [p.deltaPos]
  have hsyncLabel := Gen.V2.Duty.LabelSyncOn.of_recoveryBy E rho
    (fun o => ¬ isRowObject o) (SA.voteTime p.toParams s) (SA.gateTime p.toParams s)
    hsync (fgsaDelay_nonrow E.Δ _) hGST (by
      rw [hdelta]
      change 4 * p.Δ * (s : Int) + p.Δ + p.Δ ≤ 4 * p.Δ * (s : Int) + 6 * p.Δ
      linarith [p.deltaPos]) (hvalid.in_horizon _ (List.mem_of_getElem? ht)).2
  have hFB : Block.Preceq (eraseFG dst.fg.F) B :=
    he ▸ block_preceq_trans hframe.frame.finalRoot hframe.frame.rootBelow
  have hforward : ∀ o ∈ GridCO.cleanSupport p.toParams.engine src s, ∀ seat,
      GridCO.headSeat? o = some seat → Gen.AC.Root.voteSupports src.blocks B o = true →
      (o ∈ headSupport p dst (s + 1) ∧ Gen.AC.Root.voteSupports dst.base.blocks B o = true) ∨
        GridCO.equivocates (headVotes p dst (s + 1)) seat = true := by
    intro o ho seat hseat hsupp
    obtain ⟨K, hlookup, hKm, _, hBK⟩ := (Gen.AC.Root.vote_support_body _ _ _).mp hsupp
    have hhead := actView_resolve_target p
      (clockPre p (storeAt p c E rho i x) (SA.gateTime p.toParams s))
      (cstoreInv_clockPre p _ (cstoreInv_stateBefore E rho i x) _)
      (by rw [clockPre_headDomain]; exact base_headDomain_none p (reachable_stateBefore E rho i x))
      o hKm (resolvedTarget_root _ o hlookup)
    obtain ⟨Kfg, heK, hpath⟩ := hpaths o ho K hhead hBK
    exact fgsa_cleanSupport_forward_relay E rho hvalid hnr hdelta s hsyncLabel
      (ix := i) (iy := k) hx hy ht hk o ho seat hseat Kfg (heK ▸ hhead) B
      (heK ▸ hBK) hpath hFB
  have hraw : SA.Root.confirmationFrom p.toParams
      (eraseFG (clockPre p (storeAt p c E rho i x) (SA.gateTime p.toParams s)).fg.F)
      src s = some B := by
    have hh : gateResultAt p c E rho i = some (SA.Root.confirmationFrom p.toParams
        (eraseFG (clockPre p (storeAt p c E rho i x) (SA.gateTime p.toParams s)).fg.F)
        src s) := by
      rw [gateResultAt_eq_gateResult p c E rho hsch ht,
        gateResult_eq_saved p c E rho hsch ht, clockPre_fg]
      exact fgsa_gate_saved_result E rho hsch ht
        (fgsa_gate_joined_of_enabled E rho (wcg_gate_enabled_of_result hsch ht hB))
    exact Option.some.inj (hh.symm.trans hB)
  let P := GridCO.cleanSupport p.toParams.engine src s
  let L := GridCO.lateVotes p.toParams.engine src s
  have hscore (D : Block) := actView_score p
    (clockPre p (storeAt p c E rho i x) (SA.gateTime p.toParams s))
    (cstoreInv_clockPre p _ (cstoreInv_stateBefore E rho i x) _)
    (by rw [clockPre_headDomain]; exact base_headDomain_none p (reachable_stateBefore E rho i x))
    P P D
  have hmajority : GridCO.voterCount L < 2 * GridCO.goldfishScore src.blocks P P B := by
    rw [← hscore B]
    change (if _ then some _ else none) = some B at hraw
    split at hraw
    · have hwalk := Option.some.inj hraw
      rw [← hwalk]
      exact ‹_ < 2 * _›
    · contradiction
  have hcounts := Gen.AC.Root.transfer src.blocks dst.base.blocks P L
    (headVotes p dst (s + 1)) (headSupport p dst (s + 1)) B
    (fun _ ho => fgsa_early_subset_late p src s (List.mem_filter.mp ho).1)
    (fgsa_cleanSupport_seat_clean_late p src s) hforward
    (fgsa_headVotes_backward_relay E rho hvalid hnr hdelta s hsyncLabel hx hy ht hk)
    (fgsa_headSupport_subset_headVotes E rho hvalid k y s) hmajority
  rw [Gen.AC.Root.TransferBounds_def] at hcounts
  have hinv : CStoreInv p dst := cstoreInv_clock p _ (cstoreInv_stateBefore E rho k y) _
  have hv : ∀ A, FGBlock.Preceq dst.fg.F A → FGBlock.Preceq A Bfg →
      A ∈ voterBlocks p dst (s + 1) := by
    intro A hFA hA
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_filter.mpr ⟨(hpathB A hA).1, hFA⟩,
      Bool.or_eq_true_iff.mpr (Or.inl ?_)⟩
    apply decide_eq_true
    simpa only [Nat.add_sub_cancel] using (hpathB A hA).2
  obtain ⟨D, hD, hfloor⟩ := hframe.frame.floor
  have hDB : D = Bfg := eraseFG_injective hD
  subst D
  have hpath : ∀ A, Block.Prec (liveRoot p dst) A → Block.Preceq A B →
      A ∈ erasedList dst
        (filteredFrom p.E p.cfg (frameR p dst) (voterBlocks p dst (s + 1))) := by
    intro A hr hAB
    have hroot : Block.Preceq (liveRoot p dst) A := (Bool.and_eq_true_iff.mp hr).2
    obtain ⟨Afg, hAfg, heA, hpre⟩ := eraseFG_ancestor_preceq hinv.fg.closed
      (hpathB Bfg (preceq_refl _)).1 (he ▸ hAB)
    apply List.mem_filter.mpr
    refine ⟨(hinv.baseTree A).mpr ⟨Afg, hAfg, heA⟩, decide_eq_true ⟨Afg, ?_, heA⟩⟩
    rw [filteredFrom_of_bridge p.E p.cfg (heightView p) (heightView_bridge p)]
    apply (mem_filteredFromView (heightView p) (frameR p dst) _ Afg).mpr
    have hZA := block_preceq_trans hframe.startAbove hroot
    have hFA := eraseFG_preceq_iff.mp
      (heA ▸ block_preceq_trans hframe.frame.finalRoot hZA)
    exact ⟨hv Afg hFA hpre, hFA, eraseFG_preceq_iff.mp (heA ▸ hZA),
      Bfg, hv Bfg (eraseFG_preceq_iff.mp (he ▸ hFB)) (preceq_refl _), hpre, hfloor⟩
  have hhead : Block.Preceq B (headVote p dst (s + 1)) := by
    rw [fgsa_headVote_eq_filtered, ite_eq_right (Nat.succ_ne_zero s)]
    exact fgsa_headInTree_covers_of_transfer p dst _ _ _ B
      (block_compatible_of_common (he ▸ hframe.startBelow) (block_preceq_refl B))
      hpath hcounts.2.2.2.2.2.1 hcounts.2.2.2.2.2.2
  refine ⟨k, hki, hk, ?_, ?_, ?_⟩
  · rw [growth_headAtIdx_eq]
    unfold growth_headAtIdx
    rw [hk]
    exact hhead
  · intro A hAB
    obtain ⟨Afg, hAfg, heA⟩ := eraseFG_ancestor_mem hinv.fg.closed
      (hpathB Bfg (preceq_refl _)).1 (he ▸ hAB)
    exact (hinv.baseTree A).mpr ⟨Afg, hAfg, heA⟩
  · have hr : WCReceiptOrigins p c E rho k y (storeAt p c E rho k y) :=
      ⟨fgsa_block_stamp_source E rho k y, fgsa_vote_stamp_source E rho k y⟩
    constructor
    · simpa only [(clock_cumulative p _ _).2.2.1] using hr.blocks
    · simpa only [(clock_cumulative p _ _).2.2.2.1] using hr.votes

end AvailableChain.FGSA.Run



/-! WC plan §6.5; DC the joint event step preserves all bounded history and state fields. -/

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG KitFG Gen.Pure

variable {p : Params} {In V : Type} {c : AppCodec In} [DecidableEq V]
    {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}
    {w : HealingWitness} {iStar : Nat}

/-- WC plan §6.5; DC a completed result remains completed in an extended prefix. -/
private theorem growthStep_extend_result {i n j : Nat} {x : V} {s : Slot} {B : Block}
    (h : WCResult p c E rho w iStar i j x s B) (hin : i ≤ n) :
    WCResult p c E rho w iStar n j x s B :=
  { h with completed := h.completed.trans_le hin }

/-- WC plan §6.5; DC prefix origins remain valid in an extended history. -/
private theorem growthStep_extend_history {i n : Nat} {B : Block}
    (h : WCBelowHistory p c E rho w iStar i B) (hin : i ≤ n) :
    WCBelowHistory p c E rho w iStar n B := by
  rcases h.origin with h | ⟨j, x, s, C, hr, hb⟩
  · exact ⟨Or.inl h⟩
  · exact ⟨Or.inr ⟨j, x, s, C, growthStep_extend_result hr hin, hb⟩⟩

/-- WC plan §6.5; DC an ancestor uses the same seed or result origin. -/
private theorem growthStep_prefix_history {i : Nat} {A B : Block} (hab : Block.Preceq A B)
    (h : WCBelowHistory p c E rho w iStar i B) :
    WCBelowHistory p c E rho w iStar i A := by
  rcases h.origin with h | ⟨j, x, s, C, hr, hb⟩
  · exact ⟨Or.inl (block_preceq_trans hab h)⟩
  · exact ⟨Or.inr ⟨j, x, s, C, hr, block_preceq_trans hab hb⟩⟩

omit [DecidableEq V] in
/-- WC plan §6.5; DC the schedule orders completed gate labels. -/
private theorem growthStep_gate_label_le (hsch : V2.D.ScheduleWellFormed E rho)
    {i j : Nat} {x y : V} {s r : Slot} (hij : i ≤ j)
    (hi : IsGateTick p c rho i x s) (hj : IsGateTick p c rho j y r) : s ≤ r := by
  have ht : SA.gateTime p.toParams s ≤ SA.gateTime p.toParams r := by
    rcases hij.lt_or_eq with hij | rfl
    · obtain ⟨hil, hie⟩ := List.getElem?_eq_some_iff.mp hi
      obtain ⟨hjl, hje⟩ := List.getElem?_eq_some_iff.mp hj
      have hk := (List.pairwise_iff_getElem.mp hsch.sorted) i j hil hjl hij
      rw [hie, hje] at hk
      exact V2.D.Engine.time_le_of_key_le _ _ hk
    · exact (V2.Event.tick.inj (Option.some.inj (hi.symm.trans hj))).2.le
  change 4 * p.Δ * (s : Int) + 6 * p.Δ ≤ 4 * p.Δ * (r : Int) + 6 * p.Δ at ht
  have hc : (s : Int) ≤ r := by nlinarith [p.deltaPos]
  exact Int.ofNat_le.mp hc

variable [Fintype V] {ΔF : Time}

/-- WC plan §6.5; DC join the proved handler, origin, gate and retrospective conclusions. -/
private theorem growthStep_step_core (hcausal : WCFinalityTargetEarlierStatement p c E rho) :
  WCGStepStatement p c E rho ΔF w iStar := by
  intro hvalid hlinked hcstar hnr hdelta hroots hsync hdeltaF hfaultQ haccountable hpart
    hstore hcumul hmono hactive hframe hmeta hrec hgeo hcert hsrc hlabel hqc hstrat
    hnoslash hemitted htargets hlease hfast hdeadlines hheldRows hscopeRows hfinalHead
    hs i hi hilen inv e he
  have hsch := hvalid.toScheduleWellFormed
  have hnext : i + 1 ≤ rho.events.length := Nat.succ_le_of_lt hilen
  have hfinite := wcg_finiteStep ΔF w iStar hvalid hlinked hcstar hnr hdelta hroots hsync
    hdeltaF hfaultQ haccountable hpart hstore hcumul hmono hactive hframe hmeta hrec hgeo
    hcert hsrc hlabel hqc hstrat hnoslash hemitted htargets hlease hfast hdeadlines
    hheldRows hscopeRows hfinalHead hs i hi hilen inv e he
  have hout := (wcg_outputStep hcausal) ΔF w iStar hvalid hlinked hcstar hnr hdelta hroots hsync
    hdeltaF hfaultQ haccountable hpart hstore hcumul hmono hactive hframe hmeta hrec hgeo
    hcert hsrc hlabel hqc hstrat hnoslash hemitted htargets hlease hfast hdeadlines
    hheldRows hscopeRows hfinalHead hs i hi hilen inv e he
  have gate : ∀ x s, x ∈ rho.honest → IsGateTick p c rho i x s → w.u < s →
      ∃ B, gateResultAt p c E rho i = some (some B) ∧ Block.Preceq w.QStar B ∧
        gatePassedAt p c E rho i ∧
        (∀ j y r C, WCResult p c E rho w iStar i j y r C → r < s → Block.Preceq C B) ∧
        (∀ j y r C, WCResult p c E rho w iStar i j y r C → Block.Compatible C B) ∧
        ∀ y ∈ rho.honest, ∃ k < i, WCHeadRead p c E rho k y (s + 1) B := by
    intro x s hx ht hslabel
    obtain ⟨B, hB, hp, hQB, ho, hc, _⟩ := (wcg_gateResult hcausal) ΔF w iStar hvalid hlinked hcstar
      hnr hdelta hroots hsync hdeltaF hfaultQ haccountable hpart hstore hcumul hmono
      hactive hframe hmeta hrec hgeo hcert hsrc hlabel hqc hstrat hnoslash hemitted
      htargets hlease hfast hdeadlines hheldRows hscopeRows hfinalHead hs i x s hi hilen
      inv ht hslabel
    exact ⟨B, hB, hQB, hp, ho, hc, (wcg_retrospective hcausal) hvalid hlinked hcstar hnr hdelta
      hroots
      hsync hdeltaF hfaultQ haccountable hpart hstore hcumul hmono hactive hframe hmeta
      hrec hgeo hcert hsrc hlabel hqc hstrat hnoslash hemitted htargets hlease hfast
      hdeadlines hheldRows hscopeRows hfinalHead hs i hi hilen inv x s B hx ht hslabel hB⟩
  have nonempty : ∀ j x s, iStar ≤ j → j < i + 1 → x ∈ rho.honest →
      IsGateTick p c rho j x s → w.u < s →
      ∃ B, gateResultAt p c E rho j = some (some B) ∧
        Block.Preceq w.QStar B ∧ gatePassedAt p c E rho j := by
    intro j x s hj hji hx ht hl
    rcases (Nat.le_of_lt_succ hji).lt_or_eq with hlt | rfl
    · exact inv.nonempty j x s hj hlt hx ht hl
    · obtain ⟨B, hB, hQ, hp, _⟩ := gate x s hx ht hl
      exact ⟨B, hB, hQ, hp⟩
  have ordered : ∀ j k x y s r B C, WCResult p c E rho w iStar (i + 1) j x s B →
      WCResult p c E rho w iStar (i + 1) k y r C → s < r → Block.Preceq B C := by
    intro j k x y s r B C hb hc hsr
    by_cases hk : k < i
    · by_cases hj : j < i
      · exact inv.ordered j k x y s r B C { hb with completed := hj }
          { hc with completed := hk } hsr
      · have heq : j = i := by have := hb.completed; omega
        subst j
        exact (not_lt.mpr (growthStep_gate_label_le hsch hk.le hc.event hb.event) hsr).elim
    · have heq : k = i := by have := hc.completed; omega
      subst k
      have hj : j < i := by
        by_contra hn
        have heq : j = i := by have := hb.completed; omega
        subst j
        exact (not_lt.mpr (growthStep_gate_label_le hsch le_rfl hc.event hb.event)) hsr
      obtain ⟨D, hD, _, _, ho, _⟩ := gate y r hc.honest hc.event hc.label
      have heq : C = D := Option.some.inj (Option.some.inj (hc.value.symm.trans hD))
      exact heq ▸ ho j x s B { hb with completed := hj } hsr
  have sameLabel : ∀ j k x y s B C, WCResult p c E rho w iStar (i + 1) j x s B →
      WCResult p c E rho w iStar (i + 1) k y s C → Block.Compatible B C := by
    intro j k x y s B C hb hc
    by_cases hj : j < i
    · by_cases hk : k < i
      · exact inv.sameLabel j k x y s B C { hb with completed := hj }
          { hc with completed := hk }
      · have heq : k = i := by have := hc.completed; omega
        subst k
        obtain ⟨D, hD, _, _, _, hcompat, _⟩ := gate y s hc.honest hc.event hc.label
        have heq : C = D := Option.some.inj (Option.some.inj (hc.value.symm.trans hD))
        exact heq ▸ hcompat j x s B { hb with completed := hj }
    · have heq : j = i := by have := hb.completed; omega
      subst j
      by_cases hk : k < i
      · obtain ⟨D, hD, _, _, _, hcompat, _⟩ := gate x s hb.honest hb.event hb.label
        have heq : B = D := Option.some.inj (Option.some.inj (hb.value.symm.trans hD))
        change Block.compatible B C = true
        rw [block_compatible_comm, heq]
        exact hcompat k y s C { hc with completed := hk }
      · have heq : k = i := by have := hc.completed; omega
        subst k
        have heq : B = C := Option.some.inj (Option.some.inj (hb.value.symm.trans hc.value))
        exact block_compatible_of_common (heq ▸ block_preceq_refl C) (block_preceq_refl C)
  have resultCompat : ∀ j k x y s r B C,
      WCResult p c E rho w iStar (i + 1) j x s B →
      WCResult p c E rho w iStar (i + 1) k y r C → Block.Compatible B C := by
    intro j k x y s r B C hb hc
    rcases lt_trichotomy s r with h | h | h
    · exact block_compatible_of_common (ordered j k x y s r B C hb hc h)
        (block_preceq_refl C)
    · subst r
      exact sameLabel j k x y s B C hb hc
    · exact block_compatible_of_common (block_preceq_refl B)
        (ordered k j y x r s C B hc hb h)
  have historyCompat : ∀ A j x s B, WCBelowHistory p c E rho w iStar (i + 1) A →
      WCResult p c E rho w iStar (i + 1) j x s B → Block.Compatible A B := by
    intro A j x s B ha hr
    rcases ha.origin with ha | ⟨k, y, r, C, hc, hAC⟩
    · obtain ⟨C, hC, hQC, _⟩ := nonempty j x s hr.afterCut hr.completed hr.honest
        hr.event hr.label
      have heq : C = B := Option.some.inj (Option.some.inj (hC.symm.trans hr.value))
      exact block_compatible_of_common (block_preceq_trans ha (heq ▸ hQC))
        (block_preceq_refl B)
    · exact block_compatible_of_preceq_compatible hAC (resultCompat k j y x r s C B hc hr)
  have sources : ∀ j x r K, iStar ≤ j → j < i + 1 → x ∈ rho.honest →
      rho.events[j]? = some (.tick x (p.actionTime r)) →
      actionSourceFG p c E rho x r = some (some K) →
      ∃ B, WCResult p c E rho w iStar (i + 1) j x (r * p.R) B ∧
        Block.Preceq (eraseFG K) B := by
    intro j x r K hj hji hx ht hK
    have hread : actionSource p c E rho x r = some (some (eraseFG K)) := by
      change (actionSourceFG p c E rho x r).map (Option.map eraseFG) = _
      rw [hK]
      rfl
    obtain ⟨targets, B, _, hmem, hB, hbelow, _⟩ := hsrc x r _ hx hread
    have hgate : IsGateTick p c rho j x (r * p.R) := ht
    exact ⟨B, ⟨hx, hj, hji, (wcg_gate_cut_iff hsch hs hgate).mp hj, hgate,
      (gateResultAt_eq_gateResult p c E rho hsch hgate).trans hB⟩, hbelow _ hmem⟩
  have finite : ∀ k, iStar ≤ k → k ≤ i + 1 → WCFiniteFacts p c E rho k := by
    intro k hk hkn
    by_cases hki : k ≤ i
    · exact inv.finite k hk hki
    · have heq : k = i + 1 := by omega
      exact heq ▸ hfinite
  have outputHistory : ∀ x ∈ rho.honest,
      WCBelowHistory p c E rho w iStar (i + 1) (S_at p c E rho (i + 1) x) := by
    intro x hx
    rcases (hout x hx).2 with hkeep | ⟨s, ht, hl, hraw⟩
    · rw [hkeep]
      exact growthStep_extend_history (wcg_outputHistoryAt hs inv hi le_rfl hx) (Nat.le_succ i)
    · exact ⟨Or.inr ⟨i, x, s, _,
        ⟨hx, hi, Nat.lt_succ_self i, hl, ht, hraw⟩, block_preceq_refl _⟩⟩
  have oldOrigin : ∀ k x, iStar ≤ k → k ≤ i → x ∈ rho.honest →
      S_at p c E rho k x = w.QStar ∨
      (∃ j y s, WCResult p c E rho w iStar k j y s (S_at p c E rho k x)) ∨
      (∃ l, iStar ≤ l ∧ l ≤ k ∧ S_at p c E rho k x = F_at p c E rho l x ∧
        ∀ j y s B, WCResult p c E rho w iStar (i + 1) j y s B →
          Block.Compatible (F_at p c E rho l x) B) := by
    intro k x hlo hki hx
    rcases inv.outputOrigin k x hlo hki hx with hq | hr | ⟨l, hl, hlk, heq, _⟩
    · exact Or.inl hq
    · exact Or.inr (Or.inl hr)
    · refine Or.inr (Or.inr ⟨l, hl, hlk, heq, ?_⟩)
      intro j y s B hr
      exact historyCompat _ j y s B
        (growthStep_extend_history (wcg_finalHistoryAt hs inv hl (hlk.trans hki) hx)
          (hlk.trans (hki.trans (Nat.le_succ i)))) hr
  refine {
    interval := ⟨hi.trans (Nat.le_succ i), hnext⟩
    nonempty := nonempty
    ordered := ordered
    sameLabel := sameLabel
    retrospective := ?_
    preCutHigh := inv.preCutHigh
    suffixSources := sources
    highCertificates := ?_
    lowFinalized := ?_
    liveTargets := ?_
    oldLiveTargets := ?_
    suffixSaved := ?_
    suffixFast := ?_
    outputOrigin := ?_
    served := ?_
    transitions := ?_
    finite := finite
    carrier := ?_ }
  · intro j x s B hr y hy
    by_cases hj : j < i
    · exact inv.retrospective j x s B { hr with completed := hj } y hy
    · have heq : j = i := by have := hr.completed; omega
      subst j
      obtain ⟨C, hC, _, _, _, _, hhead⟩ := gate x s hr.honest
        (wcg_gate_enabled_of_result hsch hr.event hr.value) hr.label
      have heq : B = C := Option.some.inj (Option.some.inj (hr.value.symm.trans hC))
      exact heq ▸ hhead y hy
  · intro k x W X hlo hkn hx hW hX hn hh
    by_cases hki : k ≤ i
    · exact inv.highCertificates k x W X hlo hki hx hW hX hn hh
    · have heq : k = i + 1 := by omega
      subst k
      have ho := hfinite.certified x hx W hW X hX hn
      refine ⟨ho, ?_⟩
      obtain ⟨j, y, r, wire, K, B, hj, hrow, hname, hK, hXK, _⟩ := ho.origin
      by_cases hjcut : j < iStar
      · obtain ⟨K', B', hK', _, _, _, _, hbelow⟩ :=
          hs.highSources j y r wire _ hjcut hrow hname hh
        have heq : K = K' := Option.some.inj (Option.some.inj (hK.symm.trans hK'))
        exact ⟨Or.inl (block_preceq_trans (eraseFG_preceq hXK) (heq ▸ hbelow))⟩
      · obtain ⟨C, hr, hKC⟩ := sources j y r K (Nat.le_of_not_gt hjcut) hj hrow.1 hrow.2.1 hK
        exact ⟨Or.inr ⟨j, y, r * p.R, C, hr, block_preceq_trans (eraseFG_preceq hXK) hKC⟩⟩
  · intro k x D X h _ _ hD hF hh hlo
    exact (wcg_lowFinalized hroots haccountable hs D X h
      (wcg_finalizedOccurrence hscopeRows hnoslash D X h
        (rootScope_store hD.1 hD.2) hF hh) hlo).1
  · intro k x row hlo hkn hx hr ht
    by_cases hki : k ≤ i
    · exact inv.liveTargets k x row hlo hki hx hr ht
    · have heq : k = i + 1 := by omega
      subst k
      exact growthStep_prefix_history (htargets (i + 1) x row hr) (outputHistory x hx)
  · intro k x row hlo _ hx hr _ ht
    have hnow := V2.D.Engine.stateBefore_now_mono_noRestart (fgsaClock p c) E rho hsch hnr
      hlo x
    rw [fgsa_clock_now p c (V2.D.Run.stateBefore E rho iStar x),
      fgsa_clock_now p c (V2.D.Run.stateBefore E rho k x)] at hnow
    exact hs.liveTargets x hx row hr (hnow.trans_lt ht)
  · intro k x s B hlo hkn hx hslabel hB
    obtain ⟨j, hj, ht, hraw⟩ := (finite k hlo hkn).saved x hx s B hB
    exact ⟨j, hx, (wcg_gate_cut_iff hsch hs ht).mpr hslabel, hj, hslabel, ht, hraw⟩
  · intro k x s X hlo hkn hx hslabel hX
    obtain ⟨j, hj, ht, _, B, hB, hXB, _⟩ := (finite k hlo hkn).fastWrites x hx s X hX
    exact ⟨j, B, ⟨hx, (wcg_gate_cut_iff hsch hs ht).mpr hslabel, hj, hslabel, ht, hB⟩, hXB⟩
  · intro k x hlo hkn hx
    by_cases hki : k ≤ i
    · exact oldOrigin k x hlo hki hx
    · have heq : k = i + 1 := by omega
      subst k
      rcases (hout x hx).2 with hkeep | ⟨s, ht, hl, hB⟩
      · rcases oldOrigin i x hi le_rfl hx with hq | ⟨j, y, s, hr⟩ | ⟨l, hl, hli, hF, hc⟩
        · exact Or.inl (hkeep.trans hq)
        · right; left
          refine ⟨j, y, s, ?_⟩
          rw [hkeep]
          exact growthStep_extend_result hr (Nat.le_succ i)
        · exact Or.inr (Or.inr ⟨l, hl, hli.trans (Nat.le_succ i), hkeep.trans hF, hc⟩)
      · exact Or.inr (Or.inl ⟨i, x, s, hx, hi, Nat.lt_succ_self i, hl, ht, hB⟩)
  · intro k x hlo hkn hx
    by_cases hki : k ≤ i
    · exact inv.served k x hlo hki hx
    · have heq : k = i + 1 := by omega
      subst k
      exact block_preceq_trans (inv.served i x hi le_rfl hx) (hout x hx).1
  · intro k x hlo hkn hx
    rcases (Nat.le_of_lt_succ hkn).lt_or_eq with hki | rfl
    · exact inv.transitions k x hlo hki hx
    · exact (hout x hx).1
  · obtain ⟨W, hW, hh, _, hmem⟩ := hs.carrier
    refine ⟨W, hW, hh, ?_⟩
    intro k x hlo hkn hx
    exact (hcumul hnr iStar k x hx hlo (hkn.trans hnext)).1 (hmem x hx)

/-- WC plan §6.5; DC delivery preserves the joint invariant after immediate reconciliation. -/
theorem wcg_stepDelivery (hcausal : WCFinalityTargetEarlierStatement p c E rho) :
  WCGStepDeliveryStatement p c E rho ΔF w iStar := by
  intro hvalid hlinked hcstar hnr hdelta hroots hsync hdeltaF
    hfaultQ haccountable hpart hstore hcumul hmono hactive hframe hmeta hrec hgeo hcert
    hsrc hlabel hqc hstrat hnoslash hemitted htargets hlease hfast hdeadlines hheldRows
    hscopeRows hfinalHead hs i hi hilen inv x o t he
  exact (growthStep_step_core hcausal) hvalid hlinked hcstar hnr hdelta hroots hsync hdeltaF
    hfaultQ haccountable hpart hstore hcumul hmono hactive hframe hmeta hrec hgeo hcert
    hsrc hlabel hqc hstrat hnoslash hemitted htargets hlease hfast hdeadlines hheldRows
    hscopeRows hfinalHead hs i hi hilen inv (.deliver x o t) he

/-- WC plan §6.5; DC a tick without a gate preserves the joint invariant in handler order. -/
theorem wcg_stepNoGateTick (hcausal : WCFinalityTargetEarlierStatement p c E rho) :
  WCGStepNoGateTickStatement p c E rho ΔF w iStar := by
  intro hvalid hlinked hcstar hnr hdelta hroots hsync hdeltaF
    hfaultQ haccountable hpart hstore hcumul hmono hactive hframe hmeta hrec hgeo hcert
    hsrc hlabel hqc hstrat hnoslash hemitted htargets hlease hfast hdeadlines hheldRows
    hscopeRows hfinalHead hs i hi hilen inv x t he _hgate
  exact (growthStep_step_core hcausal) hvalid hlinked hcstar hnr hdelta hroots hsync hdeltaF
    hfaultQ haccountable hpart hstore hcumul hmono hactive hframe hmeta hrec hgeo hcert
    hsrc hlabel hqc hstrat hnoslash hemitted htargets hlease hfast hdeadlines hheldRows
    hscopeRows hfinalHead hs i hi hilen inv (.tick x t) he

/-- WC plan §6.5; DC a suffix gate adds its ordered result and retrospective HEAD evidence. -/
theorem wcg_stepGateTick (hcausal : WCFinalityTargetEarlierStatement p c E rho) :
  WCGStepGateTickStatement p c E rho ΔF w iStar := by
  intro hvalid hlinked hcstar hnr hdelta hroots hsync hdeltaF
    hfaultQ haccountable hpart hstore hcumul hmono hactive hframe hmeta hrec hgeo hcert
    hsrc hlabel hqc hstrat hnoslash hemitted htargets hlease hfast hdeadlines hheldRows
    hscopeRows hfinalHead hs i hi hilen inv x s he _hlabel
  exact (growthStep_step_core hcausal) hvalid hlinked hcstar hnr hdelta hroots hsync hdeltaF
    hfaultQ haccountable hpart hstore hcumul hmono hactive hframe hmeta hrec hgeo hcert
    hsrc hlabel hqc hstrat hnoslash hemitted htargets hlease hfast hdeadlines hheldRows
    hscopeRows hfinalHead hs i hi hilen inv (.tick x (SA.gateTime p.toParams s)) he

/-- WC plan §6.5; DC the explicit no-restart field excludes the restart branch. -/
theorem wcg_stepRestart : WCGStepRestartStatement p c E rho ΔF w iStar := by
  intro _hvalid _hlinked _hcstar hnr _hdelta _hroots _hsync _hdeltaF _hfaultQ
    _haccountable _hpart _hstore _hcumul _hmono _hactive _hframe _hmeta _hrec _hgeo _hcert
    _hsrc _hlabel _hqc _hstrat _hnoslash _hemitted _htargets _hlease _hfast _hdeadlines
    _hheldRows _hscopeRows _hfinalHead _hs i _hi _hilen _inv x t he
  exact hnr i x t he

/-- WC plan §6.5; DC split the actual event into the proved delivery, tick and restart cases. -/
theorem wcg_step (hcausal : WCFinalityTargetEarlierStatement p c E rho) : WCGStepStatement p c
  E rho ΔF w iStar := by
  intro hvalid hlinked hcstar hnr hdelta hroots hsync hdeltaF
    hfaultQ haccountable hpart hstore hcumul hmono hactive hframe hmeta hrec hgeo hcert
    hsrc hlabel hqc hstrat hnoslash hemitted htargets hlease hfast hdeadlines hheldRows
    hscopeRows hfinalHead hs i hi hilen inv e he
  cases e with
  | deliver x o t =>
    exact (wcg_stepDelivery hcausal) hvalid hlinked hcstar hnr hdelta hroots hsync hdeltaF
        hfaultQ haccountable hpart hstore hcumul hmono hactive hframe hmeta hrec hgeo hcert
        hsrc hlabel hqc hstrat hnoslash hemitted htargets hlease hfast hdeadlines hheldRows
        hscopeRows hfinalHead hs i hi hilen inv x o t he
  | restart x t =>
    exact (wcg_stepRestart hvalid hlinked hcstar hnr hdelta hroots hsync hdeltaF
        hfaultQ haccountable hpart hstore hcumul hmono hactive hframe hmeta hrec hgeo hcert
        hsrc hlabel hqc hstrat hnoslash hemitted htargets hlease hfast hdeadlines hheldRows
        hscopeRows hfinalHead hs i hi hilen inv x t he).elim
  | tick x t =>
    by_cases hg : isGateTime p t = true
    · obtain ⟨s, rfl⟩ := (isGateTime_iff p t).mp hg
      exact (wcg_stepGateTick hcausal) hvalid hlinked hcstar hnr hdelta hroots hsync hdeltaF
        hfaultQ haccountable hpart hstore hcumul hmono hactive hframe hmeta hrec hgeo hcert
        hsrc hlabel hqc hstrat hnoslash hemitted htargets hlease hfast hdeadlines hheldRows
        hscopeRows hfinalHead hs i hi hilen inv x s he
        ((wcg_gate_cut_iff hvalid.toScheduleWellFormed hs he).mp hi)
    · exact (wcg_stepNoGateTick hcausal) hvalid hlinked hcstar hnr hdelta hroots hsync hdeltaF
        hfaultQ haccountable hpart hstore hcumul hmono hactive hframe hmeta hrec hgeo hcert
        hsrc hlabel hqc hstrat hnoslash hemitted htargets hlease hfast hdeadlines hheldRows
        hscopeRows hfinalHead hs i hi hilen inv x t he (Bool.eq_false_iff.mpr hg)

end AvailableChain.FGSA.Run



/-! WC plan §6.8; DC finality remains below every honest output. -/

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG KitFG

variable {p : Params} {In V : Type} [DecidableEq V] [Fintype V] {c : AppCodec In}
    {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}

/-- WC plan §6.8; DC a finalized source is served before its finality action. -/
theorem wcg_finalBelow (hcausal : WCFinalityTargetEarlierStatement p c E rho) {ΔF : Time} {w :
  HealingWitness} {iStar : Nat} :
    WCGFinalBelowStatement p c E rho ΔF w iStar := by
  intro hvalid hlinked hcstar hnr hdelta hroots hsync hdeltaF hfaultQ haccountable hpart
    hstore hcumul hmono hactive hframe hmeta hrec hgeo hcert hsrc hlabel hqc hstrat
    hnoslash hemitted htargets hlease hfast hdeadlines hheldRows hscopeRows hfinalHead
    hs hinv i x y hi hx hy
  have inv := hinv i hi
  obtain ⟨D, hD, hF⟩ := ((inv.finite i hi.1 le_rfl).store x hx).fg.Fcar
  by_cases hlo : (finalityView p D).h_F ≤ w.M
  · exact Gen.Pure.block_preceq_trans
      (inv.lowFinalized i x D _ _ hi.1 le_rfl ⟨hx, hD⟩ hF rfl hlo)
      (Gen.Pure.block_preceq_trans hs.sourcePrefix (inv.served i y hi.1 le_rfl hy))
  have hpos : 0 < (finalityView p D).h_F := by simp only [Height] at *; omega
  have hhigh : w.M + 1 ≤ (finalityView p D).h_F := by simp only [Height] at *; omega
  obtain ⟨jf, z, rf, af, uf, H, jt, v, rt, aT, ut, K, B, hjf, haf, _, _, _, _,
      _, _, _, _, hjt, haT, hdecode, _, htarget, hK, hXK, hgate, hKB, hgap⟩ :=
    (hcausal hvalid hlinked hfaultQ hroots hheldRows hfinalHead hqc
      hemitted i x D _ _ ⟨hx, hD⟩ hpos hF rfl).finalityRow
  have hfields : aT.payload.height_pair = ut.height_pair := by
    rcases aT with ⟨auth, body⟩
    cases auth with
    | none => cases hdecode
    | proposer s => cases hdecode
    | seat label k =>
      cases label with
      | head s => cases hdecode
      | fg => exact congrArg Row.height_pair (Option.some.inj hdecode)
  have hname : namedEntry aT.payload.height_pair =
      some ((finalityView p D).h_F, (storeAt p c E rho i x).fg.F.root) := by
    rw [hfields, htarget]
    rfl
  by_cases hbefore : jt < iStar
  · obtain ⟨K', B', hK', _, _, _, _, hbelow⟩ :=
      hs.highSources jt v rt aT _ hbefore haT hname hhigh
    have heq : K = K' := Option.some.inj (Option.some.inj (hK.symm.trans hK'))
    exact Gen.Pure.block_preceq_trans (eraseFG_preceq hXK)
      (Gen.Pure.block_preceq_trans (heq ▸ hbelow) (inv.served i y hi.1 le_rfl hy))
  have hafter : iStar ≤ jt := Nat.le_of_not_gt hbefore
  have ht : IsGateTick p c rho jt v (rt * p.R) := haT.2.1
  have hlabel' : w.u < rt * p.R := by
    by_contra hn
    have hle : rt * p.R ≤ w.u := Nat.le_of_not_gt hn
    have htime : SA.gateTime p.toParams (rt * p.R) ≤ SA.gateTime p.toParams w.u := by
      have hcast : ((rt * p.R : Nat) : Int) ≤ w.u := Int.ofNat_le.mpr hle
      change 4 * p.Δ * (rt * p.R : Nat) + 6 * p.Δ ≤
        4 * p.Δ * (w.u : Int) + 6 * p.Δ
      nlinarith [p.deltaPos]
    have hf := V2.D.Engine.filter_false_of_index_ge hvalid.toScheduleWellFormed
      (cutPred (SA.gateTime p.toParams w.u)) (by
        intro e f hk hf
        exact decide_eq_true (hk.trans (of_decide_eq_true hf)))
      (show afterTicksIdx rho (SA.gateTime p.toParams w.u) ≤ jt from hs.cut ▸ hafter) ht
    have hc : cutPred (SA.gateTime p.toParams w.u)
        (.tick v (SA.gateTime p.toParams (rt * p.R)) : V2.Event V (fgsa p c).Object) = true :=
      decide_eq_true (Prod.Lex.toLex_le_toLex.mpr
        (htime.lt_or_eq.imp id (fun he => ⟨he, le_rfl⟩)))
    rw [hc] at hf
    cases hf
  have hhor : SA.gateTime p.toParams (rt * p.R) + 4 * p.Δ ≤ rho.horizon :=
    hgap.le.trans (hvalid.in_horizon _ (List.mem_of_getElem? haf.2.1)).2
  have hcut : afterTicksIdx rho (SA.gateTime p.toParams (rt * p.R) + 4 * p.Δ) ≤ i := by
    apply le_trans (b := jf) _ (Nat.le_of_lt hjf)
    by_contra hn
    have hlt := Nat.lt_of_not_ge hn
    have hm : V2.Event.tick z (p.actionTime rf) ∈ rho.events.filter
        (cutPred (SA.gateTime p.toParams (rt * p.R) + 4 * p.Δ)) := by
      rw [V2.D.Engine.filter_eq_take hvalid.toScheduleWellFormed _ (by
        intro e f hk hf
        exact decide_eq_true (hk.trans (of_decide_eq_true hf)))]
      apply List.mem_of_getElem? (i := jf)
      change (rho.events.take (afterTicksIdx rho
        (SA.gateTime p.toParams (rt * p.R) + 4 * p.Δ)))[jf]? = _
      rw [List.getElem?_take_of_lt hlt]
      exact haf.2.1
    have hk := of_decide_eq_true (List.mem_filter.mp hm).2
    have htime : p.actionTime rf ≤ SA.gateTime p.toParams (rt * p.R) + 4 * p.Δ := by
      rcases Prod.Lex.toLex_le_toLex.mp hk with ht | ⟨ht, _⟩
      · exact ht.le
      · exact ht.le
    exact (not_lt.mpr htime) hgap
  have hraw := (gateResultAt_eq_gateResult p c E rho hvalid.toScheduleWellFormed ht).trans hgate
  have hserved := wcg_service4 hvalid hlinked hcstar hnr hdelta hroots hsync hdeltaF
    hfaultQ haccountable hpart hstore hcumul hmono hactive hframe hmeta hrec hgeo hcert
    hsrc hlabel hqc hstrat hnoslash hemitted htargets hlease hfast hdeadlines hheldRows
    hscopeRows hfinalHead hs hinv jt v (rt * p.R) B haT.1 hafter ht hlabel' hraw hhor
    i y hcut hi.2 hy
  exact Gen.Pure.block_preceq_trans (eraseFG_preceq hXK)
    (Gen.Pure.block_preceq_trans hKB hserved)

end AvailableChain.FGSA.Run



/-! WC plan §§6.6–6.8; DC joint event induction and the five seeded safety fields. -/

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG KitFG

variable {p : Params} {In V : Type} {c : AppCodec In} [DecidableEq V] [Fintype V]
    {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}
    {ΔF : Time} {w : HealingWitness} {iStar : Nat}

/-- WC plan §6.6; DC initialization and actual event steps prove the complete suffix invariant. -/
theorem wcg_seededInduction (hcausal : WCFinalityTargetEarlierStatement p c E rho) :
  WCGSeededInductionStatement p c E rho ΔF w iStar := by
  intro hvalid hlinked hcstar hnr hdelta hroots hsync hdeltaF
    hfaultQ haccountable hpart hstore hcumul hmono hactive hframe hmeta hrec hgeo hcert
    hsrc hlabel hqc hstrat hnoslash hemitted htargets hlease hfast hdeadlines hheldRows
    hscopeRows hfinalHead hs
  have initial := wcg_init hvalid hlinked hcstar hnr hdelta hroots hsync hdeltaF
    hfaultQ haccountable hpart hstore hcumul hmono hactive hframe hmeta hrec hgeo hcert
    hsrc hlabel hqc hstrat hnoslash hemitted htargets hlease hfast hdeadlines hheldRows
    hscopeRows hfinalHead hs hs.within
  have step := (wcg_step hcausal) hvalid hlinked hcstar hnr hdelta hroots hsync hdeltaF
    hfaultQ haccountable hpart hstore hcumul hmono hactive hframe hmeta hrec hgeo hcert
    hsrc hlabel hqc hstrat hnoslash hemitted htargets hlease hfast hdeadlines hheldRows
    hscopeRows hfinalHead hs
  have all : ∀ i, iStar ≤ i → i ≤ rho.events.length → WCInv p c E rho w iStar i := by
    intro i hi
    induction i, hi using Nat.le_induction with
    | base => intro _; exact initial
    | succ i hi ih =>
      intro hbound
      have hlt : i < rho.events.length := by omega
      exact step i hi hlt (ih (Nat.le_of_lt hlt)) rho.events[i]
        (List.getElem?_eq_getElem hlt)
  intro i hi
  exact all i hi.1 hi.2

end AvailableChain.FGSA.Run

end
