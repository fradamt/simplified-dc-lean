module
public import AvailableChainFGSAProofs.Proofs.Foundations.RowPermission -- shake: keep (own-library route)

@[expose] public section

set_option maxSynthPendingDepth 100
set_option maxRecDepth 10000

-- Each test is complete on its own. The layer rules forbid test-to-test imports.
namespace AvailableChain.FGSA.Run.Tests.NonVacuity.HealingRun

/-- S5 fixture: one honest node, positive horizon, and unchanged SA clocks. -/
def params : Params :=
  ⟨⟨1, 1, 2, 0, by decide, by decide, by decide, by decide⟩,
    3, 6, by decide, 2, by decide⟩

def env : Generic.Env (Fin 1) := ⟨1, by decide, 0, le_rfl, fun _ _ => true⟩
def deltaF : Time := 3
def gap : Time := 4
def horizon : Time := 304

theorem params_delta : params.Δ = 1 := rfl
theorem params_n : params.n = 1 := rfl
theorem params_k : params.k = 2 := rfl
theorem params_eta : params.η = 0 := rfl
theorem params_R : params.R = 3 := rfl
theorem params_timeout : params.δt = 6 := rfl
theorem params_window : params.K_W = 2 := rfl
theorem env_delta : env.Δ = params.Δ := rfl
theorem env_gst : env.t_GST = 0 := rfl
theorem env_awake (v : Fin 1) (t : Time) : env.awake v t = true := rfl
theorem deltaF_value : deltaF = 3 := rfl
theorem gap_value : gap = 4 := rfl
theorem horizon_value : horizon = 304 := rfl
theorem horizon_pos : 0 < horizon := by decide
theorem deltaF_lower : env.Δ ≤ deltaF := by decide
theorem gap_lower : 4 * params.Δ ≤ gap := by decide

theorem kappaF_value : kappaF params deltaF = 3 := by decide
theorem betaF_value : betaF params deltaF = 12 := by decide
theorem epsF_value : epsF params deltaF = 4 := by decide
theorem period_value : P params = 12 := by decide
theorem gamma_value : Γ params gap = 4 := by decide
theorem lease_value : L params = 7 := by decide
theorem rhoGamma_value : ρΓ params gap = 26 := by decide
theorem rhoOne_value : ρ₁ params gap = 21 := by decide
theorem short_k : params.k ≤ 2 * params.R + 1 := by decide
theorem Eg_two_value : E_gF params deltaF gap (ρΓ params gap) = 53 := by decide
theorem Eg_one_value : E_gF params deltaF gap (ρ₁ params gap) = 48 := by decide
theorem Ej_two_value : E_jF params deltaF gap (ρΓ params gap) = 49 := by decide
theorem Ej_one_value : E_jF params deltaF gap (ρ₁ params gap) = 44 := by decide
theorem Bc_two_value : B_cF params deltaF gap (ρΓ params gap) = 48 := by decide
theorem Bc_one_value : B_cF params deltaF gap (ρ₁ params gap) = 43 := by decide
theorem Dc_two_value : D_cF params (ρΓ params gap) = 37 := by decide
theorem Dc_one_value : D_cF params (ρ₁ params gap) = 32 := by decide
theorem reset_two_value : B_resetF params deltaF gap (ρΓ params gap) = 325 := by decide
theorem reset_one_value : B_resetF params deltaF gap (ρ₁ params gap) = 295 := by decide
theorem reset_value : B'_resetF params deltaF gap = 295 := by decide
theorem healing_two_value : B_H2F params deltaF gap = 333 := by decide
theorem healing_one_value : B_H1F params deltaF gap = 303 := by decide
theorem healing_value : B_HF params deltaF gap = 303 := by decide

theorem healing_strict_horizon : B_HF params deltaF gap < horizon := by decide
theorem healing_horizon : env.t_GST + B_HF params deltaF gap ≤ horizon := by decide
theorem reset_horizon : env.t_GST + B'_resetF params deltaF gap ≤ horizon := by decide
theorem reset_full_horizon :
    env.t_GST + B'_resetF params deltaF gap + Γ params gap + 4 * params.Δ ≤ horizon := by
  decide
theorem reset_full_budget : B'_resetF params deltaF gap + Γ params gap + 4 * params.Δ = 303 := by
  decide
theorem action_three_value : params.actionTime 3 = 42 := by decide
theorem renewed_three_budget :
    params.actionTime 3 + 2 * P params + Γ params gap - 4 * params.Δ = 66 := by decide
theorem renewed_three_horizon :
    params.actionTime 3 + 2 * P params + Γ params gap - 4 * params.Δ ≤ horizon := by decide

theorem livenessBound : LivenessBoundW params deltaF := ⟨by decide⟩

section EmissionHelpers
open AvailableChain.SimplexFG
open AvailableChain.V2.D.Engine
variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

-- Local step lemmas use only the row-validity invariant. The fixture proves
-- this invariant by induction, before it constructs DeliveryWellFormed.
theorem nv_rows_clock (st : State p.n) (t : Time)
    (h : EmissionRowsValid st) : EmissionRowsValid (FGSA.clock p st t) := by
  constructor
  · rw [clock_rowPool]; exact h.1
  · rw [clock_proposals]; exact h.2

theorem nv_rows_admit (st : State p.n) (a : RowWire p.n)
    (h : EmissionRowsValid st) (ha : a.valid = true) :
    EmissionRowsValid (admitRow p st a) := by
  rcases admitRow_eq p st a with he | he
  · rw [he]; exact h
  · rw [he]
    refine ⟨?_, h.2⟩
    intro a' hm
    rcases List.mem_append.mp hm with hm | hm
    · exact h.1 a' hm
    · exact List.mem_singleton.mp hm ▸ ha

theorem nv_rows_fold (rows : List (RowWire p.n)) (st : State p.n)
    (h : EmissionRowsValid st) (hr : ∀ a ∈ rows, a.valid = true) :
    EmissionRowsValid (rows.foldl (admitRow p) st) := by
  induction rows generalizing st with
  | nil => exact h
  | cons a rows ih =>
    exact ih _ (nv_rows_admit st a h (hr a (List.mem_cons_self ..)))
      (fun a ha => hr a (List.mem_cons_of_mem _ ha))

theorem nv_rows_process (st : State p.n) (o : Obj p)
    (h : EmissionRowsValid st) (hw : (fgsa p c).wellFormed o = true) :
    EmissionRowsValid (FGSA.process p st (toWire p o)) := by
  change FGSA.wellFormed p (toWire p o) = true at hw
  change EmissionRowsValid (match (toWire p o).decode with
    | some (.vote s i b) => admitHead p st s i b
    | some (.row _ body) => admitRow p st ⟨(toWire p o).auth, body⟩
    | some (.block s b raw sup rows) => admitBlock p st s b raw sup rows
    | none => st)
  cases hd : (toWire p o).decode with
  | none => exact h
  | some m =>
    cases m with
    | vote s i b => exact h
    | row i body =>
      have he := decode_eq_row.mp hd
      rw [he] at hw ⊢
      exact nv_rows_admit _ _ h hw
    | block s b raw sup rows =>
      have he := decode_eq_block.mp hd
      have hr : ∀ a ∈ rows, a.valid = true := by
        change (match (toWire p o).decode with
          | some (.vote _ _ _) => true
          | some (.row _ body) => body.valid
          | some (.block s b raw sup rows) =>
            b != .genesis && s == b.slot && decide (b.parent.slot < b.slot) &&
              raw.all (fun v => match v.decode? with
                | some (r, _, _) => r + 1 == b.slot | none => false) &&
              sup.all (fun v => decide (v ∈ raw)) &&
              rows.all RowWire.valid && rowsOk b rows
          | none => false) = true at hw
        rw [hd] at hw
        intro a ha
        exact List.all_eq_true.mp
          (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hw).1).2 a ha
      change EmissionRowsValid (match parentFG st b with
        | none => st
        | some P => if blockAccepted p st s b P rows then
          rows.foldl (admitRow p)
            (if (Window.on_block p p.K_W st.fg (fgBlock P b rows)).F = st.fg.F then
              { st with
                base := (GridCO.admitProposal p.toParams.engine st.base
                  (baseProposal s b raw sup) b (raw.map baseHead)),
                fg := Window.on_block p p.K_W st.fg (fgBlock P b rows),
                proposals := st.proposals ++ [⟨.proposer s, .proposal b raw sup rows⟩] }
            else reconcile { st with
                base := (GridCO.admitProposal p.toParams.engine st.base
                  (baseProposal s b raw sup) b (raw.map baseHead)),
                fg := Window.on_block p p.K_W st.fg (fgBlock P b rows),
                proposals := st.proposals ++ [⟨.proposer s, .proposal b raw sup rows⟩] })
          else st)
      cases hp : parentFG st b with
      | none => exact h
      | some P =>
        dsimp only
        split
        · apply nv_rows_fold _ _ _ hr
          have hs : EmissionRowsValid
              { st with
                base := (GridCO.admitProposal p.toParams.engine st.base
                  (baseProposal s b raw sup) b (raw.map baseHead)),
                fg := Window.on_block p p.K_W st.fg (fgBlock P b rows),
                proposals := st.proposals ++ [⟨.proposer s, .proposal b raw sup rows⟩] } := by
            refine ⟨h.1, ?_⟩
            intro w hw s' b' raw' sup' rows' hd'
            rcases List.mem_append.mp hw with hm | hm
            · exact h.2 w hm s' b' raw' sup' rows' hd'
            · have hew := List.mem_singleton.mp hm
              subst w
              change some (Input.block s b raw sup rows) =
                some (Input.block s' b' raw' sup' rows') at hd'
              cases hd'
              exact hr
          split
          · exact hs
          · constructor
            · rw [(reconcile_frame _).2.2.1]; exact hs.1
            · rw [(reconcile_frame _).2.1]; exact hs.2
        · exact h


theorem nv_attest_valid (st : State p.n) (Λ : RecordOnce) (j : Fin p.n)
    (body : RowPayload) (hbody : (attest p st Λ j).1 = some body) : body.valid = true := by
  obtain ⟨a, ha, hp⟩ := Option.map_eq_some_iff.mp hbody
  obtain ⟨h, T, timeout, hh, he, _, _, _⟩ :=
    KitFG.createRowOnce_released p.E p.cfg Λ j (fgInputs p st).1 (fgInputs p st).2 ha
  have hf := KitFG.height_pair_vote_fields hh
  obtain ⟨C, _, hc⟩ := Option.map_eq_some_iff.mp hf
  have heh := congrArg Prod.fst hc
  change (derive p.E p.cfg C).h = h at heh
  have hpos : 1 ≤ h := heh ▸ KitFG.one_le_h p.E p.cfg C
  rw [← hp, he]
  change (decide (1 ≤ h) &&
    ((finality_pair Λ.toRecord (fgInputs p st).2).filter (fun fp => decide (fp.height < h))
      |>.map (fun fp => decide (fp.height < h))).getD true) = true
  cases hfp : finality_pair Λ.toRecord (fgInputs p st).2 with
  | none => simp [hpos, Option.filter]
  | some fp =>
      by_cases hlt : fp.height < h <;> simp [hpos, Option.filter, hlt]

theorem nv_proposal_rows (st : State p.n) (H : Block)
    (hv : EmissionRowsValid st) : ∀ a ∈ proposalRows p st H, a.valid = true := by
  intro a ha
  rw [proposalRows_eq_proposalRowsFor] at ha
  rcases proposalRowsFor_origin p st (st.slot p) H a ha with
    hm | ⟨o, ho, s, b, raw, sup, rows, hd, hm⟩
  · exact hv.1 a hm
  · exact hv.2 o ho s b raw sup rows hd a hm

theorem nv_proposal_votes (st : State p.n) (s : Slot) :
    (∀ a ∈ (proposerVotes st s).filterMap liftHead?,
      ∃ j b, a.decode? = some (s - 1, j, b)) ∧
    (∀ a ∈ (proposerSupport st s).filterMap liftHead?,
      a ∈ (proposerVotes st s).filterMap liftHead?) := by
  constructor
  · intro a ha
    obtain ⟨w, hw, hl⟩ := List.mem_filterMap.mp ha
    have ht : GridCO.headLabel? w = some (s - 1) :=
      beq_iff_eq.mp (List.mem_filter.mp hw).2
    change (GridCO.headLabel? w >>= fun r => GridCO.headSeat? w >>= fun j =>
      GridCO.headTarget? w >>= fun b => some ⟨.seat (.head r) j, b⟩) = some a at hl
    rw [ht] at hl
    obtain ⟨r, hr, hl⟩ := Option.bind_eq_some_iff.mp hl
    have her := Option.some.inj hr
    subst r
    obtain ⟨j, _, hl⟩ := Option.bind_eq_some_iff.mp hl
    obtain ⟨b, _, he⟩ := Option.bind_eq_some_iff.mp hl
    cases he
    exact ⟨j, b, rfl⟩
  · intro a ha
    obtain ⟨w, hw, he⟩ := List.mem_filterMap.mp ha
    exact List.mem_filterMap.mpr ⟨w, (List.mem_filter.mp hw).1, he⟩


theorem nv_proposal_wf (st : State p.n) (s : Slot) (a : Nat)
    (hv : EmissionRowsValid st)
    (hp : (getHead p st (proposerVotes st s) (proposerSupport st s)).slot < s)
    {m : Msg p.n} (hm : (propose p st s).map (withApp a) = some m) :
    FGSA.wellFormed p ⟨.proposer s, m⟩ = true := by
  have hs0 : 0 < s := Nat.zero_lt_of_lt hp
  let H := getHead p st (proposerVotes st s) (proposerSupport st s)
  let rows := proposalRows p st H
  have he : m = .proposal (.node H s (packBody a rows))
      ((proposerVotes st s).filterMap liftHead?)
      ((proposerSupport st s).filterMap liftHead?) rows := by
    change (if s = 0 then none else some (.proposal (.node H s (packBody 0 rows))
      ((proposerVotes st s).filterMap liftHead?)
      ((proposerSupport st s).filterMap liftHead?) rows)).map
        (withApp a) = some m at hm
    rw [ite_eq_right (Nat.ne_of_gt hs0)] at hm
    exact (Option.some.inj hm).symm
  have hcontent := rowsOk_withApp st s a hm
  rw [he]
  change (true && (s == s) && decide (H.slot < s) &&
    ((proposerVotes st s).filterMap liftHead?).all (fun v => match v.decode? with
      | some (r, _, _) => r + 1 == s | none => false) &&
    ((proposerSupport st s).filterMap liftHead?).all
      (fun v => decide (v ∈ (proposerVotes st s).filterMap liftHead?)) &&
    rows.all RowWire.valid &&
    rowsOk (.node H s (packBody a rows)) rows) = true
  obtain ⟨hraw, hsup⟩ := nv_proposal_votes st s
  have hr : rows.all RowWire.valid = true :=
    List.all_eq_true.mpr (nv_proposal_rows st H hv)
  have hvotes : ((proposerVotes st s).filterMap liftHead?).all (fun v => match v.decode? with
      | some (r, _, _) => r + 1 == s | none => false) = true := by
    apply List.all_eq_true.mpr
    intro v hv
    obtain ⟨j, b, hd⟩ := hraw v hv
    rw [hd]
    exact beq_iff_eq.mpr (Nat.sub_add_cancel hs0)
  have hsupport : ((proposerSupport st s).filterMap liftHead?).all
      (fun v => decide (v ∈ (proposerVotes st s).filterMap liftHead?)) = true :=
    List.all_eq_true.mpr (fun v hv => decide_eq_true (hsup v hv))
  have hc : rowsOk (.node H s (packBody a rows)) rows = true := by
    obtain ⟨H', raw', sup', rows', he', hc, -⟩ := hcontent
    rw [he] at he'
    have eqs := Msg.proposal.inj he'
    have hb := Block.node.inj eqs.1
    rw [← hb.1, ← eqs.2.2.2] at hc
    exact hc
  rw [hvotes, hsupport, hr, hc]
  simp only [beq_self_eq_true, Bool.true_and, Bool.and_true, decide_eq_true_eq]
  exact hp


theorem nv_proposal_shape (st : State p.n) (s : Slot) (app : Nat)
    (b : Block) (raw sup : List (HeadWire p.n)) (rows : List (RowWire p.n))
    (ha : (propose p st s).map (withApp app) = some (.proposal b raw sup rows)) :
    b = .node (getHead p st (proposerVotes st s) (proposerSupport st s)) s (packBody app rows) ∧
      raw = (proposerVotes st s).filterMap liftHead? ∧
      sup = (proposerSupport st s).filterMap liftHead? ∧
      rows = proposalRows p st (getHead p st (proposerVotes st s) (proposerSupport st s)) := by
  unfold propose at ha
  split at ha
  · cases ha
  · simp only [Option.map_some, withApp, Option.some.injEq, Msg.proposal.injEq] at ha
    obtain ⟨rfl, rfl, rfl, rfl⟩ := ha
    exact ⟨rfl, rfl, rfl, rfl⟩

theorem nv_wire_cases (o : Obj p) (hw : (fgsa p c).wellFormed o = true) :
    (∃ s j b, o = ofHead p ⟨.seat (.head s) j, b⟩) ∨
    (∃ j body, o = ofRow p ⟨.seat .fg j, body⟩) ∨
    (∃ s b raw sup rows, o = (⟨.seat (.prop s) ⟨0, Nat.one_pos⟩,
      .proposal b raw sup rows⟩ : Obj p)) := by
  cases hd : (toWire p o).decode with
  | none => change FGSA.wellFormed p (toWire p o) = true at hw
            simp only [FGSA.wellFormed, hd] at hw
            cases hw
  | some m =>
    have hinj := (toWireEquiv p).injective
    have he (w : Wire p.n) (h : toWire p o = w) : o = ofWire p w := by
      apply hinj
      exact h.trans ((toWireEquiv p).right_inv w).symm
    cases m with
    | vote s j b => exact Or.inl ⟨s, j, b, he _ (decode_eq_vote.mp hd)⟩
    | row j body => exact Or.inr (Or.inl ⟨j, body, he _ (decode_eq_row.mp hd)⟩)
    | block s b raw sup rows =>
      exact Or.inr (Or.inr ⟨s, b, raw, sup, rows, he _ (decode_eq_block.mp hd)⟩)

theorem nv_liftHead (w : GridCO.Wire p.n) (a : HeadWire p.n) (ha : liftHead? w = some a) :
    baseVote a = w ∧ ∃ s j b, a = ⟨.seat (.head s) j, b⟩ := by
  obtain ⟨auth, m⟩ := w
  cases auth with
  | seat s j =>
    cases m with
    | head b =>
      change some (⟨.seat (.head s) j, b⟩ : HeadWire p.n) = some a at ha
      cases ha
      exact ⟨rfl, s, j, b, rfl⟩
    | proposal => change none = some a at ha; cases ha
  | proposer => cases m <;> change none = some a at ha <;> cases ha
  | none => cases m <;> change none = some a at ha <;> cases ha

theorem nv_handles_carries (st : State p.n) (o o' : Obj p) (hh : handlesS p st o o') :
    o = o' ∨ carriesS p o o' := by
  rcases hh with he | hh
  · exact Or.inl he
  · right
    cases hd : (toWire p o).decode with
    | none => simp only [hd] at hh
    | some m =>
      cases m with
      | vote | row => simp only [hd] at hh
      | block s b raw sup rows =>
        rw [hd] at hh
        have he := congrArg Signed.payload (decode_eq_block.mp hd)
        change o.payload = .proposal b raw sup rows at he
        change carriesS p o o'
        rw [carriesS, he]
        exact hh.2.imp_right (fun h => Or.inr h)

theorem nv_carries_payload (o o' : Obj p) (b : Block) (raw sup : List (HeadWire p.n))
    (rows : List (RowWire p.n)) (he : o.payload = .proposal b raw sup rows)
    (hc : o' ∈ raw.map (ofHead p) ∨ o' ∈ sup.map (ofHead p) ∨ o' ∈ rows.map (ofRow p)) :
    carriesS p o o' := by
  rw [carriesS, he]
  exact hc
end EmissionHelpers

open AvailableChain.SimplexFG
open AvailableChain.V2.D.Engine

abbrev Object := (fgsa params unitCodec).Object
abbrev Event := V2.Event (Fin 1) Object
abbrev FixtureNode := (fgsa params unitCodec).State

def mkRun (es : List Event) : V2.D.Run (Fin 1) (fgsa params unitCodec) where
  honest := Finset.univ
  horizon := horizon
  events := es
  seatOf := fun _ _ => 0
  input := fun _ _ => ()

/-- One tick, then one delivery of each released object, in release order. -/
def batch (acc : List Event × FixtureNode) (n : Nat) : List Event × FixtureNode :=
  let out := V2.D.tick env (mkRun []) acc.2 0 (n : Time)
  (acc.1 ++ [.tick 0 (n : Time)] ++ out.2.map (fun o => .deliver 0 o (n : Time)),
    out.2.foldl (fgsa params unitCodec).process out.1)

/-- The cached node avoids a repeated fold of all preceding events. -/
def runPrefix (n : Nat) : List Event × FixtureNode :=
  (List.range n).foldl batch ([], (fgsa params unitCodec).init)

def run := mkRun (runPrefix 305).1

theorem runPrefix_zero : runPrefix 0 = ([], (fgsa params unitCodec).init) := rfl

theorem runPrefix_succ (n : Nat) : runPrefix (n + 1) = batch (runPrefix n) n := by
  simp [runPrefix, List.range_succ, List.foldl_append]

theorem duties_length (t : Time) : (duties params t).length ≤ 1 := by
  have hp : SA.proposalTime params.toParams (params.slotOf t) = 4 * (params.slotOf t : Time) := rfl
  have hv : SA.voteTime params.toParams (params.slotOf t) = 4 * (params.slotOf t : Time) + 1 := rfl
  have ha : params.actionTime ((params.slotOf t - 1) / params.R) =
      12 * (((params.slotOf t - 1) / params.R : Nat) : Time) + 6 := by
    change 4 * ((((params.slotOf t - 1) / params.R) * 3 : Nat) : Time) + 6 = _
    push_cast
    ring
  have hpa (a b : Time) : 4 * a ≠ 12 * b + 6 := by dsimp only [Time] at *; omega
  have hva (a b : Time) : 4 * a + 1 ≠ 12 * b + 6 := by dsimp only [Time] at *; omega
  simp only [duties, hp, hv, ha]
  split_ifs <;> simp_all
  · exact hpa (params.slotOf t : Time) ((params.slotOf t - 1 : Nat) / (params.R : Time))
      (by dsimp only [Time] at *; omega)
  · exact hva (params.slotOf t : Time) ((params.slotOf t - 1 : Nat) / (params.R : Time))
      (by dsimp only [Time] at *; omega)

theorem ownSeats_single (d : RunDuty) :
    (mkRun []).ownSeats (RunDuty.signLabel d) 0 = [⟨0, by cases d <;> exact Nat.one_pos⟩] := by
  cases d <;> change (List.finRange 1).filter (fun _ => decide ((0 : Fin 1) = 0)) = [0]
  all_goals decide

theorem released_length (nd : FixtureNode) (t : Time) :
    (V2.D.tick env (mkRun []) nd 0 t).2.length ≤ 1 := by
  change (((duties params t).flatMap (fun d =>
    ((mkRun []).ownSeats (RunDuty.signLabel d) 0).filterMap (fun i =>
      ((fgsa params unitCodec).act ((fgsa params unitCodec).clock nd t) d ()).map
        (fun m => (⟨.seat (RunDuty.signLabel d) i, m⟩ : Object))))) ++ []).length ≤ 1
  rw [List.append_nil]
  have h := duties_length t
  cases he : duties params t with
  | nil => simp
  | cons d ds =>
    have hds : ds = [] := by simpa [he] using h
    rw [hds]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, ownSeats_single,
      List.filterMap_cons, List.filterMap_nil]
    split <;> simp

theorem prefix_events_time (n : Nat) :
    ∀ e ∈ (runPrefix n).1, ∃ m < n, e.time = (m : Time) ∧
      (e = .tick 0 (m : Time) ∨ ∃ o, e = .deliver 0 o (m : Time)) := by
  induction n with
  | zero => simp [runPrefix_zero]
  | succ n ih =>
    rw [runPrefix_succ]
    intro e he
    simp only [batch, List.mem_append, List.mem_singleton, List.mem_map] at he
    rcases he with (he | he) | ⟨o, _, he⟩
    · obtain ⟨m, hm, ht, he⟩ := ih e he
      exact ⟨m, by omega, ht, he⟩
    · subst e; exact ⟨n, Nat.lt_succ_self n, rfl, Or.inl rfl⟩
    · subst e; exact ⟨n, Nat.lt_succ_self n, rfl, Or.inr ⟨o, rfl⟩⟩

theorem prefix_ticks (n m : Nat) (hm : m < n) : .tick 0 (m : Time) ∈ (runPrefix n).1 := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [runPrefix_succ]
    by_cases hmn : m < n
    · exact List.mem_append_left _ (List.mem_append_left _ (ih hmn))
    · have he : m = n := by omega
      subst m
      exact List.mem_append_left _ (List.mem_append_right _ (List.mem_singleton_self _))

theorem prefix_mono {n m : Nat} (h : n ≤ m) :
    (runPrefix n).1.IsPrefix (runPrefix m).1 := by
  induction m with
  | zero =>
    have hn : n = 0 := by omega
    subst n
    exact List.prefix_refl _
  | succ m ih =>
    by_cases hn : n ≤ m
    · apply (ih hn).trans
      rw [runPrefix_succ]
      dsimp only [batch]
      rw [List.append_assoc]
      exact List.prefix_append _ _
    · have : n = m + 1 := by omega
      subst n; exact List.prefix_refl _

theorem step_constant (nd : FixtureNode) (e : Event) :
    V2.D.World.step env (mkRun []) (fun _ => nd) e =
      fun _ => match e with
      | .restart _ _ => (fgsa params unitCodec).restore nd.record
      | .tick _ t => (V2.D.tick env (mkRun []) nd 0 t).1
      | .deliver _ o _ => (fgsa params unitCodec).process nd o := by
  funext v
  have hv : v = 0 := Subsingleton.elim _ _
  subst v
  cases e with
  | restart w t => have hw : w = 0 := Subsingleton.elim _ _; subst w; rfl
  | tick w t => have hw : w = 0 := Subsingleton.elim _ _; subst w; rfl
  | deliver w o t => have hw : w = 0 := Subsingleton.elim _ _; subst w; rfl

theorem fold_deliveries (os : List Object) (nd : FixtureNode) (t : Time) :
    (os.map (fun o => (.deliver 0 o t : Event))).foldl
        (V2.D.World.step env (mkRun [])) (fun _ => nd) =
      fun _ => os.foldl (fgsa params unitCodec).process nd := by
  induction os generalizing nd with
  | nil => rfl
  | cons o os ih =>
    rw [List.map_cons, List.foldl_cons, List.foldl_cons, step_constant]
    exact ih _

/-- The cached node equals the engine fold, for every prefix length. -/
theorem prefix_cached (n : Nat) :
    (runPrefix n).1.foldl (V2.D.World.step env (mkRun [])) V2.D.World.init =
      fun _ => (runPrefix n).2 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [runPrefix_succ]
    simp only [batch, List.foldl_append, ih]
    rw [List.foldl_cons, List.foldl_nil, step_constant, fold_deliveries]

def batchEvents (n : Nat) : List Event :=
  [.tick 0 (n : Time)] ++
    (V2.D.tick env (mkRun []) (runPrefix n).2 0 (n : Time)).2.map
      (fun o => .deliver 0 o (n : Time))

theorem prefix_flat (n : Nat) :
    (runPrefix n).1 = (List.range n).flatMap batchEvents := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [runPrefix_succ, batch, List.range_succ, List.flatMap_append,
      List.flatMap_cons, List.flatMap_nil, List.append_nil, batchEvents]
    rw [← ih, List.append_assoc]

theorem tick_at (n : Nat) (hn : n < 305) :
    run.events[(runPrefix n).1.length]? = some (.tick 0 (n : Time)) := by
  obtain ⟨tail, he⟩ := prefix_mono (show n + 1 ≤ 305 by omega)
  change (runPrefix 305).1[(runPrefix n).1.length]? = _
  rw [← he, runPrefix_succ]
  simp [batch, List.append_assoc]

theorem state_before_tick (n : Nat) (hn : n < 305) :
    V2.D.Run.stateBefore env run (runPrefix n).1.length = fun _ => (runPrefix n).2 := by
  obtain ⟨tail, he⟩ := prefix_mono (show n ≤ 305 by omega)
  unfold V2.D.Run.stateBefore
  change ((runPrefix 305).1.take (runPrefix n).1.length).foldl
      (V2.D.World.step env run) V2.D.World.init = _
  rw [← he]
  simp only [List.take_append, List.take_length, Nat.sub_self, List.take_zero,
    List.append_nil]
  exact prefix_cached n

theorem emits_at_tick (n : Nat) (hn : n < 305) :
    V2.D.Run.emitsAt env run (runPrefix n).1.length =
      (V2.D.tick env (mkRun []) (runPrefix n).2 0 (n : Time)).2 := by
  rw [V2.D.Run.emitsAt, tick_at n hn, state_before_tick n hn]
  rfl

theorem immediate_delivery (n : Nat) (hn : n < 305) (o : Object)
    (ho : o ∈ (V2.D.tick env (mkRun []) (runPrefix n).2 0 (n : Time)).2) :
    run.events[(runPrefix n).1.length + 1]? = some (.deliver 0 o (n : Time)) := by
  have hos : (V2.D.tick env (mkRun []) (runPrefix n).2 0 (n : Time)).2 = [o] := by
    have hl := released_length (runPrefix n).2 (n : Time)
    cases he : (V2.D.tick env (mkRun []) (runPrefix n).2 0 (n : Time)).2 with
    | nil => simp [he] at ho
    | cons a as =>
      have has : as = [] := by simpa [he] using hl
      rw [he, has] at ho
      rw [has]
      exact (List.mem_singleton.mp ho) ▸ rfl
  obtain ⟨tail, he⟩ := prefix_mono (show n + 1 ≤ 305 by omega)
  change (runPrefix 305).1[(runPrefix n).1.length + 1]? = _
  rw [← he, runPrefix_succ]
  simp [batch, hos, List.append_assoc]

theorem prefix_strict (n : Nat) :
    (runPrefix n).1.Pairwise (fun e f => e.key < f.key) := by
  induction n with
  | zero => simp [runPrefix_zero]
  | succ n ih =>
    rw [runPrefix_succ]
    dsimp only [batch]
    rw [List.append_assoc, List.pairwise_append]
    refine ⟨ih, ?_, ?_⟩
    · have hl := released_length (runPrefix n).2 (n : Time)
      cases he : (V2.D.tick env (mkRun []) (runPrefix n).2 0 (n : Time)).2 with
      | nil => simp
      | cons o os =>
        have hos : os = [] := by simpa [he] using hl
        rw [hos]
        simp [V2.Event.key, V2.Event.time, V2.Event.phase, Prod.Lex.lt_iff]
    · intro e he f hf
      obtain ⟨m, hm, ht, _⟩ := prefix_events_time n e he
      have hft : f.time = (n : Time) := by
        simp only [List.mem_append, List.mem_singleton, List.mem_map] at hf
        rcases hf with rfl | ⟨o, _, rfl⟩ <;> rfl
      apply Prod.Lex.lt_iff.mpr
      left
      change e.time < f.time
      rw [ht, hft]
      exact_mod_cast hm

theorem nvSchedule : V2.D.ScheduleWellFormed env run where
  horizon_nonneg := le_of_lt horizon_pos
  sorted := (prefix_strict 305).imp (fun h => le_of_lt h)
  nodup := by
    have hne : run.events.Pairwise (fun e f => e ≠ f) :=
      (prefix_strict 305).imp (fun h he => by rw [he] at h; exact lt_irrefl _ h)
    exact hne
  in_horizon := by
    intro e he
    obtain ⟨m, hm, ht, _⟩ := prefix_events_time 305 e he
    rw [ht]
    change 0 ≤ (m : Time) ∧ (m : Time) ≤ 304
    exact ⟨Int.natCast_nonneg m, by dsimp only [Time] at *; omega⟩
  honest_only := by intro e _; exact Finset.mem_univ _
  tick_public := by
    intro v t he
    obtain ⟨m, _, ht, _⟩ := prefix_events_time 305 (.tick v t) he
    exact ⟨m, by simpa only [V2.Event.time, env, Int.mul_one] using ht⟩
  tick_total := by
    intro v _ t _ ht hh
    have hv : v = 0 := Subsingleton.elim _ _
    subst v
    change t ≤ 304 at hh
    have he : t = (t.toNat : Time) := (Int.toNat_of_nonneg ht).symm
    rw [he]
    exact prefix_ticks 305 t.toNat (by dsimp only [Time] at *; omega)

theorem noRestart : V2.D.NoRestart run := by
  intro i v t hi
  obtain ⟨_, _, _, he⟩ := prefix_events_time 305 (.restart v t) (List.mem_of_getElem? hi)
  rcases he with he | ⟨o, he⟩ <;> cases he

set_option maxHeartbeats 2000000 in
-- Index uniqueness uses the symbolic prefix proof through the concrete run type.
theorem delivery_source {i : Nat} {v : Fin 1} {o : Object} {t : Time}
    (hi : run.events[i]? = some (.deliver v o t)) :
    ∃ n : Nat, n < 305 ∧ t = (n : Time) ∧ i = (runPrefix n).1.length + 1 ∧
      o ∈ (V2.D.tick env (mkRun []) (runPrefix n).2 0 (n : Time)).2 := by
  have hm := List.mem_of_getElem? hi
  rw [show run.events = (runPrefix 305).1 from rfl, prefix_flat] at hm
  obtain ⟨n, hn, hm⟩ := List.mem_flatMap.mp hm
  have hn' : n < 305 := List.mem_range.mp hn
  simp only [batchEvents, List.mem_append, List.mem_singleton, List.mem_map] at hm
  rcases hm with he | ⟨a, ha, he⟩
  · cases he
  · cases he
    have hd := immediate_delivery n hn' o ha
    obtain ⟨hil, hei⟩ := List.getElem?_eq_some_iff.mp hi
    obtain ⟨hjl, hej⟩ := List.getElem?_eq_some_iff.mp hd
    have hij : i = (runPrefix n).1.length + 1 :=
      (nvSchedule.nodup.getElem_inj_iff (hi := hil) (hj := hjl)).mp (hei.trans hej.symm)
    exact ⟨n, hn', rfl, hij, ha⟩

theorem tick_source {i : Nat} {v : Fin 1} {t : Time}
    (hi : run.events[i]? = some (.tick v t)) :
    ∃ n : Nat, n < 305 ∧ t = (n : Time) ∧ i = (runPrefix n).1.length := by
  obtain ⟨n, hn, ht, _⟩ := prefix_events_time 305 (.tick v t) (List.mem_of_getElem? hi)
  change t = (n : Time) at ht
  have hv : v = 0 := Subsingleton.elim _ _
  subst v
  have hd := tick_at n hn
  rw [← ht] at hd
  obtain ⟨hil, hei⟩ := List.getElem?_eq_some_iff.mp hi
  obtain ⟨hjl, hej⟩ := List.getElem?_eq_some_iff.mp hd
  exact ⟨n, hn, ht,
    (nvSchedule.nodup.getElem_inj_iff (hi := hil) (hj := hjl)).mp (hei.trans hej.symm)⟩

theorem sync : Gen.V2.Duty.PartialSynchronyBy env run (fgsaDelay env.Δ deltaF) where
  broadcast_emitted := by
    rintro v _ o t ⟨i, hi, ho⟩ w _ _ _
    obtain ⟨n, hn, rfl, rfl⟩ := tick_source hi
    rw [emits_at_tick n hn] at ho
    have hw : w = 0 := Subsingleton.elim _ _
    subst w
    refine ⟨(n : Time), le_rfl, ?_, (runPrefix n).1.length + 1, o,
      immediate_delivery n hn o ho, Or.inl rfl⟩
    have hd : 0 < fgsaDelay (p := params) env.Δ deltaF o := by
      cases o with
      | mk a m =>
        cases m <;> simp only [fgsaDelay, env, deltaF] <;> decide
    change (n : Int) < max (n : Int) 0 + fgsaDelay env.Δ deltaF o
    dsimp only [Time] at hd
    omega
  relay_accepted := by
    intro v _ i o t ha w _ hp
    have hvw : v = w := Subsingleton.elim _ _
    subst w
    rw [ha.2.2] at hp
    contradiction

theorem emitted_wire (n : Nat) (hn : n < 305)
    (hr : EmissionRowsValid (runPrefix n).2.st) (o : Object)
    (ho : o ∈ (V2.D.tick env (mkRun []) (runPrefix n).2 0 (n : Time)).2) :
    (fgsa params unitCodec).wellFormed o = true := by
  have hi := tick_at n hn
  have hc := state_before_tick n hn
  obtain ⟨auth, m⟩ := o
  cases auth with
  | none =>
    change (⟨.none, m⟩ : Object) ∈
      (duties params (n : Time)).flatMap (fun d =>
        ((mkRun []).ownSeats (RunDuty.signLabel d) 0).filterMap (fun j =>
          ((fgsa params unitCodec).act ((fgsa params unitCodec).clock (runPrefix n).2
            (n : Time)) d ()).map (fun m => ⟨.seat (RunDuty.signLabel d) j, m⟩))) ++ [] at ho
    rw [List.append_nil] at ho
    obtain ⟨d, _, ho⟩ := List.mem_flatMap.mp ho
    obtain ⟨j, _, ho⟩ := List.mem_filterMap.mp ho
    obtain ⟨m', _, he⟩ := Option.map_eq_some_iff.mp ho
    cases he
  | seat l j =>
    obtain ⟨_, _, d, hl, ht, ha⟩ :=
      (mem_tick_seat_iff env (mkRun []) (runPrefix n).2 0 (n : Time) l j m).mp ho
    change RunDuty.signLabel d = l at hl
    cases d with
    | headAction s =>
      change RunLabel.base (.head s) = l at hl
      subst l
      have he : .head (headVote params (FGSA.clock params (runPrefix n).2.st (n : Time)) s) = m :=
        Option.some.inj ha
      subst m
      rfl
    | fgAction r =>
      change RunLabel.base .fg = l at hl
      subst l
      change (attest params (FGSA.clock params (runPrefix n).2.st (n : Time))
        (runPrefix n).2.record ⟨0, params.nPos⟩).1.map Msg.row = some m at ha
      obtain ⟨body, hb, hm⟩ := Option.map_eq_some_iff.mp ha
      subst m
      exact nv_attest_valid _ _ _ _ hb
    | propAction s =>
      change RunLabel.prop s = l at hl
      subst l
      change SA.proposalTime params.toParams s = (n : Time) at ht
      change (propose params (FGSA.clock params (runPrefix n).2.st (n : Time)) s).map
        (withApp 0) = some m at ha
      have hs0 : 0 < s := by
        by_contra hh
        have hs : s = 0 := Nat.eq_zero_of_not_pos hh
        subst s
        change none = some m at ha
        cases ha
      have hp := fgsa_propose_parent_lt env run nvSchedule (ht.symm ▸ hi) hs0
      rw [hc] at hp
      rw [ht] at hp
      exact nv_proposal_wf _ s 0 (nv_rows_clock _ _ hr) hp ha

theorem prefix_rows (n : Nat) (hn : n ≤ 305) : EmissionRowsValid (runPrefix n).2.st := by
  induction n with
  | zero => exact ⟨fun _ h => (List.not_mem_nil h).elim,
      fun _ h => (List.not_mem_nil h).elim⟩
  | succ n ih =>
    have hn' : n < 305 := by omega
    have hr := ih (by omega)
    have hw := emitted_wire n hn' hr
    rw [runPrefix_succ]
    dsimp only [batch]
    have hclock : EmissionRowsValid
        (V2.D.tick env (mkRun []) (runPrefix n).2 0 (n : Time)).1.st := by
      exact (tick_st (c := unitCodec) env (mkRun []) (runPrefix n).2 0 (n : Time)).symm ▸
        nv_rows_clock _ _ hr
    generalize (V2.D.tick env (mkRun []) (runPrefix n).2 0 (n : Time)).1 = nd at *
    generalize (V2.D.tick env (mkRun []) (runPrefix n).2 0 (n : Time)).2 = os at *
    induction os generalizing nd with
    | nil => exact hclock
    | cons a os ih =>
      rw [List.foldl_cons]
      exact ih _ (nv_rows_process nd.st a hclock (hw a (List.mem_cons_self ..)))
        (fun o ho => hw o (List.mem_cons_of_mem a ho))

theorem wire : ∀ (i : Nat) (v : Fin 1) (o : Object) (t : Time),
    run.events[i]? = some (.deliver v o t) →
    (fgsa params unitCodec).wellFormed o = true := by
  intro i v o t hi
  obtain ⟨n, hn, _, _, ho⟩ := delivery_source hi
  exact emitted_wire n hn (prefix_rows n (by omega)) o ho

theorem state_delivery_store (n : Nat) (hn : n < 305) :
    (V2.D.Run.stateBefore env run ((runPrefix n).1.length + 1) 0).st =
      FGSA.clock params (runPrefix n).2.st (n : Time) := by
  have hs := (V2.D.Run.step_tick_eq env run (tick_at n hn)).1
  rw [state_before_tick n hn] at hs
  exact (congrArg Node.st hs).trans
    (tick_st (c := unitCodec) env run (runPrefix n).2 0 (n : Time))

theorem emitted_deps (n : Nat) (hn : n < 305) (o : Object)
    (ho : o ∈ (V2.D.tick env (mkRun []) (runPrefix n).2 0 (n : Time)).2) :
    depsS params (FGSA.clock params (runPrefix n).2.st (n : Time)) o = true := by
  have hw := emitted_wire n hn (prefix_rows n (by omega)) o ho
  rcases nv_wire_cases o hw with ⟨s, j, b, rfl⟩ | ⟨j, body, rfl⟩ |
    ⟨s, b, raw, sup, rows, rfl⟩
  · rfl
  · rfl
  · have ha := (fgsa_emits_proposal env (mkRun []) (runPrefix n).2 0 (n : Time) s
      (.proposal b raw sup rows)).mp ho
    obtain ⟨hb, _, _, _⟩ := nv_proposal_shape _ s 0 b raw sup rows ha.2.2.2
    have hc := (storeBundle_postClock env run (runPrefix n).1.length 0 (n : Time)).cstore
    rw [state_before_tick n hn] at hc
    let st := FGSA.clock params (runPrefix n).2.st (n : Time)
    let H := getHead params st (proposerVotes st s) (proposerSupport st s)
    obtain ⟨B, hB, he⟩ := (hc.baseTree H).mp (getHead_stored params st hc _ _)
    have hl := (fgBlockOf_spec params st hc H B).mpr ⟨hB, he⟩
    rw [hb]
    change (fgBlockOf st H).isSome = true
    rw [hl]
    rfl

theorem deps : ∀ (i : Nat) (v : Fin 1) (o : Object) (t : Time),
    run.events[i]? = some (.deliver v o t) →
    (fgsa params unitCodec).depsPresent (V2.D.Run.stateBefore env run i v) o = true := by
  intro i v o t hi
  obtain ⟨n, hn, _, rfl, ho⟩ := delivery_source hi
  have hv : v = 0 := Subsingleton.elim _ _
  subst v
  change depsS params _ o = true
  rw [state_delivery_store n hn]
  exact emitted_deps n hn o ho

theorem earlier_batch {i n : Nat} {v : Fin 1} {o : Object} {t : Time}
    (hi : run.events[i]? = some (.deliver v o t)) (hin : i < (runPrefix n).1.length) :
    ∃ m : Nat, m < n ∧ m < 305 ∧ t = (m : Time) ∧
      o ∈ (V2.D.tick env (mkRun []) (runPrefix m).2 0 (m : Time)).2 := by
  obtain ⟨m, hm, ht, he, ho⟩ := delivery_source hi
  refine ⟨m, ?_, hm, ht, ho⟩
  by_contra hh
  have hl := (prefix_mono (Nat.le_of_not_gt hh)).length_le
  omega

theorem carried_from_state (n : Nat) (hn : n < 305) (o o' : Object)
    (ho : o ∈ (V2.D.tick env (mkRun []) (runPrefix n).2 0 (n : Time)).2)
    (hc : carriesS params o o') :
    (∃ s j b, o' = ofHead params ⟨.seat (.head s) j, b⟩ ∧
      (⟨.seat s j, .head b⟩ : GridCO.Wire params.n) ∈ (runPrefix n).2.st.base.votes) ∨
    (∃ a : RowWire params.n, o' = ofRow params a ∧
      (a ∈ (runPrefix n).2.st.rowPool ∨
        ∃ w ∈ (runPrefix n).2.st.proposals, ∃ s b raw sup rows,
          w.decode = some (.block s b raw sup rows) ∧ a ∈ rows)) := by
  have hw := emitted_wire n hn (prefix_rows n (by omega)) o ho
  rcases nv_wire_cases o hw with ⟨s, j, b, rfl⟩ | ⟨j, body, rfl⟩ |
    ⟨s, b, raw, sup, rows, rfl⟩
  · exact hc.elim
  · exact hc.elim
  · have ha := (fgsa_emits_proposal env (mkRun []) (runPrefix n).2 0 (n : Time) s
      (.proposal b raw sup rows)).mp ho
    obtain ⟨_, hraw, hsup, hrows⟩ := nv_proposal_shape _ s 0 b raw sup rows ha.2.2.2
    let st := FGSA.clock params (runPrefix n).2.st (n : Time)
    have heads (xs : List (HeadWire params.n))
        (hxs : ∀ a ∈ xs, a ∈ (proposerVotes st s).filterMap liftHead?)
        (hc' : o' ∈ xs.map (ofHead params)) :
        ∃ r j B, o' = ofHead params ⟨.seat (.head r) j, B⟩ ∧
          (⟨.seat r j, .head B⟩ : GridCO.Wire params.n) ∈ (runPrefix n).2.st.base.votes := by
      obtain ⟨a, hm, rfl⟩ := List.mem_map.mp hc'
      obtain ⟨w, hw, hl⟩ := List.mem_filterMap.mp (hxs a hm)
      obtain ⟨he, r, j, B, rfl⟩ := nv_liftHead w a hl
      have hpool : w ∈ st.base.votes := (List.mem_filter.mp hw).1
      rw [← he] at hpool
      change (⟨.seat r j, .head B⟩ : GridCO.Wire params.n) ∈
        (FGSA.clock params (runPrefix n).2.st (n : Time)).base.votes at hpool
      rw [(clock_vn (runPrefix n).2.st (n : Time)).1] at hpool
      exact ⟨r, j, B, rfl, hpool⟩
    rcases hc with hc | hc | hc
    · left
      rw [hraw] at hc
      exact heads _ (fun _ h => h) hc
    · left
      rw [hsup] at hc
      exact heads _ (nv_proposal_votes st s).2 hc
    · right
      obtain ⟨a, hm, rfl⟩ := List.mem_map.mp hc
      rw [hrows, proposalRows_eq_proposalRowsFor] at hm
      have horigin := proposalRowsFor_origin params st (st.slot params) _ a hm
      rcases horigin with hm | ⟨w, hw, r, B, raw', sup', rows', hd, hm⟩
      · rw [clock_rowPool] at hm
        exact ⟨a, rfl, Or.inl hm⟩
      · rw [clock_proposals] at hw
        exact ⟨a, rfl, Or.inr ⟨w, hw, r, B, raw', sup', rows', hd, hm⟩⟩

def EarlierEmitted (n : Nat) (o : Object) : Prop :=
  ∃ m : Nat, m < n ∧ m < 305 ∧
    o ∈ (V2.D.tick env (mkRun []) (runPrefix m).2 0 (m : Time)).2

theorem handled_before (n : Nat)
    (past : ∀ m : Nat, m < n → m < 305 → ∀ o o' : Object,
      o ∈ (V2.D.tick env (mkRun []) (runPrefix m).2 0 (m : Time)).2 →
      carriesS params o o' → EarlierEmitted m o')
    (j : Nat) (hj : j < (runPrefix n).1.length) (o : Object) (t : Time)
    (hh : V2.D.Run.handlesAt env run j 0 o t) : EarlierEmitted n o := by
  obtain ⟨parent, he, hh⟩ := hh
  obtain ⟨m, hmn, hm, _, ho⟩ := earlier_batch he hj
  rcases nv_handles_carries _ parent o hh with rfl | hc
  · exact ⟨m, hmn, hm, ho⟩
  · obtain ⟨k, hkm, hk, ho'⟩ := past m hmn hm parent o ho hc
    exact ⟨k, hkm.trans hmn, hk, ho'⟩

theorem carried_authentic (n : Nat) (hn : n < 305) (o o' : Object)
    (ho : o ∈ (V2.D.tick env (mkRun []) (runPrefix n).2 0 (n : Time)).2)
    (hc : carriesS params o o') : EarlierEmitted n o' := by
  induction n using Nat.strong_induction_on generalizing o o' with
  | h n ih =>
    have past := fun m hm => ih m hm
    have hbefore := handled_before n past
    rcases carried_from_state n hn o o' ho hc with ⟨s, j, b, rfl, hm⟩ |
      ⟨a, rfl, hm | ⟨w, hw, s, b, raw, sup, rows, hd, hm⟩⟩
    · have hp : (⟨.seat s j, .head b⟩ : GridCO.Wire params.n) ∈
          (V2.D.Run.stateBefore env run (runPrefix n).1.length 0).st.base.votes := by
        rw [state_before_tick n hn]
        exact hm
      rw [← fgsa_vote_stamp_keys env run (runPrefix n).1.length 0] at hp
      obtain ⟨⟨v, stamp⟩, hstamp, he⟩ := List.mem_map.mp hp
      dsimp only at he
      subst v
      obtain ⟨i, hi, t, ha, _⟩ := fgsa_vote_stamp_source env run (runPrefix n).1.length
        0 s j b stamp hstamp
      exact hbefore i hi _ t ha.1
    · have hp : a ∈ (V2.D.Run.stateBefore env run (runPrefix n).1.length 0).st.rowPool := by
        rw [state_before_tick n hn]
        exact hm
      obtain ⟨i, t, hi, hh, _⟩ := rowPool_provenance env run (runPrefix n).1.length 0 a hp
      exact hbefore i hi _ t hh
    · have hp : w ∈ (V2.D.Run.stateBefore env run (runPrefix n).1.length 0).st.proposals := by
        rw [state_before_tick n hn]
        exact hw
      obtain ⟨i, parent, t, hi, he, hwire, _, _⟩ :=
        stored_proposal_delivered env run (runPrefix n).1.length 0 w hp
      have hpay := congrArg Signed.payload (hwire.trans (decode_eq_block.mp hd))
      change parent.payload = .proposal b raw sup rows at hpay
      have hcarry : carriesS params parent (ofRow params a) := by
        exact nv_carries_payload parent _ b raw sup rows hpay
          (Or.inr (Or.inr (List.mem_map.mpr ⟨a, hm, rfl⟩)))
      obtain ⟨m, hmn, hmb, _, hem⟩ := earlier_batch he hi
      obtain ⟨k, hkm, hkb, hek⟩ := past m hmn hmb parent (ofRow params a) hem hcarry
      exact ⟨k, hkm.trans hmn, hkb, hek⟩

theorem head_pool_authentic (n : Nat) (hn : n < 305) (s : Slot) (j : Fin params.n) (b : Block)
    (hm : (⟨.seat s j, .head b⟩ : GridCO.Wire params.n) ∈ (runPrefix n).2.st.base.votes) :
    EarlierEmitted n (ofHead params ⟨.seat (.head s) j, b⟩) := by
  have hp : (⟨.seat s j, .head b⟩ : GridCO.Wire params.n) ∈
      (V2.D.Run.stateBefore env run (runPrefix n).1.length 0).st.base.votes := by
    rw [state_before_tick n hn]
    exact hm
  rw [← fgsa_vote_stamp_keys env run (runPrefix n).1.length 0] at hp
  obtain ⟨⟨v, stamp⟩, hstamp, he⟩ := List.mem_map.mp hp
  dsimp only at he
  subst v
  obtain ⟨i, hi, t, ha, _⟩ :=
    fgsa_vote_stamp_source env run (runPrefix n).1.length 0 s j b stamp hstamp
  exact handled_before n (fun m _ hmb o o' ho hc => carried_authentic m hmb o o' ho hc)
    i hi _ t ha.1

theorem row_pool_authentic (n : Nat) (hn : n < 305) (a : RowWire params.n)
    (hm : a ∈ (runPrefix n).2.st.rowPool) : EarlierEmitted n (ofRow params a) := by
  have hp : a ∈ (V2.D.Run.stateBefore env run (runPrefix n).1.length 0).st.rowPool := by
    rw [state_before_tick n hn]
    exact hm
  obtain ⟨i, t, hi, hh, _⟩ := rowPool_provenance env run (runPrefix n).1.length 0 a hp
  exact handled_before n (fun m _ hmb o o' ho hc => carried_authentic m hmb o o' ho hc)
    i hi _ t hh

theorem prefix_length_strict {m n : Nat} (h : m < n) :
    (runPrefix m).1.length < (runPrefix n).1.length := by
  have hs : (runPrefix m).1.length < (runPrefix (m + 1)).1.length := by
    rw [runPrefix_succ]
    simp only [batch, List.length_append, List.length_singleton, List.length_map]
    omega
  exact hs.trans_le (prefix_mono (show m + 1 ≤ n by omega)).length_le

theorem emitted_fresh (n : Nat) (hn : n < 305) (o : Object)
    (ho : o ∈ (V2.D.tick env (mkRun []) (runPrefix n).2 0 (n : Time)).2) :
    processedS params (FGSA.clock params (runPrefix n).2.st (n : Time)) o = false := by
  have hw := emitted_wire n hn (prefix_rows n (by omega)) o ho
  rcases nv_wire_cases o hw with ⟨s, j, b, rfl⟩ | ⟨j, body, rfl⟩ |
    ⟨s, b, raw, sup, rows, rfl⟩
  · change decide ((⟨.seat s j, .head b⟩ : GridCO.Wire params.n) ∈
      (FGSA.clock params (runPrefix n).2.st (n : Time)).base.votes) = false
    apply decide_eq_false
    intro hm
    rw [(clock_vn (runPrefix n).2.st (n : Time)).1] at hm
    obtain ⟨m, hmn, hmb, hem⟩ := head_pool_authentic n hn s j b hm
    have ht := ((fgsa_emits_head env (mkRun []) (runPrefix n).2 0 (n : Time) s j b).mp ho).2.1
    have hm' := ((fgsa_emits_head env (mkRun []) (runPrefix m).2 0 (m : Time) s j b).mp hem).2.1
    have he : (m : Time) = (n : Time) := hm'.symm.trans ht
    have hne : m = n := by exact_mod_cast he
    omega
  · change decide ((⟨.seat .fg j, body⟩ : RowWire params.n) ∈
      (FGSA.clock params (runPrefix n).2.st (n : Time)).rowPool) = false
    apply decide_eq_false
    intro hm
    rw [clock_rowPool] at hm
    obtain ⟨m, hmn, hmb, hem⟩ := row_pool_authentic n hn ⟨.seat .fg j, body⟩ hm
    obtain ⟨_, _, r, _, ha⟩ := (fgsa_emits_row env (mkRun []) (runPrefix n).2
      0 (n : Time) j body).mp ho
    have hsent := fgsa_row_sent_before env run 0 j body (prefix_length_strict hmn)
      (m : Time) (tick_at m hmb) ((emits_at_tick m hmb).symm ▸ hem)
    rw [state_before_tick n hn] at hsent
    exact attest_some_fresh _ _ _ _ ha hsent
  · have ha := (fgsa_emits_proposal env (mkRun []) (runPrefix n).2 0 (n : Time) s
      (.proposal b raw sup rows)).mp ho
    obtain ⟨hb, _, _, _⟩ := nv_proposal_shape _ s 0 b raw sup rows ha.2.2.2
    have hs0 : 0 < s := by
      by_contra hh
      have he : s = 0 := Nat.eq_zero_of_not_pos hh
      subst s
      have hnone := ha.2.2.2
      change (none : Option (Msg params.n)) = some (Msg.proposal b raw sup rows) at hnone
      cases hnone
    have ht := ha.2.1
    have hg := (fgsa_stored_block_slots env run nvSchedule (ht.symm ▸ tick_at n hn) hs0).2.2.2
    rw [state_before_tick n hn, ht] at hg
    change decide (∃ B ∈ (FGSA.clock params (runPrefix n).2.st (n : Time)).fg.TF,
      B.root = b.root) = false
    apply decide_eq_false
    rintro ⟨B, hB, hroot⟩
    have he : eraseFG B = b := Block.root_injective ((eraseFG_root B).trans hroot)
    have hslot : B.slot = s := (eraseFG_slot B).symm.trans
      ((congrArg Block.slot he).trans (by rw [hb]; rfl))
    have hh := hg B hB
    rw [hslot] at hh
    exact lt_irrefl s hh

theorem fresh : ∀ (i : Nat) (v : Fin 1) (o : Object) (t : Time),
    run.events[i]? = some (.deliver v o t) →
    (fgsa params unitCodec).processed (V2.D.Run.stateBefore env run i v) o = false := by
  intro i v o t hi
  obtain ⟨n, hn, _, rfl, ho⟩ := delivery_source hi
  have hv : v = 0 := Subsingleton.elim _ _
  subst v
  change processedS params _ o = false
  rw [state_delivery_store n hn]
  exact emitted_fresh n hn o ho

theorem nvExecution : V2.D.ExecutionValid env run where
  toScheduleWellFormed := nvSchedule
  wire := wire
  deps := deps
  fresh := fresh
  unforgeable := by
    rintro v o t ⟨i, hi⟩ u _ _
    obtain ⟨n, hn, rfl, _, ho⟩ := delivery_source hi
    have hu : u = 0 := Subsingleton.elim _ _
    subst u
    exact ⟨(n : Time), le_rfl, (runPrefix n).1.length, tick_at n hn,
      (emits_at_tick n hn).symm ▸ ho⟩
  carried := by
    rintro v o t ⟨i, hi⟩ o' hc u _ _
    obtain ⟨n, hn, rfl, _, ho⟩ := delivery_source hi
    obtain ⟨m, hmn, hm, hem⟩ := carried_authentic n hn o o' ho hc
    have hu : u = 0 := Subsingleton.elim _ _
    subst u
    exact ⟨(m : Time), by exact_mod_cast hmn.le, (runPrefix m).1.length, tick_at m hm,
      (emits_at_tick m hm).symm ▸ hem⟩

theorem base : Base₂ params unitCodec env run where
  valid := nvExecution
  linked := by
    refine ⟨1, Equiv.refl _, ?_⟩
    intro l hl
    rcases l with (_ | _) | _
    · exact hl.elim
    · exact ⟨rfl, fun i => Subsingleton.elim _ _⟩
    · exact hl.elim
  cstar := by
    intro l hl
    rcases l with (_ | _) | _
    · change Function.Bijective (fun _ : Fin 1 => (0 : Fin 1))
      exact ⟨fun _ _ _ => Subsingleton.elim _ _, fun v => ⟨0, Subsingleton.elim _ _⟩⟩
    · exact hl.elim
    · exact hl.elim
  noRestart := noRestart
  delta := env_delta

theorem honest_slot {s : Slot} (hs : 0 < s) :
    Gen.V2.Duty.HonestSlot run (fgsaInterface params unitCodec) s := by
  rw [Gen.V2.Duty.HonestSlot_def]
  exact ⟨hs, Finset.mem_univ _⟩

theorem proposer_gap (t : Time) (ht : env.t_GST ≤ t) :
    ∃ s, t < V2.D.proposalTime (fgsaInterface params unitCodec) s ∧
      V2.D.proposalTime (fgsaInterface params unitCodec) s ≤ t + gap ∧
      Gen.V2.Duty.HonestSlot run (fgsaInterface params unitCodec) s := by
  change 0 ≤ t at ht
  dsimp only [Time] at *
  have he : (t.toNat : Int) = t := Int.toNat_of_nonneg ht
  refine ⟨t.toNat / 4 + 1, ?_, ?_, honest_slot (by dsimp only [Slot]; omega)⟩
  · change t < 4 * ((t.toNat / 4 + 1 : Nat) : Time)
    dsimp only [Time] at *
    omega
  · change 4 * ((t.toNat / 4 + 1 : Nat) : Time) ≤ t + 4
    dsimp only [Time] at *
    omega

theorem fault_value : (Gen.V2.Duty.faulty run).card = 0 := by
  rw [Gen.V2.Duty.faulty_def]
  change (Finset.univ \ Finset.univ : Finset (Fin 1)).card = 0
  simp

theorem nvRecovery : Recovery₂ params unitCodec env run gap deltaF where
  sync := sync
  deltaF := deltaF_lower
  gap := by intro t ht _; exact proposer_gap t ht
  base := base
  fault := by rw [fault_value]; decide
  awake := by intros; rfl
  gapPos := gap_lower
  gapAligned := by decide

theorem healingSet : HealingSet params unitCodec env run gap deltaF := nvRecovery

end AvailableChain.FGSA.Run.Tests.NonVacuity.HealingRun
end
