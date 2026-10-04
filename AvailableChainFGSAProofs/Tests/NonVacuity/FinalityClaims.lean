module
public import AvailableChainFGSAProofs.Proofs.Assembly.Root
public import AvailableChainFGSAProofs.Proofs.Assembly.Healing
public meta import AvailableChainFGSAProofs.Proofs.Foundations.RowPermission
-- shake: keep (cached prefix checks)

@[expose] public section

set_option maxSynthPendingDepth 100
set_option maxRecDepth 10000
set_option exponentiation.threshold 2000

/-! NV-FIN. DC: SAME one-node fixture, with horizon 404.
TEST-USE forbids test-to-test imports. The fixture and prefix proofs below
are copied from HealingClaims through nvHealingInput. Only the namespace,
horizon, prefix bound, and plan comments change. This duplication is reported.
The proof uses parametric folds; concrete kernel checks stop at tick 54. -/
namespace AvailableChain.FGSA.Run.Tests.NonVacuity.FinalityClaims

/-- NV-FIN: S5 fixture: one honest node, positive horizon, and unchanged SA clocks.
DC: SAME canonical fixture and cached prefix proof. -/
def params : Params :=
  ⟨⟨1, 1, 2, 0, by decide, by decide, by decide, by decide⟩,
    3, 6, by decide, 2, by decide⟩

def env : Generic.Env (Fin 1) := ⟨1, by decide, 0, le_rfl, fun _ _ => true⟩
def deltaF : Time := 3
def gap : Time := 4
def horizon : Time := 404

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
theorem horizon_value : horizon = 404 := rfl
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

/-- NV-FIN: One tick, then one delivery of each released object, in release order.
DC: SAME canonical fixture and cached prefix proof. -/
def batch (acc : List Event × FixtureNode) (n : Nat) : List Event × FixtureNode :=
  let out := V2.D.tick env (mkRun []) acc.2 0 (n : Time)
  (acc.1 ++ [.tick 0 (n : Time)] ++ out.2.map (fun o => .deliver 0 o (n : Time)),
    out.2.foldl (fgsa params unitCodec).process out.1)

/-- NV-FIN: The cached node avoids a repeated fold of all preceding events.
DC: SAME canonical fixture and cached prefix proof. -/
def runPrefix (n : Nat) : List Event × FixtureNode :=
  (List.range n).foldl batch ([], (fgsa params unitCodec).init)

def run := mkRun (runPrefix 405).1

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

/-- NV-FIN: The cached node equals the engine fold, for every prefix length.
DC: SAME canonical fixture and cached prefix proof. -/
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

theorem tick_at (n : Nat) (hn : n < 405) :
    run.events[(runPrefix n).1.length]? = some (.tick 0 (n : Time)) := by
  obtain ⟨tail, he⟩ := prefix_mono (show n + 1 ≤ 405 by omega)
  change (runPrefix 405).1[(runPrefix n).1.length]? = _
  rw [← he, runPrefix_succ]
  simp [batch, List.append_assoc]

theorem state_before_tick (n : Nat) (hn : n < 405) :
    V2.D.Run.stateBefore env run (runPrefix n).1.length = fun _ => (runPrefix n).2 := by
  obtain ⟨tail, he⟩ := prefix_mono (show n ≤ 405 by omega)
  unfold V2.D.Run.stateBefore
  change ((runPrefix 405).1.take (runPrefix n).1.length).foldl
      (V2.D.World.step env run) V2.D.World.init = _
  rw [← he]
  simp only [List.take_append, List.take_length, Nat.sub_self, List.take_zero,
    List.append_nil]
  exact prefix_cached n

theorem emits_at_tick (n : Nat) (hn : n < 405) :
    V2.D.Run.emitsAt env run (runPrefix n).1.length =
      (V2.D.tick env (mkRun []) (runPrefix n).2 0 (n : Time)).2 := by
  rw [V2.D.Run.emitsAt, tick_at n hn, state_before_tick n hn]
  rfl

theorem immediate_delivery (n : Nat) (hn : n < 405) (o : Object)
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
  obtain ⟨tail, he⟩ := prefix_mono (show n + 1 ≤ 405 by omega)
  change (runPrefix 405).1[(runPrefix n).1.length + 1]? = _
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
  sorted := (prefix_strict 405).imp (fun h => le_of_lt h)
  nodup := by
    have hne : run.events.Pairwise (fun e f => e ≠ f) :=
      (prefix_strict 405).imp (fun h he => by rw [he] at h; exact lt_irrefl _ h)
    exact hne
  in_horizon := by
    intro e he
    obtain ⟨m, hm, ht, _⟩ := prefix_events_time 405 e he
    rw [ht]
    change 0 ≤ (m : Time) ∧ (m : Time) ≤ 404
    exact ⟨Int.natCast_nonneg m, by dsimp only [Time] at *; omega⟩
  honest_only := by intro e _; exact Finset.mem_univ _
  tick_public := by
    intro v t he
    obtain ⟨m, _, ht, _⟩ := prefix_events_time 405 (.tick v t) he
    exact ⟨m, by simpa only [V2.Event.time, env, Int.mul_one] using ht⟩
  tick_total := by
    intro v _ t _ ht hh
    have hv : v = 0 := Subsingleton.elim _ _
    subst v
    change t ≤ 404 at hh
    have he : t = (t.toNat : Time) := (Int.toNat_of_nonneg ht).symm
    rw [he]
    exact prefix_ticks 405 t.toNat (by dsimp only [Time] at *; omega)

theorem noRestart : V2.D.NoRestart run := by
  intro i v t hi
  obtain ⟨_, _, _, he⟩ := prefix_events_time 405 (.restart v t) (List.mem_of_getElem? hi)
  rcases he with he | ⟨o, he⟩ <;> cases he

set_option maxHeartbeats 2000000 in
-- Index uniqueness uses the symbolic prefix proof through the concrete run type.
theorem delivery_source {i : Nat} {v : Fin 1} {o : Object} {t : Time}
    (hi : run.events[i]? = some (.deliver v o t)) :
    ∃ n : Nat, n < 405 ∧ t = (n : Time) ∧ i = (runPrefix n).1.length + 1 ∧
      o ∈ (V2.D.tick env (mkRun []) (runPrefix n).2 0 (n : Time)).2 := by
  have hm := List.mem_of_getElem? hi
  rw [show run.events = (runPrefix 405).1 from rfl, prefix_flat] at hm
  obtain ⟨n, hn, hm⟩ := List.mem_flatMap.mp hm
  have hn' : n < 405 := List.mem_range.mp hn
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
    ∃ n : Nat, n < 405 ∧ t = (n : Time) ∧ i = (runPrefix n).1.length := by
  obtain ⟨n, hn, ht, _⟩ := prefix_events_time 405 (.tick v t) (List.mem_of_getElem? hi)
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

theorem emitted_wire (n : Nat) (hn : n < 405)
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

theorem prefix_rows (n : Nat) (hn : n ≤ 405) : EmissionRowsValid (runPrefix n).2.st := by
  induction n with
  | zero => exact ⟨fun _ h => (List.not_mem_nil h).elim,
      fun _ h => (List.not_mem_nil h).elim⟩
  | succ n ih =>
    have hn' : n < 405 := by omega
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

theorem state_delivery_store (n : Nat) (hn : n < 405) :
    (V2.D.Run.stateBefore env run ((runPrefix n).1.length + 1) 0).st =
      FGSA.clock params (runPrefix n).2.st (n : Time) := by
  have hs := (V2.D.Run.step_tick_eq env run (tick_at n hn)).1
  rw [state_before_tick n hn] at hs
  exact (congrArg Node.st hs).trans
    (tick_st (c := unitCodec) env run (runPrefix n).2 0 (n : Time))

theorem emitted_deps (n : Nat) (hn : n < 405) (o : Object)
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
    ∃ m : Nat, m < n ∧ m < 405 ∧ t = (m : Time) ∧
      o ∈ (V2.D.tick env (mkRun []) (runPrefix m).2 0 (m : Time)).2 := by
  obtain ⟨m, hm, ht, he, ho⟩ := delivery_source hi
  refine ⟨m, ?_, hm, ht, ho⟩
  by_contra hh
  have hl := (prefix_mono (Nat.le_of_not_gt hh)).length_le
  omega

theorem carried_from_state (n : Nat) (hn : n < 405) (o o' : Object)
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
  ∃ m : Nat, m < n ∧ m < 405 ∧
    o ∈ (V2.D.tick env (mkRun []) (runPrefix m).2 0 (m : Time)).2

theorem handled_before (n : Nat)
    (past : ∀ m : Nat, m < n → m < 405 → ∀ o o' : Object,
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

theorem carried_authentic (n : Nat) (hn : n < 405) (o o' : Object)
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

theorem head_pool_authentic (n : Nat) (hn : n < 405) (s : Slot) (j : Fin params.n) (b : Block)
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

theorem row_pool_authentic (n : Nat) (hn : n < 405) (a : RowWire params.n)
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

theorem emitted_fresh (n : Nat) (hn : n < 405) (o : Object)
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

theorem healingPrem {Pt : Type} (pt : Pt) :
    HealingPrem params unitCodec gap deltaF env run pt := ⟨healingSet, livenessBound⟩

theorem healingTimePrem : HealingTimePrem params unitCodec gap deltaF env run () :=
  ⟨healingPrem (), healing_horizon⟩

theorem resetArrivalPrem : ResetArrivalPrem params unitCodec gap deltaF env run () :=
  ⟨healingPrem (), reset_horizon⟩

theorem resetArrivalFullPrem : ResetArrivalFullPrem params unitCodec gap deltaF env run () :=
  ⟨healingPrem (), reset_full_horizon⟩

theorem renewedPromotionPrem : RenewedPromotionPrem params unitCodec gap deltaF env run ⟨3⟩ :=
  ⟨healingPrem (⟨3⟩ : PtR), renewed_three_horizon⟩

-- NV4 uses the same fixture and the prefix invariants above.
def actionNode (r : Nat) : FixtureNode :=
  (fgsa params unitCodec).clock (runPrefix (params.actionTime r).toNat).2
    (params.actionTime r)

def rowAtAction (r : Nat) : Option RowPayload :=
  (attest params (actionNode r).st (actionNode r).record ⟨0, params.nPos⟩).1

def sourceAtAction (r : Nat) : Option (FGBlock (Fin params.n)) :=
  (fgInputs params (actionNode r).st).1

def rowEntry (r : Nat) : Option (Nat × BlockId) :=
  (rowAtAction r).bind (fun a => namedEntry a.height_pair)

-- These evaluations use at most 43 ticks, through cached nodes.

/-- NV-FIN: The time filter of any longer prefix gives the same shorter prefix.
DC: SAME canonical fixture and cached prefix proof. -/
theorem prefix_cut (n m : Nat) (hn : n ≤ m) :
    (runPrefix m).1.filter (fun e => decide (e.time < (n : Time))) = (runPrefix n).1 := by
  induction m generalizing n with
  | zero =>
    have he : n = 0 := by omega
    subst n
    rfl
  | succ m ih =>
    by_cases hnm : n ≤ m
    · rw [runPrefix_succ]
      dsimp only [batch]
      rw [List.filter_append, List.filter_append, ih n hnm]
      have ht : decide ((m : Time) < (n : Time)) = false := by
        apply decide_eq_false
        exact not_lt.mpr (by exact_mod_cast hnm)
      have hd : ((V2.D.tick env (mkRun []) (runPrefix m).2 0 (m : Time)).2.map
          (fun o => (.deliver 0 o (m : Time) : Event))).filter
            (fun e => decide (e.time < (n : Time))) = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro e he
        obtain ⟨o, _, rfl⟩ := List.mem_map.mp he
        change ¬ decide ((m : Time) < (n : Time)) = true
        rw [ht]
        decide
      rw [hd]
      simp only [List.filter_cons, List.filter_nil]
      change ((runPrefix n).1 ++
        (if decide ((m : Time) < (n : Time)) = true then [.tick 0 (m : Time)] else [])) ++ [] = _
      rw [ht]
      simp
    · have he : n = m + 1 := by omega
      subst n
      apply List.filter_eq_self.mpr
      intro e he
      obtain ⟨k, hk, ht, _⟩ := prefix_events_time (m + 1) e he
      rw [ht]
      exact decide_eq_true (by exact_mod_cast hk)

/-- NV-FIN: The inclusive read at tick n is the cached node after tick n.
DC: SAME canonical fixture and cached prefix proof. -/
theorem read_prefix (n : Nat) (hn : n < 405) :
    V2.D.Run.readAt env run (n : Time) = fun _ => (runPrefix (n + 1)).2 := by
  have hp : run.events.filter (fun e => decide (e.time ≤ (n : Time))) =
      (runPrefix (n + 1)).1 := by
    have he : (fun e : Event => decide (e.time ≤ (n : Time))) =
        (fun e : Event => decide (e.time < ((n + 1 : Nat) : Time))) := by
      funext e
      have hp : e.time ≤ (n : Time) ↔ e.time < ((n + 1 : Nat) : Time) := by
        dsimp only [Time]
        push_cast
        omega
      exact decide_eq_decide.mpr hp
    rw [he]
    exact prefix_cut (n + 1) 405 (by omega)
  unfold V2.D.Run.readAt
  rw [hp]
  exact prefix_cached (n + 1)

theorem frontier_cached (n : Nat) (hn : n < 405) :
    honestFrontier params unitCodec env run (n : Time) = (runPrefix (n + 1)).2.st.fg.h_max := by
  unfold honestFrontier
  rw [read_prefix n hn]
  change (Finset.univ : Finset (Fin 1)).sup (fun _ => (runPrefix (n + 1)).2.st.fg.h_max) = _
  simp

theorem frontier_idx_cached (n : Nat) (hn : n < 405) :
    frontierAtIdx params unitCodec env run (runPrefix n).1.length =
      (runPrefix n).2.st.fg.h_max := by
  unfold frontierAtIdx storeAt
  rw [state_before_tick n hn]
  change (Finset.univ : Finset (Fin 1)).sup (fun _ => (runPrefix n).2.st.fg.h_max) = _
  simp

set_option maxHeartbeats 2000000 in
-- The kernel checks the cached state after the first 31 ticks.
theorem nvCachedFrontier : (runPrefix 31).2.st.fg.h_max = 2 := by decide +kernel

theorem nvFrontier : honestFrontier params unitCodec env run 30 = 2 :=
  (frontier_cached 30 (by decide)).trans nvCachedFrontier

theorem nvFrontierAtIdx : frontierAtIdx params unitCodec env run (runPrefix 31).1.length = 2 :=
  (frontier_idx_cached 31 (by decide)).trans nvCachedFrontier

theorem action_read (r : Nat) (hr : (params.actionTime r).toNat < 405) :
    postClock env run 0 (params.actionTime r) = some (actionNode r) := by
  have ht : ((params.actionTime r).toNat : Time) = params.actionTime r := by
    apply Int.toNat_of_nonneg
    change 0 ≤ 4 * 1 * ((r * 3 : Nat) : Int) + 6 * 1
    omega
  have he := tick_at (params.actionTime r).toNat hr
  rw [ht] at he
  rw [postClock_def, preTick_def,
    fgsa_tickIdx_of_event params unitCodec env run nvSchedule he,
    Option.map_some, state_before_tick (params.actionTime r).toNat hr]
  rfl

theorem source_read (r : Nat) (hr : (params.actionTime r).toNat < 405) :
    actionSourceFG params unitCodec env run 0 r = some (sourceAtAction r) := by
  rw [actionSourceFG_def, action_read r hr]
  rfl

-- The reset source and wire come from the round-3 action itself.
def resetSource : FGBlock (Fin params.n) := (sourceAtAction 3).getD .genesis
def resetRow : RowWire params.n :=
  ⟨.seat .fg ⟨0, params.nPos⟩, (rowAtAction 3).getD (.vote ⟨.empty, none⟩)⟩

def w : HealingWitness :=
  ⟨0, 30, 2, 3, 9, eraseFG resetSource, 0, .genesis⟩

set_option maxHeartbeats 2000000 in
-- The kernel checks the source at tick 42, using its cached prefix.
theorem nvSourceHeight : (sourceAtAction 3).map (fun C => (heightView params C).h) = some 3 := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The kernel checks the concrete source slot at tick 42.
theorem nvSourceSlot : resetSource.slot = 9 := by decide +kernel

set_option maxHeartbeats 2000000 in
-- The kernel checks the concrete row and source entry at tick 42.
theorem nvResetRowFields :
    namedEntry resetRow.payload.height_pair =
      some (3, (heightView params resetSource).T_h.root) := by decide +kernel

set_option maxHeartbeats 2000000 in
-- The kernel checks the concrete wire emission at tick 42.
theorem nvResetEmissionWire :
    toWire params (ofRow params resetRow) ∈
      (V2.D.tick env (mkRun []) (runPrefix 42).2 0 42).2.map (toWire params) := by
  decide +kernel

theorem nvResetEmission :
    ofRow params resetRow ∈ (V2.D.tick env (mkRun []) (runPrefix 42).2 0 42).2 := by
  obtain ⟨o, ho, he⟩ := List.mem_map.mp nvResetEmissionWire
  have heq : o = ofRow params resetRow := (toWireEquiv params).injective he
  exact heq ▸ ho

theorem nvSource : sourceAtAction 3 = some resetSource := by
  have h := nvSourceHeight
  cases he : sourceAtAction 3 with
  | none => rw [he] at h; cases h
  | some C => simp only [resetSource, he, Option.getD_some]

theorem nvResetHeight : (heightView params resetSource).h = 3 := by
  have h := nvSourceHeight
  rw [nvSource] at h
  exact Option.some.inj h

theorem nvHonestResetRow :
    HonestRowAt params unitCodec env run (runPrefix 42).1.length 0 3 resetRow := by
  refine ⟨Finset.mem_univ _, tick_at 42 (by decide), ?_⟩
  rw [emits_at_tick 42 (by decide)]
  exact nvResetEmission

set_option maxHeartbeats 2000000 in
-- The kernel checks only the first three action prefixes.
theorem nvEarlySourceHeights :
    ((sourceAtAction 0).map (fun C => (heightView params C).h),
     (sourceAtAction 1).map (fun C => (heightView params C).h),
     (sourceAtAction 2).map (fun C => (heightView params C).h)) =
      (none, some 1, some 2) := by decide +kernel

/-- NV-FIN: Every named honest row in rounds 0--2 has height at most 2.
DC: SAME canonical fixture and cached prefix proof. -/
theorem nvEarlyRowCap {j : Nat} {y : Fin 1} {r h : Nat} {a : RowWire params.n} {e : BlockId}
    (ha : HonestRowAt params unitCodec env run j y r a)
    (he : namedEntry a.payload.height_pair = some (h, e)) (hr : r < 3) : h ≤ 2 := by
  have hy : y = 0 := Subsingleton.elim _ _
  subst y
  have hb : (params.actionTime r).toNat < 405 := by
    change (4 * 1 * ((r * 3 : Nat) : Int) + 6 * 1).toNat < 405
    push_cast
    omega
  obtain ⟨C, _, hC, hh, _⟩ := emittedName_window params unitCodec env run nvSchedule ha he
  rw [source_read r hb] at hC
  have hs : (sourceAtAction r).map (fun C => (heightView params C).h) = some h := by
    rw [Option.some.inj hC]
    exact congrArg some hh.symm
  have h0 : (sourceAtAction 0).map (fun C => (heightView params C).h) = none :=
    congrArg Prod.fst nvEarlySourceHeights
  have h1 : (sourceAtAction 1).map (fun C => (heightView params C).h) = some 1 :=
    congrArg (fun z => z.2.1) nvEarlySourceHeights
  have h2 : (sourceAtAction 2).map (fun C => (heightView params C).h) = some 2 :=
    congrArg (fun z => z.2.2) nvEarlySourceHeights
  have hc : r = 0 ∨ r = 1 ∨ r = 2 := by omega
  rcases hc with rfl | rfl | rfl
  · rw [h0] at hs
    cases hs
  · rw [h1] at hs
    have hh' : h = 1 := (Option.some.inj hs).symm
    omega
  · rw [h2] at hs
    have hh' : h = 2 := (Option.some.inj hs).symm
    omega

theorem nvRowCap : ∀ j y r a h e t,
    HonestRowAt params unitCodec env run j y r a →
    run.events[j]? = some (.tick y t) → t ≤ 30 →
    namedEntry a.payload.height_pair = some (h, e) → h ≤ 2 := by
  intro j y r a h e t ha ht hcut he
  have heq : params.actionTime r = t :=
    (V2.Event.tick.inj (Option.some.inj (ha.2.1.symm.trans ht))).2
  have hr : r < 3 := by
    rw [← heq] at hcut
    change 4 * 1 * ((r * 3 : Nat) : Int) + 6 * 1 ≤ 30 at hcut
    push_cast at hcut
    omega
  exact nvEarlyRowCap ha he hr

/-- NV-FIN: With GST zero, no source vote is strictly before GST.
DC: SAME canonical fixture and cached prefix proof. -/
theorem nvOldRowsEmpty : oldRowHeights params unitCodec env run = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro h ⟨j, y, r, a, e, _, _, ht⟩
  change 4 * 1 * ((r * 3 : Nat) : Int) + 1 < 0 at ht
  omega

theorem nvMu : muOf params unitCodec env run = 1 := by
  rw [muOf_def, nvOldRowsEmpty]
  simp

theorem nvHeightRow : HeightRow params unitCodec env run 3 3 :=
  ⟨(runPrefix 42).1.length, 0, resetRow, (heightView params resetSource).T_h.root,
    nvHonestResetRow, nvResetRowFields⟩

theorem nvResetFirst : ∀ r, HeightRow params unitCodec env run r 3 → 3 ≤ r := by
  rintro r ⟨j, y, a, e, ha, he⟩
  by_contra hn
  have h := nvEarlyRowCap ha he (by omega)
  omega

-- Keep the concrete witness terms closed during the final structure assembly.
attribute [irreducible] resetSource resetRow

theorem nvFresh : ∃ j y, ∃ (a : RowWire params.n) (C : FGBlock (Fin params.n)),
    HonestRowAt params unitCodec env run j y 3 a ∧
    namedEntry a.payload.height_pair = some (3, (heightView params C).T_h.root) ∧
    actionSourceFG params unitCodec env run y 3 = some (some C) ∧
    eraseFG C = eraseFG resetSource ∧ (heightView params C).h = 3 := by
  have hs : actionSourceFG params unitCodec env run 0 3 = some (some resetSource) :=
    (source_read 3 (by decide)).trans (congrArg some nvSource)
  exact ⟨(runPrefix 42).1.length, 0, resetRow, resetSource, nvHonestResetRow,
    nvResetRowFields, hs, Eq.refl _, nvResetHeight⟩

set_option maxHeartbeats 2000000 in
-- The assembly checks the concrete witness after the short-prefix source proof.
/-- NV-FIN: All 13 reset fields hold on the unchanged one-node run.
DC: SAME canonical fixture and cached prefix proof. -/
theorem nvH0Reset : H0Reset params unitCodec env run w where
  rG_after := by change 0 ≤ params.actionTime 0; decide
  rG_first := by intro r _; exact Nat.zero_le r
  cut := by decide
  frontier := nvFrontier.symm
  rowCap := nvRowCap
  mu_le := by change muOf params unitCodec env run ≤ 2; rw [nvMu]; decide
  cut_lower := by decide
  cut_upper := by decide
  reset_row := nvHeightRow
  reset_first := nvResetFirst
  label := rfl
  fresh := nvFresh
  synchronous := by decide

-- NV5 evaluates only proposal prefixes through tick 52.
def proposalObjects (s : Slot) : List Object :=
  (V2.D.tick env (mkRun []) (runPrefix (4 * s)).2 0 (4 * (s : Time))).2

def proposalBlocks (s : Slot) : List Block :=
  (proposalObjects s).filterMap (fun o => (fgsaInterface params unitCodec).block o.payload)

/-- NV-FIN: The chain is in child-to-parent order; each node records its slot and body.
DC: SAME canonical fixture and cached prefix proof. -/
def parentChain : Block → List (Slot × Nat)
  | .genesis => [(0, 0)]
  | .node B s x => (s, x) :: parentChain B

def firstProposal : Block := (proposalBlocks 11).headD .genesis

def w' : HealingWitness := { w with u := 11, QStar := firstProposal }

set_option maxHeartbeats 2000000 in
-- The kernel compares the cached proposal and reset-source prefixes.
/-- NV-FIN: The block of the first proposal has C* as its second parent.
DC: SAME canonical fixture and cached prefix proof. -/
theorem nvFirstParents : firstProposal.parent.parent = eraseFG resetSource := by
  unfold resetSource
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The kernel checks ancestry through the cached prefixes at ticks 42 and 44.
theorem nvSourcePrefix : Block.Preceq (eraseFG resetSource) firstProposal := by
  unfold resetSource
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The kernel checks the block emitted from the cached state at tick 44.
theorem nvFirstMember : firstProposal ∈ proposalBlocks 11 := by decide +kernel

/-- NV-FIN: A cached block emission is an honest proposal of the complete run.
DC: SAME canonical fixture and cached prefix proof. -/
theorem honestProposal_of_cached {s : Slot} {B : Block} (hs : 0 < s)
    (hn : 4 * s < 405) (hB : B ∈ proposalBlocks s) :
    HonestProposal env run (fgsaInterface params unitCodec) s B := by
  obtain ⟨o, ho, hb⟩ := List.mem_filterMap.mp hB
  refine ⟨⟨hs, Finset.mem_univ _⟩, o, ?_, hb⟩
  refine ⟨(runPrefix (4 * s)).1.length, ?_, ?_⟩
  · change run.events[(runPrefix (4 * s)).1.length]? = some (.tick 0 (4 * (s : Time)))
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using tick_at (4 * s) hn
  · rw [emits_at_tick (4 * s) hn]
    simpa only [proposalObjects, Nat.cast_mul, Nat.cast_ofNat] using ho

/-- NV-FIN: w' changes only the proposal slot and block in the copied NV4 witness.
DC: SAME canonical fixture and cached prefix proof. -/
theorem nvH0Reset' : H0Reset params unitCodec env run w' where
  rG_after := nvH0Reset.rG_after
  rG_first := nvH0Reset.rG_first
  cut := nvH0Reset.cut
  frontier := nvH0Reset.frontier
  rowCap := nvH0Reset.rowCap
  mu_le := nvH0Reset.mu_le
  cut_lower := nvH0Reset.cut_lower
  cut_upper := nvH0Reset.cut_upper
  reset_row := nvH0Reset.reset_row
  reset_first := nvH0Reset.reset_first
  label := nvH0Reset.label
  fresh := nvH0Reset.fresh
  synchronous := nvH0Reset.synchronous

theorem nvProposalLower : w'.sStar + 2 ≤ w'.u := by decide

theorem nvProposal : HonestProposal env run (fgsaInterface params unitCodec) w'.u w'.QStar :=
  honestProposal_of_cached (by decide) (by decide) nvFirstMember

theorem nvProposalFirst : ∀ v Q, w'.sStar + 2 ≤ v →
    HonestProposal env run (fgsaInterface params unitCodec) v Q → w'.u ≤ v := by
  intro v Q hv _
  exact hv

theorem nvAfterGST : env.t_GST ≤ tstar params w' := by decide

-- Keep the evaluated block closed during the H0 assembly.
attribute [irreducible] firstProposal

/-- NV-FIN: All H0 fields hold on the unchanged one-node run.
DC: SAME canonical fixture and cached prefix proof. -/
theorem nvH0 : H0 params unitCodec env run w' where
  toH0Reset := nvH0Reset'
  proposal_lower := nvProposalLower
  proposal := nvProposal
  proposal_first := nvProposalFirst
  after_gst := nvAfterGST
  source_prefix := nvSourcePrefix

theorem nvClock : params.δt = 2 * params.R := by decide
theorem nvTstarValue : tstar params w' = 50 := by decide
theorem nvResetActionValue : params.actionTime w'.rStar = 42 := by decide
theorem nvTimeBudgetValue : params.actionTime w'.rStar + Γ params gap + 4 * params.Δ = 50 := by
  decide

-- Equality is allowed in the first H-time bound: 50 ≤ 42 + 4 + 4.
theorem nvTstarBound :
    tstar params w' ≤ params.actionTime w'.rStar + Γ params gap + 4 * params.Δ := by
  decide

theorem nvResetTimeStrict :
    params.actionTime w'.rStar < env.t_GST + B'_resetF params deltaF gap := by
  decide

-- Both horizon forms hold at 303 ≤ 404 on this run.
theorem nvFullHorizon :
    env.t_GST + B'_resetF params deltaF gap + Γ params gap + 4 * params.Δ ≤ run.horizon :=
  healing_resetFull_horizon params gap deltaF env.t_GST run.horizon healing_horizon

theorem nvTimeStrict :
    params.actionTime w'.rStar + Γ params gap + 4 * params.Δ < env.t_GST + B_HF params deltaF gap :=
  healing_time_strict_of_reset params gap deltaF env.t_GST
    (params.actionTime w'.rStar) nvResetTimeStrict


/-- NV-FIN: apply the closed row permission producer to the NV3 package.
DC: SAME canonical run, action source, and row entry. -/
theorem nvRowPermission : RowPermissionAt params unitCodec env run :=
  fgsa_rowPermissionClaim params gap deltaF nvClock unitCodec env run () (healingPrem ())

/-- NV-FIN: apply the closed renewed promotion producer to round 3.
DC: SAME canonical run and the proved 66 <= 404 horizon. -/
theorem nvRenewedPromotion : RenewedPromotionConcl params unitCodec env run gap 3 :=
  fgsa_renewedPromotionClaim params gap deltaF nvClock unitCodec env run ⟨3⟩
    renewedPromotionPrem

/-- NV-FIN: adapt the closed reset-only statement to its claim.
DC: SAME reset-only conclusion; full H0 is a separate item. -/
theorem nvResetArrivalClaim : ResetArrivalClaim params := by
  intro G ΔF hδ V _ _ In c E rho pt h
  exact healing_resetArrivalStatement params G ΔF hδ c E rho h.set h.bound h.hhor

/-- NV-FIN: apply the reset-only claim to the NV3 package.
DC: SAME canonical run and the proved 295 <= 404 horizon. -/
theorem nvResetArrival : ResetArrivalConcl params unitCodec env run gap deltaF :=
  nvResetArrivalClaim gap deltaF nvClock unitCodec env run () resetArrivalPrem

/-- NV-FIN: the NV5 full witness supplies the healing input package.
DC: SAME full H0 and tstar = 50; this package is closed. -/
theorem nvHealingInputPrem : HealingInputPrem params unitCodec gap deltaF env run ⟨w'⟩ :=
  ⟨⟨healingPrem (⟨w'⟩ : PtW), nvH0⟩, by change (50 : Time) ≤ 404; decide⟩

/-- Blueprint 21 H.18–H.22; plan NV-FIN: apply the closed full reset statement.
DC: SAME canonical run and the proved full reset horizon. -/
theorem nvResetArrivalFull : ∃ witness, H0 params unitCodec env run witness ∧
    params.actionTime witness.rStar < env.t_GST + B'_resetF params deltaF gap :=
  healing_resetArrivalFull params gap deltaF nvClock unitCodec env run
    healingSet livenessBound nvFullHorizon

/-- Blueprint 21 H.18–H.22; plan NV-FIN: apply the closed HealingInputClaim.
DC: SAME canonical run and the full NV5 witness with tstar = 50. -/
theorem nvHealingInput : HealingInput params unitCodec env run w' deltaF :=
  healing_healingInputClaim params gap deltaF nvClock unitCodec env run ⟨w'⟩ nvHealingInputPrem


open Gen.Pure

/-- NV-FIN F1. DC: INTENTIONAL W bounds include the carrier receipt tail. -/
theorem nvBudgets : W_W params deltaF 1 = 49 ∧
    env.t_GST + B_HF params deltaF gap + W_W params deltaF 1 = 352 ∧
    env.t_GST + B_HF params deltaF gap + 2 * W_W params deltaF 1 = 401 := by
  decide

/-- NV-FIN F1. DC: SAME positive slots, with one honest awake proposer each. -/
theorem nvGood (r : Nat) (hr : 1 ≤ r) :
    FGoodE_W (Gen.V2.Duty.HonestSlot run (fgsaInterface params unitCodec))
      params.R (kappaF params deltaF) r := by
  rw [FGoodE_W_def]
  refine ⟨honest_slot (by change 0 < r * 3; omega),
    honest_slot (by change 0 < (r + 1) * 3; omega),
    ⟨(r + 2) * 3, ?_, ?_, honest_slot (by change 0 < (r + 2) * 3; omega)⟩, ?_⟩
  · change (r + 1) * 3 + 3 ≤ (r + 2) * 3
    omega
  · exact le_rfl
  · apply honest_slot
    change 0 < (r + 2) * 3 + 3
    omega

/-- NV-FIN F1. DC: INTENTIONAL RecFE_W with its full finite receipt guard. -/
theorem nvRecFE : FE_W params deltaF
    (Gen.V2.Duty.HonestSlot run (fgsaInterface params unitCodec)) env.t_GST run.horizon 1 := by
  rw [FE_W_def, RecFE_W_def]
  refine ⟨le_rfl, ?_⟩
  intro q hq _ _
  exact ⟨q, (by rw [InWindow_def]; exact ⟨le_rfl, Nat.lt_succ_self q⟩), nvGood q hq⟩

/-- NV-FIN F1. DC: INTENTIONAL RecF4_W adds the fourth honest proposer. -/
theorem nvRecF4 : F4_W params deltaF
    (Gen.V2.Duty.HonestSlot run (fgsaInterface params unitCodec)) env.t_GST run.horizon 1 := by
  rw [F4_W_def, RecF4_W_def]
  refine ⟨le_rfl, ?_⟩
  intro q hq _ _
  refine ⟨q, ?_, ?_⟩
  · rw [InWindow_def]
    exact ⟨le_rfl, Nat.lt_succ_self q⟩
  · rw [FGood4_W_def]
    exact ⟨nvGood q hq, honest_slot (by change 0 < (q + 1) * 3 + 3; omega)⟩

/-- NV-FIN F1. DC: INTENTIONAL the last guarded search is q = 30, at time 397. -/
theorem nvSearchTail :
    ((30 : Time) + 1 + 1) * P params + betaF params deltaF + params.Δ = 397 ∧
    ((30 : Time) + 1 + 1) * P params + betaF params deltaF + params.Δ ≤ run.horizon ∧
    run.horizon < ((31 : Time) + 1 + 1) * P params + betaF params deltaF + params.Δ := by
  decide

/-- NV-FIN F2. DC: SAME closed recovery, bound, and either W recurrence. -/
theorem nvFinalitySet (form : FinFormW) :
    FinalitySet_W params unitCodec env run gap deltaF form 1 := by
  refine ⟨nvRecovery, livenessBound, ?_⟩
  cases form <;> rw [FinFormW.holdsW_def]
  · exact nvRecFE
  · exact nvRecF4

/-- NV-FIN F2. DC: SAME FirstFinality with its full bound of 352. -/
theorem nvFirstFinalityPrem (form : FinFormW) :
    FirstFinalityPrem_W params unitCodec gap deltaF form 1 env run () :=
  ⟨nvFinalitySet form, by decide⟩

/-- NV-FIN F2. DC: SAME local FF5 at the concrete healing time 50. -/
theorem nvLocalPrem (form : FinFormW) :
    FinalityLivenessPrem_W params unitCodec gap deltaF form 1 w' env run ⟨50⟩ :=
  ⟨nvFinalitySet form, nvHealingInput, by decide, by decide⟩

/-- NV-FIN F2. DC: SAME GST FF5 at the recovery bound 303. -/
theorem nvGSTPrem (form : FinFormW) :
    FinalityLivenessGSTPrem_W params unitCodec gap deltaF form 1 env run ⟨303⟩ :=
  ⟨nvFinalitySet form, by decide, by decide⟩

/-- NV-FIN F2. DC: SAME local FF7 with two complete windows from time 50. -/
theorem nvAbovePrem (form : FinFormW) :
    AboveFrontierPrem_W params unitCodec gap deltaF form 1 w' env run ⟨50⟩ :=
  ⟨nvFinalitySet form, nvHealingInput, by decide, by decide, by decide⟩

/-- NV-FIN F2. DC: SAME GST FF7 needs time 401, within horizon 404. -/
theorem nvAboveGSTPrem (form : FinFormW) :
    AboveFrontierGSTPrem_W params unitCodec gap deltaF form 1 env run ⟨303⟩ :=
  ⟨nvFinalitySet form, by decide, by decide⟩

/-- NV-FIN F2/F4. DC: SAME actual block computed by the proposer at slot s. -/
def nvProposalBlock (s : Slot) : Block :=
  let st := FGSA.clock params (runPrefix (4 * s)).2.st (4 * (s : Time))
  let H := getHead params st (proposerVotes st s) (proposerSupport st s)
  Block.node H s (packBody 0 (proposalRows params st H))

/-- NV-FIN F2/F4. DC: SAME concrete proposal; no full-run evaluation is used. -/
theorem nvProposalBlock_honest (s : Slot) (hs : 0 < s) (hn : 4 * s < 405) :
    HonestProposal env run (fgsaInterface params unitCodec) s (nvProposalBlock s) := by
  apply honestProposal_of_cached hs hn
  let st := FGSA.clock params (runPrefix (4 * s)).2.st (4 * (s : Time))
  let raw := proposerVotes st s
  let sup := proposerSupport st s
  let H := getHead params st raw sup
  let rows := proposalRows params st H
  let m := Msg.proposal (nvProposalBlock s) (raw.filterMap liftHead?)
    (sup.filterMap liftHead?) rows
  let o : Object := ⟨.seat (.prop s) ⟨0, Nat.one_pos⟩, m⟩
  have hm : o ∈ proposalObjects s := by
    apply (fgsa_emits_proposal env (mkRun []) (runPrefix (4 * s)).2
      0 (4 * (s : Time)) s m).mpr
    refine ⟨rfl, rfl, rfl, ?_⟩
    delta propose
    simp only [Nat.ne_of_gt hs, ↓reduceIte, Option.map_some]
    rfl
  exact List.mem_filterMap.mpr ⟨o, hm, rfl⟩

/-- NV-FIN F2. DC: SAME FF6 for the concrete slot-76 proposal at time 304. -/
theorem nvProposalPrem (form : FinFormW) :
    ProposalFinalPrem_W params unitCodec gap deltaF form 1 w' env run
      ⟨76, nvProposalBlock 76⟩ :=
  ⟨nvFinalitySet form, nvHealingInput, nvProposalBlock_honest 76 (by decide) (by decide),
    by decide, by decide⟩

/-- NV-FIN F2. DC: SAME GST FF6 with deadline 353. -/
theorem nvProposalGSTPrem (form : FinFormW) :
    ProposalFinalGSTPrem_W params unitCodec gap deltaF form 1 env run
      ⟨76, nvProposalBlock 76⟩ :=
  ⟨nvFinalitySet form, nvProposalBlock_honest 76 (by decide) (by decide),
    by decide, by decide⟩

/-- NV-FIN F3. DC: SAME FF5 from the closed aggregate, with deadline 352. -/
theorem nvFF5 : FinalityLivenessConcl_W params unitCodec env run 303 352 := by
  obtain ⟨_, _, _, h⟩ := (fgsaClaims params).finalityLivenessGSTRecFE gap deltaF 1
    nvClock unitCodec env run ⟨303⟩ (nvGSTPrem .recFE)
  exact h

/-- NV-FIN F3. DC: SAME FirstFinality from the closed aggregate. -/
theorem nvFirstFinality : FirstFinalityConcl_W params unitCodec env run deltaF gap 352 :=
  (fgsaClaims params).firstFinalityRecFE gap deltaF 1 nvClock unitCodec env run ()
    (nvFirstFinalityPrem .recFE)

/-- NV-FIN F3. DC: SAME one witness retains strict extension and higher certificate height. -/
noncomputable def nvFinalBlock : FGBlock (Fin params.n) := Classical.choose nvFF5

/-- NV-FIN F3. DC: SAME local FF5 at the concrete H0 healing time, with deadline 99. -/
theorem nvLocalFF5 : FinalityLivenessConcl_W params unitCodec env run 50 99 :=
  fgsa_finalityLivenessRecFE_W params gap deltaF 1 w' nvClock unitCodec env run
    ⟨50⟩ (nvLocalPrem .recFE)

/-- NV-FIN F3. DC: SAME local FF5 block for both concrete comparisons. -/
noncomputable def nvLocalFinalBlock : FGBlock (Fin params.n) := Classical.choose nvLocalFF5

/-- NV-FIN F3. DC: SAME slot-12 source, already stored at time 50. -/
def nvLocalCarrier : FGBlock (Fin params.n) := (sourceAtAction 4).getD .genesis

set_option maxHeartbeats 2000000 in
-- The kernel checks only the cached prefixes through tick 54.
/-- NV-FIN F3. DC: SAME concrete prefix; the carrier certifies height 2 and block slot 5. -/
theorem nvLocalSnapshot :
    (runPrefix 51).2.st.base.stableRecord = firstProposal ∧ firstProposal.slot = 11 ∧
    nvLocalCarrier ∈ (runPrefix 51).2.st.fg.TF ∧ nvLocalCarrier.slot = 12 ∧
    (finalityView params nvLocalCarrier).F = (runPrefix 51).2.st.fg.F ∧
    (finalityView params nvLocalCarrier).F.slot = 5 ∧
    (finalityView params nvLocalCarrier).h_F = 2 := by
  decide +kernel

-- NV-FIN Risk 5: do not reduce the cached event fold during unification.
attribute [local irreducible] runPrefix

/-- NV-FIN F3. DC: SAME inclusive read, without full-run reduction. -/
theorem nvRead303 : V2.D.Run.readAt env run 303 0 = (runPrefix 304).2 :=
  congrFun (read_prefix 303 (by decide)) 0

/-- NV-FIN F3. DC: SAME strict extension at the actual node and concrete time 303. -/
theorem nvFF5Strict :
    Block.Prec (runPrefix 304).2.st.base.stableRecord (eraseFG nvFinalBlock) := by
  have h := (Classical.choose_spec nvFF5).1 0 (Finset.mem_univ _)
  rwa [nvRead303] at h

/-- NV-FIN F3. DC: SAME carrier height comparison at the actual node and time 303. -/
theorem nvFF5Higher : ∀ K ∈ (runPrefix 304).2.st.fg.TF,
    (finalityView params K).F = (runPrefix 304).2.st.fg.F →
    (finalityView params K).h_F < (heightView params nvFinalBlock).h := by
  have h := (Classical.choose_spec nvFF5).2.1 0 (Finset.mem_univ _)
  rwa [nvRead303] at h

/-- NV-FIN F3. DC: SAME store invariant supplies a carrier of the current final block. -/
theorem nvCurrentCarrier : ∃ K ∈ (runPrefix 304).2.st.fg.TF,
    (finalityView params K).F = (runPrefix 304).2.st.fg.F := by
  have h := (cstoreInv_stateBefore env run (runPrefix 304).1.length 0).fg.Fcar
  rwa [state_before_tick 304 (by decide)] at h

/-- NV-FIN F3. DC: SAME accepted carrier makes the height comparison nonempty. -/
theorem nvFF5HigherNonempty : ∃ K ∈ (runPrefix 304).2.st.fg.TF,
    (finalityView params K).F = (runPrefix 304).2.st.fg.F ∧
    (finalityView params K).h_F < (heightView params nvFinalBlock).h := by
  obtain ⟨K, hK, hF⟩ := nvCurrentCarrier
  exact ⟨K, hK, hF, nvFF5Higher K hK hF⟩

/-- NV-FIN F3. DC: SAME strict-before receipt, at node 0 and deadline 352. -/
theorem nvFF5Accepted : AcceptsFinalBefore params unitCodec env run 0 nvFinalBlock 352 :=
  (Classical.choose_spec nvFF5).2.2 0 (Finset.mem_univ _)

/-- NV-FIN F4. DC: SAME proposal-service gate at 310 is within horizon 404. -/
theorem nvServiceGate :
    V2.D.proposalTime (fgsaInterface params unitCodec) 76 = 304 ∧
    SA.gateTime params.toParams 76 = 310 ∧
    SA.gateTime params.toParams 76 ≤ run.horizon := by decide

/-- NV-FIN F4. DC: SAME aggregate availableGST serves the real slot-76 proposal. -/
theorem nvAvailableService :
    InclusionAt params unitCodec env run ⟨76, nvProposalBlock 76⟩ := by
  obtain ⟨_, _, _, h⟩ := (fgsaClaims params).availableGST gap deltaF nvClock
    unitCodec env run healingTimePrem
  exact h.2 ⟨76, nvProposalBlock 76⟩ (by decide)
    (nvProposalBlock_honest 76 (by decide) (by decide)) nvServiceGate.2.2

/-- NV-FIN F3. DC: SAME strict extension of the real slot-11 proposal. -/
theorem nvLocalStrict : Block.Prec firstProposal (eraseFG nvLocalFinalBlock) := by
  have hr : V2.D.Run.readAt env run 50 0 = (runPrefix 51).2 :=
    congrFun (read_prefix 50 (by decide)) 0
  have h := (Classical.choose_spec nvLocalFF5).1 0 (Finset.mem_univ _)
  rwa [hr, nvLocalSnapshot.1] at h

/-- NV-FIN F3. DC: SAME strict increase above certificate height 2, for the same block. -/
theorem nvLocalHigher : 2 < (heightView params nvLocalFinalBlock).h := by
  have hr : V2.D.Run.readAt env run 50 0 = (runPrefix 51).2 :=
    congrFun (read_prefix 50 (by decide)) 0
  have h := (Classical.choose_spec nvLocalFF5).2.1 0 (Finset.mem_univ _)
  rw [hr] at h
  have hK := nvLocalSnapshot.2.2.1
  have hF := nvLocalSnapshot.2.2.2.2.1
  have hh := nvLocalSnapshot.2.2.2.2.2.2
  simpa only [hh, nvLocalFinalBlock] using h nvLocalCarrier hK hF

/-- NV-FIN F3. DC: SAME local block is accepted at node 0 strictly before time 99. -/
theorem nvLocalAccepted :
    AcceptsFinalBefore params unitCodec env run 0 nvLocalFinalBlock 99 :=
  (Classical.choose_spec nvLocalFF5).2.2 0 (Finset.mem_univ _)

-- NV-FIN: DC: SAME kernel axiom audit for closed inhabitants and conclusions.
#check nvSchedule
#print axioms nvSchedule
#check nvExecution
#print axioms nvExecution
#check base
#print axioms base
#check nvRecovery
#print axioms nvRecovery
#check livenessBound
#print axioms livenessBound
#check healingSet
#print axioms healingSet
#check healingPrem
#print axioms healingPrem
#check healingTimePrem
#print axioms healingTimePrem
#check resetArrivalPrem
#print axioms resetArrivalPrem
#check resetArrivalFullPrem
#print axioms resetArrivalFullPrem
#check renewedPromotionPrem
#print axioms renewedPromotionPrem
#check nvH0Reset
#print axioms nvH0Reset
#check nvH0Reset'
#print axioms nvH0Reset'
#check nvH0
#print axioms nvH0
#check nvHealingInputPrem
#print axioms nvHealingInputPrem
#check nvHealingInput
#print axioms nvHealingInput
#check nvBudgets
#print axioms nvBudgets
#check nvRecFE
#print axioms nvRecFE
#check nvRecF4
#print axioms nvRecF4
#check nvSearchTail
#print axioms nvSearchTail
#check nvFinalitySet
#print axioms nvFinalitySet
#check nvFirstFinalityPrem
#print axioms nvFirstFinalityPrem
#check nvLocalPrem
#print axioms nvLocalPrem
#check nvGSTPrem
#print axioms nvGSTPrem
#check nvAbovePrem
#print axioms nvAbovePrem
#check nvAboveGSTPrem
#print axioms nvAboveGSTPrem
#check nvProposalBlock_honest
#print axioms nvProposalBlock_honest
#check nvProposalPrem
#print axioms nvProposalPrem
#check nvProposalGSTPrem
#print axioms nvProposalGSTPrem
#check nvFF5
#print axioms nvFF5
#check nvFirstFinality
#print axioms nvFirstFinality
#check nvFF5Strict
#print axioms nvFF5Strict
#check nvFF5Higher
#print axioms nvFF5Higher
#check nvCurrentCarrier
#print axioms nvCurrentCarrier
#check nvFF5HigherNonempty
#print axioms nvFF5HigherNonempty
#check nvFF5Accepted
#print axioms nvFF5Accepted
#check nvServiceGate
#print axioms nvServiceGate
#check nvAvailableService
#print axioms nvAvailableService
#check nvLocalFF5
#print axioms nvLocalFF5
#check nvLocalSnapshot
#print axioms nvLocalSnapshot
#check nvLocalStrict
#print axioms nvLocalStrict
#check nvLocalHigher
#print axioms nvLocalHigher
#check nvLocalAccepted
#print axioms nvLocalAccepted

end AvailableChain.FGSA.Run.Tests.NonVacuity.FinalityClaims
end
