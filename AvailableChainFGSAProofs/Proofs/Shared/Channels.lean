module
public import AvailableChainFGSAClaims.Statements.ChannelProps
import AvailableChainFGSARun.Proofs.Emission
import AvailableChainFGSARun.Proofs.Hooks

public section

/-! Channel equations for P3 F0.8a. Gen.V2.linked_holder_eq and
Gen.V2.linked_card_le_of_holders supply identity transport (Q5, S4b-14).
T7 provides `processed_stable`, `fgsa_proposal_receipt`, `fgsa_head_receipt`,
`EmitsRow`, `EmittedRowsNoSlash`, `decodeRowObject`, `honest_emit_wellFormed`,
`contentAgree_run`, and `fgsa_receiptCoverage`; this file does not restate them. -/

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

variable (p : Params)

theorem ancestorClosed_preceq (B : FGBlock (Fin p.n)) :
    AncestorClosed p (fun e => FGBlock.Preceq e B) := by
  constructor
  intro X Y hXY hYB
  exact KitFG.preceq_trans hXY hYB

theorem ancestorClosed_compatible (B : FGBlock (Fin p.n)) :
    AncestorClosed p (fun e => FGBlock.Preceq e B ∨ FGBlock.Preceq B e) := by
  constructor
  intro X Y hXY hY
  rcases hY with hYB | hBY
  · exact Or.inl (KitFG.preceq_trans hXY hYB)
  · exact KitFG.preceq_total_of_common hXY hBY

theorem srcFrame_genesis_preceq (B : FGBlock (Fin p.n)) (c₀ : Nat) :
    c₀ ≤ hOf p.E p.cfg (.genesis : FGBlock (Fin p.n)) → FGBlock.Preceq .genesis B :=
  fun _ => KitFG.genesis_preceq B

theorem srcFrame_genesis_compatible (B : FGBlock (Fin p.n)) (c₀ : Nat) :
    c₀ ≤ hOf p.E p.cfg (.genesis : FGBlock (Fin p.n)) →
      FGBlock.Preceq .genesis B ∨ FGBlock.Preceq B .genesis :=
  fun _ => Or.inl (KitFG.genesis_preceq B)

/-- The store selector is the channel's deepest member of X_r ∩ D(Σ.T). -/
theorem fgSource_eq_jointSource (st : State p.n) :
    FGSA.fgSource p st = jointSource p st := by
  rw [jointSource_def, domainR_def, frameR_def, treeT_def]
  change FGSA.deepest ((FGSA.fullTree p st).filter _) =
    FGSA.deepest ((FGSA.fullTree p st).filter _)
  apply congrArg (FGSA.deepest (n := p.n))
  apply Finset.filter_congr
  intro B _
  rw [sourceCandidates_def, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq,
    Finset.mem_filter, List.mem_toFinset]
  cases leaseOf st (eraseFG B) <;> rfl

/-- For a positive slot, propose uses the joint proposer head as parent. -/
theorem propose_head (st : State p.n) (s : Slot) (hs : s ≠ 0) :
    FGSA.propose p st s = some (.proposal
      (.node (proposerHead p st s) s (packBody 0 (proposalRows p st (proposerHead p st s))))
      ((proposerVotes st s).filterMap liftHead?) ((proposerSupport st s).filterMap liftHead?)
      (proposalRows p st (proposerHead p st s))) := by
  rw [proposerHead_def]
  change (if s = 0 then none else _) = _
  exact ite_eq_right hs

/-- The frame reads only the FG store. -/
theorem frameR_congr_fg (st st' : State p.n) (h : st.fg = st'.fg) :
    frameR p st = frameR p st' := by
  rw [frameR_def, frameR_def]
  exact congrArg (storeControls p.E p.cfg) h

/-- D(X) reads the FG store and X, with no vote-pool input. -/
theorem domainR_congr_fg (st st' : State p.n) (X : Finset (FGBlock (Fin p.n)))
    (h : st.fg = st'.fg) : domainR p st X = domainR p st' X := by
  rw [domainR_def, domainR_def, frameR_congr_fg p st st' h]

/-- HEAD eligibility uses the live lo relaxation, then score and current slot. -/
theorem eligible_lo_live (st : State p.n) (raw sup : List (GridCO.Wire p.n)) (B : Block) :
    FGSA.eligible p st raw sup B =
      (decide (∃ P ∈ st.fg.TF, eraseFG P = B.parent ∧ hOf p.E p.cfg P < (frameR p st).lo) ||
       decide (GridCO.voterCount raw < 2 * GridCO.goldfishScore st.base.blocks raw sup B) ||
       B.slot == st.slot p) := rfl

/-- All five joint selections and the finality triple ignore the own record Λ. -/
theorem jointSelections_record_irrel (st : State p.n) (Λ Λ' : Record)
    (s : Slot) (raw sup : List (GridCO.Wire p.n)) (B : Block) :
    let nd : Node p := ⟨st, Λ⟩
    let nd' : Node p := ⟨st, Λ'⟩
    (FGSA.liveRoot p nd.st, FGSA.eligible p nd.st raw sup B, jointSource p nd.st,
      proposerHead p nd.st s, FGSA.fgHead p nd.st, (FGSA.fgInputs p nd.st).2) =
    (FGSA.liveRoot p nd'.st, FGSA.eligible p nd'.st raw sup B, jointSource p nd'.st,
      proposerHead p nd'.st s, FGSA.fgHead p nd'.st, (FGSA.fgInputs p nd'.st).2) := rfl

variable {In V : Type} (c : AppCodec In) [DecidableEq V]
    (rho : V2.Run V (fgsa p c))

/-- The pre-tick and post-clock reads have the same FG frame.
The gate can still change the AC candidates. -/
theorem frame_postClock (E : Generic.Env V) (x : V) (t : Time) (nd nd' : Node p)
    (hpre : preTick E rho x t = some nd) (hpost : postClock E rho x t = some nd') :
    frameR p nd'.st = frameR p nd.st := by
  rw [postClock_def, hpre] at hpost
  have he : (fgsa p c).clock nd t = nd' := Option.some.inj hpost
  rw [← he]
  exact frameR_congr_fg p _ _ (FGSA.clock_fg p nd.st t)

omit [DecidableEq V] in
/-- A holder alone is insufficient: the authentication must be an FG seat. -/
theorem rowSigner_iff_holder (a : RowWire p.n) (x : V) : RowSigner p c rho a x ↔
    (∃ r i, a.auth = .seat (.fg r) i) ∧ V2.Run.holder rho (ofRow p a).auth = some x := by
  rw [RowSigner_def]
  constructor
  · rintro ⟨r, i, ha, hx⟩
    refine ⟨⟨r, i, ha⟩, ?_⟩
    change V2.Run.holder rho (ofAuth p a.auth) = some x
    rw [ha]
    exact congrArg some hx
  · rintro ⟨⟨r, i, ha⟩, hx⟩
    refine ⟨r, i, ha, ?_⟩
    change V2.Run.holder rho (ofAuth p a.auth) = some x at hx
    rw [ha] at hx
    exact Option.some.inj hx

/-- An honest signed row is released before its direct or carried handler call.
The time inequality can be non-strict; tick-before-delivery makes the index strict. -/
theorem emit_lt_handles (E : Generic.Env V) (h : V2.ExecutionValid E rho)
    {j k : Nat} {y x : V} {r : Nat} {a : RowWire p.n}
    (he : HonestRowAt p c E rho j y r a) (hh : HandlesRowAt p c E rho k x a) : j < k := by
  rw [HonestRowAt_def] at he
  obtain ⟨hy, hr, t, hj, hem⟩ := he
  obtain ⟨u, envelope, hk, hhandle⟩ := hh
  rcases a with ⟨auth, body⟩
  cases auth with
  | none => cases hr
  | proposer s => cases hr
  | seat label seat =>
    cases label with
    | head s => cases hr
    | fg r' =>
      have hrow := (fgsa_emitsAt_row E rho j y t hj r' seat body).mp hem
      have hholder : V2.Run.holder rho (ofRow p ⟨.seat (.fg r') seat, body⟩).auth = some y :=
        congrArg some hrow.2.2.1
      have horigin : ∃ u', u' ≤ u ∧
          V2.Run.emits E rho y (ofRow p ⟨.seat (.fg r') seat, body⟩) u' := by
        rcases (fgsaHooks p c).handles_carries _ envelope _ hhandle with heq | hc
        · subst envelope
          exact h.unforgeable x _ u ⟨k, hk⟩ y hy hholder
        · exact h.carried x envelope u ⟨k, hk⟩ _ hc y hy hholder
      obtain ⟨u', hle, j', hj', hem'⟩ := horigin
      have hrow' := (fgsa_emitsAt_row E rho j' y u' hj' r' seat body).mp hem'
      have htu : t ≤ u := hrow.2.1 ▸ (hrow'.2.1.symm ▸ hle)
      exact V2.Engine.tick_index_lt_delivery E rho h.toScheduleWellFormed hj hk htu

end AvailableChain.FGSA.Run
end
