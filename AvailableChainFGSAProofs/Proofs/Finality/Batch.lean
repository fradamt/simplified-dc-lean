module
public import AvailableChainFGSARun.Proofs.WindowExclusion
public import AvailableChainFGSAClaims.Statements.Fold

public section

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG
open Window (CoveredW)

variable (p : Params) {In V : Type} [DecidableEq V]
    (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

private theorem batch_proposal_read (s : Slot) (st : State p.n)
    (hs : proposalStateAt p c E rho s = some st) :
    ∃ k, st = ((fgsa p c).clock
      (V2.D.Run.stateBefore E rho k (V2.D.proposerOf rho (fgsaInterface p c) s))
      (V2.D.proposalTime (fgsaInterface p c) s)).st := by
  change (postClock E rho _ _).map (·.st) = some st at hs
  rw [postClock_def, preTick_def] at hs
  cases hk : V2.D.Run.tickIdx? rho (V2.D.proposerOf rho (fgsaInterface p c) s)
      (V2.D.proposalTime (fgsaInterface p c) s) with
  | none => rw [hk] at hs; cases hs
  | some k =>
      rw [hk] at hs
      exact ⟨k, (Option.some.inj hs).symm⟩

private theorem batch_chain_occurrence (st : State p.n) (hmeta : MetaInv p st)
    (H : FGBlock (Fin p.n)) (a : RowWire p.n) (b : Row (Fin p.n))
    (hd : a.toRow? = some b) (ha : a ∈ chainWireRows st (eraseFG H)) :
    ∃ W, FGBlock.Preceq W H ∧ b ∈ W.rows := by
  obtain ⟨rows, hrs, ha⟩ := List.mem_flatten.mp ha
  obtain ⟨o, ho, hrows⟩ := List.mem_filterMap.mp hrs
  obtain ⟨s, B, raw, sup, wires, rfl, _hok, _hdec, W, _hW, hWe, hWr⟩ :=
    hmeta.wireTree o ho
  change (if Block.preceq B (eraseFG H) then some wires else none) = some rows at hrows
  split at hrows
  next hpath =>
    have he := Option.some.inj hrows
    subst rows
    refine ⟨W, ?_, ?_⟩
    · apply preceq_of_eraseFG_preceq (Vw := ({W, H} : Finset (FGBlock (Fin p.n))))
        (fun A B _ _ he => FGBlock.root_injective he)
        ⟨W, by simp, KitFG.preceq_refl W⟩ ⟨H, by simp, KitFG.preceq_refl H⟩
      rwa [hWe]
    · rw [hWr]
      exact List.mem_filterMap.mpr ⟨a, ha, hd⟩
  next hpath => cases hrows

/-- Paper 22:715–728, 1265–1289: a finality row sets the retained bit or is carried.
DC: INTENTIONAL exact signed row selection and checked W history; the caller
supplies T-ROWS selection so this Finality proof does not depend on Foundations. -/
theorem finalityRow_bit_or_carried_W
    (hv : V2.D.ExecutionValid E rho) (hsel : TRowsSelect p c E rho)
    (X U : FGBlock (Fin p.n)) (y : Nat) (wireRows : List (RowWire p.n))
    (hc : HonestCarrier p c E rho X.slot (eraseFG X) wireRows)
    (hrows : X.rows = wireRows.filterMap RowWire.toRow?)
    (hparent : ∃ st, proposalStateAt p c E rho X.slot = some st ∧
      FGSA.fgBlockOf st (eraseFG X).parent = some X.parent)
    (e : Window.Entry (Fin p.n)) (he : e ∈ (Window.derive p p.K_W X.parent).W)
    (hej : e.j = y) (heX : e.X = U)
    (i : Fin p.n) (j r : Nat) (a : RowWire p.n)
    (ha : HonestRowAt p c E rho j (rho.seatOf (.base .fg) i) r a)
    (hauth : a.auth = .seat .fg i) (hnames : FinalityNames p a y U)
    (hvalid : ValidForParent p c E rho X.slot (eraseFG X) a)
    (hheld : heldAtProposal p c E rho X.slot a) :
    i ∈ e.Q ∨ ∃ row ∈ X.rows, FinRowNames p row i y U := by
  let b : Row (Fin p.n) := a.payload.toRow i
  have hdecode : a.toRow? = some b := by
    obtain ⟨auth, body⟩ := a
    dsimp only at hauth
    subst auth
    rfl
  have hpair : b.finality_pair = some ⟨y, U.root⟩ := by
    rw [FinalityNames_def] at hnames
    exact hnames
  have hrow : FinRowNames p b i y U := by
    rw [FinRowNames_def]
    exact ⟨rfl, hpair⟩
  rcases hsel X.slot (eraseFG X) wireRows j _ r a hc ha hvalid hheld with hcarry | hchain
  · right
    refine ⟨b, ?_, hrow⟩
    rw [hrows]
    exact List.mem_filterMap.mpr ⟨a, hcarry, hdecode⟩
  · obtain ⟨st, hs, hchain⟩ := hchain
    obtain ⟨parentSt, hps, hlookup⟩ := hparent
    have heq := Option.some.inj (hps.symm.trans hs)
    subst parentSt
    obtain ⟨k, rfl⟩ := batch_proposal_read p c E rho X.slot st hs
    have bundle := storeBundle_postClock E rho k
      (V2.D.proposerOf rho (fgsaInterface p c) X.slot)
      (V2.D.proposalTime (fgsaInterface p c) X.slot)
    have hstored := ((fgBlockOf_spec p _ bundle.cstore _ X.parent).mp hlookup).1
    change X.parent ∈ (clock p _ _).fg.TF at hstored
    rw [clock_fg] at hstored
    rw [eraseFG_parent] at hchain
    obtain ⟨W, hWP, hbW⟩ := batch_chain_occurrence p _ bundle.meta X.parent a b hdecode hchain
    left
    cases W with
    | genesis => exact (List.not_mem_nil hbW).elim
    | node P s body rs =>
        exact exact_row_exclusionW E rho hv k _ X.parent hstored y U e he hej heX
          P s body rs hWP b hbW hpair

variable [Fintype V]

/-- Paper 22:715–728, 1265–1289: a finality batch gives prior parent coverage
or quorum coverage of the same retained entry by the child.
DC: INTENTIONAL W coverage separates the covered and retained cases; T-ROWS
selection is an explicit input for later discharge in Assembly. -/
theorem finalityBatchCoverage_W_of_tRowsSelect (hsel : TRowsSelect p c E rho)
    (ΔF : Time) (q y : Nat) (U X : FGBlock (Fin p.n))
    (h : FinalityBatchPrem_W p c E rho ΔF q y U X) :
    CoveredW p X.parent y U ∨ FinalityCoveredByChild_W p X U y := by
  rcases h.retainedOrCovered with hretained | hcovered
  · obtain ⟨e, he, hej, heX⟩ := (Window.RetainedW_def p X.parent y U).mp hretained
    obtain ⟨wireRows, hc, hrows⟩ := h.carrier
    obtain ⟨S, _hS, hquorum, hseat⟩ := h.batch
    right
    rw [FinalityCoveredByChild_W_def]
    refine ⟨e, he, hej, heX, S, hquorum, ?_⟩
    intro i hi
    obtain ⟨j, a, ha, _hcomplete, hauth, hnames, _hreceipt, hheld, hvalid⟩ := hseat i hi
    exact finalityRow_bit_or_carried_W p c E rho h.base.valid hsel X U y wireRows
      hc hrows h.parent e he hej heX i j q a ha hauth hnames (hvalid hretained).2 hheld
  · exact Or.inl hcovered

end AvailableChain.FGSA.Run
end
