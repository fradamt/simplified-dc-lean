module
public import AvailableChainFGSAProofs.Proofs.Finality.Batch
public import AvailableChainFGSAClaims.Statements.Phases

public section

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG
open Window (RetainedW CoveredW)

private theorem carry_parent_height (p : Params) (s : Slot) (P : FGBlock (Fin p.n)) :
    (parentFoldState p s P).h = (heightView p P).h := by
  rw [heightView_def, Window.projectHeight_def]
  rfl

private theorem carry_parent_entry (p : Params) (s : Slot) (P : FGBlock (Fin p.n)) :
    (parentFoldState p s P).T_h = (heightView p P).T_h := by
  rw [heightView_def, Window.projectHeight_def]
  rfl

private theorem carry_decode (p : Params) (a : RowWire p.n) (i : Fin p.n)
    (hauth : a.auth = .seat .fg i) : a.toRow? = some (a.payload.toRow i) := by
  obtain ⟨auth, body⟩ := a
  dsimp only at hauth
  subst auth
  rfl

private theorem carry_payload_pairs (p : Params) (a : RowWire p.n) (i : Fin p.n) :
    (a.payload.toRow i).height_pair = a.payload.height_pair ∧
      (a.payload.toRow i).finality_pair = a.payload.finality_pair := by
  cases a.payload
  exact ⟨rfl, rfl⟩

/-- Paper 22:1265–1289: a retained certificate below the source height gives
the stale R6W arm after the parent crosses that source height.
DC: INTENTIONAL W retention; the certificate and source heights differ,
but the source height need not be the certificate height plus one. -/
private theorem carry_staleUseful (p : Params) (P U : FGBlock (Fin p.n)) (s : Slot)
    (y rowH : Nat) (a : RowWire p.n) (i : Fin p.n)
    (hauth : a.auth = .seat .fg i) (hheight : rowHeight a = some rowH)
    (hnames : FinalityNames p a y U) (hbelow : y < rowH)
    (hcrossed : rowH < (heightView p P).h) (hretained : RetainedW p P y U) :
    ∃ row, a.toRow? = some row ∧
      Window.staleUseful (parentFoldState p s P) row = true ∧
      row.finality_pair = some ⟨y, U.root⟩ := by
  let row := a.payload.toRow i
  have hpairs := carry_payload_pairs p a i
  have hpair : row.finality_pair = some ⟨y, U.root⟩ := by
    rw [FinalityNames_def] at hnames
    exact hpairs.2.trans hnames
  have hwindow : Window.windowMatch (parentFoldState p s P) row = true := by
    obtain ⟨e, he, hej, heX⟩ := (Window.RetainedW_def p P y U).mp hretained
    rw [Window.windowMatch_def, List.any_eq_true]
    refine ⟨e, he, ?_⟩
    simp only [hej, heX, hpair, decide_true]
  refine ⟨row, carry_decode p a i hauth, ?_, hpair⟩
  rw [Window.staleUseful_def, hpair, hpairs.1]
  rw [rowHeight_def] at hheight
  cases hh : a.payload.height_pair with
  | empty => rw [hh] at hheight; cases hheight
  | vote k T timeout =>
      rw [hh] at hheight
      have hk := Option.some.inj hheight
      simp only [hk, carry_parent_height, hbelow, hcrossed, and_self,
        decide_true, hwindow, Bool.true_and]

variable (p : Params) {In V : Type} [DecidableEq V] [Fintype V]
    (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

omit [Fintype V] in
/-- Paper 22:1250–1254, 1265–1289, 1993–2008: carriage with independent
certificate and source heights, including the Tail stale R6W arm.
DC: INTENTIONAL W retention and exact bitmap; the certificate height is
below the source height, with no successor-height requirement. -/
theorem terminalCarriage_general_W (hv : V2.D.ExecutionValid E rho)
    (hsel : TRowsSelect p c E rho) (q y sourceH : Nat) (A U X : FGBlock (Fin p.n))
    (hbelow : y < sourceH)
    (carrier : ∃ wireRows, HonestCarrier p c E rho X.slot (eraseFG X) wireRows ∧
      X.rows = wireRows.filterMap RowWire.toRow?)
    (parent : ∃ st, proposalStateAt p c E rho X.slot = some st ∧
      fgBlockOf st (eraseFG X).parent = some X.parent)
    (path : FGBlock.Preceq A X.parent) (sourceHeight : (heightView p A).h = sourceH)
    (retainedOrCovered : RetainedW p X.parent y U ∨ CoveredW p X.parent y U)
    (S : Finset (Fin p.n)) (rows : Fin p.n → RowWire p.n) (quorum : p.E.IsQuorum S)
    (emitted : ∀ i ∈ S, ∃ j,
      HonestRowAt p c E rho j (rho.seatOf (.base .fg) i) q (rows i) ∧
      (rows i).auth = .seat .fg i ∧ rowHeight (rows i) = some sourceH ∧
      FinalityNames p (rows i) y U)
    (heightEntry : ∀ i ∈ S,
      namedEntry (rows i).payload.height_pair = some (sourceH, (heightView p A).T_h.root))
    (held : ∀ i ∈ S, heldAtProposal p c E rho X.slot (rows i)) :
    CoveredW p X.parent y U ∨
      ((∀ i ∈ S,
        ValidForParent p c E rho X.slot (eraseFG X) (rows i) ∧
        ((heightView p X.parent).h = sourceH ∧
          HeightMatch p c E rho X.slot (eraseFG X) (rows i) ∨
         ∃ row rowH, (rows i).toRow? = some row ∧
           rowHeight (rows i) = some rowH ∧
           y < rowH ∧ rowH < (heightView p X.parent).h ∧
           Window.staleUseful (parentFoldState p X.slot X.parent) row = true ∧
           row.finality_pair = some ⟨y, U.root⟩ ∧ RetainedW p X.parent y U)) ∧
       FinalityCoveredByChild_W p X U y) := by
  rcases retainedOrCovered with hretained | hcovered
  · obtain ⟨e, he, hej, heX⟩ := (Window.RetainedW_def p X.parent y U).mp hretained
    obtain ⟨wireRows, hc, hrows⟩ := carrier
    obtain ⟨st, hs, hparent⟩ := parent
    have hlaws := KitFG.heightLaws_of_bridge p.E p.cfg (heightView p) (heightView_bridge p)
    have hbound : sourceH ≤ (heightView p X.parent).h := by
      rw [← sourceHeight]
      exact hlaws.h_mono path
    have hseat : ∀ i ∈ S,
        ValidForParent p c E rho X.slot (eraseFG X) (rows i) ∧
        ((heightView p X.parent).h = sourceH ∧
          HeightMatch p c E rho X.slot (eraseFG X) (rows i) ∨
         ∃ row rowH, (rows i).toRow? = some row ∧
           rowHeight (rows i) = some rowH ∧
           y < rowH ∧ rowH < (heightView p X.parent).h ∧
           Window.staleUseful (parentFoldState p X.slot X.parent) row = true ∧
           row.finality_pair = some ⟨y, U.root⟩ ∧ RetainedW p X.parent y U) := by
      intro i hi
      obtain ⟨j, _ha, hauth, hheight, hnames⟩ := emitted i hi
      by_cases hsame : (heightView p X.parent).h = sourceH
      · have hentry := hlaws.entry_plateau path (sourceHeight.trans hsame.symm)
        have hmatch : namedEntry (rows i).payload.height_pair =
            some ((parentFoldState p X.slot X.parent).h,
              (parentFoldState p X.slot X.parent).T_h.root) := by
          rw [carry_parent_height, carry_parent_entry, hsame, ← hentry]
          exact heightEntry i hi
        have hrowmatch : Window.heightMatch (parentFoldState p X.slot X.parent)
            ((rows i).payload.toRow i) = true := by
          rw [Window.heightMatch_def, (carry_payload_pairs p (rows i) i).1]
          cases hp : (rows i).payload.height_pair with
          | empty => rw [hp] at hmatch; cases hmatch
          | vote k T timeout =>
              rw [hp] at hmatch
              have hkeys := Prod.mk.inj (Option.some.inj hmatch)
              simp only [NamedHeightPair.matchesEntry, hkeys.1, hkeys.2,
                and_self, decide_true]
        refine ⟨?_, Or.inl ⟨hsame, ?_⟩⟩
        · rw [ValidForParent_def]
          refine ⟨st, X.parent, hs, hparent, ?_⟩
          exact (Window.rowValidW_iff _ _).mpr
            ⟨_, carry_decode p _ i hauth, Or.inl hrowmatch⟩
        · rw [HeightMatch_def]
          exact ⟨st, X.parent, hs, hparent, hmatch⟩
      · have hcrossed : sourceH < (heightView p X.parent).h :=
          Nat.lt_of_le_of_ne hbound (Ne.symm hsame)
        obtain ⟨row, hd, hstale, hpair⟩ := carry_staleUseful p X.parent U X.slot
          y sourceH (rows i) i hauth hheight hnames hbelow hcrossed hretained
        refine ⟨?_, Or.inr ⟨row, sourceH, hd, hheight, hbelow,
          hcrossed, hstale, hpair, hretained⟩⟩
        rw [ValidForParent_def]
        refine ⟨st, X.parent, hs, hparent, ?_⟩
        exact (Window.rowValidW_iff _ _).mpr ⟨row, hd, Or.inr hstale⟩
    right
    refine ⟨hseat, ?_⟩
    rw [FinalityCoveredByChild_W_def]
    refine ⟨e, he, hej, heX, S, quorum, ?_⟩
    intro i hi
    obtain ⟨j, ha, hauth, _hheight, hnames⟩ := emitted i hi
    exact finalityRow_bit_or_carried_W p c E rho hv hsel X U y wireRows
      hc hrows ⟨st, hs, hparent⟩ e he hej heX i j q (rows i) ha hauth hnames
      (hseat i hi).1 (held i hi)
  · exact Or.inl hcovered

/-- Paper 22:1250–1254, 1265–1289: specialize general carriage to the fresh
terminal rows, with certificate height y and source height y + 1.
DC: INTENTIONAL both R6W arms and separate prior coverage; Assembly supplies
T-ROWS selection without a global receipt premise. -/
theorem terminalCarriage_W_of_tRowsSelect (hsel : TRowsSelect p c E rho)
    (ΔF : Time) (q y : Nat) (A U X : FGBlock (Fin p.n))
    (h : TerminalCarriagePrem_W p c E rho ΔF q y A U X) :
    CoveredW p X.parent y U ∨
      ((∀ i ∈ h.seats,
        ValidForParent p c E rho X.slot (eraseFG X) (h.rows i) ∧
        ((heightView p X.parent).h = y + 1 ∧
          HeightMatch p c E rho X.slot (eraseFG X) (h.rows i) ∨
         ∃ row rowH, (h.rows i).toRow? = some row ∧
           rowHeight (h.rows i) = some rowH ∧
           y < rowH ∧ rowH < (heightView p X.parent).h ∧
           Window.staleUseful (parentFoldState p X.slot X.parent) row = true ∧
           row.finality_pair = some ⟨y, U.root⟩ ∧ RetainedW p X.parent y U)) ∧
       FinalityCoveredByChild_W p X U y) := by
  obtain ⟨_hhonest, hquorum, hfresh⟩ := (FreshFinalityRows_W_def p c E rho
    q y U h.seats h.rows).mp h.fresh
  apply terminalCarriage_general_W p c E rho h.base.valid hsel q y (y + 1) A U X
    (Nat.lt_succ_self y) h.carrier h.parent h.path h.freshHeight h.retainedOrCovered
    h.seats h.rows hquorum
  · intro i hi
    obtain ⟨j, C, ha, _hcomplete, hauth, hheight, hnames, _hsource, _hC, _hfirst⟩ :=
      hfresh i hi
    exact ⟨j, ha, hauth, hheight, hnames⟩
  · exact h.heightEntry
  · intro i hi
    exact (h.receipt i hi).2

end AvailableChain.FGSA.Run
end
