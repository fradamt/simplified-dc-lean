module
public import AvailableChainPCSAProofs.Proofs.Clean.FormationAck
public import AvailableChainPCSAProofs.Proofs.Foundations.SnapshotRun
public import AvailableChainPCSAProofs.Proofs.Foundations.AckPool
public import AvailableChainKitV2.DutyEngineClock

public section

/-! Formation retention facts. The ack pool grows across deliveries and ticks.
NoRestart supplies the run input hAckPoolMono. -/

namespace AvailableChain.PCSA

private theorem formation_row_acks (p : Params) (st : State p.n) (a : RowWire p.n) :
    (admitRow p st a).ackPool = st.ackPool := by
  delta admitRow
  cases a.decode? with
  | none => rfl
  | some val => dsimp only; split <;> rfl

private theorem formation_rows_acks (p : Params) (st : State p.n) (as : List (RowWire p.n)) :
    (as.foldl (admitRow p) st).ackPool = st.ackPool := by
  induction as generalizing st with
  | nil => rfl
  | cons a as ih => rw [List.foldl_cons, ih, formation_row_acks]

private theorem formation_raw_acks_mono {n : Nat} (st : State n) (as : List (AckWire n)) :
    st.ackPool ⊆ (as.foldl poolAckRaw st).ackPool := by
  induction as generalizing st with
  | nil => exact List.Subset.refl _
  | cons a as ih =>
    rw [List.foldl_cons]
    exact List.Subset.trans (poolAckRaw_mono st a) (ih _)

private theorem formation_normalize_acks {n : Nat} (st : State n) :
    (normalizeS st).ackPool = st.ackPool := by
  delta normalizeS
  split <;> rfl

private theorem formation_reconcile_acks {n : Nat} (st : State n) :
    (reconcile st).ackPool = st.ackPool := by
  delta reconcile
  rw [formation_normalize_acks]

private abbrev formationAccepted (p : Params) (st : State p.n) (s : Slot)
    (N : NamedProposal p.n) (P : SimplexFG.FGBlock (Fin p.n)) : State p.n :=
  let st1 : State p.n := { st with
    base := GridCO.admitProposal p.toParams.engine st.base
      (baseProposal s N.erase N.raw N.support) N.erase (N.raw.map baseHead) }
  let st1 := match N.pc with
    | none => st1
    | some C => if pcValid st1 C &&
        !st1.pcs.any (fun old => old.slot == C.slot && old.target == C.target)
      then deleteConflictingLeases st1 C else st1
  let st1 := { st1 with
    fg := FGSA.Window.on_block p p.K_W st1.fg (fgBlock P N.erase N.rows)
    proposals := st.proposals ++ [⟨.proposer s, .proposal N⟩] }
  let st2 := if st1.fg.F = st.fg.F then st1 else reconcile st1
  N.rows.foldl (admitRow p) (collectPCs (N.pcAcks.foldl poolAckRaw st2))

/-- Every handler keeps all pooled acks, including when finality changes. -/
theorem pcsa_formation_process_ackPool_mono (p : Params) (st : State p.n) (o : Wire p.n) :
    st.ackPool ⊆ (process p st o).ackPool := by
  delta process
  cases o.decode with
  | none => exact List.Subset.refl _
  | some d =>
    cases d with
    | vote s i root => exact List.Subset.refl _
    | row i body => rw [formation_row_acks]
    | ack s i root =>
      change st.ackPool ⊆ (collectPCs (poolAck p st ⟨o.auth, root⟩)).ackPool
      rw [(collectPCs_frame _).2.2.1]
      exact poolAck_mono p st _
    | pc C =>
      change st.ackPool ⊆ (admitPC st C).ackPool
      delta admitPC
      split
      · rw [(collectPCs_frame _).2.2.1]
        exact formation_raw_acks_mono st C.acks
      · exact List.Subset.refl _
    | block s N =>
      change st.ackPool ⊆ (admitBlock p st s N).ackPool
      delta admitBlock
      split
      · exact List.Subset.refl _
      · cases parentFG st N.erase with
        | none => exact List.Subset.refl _
        | some P =>
          change st.ackPool ⊆
            (if blockAccepted p st s N P then formationAccepted p st s N P else st).ackPool
          split
          · delta formationAccepted
            rw [formation_rows_acks, (collectPCs_frame _).2.2.1]
            apply List.Subset.trans ?_ (formation_raw_acks_mono _ N.pcAcks)
            cases N.pc <;> dsimp only <;> split_ifs <;>
              simp only [formation_reconcile_acks, deleteConflictingLeases_def] <;>
              exact List.Subset.refl _
          · exact List.Subset.refl _

private theorem formation_gate_acks (p : Params) {n : Nat} (st : State n)
    (a : Block) (cs : List (PC n)) (rank : Option PCRank) (s : Slot) :
    (gateFrom p a cs rank st s).ackPool = st.ackPool := by
  rw [gateFrom_def]
  dsimp only
  cases SA.Root.confirmationFrom p.toParams a (actView st) s with
  | none => rfl
  | some result =>
    dsimp only
    split
    · rfl
    · apply List.foldlRecOn (motive := fun acc : State n => acc.ackPool = st.ackPool)
      · rfl
      · intro acc ha b _
        apply List.foldlRecOn (motive := fun acc' : State n => acc'.ackPool = st.ackPool)
        · exact ha
        · intro acc' ha' g _
          exact ha'

private theorem formation_clockPre_acks (p : Params) (st : State p.n) (t : Time) :
    (clockPre p st t).ackPool = st.ackPool := by
  delta clockPre
  dsimp only
  split <;> split <;> split <;> rfl

/-- Every tick keeps the complete ack pool. -/
theorem pcsa_formation_clock_ackPool (p : Params) (st : State p.n) (t : Time) :
    (clock p st t).ackPool = st.ackPool := by
  delta clock
  dsimp only
  split
  · rw [gateStep_def, formation_normalize_acks]
    split
    · exact formation_clockPre_acks p st t
    · rw [formation_gate_acks]
      exact formation_clockPre_acks p st t
  · exact formation_clockPre_acks p st t

end AvailableChain.PCSA

namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In} {m : FGMode}

/-- NoRestart closes hAckPoolMono at every node without a frame premise. -/
theorem pcsa_formation_run_ackPool_mono (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (hNR : V2.D.NoRestart rho)
    (y : V) (i j : Nat) (hij : i ≤ j) :
    (V2.D.Run.stateBefore E rho i y).st.ackPool ⊆
      (V2.D.Run.stateBefore E rho j y).st.ackPool := by
  refine V2.D.Engine.stateBefore_step_induction E rho
    (fun nd : Node p => (V2.D.Run.stateBefore E rho i y).st.ackPool ⊆ nd.st.ackPool)
    hij y ?_ (List.Subset.refl _)
  intro k e _ _ he hn hm
  cases e with
  | restart x t => exact (hNR k x t he).elim
  | tick x t =>
    change x = y at hn
    subst x
    change (V2.D.Run.stateBefore E rho i y).st.ackPool ⊆
      (Function.update (V2.D.Run.stateBefore E rho k) y _ y).st.ackPool
    rw [Function.update_self]
    have ht := pcsa_tick_st E rho (V2.D.Run.stateBefore E rho k y) y t
    rw [ht, pcsa_formation_clock_ackPool]
    exact hm
  | deliver x o t =>
    change x = y at hn
    subst x
    change (V2.D.Run.stateBefore E rho i y).st.ackPool ⊆
      (Function.update (V2.D.Run.stateBefore E rho k) y _ y).st.ackPool
    rw [Function.update_self]
    exact List.Subset.trans hm (pcsa_formation_process_ackPool_mono p _ (toWire p o))
end AvailableChain.PCSA.Run
end
