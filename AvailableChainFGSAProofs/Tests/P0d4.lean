module
public import AvailableChainFGSAProofs.Proofs.Healing.Attempt
public import AvailableChainFGCompose.Proofs.Healing.AttemptStop

set_option linter.privateModule false

public section
namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG
variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

private def p0d4AuditCore (p : Params) {In : Type} (c : AppCodec In) :
    FGCompose.FGCoreReads (fgsa p c) p.n (GridCO.State p.n .root) (Wire p.n) (RowWire p.n) :=
  { core := fun nd => ⟨nd.st.base, nd.st.fg, nd.st.proposals, nd.st.rowPool⟩
    erase := eraseFG
    source := fun nd => FGSA.fgSource p nd.st
    headVote := fun nd s => FGSA.headVote p nd.st s
    finalityHead := fun nd => FGSA.fgBlockOf nd.st (FGSA.fgHead p nd.st)
    proposalFG := fun nd o => match (toWire p o).decode with
      | some (.block _ N) => (parentFG nd.st N.erase).map (fun P => fgBlock P N.erase N.rows)
      | some (.vote _ _ _) => none
      | some (.row _ _) => none
      | none => none }

private def p0d4AuditSafety (p : Params) {In : Type} (c : AppCodec In) :
    FGCompose.FGSafetyReads (fgsa p c) p.n (RowWire p.n) where
  proposalErase := safetyProposalErase p
  proposalRows := safetyProposalRows p
  encode := ofRow p
  decode := RowWire.toRow?
  decodeObject := decodeRowObject p
  fgLabel := .base .fg
  fgSeats := Equiv.refl _
  record := Node.record
  inputs := fun nd => fgInputs p nd.st
  enabled := fun t => decide (p.actionTime ((p.slotOf t - 1) / p.R) = t)
  finalizedOut := finalizedOut

private def p0d4AuditObs (p : Params) {In : Type} (c : AppCodec In) :
    FGCompose.FGObservationReads (p0d4AuditCore p c) where
  height := heightView p
  finality := finalityView p
  controls nd := FGSA.controls p nd.st
  viable nd X := domainR p nd.st X

private def p0d4AuditTiming (p : Params) : FGCompose.FGTiming where
  delta := p.Δ
  roundSlots := p.R
  proposal := SA.proposalTime p.toParams
  vote := SA.voteTime p.toParams
  early := SA.earlyTime p.toParams
  freeze := SA.freezeTime p.toParams
  release := SA.releaseTime p.toParams
  gate := SA.gateTime p.toParams
  action := p.actionTime

private def p0d4AuditGate (p : Params) {In : Type} (c : AppCodec In) :
    FGCompose.FGAttemptGateReads (fgsa p c) where
  restartTime nd := nd.st.restartTime
  preClock nd t := { nd with st := clockPre p nd.st t }
  saved nd s := (GridCO.savedGenuine nd.st.base s).map (fun b => b.getD .genesis)
  confirmation nd s := SA.Root.confirmationFrom p.toParams (eraseFG nd.st.fg.F)
    (actView nd.st) s
  blocked nd B := (actView nd.st).obligations.any (fun row => !Block.compatible row.1 B)
  writes nd s := fastWriteAt nd.st s

private def p0d4AuditKind : PhaseKind → FGCompose.PhaseKind
  | .gap => .gap | .topJ => .topJ | .contest => .contest

private def p0d4AuditTask : AttemptTask → FGCompose.AttemptTask
  | .raise => .raise | .firstRow => .firstRow

private def p0d4AuditKey (k : AttemptKey) : FGCompose.AttemptKey :=
  ⟨k.start, k.frontier, p0d4AuditKind k.phase, p0d4AuditTask k.task, k.served⟩

private theorem p0d4AuditGateResult (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (x : V) (s : Slot) :
    FGCompose.AttemptGateResult E rho (p0d4AuditTiming p) (p0d4AuditGate p c) x s =
      gateResult p c E rho x s := by
  rw [FGCompose.p0d4_AttemptGateResult_def, gateResult_def, gateIn_def]
  change (preTick E rho x (SA.gateTime p.toParams s)).map _ = _
  simp only [Option.map_map]
  apply congrArg (fun f : Node p → Option Block =>
    (preTick E rho x (SA.gateTime p.toParams s)).map f)
  funext nd
  change (match (clockPre p nd.st (SA.gateTime p.toParams s)).restartTime with
      | none => SA.Root.confirmationFrom p.toParams
          (eraseFG (clockPre p nd.st (SA.gateTime p.toParams s)).fg.F)
          (actView (clockPre p nd.st (SA.gateTime p.toParams s))) s
      | some w => if w ≤ slotStartZ p s then SA.Root.confirmationFrom p.toParams
          (eraseFG (clockPre p nd.st (SA.gateTime p.toParams s)).fg.F)
          (actView (clockPre p nd.st (SA.gateTime p.toParams s))) s else none) = _
  cases hr : (clockPre p nd.st (SA.gateTime p.toParams s)).restartTime <;>
    simp only [Function.comp_apply, hr, ite_true]
  all_goals rfl

private theorem p0d4AuditSource (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (x : V) (r : Nat) :
    (FGCompose.actionSourceFG (p0d4AuditCore p c) E rho (p0d4AuditTiming p) x r).map
      (Option.map eraseFG) = actionSource p c E rho x r := by
  change ((postClock E rho x (p.actionTime r)).map (fun nd => fgSource p nd.st)).map
    (Option.map eraseFG) = _
  change _ = (actionSourceFG p c E rho x r).map (Option.map eraseFG)
  rw [actionSourceFG_def]

private theorem p0d4AuditPassed (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (j : Nat) : FGCompose.AttemptGatePassed E rho (p0d4AuditTiming p)
      (p0d4AuditGate p c) j ↔ gatePassedAt p c E rho j := by
  constructor
  · rintro ⟨x, s, hg, hs, h⟩
    refine ⟨x, s, hg, ?_, h⟩
    exact Option.map_eq_none_iff.mp hs
  · rintro ⟨x, s, hg, hs, h⟩
    refine ⟨x, s, hg, ?_, h⟩
    exact Option.map_eq_none_iff.mpr hs

private theorem p0d4AuditExact (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (s : Slot) (Q : Block) :
    FGCompose.AttemptExactService (p0d4AuditCore p c) E rho (p0d4AuditTiming p)
      (fgsaInterface p c) (p0d4AuditGate p c) s Q ↔ ExactService p c E rho s Q := by
  constructor
  · intro h
    refine ⟨h.1, ?_⟩
    intro hh x hx hr
    obtain ⟨hg, hp, hw, hs, ha⟩ := h.2 hh x hx hr
    exact ⟨(p0d4AuditGateResult E rho x s) ▸ hg,
      (by obtain ⟨j, hj, hp⟩ := hp; exact ⟨j, hj, (p0d4AuditPassed E rho j).mp hp⟩), hw, hs,
      fun r he => (p0d4AuditSource E rho x r) ▸ ha r he⟩
  · intro h
    refine ⟨h.1, ?_⟩
    intro hh x hx hr
    obtain ⟨hg, hp, hw, hs, ha⟩ := h.2 hh x hx hr
    exact ⟨(p0d4AuditGateResult E rho x s).symm ▸ hg,
      (by obtain ⟨j, hj, hp⟩ := hp; exact ⟨j, hj, (p0d4AuditPassed E rho j).mpr hp⟩), hw, hs,
      fun r he => (p0d4AuditSource E rho x r).symm ▸ ha r he⟩

omit [DecidableEq V] in
private theorem p0d4AuditNamed (a : NamedHeightPair) :
    FGCompose.namedEntry a = namedEntry a := by
  cases a <;> rfl

private theorem p0d4AuditRow (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (j : Nat) (y : V) (r : Nat) (a : RowWire p.n) :
    FGCompose.HonestRowAt (p0d4AuditSafety p c) E rho (p0d4AuditTiming p) j y r a =
      HonestRowAt p c E rho j y r a := rfl

private theorem p0d4AuditValid (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {k : AttemptKey} (h : AttemptValid p c E rho k) :
    FGCompose.AttemptValid (p0d4AuditCore p c) (p0d4AuditSafety p c) E rho (p0d4AuditObs p c)
      (p0d4AuditTiming p) (fgsaInterface p c) (p0d4AuditGate p c) (fun a => a.payload.height_pair)
      (recoveryStart p E) (p0d4AuditKey k) := by
  rcases k with ⟨i, m, phase, task, served⟩
  obtain ⟨ev, hi, hgst, hcut, hf, hm, hp, hserved, hn⟩ := h
  refine ⟨ev, hi, hgst, hcut, hf, hm, ?_, ?_, ?_⟩
  · cases phase <;> exact hp
  · constructor
    · intro ht
      obtain ⟨s, Q, Qfg, hQ, heq, hh, hg, hs⟩ := hserved.mp ht
      exact ⟨s, Q, Qfg, hQ, heq, hh, hg, (p0d4AuditExact E rho s Q).mpr hs⟩
    · rintro ⟨s, Q, Qfg, hQ, heq, hh, hg, hs⟩
      exact hserved.mpr ⟨s, Q, Qfg, hQ, heq, hh, hg, (p0d4AuditExact E rho s Q).mp hs⟩
  · cases task with
    | raise => intro h; cases h
    | firstRow =>
      intro _ j y r a h e hj ha he
      rw [p0d4AuditNamed] at he
      exact hn rfl j y r a h e hj ha he

private theorem p0d4AuditEnds (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {k : AttemptKey} {budget : Time} :
    FGCompose.AttemptEndsBy (p0d4AuditCore p c) (p0d4AuditSafety p c) E rho (p0d4AuditObs p c)
      (p0d4AuditTiming p) (fun a => a.payload.height_pair) (p0d4AuditKey k) budget ↔
      AttemptEndsBy p c E rho k budget := by
  rcases k with ⟨i, m, phase, task, served⟩
  constructor <;> rintro ⟨ev, hi, j, ev', hj, hn, ht, he⟩ <;>
    refine ⟨ev, hi, j, ev', hj, hn, ht, ?_⟩
  · rcases he with he | ⟨ht, hf⟩ | ⟨ht, y, r, a, e, ha, hn⟩
    · exact Or.inl he
    · exact Or.inr (Or.inl ⟨(by cases task <;> first | rfl | cases ht), hf⟩)
    · exact Or.inr (Or.inr ⟨(by cases task <;> first | rfl | cases ht),
        y, r, a, e, ha, (p0d4AuditNamed _).symm ▸ hn⟩)
  · rcases he with he | ⟨ht, hf⟩ | ⟨ht, y, r, a, e, ha, hn⟩
    · exact Or.inl he
    · exact Or.inr (Or.inl ⟨(by cases task <;> first | rfl | cases ht), hf⟩)
    · exact Or.inr (Or.inr ⟨(by cases task <;> first | rfl | cases ht),
        y, r, a, e, ha, (p0d4AuditNamed _) ▸ hn⟩)

omit [DecidableEq V] in
private theorem p0d4AuditBudget (G : Time) (k : AttemptKey) :
    FGCompose.attemptBudget (p0d4AuditTiming p) G (ρΓ p G) (p0d4AuditKey k) =
      attemptBudget p G k := by
  rcases k with ⟨i, m, phase, task, served⟩
  rw [FGCompose.p0d4_attemptBudget_def]
  cases task <;> cases phase <;> rfl

private def p0d4AuditOldKind : FGCompose.PhaseKind → PhaseKind
  | .gap => .gap | .topJ => .topJ | .contest => .contest

private def p0d4AuditOldTask : FGCompose.AttemptTask → AttemptTask
  | .raise => .raise | .firstRow => .firstRow

private def p0d4AuditOldKey (k : FGCompose.AttemptKey) : AttemptKey :=
  ⟨k.start, k.frontier, p0d4AuditOldKind k.phase, p0d4AuditOldTask k.task, k.served⟩

omit [DecidableEq V] in
private theorem p0d4AuditKeyBack (k : FGCompose.AttemptKey) :
    p0d4AuditKey (p0d4AuditOldKey k) = k := by
  rcases k with ⟨i, m, phase, task, served⟩
  cases phase <;> cases task <;> rfl

private theorem p0d4AuditValidBack (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {k : FGCompose.AttemptKey}
    (h : FGCompose.AttemptValid (p0d4AuditCore p c) (p0d4AuditSafety p c) E rho (p0d4AuditObs p c)
      (p0d4AuditTiming p) (fgsaInterface p c) (p0d4AuditGate p c) (fun a => a.payload.height_pair)
      (recoveryStart p E) k) : AttemptValid p c E rho (p0d4AuditOldKey k) := by
  rcases k with ⟨i, m, phase, task, served⟩
  obtain ⟨ev, hi, hgst, hcut, hf, hm, hp, hserved, hn⟩ := h
  refine ⟨ev, hi, hgst, hcut, hf, hm, ?_, ?_, ?_⟩
  · cases phase <;> exact hp
  · constructor
    · intro ht
      obtain ⟨s, Q, Qfg, hQ, heq, hh, hg, hs⟩ := hserved.mp ht
      exact ⟨s, Q, Qfg, hQ, heq, hh, hg, (p0d4AuditExact E rho s Q).mp hs⟩
    · rintro ⟨s, Q, Qfg, hQ, heq, hh, hg, hs⟩
      exact hserved.mpr ⟨s, Q, Qfg, hQ, heq, hh, hg, (p0d4AuditExact E rho s Q).mpr hs⟩
  · cases task with
    | raise => intro h; cases h
    | firstRow =>
      intro _ j y r a h e hj ha he
      rw [← p0d4AuditNamed] at he
      exact hn rfl j y r a h e hj ha he

#print axioms p0d4AuditGateResult
#print axioms p0d4AuditSource
#print axioms p0d4AuditExact
#print axioms p0d4AuditValid
#print axioms p0d4AuditEnds
#print axioms p0d4AuditBudget
#print axioms p0d4AuditKeyBack
#print axioms p0d4AuditValidBack
#print axioms AvailableChain.FGSA.Run.healing_attempt_ends_of_event
#print axioms AvailableChain.FGSA.Run.healing_attempt_ends_of_row
#print axioms AvailableChain.FGSA.Run.healing_attempt_ends_mono
#print axioms AvailableChain.FGSA.Run.healing_attempt_no_event
#print axioms AvailableChain.FGSA.Run.healing_attempt_inclusive_start
#print axioms AvailableChain.FGSA.Run.healing_attempt_settle_start
#print axioms AvailableChain.FGSA.Run.healing_attempt_raise_contest_settle
#print axioms AvailableChain.FGSA.Run.healing_attempt_raise_other_settle
#print axioms AvailableChain.FGSA.Run.healing_attempt_firstRow_contest_settle
#print axioms AvailableChain.FGSA.Run.healing_attempt_firstRow_other_settle
#print axioms AvailableChain.FGSA.Run.healing_attempt_firstRow_contest
#print axioms AvailableChain.FGSA.Run.healing_attempt_firstRow_other
#print axioms AvailableChain.FGSA.Run.healing_attempt_raise_contest
#print axioms AvailableChain.FGSA.Run.healing_attempt_raise_other
#print axioms AvailableChain.FGSA.Run.healing_progressAttempt_of
#print axioms AvailableChain.FGSA.Run.healing_progressAttempt
end AvailableChain.FGSA.Run
end
