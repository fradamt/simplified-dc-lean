module
public import AvailableChainFGSAProofs.Proofs.Outage.ExactProposal
public import AvailableChainFGSAProofs.Proofs.Outage.ExactProposalHistory -- shake: keep (axioms)
public import AvailableChainFGSAProofs.Proofs.Shared.RetainedReflect -- shake: keep (X=Q example)

set_option linter.privateModule false
set_option maxRecDepth 10000
set_option maxSynthPendingDepth 100

namespace AvailableChain.FGSA.Run.Tests.InclusionExact

open AvailableChain.SimplexFG

-- Delta = 1; two honest nodes; node 1 sleeps only at the slot-1 HEAD time.
private abbrev params : Params :=
  ⟨⟨1, 2, 2, 0, by decide, by decide, by decide, by decide⟩,
    2, 0, by decide, 2, by decide⟩
private abbrev env : Generic.Env (Fin 2) :=
  ⟨1, by decide, 0, le_rfl, fun x t => !decide (x = 1 ∧ t = 5)⟩
private abbrev mkRun (es : List (V2.Event (Fin 2) (fgsa params unitCodec).Object)) :
    V2.D.Run (Fin 2) (fgsa params unitCodec) where
  honest := Finset.univ
  horizon := 5
  events := es
  seatOf := fun l j => match l with | .base _ => j | .prop _ => 0
  input := fun _ _ => ()
private abbrev events : List (V2.Event (Fin 2) (fgsa params unitCodec).Object) :=
  (List.range 6).foldl (fun es n =>
    let r := mkRun (es ++ [.tick 0 n, .tick 1 n])
    let objects := V2.D.Run.emitsAt env r es.length ++
      V2.D.Run.emitsAt env r (es.length + 1)
    es ++ [.tick 0 n, .tick 1 n] ++
      objects.flatMap (fun o => [.deliver 0 o n, .deliver 1 o n])) []
private abbrev run := mkRun events

/-- Blueprint 03:354–416; spec 2548–2551; plan I-EXACT, X4.
Class (iii). DC: INTENTIONAL.
The finite schedule keeps both same-time ticks before each delivery. -/
private theorem iexact_schedule : V2.D.ScheduleWellFormed env run where
  horizon_nonneg := by decide
  sorted := by decide +kernel
  nodup := by decide +kernel
  in_horizon := by decide +kernel
  honest_only := by decide +kernel
  tick_public := by
    intro x t ht
    have hall : ∀ e ∈ run.events, 0 ≤ e.time := by decide +kernel
    have hn : 0 ≤ t := hall _ ht
    exact ⟨t.toNat, by simp [Int.toNat_of_nonneg hn]⟩
  tick_total := by
    intro x _ t _ ht hh
    change t ≤ 5 at hh
    interval_cases t <;> fin_cases x <;> decide +kernel

/-- Blueprint 03:354–416; spec 2548–2551; plan I-EXACT, X4.
Class (iii). DC: INTENTIONAL.
The finite test run has no restart event. -/
private theorem noRestart : V2.D.NoRestart run := by
  intro i x t hi
  have hall : ∀ e ∈ run.events,
      (match e with | .restart _ _ => true | _ => false) = false := by decide +kernel
  exact Bool.noConfusion (hall _ (List.mem_of_getElem? hi))

private abbrev proposalIdx : Nat := run.events.findIdx (fun e => e == .tick 0 4)
private abbrev proposal : (fgsa params unitCodec).Object :=
  (V2.D.Run.emitsAt env run proposalIdx)[0]'(by decide +kernel)
private abbrev block : Block :=
  ((fgsaInterface params unitCodec).block proposal.payload).getD .genesis

/-- Blueprint 03:354–416; spec 2548–2551; plan I-EXACT, X4.
Class (iii). DC: INTENTIONAL.
The test block has an actual honest slot-1 proposal emission. -/
private theorem honestProposal :
    HonestProposal env run (fgsaInterface params unitCodec) 1 block := by
  constructor
  · rw [Gen.V2.Duty.HonestSlot_def]
    exact ⟨by decide, Finset.mem_univ _⟩
  · refine ⟨proposal, ⟨proposalIdx, ?_, ?_⟩, ?_⟩
    · decide +kernel
    · exact List.getElem_mem _
    · decide +kernel

-- The positive slot-1 test has a real, non-genesis honest proposal.
/-- Blueprint 03:354–416; spec 2548–2551; plan I-EXACT, X4.
Class (iii). DC: INTENTIONAL.
The emitted test proposal is a non-genesis block. -/
private theorem proposal_nonGenesis : block ≠ .genesis := by decide +kernel

-- Each node accepted the proposal at time 4, strictly before the vote at 5.
/-- Blueprint 03:354–416; spec 2548–2551; plan I-EXACT, X4.
Class (iii). DC: INTENTIONAL.
Both honest nodes accept the test proposal strictly before vote time. -/
private theorem receipt (x : Fin 2) :
    ∃ o i t, (fgsaInterface params unitCodec).block o.payload = some block ∧
      t < SA.voteTime params.toParams 1 ∧ V2.D.Run.acceptsAt env run i x o t := by
  let i := run.events.findIdx (fun e => e == .deliver x proposal 4)
  refine ⟨proposal, i, 4, ?_, by decide, ?_⟩
  · decide +kernel
  · refine ⟨⟨proposal, ?_, Or.inl rfl⟩, ?_, ?_⟩
    all_goals fin_cases x <;> decide +kernel

/-- Blueprint 03:354–416; spec 2548–2551; plan I-EXACT, X4.
Class (iii). DC: INTENTIONAL.
Both scheduled readers compute the test proposal as their HEAD. -/
private theorem headLabel (x : Fin 2) :
    headAtLabel params unitCodec env run x 1 = some block := by
  fin_cases x <;> decide +kernel

-- Both the awake and asleep readers compute the same strict-before HEAD.
/-- Blueprint 03:354–416; spec 2548–2551; plan I-EXACT, X4.
Class (iii). DC: INTENTIONAL.
The strict-before clocked read includes the sleeping reader. -/
private theorem strictHead (x : Fin 2) :
    FGSA.headVote params ((fgsa params unitCodec).clock
      (V2.D.Run.stateBeforeTime env run (SA.voteTime params.toParams 1) x)
      (SA.voteTime params.toParams 1)).st 1 = block :=
  inclusion_head_read env run iexact_schedule noRestart x 1 block (headLabel x)

/-- Blueprint 03:354–416; spec 2548–2551; plan I-EXACT, X4.
Class (iii). DC: INTENTIONAL.
The sleeping honest reader emits no object at vote time. -/
private theorem asleep_silent : ∀ o, ¬ V2.D.Run.emits env run 1 o
    (SA.voteTime params.toParams 1) :=
  inclusion_sleep_silence env run 1 1 (Finset.mem_univ _) (by decide)

-- Sleep does not remove the scheduled tick or the deterministic reader.
example : .tick 1 (SA.voteTime params.toParams 1) ∈ run.events ∧
    env.awake 1 (SA.voteTime params.toParams 1) = false := by decide +kernel
example : (Gen.V2.Duty.faulty run).card <
    (Gen.V2.Duty.awakeHonest env run (SA.voteTime params.toParams 1)).card := by decide

-- A real HEAD delivery at vote time is after all same-time ticks.
private abbrev voteIdx : Nat := run.events.findIdx (fun e => e == .tick 0 5)
private abbrev headObject : (fgsa params unitCodec).Object :=
  (V2.D.Run.emitsAt env run voteIdx)[0]'(by decide +kernel)
private abbrev deliveryIdx : Nat := run.events.findIdx
  (fun e => e == .deliver 1 headObject 5)
example : run.events[deliveryIdx]? = some (.deliver 1 headObject 5) ∧
    V2.D.Run.idxBefore run 5 ≤ voteIdx ∧ voteIdx < deliveryIdx := by decide +kernel
example : afterTicksIdx run 5 ≤ deliveryIdx ∧ deliveryIdx < timeIdx run 5 := by
  decide +kernel

-- The strict-before read excludes any delivery at the read time.
example (p : Params) {In V : Type} [DecidableEq V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hs : V2.D.ScheduleWellFormed E rho) {i : Nat} {x : V} {o : Obj p}
    {d : Time} (hi : rho.events[i]? = some (.deliver x o d)) :
    ¬ i < V2.D.Run.idxBefore rho d := by
  intro h
  exact (lt_irrefl d) ((Gen.V2.Duty.index_lt_idxBefore_iff hs hi d).mp h)

-- The same strict boundary applies to an I-GATE delivery at the gate time.
example (p : Params) {In V : Type} [DecidableEq V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hs : V2.D.ScheduleWellFormed E rho) {i : Nat} {x : V} {o : Obj p} {s : Slot}
    (hi : rho.events[i]? = some (.deliver x o (SA.gateTime p.toParams s))) :
    ¬ i < V2.D.Run.idxBefore rho (SA.gateTime p.toParams s) := by
  intro h
  exact (lt_irrefl _) ((Gen.V2.Duty.index_lt_idxBefore_iff hs hi _).mp h)

-- A delivery at vote time cannot supply an acceptance strictly before it.
example (p : Params) {In V : Type} [DecidableEq V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {i : Nat} {x : V} {o : Obj p} {s : Slot}
    (hi : rho.events[i]? = some (.deliver x o (SA.voteTime p.toParams s))) :
    ¬ ∃ t, t < SA.voteTime p.toParams s ∧ V2.D.Run.acceptsAt E rho i x o t := by
  rintro ⟨t, ht, ⟨⟨parent, he, _⟩, _⟩⟩
  rw [hi] at he
  have heq : SA.voteTime p.toParams s = t := (V2.Event.deliver.inj (Option.some.inj he)).2.2
  exact (lt_irrefl t) (heq ▸ ht)

-- DeltaF = 3 is independent of the block/HEAD delay Delta = 1.
example : fgsaDelay (p := params) 1 3 proposal = 1 ∧
    fgsaDelay (p := params) 1 3 headObject = 1 := by decide +kernel
example (body : RowPayload) :
    fgsaDelay 1 3 (ofRow params ⟨.seat .fg 0, body⟩) = 3 := rfl

-- The old-child reflection route permits a rival at X = the stored parent Q.
example {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hE : V2.D.ExecutionValid E rho) (hN : V2.D.NoRestart rho) (hDelta : E.Δ = p.Δ)
    (s : Slot) (hSync : Gen.V2.Duty.LabelSyncOn E rho (fun o => ¬ isRowObject o)
      (SA.proposalTime p.toParams (s + 1) - p.Δ) (SA.proposalTime p.toParams (s + 1)))
    {ip ih : Nat} {x y : V} (hx : x ∈ rho.honest) (hy : y ∈ rho.honest)
    (hip : rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams (s + 1))))
    (hih : rho.events[ih]? = some (.tick y (SA.voteTime p.toParams (s + 1))))
    (hseat : rho.seatOf (.prop (s + 1)) ⟨0, Nat.one_pos⟩ = x)
    (b : Block) (raw sup : List (HeadWire p.n)) (rows : List (RowWire p.n))
    (hem : (⟨.seat (.prop (s + 1)) ⟨0, Nat.one_pos⟩, .proposal b raw sup rows⟩ : Obj p) ∈
      rho.emitsAt E ip)
    (Kc C : Block)
    (hcut : Block.Preceq (RetainedWalk.z p (clock p (rho.stateBefore E ip x).st
      (SA.proposalTime p.toParams (s + 1)))) Kc)
    (hKQ : Block.Preceq Kc b.parent) (hp : C.parent? = some b.parent)
    (hold : C.slot < s + 1)
    (hm : C ∈ RetainedWalk.T p (clock p (rho.stateBefore E ih y).st
      (SA.voteTime p.toParams (s + 1))) (s + 1))
    (hw : ReflectedDomainWitness p
      (clock p (rho.stateBefore E ip x).st (SA.proposalTime p.toParams (s + 1)))
      (clock p (rho.stateBefore E ih y).st (SA.voteTime p.toParams (s + 1))) (s + 1) C) :
    C ∈ RetainedWalk.S p (clock p (rho.stateBefore E ip x).st
      (SA.proposalTime p.toParams (s + 1))) :=
  fgsa_walkRun_reflected_old_child E rho hE hN hDelta s hSync hx hy hip hih hseat
    b raw sup rows hem Kc b.parent C hcut hKQ (Gen.Pure.block_preceq_refl _)
    hp hold hm hw

#print axioms receipt
#print axioms strictHead
#print axioms asleep_silent
#print axioms honestProposal
#print axioms inclusion_acceptance_of_stored
#print axioms inclusion_receipt_of_compatible
#print axioms inclusion_proposal_receipt
#print axioms inclusion_head_read
#print axioms inclusion_sleep_silence
#print axioms inclusion_comparison_prefix

end AvailableChain.FGSA.Run.Tests.InclusionExact
