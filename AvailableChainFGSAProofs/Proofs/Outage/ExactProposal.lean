module
public import AvailableChainFGSAClaims.Statements.Packages.Safety
public import AvailableChainFGSAClaims.Statements.Channels
public import AvailableChainFGSARun.Proofs.Receipts
public import AvailableChainFGSAProofs.Proofs.Shared.CatchUp

public section

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

/-- A durable block has a network acceptance before the index. A restart
restamps the block but does not create its original acceptance. -/
theorem inclusion_acceptance_before_index
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (k : Nat) (x : V)
    (b : Block) (hne : b ≠ .genesis)
    (hm : b ∈ (V2.D.Run.stateBefore E rho k x).st.base.blocks) :
    ∃ i < k, ∃ t o, blockOf? p o = some b ∧ V2.D.Run.acceptsAt E rho i x o t := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    rw [← (metaInv_stateBefore E rho k x).stampKeys] at hm
    obtain ⟨⟨b', stamp⟩, hm, he⟩ := List.mem_map.mp hm
    dsimp only at he
    subst b'
    rcases fgsa_block_stamp_source_or_restart E rho k x b stamp hm with
      hg | ⟨i, hi, t, o, ho, ha, _⟩ | ⟨j, hj, _, _, _, hb, _⟩
    · exact (hne hg.1).elim
    · exact ⟨i, hi, t, o, ho, ha⟩
    · obtain ⟨i, hi, t, o, ho, ha⟩ := ih j hj hb
      exact ⟨i, hi.trans hj, t, o, ho, ha⟩

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 03:354–416; spec 2548–2551; plan I-EXACT, X1 (acceptance step).
Class (iii). DC: INTENTIONAL; a non-genesis block in the strict read has an
earlier acceptance. The original acceptance survives every restart. -/
theorem inclusion_acceptance_of_stored
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hs : V2.D.ScheduleWellFormed E rho) (b : Block) (u : Time) (x : V)
    (hne : b ≠ .genesis)
    (hm : b ∈ (V2.D.Run.stateBeforeTime E rho u x).st.base.blocks) :
    ∃ o i t, (fgsaInterface p c).block o.payload = some b ∧ t < u ∧
      V2.D.Run.acceptsAt E rho i x o t := by
  rw [← Gen.V2.Duty.stateBefore_idxBefore E rho u hs] at hm
  obtain ⟨i, hi, t, o, ho, ha⟩ := inclusion_acceptance_before_index E rho _ x b hne hm
  obtain ⟨parent, hd, _⟩ := ha.1
  refine ⟨o, i, t, ?_, (Gen.V2.Duty.index_lt_idxBefore_iff hs hd u).mp hi, ha⟩
  rcases o with ⟨auth, payload⟩
  cases auth with
  | none => cases payload <;> cases ho
  | seat l j =>
    cases l with
    | base l => cases l <;> cases payload <;> cases ho
    | prop s =>
        cases payload with
        | head => cases ho
        | row => cases ho
        | proposal => exact ho

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. Blueprint 03:354–416; spec 2548–2551; plan I-EXACT, X1 (receipt step).
Class (iii). DC: INTENTIONAL; non-row traffic uses Delta independently of
the row delay. This is the receipt consumer; Clean compatibility must be
produced with receiver service before it can discharge X1. Readers are joined. -/
theorem inclusion_receipt_of_compatible [Fintype V]
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (ΔF : Time)
    (hset : CleanSet p c E rho ΔF)
    (s : Slot) (N : NamedProposal p.n)
    (hne : N.erase ≠ .genesis)
    (hService : ∀ x, headReader p E rho x s (SA.voteTime p.toParams s) →
      Nonempty (ReceiverService E rho (ofWire p ⟨.proposer s, .proposal N⟩)
        (SA.proposalTime p.toParams s) (SA.voteTime p.toParams s) x)) :
    ∀ x, headReader p E rho x s (SA.voteTime p.toParams s) →
      ∃ o i t, (fgsaInterface p c).block o.payload = some N.erase ∧
        t < SA.voteTime p.toParams s ∧ V2.D.Run.acceptsAt E rho i x o t := by
  intro x hx
  obtain ⟨h⟩ := hService x hx
  obtain ⟨Y, hY, heY⟩ := h.proposal hset.pre.base.valid.toScheduleWellFormed hx.1
    hset.pre.base.receiptIdealization
  have hm := ((storeBundle_stateBeforeTime E rho (SA.voteTime p.toParams s) x).cstore.baseTree
    N.erase).mpr ⟨Y, hY, heY⟩
  exact inclusion_acceptance_of_stored E rho hset.pre.base.valid.toScheduleWellFormed
    N.erase (SA.voteTime p.toParams s) x hne hm

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 03:354–416; spec 2548–2551; plan I-EXACT, X1 (honest input).
Class (iii). DC: INTENTIONAL; the supplied honest proposal produces the
non-genesis fact. The Clean joint induction must supply receiver service
with checked dependencies, finality compatibility, and the current epoch. -/
theorem inclusion_proposal_receipt [Fintype V]
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (ΔF : Time)
    (hset : CleanSet p c E rho ΔF) (pt : PtSP)
    (hprop : HonestProposal E rho (fgsaInterface p c) pt.s pt.P)
    (hService : ∀ N, V2.D.Run.emits E rho (V2.D.proposerOf rho (fgsaInterface p c) pt.s)
      (ofWire p ⟨.proposer pt.s, .proposal N⟩) (SA.proposalTime p.toParams pt.s) →
      ∀ x, headReader p E rho x pt.s (SA.voteTime p.toParams pt.s) →
        Nonempty (ReceiverService E rho (ofWire p ⟨.proposer pt.s, .proposal N⟩)
          (SA.proposalTime p.toParams pt.s) (SA.voteTime p.toParams pt.s) x)) :
    ∀ x, headReader p E rho x pt.s (SA.voteTime p.toParams pt.s) →
      ∃ o i t, (fgsaInterface p c).block o.payload = some pt.P ∧
        t < SA.voteTime p.toParams pt.s ∧ V2.D.Run.acceptsAt E rho i x o t := by
  obtain ⟨hslot, o, ⟨ip, hip, hem⟩, hb⟩ := hprop
  have hx : V2.D.proposerOf rho (fgsaInterface p c) pt.s ∈ rho.honest := hslot.2
  have haw : E.awake (V2.D.proposerOf rho (fgsaInterface p c) pt.s)
      (SA.proposalTime p.toParams pt.s) = true := by
    cases he : E.awake (V2.D.proposerOf rho (fgsaInterface p c) pt.s)
        (SA.proposalTime p.toParams pt.s) with
    | true => rfl
    | false =>
      rw [(V2.D.Run.step_tick_eq E rho hip).2,
        (fgsa_tick_asleep E rho (V2.D.Run.stateBefore E rho ip
          (V2.D.proposerOf rho (fgsaInterface p c) pt.s))
          (V2.D.proposerOf rho (fgsaInterface p c) pt.s)
          (V2.D.proposalTime (fgsaInterface p c) pt.s) he).1] at hem
      exact (List.not_mem_nil hem).elim
  have hw := honest_emit_wellFormed E rho hset.pre.base.valid.toDeliveryWellFormed
    hset.pre.base.valid.toScheduleWellFormed ip _ _ hip hx haw o hem
  rcases o with ⟨auth, payload⟩
  cases payload with
  | head b => cases hb
  | row body => cases hb
  | proposal N =>
    have hbp : N.erase = pt.P := Option.some.inj hb
    cases auth with
    | none => cases hw
    | seat l j =>
      cases l with
      | base l => cases l <;> cases hw
      | prop s =>
        have hj : j = ⟨0, Nat.one_pos⟩ := Subsingleton.elim (α := Fin 1) _ _
        subst j
        have hm := hem
        rw [(V2.D.Run.step_tick_eq E rho hip).2] at hm
        have hp := (fgsa_emits_proposal E rho _ _ _ s _).mp hm
        have htime := hp.2.1
        change (4 * p.Δ) * (s : Int) = (4 * p.Δ) * (pt.s : Int) at htime
        have hs : s = pt.s := Int.natCast_inj.mp
          (mul_left_cancel₀ (ne_of_gt (mul_pos (by decide) p.deltaPos)) htime)
        subst s
        have hne : N.erase ≠ .genesis := by
          intro hg
          have hn := (named_erase_eq_genesis N).mp hg
          subst N
          change false = true at hw
          cases hw
        have hresult := inclusion_receipt_of_compatible E rho ΔF hset pt.s N hne
          (hService N ⟨ip, hip, hem⟩)
        simpa only [hbp] using hresult

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 03:354–416; spec 2548–2551; plan I-EXACT, X2 (read step).
Class (iii). DC: INTENTIONAL; the strict-before clocked read equals the
scheduled deterministic HEAD even for an asleep reader. The HEAD value
must first be produced by the retained-walk proof. -/
theorem inclusion_head_read
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hs : V2.D.ScheduleWellFormed E rho) (hnr : V2.D.NoRestart rho)
    (x : V) (s : Slot) (b : Block) (hh : headAtLabel p c E rho x s = some b) :
    FGSA.headVote p ((fgsa p c).clock
      (V2.D.Run.stateBeforeTime E rho (SA.voteTime p.toParams s) x)
      (SA.voteTime p.toParams s)).st s = b := by
  change (postClock E rho x (SA.voteTime p.toParams s)).map _ = some b at hh
  rw [postClock_def, preTick_def] at hh
  cases hi : V2.D.Run.tickIdx? rho x (SA.voteTime p.toParams s) with
  | none => simp only [hi, Option.map_none, reduceCtorEq] at hh
  | some i =>
    simp only [hi, Option.map_some, Option.some.injEq] at hh
    rw [fgsa_preTick_eq_timeRead E rho hs hnr (V2.D.Run.tickIdx?_spec hi)] at hh
    exact hh

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 03:354–416; spec 2548–2551; plan I-EXACT, X3.
Class (iii). DC: INTENTIONAL; sleep suppresses every emitted object while
the deterministic clock and read remain defined. No Clean or tick premise
is needed. -/
theorem inclusion_sleep_silence
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (s : Slot) :
    ∀ x ∈ rho.honest, E.awake x (SA.voteTime p.toParams s) = false →
      ∀ o, ¬ V2.D.Run.emits E rho x o (SA.voteTime p.toParams s) := by
  intro x _ hx o ⟨i, hi, hem⟩
  rw [(V2.D.Run.step_tick_eq E rho hi).2,
    (fgsa_tick_asleep E rho (V2.D.Run.stateBefore E rho i x) x _ hx).1] at hem
  exact List.not_mem_nil hem

end AvailableChain.FGSA.Run
end
