module
public import AvailableChainFGSAProofs.Proofs.Assembly.Clean -- shake: keep (fixture root lemmas)
public import AvailableChainFGSAProofs.Proofs.Outage.ContinuationTiming

/-! OUTPUT-DIRECT non-vacuity in the kernel. A closed run satisfies every field of
`OutageContinuationPrem`, in both modes. The fixture adapts the delayed-row run of
`Tests/Zero.lean` (one honest node, Δ = 1, ΔF = 3, horizon 17); its private proofs
are copied here. Here η = 2, every emission is delivered at its emission time, and
the only honest node is asleep on [b₀,b₁) = [8,13). Then b₁ − b₀ = 5 > min η L = 2,
so the old Outage₂ budget fails, while (V) holds at equality. -/

-- Test fixtures and examples stay private.
set_option linter.privateModule false

set_option maxSynthPendingDepth 100
set_option maxRecDepth 10000
open AvailableChain AvailableChain.SimplexFG
namespace AvailableChain.FGSA.Run.Tests.OutageContinuationInhabit.Sleep
private abbrev p : FGSA.Params :=
  ⟨⟨1, 1, 2, 2, by decide, by decide, by decide, by decide⟩, 2, 0, by decide, 2, by decide, fun
      d => ⟨d.slot + 1⟩⟩
private abbrev E : Generic.Env (Fin 1) :=
  ⟨1, by decide, 0, le_rfl, fun _ t => decide (t < 8 ∨ 13 ≤ t)⟩
private abbrev mkRun (es : List (V2.Event (Fin 1) (fgsa p unitCodec).Object)) :
    V2.D.Run (Fin 1) (fgsa p unitCodec) where
  honest := Finset.univ
  horizon := 17
  events := es
  seatOf := fun _ _ => 0
  input := fun _ _ => ()
private abbrev events : List (V2.Event (Fin 1) (fgsa p unitCodec).Object) :=
  (List.range 18).foldl (fun es n =>
    let r := mkRun (es ++ [.tick 0 n])
    es ++ [.tick 0 n] ++ (V2.D.Run.emitsAt E r es.length).map (fun o => .deliver 0 o n)) []
private abbrev rho := mkRun events
private abbrev children (o : (fgsa p unitCodec).Object) : List (fgsa p unitCodec).Object :=
  match o.payload with
  | .proposal N => N.raw.map (ofHead p) ++ N.support.map (ofHead p) ++ N.rows.map (ofRow p)
  | _ => []
private theorem carries_children (o o' : (fgsa p unitCodec).Object) :
    (fgsa p unitCodec).carries o o' ↔ o' ∈ children o := by
  change carriesS p o o' ↔ _
  cases o with
  | mk a m =>
    cases m with
    | head => exact ⟨False.elim, fun h => List.not_mem_nil h⟩
    | row => exact ⟨False.elim, fun h => List.not_mem_nil h⟩
    | proposal N =>
      change _ ↔ o' ∈ (N.raw.map (ofHead p) ++ N.support.map (ofHead p)) ++
        N.rows.map (ofRow p)
      constructor
      · rintro (h | h | h)
        · exact List.mem_append_left _ (List.mem_append_left _ h)
        · exact List.mem_append_left _ (List.mem_append_right _ h)
        · exact List.mem_append_right _ h
      · intro h
        rcases List.mem_append.mp h with h | h
        · rcases List.mem_append.mp h with h | h
          · exact Or.inl h
          · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h)

private def EventOK (i : Nat) (e : V2.Event (Fin 1) (fgsa p unitCodec).Object) : Prop :=
  match e with
    | .deliver v o t =>
      (fgsa p unitCodec).wellFormed o = true ∧
      (fgsa p unitCodec).depsPresent (V2.D.Run.stateBefore E rho i v) o = true ∧
      (fgsa p unitCodec).processed (V2.D.Run.stateBefore E rho i v) o = false ∧
      (∃ j : Fin rho.events.length, rho.events[j.val].time ≤ t ∧
        rho.events[j.val] = .tick v rho.events[j.val].time ∧ o ∈ V2.D.Run.emitsAt E rho j) ∧
      (∀ o' ∈ children o, ∃ j : Fin rho.events.length,
        rho.events[j.val].time ≤ t ∧ rho.events[j.val] = .tick 0 rho.events[j.val].time ∧
          o' ∈ V2.D.Run.emitsAt E rho j)
    | _ => True
private instance (i : Nat) (e : V2.Event (Fin 1) (fgsa p unitCodec).Object) :
    Decidable (EventOK i e) := by
  cases e <;> unfold EventOK <;> infer_instance

private theorem checks : ∀ i : Fin rho.events.length, EventOK i rho.events[i.val] := by
  decide +kernel

private theorem lsync_schedule : V2.D.ScheduleWellFormed E rho where
  horizon_nonneg := by decide
  sorted := by
    decide +kernel
  nodup := by
    decide +kernel
  in_horizon := by
    decide +kernel
  honest_only := by
    decide +kernel
  tick_public := by
    intro v t ht
    have hall : ∀ e ∈ rho.events, 0 ≤ e.time := by
      decide +kernel
    have hn : 0 ≤ t := hall _ ht
    exact ⟨t.toNat, by simp [Int.toNat_of_nonneg hn]⟩
  tick_total := by
    intro v _ t _ ht hh
    have hv : v = 0 := Subsingleton.elim _ _
    subst v
    change t ≤ 17 at hh
    interval_cases t <;> decide +kernel

private theorem lsync_execution : V2.D.ExecutionValid E rho where
  toScheduleWellFormed := lsync_schedule
  wire := by
    intro i v o t hi
    obtain ⟨hil, he⟩ := List.getElem?_eq_some_iff.mp hi
    have hc := checks ⟨i, hil⟩
    simp only [EventOK, he] at hc
    exact hc.1
  deps := by
    intro i v o t hi
    obtain ⟨hil, he⟩ := List.getElem?_eq_some_iff.mp hi
    have hc := checks ⟨i, hil⟩
    simp only [EventOK, he] at hc
    exact hc.2.1
  fresh := by
    intro i v o t hi
    obtain ⟨hil, he⟩ := List.getElem?_eq_some_iff.mp hi
    have hc := checks ⟨i, hil⟩
    simp only [EventOK, he] at hc
    exact hc.2.2.1
  unforgeable := by
    rintro v o t ⟨i, hi⟩ u _ _
    obtain ⟨hil, he⟩ := List.getElem?_eq_some_iff.mp hi
    have hc := checks ⟨i, hil⟩
    simp only [EventOK, he] at hc
    obtain ⟨j, ht, hj, hem⟩ := hc.2.2.2.1
    have huv : v = u := Subsingleton.elim _ _
    subst u
    exact ⟨_, ht, j, List.getElem?_eq_some_iff.mpr ⟨j.isLt, hj⟩, hem⟩
  carried := by
    rintro v o t ⟨i, hi⟩ o' hc u _ _
    obtain ⟨hil, he⟩ := List.getElem?_eq_some_iff.mp hi
    have hh := checks ⟨i, hil⟩
    simp only [EventOK, he] at hh
    obtain ⟨j, ht, hj, hem⟩ := hh.2.2.2.2 o' ((carries_children o o').mp hc)
    have hu : u = 0 := Subsingleton.elim _ _
    subst u
    exact ⟨_, ht, j, List.getElem?_eq_some_iff.mpr ⟨j.isLt, hj⟩, hem⟩

private def Delivered (i : Nat) (e : V2.Event (Fin 1) (fgsa p unitCodec).Object) : Prop :=
  match e with
      | .tick v t => ∀ o ∈ V2.D.Run.emitsAt E rho i, t + fgsaDelay E.Δ 3 o ≤ 17 →
        ∃ j : Fin rho.events.length, t ≤ rho.events[j.val].time ∧
          rho.events[j.val].time < t + fgsaDelay E.Δ 3 o ∧
          rho.events[j.val] = .deliver v o rho.events[j.val].time
      | _ => True
private instance (i : Nat) (e : V2.Event (Fin 1) (fgsa p unitCodec).Object) :
    Decidable (Delivered i e) := by
  cases e <;> unfold Delivered <;> infer_instance

private theorem lsync_delivered : ∀ i : Fin rho.events.length, Delivered i rho.events[i.val] := by
  decide +kernel

private theorem deliveryPrefix :
    Gen.V2.Duty.HealthyPrefixDeliveryBy E rho (fgsaDelay E.Δ 3) 17 where
  broadcast_emitted := by
    rintro v _ o t ⟨i, hi, hem⟩ w _ hd _
    obtain ⟨hil, he⟩ := List.getElem?_eq_some_iff.mp hi
    have hc := lsync_delivered ⟨i, hil⟩
    simp only [Delivered, he] at hc
    obtain ⟨j, ht, hd, hj⟩ := hc o hem hd
    have hvw : v = w := Subsingleton.elim _ _
    subst w
    exact ⟨_, ht, hd, j, o, List.getElem?_eq_some_iff.mpr ⟨j.isLt, hj⟩, Or.inl rfl⟩
  relay_accepted := by
    intro v _ i o t ha w _ hp
    have hvw : v = w := Subsingleton.elim _ _
    subst w
    rw [ha.2.2] at hp
    contradiction


/-- ROOT-DIGEST W3b. The existing event certificate gives actual emission origin. -/
private theorem delay_rootEmission {x : Fin 1} {o : Obj p} {t : Time}
    (hd : V2.Event.deliver x o t ∈ rho.events) : ∃ i u,
    rho.events[i]? = some (.tick 0 u) ∧ o ∈ rho.emitsAt E i := by
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hd
  obtain ⟨hjl, he⟩ := List.getElem?_eq_some_iff.mp hj
  have hc := checks ⟨j, hjl⟩
  change EventOK j rho.events[j] at hc
  have hc' : EventOK j (.deliver x o t) := he ▸ hc
  dsimp only [EventOK] at hc'
  obtain ⟨i, _, hi, hem⟩ := hc'.2.2.2.1
  have hx : x = 0 := Subsingleton.elim _ _
  subst x
  exact ⟨i, _, List.getElem?_eq_some_iff.mpr ⟨i.isLt, hi⟩, hem⟩

/-- ROOT-DIGEST W3b. Decode a delivered proposal without any root assumption. -/
private theorem delay_rootProposal {x : Fin 1} {o : Obj p} {t : Time} {B : NamedProposal p.n}
    (hd : V2.Event.deliver x o t ∈ rho.events) (hp : o.payload = .proposal B) :
    ∃ s, o = ofWire p ⟨.proposer s, .proposal B⟩ := by
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hd
  have hw := lsync_execution.wire j x o t hj
  cases hm : (toWire p o).decode with
  | none =>
    change FGSA.wellFormed p (toWire p o) = true at hw
    simp only [FGSA.wellFormed, hm, Bool.false_eq_true] at hw
  | some m =>
    have he (w : Wire p.n) (h : toWire p o = w) : o = ofWire p w := by
      apply (toWireEquiv p).injective
      exact h.trans ((toWireEquiv p).right_inv w).symm
    cases m with
    | vote s j b => rw [he _ (decode_eq_vote.mp hm)] at hp; cases hp
    | row j body => rw [he _ (decode_eq_row.mp hm)] at hp; cases hp
    | block s b =>
      have ho := he _ (decode_eq_block.mp hm)
      rw [ho] at hp
      cases Msg.proposal.inj hp
      exact ⟨s, ho⟩

/-- ROOT-DIGEST W3b. Each scoped non-genesis body has a delivered origin. -/
private theorem delay_rootParents : ∀ x o t b,
    V2.Event.deliver x o t ∈ rho.events → o.payload = .proposal b →
    ∃ i y, b.parent ∈ (V2.D.Run.stateBefore E rho i y).st.namedBodies := by
  intro x o t b hd hp
  obtain ⟨i, u, hi, hem⟩ := delay_rootEmission hd
  obtain ⟨j, hj⟩ := emitted_payload_parent_stored E rho ⟨i, hi, hem⟩ hp
  exact ⟨j, 0, hj⟩

/-- ROOT-DIGEST W3b. Equal delivered slot roots identify the same single-seat action. -/
private theorem delay_rootDeliveredEq {x y : Fin 1} {o o' : Obj p} {t u : Time}
    {B C : NamedProposal p.n}
    (hd : V2.Event.deliver x o t ∈ rho.events) (hp : o.payload = .proposal B)
    (hd' : V2.Event.deliver y o' u ∈ rho.events) (hp' : o'.payload = .proposal C)
    (he : B.root = C.root) : B = C := by
  obtain ⟨s, rfl⟩ := delay_rootProposal hd hp
  obtain ⟨s', rfl⟩ := delay_rootProposal hd' hp'
  obtain ⟨i, ti, hi, hem⟩ := delay_rootEmission hd
  obtain ⟨j, tj, hj, hem'⟩ := delay_rootEmission hd'
  have hbr := emitted_proposal_slot_root E rho (fun _ => rfl) i 0 ti s B hi hem
  have hcr := emitted_proposal_slot_root E rho (fun _ => rfl) j 0 tj s' C hj hem'
  have hslots : B.slot = C.slot := Nat.add_right_cancel
    (congrArg BlockId.value (hbr.symm.trans (he.trans hcr)))
  rw [(V2.D.Run.step_tick_eq E rho hi).2] at hem
  rw [(V2.D.Run.step_tick_eq E rho hj).2] at hem'
  have ha := (fgsa_emits_proposal E rho _ 0 ti s _).mp hem
  have ha' := (fgsa_emits_proposal E rho _ 0 tj s' _).mp hem'
  obtain ⟨H, raw0, sup0, rows0, hb, _, _⟩ := rowsOk_withApp _ _ _ ha.2.2.2
  obtain ⟨H', raw1, sup1, rows1, hc, _, _⟩ := rowsOk_withApp _ _ _ ha'.2.2.2
  have hBs : B.slot = s := by
    have hh := congrArg (fun m : Msg p.n => match m with
      | .proposal b => b.slot | _ => 0) hb
    exact hh
  have hCs : C.slot = s' := by
    have hh := congrArg (fun m : Msg p.n => match m with
      | .proposal b => b.slot | _ => 0) hc
    exact hh
  have hss : s = s' := hBs.symm.trans (hslots.trans hCs)
  rw [← hss] at ha'
  have htt : ti = tj := ha.2.1.symm.trans ha'.2.1
  subst tj
  have hij : i = j := by
    obtain ⟨hil, hei⟩ := List.getElem?_eq_some_iff.mp hi
    obtain ⟨hjl, hej⟩ := List.getElem?_eq_some_iff.mp hj
    exact (lsync_execution.nodup.getElem_inj_iff (hi := hil) (hj := hjl)).mp (hei.trans hej.symm)
  subst j
  exact (Msg.proposal.inj (Option.some.inj (ha.2.2.2.symm.trans ha'.2.2.2)))

/-- ROOT-DIGEST W3b. Origin closes the body scope; no fixture premise is assumed. -/
private theorem delay_rootPremise : NamedRootCollisionFree p unitCodec E rho where
  root_injective := by
    intro B C hB hC A D hA hD he
    have scopeX {X : NamedProposal p.n} (hX : NamedProposal.Preceq X B ∨ NamedProposal.Preceq X C) :
        NamedProposalInRun p unitCodec E rho X := by
      rcases hX with hX | hX
      · exact namedScope_ancestor E rho hB hX
      · exact namedScope_ancestor E rho hC hX
    have deliveredRoot {x : Fin 1} {o : Obj p} {t : Time} {X : NamedProposal p.n}
            (hd : V2.Event.deliver x o t ∈ rho.events) (hp : o.payload = .proposal X) :
        X.root = ⟨X.slot + 1⟩ := by
      obtain ⟨s, rfl⟩ := delay_rootProposal hd hp
      obtain ⟨i, u, hi, hem⟩ := delay_rootEmission hd
      exact emitted_proposal_slot_root E rho (fun _ => rfl) i 0 u s X hi hem
    rcases namedProposalInRun_genesis_or_delivered E rho delay_rootParents (scopeX hA) with
      rfl | hdA
    · rcases namedProposalInRun_genesis_or_delivered E rho delay_rootParents (scopeX hD) with
        rfl | hdD
      · rfl
      · obtain ⟨x, o, t, hd, hp⟩ := hdD
        exact (Nat.succ_ne_zero D.slot
          (congrArg BlockId.value (he.trans (deliveredRoot hd hp))).symm).elim
    · obtain ⟨x, o, t, hd, hp⟩ := hdA
      rcases namedProposalInRun_genesis_or_delivered E rho delay_rootParents (scopeX hD) with
        rfl | hdD
      · exact (Nat.succ_ne_zero A.slot
          (congrArg BlockId.value ((deliveredRoot hd hp).symm.trans he))).elim
      · obtain ⟨y, o', u, hd', hp'⟩ := hdD
        exact delay_rootDeliveredEq hd hp hd' hp' he

private theorem base : Base₂ p unitCodec E rho where
  valid := lsync_execution
  idealization := delay_rootPremise
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
  noRestart := by
    intro i v t hi
    have hm := List.mem_of_getElem? hi
    have cert : ∀ e ∈ rho.events, (match e with | .restart _ _ => true | _ => false) = false := by
      decide +kernel
    exact Bool.noConfusion (cert _ hm)
  delta := rfl

private theorem awake_card {t : Time} (ht : t < 8 ∨ 13 ≤ t) :
    (Gen.V2.Duty.awakeHonest E rho t).card = 1 := by
  rw [Gen.V2.Duty.awakeHonest_def, Finset.filter_true_of_mem (fun _ _ => decide_eq_true ht)]
  rfl

private theorem faulty_card : (Gen.V2.Duty.faulty rho).card = 0 := by decide

/-- Every honest node is asleep throughout the outage interval [8,13). -/
theorem all_asleep (t : Time) (h8 : 8 ≤ t) (h13 : t < 13) :
    Gen.V2.Duty.awakeHonest E rho t = ∅ := by
  rw [Gen.V2.Duty.awakeHonest_def]
  exact Finset.filter_false_of_mem (fun _ _ h => by
    rcases (of_decide_eq_true h : t < 8 ∨ 13 ≤ t) with h' | h'
    · exact (not_lt.mpr h8) h'
    · exact (not_le.mpr h13) h')

private theorem healthy_cut {b : Time} (hb : b ≤ 17) :
    Gen.V2.Duty.HealthyPrefixDeliveryBy E rho (fgsaDelay E.Δ 3) b where
  broadcast_emitted := fun v hv o t he w hw hd hx =>
    deliveryPrefix.broadcast_emitted v hv o t he w hw (hd.trans hb) hx
  relay_accepted := fun v hv i o t ha w hw hp hd hx =>
    deliveryPrefix.relay_accepted v hv i o t ha w hw hp (hd.trans hb) hx

private theorem sync : Gen.V2.Duty.PartialSynchronyBy E rho (fgsaDelay E.Δ 3) where
  broadcast_emitted := by
    rintro v hv o t ⟨i, hi, hem⟩ w hw hd hx
    have h0 : 0 ≤ t := (lsync_schedule.in_horizon _ (List.mem_of_getElem? hi)).1
    have hm : max t E.t_GST = t := max_eq_left h0
    rw [hm] at hd hx ⊢
    exact deliveryPrefix.broadcast_emitted v hv o t ⟨i, hi, hem⟩ w hw hd hx
  relay_accepted := by
    intro v _ i o t ha w _ hp
    have hvw : v = w := Subsingleton.elim _ _
    subst w
    rw [ha.2.2] at hp
    contradiction

/-- Every field of the continuation premise holds, in both modes, through full
honest sleep on [b₀,b₁) = [8,13). -/
theorem outageContinuation_inhabited_sleep (fast : Bool) :
    OutageContinuationPrem p unitCodec fast E rho 4 8 13 3 where
  pre := ⟨base, ⟨by decide, by decide⟩, healthy_cut (by decide), by decide, by
    intro t _ ht
    rw [awake_card (Or.inl ht), faulty_card]
    decide⟩
  sleepy := by
    intro t _ ht
    have h1 := Finset.card_le_univ (awakeHonestIn E rho (t - p.η) t ∪ Gen.V2.Duty.faulty rho)
    rw [Fintype.card_fin] at h1
    rw [awake_card (Or.inl ht)]
    omega
  order := by decide
  lag := by cases fast <;> decide
  -- (V) at equality: b₁ is the vote time of the restored label j + K = 3.
  lengthV := (outageV_iff_vote_bound p 8 13 (by decide)).mpr (by decide)
  fastPart := by
    intro _ t _ ht
    rw [awake_card (Or.inl ht)]
    decide
  sync := sync
  gst := by decide
  partAfter := by
    intro t ht _
    rw [awake_card (Or.inr ht), faulty_card]
    decide

/-- The old Outage₂ budget fails for these endpoints, so only the continuation
claim covers this run. -/
theorem old_budget_fails : ¬ ((13 : Time) - 8 ≤ min p.η (L p)) := by decide

theorem not_outage₂ (fast : Bool) : ¬ Outage₂ p unitCodec fast E rho 4 8 13 3 :=
  fun h => old_budget_fails h.budget

#print axioms outageContinuation_inhabited_sleep
#print axioms all_asleep
#print axioms not_outage₂

end AvailableChain.FGSA.Run.Tests.OutageContinuationInhabit.Sleep
