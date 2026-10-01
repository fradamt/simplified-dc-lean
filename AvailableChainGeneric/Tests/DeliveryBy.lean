module
public import AvailableChainGeneric.Proofs.V2.Duty.DeliveryBy

@[expose] public section

open AvailableChain AvailableChain.V2 AvailableChain.V2.D AvailableChain.V2.D.Engine
open AvailableChain.Gen.Pure

namespace AvailableChain.Gen.V2.Duty.DeliveryByTests

variable {V : Type} [DecidableEq V] {In : Type} {P : ProtocolSpecD In}
    (E : Generic.Env V) (rho : D.Run V P)

theorem partial_forward (h : D.PartialSynchrony E rho) :
    PartialSynchronyBy E rho (fun _ => E.Δ) :=
  (partialSynchrony_iff_by_const E rho).1 h

theorem partial_reverse (h : PartialSynchronyBy E rho (fun _ => E.Δ)) :
    D.PartialSynchrony E rho :=
  (partialSynchrony_iff_by_const E rho).2 h

theorem prefix_forward (cut : Time) (h : D.HealthyPrefixDelivery E rho cut) :
    HealthyPrefixDeliveryBy E rho (fun _ => E.Δ) cut :=
  (healthyPrefix_iff_by_const E rho cut).1 h

theorem prefix_reverse (cut : Time) (h : HealthyPrefixDeliveryBy E rho (fun _ => E.Δ) cut) :
    D.HealthyPrefixDelivery E rho cut :=
  (healthyPrefix_iff_by_const E rho cut).2 h

theorem true_forward (dl : Time → Time) (cut : Time) (h : DeliveryWithin E rho dl cut) :
    DeliveryWithinOn E rho (fun _ => True) dl cut :=
  (deliveryWithin_iff_on_true E rho dl cut).1 h

theorem true_reverse (dl : Time → Time) (cut : Time)
    (h : DeliveryWithinOn E rho (fun _ => True) dl cut) : DeliveryWithin E rho dl cut :=
  (deliveryWithin_iff_on_true E rho dl cut).2 h

theorem false_vacuous (dl : Time → Time) (cut : Time) :
    DeliveryWithinOn E rho (fun _ => False) dl cut := by
  constructor
  · intro v hv o ho
    exact ho.elim
  · intro v hv i o ho
    exact ho.elim

theorem family_mono {Q Q' : P.Object → Prop} {dl : Time → Time} {cut : Time}
    (h : DeliveryWithinOn E rho Q dl cut) (hQ : ∀ o, Q' o → Q o) :
    DeliveryWithinOn E rho Q' dl cut :=
  DeliveryWithinOn.restrict E rho h hQ

theorem sync_bridge (Q : P.Object → Prop) (vt dt : Time) (h : LabelSync E rho vt dt) :
    LabelSyncOn E rho Q vt dt := labelSync_to_on E rho Q vt dt h

theorem facts_bridge (Q : P.Object → Prop) (vt dt : Time) (h m : Nat)
    (hf : LabelFacts E rho vt dt h m) : LabelFactsOn E rho Q vt dt h m :=
  labelFacts_to_on E rho Q vt dt h m hf

/-- False is the block family. True is the row family. A block can accept a row. -/
abbrev toy : ProtocolSpecD Unit where
  State := Bool
  Label := Unit
  Duty := Empty
  signLabel := Empty.elim
  seats := fun _ => 1
  Payload := Bool
  Durable := Bool
  init := false
  clock := fun st _ => st
  actTime := Empty.elim
  duties := fun _ => []
  duties_spec := by intro d; exact d.elim
  duties_nodup := by intro t; simp
  act := fun _ d => d.elim
  gossip := fun _ _ => []
  process := fun _ _ => true
  selfVisible := fun _ => false
  recordOwn := fun st _ => st
  durable := id
  restore := id
  wellFormed := fun _ => true
  depsPresent := fun _ _ => true
  processed := fun st o => if o.payload then st else false
  excludes := fun _ _ => false
  handles := fun _ o' o => o'.payload = o.payload ∨
    (o'.payload = false ∧ o.payload = true)
  carries := fun o' o => o'.payload = false ∧ o.payload = true

abbrev env : Generic.Env (Fin 2) := ⟨2, by decide, 0, by decide, fun _ _ => true⟩
abbrev ΔF : Time := 5
abbrev block : toy.Object := ⟨.none, false⟩
abbrev row : toy.Object := ⟨.none, true⟩
abbrev delayOf (o : toy.Object) : Time := if o.payload then ΔF else env.Δ
abbrev IsRow (o : toy.Object) : Prop := o.payload = true
abbrev IsBlock (o : toy.Object) : Prop := o.payload = false

abbrev run : D.Run (Fin 2) toy where
  honest := {0, 1}
  horizon := 12
  events := [.deliver 0 block 4, .deliver 1 row 8]
  seatOf := fun _ _ => 0
  input := fun _ _ => ()

theorem delay_gap : env.Δ < ΔF := by decide

theorem row_positive : 0 < ΔF :=
  delay_pos_of_env_le env (le_of_lt delay_gap)

theorem row_deadline_strict (t : Time) : t < t + ΔF :=
  lt_add_of_pos_right t row_positive

theorem row_exact : ∀ o, IsRow o → delayOf o = ΔF := by
  intro o ho
  simp [delayOf, ho]

theorem block_exact : ∀ o, IsBlock o → delayOf o = env.Δ := by
  intro o ho
  simp [delayOf, ho]

theorem no_emission (v : Fin 2) (o : toy.Object) (t : Time) :
    ¬ D.Run.emits env run v o t := by
  rintro ⟨i, hi, _⟩
  have hm := List.mem_of_getElem? hi
  simp at hm

theorem acceptance_cases {i : Nat} {v : Fin 2} {o : toy.Object} {t : Time}
    (ha : D.Run.acceptsAt env run i v o t) :
    IsRow o ∧ ((i = 0 ∧ v = 0 ∧ t = 4) ∨ (i = 1 ∧ v = 1 ∧ t = 8)) := by
  obtain ⟨⟨o', hi, _⟩, _, ht⟩ := ha
  have ho : IsRow o := by
    cases hp : o.payload
    · simp [hp] at ht
    · exact hp
  have hil : i < 2 := (List.getElem?_eq_some_iff.mp hi).1
  have hic : i = 0 ∨ i = 1 := by omega
  refine ⟨ho, ?_⟩
  rcases hic with rfl | rfl
  · change some (Event.deliver (0 : Fin 2) block 4) = some (Event.deliver v o' t) at hi
    have he := Event.deliver.inj (Option.some.inj hi)
    exact Or.inl ⟨rfl, he.1.symm, he.2.2.symm⟩
  · change some (Event.deliver (1 : Fin 2) row 8) = some (Event.deliver v o' t) at hi
    have he := Event.deliver.inj (Option.some.inj hi)
    exact Or.inr ⟨rfl, he.1.symm, he.2.2.symm⟩

theorem relay_delivery (v : Fin 2) (i : Nat) (o : toy.Object) (t : Time)
    (ha : D.Run.acceptsAt env run i v o t) (w : Fin 2)
    (hp : toy.processed (D.Run.stateBefore env run (i + 1) w) o = false) :
    ∃ t', t ≤ t' ∧ t' < t + delayOf o ∧ ∃ j, D.Run.handlesAt env run j w o t' := by
  obtain ⟨ho, hc⟩ := acceptance_cases ha
  rcases hc with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · have hw : w = 0 ∨ w = 1 := by
      have hv : w.val = 0 ∨ w.val = 1 := by omega
      exact hv.imp (fun h => Fin.ext h) (fun h => Fin.ext h)
    rcases hw with rfl | rfl
    · change (if o.payload then true else false) = false at hp
      simp [ho] at hp
    · refine ⟨8, by decide, ?_, 1, row, rfl, Or.inl ho.symm⟩
      rw [row_exact o ho]
      decide
  · have hw : w = 0 ∨ w = 1 := by
      have hv : w.val = 0 ∨ w.val = 1 := by omega
      exact hv.imp (fun h => Fin.ext h) (fun h => Fin.ext h)
    rcases hw with rfl | rfl <;>
      change (if o.payload then true else false) = false at hp <;>
      simp [ho] at hp

theorem partial_by : PartialSynchronyBy env run delayOf := by
  constructor
  · intro v hv o t he
    exact (no_emission v o t he).elim
  · intro v hv i o t ha w hw hp hc hx
    obtain ⟨t', htt, htd, j, hj⟩ := relay_delivery v i o t ha w hp
    exact ⟨t', htt, htd.trans_le (add_le_add (le_max_left t env.t_GST) le_rfl), j, hj⟩

theorem prefix_by : HealthyPrefixDeliveryBy env run delayOf 12 := by
  constructor
  · intro v hv o t he
    exact (no_emission v o t he).elim
  · intro v hv i o t ha w hw hp hc hx
    exact relay_delivery v i o t ha w hp

theorem row_partial : DeliveryWithinOn env run IsRow
    (fun t => max t env.t_GST + ΔF) run.horizon :=
  deliveryWithinOn_of_partialSynchronyBy env run partial_by IsRow ΔF row_exact

theorem block_partial : DeliveryWithinOn env run IsBlock
    (fun t => max t env.t_GST + env.Δ) run.horizon :=
  deliveryWithinOn_of_partialSynchronyBy env run partial_by IsBlock env.Δ block_exact

theorem row_prefix : DeliveryWithinOn env run IsRow (fun t => t + ΔF) 12 :=
  deliveryWithinOn_of_healthyPrefixBy env run 12 prefix_by IsRow ΔF row_exact

theorem block_prefix : DeliveryWithinOn env run IsBlock (fun t => t + env.Δ) 12 :=
  deliveryWithinOn_of_healthyPrefixBy env run 12 prefix_by IsBlock env.Δ block_exact

theorem block_sync_clean : LabelSyncOn env run IsBlock 0 2 :=
  LabelSyncOn.of_cleanCutBy env run IsBlock 12 0 2 prefix_by block_exact
    (by decide) (by decide) (by decide)

theorem block_sync_recovery : LabelSyncOn env run IsBlock 0 2 :=
  LabelSyncOn.of_recoveryBy env run IsBlock 0 2 partial_by block_exact
    (by decide) (by decide) (by decide)

theorem block_facts_clean : LabelFactsOn env run IsBlock 0 2 1 0 :=
  LabelFactsOn.of_cleanCutBy env run IsBlock 12 0 2 1 0 prefix_by block_exact
    (by decide) (by decide) (by decide) ⟨by decide⟩

theorem block_facts_recovery : LabelFactsOn env run IsBlock 0 2 1 0 :=
  LabelFactsOn.of_recoveryBy env run IsBlock 0 2 1 0 partial_by block_exact
    (by decide) (by decide) (by decide) ⟨by decide⟩

/-- The delivered object is the block; the accepted object is the row. -/
theorem row_accepted_through_block : D.Run.acceptsAt env run 0 0 row 4 := by
  exact ⟨⟨block, rfl, Or.inr ⟨rfl, rfl⟩⟩, rfl, rfl⟩

/-- Relay is due at 4 + 5 = 9, from row acceptance, and arrives at 8. -/
theorem row_relay_from_acceptance :
    ∃ t', 4 ≤ t' ∧ t' < 4 + ΔF ∧ ∃ j, D.Run.handlesAt env run j 1 row t' := by
  simpa only [max_eq_left (by decide : env.t_GST ≤ 4), delayOf, row, ↓reduceIte] using
    partial_by.relay_accepted 0 (by simp) 0 row 4 row_accepted_through_block
      1 (by simp) rfl (by decide) rfl

theorem row_relay_after_block_deadline :
    D.Run.handlesAt env run 1 1 row 8 ∧ 4 + env.Δ ≤ 8 ∧ 8 < 4 + ΔF := by
  exact ⟨⟨row, rfl, Or.inl rfl⟩, by decide, by decide⟩

/-- The old all-object delay would require the row before time 6. -/
theorem old_partial_rejected : ¬ D.PartialSynchrony env run := by
  intro h
  obtain ⟨t', _, hlt, j, o', hj, _⟩ := h.relay_accepted 0 (by simp) 0 row 4
    row_accepted_through_block 1 (by simp) rfl (by decide) rfl
  have hm := List.mem_of_getElem? hj
  change Event.deliver (1 : Fin 2) o' t' ∈
    [Event.deliver 0 block 4, Event.deliver 1 row 8] at hm
  simp only [List.mem_cons, List.not_mem_nil, or_false, Event.deliver.injEq] at hm
  rcases hm with ⟨he, _, _⟩ | ⟨_, _, ht⟩
  · exact (by decide : (1 : Fin 2) ≠ 0) he
  · subst t'
    exact (by decide : ¬ (8 : Time) < max 4 env.t_GST + env.Δ) hlt

end AvailableChain.Gen.V2.Duty.DeliveryByTests

-- Kernel audit of the concrete family tests.
#print axioms AvailableChain.Gen.V2.Duty.DeliveryByTests.partial_forward
#print axioms AvailableChain.Gen.V2.Duty.DeliveryByTests.partial_reverse
#print axioms AvailableChain.Gen.V2.Duty.DeliveryByTests.prefix_forward
#print axioms AvailableChain.Gen.V2.Duty.DeliveryByTests.prefix_reverse
#print axioms AvailableChain.Gen.V2.Duty.DeliveryByTests.true_forward
#print axioms AvailableChain.Gen.V2.Duty.DeliveryByTests.true_reverse
#print axioms AvailableChain.Gen.V2.Duty.DeliveryByTests.false_vacuous
#print axioms AvailableChain.Gen.V2.Duty.DeliveryByTests.family_mono
#print axioms AvailableChain.Gen.V2.Duty.DeliveryByTests.sync_bridge
#print axioms AvailableChain.Gen.V2.Duty.DeliveryByTests.facts_bridge
#print axioms AvailableChain.Gen.V2.Duty.DeliveryByTests.delay_gap
#print axioms AvailableChain.Gen.V2.Duty.DeliveryByTests.row_positive
#print axioms AvailableChain.Gen.V2.Duty.DeliveryByTests.row_deadline_strict
#print axioms AvailableChain.Gen.V2.Duty.DeliveryByTests.row_exact
#print axioms AvailableChain.Gen.V2.Duty.DeliveryByTests.block_exact
#print axioms AvailableChain.Gen.V2.Duty.DeliveryByTests.no_emission
#print axioms AvailableChain.Gen.V2.Duty.DeliveryByTests.acceptance_cases
#print axioms AvailableChain.Gen.V2.Duty.DeliveryByTests.relay_delivery
#print axioms AvailableChain.Gen.V2.Duty.DeliveryByTests.partial_by
#print axioms AvailableChain.Gen.V2.Duty.DeliveryByTests.prefix_by
#print axioms AvailableChain.Gen.V2.Duty.DeliveryByTests.row_partial
#print axioms AvailableChain.Gen.V2.Duty.DeliveryByTests.block_partial
#print axioms AvailableChain.Gen.V2.Duty.DeliveryByTests.row_prefix
#print axioms AvailableChain.Gen.V2.Duty.DeliveryByTests.block_prefix
#print axioms AvailableChain.Gen.V2.Duty.DeliveryByTests.block_sync_clean
#print axioms AvailableChain.Gen.V2.Duty.DeliveryByTests.block_sync_recovery
#print axioms AvailableChain.Gen.V2.Duty.DeliveryByTests.block_facts_clean
#print axioms AvailableChain.Gen.V2.Duty.DeliveryByTests.block_facts_recovery
#print axioms AvailableChain.Gen.V2.Duty.DeliveryByTests.row_accepted_through_block
#print axioms AvailableChain.Gen.V2.Duty.DeliveryByTests.row_relay_from_acceptance
#print axioms AvailableChain.Gen.V2.Duty.DeliveryByTests.row_relay_after_block_deadline
#print axioms AvailableChain.Gen.V2.Duty.DeliveryByTests.old_partial_rejected
