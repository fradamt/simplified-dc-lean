module
public import AvailableChainFGSAProofs.Proofs.WeakContinuationGrowth.Counts
-- shake: keep (own-library route)

@[expose] public section

set_option maxRecDepth 1000

namespace AvailableChain.FGSA.Run.Tests.WeakContinuationGrowthNonVacuity

/-! Closed partial witness for the corruption-growth companion.
The W1 generator supplies the model for this five-validator test.
TEST-SCOPE prevents an import of the Inhabit fixture or another Tests module.
The source ends at 247 and three honest validators continue at 248.
MissingFields states the exact fields needed to close both regime records. -/

def params : Params where
  Δ := 1
  n := 5
  k := 2
  η := 0
  deltaPos := by decide
  nPos := by decide
  kLarge := by decide
  etaNonneg := by decide
  R := 2
  δt := 4
  RLarge := by decide
  digest := fun d => ⟨d.slot + 1⟩

abbrev Validator := Fin 5

abbrev Event := V2.Event Validator (fgsa params unitCodec).Object

abbrev World := V2.D.World Validator (fgsa params unitCodec)

instance : DecidableEq Event := by
  change DecidableEq (V2.Event Validator (Obj params))
  infer_instance

def env : Generic.Env Validator where
  Δ := 1
  Δ_pos := by decide
  t_GST := 0
  t_GST_nonneg := by decide
  awake _ _ := true

def seatOf : (ℓ : RunLabel) → Fin (RunLabel.seats params ℓ) → Validator
  | .base _, i => i
  | .prop _, _ => 0

def runData (h : Time) (es : List Event) : V2.D.Run Validator (fgsa params unitCodec) where
  honest := Finset.univ
  horizon := h
  events := es
  seatOf := seatOf
  input _ _ := ()

def nodes : List Validator := [0, 1, 2, 3, 4]

def retained : List Validator := [0, 1, 2]

def retainedSet : Finset Validator := {0, 1, 2}

def tickBatch (vs : List Validator) (t : Time) (w : World) : World × List (Obj params) :=
  vs.foldl (fun acc v =>
    let result := V2.D.tick env (runData 0 []) (acc.1 v) v t
    (Function.update acc.1 v result.1, acc.2 ++ (show List (Obj params) from result.2))) (w, [])

def deliverOne (t : Time) (acc : World × List Event) (vo : Validator × Obj params) :
    World × List Event :=
  if (fgsa params unitCodec).processed (acc.1 vo.1) vo.2 = true ∨
      (V2.Event.deliver vo.1 vo.2 t : Event) ∈ acc.2 then acc else
    (V2.D.World.step env (runData 0 []) acc.1 (.deliver vo.1 vo.2 t),
      acc.2 ++ [.deliver vo.1 vo.2 t])

def timeBatch (vs : List Validator) (t : Time) (w : World) : World × List Event :=
  let ticks := tickBatch vs t w
  let offered := ticks.2.flatMap (fun o => vs.map (fun v => (v, o)))
  offered.foldl (deliverOne t) (ticks.1, vs.map (fun v => .tick v t))

def buildPrefix : Nat → World × List Event
  | 0 => (V2.D.World.init, [])
  | steps + 1 =>
      let previous := buildPrefix steps
      let batch := timeBatch nodes (steps : Time) previous.1
      (batch.1, previous.2 ++ batch.2)

def continuationData (es ds : List Event) : V2.D.Run Validator (fgsa params unitCodec) :=
  { runData 248 [] with
    honest := retainedSet
    events := es.filter (fun e => decide (e.node ∈ retainedSet)) ++ ds }

theorem nvGrowth_liveness : LivenessBoundW params 1 := ⟨by decide⟩

theorem nvGrowth_delta_ratio : params.δt = 2 * params.R := by decide

theorem nvGrowth_committees (rho : V2.D.Run Validator (fgsa params unitCodec))
    (hseat : rho.seatOf = seatOf) :
    V2.D.Linked (fgsaFamilies params unitCodec).linked rho ∧
    V2.D.CStar (fgsaFamilies params unitCodec).fresh rho := by
  constructor
  · refine ⟨5, Equiv.refl _, ?_⟩
    intro label hf
    cases label with
    | prop s => exact hf.elim
    | base label =>
        cases label with
        | head s => exact hf.elim
        | fg => exact ⟨rfl, fun i => by rw [hseat]; rfl⟩
  · intro label hf
    cases label with
    | prop s => exact hf.elim
    | base label =>
        cases label with
        | fg => exact hf.elim
        | head s =>
            rw [hseat]
            exact Function.bijective_id

theorem nvGrowth_delivery_mem (t : Time) (xs : List (Validator × Obj params))
    (acc : World × List Event) (e : Event) :
    (e ∈ acc.2 → e ∈ (xs.foldl (deliverOne t) acc).2) ∧
    (e ∈ (xs.foldl (deliverOne t) acc).2 →
      e ∈ acc.2 ∨ ∃ vo ∈ xs, e = .deliver vo.1 vo.2 t) := by
  induction xs generalizing acc with
  | nil => exact ⟨id, Or.inl⟩
  | cons x xs ih =>
      rw [List.foldl_cons]
      by_cases hp : (fgsa params unitCodec).processed (acc.1 x.1) x.2 = true ∨
          (V2.Event.deliver x.1 x.2 t : Event) ∈ acc.2
      · simp only [deliverOne, hp, ↓reduceIte]
        refine ⟨(ih acc).1, ?_⟩
        intro he
        rcases (ih acc).2 he with he | ⟨vo, hvo, he⟩
        · exact Or.inl he
        · exact Or.inr ⟨vo, List.mem_cons_of_mem _ hvo, he⟩
      · simp only [deliverOne, hp, ↓reduceIte]
        constructor
        · intro he
          exact (ih _).1 (List.mem_append_left _ he)
        · intro he
          rcases (ih _).2 he with he | ⟨vo, hvo, he⟩
          · rcases List.mem_append.mp he with he | he
            · exact Or.inl he
            · exact Or.inr ⟨x, List.mem_cons_self, List.mem_singleton.mp he⟩
          · exact Or.inr ⟨vo, List.mem_cons_of_mem _ hvo, he⟩

theorem nvGrowth_batch_shape (vs : List Validator) (t : Time) (w : World) (e : Event)
    (he : e ∈ (timeBatch vs t w).2) :
    e.time = t ∧ e.node ∈ vs ∧
      ((∃ v, e = .tick v t) ∨ ∃ v o, e = .deliver v o t) := by
  rcases (nvGrowth_delivery_mem t _ _ e).2 he with he | ⟨vo, hvo, rfl⟩
  · obtain ⟨v, hv, rfl⟩ := List.mem_map.mp he
    exact ⟨rfl, hv, Or.inl ⟨v, rfl⟩⟩
  · obtain ⟨o, _, hvo⟩ := List.mem_flatMap.mp hvo
    obtain ⟨v, hv, he⟩ := List.mem_map.mp hvo
    cases he
    exact ⟨rfl, hv, Or.inr ⟨v, o, rfl⟩⟩

theorem nvGrowth_batch_tick (vs : List Validator) (t : Time) (w : World) (v : Validator)
    (hv : v ∈ vs) : V2.Event.tick v t ∈ (timeBatch vs t w).2 :=
  (nvGrowth_delivery_mem t _ _ _).1 (List.mem_map.mpr ⟨v, hv, rfl⟩)

theorem nvGrowth_prefix_times (steps : Nat) (e : Event) (he : e ∈ (buildPrefix steps).2) :
    0 ≤ e.time ∧ e.time < steps := by
  induction steps with
  | zero => simp [buildPrefix] at he
  | succ steps ih =>
      rcases List.mem_append.mp he with he | he
      · have := ih he
        simp only [Nat.cast_add, Nat.cast_one, Time] at *
        omega
      · rw [(nvGrowth_batch_shape _ _ _ _ he).1]
        exact ⟨Int.natCast_nonneg _, by simp⟩

theorem nvGrowth_prefix_tick (steps t : Nat) (ht : t < steps) (v : Validator) :
    V2.Event.tick v (t : Time) ∈ (buildPrefix steps).2 := by
  induction steps with
  | zero => omega
  | succ steps ih =>
      by_cases he : t = steps
      · subst t
        apply List.mem_append_right
        exact nvGrowth_batch_tick nodes (steps : Time) (buildPrefix steps).1 v
          (by fin_cases v <;> simp [nodes])
      · exact List.mem_append_left _ (ih (by omega))

theorem nvGrowth_agreement_of_suffix (es ds : List Event)
    (hds : ∀ e ∈ ds, (247 : Time) < e.time) :
    RetainedAgreesThrough₂ params unitCodec env (runData 247 es) env
      (continuationData es ds) where
  honest := fun _ _ => Finset.mem_univ _
  gst := rfl
  delta := rfl
  seats := rfl
  inputs := fun _ _ _ _ => rfl
  awake := fun _ _ _ _ => rfl
  events := by
    intro v hv
    change v ∈ retainedSet at hv
    change (es.filter (fun e => decide (e.node ∈ retainedSet)) ++ ds).filter
      (fun e => decide (e.node = v ∧ e.time ≤ (247 : Time))) =
        es.filter (fun e => decide (e.node = v ∧ e.time ≤ (247 : Time)))
    rw [List.filter_append]
    have hs : ds.filter (fun e => decide (e.node = v ∧ e.time ≤ (247 : Time))) = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro e he
      have ht := hds e he
      simp [not_le.mpr ht]
    rw [hs, List.append_nil, List.filter_filter]
    apply List.filter_congr
    intro e _
    by_cases he : e.node = v
    · simp [he, hv]
    · simp [he]

theorem nvGrowth_prefix_no_restart (steps : Nat) (v : Validator) (t : Time) :
    V2.Event.restart v t ∉ (buildPrefix steps).2 := by
  induction steps with
  | zero => simp [buildPrefix]
  | succ steps ih =>
      intro he
      rcases List.mem_append.mp he with he | he
      · exact ih he
      · rcases (nvGrowth_batch_shape _ _ _ _ he).2.2 with ⟨u, hu⟩ | ⟨u, o, hu⟩ <;> cases hu

theorem nvGrowth_no_restart_of (es : List Event) (w : World)
    (hnr : ∀ v t, V2.Event.restart v t ∉ es) :
    V2.D.NoRestart (runData 247 es) ∧
    V2.D.NoRestart (continuationData es (timeBatch retained 248 w).2) := by
  constructor
  · intro i v t he
    exact hnr v t (List.mem_of_getElem? he)
  · intro i v t he
    rcases List.mem_append.mp (List.mem_of_getElem? he) with he | he
    · exact hnr v t (List.mem_filter.mp he).1
    · rcases (nvGrowth_batch_shape retained 248 w _ he).2.2 with
        ⟨u, hu⟩ | ⟨u, o, hu⟩ <;> cases hu

theorem nvGrowth_delivery_nodup (t : Time) (xs : List (Validator × Obj params))
    (acc : World × List Event) (hn : acc.2.Nodup) :
    (xs.foldl (deliverOne t) acc).2.Nodup := by
  induction xs generalizing acc with
  | nil => exact hn
  | cons x xs ih =>
      rw [List.foldl_cons]
      by_cases hp : (fgsa params unitCodec).processed (acc.1 x.1) x.2 = true ∨
          (V2.Event.deliver x.1 x.2 t : Event) ∈ acc.2
      · simpa only [deliverOne, hp, ↓reduceIte] using ih acc hn
      · simp only [deliverOne, hp, ↓reduceIte]
        apply ih
        apply hn.append (List.nodup_singleton _)
        intro e he hf
        obtain rfl := List.mem_singleton.mp hf
        exact hp (Or.inr he)

theorem nvGrowth_batch_nodup (vs : List Validator) (hn : vs.Nodup) (t : Time) (w : World) :
    (timeBatch vs t w).2.Nodup :=
  nvGrowth_delivery_nodup _ _ _ (hn.map (by intro v u he; cases he; rfl))

theorem nvGrowth_prefix_nodup (steps : Nat) : (buildPrefix steps).2.Nodup := by
  induction steps with
  | zero => exact List.nodup_nil
  | succ steps ih =>
      apply ih.append (nvGrowth_batch_nodup nodes (by decide) _ _)
      intro e he hb
      have hlt := (nvGrowth_prefix_times steps e he).2
      rw [(nvGrowth_batch_shape _ _ _ _ hb).1] at hlt
      exact (lt_irrefl _ hlt)

theorem nvGrowth_phase_le_two (e : Event) : e.phase ≤ 2 := by cases e <;> simp [V2.Event.phase]

theorem nvGrowth_delivery_sorted (t : Time) (xs : List (Validator × Obj params))
    (acc : World × List Event) (hs : acc.2.Pairwise (fun e f => e.key ≤ f.key))
    (ht : ∀ e ∈ acc.2, e.time ≤ t) :
    (xs.foldl (deliverOne t) acc).2.Pairwise (fun e f => e.key ≤ f.key) := by
  induction xs generalizing acc with
  | nil => exact hs
  | cons x xs ih =>
      rw [List.foldl_cons]
      by_cases hp : (fgsa params unitCodec).processed (acc.1 x.1) x.2 = true ∨
          (V2.Event.deliver x.1 x.2 t : Event) ∈ acc.2
      · simpa only [deliverOne, hp, ↓reduceIte] using ih acc hs ht
      · simp only [deliverOne, hp, ↓reduceIte]
        apply ih
        · rw [List.pairwise_append]
          refine ⟨hs, List.pairwise_singleton _ _, ?_⟩
          intro e he f hf
          obtain rfl := List.mem_singleton.mp hf
          exact Prod.Lex.toLex_le_toLex'.mpr ⟨ht e he, fun _ => nvGrowth_phase_le_two e⟩
        · intro e he
          rcases List.mem_append.mp he with he | he
          · exact ht e he
          · obtain rfl := List.mem_singleton.mp he
            exact le_rfl

theorem nvGrowth_batch_sorted (vs : List Validator) (t : Time) (w : World) :
    (timeBatch vs t w).2.Pairwise (fun e f => e.key ≤ f.key) := by
  apply nvGrowth_delivery_sorted
  · simp only [List.pairwise_map, V2.Event.key, V2.Event.time, V2.Event.phase]
    exact List.pairwise_of_forall (fun _ _ => le_rfl)
  · intro e he
    obtain ⟨v, _, rfl⟩ := List.mem_map.mp he
    exact le_rfl

theorem nvGrowth_prefix_sorted (steps : Nat) :
    (buildPrefix steps).2.Pairwise (fun e f => e.key ≤ f.key) := by
  induction steps with
  | zero => exact List.Pairwise.nil
  | succ steps ih =>
      rw [buildPrefix, List.pairwise_append]
      refine ⟨ih, nvGrowth_batch_sorted _ _ _, ?_⟩
      intro e he f hf
      have he' := (nvGrowth_prefix_times steps e he).2
      apply Prod.Lex.toLex_le_toLex'.mpr
      dsimp only
      rw [(nvGrowth_batch_shape _ _ _ _ hf).1]
      exact ⟨he'.le, fun h => False.elim (ne_of_lt he' h)⟩

/-- A duty-free round releases no object, for any state or run data. -/
theorem nvGrowth_tick_empty {p : Params} {In V : Type} [DecidableEq V]
    (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (st : (fgsa p c).State) (v : V) (t : Time) (hd : duties p t = []) :
    (V2.D.tick E rho st v t).2 = [] := by
  simp [V2.D.tick, fgsa, hd]
  intro _
  rfl

/-- The generator has no deliveries in a duty-free round. -/
theorem nvGrowth_batch_empty (vs : List Validator) (t : Time) (w : World)
    (hd : duties params t = []) :
    (timeBatch vs t w).2 = vs.map (fun v => .tick v t) := by
  have ht (vs : List Validator) (w : World)
      (os : List (fgsa params unitCodec).Object) :
      (vs.foldl (fun acc v =>
        let result := V2.D.tick env (runData 0 []) (acc.1 v) v t
        (Function.update acc.1 v result.1, acc.2 ++ result.2)) (w, os)).2 = os := by
    induction vs generalizing w os with
    | nil => rfl
    | cons v vs ih =>
        exact (ih _ _).trans (by
          rw [nvGrowth_tick_empty unitCodec env _ _ v t hd, List.append_nil])
  have he : (tickBatch vs t w).2 = [] := ht vs w []
  simp [timeBatch, he]

/-- This fact holds for every prefix length, without trace evaluation. -/
theorem nvGrowth_prefix_no_delivery (steps : Nat) (v : Validator) (o : Obj params)
    (t : Time) (hd : duties params t = []) :
    V2.Event.deliver v o t ∉ (buildPrefix steps).2 := by
  induction steps with
  | zero => exact List.not_mem_nil
  | succ steps ih =>
      intro he
      rcases List.mem_append.mp he with he | he
      · exact ih he
      · have ht : t = (steps : Time) := (nvGrowth_batch_shape _ _ _ _ he).1
        rw [← ht, nvGrowth_batch_empty nodes t _ hd] at he
        obtain ⟨u, _, hu⟩ := List.mem_map.mp he
        cases hu

/-- Schedule facts proved for each symbolic prefix. -/
structure PrefixFacts (steps : Nat) (es : List Event) : Prop where
  sorted : es.Pairwise (fun e f => e.key ≤ f.key)
  nodup : es.Nodup
  times : ∀ e ∈ es, 0 ≤ e.time ∧ e.time < steps
  ticks : ∀ t, t < steps → ∀ v, V2.Event.tick v (t : Time) ∈ es
  noRestart : ∀ v t, V2.Event.restart v t ∉ es
  noDelivery : ∀ v o t, duties params t = [] → V2.Event.deliver v o t ∉ es

def certifiedPrefix (steps : Nat) :
    { data : World × List Event // PrefixFacts steps data.2 } :=
  ⟨buildPrefix steps, ⟨nvGrowth_prefix_sorted steps, nvGrowth_prefix_nodup steps,
    nvGrowth_prefix_times steps, nvGrowth_prefix_tick steps, nvGrowth_prefix_no_restart steps,
    nvGrowth_prefix_no_delivery steps⟩⟩

/-- A checked opaque value keeps the long trace out of kernel conversion.
The value is the real generator paired with its symbolic schedule proofs. -/
opaque generatedPrefix : { data : World × List Event // PrefixFacts 248 data.2 } :=
  certifiedPrefix 248

def source : V2.D.Run Validator (fgsa params unitCodec) := runData 247 generatedPrefix.val.2

def endWorld : World := generatedPrefix.val.1

def suffix : List Event := (timeBatch retained 248 endWorld).2

def continuation : V2.D.Run Validator (fgsa params unitCodec) :=
  continuationData source.events suffix

theorem nvGrowth_numbers :
    source.horizon = env.t_GST + B_HF params 1 4 ∧
    0 < source.horizon ∧ source.horizon < continuation.horizon ∧
    (Gen.V2.Duty.faulty source).card = 0 ∧
    (Gen.V2.Duty.faulty continuation).card = 2 ∧
    params.n < 3 * (Gen.V2.Duty.faulty continuation).card ∧
    2 * (Gen.V2.Duty.faulty continuation).card < params.n := by decide

theorem nvGrowth_source_gap (t : Time) (ht : env.t_GST ≤ t) (_hh : t + 4 ≤ source.horizon) :
    ∃ s, t < V2.D.proposalTime (fgsaInterface params unitCodec) s ∧
      V2.D.proposalTime (fgsaInterface params unitCodec) s ≤ t + 4 ∧
      Gen.V2.Duty.HonestSlot source (fgsaInterface params unitCodec) s := by
  refine ⟨(t / 4).toNat + 1, ?_, ?_, ?_⟩
  · change t < 4 * (((t / 4).toNat + 1 : Nat) : Int)
    have ht0 : (0 : Int) ≤ t := ht
    simp only [Time] at *
    omega
  · change 4 * (((t / 4).toNat + 1 : Nat) : Int) ≤ t + 4
    have ht0 : (0 : Int) ≤ t := ht
    simp only [Time] at *
    omega
  · exact ⟨Nat.zero_lt_succ _, Finset.mem_univ _⟩

theorem nvGrowth_participation (t : Time) :
    (Gen.V2.Duty.faulty continuation).card <
      (Gen.V2.Duty.awakeHonest env continuation t).card := by
  change (Finset.univ \ retainedSet).card <
    (retainedSet.filter (fun v => env.awake v t = true)).card
  simp only [env, Finset.filter_true]
  decide

theorem nvGrowth_suffix_nonempty : V2.Event.tick 0 248 ∈ suffix := by
  unfold suffix
  exact nvGrowth_batch_tick retained 248 endWorld 0 (by simp [retained])

theorem nvGrowth_agreement :
    RetainedAgreesThrough₂ params unitCodec env source env continuation := by
  apply nvGrowth_agreement_of_suffix source.events suffix
  intro e he
  rw [(nvGrowth_batch_shape retained 248 endWorld e he).1]
  decide

theorem nvGrowth_no_restart : V2.D.NoRestart source ∧ V2.D.NoRestart continuation :=
  nvGrowth_no_restart_of generatedPrefix.val.2 endWorld generatedPrefix.property.noRestart

theorem nvGrowth_source_in_horizon (e : Event) (he : e ∈ source.events) :
    0 ≤ e.time ∧ e.time ≤ source.horizon := by
  have ht := generatedPrefix.property.times e he
  change 0 ≤ e.time ∧ e.time ≤ 247
  simp only [Time] at *
  omega

theorem nvGrowth_source_tick_total (v : Validator) (t : Time)
    (ht : 0 ≤ t) (hh : t ≤ source.horizon) :
    V2.Event.tick v t ∈ source.events := by
  rw [← Int.toNat_of_nonneg ht]
  apply generatedPrefix.property.ticks
  change t ≤ 247 at hh
  simp only [Time] at *
  omega

theorem nvGrowth_source_schedule : V2.D.ScheduleWellFormed env source where
  horizon_nonneg := by decide
  sorted := generatedPrefix.property.sorted
  nodup := generatedPrefix.property.nodup
  in_horizon := nvGrowth_source_in_horizon
  honest_only := fun _ _ => Finset.mem_univ _
  tick_public := by
    intro v t ht
    have hn : 0 ≤ t := (nvGrowth_source_in_horizon _ ht).1
    exact ⟨t.toNat, by simpa [env] using (Int.toNat_of_nonneg hn).symm⟩
  tick_total := fun v _ t _ ht hh => nvGrowth_source_tick_total v t ht hh

theorem nvGrowth_continuation_schedule_of (es : List Event) (w : World)
    (hs : V2.D.ScheduleWellFormed env (runData 247 es)) :
    V2.D.ScheduleWellFormed env (continuationData es (timeBatch retained 248 w).2) where
  horizon_nonneg := by change (0 : Time) ≤ 248; decide
  sorted := by
    change (es.filter _ ++ (timeBatch retained 248 w).2).Pairwise _
    rw [List.pairwise_append]
    refine ⟨hs.sorted.filter _, nvGrowth_batch_sorted _ _ _, ?_⟩
    intro e he f hf
    have ht : e.time ≤ 247 := (hs.in_horizon e (List.mem_filter.mp he).1).2
    apply Prod.Lex.toLex_le_toLex'.mpr
    dsimp only
    rw [(nvGrowth_batch_shape retained 248 w f hf).1]
    have hlt : e.time < (248 : Time) := lt_of_le_of_lt ht (by decide)
    exact ⟨hlt.le, fun h => False.elim (ne_of_lt hlt h)⟩
  nodup := by
    apply (hs.nodup.filter _).append (nvGrowth_batch_nodup retained (by decide) _ _)
    intro e he hf
    have ht : e.time ≤ 247 := (hs.in_horizon e (List.mem_filter.mp he).1).2
    rw [(nvGrowth_batch_shape retained 248 w e hf).1] at ht
    simp only [Time] at ht
    omega
  in_horizon := by
    intro e he
    rcases List.mem_append.mp he with he | he
    · have ht := hs.in_horizon e (List.mem_filter.mp he).1
      change 0 ≤ e.time ∧ e.time ≤ 248
      change 0 ≤ e.time ∧ e.time ≤ 247 at ht
      exact ⟨ht.1, ht.2.trans (by decide)⟩
    · rw [(nvGrowth_batch_shape retained 248 w e he).1]
      exact ⟨by decide, le_rfl⟩
  honest_only := by
    intro e he
    rcases List.mem_append.mp he with he | he
    · exact of_decide_eq_true (List.mem_filter.mp he).2
    · have hv := (nvGrowth_batch_shape retained 248 w e he).2.1
      simpa [retained, retainedSet, continuationData] using hv
  tick_public := by
    intro v t ht
    rcases List.mem_append.mp ht with ht | ht
    · exact hs.tick_public v t (List.mem_filter.mp ht).1
    · have heq : t = 248 := (nvGrowth_batch_shape retained 248 w _ ht).1
      subst t
      exact ⟨248, rfl⟩
  tick_total := by
    intro v hv t hp ht hh
    change v ∈ retainedSet at hv
    change t ≤ 248 at hh
    change V2.Event.tick v t ∈ es.filter _ ++ (timeBatch retained 248 w).2
    by_cases hbefore : t ≤ 247
    · apply List.mem_append_left
      exact List.mem_filter.mpr ⟨hs.tick_total v (Finset.mem_univ _) t hp ht hbefore,
        by change decide (v ∈ retainedSet) = true; exact decide_eq_true hv⟩
    · have heq : t = 248 := by simp only [Time] at *; omega
      subst t
      apply List.mem_append_right
      exact nvGrowth_batch_tick retained 248 w v (by simpa [retained, retainedSet] using hv)

theorem nvGrowth_continuation_schedule : V2.D.ScheduleWellFormed env continuation :=
  nvGrowth_continuation_schedule_of source.events endWorld nvGrowth_source_schedule

/-- The endpoint round has no network trigger. Both original pending guards remain. -/
theorem nvGrowth_pending :
    PendingSourceDelivery₂ params unitCodec env source env continuation 1 where
  sourceBroadcast := by
    intro v _ o t hem hh w _ hcross _ _
    obtain ⟨i, hi, ho⟩ := hem
    have ht := (nvGrowth_source_in_horizon _ (List.mem_of_getElem? hi)).1
    have hd : fgsaDelay (p := params) env.Δ 1 o = 1 := by
      cases o with | mk a m => cases m <;> rfl
    rw [hd] at hcross
    change 247 < max t 0 + 1 at hcross
    change t ≤ 247 at hh
    have he : t = 247 := by simp only [Time] at *; omega
    subst t
    rw [(V2.D.Run.step_tick_eq env source hi).2,
      nvGrowth_tick_empty unitCodec env source _ v 247 (by decide)] at ho
    cases ho
  sourceRelay := by
    intro v _ i o t ha hh w _ _ hcross _ _
    obtain ⟨a, hi, _⟩ := ha.1
    have ht := (nvGrowth_source_in_horizon _ (List.mem_of_getElem? hi)).1
    have hd : fgsaDelay (p := params) env.Δ 1 o = 1 := by
      cases o with | mk a m => cases m <;> rfl
    rw [hd] at hcross
    change 247 < max t 0 + 1 at hcross
    change t ≤ 247 at hh
    have he : t = 247 := by simp only [Time] at *; omega
    subst t
    exact (generatedPrefix.property.noDelivery v a 247 (by decide)
      (List.mem_of_getElem? hi)).elim

theorem nvGrowth_partialWitness :
    V2.D.ScheduleWellFormed env source ∧
    V2.D.ScheduleWellFormed env continuation ∧
    RetainedAgreesThrough₂ params unitCodec env source env continuation ∧
    source.horizon = env.t_GST + B_HF params 1 4 ∧
    0 < source.horizon ∧ source.horizon < continuation.horizon ∧
    V2.Event.tick 0 248 ∈ suffix ∧
    params.n < 3 * (Gen.V2.Duty.faulty continuation).card ∧
    2 * (Gen.V2.Duty.faulty continuation).card < params.n :=
  ⟨nvGrowth_source_schedule, nvGrowth_continuation_schedule, nvGrowth_agreement, nvGrowth_numbers.1,
    nvGrowth_numbers.2.1, nvGrowth_numbers.2.2.1, nvGrowth_suffix_nonempty,
    nvGrowth_numbers.2.2.2.2.2.1, nvGrowth_numbers.2.2.2.2.2.2⟩

structure MissingFields : Prop where
  sourceValid : V2.D.ExecutionValid env source
  sourceRoots : NamedRootCollisionFree params unitCodec env source
  sourceSync : Gen.V2.Duty.PartialSynchronyBy env source (fgsaDelay env.Δ 1)
  continuationValid : V2.D.ExecutionValid env continuation
  continuationRoots : NamedRootCollisionFree params unitCodec env continuation
  continuationSync : Gen.V2.Duty.PartialSynchronyBy env continuation (fgsaDelay env.Δ 1)
  pending : PendingSourceDelivery₂ params unitCodec env source env continuation 1
  accountable : FinalitySlashableBound params unitCodec env continuation

theorem nvGrowth_complete_of_missing (h : MissingFields) :
    StrongRecoverySearchPrefix₂ params unitCodec env source 4 1 ∧
    CleanGrowthContinuation₂ params unitCodec env source env continuation 1 := by
  constructor
  · exact {
      sync := h.sourceSync
      deltaF := le_rfl
      gap := nvGrowth_source_gap
      base := ⟨h.sourceValid, (nvGrowth_committees source rfl).1,
        (nvGrowth_committees source rfl).2,
        nvGrowth_no_restart.1, rfl, h.sourceRoots⟩
      fault := by decide
      awake := fun _ _ _ _ _ => rfl
      gapPos := by decide
      liveness := nvGrowth_liveness
      endpoint := nvGrowth_numbers.1 }
  · exact {
      base := ⟨h.continuationValid, (nvGrowth_committees continuation rfl).1,
        (nvGrowth_committees continuation rfl).2, nvGrowth_no_restart.2, rfl, h.continuationRoots⟩
      agrees := nvGrowth_agreement
      covered := nvGrowth_numbers.2.2.1.le
      sync := h.continuationSync
      pending := h.pending
      deltaF := le_rfl
      accountable := h.accountable
      participation := fun t _ _ => nvGrowth_participation t }

#print axioms nvGrowth_numbers
#print axioms nvGrowth_agreement
#print axioms nvGrowth_suffix_nonempty
#print axioms nvGrowth_no_restart
#print axioms nvGrowth_source_schedule
#print axioms nvGrowth_continuation_schedule
#print axioms nvGrowth_pending
#print axioms nvGrowth_partialWitness
#print axioms nvGrowth_complete_of_missing

end AvailableChain.FGSA.Run.Tests.WeakContinuationGrowthNonVacuity
end
