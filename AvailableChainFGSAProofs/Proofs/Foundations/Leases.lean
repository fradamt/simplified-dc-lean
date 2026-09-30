module
public import AvailableChainFGSAClaims.Statements.Reads
public import AvailableChainFGSA.Proofs.LeaseOutput

public import AvailableChainFGSARun.Proofs.AncestorDeadlines
public import AvailableChainGeneric.Proofs.V2.BaseTransport
public import AvailableChainFGSAProofs.Proofs.Shared.Reads

public section

namespace AvailableChain.FGSA.Run

variable (p : Params) {In V : Type} [DecidableEq V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.Run V (fgsa p c))

/-- All stored targets, including due rows, are below the current output.
Gen E-10 `invariant_triple` lifts the E-11 store preservation lemmas.
T7.5 supplies `CStoreInv` and `NestOK` through the reachable store bundle. -/
theorem fgsa_storedTargetsBelowOutput (i : Nat) (x : V) :
    StoredTargetsBelowOutput p (storeAt p c E rho i x) := by
  have h := Gen.V2.invariant_triple (P := fgsa p c)
    (fun nd : Node p => Reachable p nd.st ∧ StoredTargetsBelowOutput p nd.st)
    ⟨Reachable.init, storedTargetsBelowOutput_init p⟩
    (fun nd t h => ⟨Reachable.tick t h.1,
      storedTargetsBelowOutput_clock p nd.st t
        (storeBundle_of_reachable p nd.st h.1).cstore
        (storeBundle_of_reachable p nd.st h.1).nest h.2⟩)
    (fun nd o h => ⟨Reachable.deliver (toWire p o) h.1,
      storedTargetsBelowOutput_process p nd.st (toWire p o)
        (storeBundle_of_reachable p nd.st h.1).cstore h.2⟩)
    (fun _ _ h => h)
    (fun _ _ => ⟨Reachable.init, storedTargetsBelowOutput_init p⟩)
    E rho i x
  exact h.2

private def fastPairs (st : State p.n) : List (Slot × Block) :=
  st.fastWrite.flatMap (fun row => row.2.map (fun B => (row.1, B)))

private theorem fastPairs_reconcile (st : State p.n) :
    fastPairs p (reconcile st) ⊆ fastPairs p st := by
  intro pair hp
  obtain ⟨row, hr, hm⟩ := List.mem_flatMap.mp hp
  rw [reconcile_fastWrite] at hr
  obtain ⟨old, ho, rfl⟩ := List.mem_map.mp hr
  obtain ⟨B, hB, rfl⟩ := List.mem_map.mp hm
  exact List.mem_flatMap.mpr ⟨old, ho,
    List.mem_map.mpr ⟨B, (List.mem_filter.mp hB).1, rfl⟩⟩

private theorem fastPairs_admitRows (rows : List (RowWire p.n)) (st : State p.n) :
    fastPairs p (rows.foldl (admitRow p) st) = fastPairs p st := by
  induction rows generalizing st with
  | nil => rfl
  | cons a rows ih =>
    rw [List.foldl_cons, ih]
    rcases admitRow_eq p st a with h | h <;> rw [h]
    rfl

private theorem fastPairs_process (st : State p.n) (o : Wire p.n) :
    fastPairs p (process p st o) ⊆ fastPairs p st := by
  change fastPairs p (match o.decode with
    | some (.vote s i b) => admitHead p st s i b
    | some (.row _ _ body) => admitRow p st ⟨o.auth, body⟩
    | some (.block s b raw sup rows) => admitBlock p st s b raw sup rows
    | none => st) ⊆ fastPairs p st
  cases o.decode with
  | none => exact List.Subset.refl _
  | some a =>
    cases a <;> dsimp only
    case vote s i b => exact List.Subset.refl _
    case row r i body =>
      rcases admitRow_eq p st ⟨o.auth, body⟩ with h | h <;> rw [h]
      exact List.Subset.refl _
    case block s b raw sup rows =>
      cases hp : parentFG st b with
      | none => rw [admitBlock_refused p st s b raw sup rows (Or.inl hp)]
      | some P =>
        cases ha : blockAccepted p st s b P rows with
        | false => rw [admitBlock_refused p st s b raw sup rows (Or.inr ⟨P, hp, ha⟩)]
        | true =>
          unfold admitBlock
          rw [hp]
          dsimp only
          rw [ha, ite_eq_left rfl, fastPairs_admitRows]
          split
          · exact List.Subset.refl _
          · exact fastPairs_reconcile p _

private def fastSource (st : State p.n) (t : Time) (pair : Slot × Block) : Prop :=
  t = SA.gateTime p.toParams pair.1 ∧
    let pre := clockPre p st t
    GridCO.savedGenuine pre.base pair.1 = none ∧
    ∃ B, SA.confirmationFrom p.toParams (eraseFG pre.fg.F) (actView pre) pair.1 = some B ∧
      (actView pre).obligations.any (fun r => !Block.compatible r.1 B) = false ∧
      Block.Preceq pair.2 B ∧
      SA.releaseThreshold p.toParams ≤ SA.prefixSupport p.toParams (actView pre) pair.1 pair.2

private theorem fastPairs_clock (st : State p.n) (t : Time) (pair : Slot × Block)
    (hm : pair ∈ fastPairs p (clock p st t)) :
    pair ∈ fastPairs p st ∨ fastSource p st t pair := by
  change pair ∈ fastPairs p (if isGateTime p t then
    gateStep p (clockPre p st t) ((t - 6 * p.Δ) / (4 * p.Δ)).toNat
    else clockPre p st t) at hm
  have hpre : fastPairs p (clockPre p st t) = fastPairs p st := by
    unfold fastPairs
    rw [clockPre_fastWrite]
  split at hm
  · rename_i ht
    let s := ((t - 6 * p.Δ) / (4 * p.Δ)).toNat
    let pre := clockPre p st t
    have htime : t = SA.gateTime p.toParams s :=
      beq_iff_eq.mp (Bool.and_eq_true_iff.mp ht).2
    cases hs : GridCO.savedGenuine pre.base s with
    | some saved =>
      rw [gateStep_saved p pre s (by rw [hs]; rfl)] at hm
      change pair ∈ (normalizeS pre).fastWrite.flatMap _ at hm
      rw [normalizeS_fields] at hm
      exact Or.inl (hpre ▸ hm)
    | none =>
      change pair ∈ (gateStep p pre s).fastWrite.flatMap _ at hm
      rw [(gateStep_fresh p pre s hs).2.2, List.flatMap_append, List.mem_append] at hm
      rcases hm with hold | hnew
      · exact Or.inl (hpre ▸ hold)
      · have hm : pair ∈ (fastSet p (eraseFG pre.fg.F) (actView pre) s).map
            (fun B => (s, B)) := by
          simpa only [List.flatMap_cons, List.flatMap_nil, List.append_nil] using hnew
        obtain ⟨X, hX, rfl⟩ := List.mem_map.mp hm
        obtain ⟨B, hc, hp, _, _⟩ := fastSet_prefix p _ _ _ hX
        have hfast : (actView pre).obligations.any (fun r => !Block.compatible r.1 B) = false ∧
            SA.releaseThreshold p.toParams ≤ SA.prefixSupport p.toParams (actView pre) s X := by
          unfold fastSet at hX
          simp only [hc] at hX
          split at hX
          · exact (List.not_mem_nil hX).elim
          · rename_i hg
            exact ⟨Bool.eq_false_iff.mpr hg,
              of_decide_eq_true (Bool.and_eq_true_iff.mp (List.mem_filter.mp hX).2).2⟩
        exact Or.inr ⟨htime, hs, B, hc, hfast.1, hp, hfast.2⟩
  · exact Or.inl (hpre ▸ hm)

private theorem leaseGate_label (s : Slot) :
    ((SA.gateTime p.toParams s - 6 * p.Δ) / (4 * p.Δ)).toNat = s := by
  have he : SA.gateTime p.toParams s - 6 * p.Δ = 4 * p.Δ * (s : Int) := by
    change 4 * p.Δ * (s : Int) + 6 * p.Δ - 6 * p.Δ = _
    ring
  have hDelta : (0 : Int) < p.Δ := p.deltaPos
  rw [he, Int.mul_ediv_cancel_left _ (by omega), Int.toNat_natCast]

private theorem leaseGate_result {j : Nat} {x : V} {s : Slot} {B : Block}
    (ht : rho.events[j]? = some (.tick x (SA.gateTime p.toParams s)))
    (hc : SA.confirmationFrom p.toParams
      (eraseFG (clockPre p (V2.Run.stateBefore E rho j x).st (SA.gateTime p.toParams s)).fg.F)
      (actView (clockPre p (V2.Run.stateBefore E rho j x).st
        (SA.gateTime p.toParams s))) s = some B) :
    gateResultAt p c E rho j = some (some B) := by
  delta gateResultAt
  rw [ht]
  dsimp only
  have htest := (isGateTime_iff p (SA.gateTime p.toParams s)).mpr ⟨s, rfl⟩
  rw [htest, ite_eq_left rfl]
  rw [leaseGate_label p s, hc]

/-- Clause (4). Flattened label/block pairs retain their clock source under
reconcile. T7.6 identifies the scheduled time read with this gate event. -/
theorem fgsa_leaseOrigins_fastWrites (hs : V2.ScheduleWellFormed E rho) (i : Nat) (x : V) :
    ∀ s X, X ∈ (FGSA.fastWriteAt (storeAt p c E rho i x) s).getD [] →
      ∃ j < i, IsGateTick p c rho j x s ∧ gatePassedAt p c E rho j ∧
        ∃ B, gateResultAt p c E rho j = some (some B) ∧
          Block.Preceq X B ∧ fastAt p c E rho x s X := by
  intro s X hX
  have hm : (s, X) ∈ fastPairs p (storeAt p c E rho i x) := by
    unfold FGSA.fastWriteAt at hX
    cases hf : (storeAt p c E rho i x).fastWrite.find? (fun row => row.1 == s) with
    | none =>
      simp only [hf, Option.map_none, Option.getD_none] at hX
      exact (List.not_mem_nil hX).elim
    | some row =>
      have he : row.1 = s := by simpa using List.find?_some hf
      simp only [hf, Option.map_some, Option.getD_some] at hX
      exact List.mem_flatMap.mpr ⟨row, List.mem_of_find?_eq_some hf,
        List.mem_map.mpr ⟨X, hX, by rw [he]⟩⟩
  obtain ⟨j, hj, t, ht, htime, hn, B, hc, hg, hp, hfast⟩ :=
    V2.Engine.clock_field_origin_of_subset (P := fgsa p c)
      (fun nd => fastPairs p nd.st) rfl
      (fun nd o pair h => fastPairs_process p nd.st (toWire p o) h)
      (fun _ _ _ h => h) (fgsa_hrestore_field p c (fastPairs p) rfl)
      (fun nd t pair => fastSource p nd.st t pair)
      (fun nd t pair h => fastPairs_clock p nd.st t pair h) E rho i x (s, X) hm
  change t = SA.gateTime p.toParams s at htime
  subst t
  have hit : IsGateTick p c rho j x s := ht
  have hresult := leaseGate_result p c E rho ht hc
  refine ⟨j, hj, hit, ⟨x, s, hit, hn, B, hc, hg⟩, B, hresult, hp, ?_⟩
  have hread := (gateResultAt_eq_gateResult p c E rho hs hit).symm.trans hresult
  rw [gateResult_def, gateIn_def, preTick_def] at hread
  cases hidx : V2.Run.tickIdx? rho x (SA.gateTime p.toParams s) with
  | none => simp only [hidx, Option.map_none] at hread; cases hread
  | some k =>
    have hk := fgsa_tick_unique E rho hs (V2.Run.tickIdx?_spec hidx) ht
    subst k
    refine ⟨clockPre p (V2.Run.stateBefore E rho j x).st (SA.gateTime p.toParams s), ?_, hfast⟩
    rw [gateIn_def, preTick_def, hidx]
    rfl

/-- Clause (2), including due rows, from the common output bound. -/
theorem fgsa_leaseOrigins_chain (i : Nat) (x : V) :
    Gen.AC.LeaseMapChain (storeAt p c E rho i x).base := by
  rw [Gen.AC.LeaseMapChain_def]
  intro K g d hK B level expiry hB
  exact Gen.Pure.block_compatible_of_common
    (storedTargetsBelowOutput_target p _ (fgsa_storedTargetsBelowOutput p c E rho i x) _ hK)
    (storedTargetsBelowOutput_target p _ (fgsa_storedTargetsBelowOutput p c E rho i x) _ hB)

/-- Clause (3). BASE TRANSPORT lifts the FG-SA ancestor deadline producers. -/
theorem fgsa_leaseOrigins_ancestorDeadlines (i : Nat) (x : V) :
    ∀ K g deadline, (K, g, deadline) ∈ (storeAt p c E rho i x).base.obligations →
      ∀ B, B ≠ .genesis → Block.Preceq B K →
        Gen.AC.ProtectsUntil (storeAt p c E rho i x).base B g deadline := by
  have h := Gen.V2.base_invariant (P := fgsa p c) (fun nd => nd.st)
    (fun a b => (∃ t, b = clock p a t ∧ CStoreInv p a) ∨
      (∃ o, b = process p a o) ∨ ∃ d, b = ((fgsa p c).restore d).st)
    AncestorDeadlines E rho (ancestorDeadlines_init p.n)
    (by
      intro a b ha hab
      rcases hab with ⟨t, rfl, hc⟩ | ⟨o, rfl⟩ | ⟨d, rfl⟩
      · exact ancestorDeadlines_clock p a t hc ha
      · exact ancestorDeadlines_process p a o ha
      · exact ancestorDeadlines_restore d)
    (by
      intro k e he
      right
      cases e with
      | tick v t =>
        left
        refine ⟨t, ?_, cstoreInv_stateBefore E rho k v⟩
        simp only [V2.Event.node, V2.World.step, Function.update_self]
        exact tick_st E rho _ v t
      | deliver v o t =>
        exact Or.inr (Or.inl ⟨toWire p o, by
          simp only [V2.Event.node, V2.World.step, Function.update_self]; rfl⟩)
      | restart v t =>
        exact Or.inr (Or.inr ⟨(fgsa p c).durable (V2.Run.stateBefore E rho k v), by
          simp only [V2.Event.node, V2.World.step, Function.update_self]⟩)) i x
  exact fun K g d hr B hB hBK => h.protectsUntil K g d hr B hB hBK

end AvailableChain.FGSA.Run
end
