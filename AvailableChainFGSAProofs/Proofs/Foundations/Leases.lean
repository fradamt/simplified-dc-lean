module
public import AvailableChainFGSA.Proofs.LeaseOutput

public import AvailableChainFGSARun.Proofs.AncestorDeadlines
public import AvailableChainGeneric.Proofs.V2.Duty.BaseTransport
public import AvailableChainFGSAProofs.Proofs.Shared.Reads

-- ROOT-DIGEST-2: private matcher copy; equality is checked by the kernel (BUILD B3).
namespace AvailableChain.FGSA
open AvailableChain.Generic AvailableChain.SimplexFG

private def hygiene_admitBlock (p : Params) (st : State p.n) (s : Slot)
    (N : NamedProposal p.n) : State p.n :=
  if !namedParentHeld st N then st else
  match parentFG st N.erase with
  | none => st
  | some P =>
      if blockAccepted p st s N P then
        let st1 : State p.n := { st with
          base := GridCO.admitProposal p.toParams.engine st.base
            (baseProposal s N.erase N.raw N.support) N.erase (N.raw.map baseHead)
          fg := Window.on_block p p.K_W st.fg (fgBlock P N.erase N.rows)
          proposals := st.proposals ++ [⟨.proposer s, .proposal N⟩] }
        let st2 := if st1.fg.F = st.fg.F then st1 else reconcile st1
        N.rows.foldl (admitRow p) st2
      else st

private theorem hygiene_admitBlock_eq : @admitBlock = @hygiene_admitBlock := rfl

end AvailableChain.FGSA

public section

namespace AvailableChain.FGSA.Run

variable (p : Params) {In V : Type} [DecidableEq V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
All stored targets, including due rows, are below the current output.
Gen E-10 `invariant_triple` lifts the E-11 store preservation lemmas.
T7.5 supplies `CStoreInv` and `NestOK` through the reachable store bundle. -/
theorem fgsa_storedTargetsBelowOutput (i : Nat) (x : V) :
    StoredTargetsBelowOutput p (storeAt p c E rho i x) := by
  have h := Gen.V2.Duty.invariant_triple (P := fgsa p c)
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
    (fun nd _ => ⟨Reachable.reset nd.st.base.now,
      storedTargetsBelowOutput_initialAt p nd.st.base.now⟩)
    E rho i x
  exact h.2

private def leaseSource (st : State p.n) (t : Time) (row : Block × Nat × Time) : Prop :=
  ∃ s B, t = SA.gateTime p.toParams s ∧
    let pre := clockPre p st t
    GridCO.savedGenuine pre.base s = none ∧
    SA.Root.confirmationFrom p.toParams (eraseFG pre.fg.F) (actView pre) s = some B ∧
    (actView pre).obligations.any (fun r => !Block.compatible r.1 B) = false ∧
    Block.Preceq row.1 B ∧
    (row.1, row.2.1) ∈ @GridCO.gateWriteKeys GridCO.slowLeasePolicy .root p.toParams.engine p.n
      (actView pre) s B ∧ row.2.2 = SA.gateTime p.toParams s + SA.lifetime p.toParams

private theorem leaseRows_admitRows (rows : List (RowWire p.n)) (st : State p.n) :
    (rows.foldl (admitRow p) st).base.obligations = st.base.obligations := by
  induction rows generalizing st with
  | nil => rfl
  | cons a rows ih =>
    rw [List.foldl_cons, ih]
    rcases admitRow_eq p st a with h | h <;> rw [h]

private theorem leaseRows_process (st : State p.n) (o : Wire p.n) :
    (process p st o).base.obligations ⊆ st.base.obligations := by
  change (match o.decode with
    | some (.vote s i b) => admitHead p st s i b
    | some (.row _ body) => admitRow p st ⟨o.auth, body⟩
    | some (.block s N) => admitBlock p st s N
    | none => st).base.obligations ⊆ st.base.obligations
  cases o.decode with
  | none => exact List.Subset.refl _
  | some a =>
    cases a <;> dsimp only
    case vote s i b => rw [admitHead_obligations]
    case row i body =>
      rcases admitRow_eq p st ⟨o.auth, body⟩ with h | h <;> rw [h]
    case block s N =>
      cases hn : namedParentHeld st N with
      | false => rw [admitBlock_refused p st s N (Or.inl hn)]
      | true =>
        cases hp : parentFG st N.erase with
        | none => rw [admitBlock_refused p st s N (Or.inr (Or.inl hp))]
        | some P =>
          cases ha : blockAccepted p st s N P with
          | false =>
            rw [admitBlock_refused p st s N (Or.inr (Or.inr ⟨P, hp, ha⟩))]
          | true =>
            rw [hygiene_admitBlock_eq]
            unfold hygiene_admitBlock
            simp only [hn, Bool.not_true, Bool.false_eq_true, ite_false]
            rw [hp]
            dsimp only
            rw [ha, ite_eq_left rfl, leaseRows_admitRows]
            split
            · dsimp only
              rw [admitProposal_obligations_slow]
            · rw [reconcile_obligations]
              intro row hr
              have hm := (List.mem_filter.mp hr).1
              rwa [admitProposal_obligations_slow] at hm

private theorem leaseRows_clock (st : State p.n) (t : Time) (row : Block × Nat × Time)
    (hm : row ∈ (clock p st t).base.obligations) :
    row ∈ st.base.obligations ∨ leaseSource p st t row := by
  change row ∈ (if isGateTime p t then
    gateStep p (clockPre p st t) ((t - 6 * p.Δ) / (4 * p.Δ)).toNat
    else clockPre p st t).base.obligations at hm
  split at hm
  · rename_i ht
    let s := ((t - 6 * p.Δ) / (4 * p.Δ)).toNat
    let pre := clockPre p st t
    have htime : t = SA.gateTime p.toParams s := by
      exact beq_iff_eq.mp (Bool.and_eq_true_iff.mp ht).2
    cases hs : GridCO.savedGenuine pre.base s with
    | some saved =>
      rw [gateStep_saved p pre s (by rw [hs]; rfl), normalizeS_fields] at hm
      exact Or.inl ((clockPre_obligations_sublist p st t).subset hm)
    | none =>
      have he : (gateStep p pre s).base.obligations =
          (SA.Root.gateFrom p.toParams (eraseFG pre.fg.F) (actView pre) s).obligations := by
        unfold gateStep
        rw [normalizeS_fields]
        simp only [hs, Option.isSome_none, Bool.false_eq_true, ite_false]
        rfl
      rw [he] at hm
      cases hc : SA.Root.confirmationFrom p.toParams (eraseFG pre.fg.F) (actView pre) s with
      | none =>
        unfold SA.Root.gateFrom GridCO.gateFrom at hm
        rw [show GridCO.confirmationFrom p.toParams.engine
          (eraseFG pre.fg.F) (actView pre) s = none from hc] at hm
        exact Or.inl ((clockPre_obligations_sublist p st t).subset hm)
      | some B =>
        cases hg : (actView pre).obligations.any (fun r => !Block.compatible r.1 B) with
        | true =>
          unfold SA.Root.gateFrom GridCO.gateFrom at hm
          rw [show GridCO.confirmationFrom p.toParams.engine
            (eraseFG pre.fg.F) (actView pre) s = some B from hc] at hm
          dsimp only at hm
          rw [hg, ite_eq_left rfl] at hm
          exact Or.inl ((clockPre_obligations_sublist p st t).subset hm)
        | false =>
          have he := @gateFrom_eq_writeKeys_fgsa p.toParams p.n
            (eraseFG pre.fg.F) (actView pre) s B hc hg
          change SA.Root.gateFrom p.toParams (eraseFG pre.fg.F) (actView pre) s = _ at he
          rw [he] at hm
          rcases writeKeys_row_cases _ _ _ row hm with hold | ⟨hk, hd⟩
          · exact Or.inl ((clockPre_obligations_sublist p st t).subset hold)
          · have hkey := hk
            obtain ⟨A, hA, hmap⟩ := List.mem_flatMap.mp hk
            obtain ⟨g, _, heq⟩ := List.mem_map.mp hmap
            have hAB : A = row.1 := congrArg Prod.fst heq
            have hpre := (Bool.and_eq_true_iff.mp (List.mem_filter.mp hA).2).2
            rw [hAB] at hpre
            exact Or.inr ⟨s, B, htime, hs, hc, hg, hpre, hkey, hd⟩
  · exact Or.inl ((clockPre_obligations_sublist p st t).subset hm)

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
    | some (.row _ body) => admitRow p st ⟨o.auth, body⟩
    | some (.block s N) => admitBlock p st s N
    | none => st) ⊆ fastPairs p st
  cases o.decode with
  | none => exact List.Subset.refl _
  | some a =>
    cases a <;> dsimp only
    case vote s i b => exact List.Subset.refl _
    case row i body =>
      rcases admitRow_eq p st ⟨o.auth, body⟩ with h | h <;> rw [h]
      exact List.Subset.refl _
    case block s N =>
      cases hn : namedParentHeld st N with
      | false => rw [admitBlock_refused p st s N (Or.inl hn)]
      | true =>
        cases hp : parentFG st N.erase with
        | none => rw [admitBlock_refused p st s N (Or.inr (Or.inl hp))]
        | some P =>
          cases ha : blockAccepted p st s N P with
          | false => rw [admitBlock_refused p st s N (Or.inr (Or.inr ⟨P, hp, ha⟩))]
          | true =>
            rw [hygiene_admitBlock_eq]
            unfold hygiene_admitBlock
            simp only [hn, Bool.not_true, Bool.false_eq_true, ite_false]
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
    ∃ B, SA.Root.confirmationFrom p.toParams (eraseFG pre.fg.F) (actView pre) pair.1 = some B ∧
      (actView pre).obligations.any (fun r => !Block.compatible r.1 B) = false ∧
      Block.Preceq pair.2 B ∧
      SA.releaseThreshold p.toParams ≤ SA.Root.prefixSupport p.toParams (actView pre) pair.1 pair.2

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
            SA.releaseThreshold p.toParams ≤ SA.Root.prefixSupport p.toParams (actView pre) s X
                := by
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
    (hc : SA.Root.confirmationFrom p.toParams
      (eraseFG (clockPre p (V2.D.Run.stateBefore E rho j x).st (SA.gateTime p.toParams s)).fg.F)
      (actView (clockPre p (V2.D.Run.stateBefore E rho j x).st
        (SA.gateTime p.toParams s))) s = some B) :
    gateResultAt p c E rho j = some (some B) := by
  delta gateResultAt
  rw [ht]
  dsimp only
  have htest := (isGateTime_iff p (SA.gateTime p.toParams s)).mpr ⟨s, rfl⟩
  rw [htest, ite_eq_left rfl]
  rw [leaseGate_label p s, hc]

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
IF.1 deadline source. The same exact row has an actual passed gate write
at label `s`; its deadline is `d_s + L = q_(s+k)`. KitV2 handles deletion
and restore, so no NoRestart premise is needed. -/
theorem fgsa_leaseOrigins_writeLabel
    (i : Nat) (x : V) (row : Block × Nat × Time)
    (hr : row ∈ (storeAt p c E rho i x).base.obligations) :
    ∃ j < i, ∃ s B, IsGateTick p c rho j x s ∧ gatePassedAt p c E rho j ∧
      gateResultAt p c E rho j = some (some B) ∧ Block.Preceq row.1 B ∧
      (row.1, row.2.1) ∈ @GridCO.gateWriteKeys GridCO.slowLeasePolicy .root p.toParams.engine p.n
        (actView (clockPre p (storeAt p c E rho j x) (SA.gateTime p.toParams s))) s B ∧
      row.2.2 = SA.gateTime p.toParams s + SA.lifetime p.toParams ∧
      row.2.2 = SA.releaseTime p.toParams (s + p.k) := by
  obtain ⟨j, hj, t, ht, s, B, htime, hn, hc, hg, hp, hkey, hd⟩ :=
    V2.D.Engine.clock_field_origin_of_subset (P := fgsa p c)
      (fun nd => nd.st.base.obligations) rfl
      (fun nd o a ha => leaseRows_process p nd.st (toWire p o) ha)
      (fun _ _ _ h => h)
        (fgsa_hrestore_field_retained p c (fun st => st.base.obligations) (fun _ => rfl))
      (fun nd t row => leaseSource p nd.st t row)
      (fun nd t row hm => leaseRows_clock p nd.st t row hm) E rho i x row hr
  subst t
  have hit : IsGateTick p c rho j x s := ht
  have hpassed : gatePassedAt p c E rho j := ⟨x, s, hit, hn, B, hc, hg⟩
  have hresult := leaseGate_result p c E rho ht hc
  refine ⟨j, hj, s, B, hit, hpassed, hresult, hp, hkey, hd, ?_⟩
  rw [hd]
  change 4 * p.Δ * (s : Int) + 6 * p.Δ + (4 * (p.k : Int) - 1) * p.Δ =
    4 * p.Δ * ((s + p.k : Nat) : Int) + 5 * p.Δ
  push_cast
  ring

private theorem leaseGate_written (hs : V2.D.ScheduleWellFormed E rho)
    {j : Nat} {x : V} {s : Slot} {K B : Block} {g : Nat}
    (ht : IsGateTick p c rho j x s)
    (hn : GridCO.savedGenuine (clockPre p (storeAt p c E rho j x)
      (SA.gateTime p.toParams s)).base s = none)
    (hc : SA.Root.confirmationFrom p.toParams
      (eraseFG (clockPre p (storeAt p c E rho j x) (SA.gateTime p.toParams s)).fg.F)
      (actView (clockPre p (storeAt p c E rho j x) (SA.gateTime p.toParams s))) s = some B)
    (hg : (actView (clockPre p (storeAt p c E rho j x) (SA.gateTime p.toParams s))).obligations.any
      (fun r => !Block.compatible r.1 B) = false)
    (hkey : (K, g) ∈ @GridCO.gateWriteKeys GridCO.slowLeasePolicy .root p.toParams.engine p.n
      (actView (clockPre p (storeAt p c E rho j x) (SA.gateTime p.toParams s))) s B) :
    (K, g, SA.gateTime p.toParams s + SA.lifetime p.toParams) ∈
      (clock p (storeAt p c E rho j x) (SA.gateTime p.toParams s)).base.obligations := by
  let pre := clockPre p (storeAt p c E rho j x) (SA.gateTime p.toParams s)
  have hbound : DeadlinesAtMost (actView pre)
      (SA.gateTime p.toParams s + SA.lifetime p.toParams) := by
    rw [DeadlinesAtMost_def]
    intro K g d hr
    let row := (K, g, d)
    have hold := (clockPre_obligations_sublist p (storeAt p c E rho j x) _).subset hr
    obtain ⟨k, hk, w, C, htk, _, _, _, _, hd, _⟩ :=
      fgsa_leaseOrigins_writeLabel p c E rho j x row hold
    have htime := fgsa_tick_time_strict E rho hs htk ht hk
    change row.2.2 ≤ SA.gateTime p.toParams s + SA.lifetime p.toParams
    rw [hd]
    exact add_le_add (le_of_lt htime) le_rfl
  have he := @gateFrom_eq_writeKeys_fgsa p.toParams p.n
    (eraseFG pre.fg.F) (actView pre) s B hc hg
  change SA.Root.gateFrom p.toParams (eraseFG pre.fg.F) (actView pre) s = _ at he
  have hm : (K, g, SA.gateTime p.toParams s + SA.lifetime p.toParams) ∈
      (SA.Root.gateFrom p.toParams (eraseFG pre.fg.F) (actView pre) s).obligations := by
    rw [he]
    exact writeKeys_mem_of_key_fgsa _ _ K g _
      ((DeadlinesAtMost_def _ _).2 fun b g d h =>
        (DeadlinesAtMost_def _ _).1 hbound b g d h) hkey
  have htime := (isGateTime_iff p (SA.gateTime p.toParams s)).mpr ⟨s, rfl⟩
  change _ ∈ (if isGateTime p (SA.gateTime p.toParams s) then
    gateStep p pre ((SA.gateTime p.toParams s - 6 * p.Δ) / (4 * p.Δ)).toNat
    else pre).base.obligations
  rw [htime, ite_eq_left rfl, leaseGate_label p s]
  change GridCO.savedGenuine pre.base s = none at hn
  unfold gateStep
  rw [normalizeS_fields]
  simp only [hn, Option.isSome_none, Bool.false_eq_true, ite_false]
  exact hm

private theorem leaseRows_lowerBound (hs : V2.D.ScheduleWellFormed E rho)
    {j i : Nat} {x : V} {s : Slot} (ht : IsGateTick p c rho j x s) (hji : j < i)
    (K : Block) (g : Nat) (limit : Time)
    (hlimit : limit = SA.gateTime p.toParams s + SA.lifetime p.toParams)
    (hwrite : (K, g, limit) ∈
      (clock p (storeAt p c E rho j x) (SA.gateTime p.toParams s)).base.obligations) :
    ∀ row ∈ (storeAt p c E rho i x).base.obligations, row.1 = K → limit ≤ row.2.2 := by
  let Q := fun nd : Node p => ∀ row ∈ nd.st.base.obligations, row.1 = K → limit ≤ row.2.2
  have hinit : Q (V2.D.Run.stateBefore E rho (j + 1) x) := by
    rw [V2.D.Run.stateBefore_succ E rho ht]
    simp only [V2.D.World.step, Function.update_self]
    intro row hr hK
    rw [tick_st (c := c) E rho (V2.D.Run.stateBefore E rho j x) x (SA.gateTime p.toParams s)] at hr
    have hinv := (storeBundle_postClock E rho j x (SA.gateTime p.toParams s)).cstore.leaseKeys.1
    have he : row = (K, g, limit) := List.inj_on_of_nodup_map hinv hr hwrite hK
    rw [he]
  have h := V2.D.Engine.stateBefore_step_induction E rho Q (show j + 1 ≤ i by omega) x ?_ hinit
  · exact h
  intro k e hjk hki he hv hQ
  cases e with
  | restart y t =>
    change y = x at hv
    subst y
    simp only [V2.D.World.step, Function.update_self]
    intro row hr
    exact (List.not_mem_nil hr).elim
  | deliver y o t =>
    change y = x at hv
    subst y
    simp only [V2.D.World.step, Function.update_self]
    intro row hr hK
    exact hQ row (leaseRows_process p _ (toWire p o) hr) hK
  | tick y t =>
    change y = x at hv
    subst y
    simp only [V2.D.World.step, Function.update_self]
    intro row hr hK
    rw [tick_st (c := c) E rho (V2.D.Run.stateBefore E rho k x) x t] at hr
    rcases leaseRows_clock p _ t row hr with hold | ⟨w, C, htime, _, _, _, _, _, hd⟩
    · exact hQ row hold hK
    · have htime' := fgsa_tick_time_strict E rho hs ht he (by omega)
      rw [hlimit, hd]
      rw [htime] at htime'
      exact add_le_add (le_of_lt htime') le_rfl

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
IF.1: the deadline source is the last actual write of this key before
this read. A later passed gate cannot write the same block and level. -/
theorem fgsa_leaseOrigins_lastWrite (hs : V2.D.ScheduleWellFormed E rho)
    (i : Nat) (x : V) (row : Block × Nat × Time)
    (hr : row ∈ (storeAt p c E rho i x).base.obligations) :
    ∃ j < i, ∃ s B, IsGateTick p c rho j x s ∧ gatePassedAt p c E rho j ∧
      gateResultAt p c E rho j = some (some B) ∧ Block.Preceq row.1 B ∧
      (row.1, row.2.1) ∈ @GridCO.gateWriteKeys GridCO.slowLeasePolicy .root p.toParams.engine p.n
        (actView (clockPre p (storeAt p c E rho j x) (SA.gateTime p.toParams s))) s B ∧
      row.2.2 = SA.gateTime p.toParams s + SA.lifetime p.toParams ∧
      row.2.2 = SA.releaseTime p.toParams (s + p.k) ∧
      ∀ k w C, j < k → k < i → IsGateTick p c rho k x w →
        let pre := clockPre p (storeAt p c E rho k x) (SA.gateTime p.toParams w)
        GridCO.savedGenuine pre.base w = none →
        SA.Root.confirmationFrom p.toParams (eraseFG pre.fg.F) (actView pre) w = some C →
        (actView pre).obligations.any (fun r => !Block.compatible r.1 C) = false →
        (row.1, row.2.1) ∉ @GridCO.gateWriteKeys GridCO.slowLeasePolicy .root p.toParams.engine p.n
          (actView pre) w C := by
  obtain ⟨j, hj, s, B, ht, hp, hc, hB, hkey, hd, hq⟩ :=
    fgsa_leaseOrigins_writeLabel p c E rho i x row hr
  refine ⟨j, hj, s, B, ht, hp, hc, hB, hkey, hd, hq, ?_⟩
  intro k w C hjk hki htk
  dsimp only
  intro hn hconf hg hkey'
  have hw := leaseGate_written p c E rho hs htk hn hconf hg hkey'
  have hl := leaseRows_lowerBound p c E rho hs htk hki row.1 row.2.1 _ rfl hw row hr rfl
  have htime := fgsa_tick_time_strict E rho hs ht htk hjk
  rw [hd] at hl
  exact (not_le_of_gt (add_lt_add_of_lt_of_le htime le_rfl)) hl

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Clause (1): every obligation row, including a due row, has a passed gate origin. -/
theorem fgsa_leaseOrigins_origins (i : Nat) (x : V) :
    ∀ row ∈ (storeAt p c E rho i x).base.obligations, ∃ j < i, ∃ s B,
      IsGateTick p c rho j x s ∧ gatePassedAt p c E rho j ∧
      gateResultAt p c E rho j = some (some B) ∧ Block.Preceq row.1 B := by
  intro row hr
  obtain ⟨j, hj, s, B, ht, hg, hc, hp, _⟩ := fgsa_leaseOrigins_writeLabel p c E rho i x row hr
  exact ⟨j, hj, s, B, ht, hg, hc, hp⟩

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Clause (4). Flattened label/block pairs retain their clock source under
reconcile. T7.6 identifies the scheduled time read with this gate event. -/
theorem fgsa_leaseOrigins_fastWrites (hs : V2.D.ScheduleWellFormed E rho) (i : Nat) (x : V) :
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
    V2.D.Engine.clock_field_origin_of_subset (P := fgsa p c)
      (fun nd => fastPairs p nd.st) rfl
      (fun nd o pair h => fastPairs_process p nd.st (toWire p o) h)
      (fun _ _ _ h => h) (fgsa_hrestore_field_retained p c (fastPairs p) (fun _ => rfl))
      (fun nd t pair => fastSource p nd.st t pair)
      (fun nd t pair h => fastPairs_clock p nd.st t pair h) E rho i x (s, X) hm
  change t = SA.gateTime p.toParams s at htime
  subst t
  have hit : IsGateTick p c rho j x s := ht
  have hresult := leaseGate_result p c E rho ht hc
  refine ⟨j, hj, hit, ⟨x, s, hit, hn, B, hc, hg⟩, B, hresult, hp, ?_⟩
  have hread := (gateResultAt_eq_gateResult p c E rho hs hit).symm.trans hresult
  rw [gateResult_def, gateIn_def, preTick_def] at hread
  cases hidx : V2.D.Run.tickIdx? rho x (SA.gateTime p.toParams s) with
  | none => simp only [hidx, Option.map_none] at hread; cases hread
  | some k =>
    have hk := fgsa_tick_unique E rho hs (V2.D.Run.tickIdx?_spec hidx) ht
    subst k
    refine ⟨clockPre p (V2.D.Run.stateBefore E rho j x).st (SA.gateTime p.toParams s), ?_, hfast⟩
    rw [gateIn_def, preTick_def, hidx]
    rfl

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Clause (2), including due rows, from the common output bound. -/
theorem fgsa_leaseOrigins_chain (i : Nat) (x : V) :
    Gen.AC.Root.LeaseMapChain (storeAt p c E rho i x).base := by
  rw [Gen.AC.Root.LeaseMapChain_def]
  intro K g d hK B level expiry hB
  exact Gen.Pure.block_compatible_of_common
    (storedTargetsBelowOutput_target p _ (fgsa_storedTargetsBelowOutput p c E rho i x) _ hK)
    (storedTargetsBelowOutput_target p _ (fgsa_storedTargetsBelowOutput p c E rho i x) _ hB)

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Clause (3). BASE TRANSPORT lifts the FG-SA ancestor deadline producers. -/
theorem fgsa_leaseOrigins_ancestorDeadlines (i : Nat) (x : V) :
    ∀ K g deadline, (K, g, deadline) ∈ (storeAt p c E rho i x).base.obligations →
      ∀ B, B ≠ .genesis → Block.Preceq B K →
        Gen.AC.Root.ProtectsUntil (storeAt p c E rho i x).base B g deadline := by
  have h := Gen.V2.Duty.base_invariant (P := fgsa p c) (fun nd => nd.st)
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
        simp only [V2.Event.node, V2.D.World.step, Function.update_self]
        exact tick_st E rho _ v t
      | deliver v o t =>
        exact Or.inr (Or.inl ⟨toWire p o, by
          simp only [V2.Event.node, V2.D.World.step, Function.update_self]; rfl⟩)
      | restart v t =>
        exact Or.inr (Or.inr ⟨(fgsa p c).durable (V2.D.Run.stateBefore E rho k v), by
          simp only [V2.Event.node, V2.D.World.step, Function.update_self]⟩)) i x
  exact fun K g d hr B hB hBK => h.protectsUntil K g d hr B hB hBK

end AvailableChain.FGSA.Run
end
