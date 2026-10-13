module
public import AvailableChainFGCompose.Statements.HolderClient
public import AvailableChainFGCompose.Proofs.ExecutionObs
public import AvailableChainFGCompose.Proofs.SafetyClient -- shake: keep (Compose import policy)

public section

/-! Ordinary-instance bridges for X1c. These concern client records and releases only;
no driver delivery is identified with ordinary `P.process`. -/

namespace AvailableChain.FGCompose
open AvailableChain.SimplexFG AvailableChain.KitFG
variable {In V : Type} {P : V2.ProtocolSpecD In} [DecidableEq V]
variable {n : Nat} {Wire : Type}
variable (S : FGSafetyReads P n Wire) (Ef : Electorate (Fin n)) (cfg : FGConfig)
variable (E : Generic.Env V) (rho : V2.D.Run V P)

/-- Equality: the ordinary duty state of a tick is its post-clock state. -/
theorem ordinary_obsDutyState_tick {x : V} {j : Nat} {t : Time}
    (he : rho.events[j]? = some (.tick x t)) :
    obsDutyState (ordinaryFGExecutionObs E rho) x j =
      P.clock (V2.D.Run.stateBefore E rho j x) t := by
  have h := (ordinaryFGExecutionObs_laws E rho).tick_entry j x t he
  rw [(ordinaryFGExecutionObs_laws E rho).start_state j _ x he] at h
  exact h

/-- Equality of both client inputs in the ordinary specialization. -/
theorem ordinary_obsSafetyInputAt (x : V) (j : Nat) :
    obsSafetyInputAt S E rho (ordinaryFGExecutionObs E rho) x j =
      safetyInputAt S E rho x j := by
  rw [obsSafetyInputAt_def, safetyInputAt_def]
  cases he : rho.events[j]? with
  | none => rfl
  | some e =>
    cases e with
    | restart y t => rfl
    | deliver y o t => rfl
    | tick y t =>
      dsimp only
      split_ifs with h
      · have hy := h.1
        subst y
        rw [ordinary_obsDutyState_tick E rho he]
      · rfl

/-- Equality of exact self-visible release lists at each ordinary event. -/
theorem ordinary_obsOwnReleased (x : V) (j : Nat) :
    obsOwnReleased (ordinaryFGExecutionObs E rho) x j = V2.D.Engine.ownReleasedAt E rho x j := by
  cases he : rho.events[j]? with
  | none => simp [obsOwnReleased, ordinaryFGExecutionObs, V2.D.Engine.ownReleasedAt_def, he]
  | some e =>
    cases e with
    | restart y t =>
      simp [obsOwnReleased, ordinaryFGExecutionObs, ordinaryReleaseStep,
        V2.D.Engine.ownReleasedAt_def, V2.D.Run.emitsAt, he]
    | deliver y o t =>
      simp [obsOwnReleased, ordinaryFGExecutionObs, ordinaryReleaseStep,
        V2.D.Engine.ownReleasedAt_def, V2.D.Run.emitsAt, he]
    | tick y t =>
      by_cases h : y = x
      · subst y
        simp [obsOwnReleased, ordinaryFGExecutionObs, ordinaryReleaseStep,
          V2.D.Engine.ownReleasedAt_def, V2.D.Run.emitsAt, V2.Event.node, he,
          dependencyReleased, V2.D.tick]
      · simp [obsOwnReleased, ordinaryFGExecutionObs, ordinaryReleaseStep,
          V2.D.Engine.ownReleasedAt_def, V2.Event.node, he, h]

/-- Equality of the ordinary prefix release lists. -/
theorem ordinary_obsOwnReleasedBefore (x : V) (k : Nat) :
    obsOwnReleasedBefore (ordinaryFGExecutionObs E rho) x k =
      V2.D.Engine.ownReleased E rho x 0 k := by
  rw [obsOwnReleasedBefore_def, V2.D.Engine.ownReleased_def]
  simp only [Nat.sub_zero, ← List.range_eq_range']
  congr 1
  funext j
  exact ordinary_obsOwnReleased E rho x j

/-- Iff: the observed no-slash predicate specializes exactly to the frozen predicate. -/
theorem ordinary_obsSafetyNoSlash_iff (x : V) :
    obsSafetyNoSlash S rho (ordinaryFGExecutionObs E rho) x ↔ safetyNoSlash S E rho x := by
  have he (a : Wire) : (∃ t, obsEmits (ordinaryFGExecutionObs E rho) rho x (S.encode a) t) ↔
      safetyEmits S E rho x a := by
    simp only [ordinary_obsEmits_iff, V2.D.Run.emits, safetyEmits]
    exact exists_comm
  simp only [obsSafetyNoSlash, safetyNoSlash, he]

/-- Iff: honest action release retains exactly the old wire and event witnesses. -/
theorem ordinary_obsHonestRowAt_iff (T : FGTiming) (j : Nat) (x : V) (r : Nat) (a : Wire) :
    obsHonestRowAt S rho (ordinaryFGExecutionObs E rho) T j x r a ↔
      HonestRowAt S E rho T j x r a := by
  have hr (he : rho.events[j]? = some (.tick x (T.action r))) :
      (ordinaryFGExecutionObs E rho).released x j = V2.D.Run.emitsAt E rho j := by
    simp only [ordinaryFGExecutionObs, he, Option.map_some, Option.getD_some,
      ordinaryReleaseStep, ite_true, V2.D.Run.emitsAt]
    rfl
  constructor
  · rintro ⟨hx, hj, ha⟩
    exact ⟨hx, hj, hr hj ▸ ha⟩
  · rintro ⟨hx, hj, ha⟩
    exact ⟨hx, hj, (hr hj).symm ▸ ha⟩

/-- Iff: the holder trace specializes to the ordinary record and release trace. -/
theorem ordinary_FGHolderClientTrace_iff (holder : Fin n → V) :
    FGHolderClientTrace S Ef cfg E rho (ordinaryFGExecutionObs E rho) holder ↔
      ∀ i, holder i ∈ rho.honest → ∀ k,
        S.record (V2.D.Run.stateBefore E rho k (holder i)) =
          clientRecordOnce Ef cfg i RecordOnce.initial
            ((List.range k).filterMap (safetyInputAt S E rho (holder i))) ∧
        (V2.D.Engine.ownReleased E rho (holder i) 0 k).filterMap S.decodeObject =
          clientRunOnce Ef cfg i RecordOnce.initial
            ((List.range k).filterMap (safetyInputAt S E rho (holder i))) := by
  simp only [FGHolderClientTrace, ordinary_obsOwnReleasedBefore, ordinary_obsSafetyInputAt]
  rfl

/-- One-way: the current/prior split implies the frozen existential coverage conclusion.
That conclusion forgets whether the release was current or strictly earlier. -/
theorem ordinary_rowPermission_covered (T : FGTiming)
    (entry : Wire → Option (Height × BlockId)) (x : V) (j r : Nat)
    (target : Height × BlockId)
    (h : FGHolderRowCoverage S rho (ordinaryFGExecutionObs E rho) T entry x j r target) :
    ∃ k rSent a, rSent ≤ r ∧ HonestRowAt S E rho T k x rSent a ∧ entry a = some target := by
  rcases h with ⟨a, ha, he⟩ | ⟨k, rSent, a, _, hr, ha, he⟩
  · exact ⟨j, r, a, le_rfl, (ordinary_obsHonestRowAt_iff S E rho T j x r a).1 ha, he⟩
  · exact ⟨k, rSent, a, hr, (ordinary_obsHonestRowAt_iff S E rho T k x rSent a).1 ha, he⟩

private theorem record_entry (J : FGSafetyClientLaws S Ef cfg) (x : V) (j : Nat) :
    S.record (ordinaryEntry E rho x j) = S.record (V2.D.Run.stateBefore E rho j x) := by
  rw [ordinaryEntry_def]
  cases he : rho.events[j]? with
  | none => rfl
  | some e =>
    dsimp only [Option.map, Option.getD]
    cases e with
    | restart y t =>
      dsimp only [ordinaryEntryStep]
      split_ifs <;> simp only [J.restart_record]
    | tick y t =>
      dsimp only [ordinaryEntryStep]
      split_ifs <;> simp only [J.clock_record]
    | deliver y o t =>
      dsimp only [ordinaryEntryStep]
      split_ifs <;> simp only [J.process_record]

private theorem record_prefix (J : FGSafetyClientLaws S Ef cfg) (x : V) (j : Nat) :
    S.record (V2.D.Run.stateBefore E rho (j + 1) x) =
      (V2.D.Engine.ownReleasedAt E rho x j).foldl (safetyRecordStep S)
        (S.record (V2.D.Run.stateBefore E rho j x)) := by
  have h := Gen.V2.Duty.ownRecord_fold_restart S.record (safetyRecordStep S)
    J.clock_record J.process_record J.own_record E rho (Nat.le_succ j) x
    (fun _ t _ _ _ => J.restart_record _ t)
  rw [V2.D.Engine.ownReleased_succ E rho x (le_refl j), V2.D.Engine.ownReleased_self,
    List.nil_append] at h
  exact h

/-- One-way: global ordinary client laws imply run-local holder laws when the caller
explicitly supplies a bijection. This specialization does not restrict the general driver. -/
theorem ordinary_FGHolderClientLaws (J : FGSafetyClientLaws S Ef cfg) (e : Fin n ≃ V)
    (he : ∀ i, rho.seatOf S.fgLabel (S.fgSeats i) = e i) :
    FGHolderClientLaws S Ef cfg E rho (ordinaryFGExecutionObs E rho) e where
  holder_eq := he
  holder_inj := e.injective
  initial_record := J.initial_record
  record_step x k _ := by
    obtain ⟨j, r, hr, rfl⟩ : ∃ j r, r < 3 ∧ k = 3 * j + r :=
      ⟨k / 3, k % 3, by omega, by omega⟩
    have hd1 : (3 * j + 1) / 3 = j := by omega
    have hd2 : (3 * j + 2) / 3 = j := by omega
    have hm2 : (3 * j + 2) % 3 = 2 := by omega
    obtain rfl | rfl | rfl : r = 0 ∨ r = 1 ∨ r = 2 := by omega
    · simpa [ordinaryFGExecutionObs, ordinaryCutState, hd1] using record_entry S Ef cfg E rho J x j
    · have hr := record_prefix S Ef cfg E rho J x j
      rw [← ordinary_obsOwnReleased E rho x j, ← record_entry S Ef cfg E rho J x j] at hr
      simpa [ordinaryFGExecutionObs, ordinaryCutState, obsOwnReleased, Nat.add_assoc,
        hd1, hd2, hm2] using hr
    · simp [ordinaryFGExecutionObs, ordinaryCutState, hd2,
        show 3 * j + 2 + 1 = 3 * (j + 1) by omega]
  holder_rows j x t i ht hi := by
    rw [ordinary_obsOwnReleased]
    rw [V2.D.Engine.ownReleasedAt_def, ht]
    simp only [Option.map_some, V2.Event.node, ite_true]
    rw [(V2.D.Run.step_tick_eq E rho ht).2, J.tick_rows E rho e he]
    have hd := ordinary_obsDutyState_tick E rho ht
    dsimp only [obsDutyState] at hd
    rw [hd, J.clock_record, ← hi, e.symm_apply_apply]
  nonholder_rows j x t ht hn := by
    obtain ⟨i, hi⟩ := e.surjective x
    exact False.elim (hn i hi)

end AvailableChain.FGCompose
end
