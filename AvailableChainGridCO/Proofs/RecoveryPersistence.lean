module
public import AvailableChainGridCO.Proofs.RecoverySupport

@[expose] public section

namespace AvailableChain.GridCO

set_option linter.unusedSectionVars false
variable [LeasePolicy]

open AvailableChain.Generic AvailableChain.Statements.Generic

/-- After an event boundary, an exact row is either retained from that
boundary or written by a later genuine gate. -/
theorem run_row_origin_since {V : Type} [DecidableEq V] (p : Params)
    (E : Env V) (rho : Run V (gridCO p)) (hs : ScheduleWellFormed E rho)
    (start finish : Nat) (hle : start ≤ finish) (reader : V)
    (B : Block) (g : Nat) (d : Time)
    (hm : (B, g, d) ∈ (Run.stateBefore (gridCO p) rho finish reader).obligations) :
    (B, g, d) ∈ (Run.stateBefore (gridCO p) rho start reader).obligations ∨
      ∃ j, start ≤ j ∧ j < finish ∧ ∃ s C,
        rho.events[j]? = some (.tick reader (gateTime p s)) ∧
        confirmation p (gateInput p rho s reader) s = some C ∧ Block.Preceq B C := by
  induction finish with
  | zero => simpa only [Nat.le_zero.mp hle] using Or.inl hm
  | succ finish ih =>
      by_cases he : start = finish + 1
      · subst start; exact Or.inl hm
      have hsf : start ≤ finish := by omega
      have old (hold : (B, g, d) ∈ (Run.stateBefore (gridCO p) rho finish reader).obligations) :
          (B, g, d) ∈ (Run.stateBefore (gridCO p) rho start reader).obligations ∨
            ∃ j, start ≤ j ∧ j < finish + 1 ∧ ∃ s C,
              rho.events[j]? = some (.tick reader (gateTime p s)) ∧
              confirmation p (gateInput p rho s reader) s = some C ∧ Block.Preceq B C := by
        rcases ih hsf hold with h | ⟨j, hj, hlt, rest⟩
        · exact Or.inl h
        · exact Or.inr ⟨j, hj, by omega, rest⟩
      cases hi : rho.events[finish]? with
      | none => exact old (by simpa [Run.stateBefore, List.take_add_one, hi] using hm)
      | some e =>
          rw [stateBefore_succ_event hi] at hm
          cases e with
          | tick v t =>
              by_cases hv : reader = v
              · subst v
                have hrow : (B, g, d) ∈
                    (clock p (Run.stateBefore (gridCO p) rho finish reader) t).obligations := by
                  simpa [World.step] using hm
                rcases clock_row_admitted_origin p _ t (run_receiptStamped p rho finish reader)
                    B g d hrow with hold | ⟨s, C, ht, hc, hp, _⟩
                · exact old hold
                · subst t
                  rw [stateBefore_tick_eq_stateBeforeTime hs hi] at hc
                  exact Or.inr ⟨finish, hsf, by omega, s, C, hi, hc, hp⟩
              · exact old (by simpa [World.step, hv] using hm)
          | deliver v o t =>
              apply old
              by_cases hv : reader = v
              · subst v; simpa [World.step, gridCO, process_obligations] using hm
              · simpa [World.step, hv] using hm

/-- A later HEAD row was already present after the initial release or
comes from a gate at or after that release's label. This includes the
initial label's pending gate, which runs after the release. -/
theorem nextHeadState_row_origin_since {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (gridCO p)) (hΔ : E.Δ = p.Δ)
    (r t : Slot) (hrt : r < t) (hsync : SynchronousLabel p E rho r)
    (reader : V) (hr : reader ∈ rho.honest) (B : Block) (g : Nat) (d : Time)
    (hm : (B, g, d) ∈ (nextHeadState p rho t reader).obligations) :
    (B, g, d) ∈ (nextHeadState p rho r reader).obligations ∨
      ∃ s C, r ≤ s ∧ s < t ∧
        confirmation p (gateInput p rho s reader) s = some C ∧ Block.Preceq B C := by
  have hs := hsync.1.toScheduleWellFormed
  have hpub : PublicTime E (releaseTime p r) := by
    refine ⟨4 * r + 5, ?_⟩
    simp only [releaseTime, proposalTime, hΔ, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    ring
  have hz : 0 ≤ releaseTime p r := by
    dsimp [releaseTime, proposalTime]
    nlinarith [p.deltaPos, Int.natCast_nonneg r]
  have hh : releaseTime p r ≤ rho.horizon := by
    have := hsync.2.2.1
    dsimp [releaseTime, gateTime] at *; linarith [p.deltaPos]
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp (hsync.1.tick_total reader hr _ hpub hz hh)
  have hiState : Run.stateBefore (gridCO p) rho (i + 1) reader = nextHeadState p rho r reader := by
    rw [stateBefore_succ_event hi]
    simp only [World.step, Function.update_self]
    change clock p _ _ = clock p _ _
    rw [stateBefore_tick_eq_stateBeforeTime hs hi]
    rfl
  have hrow := (List.mem_filter.mp
    (nextHeadState_row_survives_release p rho t reader B g d hm).1).1
  change (B, g, d) ∈ (Run.stateBeforeTime (gridCO p) rho (releaseTime p t) reader).obligations
    at hrow
  rw [time_input_eq_event_prefix p E rho hs] at hrow
  have htime : releaseTime p r < releaseTime p t := by
    have hc : (r : Time) < t := by exact_mod_cast hrt
    dsimp [releaseTime, proposalTime]; nlinarith [p.deltaPos]
  have hil := (index_lt_read_length_iff hs (releaseTime p t - 1) hi).mpr
    (Int.le_sub_one_iff.mpr htime)
  rcases run_row_origin_since p E rho hs (i + 1) _ (by omega) reader B g d hrow
      with hold | ⟨j, hj, hjt, s, C, hjget, hc, hp⟩
  · exact Or.inl (hiState ▸ hold)
  · have hbefore : gateTime p s < releaseTime p t :=
      Int.le_sub_one_iff.mp ((index_lt_read_length_iff hs _ hjget).mp hjt)
    have hafter : releaseTime p r ≤ gateTime p s := by
      obtain ⟨hiL, hiE⟩ := List.getElem?_eq_some_iff.mp hi
      obtain ⟨hjL, hjE⟩ := List.getElem?_eq_some_iff.mp hjget
      have hk := (List.pairwise_iff_getElem.mp hs.sorted) i j hiL hjL (by omega)
      rw [hiE, hjE] at hk
      have hx : releaseTime p r < gateTime p s ∨ releaseTime p r = gateTime p s := by
        simpa [Event.key, Event.time, Event.phase, Prod.Lex.toLex_le_toLex] using hk
      exact hx.elim le_of_lt le_of_eq
    refine Or.inr ⟨s, C, ?_, ?_, hc, hp⟩
    · by_contra hn
      have hle := (gateTime_le_iff p (s + 1) r).mpr (Nat.succ_le_of_lt (Nat.lt_of_not_ge hn))
      dsimp [gateTime, releaseTime, proposalTime] at hafter hle
      nlinarith [p.deltaPos]
    · by_contra hn
      have hle := (gateTime_le_iff p t s).mpr (Nat.le_of_not_gt hn)
      dsimp [gateTime, releaseTime] at hbefore hle
      linarith [p.deltaPos]

/-- Prefixes of compatible blocks are compatible. -/
theorem compatible_prefixes (A B C D : Block)
    (hAB : Block.Preceq A B) (hCD : Block.Preceq C D) (hBD : Block.Compatible B D) :
    Block.Compatible A C := by
  rcases Bool.or_eq_true_iff.mp hBD with h | h
  · exact ancestors_compatible A C D (prefix_trans A B D hAB h) hCD
  · exact ancestors_compatible A C B hAB (prefix_trans C D B hCD h)

/-- All honest would-be HEADs after release r cover B. Sleeping readers
are included, so changing the awake set does not change this property. -/
def HeadCovers {V : Type} [DecidableEq V] (p : Params)
    (rho : Run V (gridCO p)) (r : Slot) (B : Block) : Prop :=
  ∀ reader ∈ rho.honest, Block.Preceq B (nextHead p (nextHeadState p rho r reader) r)

/-- Every row left by release is compatible with B, including rows that
do not currently supply the deepest live root. -/
def ReleasedRowsCompatible {V : Type} [DecidableEq V] (p : Params)
    (rho : Run V (gridCO p)) (r : Slot) (B : Block) : Prop :=
  ∀ reader ∈ rho.honest, ∀ K g d,
    (K, g, d) ∈ (nextHeadState p rho r reader).obligations → Block.Compatible K B

/-- Once a genuine prefix transfers with compatible rows, it stays
covered by every later complete synchronous HEAD. Same-label safety
controls the initial pending gate. Later gates use the honest batch.
Expiry, release, and renewal cannot add another source of conflict. -/
theorem permanent_support_of_release {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (gridCO p)) (hΔ : E.Δ = p.Δ)
    (r : Slot) (hsync : SynchronousLabel p E rho r)
    (hseq : ∀ t, r ≤ t → gateTime p t ≤ rho.horizon → SynchronousLabel p E rho t)
    (source : V) (hs : source ∈ rho.honest) (B C : Block)
    (hc : confirmation p (gateInput p rho r source) r = some C) (hp : Block.Preceq B C)
    (hrows : ReleasedRowsCompatible p rho r B) (hheads : HeadCovers p rho r B) :
    ∀ t, r ≤ t → gateTime p t ≤ rho.horizon →
      ReleasedRowsCompatible p rho t B ∧ HeadCovers p rho t B ∧
      (r < t → ∀ reader ∈ rho.honest, ∃ D,
        confirmation p (gateInput p rho t reader) t = some D ∧ Block.Preceq B D) := by
  intro t
  induction t using Nat.strong_induction_on with
  | h t ih =>
      intro hrt hhor
      by_cases he : t = r
      · subst t
        exact ⟨hrows, hheads, by intro h; exact (Nat.lt_irrefl r h).elim⟩
      have hlt : r < t := lt_of_le_of_ne hrt (Ne.symm he)
      obtain ⟨u, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_zero_of_lt hlt : t ≠ 0)
      have hprev := ih u (Nat.lt_succ_self u) (Nat.le_of_lt_succ hlt)
        (((gateTime_le_iff p u (u + 1)).mpr (Nat.le_succ u)).trans hhor)
      have hnow := hseq (u + 1) hrt hhor
      have hresults : ∀ reader ∈ rho.honest, ∃ D,
          confirmation p (gateInput p rho (u + 1) reader) (u + 1) = some D ∧
          Block.Preceq B D := by
        intro reader hr
        obtain ⟨D, hD, hBD, _⟩ := preserve_from_engine p E rho hΔ u
          hnow hnow.2.1 B hprev.2.1 reader hr
        exact ⟨D, hD, hBD⟩
      have hnewrows : ReleasedRowsCompatible p rho (u + 1) B := by
        intro reader hr K g d hm
        rcases nextHeadState_row_origin_since p E rho hΔ r (u + 1) hlt hsync
            reader hr K g d hm with hold | ⟨s, D, hrs, hst, hD, hKD⟩
        · exact hrows reader hr K g d hold
        · by_cases heq : s = r
          · subst s
            exact compatible_prefixes K D B C hKD hp
              (sameLabel_from_engine p E rho hΔ r hsync reader hr source hs
                D C hD hc)
          · have hpast := ih s hst hrs
              (((gateTime_le_iff p s (u + 1)).mpr (Nat.le_of_lt hst)).trans hhor)
            obtain ⟨D', hD', hBD⟩ := hpast.2.2 (lt_of_le_of_ne hrs (Ne.symm heq)) reader hr
            have heq : D' = D := Option.some.inj (hD'.symm.trans hD)
            subst D'
            exact ancestors_compatible K B D hKD hBD
      refine ⟨hnewrows, ?_, fun _ => hresults⟩
      obtain ⟨D, hD, hBD⟩ := hresults source hs
      apply transfer_from_engine p E rho hΔ (u + 1) hnow
        source hs B D hD hBD
      intro reader hr K hK
      obtain ⟨⟨target, g, d⟩, hm, heq⟩ := List.mem_filterMap.mp hK
      dsimp only at heq
      split at heq
      · have heq' : target = K := Option.some.inj heq
        subst target
        exact hnewrows reader hr K g d hm
      · contradiction

end AvailableChain.GridCO
end
