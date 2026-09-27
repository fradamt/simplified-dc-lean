module
public import AvailableChainGridCO.Proofs.Handling

@[expose] public section

namespace AvailableChain.GridCO

-- Keep one shared proof interface for both lease policies.
set_option linter.unusedSectionVars false

variable [LeasePolicy]

open AvailableChain.Generic AvailableChain.Statements.Generic

/-- Delivery through the early cutoff suffices for an honest batch. Its
confirmation gate can occur later, including after an outage starts. -/
structure EarlyDelivery {V : Type} [DecidableEq V]
    (p : Params) (E : Env V) (rho : Run V (gridCO p)) (r : Slot) : Prop where
  execution : ExecutionValid (gridCO p) E rho
  horizon : earlyTime p r ≤ rho.horizon
  delivery :
    (E.t_GST ≤ proposalTime p r ∧ PartialSynchrony (gridCO p) E rho ∧
      AcceptedObjectRelay (gridCO p) E rho) ∨
    ∃ cut, earlyTime p r ≤ cut ∧ HealthyPrefixDelivery (gridCO p) E rho cut ∧
      HealthyAcceptedObjectRelay (gridCO p) E rho cut

/-- A complete synchronous label supplies its early delivery window. -/
theorem EarlyDelivery.of_synchronous {V : Type} [DecidableEq V] [Fintype V]
    {p : Params} {E : Env V} {rho : Run V (gridCO p)} {r : Slot}
    (h : SynchronousLabel p E rho r) : EarlyDelivery p E rho r := by
  have he : earlyTime p r ≤ gateTime p r := by
    dsimp [earlyTime, gateTime]; linarith [p.deltaPos]
  refine ⟨h.1, he.trans h.2.2.1, ?_⟩
  rcases h.2.2.2 with hp | ⟨cut, hc, hd, hr⟩
  · exact Or.inl hp
  · exact Or.inr ⟨cut, he.trans hc, hd, hr⟩

/-- The outage contract supplies early delivery for a pending healthy
batch even when its gate is after the healthy cutoff. -/
theorem EarlyDelivery.of_outage {V : Type} [DecidableEq V] [Fintype V]
    {p : Params} {E : Env V} {rho : Run V (gridCO p)}
    (G T b₀ b₁ : Time)
    (h : OutageRegime (gridCO p) E (gridInterface p) (gridConstants p G) rho T b₀ b₁)
    (r : Slot) (he : earlyTime p r ≤ b₀) : EarlyDelivery p E rho r :=
  ⟨h.execution, he.trans (h.interval.2.2.1.trans h.interval.2.2.2),
    Or.inr ⟨b₀, he, h.healthy, h.acceptedRelay⟩⟩

private theorem key_time_le {V O : Type} (e f : Event V O)
    (h : e.key ≤ f.key) : e.time ≤ f.time := by
  rcases Prod.Lex.toLex_le_toLex.mp h with h | ⟨h, _⟩
  · exact le_of_lt h
  · exact le_of_eq h

/-- A stored clock value is zero or comes from an earlier local tick. -/
theorem stateBefore_now_source {V : Type} [DecidableEq V] (p : Params)
    (rho : Run V (gridCO p)) (i : Nat) (v : V) :
    (Run.stateBefore (gridCO p) rho i v).now = 0 ∨
      ∃ j < i, rho.events[j]? =
        some (.tick v (Run.stateBefore (gridCO p) rho i v).now) := by
  induction i with
  | zero => exact Or.inl rfl
  | succ i ih =>
      cases hi : rho.events[i]? with
      | none =>
          have he : Run.stateBefore (gridCO p) rho (i + 1) =
              Run.stateBefore (gridCO p) rho i := by
            simp [Run.stateBefore, List.take_add_one, hi]
          rw [he]
          exact ih.imp_right (fun ⟨j, hj, he⟩ => ⟨j, by omega, he⟩)
      | some e =>
          rw [stateBefore_succ_event hi]
          cases e with
          | tick u t =>
              by_cases hv : v = u
              · subst u
                simp only [World.step, Function.update_self]
                right
                exact ⟨i, by omega, by simpa [gridCO, clock_now] using hi⟩
              · simp only [World.step, Function.update_of_ne hv]
                exact ih.imp_right (fun ⟨j, hj, he⟩ => ⟨j, by omega, he⟩)
          | deliver u o t =>
              by_cases hv : v = u
              · subst u
                simp only [World.step, Function.update_self]
                simp only [gridCO, process_now]
                exact ih.imp_right (fun ⟨j, hj, he⟩ => ⟨j, by omega, he⟩)
              · simp only [World.step, Function.update_of_ne hv]
                exact ih.imp_right (fun ⟨j, hj, he⟩ => ⟨j, by omega, he⟩)

/-- No reader's clock can exceed the next event time. -/
theorem stateBefore_now_le_event {V : Type} [DecidableEq V] (p : Params)
    (E : Env V) (rho : Run V (gridCO p)) (hs : ScheduleWellFormed E rho)
    {i : Nat} {e : Event V (gridCO p).Object}
    (hi : rho.events[i]? = some e) (v : V) :
    (Run.stateBefore (gridCO p) rho i v).now ≤ e.time := by
  rcases stateBefore_now_source p rho i v with hz | ⟨j, hj, ht⟩
  · rw [hz]
    exact (hs.in_horizon e (List.mem_of_getElem? hi)).1
  · obtain ⟨hil, hie⟩ := List.getElem?_eq_some_iff.mp hi
    obtain ⟨hjl, hje⟩ := List.getElem?_eq_some_iff.mp ht
    have hk := (List.pairwise_iff_getElem.mp hs.sorted) j i hjl hil hj
    rw [hje, hie] at hk
    exact key_time_le _ _ hk

/-- Local clock values increase along a valid event list. -/
theorem stateBefore_now_mono {V : Type} [DecidableEq V] (p : Params)
    (E : Env V) (rho : Run V (gridCO p)) (hs : ScheduleWellFormed E rho)
    {i j : Nat} (hij : i ≤ j) (v : V) :
    (Run.stateBefore (gridCO p) rho i v).now ≤
      (Run.stateBefore (gridCO p) rho j v).now := by
  induction j with
  | zero => simp [Nat.le_zero.mp hij]
  | succ j ih =>
      rcases Nat.eq_or_lt_of_le hij with he | hlt
      · subst i; exact le_refl _
      · apply le_trans (ih (by omega))
        cases hj : rho.events[j]? with
        | none => simp [Run.stateBefore, List.take_add_one, hj]
        | some e =>
            rw [stateBefore_succ_event hj]
            cases e with
            | tick u t =>
                by_cases hv : v = u
                · subst u
                  simpa [World.step, gridCO, clock_now] using
                    stateBefore_now_le_event p E rho hs hj v
                · simp [World.step, hv]
            | deliver u o t =>
                by_cases hv : v = u
                · subst u; simp [World.step, gridCO, process_now]
                · simp [World.step, hv]

/-- A local tick at or before a delivery precedes that delivery in the list.
This includes equal times, because ticks have the earlier event phase. -/
theorem tick_index_lt_delivery {V : Type} (p : Params)
    (E : Env V) (rho : Run V (gridCO p)) (hs : ScheduleWellFormed E rho)
    {i j : Nat} {v w : V} {o : Wire p.n} {a t : Time}
    (hi : rho.events[i]? = some (.tick v a))
    (hj : rho.events[j]? = some (.deliver w o t)) (hat : a ≤ t) : i < j := by
  obtain ⟨hil, hie⟩ := List.getElem?_eq_some_iff.mp hi
  obtain ⟨hjl, hje⟩ := List.getElem?_eq_some_iff.mp hj
  by_contra hn
  rcases Nat.lt_or_ge j i with hji | hij
  · have hk := (List.pairwise_iff_getElem.mp hs.sorted) j i hjl hil hji
    rw [hje, hie] at hk
    have hbad : t < a := by
      simpa [Event.key, Event.time, Event.phase, Prod.Lex.toLex_le_toLex] using hk
    exact (not_lt.mpr hat) hbad
  · have he : i = j := by omega
    subst j
    simp [hi] at hj

/-- A delivery after a required local public tick has a clock at least
that tick time, including for a sleeping reader. -/
theorem delivery_now_ge_public {V : Type} [DecidableEq V] (p : Params)
    (E : Env V) (rho : Run V (gridCO p)) (hs : ScheduleWellFormed E rho)
    {i : Nat} {v : V} {o : Wire p.n} {a t : Time}
    (hi : rho.events[i]? = some (.deliver v o t))
    (ha : PublicTime E a) (ha0 : 0 ≤ a) (hat : a ≤ t) :
    a ≤ (Run.stateBefore (gridCO p) rho i v).now := by
  have hm := List.mem_of_getElem? hi
  have hv := hs.honest_only _ hm
  have ht := (hs.in_horizon _ hm).2
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp
    (hs.tick_total v hv a ha ha0 (hat.trans ht))
  have hji := tick_index_lt_delivery p E rho hs hj hi hat
  have hb := stateBefore_now_mono p E rho hs (Nat.succ_le_of_lt hji) v
  rw [stateBefore_succ_event hj] at hb
  simpa [World.step, gridCO, clock_now] using hb

/-- Between the HEAD and its early cutoff, the receiver's clock names
exactly the HEAD label. -/
theorem head_delivery_current_label {V : Type} [DecidableEq V] (p : Params)
    (E : Env V) (rho : Run V (gridCO p)) (hs : ScheduleWellFormed E rho)
    (hΔ : E.Δ = p.Δ) {index : Nat} {reader : V} {parent : Wire p.n}
    {r : Slot} {t : Time}
    (hi : rho.events[index]? = some (.deliver reader parent t))
    (hlo : voteTime p r ≤ t) (hhi : t < earlyTime p r) :
    ((Run.stateBefore (gridCO p) rho index reader).now / (4 * p.Δ)).toNat = r := by
  have hpub : PublicTime E (voteTime p r) := by
    refine ⟨4 * r + 1, ?_⟩
    simp only [voteTime, proposalTime, hΔ, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
      Nat.cast_one]
    ring
  have hnonneg : 0 ≤ voteTime p r := by
    unfold voteTime proposalTime
    exact add_nonneg (mul_nonneg (by linarith [p.deltaPos]) (Int.natCast_nonneg r))
      (le_of_lt p.deltaPos)
  have hl := delivery_now_ge_public p E rho hs hi hpub hnonneg hlo
  have hh := (stateBefore_now_le_event p E rho hs hi reader).trans_lt hhi
  have hd : 0 < 4 * p.Δ := by linarith [p.deltaPos]
  have hdiv : (Run.stateBefore (gridCO p) rho index reader).now / (4 * p.Δ) = (r : Int) := by
    apply (Int.ediv_eq_iff_of_pos hd).mpr
    constructor
    · dsimp [voteTime, proposalTime] at hl
      nlinarith [p.deltaPos]
    · dsimp [earlyTime, proposalTime] at hh
      nlinarith [p.deltaPos]
  rw [hdiv]
  simp

/-- An honest HEAD handled before the early cutoff is stored. The valid
schedule supplies the admission window; no clock premise is added. -/
theorem early_handled_honest_head_stored {V : Type} [DecidableEq V]
    (p : Params) (E : Env V) (rho : Run V (gridCO p))
    (hx : ExecutionValid (gridCO p) E rho) (hΔ : E.Δ = p.Δ)
    (index : Nat) (reader : V) (r : Slot) (i : Fin p.n) (B : Block) (t : Time)
    (hh : rho.seatOf r i ∈ rho.honest)
    (hlo : voteTime p r ≤ t) (hhi : t < earlyTime p r)
    (hhandle : Run.handlesAt (gridCO p) rho index reader ⟨.seat r i, .head B⟩ t) :
    (⟨.seat r i, .head B⟩ : Wire p.n) ∈
      (Run.stateBefore (gridCO p) rho (index + 1) reader).votes := by
  obtain ⟨parent, hp, hcarr⟩ := hhandle
  have hc := head_delivery_current_label p E rho hx.toScheduleWellFormed hΔ hp hlo hhi
  exact handled_honest_head_stored p E rho hx index reader r i B t hh
    (by rw [hc]; omega) (by rw [hc]) ⟨parent, hp, hcarr⟩

/-- The broadcast part of a synchronous label gives an honest HEAD call
before its early cutoff, in both the healthy-prefix and post-GST cases. -/
theorem synchronous_head_handled_early {V : Type} [DecidableEq V]
    (p : Params) (E : Env V) (rho : Run V (gridCO p)) (hΔ : E.Δ = p.Δ)
    (r : Slot) (hsync : EarlyDelivery p E rho r)
    (source reader : V) (hs : source ∈ rho.honest) (hr : reader ∈ rho.honest)
    (o : Wire p.n) (he : Run.emits (gridCO p) E rho source o (voteTime p r)) :
    ∃ index t, voteTime p r ≤ t ∧ t < earlyTime p r ∧
      Run.handlesAt (gridCO p) rho index reader o t := by
  have hdeadline : voteTime p r + E.Δ = earlyTime p r := by
    simp only [voteTime, earlyTime, hΔ]
    ring
  rcases hsync.delivery with ⟨hgst, hnet, _⟩ | ⟨cut, hcut, hnet, _⟩
  · have hg : E.t_GST ≤ voteTime p r := by
      dsimp [voteTime]
      linarith [p.deltaPos]
    have hmax : max (voteTime p r) E.t_GST = voteTime p r := max_eq_left hg
    obtain ⟨t, ht, hd, index, hh⟩ := hnet.broadcast source hs o _ he reader hr
      (by rw [hmax, hdeadline]; exact hsync.horizon) rfl
    exact ⟨index, t, ht, by simpa [hmax, hdeadline] using hd, hh⟩
  · obtain ⟨t, ht, hd, index, hh⟩ := hnet.broadcast source hs o _ he reader hr
      (by rw [hdeadline]; exact hcut) rfl
    exact ⟨index, t, ht, by simpa [hdeadline] using hd, hh⟩

/-- A synchronous honest HEAD is stored before the early cutoff at every
honest reader. Target-path receipt is a separate obligation. -/
theorem synchronous_honest_head_stored_early
    {V : Type} [DecidableEq V]
    (p : Params) (E : Env V) (rho : Run V (gridCO p)) (hΔ : E.Δ = p.Δ)
    (r : Slot) (hsync : EarlyDelivery p E rho r)
    (i : Fin p.n) (B : Block) (hh : rho.seatOf r i ∈ rho.honest)
    (he : Run.emits (gridCO p) E rho (rho.seatOf r i)
      ⟨.seat r i, .head B⟩ (voteTime p r))
    (reader : V) (hr : reader ∈ rho.honest) :
    ∃ index t, voteTime p r ≤ t ∧ t < earlyTime p r ∧
      Run.handlesAt (gridCO p) rho index reader ⟨.seat r i, .head B⟩ t ∧
      (⟨.seat r i, .head B⟩ : Wire p.n) ∈
        (Run.stateBefore (gridCO p) rho (index + 1) reader).votes := by
  obtain ⟨index, t, hlo, hhi, hhandle⟩ :=
    synchronous_head_handled_early p E rho hΔ r hsync (rho.seatOf r i) reader hh hr _ he
  exact ⟨index, t, hlo, hhi, hhandle,
    early_handled_honest_head_stored p E rho hsync.execution hΔ index reader r i B t
      hh hlo hhi hhandle⟩

end AvailableChain.GridCO
end
