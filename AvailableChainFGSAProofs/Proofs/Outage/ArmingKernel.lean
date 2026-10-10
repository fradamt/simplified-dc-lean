module
public import AvailableChainFGSAProofs.Proofs.Outage.ArmingPending
public import AvailableChainFGSAProofs.Proofs.Outage.ArmingReceipt
public import AvailableChainGeneric.Proofs.V2.Duty.Sleep
public import AvailableChainGeneric.Proofs.V2.Duty.DeliveryBy
public import AvailableChainFGSARun.Proofs.Interface

public section

/-! P-Ar sleep kernel. Each window and epoch belongs to one protected receiver.
The slow window starts at t(q0). The fast window starts at t(j).
Receipt services are local inputs until the Clean joint induction supplies them. -/

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

omit [DecidableEq V] in
/-- The approved fast guard gives awake on the whole receiver window. -/
theorem arming_fast_awake {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}
    {x : V} {j : Slot} (hG : fastCoveredSchedule p E rho x j) :
    AwakeClosed E x (slotStartZ p (j : Int)) (SA.gateTime p.toParams j) := by
  classical
  intro t ht hstart hgate
  by_contra hn
  have hfalse : E.awake x t = false := Bool.eq_false_iff.mpr hn
  obtain ⟨w, htw, hwg, hw⟩ := V2.D.Engine.wake_between hgate hfalse hG.1
  have hbound := hG.2.1 w (lt_of_le_of_lt ht htw) hwg hw
  have heq : slotStartZ p (((j + 1 : Nat) : Int) - 1) = slotStartZ p (j : Int) := by
    congr 1
    dsimp [Time] at *
    omega
  rw [heq] at hbound
  exact (not_lt.mpr hbound) (hstart.trans_lt htw)

omit [DecidableEq V] in
/-- The approved fast guard also excludes every restart after t(j), through g(j). -/
theorem arming_fast_restart_free {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}
    {x : V} {j : Slot} (hG : fastCoveredSchedule p E rho x j) :
    RestartFreeTime rho x (slotStartZ p (j : Int)) (SA.gateTime p.toParams j) := by
  classical
  intro w hstart hgate he
  have h0 : 0 ≤ slotStartZ p (j : Int) := by
    unfold slotStartZ
    have hd := p.deltaPos
    positivity
  have hw := hG.2.2 w (h0.trans hstart.le) hgate he
  have heq : slotStartZ p (((j + 1 : Nat) : Int) - 1) = slotStartZ p (j : Int) := by
    congr 1
    dsimp [Time] at *
    omega
  rw [heq] at hw
  exact (not_lt.mpr hw) hstart

omit [DecidableEq V] in
/-- Exact awake and restart-free windows at each protected receiver. -/
theorem arming_receiver_window {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}
    {fast : Bool} {b₀ : Time} {x : V}
    (hx : x ∈ coveredNodes p E rho fast b₀) {q : Slot}
    (hq : (if fast then q = coverLabel p b₀
      else (coverLabel p b₀ : Int) - (p.k : Int) + 1 ≤ (q : Int) ∧ q ≤ coverLabel p b₀)) :
    x ∈ rho.honest ∧
    AwakeClosed E x (slotStartZ p (q : Int)) (SA.gateTime p.toParams (coverLabel p b₀)) ∧
    RestartFreeTime rho x (slotStartZ p (q : Int))
      (SA.gateTime p.toParams (coverLabel p b₀)) := by
  classical
  classical
  change x ∈ rho.honest.filter _ at hx
  obtain ⟨hxH, hG⟩ := Finset.mem_filter.mp hx
  cases fast with
  | true =>
    change fastCoveredSchedule p E rho x (coverLabel p b₀) at hG
    change q = coverLabel p b₀ at hq
    subst q
    exact ⟨hxH, arming_fast_awake hG, arming_fast_restart_free hG⟩
  | false =>
    change slowCoveredSchedule p E rho x (coverLabel p b₀) at hG
    change _ ∧ _ at hq
    have hstart : slotStartZ p ((coverLabel p b₀ : Int) - (p.k : Int) + 1) ≤
        slotStartZ p (q : Int) := by
      unfold slotStartZ
      exact mul_le_mul_of_nonneg_left hq.1 (by have hd := p.deltaPos; positivity)
    exact ⟨hxH, fun t ht ha hb => hG.2.1 t ht (hstart.trans ha) hb,
      fun w ha hb he => hG.2.2 w (hstart.trans_lt ha) hb he⟩

omit [DecidableEq V] in
/-- A protected receiver is awake at both the early read and gate of each scoped label. -/
theorem arming_receiver_times {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}
    {fast : Bool} {b₀ : Time} {x : V}
    (hx : x ∈ coveredNodes p E rho fast b₀) {q : Slot}
    (hq : (if fast then q = coverLabel p b₀
      else (coverLabel p b₀ : Int) - (p.k : Int) + 1 ≤ (q : Int) ∧ q ≤ coverLabel p b₀)) :
    E.awake x (SA.earlyTime p.toParams q) = true ∧
    E.awake x (SA.gateTime p.toParams q) = true := by
  classical
  obtain ⟨_, hA, _⟩ := arming_receiver_window hx hq
  have hqj : q ≤ coverLabel p b₀ := by
    cases fast <;> simp_all
  have hd := p.deltaPos
  have ht0 : 0 ≤ slotStartZ p (q : Int) := by unfold slotStartZ; positivity
  have hte : slotStartZ p (q : Int) ≤ SA.earlyTime p.toParams q := by
    change 4 * p.Δ * (q : Int) ≤ 4 * p.Δ * (q : Int) + 2 * p.Δ
    dsimp [Time] at *
    omega
  have htg : slotStartZ p (q : Int) ≤ SA.gateTime p.toParams q := by
    change 4 * p.Δ * (q : Int) ≤ 4 * p.Δ * (q : Int) + 6 * p.Δ
    dsimp [Time] at *
    omega
  have heg : SA.earlyTime p.toParams q ≤ SA.gateTime p.toParams q := by
    rw [arming_early_eq, arming_gate_eq]
    dsimp [Time] at *
    omega
  have hgj := (arming_gate_le_iff p q _).mpr hqj
  exact ⟨hA _ (ht0.trans hte) hte (heg.trans hgj), hA _ (ht0.trans htg) htg hgj⟩

omit [DecidableEq V] in
/-- Saved rows use the receiver epoch from t(q0), after phase-zero restarts. -/
theorem arming_receiver_start_epoch {E : Generic.Env V}
    {rho : V2.D.Run V (fgsa p c)} (hs : V2.D.ScheduleWellFormed E rho)
    {fast : Bool} {b₀ : Time} {x : V} (hx : x ∈ coveredNodes p E rho fast b₀) {q : Slot}
    (hq : (if fast then q = coverLabel p b₀
      else (coverLabel p b₀ : Int) - (p.k : Int) + 1 ≤ (q : Int) ∧ q ≤ coverLabel p b₀)) :
    V2.D.restartFree rho x (V2.D.Run.actionCut rho (slotStartZ p (q : Int)))
      (V2.D.Run.idxBefore rho (SA.gateTime p.toParams (coverLabel p b₀))) := by
  classical
  obtain ⟨_, _, hR⟩ := arming_receiver_window hx hq
  have hqj : q ≤ coverLabel p b₀ := by cases fast <;> simp_all
  have hd := p.deltaPos
  have hstart : slotStartZ p (q : Int) < SA.gateTime p.toParams q := by
    change 4 * p.Δ * (q : Int) < 4 * p.Δ * (q : Int) + 6 * p.Δ
    dsimp [Time] at *
    omega
  apply Gen.V2.Duty.restartFree_actionCut_idxBefore hs
    (hstart.trans_le ((arming_gate_le_iff p q _).mpr hqj))
  intro k w he hw hg
  exact hR w hw hg.le (List.mem_of_getElem? he)

omit [DecidableEq V] in
/-- The time window gives the exact event-index epoch for a fresh batch. -/
theorem arming_receiver_epoch {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}
    (hs : V2.D.ScheduleWellFormed E rho) {fast : Bool} {b₀ : Time} {x : V}
    (hx : x ∈ coveredNodes p E rho fast b₀) {q : Slot}
    (hq : (if fast then q = coverLabel p b₀
      else (coverLabel p b₀ : Int) - (p.k : Int) + 1 ≤ (q : Int) ∧ q ≤ coverLabel p b₀)) :
    V2.D.restartFree rho x (V2.D.Run.actionCut rho (SA.voteTime p.toParams q))
      (V2.D.Run.idxBefore rho (SA.gateTime p.toParams (coverLabel p b₀))) := by
  classical
  obtain ⟨_, _, hR⟩ := arming_receiver_window hx hq
  have hqj : q ≤ coverLabel p b₀ := by cases fast <;> simp_all
  have hd := p.deltaPos
  have htv : slotStartZ p (q : Int) < SA.voteTime p.toParams q := by
    change 4 * p.Δ * (q : Int) < 4 * p.Δ * (q : Int) + p.Δ
    dsimp [Time] at *
    omega
  have hvg : SA.voteTime p.toParams q < SA.gateTime p.toParams q := by
    rw [arming_vote_eq, arming_gate_eq]
    dsimp [Time] at *
    omega
  apply Gen.V2.Duty.restartFree_actionCut_idxBefore hs
    (hvg.trans_le ((arming_gate_le_iff p q _).mpr hqj))
  intro k w he hv hg
  exact hR w (htv.trans hv) hg.le (List.mem_of_getElem? he)

/-- Each protected gate is enabled, including a wake exactly at t(q0). -/
theorem arming_receiver_enabled {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}
    (hs : V2.D.ScheduleWellFormed E rho) {fast : Bool} {b₀ : Time} {x : V}
    (hx : x ∈ coveredNodes p E rho fast b₀) {q : Slot}
    (hq : (if fast then q = coverLabel p b₀
      else (coverLabel p b₀ : Int) - (p.k : Int) + 1 ≤ (q : Int) ∧ q ≤ coverLabel p b₀)) {i : Nat}
    (hi : IsGateTick p c rho i x q) : enabledGateAt p c E rho i x q := by
  obtain ⟨_, _, hR⟩ := arming_receiver_window hx hq
  have hqj : q ≤ coverLabel p b₀ := by cases fast <;> simp_all
  have hbound := fgsa_restartTime_bound E rho i x (slotStartZ p (q : Int)) (by
    intro k w hki he
    obtain ⟨hkl, hke⟩ := List.getElem?_eq_some_iff.mp he
    obtain ⟨hil, hie⟩ := List.getElem?_eq_some_iff.mp hi
    have hk := List.pairwise_iff_getElem.mp hs.sorted k i hkl hil hki
    rw [hke, hie] at hk
    have htime : w ≤ SA.gateTime p.toParams q := V2.D.Engine.time_le_of_key_le _ _ hk
    by_contra hn
    exact hR w (lt_of_not_ge hn)
      (htime.trans ((arming_gate_le_iff p q _).mpr hqj)) (List.mem_of_getElem? he))
  refine ⟨hi, ?_⟩
  cases hr : (storeAt p c E rho i x).restartTime with
  | none => trivial
  | some w => exact hbound w hr

omit [DecidableEq V] in
/-- The actual gate tick remains in this receiver's epoch, including equal-time phases. -/
theorem arming_receiver_gate_epoch {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}
    (hs : V2.D.ScheduleWellFormed E rho) {fast : Bool} {b₀ : Time} {x : V}
    (hx : x ∈ coveredNodes p E rho fast b₀) {q : Slot}
    (hq : (if fast then q = coverLabel p b₀
      else (coverLabel p b₀ : Int) - (p.k : Int) + 1 ≤ (q : Int) ∧ q ≤ coverLabel p b₀))
    {i : Nat} (hi : IsGateTick p c rho i x q) :
    V2.D.restartFree rho x (V2.D.Run.actionCut rho (slotStartZ p (q : Int))) i := by
  obtain ⟨_, _, hR⟩ := arming_receiver_window hx hq
  have hqj : q ≤ coverLabel p b₀ := by cases fast <;> simp_all
  intro k w hak hki he
  have hnot := (V2.D.Engine.index_lt_actionCut_iff hs he (slotStartZ p (q : Int))).not.mp
    (Nat.not_lt.mpr hak)
  have hw : slotStartZ p (q : Int) < w := by
    apply lt_of_not_ge
    intro hle
    rcases lt_or_eq_of_le hle with hlt | heq
    · exact hnot (Or.inl hlt)
    · exact hnot (Or.inr ⟨heq, rfl⟩)
  obtain ⟨hkl, hke⟩ := List.getElem?_eq_some_iff.mp he
  obtain ⟨hil, hie⟩ := List.getElem?_eq_some_iff.mp hi
  have hk := List.pairwise_iff_getElem.mp hs.sorted k i hkl hil hki
  rw [hke, hie] at hk
  have htime : w ≤ SA.gateTime p.toParams q := V2.D.Engine.time_le_of_key_le _ _ hk
  exact hR w hw (htime.trans ((arming_gate_le_iff p q _).mpr hqj))
    (List.mem_of_getElem? he)

/-- The strict read equals the actual tick store when its equal-time receiver epoch survives. -/
theorem arming_tick_store_on {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}
    (hs : V2.D.ScheduleWellFormed E rho) {i : Nat} {x : V} {t : Time}
    (hi : rho.events[i]? = some (.tick x t))
    (hEpoch : V2.D.restartFree rho x (V2.D.Run.idxBefore rho t) i) :
    storeAt p c E rho i x = storeAt p c E rho (V2.D.Run.idxBefore rho t) x := by
  have hidx : V2.D.Run.idxBefore rho t ≤ i := by
    by_contra hn
    exact (lt_irrefl t) ((Gen.V2.Duty.index_lt_idxBefore_iff hs hi t).mp
      (Nat.lt_of_not_ge hn))
  apply congrArg Node.st
  apply V2.D.Run.stateBefore_eq_of_node_ne E rho hidx
  intro k e hstart hki he hnode
  have hnot := (Gen.V2.Duty.index_lt_idxBefore_iff hs he t).not.mp
    (Nat.not_lt.mpr hstart)
  obtain ⟨hkl, hke⟩ := List.getElem?_eq_some_iff.mp he
  obtain ⟨hil, hie⟩ := List.getElem?_eq_some_iff.mp hi
  have hk := List.pairwise_iff_getElem.mp hs.sorted k i hkl hil hki
  rw [hke, hie] at hk
  have ht : e.time = t := le_antisymm (V2.D.Engine.time_le_of_key_le _ _ hk)
    (le_of_not_gt hnot)
  cases e with
  | restart y w =>
    change y = x at hnode
    subst y
    exact hEpoch k w hstart hki he
  | tick y u =>
    change y = x at hnode
    change u = t at ht
    subst y
    subst u
    have hEq : k = i := fgsa_tick_unique E rho hs he hi
    omega
  | deliver y o u =>
    change u = t at ht
    subst u
    simp [V2.Event.key, V2.Event.time, V2.Event.phase, Prod.Lex.toLex_le_toLex] at hk

/-- The healthy non-row law is the sleep prefix's a + Δ service law. -/
theorem arming_nonrow_delivery [Fintype V] {E : Generic.Env V}
    {rho : V2.D.Run V (fgsa p c)} {fast : Bool} {T b₀ b₁ ΔF : Time}
    (h : OutageSleep₂ p c fast E rho T b₀ b₁ ΔF) :
    Gen.V2.Duty.DeliveryWithinOn E rho (fun o => ¬ isRowObject o)
      (fun a => a + p.Δ) b₀ := by
  have hp := h.sleepPre.toHealthyPrefix₂
  have hd := Gen.V2.Duty.deliveryWithinOn_of_healthyPrefixBy E rho b₀
    hp.healthy (fun o => ¬ isRowObject o) E.Δ (fgsaDelay_nonrow E.Δ ΔF)
  rwa [hp.base.delta] at hd

/-- A protected receiver supplies readiness for an honest emitted fresh HEAD. -/
theorem arming_head_ready {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}
    {fast : Bool} {b₀ : Time} {x y : V} (hx : x ∈ coveredNodes p E rho fast b₀)
    {s : Slot} (hs : (if fast then s = coverLabel p b₀
      else (coverLabel p b₀ : Int) - (p.k : Int) + 1 ≤ (s : Int) ∧ s ≤ coverLabel p b₀))
    {o : Obj p} (hy : y ∈ rho.honest)
    (he : V2.D.Run.emits E rho y o (SA.voteTime p.toParams s)) :
    Gen.V2.Duty.ReadyTrigger E rho o (SA.voteTime p.toParams s) x
      (SA.voteTime p.toParams s) (SA.voteTime p.toParams s + p.Δ) := by
  obtain ⟨_, hA, _⟩ := arming_receiver_window hx hs
  have hsj : s ≤ coverLabel p b₀ := by cases fast <;> simp_all
  have hd := p.deltaPos
  refine ⟨y, hy, Or.inl he, ?_⟩
  intro t hv ht
  apply hA t
  · rw [arming_vote_eq] at hv
    have hn : (0 : Time) ≤ 4 * p.Δ * (s : Int) := by positivity
    dsimp [Time] at *
    omega
  · change 4 * p.Δ * (s : Int) ≤ t
    rw [arming_vote_eq] at hv
    dsimp [Time] at *
    omega
  · have heg : SA.earlyTime p.toParams s ≤ SA.gateTime p.toParams s := by
      rw [arming_early_eq, arming_gate_eq]
      dsimp [Time] at *
      omega
    rw [arming_vote_add] at ht
    exact ht.le.trans (heg.trans ((arming_gate_le_iff p s _).mpr hsj))

/-- Transport, readiness and epoch come from the regime and protected receiver.
Handler acceptance and exclusion remain local proof obligations. -/
theorem arming_fresh_head_service [Fintype V] {E : Generic.Env V}
    {rho : V2.D.Run V (fgsa p c)} {fast : Bool} {T b₀ b₁ ΔF : Time}
    (h : OutageSleep₂ p c fast E rho T b₀ b₁ ΔF)
    {x y : V} (hx : x ∈ coveredNodes p E rho fast b₀) {s : Slot}
    (hs : (if fast then s = coverLabel p b₀
      else (coverLabel p b₀ : Int) - (p.k : Int) + 1 ≤ (s : Int) ∧ s ≤ coverLabel p b₀))
    (hcut : SA.earlyTime p.toParams s ≤ b₀) {q : Fin p.n} {b : BlockId}
    (hy : y ∈ rho.honest)
    (he : V2.D.Run.emits E rho y (ofHead p ⟨.seat (.head s) q, b⟩)
      (SA.voteTime p.toParams s))
    (hhandlers : ∀ j t, SA.voteTime p.toParams s ≤ t → t < SA.earlyTime p.toParams s →
      V2.D.Run.handlesAt E rho j x (ofHead p ⟨.seat (.head s) q, b⟩) t →
      (fgsa p c).wellFormed (ofHead p ⟨.seat (.head s) q, b⟩) = true ∧
      (fgsa p c).depsPresent (V2.D.Run.stateBefore E rho j x)
        (ofHead p ⟨.seat (.head s) q, b⟩) = true ∧
      fgsaTimely p (V2.D.Run.stateBefore E rho j x) (ofHead p ⟨.seat (.head s) q, b⟩))
    (hnx : (fgsa p c).excludes (V2.D.Run.stateBeforeTime E rho
      (SA.earlyTime p.toParams s) x) (ofHead p ⟨.seat (.head s) q, b⟩) = false) :
    Nonempty (FreshHeadService E rho s q b (SA.earlyTime p.toParams s) x) := by
  have hp := h.sleepPre.toHealthyPrefix₂
  have hsj : s ≤ coverLabel p b₀ := by cases fast <;> simp_all
  have heg : SA.earlyTime p.toParams s ≤ SA.gateTime p.toParams (coverLabel p b₀) := by
    apply le_trans _ ((arming_gate_le_iff p s _).mpr hsj)
    rw [arming_early_eq, arming_gate_eq]
    have hd := p.deltaPos
    dsimp [Time] at *
    omega
  refine ⟨{
    dl := fun a => a + p.Δ
    cut := b₀
    within := arming_nonrow_delivery h
    ready := arming_head_ready hx hs hy he
    later := lt_add_of_pos_right _ p.deltaPos
    cut_le := by rw [arming_vote_add]; exact hcut
    horizon := by rw [arming_vote_add]; exact hcut.trans hp.cut.2
    freeze_le := (arming_vote_add p s).le
    epoch := (arming_receiver_epoch hp.base.valid.toScheduleWellFormed hx hs).mono
      le_rfl (fgsa_idxBefore_mono rho heg)
    handlers := by simpa only [arming_vote_add] using hhandlers
    not_excluded := by simpa only [arming_vote_add] using hnx }⟩

/-- A proposal service uses the healthy prefix and this receiver's current epoch.
Safe replay history, dependencies, timely handling and exclusion need local proofs. -/
theorem arming_proposal_service [Fintype V] {E : Generic.Env V}
    {rho : V2.D.Run V (fgsa p c)} {fast : Bool} {T b₀ b₁ ΔF : Time}
    (h : OutageSleep₂ p c fast E rho T b₀ b₁ ΔF)
    {x y : V} (hx : x ∈ coveredNodes p E rho fast b₀) {s : Slot}
    (hs : (if fast then s = coverLabel p b₀
      else (coverLabel p b₀ : Int) - (p.k : Int) + 1 ≤ (s : Int) ∧ s ≤ coverLabel p b₀))
    (hcut : SA.earlyTime p.toParams s ≤ b₀) {q : Slot} {N : NamedProposal p.n}
    {send a : Time} (hy : y ∈ rho.honest)
    (he : V2.D.Run.emits E rho y (ofWire p ⟨.proposer q, .proposal N⟩) send)
    (hsa : send ≤ a) (hstart : slotStartZ p (s : Int) ≤ a)
    (hav : a ≤ SA.voteTime p.toParams s)
    (hhistory : Gen.V2.Duty.HistorySafeAt E rho x
      (ofWire p ⟨.proposer q, .proposal N⟩) a)
    (hhandlers : ∀ j t, a ≤ t → t < a + p.Δ → V2.D.Run.handlesAt E rho j x
      (ofWire p ⟨.proposer q, .proposal N⟩) t →
      (fgsa p c).wellFormed (ofWire p ⟨.proposer q, .proposal N⟩) = true ∧
      (fgsa p c).depsPresent (V2.D.Run.stateBefore E rho j x)
        (ofWire p ⟨.proposer q, .proposal N⟩) = true ∧
      fgsaTimely p (V2.D.Run.stateBefore E rho j x) (ofWire p ⟨.proposer q, .proposal N⟩))
    (hnx : (fgsa p c).excludes (V2.D.Run.stateBeforeTime E rho (a + p.Δ) x)
      (ofWire p ⟨.proposer q, .proposal N⟩) = false) :
    Nonempty (ReceiverService E rho (ofWire p ⟨.proposer q, .proposal N⟩)
      send (SA.earlyTime p.toParams s) x) := by
  have hp := h.sleepPre.toHealthyPrefix₂
  obtain ⟨_, hA, hR⟩ := arming_receiver_window hx hs
  have hsj : s ≤ coverLabel p b₀ := by cases fast <;> simp_all
  have hdeadline : a + p.Δ ≤ SA.earlyTime p.toParams s := by
    rw [← arming_vote_add]
    exact add_le_add hav le_rfl
  have heg : SA.earlyTime p.toParams s ≤ SA.gateTime p.toParams (coverLabel p b₀) := by
    apply le_trans _ ((arming_gate_le_iff p s _).mpr hsj)
    rw [arming_early_eq, arming_gate_eq]
    have hd := p.deltaPos
    dsimp [Time] at *
    omega
  have ha : 0 ≤ a := le_trans (by unfold slotStartZ; have hd := p.deltaPos; positivity) hstart
  have hready : Gen.V2.Duty.ReadyTrigger E rho (ofWire p ⟨.proposer q, .proposal N⟩)
      send x a (a + p.Δ) := by
    refine ⟨y, hy, Or.inl he, ?_⟩
    intro t hat htd
    exact hA t (ha.trans hat) (hstart.trans hat) (htd.le.trans (hdeadline.trans heg))
  have hepoch : V2.D.restartFree rho x (V2.D.Run.actionCut rho a)
      (V2.D.Run.idxBefore rho (SA.earlyTime p.toParams s)) := by
    apply Gen.V2.Duty.restartFree_actionCut_idxBefore hp.base.valid.toScheduleWellFormed
      (hav.trans_lt (arming_vote_lt_early p s).1)
    intro k w hw haw hwe
    exact hR w (hstart.trans_lt haw) (hwe.le.trans heg) (List.mem_of_getElem? hw)
  exact ⟨{
    dl := fun t => t + p.Δ
    cut := b₀
    anchor := a
    within := arming_nonrow_delivery h
    ready := hready
    send_le := hsa
    nonneg := ha
    later := lt_add_of_pos_right _ p.deltaPos
    cut_le := hdeadline.trans hcut
    horizon := (hdeadline.trans hcut).trans hp.cut.2
    freeze_le := hdeadline
    history := hhistory
    epoch := hepoch
    handlers := hhandlers
    not_excluded := hnx }⟩

/-- P-Cl1's intended cut rows pass to the actual pending gate in the same epoch. -/
theorem arming_pending_rows_on {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}
    (hs : V2.D.ScheduleWellFormed E rho) {b₀ : Time} {l : Slot} {B D : Block}
    (hl : SA.gateTime p.toParams l ≤ b₀) (hcut : b₀ < SA.gateTime p.toParams (l + 1))
    {x : V} {i : Nat} (hi : IsGateTick p c rho i x (l + 1))
    (hCutEpoch : V2.D.restartFree rho x (timeIdx rho b₀)
      (V2.D.Run.idxBefore rho (SA.gateTime p.toParams (l + 1))))
    (hTickEpoch : V2.D.restartFree rho x
      (V2.D.Run.idxBefore rho (SA.gateTime p.toParams (l + 1))) i)
    (hF : ∀ k, k ≤ V2.D.Run.idxBefore rho (SA.gateTime p.toParams (l + 1)) →
      Block.Preceq (F_at p c E rho k x) D)
    (hrows : ∀ a < p.k - 1, ∃ Ca,
      GridCO.savedGenuine (storeAt p c E rho (timeIdx rho b₀) x).base
        (l + 1 - (a + 1)) = some (some Ca) ∧ Block.Preceq B Ca ∧ Block.Preceq Ca D) :
    ∀ a < p.k - 1, ∃ Ca,
      GridCO.savedGenuine (FGSA.clockPre p (storeAt p c E rho i x)
        (SA.gateTime p.toParams (l + 1))).base (l + 1 - (a + 1)) = some (some Ca) ∧
      Block.Preceq B Ca := by
  rw [arming_tick_store_on hs hi hTickEpoch]
  exact arming_slow_saved_on hs hl (arming_timeIdx_le_idxBefore rho hcut)
    le_rfl hCutEpoch hF hrows

end AvailableChain.FGSA.Run
end
