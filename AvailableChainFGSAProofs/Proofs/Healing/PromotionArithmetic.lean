module
public import AvailableChainFGSAProofs.Proofs.Shared.BoundsW
public import AvailableChainFGSAProofs.Proofs.Shared.StoreRun
public import AvailableChainFGSAProofs.Proofs.Shared.Reads -- shake: keep (healing lane strict-read supplier)
public import AvailableChainFGSAClaims.Statements.Regimes
public import AvailableChainFGSAClaims.Statements.Channels
public import AvailableChainFGSARun.Proofs.Interface

public section

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG Gen.Pure

variable {p : Params} {In V : Type} [DecidableEq V] [Fintype V] {c : AppCodec In}

private theorem promotion_period_pos (p : Params) : 0 < P p := by
  have hR : (2 : Time) ≤ p.R := by exact_mod_cast p.RLarge
  change 0 < 4 * (p.R : Time) * p.Δ
  have := p.deltaPos
  nlinarith

/-- Blueprint 21:1356–1370; plan §3.2 step 2.
DC: INTENTIONAL GUP r2 rounds the gap up by less than one proposal-grid interval. -/
theorem healing_promotion_gap_remainder (p : Params) (G : Time) :
    G ≤ Γ p G ∧ Γ p G < G + 4 * p.Δ :=
  fgsa_gamma_bounds p G

private theorem promotion_grid_upper (p : Params) (G z : Time) (s : Slot)
    (hs : SA.proposalTime p.toParams s ≤ 4 * p.Δ * z + G) :
    SA.proposalTime p.toParams s ≤ 4 * p.Δ * z + Γ p G := by
  linarith [(fgsa_gamma_bounds p G).1]

/-- A row held before one deadline remains held before each later deadline. -/
theorem healing_promotion_held_mono (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : Recovery₂ p c E rho G ΔF)
    {d d' : Time} (hdd : d ≤ d') {x : V} {a : RowWire p.n}
    (ha : HeldBefore p c E rho x a d) : HeldBefore p c E rho x a d' := by
  have hs := hrec.base.valid.toScheduleWellFormed
  change rowHeld p (V2.D.Run.stateBeforeTime E rho d x).st a at ha
  change rowHeld p (V2.D.Run.stateBeforeTime E rho d' x).st a
  rw [← Gen.V2.Duty.stateBefore_idxBefore E rho d hs] at ha
  rw [← Gen.V2.Duty.stateBefore_idxBefore E rho d' hs]
  have hi : V2.D.Run.idxBefore rho d ≤ V2.D.Run.idxBefore rho d' := by
    rw [V2.D.Run.idxBefore_def, V2.D.Run.idxBefore_def]
    rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
    exact List.countP_mono_left (fun e _ he => decide_eq_true
      (lt_of_lt_of_le (of_decide_eq_true he) hdd))
  obtain ⟨_, _, hprops, hpool⟩ := fgsa_store_durable p c E rho hi x
  change a ∈ (storeAt p c E rho (V2.D.Run.idxBefore rho d) x).rowPool ∨
    a ∈ FGSA.blockWireRows (storeAt p c E rho (V2.D.Run.idxBefore rho d) x) at ha
  change a ∈ (storeAt p c E rho (V2.D.Run.idxBefore rho d') x).rowPool ∨
    a ∈ FGSA.blockWireRows (storeAt p c E rho (V2.D.Run.idxBefore rho d') x)
  rcases ha with hp | hb
  · exact Or.inl (hpool.subset hp)
  · right
    change a ∈ FGSA.allBlockRows _ at hb ⊢
    unfold FGSA.allBlockRows at hb ⊢
    obtain ⟨rows, hr, ha⟩ := List.mem_flatten.mp hb
    obtain ⟨o, ho, he⟩ := List.mem_filterMap.mp hr
    exact List.mem_flatten.mpr ⟨rows, List.mem_filterMap.mpr ⟨o, hprops.subset ho, he⟩, ha⟩

/-- Blueprint 21:1356–1370; plan §3.2 step 2.
DC: INTENTIONAL the full G window fits inside the supplied gate horizon.
The result retains the honest slot; it does not assert proposal emission. -/
theorem healing_promotion_gap (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {G ΔF : Time} (hrec : Recovery₂ p c E rho G ΔF) (r : Nat)
    (hgst : E.t_GST ≤ p.actionTime r)
    (hhor : p.actionTime r + 2 * P p + Γ p G - 4 * p.Δ ≤ rho.horizon) :
    (r : Time) * P p + 2 * P p - 4 * p.Δ + G ≤ rho.horizon ∧
    ∃ s, (r : Time) * P p + 2 * P p ≤ SA.proposalTime p.toParams s ∧
      SA.proposalTime p.toParams s ≤
        p.actionTime r + 2 * P p + Γ p G - 10 * p.Δ ∧
      Gen.V2.Duty.HonestSlot rho (fgsaInterface p c) s ∧
      SA.gateTime p.toParams s ≤
        p.actionTime r + 2 * P p + Γ p G - 4 * p.Δ := by
  have hrem := (healing_promotion_gap_remainder p G).1
  have hR : (2 : Time) ≤ p.R := by exact_mod_cast p.RLarge
  have hP : 8 * p.Δ ≤ P p := by change 8 * p.Δ ≤ 4 * (p.R : Time) * p.Δ; nlinarith [p.deltaPos]
  have ha := actionTime_periodW p r
  have hwindow : (r : Time) * P p + 2 * P p - 4 * p.Δ + G ≤ rho.horizon := by
    linarith [p.deltaPos]
  have hstart : E.t_GST ≤ (r : Time) * P p + 2 * P p - 4 * p.Δ := by
    linarith [p.deltaPos]
  obtain ⟨s, hlo, hhi, hs⟩ := hrec.gap _ hstart hwindow
  rw [proposalTime_fgsa] at hlo hhi
  have hgrid : (r : Time) * P p + 2 * P p - 4 * p.Δ =
      4 * p.Δ * ((r : Time) * p.R + 2 * p.R - 1) := by
    change (r : Time) * (4 * (p.R : Time) * p.Δ) +
      2 * (4 * (p.R : Time) * p.Δ) - 4 * p.Δ = _
    ring
  have hup := promotion_grid_upper p G ((r : Time) * p.R + 2 * p.R - 1) s
    (by rw [← hgrid]; exact hhi)
  rw [← hgrid] at hup
  have hlow : (r : Time) * P p + 2 * P p ≤ SA.proposalTime p.toParams s := by
    rw [hgrid] at hlo
    change 4 * p.Δ * ((r : Time) * p.R + 2 * p.R - 1) < 4 * p.Δ * (s : Time) at hlo
    have hc : (r : Time) * p.R + 2 * p.R ≤ s := by
      have := p.deltaPos
      have : (r : Time) * p.R + 2 * p.R - 1 < s := by nlinarith
      linarith only [Int.add_one_le_iff.mpr this]
    change (r : Time) * (4 * (p.R : Time) * p.Δ) +
      2 * (4 * (p.R : Time) * p.Δ) ≤ 4 * p.Δ * (s : Time)
    nlinarith [p.deltaPos]
  refine ⟨hwindow, s, hlow, by linarith, hs, ?_⟩
  change SA.proposalTime p.toParams s + 6 * p.Δ ≤ _
  linarith

/-- Blueprint 21:1371–1384; plan §3.2 step 3.
DC: SAME the earlier row's deadline is bounded without a later row selection. -/
theorem healing_promotion_row_deadline (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time}
    (hrec : Recovery₂ p c E rho G ΔF) (hbound : LivenessBoundW p ΔF)
    {r rSent : Nat} (hr : rSent ≤ r) (hgst : E.t_GST ≤ p.actionTime r)
    {s : Slot} (hs : carrierTimeW p ΔF r ≤ SA.proposalTime p.toParams s) :
    max (p.actionTime rSent) E.t_GST + ΔF ≤ p.actionTime r + ΔF ∧
    p.actionTime r + ΔF ≤ carrierTimeW p ΔF r ∧
    carrierTimeW p ΔF r ≤ ((r : Time) + 1) * P p ∧
    max (p.actionTime rSent) E.t_GST + ΔF ≤ SA.proposalTime p.toParams s ∧
    max (p.actionTime r) E.t_GST + ΔF ≤ SA.proposalTime p.toParams s ∧
    r * p.R + 2 ≤ s := by
  have hF : 0 ≤ ΔF := by have := hrec.deltaF; rw [hrec.base.delta] at this; linarith [p.deltaPos]
  have hcast : (rSent : Time) ≤ r := by exact_mod_cast hr
  have htime : p.actionTime rSent ≤ p.actionTime r := by
    rw [actionTime_periodW, actionTime_periodW]
    have := promotion_period_pos p
    nlinarith
  have hb := action_delivery_boundsW p ΔF r hF hbound
  change _ ∧ _ ∧ _ at hb
  have h1 : max (p.actionTime rSent) E.t_GST + ΔF ≤ p.actionTime r + ΔF := by
    have := max_le htime hgst
    linarith
  have hdeadline := hb.2.1.trans hs
  have hk : (2 : Time) ≤ kappaF p ΔF := by exact_mod_cast kappaF_ge_two p ΔF hF
  have hcast : ((r * p.R + 2 : Nat) : Time) ≤ s := by
    rw [carrierTimeW_def, betaF_def] at hs
    change (r : Time) * (4 * (p.R : Time) * p.Δ) +
      4 * (kappaF p ΔF : Time) * p.Δ ≤ 4 * p.Δ * (s : Time) at hs
    push_cast
    nlinarith [p.deltaPos]
  exact ⟨h1, hb.2.1, hb.2.2, h1.trans hdeadline,
    by rw [max_eq_left hgst]; exact hdeadline, by exact_mod_cast hcast⟩

/-- The H.9(b) trigger keeps the earlier strict deadline chain. -/
theorem healing_promotion_row_deadline_strict (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time}
    (hrec : Recovery₂ p c E rho G ΔF) (hbound : LivenessBoundW p ΔF)
    {r rSent : Nat} (hr : rSent ≤ r) (hgst : E.t_GST ≤ p.actionTime r)
    {s : Slot} (hs : (r : Time) * P p + 2 * P p ≤ SA.proposalTime p.toParams s) :
    max (p.actionTime rSent) E.t_GST + ΔF ≤ p.actionTime r + ΔF ∧
    p.actionTime r + ΔF ≤ carrierTimeW p ΔF r ∧
    carrierTimeW p ΔF r ≤ ((r : Time) + 1) * P p ∧
    ((r : Time) + 1) * P p < SA.proposalTime p.toParams s := by
  have hc : carrierTimeW p ΔF r ≤ SA.proposalTime p.toParams s := by
    rw [carrierTimeW_def]
    have := betaF_le_period p ΔF hbound
    have := promotion_period_pos p
    linarith
  obtain ⟨h1, h2, h3, _⟩ := healing_promotion_row_deadline E rho hrec hbound hr hgst hc
  exact ⟨h1, h2, h3, by have := promotion_period_pos p; linarith⟩

/-- Blueprint 21:1371–1384; plan §3.2 step 3.
DC: SAME strict receipt at max(send,GST)+ΔF, for the original signed row.
Assembly supplies rowsReceipt with RowService.fgsa_tRowsReceipt. -/
theorem healing_promotion_row_receipt (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time}
    (hrec : Recovery₂ p c E rho G ΔF) (hbound : LivenessBoundW p ΔF)
    (rowsReceipt : ∀ j y r (a : RowWire p.n),
      HonestRowAt p c E rho j y r a →
      max (p.actionTime r) E.t_GST + ΔF ≤ rho.horizon →
      ∀ x ∈ rho.honest,
        HeldBefore p c E rho x a (max (p.actionTime r) E.t_GST + ΔF))
    {r j rSent : Nat} {y : V} {a : RowWire p.n}
    (hr : rSent ≤ r) (ha : HonestRowAt p c E rho j y rSent a)
    (hgst : E.t_GST ≤ p.actionTime r) {s : Slot}
    (hs : carrierTimeW p ΔF r ≤ SA.proposalTime p.toParams s)
    (hhor : SA.proposalTime p.toParams s ≤ rho.horizon) :
    max (p.actionTime rSent) E.t_GST + ΔF ≤ SA.proposalTime p.toParams s ∧
    max (p.actionTime r) E.t_GST + ΔF ≤ SA.proposalTime p.toParams s ∧
    r * p.R + 2 ≤ s ∧
    ∀ x ∈ rho.honest,
      HeldBefore p c E rho x a (max (p.actionTime rSent) E.t_GST + ΔF) ∧
      HeldBefore p c E rho x a (p.actionTime r + ΔF) := by
  obtain ⟨h1, _, _, hd, hbatch, hslot⟩ :=
    healing_promotion_row_deadline E rho hrec hbound hr hgst hs
  refine ⟨hd, hbatch, hslot, ?_⟩
  intro x hx
  have hheld := rowsReceipt j y rSent a ha (hd.trans hhor) x hx
  exact ⟨hheld, healing_promotion_held_mono E rho hrec h1 hheld⟩

/-- The H.9(b) trigger keeps the strict deadline and the original signed row. -/
theorem healing_promotion_row_receipt_strict (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time}
    (hrec : Recovery₂ p c E rho G ΔF) (hbound : LivenessBoundW p ΔF)
    (rowsReceipt : ∀ j y r (a : RowWire p.n),
      HonestRowAt p c E rho j y r a →
      max (p.actionTime r) E.t_GST + ΔF ≤ rho.horizon →
      ∀ x ∈ rho.honest,
        HeldBefore p c E rho x a (max (p.actionTime r) E.t_GST + ΔF))
    {r j rSent : Nat} {y : V} {a : RowWire p.n}
    (hr : rSent ≤ r) (ha : HonestRowAt p c E rho j y rSent a)
    (hgst : E.t_GST ≤ p.actionTime r) {s : Slot}
    (hs : (r : Time) * P p + 2 * P p ≤ SA.proposalTime p.toParams s)
    (hhor : SA.proposalTime p.toParams s ≤ rho.horizon) :
    max (p.actionTime rSent) E.t_GST + ΔF < SA.proposalTime p.toParams s ∧
    ∀ x ∈ rho.honest,
      HeldBefore p c E rho x a (max (p.actionTime rSent) E.t_GST + ΔF) ∧
      HeldBefore p c E rho x a (p.actionTime r + ΔF) := by
  obtain ⟨h1, h2, h3, h4⟩ :=
    healing_promotion_row_deadline_strict E rho hrec hbound hr hgst hs
  have hd := lt_of_le_of_lt (h1.trans (h2.trans h3)) h4
  obtain ⟨_, _, _, hheld⟩ :=
    healing_promotion_row_receipt E rho hrec hbound rowsReceipt hr ha hgst
      ((h3.trans h4.le)) hhor
  exact ⟨hd, hheld⟩

/-- Blueprint 21:1385–1410; plan §3.2 steps 4–5.
DC: SAME two full periods give the maturity required by K-HEIGHT. -/
theorem healing_promotion_maturity (p : Params) (hδ : p.δt = 2 * p.R)
    {s : Nat} {U : FGBlock (Fin p.n)}
    (hs : SA.proposalTime p.toParams U.slot + 2 * P p ≤ SA.proposalTime p.toParams s) :
    U.slot + p.δt ≤ s := by
  have hcast : ((U.slot + 2 * p.R : Nat) : Time) ≤ s := by
    push_cast
    change 4 * p.Δ * (U.slot : Time) +
      2 * (4 * (p.R : Time) * p.Δ) ≤ 4 * p.Δ * (s : Time) at hs
    have := p.deltaPos
    nlinarith
  rw [hδ]
  exact_mod_cast hcast

/-- The entry-slot bound supplies the old action-based maturity case. -/
theorem healing_promotion_maturity_of_action (p : Params) (hδ : p.δt = 2 * p.R)
    {r s : Nat} {U : FGBlock (Fin p.n)} (hU : U.slot ≤ r * p.R)
    (hs : (r : Time) * P p + 2 * P p ≤ SA.proposalTime p.toParams s) :
    U.slot + p.δt ≤ s := by
  apply healing_promotion_maturity p hδ
  have hcast : (U.slot : Time) ≤ (r : Time) * p.R := by exact_mod_cast hU
  change 4 * p.Δ * (U.slot : Time) + 2 * P p ≤ _
  change (r : Time) * (4 * (p.R : Time) * p.Δ) +
    2 * (4 * (p.R : Time) * p.Δ) ≤ _ at hs
  change _ + 2 * (4 * (p.R : Time) * p.Δ) ≤ _
  nlinarith [p.deltaPos]

/-- Blueprint 21:1592–1638; plan §3.2 step 7.
DC: INTENTIONAL the age-sensitive trigger is on the proposal grid.
This is the deadline component, not an acceptance or service producer. -/
theorem healing_promotion_age_gap (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time}
    (hrec : Recovery₂ p c E rho G ΔF) (r : Nat) (q : Slot)
    (hgst : E.t_GST ≤ (r : Time) * P p)
    (hwin : max ((r : Time) * P p + betaF p ΔF - 4 * p.Δ)
      (SA.proposalTime p.toParams q + 2 * P p - 4 * p.Δ) + G ≤ rho.horizon) :
    let U_F := max ((r : Time) * P p + betaF p ΔF - 4 * p.Δ)
      (SA.proposalTime p.toParams q + 2 * P p - 4 * p.Δ)
    U_F + G ≤ rho.horizon ∧
    ∃ s, U_F < SA.proposalTime p.toParams s ∧
      SA.proposalTime p.toParams s ≤ U_F + Γ p G ∧
      Gen.V2.Duty.HonestSlot rho (fgsaInterface p c) s ∧
      SA.proposalTime p.toParams s + p.Δ ≤
        max (p.actionTime r + Γ p G - p.Δ + epsF p ΔF)
          (SA.proposalTime p.toParams q + 2 * P p + Γ p G - 3 * p.Δ) ∧
      SA.gateTime p.toParams s ≤
        max (p.actionTime r + Γ p G + 4 * p.Δ + epsF p ΔF)
          (SA.proposalTime p.toParams q + 2 * P p + Γ p G + 2 * p.Δ) := by
  let a := (r : Time) * P p + betaF p ΔF - 4 * p.Δ
  let b := SA.proposalTime p.toParams q + 2 * P p - 4 * p.Δ
  let U_F := max a b
  have hF : 0 ≤ ΔF := by have := hrec.deltaF; rw [hrec.base.delta] at this; linarith [p.deltaPos]
  have hk : (2 : Time) ≤ kappaF p ΔF := by exact_mod_cast kappaF_ge_two p ΔF hF
  have ha : E.t_GST ≤ a := by
    dsimp only [a]
    rw [betaF_def]
    nlinarith [p.deltaPos]
  have hstart : E.t_GST ≤ U_F := ha.trans (le_max_left a b)
  have hgate : max (p.actionTime r + Γ p G + 4 * p.Δ + epsF p ΔF)
      (SA.proposalTime p.toParams q + 2 * P p + Γ p G + 2 * p.Δ) =
      U_F + Γ p G + 6 * p.Δ := by
    rw [actionTime_periodW, epsF_def]
    change max _ _ = max a b + _ + _
    rw [← max_add_add_right, ← max_add_add_right]
    congr 1 <;> dsimp only [a, b] <;> ring
  have hterminal : max (p.actionTime r + Γ p G - p.Δ + epsF p ΔF)
      (SA.proposalTime p.toParams q + 2 * P p + Γ p G - 3 * p.Δ) =
      U_F + Γ p G + p.Δ := by
    rw [actionTime_periodW, epsF_def]
    change max _ _ = max a b + _ + _
    rw [← max_add_add_right, ← max_add_add_right]
    congr 1 <;> dsimp only [a, b] <;> ring
  have hwindow : U_F + G ≤ rho.horizon := hwin
  obtain ⟨s, hlo, hhi, hs⟩ := hrec.gap U_F hstart hwindow
  rw [proposalTime_fgsa] at hlo hhi
  have hgrid : U_F = 4 * p.Δ * max
      ((r : Time) * p.R + kappaF p ΔF - 1) ((q : Time) + 2 * p.R - 1) := by
    dsimp only [U_F, a, b]
    rw [mul_max_of_nonneg _ _ (by linarith [p.deltaPos])]
    congr 1
    · change (r : Time) * (4 * (p.R : Time) * p.Δ) + betaF p ΔF - 4 * p.Δ = _
      rw [betaF_def]; ring
    · change 4 * p.Δ * (q : Time) + 2 * (4 * (p.R : Time) * p.Δ) - 4 * p.Δ = _
      ring
  have hup := promotion_grid_upper p G _ s (by rw [← hgrid]; exact hhi)
  rw [← hgrid] at hup
  refine ⟨hwindow, s, hlo, hup, hs, ?_, ?_⟩
  · rw [hterminal]; linarith
  · rw [hgate]
    change SA.proposalTime p.toParams s + 6 * p.Δ ≤ _
    linarith

end AvailableChain.FGSA.Run
end
