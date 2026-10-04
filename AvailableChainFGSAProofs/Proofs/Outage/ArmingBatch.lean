module
public import AvailableChainFGSAProofs.Proofs.Outage.ArmingHistory
public import AvailableChainFGSAProofs.Proofs.Shared.HeadAdmit
public import AvailableChainFGSAProofs.Proofs.Shared.GateReceipt
public import AvailableChainFGSARun.Proofs.Receipts

public section

/-! Plan O-ARM §4 field 6, §6.2 steps 1–2 and 4, §11 obligation 3. The last
healthy label-`(l + 1)` batch. Each honest awake HEAD of label `l + 1` extends
`D` by `htransfer`, and the healthy cut delivers it, with its block and every
stored ancestor, before e(l + 1) = d(l) ≤ b₀. NoRestart keeps the votes, the
blocks and their original stamps at every later index. -/

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG
open Gen.Pure

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

/-- Plan O-ARM §2. Class (iii). DC: INTENTIONAL; v(r) as a multiple of Δ. -/
theorem arming_vote_nat (p : Params) (r : Slot) :
    ((4 * r + 1 : Nat) : Time) * p.Δ = SA.voteTime p.toParams r := by
  rw [arming_vote_eq]
  push_cast
  ring

/-- Plan O-ARM §2. Class (iii). DC: INTENTIONAL; e(r) as a multiple of Δ. -/
theorem arming_early_nat (p : Params) (r : Slot) :
    ((4 * r + 2 : Nat) : Time) * p.Δ = SA.earlyTime p.toParams r := by
  rw [arming_early_eq]
  push_cast
  ring

/-- Plan O-ARM §2. Class (iii). DC: INTENTIONAL; t(r) as a multiple of Δ. -/
theorem arming_proposal_nat (p : Params) (r : Slot) :
    ((4 * r : Nat) : Time) * p.Δ = SA.proposalTime p.toParams r := by
  rw [arming_proposal_eq]
  push_cast
  ring

/-- Plan O-ARM §2. Class (iii). DC: INTENTIONAL; d(r) as a multiple of Δ. -/
theorem arming_gate_nat (p : Params) (r : Slot) :
    ((4 * r + 6 : Nat) : Time) * p.Δ = SA.gateTime p.toParams r := by
  rw [arming_gate_eq]
  push_cast
  ring

omit [DecidableEq V] in
/-- Plan O-ARM §6.2 step 1. Class (iii). DC: INTENTIONAL; an honest node ticks
at every public multiple of Δ in the horizon, also asleep. -/
theorem arming_tick_exists {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}
    (hs : V2.D.ScheduleWellFormed E rho) (hΔ : E.Δ = p.Δ) {y : V} (hy : y ∈ rho.honest)
    (m : Nat) {t : Time} (ht : (m : Time) * p.Δ = t) (hh : t ≤ rho.horizon) :
    ∃ k : Nat, rho.events[k]? = some (.tick y t) := by
  subst ht
  obtain ⟨k, hk, _⟩ := fgsa_tick_total E rho hs hΔ y hy m hh
  exact ⟨k, hk⟩

/-- ROOT-DIGEST W2b. Plan O-ARM §6.2 step 2, §11 obligation 3. Class (iii). DC: INTENTIONAL;
the block step of `inclusion_head_receipt_early` for any non-genesis block in
the store of an honest node before its v(r) tick: the healthy label window
delivers it to every honest reader before the e(r) tick. -/
theorem arming_block_early {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}
    (hE : V2.D.ExecutionValid E rho) (hN : V2.D.NoRestart rho) (hDelta : E.Δ = p.Δ)
    (r : Slot)
    (hSync : Gen.V2.Duty.LabelSyncOn E rho (fun o => ¬ isRowObject o)
      (SA.voteTime p.toParams r) (SA.earlyTime p.toParams r))
    {j : Nat} {x : V} (hj : rho.events[j]? = some (.tick x (SA.earlyTime p.toParams r)))
    {k : Nat} {z : V} (hz : z ∈ rho.honest)
    (hk : rho.events[k]? = some (.tick z (SA.voteTime p.toParams r)))
    (a : Block) (hne : a ≠ .genesis) (ha : a ∈ (storeAt p c E rho k z).base.blocks)
    (hF : Block.Preceq (eraseFG (storeAt p c E rho j x).fg.F) a)
    (hroots : NamedRootCollisionFree p c E rho) :
    a ∈ (storeAt p c E rho j x).base.blocks ∧
      GridCO.stampBlock (storeAt p c E rho j x).base a < SA.earlyTime p.toParams r := by
  have hsch := hE.toScheduleWellFormed
  have htimes : SA.voteTime p.toParams r + p.Δ = SA.earlyTime p.toParams r :=
    arming_vote_add p r
  rw [Gen.V2.Duty.LabelSyncOn_def] at hSync
  obtain ⟨dl, cut, hD, _, hlt, hbound, _, hcut, _⟩ := hSync
  have hdeadline : ∀ t, t ≤ SA.voteTime p.toParams r → dl t ≤ SA.earlyTime p.toParams r := by
    intro t ht
    have hb := hbound t
    rw [max_eq_right ht, hDelta, htimes] at hb
    exact hb
  have hm := ha
  change a ∈ (V2.D.Run.stateBefore E rho k z).st.base.blocks at hm
  rw [fgsa_preTick_eq_timeRead E rho hsch hN hk,
    ← Gen.V2.Duty.stateBefore_idxBefore E rho (SA.voteTime p.toParams r) hsch] at hm
  rw [← (metaInv_stateBefore E rho (V2.D.Run.idxBefore rho
    (SA.voteTime p.toParams r)) z).stampKeys] at hm
  obtain ⟨⟨b, stamp⟩, hm, he⟩ := List.mem_map.mp hm
  dsimp only at he
  subst b
  have hmem : a ∈ (storeAt p c E rho j x).base.blocks := by
    rcases fgsa_block_stamp_source E rho _ z a stamp hm with hgen |
      ⟨l, hl, t, o, ho, hacc, _⟩
    · exact (hne hgen.1).elim
    · obtain ⟨parent, hdel, _⟩ := hacc.1
      have htv := (Gen.V2.Duty.index_lt_idxBefore_iff hsch hdel _).mp hl
      have hdl := hdeadline t htv.le
      exact fgsa_gateReceipt_block_to_tick (hroots := hroots) E rho hE hN hDelta dl cut hD t o a ho
        (Or.inr ⟨z, hz, l, hacc⟩) (hlt t) (hdl.trans hcut)
        (hsch.honest_only _ (List.mem_of_getElem? hj)) hj hdl hF
  refine ⟨hmem, ?_⟩
  apply fgsa_gateReceipt_block_stamp_lt E rho hsch hN hj _ a hmem
  have := p.deltaPos
  rw [arming_early_eq]
  positivity

/-- Plan O-ARM §6.1 step 6. Class (iii). DC: INTENTIONAL; `htransfer` at the
label `l` of `D`: every honest label-`(l + 1)` HEAD extends `D`. -/
theorem arming_head_ge {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}
    (hs : V2.D.ScheduleWellFormed E rho) {b₀ : Time}
    (htransfer : ∀ y z s C H, y ∈ rho.honest → z ∈ rho.honest →
      SA.gateTime p.toParams s ≤ b₀ →
      gateResult p c E rho y s = some (some C) →
      vHead p c E rho z s = some H → Block.Preceq C H)
    {l : Slot} {D : Block} (hDmem : (l, D) ∈ cleanResults p c E rho (timeIdx rho b₀))
    {z : V} (hz : z ∈ rho.honest) {k : Nat}
    (hk : rho.events[k]? = some (.tick z (SA.voteTime p.toParams (l + 1)))) :
    Block.Preceq D (headVote p ((fgsa p c).clock (V2.D.Run.stateBefore E rho k z)
      (SA.voteTime p.toParams (l + 1))).st (l + 1)) := by
  obtain ⟨_, u, _, hu, _, hlb, _, hgr⟩ := arming_clean_mem hs le_rfl hDmem
  have hvh := vHead_eq_headAtIdx p c E rho hs hk
  have hread : headAtIdx p c E rho k (l + 1) = headVote p ((fgsa p c).clock
      (V2.D.Run.stateBefore E rho k z) (SA.voteTime p.toParams (l + 1))).st (l + 1) := by
    delta headAtIdx
    rw [hk]
  rw [hread] at hvh
  exact htransfer u z l D _ hu hz hlb hgr hvh

/-- ROOT-DIGEST W2b. Plan O-ARM §4 field 6, §6.2 steps 1–2, §11 obligation 3. Class (iii).
DC: INTENTIONAL; the last healthy batch at every honest receiver, asleep or
awake. Its window v(l + 1) < e(l + 1) = d(l) ≤ b₀ is inside the healthy cut. -/
theorem arming_healthy_batch {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}
    (hE : V2.D.ExecutionValid E rho) (hN : V2.D.NoRestart rho) (hDelta : E.Δ = p.Δ)
    (hC : V2.D.CStar (fgsaFamilies p c).fresh rho) {b₀ ΔF : Time}
    (hcut : 0 ≤ b₀ ∧ b₀ ≤ rho.horizon)
    (hhealthy : Gen.V2.Duty.HealthyPrefixDeliveryBy E rho (fgsaDelay E.Δ ΔF) b₀)
    (htransfer : ∀ y z s C H, y ∈ rho.honest → z ∈ rho.honest →
      SA.gateTime p.toParams s ≤ b₀ →
      gateResult p c E rho y s = some (some C) →
      vHead p c E rho z s = some H → Block.Preceq C H)
    {l : Slot} {D : Block} (hl : SA.gateTime p.toParams l ≤ b₀)
    (hcutl : b₀ < SA.gateTime p.toParams (l + 1))
    (hDmem : (l, D) ∈ cleanResults p c E rho (timeIdx rho b₀))
    (hF : ∀ k y, k ≤ V2.D.Run.idxBefore rho (SA.gateTime p.toParams (l + 1)) →
      y ∈ rho.honest → Block.Preceq (F_at p c E rho k y) D)
    (hroots : NamedRootCollisionFree p c E rho) :
    ∀ y (q : Fin p.n), y ∈ rho.honest →
      rho.seatOf (.base (.head (l + 1))) q ∈ rho.honest →
      E.awake (rho.seatOf (.base (.head (l + 1))) q) (SA.voteTime p.toParams (l + 1)) = true →
      ∃ K k, rho.events[k]? = some (.tick y (SA.earlyTime p.toParams (l + 1))) ∧
        V2.D.Run.emits E rho (rho.seatOf (.base (.head (l + 1))) q)
          (ofHead p ⟨.seat (.head (l + 1)) q, K⟩) (SA.voteTime p.toParams (l + 1)) ∧
        Block.Preceq D K ∧ K.slot ≤ l + 1 ∧
        baseVote (⟨.seat (.head (l + 1)) q, K⟩ : HeadWire p.n) ∈
          (storeAt p c E rho k y).base.votes ∧
        K ∈ (storeAt p c E rho k y).base.blocks ∧
        GridCO.stampVote (storeAt p c E rho k y).base
          (baseVote (⟨.seat (.head (l + 1)) q, K⟩ : HeadWire p.n)) <
          SA.earlyTime p.toParams (l + 1) ∧
        GridCO.stampBlock (storeAt p c E rho k y).base K < SA.earlyTime p.toParams (l + 1) := by
  intro y q hy hq hawake
  have hs := hE.toScheduleWellFormed
  have hd := p.deltaPos
  have he : SA.earlyTime p.toParams (l + 1) ≤ b₀ := (arming_early_next p l).trans_le hl
  have hv : SA.voteTime p.toParams (l + 1) < SA.earlyTime p.toParams (l + 1) :=
    (arming_vote_lt_early p (l + 1)).1
  obtain ⟨k, hk⟩ := arming_tick_exists hs hDelta hy (4 * (l + 1) + 2)
    (arming_early_nat p (l + 1)) (he.trans hcut.2)
  obtain ⟨kk, hkk⟩ := arming_tick_exists hs hDelta hq (4 * (l + 1) + 1)
    (arming_vote_nat p (l + 1)) ((hv.trans_le he).le.trans hcut.2)
  have hSync : Gen.V2.Duty.LabelSyncOn E rho (fun o => ¬ isRowObject o)
      (SA.voteTime p.toParams (l + 1)) (SA.earlyTime p.toParams (l + 1)) :=
    Gen.V2.Duty.LabelSyncOn.of_cleanCutBy E rho (fun o => ¬ isRowObject o) b₀ _ _
      hhealthy (fgsaDelay_nonrow E.Δ ΔF)
      (by rw [hDelta, arming_vote_add]) he hcut.2
  have hDK := arming_head_ge hs htransfer hDmem hq hkk
  have hkI : k ≤ V2.D.Run.idxBefore rho (SA.gateTime p.toParams (l + 1)) :=
    ((Gen.V2.Duty.index_lt_idxBefore_iff hs hk _).mpr (he.trans_lt hcutl)).le
  obtain ⟨hem, hvm, hvs, hKm, hbs, hslot⟩ := inclusion_head_receipt_early (hroots := hroots)
    E rho hE hN hDelta hC
    (l + 1) hSync hk q hq hawake hkk _ rfl (block_preceq_trans (hF k y hkI hy) hDK)
  exact ⟨_, k, hk, hem, hDK, hslot, hvm, hKm, hvs, hbs⟩

end AvailableChain.FGSA.Run
end
