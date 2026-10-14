module
public import AvailableChainFGCompose.Proofs.Population.FrontierSearchAge
public import AvailableChainFGCompose.Proofs.Population.FrontierSearchRepair
import all AvailableChainFGCompose.Proofs.Healing.FrontierSearchTop

public section

namespace AvailableChain.FGCompose
open AvailableChain.SimplexFG AvailableChain.KitFG

variable {In V : Type} {Prot : V2.ProtocolSpecD In} [DecidableEq V]
variable {n : Nat} {Base Proposal Wire Body : Type}
variable (R : FGCoreReads Prot n Base Proposal Wire) (S : FGSafetyReads Prot n Wire)
variable (O : FGObservationReads R) (T : FGTiming)
variable (E : Generic.Env V) (rho : V2.D.Run V Prot) (I : V2.D.Interface Prot)
variable (D : FGHistoryWireReads S) (Ef : Electorate (Fin n))
variable (decodeProposal : Prot.Object → Option (Slot × Body))
variable (bodyErase : Body → Block) (bodyRows : Body → List Wire)
variable (blockWireRows : Prot.State → List Wire)
variable (parentFG : Prot.State → Block → Option (FGBlock (Fin n)))
variable (parentHeight : Prot.State → Slot → FGBlock (Fin n) → Height × BlockId)
variable (validFor : Prot.State → Slot → FGBlock (Fin n) → Wire → Bool)
variable (fold : Prot.State → Slot → FGBlock (Fin n) → Window.State (Fin n))
variable (Jst : Time) (leaseSlots : Nat)
variable (obs : FGObservationLaws R O) (cert : FGCertificateLaws Ef O.height O.finality)
variable (inv : ∀ i x, FGStoreInvariant O.height O.finality
  (R.core (rho.stateBefore E i x)).fg)
variable (justif : FGJustificationLaws O.height)
variable (keep : ∀ i j, i ≤ j → ∀ x, TFAt R E rho i x ⊆ TFAt R E rho j x)
variable (positive : 0 < T.delta) (coreLaws : FGCoreLaws R)
variable (erasePreceq : ∀ {A B}, FGBlock.Preceq A B → Block.Preceq (R.erase A) (R.erase B))
variable (joined : Prot.State → Bool) (receipt : Block → Time → V → Prop)

include obs cert inv in
/-- ROOT-DIGEST W2b. Blueprint 21 HG.3 top J. DC: SAME finish repair in a quiet settled
phase. The entry-age input is local to this helper; the public consumer proves it
from the actual start carrier. -/
private theorem p0d5c_top_phase_holder (hT : FGTimingLaws T) (hk : 1 ≤ leaseSlots)
    (schedule : V2.D.ScheduleWellFormed E rho)
    (faultWeight : Ef.weightOf (historyFaulty S rho) < Ef.q)
    {G ΔF ρbar u Dl : Time} (deltaF : E.Δ ≤ ΔF) (hdelta : E.Δ = T.delta)
    (gap : ∀ t, E.t_GST ≤ t → t + G ≤ rho.horizon →
      ∃ s, t < T.proposal s ∧ T.proposal s ≤ t + G ∧ Gen.V2.Duty.HonestSlot rho I s)
    (hJst : E.t_GST ≤ Jst) (hG : 4 * T.delta ≤ G)
    (slotProposal : PromotionSlotProposal R E rho T I)
    (read : PromotionProposalRead R S E rho O I decodeProposal bodyErase bodyRows parentFG
      parentHeight validFor fold)
    (order : PromotionRowOrder R E rho O I) (signer : PromotionRowSigner S E rho T D)
    (sourceParent : PromotionSourceParent R E rho O T I Jst)
    {deltaT : Nat} (hδ : deltaT = 2 * T.roundSlots) (hbound : LivenessBoundW T ΔF)
    (rowsReceipt : TRowsReceipt R S E rho T blockWireRows ΔF)
    (progressCoverage : ∀ (r height : Nat) (U X : FGBlock (Fin n)),
      BatchPrem R S O T E rho I D Ef decodeProposal bodyErase bodyRows blockWireRows
        parentFG parentHeight validFor ΔF .progress r height U X →
      (O.height X.parent).h = height → ProgressCoveredByChild Ef O.height X U height)
    (hfold : ProgressFoldAdvance Ef O.height deltaT)
    (honestQuorum : ∃ Q : Finset (Fin n),
      (∀ i ∈ Q, safetyHolder S rho i ∈ rho.honest) ∧ Ef.q ≤ Ef.weightOf Q)
    (entryAgreement : ∀ r x y K L, x ∈ rho.honest → y ∈ rho.honest →
      actionSourceFG R E rho T x r = some (some K) →
      actionSourceFG R E rho T y r = some (some L) →
      (O.height K).T_h.root = (O.height L).T_h.root → (O.height K).T_h = (O.height L).T_h)
    (sourceSlot : ∀ r x K, x ∈ rho.honest →
      actionSourceFG R E rho T x r = some (some K) → K.slot ≤ r * T.roundSlots)
    (ancestorSlot : ∀ r x K A, x ∈ rho.honest →
      actionSourceFG R E rho T x r = some (some K) → FGBlock.Preceq A K →
      A.slot ≤ K.slot)
    (eraseInj : Function.Injective R.erase)
    (eraseReflect : ∀ A B : FGBlock (Fin n), Block.Preceq (R.erase A) (R.erase B) →
      FGBlock.Preceq A B)
    (floor : AttemptProposalFloor R E rho O T I Jst)
    (gateCopy : ∀ u v m J contested q Q, Jst ≤ u →
      PhaseInterval R E rho O u v m J contested →
      FrontierSeedQualification T leaseSlots E.t_GST u q → T.gate q ≤ v →
      HonestProposal E rho I q Q → ∃ i x Qfg, V2.D.Run.idxBefore rho u ≤ i ∧
        i ≤ timeIdx rho v ∧ x ∈ rho.honest ∧
        Qfg ∈ (R.core (rho.stateBefore E i x)).fg.TF ∧ R.erase Qfg = Q)
    (service : ∀ u v m J contested q Q Qfg, Jst ≤ u → HonestProposal E rho I q Q →
      R.erase Qfg = Q → (O.height Qfg).h = m → FrontierProposalService R E rho T q Q →
      FrontierSeedQualification T leaseSlots E.t_GST u q → u ≤ T.proposal q →
      PhaseInterval R E rho O u (T.gate q) m J contested → T.gate q ≤ v →
      v ≤ rho.horizon →
      (∀ i x, timeIdx rho u ≤ i → i ≤ timeIdx rho v → x ∈ rho.honest →
        (R.core (rho.stateBefore E i x)).fg.h_max ≤ m) →
      FrontierLocalServiceFG R S E rho O T I D.heightPair q Q Qfg m v)
    (common : ∀ u m J contested q Q Qfg r, Jst ≤ u → HonestProposal E rho I q Q →
      R.erase Qfg = Q → FrontierProposalService R E rho T q Q →
      FrontierSeedQualification T leaseSlots E.t_GST u q → u ≤ T.proposal q →
      q ≤ r * T.roundSlots → (∀ r', q ≤ r' * T.roundSlots → r ≤ r') →
      PhaseInterval R E rho O u (T.action r) m J contested →
      OpeningCoveredFG R S E rho O.height T D.heightPair (FGHonestSeats S rho) r Q ∧
      ((O.height Qfg).h = m - 1 → OpeningEntry R E rho O.height T r (m - 1) ∨
        ∃ x K, x ∈ rho.honest ∧ actionSourceFG R E rho T x r = some (some K) ∧
          (O.height K).h = m))
    {J : FGBlock (Fin n)} {m : Nat} {w : Time} (hready : Jst ≤ u)
    (hp : PhaseInterval R E rho O u Dl m (some J) false)
    (allowance : FrontierRepairAllowance R E rho O T I Jst leaseSlots G ρbar u)
    (hrepairBudget : u + ρbar ≤ Dl)
    (hopeningBudget : u + ρbar + FGCompose.P T + Γ T G + epsF T ΔF ≤ Dl)
    (hentryBudget : w + 2 * FGCompose.P T + Γ T G - 4 * T.delta ≤ Dl)
    (hentryAge : ∀ q Q Qfg, HonestProposal E rho I q Q → R.erase Qfg = Q →
      u ≤ T.proposal q → T.gate q ≤ Dl → (O.height Qfg).h = m - 1 →
      T.proposal (O.height Qfg).T_h.slot ≤ w - 6 * T.delta) :
    ∃ t, u ≤ t ∧ t ≤ Dl ∧
      StrongServedFG R S E rho O T I D.heightPair Jst leaseSlots m t := by
  classical
  have hGST : E.t_GST ≤ u := hJst.trans hready
  have hd := hT.delta_pos
  have hP := frontierSearch_period_bound T hT
  have hΓ := (healing_promotion_gap_remainder T hT G).1
  have hbudget0 : u + ρbar ≤ Dl := hrepairBudget
  have hF : 0 ≤ ΔF := by rw [hdelta] at deltaF; linarith
  have heps0 := p0d5c_top_eps_nonneg T hT hF
  obtain ⟨_, l, hl, hrep⟩ := allowance
  obtain ⟨hafter, hseedEx⟩ := hrep hG Dl m (some J) false hready hp
  obtain ⟨q, Q, hlq, hgate, hQ, hsvc⟩ := hseedEx hbudget0
  have hseed := frontierSearch_seed_of_start E T leaseSlots hl hlq
  have huq := frontierSearch_seed_after T leaseSlots hT hk hseed
  have hqg : T.proposal q ≤ T.gate q := by rw [hT.gate_eq]; linarith
  have hgateD : T.gate q ≤ Dl := hgate.trans hbudget0
  obtain ⟨iq, xq, Qfg, hiq0, hiq1, hxq, hQmem, hErase⟩ :=
    gateCopy u Dl m (some J) false q Q hready hp hseed hgateD hQ
  obtain ⟨hlo, hhi⟩ := frontierSearch_proposal_heights R E rho O T I Jst Ef obs cert inv
    floor hready hp huq hgateD hQ hErase ⟨iq, xq, hiq0, hiq1, hxq, hQmem⟩
  have finishAt {s : Slot} {X : FGBlock (Fin n)} (hls : T.proposal l < T.proposal s)
      (hnew : HonestProposal E rho I s (R.erase X)) (hut : u ≤ T.proposal s)
      (hsD : T.gate s ≤ Dl) (hh : m ≤ (O.height X).h) :
      ∃ t, u ≤ t ∧ t ≤ Dl ∧
      StrongServedFG R S E rho O T I D.heightPair Jst leaseSlots m t := by
    have hsg : u ≤ T.gate s := hut.trans (by rw [hT.gate_eq]; linarith)
    have hps := frontierSearch_phase_cut R E rho O hp hsg hsD
    have hss := (hrep hG (T.gate s) m (some J) false hready hps).1 s _ hls le_rfl hnew
    have hseedS := frontierSearch_seed_of_start E T leaseSlots hl hls
    obtain ⟨j, y, Y, hj0, hj1, hy, hYmem, hYe⟩ :=
      gateCopy u Dl m (some J) false s _ hready hp hseedS hsD hnew
    have hYX : Y = X := eraseInj hYe
    subst Y
    have hheights := frontierSearch_proposal_heights R E rho O T I Jst Ef obs cert inv
      floor hready hp hut hsD hnew rfl ⟨j, y, hj0, hj1, hy, hYmem⟩
    have hh' : (O.height X).h = m := Nat.le_antisymm hheights.2 hh
    exact ⟨_, hsg, hsD, frontierSearch_save_seed_holder R S E rho O T I D.heightPair Jst leaseSlots
      obs hT hk hready hp hseedS hnew rfl hh' hss hsD
      (service u (T.gate s) m (some J) false s _ X hready hnew rfl hh' hss hseedS hut hps le_rfl
        (hsD.trans hp.2.1) (frontierSearch_phase_cap R E rho O obs hp hsD))⟩
  by_cases hhigh : (O.height Qfg).h = m
  · exact finishAt hlq (hErase ▸ hQ) huq hgateD hhigh.ge
  have hlow : (O.height Qfg).h = m - 1 := by
    have hlo' : m - 1 ≤ (O.height Qfg).h := by simpa using hlo
    exact Nat.le_antisymm (Nat.le_sub_one_of_lt (lt_of_le_of_ne hhi hhigh)) hlo'
  have hex : ∃ r, q ≤ r * T.roundSlots := ⟨q, by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left q
      (show 1 ≤ T.roundSlots from (by decide : 1 ≤ 2).trans hT.rounds)⟩
  let r := Nat.find hex
  have hqr : q ≤ r * T.roundSlots := Nat.find_spec hex
  have hfirst : ∀ r', q ≤ r' * T.roundSlots → r ≤ r' := fun r' hr' => Nat.find_min' hex hr'
  obtain ⟨h0, h1⟩ := p0d5c_top_first_time T hT hqr hfirst
  have ha := p0d5c_top_action T hT r
  have har : T.action r ≤ u + ρbar + (FGCompose.P T - 4 * T.delta) := by linarith
  have harD : T.action r ≤ Dl := by linarith
  have hur : u ≤ T.action r := by linarith
  have hpr := frontierSearch_phase_cut R E rho O hp hur harD
  obtain ⟨hc, hlowOr⟩ := common u m (some J) false q Q Qfg r hready hQ hErase hsvc hseed huq hqr
    hfirst hpr
  have hqrT : T.proposal q ≤ (r : Time) * FGCompose.P T := by
    have hqrI : (q : Time) ≤ ((r * T.roundSlots : Nat) : Time) := by exact_mod_cast hqr
    rw [hT.proposal_eq]
    unfold FGCompose.P
    push_cast at hqrI
    nlinarith
  have huvote : u ≤ T.vote (r * T.roundSlots) := by
    rw [hT.vote_eq]
    have := p0d5c_top_slot_time T hT hqr
    linarith
  have hstart : E.t_GST ≤ (r : Time) * FGCompose.P T := hGST.trans (huq.trans hqrT)
  rcases hlowOr hlow with he | ⟨x, K, hx, hK, hKh⟩
  · obtain ⟨A, hAh, hAq⟩ := honestQuorum
    have hA : A ⊆ FGHonestSeats S rho := by
      intro i hi
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, hAh i hi⟩
    have hne : A.Nonempty := by
      by_contra hn
      have he := Finset.not_nonempty_iff_eq_empty.mp hn
      change Ef.q ≤ ∑ i ∈ A, Ef.weight i at hAq
      rw [he, Finset.sum_empty] at hAq
      omega
    obtain ⟨seat, hseat⟩ := hne
    let xh := safetyHolder S rho seat
    have hxh : xh ∈ rho.honest := hAh seat hseat
    obtain ⟨K, nd, j, rSent, a, _, hK, _, hQK, _, _, _⟩ := hc seat (hA hseat)
    have hKheight := (he.choose_spec xh K hxh hK).1
    have hQKfg : FGBlock.Preceq Qfg K := eraseReflect _ _ (hErase ▸ hQK)
    have hKU : (O.height K).T_h = (O.height Qfg).T_h :=
      (cert.height.entry_plateau hQKfg (hlow.trans hKheight.symm)).symm
    let U := (O.height Qfg).T_h
    have hage : T.proposal U.slot ≤ w - 6 * T.delta :=
      hentryAge q Q Qfg hQ hErase huq hgateD hlow
    have heps : epsF T ΔF ≤ FGCompose.P T - 8 * T.delta := by
      have := p0d5c_top_beta T hT hbound
      unfold epsF
      linarith
    have hgateBudget : max (T.action r + Γ T G + 4 * T.delta + epsF T ΔF)
        (T.proposal U.slot + 2 * FGCompose.P T + Γ T G + 2 * T.delta) ≤ Dl := by
      apply max_le
      · linarith
      · linarith
    have hwindow : max ((r : Time) * FGCompose.P T + betaF T ΔF - 4 * T.delta)
        (T.proposal U.slot + 2 * FGCompose.P T - 4 * T.delta) + G ≤ rho.horizon := by
      have hb := p0d5c_top_beta T hT hbound
      apply le_trans _ hp.2.1
      rw [← max_add_add_right]
      apply max_le
      · have hg := (le_max_left _ _).trans hgateBudget
        unfold epsF at hg
        linarith
      · linarith
    obtain ⟨s, X, hnew, _, hlater, hsD, hh⟩ :=
      frontierSearch_age_service_holder R S O T E rho I D Ef
      decodeProposal bodyErase bodyRows blockWireRows parentFG parentHeight validFor fold
      cert.height hA ⟨seat, hseat⟩ hT schedule faultWeight deltaF hdelta gap hJst
      slotProposal read order signer
      sourceParent hδ hbound rowsReceipt progressCoverage hfold hAq he
      (fun i hi => hc i (hA hi))
      ⟨xh, K, hxh, hK, hKU⟩ (entryAgreement r) (sourceSlot r) (ancestorSlot r) hready hstart
      huvote hp hwindow hgateBudget
    have hls : T.proposal l < T.proposal s := by linarith
    exact finishAt hls hnew (hur.trans hlater.le) hsD
      (by simpa only [Nat.sub_add_cancel hp.2.2.1] using hh)
  · let b := (r : Time) * FGCompose.P T + 4 * T.delta
    have hbGST : E.t_GST ≤ b := by dsimp only [b]; linarith
    have hbhor : b + G ≤ rho.horizon := by
      apply le_trans _ hp.2.1
      dsimp only [b]
      linarith
    obtain ⟨s, hloS, hhiS, hslotS⟩ := gap b hbGST hbhor
    have hsD : T.gate s ≤ Dl := by
      rw [hT.gate_eq]
      dsimp only [b] at hhiS
      linarith
    have hsHor : T.proposal s ≤ rho.horizon := by
      rw [hT.gate_eq] at hsD
      linarith [hp.2.1]
    obtain ⟨X, hnew, _⟩ := slotProposal s hslotS (by dsimp only [b] at hloS; linarith) hsHor
    have hslabel : r * T.roundSlots + 2 ≤ s := by
      dsimp only [b] at hloS
      rw [hT.proposal_eq] at hloS
      unfold FGCompose.P at hloS
      have hz : ((r * T.roundSlots : Nat) : Time) + 1 < s := by push_cast; nlinarith
      exact_mod_cast Int.add_one_le_iff.mpr hz
    have hat : T.action r < T.proposal s := by
      have hz : ((r * T.roundSlots + 2 : Nat) : Time) ≤ s := by exact_mod_cast hslabel
      rw [ha, hT.proposal_eq]
      unfold FGCompose.P
      push_cast at hz
      have hm := mul_le_mul_of_nonneg_left hz (show (0 : Time) ≤ 4 * T.delta by linarith)
      have he : (r : Time) * (4 * (T.roundSlots : Time) * T.delta) =
          4 * T.delta * ((r : Time) * T.roundSlots) := by ring
      have he' : 4 * (s : Time) * T.delta = 4 * T.delta * s := by ring
      rw [he, he']
      linarith
    have hpts := frontierSearch_phase_cut R E rho O hp (hur.trans hat.le)
      (by rw [hT.gate_eq] at hsD; linarith)
    have hpath := sourceParent u m (some J) false r s X x K hready hpts huvote hat.le hslabel
      hnew hx hK
    have hPX : FGBlock.Preceq X.parent X := by
      cases X with
      | genesis => exact KitFG.preceq_refl _
      | node P s root body rows => exact KitFG.preceq_parent_node _ _ _ _ _
    have hh : m ≤ (O.height X).h :=
      (hKh ▸ cert.height.h_mono hpath).trans (cert.height.h_mono hPX)
    have hls : T.proposal l < T.proposal s := by linarith
    exact finishAt hls hnew (hur.trans hat.le) hsD hh

include obs cert inv justif keep positive coreLaws erasePreceq in
/-- ROOT-DIGEST W2b. Blueprint 21 HG.3 top J; run 2 R2-b.
DC: SAME keep both E_jF branches. The actual accepted J supplies its age;
no exact-service-to-seed reconstruction or E_jF collapse is used. -/
theorem frontier_hg3_topJ_holder (hT : FGTimingLaws T) (hk : 1 ≤ leaseSlots)
    (crossing : RXing R E rho O) (schedule : V2.D.ScheduleWellFormed E rho)
    (mono : FGRunOrderLaws E rho R)
    (awake : ∀ y ∈ rho.honest, ∀ t, E.t_GST ≤ t → t ≤ rho.horizon →
      E.awake y t = true)
    (joinedTick : ∀ iy y t, y ∈ rho.honest →
      rho.events[iy]? = some (.tick y t) → t ≤ rho.horizon →
      E.t_GST ≤ slotStartZ T (((slotAt T t : Slot) : Int) - 1) →
      joined (Prot.clock (rho.stateBefore E iy y) t) = true)
    (readyCut : ∀ t, Jst ≤ t → E.t_GST ≤ slotStartZ T (((slotAt T t : Slot) : Int) - 1))
    (hServices : ∀ i (ev : V2.Event V Prot.Object) m,
      rho.events[i]? = some ev → Jst ≤ ev.time → 1 ≤ m →
      frontierAtIdx R E rho (i + 1) = m → ev.time + T.delta ≤ rho.horizon →
      PhaseWitnessReceiptScope R E rho O joined receipt (i + 1) m (ev.time + T.delta))
    (receiptHeld : ∀ W d y, y ∈ rho.honest → receipt (R.erase W) d y →
      W ∈ (R.core (rho.stateBeforeTime E d y)).fg.TF)
    (faultWeight : Ef.weightOf (historyFaulty S rho) < Ef.q)
    {G ΔF ρbar : Time} (deltaF : E.Δ ≤ ΔF) (hdelta : E.Δ = T.delta)
    (gap : ∀ t, E.t_GST ≤ t → t + G ≤ rho.horizon →
      ∃ s, t < T.proposal s ∧ T.proposal s ≤ t + G ∧ Gen.V2.Duty.HonestSlot rho I s)
    (hJst : E.t_GST ≤ Jst) (hG : 4 * T.delta ≤ G)
    (slotProposal : PromotionSlotProposal R E rho T I)
    (read : PromotionProposalRead R S E rho O I decodeProposal bodyErase bodyRows parentFG
      parentHeight validFor fold)
    (order : PromotionRowOrder R E rho O I) (signer : PromotionRowSigner S E rho T D)
    (sourceParent : PromotionSourceParent R E rho O T I Jst)
    {deltaT : Nat} (hδ : deltaT = 2 * T.roundSlots) (hbound : LivenessBoundW T ΔF)
    (rowsReceipt : TRowsReceipt R S E rho T blockWireRows ΔF)
    (progressCoverage : ∀ (r height : Nat) (U X : FGBlock (Fin n)),
      BatchPrem R S O T E rho I D Ef decodeProposal bodyErase bodyRows blockWireRows
        parentFG parentHeight validFor ΔF .progress r height U X →
      (O.height X.parent).h = height → ProgressCoveredByChild Ef O.height X U height)
    (hfold : ProgressFoldAdvance Ef O.height deltaT)
    (honestQuorum : ∃ Q : Finset (Fin n),
      (∀ i ∈ Q, safetyHolder S rho i ∈ rho.honest) ∧ Ef.q ≤ Ef.weightOf Q)
    (entryAgreement : ∀ r x y K L, x ∈ rho.honest → y ∈ rho.honest →
      actionSourceFG R E rho T x r = some (some K) →
      actionSourceFG R E rho T y r = some (some L) →
      (O.height K).T_h.root = (O.height L).T_h.root → (O.height K).T_h = (O.height L).T_h)
    (sourceSlot : ∀ r x K, x ∈ rho.honest →
      actionSourceFG R E rho T x r = some (some K) → K.slot ≤ r * T.roundSlots)
    (ancestorSlot : ∀ r x K A, x ∈ rho.honest →
      actionSourceFG R E rho T x r = some (some K) → FGBlock.Preceq A K →
      A.slot ≤ K.slot)
    (eraseReflect : ∀ A B : FGBlock (Fin n), Block.Preceq (R.erase A) (R.erase B) →
      FGBlock.Preceq A B)
    (floor : AttemptProposalFloor R E rho O T I Jst)
    (gateCopy : ∀ u v m J contested q Q, Jst ≤ u →
      PhaseInterval R E rho O u v m J contested →
      FrontierSeedQualification T leaseSlots E.t_GST u q → T.gate q ≤ v →
      HonestProposal E rho I q Q → ∃ i x Qfg, V2.D.Run.idxBefore rho u ≤ i ∧
        i ≤ timeIdx rho v ∧ x ∈ rho.honest ∧
        Qfg ∈ (R.core (rho.stateBefore E i x)).fg.TF ∧ R.erase Qfg = Q)
    (service : ∀ u v m J contested q Q Qfg, Jst ≤ u → HonestProposal E rho I q Q →
      R.erase Qfg = Q → (O.height Qfg).h = m → FrontierProposalService R E rho T q Q →
      FrontierSeedQualification T leaseSlots E.t_GST u q → u ≤ T.proposal q →
      PhaseInterval R E rho O u (T.gate q) m J contested → T.gate q ≤ v →
      v ≤ rho.horizon →
      (∀ i x, timeIdx rho u ≤ i → i ≤ timeIdx rho v → x ∈ rho.honest →
        (R.core (rho.stateBefore E i x)).fg.h_max ≤ m) →
      FrontierLocalServiceFG R S E rho O T I D.heightPair q Q Qfg m v)
    (common : ∀ u m J contested q Q Qfg r, Jst ≤ u → HonestProposal E rho I q Q →
      R.erase Qfg = Q → FrontierProposalService R E rho T q Q →
      FrontierSeedQualification T leaseSlots E.t_GST u q → u ≤ T.proposal q →
      q ≤ r * T.roundSlots → (∀ r', q ≤ r' * T.roundSlots → r ≤ r') →
      PhaseInterval R E rho O u (T.action r) m J contested →
      OpeningCoveredFG R S E rho O.height T D.heightPair (FGHonestSeats S rho) r Q ∧
      ((O.height Qfg).h = m - 1 → OpeningEntry R E rho O.height T r (m - 1) ∨
        ∃ x K, x ∈ rho.honest ∧ actionSourceFG R E rho T x r = some (some K) ∧
          (O.height K).h = m))
    (justifiedSource : ∀ i x, x ∈ rho.honest →
      (R.core (rho.stateBefore E i x)).fg.h_j ≠ 0 →
      ∃ j y r a K, j < i ∧ HonestRowAt S E rho T j y r a ∧
        actionSourceFG R E rho T y r = some (some K) ∧
        (O.height K).T_h = (R.core (rho.stateBefore E i x)).fg.J)
    (parentFrame : ∀ q Q, HonestProposal E rho I q Q → ∃ j,
      rho.events[j]? = some (.tick (V2.D.proposerOf rho I q) (T.proposal q)) ∧
      ∀ Qfg, R.erase Qfg = Q → FGBlock.Preceq
        (O.controls (rho.stateBefore E j (V2.D.proposerOf rho I q))).Z Qfg.parent)
    {i m : Nat} {ev : V2.Event V Prot.Object}
    (hstart : FrontierSearchStart R E rho O T Jst i ev m .topJ)
    (allowance : FrontierRepairAllowance R E rho O T I Jst leaseSlots G ρbar
      (ev.time + 3 * T.delta))
    (hhor : ev.time + E_jF T ΔF G ρbar ≤ rho.horizon) :
    FrontierHG3ResultFG R S E rho O T I D.heightPair Jst leaseSlots i m ev.time
      (ev.time + E_jF T ΔF G ρbar) := by
  obtain ⟨hi, hgst0, _, hfront, hm, hkind⟩ :=
    (FrontierSearchStart_def R E rho O T Jst i ev m .topJ).mp hstart
  have hρ : 0 ≤ ρbar := allowance.1
  have hd := hT.delta_pos
  have hP := frontierSearch_period_bound T hT
  have hΓ := (healing_promotion_gap_remainder T hT G).1
  have hF : 0 ≤ ΔF := by rw [hdelta] at deltaF; linarith
  have heps := p0d5c_top_eps_nonneg T hT hF
  have hleft : ev.time + 3 * T.delta + ρbar + FGCompose.P T + Γ T G + epsF T ΔF ≤
      ev.time + E_jF T ΔF G ρbar := by
    have hb := le_max_left (ρbar + FGCompose.P T + Γ T G + 3 * T.delta + epsF T ΔF)
      (2 * FGCompose.P T + Γ T G - 4 * T.delta)
    unfold E_jF
    linarith only [hb]
  have hright : ev.time + 2 * FGCompose.P T + Γ T G - 4 * T.delta ≤
      ev.time + E_jF T ΔF G ρbar := by
    have hb := le_max_right (ρbar + FGCompose.P T + Γ T G + 3 * T.delta + epsF T ΔF)
      (2 * FGCompose.P T + Γ T G - 4 * T.delta)
    unfold E_jF
    linarith only [hb]
  have hrepair : ev.time + 3 * T.delta + ρbar ≤ ev.time + E_jF T ΔF G ρbar := by linarith
  rcases frontierSearch_first_effective_split R E rho O schedule i
      (ev.time + E_jF T ΔF G ρbar) with hstop | hquiet
  · rcases frontierSearch_classify_stop R E rho O mono hfront hstop with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  obtain ⟨J, hp, _⟩ := healing_settle_start_on (R := R) (E := E) (rho := rho) (O := O)
    (Ef := Ef) (obs := obs) (cert := cert) (inv := inv) (justif := justif) (keep := keep)
    (Jst := Jst) (T := T) (positive := positive) (coreLaws := coreLaws)
    (erasePreceq := erasePreceq) (joined := joined) (receipt := receipt)
    crossing schedule mono hdelta hJst awake joinedTick readyCut hServices receiptHeld
    i ev _ m .topJ hi hgst0 (by linarith) hhor hm hfront hkind hquiet
  have hready : Jst ≤ ev.time + 3 * T.delta := by linarith
  have hage := p0d5c_top_seed_age (R := R) (S := S) (O := O) (T := T) (E := E) (rho := rho)
    (I := I) (Ef := Ef) (Jst := Jst) (obs := obs) (cert := cert) (inv := inv)
    (justif := justif) (keep := keep) (erasePreceq := erasePreceq)
    (joined := joined) (receipt := receipt) hT crossing schedule mono joinedTick
    readyCut hServices receiptHeld justifiedSource sourceSlot ancestorSlot parentFrame hstart
    hquiet hp
  obtain ⟨t, hut, htD, hs⟩ := p0d5c_top_phase_holder (R := R) (S := S) (O := O) (T := T)
    (E := E) (rho := rho) (I := I) (D := D) (Ef := Ef) (decodeProposal := decodeProposal)
    (bodyErase := bodyErase) (bodyRows := bodyRows) (blockWireRows := blockWireRows)
    (parentFG := parentFG) (parentHeight := parentHeight) (validFor := validFor)
    (fold := fold) (Jst := Jst) (leaseSlots := leaseSlots) (obs := obs) (cert := cert)
    (inv := inv) hT hk schedule faultWeight deltaF hdelta gap hJst hG slotProposal read order
    signer sourceParent hδ hbound rowsReceipt progressCoverage hfold honestQuorum
    entryAgreement sourceSlot ancestorSlot coreLaws.erase_inj eraseReflect floor gateCopy
    service common hready hp allowance hrepair hleft hright hage
  exact Or.inr (Or.inr ⟨t, by linarith, htD, hs⟩)

end AvailableChain.FGCompose
end
