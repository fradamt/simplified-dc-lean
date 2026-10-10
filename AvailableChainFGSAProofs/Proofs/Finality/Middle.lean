module
public import AvailableChainFGSAProofs.Proofs.Finality.MiddleSupport
public import AvailableChainFGSAProofs.Proofs.Finality.History
public import AvailableChainFGSAProofs.Proofs.Shared.Regimes
public import AvailableChainFGSAProofs.Proofs.Shared.RegimesService

public section

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG AvailableChain.KitFG

/-- FINAL 22:1171–1226 (F1–F5). The opening, middle, fresh entry and early carrier
of one forward window, with the raw cuts that later kernel steps reuse.
DC: INTENTIONAL: the W kernel keeps its chosen witnesses as data. -/
structure KernelMiddleWitness_W
    (p : Params) {In V : Type} [DecidableEq V] [Fintype V]
    (c : AppCodec In) (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c))
    (ΔF : Time) (pt : KernelPt) (A : Block) where
  A₀ : FGBlock (Fin p.n)
  B : FGBlock (Fin p.n)
  U : FGBlock (Fin p.n)
  X_D : FGBlock (Fin p.n)
  cD : Slot
  d : Nat

  opening : HonestProposal E rho (fgsaInterface p c) (pt.r * p.R) A
  eraseA : eraseFG A₀ = A
  carrierA : OpeningCarrier_W p c E rho (pt.r * p.R) A A₀
  carrierB : OpeningCarrier_W p c E rho ((pt.r + 1) * p.R) (eraseFG B) B
  carrierD : OpeningCarrier_W p c E rho cD (eraseFG X_D) X_D
  honestB : HonestProposal E rho (fgsaInterface p c) ((pt.r + 1) * p.R) (eraseFG B)
  honestD : HonestProposal E rho (fgsaInterface p c) cD (eraseFG X_D)
  slotA : A₀.slot = pt.r * p.R
  slotB : B.slot = (pt.r + 1) * p.R
  slotD : X_D.slot = cD
  earlySlot : (pt.r + 1) * p.R + kappaF p ΔF ≤ cD ∧ cD ≤ (pt.r + 2) * p.R

  heightA : (heightView p A₀).h = d
  highA : pt.w.M + 1 ≤ d
  heightB : (heightView p B).h = d + 1
  entryB : (heightView p B).T_h = U
  freshEntry : EntryAt p U (d + 1)
  strictAU : FGBlock.Preceq A₀ U ∧ A₀ ≠ U
  pathUB : FGBlock.Preceq U B
  freshSlot : pt.r * p.R < U.slot ∧ U.slot ≤ (pt.r + 1) * p.R
  parentAB : FGBlock.Preceq A₀ B.parent
  parentBD : FGBlock.Preceq B X_D.parent

  sourceA : ∀ x ∈ rho.honest,
    actionSourceFG p c E rho x pt.r = some (some A₀)
  sourceB : ∀ x ∈ rho.honest,
    actionSourceFG p c E rho x (pt.r + 1) = some (some B)
  serviceD : ExactService p c E rho cD (eraseFG X_D)

  heightD : (heightView p X_D).h = d + 2
  justifiedD : (heightView p X_D).J = U
  justifiedHeightD : (heightView p X_D).h_j = d + 1
  pendingD : (Window.derive p p.K_W X_D).h_F < d + 1
  retainedD : Window.RetainedW p X_D (d + 1) U

  noFirstHeight : ∀ j x q a h t,
    HonestRowAt p c E rho j x q a → rowHeight a = some h →
    d + 1 ≤ h → eventTime rho j = some t →
    p.actionTime (pt.r + 1) ≤ t
  noSecondHeight : ∀ j x q a h t,
    HonestRowAt p c E rho j x q a → rowHeight a = some h →
    d + 2 ≤ h → eventTime rho j = some t →
    p.actionTime (pt.r + 2) ≤ t
  noEarlyFinality : ∀ j x q a h t,
    HonestRowAt p c E rho j x q a → finHeight a = some h →
    d + 1 ≤ h → eventTime rho j = some t →
    p.actionTime (pt.r + 2) ≤ t

  chainA : ChainRowsBefore p c E rho A₀ (p.actionTime pt.r)
  chainB : ChainRowsBefore p c E rho B (p.actionTime (pt.r + 1))
  chainD : ChainRowsBefore p c E rho X_D (p.actionTime (pt.r + 2))
  freshD : FreshPrem p c E rho (pt.r + 1) (d + 1) X_D
  noMixedD : NoMixedOnPath p X_D (d + 1)

  batchB : (heightView p B.parent).h = d →
    BatchPrem p c E rho ΔF .target pt.r d (heightView p A₀).T_h B
  batchD : (heightView p X_D.parent).h = d + 1 →
    BatchPrem p c E rho ΔF .target (pt.r + 1) (d + 1) U X_D

  targetsB : ∀ x ∈ rho.honest, ∃ j a,
    HonestRowAt p c E rho j x (pt.r + 1) a ∧
    RowComplete p c rho x a ∧ NamesEntry p .target a (d + 1) U

  actionsInRun : p.actionTime (pt.r + 2) ≤ rho.horizon
  capThroughBAction : ∀ i x W,
    i ≤ rho.events.length → i ≤ afterTicksIdx rho (p.actionTime (pt.r + 1)) →
    HeldAt p c E rho i x W → (heightView p W).h ≤ d + 1
  capThroughFinalAction : ∀ i x W,
    i ≤ rho.events.length → i ≤ afterTicksIdx rho (p.actionTime (pt.r + 2)) →
    HeldAt p c E rho i x W → (heightView p W).h ≤ d + 2
  finalityThroughFinalAction : ∀ i x W,
    i ≤ rho.events.length → i ≤ afterTicksIdx rho (p.actionTime (pt.r + 2)) →
    HeldAt p c E rho i x W → (finalityView p W).h_F < d + 1
  heldDAtFinalAction : ∀ x ∈ rho.honest,
    X_D ∈ (storeAt p c E rho (afterTicksIdx rho (p.actionTime (pt.r + 2))) x).fg.TF
  heldAAtEnd : ∀ x ∈ rho.honest,
    A₀ ∈ (storeAt p c E rho rho.events.length x).fg.TF

/-- FINAL 22:1171–1226 (F1–F5). The kernel opening, middle block, fresh entry and early
carrier, with their raw history. The Foundation facts are explicit inputs.
DC: INTENTIONAL: Assembly supplies the source names, raw origin, batch coverage and the
FF2 target coverage. -/
theorem kernel_opening_and_middle
    (p : Params) {In V : Type} [DecidableEq V] [Fintype V]
    (c : AppCodec In) (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) (G ΔF : Time) (pt : KernelPt)
    (hδ : p.δt = 2 * p.R)
    (hK : KernelPrem_W p c G ΔF E rho pt)
    (hNames : ∀ j x r a e, HonestRowAt p c E rho j x r a →
      namedEntry a.payload.height_pair = some e →
      ∃ C, actionSourceFG p c E rho x r = some (some C) ∧
        e = ((heightView p C).h, (heightView p C).T_h.root))
    (hOrigin : ∀ (i : Nat) (x : V) (W : FGBlock (Fin p.n)),
      HeldAt p c E rho i x W → ∀ u ∈ chainRows W,
        ∃ (a : RowWire p.n) (r : Nat),
          a.toRow? = some u ∧ a.auth = .seat .fg u.signer ∧
          ∃ k o t, k < i ∧ rho.events[k]? = some (.deliver x o t) ∧
            ∀ z : V, RowSigner p c rho a z → z ∈ rho.honest →
              HonestRowBefore p c E rho i z r a ∧ p.actionTime r ≤ t)
    (hBatch : BatchCoverage p ΔF .target)
    (hSOCOVTarget : ∀ x ∈ rho.honest, ∀ (r : Nat) (C : FGBlock (Fin p.n)),
      actionSourceFG p c E rho x r = some (some C) → high p pt.w C →
      E.awake x (p.actionTime r) = true →
      ∃ j rSent a, rSent ≤ r ∧ HonestRowAt p c E rho j x rSent a ∧
        RowComplete p c rho x a ∧
        a.payload.height_pair = .vote (heightView p C).h (heightView p C).T_h.root false)
    (A : Block)
    (hA : HonestProposal E rho (fgsaInterface p c) (pt.r * p.R) A) :
    Nonempty (KernelMiddleWitness_W p c E rho ΔF pt A) := by
  classical
  obtain ⟨_hF0, hκ2, hκR, hR2, _hs2, hGST, hhorA⟩ := kmid_kernel_bounds hK
  have hs := hK.set.base.valid.toScheduleWellFormed
  have faultQ := hK.set.faultQ
  have hΔ := p.deltaPos
  have laws := (fgCertificateLaws p).height
  have hwin := hK.window
  rw [Gen.Pure.FGoodE_W_def] at hwin
  obtain ⟨hwA, hwB, ⟨cD, hcD1, hcD2, hwD⟩, -⟩ := hwin
  have e1 : (pt.r + 1) * p.R = pt.r * p.R + p.R := Nat.succ_mul _ _
  have e2 : (pt.r + 2) * p.R = pt.r * p.R + 2 * p.R := by ring
  have hcD1' : (pt.r + 1) * p.R + kappaF p ΔF ≤ (cD : Nat) := hcD1
  have hcD2' : (cD : Nat) ≤ (pt.r + 2) * p.R := hcD2
  have n01 : pt.r * p.R ≤ (pt.r + 1) * p.R := by omega
  have n12 : (pt.r + 1) * p.R ≤ (pt.r + 2) * p.R := by omega
  have n02 : pt.r * p.R ≤ (pt.r + 2) * p.R := by omega
  have nA2 : pt.r * p.R + 2 ≤ (pt.r + 1) * p.R := by omega
  have nAκ : pt.r * p.R + kappaF p ΔF ≤ (pt.r + 1) * p.R := by omega
  have nD2 : (pt.r + 1) * p.R + 2 ≤ (cD : Nat) := by omega
  have n0D : pt.r * p.R ≤ (cD : Nat) := by omega
  have hx₀ := hwA.2
  have hGSTr : ∀ r, pt.r ≤ r → E.t_GST ≤ p.actionTime r := fun r hr =>
    hGST.trans (kmid_proposal_le_action p (Nat.mul_le_mul_right _ hr))
  have hawake : ∀ x ∈ rho.honest, ∀ r, pt.r ≤ r → r ≤ pt.r + 2 →
      E.awake x (p.actionTime r) = true := fun x hx r hlo hhi =>
    hK.set.awake x hx _ (hGSTr r hlo)
      (le_trans ((kmid_action_strictMono p).monotone hhi) hhorA)
  -- Step group A: the opening, middle and early proposals.
  obtain ⟨A₀, heA, carrierA, slotA, -, -⟩ := kmid_opening_carrier p c E rho hs hA
  have hA' : HonestProposal E rho (fgsaInterface p c) (pt.r * p.R) (eraseFG A₀) := heA ▸ hA
  have exA := kmid_window_exact hK hA' le_rfl
  have hhA := kmid_slot_horizon hK (s := pt.r * p.R) n02
  have sourceA : ∀ x ∈ rho.honest,
      actionSourceFG p c E rho x pt.r = some (some A₀) := fun x hx =>
    kmid_source_of_exact p c E rho exA hhA.2.2 pt.r rfl x hx
      (kmid_window_confirmed hK le_rfl hhA.2.2 hx)
  obtain ⟨b, hb⟩ := kmid_window_proposal hK hwB n01 n12
  obtain ⟨B, heB, carrierB, slotB, ⟨rowsB, hcarB, hrowsB⟩, stB, hstB, hlookB, hparTFB⟩ :=
    kmid_opening_carrier p c E rho hs hb
  subst heB
  have exB := kmid_window_exact hK hb n01
  have hhB := kmid_slot_horizon hK (s := (pt.r + 1) * p.R) n12
  have sourceB : ∀ x ∈ rho.honest,
      actionSourceFG p c E rho x (pt.r + 1) = some (some B) := fun x hx =>
    kmid_source_of_exact p c E rho exB hhB.2.2 (pt.r + 1) rfl x hx
      (kmid_window_confirmed hK n01 hhB.2.2 hx)
  obtain ⟨xd, hxd⟩ := kmid_window_proposal hK hwD n0D hcD2
  obtain ⟨X_D, heD, carrierD, slotD, ⟨rowsD, hcarD, hrowsD⟩, stD, hstD, hlookD, hparTFD⟩ :=
    kmid_opening_carrier p c E rho hs hxd
  subst heD
  have exD := kmid_window_exact hK hxd n0D
  have hhD := kmid_slot_horizon hK hcD2
  -- Step 4: the opening is high.
  obtain ⟨_, y₀, _, C₀, hrow₀, -, hsrc₀, -, hC₀⟩ := hK.input.wit.fresh
  have hpre := hK.input.t.h2 y₀ pt.w.rStar C₀ (pt.r * p.R) (eraseFG A₀)
    ((HonestRowAt_def p c E rho _ _ _ _).mp hrow₀).1 hsrc₀
    (show pt.w.M + 1 ≤ (heightView p C₀).h by rw [hC₀]) hA'
    (by rw [← hK.input.wit.label]; exact _hs2)
  rw [eraseFG_parent] at hpre
  have highA : pt.w.M + 1 ≤ (heightView p A₀).h := by
    have h1 := laws.h_mono (kmid_lift_preceq p hpre)
    have h2 := laws.h_mono (kmid_parent_preceq p A₀)
    rw [hC₀] at h1
    exact h1.trans h2
  -- Step 6–8: rows through action q and the first raw cut.
  have rowsQ : ∀ j x r a h, r ≤ pt.r → HonestRowAt p c E rho j x r a →
      rowHeight a = some h → h ≤ (heightView p A₀).h := by
    intro j x r a h hr ha hh
    rcases Nat.lt_or_ge r pt.r with hlt | hge
    · exact kmid_rows_below_opening p c E rho pt.w hK.input.t.h2 hNames pt.r A₀ hA' highA
        j x r a h hlt ha hh
    · obtain rfl : r = pt.r := le_antisymm hr hge
      exact (kmid_rows_at_source p c E rho hNames pt.r A₀ sourceA j x a h ha hh).le
  obtain ⟨noFirstHeight, rowsBeforeB⟩ :=
    kmid_rows_cut p c E rho (heightView p A₀).h pt.r rowsQ
  have capB : ∀ i x W, i ≤ afterTicksIdx rho (p.actionTime (pt.r + 1)) →
      HeldAt p c E rho i x W → (heightView p W).h ≤ (heightView p A₀).h + 1 :=
    fun i x W hi hW => kmid_held_cap_afterTicks p c E rho hOrigin hK.set.base faultQ _ _
      rowsBeforeB i x W hi hW
  -- Step 10: the middle height.
  obtain ⟨iB, hiB, hBTF⟩ := kmid_head_held p c E rho exB hhB.2.1 _ hwB.2
    (kmid_window_joined hK n01 n12 hwB.2)
  have hBup : (heightView p B).h ≤ (heightView p A₀).h + 1 :=
    capB iB _ B ((kmid_tick_lt_afterTicks p c E rho hs hiB
      (kmid_vote_lt_action p (le_refl ((pt.r + 1) * p.R))).le).le) ⟨hwB.2, hBTF⟩
  have hpAB := hK.input.t.h2 _ pt.r A₀ ((pt.r + 1) * p.R) (eraseFG B) hx₀
    (sourceA _ hx₀) highA hb nA2
  rw [eraseFG_parent] at hpAB
  have parentAB := kmid_lift_preceq p hpAB
  have hBne : B ≠ .genesis := by
    intro h
    rw [h] at slotB
    have h0 : (0 : Nat) = (pt.r + 1) * p.R := slotB
    omega
  have hparLow : (heightView p A₀).h ≤ (heightView p B.parent).h := laws.h_mono parentAB
  have entryA : EntryAt p (heightView p A₀).T_h (heightView p A₀).h :=
    ⟨laws.entry_same_height A₀, laws.entry_idem A₀⟩
  have pathA : FGBlock.Preceq (heightView p A₀).T_h B.parent :=
    preceq_trans (laws.entry_preceq A₀) parentAB
  have batchB : (heightView p B.parent).h = (heightView p A₀).h →
      BatchPrem p c E rho ΔF .target pt.r (heightView p A₀).h (heightView p A₀).T_h B := by
    intro hpar
    refine kmid_batchPrem p c E rho ΔF hK.set.base faultQ hK.set.fault hK.set.deltaF
      hK.input.t.rows.receipt pt.r _ _ B ?_ ⟨rowsB, by rw [slotB]; exact hcarB, hrowsB⟩ stB
      (by rw [slotB]; exact hstB) hlookB hparTFB (by rw [slotB]; exact nA2) entryA pathA hpar ?_
    · rw [slotB]
      exact kmid_batch_horizon hK (hGSTr _ le_rfl) nAκ n12
    · intro x hx
      obtain ⟨j, rS, a, hle, ha, hc, hp⟩ := hSOCOVTarget x hx pt.r A₀ (sourceA x hx) highA
        (hawake x hx _ le_rfl (by omega))
      exact ⟨j, rS, a, hle, ha, hc, hp⟩
  have hBlow : (heightView p A₀).h + 1 ≤ (heightView p B).h := by
    rcases Nat.eq_or_lt_of_le hparLow with heq | hlt
    · have htri := fgsa_foldTrichotomy_target p
      rw [foldTrichotomy_def] at htri
      exact (htri _ _ B hBne entryA pathA
        (fun h => hBatch c E rho pt.r _ _ B (batchB h) h) (fun h => by cases h)).1
    · exact hlt.trans_le (laws.h_mono (kmid_parent_preceq p B))
  have heightB : (heightView p B).h = (heightView p A₀).h + 1 := le_antisymm hBup hBlow
  -- Step 11: the fresh entry.
  have entryU : EntryAt p (heightView p B).T_h ((heightView p A₀).h + 1) :=
    ⟨(laws.entry_same_height B).trans heightB, laws.entry_idem B⟩
  have pathUB : FGBlock.Preceq (heightView p B).T_h B := laws.entry_preceq B
  have slotChainB := kmid_stored_slotChain p c E rho hK.set.base.valid iB _ B hBTF
  have hA₀B : FGBlock.Preceq A₀ B := preceq_trans parentAB (kmid_parent_preceq p B)
  have strictAU : FGBlock.Preceq A₀ (heightView p B).T_h ∧ A₀ ≠ (heightView p B).T_h := by
    rcases preceq_total_of_common hA₀B pathUB with h | h
    · refine ⟨h, ?_⟩
      intro he
      have h1 := entryU.1
      rw [← he] at h1
      exact Nat.succ_ne_self _ h1.symm
    · exfalso
      have h1 := laws.h_mono h
      rw [entryU.1] at h1
      exact Nat.not_succ_le_self _ h1
  have freshSlot : pt.r * p.R < ((heightView p B).T_h).slot ∧
      ((heightView p B).T_h).slot ≤ (pt.r + 1) * p.R := by
    have hUc : SlotChain (heightView p B).T_h := fun W hW hg =>
      slotChainB W (preceq_trans hW pathUB) hg
    exact ⟨slotA ▸ kmid_slot_lt_of_strict p hUc strictAU.1 strictAU.2,
      slotB ▸ kmid_slot_le_of_preceq p slotChainB pathUB⟩
  -- Step 12: fresh targets at action q+1.
  have highB : high p pt.w B := by
    change pt.w.M + 1 ≤ (heightView p B).h
    rw [heightB]
    exact highA.trans (Nat.le_succ _)
  have targetsB : ∀ x ∈ rho.honest, ∃ j a,
      HonestRowAt p c E rho j x (pt.r + 1) a ∧ RowComplete p c rho x a ∧
      NamesEntry p .target a ((heightView p A₀).h + 1) (heightView p B).T_h := by
    intro x hx
    obtain ⟨j, rS, a, hle, ha, hc, hp⟩ := hSOCOVTarget x hx (pt.r + 1) B (sourceB x hx) highB
      (hawake x hx _ (by omega) (by omega))
    have hrS : rS = pt.r + 1 := by
      by_contra hne
      have hlt : rS < pt.r + 1 := lt_of_le_of_ne hle hne
      have hh : rowHeight a = some ((heightView p A₀).h + 1) := by
        have hdef : rowHeight a = (match a.payload.height_pair with
            | .empty => none | .vote h _ _ => some h) := rfl
        rw [hdef, hp, heightB]
      have hlate := noFirstHeight j x rS a _ _ ha hh le_rfl (kmid_event_time p c E rho ha)
      exact absurd ((kmid_action_strictMono p).lt_iff_lt.mpr hlt) (not_lt.mpr hlate)
    subst hrS
    refine ⟨j, a, ha, hc, ?_⟩
    change a.payload.height_pair = .vote _ _ false
    rw [hp, heightB]
  -- Step 12: rows through action q+1 and the second raw cut.
  have rowsQ1 : ∀ j x r a h, r ≤ pt.r + 1 → HonestRowAt p c E rho j x r a →
      rowHeight a = some h → h ≤ (heightView p A₀).h + 1 := by
    intro j x r a h hr ha hh
    rcases Nat.lt_or_ge r (pt.r + 1) with hlt | hge
    · exact (rowsQ j x r a h (Nat.le_of_lt_succ hlt) ha hh).trans (Nat.le_succ _)
    · obtain rfl : r = pt.r + 1 := le_antisymm hr hge
      rw [kmid_rows_at_source p c E rho hNames _ B sourceB j x a h ha hh, heightB]
  obtain ⟨noSecondHeight, rowsBeforeD⟩ :=
    kmid_rows_cut p c E rho ((heightView p A₀).h + 1) (pt.r + 1) rowsQ1
  obtain ⟨noEarlyFinality, finBeforeD⟩ :=
    kmid_fin_cut p c E rho ((heightView p A₀).h + 1) (pt.r + 1) rowsQ1
  -- Step 13: the early carrier is above B.
  have hpBD := hK.input.t.h2 _ (pt.r + 1) B cD (eraseFG X_D) hx₀ (sourceB _ hx₀) highB hxd
    nD2
  rw [eraseFG_parent] at hpBD
  have parentBD := kmid_lift_preceq p hpBD
  have pathUD : FGBlock.Preceq (heightView p B).T_h X_D.parent := preceq_trans pathUB parentBD
  obtain ⟨iD, _hiD, hDTF⟩ := kmid_head_held p c E rho exD hhD.2.1 _ hwD.2
    (kmid_window_joined hK n0D hcD2 hwD.2)
  have slotChainD := kmid_stored_slotChain p c E rho hK.set.base.valid iD _ X_D hDTF
  have hDne : X_D ≠ .genesis := by
    intro h
    rw [h] at slotD
    have h0 : (0 : Nat) = cD := slotD
    omega
  have hmat : X_D.slot < ((heightView p B).T_h).slot + p.δt + 1 := by
    have hU : pt.r * p.R < ((heightView p B).T_h).slot := freshSlot.1
    rw [slotD, hδ]
    refine lt_of_le_of_lt hcD2' ?_
    rw [e2]
    exact Nat.lt_succ_of_lt (Nat.add_lt_add_right hU _)
  have noMixedD : NoMixedOnPath p X_D ((heightView p A₀).h + 1) :=
    fgsa_noMixedMaturity p _ _ X_D slotChainD entryU pathUD hmat
  -- Step 17: raw chain rows through each carrier.
  have chainA : ChainRowsBefore p c E rho A₀ (p.actionTime pt.r) :=
    kmid_chainRows_of_head p c E rho hs exA hhA.2.1 _ hx₀
      (kmid_window_joined hK le_rfl n02 hx₀) _ (kmid_vote_lt_action p le_rfl)
  have chainB : ChainRowsBefore p c E rho B (p.actionTime (pt.r + 1)) :=
    kmid_chainRows_of_head p c E rho hs exB hhB.2.1 _ hx₀
      (kmid_window_joined hK n01 n12 hx₀) _ (kmid_vote_lt_action p le_rfl)
  have chainD : ChainRowsBefore p c E rho X_D (p.actionTime (pt.r + 2)) :=
    kmid_chainRows_of_head p c E rho hs exD hhD.2.1 _ hx₀
      (kmid_window_joined hK n0D hcD2 hx₀) _ (kmid_vote_lt_action p hcD2)
  -- Step 15: the early batch.
  have batchD : (heightView p X_D.parent).h = (heightView p A₀).h + 1 →
      BatchPrem p c E rho ΔF .target (pt.r + 1) ((heightView p A₀).h + 1)
        (heightView p B).T_h X_D := by
    intro hpar
    refine kmid_batchPrem p c E rho ΔF hK.set.base faultQ hK.set.fault hK.set.deltaF
      hK.input.t.rows.receipt (pt.r + 1) _ _ X_D ?_ ⟨rowsD, by rw [slotD]; exact hcarD, hrowsD⟩
      stD (by rw [slotD]; exact hstD) hlookD hparTFD (by rw [slotD]; exact nD2) entryU pathUD
      hpar ?_
    · rw [slotD]
      exact kmid_batch_horizon hK (hGSTr _ (by omega)) hcD1 hcD2
    · intro x hx
      obtain ⟨j, a, ha, hc, hn⟩ := targetsB x hx
      exact ⟨j, pt.r + 1, a, le_rfl, ha, hc, hn⟩
  -- Step 18: the fresh pending justification.
  let freshD : FreshPrem p c E rho (pt.r + 1) ((heightView p A₀).h + 1) X_D :=
    ⟨hK.set.base, faultQ, p.actionTime (pt.r + 2), le_rfl, chainD, noSecondHeight,
      noEarlyFinality⟩
  obtain ⟨heightD, justifiedD, justifiedHeightD, pendingD, retainedD⟩ :=
    justifyFresh_W p c E rho hOrigin (pt.r + 1) _ _ X_D hDne entryU pathUD
      (fun h => hBatch c E rho (pt.r + 1) _ _ X_D (batchD h) h) noMixedD freshD
  -- Step 19: the package.
  exact ⟨{
    A₀ := A₀
    B := B
    U := (heightView p B).T_h
    X_D := X_D
    cD := cD
    d := (heightView p A₀).h
    opening := hA
    eraseA := heA
    carrierA := carrierA
    carrierB := carrierB
    carrierD := carrierD
    honestB := hb
    honestD := hxd
    slotA := slotA
    slotB := slotB
    slotD := slotD
    earlySlot := ⟨hcD1, hcD2⟩
    heightA := rfl
    highA := highA
    heightB := heightB
    entryB := rfl
    freshEntry := entryU
    strictAU := strictAU
    pathUB := pathUB
    freshSlot := freshSlot
    parentAB := parentAB
    parentBD := parentBD
    sourceA := sourceA
    sourceB := sourceB
    serviceD := exD
    heightD := heightD
    justifiedD := justifiedD
    justifiedHeightD := justifiedHeightD
    pendingD := pendingD
    retainedD := retainedD
    noFirstHeight := noFirstHeight
    noSecondHeight := noSecondHeight
    noEarlyFinality := noEarlyFinality
    chainA := chainA
    chainB := chainB
    chainD := chainD
    freshD := freshD
    noMixedD := noMixedD
    batchB := batchB
    batchD := batchD
    targetsB := targetsB
    actionsInRun := hhorA
    capThroughBAction := fun i x W _ hi hW => capB i x W hi hW
    capThroughFinalAction := fun i x W _ hi hW =>
      kmid_held_cap_afterTicks p c E rho hOrigin hK.set.base faultQ _ _ rowsBeforeD i x W hi hW
    finalityThroughFinalAction := fun i x W _ hi hW =>
      kmid_held_finality_afterTicks p c E rho hOrigin hK.set.base faultQ _ _ (Nat.succ_pos _)
        finBeforeD i x W hi hW
    heldDAtFinalAction := fun x hx =>
      kmid_head_held_from p c E rho hs exD hhD.2.1 x hx
        (kmid_window_joined hK n0D hcD2 hx) _ _
        (kmid_vote_lt_action p hcD2).le le_rfl
    heldAAtEnd := fun x hx =>
      kmid_head_held_from p c E rho hs exA hhA.2.1 x hx
        (kmid_window_joined hK le_rfl n02 hx) _ _ le_rfl
        (List.length_filter_le _ _) }⟩

/-- FINAL 22:1199–1206 (F2). The fresh entry of the middle block, as kept in the witness.
DC: INTENTIONAL: a projection, not a new choice of the fresh entry. -/
theorem kernel_middle_fresh_U
    (p : Params) {In V : Type} [DecidableEq V] [Fintype V]
    (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (ΔF : Time) (pt : KernelPt) (A : Block)
    (m : KernelMiddleWitness_W p c E rho ΔF pt A) :
    FGBlock.Preceq m.A₀ m.U ∧ m.A₀ ≠ m.U ∧
    (heightView p m.U).h = (heightView p m.A₀).h + 1 ∧
    FGBlock.Preceq m.U m.B := by
  refine ⟨m.strictAU.1, m.strictAU.2, ?_, m.pathUB⟩
  rw [m.freshEntry.1, m.heightA]

/-- FINAL 22:1218–1226 (F5). The pending justification of the early carrier.
DC: INTENTIONAL: a projection, not a new choice of the pending pair. -/
theorem kernel_middle_early_justification
    (p : Params) {In V : Type} [DecidableEq V] [Fintype V]
    (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (ΔF : Time) (pt : KernelPt) (A : Block)
    (m : KernelMiddleWitness_W p c E rho ΔF pt A) :
    (heightView p m.X_D).h = m.d + 2 ∧
    (heightView p m.X_D).J = m.U ∧
    (heightView p m.X_D).h_j = m.d + 1 ∧
    (Window.derive p p.K_W m.X_D).h_F < m.d + 1 ∧
    Window.RetainedW p m.X_D (m.d + 1) m.U :=
  ⟨m.heightD, m.justifiedD, m.justifiedHeightD, m.pendingD, m.retainedD⟩

/-- FINAL 22:1265–1304. An honest source at action q+2 is at most d+2 high. Its own
action tick is a held read before the read-phase cut of that action.
DC: INTENTIONAL: the receipt Assembly reads the round-(q+2) source cap here. -/
theorem kernel_middle_source_cap
    (p : Params) {In V : Type} [DecidableEq V] [Fintype V]
    (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (ΔF : Time) (pt : KernelPt) (A : Block)
    (m : KernelMiddleWitness_W p c E rho ΔF pt A)
    (hs : V2.D.ScheduleWellFormed E rho) {x : V} {C : FGBlock (Fin p.n)}
    (hx : x ∈ rho.honest)
    (hsrc : actionSourceFG p c E rho x (pt.r + 2) = some (some C)) :
    (heightView p C).h ≤ m.d + 2 := by
  obtain ⟨i, hi, hcut, hheld⟩ := kmid_source_held_at_tick p c E rho hs hx hsrc
  exact m.capThroughFinalAction i x C (List.getElem?_eq_some_iff.mp hi).1.le hcut.le hheld

end AvailableChain.FGSA.Run
end
