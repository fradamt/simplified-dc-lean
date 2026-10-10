module
public import AvailableChainFGSAProofs.Proofs.Healing.RepairH6S
public import AvailableChainFGSAProofs.Proofs.Healing.SupportPerm

public section

/-! Local last-write split and lease covers for the selected joined-start phase. -/

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG Gen.Pure

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

private theorem repair_last_write_support_at (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) (hs : V2.D.ScheduleWellFormed E rho)
    (writes : ∀ i x (row : Block × Nat × Time),
      row ∈ (storeAt p c E rho i x).base.obligations →
      ∃ j < i, ∃ s B, IsGateTick p c rho j x s ∧ gatePassedAt p c E rho j ∧
        gateResultAt p c E rho j = some (some B) ∧ Block.Preceq row.1 B ∧
        (row.1, row.2.1) ∈ @GridCO.gateWriteKeys GridCO.slowLeasePolicy .root p.toParams.engine p.n
          (actView (clockPre p (storeAt p c E rho j x) (SA.gateTime p.toParams s))) s B ∧
        row.2.2 = SA.gateTime p.toParams s + SA.lifetime p.toParams ∧
        row.2.2 = SA.releaseTime p.toParams (s + p.k) ∧
        ∀ k w C, j < k → k < i → IsGateTick p c rho k x w →
          let pre := clockPre p (storeAt p c E rho k x) (SA.gateTime p.toParams w)
          joinedNow p pre = true →
          GridCO.savedGenuine pre.base w = none →
          SA.Root.confirmationFrom p.toParams (eraseFG pre.fg.F) (actView pre) w = some C →
          (actView pre).obligations.any (fun r => !Block.compatible r.1 C) = false →
          (row.1, row.2.1) ∉ @GridCO.gateWriteKeys GridCO.slowLeasePolicy .root
              p.toParams.engine p.n
            (actView pre) w C)
    {u v : Time} {m bcut : Nat} {J : Option (FGBlock (Fin p.n))} {contested : Bool}
    (_hready : recoveryStart p E ≤ u) (_hphase : PhaseInterval p c E rho u v m J contested)
    (perm : ∀ s B, u ≤ SA.voteTime p.toParams s → SA.gateTime p.toParams s ≤ v →
      PhaseBody p c E rho s B → Transfers p c E rho s B v)
    (hcurrent : u ≤ SA.voteTime p.toParams bcut)
    (hsyncWindow : E.t_GST ≤ SA.voteTime p.toParams (bcut + 1 - p.k)) :
    ∀ i x (row : Block × Nat × Time), i ≤ timeIdx rho v → x ∈ rho.honest →
      row ∈ (storeAt p c E rho i x).base.obligations →
      ∃ j < i, ∃ w C, IsGateTick p c rho j x w ∧ gatePassedAt p c E rho j ∧
        gateResultAt p c E rho j = some (some C) ∧ Block.Preceq row.1 C ∧
        (row.1, row.2.1) ∈ @GridCO.gateWriteKeys GridCO.slowLeasePolicy .root p.toParams.engine p.n
          (actView (clockPre p (storeAt p c E rho j x) (SA.gateTime p.toParams w))) w C ∧
        row.2.2 = SA.gateTime p.toParams w + SA.lifetime p.toParams ∧
        row.2.2 = SA.releaseTime p.toParams (w + p.k) ∧
        (∀ k a D, j < k → k < i → IsGateTick p c rho k x a →
          let pre := clockPre p (storeAt p c E rho k x) (SA.gateTime p.toParams a)
          joinedNow p pre = true →
          GridCO.savedGenuine pre.base a = none →
          SA.Root.confirmationFrom p.toParams (eraseFG pre.fg.F) (actView pre) a = some D →
          (actView pre).obligations.any (fun r => !Block.compatible r.1 D) = false →
          (row.1, row.2.1) ∉ @GridCO.gateWriteKeys GridCO.slowLeasePolicy .root
              p.toParams.engine p.n
            (actView pre) a D) ∧
        ((w < bcut ∧
            row.2.2 ≤ SA.gateTime p.toParams (bcut - 1) + SA.lifetime p.toParams) ∨
          (bcut ≤ w ∧ Transfers p c E rho w row.1 v)) := by
  intro i x row hiv hx hr
  obtain ⟨j, hji, w, C, ht, hpass, hres, hrow, hkey, hd, hq, hlast⟩ := writes i x row hr
  refine ⟨j, hji, w, C, ht, hpass, hres, hrow, hkey, hd, hq, hlast, ?_⟩
  have hd0 := p.deltaPos
  by_cases hwb : w < bcut
  · left
    refine ⟨hwb, ?_⟩
    rw [hd]
    have hc : ((bcut - 1 : Nat) : Int) = (bcut : Int) - 1 := by
      rw [Nat.cast_sub (Nat.lt_of_le_of_lt (Nat.zero_le w) hwb)]
      rfl
    have hw : (w : Int) + 1 ≤ (bcut : Int) := by exact_mod_cast hwb
    change 4 * p.Δ * (w : Int) + 6 * p.Δ + SA.lifetime p.toParams ≤
      4 * p.Δ * ((bcut - 1 : Nat) : Int) + 6 * p.Δ + SA.lifetime p.toParams
    rw [hc]
    nlinarith
  · right
    have hbw : bcut ≤ w := Nat.le_of_not_gt hwb
    refine ⟨hbw, ?_⟩
    have hgv : SA.gateTime p.toParams w ≤ v :=
      (V2.D.Engine.index_lt_read_length_iff hs v ht).mp (hji.trans_le hiv)
    have hu : u ≤ SA.voteTime p.toParams w := by
      refine hcurrent.trans ?_
      change 4 * p.Δ * (bcut : Int) + p.Δ ≤ 4 * p.Δ * (w : Int) + p.Δ
      have hbw' : (bcut : Int) ≤ w := by exact_mod_cast hbw
      nlinarith
    have hwin : E.t_GST ≤ SA.voteTime p.toParams (w + 1 - p.k) := by
      refine hsyncWindow.trans ?_
      change 4 * p.Δ * ((bcut + 1 - p.k : Nat) : Int) + p.Δ ≤
        4 * p.Δ * ((w + 1 - p.k : Nat) : Int) + p.Δ
      have hm : ((bcut + 1 - p.k : Nat) : Int) ≤ ((w + 1 - p.k : Nat) : Int) := by
        exact_mod_cast Nat.sub_le_sub_right (Nat.succ_le_succ hbw) p.k
      nlinarith
    exact perm w row.1 hu hgv
      (healing_support_phaseBody_of_write p c E rho hs hx ht hpass hres hkey hwin)

/-- Local two-lease cover from the actual bounded phase services. -/
theorem repair_lease_cover_two_at [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF)
    (mono : RMonoAll p c E rho) (crossing : RXing p c E rho)
    (writes : ∀ i x (row : Block × Nat × Time),
      row ∈ (storeAt p c E rho i x).base.obligations →
      ∃ j < i, ∃ s B, IsGateTick p c rho j x s ∧ gatePassedAt p c E rho j ∧
        gateResultAt p c E rho j = some (some B) ∧ Block.Preceq row.1 B ∧
        (row.1, row.2.1) ∈ @GridCO.gateWriteKeys GridCO.slowLeasePolicy .root p.toParams.engine p.n
          (actView (clockPre p (storeAt p c E rho j x) (SA.gateTime p.toParams s))) s B ∧
        row.2.2 = SA.gateTime p.toParams s + SA.lifetime p.toParams ∧
        row.2.2 = SA.releaseTime p.toParams (s + p.k) ∧
        ∀ k w C, j < k → k < i → IsGateTick p c rho k x w →
          let pre := clockPre p (storeAt p c E rho k x) (SA.gateTime p.toParams w)
          joinedNow p pre = true →
          GridCO.savedGenuine pre.base w = none →
          SA.Root.confirmationFrom p.toParams (eraseFG pre.fg.F) (actView pre) w = some C →
          (actView pre).obligations.any (fun r => !Block.compatible r.1 C) = false →
          (row.1, row.2.1) ∉ @GridCO.gateWriteKeys GridCO.slowLeasePolicy .root
              p.toParams.engine p.n
            (actView pre) w C)
    {u v : Time} {m : Nat} {J : Option (FGBlock (Fin p.n))} {contested : Bool}
    (hready : recoveryStart p E ≤ u) (hphase : PhaseInterval p c E rho u v m J contested)
    (hServices : SupportPermanenceServices E rho u v m J contested)
    {β : Slot} (hβ : u < SA.proposalTime p.toParams β) {s : Slot}
    (hls : SA.proposalTime p.toParams (β + 2 * p.k - 1) < SA.proposalTime p.toParams s)
    (hvs : SA.voteTime p.toParams s ≤ v) : RepairLeaseCover E rho s := by
  have split : ∀ i x (row : Block × Nat × Time), i ≤ timeIdx rho v → x ∈ rho.honest →
      row ∈ (storeAt p c E rho i x).base.obligations →
      ∃ j < i, ∃ w C, IsGateTick p c rho j x w ∧ gatePassedAt p c E rho j ∧
        gateResultAt p c E rho j = some (some C) ∧ Block.Preceq row.1 C ∧
        ((row.2.2 ≤ SA.voteTime p.toParams (β + 2 * p.k - 1) ∧
          ∀ s, SA.proposalTime p.toParams (β + 2 * p.k - 1) < SA.proposalTime p.toParams s →
            row.2.2 ≤ SA.voteTime p.toParams (s - 1)) ∨
          (β + p.k - 1 ≤ w ∧ Transfers p c E rho w row.1 v)) := by
    have hk := p.kLarge
    have hd := p.deltaPos
    have hwin : β + p.k - 1 + 1 - p.k = β := by
      have key : ∀ b k : Nat, 2 ≤ k → b + k - 1 + 1 - k = b := by
        intro b k hk; omega
      exact key β p.k hk
    have hcur : u ≤ SA.voteTime p.toParams (β + p.k - 1) := by
      refine hβ.le.trans ?_
      change 4 * p.Δ * (β : Int) ≤ 4 * p.Δ * ((β + p.k - 1 : Nat) : Int) + p.Δ
      have h : (β : Int) ≤ ((β + p.k - 1 : Nat) : Int) := by
        exact_mod_cast (show β ≤ β + p.k - 1 from by
          have key : ∀ b k : Nat, 2 ≤ k → b ≤ b + k - 1 := by
            intro b k hk; omega
          exact key β p.k hk)
      nlinarith
    have hsync : E.t_GST ≤ SA.voteTime p.toParams (β + p.k - 1 + 1 - p.k) := by
      rw [hwin]
      refine (by
        have := healing_recovery_start_lower (p := p) E
        linarith [p.deltaPos] : E.t_GST ≤ u).trans (hβ.le.trans ?_)
      change 4 * p.Δ * (β : Int) ≤ 4 * p.Δ * (β : Int) + p.Δ
      linarith
    intro i x row hiv hx hr
    obtain ⟨j, hji, w, C, ht, hpass, hres, hrow, _, hd', _, _, hcase⟩ :=
      repair_last_write_support_at E rho hrec.base.valid.toScheduleWellFormed writes
        hready hphase (fun s B hhead hgate hbody =>
          healing_tPerm_at E rho hrec mono crossing writes hready hphase hServices
            hhead hgate hbody) hcur hsync i x row hiv hx hr
    refine ⟨j, hji, w, C, ht, hpass, hres, hrow, ?_⟩
    rcases hcase with ⟨hwb, _⟩ | hnew
    · left
      have hwl : w + p.k + 1 ≤ β + 2 * p.k - 1 := by
        have e : β + 2 * p.k - 1 = (β + p.k - 1) + p.k := by
          have key : ∀ b k : Nat, 2 ≤ k → b + 2 * k - 1 = (b + k - 1) + k := by
            intro b k hk; omega
          exact key β p.k hk
        rw [e]
        exact Nat.succ_le_of_lt (Nat.add_lt_add_right hwb p.k)
      have hold : row.2.2 ≤ SA.voteTime p.toParams (β + 2 * p.k - 1) :=
        hd' ▸ healing_support_deadline_le_vote p hwl
      exact ⟨hold, fun s hs' => hold.trans (healing_support_vote_before_proposal p hs')⟩
    · exact Or.inr hnew
  exact repair_lease_cover_of_split E rho hrec.base.valid.toScheduleWellFormed
    split hls hvs

/-- Local one-lease cover from the actual bounded phase services. -/
theorem repair_lease_cover_one_at [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF)
    (mono : RMonoAll p c E rho) (crossing : RXing p c E rho)
    (writes : ∀ i x (row : Block × Nat × Time),
      row ∈ (storeAt p c E rho i x).base.obligations →
      ∃ j < i, ∃ s B, IsGateTick p c rho j x s ∧ gatePassedAt p c E rho j ∧
        gateResultAt p c E rho j = some (some B) ∧ Block.Preceq row.1 B ∧
        (row.1, row.2.1) ∈ @GridCO.gateWriteKeys GridCO.slowLeasePolicy .root p.toParams.engine p.n
          (actView (clockPre p (storeAt p c E rho j x) (SA.gateTime p.toParams s))) s B ∧
        row.2.2 = SA.gateTime p.toParams s + SA.lifetime p.toParams ∧
        row.2.2 = SA.releaseTime p.toParams (s + p.k) ∧
        ∀ k w C, j < k → k < i → IsGateTick p c rho k x w →
          let pre := clockPre p (storeAt p c E rho k x) (SA.gateTime p.toParams w)
          joinedNow p pre = true →
          GridCO.savedGenuine pre.base w = none →
          SA.Root.confirmationFrom p.toParams (eraseFG pre.fg.F) (actView pre) w = some C →
          (actView pre).obligations.any (fun r => !Block.compatible r.1 C) = false →
          (row.1, row.2.1) ∉ @GridCO.gateWriteKeys GridCO.slowLeasePolicy .root
              p.toParams.engine p.n
            (actView pre) w C)
    {u v : Time} {m : Nat} {J : Option (FGBlock (Fin p.n))} {contested : Bool}
    (hready : recoveryStart p E ≤ u) (hphase : PhaseInterval p c E rho u v m J contested)
    (hServices : SupportPermanenceServices E rho u v m J contested)
    {b : Slot} (hb : u ≤ SA.voteTime p.toParams b)
    (hwindow : E.t_GST ≤ SA.voteTime p.toParams (b + 1 - p.k)) {s : Slot}
    (hls : SA.proposalTime p.toParams (b + p.k) < SA.proposalTime p.toParams s)
    (hvs : SA.voteTime p.toParams s ≤ v) : RepairLeaseCover E rho s := by
  have split : ∀ i x (row : Block × Nat × Time), i ≤ timeIdx rho v → x ∈ rho.honest →
      row ∈ (storeAt p c E rho i x).base.obligations →
      ∃ j < i, ∃ w C, IsGateTick p c rho j x w ∧ gatePassedAt p c E rho j ∧
        gateResultAt p c E rho j = some (some C) ∧ Block.Preceq row.1 C ∧
        ((row.2.2 ≤ SA.voteTime p.toParams (b + p.k) ∧
          ∀ s, SA.proposalTime p.toParams (b + p.k) < SA.proposalTime p.toParams s →
            row.2.2 ≤ SA.voteTime p.toParams (s - 1)) ∨
          (b ≤ w ∧ Transfers p c E rho w row.1 v)) := by
    intro i x row hiv hx hr
    obtain ⟨j, hji, w, C, ht, hpass, hres, hrow, _, hd', _, _, hcase⟩ :=
      repair_last_write_support_at E rho hrec.base.valid.toScheduleWellFormed writes
        hready hphase (fun s B hhead hgate hbody =>
          healing_tPerm_at E rho hrec mono crossing writes hready hphase hServices
            hhead hgate hbody) hb hwindow i x row hiv hx hr
    refine ⟨j, hji, w, C, ht, hpass, hres, hrow, ?_⟩
    rcases hcase with ⟨hwb, _⟩ | hnew
    · left
      have hwl : w + p.k + 1 ≤ b + p.k := Nat.succ_le_of_lt (Nat.add_lt_add_right hwb p.k)
      have hold : row.2.2 ≤ SA.voteTime p.toParams (b + p.k) :=
        hd' ▸ healing_support_deadline_le_vote p hwl
      exact ⟨hold, fun s hs' => hold.trans (healing_support_vote_before_proposal p hs')⟩
    · exact Or.inr hnew
  exact repair_lease_cover_of_split E rho hrec.base.valid.toScheduleWellFormed
    split hls hvs

end AvailableChain.FGSA.Run
end
