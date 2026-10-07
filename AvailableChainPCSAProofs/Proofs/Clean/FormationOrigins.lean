module
public import AvailableChainPCSAProofs.Proofs.Shared.Certificates
public import AvailableChainPCSAProofs.Proofs.Shared.FormationWindow
public import AvailableChainPCSAProofs.Proofs.Clean.FormationView
public import AvailableChainPCSAProofs.Proofs.Shared.RelayRun

public section

/-! Frozen-PC origins for Formation. Shared stage-1 retention fixes each
frozen row. Its PCs have whole-PC acceptance origins no later than the
freeze. F1 gives the receiver either a held key or a strict earlier handler.
This closes hFrozenPCOrigin at the actual early read. Target-body receipt
and the resulting collection remain separate inputs. -/

open AvailableChain AvailableChain.SimplexFG
namespace AvailableChain.PCSA
private theorem formation_pcs_wellFormed (p : Params) (st : State p.n) (h : Reachable p st) :
    ∀ D ∈ st.pcs, D.wellFormed = true := by
  have hs : CertSafe (fun _ => True) st := by
    induction h with
    | init =>
      rw [CertSafe_def]
      refine ⟨fun _ _ => True.intro, ?_⟩
      intro d hd
      change d ∈ ([] : List (PC p.n)) at hd
      cases hd
    | tick t _ ih => exact clock_certSafe p _ _ t ih
    | deliver o _ ih =>
      exact process_certSafe p _ _ o ih (by intros; trivial)
        (by intros; trivial) (by intros; trivial)
  rw [CertSafe_def] at hs
  exact fun D hD => (hs.2 D hD).1

private theorem formation_freeze_row (p : Params) (st : State p.n) (s : Slot)
    (h : st.pcSnapshot.find? (fun row => row.1 == s) = none) :
    (clock p st (SA.freezeTime p.toParams s)).pcSnapshot.find?
      (fun row => row.1 == s) = some (s, st.pcs) := by
  have hΔ : (0 : Int) < p.Δ := p.deltaPos
  have hf : ((SA.freezeTime p.toParams s - 3 * p.Δ) / (4 * p.Δ)).toNat = s := by
    change ((4 * p.Δ * (s : Int) + 3 * p.Δ - 3 * p.Δ) / (4 * p.Δ)).toNat = s
    rw [add_sub_cancel_right, Int.mul_ediv_cancel_left _ (by omega), Int.toNat_natCast]
  have hz : 0 ≤ SA.freezeTime p.toParams s - 3 * p.Δ := by
    change 0 ≤ 4 * p.Δ * (s : Int) + 3 * p.Δ - 3 * p.Δ
    rw [add_sub_cancel_right]
    positivity
  rw [clock_freeze, clockPre_snapshot]
  simp only [hf, hz, decide_true, BEq.rfl, Bool.and_self, ite_true,
    h, Option.isSome_none, Bool.false_eq_true, ite_false,
    List.find?_append, List.find?_cons]
  rfl
end AvailableChain.PCSA

namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In} {m : FGMode}
/-- Each frozen key comes from acceptance no later than its freeze. -/
theorem pcsa_formation_frozen_pc_origin_valid (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (hBase : Base₂ p c E rho)
    (hFrame : StageOneFrame p c E rho) (x : V) (hx : x ∈ rho.honest)
    (K : Nat) (s : Slot) (C : PC p.n)
    (hC : C ∈ pcSnapshotAt (V2.D.Run.stateBefore E rho K x).st s) :
    ∃ j t D, t ≤ SA.freezeTime p.toParams s ∧ D.slot = C.slot ∧ D.target = C.target ∧
      D.wellFormed = true ∧
      V2.D.Run.acceptsAt E rho j x (⟨.none, .pc D⟩ : Obj p) t := by
  have hlabel : s ∈ (V2.D.Run.stateBefore E rho K x).st.pcSnapshot.map Prod.fst := by
    delta pcSnapshotAt at hC
    cases hr : (V2.D.Run.stateBefore E rho K x).st.pcSnapshot.find? (fun row => row.1 == s) with
    | none => rw [hr] at hC; exact (List.not_mem_nil hC).elim
    | some row =>
      exact List.mem_map.mpr ⟨row, List.mem_of_find?_eq_some hr,
        beq_iff_eq.mp (List.find?_some
          (p := fun r : Slot × List (PC p.n) => r.1 == s) hr)⟩
  obtain ⟨i, hiK, hi⟩ := snapshot_key_origin E rho K x s hlabel
  have hs := snapshot_absent_before_tick E rho hBase.valid.nodup i x s hi
  have hrow : ((V2.D.Run.stateBefore E rho (i + 1) x).st.pcSnapshot.find?
      (fun row => row.1 == s)).isSome := by
    rw [V2.D.Run.stateBefore_succ E rho hi]
    rw [pcsa_tick_step, formation_freeze_row p _ s hs]
    rfl
  have he := ((pcsa_stageOne_mono E rho hBase.noRestart hFrame x hx
    (Nat.succ_le_of_lt hiK)).2 s hrow).1
  rw [he, V2.D.Run.stateBefore_succ E rho hi] at hC
  change C ∈ pcSnapshotAt
    (V2.D.World.step E rho (V2.D.Run.stateBefore E rho i) (.tick x _) x).st s at hC
  rw [pcsa_tick_step, clock_freeze_snapshot p _ s hs, pcsa_clock_pcs] at hC
  obtain ⟨j, hji, D, t, hDs, hDt, hD, ha⟩ := pcsa_keyHeld_accepted E rho hBase hFrame x hx
    C.slot C.target i ((KeyHeld_def _ _ _).mpr ⟨C, hC, rfl, rfl⟩)
  obtain ⟨o, hj, _⟩ := ha.1
  obtain ⟨hjl, hje⟩ := List.getElem?_eq_some_iff.mp hj
  obtain ⟨hil, hie⟩ := List.getElem?_eq_some_iff.mp hi
  have ht := (List.pairwise_iff_getElem.mp hBase.valid.sorted) j i hjl hil hji
  rw [hje, hie] at ht
  exact ⟨j, t, D, V2.D.Engine.time_le_of_key_le _ _ ht, hDs, hDt,
    formation_pcs_wellFormed p _ (pcsa_reachable_stateBefore E rho (j + 1) x) D hD, ha⟩
/-- The original frozen-key origin follows from its valid certificate origin. -/
theorem pcsa_formation_frozen_pc_origin (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (hBase : Base₂ p c E rho)
    (hFrame : StageOneFrame p c E rho) (x : V) (hx : x ∈ rho.honest)
    (K : Nat) (s : Slot) (C : PC p.n)
    (hC : C ∈ pcSnapshotAt (V2.D.Run.stateBefore E rho K x).st s) :
    ∃ j t D, t ≤ SA.freezeTime p.toParams s ∧ D.slot = C.slot ∧ D.target = C.target ∧
      V2.D.Run.acceptsAt E rho j x (⟨.none, .pc D⟩ : Obj p) t := by
  obtain ⟨j, t, D, ht, hs, hb, _, ha⟩ := pcsa_formation_frozen_pc_origin_valid
    E rho hBase hFrame x hx K s C hC
  exact ⟨j, t, D, ht, hs, hb, ha⟩

end AvailableChain.PCSA.Run

namespace AvailableChain.PCSA
private theorem formation_snapshot_label {n : Nat} (st : State n) (s : Slot) (C : PC n)
    (hC : C ∈ pcSnapshotAt st s) : s ∈ st.pcSnapshot.map Prod.fst := by
  delta pcSnapshotAt at hC
  cases hr : st.pcSnapshot.find? (fun row => row.1 == s) with
  | none => rw [hr] at hC; exact (List.not_mem_nil hC).elim
  | some row =>
    exact List.mem_map.mpr ⟨row, List.mem_of_find?_eq_some hr,
      beq_iff_eq.mp (List.find?_some (p := fun r : Slot × List (PC n) => r.1 == s) hr)⟩
private theorem formation_snapshot_before_clock (p : Params) (st : State p.n)
    (s : Slot) (t : Time) (C : PC p.n) (ht : t ≠ SA.freezeTime p.toParams s)
    (hC : C ∈ pcSnapshotAt (clock p st t) s) : C ∈ pcSnapshotAt st s := by
  cases hr : st.pcSnapshot.find? (fun row => row.1 == s) with
  | some row =>
    have hs : (st.pcSnapshot.find? (fun row => row.1 == s)).isSome := by rw [hr]; rfl
    rw [(pcsa_clock_pcSnapshotAt p st t s hs).1] at hC
    exact hC
  | none =>
    rcases clock_snapshot_origin p st t s (formation_snapshot_label _ _ C hC) with hs | hs
    · obtain ⟨row, hrow, he⟩ := List.mem_map.mp hs
      have hh := List.find?_eq_none.mp hr row hrow
      rw [he, BEq.rfl] at hh
      exact (hh rfl).elim
    · exact (ht hs).elim
end AvailableChain.PCSA

namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In} {m : FGMode}
/-- A duty read after another time keeps the old frozen-key origin. -/
theorem pcsa_formation_frozen_pc_origin_read_valid (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (hBase : Base₂ p c E rho)
    (hFrame : StageOneFrame p c E rho) (x : V) (hx : x ∈ rho.honest)
    (s : Slot) (t : Time) (nd : Node p) (C : PC p.n)
    (hr : pcsa_postClock E rho x t = some nd) (ht : t ≠ SA.freezeTime p.toParams s)
    (hC : C ∈ pcSnapshotAt nd.st s) :
    ∃ j u D, u ≤ SA.freezeTime p.toParams s ∧ D.slot = C.slot ∧ D.target = C.target ∧
      D.wellFormed = true ∧
      V2.D.Run.acceptsAt E rho j x (⟨.none, .pc D⟩ : Obj p) u := by
  rw [pcsa_postClock_def] at hr
  obtain ⟨pre, hp, hc⟩ := Option.map_eq_some_iff.mp hr
  rw [pcsa_preTick_def] at hp
  obtain ⟨k, _, he⟩ := Option.map_eq_some_iff.mp hp
  subst pre
  subst nd
  exact pcsa_formation_frozen_pc_origin_valid E rho hBase hFrame x hx k s C
    (formation_snapshot_before_clock p _ s t C ht hC)
end AvailableChain.PCSA.Run

namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] [Fintype V] {c : AppCodec In} {m : FGMode}
omit [Fintype V] in
/-- The original read interface follows from the valid certificate origin. -/
theorem pcsa_formation_frozen_pc_origin_read (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (hBase : Base₂ p c E rho)
    (hFrame : StageOneFrame p c E rho) (x : V) (hx : x ∈ rho.honest)
    (s : Slot) (t : Time) (nd : Node p) (C : PC p.n)
    (hr : pcsa_postClock E rho x t = some nd) (ht : t ≠ SA.freezeTime p.toParams s)
    (hC : C ∈ pcSnapshotAt nd.st s) :
    ∃ j u D, u ≤ SA.freezeTime p.toParams s ∧ D.slot = C.slot ∧ D.target = C.target ∧
      V2.D.Run.acceptsAt E rho j x (⟨.none, .pc D⟩ : Obj p) u := by
  obtain ⟨j, u, D, hu, hs, hb, _, ha⟩ := pcsa_formation_frozen_pc_origin_read_valid
    E rho hBase hFrame x hx s t nd C hr ht hC
  exact ⟨j, u, D, hu, hs, hb, ha⟩

/-- F1 supplies old-PC receipt from the run, without hFrozenPCOrigin. -/
theorem pcsa_formation_frozen_pc_receipt_of_run (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (s : Slot) (N : NamedProposal p.n) (ΔF : Time)
    (h : FormationPreFreezePrem p c E rho s N ΔF) (x y : V) (nd : Node p) (C : PC p.n)
    (hx : x ∈ rho.honest) (hy : y ∈ rho.honest)
    (hr : pcsa_postClock E rho x (SA.earlyTime p.toParams s) = some nd)
    (hFrozen : C ∈ pcSnapshotAt nd.st (s - 1)) :
    (∃ A ∈ (V2.D.Run.stateBeforeTime E rho (SA.proposalTime p.toParams s) y).st.pcs,
      A.slot = C.slot ∧ A.target = C.target) ∨
      ∃ D u k, D.slot = C.slot ∧ D.target = C.target ∧
        u < SA.proposalTime p.toParams s ∧
        V2.D.Run.handlesAt E rho k y (⟨.none, .pc D⟩ : Obj p) u := by
  have ht : SA.earlyTime p.toParams s ≠ SA.freezeTime p.toParams (s - 1) := by
    have hs : ((s - 1 : Nat) : Int) = (s : Int) - 1 := by
      have hnat : s - 1 + 1 = s := Nat.sub_add_cancel h.slotPos
      have hi : ((s - 1 : Nat) : Int) + 1 = (s : Int) := by exact_mod_cast hnat
      omega
    have hd : (0 : Int) < p.Δ := p.deltaPos
    change 4 * p.Δ * (s : Int) + 2 * p.Δ ≠ 4 * p.Δ * ((s - 1 : Nat) : Int) + 3 * p.Δ
    rw [hs]
    nlinarith
  exact pcsa_formation_frozen_pc_receipt E rho s N ΔF h x y nd C hx hy hFrozen
    (fun A hA => pcsa_formation_frozen_pc_origin_read E rho h.base h.frame x hx
      (s - 1) _ nd A hr ht hA)
end AvailableChain.PCSA.Run

end
