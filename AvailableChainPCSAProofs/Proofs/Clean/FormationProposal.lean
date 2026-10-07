module
public import AvailableChainPCSAProofs.Proofs.Shared.FormationWindow
public import AvailableChainPCSAProofs.Proofs.Clean.FormationWalk
public import AvailableChainPCSAProofs.Proofs.Foundations.Duties
public import AvailableChainPCSAProofs.Proofs.Clean.FormationFrame

public section

/-! Exact honest proposer geometry for Formation (pcsa34-r4.3b §5.3). -/

namespace AvailableChain.PCSA

/-- Changing the application value keeps the selected parent and walk inputs. -/
theorem pcsa_formation_propose_parent (p : Params) (st : State p.n) (s app : Nat)
    (N : NamedProposal p.n)
    (h : (propose p st s).map (Run.withApp p app) = some (.proposal N)) :
    N.erase.slot = s ∧ N.erase.parent =
      getHead p st (proposerPC p st) (proposerVotes st s) (proposerSupport st s) ∧
      N.pc = proposerPC p st := by
  obtain ⟨M, hM, hN⟩ := Option.map_eq_some_iff.mp h
  delta propose at hM
  split at hM
  · cases hM
  · obtain ⟨P, hP, hMsg⟩ := Option.map_eq_some_iff.mp hM
    subst M
    change Msg.proposal (namedProposal p P s app _ _ _ _) = Msg.proposal N at hN
    have he := Msg.proposal.inj hN
    subst N
    have hErase : P.erase =
        getHead p st (proposerPC p st) (proposerVotes st s) (proposerSupport st s) := by
      delta namedByErase? at hP
      cases heq : (st.namedBodies.filter (fun X => X.erase ==
          getHead p st (proposerPC p st) (proposerVotes st s)
            (proposerSupport st s))).eraseDups with
      | nil => rw [heq] at hP; cases hP
      | cons A tail =>
        rw [heq] at hP
        cases ht : tail with
        | nil =>
          rw [ht] at hP
          change some A = some P at hP
          cases Option.some.inj hP
          have hm : P ∈ (st.namedBodies.filter (fun X => X.erase ==
              getHead p st (proposerPC p st) (proposerVotes st s)
                (proposerSupport st s))).eraseDups := by
            rw [heq, ht]
            exact List.mem_singleton_self _
          exact beq_iff_eq.mp (List.mem_filter.mp (List.mem_eraseDups.mp hm)).2
        | cons B rest => rw [ht] at hP; cases hP
    exact ⟨rfl, hErase, rfl⟩

end AvailableChain.PCSA

namespace AvailableChain.PCSA.Run

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In} {m : FGMode}

/-- Only the proposal duty uses the proposal signing label of a slot. -/
theorem pcsa_formation_signLabel_prop (d : RunDuty) (s : Slot) :
    d.signLabel = .prop s ↔ d = .propAction s := by
  cases d <;> delta RunDuty.signLabel <;>
    simp only [RunLabel.prop.injEq, RunDuty.propAction.injEq, reduceCtorEq]

/-- An honest emitted proposal has the exact parent selected by its duty. -/
theorem pcsa_formation_emitted_parent (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (s : Slot) (N : NamedProposal p.n)
    (x : V) (t : Time) (k : Nat)
    (hk : rho.events[k]? = some (.tick x t))
    (ho : (⟨.seat (.prop s) ⟨0, Nat.one_pos⟩, .proposal N⟩ : Obj p) ∈
      V2.D.Run.emitsAt E rho k) :
    t = SA.proposalTime p.toParams s ∧ N.erase.slot = s ∧
      N.erase.parent = getHead p (clock p (V2.D.Run.stateBefore E rho k x).st t)
        (proposerPC p (clock p (V2.D.Run.stateBefore E rho k x).st t))
        (proposerVotes (clock p (V2.D.Run.stateBefore E rho k x).st t) s)
        (proposerSupport (clock p (V2.D.Run.stateBefore E rho k x).st t) s) ∧
      N.pc = proposerPC p (clock p (V2.D.Run.stateBefore E rho k x).st t) := by
  rw [(V2.D.Run.step_tick_eq E rho hk).2] at ho
  obtain ⟨_, _, d, hl, ht, ha⟩ :=
    (V2.D.Engine.mem_tick_seat_iff E rho _ x t (.prop s) ⟨0, Nat.one_pos⟩
      (.proposal N)).mp ho
  obtain rfl := (pcsa_formation_signLabel_prop d s).mp hl
  cases m <;>
    change (propose p (clock p (V2.D.Run.stateBefore E rho k x).st t) s).map
      (withApp p (c.app (rho.input x t))) = some (.proposal N) at ha
  all_goals exact ⟨ht.symm, pcsa_formation_propose_parent p _ s _ N ha⟩

variable [Fintype V]

/-- Corrected F4 puts the common base root below the emitted proposal parent. -/
theorem pcsa_formation_base_below_parent (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (s : Slot) (N : NamedProposal p.n) (ΔF : Time)
    (h : FormationPreFreezePrem p c E rho s N ΔF) :
    ∃ nd : Node p, pcsa_postClock E rho
      (V2.D.proposerOf rho (pcsaInterface p c (m := m)).toInterface s)
      (V2.D.proposalTime (pcsaInterface p c (m := m)).toInterface s) = some nd ∧
      N.erase.slot = s ∧
      N.pc = proposerPC p nd.st ∧
      Block.Preceq ((N.pc.map PC.target).getD (eraseFG (controls p nd.st).Z))
        N.erase.parent := by
  obtain ⟨k, hk, hem⟩ := h.proposal.2
  have hd := pcsa_formation_emitted_parent E rho s N _ _ k hk hem
  let nd : Node p := (pcsaWith m p c).clock
    (V2.D.Run.stateBefore E rho k
      (V2.D.proposerOf rho (pcsaInterface p c (m := m)).toInterface s))
    (V2.D.proposalTime (pcsaInterface p c (m := m)).toInterface s)
  have hr : pcsa_postClock E rho
      (V2.D.proposerOf rho (pcsaInterface p c (m := m)).toInterface s)
      (V2.D.proposalTime (pcsaInterface p c (m := m)).toInterface s) = some nd := by
    rw [pcsa_postClock_def, pcsa_preTick_def]
    have hk' := hk
    obtain ⟨j, hj⟩ := Option.isSome_iff_exists.mp
      (show (V2.D.Run.tickIdx? rho
        (V2.D.proposerOf rho (pcsaInterface p c (m := m)).toInterface s)
        (V2.D.proposalTime (pcsaInterface p c (m := m)).toInterface s)).isSome = true from by
        delta V2.D.Run.tickIdx?
        rw [List.findIdx?_isSome, List.any_eq_true]
        refine ⟨_, List.mem_of_getElem? hk', ?_⟩
        exact decide_eq_true ⟨rfl, rfl⟩)
    have he := V2.D.Run.tickIdx?_spec hj
    have heq : j = k := (List.Nodup.getElem?_inj
      (List.getElem?_eq_some_iff.mp he).1 h.base.valid.nodup).mp (he.trans hk.symm)
    rw [heq] at hj
    rw [hj]
    rfl
  have hb := pcsa_formation_proposer_base_walk E rho s N ΔF h nd hr
  have hp : N.erase.parent =
      getHead p nd.st (proposerPC p nd.st) (proposerVotes nd.st s) (proposerSupport nd.st s) :=
    hd.2.2.1
  refine ⟨nd, hr, hd.2.1, hd.2.2.2, ?_⟩
  rw [hd.2.2.2, hp, ← hb]
  exact @GridCO.ghost_extends GridCO.slowLeasePolicy _ _ _ _

/-- The two corrected F4 clauses bound the actual post-release voter root. -/
theorem pcsa_formation_voter_root_below_parent (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (s : Slot) (N : NamedProposal p.n) (ΔF : Time)
    (h : FormationPreFreezePrem p c E rho s N ΔF) (y : V) (nd : Node p)
    (hy : y ∈ rho.honest) (haw : E.awake y (SA.voteTime p.toParams s) = true)
    (hr : pcsa_postClock E rho y (SA.voteTime p.toParams s) = some nd) :
    Block.Preceq (liveRoot p nd.st (voterPC p nd.st s)) N.erase.parent := by
  obtain ⟨src, hs, _, _, hb⟩ := pcsa_formation_base_below_parent E rho s N ΔF h
  have hfSrc := pcsa_formation_frame_read E rho h.frame _ _ src h.proposal.1 hs
  have hfDst := pcsa_formation_frame_read E rho h.frame y _ nd hy hr
  have hv := h.commonView y hy haw
  rw [pcsa_viewAt_def, hr] at hv
  change some ((voterPC p nd.st s).map PC.target) = some (N.pc.map PC.target) at hv
  have ht := Option.some.inj hv
  have he : walkBase p nd.st (voterPC p nd.st s) =
      (N.pc.map PC.target).getD (eraseFG (controls p nd.st).Z) := by
    cases hc : voterPC p nd.st s with
    | none =>
      rw [hc] at ht
      rw [← ht]
      rfl
    | some C =>
      have hm : C ∈ ((pcSnapshotAt nd.st (s - 1) ++ carriedPCs nd.st s).filter
          (frameActive p nd.st)) := bestPC_mem _ C hc
      have ha := (List.mem_filter.mp hm).2
      rw [hc] at ht
      rw [← ht]
      change (if frameActive p nd.st C then C.target else _) = C.target
      rw [ite_eq_left ha]
  apply pcsa_formation_root_below_parent p nd.st (voterPC p nd.st s) N.erase
  · rw [he, hfDst.2.1]
    rw [hfSrc.2.1] at hb
    exact hb
  · intro B hl hc hd
    rw [he] at hc hd
    exact h.leases y hy haw nd hr B hl hc hd

end AvailableChain.PCSA.Run
end
