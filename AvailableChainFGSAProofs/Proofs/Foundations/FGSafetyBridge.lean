module
public import AvailableChainFGCompose.Proofs.SafetyAccountable
public import AvailableChainFGSAProofs.Proofs.Shared.FGSafetyStore
public import AvailableChainFGSAProofs.Proofs.Shared.FGSafetyScope

public section

/-! FG finality safety, step S4a: the generic accountability results (fields 3,
4 and 5) at the FG-SA reads. `Accountable` imports this module, so the
statements expand `FinalityRunBlock` instead of naming it. -/

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG AvailableChain.FGCompose

variable (p : Params) {In V : Type} [DecidableEq V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

private theorem bridge_proposalErase_some {o : Obj p} {b : Block}
    (h : safetyProposalErase p o = some b) :
    ∃ N, o.payload = .proposal N ∧ N.erase = b := by
  rw [fgsa_safetyProposalErase_def] at h
  cases hp : o.payload with
  | proposal N =>
      simp only [hp, Option.some.injEq] at h
      exact ⟨N, rfl, h⟩
  | _ => simp [hp] at h

private theorem bridge_proposalErase_of {o : Obj p} {N : NamedProposal p.n}
    (ho : o.payload = .proposal N) : safetyProposalErase p o = some N.erase := by
  rw [fgsa_safetyProposalErase_def, ho]

/-- The Compose run block at the FG-SA reads is the body of `FinalityRunBlock`. -/
private theorem bridge_runBlock_iff (K : FGBlock (Fin p.n)) :
    safetyRunBlock (fgsaCoreReads p c) (fgsaSafetyReads p c) E rho K ↔
      ∃ o N, o.payload = Msg.proposal N ∧
        ((∃ x t, V2.D.Run.emits E rho x o t) ∨
          (∃ x t, V2.Event.deliver x o t ∈ rho.events)) ∧
        Block.Preceq (eraseFG K) N.erase := by
  rw [safetyRunBlock_def, fgsaCoreReads_def, fgsaSafetyReads_def]
  constructor
  · rintro ⟨o, b, he, hrun, hKb⟩
    obtain ⟨N, ho, rfl⟩ := bridge_proposalErase_some p he
    exact ⟨o, N, ho, hrun, hKb⟩
  · rintro ⟨o, N, ho, hrun, hKb⟩
    refine ⟨o, N.erase, ?_, hrun, hKb⟩
    exact bridge_proposalErase_of p ho

/-- Field 3 (Compose form) at the FG-SA reads. -/
private theorem bridge_wholeAccountable (hroots : NamedRootCollisionFree p c E rho) :
    SafetyWholeAccountable (fgsaCoreReads p c) (fgsaSafetyReads p c) p.E (finalityView p)
      E rho :=
  safety_run_accountable _ _ _ _ _ E rho _ _ (fgsaCoreLaws p c) (fgsaSafetyStoreLaws p c)
    (fgCertificateLaws p) (fgsaSafetyScopeLaws p c E rho)
    (fgsa_safetyScopedRoots p c E rho hroots)

/-- The all-run bound in expanded FG-SA form is the Compose bound. -/
private theorem bridge_bound_of
    (hb : ∀ K W,
      (∃ o N, o.payload = Msg.proposal N ∧
        ((∃ x t, V2.D.Run.emits E rho x o t) ∨
          (∃ x t, V2.Event.deliver x o t ∈ rho.events)) ∧
        Block.Preceq (eraseFG K) N.erase) →
      (∃ o N, o.payload = Msg.proposal N ∧
        ((∃ x t, V2.D.Run.emits E rho x o t) ∨
          (∃ x t, V2.Event.deliver x o t ∈ rho.events)) ∧
        Block.Preceq (eraseFG W) N.erase) →
      ¬ HasSlashableWeightBetween p.E (chainRows K) (chainRows W)) :
    safetyBound (fgsaCoreReads p c) (fgsaSafetyReads p c) p.E E rho := by
  rw [safetyBound_def]
  exact fun K W hK hW => hb K W ((bridge_runBlock_iff p c E rho K).1 hK)
    ((bridge_runBlock_iff p c E rho W).1 hW)

/-- Two run blocks: slashable weight between their chains, or compatible
finalized targets. -/
theorem fgsa_bridge_runAccountable (hroots : NamedRootCollisionFree p c E rho)
    {K W : FGBlock (Fin p.n)}
    (hK : ∃ o N, o.payload = Msg.proposal N ∧
      ((∃ x t, V2.D.Run.emits E rho x o t) ∨
        (∃ x t, V2.Event.deliver x o t ∈ rho.events)) ∧
      Block.Preceq (eraseFG K) N.erase)
    (hW : ∃ o N, o.payload = Msg.proposal N ∧
      ((∃ x t, V2.D.Run.emits E rho x o t) ∨
        (∃ x t, V2.Event.deliver x o t ∈ rho.events)) ∧
      Block.Preceq (eraseFG W) N.erase) :
    HasSlashableWeightBetween p.E (chainRows K) (chainRows W) ∨
      FGBlock.compatible (finalityView p K).F (finalityView p W).F = true :=
  safety_runBlock_accountable (fgCertificateLaws p) (fgsaSafetyScopeLaws p c E rho)
    (fgsa_safetyScopedRoots p c E rho hroots) ((bridge_runBlock_iff p c E rho K).2 hK)
    ((bridge_runBlock_iff p c E rho W).2 hW)

/-- A non-genesis parent of a run block is in the named scope of the run. -/
theorem fgsa_bridge_parent_scope {K : FGBlock (Fin p.n)}
    (hK : ∃ o N, o.payload = Msg.proposal N ∧
      ((∃ x t, V2.D.Run.emits E rho x o t) ∨
        (∃ x t, V2.Event.deliver x o t ∈ rho.events)) ∧
      Block.Preceq (eraseFG K) N.erase)
    (hne : K.parent ≠ .genesis) :
    RootBlockInRun p c E rho (eraseFG K.parent) := by
  have h := (fgsaSafetyScopeLaws p c E rho).parent_scope K
    ((bridge_runBlock_iff p c E rho K).2 hK) hne
  rw [fgsaCoreReads_def] at h
  exact h

/-- Every block of an honest time read is in the named scope of the run. -/
theorem fgsa_bridge_read_scope (t : Time) (x : V) (hx : x ∈ rho.honest)
    (K : FGBlock (Fin p.n)) (hK : K ∈ (V2.D.Run.readAt E rho t x).st.fg.TF) :
    RootBlockInRun p c E rho (eraseFG K) := by
  have h := safety_read_scope (fgsaCoreLaws p c) (fgsaSafetyStoreLaws p c)
    (fgsaSafetyScopeLaws p c E rho) t x hx K (by rw [fgsaCoreReads_def]; exact hK)
  rw [fgsaCoreReads_def] at h
  exact h

/-- Field 3, event prefixes: two honest stores before any events. -/
theorem fgsa_bridge_stores_accountable (hroots : NamedRootCollisionFree p c E rho)
    (u : V) (hu : u ∈ rho.honest) (v : V) (hv : v ∈ rho.honest) (i j : Nat) :
    HasSlashableWeightBetween p.E
        ((V2.D.Run.stateBefore E rho i u).st.fg.TF.biUnion chainRows)
        ((V2.D.Run.stateBefore E rho j v).st.fg.TF.biUnion chainRows) ∨
      FGBlock.compatible (V2.D.Run.stateBefore E rho i u).st.fg.F
        (V2.D.Run.stateBefore E rho j v).st.fg.F = true := by
  have h := bridge_wholeAccountable p c E rho hroots
  rw [SafetyWholeAccountable_def] at h
  have h' := h.2.1 u hu v hv i j
  rw [safetyRows_def, safetyRows_def, fgsaCoreReads_def] at h'
  exact h'

/-- Field 3, reads: two honest time reads. -/
theorem fgsa_bridge_reads_accountable (hroots : NamedRootCollisionFree p c E rho)
    (u : V) (hu : u ∈ rho.honest) (v : V) (hv : v ∈ rho.honest) (t t' : Time) :
    HasSlashableWeightBetween p.E
        ((V2.D.Run.readAt E rho t u).st.fg.TF.biUnion chainRows)
        ((V2.D.Run.readAt E rho t' v).st.fg.TF.biUnion chainRows) ∨
      FGBlock.compatible (V2.D.Run.readAt E rho t u).st.fg.F
        (V2.D.Run.readAt E rho t' v).st.fg.F = true := by
  have h := bridge_wholeAccountable p c E rho hroots
  rw [SafetyWholeAccountable_def] at h
  have h' := h.2.2 u hu v hv t t'
  rw [safetyRows_def, safetyRows_def, fgsaCoreReads_def] at h'
  exact h'

/-- Field 5: under the all-run bound, any two event prefixes agree. -/
theorem fgsa_bridge_event_agreement (hroots : NamedRootCollisionFree p c E rho)
    (hb : ∀ K W,
      (∃ o N, o.payload = Msg.proposal N ∧
        ((∃ x t, V2.D.Run.emits E rho x o t) ∨
          (∃ x t, V2.Event.deliver x o t ∈ rho.events)) ∧
        Block.Preceq (eraseFG K) N.erase) →
      (∃ o N, o.payload = Msg.proposal N ∧
        ((∃ x t, V2.D.Run.emits E rho x o t) ∨
          (∃ x t, V2.Event.deliver x o t ∈ rho.events)) ∧
        Block.Preceq (eraseFG W) N.erase) →
      ¬ HasSlashableWeightBetween p.E (chainRows K) (chainRows W))
    (i j : Nat) (x y : V) :
    FGBlock.compatible (V2.D.Run.stateBefore E rho i x).st.fg.F
      (V2.D.Run.stateBefore E rho j y).st.fg.F = true := by
  have h := safety_event_agreement _ _ _ _ _ E rho _ _ (fgsaCoreLaws p c)
    (fgsaSafetyStoreLaws p c) (fgCertificateLaws p) (fgsaSafetyScopeLaws p c E rho)
    (fgsa_safetyScopedRoots p c E rho hroots) (bridge_bound_of p c E rho hb) i j x y
  rw [fgsaCoreReads_def] at h
  exact h

/-- Field 4, reads: under the all-run bound, two honest time reads agree. -/
theorem fgsa_bridge_read_agreement (hroots : NamedRootCollisionFree p c E rho)
    (hb : ∀ K W,
      (∃ o N, o.payload = Msg.proposal N ∧
        ((∃ x t, V2.D.Run.emits E rho x o t) ∨
          (∃ x t, V2.Event.deliver x o t ∈ rho.events)) ∧
        Block.Preceq (eraseFG K) N.erase) →
      (∃ o N, o.payload = Msg.proposal N ∧
        ((∃ x t, V2.D.Run.emits E rho x o t) ∨
          (∃ x t, V2.Event.deliver x o t ∈ rho.events)) ∧
        Block.Preceq (eraseFG W) N.erase) →
      ¬ HasSlashableWeightBetween p.E (chainRows K) (chainRows W))
    (u : V) (hu : u ∈ rho.honest) (v : V) (hv : v ∈ rho.honest) (t t' : Time) :
    FGBlock.compatible (V2.D.Run.readAt E rho t u).st.fg.F
      (V2.D.Run.readAt E rho t' v).st.fg.F = true := by
  have h := safety_run_agreement _ _ _ _ _ E rho _ _ (fgsaCoreLaws p c)
    (fgsaSafetyStoreLaws p c) (fgCertificateLaws p) (fgsaSafetyScopeLaws p c E rho)
    (fgsa_safetyScopedRoots p c E rho hroots) (bridge_bound_of p c E rho hb)
  rw [SafetyWholeAgreement_def] at h
  have h' := h.2 u hu v hv t t'
  rw [fgsaCoreReads_def] at h'
  exact h'

end AvailableChain.FGSA.Run
end
