module
public import AvailableChainFGCompose.Statements.SafetyOrigin
public import AvailableChainFGCompose.Proofs.SafetyAccountable
public import AvailableChainFGCompose.Proofs.SafetySlashing

public section

/-! The safety consumers under the origin laws. A delivery can admit the delivered body
and bodies that were pending. Each stored non-genesis block still has a delivery to the
same node with its erasure and rows, so the conclusions of the consumers do not change. -/

namespace AvailableChain.FGCompose
open AvailableChain.SimplexFG AvailableChain.KitFG
variable {In V : Type} {P : V2.ProtocolSpecD In}
variable {n : Nat} {Base Proposal Wire : Type}
variable {R : FGCoreReads P n Base Proposal Wire} {S : FGSafetyReads P n Wire}
variable {Ef : Electorate (Fin n)} {H : FGHeightView (Fin n)} {f : FGFinalityView (Fin n)}
variable {cfg : FGConfig}
variable [DecidableEq V] {E : Generic.Env V} {rho : V2.D.Run V P}
variable {Good : P.State → Prop} {pending : P.State → P.Object → Prop} {Q : Block → Prop}

/-- The frozen record implies the origin record, with no pending object: the one new block
of a delivery has the delivered object as its origin. The converse does not hold. -/
theorem safetyStoreOriginLaws_of_storeLaws (L : FGSafetyStoreLaws R S H f Good) :
    FGSafetyStoreOriginLaws R S H f Good (fun _ _ => False) where
  initial_good := L.initial_good
  clock_good := L.clock_good
  process_good := L.process_good
  own_good := L.own_good
  restart_good := L.restart_good
  invariant := L.invariant
  initial_tf := L.initial_tf
  restart_tf := L.restart_tf
  process_origin := fun nd o B hg hB hold =>
    ⟨o, Or.inl rfl, L.process_new nd o B hg hB hold⟩
  pending_origin := ⟨fun _ h => h, fun _ _ _ _ h => h, fun _ _ _ _ h => h.elim,
    fun _ _ _ _ h => h, fun _ _ _ _ h => h⟩

/-- The shared origin lemma under the origin record: every prefix state is `Good`, each
stored block is genesis or was delivered to the same node, and each pending object was
delivered to the same node. -/
theorem safety_origin_stateBefore (C : FGCoreLaws R)
    (L : FGSafetyStoreOriginLaws R S H f Good pending)
    (E : Generic.Env V) (rho : V2.D.Run V P) (i : Nat) (x : V) :
    Good (V2.D.Run.stateBefore E rho i x) ∧
      (∀ B ∈ (R.core (V2.D.Run.stateBefore E rho i x)).fg.TF, B = .genesis ∨
        ∃ o t, V2.Event.deliver x o t ∈ rho.events ∧
          S.proposalErase o = some (R.erase B) ∧
          B.rows = (S.proposalRows o).filterMap S.decode) ∧
      ∀ q, pending (V2.D.Run.stateBefore E rho i x) q →
        ∃ t, V2.Event.deliver x q t ∈ rho.events := by
  obtain ⟨pInit, pClock, pProcess, pOwn, pRestart⟩ := L.pending_origin
  let M : P.State → Prop := fun st => Good st ∧
    (∀ B ∈ (R.core st).fg.TF, B = .genesis ∨
      ∃ o t, V2.Event.deliver x o t ∈ rho.events ∧
        S.proposalErase o = some (R.erase B) ∧
        B.rows = (S.proposalRows o).filterMap S.decode) ∧
    ∀ q, pending st q → ∃ t, V2.Event.deliver x q t ∈ rho.events
  refine V2.D.Engine.stateBefore_step_induction E rho M (Nat.zero_le i) x ?_
    ⟨L.initial_good, fun B hB => Or.inl (L.initial_tf B hB), fun q hq => (pInit q hq).elim⟩
  intro k e _ _ he hv hk
  obtain ⟨hg, htf, hpend⟩ := hk
  cases e with
  | restart u t =>
    change u = x at hv
    subst u
    have hM : M (P.restore (P.durable (V2.D.Run.stateBefore E rho k x)) t) :=
      ⟨L.restart_good _ t hg, fun B hB => htf B (L.restart_tf _ t B hg hB),
        fun q hq => hpend q (pRestart _ t q hg hq)⟩
    change M (Function.update (V2.D.Run.stateBefore E rho k) x _ x)
    rw [Function.update_self]
    exact hM
  | tick u t =>
    change u = x at hv
    subst u
    have hown : ∀ st o, M st → M (P.recordOwn st o) := by
      intro st o hst
      refine ⟨L.own_good st o hst.1, ?_, fun q hq => hst.2.2 q (pOwn st o q hst.1 hq)⟩
      rw [C.own_core]
      exact hst.2.1
    have hclock : M (P.clock (V2.D.Run.stateBefore E rho k x) t) := by
      refine ⟨L.clock_good _ t hg, ?_, fun q hq => hpend q (pClock _ t q hg hq)⟩
      rw [C.clock_fg]
      exact htf
    change M (Function.update (V2.D.Run.stateBefore E rho k) x _ x)
    rw [Function.update_self]
    exact V2.D.Engine.tick_preserve E rho M hown hclock
  | deliver u o t =>
    change u = x at hv
    subst u
    have hM : M (P.process (V2.D.Run.stateBefore E rho k x) o) := by
      refine ⟨L.process_good _ o hg, fun B hB => ?_, fun q hq => ?_⟩
      · by_cases hold : B ∈ (R.core (V2.D.Run.stateBefore E rho k x)).fg.TF
        · exact htf B hold
        · obtain ⟨origin, hsource, hp, hrows⟩ := L.process_origin _ o B hg hB hold
          rcases hsource with rfl | hwaiting
          · exact Or.inr ⟨origin, t, List.mem_of_getElem? he, hp, hrows⟩
          · obtain ⟨t', hd⟩ := hpend origin hwaiting
            exact Or.inr ⟨origin, t', hd, hp, hrows⟩
      · rcases pProcess _ o q hg hq with hold | rfl
        · exact hpend q hold
        · exact ⟨t, List.mem_of_getElem? he⟩
    change M (Function.update (V2.D.Run.stateBefore E rho k) x _ x)
    rw [Function.update_self]
    exact hM

private theorem safety_origin_good_readAt (C : FGCoreLaws R)
    (L : FGSafetyStoreOriginLaws R S H f Good pending)
    (E : Generic.Env V) (rho : V2.D.Run V P) (t : Time) (x : V) :
    Good (V2.D.Run.readAt E rho t x) := by
  obtain ⟨rho', -, h⟩ := safety_readAt_replay E rho t
  rw [h]
  exact (safety_origin_stateBefore C L E rho' _ x).1

private theorem safety_origin_read_delivery (C : FGCoreLaws R)
    (L : FGSafetyStoreOriginLaws R S H f Good pending)
    (E : Generic.Env V) (rho : V2.D.Run V P) (t : Time) (x : V) (B : FGBlock (Fin n))
    (hB : B ∈ (R.core (V2.D.Run.readAt E rho t x)).fg.TF) (hne : B ≠ .genesis) :
    ∃ o t', V2.Event.deliver x o t' ∈ rho.events ∧
      S.proposalErase o = some (R.erase B) ∧
      B.rows = (S.proposalRows o).filterMap S.decode := by
  obtain ⟨rho', hsub, h⟩ := safety_readAt_replay E rho t
  rw [h] at hB
  obtain ⟨o, t', hd, hp, hrows⟩ :=
    ((safety_origin_stateBefore C L E rho' _ x).2.1 B hB).resolve_left hne
  exact ⟨o, t', hsub _ hd, hp, hrows⟩

private theorem safety_origin_preceq_refl (b : Block) : Block.Preceq b b := by
  cases b <;> simp [Block.Preceq, Block.preceq]

private theorem safety_origin_stored_runBlock (C : FGCoreLaws R)
    (L : FGSafetyStoreOriginLaws R S H f Good pending)
    (E : Generic.Env V) (rho : V2.D.Run V P) (i : Nat) (x : V) (B : FGBlock (Fin n))
    (hB : B ∈ (R.core (V2.D.Run.stateBefore E rho i x)).fg.TF) (hne : B ≠ .genesis) :
    safetyRunBlock R S E rho B := by
  obtain ⟨o, t, hd, hp, -⟩ :=
    ((safety_origin_stateBefore C L E rho i x).2.1 B hB).resolve_left hne
  exact ⟨o, R.erase B, hp, Or.inr ⟨x, t, hd⟩, safety_origin_preceq_refl _⟩

private theorem safety_origin_read_runBlock (C : FGCoreLaws R)
    (L : FGSafetyStoreOriginLaws R S H f Good pending)
    (E : Generic.Env V) (rho : V2.D.Run V P) (t : Time) (x : V) (B : FGBlock (Fin n))
    (hB : B ∈ (R.core (V2.D.Run.readAt E rho t x)).fg.TF) (hne : B ≠ .genesis) :
    safetyRunBlock R S E rho B := by
  obtain ⟨o, t', hd, hp, -⟩ := safety_origin_read_delivery C L E rho t x B hB hne
  exact ⟨o, R.erase B, hp, Or.inr ⟨x, t', hd⟩, safety_origin_preceq_refl _⟩

private theorem safety_origin_stored_scope (C : FGCoreLaws R)
    (L : FGSafetyStoreOriginLaws R S H f Good pending)
    (N : FGSafetyScopeLaws R S E rho Q) (i : Nat) (x : V) (hx : x ∈ rho.honest)
    (B : FGBlock (Fin n)) (hB : B ∈ (R.core (V2.D.Run.stateBefore E rho i x)).fg.TF) :
    Q (R.erase B) := by
  by_cases hne : B = .genesis
  · subst B
    exact N.genesis_scope x hx
  obtain ⟨o, t, hd, hp, -⟩ :=
    ((safety_origin_stateBefore C L E rho i x).2.1 B hB).resolve_left hne
  exact N.delivered_scope x o t _ hd hp

/-- `safety_read_scope` under the origin record. -/
theorem safety_read_scope_origin (C : FGCoreLaws R)
    (L : FGSafetyStoreOriginLaws R S H f Good pending)
    (N : FGSafetyScopeLaws R S E rho Q) (t : Time) (x : V) (hx : x ∈ rho.honest)
    (B : FGBlock (Fin n)) (hB : B ∈ (R.core (V2.D.Run.readAt E rho t x)).fg.TF) :
    Q (R.erase B) := by
  by_cases hne : B = .genesis
  · subst B
    exact N.genesis_scope x hx
  obtain ⟨o, t', hd, hp, -⟩ := safety_origin_read_delivery C L E rho t x B hB hne
  exact N.delivered_scope x o t' _ hd hp

variable (R S Ef H f E rho Good pending Q) in
/-- `safety_run_accountable` under the origin record. -/
theorem safety_run_accountable_origin
    (C : FGCoreLaws R) (L : FGSafetyStoreOriginLaws R S H f Good pending)
    (K : FGCertificateLaws Ef H f) (N : FGSafetyScopeLaws R S E rho Q)
    (hr : safetyScopedRoots R Q) : SafetyWholeAccountable R S Ef f E rho := by
  refine ⟨fun A B T T' _ _ hA hB hfA hfB => ?_, fun x hx y hy i j => ?_,
    fun x hx y hy t t' => ?_⟩
  · exact (safety_runBlock_accountable K N hr hA hB).imp id (fun hc => hfA.1 ▸ hfB.1 ▸ hc)
  · exact safety_store_accountable K hr
      (L.invariant _ (safety_origin_stateBefore C L E rho i x).1)
      (L.invariant _ (safety_origin_stateBefore C L E rho j y).1)
      (fun B hB => safety_origin_stored_scope C L N i x hx B hB)
      (fun B hB => safety_origin_stored_scope C L N j y hy B hB)
  · exact safety_store_accountable K hr
      (L.invariant _ (safety_origin_good_readAt C L E rho t x))
      (L.invariant _ (safety_origin_good_readAt C L E rho t' y))
      (fun B hB => safety_read_scope_origin C L N t x hx B hB)
      (fun B hB => safety_read_scope_origin C L N t' y hy B hB)

variable (R S Ef H f E rho Good pending Q) in
/-- `safety_run_agreement` under the origin record. -/
theorem safety_run_agreement_origin
    (C : FGCoreLaws R) (L : FGSafetyStoreOriginLaws R S H f Good pending)
    (K : FGCertificateLaws Ef H f) (N : FGSafetyScopeLaws R S E rho Q)
    (hr : safetyScopedRoots R Q) (hb : safetyBound R S Ef E rho) :
    SafetyWholeAgreement R S f E rho := by
  refine ⟨fun A B T T' _ _ hA hB hfA hfB => ?_, fun x _ y _ t t' => ?_⟩
  · exact hfA.1 ▸ hfB.1 ▸
      (safety_runBlock_accountable K N hr hA hB).resolve_left (hb A B hA hB)
  · exact safety_store_agreement K N hr hb
      (L.invariant _ (safety_origin_good_readAt C L E rho t x))
      (L.invariant _ (safety_origin_good_readAt C L E rho t' y))
      (fun B hB hne => safety_origin_read_runBlock C L E rho t x B hB hne)
      (fun B hB hne => safety_origin_read_runBlock C L E rho t' y B hB hne)

end AvailableChain.FGCompose
end
