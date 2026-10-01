module
public import AvailableChainFGSAProofs.Proofs.Shared.HeadCover -- shake: keep (P3 M6 dependency)
public import AvailableChainFGSAProofs.Proofs.Shared.HeadGeometry -- shake: keep (P3 M6 dependency)
public import AvailableChainFGSAClaims.Statements.ChannelProps

public section

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG
open Gen.Pure

/-- P3 F1b.8, G31; 21 H.13–H.14; GLY F-25. Class (iii), composition.
DC: FGRootWitness.lean:548 `fgRoot_compatible_of_bootstrap_and_recentActions_at_read`
is a root-compatibility ingredient, not an FJ retention theorem.
INTENTIONAL: FJ uses the duty's X and its witness W (F-25).
Source extraction for an incompatible control is an explicit supplier;
this lemma does not prove the run-level certificate provenance (21 H.13).
A floor witness rules out band exclusion, including the two-source case.
RExcl/H.13 must prove the band, contested and two-source cause cases outside this lemma (21
:2599–2627). -/
theorem kept_or_conflict (p : Params) {In V : Type} [DecidableEq V]
    (c : AppCodec In) (E : Generic.Env V) (rho : V2.Run V (fgsa p c))
    (i : Nat) (x : V) (X : Finset (FGBlock (Fin p.n))) (C W : FGBlock (Fin p.n))
    (hC : C ∈ X) (hW : W ∈ X) (hCW : FGBlock.Preceq C W)
    (hlo : (R_at p c E rho i x).lo ≤ hOf p.E p.cfg W)
    (hcontrolSource : ∀ K ∈ [(storeAt p c E rho i x).fg.F, (R_at p c E rho i x).Z],
      ¬ (FGBlock.Preceq K C ∨ FGBlock.Preceq C K) →
      ∃ C' s, SourceBefore p c E rho i C' s ∧
        FGBlock.Preceq K C' ∧ hOf p.E p.cfg C ≤ hOf p.E p.cfg C') :
    Kept p c E rho i x X C ∨
      (∃ C' s, SourceBefore p c E rho i C' s ∧
        ¬ Block.Compatible (eraseFG C) (eraseFG C') ∧ hOf p.E p.cfg C ≤ hOf p.E p.cfg C') := by
  have cause (K : FGBlock (Fin p.n))
      (hK : K ∈ [(storeAt p c E rho i x).fg.F, (R_at p c E rho i x).Z])
      (hbad : ¬ (FGBlock.Preceq K C ∨ FGBlock.Preceq C K)) :
      ∃ C' s, SourceBefore p c E rho i C' s ∧
        ¬ Block.Compatible (eraseFG C) (eraseFG C') ∧ hOf p.E p.cfg C ≤ hOf p.E p.cfg C' := by
    obtain ⟨C', s, hsrc, hKC', hh⟩ := hcontrolSource K hK hbad
    refine ⟨C', s, hsrc, ?_, hh⟩
    intro hc
    have hKC : Block.Compatible (eraseFG K) (eraseFG C) :=
      block_compatible_of_preceq_compatible (eraseFG_preceq hKC')
        (by
          change Block.compatible (eraseFG C') (eraseFG C) = true
          rw [block_compatible_comm]
          exact hc)
    have hfg : FGBlock.compatible K C = true := by
      rw [compatible_iff_eraseFG (Vw := {K, C}) (KitFG.viewRootInj_all _)
        ⟨K, by simp, KitFG.preceq_refl _⟩ ⟨C, by simp, KitFG.preceq_refl _⟩]
      exact hKC
    exact hbad (Bool.or_eq_true_iff.mp hfg)
  by_cases hF : FGBlock.Preceq (storeAt p c E rho i x).fg.F C ∨
      FGBlock.Preceq C (storeAt p c E rho i x).fg.F
  · by_cases hZ : FGBlock.Preceq (R_at p c E rho i x).Z C ∨
        FGBlock.Preceq C (R_at p c E rho i x).Z
    · apply Or.inl
      rcases hF with hFC | hCF
      · rcases hZ with hZC | hCZ
        · apply Or.inr ∘ Or.inl
          exact (KitFG.mem_filteredFrom p.E p.cfg _ _ C).mpr
            ⟨hC, hFC, hZC, W, hW, hCW, hlo⟩
        · exact Or.inl hCZ
      · exact Or.inr (Or.inr hCF)
    · exact Or.inr (cause _ (by simp) hZ)
  · exact Or.inr (cause _ (by simp) hF)

/-- P3 F1b.8, G31; 21 H.13–H.14; GLY F-25. Class (iii), composition.
DC: FGRootWitness.lean:548 `fgRoot_compatible_of_bootstrap_and_recentActions_at_read`
is a root-compatibility ingredient, not an FJ retention theorem.
INTENTIONAL: FJ uses the duty's X and its witness W (F-25).
Source extraction for an incompatible control is an explicit supplier;
this lemma does not prove the run-level certificate provenance (21 H.13).
A floor witness rules out band exclusion, including the two-source case.
RExcl/H.13 must prove the band, contested and two-source cause cases outside this lemma (21
:2599–2627). -/
theorem kept_or_cause (p : Params) {In V : Type} [DecidableEq V]
    (c : AppCodec In) (E : Generic.Env V) (rho : V2.Run V (fgsa p c))
    (i : Nat) (x : V) (X : Finset (FGBlock (Fin p.n))) (C W : FGBlock (Fin p.n))
    (hC : C ∈ X) (hW : W ∈ X) (hCW : FGBlock.Preceq C W)
    (hlo : (R_at p c E rho i x).lo ≤ hOf p.E p.cfg W)
    (hcontrolSource : ∀ K ∈ [(storeAt p c E rho i x).fg.F, (R_at p c E rho i x).Z],
      ¬ (FGBlock.Preceq K C ∨ FGBlock.Preceq C K) →
      ∃ C' s, SourceBefore p c E rho i C' s ∧
        FGBlock.Preceq K C' ∧ hOf p.E p.cfg C ≤ hOf p.E p.cfg C') :
    KeepOrCause p c E rho i x X C := by
  rcases kept_or_conflict p c E rho i x X C W hC hW hCW hlo hcontrolSource with hk | hc
  · exact Or.inl hk
  · exact Or.inr (Or.inl hc)

/-- F1b.5a closure at a later pivot in the same FG-SA duty domain.
DC: Goldfish/Walk.lean:433 `ghost_reaches` uses a path in its tree.
INTENTIONAL: this local corollary moves FJ filtered closure from A to T
for F1b.8 (21 H.17); it adds no generic walk declaration. -/
theorem fgsa_domain_anchorClosed_mono (p : Params) (st : State p.n)
    (X : Finset (FGBlock (Fin p.n))) (A T : Block)
    (hAT : Block.Preceq A T)
    (hclosed : Gen.Pure.AnchorClosed A (erasedList st (domainR p st X))) :
    Gen.Pure.AnchorClosed T (erasedList st (domainR p st X)) := by
  intro B hB hTB C hTC hCB
  exact hclosed B hB (block_preceq_trans hAT hTB) C (block_preceq_trans hAT hTC) hCB

/-- P3 F1b.8, G33; 21 H.17:2778–2825 and H.22 head clause.
Class (iii), conditional walk composition. DC:
ProposalWalkTransportCore.lean:162 `ghost_transport_of_source` and
Goldfish/Walk.lean:433 `ghost_reaches`.
INTENTIONAL: common pivot T replaces equality of the live roots, which
may change (21 H.17). Each local prefix and the transferred suffix have
explicit keep suppliers (P3 M6). Terminality at Q is required, as in G10.
Closure above T follows from F1b.5a and `fgsa_domain_anchorClosed_mono` when the live root
precedes T. The caller supplies source coverage
of P; the final step is either P = Q
or the unique eligible child Q of P (21 H.17:2820–2825). This does not produce ExactService
or identify a scheduled HEAD read. X and Y may be different duty views. -/
theorem exactHead_of_pivot (p : Params) (st st' : State p.n)
    (X Y : Finset (FGBlock (Fin p.n)))
    (raw support raw' support' : List (GridCO.Wire p.n)) (T P Q : Block)
    (hAT : Block.Preceq (liveRoot p st) T) (hAT' : Block.Preceq (liveRoot p st') T)
    (hTP : Block.Preceq T P)
    (hprefix : DominatedSuffix (liveRoot p st) T (erasedList st (domainR p st X))
      (GridCO.goldfishScore st.base.blocks raw support) (eligible p st raw support))
    (hprefix' : DominatedSuffix (liveRoot p st') T (erasedList st' (domainR p st' Y))
      (GridCO.goldfishScore st'.base.blocks raw' support') (eligible p st' raw' support'))
    (hcover : Block.Preceq P (headInTree p st (erasedList st (domainR p st X)) raw support))
    (hkeep : SuffixPersists T P
      (erasedList st (domainR p st X)) (erasedList st' (domainR p st' Y))
      (GridCO.goldfishScore st.base.blocks raw support)
      (eligible p st raw support) (eligible p st' raw' support'))
    (hreflect : SuffixReflects T P
      (erasedList st (domainR p st X)) (erasedList st' (domainR p st' Y))
      (eligible p st raw support) (eligible p st' raw' support'))
    (hscore : SuffixScoresAgree T P (erasedList st' (domainR p st' Y))
      (GridCO.goldfishScore st.base.blocks raw support)
      (GridCO.goldfishScore st'.base.blocks raw' support') (eligible p st' raw' support'))
    (hlast : P = Q ∨
      (Q ∈ erasedList st' (domainR p st' Y) ∧ Q.parent? = some P ∧
        eligible p st' raw' support' Q = true ∧
        ∀ C ∈ erasedList st' (domainR p st' Y), C.parent? = some P →
          eligible p st' raw' support' C = true → C = Q))
    (hclosed : AnchorClosed T (erasedList st' (domainR p st' Y)))
    (hstop : NoEligibleChild (erasedList st' (domainR p st' Y)) (eligible p st' raw' support') Q) :
    headInTree p st' (erasedList st' (domainR p st' Y)) raw' support' = Q := by
  have hs := walk_reanchor_of_dominated_suffix _ _ _ _ _ hAT hprefix
  have ht := walk_reanchor_of_dominated_suffix _ _ _ _ _ hAT' hprefix'
  change Block.Preceq P (GridCO.ghost _ _ _ _) at hcover
  rw [hs] at hcover
  have hc := ghost_transfer_sfx _ _ _ _ _ _ _ _ hTP hcover hkeep hreflect hscore
  let tree := erasedList st' (domainR p st' Y)
  let score := GridCO.goldfishScore st'.base.blocks raw' support'
  let elig := eligible p st' raw' support'
  let H := GridCO.ghost T tree score elig
  have parent_prefix {B C : Block} (hp : C.parent? = some B) : Block.Preceq B C := by
    cases C with
    | genesis => cases hp
    | node A s r =>
      have he : A = B := Option.some.inj hp
      subst A
      change (decide _ || Block.preceq B B) = true
      exact Bool.or_eq_true_iff.mpr (Or.inr (block_preceq_refl _))
  have hPQ : Block.Preceq P Q := by
    rcases hlast with he | ⟨_, hp, _, _⟩
    · rw [he]; exact block_preceq_refl _
    · exact parent_prefix hp
  have hTQ := block_preceq_trans hTP hPQ
  have hQH : Block.Preceq Q H := by
    rcases hlast with he | ⟨hQ, hpQ, helQ, honly⟩
    · exact he ▸ hc
    · have hne : H ≠ P := by
        intro he
        have hn := walk_noEligibleChild_of_anchorClosed T tree score elig hclosed Q hQ
          (by change Q.parent? = some H; rw [he]; exact hpQ)
        change eligible p st' raw' support' Q = false at hn
        rw [helQ] at hn
        cases hn
      obtain ⟨C, hpC, hCH⟩ := path_child P H hc (Ne.symm hne)
      have hH : H ∈ tree := by
        rcases fgsa_headInTree_mem_or_anchor p st' tree raw' support' with he | hm
        · have he' : H = liveRoot p st' := ht.symm.trans he
          exact (hne (he'.trans (block_preceq_antisymm
            (block_preceq_trans hAT' hTP) (he' ▸ hc)))).elim
        · change GridCO.ghost _ _ _ _ ∈ tree at hm
          rw [ht] at hm
          exact hm
      have hC := hclosed H hH (block_preceq_trans hTP hc) C
        (block_preceq_trans hTP (parent_prefix hpC)) hCH
      have helC : elig C = true := by
        cases he : elig C with
        | false => exact (walk_avoids_unsupported_child T P C tree score elig hTP hpC he hCH).elim
        | true => rfl
      exact honly C hC hpC helC ▸ hCH
  change GridCO.ghost _ _ _ _ = Q
  rw [ht]
  change H = Q
  by_contra hne
  obtain ⟨C, hp, hCH⟩ := path_child Q H hQH (Ne.symm hne)
  have hQC : Block.Preceq Q C := by
    cases C with
    | genesis => cases hp
    | node P s r =>
      have he : P = Q := Option.some.inj hp
      subst P
      change (decide _ || Block.preceq Q Q) = true
      exact Bool.or_eq_true_iff.mpr (Or.inr (block_preceq_refl _))
  have hH : H ∈ tree := by
    rcases fgsa_headInTree_mem_or_anchor p st' tree raw' support' with he | hm
    · have he' : H = liveRoot p st' := ht.symm.trans he
      exact (hne (he'.trans (block_preceq_antisymm
        (block_preceq_trans hAT' hTQ) (he' ▸ hQH)))).elim
    · change GridCO.ghost _ _ _ _ ∈ tree at hm
      rw [ht] at hm
      exact hm
  have hC := hclosed H hH (block_preceq_trans hTQ hQH) C
    (block_preceq_trans hTQ hQC) hCH
  exact walk_avoids_unsupported_child T Q C tree score elig hTQ hp
    (hstop C hC hp) hCH

end AvailableChain.FGSA.Run
