module
public import AvailableChainFGSAProofs.Statements.WeakContinuation
public import AvailableChainFGSAProofs.Proofs.Shared.OutputGrowthReads
public import AvailableChainFGSA.Proofs.StoreLaws
public import AvailableChainGeneric.Proofs.Pure.BlockOrder

public section

/-! WC plan §6.7; DC safety follows from the joint finite invariant. -/

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG KitFG Gen.Pure

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}
    {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}
    {w : HealingWitness} {iStar : Nat}

/-- WC plan §6.7; DC completed result evidence persists in a longer history. -/
private theorem result_mono {i k j : Nat} {x : V} {s : Slot} {B : Block}
    (h : WCResult p c E rho w iStar i j x s B) (hik : i ≤ k) :
    WCResult p c E rho w iStar k j x s B :=
  { h with completed := h.completed.trans_le hik }

/-- WC plan §6.7; DC prefix origins persist in a longer history. -/
private theorem history_mono {i k : Nat} {B : Block}
    (h : WCBelowHistory p c E rho w iStar i B) (hik : i ≤ k) :
    WCBelowHistory p c E rho w iStar k B := by
  rcases h.origin with h | ⟨j, x, s, C, hr, hb⟩
  · exact ⟨Or.inl h⟩
  · exact ⟨Or.inr ⟨j, x, s, C, result_mono hr hik, hb⟩⟩

/-- WC plan §6.7; DC cached finality has a low or a high historical origin. -/
theorem wc_finalHistoryAt {i k : Nat} {x : V}
    (hs : WCSeed p c E rho w iStar) (hi : WCInv p c E rho w iStar i)
    (hlo : iStar ≤ k) (hki : k ≤ i) (hx : x ∈ rho.honest) :
    WCBelowHistory p c E rho w iStar k (F_at p c E rho k x) := by
  obtain ⟨D, hD, hF⟩ := ((hi.finite k hlo hki).store x hx).fg.Fcar
  by_cases hX : (finalityView p D).F = .genesis
  · have he : F_at p c E rho k x = .genesis := by
      change eraseFG (storeAt p c E rho k x).fg.F = _
      rw [← hF, hX]
      rfl
    rw [he]
    exact ⟨Or.inl (block_genesis_preceq _)⟩
  by_cases hlow : (finalityView p D).h_F ≤ w.M
  · exact ⟨Or.inl (block_preceq_trans
      (hi.lowFinalized k x D _ _ hlo hki ⟨hx, hD⟩ hF rfl hlow) hs.sourcePrefix)⟩
  · have hn : (finalityView p D).h_F ≠ 0 := by
      simp only [Height] at *
      omega
    obtain ⟨C, D₀, _, _, hbirth, _⟩ := (fgCertificateLaws p).finality_origin D hn
    have hheight : (heightView p (finalityView p D).F).h = (finalityView p D).h_F := by
      rw [← hbirth.2.2.1, (fgCertificateLaws p).height.entry_same_height, hbirth.2.1]
    have hcert : (finalityView p D).F ∈ certified p D :=
      ⟨D, preceq_refl D, Or.inr (Or.inl rfl)⟩
    have hh : w.M + 1 ≤ (heightView p (finalityView p D).F).h := by
      rw [hheight]
      simp only [Height] at *
      omega
    have ho := (hi.highCertificates k x D _ hlo hki hx hD hcert hX hh).2
    rw [hF] at ho
    exact ho

/-- WC plan §6.7; DC the output origin keeps its own finite history bound. -/
theorem wc_outputHistoryAt {i k : Nat} {x : V}
    (hs : WCSeed p c E rho w iStar) (hi : WCInv p c E rho w iStar i)
    (hlo : iStar ≤ k) (hki : k ≤ i) (hx : x ∈ rho.honest) :
    WCBelowHistory p c E rho w iStar k (S_at p c E rho k x) := by
  rcases hi.outputOrigin k x hlo hki hx with hq | ⟨j, y, s, hr⟩ | ⟨l, hl, hlk, he, _⟩
  · exact ⟨Or.inl (hq ▸ block_preceq_refl w.QStar)⟩
  · exact ⟨Or.inr ⟨j, y, s, _, hr, block_preceq_refl _⟩⟩
  · rw [he]
    exact history_mono (wc_finalHistoryAt hs hi hl (hlk.trans hki) hx) hlk

/-- WC plan §6.7; DC result and output origins are compatible within the proved history. -/
theorem wc_result_output_compatible {i k j : Nat} {x y : V} {s : Slot} {B : Block}
    (hi : WCInv p c E rho w iStar i) (hr : WCResult p c E rho w iStar i j y s B)
    (hlo : iStar ≤ k) (hki : k ≤ i) (hx : x ∈ rho.honest) :
    Block.Compatible (S_at p c E rho k x) B := by
  rcases hi.outputOrigin k x hlo hki hx with hq | ⟨l, z, r, ho⟩ | ⟨l, _, _, he, hc⟩
  · obtain ⟨C, hC, hqC, _⟩ :=
      hi.nonempty j y s hr.afterCut hr.completed hr.honest hr.event hr.label
    have he : C = B := Option.some.inj (Option.some.inj (hC.symm.trans hr.value))
    rw [hq]
    exact block_compatible_of_common (he ▸ hqC) (block_preceq_refl B)
  · have ho' := result_mono ho hki
    rcases lt_trichotomy r s with h | h | h
    · exact block_compatible_of_common (hi.ordered l j z y r s _ B ho' hr h)
        (block_preceq_refl B)
    · subst r
      exact hi.sameLabel l j z y s _ B ho' hr
    · exact block_compatible_of_common (block_preceq_refl _)
        (hi.ordered j l y z s r B _ hr ho' h)
  · rw [he]
    exact hc j y s B hr

/-- WC plan §6.7; DC event safety and both public output reads follow the joint invariant. -/
theorem wc_seededSafety : WCSeededSafetyStatement p c E rho w iStar := by
  intro hschedule hs hinv
  let last := rho.events.length
  have hi := hinv last ⟨hs.within, le_rfl⟩
  have resultSeed : ∀ j x s B, WCResult p c E rho w iStar last j x s B →
      Block.Preceq w.QStar B := by
    intro j x s B hr
    obtain ⟨C, hc, hq, _⟩ :=
      hi.nonempty j x s hr.afterCut hr.completed hr.honest hr.event hr.label
    have he : B = C := Option.some.inj (Option.some.inj (hr.value.symm.trans hc))
    exact he ▸ hq
  have resultsCompat : ∀ j k x y s r B C,
      WCResult p c E rho w iStar last j x s B →
      WCResult p c E rho w iStar last k y r C → Block.Compatible B C := by
    intro j k x y s r B C hb hc
    rcases lt_trichotomy s r with h | h | h
    · exact block_compatible_of_common (hi.ordered j k x y s r B C hb hc h)
        (block_preceq_refl C)
    · subst r
      exact hi.sameLabel j k x y s B C hb hc
    · exact block_compatible_of_common (block_preceq_refl B)
        (hi.ordered k j y x r s C B hc hb h)
  have historyCompat : ∀ B C, WCBelowHistory p c E rho w iStar last B →
      WCBelowHistory p c E rho w iStar last C → Block.Compatible B C := by
    intro B C hb hc
    rcases hb.origin with hb | ⟨j, x, s, B', hr, hb⟩
    · rcases hc.origin with hc | ⟨k, y, r, C', hr, hc⟩
      · exact block_compatible_of_common hb hc
      · exact block_compatible_of_common
          (block_preceq_trans hb (resultSeed k y r C' hr)) hc
    · rcases hc.origin with hc | ⟨k, y, r, C', hr', hc⟩
      · exact block_compatible_of_common hb
          (block_preceq_trans hc (resultSeed j x s B' hr))
      · apply block_compatible_of_preceq_compatible hb
        change Block.compatible _ _ = true
        rw [block_compatible_comm]
        apply block_compatible_of_preceq_compatible hc
        change Block.compatible _ _ = true
        rw [block_compatible_comm]
        exact resultsCompat j k x y s r B' C' hr hr'
  have outputHistory : ∀ k x, iStar ≤ k → k ≤ last → x ∈ rho.honest →
      WCBelowHistory p c E rho w iStar last (S_at p c E rho k x) := by
    intro k x hlo hki hx
    rcases hi.outputOrigin k x hlo hki hx with hq | ⟨j, y, s, hr⟩ | ⟨l, hl, hlk, he, _⟩
    · exact ⟨Or.inl (hq ▸ block_preceq_refl w.QStar)⟩
    · exact ⟨Or.inr ⟨j, y, s, _, result_mono hr hki, block_preceq_refl _⟩⟩
    · rw [he]
      exact history_mono (wc_finalHistoryAt hs hi hl (hlk.trans hki) hx) (hlk.trans hki)
  have hcompat : CompatOn (· ∈ rho.honest) (S_at p c E rho)
      (fun i => iStar ≤ i ∧ i ≤ last) := by
    intro i j x y hii hjj hx hy
    exact historyCompat _ _ (outputHistory i x hii.1 hii.2 hx)
      (outputHistory j y hjj.1 hjj.2 hy)
  have hmono : MonoOn (· ∈ rho.honest) (S_at p c E rho)
      (fun i => iStar ≤ i ∧ i ≤ last) := by
    intro i j x hii hjj hij hx
    induction j, hij using Nat.le_induction with
    | base => exact block_preceq_refl _
    | succ k hik ih =>
      exact block_preceq_trans (ih ⟨hii.1.trans hik, by omega⟩)
        (hi.transitions k x (hii.1.trans hik) (by omega) hx)
  refine ⟨hcompat, hmono, ?_, ?_⟩
  · intro i x hii hx
    exact hi.served i x hii.1 hii.2 hx
  · intro g hg
    constructor
    · intro t u x y ht hu hx hy
      change Block.Compatible (V2.D.outputAt E rho g x t) (V2.D.outputAt E rho g y u)
      rw [fgsa_outputAt_eq_S_at E rho hschedule g hg x t,
        fgsa_outputAt_eq_S_at E rho hschedule g hg y u]
      exact hcompat _ _ x y ⟨ht, List.length_filter_le _ _⟩
        ⟨hu, List.length_filter_le _ _⟩ hx hy
    · intro t u x ht hu htu hx
      change Block.Preceq (V2.D.outputAt E rho g x t) (V2.D.outputAt E rho g x u)
      rw [fgsa_outputAt_eq_S_at E rho hschedule g hg x t,
        fgsa_outputAt_eq_S_at E rho hschedule g hg x u]
      exact hmono _ _ x ⟨ht, List.length_filter_le _ _⟩
        ⟨hu, List.length_filter_le _ _⟩ (V2.D.Engine.read_length_mono _ _ htu) hx

end AvailableChain.FGSA.Run
end
