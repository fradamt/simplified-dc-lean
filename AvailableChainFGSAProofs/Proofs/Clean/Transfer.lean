module
public import AvailableChainFGSAProofs.Proofs.Clean.TransferFrame
public import AvailableChainFGSAProofs.Proofs.Shared.Relay
public import AvailableChainFGSA.Proofs.Head.Transfer
public import AvailableChainGeneric.Proofs.V2.Regimes

public section

-- The F2.3 split ruling permits only private declarations in this module.
set_option linter.privateModule false

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

variable (p : Params) {In V : Type} (c : AppCodec In)
    [DecidableEq V] [Fintype V]
    (E : Generic.Env V) (rho : V2.Run V (fgsa p c))

set_option linter.unusedVariables false in
/-- P3 F2.3:5496–5503; bp02 §4.2, G24. Class B, private run instance.
DC: Goldfish/Adoption.lean:53–67,158–170; AdoptionTransport.lean:346.
INTENTIONAL: the actual F-anchored optional gate result supplies the majority
(spec:2506–2513). The named forward hypothesis is private, as required by the
F2.3 split ruling; unlike DC it covers all P, not only supporters of B. -/
private theorem clean_transfer_counts_of_forward (b₀ : Time) :
  CleanCut₂ p c E rho b₀ → Gen.Pure.FaultQ p.n (Gen.V2.faulty rho).card →
  FGFoundation p c E rho → SrcFrameAboveStmt p c E rho →
  ∀ i k x y s B, i < timeIdx rho b₀ → k < i →
    IsGateTick p c rho i x s →
    rho.events[k]? = some (.tick y (SA.voteTime p.toParams (s + 1))) →
    CleanHist p c E rho i → (∀ j, j ≤ i → CleanState p c E rho j) →
    gateResultAt p c E rho i = some (some B) →
    (∀ r C, (r, C) ∈ cleanResults p c E rho i → r < s → Block.Preceq C B) →
    let src := FGSA.actView (FGSA.clockPre p (storeAt p c E rho i x)
      (SA.gateTime p.toParams s))
    let dst := ((fgsa p c).clock (V2.Run.stateBefore E rho k y)
      (SA.voteTime p.toParams (s + 1))).st
    let P := GridCO.cleanSupport p.toParams.engine src s
    let L := GridCO.lateVotes p.toParams.engine src s
    let U := FGSA.headVotes p dst (s + 1)
    let Vsup := FGSA.headSupport p dst (s + 1)
    ∀ (hC5 : ∀ o ∈ P, ∀ seat, GridCO.headSeat? o = some seat →
      (o ∈ Vsup ∧ Gen.AC.voteSupports dst.base.blocks B o = true) ∨
        GridCO.equivocates U seat = true),
    Gen.AC.TransferBounds (Gen.AC.plainSupporters src.blocks P P B)
      L dst.base.blocks U Vsup B := by
  intro h _ _ _ i k x y s B hi _ ht hk _ _ hB _ src dst P L U Vsup hC5
  have hsch := h.base.valid.toScheduleWellFormed
  have hx := hsch.honest_only _ (List.mem_of_getElem? ht)
  have hy := hsch.honest_only _ (List.mem_of_getElem? hk)
  have hcut := (V2.Engine.index_lt_read_length_iff hsch b₀ ht).mp hi
  have hvd : SA.voteTime p.toParams s + E.Δ ≤ SA.gateTime p.toParams s := by
    rw [h.base.delta]
    change 4 * p.Δ * (s : Int) + p.Δ + p.Δ ≤ 4 * p.Δ * (s : Int) + 6 * p.Δ
    have hd := p.deltaPos
    linarith
  have hsync := Gen.V2.LabelSync.of_cleanCut E rho b₀ _ _ h.healthy hvd hcut h.cut.2
  have hraw := Option.some.inj ((clean_gate_raw hsch ht).symm.trans hB)
  have hmajority : GridCO.voterCount L < 2 * GridCO.goldfishScore src.blocks P P B := by
    change (if _ then some _ else none) = some B at hraw
    split at hraw
    · have he := Option.some.inj hraw
      subst B
      exact ‹_ < 2 * _›
    · contradiction
  exact Gen.AC.transfer src.blocks dst.base.blocks P L U Vsup B
    (fun _ ho => fgsa_early_subset_late p src s (List.mem_filter.mp ho).1)
    (fgsa_cleanSupport_seat_clean_late p src s)
    (fun o ho seat hs _ => hC5 o ho seat hs)
    (fgsa_headVotes_backward_relay E rho h.base.valid h.base.noRestart h.base.delta
      s hsync hx hy ht hk)
    (fgsa_headSupport_subset_headVotes E rho h.base.valid k y s) hmajority

set_option linter.unusedVariables false in
/-- P3 F2.3:5496–5503; bp02 §4.2; blueprint claim bp.cleanTransfer.v1
(00:756–765): internal lane theorem, public statement candidate for a later freeze.
Class B. DC: AdoptionTransport.lean:346 and Goldfish/Adoption.lean:441–461.
INTENTIONAL: FG-SA uses an F-anchored optional result, a lease liveRoot and
an FJ voter domain (spec:2506–2525,2557–2565). Current Ordered is explicit
(review-00-02:234–236). The split ruling keeps the named C5 premise private;
this conditional lemma does not export the later public cleanTransfer. -/
private theorem cleanTransfer_of_forward (b₀ : Time) :
  CleanCut₂ p c E rho b₀ → Gen.Pure.FaultQ p.n (Gen.V2.faulty rho).card →
  FGFoundation p c E rho → SrcFrameAboveStmt p c E rho →
  ∀ i k x y s B, i < timeIdx rho b₀ → k < i →
    IsGateTick p c rho i x s →
    rho.events[k]? = some (.tick y (SA.voteTime p.toParams (s + 1))) →
    CleanHist p c E rho i → (∀ j, j ≤ i → CleanState p c E rho j) →
    gateResultAt p c E rho i = some (some B) →
    (∀ r C, (r, C) ∈ cleanResults p c E rho i → r < s → Block.Preceq C B) →
    let src := FGSA.actView (FGSA.clockPre p (storeAt p c E rho i x)
      (SA.gateTime p.toParams s))
    let dst := ((fgsa p c).clock (V2.Run.stateBefore E rho k y)
      (SA.voteTime p.toParams (s + 1))).st
    let P := GridCO.cleanSupport p.toParams.engine src s
    let L := GridCO.lateVotes p.toParams.engine src s
    let U := FGSA.headVotes p dst (s + 1)
    let Vsup := FGSA.headSupport p dst (s + 1)
    ∀ (hC5 : ∀ o ∈ P, ∀ seat, GridCO.headSeat? o = some seat →
      (o ∈ Vsup ∧ Gen.AC.voteSupports dst.base.blocks B o = true) ∨
        GridCO.equivocates U seat = true),
    Block.Preceq B (headAtIdx p c E rho k (s + 1)) := by
  intro h hq hf hsrc i k x y s B hi hki ht hk hh hall hB hord src dst P L U Vsup hC5
  have hc := clean_transfer_counts_of_forward p c E rho b₀ h hq hf hsrc
    i k x y s B hi hki ht hk hh hall hB hord hC5
  rw [Gen.AC.TransferBounds_def] at hc
  obtain ⟨Bfg, he, _, _, _, _, _, hroot, hV, hdom⟩ :=
    clean_transfer_frame p c E rho b₀ h hq hf hsrc
      i k x y s B hi hki ht hk hh hall hB hord
  have hinv : CStoreInv p dst :=
    cstoreInv_clock p _ (cstoreInv_stateBefore E rho k y) _
  have hstored : Bfg ∈ dst.fg.TF := by
    exact (Finset.mem_filter.mp hV).1
  have hpath : ∀ C, Block.Prec (liveRoot p dst) C → Block.Preceq C B →
      C ∈ erasedList dst (storeFrame p.E p.cfg dst.fg (voterBlocks p dst (s + 1))) := by
    intro C hr hCB
    have hr' : liveRoot p dst ≠ C ∧ Block.Preceq (liveRoot p dst) C := by
      change ((!decide (liveRoot p dst = C)) && Block.preceq (liveRoot p dst) C) = true at hr
      simpa only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
        Block.Preceq] using hr
    obtain ⟨A, hA, heA, hAB⟩ := eraseFG_ancestor_preceq hinv.fg.closed hstored (he ▸ hCB)
    apply List.mem_filter.mpr
    refine ⟨(hinv.baseTree C).mpr ⟨A, hA, heA⟩, decide_eq_true ⟨A, ?_, heA⟩⟩
    exact hdom A (heA ▸ hr'.2) hAB (by simpa only [heA] using Ne.symm hr'.1)
  have hhead := fgsa_headVote_covers_of_transfer p dst s B
    (Bool.or_eq_true_iff.mpr (Or.inl hroot)) hpath hc.2.2.2.2.2.1 hc.2.2.2.2.2.2
  have hread : headAtIdx p c E rho k (s + 1) = headVote p dst (s + 1) := by
    delta headAtIdx
    rw [hk]
  exact hread ▸ hhead

end AvailableChain.FGSA.Run
