module
public import AvailableChainFGSAProofs.Proofs.Healing.DescentTiming -- shake: keep (D4 boundary examples)

set_option linter.privateModule false

namespace AvailableChain.FGSA.Run.Tests.HealingDescentTiming
open AvailableChain.SimplexFG

private abbrev params : Params :=
  { Δ := 1, n := 1, k := 2, η := 0, deltaPos := by decide, nPos := by decide,
    kLarge := by decide, etaNonneg := by decide,
    R := 2, δt := 1, RLarge := by decide }

local instance : DecidableEq (KitFG.FGCertEntry (Fin 1)) := fun a b =>
  decidable_of_iff (a.j = b.j ∧ a.X = b.X ∧ a.Q = b.Q) (by cases a; cases b; simp)

-- Different honest nodes can have ordered tick indices at the same time.
-- This order supplies no complete period.
private def sameTicks : List (V2.Event Bool (Obj params)) :=
  [.tick false 6, .tick true 6]

example : sameTicks[0]? = some (.tick false 6) ∧
    sameTicks[1]? = some (.tick true 6) ∧
    false ∈ ({false, true} : Finset Bool) ∧ true ∈ ({false, true} : Finset Bool) ∧
    (V2.Event.tick false 6 : V2.Event Bool (Obj params)).key ≤
      (V2.Event.tick true 6 : V2.Event Bool (Obj params)).key ∧
    ¬ (params.actionTime 0 + P params ≤ params.actionTime 0) := by decide

-- Same-time delivery is after all ticks. A saved receipt strictly before
-- an action tick must therefore have strictly smaller time.
example {In V : Type} [DecidableEq V] (c : AppCodec In) (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa params c)) (hs : V2.D.ScheduleWellFormed E rho)
    {k i : Nat} {x z : V} {o : Obj params} {t : Time} {r : Nat}
    (hki : k < i) (hk : rho.events[k]? = some (.deliver x o t))
    (hi : rho.events[i]? = some (.tick z (params.actionTime r))) :
    t < params.actionTime r :=
  healing_receipt_before_tick params c E rho hs hki hk hi

example : params.actionTime 0 + P params ≤ params.actionTime 1 :=
  healing_action_period params (by decide)

private def progressBlock : FGBlock (Fin 1) :=
  .node .genesis 1 0 [⟨0, .vote 1 genesisRoot true, none⟩]
private def signerHead : FGBlock (Fin 1) :=
  .node progressBlock 2 0 [⟨0, .vote 2 progressBlock.root false, none⟩]
private def latestBirth : FGBlock (Fin 1) :=
  .node signerHead 3 0 [⟨0, .vote 3 signerHead.root false, none⟩]
private def oldChoice : FGBlock (Fin 1) :=
  .node latestBirth 4 0 [⟨0, .empty, some ⟨2, progressBlock.root⟩⟩]

-- The honest finality signer's justification can differ from the eventual
-- carrier's latest J. The pair retains the exact height and root.
example : (heightView params signerHead).h_j = 2 ∧
    (heightView params signerHead).J = progressBlock ∧
    finality_pair Record.initial
      (Window.headFields params 2 signerHead) =
      some ⟨2, progressBlock.root⟩ ∧
    (heightView params oldChoice).h_j = 3 ∧
    (heightView params oldChoice).J = signerHead ∧
    (heightView params signerHead).J ≠ (heightView params oldChoice).J := by decide

-- The selected F is an older window entry. Its h_F is retained, while
-- the later justification remains in the window.
example : (Window.certificateSelection params 2).chosen oldChoice =
      some ⟨2, progressBlock, {0}⟩ ∧
    (finalityView params oldChoice).F = progressBlock ∧
    (finalityView params oldChoice).h_F = 2 ∧
    (Window.certificateSelection params 2).afterPrune oldChoice =
      [⟨3, signerHead, ∅⟩] := by decide

private def genesisBirth : FGBlock (Fin 1) :=
  .node .genesis 1 0 [⟨0, .vote 1 genesisRoot false, none⟩]
private def genesisFinal : FGBlock (Fin 1) :=
  .node genesisBirth 2 0 [⟨0, .empty, some ⟨1, genesisRoot⟩⟩]

-- A positive certificate height does not require a non-genesis F.
example : (finalityView params genesisFinal).F = .genesis ∧
    (finalityView params genesisFinal).h_F = 1 := by decide

-- The release q_(sStar) is before the reset action. RFProv's lower cut
-- cannot supply a proof at this release. T1 must cover this earlier cut.
example (p : Params) (r : Nat) :
    SA.releaseTime p.toParams (r * p.R) < p.actionTime r := by
  change 4 * p.Δ * ((r * p.R : Nat) : Int) + 5 * p.Δ <
    4 * p.Δ * ((r * p.R : Nat) : Int) + 6 * p.Δ
  nlinarith [p.deltaPos]

-- The clock adapter accepts any read index after the saved receipt,
-- including a read past the final event. No awake premise is present.
example {In V : Type} [DecidableEq V] (c : AppCodec In) (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa params c)) (hs : V2.D.ScheduleWellFormed E rho)
    (hnr : V2.D.NoRestart rho) {k j r : Nat} {x z : V} {o : Obj params} {t : Time}
    (hk : rho.events[k]? = some (.deliver x o t))
    (hj : rho.events[j]? = some (.tick z (params.actionTime r)))
    (ht : params.actionTime r ≤ t) :
    params.actionTime r ≤ (storeAt params c E rho (rho.events.length + 7) x).base.now := by
  have hkl := (List.getElem?_eq_some_iff.mp hk).1
  exact healing_delivery_clock params c E rho hs hnr (by omega) hk hj ht

end AvailableChain.FGSA.Run.Tests.HealingDescentTiming
