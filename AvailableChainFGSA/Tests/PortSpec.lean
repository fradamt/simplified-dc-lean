module
public import AvailableChainFGSA.Proofs.Spec.Codec
public import AvailableChainFGSA.Proofs.Spec.Frame
public import AvailableChainFGSA.Proofs.Spec.Locks
public import AvailableChainFGSA.Proofs.Spec.Clock
public import AvailableChainFGSA.Proofs.Spec.Handlers

public section

/-! S0-C fixtures: arbitrary inputs, duplicate lists, late witnesses and lock expiry. -/

namespace AvailableChain.FGSA.Spec.Tests

open AvailableChain.SimplexFG

/-- Small fixture parameters; the digest is deliberately constant. -/
abbrev p : Params :=
  { Δ := 1, n := 1, k := 2, η := 0, deltaPos := by decide, nPos := by decide,
    kLarge := by decide, etaNonneg := by decide, R := 2, δt := 0,
    RLarge := by decide, digest := fun _ => ⟨7⟩ }

private def vote : HeadWire 1 := ⟨.seat (.head 0) ⟨0, by decide⟩, ⟨3⟩⟩
private def badVote : HeadWire 1 := ⟨.none, ⟨3⟩⟩
private def proposal : Block 1 := .node .genesis 1 ⟨0, by decide⟩ ⟨7⟩ [] [vote, vote] [vote]

example : wellFormed p ⟨.proposer 1, .proposal proposal⟩ = true := by decide
example : wellFormed p ⟨.proposer 2, .proposal proposal⟩ = false := by decide
example : wellFormed p
    ⟨.proposer 1, .proposal (.node .genesis 1 ⟨0, by decide⟩ ⟨8⟩ [] [vote] [])⟩ = false := by decide
example : wellFormed p
    ⟨.proposer 1, .proposal (.node .genesis 1 ⟨0, by decide⟩ ⟨7⟩ [] [badVote] [])⟩ = false := by
  decide
example : wellFormed p
    ⟨.proposer 1, .proposal (.node .genesis 1 ⟨0, by decide⟩ ⟨7⟩ [] [] [vote])⟩ = false := by decide
example : proposal.embed.raw = [vote, vote] := rfl
example : (Wire.embed (⟨.none, .proposal proposal⟩ : Wire 1)).decode = none := rfl

example : wellFormed p ⟨.proposer 0, .proposal .genesis⟩ = false := by decide
example : (Wire.embed
    (⟨.seat .fg ⟨0, by decide⟩, .head ⟨3⟩⟩ : Wire 1)).decode = none := rfl
example :
    (Block.node .genesis 1 ⟨0, by decide⟩ ⟨7⟩ [] [vote, badVote] [badVote, vote]).embed.support =
    [badVote, vote] := rfl

private def parentA : Block 1 := .node .genesis 1 ⟨0, by decide⟩ ⟨7⟩ [] [vote] []
private def parentB : Block 1 :=
  .node .genesis 1 ⟨0, by decide⟩ ⟨7⟩ [] [vote, vote] []
example : parentA.embed ≠ parentB.embed := by
  intro h
  have := congrArg NamedProposal.raw h
  contradiction

-- The parent-slot assertion is an admission check, after the stateless wire check.
private def equalSlot : Wire 1 :=
  ⟨.proposer 1, .proposal (.node parentA 1 ⟨0, by decide⟩ ⟨7⟩ [] [vote] [])⟩
example : wellFormed p equalSlot = true := by decide
example : parentSlotValid equalSlot = false := by decide
example : FGSA.wellFormed p equalSlot.embed = false := by decide
example (st : State 1) : process p st equalSlot.embed = st :=
  process_parent_slot_refused p st equalSlot (by decide)
example : checkedDelivery p (fun _ => ⟨0, by decide⟩) equalSlot Nat.succ 4 = 4 := by
  decide

private def pTwo : Params :=
  { p with n := 2, nPos := by decide, digest := fun _ => ⟨7⟩ }
private def otherProposer : Block 2 := .node .genesis 1 ⟨1, by decide⟩ ⟨7⟩ [] [] []
private def assignedBlock : Block 2 := .node .genesis 1 ⟨0, by decide⟩ ⟨7⟩ [] [] []
private def otherWire : Wire 2 := ⟨.proposer 1, .proposal otherProposer⟩
example : wellFormed pTwo otherWire = true := by decide
example : proposerAllowed (fun _ => ⟨0, by decide⟩) otherWire = false := by decide
example : FGSA.wellFormed pTwo (deliveryWire (fun _ => ⟨0, by decide⟩) otherWire) =
    false := by decide
example : otherProposer.embed = assignedBlock.embed := rfl
example : otherProposer.representation ≠ assignedBlock.representation := by decide
example : BlockCorresponds otherProposer assignedBlock.embed [⟨1, by decide⟩] := rfl
example : (Block.node otherProposer 2 ⟨0, by decide⟩ ⟨8⟩ [] [] []).identities =
    [⟨0, by decide⟩, ⟨1, by decide⟩] := rfl
example : checkedDelivery pTwo (fun _ => ⟨0, by decide⟩) otherWire Nat.succ 4 = 4 := by
  decide

private def A : FGBlock (Fin 1) := .node .genesis 1 ⟨1⟩ 0 []
private def B : FGBlock (Fin 1) := .node A 2 ⟨2⟩ 0 []
private def Φ : Frame 1 := ⟨{.genesis, A, B}, .genesis, .genesis, {B}⟩

example : A ∉ viableTree Φ {.genesis, A} := by decide
example : A ∈ viableTree Φ {.genesis, A, B} := by decide

private def a : AvailableChain.Block := .node .genesis 1 ⟨1⟩ 0
private def b : AvailableChain.Block := .node a 2 ⟨2⟩ 0
private def other : AvailableChain.Block := .node .genesis 1 ⟨9⟩ 0

example : lockMap [(a, 8), (b, 10)] a = (10 : WithBot Time) := by decide
example : lockMap [(a, 8), (b, 10)] b = (10 : WithBot Time) := by decide
example : liveEntries [a, b] 8 [(a, 8), (b, 10), (other, 20)] = [(b, 10)] := by decide
example : (expire ({ locks := [(a, 8), (b, 10)] } : ACState 1) 8).locks = [(b, 10)] := by
  decide
example : normalizeRecord b a = b := by decide
example : advance [a, b] b (some a) = b := by decide
example : normalizeRecord a (advance [a, b] other (some b)) =
    GridCO.advance (normalizeRecord a other) b := by decide
example : normalizeRecord a (advance [a, b] other none) = a := by decide
example : phaseTime 2 3 5 = phaseTime 2 4 1 := by decide
example : tick (fun x : Nat => 10 * x + 1) (fun x => 10 * x + 2)
    (fun x => 10 * x + 3) (fun x => 10 * x + 4) 0 = 1234 := by decide
example : onBlock false (fun _ : Nat => none) (fun x : Nat => x + 1) (3, 4) = (3, 4) := rfl

end AvailableChain.FGSA.Spec.Tests
