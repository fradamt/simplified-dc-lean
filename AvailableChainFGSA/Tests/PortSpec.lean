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
private def proposal : Block 1 := .node .genesis 1 ⟨7⟩ [] [vote, vote] [vote]

example : wellFormed p ⟨.proposer 1, .proposal proposal⟩ = true := by decide
example : wellFormed p ⟨.proposer 2, .proposal proposal⟩ = false := by decide
example : wellFormed p
    ⟨.proposer 1, .proposal (.node .genesis 1 ⟨8⟩ [] [vote] [])⟩ = false := by decide
example : wellFormed p
    ⟨.proposer 1, .proposal (.node .genesis 1 ⟨7⟩ [] [badVote] [])⟩ = false := by decide
example : wellFormed p
    ⟨.proposer 1, .proposal (.node .genesis 1 ⟨7⟩ [] [] [vote])⟩ = false := by decide
example : proposal.embed.raw = [vote, vote] := rfl
example : (Wire.embed (⟨.none, .proposal proposal⟩ : Wire 1)).decode = none := rfl

example : wellFormed p ⟨.proposer 0, .proposal .genesis⟩ = false := by decide
example : (Wire.embed
    (⟨.seat .fg ⟨0, by decide⟩, .head ⟨3⟩⟩ : Wire 1)).decode = none := rfl
example : (Block.node .genesis 1 ⟨7⟩ [] [vote, badVote] [badVote, vote]).embed.support =
    [badVote, vote] := rfl

private def parentA : Block 1 := .node .genesis 1 ⟨7⟩ [] [vote] []
private def parentB : Block 1 := .node .genesis 1 ⟨7⟩ [] [vote, vote] []
example : parentA.embed ≠ parentB.embed := by
  intro h
  have := embed_injective h
  contradiction

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
example : phaseTime 2 3 5 = phaseTime 2 4 1 := by decide
example : tick (fun x : Nat => 10 * x + 1) (fun x => 10 * x + 2)
    (fun x => 10 * x + 3) (fun x => 10 * x + 4) 0 = 1234 := by decide
example : onBlock false (fun _ : Nat => none) (fun x : Nat => x + 1) (3, 4) = (3, 4) := rfl

end AvailableChain.FGSA.Spec.Tests
