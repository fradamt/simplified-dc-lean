module
public import AvailableChainFGSARun.Proofs.Reachable
public import AvailableChainFGSARun.Statements.Roots

@[expose] public section

namespace AvailableChain.FGSA.Run.Tests.DigestScope

/-- ROOT-DIGEST W3: small roots for the positive finite body scope. -/
abbrev pT : Params :=
  { Δ := 1, n := 4, k := 2, η := 11, deltaPos := by decide, nPos := by decide,
    kLarge := by decide, etaNonneg := by decide,
    R := 2, δt := 1, RLarge := by decide, digest := fun d => ⟨d.slot + 1⟩ }

def ba : Block := .node .genesis 4 ⟨5⟩ (packBody 0 ([] : List (RowWire 4)))


def env : Generic.Env (Fin 1) := ⟨1, by decide, 0, le_rfl, fun _ _ => true⟩

def traceRun (p : Params) (es : List (V2.Event (Fin 1) (Obj p))) :
    V2.D.Run (Fin 1) (fgsa p unitCodec) where
  honest := ∅
  horizon := 20
  events := es
  seatOf := fun _ _ => 0
  input := fun _ _ => ()

/-- ROOT-DIGEST W3: two locally valid bodies share one deliberately colliding digest. -/
abbrev collisionParams : Params := { pT with digest := fun _ => ⟨77⟩ }
def collisionA : Block := proposalBlock collisionParams .genesis 1 0 [] [] []
def collisionB : Block := proposalBlock collisionParams .genesis 1 1 [] [] []
def collisionWireA : Wire 4 := ⟨.proposer 1, .proposal collisionA [] [] []⟩
def collisionWireB : Wire 4 := ⟨.proposer 1, .proposal collisionB [] [] []⟩
def collisionRun := traceRun collisionParams
  [.deliver 0 (ofWire collisionParams collisionWireA) 4, .deliver 0 (ofWire collisionParams
      collisionWireB) 4]

/-- ROOT-DIGEST W3: each separate store admits its colliding body. -/
theorem body_collision_admitted :
    collisionA ∈ (process collisionParams (clock collisionParams (initial 4) 4)
      collisionWireA).base.blocks ∧
    collisionB ∈ (process collisionParams (clock collisionParams (initial 4) 4)
      collisionWireB).base.blocks ∧
    contentOk collisionParams collisionA [] [] [] = true ∧
    contentOk collisionParams collisionB [] [] [] = true := by decide +kernel

/-- ROOT-DIGEST W3: local reachability cannot supply the two-body run premise. -/
theorem body_collision_control :
    Reachable collisionParams (process collisionParams (clock collisionParams (initial 4) 4)
      collisionWireA) ∧
    Reachable collisionParams (process collisionParams (clock collisionParams (initial 4) 4)
      collisionWireB) ∧
    ¬ NamedRootCollisionFree collisionParams unitCodec env collisionRun := by
  refine ⟨.deliver _ (.tick _ .init), .deliver _ (.tick _ .init), ?_⟩
  intro h
  have hA : RootBlockInRun collisionParams unitCodec env collisionRun collisionA :=
    ⟨collisionA, Or.inl ⟨0, ofWire collisionParams collisionWireA, 4, [], [], [], by decide +kernel,
        rfl⟩,
      by decide +kernel⟩
  have hB : RootBlockInRun collisionParams unitCodec env collisionRun collisionB :=
    ⟨collisionB, Or.inl ⟨0, ofWire collisionParams collisionWireB, 4, [], [], [], by decide +kernel,
        rfl⟩,
      by decide +kernel⟩
  have he := h.root_injective collisionA collisionB hA hB collisionA collisionB
    (Or.inl (by decide +kernel)) (Or.inr (by decide +kernel)) rfl
  exact (by decide +kernel : collisionA ≠ collisionB) he

/-- ROOT-DIGEST W3: the fabricated HEAD target reuses genesis root 0. -/
def fakeHeadBody : Block := .node .genesis 1 genesisRoot (packBody 0 ([] : List (RowWire 4)))
def fakeHead : HeadWire 4 := ⟨.seat (.head 3) 0, fakeHeadBody⟩
def headWire : Wire 4 := ⟨fakeHead.auth, .head fakeHeadBody⟩
def headProposal : Wire 4 := ⟨.proposer 4, .proposal ba [fakeHead] [fakeHead] []⟩
def headRun := traceRun pT [.deliver 0 (ofWire pT headWire) 16, .deliver 0 (ofWire pT headProposal)
    16]

/-- ROOT-DIGEST W3: direct body scope contains only ba, despite both HEAD forms. -/
theorem head_direct_scope (B : Block) (h : DirectRootBlockInRun pT unitCodec env headRun B) :
    B = ba := by
  rcases h with ⟨v, o, t, raw, sup, rows, hm, hp⟩ | ⟨v, hv, _⟩
  · change V2.Event.deliver v o t ∈
      [.deliver 0 (ofWire pT headWire) 16, .deliver 0 (ofWire pT headProposal) 16] at hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with ⟨_, rfl, _⟩ | ⟨_, rfl, _⟩
    · cases hp
    · exact (Msg.proposal.inj hp).1.symm
  · exact (Finset.notMem_empty v hv).elim

/-- ROOT-DIGEST W3: structural scope inclusion precedes the finite root check. -/
theorem head_body_scope (B : Block) (h : RootBlockInRun pT unitCodec env headRun B) :
    B ∈ ([.genesis, ba] : List Block) := by
  obtain ⟨tip, ht, hb⟩ := h
  rw [head_direct_scope tip ht] at hb
  simpa only [ba, Block.Preceq, Block.preceq, Bool.or_eq_true, decide_eq_true_eq,
    List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false, false_or, or_comm] using hb

/-- ROOT-DIGEST W3: a HEAD-only genesis collision adds no body-root obligation. -/
theorem head_scope_control : NamedRootCollisionFree pT unitCodec env headRun ∧
    ¬ RootBlockInRun pT unitCodec env headRun fakeHeadBody := by
  have closed : ∀ B ∈ ([.genesis, ba] : List Block), ∀ A, Block.Preceq A B →
      A ∈ ([.genesis, ba] : List Block) := by
    intro B hB A hA
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hB
    rcases hB with rfl | rfl
    · have he : A = .genesis := of_decide_eq_true hA
      rw [he]; exact List.mem_cons_self
    · simpa only [ba, Block.Preceq, Block.preceq, Bool.or_eq_true, decide_eq_true_eq,
        List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false, false_or, or_comm] using hA
  constructor
  · constructor
    intro B C hB hC A D hA hD hr
    have mem (X : Block) (hX : Block.Preceq X B ∨ Block.Preceq X C) :
        X ∈ ([.genesis, ba] : List Block) := by
      rcases hX with hX | hX
      · exact closed B (head_body_scope B hB) X hX
      · exact closed C (head_body_scope C hC) X hX
    have hinj : ∀ X ∈ ([.genesis, ba] : List Block),
        ∀ Y ∈ ([.genesis, ba] : List Block), X.root = Y.root → X = Y := by
      decide +kernel
    exact hinj A (mem A hA) D (mem D hD) hr
  · intro h
    exact (by decide +kernel : fakeHeadBody ∉ ([.genesis, ba] : List Block))
      (head_body_scope fakeHeadBody h)

#print axioms body_collision_admitted
#print axioms body_collision_control
#print axioms head_direct_scope
#print axioms head_body_scope
#print axioms head_scope_control

end AvailableChain.FGSA.Run.Tests.DigestScope
end
