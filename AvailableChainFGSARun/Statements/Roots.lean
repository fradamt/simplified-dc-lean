module
public import AvailableChainFGSARun.Model.Protocol
public import AvailableChainEngineV2.Engine.Duty.Run

@[expose] public section

namespace AvailableChain.FGSA.Run

variable (p : Params) {In V : Type} (c : AppCodec In) [DecidableEq V]
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

/-- [ROOT-DIGEST W1; DC NamedRun.directBlockInRun] Delivered and honest-held bodies. -/
def DirectRootBlockInRun (B : Block) : Prop :=
  (∃ x o t raw support rows,
    V2.Event.deliver x o t ∈ rho.events ∧
    o.payload = Msg.proposal B raw support rows) ∨
  (∃ x ∈ rho.honest, ∃ i : Nat,
    B ∈ (V2.D.Run.stateBefore E rho i x).st.base.blocks)

/-- [ROOT-DIGEST W1; DC NamedRun.blockInRun] Ancestors of scoped bodies. -/
def RootBlockInRun (A : Block) : Prop :=
  ∃ B : Block, DirectRootBlockInRun p c E rho B ∧ Block.Preceq A B

/-- [ROOT-DIGEST W1; DC NamedRootCollisionFree] One run premise on body ancestors. -/
structure NamedRootCollisionFree : Prop where
  root_injective : ∀ B C : Block,
    RootBlockInRun p c E rho B → RootBlockInRun p c E rho C →
    ∀ A D : Block,
      (Block.Preceq A B ∨ Block.Preceq A C) →
      (Block.Preceq D B ∨ Block.Preceq D C) → A.root = D.root → A = D

end AvailableChain.FGSA.Run
end
