module
public import AvailableChainFGSARun.Model.Families

@[expose] public section
namespace AvailableChain.FGSA.Run

/-- Every pool row and every row in a stored proposal passes the row check. -/
def EmissionRowsValid {p : Params} (st : State p.n) : Prop :=
  (∀ a ∈ st.rowPool, a.valid = true) ∧
    ∀ w ∈ st.proposals, ∀ s b raw sup rows,
      w.decode = some (.block s b raw sup rows) → ∀ a ∈ rows, a.valid = true

/-- Decode the application value of a block. -/
def decode {In : Type} (c : AppCodec In) (b : Block) : Option In :=
  c.unapp (appOf b.body)

/-- The wire check holds for every object released by an honest awake node. -/
def HonestEmissionWellFormed (p : Params) {In V : Type} [DecidableEq V]
    (c : AppCodec In) (E : Generic.Env V) (rho : V2.Run V (fgsa p c)) : Prop :=
  ∀ i v t, rho.events[i]? = some (.tick v t) → v ∈ rho.honest →
    E.awake v t = true → ∀ o ∈ V2.Run.emitsAt E rho i, (fgsa p c).wellFormed o = true

/-- Each released proposal decodes to its proposer's input at that tick. -/
def HonestProposalDecodes (p : Params) {In V : Type} [DecidableEq V]
    (c : AppCodec In) (E : Generic.Env V) (rho : V2.Run V (fgsa p c)) : Prop :=
  ∀ i v s, rho.events[i]? = some (.tick v (SA.proposalTime p.toParams s)) →
    0 < s → v = rho.seatOf (.prop s) ⟨0, Nat.one_pos⟩ →
    E.awake v (SA.proposalTime p.toParams s) = true →
    ∀ b raw sup rows,
      (⟨.seat (.prop s) ⟨0, Nat.one_pos⟩, .proposal b raw sup rows⟩ : Obj p) ∈
        V2.Run.emitsAt E rho i → decode c b = some (rho.input v (SA.proposalTime p.toParams s))

end AvailableChain.FGSA.Run
end
