module
public import AvailableChainFGSA.Model.Spec.Transitions
public import AvailableChainFGSA.Proofs.Spec.Codec

@[expose] public section

namespace AvailableChain.FGSA.Spec

/-- A failed signature decode is refused by the unchanged delivery handler. -/
theorem process_decode_refused (p : Params) (st : State p.n) (o : Wire p.n)
    (h : o.decode = none) : process p st o.embed = st := by
  simp [process, decode_embedding, h]

/-- Exact recursive parent membership is preserved, even on adversarial inputs. -/
theorem parent_membership (B : Block n) (held : List (Block n)) :
    B.embed.parent ∈ held.map Block.embed ↔ B.parent ∈ held := by
  simp [embed_injective.eq_iff]

/-- Once authenticated, the attestation handler is the spec's ordered set insert. -/
theorem admitRow_pool (p : Params) (st : State p.n) (a : RowWire p.n)
    (h : a.decode?.isSome = true) :
    (admitRow p st a).rowPool = insertRow st.rowPool a := by
  unfold admitRow insertRow
  cases hd : a.decode? with
  | none => simp [hd] at h
  | some x =>
      simp only
      split <;> rfl

/-- Lean normalization represents the core record, before any saved-head clamp. -/
theorem normalized_record (st : State n) :
    (normalizeS st).base.stableRecord = normalizeRecord (eraseFG st.fg.F) st.base.stableRecord := by
  unfold normalizeS normalizeRecord
  split <;> rfl

theorem advance_embedding (tree : List AvailableChain.Block)
    (old C : AvailableChain.Block) (h : old ∈ tree) :
    advance tree old (some C) = GridCO.advance old C := by
  simp [advance, GridCO.advance, h]

theorem onBlock_future {σ α : Type} (fg : σ → Option σ) (ac : α → α) (state : σ × α) :
    onBlock true fg ac state = state := rfl

theorem onBlock_refused {σ α : Type} (fg : σ → Option σ) (ac : α → α) (state : σ × α)
    (h : fg state.1 = none) : onBlock false fg ac state = state := by
  simp [onBlock, h]

theorem onBlock_accepted {σ α : Type} (fg : σ → Option σ) (ac : α → α)
    (state : σ × α) (next : σ) (h : fg state.1 = some next) :
    onBlock false fg ac state = (next, ac state.2) := by
  simp [onBlock, h]

end AvailableChain.FGSA.Spec
end
