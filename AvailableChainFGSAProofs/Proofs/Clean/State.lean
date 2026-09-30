module
public import AvailableChainFGSAProofs.Proofs.Clean.Chain
public import AvailableChainFGSAProofs.Proofs.Shared.Reads
public import AvailableChainFGSARun.Proofs.ClientTrace

public section

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG

variable {p : Params} {In V : Type} {c : AppCodec In} [DecidableEq V]
    {E : Generic.Env V} {rho : V2.Run V (fgsa p c)}

/-- A non-gate event adds no completed result. -/
theorem cleanResults_eq_of_noGate {i : Nat}
    (hn : ∀ x s, ¬ IsGateTick p c rho i x s) :
    cleanResults p c E rho (i + 1) = cleanResults p c E rho i := by
  ext ⟨s, B⟩
  rw [cleanResults_mem_succ_iff]
  constructor
  · rintro (h | ⟨x, hx, _⟩)
    · exact h
    · exact (hn x s hx).elim
  · exact Or.inl

/-- All four history fields persist at a non-gate event. -/
theorem cleanHist_step_of_noGate {i : Nat}
    (hn : ∀ x s, ¬ IsGateTick p c rho i x s)
    (hh : CleanHist p c E rho i) : CleanHist p c E rho (i + 1) := by
  have he := cleanResults_eq_of_noGate (E := E) hn
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [he] using hh.ordered
  · simpa only [he] using hh.same
  · intro j x s hj hx
    have hji : j < i := by
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj) with h | rfl
      · exact h
      · exact (hn x s hx).elim
    exact hh.nonempty j x s hji hx
  · intro j k x y s B hj hk hx hy hB
    have hji : j < i := by
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj) with h | rfl
      · exact h
      · exact (hn x s hx).elim
    exact hh.continues j k x y s B hji hk hx hy hB

omit [DecidableEq V] in
private theorem delivery_noGate {i : Nat} {v : V} {o} {t : Time}
    (he : rho.events[i]? = some (.deliver v o t)) :
    ∀ x s, ¬ IsGateTick p c rho i x s := by
  intro x s hx
  change rho.events[i]? = some (.tick x _) at hx
  rw [he] at hx
  cases hx

/-- Every delivery, including an admitted block, preserves history. -/
theorem cleanHist_step_delivery {i : Nat} {v : V} {o} {t : Time}
    (he : rho.events[i]? = some (.deliver v o t))
    (hh : CleanHist p c E rho i) : CleanHist p c E rho (i + 1) :=
  cleanHist_step_of_noGate (delivery_noGate he) hh

/-- A tick without a gate preserves the completed history. -/
theorem cleanHist_step_noGateTick {i : Nat} {v : V} {t : Time}
    (he : rho.events[i]? = some (.tick v t)) (hn : isGateTime p t = false)
    (hh : CleanHist p c E rho i) : CleanHist p c E rho (i + 1) := by
  apply cleanHist_step_of_noGate ?_ hh
  intro x s hx
  change rho.events[i]? = some (.tick x _) at hx
  have ht := (V2.Event.tick.inj (Option.some.inj (he.symm.trans hx))).2
  have hg := (isGateTime_iff p t).mpr ⟨s, ht.symm⟩
  rw [hn] at hg
  cases hg

/-- A vote, row, or refused block keeps every state field used by the SA origins.
The vote case uses the FG-SA store wrappers for GridCO admission. -/
theorem clean_delivery_fields {j : Nat} {v : V} {o} {t : Time}
    (he : rho.events[j]? = some (.deliver v o t))
    (href : ∀ s b raw support rows P,
      (toWire p o).decode = some (.block s b raw support rows) →
      parentFG (storeAt p c E rho j v) b = some P →
      blockAccepted p (storeAt p c E rho j v) s b P rows = false) :
    let a := storeAt p c E rho j v
    let b := storeAt p c E rho (j + 1) v
    b.fg = a.fg ∧ b.base.stableRecord = a.base.stableRecord ∧
      b.base.obligations = a.base.obligations ∧ b.base.genuine = a.base.genuine ∧
      b.fastWrite = a.fastWrite := by
  have hstore : storeAt p c E rho (j + 1) v =
      FGSA.process p (storeAt p c E rho j v) (toWire p o) := by
    change (V2.Run.stateBefore E rho (j + 1) v).st = _
    rw [V2.Run.stateBefore_succ E rho he]
    simp only [V2.World.step, Function.update_self]
    rfl
  dsimp only
  rw [hstore]
  generalize hw : toWire p o = w at href ⊢
  change (let b := match w.decode with
    | some (.vote s k B) => admitHead p (storeAt p c E rho j v) s k B
    | some (.row _ _ body) => admitRow p (storeAt p c E rho j v) ⟨w.auth, body⟩
    | some (.block s B raw sup rows) => admitBlock p (storeAt p c E rho j v) s B raw sup rows
    | none => storeAt p c E rho j v
    b.fg = _ ∧ b.base.stableRecord = _ ∧ b.base.obligations = _ ∧
      b.base.genuine = _ ∧ b.fastWrite = _)
  cases hd : w.decode with
  | none => exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  | some input =>
    cases input with
    | vote s k B =>
      exact ⟨admitHead_fg p _ s k B, admitHead_base_stable p _ s k B,
        admitHead_obligations p _ s k B, admitHead_genuine p _ s k B,
        admitHead_fastWrite p _ s k B⟩
    | row r k body =>
      dsimp only
      rcases admitRow_eq p (storeAt p c E rho j v) ⟨w.auth, body⟩ with hr | hr <;>
        rw [hr] <;> exact ⟨rfl, rfl, rfl, rfl, rfl⟩
    | block s B raw sup rows =>
      have hr : admitBlock p (storeAt p c E rho j v) s B raw sup rows =
          storeAt p c E rho j v := by
        apply admitBlock_refused
        cases hP : parentFG (storeAt p c E rho j v) B with
        | none => exact Or.inl rfl
        | some P => exact Or.inr ⟨P, rfl, href s B raw sup rows P hd hP⟩
      dsimp only
      rw [hr]
      exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- K1 lifted to an admitted block event. The three compatibility premises
are the obligations left for the source-origin argument. Due rows are included. -/
theorem clean_block_reconcile {j : Nat} {v : V} {o} {t : Time}
    {s : Slot} {B : Block} {raw support : List (HeadWire p.n)}
    {rows : List (RowWire p.n)} {P : FGBlock (Fin p.n)}
    (he : rho.events[j]? = some (.deliver v o t))
    (hd : (toWire p o).decode = some (.block s B raw support rows))
    (hP : parentFG (storeAt p c E rho j v) B = some P)
    (ha : blockAccepted p (storeAt p c E rho j v) s B P rows = true)
    (hL : ∀ row ∈ (storeAt p c E rho j v).base.obligations,
      Block.Compatible row.1 (F_at p c E rho (j + 1) v))
    (hG : ∀ r C, (r, some C) ∈ (storeAt p c E rho j v).base.genuine →
      Block.Compatible C (F_at p c E rho (j + 1) v))
    (hS : Block.Compatible (S_at p c E rho j v) (F_at p c E rho (j + 1) v)) :
    (storeAt p c E rho (j + 1) v).base.obligations = (storeAt p c E rho j v).base.obligations ∧
    (storeAt p c E rho (j + 1) v).base.genuine = (storeAt p c E rho j v).base.genuine ∧
    (storeAt p c E rho (j + 1) v).fastWrite = (storeAt p c E rho j v).fastWrite ∧
    Block.Preceq (S_at p c E rho j v) (S_at p c E rho (j + 1) v) := by
  have hstore : storeAt p c E rho (j + 1) v =
      admitBlock p (storeAt p c E rho j v) s B raw support rows := by
    change (V2.Run.stateBefore E rho (j + 1) v).st = _
    rw [V2.Run.stateBefore_succ E rho he]
    simp only [V2.World.step, Function.update_self]
    change (match (toWire p o).decode with
      | some (.vote r k b) => admitHead p (storeAt p c E rho j v) r k b
      | some (.row _ _ body) => admitRow p (storeAt p c E rho j v) ⟨(toWire p o).auth, body⟩
      | some (.block r b raw sup rows) => admitBlock p (storeAt p c E rho j v) r b raw sup rows
      | none => storeAt p c E rho j v) = _
    rw [hd]
  change (∀ row ∈ (storeAt p c E rho j v).base.obligations,
    Block.Compatible row.1 (eraseFG (storeAt p c E rho (j + 1) v).fg.F)) at hL
  change (∀ r C, (r, some C) ∈ (storeAt p c E rho j v).base.genuine →
    Block.Compatible C (eraseFG (storeAt p c E rho (j + 1) v).fg.F)) at hG
  change Block.Compatible (storeAt p c E rho j v).base.stableRecord
    (eraseFG (storeAt p c E rho (j + 1) v).fg.F) at hS
  change _ ∧ _ ∧ _ ∧ Block.Preceq (storeAt p c E rho j v).base.stableRecord
    (storeAt p c E rho (j + 1) v).base.stableRecord
  rw [hstore] at hL hG hS ⊢
  exact admitBlock_reconcile_harmless p _ (cstoreInv_stateBefore E rho j v)
    s B raw support rows P hP ha hL hG hS

/-- Expiry and release remove targets. Cache and own-record writes keep the
FG state, output, genuine results, and fast-write history. -/
theorem clean_noGate_fields {j : Nat} {v : V} {t : Time}
    (he : rho.events[j]? = some (.tick v t)) (hn : isGateTime p t = false) :
    let a := storeAt p c E rho j v
    let b := storeAt p c E rho (j + 1) v
    b.fg = a.fg ∧ b.base.stableRecord = a.base.stableRecord ∧
      b.base.obligations.Sublist a.base.obligations ∧ b.base.genuine = a.base.genuine ∧
      b.fastWrite = a.fastWrite := by
  have hstore : storeAt p c E rho (j + 1) v = clockPre p (storeAt p c E rho j v) t := by
    change (V2.Run.stateBefore E rho (j + 1) v).st = _
    rw [V2.Run.stateBefore_succ E rho he]
    simp only [V2.World.step, Function.update_self]
    rw [tick_st (c := c) E rho (V2.Run.stateBefore E rho j v) v t]
    change (if isGateTime p t then _ else _) = _
    rw [hn]
    rfl
  dsimp only
  rw [hstore]
  exact ⟨clockPre_fg p _ t, clockPre_stable p _ t, clockPre_obligations_sublist p _ t,
    clockPre_genuine p _ t, clockPre_fastWrite p _ t⟩

variable [Fintype V]

/-- These state fields hold at every index, independently of Clean history. -/
theorem cleanState_index_facts {b₀ : Time} (h : CleanCut₂ p c E rho b₀)
    (hf : FGFoundation p c E rho) (i : Nat) :
    (∀ v, v ∈ rho.honest → FGSA.NestOK (storeAt p c E rho i v)) ∧
    (∀ v, v ∈ rho.honest → FGSA.CStoreInv p (storeAt p c E rho i v)) ∧
    (∀ v, v ∈ rho.honest → FGSA.controls p (storeAt p c E rho i v) =
      fjControls p.E p.cfg (storeAt p c E rho i v).fg.F (storeAt p c E rho i v).fg.TF) ∧
    (∀ v, v ∈ rho.honest → EmittedRowsNoSlash p c E rho v) := by
  exact ⟨fun v _ => nestOK_stateBefore E rho i v,
    fun v hv => (hf.store i v hv).1,
    fun v hv => (hf.frame i v hv).1,
    emittedRowsNoSlash E rho h.base.linked⟩

end AvailableChain.FGSA.Run
end
