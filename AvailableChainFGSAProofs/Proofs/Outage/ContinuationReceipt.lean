module
public import AvailableChainFGSARun.Proofs.ReceiptCoverage
public import AvailableChainFGSAClaims.Statements.Reads

public section

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG Gen.Pure

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}
    {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}

/-- OUTPUT-DIRECT §§3,6. DC: INTENTIONAL; each ancestor of a held block
has its own earlier acceptance trigger. The source cutoff is inclusive. -/
theorem outageV_source_path (hsch : V2.D.ScheduleWellFormed E rho)
    {k : Nat} {y : V} {K : Block} {u : Time}
    (hK : K ∈ (storeAt p c E rho k y).base.blocks)
    (hcut : ∀ l < k, ∀ e, rho.events[l]? = some e → e.time ≤ u) :
    ∀ b, Block.Preceq b K → b ≠ .genesis →
      ∃ l < k, ∃ t o, blockOf? p o = some b ∧
        V2.D.Run.acceptsAt E rho l y o t ∧ 0 ≤ t ∧ t ≤ u := by
  intro b hb hne
  have hc := (storeBundle_stateBefore E rho k y).cstore
  obtain ⟨Kfg, hKfg, he⟩ := (hc.baseTree K).mp hK
  rw [← he] at hb
  obtain ⟨Bfg, hBfg, heB⟩ := eraseFG_ancestor_mem hc.fg.closed hKfg hb
  have hbm := (hc.baseTree b).mpr ⟨Bfg, hBfg, heB⟩
  rw [← (storeBundle_stateBefore E rho k y).«meta».stampKeys] at hbm
  obtain ⟨⟨b', stamp⟩, hstamp, he'⟩ := List.mem_map.mp hbm
  dsimp only at he'
  subst b'
  rcases fgsa_block_stamp_source E rho k y b stamp hstamp with hg | ⟨l, hl, t, o, ho, ha, _⟩
  · exact (hne hg.1).elim
  · obtain ⟨parent, hd, _⟩ := ha.1
    exact ⟨l, hl, t, o, ho, ha, (hsch.in_horizon _ (List.mem_of_getElem? hd)).1,
      hcut l hl _ hd⟩

/-- OUTPUT-DIRECT §§3,6. DC: INTENTIONAL; full-run relay gives path
coverage at any deadline after max(source cutoff,GST)+delta. This generalizes
the private gate_path_coverage construction in WeakContinuation/StepGateBatch.
It includes acceptances before GST and uses compatibility with F. -/
theorem outageV_path_coverage (hE : V2.D.ExecutionValid E rho) (hDelta : E.Δ = p.Δ)
    {ΔF : Time} (hsync : Gen.V2.Duty.PartialSynchronyBy E rho (fgsaDelay E.Δ ΔF))
    {k : Nat} {x y : V} {K : Block} {u D : Time}
    (hy : y ∈ rho.honest) (hK : K ∈ (storeAt p c E rho k y).base.blocks)
    (hcut : ∀ l < k, ∀ e, rho.events[l]? = some e → e.time ≤ u)
    (hdeadline : max u E.t_GST + p.Δ ≤ D) (hhor : D ≤ rho.horizon)
    (hF : ∀ j, j ≤ V2.D.Run.idxBefore rho D → Block.Compatible K (F_at p c E rho j x)) :
    ∃ required paths,
      ReceiptCoveragePremises E rho (fun t => max t E.t_GST + p.Δ) rho.horizon
        D 0 x K required paths ∧ paths K D := by
  let required := fun o t => ∃ l < k, V2.D.Run.acceptsAt E rho l y o t ∧
    ∃ b, blockOf? p o = some b ∧ Block.Preceq b K
  let paths := fun B d => B = K ∧ d = D
  have htime : ∀ o t, required o t → 0 ≤ t ∧ t ≤ u := by
    rintro o t ⟨l, hl, ha, _⟩
    obtain ⟨parent, hd, _⟩ := ha.1
    exact ⟨(hE.toScheduleWellFormed.in_horizon _ (List.mem_of_getElem? hd)).1, hcut l hl _ hd⟩
  have hbound : ∀ t, t ≤ u → max t E.t_GST + p.Δ ≤ D := by
    intro t ht
    exact (add_le_add (max_le_max ht le_rfl) le_rfl).trans hdeadline
  refine ⟨required, paths, ?_, rfl, rfl⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [hDelta] using Gen.V2.Duty.deliveryWithinOn_of_partialSynchronyBy E rho hsync
      (fun o => ¬ isRowObject o) E.Δ (fgsaDelay_nonrow E.Δ _)
  · intro o t hr
    obtain ⟨l, _, ha, b, hb, _⟩ := hr
    obtain ⟨parent, he, hh⟩ := ha.1
    refine ⟨Or.inr ⟨y, hy, l, ha⟩,
      handles_wellFormed p c _ parent o hh (hE.wire l y parent t he), ?_⟩
    intro r a B hv
    have hn : blockOf? p o = none := by
      change (match (toWire p o).decode with | some (.block _ N) => some N.erase | _ => none) = _
      rw [hv]
    rw [hn] at hb
    contradiction
  · intro j _ hj
    exact hF j hj
  · refine ⟨fun _ _ hab => add_le_add (max_le_max hab le_rfl) le_rfl,
      hhor, le_rfl, Nat.zero_le _, ?_, ?_, ?_⟩
    · intro o t hr
      exact ⟨Nat.zero_le _, (htime o t hr).1,
        (le_max_left _ _).trans_lt (lt_add_of_pos_right _ p.deltaPos),
        hbound t (htime o t hr).2⟩
    · rintro B d ⟨hBK, hdD⟩
      subst B
      subst d
      refine ⟨block_preceq_refl K, le_rfl, ?_⟩
      intro b hb hne
      obtain ⟨l, hl, t, o, ho, ha, _, ht⟩ :=
        outageV_source_path hE.toScheduleWellFormed hK hcut b hb hne
      have hdecode : ∃ r N, N.erase = b ∧ (toWire p o).decode = some (.block r N) := by
        change (match (toWire p o).decode with
          | some (.block _ N) => some N.erase | _ => none) = _ at ho
        cases he : (toWire p o).decode with
        | none => rw [he] at ho; contradiction
        | some m =>
          cases m <;> simp only [he, reduceCtorEq, Option.some.injEq] at ho
          exact ⟨_, _, ho, rfl⟩
      obtain ⟨r, N, heN, hdec⟩ := hdecode
      exact ⟨o, t, r, N, heN, ⟨l, hl, ha, b, ho, hb⟩, hdec, hbound t ht⟩
    · intro o t r N hr hdec
      obtain ⟨l, hl, ha, b', hb', hBK⟩ := hr
      have hb : blockOf? p o = some N.erase := by
        change (match (toWire p o).decode with | some (.block _ N) => some N.erase | _ => none) = _
        rw [hdec]
      have heq := Option.some.inj (hb'.symm.trans hb)
      subst b'
      exact ⟨K, D, ⟨rfl, rfl⟩, hBK⟩

/-- OUTPUT-DIRECT §7. DC: INTENTIONAL; a received compatible HEAD path
is active even when its target is a strict ancestor of the receiver's F. -/
theorem outageV_active_path_of_coverage (hE : V2.D.ExecutionValid E rho)
    (hN : V2.D.NoRestart rho) (hDelta : E.Δ = p.Δ)
    (dl : Time → Time) (cut D : Time) (first : Nat) (x : V) (K : Block)
    (required : Obj p → Time → Prop) (paths : Block → Time → Prop)
    (hx : x ∈ rho.honest)
    (hcov : ReceiptCoveragePremises E rho dl cut D first x K required paths)
    (hpath : paths K D)
    (hKF : Block.Compatible K (eraseFG (V2.D.Run.stateBeforeTime E rho D x).st.fg.F))
    (hroots : NamedRootCollisionFree p c E rho) :
    ∀ X, Block.Preceq X K → X ∈ (actView (V2.D.Run.stateBeforeTime E rho D x).st).blocks := by
  let st := (V2.D.Run.stateBeforeTime E rho D x).st
  have hc := (fgsa_receiptCoverage E rho dl cut D first x K required paths
    hroots hDelta hE hN hx hcov).1
  have hb := (storeBundle_stateBeforeTime E rho D x).cstore
  have hK : K ∈ (actView st).blocks := by
    rcases hc with ⟨hbelow, _⟩ | ⟨_, _, hpaths⟩
    · exact actView_ancestor_closed p st hb ((actView_genesis_F p st hb).2) hbelow
    · obtain ⟨Y, hY, hYK⟩ := hpaths K D hpath K (block_preceq_refl K)
      exact (actView_blocks st K).mpr ⟨(hb.baseTree K).mpr ⟨Y, hY, hYK⟩, hKF⟩
  intro X hX
  exact actView_ancestor_closed p st hb hK hX

end AvailableChain.FGSA.Run
end
