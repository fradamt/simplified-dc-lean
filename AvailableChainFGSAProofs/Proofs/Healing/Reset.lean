module
public import AvailableChainFGSAProofs.Proofs.Healing.ResetCut
public import AvailableChainFGSAProofs.Proofs.Healing.FrontierSearchDefs

public section

/-! Blueprint 21 H.11:1744–1800, H.22:3229–3241; S5 J8 R1–R3.
DC: INTENTIONAL inclusive SA cut and the first honest height-(M+1) row.
R1/R2 STOP: FrontierSearchStatement has no exposed body or eliminator.
The named input is HG.5: producer HG4-RISE F3 (lf-hg4).
The budget definitions also have no exposed bodies or equation exports.
R3 uses their explicit integer charges. No frozen interface is changed.
The source input is INLINE: producer sourceDiscipline_emittedName,
projected through heightView_eq_simplex. It keeps the actual source and root.
No progress-attempt statement or full-H0 proposal service is used. -/

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

/-- Blueprint 21 H.11:1791–1797; S5 J8 R3.
DC: SAME the two HG.5 charges, with all subtraction in integer time. -/
theorem healing_reset_budget_sum (p : Params) (G ΔF ρbar : Time) :
    B_resetF p ΔF G ρbar = 3 * P p +
      (E_gF p ΔF G ρbar + E_jF p ΔF G ρbar + B_cF p ΔF G ρbar) +
      (E_gF p ΔF G ρbar + E_jF p ΔF G ρbar + D_cF p ρbar) := by
  unfold B_resetF
  ring

/-- Blueprint 21 H.11:1791–1797; S5 J8 R3.
DC: SAME choose the allowance that attains the frozen minimum. -/
theorem healing_reset_budget_choice (p : Params) (G ΔF : Time) :
    ∃ ρbar, (ρbar = ρΓ p G ∨ (ρbar = ρ₁ p G ∧ p.k ≤ 2 * p.R + 1)) ∧
      B'_resetF p ΔF G = 3 * P p +
        (E_gF p ΔF G ρbar + E_jF p ΔF G ρbar + B_cF p ΔF G ρbar) +
        (E_gF p ΔF G ρbar + E_jF p ΔF G ρbar + D_cF p ρbar) := by
  by_cases hk : p.k ≤ 2 * p.R + 1
  · by_cases hle : B_resetF p ΔF G (ρΓ p G) ≤ B_resetF p ΔF G (ρ₁ p G)
    · refine ⟨ρΓ p G, Or.inl rfl, ?_⟩
      rw [B'_resetF_def, ite_eq_left hk, min_eq_left hle]
      exact healing_reset_budget_sum p G ΔF (ρΓ p G)
    · refine ⟨ρ₁ p G, Or.inr ⟨rfl, hk⟩, ?_⟩
      rw [B'_resetF_def, ite_eq_left hk, min_eq_right (le_of_not_ge hle)]
      exact healing_reset_budget_sum p G ΔF (ρ₁ p G)
  · refine ⟨ρΓ p G, Or.inl rfl, ?_⟩
    rw [B'_resetF_def, ite_eq_right hk]
    exact healing_reset_budget_sum p G ΔF (ρΓ p G)

/-- Blueprint 21 H.11:1791–1797; S5 J8 R3.
DC: SAME the strict cut bound gives the strict frozen minimum deadline. -/
theorem healing_reset_budget_lt (p : Params) (G ΔF GST u₀ : Time)
    (hcut : u₀ < GST + 3 * P p) :
    ∃ ρbar, (ρbar = ρΓ p G ∨ (ρbar = ρ₁ p G ∧ p.k ≤ 2 * p.R + 1)) ∧
      u₀ + (E_gF p ΔF G ρbar + E_jF p ΔF G ρbar + B_cF p ΔF G ρbar) +
        (E_gF p ΔF G ρbar + E_jF p ΔF G ρbar + D_cF p ρbar) <
        GST + B'_resetF p ΔF G := by
  obtain ⟨ρbar, hallow, hbudget⟩ := healing_reset_budget_choice p G ΔF
  refine ⟨ρbar, hallow, ?_⟩
  rw [hbudget]
  linarith only [hcut]

variable (p : Params) {In V : Type} [DecidableEq V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

section Source

variable
    (emittedName : ∀ {j : Nat} {x : V} {r : Nat} {a : RowWire p.n}
      {e : Height × BlockId}, HonestRowAt p c E rho j x r a →
      namedEntry a.payload.height_pair = some e →
      ∃ C G, actionSourceFG p c E rho x r = some (some C) ∧
        e = ((heightView p C).h, (heightView p C).T_h.root) ∧
        gateResult p c E rho x (r * p.R) = some (some G) ∧
        Block.Preceq (eraseFG C) G ∧ fastAt p c E rho x (r * p.R) (eraseFG C))

include emittedName

/-- Blueprint 21 H.11:1755–1756; S5 J8 R1 rowCap.
DC: SAME the closed cap. INLINE producer: sourceDiscipline_emittedName. -/
theorem healing_reset_rowCap (hs : V2.D.ScheduleWellFormed E rho)
    (hnr : V2.D.NoRestart rho) :
    ∀ j y r a h e t, HonestRowAt p c E rho j y r a →
      rho.events[j]? = some (.tick y t) → t ≤ resetCutTime p E →
      namedEntry a.payload.height_pair = some (h, e) → h ≤ resetCutFrontier p c E rho := by
  intro j y r a h e t ha hj ht he
  rw [reset_frontier]
  apply reset_row_cap p c E rho hs hnr _ ha hj ht he
  intro j x r a e ha he
  obtain ⟨C, G, hC, hh, hG, hCG, hf⟩ := emittedName ha he
  exact ⟨C, G, hC, congrArg Prod.fst hh, hG, hCG, hf⟩

/-- Blueprint 21 H.11:1754–1756,1772–1777; S5 J8 R1 mu_le.
DC: SAME an actual HG.5 row supplies a nonempty honest set. -/
theorem healing_reset_mu_le (hs : V2.D.ScheduleWellFormed E rho)
    (hnr : V2.D.NoRestart rho) {r h : Nat} (hrow : HeightRow p c E rho r h) :
    muOf p c E rho ≤ resetCutFrontier p c E rho := by
  refine (reset_mu_le_iff p c E rho hs hnr ?_).mpr ?_
  · intro j x r a e ha he
    obtain ⟨C, G, hC, hh, hG, hCG, hf⟩ := emittedName ha he
    exact ⟨C, G, hC, congrArg Prod.fst hh, hG, hCG, hf⟩
  · obtain ⟨j, y, a, e, ha, _⟩ := hrow
    exact ⟨y, ha.1⟩

/-- Blueprint 21 H.11:1757–1759,1799–1800; S5 J8 R1 fresh.
DC: SAME select an erased actual fresh source, with the row's exact root.
INLINE producer: sourceDiscipline_emittedName through heightView_eq_simplex. -/
theorem healing_reset_fresh {r M : Nat} (hrow : HeightRow p c E rho r (M + 1)) :
    ∃ CStar, ∃ j y, ∃ (a : RowWire p.n) (C : FGBlock (Fin p.n)),
      HonestRowAt p c E rho j y r a ∧
      namedEntry a.payload.height_pair = some (M + 1, (heightView p C).T_h.root) ∧
      actionSourceFG p c E rho y r = some (some C) ∧
      eraseFG C = CStar ∧ (heightView p C).h = M + 1 := by
  obtain ⟨j, y, a, e, ha, he⟩ := hrow
  obtain ⟨C, _, hC, hh, _⟩ := emittedName ha he
  have hheight : M + 1 = (heightView p C).h := congrArg Prod.fst hh
  have hroot : e = (heightView p C).T_h.root := congrArg Prod.snd hh
  exact ⟨eraseFG C, j, y, a, C, ha, hroot ▸ he, hC, rfl, hheight.symm⟩

end Source

/-- Blueprint 21 H.11:1778–1780; S5 J8 R1 synchronous.
DC: SAME a height-(M+1) row is strictly after the inclusive cut. -/
theorem healing_reset_synchronous {r : Nat}
    (rowCap : ∀ j y r a h e t, HonestRowAt p c E rho j y r a →
      rho.events[j]? = some (.tick y t) → t ≤ resetCutTime p E →
      namedEntry a.payload.height_pair = some (h, e) → h ≤ resetCutFrontier p c E rho)
    (hrow : HeightRow p c E rho r (resetCutFrontier p c E rho + 1)) :
    E.t_GST ≤ SA.voteTime p.toParams (r * p.R) := by
  obtain ⟨j, y, a, e, ha, he⟩ := hrow
  have hafter : resetCutTime p E < p.actionTime r := by
    by_contra hn
    have hc := rowCap j y r a (resetCutFrontier p c E rho + 1) e
      (p.actionTime r) ha ha.2.1 (le_of_not_gt hn) he
    exact Nat.not_succ_le_self _ hc
  have ht : p.actionTime r = SA.voteTime p.toParams (r * p.R) + 5 * p.Δ := by
    change 4 * p.Δ * ((r * p.R : Nat) : Time) + 6 * p.Δ =
      4 * p.Δ * ((r * p.R : Nat) : Time) + p.Δ + 5 * p.Δ
    ring
  have hc := reset_cut_lower p E
  have hp := reset_period_lower p
  rw [ht] at hafter
  linarith [p.deltaPos]

/-- Blueprint 21 H.11:1757–1758; S5 J8 R1 reset_first support.
DC: SAME the exported first-row contract supplies the exact minimality field.
Obtaining this contract from the named HG.5 input remains STOPPED. -/
theorem healing_reset_reset_first {M : Nat} {deadline : Time}
    (firstRow : FirstHeightRowBy p c E rho (M + 1) deadline) :
    ∃ rStar, HeightRow p c E rho rStar (M + 1) ∧
      (∀ r, HeightRow p c E rho r (M + 1) → rStar ≤ r) ∧
      p.actionTime rStar ≤ deadline :=
  (firstHeightRowBy_iff p c E rho (M + 1) deadline).mp firstRow

section Source

variable
    (emittedName : ∀ {j : Nat} {x : V} {r : Nat} {a : RowWire p.n}
      {e : Height × BlockId}, HonestRowAt p c E rho j x r a →
      namedEntry a.payload.height_pair = some e →
      ∃ C G, actionSourceFG p c E rho x r = some (some C) ∧
        e = ((heightView p C).h, (heightView p C).T_h.root) ∧
        gateResult p c E rho x (r * p.R) = some (some G) ∧
        Block.Preceq (eraseFG C) G ∧ fastAt p c E rho x (r * p.R) (eraseFG C))

include emittedName

/-- Blueprint 21 H.11:1744–1800, H.22:3229–3241; S5 J8 R1 field support.
DC: INTENTIONAL reset-only fields, with no Q* service at this horizon.
The first-row contract is a frozen field input for this support lemma.
R1 is STOPPED at its derivation from HG.5, producer HG4-RISE F3 (lf-hg4).
INLINE producer: sourceDiscipline_emittedName through heightView_eq_simplex. -/
theorem healing_reset_fields [Fintype V] {G ΔF deadline : Time}
    (hset : HealingSet p c E rho G ΔF)
    (firstRow : FirstHeightRowBy p c E rho (resetCutFrontier p c E rho + 1) deadline) :
    ∃ w, H0Reset p c E rho w ∧ p.actionTime w.rStar ≤ deadline := by
  have hs := hset.base.valid.toScheduleWellFormed
  have hnr := hset.base.noRestart
  have hcap := healing_reset_rowCap p c E rho emittedName hs hnr
  obtain ⟨rStar, hrow, hfirst, htime⟩ :=
    healing_reset_reset_first p c E rho firstRow
  obtain ⟨CStar, hfresh⟩ := healing_reset_fresh p c E rho emittedName hrow
  let w : HealingWitness :=
    { rG := resetFirstRound p E, u₀ := resetCutTime p E,
      M := resetCutFrontier p c E rho, rStar := rStar, sStar := rStar * p.R,
      CStar := CStar, u := 0, QStar := .genesis }
  refine ⟨w, ?_, htime⟩
  exact
    { rG_after := reset_rG_after p E
      rG_first := reset_rG_first p E
      cut := reset_cut p E
      frontier := reset_frontier p c E rho
      rowCap := hcap
      mu_le := healing_reset_mu_le p c E rho emittedName hs hnr hrow
      cut_lower := reset_cut_lower p E
      cut_upper := reset_cut_upper p E
      reset_row := hrow
      reset_first := hfirst
      label := rfl
      fresh := hfresh
      synchronous := healing_reset_synchronous p c E rho hcap hrow }

end Source

end AvailableChain.FGSA.Run
end
