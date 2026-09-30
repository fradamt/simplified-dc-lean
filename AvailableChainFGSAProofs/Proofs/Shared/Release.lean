module
public import AvailableChainFGSARun.Proofs.Receipts
public import AvailableChainFGSAClaims.Statements.Reads
public import AvailableChainGeneric.Statements.V2.Counts

public section

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

private def releaseSeats {n : Nat} (q : GridCO.Params) (v : GridCO.State n)
    (s : Slot) (B : Block) : Finset (Fin n) :=
  ((GridCO.seats n ((GridCO.votesAt v s).filter (fun o =>
    GridCO.resolvedBefore v o (GridCO.releaseTime q s)))).filter (fun k =>
      !GridCO.equivocates (GridCO.votesAt v s) k &&
      (GridCO.seatVotes ((GridCO.votesAt v s).filter (fun o =>
        GridCO.resolvedBefore v o (GridCO.releaseTime q s))) k).any (fun o =>
          (GridCO.headTarget? o).any (fun C => !Block.compatible C B)))).toFinset

private theorem release_card {n : Nat} (q : GridCO.Params) (v : GridCO.State n)
    (s : Slot) (B : Block) : GridCO.releaseCount q v s B = (releaseSeats q v s B).card := by
  have hp : (fun o : GridCO.Wire n => match GridCO.headTarget? o with
      | some C => !Block.compatible C B
      | none => false) = (fun o => (GridCO.headTarget? o).any
        (fun C => !Block.compatible C B)) := by
    funext o
    cases GridCO.headTarget? o <;> rfl
  unfold GridCO.releaseCount releaseSeats
  dsimp only
  refine Eq.trans ?_ (List.toFinset_card_of_nodup
    (List.Nodup.filter _ (List.nodup_dedup (α := Fin n) _))).symm
  congr 1
  apply congrArg (fun f => List.filter f _)
  funext k
  congr 1
  apply congrArg (fun f => (GridCO.seatVotes _ k).any f)
  exact hp

private theorem release_mem {n : Nat} (q : GridCO.Params) (v : GridCO.State n)
    (s : Slot) (B : Block) (k : Fin n) : k ∈ releaseSeats q v s B ↔
      GridCO.equivocates (GridCO.votesAt v s) k = false ∧
      ∃ o ∈ GridCO.votesAt v s,
        GridCO.resolvedBefore v o (GridCO.releaseTime q s) = true ∧
        GridCO.headSeat? o = some k ∧
        (GridCO.headTarget? o).any (fun C => !Block.compatible C B) = true := by
  dsimp only [releaseSeats]
  simp only [List.mem_toFinset, List.mem_filter, Bool.and_eq_true,
    Bool.not_eq_true', List.any_eq_true, GridCO.seatVotes, beq_iff_eq]
  constructor
  · rintro ⟨_, he, o, ⟨⟨ho, hr⟩, hk⟩, hc⟩
    exact ⟨he, o, ho, hr, hk, hc⟩
  · rintro ⟨he, o, ho, hr, hk, hc⟩
    refine ⟨?_, he, o, ⟨⟨ho, hr⟩, hk⟩, hc⟩
    exact List.mem_dedup.mpr (List.mem_filterMap.mpr
      ⟨o, List.mem_filter.mpr ⟨ho, hr⟩, hk⟩)

private theorem resolved_active_base {n : Nat} (st : State n) (o : GridCO.Wire n)
    (t : Time) (h : GridCO.resolvedBefore (actView st) o t = true) :
    GridCO.resolvedBefore st.base o t = true := by
  unfold GridCO.resolvedBefore at h ⊢
  cases ht : GridCO.headTarget? o with
  | none => simp only [ht, Bool.false_eq_true] at h
  | some C =>
    simp only [ht, Bool.and_eq_true, GridCO.blockKnown, decide_eq_true_eq] at h ⊢
    exact ⟨⟨⟨((actView_blocks st C).mp h.1.1.1).1, h.1.1.2⟩, h.1.2⟩, h.2⟩

/-- P3 F1b.3: restricting the block domain to actView can only decrease release.
Class (iii), store instance. DC counterpart: none; INTENTIONAL, SA adds the
lease lifecycle (spec/fgsa-protocol.tex:2514–2515; blueprint 01 §5). -/
theorem fgsa_releaseCount_antitone (p : Params) (st : State p.n) (s : Slot) (B : Block) :
    GridCO.releaseCount p.toParams.engine (actView st) s B ≤
      GridCO.releaseCount p.toParams.engine st.base s B := by
  rw [release_card, release_card]
  apply Finset.card_le_card
  intro k hk
  obtain ⟨he, o, ho, hr, hs, hc⟩ := (release_mem _ _ _ _ _).mp hk
  exact (release_mem _ _ _ _ _).mpr
    ⟨he, o, ho, resolved_active_base st o _ hr, hs, hc⟩

/-- P3 F1b.3, bp.release.v1(a,c), blueprint 01 §5 item 6: both store laws.
Class (iii), store instance. DC counterpart: none; INTENTIONAL, SA adds the
lease lifecycle (spec/fgsa-protocol.tex:2514–2515). -/
theorem fgsa_release_store (p : Params) (st : State p.n) :
    ∀ s B, GridCO.releaseCount p.toParams.engine (actView st) s B ≤
      GridCO.releaseCount p.toParams.engine st.base s B ∧
      (Block.Preceq B (eraseFG st.fg.F) →
        GridCO.releaseCount p.toParams.engine (actView st) s B = 0) := by
  intro s B
  exact ⟨fgsa_releaseCount_antitone p st s B, actView_releaseCount_zero st _ s⟩

/-- P3 F1b.3, bp.release.v1(b): only faulty HEAD holders count against B.
Class (ii), FG-SA instance of v2 signature authenticity and CStar, with
finite-set injection. DC counterpart: none; INTENTIONAL, SA adds release
(spec/fgsa-protocol.tex:2514–2515; blueprint 02 §2, 21 H.1).
The local compatibility premise keeps the emitted HEAD label. -/
theorem fgsa_release_bound (p : Params) {In V : Type} [DecidableEq V] [Fintype V]
    (c : AppCodec In) (E : Generic.Env V) (rho : V2.Run V (fgsa p c))
    (hE : V2.ExecutionValid E rho) (hN : V2.NoRestart rho)
    (hC : V2.CStar (fgsaFamilies p c).fresh rho) (hDelta : E.Δ = p.Δ)
    (i : Nat) (x : V) (s : Slot) (B : Block)
    (hheads : ∀ y ∈ rho.honest, ∀ o t, V2.Run.emits E rho y o t →
      ∀ k C, o.auth = .seat (.base (.head s)) k → o.payload = .head C →
        Block.Compatible C B) :
    GridCO.releaseCount p.toParams.engine (actView (storeAt p c E rho i x)) s B ≤
      (Gen.V2.faulty rho).card := by
  rw [release_card]
  apply Finset.card_le_card_of_injOn (rho.seatOf (.base (.head s)))
  · intro k hk
    change rho.seatOf (.base (.head s)) k ∈ Gen.V2.faulty rho
    rw [Gen.V2.faulty_def]
    apply Finset.mem_sdiff.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    intro hhonest
    obtain ⟨_, o, ho, hr, hseat, hconf⟩ := (release_mem _ _ _ _ _).mp hk
    have hl : GridCO.headLabel? o = some s := by
      simpa only [beq_iff_eq] using (List.mem_filter.mp ho).2
    have hstored : o ∈ (storeAt p c E rho i x).base.votes :=
      (List.mem_filter.mp ho).1
    have hrbase := resolved_active_base (storeAt p c E rho i x) o _ hr
    obtain ⟨auth, payload⟩ := o
    cases auth with
    | none => cases payload <;> change (none : Option Slot) = some s at hl <;> contradiction
    | proposer r => cases payload <;> change (none : Option Slot) = some s at hl <;> contradiction
    | seat r j =>
      cases payload with
      | proposal C raw support =>
          change (none : Option Slot) = some s at hl
          contradiction
      | head C =>
        have hrs : r = s := Option.some.inj hl
        have hjk : j = k := Option.some.inj hseat
        subst r; subst j
        have hv : GridCO.stampVote (storeAt p c E rho i x).base
            ⟨.seat s k, .head C⟩ < SA.releaseTime p.toParams s := by
          change (_ && _ && _ && _) = true at hrbase
          exact of_decide_eq_true (Bool.and_eq_true_iff.mp
            (Bool.and_eq_true_iff.mp hrbase).1).2
        have hpub : V2.PublicTime E (SA.releaseTime p.toParams s) := by
          refine ⟨4 * s + 5, ?_⟩
          rw [hDelta]
          change 4 * p.Δ * (s : Int) + 5 * p.Δ = _
          push_cast
          ring
        have hzero : 0 ≤ SA.releaseTime p.toParams s := by
          change 0 ≤ 4 * p.Δ * (s : Int) + 5 * p.Δ
          have := p.deltaPos
          positivity
        obtain ⟨j, _, t, ha, _⟩ := fgsa_vote_accepted_before E rho
          hE.toScheduleWellFormed hN i x s k C (SA.releaseTime p.toParams s)
          hpub hzero hstored hv
        obtain ⟨parent, hd, hh⟩ := ha.1
        have hholder : V2.Run.holder rho (ofHead p ⟨.seat (.head s) k, C⟩).auth =
            some (rho.seatOf (.base (.head s)) k) := rfl
        have hem : ∃ u, u ≤ t ∧ V2.Run.emits E rho (rho.seatOf (.base (.head s)) k)
            (ofHead p ⟨.seat (.head s) k, C⟩) u := by
          rcases (fgsaHooks p c).handles_carries _ parent _ hh with hp | hc
          · subst parent
            exact hE.unforgeable x _ t ⟨j, hd⟩ _ hhonest hholder
          · exact hE.carried x parent t ⟨j, hd⟩ _ hc _ hhonest hholder
        obtain ⟨u, _, hem⟩ := hem
        have hcompat := hheads _ hhonest _ u hem k C rfl rfl
        change (!Block.compatible C B) = true at hconf
        rw [show Block.compatible C B = true from hcompat] at hconf
        contradiction
  · intro k _ j _ he
    exact (hC (.base (.head s)) trivial).injective he

end AvailableChain.FGSA.Run
end
