module
public import AvailableChainEngineV2.Conditions.Delivery
public import AvailableChainEngineV2.Conditions.Interface
public import AvailableChainEngineV2.Laws.Outputs
public import AvailableChainEngineV2.Tests.Laws

@[expose] public section

/-! Tests of the interface, the output reader, the outputs law and the delivery
conditions (plan 2a, Task 5). A proposal duty is a one-seat label, and a
two-seat label cannot be one. `OutputsFactor` with `base := id` holds by
`rfl`, and it fails for an output that reads the own record. Broadcast in
`HealthyPrefixDelivery` includes the emitting node. -/

namespace AvailableChain.V2.Tests

open AvailableChain AvailableChain.V2

/-! ### `Interface` with a one-seat proposal label -/

/-- Every slot proposes with label `false` of `specM`, which has one seat. -/
def IM : Interface specM where
  confirmed := fun _ => .genesis
  stable := fun _ => .genesis
  block := fun _ => none
  opening := fun _ => True
  propLabel := fun _ => false
  propLabel_single := fun _ => rfl

example : proposalTime IM 7 = 3 := rfl
example : propSeat IM 7 = ⟨0, by decide⟩ := rfl
-- In `rhoM`, validator 1 holds every seat, so it is the proposer.
example : proposerOf rhoM IM 7 = 1 := rfl
-- The proposal of slot 7 is the object of label `false` that `rhoM` emits.
example : (⟨.seat (IM.propLabel 7) (propSeat IM 7), 106⟩ : specM.Object) ∈
    Run.emitsAt (envAwake _) rhoM 0 := by
  rw [show Run.emitsAt (envAwake _) rhoM 0 =
    [⟨.seat true ⟨0, by decide⟩, 106⟩, ⟨.seat true ⟨1, by decide⟩, 106⟩,
      ⟨.seat false ⟨0, by decide⟩, 106⟩] from rfl]
  decide
example (i : Fin (specM.seats (IM.propLabel 7))) :
    Run.holder rhoM (.seat (IM.propLabel 7) i) = some 1 :=
  holder_propLabel rhoM IM 7 i

-- Label `true` has two seats: it is not a proposal duty.
example : ¬ ∃ I : Interface specM, I.propLabel 0 = true := by
  rintro ⟨I, h⟩
  have h1 := I.propLabel_single 0
  rw [h] at h1
  exact absurd h1 (by decide)

/-! ### The output reader and roots -/

/-- `specB` with a confirmed output that names the state. -/
def IB : Interface specB where
  confirmed := fun st => .node .genesis 1 st
  stable := fun _ => .genesis
  block := fun p => some (.node .genesis 1 p)
  opening := fun _ => True
  propLabel := fun _ => ()
  propLabel_single := fun _ => rfl

-- At time 4 the delivery set the state to 1; at time 5 the restart restored 0,
-- and the tick kept it.
example : outputAt (envAwake _) rhoB IB.confirmed () 4 = .node .genesis 1 1 := rfl
example : outputAt (envAwake _) rhoB IB.confirmed () 5 = .node .genesis 1 0 := rfl
example : RootInjective (envAwake _) IB rhoB := rootInjective_all _ _ _
-- The block of the delivered payload at time 4 is in the run.
example : BlockInRun (envAwake _) IB rhoB (.node .genesis 1 1) :=
  Or.inr ⟨(), ⟨.none, 1⟩, 4, _, Or.inl ⟨0, rfl⟩, rfl, by decide⟩

/-! ### `OutputsFactor` -/

/-- With `base := id` (`isoB`), the factors are the getters. -/
def outB : OutputsFactor IB isoB where
  confirmedB := IB.confirmed
  confirmed_base := fun _ => rfl
  stableB := IB.stable
  stable_base := fun _ => rfl

example (st : Nat) : IB.confirmed (tick (envAwake _) rhoB st () 5).1 =
    IB.confirmed (specB.clock st 5) :=
  outB.confirmed_tick _ _ _ _ _

/-- `specA` with a confirmed output that names the state. -/
def IA : Interface specA where
  confirmed := fun st => .node .genesis 1 st
  stable := fun _ => .genesis
  block := fun _ => none
  opening := fun _ => True
  propLabel := fun _ => false
  propLabel_single := fun _ => rfl

-- The base of `isoLinked` is trivial, but `confirmed` reads the state, which
-- the own record changes: there is no `OutputsFactor` value.
example : IsEmpty (OutputsFactor IA isoLinked) := by
  refine ⟨fun h => ?_⟩
  have h0 := h.confirmed_base 0
  have h1 := h.confirmed_base 1
  rw [show isoLinked.base 1 = isoLinked.base 0 from rfl, ← h0] at h1
  exact absurd h1 (by decide)

/-! ### Delivery conditions -/

-- With no honest node, both conditions hold.
example : PartialSynchrony (envAwake _) rhoR :=
  ⟨fun _ hv => absurd hv (Finset.notMem_empty _),
    fun _ hv => absurd hv (Finset.notMem_empty _)⟩
example : HealthyPrefixDelivery (envAwake _) rhoR 10 :=
  ⟨fun _ hv => absurd hv (Finset.notMem_empty _),
    fun _ hv => absurd hv (Finset.notMem_empty _)⟩

-- Broadcast includes the emitting node: in `rhoNoSD`, validator 0 emits `oSD`
-- at time 1 and never gets it, so the healthy prefix up to time 2 fails.
example : ¬ HealthyPrefixDelivery (envAwake _) rhoNoSD 2 := by
  intro h
  obtain ⟨_, _, _, j, _, hj, _⟩ := h.broadcast 0 (by decide) oSD 1
    ⟨0, rfl, List.mem_singleton_self _⟩ 0 (by decide) (by decide) rfl
  match j, hj with
  | 0, hj => simp [rhoNoSD, rhoSD] at hj
  | _ + 1, hj => simp [rhoNoSD, rhoSD] at hj

end AvailableChain.V2.Tests

end
