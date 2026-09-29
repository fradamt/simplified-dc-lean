module
public import AvailableChainModel.Objects.Blocks
public import AvailableChainModel.Objects.Time

@[expose] public section

namespace AvailableChain.Framework.V2Sketch

open AvailableChain

/-- The part of a v2 spec that E5 and E6 need. -/
structure SpecV2 where
  State : Type
  Base : Type
  Object : Type
  Durable : Type
  DBase : Type
  base : State → Base
  clock : State → Time → State
  process : State → Object → State
  recordOwn : State → Object → State
  selfVisible : Object → Bool
  durable : State → Durable
  restore : Durable → State
  /-- The base-visible part of durable data. -/
  dbase : Durable → DBase
  output : State → Block

/-- E5 isolation laws. -/
structure Isolated (S : SpecV2) : Prop where
  clock_base : ∃ f : S.Base → Time → S.Base, ∀ st t, S.base (S.clock st t) = f (S.base st) t
  process_base : ∃ g : S.Base → S.Object → S.Base,
    ∀ st o, S.base (S.process st o) = g (S.base st) o
  recordOwn_base : ∀ st o, S.base (S.recordOwn st o) = S.base st
  output_base : ∃ h : S.Base → Block, ∀ st, S.output st = h (S.base st)

/-- E6 restore law: the base after a restart depends only on the
base-visible durable part, and that part only on the base. -/
structure Restorable (S : SpecV2) : Prop where
  restore_base : ∃ r : S.DBase → S.Base, ∀ d, S.base (S.restore d) = r (S.dbase d)
  durable_base : ∃ k : S.Base → S.DBase, ∀ st, S.dbase (S.durable st) = k (S.base st)

/-- The atomic tick: clock, then the own record over the self-visible
emitted objects in list order. Emission itself is outside this sketch. -/
def tickV2 (S : SpecV2) (st : S.State) (t : Time) (emitted : List S.Object) : S.State :=
  (emitted.filter S.selfVisible).foldl S.recordOwn (S.clock st t)

def restartV2 (S : SpecV2) (st : S.State) : S.State := S.restore (S.durable st)

/-- The own record does not move the base (fallback helper: the sketch's
direct `induction … generalizing` proof does not elaborate, because the
goal after `rw [hh, hh]` carries an extra `hb` wrapper that
`h.recordOwn_base` does not produce; this lemma stays below that wrapper). -/
theorem foldl_recordOwn_base (S : SpecV2) (h : Isolated S) :
    ∀ (l : List S.Object) (s : S.State), S.base (l.foldl S.recordOwn s) = S.base s := by
  intro l
  induction l with
  | nil => intro s; rfl
  | cons o rest ih =>
      intro s
      simp only [List.foldl_cons]
      rw [ih]
      exact h.recordOwn_base s o

/-- The own record never changes an output. -/
theorem output_tick (S : SpecV2) (h : Isolated S) (st : S.State) (t : Time)
    (os : List S.Object) : S.output (tickV2 S st t os) = S.output (S.clock st t) := by
  obtain ⟨hb, hh⟩ := h.output_base
  rw [hh, hh]
  unfold tickV2
  rw [foldl_recordOwn_base S h]

/-- Two states with the same base have the same base after a restart. -/
theorem base_restart (S : SpecV2) (h : Restorable S) (a b : S.State)
    (hab : S.base a = S.base b) : S.base (restartV2 S a) = S.base (restartV2 S b) := by
  obtain ⟨r, hr⟩ := h.restore_base
  obtain ⟨k, hk⟩ := h.durable_base
  simp only [restartV2, hr, hk, hab]

/-- State: (height, recorded seat index). Base: height. -/
def toyV2 : SpecV2 where
  State := Nat × Nat
  Base := Nat
  Object := Nat × Bool       -- (value, self-visible)
  Durable := Nat × Nat
  DBase := Nat
  base := fun st => st.1
  clock := fun st _ => st
  process := fun st o => (max st.1 o.1, st.2)
  recordOwn := fun st o => (st.1, o.1)
  selfVisible := fun o => o.2
  durable := fun st => st
  restore := fun d => (d.1, 0)
  dbase := fun d => d.1
  output := fun st => (List.range st.1).foldl (fun b k => .node b k ⟨k + 1⟩) .genesis

theorem toyV2_isolated : Isolated toyV2 :=
  ⟨⟨fun b _ => b, fun _ _ => rfl⟩,
    -- `Nat.max`, not `max`: elaborating the witness against
    -- `toyV2.Base → toyV2.Object → toyV2.Base` runs instance search for
    -- `Max toyV2.Base` before the projection unfolds to `Nat`, and that
    -- search fails. `Nat.max` is the plain function, so no instance search.
    ⟨fun (b : Nat) (o : Nat × Bool) => Nat.max b o.1, fun _ _ => rfl⟩,
    fun _ _ => rfl, ⟨fun b => (List.range b).foldl (fun c k => .node c k ⟨k + 1⟩) .genesis,
      fun _ => rfl⟩⟩

theorem toyV2_restorable : Restorable toyV2 :=
  ⟨⟨fun d => d, fun _ => rfl⟩, ⟨fun b => b, fun _ => rfl⟩⟩

end AvailableChain.Framework.V2Sketch

end
