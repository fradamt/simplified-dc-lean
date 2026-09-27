module
public import AvailableChainModel.Objects.Time

@[expose] public section

namespace AvailableChain.Generic

/-- The environment. Validators are unit seats: every validator has weight 1,
so participation premises count validators. -/
structure Env (V : Type) where
  Δ : Time
  Δ_pos : 0 < Δ
  t_GST : Time
  t_GST_nonneg : 0 ≤ t_GST
  /-- Who is awake when. An asleep node receives, processes, and runs its
  clock, but emits nothing. Participation premises are stated on this
  profile. -/
  awake : V → Time → Bool

end AvailableChain.Generic

end
