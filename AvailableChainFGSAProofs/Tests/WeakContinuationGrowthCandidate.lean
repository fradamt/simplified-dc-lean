module
public import AvailableChainFGSAProofs.Proofs.WeakContinuationGrowth.Counts -- shake: keep (own-library route)
public meta import AvailableChainFGSAProofs.Proofs.WeakContinuationGrowth.Counts -- shake: keep (engine execution)

@[expose] public section

/-! Executable candidate for the full non-vacuity obligation.
Seven validators execute the real duty engine and FG-SA handlers. The source
has five honest validators; the continuation retains four. All seven follow
the generator, which is permitted behavior for the three faulty validators.
This test does not prove Base₂, synchrony, or the slashing bound. Those full
regime obligations remain in the companion OPEN.md. -/
namespace AvailableChain.FGSA.Run.Tests.WeakContinuationGrowthCandidate

def params : Params where
  Δ := 1
  n := 7
  k := 2
  η := 0
  deltaPos := by decide
  nPos := by decide
  kLarge := by decide
  etaNonneg := by decide
  R := 2
  δt := 4
  RLarge := by decide
  digest := fun d => ⟨d.slot + 1⟩

abbrev Validator := Fin 7
abbrev Event := V2.Event Validator (fgsa params unitCodec).Object
abbrev World := V2.D.World Validator (fgsa params unitCodec)

def strongEnv : Generic.Env Validator where
  Δ := 1
  Δ_pos := by decide
  t_GST := 0
  t_GST_nonneg := by decide
  awake _ _ := true

def weakEnv : Generic.Env Validator :=
  { strongEnv with awake := fun _ _ => true }

/-- One holder per base seat; node zero proposes in every slot. -/
def seatOf : (ℓ : RunLabel) → Fin (RunLabel.seats params ℓ) → Validator
  | .base _, i => i
  | .prop _, _ => 0

/-- Static run data for the schedule generator. -/
def runData (horizon : Time) (events : List Event) :
    V2.D.Run Validator (fgsa params unitCodec) where
  honest := {0, 1, 2, 3, 4}
  horizon := horizon
  events := events
  seatOf := seatOf
  input _ _ := ()

def nodes : List Validator := List.finRange 7

/-- Run all ticks first, and keep the actual objects that they release. -/
def tickBatch (t : Time) (w : World) : World × List (Obj params) :=
  nodes.foldl (fun acc v =>
    let result := V2.D.tick weakEnv (runData 263 []) (acc.1 v) v t
    (Function.update acc.1 v result.1, acc.2 ++ (show List (Obj params) from result.2))) (w, [])

/-- Deliver a fresh object with the real handler, including to sleepers. -/
def deliverOne (t : Time) (acc : World × List Event) (vo : Validator × Obj params) :
    World × List Event :=
  if (fgsa params unitCodec).processed (acc.1 vo.1) vo.2 then acc else
    (V2.D.World.step weakEnv (runData 263 []) acc.1 (.deliver vo.1 vo.2 t),
      acc.2 ++ [.deliver vo.1 vo.2 t])

/-- Every object is offered to every receiver before the next object. -/
def timeBatch (t : Time) (w : World) : World × List Event :=
  let ticks := tickBatch t w
  let deliveries := ticks.2.flatMap (fun o => nodes.map (fun v => (v, o)))
  deliveries.foldl (deliverOne t) (ticks.1, nodes.map (fun v => .tick v t))

/-- The first `steps` integer times, starting at zero. -/
def buildPrefix : Nat → World × List Event
  | 0 => (V2.D.World.init, [])
  | steps + 1 =>
      let previous := buildPrefix steps
      let batch := timeBatch (steps : Time) previous.1
      (batch.1, previous.2 ++ batch.2)


def source : V2.D.Run Validator (fgsa params unitCodec) :=
  runData 247 (buildPrefix 248).2

def continuation : V2.D.Run Validator (fgsa params unitCodec) :=
  { runData 263 (buildPrefix 264).2 with honest := {0, 1, 2, 3} }

/-- Counts use the actual fixture honest sets and the actual n = 7. -/
theorem fault_counts :
    (Finset.univ \ source.honest).card = 2 ∧
    (Finset.univ \ continuation.honest).card = 3 ∧
    (params.n - 1) / 3 < (Finset.univ \ continuation.honest).card ∧
    (Finset.univ \ continuation.honest).card < continuation.honest.card := by decide

/-- The generated source uses the real bounded healing endpoint. -/
theorem candidate_endpoint : source.horizon = strongEnv.t_GST + B_HF params 1 4 := by decide

/-- Run the full 264-time trace, including a nonempty corruption-growth suffix.
Check common retained outputs on every time slice and a non-genesis endpoint. -/
def runCandidate : IO Unit := do
  let mut world : World := V2.D.World.init
  let mut eventCount := 0
  let mut sourceOutput := Block.genesis
  for t in [:264] do
    let batch := timeBatch (t : Time) world
    world := batch.1
    eventCount := eventCount + batch.2.length
    if 247 ≤ t then
      let output := (world 0).st.base.stableRecord
      for v in ([0, 1, 2, 3] : List Validator) do
        unless (world v).st.base.stableRecord == output do
          throw (IO.userError s!"retained outputs differ at time {t}")
      if t == 247 then sourceOutput := output
      unless Block.preceq sourceOutput output do
        throw (IO.userError s!"source endpoint output lost at time {t}")
  if sourceOutput == Block.genesis then
    throw (IO.userError "source endpoint output is genesis")
  IO.println s!"candidate PASS: 264 times, {eventCount} events"
  IO.println "source faults 2, continuation faults 3, retained honest 4"
  IO.println "Full regime non-vacuity remains unproved."

end AvailableChain.FGSA.Run.Tests.WeakContinuationGrowthCandidate

def main : IO Unit := AvailableChain.FGSA.Run.Tests.WeakContinuationGrowthCandidate.runCandidate
end
