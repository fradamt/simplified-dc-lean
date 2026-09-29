module
public import AvailableChainModel.Generic.Run
public import AvailableChainModel.Objects.Blocks
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

@[expose] public section

namespace AvailableChain.GridCO

open AvailableChain.Generic

/-- The shared engine has two lease admission rules. The default is Grid CO.
SA uses the same engine with `slowArming = true`. -/
class LeasePolicy where
  slowArming : Bool

instance gridLeasePolicy : LeasePolicy := ⟨false⟩

abbrev slowLeasePolicy : LeasePolicy := ⟨true⟩

/-- Largest grid level no greater than the observed support. -/
def gridLevel (n : Nat) (grid : Finset Nat) (h : Nat) : Nat :=
  ((List.range (n + 1)).filter (fun g => g ∈ grid && g ≤ h)).foldl max 0

/-- Grid counted-obligations parameters. The grid is fixed in honest code. -/
structure Params where
  Δ : Time
  n : Nat
  m : Nat
  η : Time
  grid : Finset Nat
  θ_R : ℚ
  deltaPos : 0 < Δ
  mLarge : 2 ≤ m
  one_mem : 1 ∈ grid
  levels_pos : ∀ g ∈ grid, 0 < g
  levels_le : ∀ g ∈ grid, g ≤ n
  etaNonneg : 0 ≤ η
  thetaLower : (1 / 2 : ℚ) ≤ θ_R
  thetaUpper : θ_R ≤ (3 / 4 : ℚ)
  /-- The grid has enough levels for each admissible current count. -/
  gridMatchesTheta : ∀ a h : Nat, 1 ≤ a → h ≤ n →
    θ_R * ((h + a : Nat) : ℚ) < (h : ℚ) → a < gridLevel n grid h

def lifetime (p : Params) : Time := (4 * (p.m : Time) - 1) * p.Δ

def proposalTime (p : Params) (s : Slot) : Time := 4 * p.Δ * s
def voteTime (p : Params) (s : Slot) : Time := proposalTime p s + p.Δ
def earlyTime (p : Params) (s : Slot) : Time := proposalTime p s + 2 * p.Δ
def freezeTime (p : Params) (s : Slot) : Time := proposalTime p s + 3 * p.Δ
def releaseTime (p : Params) (s : Slot) : Time := proposalTime p s + 5 * p.Δ
def gateTime (p : Params) (s : Slot) : Time := proposalTime p s + 6 * p.Δ

/-- Signed HEADs inside proposals retain the proposer's raw and resolved views.
Source: verified-consensus docs/PROTOCOL.md §§2.1–2.3, `propose_block` and
`goldfish_vote`. No FG, SG, height, grade, or acknowledgement payload exists. -/
abbrev HeadWire (n : Nat) := Signed Slot n Block

inductive Msg (n : Nat) where
  | head (target : Block)
  | proposal (b : Block) (view supportView : List (HeadWire n))
  deriving DecidableEq, Repr

abbrev Wire (n : Nat) := Signed Slot n (Msg n)

def fromHead {n : Nat} (o : HeadWire n) : Wire n :=
  ⟨o.auth, .head o.payload⟩

def toHead? {n : Nat} (o : Wire n) : Option (HeadWire n) :=
  match o.payload with
  | .head b => some ⟨o.auth, b⟩
  | _ => none

def headTarget? {n : Nat} (o : Wire n) : Option Block :=
  match o.payload with
  | .head b => some b
  | _ => none

def headLabel? {n : Nat} (o : Wire n) : Option Slot :=
  match o.auth, o.payload with
  | .seat r _, .head _ => some r
  | _, _ => none

def headSeat? {n : Nat} (o : Wire n) : Option (Fin n) :=
  match o.auth, o.payload with
  | .seat _ i, .head _ => some i
  | _, _ => none

def sameSeat {n : Nat} (a b : Wire n) : Bool :=
  match a.auth, b.auth with
  | .seat r i, .seat s j => r == s && i == j
  | _, _ => false

/-- Local store. Receipt stamps use the last public tick, as in
verified-consensus `StoreBase.lean` and `Handlers.lean`. -/
structure State (n : Nat) where
  now : Time := 0
  blocks : List Block := [.genesis]
  blockStamp : List (Block × Time) := [(.genesis, 0)]
  votes : List (Wire n) := []
  voteStamp : List (Wire n × Time) := []
  proposals : List (Wire n) := []
  /-- Label, raw frozen pool, resolved frozen pool, frozen block domain. -/
  frozen : List (Slot × List (Wire n) × List (Wire n) × List Block) := []
  early : List (Slot × List (Wire n)) := []
  /-- Local raw gate results. `none` records an empty gate, not a missing label.
  Only SA uses this field; Grid CO leaves it empty. -/
  genuine : List (Slot × Option Block) := []
  /-- One deadline per block and grid level. -/
  obligations : List (Block × Nat × Time) := []
  /-- Frozen label-r raw and resolved release views before the next HEAD. -/
  releaseSnapshots : List (Slot × List (Wire n) × List (Wire n)) := []
  stableRecord : Block := .genesis
  goldfishRecord : Block := .genesis
  deriving Repr

def initial (n : Nat) : State n := {}

def blockKnown {n : Nat} (st : State n) (b : Block) : Bool := b ∈ st.blocks

def stampBlock {n : Nat} (st : State n) (b : Block) : Time :=
  ((st.blockStamp.find? (fun row => row.1 == b)).map Prod.snd).getD st.now

def stampVote {n : Nat} (st : State n) (o : Wire n) : Time :=
  ((st.voteStamp.find? (fun row => row.1 == o)).map Prod.snd).getD st.now

/-- `resolution_time = max(receipt(vote), receipt(head))`, or infinity for
an unknown head. Source: PROTOCOL.md §2.2, `resolution_time`. -/
def resolvedBefore {n : Nat} (st : State n) (o : Wire n) (cutoff : Time) : Bool :=
  match headTarget? o with
  | none => false
  | some b => blockKnown st b && b.slot ≤ (headLabel? o).getD 0 &&
      stampVote st o < cutoff && stampBlock st b < cutoff

def votesAt {n : Nat} (st : State n) (r : Slot) : List (Wire n) :=
  st.votes.filter (fun o => headLabel? o == some r)

def seats (n : Nat) (xs : List (Wire n)) : List (Fin n) :=
  (xs.filterMap headSeat?).dedup

def seatVotes {n : Nat} (xs : List (Wire n)) (i : Fin n) : List (Wire n) :=
  xs.filter (fun o => headSeat? o == some i)

def equivocates {n : Nat} (xs : List (Wire n)) (i : Fin n) : Bool :=
  2 ≤ ((seatVotes xs i).eraseDups).length

/-- Each equivocating seat contributes one point to every subtree. Other
seats contribute once if a support vote covers the block. Source:
verified-consensus `ForkChoice/Goldfish.lean`, `goldfish_score`. -/
def goldfishScore {n : Nat} (tree : List Block)
    (raw support : List (Wire n)) (b : Block) : Nat :=
  ((seats n raw).filter (fun i =>
    equivocates raw i || (seatVotes support i).any (fun o =>
      match headTarget? o with
      | some target => target ∈ tree && target.slot ≤ (headLabel? o).getD 0 &&
          Block.preceq b target
      | none => false))).length

def voterCount {n : Nat} (xs : List (Wire n)) : Nat := (seats n xs).length

/-- The source GHOST walk, with the greatest root winning a score tie.
Source: verified-consensus `ForkChoice/Goldfish.lean`, `ghost`. -/
def ghostStep (tree : List Block) (score : Block → Nat)
    (eligible : Block → Bool) (anchor : Block) : Option Block :=
  let children := tree.filter (fun b => b.parent? == some anchor && eligible b)
  let best := children.foldl (fun best b =>
    match best with
    | none => some b
    | some old =>
      if score old < score b || (score old == score b && old.root < b.root)
      then some b else best) none
  match best with
  | none => none
  | some b =>
      if children.any (fun c => c != b && score c == score b && c.root == b.root)
      then none else some b

def ghostWalk (tree : List Block) (score : Block → Nat)
    (eligible : Block → Bool) : Nat → Block → Block
  | 0, b => b
  | fuel + 1, b =>
      match ghostStep tree score eligible b with
      | none => b
      | some c => ghostWalk tree score eligible fuel c

def ghost (anchor : Block) (tree : List Block) (score : Block → Nat)
    (eligible : Block → Bool) : Block :=
  let tree := tree.eraseDups
  ghostWalk tree score eligible tree.length anchor

def liveRoot {n : Nat} (st : State n) : Block :=
  ((st.obligations.filterMap (fun (b, _, expiry) =>
    if st.now < expiry then some b else none)).foldl (fun best b =>
      if best.depth < b.depth ||
         (best.depth == b.depth && best.root < b.root) then b else best)
    .genesis)

def advance (old candidate : Block) : Block :=
  if Block.preceq candidate old then old else candidate

/-- The proposal-time raw pool and its resolved subset.
Source: verified-consensus `ForkChoice/Views.lean`, `proposer_view`. -/
def proposerView {n : Nat} (st : State n) (s : Slot) : List (Wire n) :=
  votesAt st (s - 1)

def proposerSupportView {n : Nat} (st : State n) (s : Slot) : List (Wire n) :=
  (proposerView st s).filter (fun o =>
    match headTarget? o with
    | some b => blockKnown st b && b.slot ≤ s - 1
    | none => false)

def proposalsAt {n : Nat} (st : State n) (s : Slot) : List (Wire n) :=
  st.proposals.filter (fun o =>
    match o.payload with
    | .proposal b _ _ => b.slot == s
    | _ => false)

def carriedRaw {n : Nat} (st : State n) (s : Slot) : List (Wire n) :=
  ((proposalsAt st s).flatMap (fun o =>
    match o.payload with
    | .proposal _ raw _ => raw.map fromHead
    | _ => [])).filter (fun o => headLabel? o == some (s - 1))

def carriedSupport {n : Nat} (st : State n) (s : Slot) : List (Wire n) :=
  ((proposalsAt st s).flatMap (fun o =>
    match o.payload with
    | .proposal _ _ support => support.map fromHead
    | _ => [])).filter (fun o =>
      headLabel? o == some (s - 1) &&
      match headTarget? o with
      | some b => blockKnown st b && b.slot ≤ s - 1
      | none => false)

def frozenAt {n : Nat} (st : State n) (r : Slot) :
    Option (List (Wire n) × List (Wire n) × List Block) :=
  ((st.frozen.find? (fun row => row.1 == r)).map Prod.snd)

/-- The previous-slot freeze is a local clock evaluation. Its saved block
domain and vote subsets are later merged with current proposals. -/
def freeze (p : Params) {n : Nat} (st : State n) (r : Slot) : State n :=
  let cutoff := freezeTime p r
  let raw := (votesAt st r).filter (fun o => stampVote st o < cutoff)
  let support := (votesAt st r).filter (fun o => resolvedBefore st o cutoff)
  let blocks := st.blocks.filter (fun b => stampBlock st b < cutoff)
  { st with frozen := st.frozen ++ [(r, raw, support, blocks)] }

/-- Previous-slot freeze and proposal merge. Source:
verified-consensus `ForkChoice/Views.lean`, `voter_view`,
`voter_support_view`, `voter_processed_block_tree`. -/
def voterView (_p : Params) {n : Nat} (st : State n) (s : Slot) : List (Wire n) :=
  let pool := match frozenAt st (s - 1) with
    | some (raw, _, _) => raw
    | none => []
  (pool ++ carriedRaw st s).eraseDups

def voterSupportView (_p : Params) {n : Nat} (st : State n) (s : Slot) : List (Wire n) :=
  let pool := match frozenAt st (s - 1) with
    | some (_, support, _) => support
    | none => []
  (pool ++ carriedSupport st s).eraseDups

def voterTree (_p : Params) {n : Nat} (st : State n) (s : Slot) : List Block :=
  let proposals := (proposalsAt st s).filterMap (fun o =>
    match o.payload with
    | .proposal b _ _ => some b
    | _ => none)
  let frozenBlocks := match frozenAt st (s - 1) with
    | some (_, _, blocks) => blocks
    | none => []
  st.blocks.filter (fun b =>
    b ∈ frozenBlocks ||
      proposals.any (fun q => Block.preceq b q))

/-- With no heights or finality, the Goldfish eligibility clauses are
strict majority for an old child and unconditional for a current-slot child.
Source: PROTOCOL.md §2.2, `goldfish_eligible`. -/
def goldfishEligible {n : Nat} (tree : List Block) (raw support : List (Wire n))
    (current : Slot) (b : Block) : Bool :=
  b.slot == current || 2 * goldfishScore tree raw support b > voterCount raw

def forkChoice {n : Nat} (st : State n) (tree : List Block)
    (raw support : List (Wire n)) (current : Slot) : Block :=
  ghost (liveRoot st) tree (goldfishScore st.blocks raw support)
    (goldfishEligible st.blocks raw support current)

def propose (_p : Params) {n : Nat} (st : State n) (s : Slot) : Option (Msg n) :=
  if s == 0 then none else
    let raw := proposerView st s
    let support := proposerSupportView st s
    let parent := forkChoice st st.blocks raw support s
    let b := Block.node parent s 0
    some (.proposal b (raw.filterMap toHead?) (support.filterMap toHead?))

def act (p : Params) {n : Nat} (st : State n) (s : Slot) : Option (Msg n) :=
  if s == 0 then some (.head .genesis) else
    some (.head (forkChoice st (voterTree p st s)
      (voterView p st s) (voterSupportView p st s) s))

def admitVote (p : Params) {n : Nat} (st : State n) (o : Wire n) : State n :=
  match o.auth, o.payload with
  | .seat r i, .head _ =>
      let current := (st.now / (4 * p.Δ)).toNat
      -- Retain old-label HEADs for relay and equivocation evidence. Receipt
      -- stamps keep them out of earlier frozen views and snapshots.
      if r < current - 1 || current < r || decide (o ∈ st.votes) ||
          equivocates (votesAt st r) i then st else
        { st with votes := st.votes ++ [o], voteStamp := st.voteStamp ++ [(o, st.now)] }
  | _, _ => st

/-- Block admission then carried-vote admission, following the source
`Handlers.lean` order. The support subset remains fixed metadata. -/
def admitProposal (p : Params) {n : Nat} (st : State n) (o : Wire n)
    (b : Block) (raw : List (HeadWire n)) : State n :=
  let current := (st.now / (4 * p.Δ)).toNat
  let correctProposer := match o.auth with
    | .proposer s => s == b.slot
    | _ => false
  if b.slot > current || !blockKnown st b.parent || b ∈ st.blocks ||
      !(b.parent.slot < b.slot) || !correctProposer then st else
    let st' := { st with
      blocks := st.blocks ++ [b]
      blockStamp := st.blockStamp ++ [(b, st.now)]
      proposals := st.proposals ++ [o] }
    raw.foldl (fun acc row => admitVote p acc (fromHead row)) st'

def process (p : Params) {n : Nat} (st : State n) (o : Wire n) : State n :=
  match o.auth, o.payload with
  | .seat _ _, .head _ => admitVote p st o
  | .proposer _, .proposal b raw _ => admitProposal p st o b raw
  | _, _ => st

def wellFormed {n : Nat} (o : Wire n) : Bool :=
  match o.auth, o.payload with
  | .seat _ _, .head _ => true
  | .proposer s, .proposal b raw support =>
      s == b.slot && b.parent?.isSome && b.parent.slot < s &&
      raw.all (fun v => match v.auth with
        | .seat r _ => r == s - 1
        | _ => false) &&
      support.all (fun v => decide (v ∈ raw))
  | _, _ => false

def depsPresent {n : Nat} (st : State n) (o : Wire n) : Bool :=
  match o.payload with
  | .head _ => true
  | .proposal b _ _ => blockKnown st b.parent

def processed {n : Nat} (st : State n) (o : Wire n) : Bool :=
  match o.payload with
  | .head _ => decide (o ∈ st.votes)
  | .proposal b _ _ => blockKnown st b

def carries {n : Nat} (parent child : Wire n) : Prop :=
  match parent.payload with
  | .head _ => False
  | .proposal _ raw support => child ∈ raw.map fromHead ∨ child ∈ support.map fromHead

/-- A direct delivery calls its handler. A proposal calls its raw HEAD
handlers only when its block enters the store. This matches the reference
`Execution.handles` / `NamedReceiptCalls.postCore` admission test.
Support metadata alone does not cause a call; `carries` remains structural
for signature checks, including rejected proposals. -/
def handles (p : Params) {n : Nat} (st : State n) (parent child : Wire n) : Prop :=
  parent = child ∨ match parent.payload with
    | .proposal b raw _ =>
        b ∉ st.blocks ∧ b ∈ (process p st parent).blocks ∧ child ∈ raw.map fromHead
    | .head _ => False

def earlyVotes (p : Params) {n : Nat} (st : State n) (r : Slot) : List (Wire n) :=
  (votesAt st r).filter (fun o => resolvedBefore st o (earlyTime p r))

def savedEarly {n : Nat} (st : State n) (r : Slot) : List (Wire n) :=
  ((st.early.find? (fun row => row.1 == r)).map Prod.snd).getD []

/-- `D_i[r,u]`: max distinct seats among labels in the fixed vote-time
window. An equivocating seat occurs once. Source: guarded-override.md §3.1. -/
def lateVotes (p : Params) {n : Nat} (st : State n) (r : Slot) : List (Wire n) :=
  (votesAt st r).filter (fun o => stampVote st o < gateTime p r)

def cleanSupport (p : Params) {n : Nat} (st : State n) (r : Slot) : List (Wire n) :=
  (earlyVotes p st r).filter (fun o =>
    !(lateVotes p st r).any (fun u => sameSeat u o && u != o))

/-- Genuine Goldfish confirmation at `d_r` with the walk anchored at `a`:
early resolved support, late equivocation exclusion, and a strict majority
of late participants. The final test checks the walk result itself. -/
def confirmationFrom (p : Params) {n : Nat} (a : Block) (st : State n) (r : Slot) :
    Option Block :=
  let support := cleanSupport p st r
  let late := lateVotes p st r
  let eligible := fun b => 2 * goldfishScore st.blocks support support b > voterCount late
  let h := ghost a st.blocks (goldfishScore st.blocks support support) eligible
  if eligible h then some h else none

/-- Genuine Goldfish confirmation at `d_r`: early resolved support,
late equivocation exclusion, and a strict majority of late participants.
The walk starts at genesis; proposals and HEADs start at the live root. -/
def confirmation (p : Params) {n : Nat} (st : State n) (r : Slot) : Option Block :=
  let support := cleanSupport p st r
  let late := lateVotes p st r
  let eligible := fun b => 2 * goldfishScore st.blocks support support b > voterCount late
  let h := ghost .genesis st.blocks (goldfishScore st.blocks support support) eligible
  if eligible h then some h else none

theorem confirmation_eq_from_genesis (p : Params) {n : Nat} (st : State n) (r : Slot) :
    confirmation p st r = confirmationFrom p .genesis st r := rfl

/-- A resolved label-r HEAD contributes to release only when its seat has
exactly one known label-r HEAD and its target conflicts with the obligation. -/
def releaseCount (p : Params) {n : Nat} (st : State n) (r : Slot)
    (b : Block) : Nat :=
  let raw := votesAt st r
  let resolved := raw.filter (fun o => resolvedBefore st o (releaseTime p r))
  ((seats n resolved).filter (fun i =>
    !equivocates raw i &&
    (seatVotes resolved i).any (fun o =>
      match headTarget? o with
      | some target => !Block.compatible target b
      | none => false))).length

def expire {n : Nat} (st : State n) (t : Time) : State n :=
  { st with obligations := st.obligations.filter (fun (_, _, deadline) => t < deadline) }

def release (p : Params) {n : Nat} (st : State n) (r : Slot) : State n :=
  let raw := votesAt st r
  let resolved := raw.filter
    (fun o => resolvedBefore st o (releaseTime p r))
  { st with
    releaseSnapshots := st.releaseSnapshots ++ [(r, raw, resolved)]
    obligations := st.obligations.filter
      (fun (b, g, _) => releaseCount p st r b < g) }

def deadlineOf {n : Nat} (st : State n) (b : Block) (g : Nat) : Option Time :=
  ((st.obligations.find? (fun (target, level, _) =>
    target == b && level == g)).map (fun (_, _, deadline) => deadline))

def writeObligation {n : Nat} (st : State n) (b : Block) (g : Nat)
    (deadline : Time) : State n :=
  let newDeadline := max (deadlineOf st b g |>.getD deadline) deadline
  { st with obligations :=
    st.obligations.filter (fun (target, level, _) =>
      !(target == b && level == g)) ++ [(b, g, newDeadline)] }

def prefixSupport (p : Params) {n : Nat} (st : State n) (r : Slot) (b : Block) : Nat :=
  goldfishScore st.blocks (cleanSupport p st r) (cleanSupport p st r) b

/-- The single SA release threshold is the ceiling of half the seats. -/
def releaseThreshold (p : Params) : Nat := (p.n + 1) / 2

def savedGenuine {n : Nat} (st : State n) (r : Slot) : Option (Option Block) :=
  (st.genuine.find? (fun row => row.1 == r)).map Prod.snd

/-- Save the raw result before the local guard. A saved label is immutable. -/
def recordGenuine [LeasePolicy] {n : Nat} (st : State n) (r : Slot)
    (result : Option Block) : List (Slot × Option Block) :=
  if LeasePolicy.slowArming && !(savedGenuine st r).isSome then
    st.genuine ++ [(r, result)] else st.genuine

/-- The current genuine result is supplied separately. The preceding `m-1`
labels must all exist and cover the same prefix. No negative label is used. -/
def slowEligible (p : Params) {n : Nat} (st : State n) (r : Slot) (b : Block) : Bool :=
  p.m ≤ r + 1 && (List.range (p.m - 1)).all (fun j =>
    match savedGenuine st (r - (j + 1)) with
    | some (some C) => Block.preceq b C
    | _ => false)

/-- The shared gate changes only the selected lease levels. SA selects
its one level after either admission test. The outer gate checks containment. -/
def admissionLevels [LeasePolicy] (p : Params) {n : Nat} (st : State n)
    (r : Slot) (b : Block) : List Nat :=
  if LeasePolicy.slowArming then
    if releaseThreshold p ≤ prefixSupport p st r b || slowEligible p st r b then
      [releaseThreshold p] else []
  else
    (List.range (p.n + 1)).filter (fun g => g ∈ p.grid && g ≤ prefixSupport p st r b)

/-- A genuine gate advances G. It advances S and writes obligations only
when the result is compatible with every live target. The walk starts at `a`. -/
def gateFrom [LeasePolicy] (p : Params) {n : Nat} (a : Block) (st : State n) (r : Slot) :
    State n :=
  match confirmationFrom p a st r with
  | none => { st with genuine := recordGenuine st r none }
  | some h =>
      let levels := admissionLevels p st r
      let st := { st with
        goldfishRecord := advance st.goldfishRecord h
        genuine := recordGenuine st r (some h) }
      if st.obligations.any (fun (target, _, _) =>
        !Block.compatible target h) then st else
        let st := { st with stableRecord := advance st.stableRecord h }
        let prefixes := st.blocks.filter (fun b =>
          b != .genesis && Block.preceq b h)
        prefixes.foldl (fun acc b =>
          (levels b).foldl
            (fun acc g => writeObligation acc b g (gateTime p r + lifetime p)) acc) st

/-- A genuine gate advances G. It advances S and writes obligations only
when the result is compatible with every live target. -/
def gate [LeasePolicy] (p : Params) {n : Nat} (st : State n) (r : Slot) : State n :=
  match confirmation p st r with
  | none => { st with genuine := recordGenuine st r none }
  | some h =>
      let levels := admissionLevels p st r
      let st := { st with
        goldfishRecord := advance st.goldfishRecord h
        genuine := recordGenuine st r (some h) }
      if st.obligations.any (fun (target, _, _) =>
        !Block.compatible target h) then st else
        let st := { st with stableRecord := advance st.stableRecord h }
        let prefixes := st.blocks.filter (fun b =>
          b != .genesis && Block.preceq b h)
        prefixes.foldl (fun acc b =>
          (levels b).foldl
            (fun acc g => writeObligation acc b g (gateTime p r + lifetime p)) acc) st

theorem gate_eq_from_genesis [LeasePolicy] (p : Params) {n : Nat} (st : State n)
    (r : Slot) : gate p st r = gateFrom p .genesis st r := rfl

/-- Local public-time evaluations run for awake and asleep nodes. Equality
checks make each cutoff run once; same-time expiry precedes acquisition.
The gate walk starts at `a`. -/
def clockFrom [LeasePolicy] (p : Params) {n : Nat} (a : Block) (st : State n) (t : Time) :
    State n :=
  let st := expire { st with now := t } t
  let fSlot := ((t - 3 * p.Δ) / (4 * p.Δ)).toNat
  let st := if 0 ≤ t - 3 * p.Δ && t == freezeTime p fSlot then
    freeze p st fSlot else st
  let eSlot := ((t - 2 * p.Δ) / (4 * p.Δ)).toNat
  let st := if 0 ≤ t - 2 * p.Δ && t == earlyTime p eSlot then
    { st with early := st.early ++ [(eSlot, earlyVotes p st eSlot)] }
    else st
  let qSlot := ((t - 5 * p.Δ) / (4 * p.Δ)).toNat
  let st := if 0 ≤ t - 5 * p.Δ && t == releaseTime p qSlot then
    release p st qSlot else st
  let dSlot := ((t - 6 * p.Δ) / (4 * p.Δ)).toNat
  if 0 ≤ t - 6 * p.Δ && t == gateTime p dSlot then gateFrom p a st dSlot else st

/-- Local public-time evaluations run for awake and asleep nodes. Equality
checks make each cutoff run once; same-time expiry precedes acquisition. -/
def clock [LeasePolicy] (p : Params) {n : Nat} (st : State n) (t : Time) : State n :=
  let st := expire { st with now := t } t
  let fSlot := ((t - 3 * p.Δ) / (4 * p.Δ)).toNat
  let st := if 0 ≤ t - 3 * p.Δ && t == freezeTime p fSlot then
    freeze p st fSlot else st
  let eSlot := ((t - 2 * p.Δ) / (4 * p.Δ)).toNat
  let st := if 0 ≤ t - 2 * p.Δ && t == earlyTime p eSlot then
    { st with early := st.early ++ [(eSlot, earlyVotes p st eSlot)] }
    else st
  let qSlot := ((t - 5 * p.Δ) / (4 * p.Δ)).toNat
  let st := if 0 ≤ t - 5 * p.Δ && t == releaseTime p qSlot then
    release p st qSlot else st
  let dSlot := ((t - 6 * p.Δ) / (4 * p.Δ)).toNat
  if 0 ≤ t - 6 * p.Δ && t == gateTime p dSlot then gate p st dSlot else st

theorem clock_eq_from_genesis [LeasePolicy] (p : Params) {n : Nat} (st : State n)
    (t : Time) : clock p st t = clockFrom p .genesis st t := rfl

def confirmed {n : Nat} (st : State n) : Block := st.stableRecord

def stable {n : Nat} (st : State n) : Block := st.stableRecord

def block {n : Nat} : Msg n → Option Block
  | .proposal b _ _ => some b
  | .head _ => none

def slotsAt (p : Params) (t : Time) : List Slot :=
  (List.range (t.toNat + 1)).filter (fun s => proposalTime p s == t)

def duties (p : Params) (t : Time) : List Slot :=
  (List.range (t.toNat + 1)).filter (fun s => voteTime p s == t)

private theorem proposal_le_time (p : Params) (s : Slot) (t : Time)
    (h : proposalTime p s = t) : s ≤ t.toNat := by
  have hd : 1 ≤ p.Δ := by
    simpa using (Int.add_one_le_iff.mpr p.deltaPos)
  have hs : 0 ≤ (s : ℤ) := Int.natCast_nonneg s
  have hprod := mul_nonneg hs (show 0 ≤ 4 * p.Δ - 1 by nlinarith [hd])
  have ht : (s : ℤ) ≤ t := by
    dsimp [proposalTime] at h
    nlinarith [hprod]
  have htn : 0 ≤ t := le_trans hs ht
  have hcast := Int.toNat_of_nonneg htn
  exact_mod_cast (show (s : ℤ) ≤ (t.toNat : ℤ) by simpa [hcast] using ht)

private theorem vote_le_time (p : Params) (s : Slot) (t : Time)
    (h : voteTime p s = t) : s ≤ t.toNat := by
  have hd : 1 ≤ p.Δ := by
    simpa using (Int.add_one_le_iff.mpr p.deltaPos)
  have hs : 0 ≤ (s : ℤ) := Int.natCast_nonneg s
  have hprod := mul_nonneg hs (show 0 ≤ 4 * p.Δ - 1 by nlinarith [hd])
  have ht : (s : ℤ) ≤ t := by
    dsimp [voteTime, proposalTime] at h
    nlinarith [hprod]
  have htn : 0 ≤ t := le_trans hs ht
  have hcast := Int.toNat_of_nonneg htn
  exact_mod_cast (show (s : ℤ) ≤ (t.toNat : ℤ) by simpa [hcast] using ht)

theorem slotsAt_spec (p : Params) (s : Slot) (t : Time) :
    s ∈ slotsAt p t ↔ proposalTime p s = t := by
  simp only [slotsAt, List.mem_filter, List.mem_range, beq_iff_eq]
  constructor
  · intro h
    exact h.2
  · intro h
    exact ⟨Nat.lt_succ_of_le (proposal_le_time p s t h), h⟩

theorem duties_spec (p : Params) (s : Slot) (t : Time) :
    s ∈ duties p t ↔ voteTime p s = t := by
  simp only [duties, List.mem_filter, List.mem_range, beq_iff_eq]
  constructor
  · intro h
    exact h.2
  · intro h
    exact ⟨Nat.lt_succ_of_le (vote_le_time p s t h), h⟩

theorem slotsAt_nodup (p : Params) (t : Time) : (slotsAt p t).Nodup := by
  exact List.Nodup.filter _ List.nodup_range

theorem duties_nodup (p : Params) (t : Time) : (duties p t).Nodup := by
  exact List.Nodup.filter _ List.nodup_range

/-- Permanent rejection (design §2 E4) of a HEAD that is not yet processed:
its label `r` is before the previous slot (the clock only goes forward), or
its seat already equivocates at `r`. `admitVote` returns the state unchanged
in both cases, and in no later state of a valid run accepts the HEAD. A
processed HEAD is not excluded, and a proposal is never excluded. "Exactly the
permanent refusals" is a statement about objects that pass the wire check
(`wellFormed`). An ill-formed object is outside every valid run by
`DeliveryWellFormed.wire`, so `excludes` does not have to cover it. -/
def excludes (p : Params) {n : Nat} (st : State n) (o : Wire n) : Bool :=
  match o.auth, o.payload with
  | .seat r i, .head _ =>
      !decide (o ∈ st.votes) &&
        (decide (r + 1 < (st.now / (4 * p.Δ)).toNat) || equivocates (votesAt st r) i)
  | _, _ => false

/-- The C* instance: seat identities occur in authentication only. Every
seat of a label signs the same payload. Source: CONTRACT.md §2a. -/
def gridCO [LeasePolicy] (p : Params) : ProtocolSpec p.n where
  State := State p.n
  Label := Slot
  Payload := Msg p.n
  init := initial p.n
  clock := clock p
  actTime := voteTime p
  duties := duties p
  duties_spec := duties_spec p
  duties_nodup := duties_nodup p
  act := act p
  proposalTime := proposalTime p
  slotsAt := slotsAt p
  slotsAt_spec := slotsAt_spec p
  slotsAt_nodup := slotsAt_nodup p
  propose := propose p
  gossip := fun _ _ => []
  process := process p
  wellFormed := wellFormed
  depsPresent := depsPresent
  processed := processed
  excludes := excludes p
  handles := handles p
  carries := carries

end AvailableChain.GridCO
end
