module
public import AvailableChainFGSARun.Statements.AC
public import AvailableChainFGSAClaims.Statements.Healed

@[expose] public section

/-! P3 App. A.1/A.10, F0.8a. The generic composition rules stay in Gen:
Gen.Pure.AGRule.holds, Gen.Pure.firstFailure_holds, Gen.Pure.WindowRule.holds
(Proofs/Pure/FirstBad). Gen.Pure.RetroAt and Gen.V2.Duty.Pending supply the
retrospective and deadline predicates. No F2 invariant enters this module. -/

namespace AvailableChain.FGSA.Run

variable (p : Params) {In V : Type} (c : AppCodec In) (rho : V2.D.Run V (fgsa p c))

/-- Study §5.4 (895–903): event indices between consecutive post-gate cuts.
Slot zero starts at index zero. Consumers: F5, H.14–H.17, with Gen.Pure.WindowRule. -/
def windowIdx (s : Slot) (i : Nat) : Prop :=
  (match s with
   | 0 => True
   | s' + 1 => afterTicksIdx rho (SA.gateTime p.toParams s') ≤ i) ∧
  i < afterTicksIdx rho (SA.gateTime p.toParams s)

variable {rho} [DecidableEq V] (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

/-- P3 App. A.1: study §3.1 (229–260), 01 §8.4 (795–801).
Earlier rows and certificates, bounded labels, atomic reads, and fixed tick FG state. -/
structure TimingContract : Prop where
  rowLag : ∀ j k y r a x, HonestRowAt p c E rho j y r a →
    HandlesRowAt p c E rho k x a → j < k
  certLag : RStrat p c E rho
  label : LabelBound p c E rho
  atomic : ∀ i x, x ∈ rho.honest →
    FGSA.SACompat (storeAt p c E rho i x) ∧ FGSA.NestOK (storeAt p c E rho i x)
  tickFG : ∀ x t nd, preTick E rho x t = some nd →
    ∀ nd', postClock E rho x t = some nd' → nd'.st.fg = nd.st.fg

/-- P3 App. A.10, D09: unconditional FG channels of App. A.2.
Blueprint bp.store.v1, bp.frame.v1, bp.chainCertificates.v1,
bp.sourceDiscipline.v1, and bp.reconcile.v1. -/
structure FGFoundation : Prop where
  store : RStore p c E rho
  cumul : RStoreCumul p c E rho
  mono : RMono p c E rho
  frame : RFrameExact p c E rho
  geo : RGeo p c E rho
  strat : RStrat p c E rho
  reconcile : RRec p c E rho


open AvailableChain.SimplexFG
open Gen.Pure

/-- T-START (01:137–140,166–182; 22 I5:538–581), P3 A.7.
Consumers: FF1, F6, F8, FL-T7. Both clauses hold at every event index. -/
def TStart : Prop := Gen.AC.Duty.LeaseBelowOutput (fgsaAC E rho) ∧
  ∀ i x, x ∈ rho.honest →
    let st := storeAt p c E rho i x
    FGSA.liveRoot p st = eraseFG (FGSA.controls p st).Z ∨
      ∃ row ∈ st.base.obligations, st.base.now < row.2.2 ∧
        row.1 = FGSA.liveRoot p st ∧
        (∃ B ∈ FGSA.fullTree p st, eraseFG B = row.1) ∧ Block.Preceq row.1 (outputS p st)

/-- Full-batch read (01:150–157), P3 A.7. Consumer: TVote.
Admission resolves a held vote; finality coverage is the alternate case. -/
def FullVoteService (st : State p.n) (s : Slot) : Prop :=
  ∀ y (a : HeadWire p.n), y ∈ rho.honest →
    V2.D.Run.emits E rho y (ofHead p a) (SA.voteTime p.toParams s) →
    GridCO.headLabel? (baseVote a) = some s →
    baseVote a ∈ GridCO.votesAt st.base s ∧
    (a.payload ∈ (FGSA.actView st).blocks → a.payload.slot ≤ s →
      baseVote a ∈ (GridCO.votesAt st.base s).filter (fun o =>
        match GridCO.headTarget? o with
        | some h => GridCO.blockKnown (actView st) h && decide (h.slot ≤ s)
        | none => false))
/-- T-VOTE (01:150–157), P3 A.7 OD18, D67.
Consumers: FF1, F6, F8, FL-T7. Sync begins at the batch's vote time,
not at the later proposal/action. This is a composition service. -/
def TVote : Prop :=
  (∀ v st, Gen.V2.Duty.HonestSlot rho (fgsaInterface p c) v →
    Gen.V2.Duty.LabelSync E rho (SA.voteTime p.toParams (v - 1))
      (SA.proposalTime p.toParams v) →
    proposalStateAt p c E rho v = some st → FullVoteService p c E rho st (v - 1)) ∧
  (∀ r x nd, x ∈ rho.honest →
    Gen.V2.Duty.LabelSync E rho (SA.voteTime p.toParams (r * p.R + 1)) (p.actionTime r) →
    postClock E rho x (p.actionTime r) = some nd →
    FullVoteService p c E rho nd.st (r * p.R + 1)) ∧
  (∀ y s (a : HeadWire p.n), y ∈ rho.honest →
    V2.D.Run.emits E rho y (ofHead p a) (SA.voteTime p.toParams s) →
    ∃ nd, postClock E rho y (SA.voteTime p.toParams s) = some nd ∧ a.payload ∈ nd.st.base.blocks)

/-- Honest resolving seats of a read (01:158–164,184–199), P3 A.7.
Consumer: TWalk. The other seats have total size at most m. -/
def WalkBatch (st : State p.n) (s : Slot) (raw support : List (GridCO.Wire p.n))
    (Q : Block) (seats : Finset (Fin p.n)) (m : Nat) : Prop :=
  support ⊆ raw ∧ (∀ o ∈ raw, GridCO.headLabel? o = some s) ∧
  (∀ a ∈ seats, rho.seatOf (.base (.head s)) a ∈ rho.honest ∧
    ∃ o ∈ support, o ∈ raw ∧ GridCO.headSeat? o = some a ∧
      ∃ H, GridCO.headTarget? o = some H ∧ H ∈ st.base.blocks ∧ H.slot ≤ s ∧ Block.Preceq Q H) ∧
  ((GridCO.seats p.n raw).toFinset \ seats).card ≤ m ∧
  (∀ a ∈ seats, GridCO.equivocates raw a = false)

/-- T-WALK (01:158–164,184–199; 22 I8:637), P3 A.7.
Consumers: FF1, F6, F8, FF3–FF4, FL-*. Batch h m is the local count premise. -/
def TWalk : Prop := ∀ i x s raw support Q seats m,
  x ∈ rho.honest → Batch seats.card m →
  let st := storeAt p c E rho i x
  Q ∈ FGSA.fullTree p st → Block.Compatible (FGSA.liveRoot p st) (eraseFG Q) →
  WalkBatch p c rho st s raw support (eraseFG Q) seats m →
  Block.Preceq (eraseFG Q) (FGSA.getHead p st raw support) ∧
  ((∀ B ∈ FGSA.fullTree p st, FGBlock.Preceq Q B → B = Q) →
    FGSA.getHead p st raw support = eraseFG Q) ∧
  (∀ B, Block.Prec (FGSA.liveRoot p st) B → Block.Preceq B (FGSA.getHead p st raw support) →
    (∀ a ∈ seats, ∀ o ∈ support, GridCO.headSeat? o = some a →
      ∀ H, GridCO.headTarget? o = some H → ¬ Block.Preceq B H) →
    B.slot = st.slot p ∨ ∃ A ∈ st.fg.TF,
      eraseFG A = B.parent ∧ hOf p.E p.cfg A < (FGSA.controls p st).lo)

/-- The three composition services (01 §1.2), P3 A.7/A.10 D10.
Consumer: kernel. H3 and H4 remain projections of HealAC, not fields here. -/
structure CoreServices (_w : HealingWitness) : Prop where
  start : TStart p c E rho
  vote : TVote p c E rho
  walk : TWalk p c E rho

/-- Retained phase kinds (21 H.10:1263–1279), P3 A.10. Consumer: AttemptKey. -/
inductive PhaseKind | gap | topJ | contest
/-- Tasks in the per-phase budget table (21:1270–1279), P3 A.10. -/
inductive AttemptTask | raise | firstRow
/-- Attempt identity (21 H.10:1263–1279; HG.1–HG.5), P3 A.10.
Consumer: progress-attempt contract. A phase event ends the attempt. -/
structure AttemptKey where
  start : Nat
  frontier : Nat
  phase : PhaseKind
  task : AttemptTask
  served : Bool

/-- H.11 reset bound (21:1588–1595), P3 A.10. Consumers: both arrival statements. -/
def B'_reset (G : Time) : Time :=
  if p.k ≤ 2 * p.R + 1 then min (B_reset p G (ρΓ p G)) (B_reset p G (ρ₁ p G))
  else B_reset p G (ρΓ p G)
/-- Reset arrival, exactly H.11 (21:1572–1595), P3 A.10 with lead ruling
2026-09-30. Consumers: H.12–H.17. The reset horizon is unchanged.
A consumer of Q* must use ResetArrivalFullStatement. -/
def ResetArrivalStatement (G : Time) : Prop := p.δt = 2 * p.R →
  ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
    HealingSet p c E rho G → E.t_GST + B'_reset p G ≤ rho.horizon →
    ∃ w, H0Reset p c E rho w ∧ p.actionTime w.rStar < E.t_GST + B'_reset p G
/-- Full companion: H.11 reset plus H.18 (21:2868–2876;3174–3176),
P3 A.10 with lead ruling 2026-09-30. Consumers: full H0, HealingInput,
tstarOf and joined kernel. Only the horizon adds Γ + 4Δ; reset time does not. -/
def ResetArrivalFullStatement (G : Time) : Prop := p.δt = 2 * p.R →
  ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
    HealingSet p c E rho G → E.t_GST + B'_reset p G + Γ p G + 4 * p.Δ ≤ rho.horizon →
    ∃ w, H0 p c E rho w ∧ p.actionTime w.rStar < E.t_GST + B'_reset p G

/-- bp.finalityKernel.v1 conclusion (00:1124–1128), P3 A.10.
Consumer: kernel and finality claims. Afg is concluded, not assumed held.
Acceptance is strictly before the deadline. -/
def KernelConclusion (r : Nat) : Prop := ∀ A,
  HonestProposal E rho (fgsaInterface p c) (r * p.R) A →
  ∃ Afg : FGBlock (Fin p.n), eraseFG Afg = A ∧
    (∀ x ∈ rho.honest, Afg ∈ (storeAt p c E rho rho.events.length x).fg.TF) ∧
    ∃ U : FGBlock (Fin p.n), FGBlock.Preceq Afg U ∧ Afg ≠ U ∧
      hOf p.E p.cfg U = hOf p.E p.cfg Afg + 1 ∧
      ∀ x ∈ rho.honest, AcceptsFinalBefore p c E rho x U (↑(r + 2) * P p + 9 * p.Δ)
/-- Kernel point (00:1119–1134; 22 §1), P3 A.10 D12. Consumer: KernelPrem. -/
structure KernelPt where
  w : HealingWitness
  r : Nat
/-- Kernel premise split (22 §1:41–63; 00:1122–1123), P3 A.10.
Consumer: KernelFromContract. The disjunction is one run premise. -/
structure KernelPrem [Fintype V] (G : Time) (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) (pt : KernelPt) : Prop where
  set : Recovery₂ p c E rho G
  window : (FGood (Gen.V2.Duty.HonestSlot rho (fgsaInterface p c)) p.R pt.r ∧ G ≤ P p) ∨
    FGood4 (Gen.V2.Duty.HonestSlot rho (fgsaInterface p c)) p.R pt.r
  start : tstar p pt.w ≤ ↑pt.r * P p
  hhor : ↑(pt.r + 2) * P p + 9 * p.Δ ≤ rho.horizon
  input : HealingInput p c E rho pt.w
  services : CoreServices p c E rho pt.w
/-- Kernel from contract (00:1119–1134; 22 §1:41–63), P3 A.10.
Consumer: split-to-joined composition. The delay ratio is a parameter premise. -/
def KernelFromContract : Prop := p.δt = 2 * p.R →
  ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (G : Time) (pt : KernelPt),
    KernelPrem p c G E rho pt → KernelConclusion p c E rho pt.r
/-- AC side (01:126–129), P3 A.10. Consumer: kernel_of_split (F0.6b).
Recovery supplies participation and receipt; services are not HealingInput fields. -/
def KernelACSide : Prop := p.δt = 2 * p.R →
  ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (G : Time) (w : HealingWitness),
    Recovery₂ p c E rho G → HealingInput p c E rho w → CoreServices p c E rho w
/-- Joined kernel start (21 H.18:2868–2876), P3 A.10 D44.
Consumer: KernelJoinedPrem. The time comes from full H0. -/
def kernelStart (r : Nat) : Prop := ∃ t, tstarOf p c E rho = some t ∧ t ≤ ↑r * P p


/-- T-side healing contract (21 H.3–H.18), P3 A.10.
Consumer: F5 composition. Only reset delivery has an H0 premise. -/
structure HealTContract (w : HealingWitness) : Prop where
  del : TDel p c E rho
  delReset : TDelReset p c E rho w
  perm : TPerm p c E rho
  repair : TRepair p c E rho
  common : TCommon p c E rho
  frontier : TFrontier p c E rho
  geom : TGeom p c E rho


/-- Global frontier at an event prefix (21 H.7:918–1012), P3 A.10.
Consumers: effective events and attempts. -/
def frontierAtIdx (i : Nat) : Nat := rho.honest.sup (fun x => (storeAt p c E rho i x).fg.h_max)
/-- Accepted top-J evidence at the frontier (21 H.7:918–1012), P3 A.10.
Consumers: phase classification and effective events. -/
def TopEvidence (i m : Nat) : Prop := ∃ x, x ∈ rho.honest ∧
  (storeAt p c E rho i x).fg.h_j + 1 = m
/-- Accepted contest evidence at the frontier (21 H.7:918–1012), P3 A.10.
Consumers: phase classification and effective events. -/
def ContestEvidence (i m : Nat) : Prop := ∃ x, x ∈ rho.honest ∧
  (R_at p c E rho i x).H = m ∧ (R_at p c E rho i x).contest = true
/-- Effective event (21 H.7:1003–1012; H.10:1263–1265), P3 A.4/A.10.
Consumers: attempts. A lower F move is not an effective event. -/
def EffectiveEvent (i : Nat) : Prop :=
  frontierAtIdx p c E rho i < frontierAtIdx p c E rho (i + 1) ∨
  (let m := frontierAtIdx p c E rho (i + 1)
   (¬ TopEvidence p c E rho i m ∧ TopEvidence p c E rho (i + 1) m) ∨
   (¬ ContestEvidence p c E rho i m ∧ ContestEvidence p c E rho (i + 1) m))
/-- Phase selected by global accepted evidence (21 H.7:1003–1012), P3 A.10.
Consumer: AttemptValid. -/
def AttemptPhaseAt (i m : Nat) (kind : PhaseKind) : Prop :=
  match kind with
  | .gap => ¬ TopEvidence p c E rho i m ∧ ¬ ContestEvidence p c E rho i m
  | .topJ => TopEvidence p c E rho i m ∧ ¬ ContestEvidence p c E rho i m
  | .contest => ContestEvidence p c E rho i m
/-- A served frontier proposal by a given time (21 HG.1:1333–1350), P3 A.10.
Consumer: the served flag of AttemptValid. -/
def ServedFrontier (m : Nat) (t : Time) : Prop := ∃ s Q Qfg,
  HonestProposal E rho (fgsaInterface p c) s Q ∧ eraseFG Qfg = Q ∧
  hOf p.E p.cfg Qfg = m ∧ SA.gateTime p.toParams s ≤ t ∧ ExactService p c E rho s Q
/-- Attempt validity (21 H.10:1263–1279; H.11:1572–1595; HG.1:1333–1350),
P3 A.10 D44. Consumers: progress-attempt contract and HealingAttemptPrem.
start is the event index; its resulting prefix is start+1. The inclusive-cut
alternative requires that exact resulting prefix. No budget horizon is hidden here. -/
def AttemptValid (k : AttemptKey) : Prop := ∃ ev,
  rho.events[k.start]? = some ev ∧ E.t_GST ≤ ev.time ∧
  (EffectiveEvent p c E rho k.start ∨
    ∃ rG, E.t_GST ≤ p.actionTime rG ∧
      (∀ r, E.t_GST ≤ p.actionTime r → rG ≤ r) ∧
      ev.time = p.actionTime (rG + 2) ∧
      timeIdx rho (p.actionTime (rG + 2)) = k.start + 1) ∧
  k.frontier = frontierAtIdx p c E rho (k.start + 1) ∧ 2 ≤ k.frontier ∧
  AttemptPhaseAt p c E rho (k.start + 1) k.frontier k.phase ∧
  (k.served = true ↔ ServedFrontier p c E rho k.frontier ev.time) ∧
  (k.task = .firstRow → ∀ j y r a h e, j ≤ k.start → HonestRowAt p c E rho j y r a →
    namedEntry a.payload.height_pair = some (h, e) → h ≠ k.frontier)
/-- Retained H.10 budget table (21:1270–1279), P3 A.10.
Consumer: progress-attempt contract. This uses the unconditional two-lease bound;
HG improvements can be separate bounds for attempts with served=true. -/
def attemptBudget (G : Time) (k : AttemptKey) : Time :=
  match k.task, k.phase with
  | .raise, .contest => ρΓ p G + 3 * P p + Γ p G - 10 * p.Δ
  | .raise, _ => ρΓ p G + 6 * P p + 2 * Γ p G - 18 * p.Δ
  | .firstRow, .contest => ρΓ p G + P p - p.Δ
  | .firstRow, _ => ρΓ p G + 4 * P p + Γ p G - 9 * p.Δ
/-- Event or completed task within a duration (21 H.10:1263–1279), P3 A.10.
Consumer: progress-attempt contract. Service never continues through an earlier event. -/
def AttemptEndsBy (k : AttemptKey) (budget : Time) : Prop := ∃ ev,
  rho.events[k.start]? = some ev ∧
  ∃ j ev', k.start < j ∧ rho.events[j]? = some ev' ∧ ev'.time ≤ ev.time + budget ∧
    (EffectiveEvent p c E rho j ∨
      (k.task = .raise ∧ k.frontier < frontierAtIdx p c E rho (j + 1)) ∨
      (k.task = .firstRow ∧ ∃ y r a e, HonestRowAt p c E rho j y r a ∧
        namedEntry a.payload.height_pair = some (k.frontier, e)))

end AvailableChain.FGSA.Run
end
