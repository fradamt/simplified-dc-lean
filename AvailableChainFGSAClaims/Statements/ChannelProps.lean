module
public import AvailableChainFGSAClaims.Statements.Channels
public import AvailableChainFGSA.Statements.Invariants

@[expose] public section

/-! Safety channels, P3 App. A.2–A.5 (F0.8a). Each predicate describes one
run. The claim forms supply regimes. F0.8b adds Witness and the healing tier.
The property kernel remains Gen.Pure.CompatOn, MonoOn, BelowOn, ServedOn. -/

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

variable (p : Params) {In V : Type} (c : AppCodec In) [DecidableEq V]
    (E : Generic.Env V) (rho : V2.Run V (fgsa p c))

/-- bp.store.v1 (00:516–527), bp.activeView.v1 (00:529–536); 01 §§4–5.
Consumers: all lanes. Producer: T7.5 and F1.1. This is a snapshot;
`RStoreCumul` states the temporal part. -/
def RStore : Prop := ∀ i x, x ∈ rho.honest →
  let st := storeAt p c E rho i x
  FGSA.CStoreInv p st ∧
  (∀ b, b ∈ (FGSA.actView st).blocks ↔
    b ∈ st.base.blocks ∧ Block.Compatible b (eraseFG st.fg.F)) ∧
  Block.genesis ∈ (FGSA.actView st).blocks ∧
  eraseFG st.fg.F ∈ (FGSA.actView st).blocks ∧
  (∀ b ∈ (FGSA.actView st).blocks, ∀ a, Block.Preceq a b →
    a ∈ (FGSA.actView st).blocks) ∧
  (FGSA.actView st).votes = st.base.votes ∧
  (FGSA.actView st).blockStamp = st.base.blockStamp ∧
  (FGSA.actView st).voteStamp = st.base.voteStamp

/-- bp.store.v1 (00:517–518): cumulative T and unchanged old stamps.
Consumers: all lanes, 02 §5.2, 21 H.12. Producer: F1.1 via
`process_cumulative` and `clock_cumulative`. Restarts reset the store. -/
def RStoreCumul : Prop := V2.NoRestart rho → ∀ i j x, x ∈ rho.honest →
  i ≤ j → j ≤ rho.events.length →
  let st := storeAt p c E rho i x
  let st' := storeAt p c E rho j x
  st.fg.TF ⊆ st'.fg.TF ∧ st.base.blocks <+: st'.base.blocks ∧
  st.base.blockStamp <+: st'.base.blockStamp ∧ st.base.voteStamp <+: st'.base.voteStamp

/-- bp.store.v1 (00:516–527), last sentence: F, the lex pair, and H increase.
Consumers: 02 §5.3, 03 F′ cases, 22 FF2. Producer: F1.1 via `fMonotone`,
`process_pair_mono`, and `process_hmax_mono`. -/
def RMono : Prop := V2.NoRestart rho → ∀ i j x, x ∈ rho.honest → i ≤ j →
  let st := storeAt p c E rho i x
  let st' := storeAt p c E rho j x
  FGBlock.Preceq st.fg.F st'.fg.F ∧
  lexKey (st.fg.h_j, st.fg.J) ≤ lexKey (st'.fg.h_j, st'.fg.J) ∧
  st.fg.h_max ≤ st'.fg.h_max

/-- bp.frame.v1 (00:581–587), 01 §1.1 and §4.3: cached controls and D(Σ.T).
Consumers: 02 §4.1, 22 F6/F8/FL-T7, 21 H.17. Producer: F1.1 via `storeControls_eq`. -/
def RFrameExact : Prop := ∀ i x, x ∈ rho.honest →
  let st := storeAt p c E rho i x
  FGSA.controls p st = SimplexFG.fjControls p.E p.cfg st.fg.F st.fg.TF ∧
  FGSA.fullTree p st = domainR p st st.fg.TF

/-- bp.chainCertificates.v1 (00:503–514): path heights and entries.
Consumers: 02 §3.1, 21 H.9(a), 22 I2. Producer: F1.1 from KitFG
`h_mono`, `derive_node_height_cases`, `entry_same_height`, `entry_eq_on_plateau`. -/
def RGeo : Prop := ∀ i x W, x ∈ rho.honest → W ∈ (storeAt p c E rho i x).fg.TF →
  hOf p.E p.cfg (.genesis : FGBlock (Fin p.n)) = 1 ∧
  (∀ A B, FGBlock.Preceq A B → FGBlock.Preceq B W → hOf p.E p.cfg A ≤ hOf p.E p.cfg B) ∧
  (∀ B, FGBlock.Preceq B W → hOf p.E p.cfg B ≤ hOf p.E p.cfg B.parent + 1) ∧
  (∀ B, FGBlock.Preceq B W →
    FGBlock.Preceq (derive p.E p.cfg B).T_h B ∧
    hOf p.E p.cfg (derive p.E p.cfg B).T_h = hOf p.E p.cfg B) ∧
  (∀ A B, FGBlock.Preceq A B → FGBlock.Preceq B W →
    hOf p.E p.cfg A = hOf p.E p.cfg B → (derive p.E p.cfg A).T_h = (derive p.E p.cfg B).T_h)

/-- bp.reconcile.v1 (00:559–567), 01 §6: the exact AC edits at an F move.
The displayed record update isolates reconcile from the other admission writes.
Consumers: 02 §5.3, 03 F′ cases, 21 IF.7, 22 I5. Producer: F1.4 via
`reconcile_frame`, `reconcile_harmless_origin`, `admitBlock_reconcile_harmless`. -/
def RRec : Prop := ∀ i x, x ∈ rho.honest → FAdvanceAt p c E rho i x →
  let st := storeAt p c E rho i x
  let st' := storeAt p c E rho (i + 1) x
  st'.base.obligations = st.base.obligations.filter (fun row => FGSA.activeCompatible st' row.1) ∧
  st'.base.genuine = st.base.genuine.map
    (fun row => (row.1, row.2.filter (FGSA.activeCompatible st'))) ∧
  st'.fastWrite = st.fastWrite.map
    (fun row => (row.1, row.2.filter (FGSA.activeCompatible st'))) ∧
  st'.base.stableRecord =
    (if Block.preceq (eraseFG st'.fg.F) st.base.stableRecord then st.base.stableRecord
     else eraseFG st'.fg.F) ∧
  (V2.Run.stateBefore E rho (i + 1) x).record = (V2.Run.stateBefore E rho i x).record ∧
  (∀ u : State p.n, FGSA.reconcile u = { u with
    base := { u.base with
      obligations := u.base.obligations.filter (fun row => FGSA.activeCompatible u row.1)
      genuine := u.base.genuine.map (fun row => (row.1, row.2.filter (FGSA.activeCompatible u)))
      stableRecord := if Block.preceq (eraseFG u.fg.F) u.base.stableRecord then
        u.base.stableRecord else eraseFG u.fg.F }
    fastWrite := u.fastWrite.map (fun row => (row.1, row.2.filter (FGSA.activeCompatible u))) })

/-- 01 §1.1 T-SRC (74–79), bp.sourceDiscipline.v1(a) (00:689–697).
Consumers: CPPrefix in 02 §5.4 and 03 §8, 21 H.11, 22 kernel.
Producer: F1.5(a) via `FastOrigin`, `fastOrigin_gateStep`, `deepest_spec`. -/
def TSrc : Prop := ∀ x r C, x ∈ rho.honest →
  actionSource p c E rho x r = some (some C) →
  ∃ X G, candidatesAt p c E rho x r = some X ∧ C ∈ X ∧
    gateResult p c E rho x (r * p.R) = some (some G) ∧
    (∀ B ∈ X, Block.Preceq B G) ∧ (∀ B ∈ X, fastAt p c E rho x (r * p.R) B) ∧
    ∃ j, IsGateTick p c rho j x (r * p.R) ∧ gatePassedAt p c E rho j

/-- 01 §8.4 (795–801): earlier honest row sources have bounded gate labels.
This also applies to every such row used by a duty. At q_s the bound is s−1;
at a positive-slot proposal or HEAD it is s−2. Consumers: TimingContract.label
and BelowLabel in the Clean induction. Producer: F1.5(d). -/
def LabelBound : Prop := ∀ i x y r a t, x ∈ rho.honest →
  rho.events[i]? = some (.tick x t) → HonestRowBefore p c E rho i y r a →
  r * p.R ≤ labelBoundAt p c rho i ∧
  (∀ s, t = SA.releaseTime p.toParams s → r * p.R ≤ s - 1) ∧
  (∀ s, 1 ≤ s → (t = SA.proposalTime p.toParams s ∨ t = SA.voteTime p.toParams s) →
    r * p.R ≤ s - 2)

/-- bp.cleanHistory.v1 (00:767–775): honest raw results through b₀ lie on
one chain; each nonempty emitted name through b₀ lies below such a result.
Consumers: no lane assumes this; F2 proves it as the Clean composition result. -/
def TChain (b₀ : Time) : Prop :=
  (∀ x y s r B C, x ∈ rho.honest → y ∈ rho.honest →
    SA.gateTime p.toParams s ≤ b₀ → SA.gateTime p.toParams r ≤ b₀ →
    gateResult p c E rho x s = some (some B) → gateResult p c E rho y r = some (some C) →
    Block.Compatible B C) ∧
  (∀ i x r a e t, HonestRowAt p c E rho i x r a →
    rho.events[i]? = some (.tick x t) → t ≤ b₀ → namedEntry a.payload.height_pair = some e →
    ∃ s B X, SA.gateTime p.toParams s ≤ b₀ ∧ gateResult p c E rho x s = some (some B) ∧
      (hOf p.E p.cfg X, X.root) = e ∧ Block.Preceq (eraseFG X) B)

/-- 03 §8.3 (702–726): after arming at d_j, honest sources are compatible
with protected B. Consumers: no lane assumes this; F3 proves it. -/
def TCompat (B : Block) (j : Slot) : Prop := ∀ x r C, x ∈ rho.honest →
  SA.gateTime p.toParams j ≤ p.actionTime r → actionSource p c E rho x r = some (some C) →
  Block.Compatible C B

/-- S3 D09, P3 App. A.10: the source-frame predicate is closed under ancestors.
Consumers: F1.5 source frame, then F2–F5 via SrcFrameAboveStmt. -/
structure AncestorClosed (Φ : FGBlock (Fin p.n) → Prop) : Prop where
  down : ∀ X Y, FGBlock.Preceq X Y → Φ Y → Φ X

/-- P3 App. A.10: bp.cleanFrame.v1, 02 §3; lead FB1.
Each frame block above the threshold satisfies Φ. -/
def FrameBelow (Φ : FGBlock (Fin p.n) → Prop) (c₀ : Nat)
    (R : Controls (Fin p.n)) : Prop :=
  (c₀ ≤ hOf p.E p.cfg R.F → Φ R.F) ∧
  (c₀ ≤ hOf p.E p.cfg R.J → Φ R.J) ∧
  (c₀ ≤ hOf p.E p.cfg R.Z → Φ R.Z)

/-- P3 App. A.2: bp.sourceDiscipline.v1(b,c), 01 §8.4, 02 §§3.3–3.5.
Each non-genesis certified entry has an earlier honest row at its height. -/
def RStrat : Prop := ∀ i x W, x ∈ rho.honest →
  W ∈ (storeAt p c E rho i x).fg.TF →
  ∀ e ∈ certified p W, e ≠ .genesis →
    ∃ y r, ∃ a : RowWire p.n, HonestRowBefore p c E rho i y r a ∧
      namedEntry a.payload.height_pair = some (hOf p.E p.cfg e, e.root)

/-- P3 App. A.10, S3 D09: bp.sourceDiscipline.v1, 01 §8.4.
T1 names an FG block by its height and root.
genesis case: P3 r3.5.6 form refutable at index 0; lead G1. -/
def SrcFrameAbove (Φ : FGBlock (Fin p.n) → Prop) (c₀ : Nat) : Prop :=
  (c₀ ≤ hOf p.E p.cfg (.genesis : FGBlock (Fin p.n)) → Φ .genesis) →
  ∀ i x, x ∈ rho.honest →
    (∀ y r (a : RowWire p.n) (e : FGBlock (Fin p.n)),
      HonestRowBefore p c E rho i y r a →
      namedEntry a.payload.height_pair = some (hOf p.E p.cfg e, e.root) →
      c₀ ≤ hOf p.E p.cfg e → Φ e) →
    (∀ W ∈ (storeAt p c E rho i x).fg.TF, ∀ e ∈ certified p W,
      c₀ ≤ hOf p.E p.cfg e → Φ e) ∧ FrameBelow p Φ c₀ (R_at p c E rho i x)

/-- P3 App. A.10, S3 D09: source frame at threshold zero. -/
abbrev SrcFrame (Φ : FGBlock (Fin p.n) → Prop) : Prop :=
  SrcFrameAbove p c E rho Φ 0

/-- P3 App. A.10, G30: source frame for each ancestor-closed predicate and threshold.
Blueprint bp.sourceDiscipline.v1, 01 §8.4. -/
def SrcFrameAboveStmt : Prop :=
  ∀ (Φ : FGBlock (Fin p.n) → Prop) (c₀ : Nat),
    AncestorClosed p Φ → SrcFrameAbove p c E rho Φ c₀

/-- P3 App. A.3: bp.cleanFrame.v1 (00:733–741), 02 §3.
The EntryBelow premise and prefix conclusion are frozen. -/
def CPPrefix : Prop := ∀ i x (B : FGBlock (Fin p.n)), x ∈ rho.honest →
  (∀ y r (a : RowWire p.n) e, HonestRowBefore p c E rho i y r a →
    namedEntry a.payload.height_pair = some e → EntryBelow p e B) →
  (∀ W ∈ (storeAt p c E rho i x).fg.TF, ∀ e ∈ certified p W, FGBlock.Preceq e B) ∧
  (let R := R_at p c E rho i x
   FGBlock.Preceq R.F B ∧ FGBlock.Preceq R.J B ∧ FGBlock.Preceq R.Z B ∧
   R.contest = false ∧ R.lo ≤ hOf p.E p.cfg B)

/-- P3 App. A.3: bp.outageCompatibility.v1 (00:850–859), 03 §7.
Every contest witness extends B (lead-approved universal form). -/
def CPCompat : Prop := ∀ i x (B : FGBlock (Fin p.n)), x ∈ rho.honest →
  (∀ y r (a : RowWire p.n) (e : FGBlock (Fin p.n)),
    HonestRowBefore p c E rho i y r a →
    namedEntry a.payload.height_pair = some (hOf p.E p.cfg e, e.root) →
    FGBlock.Preceq e B ∨ FGBlock.Preceq B e) →
  (∀ W ∈ (storeAt p c E rho i x).fg.TF, ∀ e ∈ certified p W,
    FGBlock.Preceq e B ∨ FGBlock.Preceq B e) ∧
  (let st := storeAt p c E rho i x
   let R := R_at p c E rho i x
   (FGBlock.Preceq R.F B ∨ FGBlock.Preceq B R.F) ∧
   (FGBlock.Preceq R.J B ∨ FGBlock.Preceq B R.J) ∧
   (B ∈ st.fg.TF → FGBlock.Preceq R.F B →
     FGBlock.Preceq B R.Z ∨ B ∈ domainR p st st.fg.TF) ∧
   (R.contest = true → FGBlock.Preceq B R.J ∧
     ∀ W ∈ st.fg.TF, hOf p.E p.cfg W = R.H → ¬ FGBlock.Preceq R.J W →
       FGBlock.Preceq B W))

end AvailableChain.FGSA.Run
end
