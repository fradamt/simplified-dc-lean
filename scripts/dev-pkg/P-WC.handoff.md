# P-WC Round 2 handoff

Base: 318c74a37aa62d386c42d22afbec2ff21ca82968. Branch: sleep-pwc2.
Status: PREPARED. These suppliers compile with --wfail.
The complete event induction and the assembly consumers remain open.
Public Claims/Statements and public P23 are unchanged.

Import WC StepService or WCG StepService from the corresponding proof directory.
Each family has its own supplier modules. WCG has no WC proof import.

The internal participation input keeps every time from the first covered vote:
`SA.voteTime p.toParams (w.u + 1) ≤ t → t ≤ rho.horizon`.
Do not reduce this input to votes before the earlier gate actor is selected.
P-As must keep the source interval and continuation interval through this selection.
The source endpoint is inclusive; use the continuation count after that endpoint.

The store input is `RStoreDurable ∧ RStoreEpoch`. Use RMonoAll and RFrameNextEpoch.
The wake input is RestartsAtWakes. No sleep caller can supply global NoRestart.

The full service contracts follow. The implicit parameters are
`p : Params`, `c : AppCodec In`, `E : Generic.Env V`, and
`rho : V2.D.Run V (fgsa p c)`, with DecidableEq V and Fintype V.

```lean
abbrev WCService4Statement (ΔF : Time) (w : HealingWitness) (iStar : Nat) : Prop :=
  ∀
  (_hvalid : V2.D.ExecutionValid E rho)
  (_hlinked : V2.D.Linked (fgsaFamilies p c).linked rho)
  (_hcstar : V2.D.CStar (fgsaFamilies p c).fresh rho)
  (_hwakes : V2.D.RestartsAtWakes E rho)
  (_hdelta : E.Δ = p.Δ)
  (_hroots : NamedReceiptRootCollisionFree p c E rho)
  (_hsync : Gen.V2.Duty.PartialSynchronyBy E rho (fgsaDelay E.Δ ΔF))
  (_hdeltaF : E.Δ ≤ ΔF)
  (_hfault : (Gen.V2.Duty.faulty rho).card ≤ (p.n - 1) / 3)
  (_hfaultQ : Gen.Pure.FaultQ p.n (Gen.V2.Duty.faulty rho).card)
  (_hfaultX : Gen.Pure.FaultX p.n (Gen.V2.Duty.faulty rho).card)
  (_hpart : ∀ t, SA.voteTime p.toParams (w.u + 1) ≤ t → t ≤ rho.horizon →
    (Gen.V2.Duty.faulty rho).card < (joinedHonest p E rho t).card)
  (_hstore : RStore p c E rho)
  (_hcumul : RStoreDurable p c E rho ∧ RStoreEpoch p c E rho)
  (_hmono : RMonoAll p c E rho)
  (_hactive : RActive p c E rho)
  (_hframe : RFrameExactNext p c E rho)
  (_hmeta : RFrameNextEpoch p c E rho)
  (_hrec : RRec p c E rho)
  (_hgeo : RGeo p c E rho)
  (_hcert : RCert p c E rho)
  (_hsrc : TSrc p c E rho)
  (_hlabel : LabelBound p c E rho)
  (_hqc : RQCOrigin p c E rho)
  (_hstrat : RStrat p c E rho)
  (_hnoslash : ∀ x ∈ rho.honest, EmittedRowsNoSlash p c E rho x)
  (_hemitted : ∀ j x r a e, HonestRowAt p c E rho j x r a →
    namedEntry a.payload.height_pair = some e →
    ∃ C B, actionSourceFG p c E rho x r = some (some C) ∧
      e = (hOf p.E p.cfg C, (derive p.E p.cfg C).T_h.root) ∧
      FGBlock.Preceq (derive p.E p.cfg C).T_h C ∧
      gateResult p c E rho x (r * p.R) = some (some B) ∧
      Block.Preceq (eraseFG C) B ∧ fastAt p c E rho x (r * p.R) (eraseFG C))
  (_htargets : ∀ i x row, row ∈ (storeAt p c E rho i x).base.obligations →
    Block.Preceq row.1 (storeAt p c E rho i x).base.stableRecord)
  (_hlease : ∀ i x row, row ∈ (storeAt p c E rho i x).base.obligations →
    ∃ j < i, ∃ s B, IsGateTick p c rho j x s ∧ gatePassedAt p c E rho j ∧
      gateResultAt p c E rho j = some (some B) ∧ Block.Preceq row.1 B ∧
      (row.1, row.2.1) ∈
      (let wcView := actView (clockPre p (storeAt p c E rho j x) (SA.gateTime p.toParams s));
        (wcView.blocks.filter (fun b => b != .genesis && Block.preceq b B)).flatMap
          (fun b => (@GridCO.admissionLevels GridCO.slowLeasePolicy
            p.toParams.engine p.n .root wcView s b).map (fun g => (b, g)))) ∧
      row.2.2 = SA.gateTime p.toParams s + SA.lifetime p.toParams ∧
      row.2.2 = SA.releaseTime p.toParams (s + p.k) ∧
      ∀ k w C, j < k → k < i → enabledGateAt p c E rho k x w →
        let pre := clockPre p (storeAt p c E rho k x) (SA.gateTime p.toParams w)
        GridCO.savedGenuine pre.base w = none →
        SA.Root.confirmationFrom p.toParams (eraseFG pre.fg.F) (actView pre) w = some C →
        (actView pre).obligations.any (fun r => !Block.compatible r.1 C) = false →
        (row.1, row.2.1) ∉ (let wcView := actView pre;
        (wcView.blocks.filter (fun b => b != .genesis && Block.preceq b C)).flatMap
          (fun b => (@GridCO.admissionLevels GridCO.slowLeasePolicy
            p.toParams.engine p.n .root wcView w b).map (fun g => (b, g)))))
  (_hfast : ∀ i x,
    ∀ s X, X ∈ (FGSA.fastWriteAt (storeAt p c E rho i x) s).getD [] →
      ∃ j < i, V2.D.restartFree rho x j i ∧
      enabledGateAt p c E rho j x s ∧ gatePassedAt p c E rho j ∧
        ∃ B, gateResultAt p c E rho j = some (some B) ∧
          Block.Preceq X B ∧ fastAt p c E rho x s X)
  (_hdeadlines : ∀ i x,
    ∀ K g deadline, (K, g, deadline) ∈ (storeAt p c E rho i x).base.obligations →
      ∀ B, B ≠ .genesis → Block.Preceq B K →
        Gen.AC.Root.ProtectsUntil (storeAt p c E rho i x).base B g deadline)
  (_hheldRows : ∀ i x W, HeldAt p c E rho i x W → ∀ a ∈ chainRows W,
    ∃ (wire : RowWire p.n) (r : Nat), wire.toRow? = some a ∧
      wire.auth = .seat .fg a.signer ∧ ∃ k o t, k < i ∧
        rho.events[k]? = some (.deliver x o t) ∧
        ∀ z, RowSigner p c rho wire z → z ∈ rho.honest →
          HonestRowBefore p c E rho i z r wire ∧ p.actionTime r ≤ t)
  (_hscopeRows : ∀ D, RootBlockInRun p c E rho (eraseFG D) → ∀ a ∈ chainRows D,
    rho.seatOf (.base .fg) a.signer ∈ rho.honest → ∃ j r wire,
      HonestRowAt p c E rho j (rho.seatOf (.base .fg) a.signer) r wire ∧
      wire.toRow? = some a ∧ wire.auth = .seat .fg a.signer)
  (_hfinalHead : ∀ j z r a u, HonestRowAt p c E rho j z r a →
    RowSigner p c rho a z → a.toRow? = some u → ∀ fp,
    u.finality_pair = some fp → ∃ B, HeldAt p c E rho j z B ∧
      fp.height = (heightView p B).h_j ∧ fp.target = (heightView p B).J.root ∧
      TargetQCAt p.E B fp.height (heightView p B).J),
  WCSeed p c E rho w iStar →
    (∀ i, iStar ≤ i ∧ i ≤ rho.events.length → WCInv p c E rho w iStar i) →
    ∀ j x s B, x ∈ rho.honest → iStar ≤ j → IsGateTick p c rho j x s → w.u < s →
      gateResultAt p c E rho j = some (some B) →
      SA.gateTime p.toParams s + 4 * p.Δ ≤ rho.horizon →
      ∀ i y, afterTicksIdx rho (SA.gateTime p.toParams s + 4 * p.Δ) ≤ i →
        i ≤ rho.events.length → confirmedReaderIdx p c E rho y i →
          Block.Preceq B (S_at p c E rho i y)
```

Supplier: `wc_service4 : WCService4Statement p c E rho ΔF w iStar`.

```lean
abbrev WCGService4Statement (ΔF : Time) (w : HealingWitness) (iStar : Nat) : Prop :=
  ∀
  (_hvalid : V2.D.ExecutionValid E rho)
  (_hlinked : V2.D.Linked (fgsaFamilies p c).linked rho)
  (_hcstar : V2.D.CStar (fgsaFamilies p c).fresh rho)
  (_hwakes : V2.D.RestartsAtWakes E rho)
  (_hdelta : E.Δ = p.Δ)
  (_hroots : NamedReceiptRootCollisionFree p c E rho)
  (_hsync : Gen.V2.Duty.PartialSynchronyBy E rho (fgsaDelay E.Δ ΔF))
  (_hdeltaF : E.Δ ≤ ΔF)
  (_hfaultQ : Gen.Pure.FaultQ p.n (Gen.V2.Duty.faulty rho).card)
  (_haccountable : FinalitySlashableBound p c E rho)
  (_hpart : ∀ t, SA.voteTime p.toParams (w.u + 1) ≤ t → t ≤ rho.horizon →
    (Gen.V2.Duty.faulty rho).card < (joinedHonest p E rho t).card)
  (_hstore : RStore p c E rho)
  (_hcumul : RStoreDurable p c E rho ∧ RStoreEpoch p c E rho)
  (_hmono : RMonoAll p c E rho)
  (_hactive : RActive p c E rho)
  (_hframe : RFrameExactNext p c E rho)
  (_hmeta : RFrameNextEpoch p c E rho)
  (_hrec : RRec p c E rho)
  (_hgeo : RGeo p c E rho)
  (_hcert : RCert p c E rho)
  (_hsrc : TSrc p c E rho)
  (_hlabel : LabelBound p c E rho)
  (_hqc : RQCOrigin p c E rho)
  (_hstrat : RStrat p c E rho)
  (_hnoslash : ∀ x ∈ rho.honest, EmittedRowsNoSlash p c E rho x)
  (_hemitted : ∀ j x r a e, HonestRowAt p c E rho j x r a →
    namedEntry a.payload.height_pair = some e →
    ∃ C B, actionSourceFG p c E rho x r = some (some C) ∧
      e = (hOf p.E p.cfg C, (derive p.E p.cfg C).T_h.root) ∧
      FGBlock.Preceq (derive p.E p.cfg C).T_h C ∧
      gateResult p c E rho x (r * p.R) = some (some B) ∧
      Block.Preceq (eraseFG C) B ∧ fastAt p c E rho x (r * p.R) (eraseFG C))
  (_htargets : ∀ i x row, row ∈ (storeAt p c E rho i x).base.obligations →
    Block.Preceq row.1 (storeAt p c E rho i x).base.stableRecord)
  (_hlease : ∀ i x row, row ∈ (storeAt p c E rho i x).base.obligations →
    ∃ j < i, ∃ s B, IsGateTick p c rho j x s ∧ gatePassedAt p c E rho j ∧
      gateResultAt p c E rho j = some (some B) ∧ Block.Preceq row.1 B ∧
      (row.1, row.2.1) ∈
      (let wcView := actView (clockPre p (storeAt p c E rho j x) (SA.gateTime p.toParams s));
        (wcView.blocks.filter (fun b => b != .genesis && Block.preceq b B)).flatMap
          (fun b => (@GridCO.admissionLevels GridCO.slowLeasePolicy
            p.toParams.engine p.n .root wcView s b).map (fun g => (b, g)))) ∧
      row.2.2 = SA.gateTime p.toParams s + SA.lifetime p.toParams ∧
      row.2.2 = SA.releaseTime p.toParams (s + p.k) ∧
      ∀ k w C, j < k → k < i → enabledGateAt p c E rho k x w →
        let pre := clockPre p (storeAt p c E rho k x) (SA.gateTime p.toParams w)
        GridCO.savedGenuine pre.base w = none →
        SA.Root.confirmationFrom p.toParams (eraseFG pre.fg.F) (actView pre) w = some C →
        (actView pre).obligations.any (fun r => !Block.compatible r.1 C) = false →
        (row.1, row.2.1) ∉ (let wcView := actView pre;
        (wcView.blocks.filter (fun b => b != .genesis && Block.preceq b C)).flatMap
          (fun b => (@GridCO.admissionLevels GridCO.slowLeasePolicy
            p.toParams.engine p.n .root wcView w b).map (fun g => (b, g)))))
  (_hfast : ∀ i x,
    ∀ s X, X ∈ (FGSA.fastWriteAt (storeAt p c E rho i x) s).getD [] →
      ∃ j < i, V2.D.restartFree rho x j i ∧
        enabledGateAt p c E rho j x s ∧ gatePassedAt p c E rho j ∧
        ∃ B, gateResultAt p c E rho j = some (some B) ∧
          Block.Preceq X B ∧ fastAt p c E rho x s X)
  (_hdeadlines : ∀ i x,
    ∀ K g deadline, (K, g, deadline) ∈ (storeAt p c E rho i x).base.obligations →
      ∀ B, B ≠ .genesis → Block.Preceq B K →
        Gen.AC.Root.ProtectsUntil (storeAt p c E rho i x).base B g deadline)
  (_hheldRows : ∀ i x W, HeldAt p c E rho i x W → ∀ a ∈ chainRows W,
    ∃ (wire : RowWire p.n) (r : Nat), wire.toRow? = some a ∧
      wire.auth = .seat .fg a.signer ∧ ∃ k o t, k < i ∧
        rho.events[k]? = some (.deliver x o t) ∧
        ∀ z, RowSigner p c rho wire z → z ∈ rho.honest →
          HonestRowBefore p c E rho i z r wire ∧ p.actionTime r ≤ t)
  (_hscopeRows : ∀ D, RootBlockInRun p c E rho (eraseFG D) → ∀ a ∈ chainRows D,
    rho.seatOf (.base .fg) a.signer ∈ rho.honest → ∃ j r wire,
      HonestRowAt p c E rho j (rho.seatOf (.base .fg) a.signer) r wire ∧
      wire.toRow? = some a ∧ wire.auth = .seat .fg a.signer)
  (_hfinalHead : ∀ j z r a u, HonestRowAt p c E rho j z r a →
    RowSigner p c rho a z → a.toRow? = some u → ∀ fp,
    u.finality_pair = some fp → ∃ B, HeldAt p c E rho j z B ∧
      fp.height = (heightView p B).h_j ∧ fp.target = (heightView p B).J.root ∧
      TargetQCAt p.E B fp.height (heightView p B).J),
  WCSeed p c E rho w iStar →
    (∀ i, iStar ≤ i ∧ i ≤ rho.events.length → WCInv p c E rho w iStar i) →
    ∀ j x s B, x ∈ rho.honest → iStar ≤ j → IsGateTick p c rho j x s → w.u < s →
      gateResultAt p c E rho j = some (some B) →
      SA.gateTime p.toParams s + 4 * p.Δ ≤ rho.horizon →
      ∀ i y, afterTicksIdx rho (SA.gateTime p.toParams s + 4 * p.Δ) ≤ i →
        i ≤ rho.events.length → confirmedReaderIdx p c E rho y i →
          Block.Preceq B (S_at p c E rho i y)
```

Supplier: `wcg_service4 : WCGService4Statement p c E rho ΔF w iStar`.

The original gate and later reader inclusion types follow. The implicit parameters
also include `w : HealingWitness` and `iStar : Nat`. These suppliers carry the
service inclusion to both stable and confirmed getters.

```lean
theorem wc_gate_result_served {i j : Nat} {x : V} {s : Slot} {B : Block}
    (hsch : V2.D.ScheduleWellFormed E rho) (hi : WCInv p c E rho w iStar i)
    (hr : WCResult p c E rho w iStar i j x s B) :
    Block.Preceq B (S_at p c E rho (j + 1) x)
```

```lean
theorem wc_gate_result_outputs {n j : Nat} {x : V} {s : Slot} {B : Block} {t : Time}
    (hS : V2.D.ScheduleWellFormed E rho) (hs : WCSeed p c E rho w iStar)
    (inv : WCInv p c E rho w iStar n) (hr : WCResult p c E rho w iStar n j x s B)
    (ht : SA.gateTime p.toParams s ≤ t) (hin : timeIdx rho t ≤ n)
    (g : V2.D.Output (fgsa p c))
    (hg : g ∈ [(fgsaInterface p c).stable, (fgsaInterface p c).confirmed]) :
    Block.Preceq B (V2.D.outputAt E rho g x t)
```

```lean
theorem wc_service_result_outputs {d t : Time} {B : Block} {y : V}
    (hS : V2.D.ScheduleWellFormed E rho)
    (hservice : ∀ i x, afterTicksIdx rho d ≤ i → i ≤ rho.events.length →
      confirmedReaderIdx p c E rho x i → Block.Preceq B (S_at p c E rho i x))
    (hcut : afterTicksIdx rho d ≤ timeIdx rho t)
    (hy : confirmedReaderIdx p c E rho y (timeIdx rho t))
    (g : V2.D.Output (fgsa p c))
    (hg : g ∈ [(fgsaInterface p c).stable, (fgsaInterface p c).confirmed]) :
    Block.Preceq B (V2.D.outputAt E rho g y t)
```

```lean
theorem wcg_gate_result_served {i j : Nat} {x : V} {s : Slot} {B : Block}
    (hsch : V2.D.ScheduleWellFormed E rho) (hi : WCInv p c E rho w iStar i)
    (hr : WCResult p c E rho w iStar i j x s B) :
    Block.Preceq B (S_at p c E rho (j + 1) x)
```

```lean
theorem wcg_gate_result_outputs {n j : Nat} {x : V} {s : Slot} {B : Block} {t : Time}
    (hS : V2.D.ScheduleWellFormed E rho) (hs : WCSeed p c E rho w iStar)
    (inv : WCInv p c E rho w iStar n) (hr : WCResult p c E rho w iStar n j x s B)
    (ht : SA.gateTime p.toParams s ≤ t) (hin : timeIdx rho t ≤ n)
    (g : V2.D.Output (fgsa p c))
    (hg : g ∈ [(fgsaInterface p c).stable, (fgsaInterface p c).confirmed]) :
    Block.Preceq B (V2.D.outputAt E rho g x t)
```

```lean
theorem wcg_service_result_outputs {d t : Time} {B : Block} {y : V}
    (hS : V2.D.ScheduleWellFormed E rho)
    (hservice : ∀ i x, afterTicksIdx rho d ≤ i → i ≤ rho.events.length →
      confirmedReaderIdx p c E rho x i → Block.Preceq B (S_at p c E rho i x))
    (hcut : afterTicksIdx rho d ≤ timeIdx rho t)
    (hy : confirmedReaderIdx p c E rho y (timeIdx rho t))
    (g : V2.D.Output (fgsa p c))
    (hg : g ∈ [(fgsaInterface p c).stable, (fgsaInterface p c).confirmed]) :
    Block.Preceq B (V2.D.outputAt E rho g y t)
```

The gate path anchor is voteTime(s), with deadline earlyTime(s), receiver x,
and first=0. The transfer path anchor is earlyTime(s), with deadline
freezeTime(s), receiver y, and first=0. Pass this receiver's enabled gate
or the exact next voter's joinedAt guard. AnchorCoverage also supplies the
separate epoch from the strict Count read through the consuming action.

The four Count implementations now live in WC/StepGateBatch,
WC/StepTransferReceipts, WCG/StepGateBatch, and WCG/StepTransferReceipts.
Dynamics imports its family suppliers. The pinned Dynamics caller lines
1531 and 2817 map to these two WCG modules.

Serial integration: add the production imports and audit commands from
claude-files/sleep-pwc-round2-audit-fragment.txt to the existing
FGSAProofs audit key. The corresponding coverage fragment uses that same key.
Import these production modules directly into Tests.Axioms.
Do not import Tests.WeakContinuationSleepAxioms there. Keep that standalone
audit registered through the test glob. No new canonical coverage key is needed.
