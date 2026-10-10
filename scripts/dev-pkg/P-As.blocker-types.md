# P-As round 2 — exact blocked declaration types

These are current source declarations in the failed import closures, not new assumptions.
The build log is `.lake/sleep-pas2/targets-build.log`. A legacy NoRestart type is not
available from a sleep regime. Repair belongs to the listed owner. Local fixture
failures have no missing family supplier; their owner must repair the execution proof.

## B01 — P-As

AvailableChainFGSAInhabit/WeakContinuationW1.lean:91; first build error at :106.
Declaration: w1_known_fold. Read the type with this module's section variables.

```lean
theorem w1_known_fold (P : Obj params → Prop) (w : World) (es : List Event)
    (hw : ∀ v, GenKnown P (w v).st)
    (he : ∀ v o t, V2.Event.deliver v o t ∈ es →
      P o ∧ ∀ o', carriesS params o o' → P o') :
    ∀ v, GenKnown P (genFold w es v).st
```

## B02 — P-Cl2

AvailableChainFGSAProofs/Proofs/Clean/Export.lean:107; first build error at :111.
Declaration: cleanSafetyAt_of_trunc. Read the type with this module's section variables.

```lean
theorem cleanSafetyAt_of_trunc (p : Params) {In V : Type} [DecidableEq V]
    (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hs : V2.D.ScheduleWellFormed E rho)
    (ht : CleanTruncAt p c E rho rho.horizon) : CleanSafetyAt p c E rho
```

## B03 — P-H1

AvailableChainFGSAProofs/Proofs/Healing/SupportTransfer.lean:226; first build error at :242.
Declaration: healing_support_honest_head. Read the type with this module's section variables.

```lean
theorem healing_support_honest_head (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hE : V2.D.ExecutionValid E rho) {i : Nat} {x : V} {s : Slot} {k : Fin p.n}
    {o : GridCO.Wire p.n .root} (ho : o ∈ (storeAt p c E rho i x).base.votes)
    (hl : GridCO.headLabel? o = some s) (hk : GridCO.headSeat? o = some k)
    (hh : rho.seatOf (.base (.head s)) k ∈ rho.honest) :
    ∃ j, rho.events[j]? = some (.tick (rho.seatOf (.base (.head s)) k)
        (SA.voteTime p.toParams s)) ∧
      GridCO.headTarget? o = some (headVote p (FGSA.clock p
        (V2.D.Run.stateBefore E rho j (rho.seatOf (.base (.head s)) k)).st
        (SA.voteTime p.toParams s)) s).root
```

## B04 — P-Ou

AvailableChainFGSAProofs/Proofs/Outage/ContinuationReceipt.lean:19; first build error at :36.
Declaration: outageV_source_path. Read the type with this module's section variables.

```lean
theorem outageV_source_path (hsch : V2.D.ScheduleWellFormed E rho)
    {k : Nat} {y : V} {K : Block} {u : Time}
    (hK : K ∈ (storeAt p c E rho k y).base.blocks)
    (hcut : ∀ l < k, ∀ e, rho.events[l]? = some e → e.time ≤ u) :
    ∀ b, Block.Preceq b K → b ≠ .genesis →
      ∃ l < k, ∃ t o, blockOf? p o = some b ∧
        V2.D.Run.acceptsAt E rho l y o t ∧ 0 ≤ t ∧ t ≤ u
```

## B05 — P-Ou

AvailableChainFGSAProofs/Proofs/Outage/ExactProposalRetained.lean:142; first build error at :151.
Declaration: inclusion_comparison_lift. Read the type with this module's section variables.

```lean
theorem inclusion_comparison_lift (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {i : Nat} {r : Slot} {D0 : Block} (hD : (r, D0) ∈ cleanResults p c E rho i) :
    ∃ D : FGBlock (Fin p.n), eraseFG D = D0
```

## B06 — P-Ou

AvailableChainFGSAProofs/Proofs/Outage/PersistenceStep.lean:114; first build error at :187.
Declaration: outage_gateStep_protection. Read the type with this module's section variables.

```lean
theorem outage_gateStep_protection (p : Params) {B : Block} {j s : Slot} (st : State p.n)
    (hinv : CStoreInv p st) (hp : OutageProtection p B j st)
    (hc : Block.Compatible (eraseFG st.fg.F) B) (hjs : j ≤ s) :
    OutageProtection p B j (FGSA.gateStep p st s)
```

## B07 — P-Ou

AvailableChainFGSAProofs/Proofs/Outage/Suppliers.lean:15; first build error at :110.
Declaration: outage_supplier_history. Read the type with this module's section variables.

```lean
theorem outage_supplier_history (p : Params)
    (hsrc : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
      (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (pt : Unit),
      SourceDisciplinePrem p c E rho pt → SrcFrameAboveStmt p c E rho)
    (hordered : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
      (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) {ΔF : Time} (pt : PtB₀),
      CleanCutPrem p c E rho pt ΔF →
      ∀ x y r s B C, x ∈ rho.honest → y ∈ rho.honest →
        SA.gateTime p.toParams r ≤ pt.b₀ → SA.gateTime p.toParams s ≤ pt.b₀ →
        gateResult p c E rho x r = some (some B) →
        gateResult p c E rho y s = some (some C) →
        (r < s → Block.Preceq B C) ∧ (r = s → Block.Compatible B C))
    (hnonempty : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
      (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) {ΔF : Time} (pt : PtB₀),
      CleanCutPrem p c E rho pt ΔF →
      ∀ j x s, j < timeIdx rho pt.b₀ → x ∈ rho.honest → IsGateTick p c rho j x s →
        ∃ B, gateResultAt p c E rho j = some (some B) ∧ (s = 0 → B = .genesis))
    (htransfer : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
      (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) {ΔF : Time} (pt : PtB₀),
      CleanCutPrem p c E rho pt ΔF →
      ∀ x y s B H, x ∈ rho.honest → y ∈ rho.honest →
        SA.gateTime p.toParams s ≤ pt.b₀ → gateResult p c E rho x s = some (some B) →
        vHead p c E rho y s = some H → Block.Preceq B H)
    (hleases : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
      (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) {ΔF : Time} (pt : PtB₀),
      CleanCutPrem p c E rho pt ΔF →
      ∀ i v, i ≤ timeIdx rho pt.b₀ → v ∈ rho.honest →
        let st := storeAt p c E rho i v
        let below := BelowLabel p c E rho i (labelBoundAt p c rho i)
        below (F_at p c E rho i v) ∧ below (J_at p c E rho i v) ∧
        below (S_at p c E rho i v) ∧
        (∀ row ∈ st.base.obligations, below row.1 ∧
          ∃ j < i, ∃ s B, IsGateTick p c rho j v s ∧ gatePassedAt p c E rho j ∧
            gateResultAt p c E rho j = some (some B) ∧ Block.Preceq row.1 B) ∧
        (∀ s C, GridCO.savedGenuine st.base s = some (some C) → below C ∧
          ∃ j < i, IsGateTick p c rho j v s ∧ gateResultAt p c E rho j = some (some C)) ∧
        (∀ j s C, j < i → IsGateTick p c rho j v s →
          gateResultAt p c E rho j = some (some C) →
          GridCO.savedGenuine st.base s = some (some C)) ∧
        (∀ s X, X ∈ (FGSA.fastWriteAt st s).getD [] → below X ∧
          ∃ j < i, IsGateTick p c rho j v s ∧ gatePassedAt p c E rho j ∧
            ∃ C, gateResultAt p c E rho j = some (some C) ∧
              Block.Preceq X C ∧ fastAt p c E rho v s X) ∧
        (S_at p c E rho i v = .genesis ∨
          (∃ j < i, ∃ s, IsGateTick p c rho j v s ∧
            gateResultAt p c E rho j = some (some (S_at p c E rho i v))) ∨
          (∃ j ≤ i, S_at p c E rho i v = F_at p c E rho j v)))
    (hrows : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
      (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) {ΔF : Time} (pt : PtB₀),
      CleanCutPrem p c E rho pt ΔF →
      ∀ i j x r a e, i ≤ timeIdx rho pt.b₀ → j < i → HonestRowAt p c E rho j x r a →
        namedEntry a.payload.height_pair = some e →
        ∃ C, actionSourceFG p c E rho x r = some (some C) ∧ EntryBelow p e C ∧
          BelowLabel p c E rho i (labelBoundAt p c rho j) (eraseFG C))
    {V : Type} [DecidableEq V] [Fintype V] {In : Type}
    (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {ΔF : Time} (hset : CleanSet p c E rho ΔF) (hpos : 0 < rho.horizon) :
    (SrcFrameAboveStmt p c E rho) ∧
    (∀ x y r s B C, x ∈ rho.honest → y ∈ rho.honest →
        SA.gateTime p.toParams r ≤ rho.horizon → SA.gateTime p.toParams s ≤ rho.horizon →
        gateResult p c E rho x r = some (some B) →
        gateResult p c E rho y s = some (some C) →
        (r < s → Block.Preceq B C) ∧ (r = s → Block.Compatible B C)) ∧
    (∀ j x s, j < timeIdx rho rho.horizon → x ∈ rho.honest → IsGateTick p c rho j x s →
        ∃ B, gateResultAt p c E rho j = some (some B) ∧ (s = 0 → B = .genesis)) ∧
    (∀ x y s B H, x ∈ rho.honest → y ∈ rho.honest →
        SA.gateTime p.toParams s ≤ rho.horizon → gateResult p c E rho x s = some (some B) →
        vHead p c E rho y s = some H → Block.Preceq B H) ∧
    (∀ i v, i ≤ timeIdx rho rho.horizon → v ∈ rho.honest →
        let st := storeAt p c E rho i v
        let below := BelowLabel p c E rho i (labelBoundAt p c rho i)
        below (F_at p c E rho i v) ∧ below (J_at p c E rho i v) ∧
        below (S_at p c E rho i v) ∧
        (∀ row ∈ st.base.obligations, below row.1 ∧
          ∃ j < i, ∃ s B, IsGateTick p c rho j v s ∧ gatePassedAt p c E rho j ∧
            gateResultAt p c E rho j = some (some B) ∧ Block.Preceq row.1 B) ∧
        (∀ s C, GridCO.savedGenuine st.base s = some (some C) → below C ∧
          ∃ j < i, IsGateTick p c rho j v s ∧ gateResultAt p c E rho j = some (some C)) ∧
        (∀ j s C, j < i → IsGateTick p c rho j v s →
          gateResultAt p c E rho j = some (some C) →
          GridCO.savedGenuine st.base s = some (some C)) ∧
        (∀ s X, X ∈ (FGSA.fastWriteAt st s).getD [] → below X ∧
          ∃ j < i, IsGateTick p c rho j v s ∧ gatePassedAt p c E rho j ∧
            ∃ C, gateResultAt p c E rho j = some (some C) ∧
              Block.Preceq X C ∧ fastAt p c E rho v s X) ∧
        (S_at p c E rho i v = .genesis ∨
          (∃ j < i, ∃ s, IsGateTick p c rho j v s ∧
            gateResultAt p c E rho j = some (some (S_at p c E rho i v))) ∨
          (∃ j ≤ i, S_at p c E rho i v = F_at p c E rho j v))) ∧
    (∀ i j x r a e, i ≤ timeIdx rho rho.horizon → j < i → HonestRowAt p c E rho j x r a →
        namedEntry a.payload.height_pair = some e →
        ∃ C, actionSourceFG p c E rho x r = some (some C) ∧ EntryBelow p e C ∧
          BelowLabel p c E rho i (labelBoundAt p c rho j) (eraseFG C))
```

## B08 — P-WC

AvailableChainFGSAProofs/Proofs/WeakContinuation/FinalBelow.lean:17; first build error at :33.
Declaration: wc_finalBelow. Read the type with this module's section variables.

```lean
theorem wc_finalBelow {ΔF : Time} {w : HealingWitness} {iStar : Nat} :
    WCFinalBelowStatement p c E rho ΔF w iStar
```

## B09 — P-WC

AvailableChainFGSAProofs/Proofs/WeakContinuation/Proposal.lean:24; first build error at :41.
Declaration: wc_historyMax. Read the type with this module's section variables.

```lean
theorem wc_historyMax
    (hi : WCInv p c E rho w iStar rho.events.length) (r : Slot) :
    ∃ D, (D = w.QStar ∨ ∃ j x s,
      WCResult p c E rho w iStar rho.events.length j x s D ∧ s ≤ r) ∧
      Block.Preceq w.QStar D ∧
      ∀ j x s B, WCResult p c E rho w iStar rho.events.length j x s B →
        s ≤ r → Block.Preceq B D
```

## B10 — P-WC

AvailableChainFGSAProofs/Proofs/WeakContinuation/StepFacts.lean:44; first build error at :47.
Declaration: step_receiptOrigins. Read the type with this module's section variables.

```lean
private theorem step_receiptOrigins (i : Nat) (x : V) :
    WCReceiptOrigins p c E rho i x (storeAt p c E rho i x)
```

## B11 — P-WC

AvailableChainFGSAProofs/Proofs/WeakContinuation/StepReconcile.lean:17; first build error at :112.
Declaration: wc_reconcileBound. Read the type with this module's section variables.

```lean
theorem wc_reconcileBound (ΔF : Time) (w : HealingWitness) (iStar : Nat) :
  ∀
  (_hvalid : V2.D.ExecutionValid E rho)
  (_hlinked : V2.D.Linked (fgsaFamilies p c).linked rho)
  (_hcstar : V2.D.CStar (fgsaFamilies p c).fresh rho)
  (_hnr : V2.D.NoRestart rho)
  (_hdelta : E.Δ = p.Δ)
  (_hroots : NamedRootCollisionFree p c E rho)
  (_hsync : Gen.V2.Duty.PartialSynchronyBy E rho (fgsaDelay E.Δ ΔF))
  (_hdeltaF : E.Δ ≤ ΔF)
  (_hfault : (Gen.V2.Duty.faulty rho).card ≤ (p.n - 1) / 3)
  (_hfaultQ : Gen.Pure.FaultQ p.n (Gen.V2.Duty.faulty rho).card)
  (_hfaultX : Gen.Pure.FaultX p.n (Gen.V2.Duty.faulty rho).card)
  (_hpart : ∀ s, w.u + 1 ≤ s → SA.voteTime p.toParams s ≤ rho.horizon →
    (Gen.V2.Duty.faulty rho).card <
      (Gen.V2.Duty.awakeHonest E rho (SA.voteTime p.toParams s)).card)
  (_hstore : RStore p c E rho)
  (_hcumul : RStoreCumul p c E rho)
  (_hmono : RMono p c E rho)
  (_hactive : RActive p c E rho)
  (_hframe : RFrameExactNext p c E rho)
  (_hmeta : RFrameNext p c E rho)
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
      ∀ k w C, j < k → k < i → IsGateTick p c rho k x w →
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
      ∃ j < i, IsGateTick p c rho j x s ∧ gatePassedAt p c E rho j ∧
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
  WCSeed p c E rho w iStar → ∀ i, iStar ≤ i → i < rho.events.length →
    WCInv p c E rho w iStar i → ∀ v o t, rho.events[i]? = some (.deliver v o t) →
    ∀ x y, x ∈ rho.honest → y ∈ rho.honest →
      Block.Preceq (F_at p c E rho (i + 1) x) (S_at p c E rho i y)
```

## B12 — P-WC

AvailableChainFGSAProofs/Proofs/WeakContinuation/StepTransfer.lean:21; first build error at :93.
Declaration: wc_retrospective. Read the type with this module's section variables.

```lean
theorem wc_retrospective : WCRetrospectiveStatement p c E rho ΔF w iStar
```

## B13 — P-WC

AvailableChainFGSAProofs/Proofs/WeakContinuationGrowth/Dynamics.lean:158; first build error at :161.
Declaration: growthStepFacts_step_receiptOrigins. Read the type with this module's section variables.

```lean
private theorem growthStepFacts_step_receiptOrigins (i : Nat) (x : V) :
    WCReceiptOrigins p c E rho i x (storeAt p c E rho i x)
```

## B14 — P-WC

AvailableChainFGSAProofs/Proofs/WeakContinuationGrowth/Empty.lean:55; first build error at :85.
Declaration: wcg_empty_outputDomain. Read the type with this module's section variables.

```lean
theorem wcg_empty_outputDomain
    (ha : RetainedAgreesThrough₂ p c E source E' rho)
    (hs : V2.D.ScheduleWellFormed E source) (hr : V2.D.ScheduleWellFormed E' rho)
    (hend : rho.horizon = source.horizon)
    {w : HealingWitness} {iSource : Nat} {ΔF : Time}
    (hseed : WCSeed p c E source w iSource)
    (hgate : SA.gateTime p.toParams w.u ≤ source.horizon)
    (hsafe : SSafeFromCut₂ p c E source iSource w.QStar ΔF) :
    ∀ g ∈ [(fgsaInterface p c).stable, (fgsaInterface p c).confirmed],
      Gen.Pure.CompatOn (· ∈ rho.honest) (fun t x => V2.D.outputAt E' rho g x t)
        (fun t => afterTicksIdx rho (SA.gateTime p.toParams w.u) ≤ timeIdx rho t) ∧
      Gen.Pure.MonoOn (· ∈ rho.honest) (fun t x => V2.D.outputAt E' rho g x t)
        (fun t => afterTicksIdx rho (SA.gateTime p.toParams w.u) ≤ timeIdx rho t)
```

## B15 — P-H1

AvailableChainFGSAProofs/Tests/HealingBase.lean:32; first build error at :36.
Declaration: local fixture construction. Read the type with this module's section variables.

```lean
    (ha : HonestRowAt p c E rho j y r a) (hpre : p.actionTime r < E.t_GST)
    (hhor : E.t_GST + ΔF ≤ rho.horizon) (hx : x ∈ rho.honest) :
    HeldBefore p c E rho x a (E.t_GST + ΔF) :=
  healing_phase_receipt p c E rho ΔF hv.toScheduleWellFormed hnr
    (fgsa_tRowsReceipt p c E rho ΔF hΔ hv hnr hsync hΔF) ha hpre.le le_rfl hhor hx

-- A delivery exactly at the deadline is outside the strict receipt read.
example (hs : V2.D.ScheduleWellFormed E rho) {i : Nat} {x : V} {o : Obj p} {d : Time}
    (hi : rho.events[i]? = some (.deliver x o d)) : ¬ i < V2.D.Run.idxBefore rho d := by
  intro h
```

## B16 — P-As

AvailableChainFGSAProofs/Tests/NonVacuity/HealingPackages.lean:450; first build error at :453.
Declaration: step_constant. Read the type with this module's section variables.

```lean
theorem step_constant (nd : FixtureNode) (e : Event) :
    V2.D.World.step env (mkRun []) (fun _ => nd) e =
      fun _ => match e with
      | .restart _ _ => (fgsa params unitCodec).restore ((fgsa params unitCodec).durable nd)
      | .tick _ t => (V2.D.tick env (mkRun []) nd 0 t).1
      | .deliver _ o _ => (fgsa params unitCodec).process nd o
```

## B17 — P-As

AvailableChainFGSAProofs/Tests/NonVacuity/HealingReset.lean:199; first build error at :202.
Declaration: step_constant. Read the type with this module's section variables.

```lean
theorem step_constant (nd : FixtureNode) (e : Event) :
    V2.D.World.step env (mkRun []) (fun _ => nd) e =
      fun _ => match e with
      | .restart _ _ => (fgsa params unitCodec).restore ((fgsa params unitCodec).durable nd)
      | .tick _ t => (V2.D.tick env (mkRun []) nd 0 t).1
      | .deliver _ o _ => (fgsa params unitCodec).process nd o
```

## B18 — P-As

AvailableChainFGSAProofs/Tests/WeakContinuationGrowthNonVacuity.lean:744; first build error at :753.
Declaration: nvGen_gen_tick_nonproposal_wire. Read the type with this module's section variables.

```lean
theorem nvGen_gen_tick_nonproposal_wire (st : Node (params (count := count))) (v : (Validator (count
  := count))) (t : Time) (o : Obj (params (count := count)))
    (ho : o ∈ (V2.D.tick (weakEnv (count := count)) ((runData (count := count)) 263 []) st v t).2)
    (hn : ∀ b, o.payload ≠ .proposal b) :
    (fgsa (params (count := count)) unitCodec).wellFormed o = true
```

## Additional family contracts

These are the exact current supplier telescopes used by the continuation and growth
assembly. Their legacy NoRestart/all-honest clauses still need owner ports. FAST lacks
the restartFree interval shown in the Round 2 handoff. OU-GROWTH gives both missing
P-Ou inputs; the assembly implication is proved with these inputs explicit.

### WCFIN — P-WC

AvailableChainFGSAProofs/Proofs/WeakContinuationGrowth/Dynamics.lean:337.

```lean
theorem wcg_finiteFacts :
  ∀
  (_hvalid : V2.D.ExecutionValid E rho)
  (_hroots : NamedRootCollisionFree p c E rho)
  (_hstrat : RStrat p c E rho)
  (_hnoslash : ∀ x ∈ rho.honest, EmittedRowsNoSlash p c E rho x)
  (_hemitted : ∀ j x r a e, HonestRowAt p c E rho j x r a →
    namedEntry a.payload.height_pair = some e →
    ∃ C B, actionSourceFG p c E rho x r = some (some C) ∧
      e = (hOf p.E p.cfg C, (derive p.E p.cfg C).T_h.root) ∧
      FGBlock.Preceq (derive p.E p.cfg C).T_h C ∧
      gateResult p c E rho x (r * p.R) = some (some B) ∧
      Block.Preceq (eraseFG C) B ∧ fastAt p c E rho x (r * p.R) (eraseFG C))
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
      ∀ k w C, j < k → k < i → IsGateTick p c rho k x w →
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
      ∃ j < i, IsGateTick p c rho j x s ∧ gatePassedAt p c E rho j ∧
        ∃ B, gateResultAt p c E rho j = some (some B) ∧
          Block.Preceq X B ∧ fastAt p c E rho x s X)
  (_hdeadlines : ∀ i x,
    ∀ K g deadline, (K, g, deadline) ∈ (storeAt p c E rho i x).base.obligations →
      ∀ B, B ≠ .genesis → Block.Preceq B K →
        Gen.AC.Root.ProtectsUntil (storeAt p c E rho i x).base B g deadline),
  ∀ n, WCFiniteFacts p c E rho n
```

### WCIND — P-WC

AvailableChainFGSAProofs/Proofs/WeakContinuationGrowth/Dynamics.lean:1649.

```lean
theorem wcg_seededInduction (hcausal : WCFinalityTargetEarlierStatement p c E rho) :
  WCGSeededInductionStatement p c E rho ΔF w iStar
```

### WCEMPTY — P-WC

AvailableChainFGSAProofs/Proofs/WeakContinuationGrowth/Empty.lean:481.

```lean
theorem wcg_empty_live_of_finalBelow
    (ha : RetainedAgreesThrough₂ p c E source E' rho)
    (hb : Base₂ p c E' rho) (hs : V2.D.ScheduleWellFormed E source)
    (hns : V2.D.NoRestart source) (hend : rho.horizon = source.horizon)
    {w : HealingWitness} {iSource : Nat} {ΔF : Time}
    (hseed : WCSeed p c E source w iSource)
    (hgate : SA.gateTime p.toParams w.u ≤ source.horizon)
    (hlive : WeakContinuationLiveAt₂ p c E source w.u w.QStar iSource ΔF)
    (hfinal : ∀ i x y, afterTicksIdx rho (SA.gateTime p.toParams w.u) ≤ i →
      i ≤ rho.events.length → x ∈ rho.honest → y ∈ rho.honest →
      Block.Preceq (F_at p c E' rho i x) (S_at p c E' rho i y)) :
    WeakContinuationLiveAt₂ p c E' rho w.u w.QStar
      (afterTicksIdx rho (SA.gateTime p.toParams w.u)) ΔF
```

### WCREADS — P-WC

AvailableChainFGSAProofs/Proofs/WeakContinuation/ExactProposal.lean:39.

```lean
theorem wc_retainedReads
    (hvalid : V2.D.ExecutionValid E rho) (hnr : V2.D.NoRestart rho)
    (hdelta : E.Δ = p.Δ) (hcstar : V2.D.CStar (fgsaFamilies p c).fresh rho)
    (hroots : NamedRootCollisionFree p c E rho) (hmono : RMono p c E rho)
    (ΔF : Time) (hsync : Gen.V2.Duty.PartialSynchronyBy E rho (fgsaDelay E.Δ ΔF))
    (hpart : ∀ s, w.u + 1 ≤ s → SA.voteTime p.toParams s ≤ rho.horizon →
      (Gen.V2.Duty.faulty rho).card <
        (Gen.V2.Duty.awakeHonest E rho (SA.voteTime p.toParams s)).card)
    (hseed : WCSeed p c E rho w iStar) (pt : PtSP) (D0 : Block)
    (hstart : w.u + 2 ≤ pt.s)
    (hprop : HonestProposal E rho (fgsaInterface p c) pt.s pt.P)
    (hgate : SA.gateTime p.toParams pt.s ≤ rho.horizon)
    (hpivot : WCProposalPivot p c E rho w iStar pt D0) :
    ∃ (ip : Nat) (N : NamedProposal p.n) (D : FGBlock (Fin p.n)), N.erase = pt.P ∧
      rho.events[ip]? = some (.tick (V2.D.proposerOf rho (fgsaInterface p c) pt.s)
        (SA.proposalTime p.toParams pt.s)) ∧
      (⟨.seat (.prop pt.s) ⟨0, Nat.one_pos⟩, .proposal N⟩ : Obj p) ∈ rho.emitsAt E ip ∧
      ∀ y ∈ rho.honest, ∀ ih,
        rho.events[ih]? = some (.tick y (SA.voteTime p.toParams pt.s)) →
        ∃ Kc, RetainedReadPremises p
          (clock p (rho.stateBefore E ip
            (V2.D.proposerOf rho (fgsaInterface p c) pt.s)).st
            (SA.proposalTime p.toParams pt.s))
          (clock p (rho.stateBefore E ih y).st (SA.voteTime p.toParams pt.s))
          pt.s D N.erase Kc
```

### WCGATES — P-WC

AvailableChainFGSAProofs/Proofs/WeakContinuation/Inclusion.lean:131.

```lean
theorem wc_proposal_gates [Fintype V]
    (hvalid : V2.D.ExecutionValid E rho) (hnr : V2.D.NoRestart rho)
    (hdelta : E.Δ = p.Δ) (hcstar : V2.D.CStar (fgsaFamilies p c).fresh rho)
    (hroots : NamedRootCollisionFree p c E rho)
    (hseed : WCSeed p c E rho w iStar)
    (hi : WCInv p c E rho w iStar rho.events.length)
    (pt : PtSP) (hstart : w.u + 2 ≤ pt.s)
    (hgate : SA.gateTime p.toParams pt.s ≤ rho.horizon)
    (hhead : ∀ y ∈ rho.honest, headAtLabel p c E rho y pt.s = some pt.P)
    (had : ∀ y ∈ rho.honest, WCProposalAdmittedBeforeVote p c E rho y pt)
    (hQP : Block.Preceq w.QStar pt.P)
    (hprior : ∀ j x r B, WCResult p c E rho w iStar rho.events.length j x r B →
      r < pt.s → Block.Preceq B pt.P)
    (hfl : ∀ i x phase st WStar (Bfg : FGBlock (Fin p.n)),
      WCDutyInput p c E rho i x phase st → x ∈ rho.honest → iStar ≤ i →
      WStar ∈ st.fg.TF → eraseFG WStar = w.CStar → (heightView p WStar).h = w.M + 1 →
      Block.Preceq w.QStar (eraseFG Bfg) →
      WCUsableHighSourcesBelow p c E rho w i x st (eraseFG Bfg) →
      (∀ row ∈ st.base.obligations, st.base.now < row.2.2 →
        Block.Preceq row.1 (eraseFG Bfg)) →
      ∀ view, WCDutyView p st phase view → view ⊆ st.fg.TF →
        WCFrameLiveBelow p st phase Bfg view)
    (hSync : Gen.V2.Duty.LabelSyncOn E rho (fun o => ¬ isRowObject o)
      (SA.voteTime p.toParams pt.s) (SA.gateTime p.toParams pt.s))
    (hpart : (Gen.V2.Duty.faulty rho).card <
      (Gen.V2.Duty.awakeHonest E rho (SA.voteTime p.toParams pt.s)).card) :
    ∀ i x, x ∈ rho.honest → IsGateTick p c rho i x pt.s →
      gateResultAt p c E rho i = some (some pt.P) ∧
        Block.Preceq pt.P (S_at p c E rho (i + 1) x)
```

### FAST — P-Fd

AvailableChainFGSAProofs/Proofs/Foundations/Leases.lean:541.

```lean
theorem fgsa_leaseOrigins_fastWrites (hs : V2.D.ScheduleWellFormed E rho) (i : Nat) (x : V) :
    ∀ s X, X ∈ (FGSA.fastWriteAt (storeAt p c E rho i x) s).getD [] →
      ∃ j < i, IsGateTick p c rho j x s ∧ gatePassedAt p c E rho j ∧
        ∃ B, gateResultAt p c E rho j = some (some B) ∧
          Block.Preceq X B ∧ fastAt p c E rho x s X
```

### OU-GROWTH — P-Ou

AvailableChainFGSAProofs/Proofs/Assembly/Outage.lean:103.

```lean
theorem fgsa_cleanGrowthClaim_of_clean
    (hcut : CleanCutClaim p)
    (hWitness : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (ΔF : Time),
      CleanSet p c E rho ΔF → ∀ s B, HonestProposal E rho (fgsaInterface p c) s B →
      SA.gateTime p.toParams s ≤ rho.horizon →
      ∃ y, confirmedReader p c E rho y (SA.gateTime p.toParams s) ∧
        Block.Preceq B (S_at p c E rho (timeIdx rho (SA.gateTime p.toParams s)) y))
    (hInclusion : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (ΔF : Time),
      CleanSet p c E rho ΔF → ∀ s B, HonestProposal E rho (fgsaInterface p c) s B →
      SA.gateTime p.toParams s ≤ rho.horizon → ∀ u x g,
      SA.gateTime p.toParams s ≤ u → u ≤ rho.horizon → confirmedReader p c E rho x u →
      g ∈ [(fgsaInterface p c).stable, (fgsaInterface p c).confirmed] →
      Block.Preceq B (V2.D.outputAt E rho g x u)) : CleanGrowthClaim p
```
