module
public import AvailableChainPCSAClaims.Statements.Premises
public import AvailableChainPCSAClaims.Statements.FinalityApi

@[expose] public section

/-! [PC-SA claims, W0; pcsa-proof-plan §1 C12, C13] The Finality lane
statements over PC-SA objects: source transfer under R8′ (pcsa34-r4 5.7),
Q0-PC (5.8.3, the replacement of Q0), and the finality safety claims of the
FG-SA `FGSAFinalityClaims` shape (5.8.2: UNCHANGED, pure FG). Every statement
reads the PC-SA source (`fgSource`: the R8′ selector over the `z_{rR}`
snapshot), the PC-SA store and `pcsa_finalityView`; none reads a fast write
or a gate service, so the proofs can go through the generic FG interface.
The kernel (F1–F9) and finality liveness are not stated here: they need the
stage-2 frame (under `StageOneFrame` no block is ever finalized) and the
deferred kernel-reuse decision (plan §5). -/

namespace AvailableChain.PCSA.Run

open AvailableChain.SimplexFG

/-- [PC-SA claims, W0; pcsa34-r4 5.7 Claim (honest opening), PROVED-paper;
plan C12] At the honest opening `rR = r·R` with the formation premises
(F1)–(F7) at slot `rR` (an honest awake proposer of `N`, `h_{rR} ≥ q_N`,
`a ≤ ⌊n/4⌋`, stage 1, so `PC(rR, P_{rR})` is frame-active at `a_r`), every
honest node's source at `a_r` is `P_{rR}` (`C_fg = P_{rR}`). r4.3's "after
t* (or in a CLEAN run)" is the condition under which (F1)–(F7) hold; here they
are the premise. -/
def SourceTransferClaim (p : Params) : Prop :=
  ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (pcsa p c)) (r : Nat) (N : NamedProposal p.n)
    (ΔF : Time),
    FormationPrem p c E rho (r * p.R) N ΔF →
    ∀ x ∈ rho.honest, ∃ C : FGBlock (Fin p.n),
      actionSourceAt p c E rho x r = some (some C) ∧ eraseFG C = N.erase

theorem SourceTransferClaim_def (p : Params) : SourceTransferClaim p =
    (∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
      (E : Generic.Env V) (rho : V2.D.Run V (pcsa p c)) (r : Nat) (N : NamedProposal p.n)
      (ΔF : Time),
      FormationPrem p c E rho (r * p.R) N ΔF →
      ∀ x ∈ rho.honest, ∃ C : FGBlock (Fin p.n),
        actionSourceAt p c E rho x r = some (some C) ∧ eraseFG C = N.erase) := by
  rw [SourceTransferClaim]

/-- [PC-SA claims, W0; pcsa34-r4 5.8.3 Q0-PC; q0-pc.md §2 Statement and
steps 2–4, PROVED-paper; plan C13] Let `D` be a block with `PC(cD, D)`
stamped before `z_{cD}` at every honest node (step 1a, from L-PC1 = 5.3), and
`j = rR = r·R` an opening label with `cD ≤ j < cD + R`. Premises, as q0-pc.md
states them or as their stated role: `F ⪯ D` at every honest read through
`a_r`; `PC(cD, D)` is frame-active at every honest node at `a_r` (the
conclusion of steps 1c–1d, which q0-pc.md derives from `t*`, `ht(D) ≥ M + 1`,
the cap `H ≤ y + 1` and the FF2/transfer package); H2′: every honest HEAD of
every label in `(cD, j]` covers `D`; `a < ⌈n/2⌉`. Conclusion: at `a_r` every
honest node has a source `T ⪰ D` with `slot(T) ∈ [cD, j]`; under the cap
`H ≤ ht(D)` every honest source has the height and the entry of `D`. No
honest proposer at `j`, no gate write. -/
def Q0PCClaim (p : Params) : Prop :=
  ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (pcsa p c)) (r : Nat) (cD : Slot) (D : Block),
    Base₂ p c E rho → FaultsBelowQA p c rho →
    cD ≤ r * p.R → r * p.R < cD + p.R → p.actionTime r ≤ rho.horizon →
    (∀ y ∈ rho.honest, PCStampedBefore p c E rho y (SA.freezeTime p.toParams cD) cD D) →
    (∀ y ∈ rho.honest, ∀ t : Time, t ≤ p.actionTime r →
      Block.Preceq (eraseFG (storeAt p c E rho y t).fg.F) D) →
    (∀ y ∈ rho.honest, ∀ nd, pcsa_postClock E rho y (p.actionTime r) = some nd →
      ∃ B ∈ fullTree p nd.st, eraseFG B = D) →
    (∀ (s' : Slot) (x : V) (H : Block), cD < s' → s' ≤ r * p.R →
      HonestHeadAt p c E rho x s' H → Block.Preceq D H) →
    (∀ x ∈ rho.honest, ∃ C : FGBlock (Fin p.n),
      actionSourceAt p c E rho x r = some (some C) ∧ Block.Preceq D (eraseFG C) ∧
        cD ≤ (eraseFG C).slot ∧ (eraseFG C).slot ≤ r * p.R) ∧
    (∀ Dfg : FGBlock (Fin p.n), eraseFG Dfg = D →
      (∀ x ∈ rho.honest, ∀ nd, pcsa_postClock E rho x (p.actionTime r) = some nd →
        ∀ B ∈ nd.st.fg.TF, (FGSA.heightView p B).h ≤ (FGSA.heightView p Dfg).h) →
      ∀ x ∈ rho.honest, ∃ C : FGBlock (Fin p.n),
        actionSourceAt p c E rho x r = some (some C) ∧
          (FGSA.heightView p C).h = (FGSA.heightView p Dfg).h ∧
          (FGSA.heightView p C).T_h = (FGSA.heightView p Dfg).T_h)

theorem Q0PCClaim_def (p : Params) : Q0PCClaim p =
    (∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
      (E : Generic.Env V) (rho : V2.D.Run V (pcsa p c)) (r : Nat) (cD : Slot) (D : Block),
      Base₂ p c E rho → FaultsBelowQA p c rho →
      cD ≤ r * p.R → r * p.R < cD + p.R → p.actionTime r ≤ rho.horizon →
      (∀ y ∈ rho.honest, PCStampedBefore p c E rho y (SA.freezeTime p.toParams cD) cD D) →
      (∀ y ∈ rho.honest, ∀ t : Time, t ≤ p.actionTime r →
        Block.Preceq (eraseFG (storeAt p c E rho y t).fg.F) D) →
      (∀ y ∈ rho.honest, ∀ nd, pcsa_postClock E rho y (p.actionTime r) = some nd →
        ∃ B ∈ fullTree p nd.st, eraseFG B = D) →
      (∀ (s' : Slot) (x : V) (H : Block), cD < s' → s' ≤ r * p.R →
        HonestHeadAt p c E rho x s' H → Block.Preceq D H) →
      (∀ x ∈ rho.honest, ∃ C : FGBlock (Fin p.n),
        actionSourceAt p c E rho x r = some (some C) ∧ Block.Preceq D (eraseFG C) ∧
          cD ≤ (eraseFG C).slot ∧ (eraseFG C).slot ≤ r * p.R) ∧
      (∀ Dfg : FGBlock (Fin p.n), eraseFG Dfg = D →
        (∀ x ∈ rho.honest, ∀ nd, pcsa_postClock E rho x (p.actionTime r) = some nd →
          ∀ B ∈ nd.st.fg.TF, (FGSA.heightView p B).h ≤ (FGSA.heightView p Dfg).h) →
        ∀ x ∈ rho.honest, ∃ C : FGBlock (Fin p.n),
          actionSourceAt p c E rho x r = some (some C) ∧
            (FGSA.heightView p C).h = (FGSA.heightView p Dfg).h ∧
            (FGSA.heightView p C).T_h = (FGSA.heightView p Dfg).T_h)) := by
  rw [Q0PCClaim]

/-! ### Finality safety (FGSAFinalityClaims shape; pcsa34-r4 5.8.2 UNCHANGED) -/

/-- [PC-SA claims, W0; FG-SA PureAccountableClaim; DC certificatesAccountable]
Two window certificates finalize compatible blocks, or slashable weight lies
between their chains. Pure FG; scoped root injectivity. -/
def PCSAPureAccountableClaim (p : Params) : Prop :=
  ∀ (K W T₁ T₂ : FGBlock (Fin p.n)) (h₁ h₂ : Nat),
    KitFG.RootInjectiveOn K W →
    PCFinalizedAt p K T₁ h₁ → PCFinalizedAt p W T₂ h₂ →
    HasSlashableWeightBetween p.E (chainRows K) (chainRows W) ∨
      FGBlock.compatible T₁ T₂ = true

theorem PCSAPureAccountableClaim_def (p : Params) : PCSAPureAccountableClaim p =
    (∀ (K W T₁ T₂ : FGBlock (Fin p.n)) (h₁ h₂ : Nat),
      KitFG.RootInjectiveOn K W →
      PCFinalizedAt p K T₁ h₁ → PCFinalizedAt p W T₂ h₂ →
      HasSlashableWeightBetween p.E (chainRows K) (chainRows W) ∨
        FGBlock.compatible T₁ T₂ = true) := by
  rw [PCSAPureAccountableClaim]

/-- [PC-SA claims, W0; FG-SA PureAgreementClaim] Without slashable weight
between the chains, two window certificates finalize compatible blocks. -/
def PCSAPureAgreementClaim (p : Params) : Prop :=
  ∀ (K W T₁ T₂ : FGBlock (Fin p.n)) (h₁ h₂ : Nat),
    KitFG.RootInjectiveOn K W →
    PCFinalizedAt p K T₁ h₁ → PCFinalizedAt p W T₂ h₂ →
    ¬ HasSlashableWeightBetween p.E (chainRows K) (chainRows W) →
      FGBlock.compatible T₁ T₂ = true

theorem PCSAPureAgreementClaim_def (p : Params) : PCSAPureAgreementClaim p =
    (∀ (K W T₁ T₂ : FGBlock (Fin p.n)) (h₁ h₂ : Nat),
      KitFG.RootInjectiveOn K W →
      PCFinalizedAt p K T₁ h₁ → PCFinalizedAt p W T₂ h₂ →
      ¬ HasSlashableWeightBetween p.E (chainRows K) (chainRows W) →
        FGBlock.compatible T₁ T₂ = true) := by
  rw [PCSAPureAgreementClaim]

/-- [PC-SA claims, W0; FG-SA WholeRunAccountableClaim; DC finalizedAccountable]
Whole-run accountability over a PC-SA run with root collision freedom and
sorted events. -/
def PCSAWholeRunAccountableClaim (p : Params) : Prop :=
  ∀ {V : Type} [DecidableEq V] {In : Type} (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (pcsa p c)),
    NamedRootCollisionFree p c E rho → PCFinalityExecution p c rho →
    PCWholeRunAccountable p c E rho

theorem PCSAWholeRunAccountableClaim_def (p : Params) : PCSAWholeRunAccountableClaim p =
    (∀ {V : Type} [DecidableEq V] {In : Type} (c : AppCodec In)
      (E : Generic.Env V) (rho : V2.D.Run V (pcsa p c)),
      NamedRootCollisionFree p c E rho → PCFinalityExecution p c rho →
      PCWholeRunAccountable p c E rho) := by
  rw [PCSAWholeRunAccountableClaim]

/-- [PC-SA claims, W0; FG-SA WholeRunAgreementClaim; DC finalizedSafe]
Whole-run agreement under the slashable bound. -/
def PCSAWholeRunAgreementClaim (p : Params) : Prop :=
  ∀ {V : Type} [DecidableEq V] {In : Type} (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (pcsa p c)),
    NamedRootCollisionFree p c E rho → PCFinalityExecution p c rho →
    PCFinalitySlashableBound p c E rho → PCWholeRunAgreement p c E rho

theorem PCSAWholeRunAgreementClaim_def (p : Params) : PCSAWholeRunAgreementClaim p =
    (∀ {V : Type} [DecidableEq V] {In : Type} (c : AppCodec In)
      (E : Generic.Env V) (rho : V2.D.Run V (pcsa p c)),
      NamedRootCollisionFree p c E rho → PCFinalityExecution p c rho →
      PCFinalitySlashableBound p c E rho → PCWholeRunAgreement p c E rho) := by
  rw [PCSAWholeRunAgreementClaim]

/-- [PC-SA claims, W0; FG-SA EventPrefixAgreementClaim] Under the slashable
bound, the finalized blocks of any two honest event states are compatible. -/
def PCSAEventPrefixAgreementClaim (p : Params) : Prop :=
  ∀ {V : Type} [DecidableEq V] {In : Type} (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (pcsa p c)),
    NamedRootCollisionFree p c E rho → PCFinalityExecution p c rho →
    PCFinalitySlashableBound p c E rho →
    ∀ x ∈ rho.honest, ∀ y ∈ rho.honest, ∀ i j : Nat,
      FGBlock.compatible (storeBefore p c E rho i x).fg.F (storeBefore p c E rho j y).fg.F = true

theorem PCSAEventPrefixAgreementClaim_def (p : Params) : PCSAEventPrefixAgreementClaim p =
    (∀ {V : Type} [DecidableEq V] {In : Type} (c : AppCodec In)
      (E : Generic.Env V) (rho : V2.D.Run V (pcsa p c)),
      NamedRootCollisionFree p c E rho → PCFinalityExecution p c rho →
      PCFinalitySlashableBound p c E rho →
      ∀ x ∈ rho.honest, ∀ y ∈ rho.honest, ∀ i j : Nat,
        FGBlock.compatible (storeBefore p c E rho i x).fg.F
          (storeBefore p c E rho j y).fg.F = true) := by
  rw [PCSAEventPrefixAgreementClaim]

/-- [PC-SA claims, W0; FG-SA FinalizedMonotonicityClaim; DC finalizedMonotone]
The finalized output of an honest node is monotone in time. A restart resets
`F`, so `NoRestart` is a premise. No fault bound. -/
def PCSAFinalizedMonotoneClaim (p : Params) : Prop :=
  ∀ {V : Type} [DecidableEq V] {In : Type} (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (pcsa p c)),
    PCFinalityExecution p c rho → V2.D.NoRestart rho →
    ∀ x ∈ rho.honest, ∀ t t' : Time, t ≤ t' →
      Block.Preceq (pcsaFinalizedOut (V2.D.Run.readAt E rho t x))
        (pcsaFinalizedOut (V2.D.Run.readAt E rho t' x))

theorem PCSAFinalizedMonotoneClaim_def (p : Params) : PCSAFinalizedMonotoneClaim p =
    (∀ {V : Type} [DecidableEq V] {In : Type} (c : AppCodec In)
      (E : Generic.Env V) (rho : V2.D.Run V (pcsa p c)),
      PCFinalityExecution p c rho → V2.D.NoRestart rho →
      ∀ x ∈ rho.honest, ∀ t t' : Time, t ≤ t' →
        Block.Preceq (pcsaFinalizedOut (V2.D.Run.readAt E rho t x))
          (pcsaFinalizedOut (V2.D.Run.readAt E rho t' x))) := by
  rw [PCSAFinalizedMonotoneClaim]

/-- [PC-SA claims, W0; FG-SA FGSAFinalityClaims] The finality safety claims
of PC-SA. Not stated in W0: the fault-count slashable bound and
honest-never-slashed (they need the PC-SA row-emission and slashing reads). -/
structure PCSAFinalitySafetyClaims (p : Params) : Prop where
  accountable : PCSAPureAccountableClaim p
  agreement : PCSAPureAgreementClaim p
  runAccountable : PCSAWholeRunAccountableClaim p
  runAgreement : PCSAWholeRunAgreementClaim p
  eventPrefixAgreement : PCSAEventPrefixAgreementClaim p
  finalizedMonotone : PCSAFinalizedMonotoneClaim p

end AvailableChain.PCSA.Run

end
