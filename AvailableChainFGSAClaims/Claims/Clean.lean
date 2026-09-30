module
public import AvailableChainFGSAClaims.Statements.Packages.Safety
public import AvailableChainFGSAClaims.Statements.Channels
public import AvailableChainGeneric.Statements.Pure.Props

@[expose] public section

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG
open Gen.Pure (CompatOn MonoOn)

variable (p : Params) {In V : Type} [DecidableEq V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.Run V (fgsa p c))

/-- bp.cleanHistory.v1, P3 §4.7 and 00:767–775. The clauses use public
event reads and BelowLabel; no F2 invariant occurs in this statement.
Nonempty and continuation refer to actual ticks, including at the cut. -/
def CleanHistoryAt (b₀ : Time) : Prop :=
  (∀ x y r s B C, x ∈ rho.honest → y ∈ rho.honest →
    SA.gateTime p.toParams r ≤ b₀ → SA.gateTime p.toParams s ≤ b₀ →
    gateResult p c E rho x r = some (some B) →
    gateResult p c E rho y s = some (some C) →
    (r < s → Block.Preceq B C) ∧ (r = s → Block.Compatible B C)) ∧
  (∀ j x s, j < timeIdx rho b₀ → x ∈ rho.honest → IsGateTick p c rho j x s →
    ∃ B, gateResultAt p c E rho j = some (some B) ∧ (s = 0 → B = .genesis)) ∧
  (∀ x y s B H, x ∈ rho.honest → y ∈ rho.honest →
    SA.gateTime p.toParams s ≤ b₀ → gateResult p c E rho x s = some (some B) →
    vHead p c E rho y s = some H → Block.Preceq B H) ∧
  (∀ i v, i ≤ timeIdx rho b₀ → v ∈ rho.honest →
    let st := storeAt p c E rho i v
    let below := BelowLabel p c E rho i (labelBoundAt p c rho i)
    below (F_at p c E rho i v) ∧ below (J_at p c E rho i v) ∧ below (S_at p c E rho i v) ∧
    (∀ row ∈ st.base.obligations, below row.1 ∧
      ∃ j < i, ∃ s B, IsGateTick p c rho j v s ∧ gatePassedAt p c E rho j ∧
        gateResultAt p c E rho j = some (some B) ∧ Block.Preceq row.1 B) ∧
    (∀ s C, GridCO.savedGenuine st.base s = some (some C) → below C ∧
      ∃ j < i, IsGateTick p c rho j v s ∧ gateResultAt p c E rho j = some (some C)) ∧
    (∀ j s C, j < i → IsGateTick p c rho j v s →
      gateResultAt p c E rho j = some (some C) → GridCO.savedGenuine st.base s = some (some C)) ∧
    (∀ s X, X ∈ (FGSA.fastWriteAt st s).getD [] → below X ∧
      ∃ j < i, IsGateTick p c rho j v s ∧ gatePassedAt p c E rho j ∧
        ∃ C, gateResultAt p c E rho j = some (some C) ∧ Block.Preceq X C ∧ fastAt p c E rho v s X) ∧
    (S_at p c E rho i v = .genesis ∨
      (∃ j < i, ∃ s, IsGateTick p c rho j v s ∧
        gateResultAt p c E rho j = some (some (S_at p c E rho i v))) ∨
      (∃ j ≤ i, S_at p c E rho i v = F_at p c E rho j v))) ∧
  (∀ i j x r C, i ≤ timeIdx rho b₀ → j < i → x ∈ rho.honest →
    rho.events[j]? = some (.tick x (p.actionTime r)) →
    actionSource p c E rho x r = some (some C) →
    BelowLabel p c E rho i (labelBoundAt p c rho j) C) ∧
  (∀ i j x r a e, i ≤ timeIdx rho b₀ → j < i → HonestRowAt p c E rho j x r a →
    namedEntry a.payload.height_pair = some e →
    ∃ C, actionSourceFG p c E rho x r = some (some C) ∧ EntryBelow p e C ∧
      BelowLabel p c E rho i (labelBoundAt p c rho j) (eraseFG C)) ∧
  (∀ i v, i < timeIdx rho b₀ → v ∈ rho.honest → FAdvanceAt p c E rho i v →
    let st := storeAt p c E rho i v
    let st' := storeAt p c E rho (i + 1) v
    st'.base.obligations = st.base.obligations ∧
    st'.base.genuine = st.base.genuine ∧ st'.fastWrite = st.fastWrite)

/-- bp.cleanPrefixTruncation.v1 (00:795–802). All event states at the
inclusive cut and all public reads in [0,b₀] have the Clean properties. -/
def CleanTruncAt (b₀ : Time) : Prop :=
  CompatOn (· ∈ rho.honest) (S_at p c E rho) (· ≤ timeIdx rho b₀) ∧
  MonoOn (· ∈ rho.honest) (S_at p c E rho) (· ≤ timeIdx rho b₀) ∧
  (∀ g ∈ [(fgsaInterface p c).stable, (fgsaInterface p c).confirmed],
    CompatOn (· ∈ rho.honest) (fun t x => V2.outputAt E rho g x t) (fun t => 0 ≤ t ∧ t ≤ b₀) ∧
    MonoOn (· ∈ rho.honest) (fun t x => V2.outputAt E rho g x t) (fun t => 0 ≤ t ∧ t ≤ b₀)) ∧
  CleanHistoryAt p c E rho b₀ ∧
  (∀ i v, i ≤ timeIdx rho b₀ → v ∈ rho.honest →
    let st := storeAt p c E rho i v
    (FGSA.controls p st).contest = false ∧
    BelowLabel p c E rho i (labelBoundAt p c rho i) (eraseFG (FGSA.controls p st).Z) ∧
    (∀ B ∈ st.fg.TF,
      BelowLabel p c E rho i (labelBoundAt p c rho i) (eraseFG B) →
      Block.Preceq (eraseFG B) (eraseFG (FGSA.controls p st).Z) ∨
      Block.Preceq (eraseFG B) (eraseFG st.fg.F) ∨
      (FGBlock.Preceq st.fg.F (FGSA.controls p st).Z ∧
        FGBlock.Preceq (FGSA.controls p st).Z B ∧ B ∈ FGSA.fullTree p st)))

/-- FS20 named conclusion of bp.cleanSafety.v1, using the Gen property kernel. -/
def CleanSafetyAt : Prop :=
  CompatOn (· ∈ rho.honest) (S_at p c E rho) (· ≤ rho.events.length) ∧
  MonoOn (· ∈ rho.honest) (S_at p c E rho) (· ≤ rho.events.length) ∧
  (∀ g ∈ [(fgsaInterface p c).stable, (fgsaInterface p c).confirmed],
    CompatOn (· ∈ rho.honest) (fun t x => V2.outputAt E rho g x t) (fun _ => True) ∧
    MonoOn (· ∈ rho.honest) (fun t x => V2.outputAt E rho g x t) (fun _ => True))

/-- Blueprint cut form. Assembly of its two lanes is deferred. -/
def CleanCutClaim : Prop :=
  ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.Run V (fgsa p c)) (pt : PtB₀),
    CleanCutPrem p c E rho pt → CleanHistoryAt p c E rho pt.b₀ ∧ CleanTruncAt p c E rho pt.b₀

/-- F2 zero lane. There is no channel or quorum premise. -/
def CleanCutZeroClaim : Prop :=
  ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.Run V (fgsa p c)),
    CleanCutPrem p c E rho ⟨0⟩ → CleanHistoryAt p c E rho 0 ∧ CleanTruncAt p c E rho 0

def CleanHistoryClaim : Prop :=
  ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.Run V (fgsa p c)) (pt : PtB₀),
    CleanPrefixPrem p c E rho pt → CleanHistoryAt p c E rho pt.b₀

def CleanPrefixTruncationClaim : Prop :=
  ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.Run V (fgsa p c)) (pt : PtB₀),
    CleanPrefixPrem p c E rho pt → CleanTruncAt p c E rho pt.b₀

def CleanSafetyClaim : Prop :=
  ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.Run V (fgsa p c)) (pt : Unit),
    CleanPrem p c E rho pt → CleanSafetyAt p c E rho

end AvailableChain.FGSA.Run
end
