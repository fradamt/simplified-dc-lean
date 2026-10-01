module
public import AvailableChainFGSAClaims.Statements.Channels
public import AvailableChainGeneric.Statements.Pure.Props
public import AvailableChainKitV2.Execution

public section

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG
open Gen.Pure (CompatOn MonoOn)

variable (p : Params) {In V : Type} [DecidableEq V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.Run V (fgsa p c))

/-- P3 §8.5 (cleanSafety), bp02 §6: transport the supplied truncation to
all public reads. DC Generic/Properties:27,41,48 and Generic/Interface:64
have the same compatibility and monotonicity meaning. The representation
and all-integer domain differ intentionally: finite prefix reads always
have an index at most the event count, even outside the run horizon.
Three-class rule: INTENTIONAL, for this finite-read reason (S3 D43/D61);
no UNMOTIVATED or UNCLEAR premise difference. No restart, quorum, channel,
or extra honesty premise is needed by this read transport. -/
theorem cleanSafety_of_trunc_body
    (hs : V2.ScheduleWellFormed E rho)
    (ht :
  CompatOn (· ∈ rho.honest) (S_at p c E rho) (· ≤ timeIdx rho rho.horizon) ∧
  MonoOn (· ∈ rho.honest) (S_at p c E rho) (· ≤ timeIdx rho rho.horizon) ∧
  (∀ g ∈ [(fgsaInterface p c).stable, (fgsaInterface p c).confirmed],
    CompatOn (· ∈ rho.honest) (fun t x => V2.outputAt E rho g x t)
      (fun t => 0 ≤ t ∧ t ≤ rho.horizon) ∧
    MonoOn (· ∈ rho.honest) (fun t x => V2.outputAt E rho g x t)
      (fun t => 0 ≤ t ∧ t ≤ rho.horizon)) ∧
  ((∀ x y r s B C, x ∈ rho.honest → y ∈ rho.honest →
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
  (∀ i j x r C, i ≤ timeIdx rho rho.horizon → j < i → x ∈ rho.honest →
    rho.events[j]? = some (.tick x (p.actionTime r)) →
    actionSource p c E rho x r = some (some C) →
    BelowLabel p c E rho i (labelBoundAt p c rho j) C) ∧
  (∀ i j x r a e, i ≤ timeIdx rho rho.horizon → j < i → HonestRowAt p c E rho j x r a →
    namedEntry a.payload.height_pair = some e →
    ∃ C, actionSourceFG p c E rho x r = some (some C) ∧ EntryBelow p e C ∧
      BelowLabel p c E rho i (labelBoundAt p c rho j) (eraseFG C)) ∧
  (∀ i v, i < timeIdx rho rho.horizon → v ∈ rho.honest → FAdvanceAt p c E rho i v →
    let st := storeAt p c E rho i v
    let st' := storeAt p c E rho (i + 1) v
    st'.base.obligations = st.base.obligations ∧
    st'.base.genuine = st.base.genuine ∧ st'.fastWrite = st.fastWrite)) ∧
  (∀ i v, i ≤ timeIdx rho rho.horizon → v ∈ rho.honest →
    let st := storeAt p c E rho i v
    (FGSA.controls p st).contest = false ∧
    BelowLabel p c E rho i (labelBoundAt p c rho i) (eraseFG (FGSA.controls p st).Z) ∧
    (∀ B ∈ st.fg.TF,
      BelowLabel p c E rho i (labelBoundAt p c rho i) (eraseFG B) →
      Block.Preceq (eraseFG B) (eraseFG (FGSA.controls p st).Z) ∨
      Block.Preceq (eraseFG B) (eraseFG st.fg.F) ∨
      (FGBlock.Preceq st.fg.F (FGSA.controls p st).Z ∧
        FGBlock.Preceq (FGSA.controls p st).Z B ∧ B ∈ FGSA.fullTree p st))) ∧
  (∀ l x, SA.gateTime p.toParams l ≤ rho.horizon → x ∈ rho.honest →
    ∃ B, gateResult p c E rho x l = some (some B) ∧
      (∃ j, IsGateTick p c rho j x l ∧ gatePassedAt p c E rho j) ∧
      Block.Preceq B (S_at p c E rho (afterTicksIdx rho (SA.gateTime p.toParams l)) x) ∧
      ∀ l' < l, ∀ B', gateResult p c E rho x l' = some (some B') → Block.Preceq B' B)) :
  CompatOn (· ∈ rho.honest) (S_at p c E rho) (· ≤ rho.events.length) ∧
  MonoOn (· ∈ rho.honest) (S_at p c E rho) (· ≤ rho.events.length) ∧
  (∀ g ∈ [(fgsaInterface p c).stable, (fgsaInterface p c).confirmed],
    CompatOn (· ∈ rho.honest) (fun t x => V2.outputAt E rho g x t) (fun _ => True) ∧
    MonoOn (· ∈ rho.honest) (fun t x => V2.outputAt E rho g x t) (fun _ => True)) := by
  have hlast : timeIdx rho rho.horizon = rho.events.length := by
    change (rho.events.filter _).length = _
    congr 1
    apply List.filter_eq_self.mpr
    intro e he
    exact decide_eq_true (hs.in_horizon e he).2
  have hbound (t : Time) : timeIdx rho t ≤ rho.events.length :=
    List.length_filter_le _ _
  have hread (g) (hg : g ∈ [(fgsaInterface p c).stable,
      (fgsaInterface p c).confirmed]) (t : Time) (x : V) :
      V2.outputAt E rho g x t = S_at p c E rho (timeIdx rho t) x := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl <;>
      change (V2.Run.readAt E rho t x).st.base.stableRecord = _ <;>
      rw [V2.Engine.readAt_eq_stateBefore hs t] <;> rfl
  have hc := ht.1
  have hm := ht.2.1
  rw [hlast] at hc hm
  refine ⟨hc, hm, ?_⟩
  intro g hg
  constructor
  · intro t u x y _ _ hx hy
    change Block.Compatible (V2.outputAt E rho g x t) (V2.outputAt E rho g y u)
    rw [hread g hg t x, hread g hg u y]
    exact hc _ _ _ _ (hbound t) (hbound u) hx hy
  · intro t u x _ _ htu hx
    change Block.Preceq (V2.outputAt E rho g x t) (V2.outputAt E rho g x u)
    rw [hread g hg t x, hread g hg u x]
    exact hm _ _ _ (hbound t) (hbound u)
      (V2.Engine.read_length_mono t u htu) hx

end AvailableChain.FGSA.Run
end
