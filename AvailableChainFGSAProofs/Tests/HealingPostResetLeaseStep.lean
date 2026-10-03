module
public import AvailableChainFGSAProofs.Proofs.Healing.PostResetLeaseStep -- shake: keep (J4-A fixtures)

set_option linter.privateModule false

/-! Blueprint 21 H.15:2894–2914; plan J4-A; B1/B13/B17/B18.
Conditional package: an actual passed write on a prefix with no emitted
source. The domain remains an explicit input; this is an A1 consumer.
No successor producer or concrete H0Reset run is claimed. -/

section
namespace AvailableChain.FGSA.Run.Tests.HealingPostResetLeaseStep
open AvailableChain.SimplexFG

variable (p : Params) {In V : Type} [DecidableEq V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

-- conditional package, anti-vacuity: A1 covers an actual written prefix
-- that has no emitted source. Its synchrony comes from the reset cut.
example [Fintype V] {G ΔF : Time}
    (hrec : Recovery₂ p c E rho G ΔF) (mono : RMono p c E rho)
    (writes : ∀ i x (row : Block × Nat × Time),
      row ∈ (storeAt p c E rho i x).base.obligations →
      ∃ j < i, ∃ s B, IsGateTick p c rho j x s ∧ gatePassedAt p c E rho j ∧
        gateResultAt p c E rho j = some (some B) ∧ Block.Preceq row.1 B ∧
        (row.1, row.2.1) ∈ @GridCO.gateWriteKeys GridCO.slowLeasePolicy p.toParams.engine p.n
          (actView (clockPre p (storeAt p c E rho j x) (SA.gateTime p.toParams s))) s B ∧
        row.2.2 = SA.gateTime p.toParams s + SA.lifetime p.toParams ∧
        row.2.2 = SA.releaseTime p.toParams (s + p.k) ∧
        ∀ k w C, j < k → k < i → IsGateTick p c rho k x w →
          let pre := clockPre p (storeAt p c E rho k x) (SA.gateTime p.toParams w)
          GridCO.savedGenuine pre.base w = none →
          SA.confirmationFrom p.toParams (eraseFG pre.fg.F) (actView pre) w = some C →
          (actView pre).obligations.any (fun r => !Block.compatible r.1 C) = false →
          (row.1, row.2.1) ∉ @GridCO.gateWriteKeys GridCO.slowLeasePolicy p.toParams.engine p.n
            (actView pre) w C)
    {w : HealingWitness} (h0r : H0Reset p c E rho w)
    {ix : Nat} {x : V} {s : Slot} {C : Block} {g : Nat}
    (hx : x ∈ rho.honest) (hix : IsGateTick p c rho ix x s)
    (hpass : gatePassedAt p c E rho ix)
    (hres : gateResultAt p c E rho ix = some (some C))
    {B : FGBlock (Fin p.n)} (hCB : Block.Preceq w.CStar (eraseFG B))
    (hne : eraseFG B ≠ w.CStar)
    (hkey : (eraseFG B, g) ∈ @GridCO.gateWriteKeys GridCO.slowLeasePolicy
      p.toParams.engine p.n
      (actView (clockPre p (storeAt p c E rho ix x) (SA.gateTime p.toParams s))) s C)
    (hgw : E.t_GST ≤ SA.voteTime p.toParams (s + 1 - p.k))
    (hnotSource : ¬ ∃ r, SrcN p c E rho B r)
    {iy : Nat} {y : V} (hy : y ∈ rho.honest)
    (hiy : rho.events[iy]? = some (.tick y (SA.voteTime p.toParams (s + 1))))
    {X : Finset (FGBlock (Fin p.n))}
    (hXv : X ⊆ voterBlocks p (FGSA.clock p (storeAt p c E rho iy y)
      (SA.voteTime p.toParams (s + 1))) (s + 1))
    (hXc : ∀ W ∈ X, ∀ A, FGBlock.Preceq A W → A ∈ X)
    (hD : B ∈ D_at p c E rho iy y X) :
    Block.Preceq (eraseFG B) (headAtIdx p c E rho iy (s + 1)) ∧
      gatePassedAt p c E rho ix ∧ eraseFG B ≠ w.CStar ∧ ¬ ∃ r, SrcN p c E rho B r := by
  obtain ⟨hmem, _, hBC, _, hcase⟩ := healing_support_key_cases p hkey
  have hgst := postReset_written_sync p c E rho hrec h0r hx hix hCB hmem
  have harm : SA.releaseThreshold p.toParams ≤ SA.prefixSupport p.toParams
        (actView (clockPre p (storeAt p c E rho ix x) (SA.gateTime p.toParams s))) s
        (eraseFG B) ∨
      (E.t_GST ≤ SA.voteTime p.toParams (s + 1 - p.k) ∧
        GridCO.slowEligible p.toParams.engine
          (actView (clockPre p (storeAt p c E rho ix x) (SA.gateTime p.toParams s))) s
          (eraseFG B) = true) := hcase.imp_right (fun hel => ⟨hgw, hel⟩)
  exact ⟨healing_first_transfer_written p c E rho hrec mono writes hx hix hres hBC
    hgst.le harm hy hiy hXv hXc hD, hpass, hne, hnotSource⟩

-- conditional package: the causal cut gives strict label synchrony even
-- without a gate result or an emitted action source for the prefix.
example [Fintype V] {G ΔF : Time} (hrec : Recovery₂ p c E rho G ΔF)
    {w : HealingWitness} (h0r : H0Reset p c E rho w)
    {i : Nat} {y : V} {s : Slot} {B : Block}
    (hy : y ∈ rho.honest) (ht : IsGateTick p c rho i y s)
    (hCB : Block.Preceq w.CStar B)
    (hB : B ∈ (actView (clockPre p (storeAt p c E rho i y)
      (SA.gateTime p.toParams s))).blocks) : E.t_GST < SA.voteTime p.toParams s :=
  postReset_written_sync p c E rho hrec h0r hy ht hCB hB


section WrittenConsumers
variable [Fintype V] {G ΔF : Time}
    (hrec : Recovery₂ p c E rho G ΔF) (mono : RMono p c E rho)
    (emittedNonempty : ∀ {j : Nat} {x : V} {r : Nat} {a : RowWire p.n},
      HonestRowAt p c E rho j x r a → ∃ e, namedEntry a.payload.height_pair = some e)
    (emittedName : ∀ {j : Nat} {x : V} {r : Nat} {a : RowWire p.n} {e : Height × BlockId},
      HonestRowAt p c E rho j x r a → namedEntry a.payload.height_pair = some e →
      ∃ C G, actionSourceFG p c E rho x r = some (some C) ∧
        e.1 = (heightView p C).h ∧
        gateResult p c E rho x (r * p.R) = some (some G) ∧
        Block.Preceq (eraseFG C) G ∧ fastAt p c E rho x (r * p.R) (eraseFG C))
    (writes : ∀ i x (row : Block × Nat × Time),
      row ∈ (storeAt p c E rho i x).base.obligations →
      ∃ j < i, ∃ s B, IsGateTick p c rho j x s ∧ gatePassedAt p c E rho j ∧
        gateResultAt p c E rho j = some (some B) ∧ Block.Preceq row.1 B ∧
        (row.1, row.2.1) ∈ @GridCO.gateWriteKeys GridCO.slowLeasePolicy p.toParams.engine p.n
          (actView (clockPre p (storeAt p c E rho j x) (SA.gateTime p.toParams s))) s B ∧
        row.2.2 = SA.gateTime p.toParams s + SA.lifetime p.toParams ∧
        row.2.2 = SA.releaseTime p.toParams (s + p.k) ∧
        ∀ k w C, j < k → k < i → IsGateTick p c rho k x w →
          let pre := clockPre p (storeAt p c E rho k x) (SA.gateTime p.toParams w)
          GridCO.savedGenuine pre.base w = none →
          SA.confirmationFrom p.toParams (eraseFG pre.fg.F) (actView pre) w = some C →
          (actView pre).obligations.any (fun r => !Block.compatible r.1 C) = false →
          (row.1, row.2.1) ∉ @GridCO.gateWriteKeys GridCO.slowLeasePolicy p.toParams.engine p.n
            (actView pre) w C)
    (xing : RXing p c E rho) (origin : RQCOrigin p c E rho)
    {w : HealingWitness} (h0r : H0Reset p c E rho w)
    (gateResultSupporter : ∀ {G ΔF : Time}, Recovery₂ p c E rho G ΔF →
      ∀ {s : Slot}, E.t_GST ≤ SA.voteTime p.toParams s →
      ∀ {ix : Nat} {x : V} {C : Block}, x ∈ rho.honest →
      IsGateTick p c rho ix x s → gateResultAt p c E rho ix = some (some C) →
      ∃ k z, z ∈ rho.honest ∧
        rho.events[k]? = some (.tick z (SA.voteTime p.toParams s)) ∧
        Block.Preceq C (headAtIdx p c E rho k s) ∧ k < ix)

include hrec mono emittedNonempty emittedName writes xing origin h0r gateResultSupporter


-- conditional package, anti-vacuity: A2 supplies a frozen domain witness
-- for an actual written prefix that is not an emitted action source.
example {i : Nat} (hinv : PostResetInv p c E rho w i)
    {ix : Nat} {x : V} {s : Slot} {C : Block} {B : FGBlock (Fin p.n)} {g : Nat}
    (hx : x ∈ rho.honest) (hix : IsGateTick p c rho ix x s)
    (hpass : gatePassedAt p c E rho ix)
    (hres : gateResultAt p c E rho ix = some (some C))
    (hCB : Block.Preceq w.CStar (eraseFG B)) (hne : eraseFG B ≠ w.CStar)
    (hkey : (eraseFG B, g) ∈ @GridCO.gateWriteKeys GridCO.slowLeasePolicy
      p.toParams.engine p.n
      (actView (clockPre p (storeAt p c E rho ix x) (SA.gateTime p.toParams s))) s C)
    (hnotSource : ¬ ∃ r, SrcN p c E rho B r)
    {iy : Nat} {y : V} (hy : y ∈ rho.honest)
    (hiy : rho.events[iy]? = some (.tick y (SA.voteTime p.toParams (s + 1))))
    (hyi : iy ≤ i)
    (hnZ : ¬ FGBlock.Preceq B (R_at p c E rho iy y).Z)
    (hnF : ¬ FGBlock.Preceq B (storeAt p c E rho iy y).fg.F) :
    B ∈ D_at p c E rho iy y
      (storeAt p c E rho (V2.D.Run.idxBefore rho (SA.freezeTime p.toParams s)) y).fg.TF ∧
      gatePassedAt p c E rho ix ∧ eraseFG B ≠ w.CStar ∧ ¬ ∃ r, SrcN p c E rho B r := by
  obtain ⟨hmem, -, hBC, -, -⟩ := healing_support_key_cases p hkey
  exact ⟨postReset_written_domain p c E rho hrec mono emittedNonempty emittedName writes
    xing origin h0r gateResultSupporter hinv hx hix hres hCB hmem hBC hy hiy hyi hnZ hnF,
    hpass, hne, hnotSource⟩

variable (slowWindowSync : ∀ {G ΔF : Time}, Recovery₂ p c E rho G ΔF →
  ∀ {w : HealingWitness}, H0Reset p c E rho w →
  ∀ {i : Nat} {x : V} {s : Slot} {C : Block} {B : FGBlock (Fin p.n)},
  x ∈ rho.honest →
  GridCO.savedGenuine (storeAt p c E rho i x).base s = some (some C) →
  Block.Preceq w.CStar (eraseFG B) → Block.Preceq (eraseFG B) C →
  E.t_GST < SA.voteTime p.toParams s)

include slowWindowSync


-- conditional package, anti-vacuity: consume A5's proved new-write S1
-- clause at i + 1, with an actual HEAD and no domain premise.
example {i : Nat} (hinv : PostResetInv p c E rho w i)
    {x : V} {s : Slot} {C : Block} {B : FGBlock (Fin p.n)} {g : Nat}
    (hx : x ∈ rho.honest) (hi : IsGateTick p c rho i x s)
    (hpass : gatePassedAt p c E rho i)
    (hres : gateResultAt p c E rho i = some (some C))
    (hCB : Block.Preceq w.CStar (eraseFG B)) (hne : eraseFG B ≠ w.CStar)
    (hkey : (eraseFG B, g) ∈ @GridCO.gateWriteKeys GridCO.slowLeasePolicy
      p.toParams.engine p.n
      (actView (clockPre p (storeAt p c E rho i x) (SA.gateTime p.toParams s))) s C)
    (hnotSource : ¬ ∃ r, SrcN p c E rho B r)
    {y : V} {j : Slot} {H : Block} (hy : y ∈ rho.honest) (hsj : s + 1 ≤ j)
    (hcut : timeIdx rho (SA.voteTime p.toParams j) ≤ i + 1)
    (hhead : headAtLabel p c E rho y j = some H) :
    Block.Preceq (eraseFG B) H ∧ gatePassedAt p c E rho i ∧
      eraseFG B ≠ w.CStar ∧ ¬ ∃ r, SrcN p c E rho B r := by
  exact ⟨postReset_written_heads_at_write_cut p c E rho hrec mono emittedNonempty emittedName
    writes xing origin h0r gateResultSupporter slowWindowSync hinv hx hi hres hCB hkey
    y j H hy hsj hcut hhead, hpass, hne, hnotSource⟩


-- conditional package: consume the full result clause at i + 1 for an
-- old actual write and the new genuine gate reader at index i.
omit slowWindowSync in
example {i : Nat} (hinv : PostResetInv p c E rho w i)
    {k : Nat} (hki : k < i) {x : V} {s : Slot} {B C : Block} {g : Nat}
    (hx : x ∈ rho.honest) (hk : IsGateTick p c rho k x s)
    (hpass : gatePassedAt p c E rho k)
    (hres : gateResultAt p c E rho k = some (some C))
    (hCB : Block.Preceq w.CStar B) (hne : B ≠ w.CStar)
    (hmem : B ∈ (actView (clockPre p (storeAt p c E rho k x)
      (SA.gateTime p.toParams s))).blocks) (hgen : B ≠ .genesis) (hBC : Block.Preceq B C)
    (hg : g ∈ @GridCO.admissionLevels GridCO.slowLeasePolicy p.toParams.engine p.n
      (actView (clockPre p (storeAt p c E rho k x) (SA.gateTime p.toParams s))) s B)
    {y : V} {j : Slot} {D : Block} (hy : y ∈ rho.honest) (hsj : s + 1 ≤ j)
    (hi : IsGateTick p c rho i y j)
    (hresult : gateResultAt p c E rho i = some (some D)) :
    Block.Preceq B D ∨ Block.Preceq B (F_at p c E rho i y) := by
  exact postReset_leaseSafe_results_succ p c E rho hrec mono emittedNonempty emittedName
    writes xing origin h0r gateResultSupporter hinv k (hki.trans (Nat.lt_succ_self i))
    x s B g C hx hk hpass hres hCB hne hmem hgen hBC hg
    i (Nat.lt_succ_self i) y j D hy hsj hi hresult

end WrittenConsumers

end AvailableChain.FGSA.Run.Tests.HealingPostResetLeaseStep
end
