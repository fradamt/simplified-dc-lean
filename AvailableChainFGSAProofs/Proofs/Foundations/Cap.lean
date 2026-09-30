module
public import AvailableChainFGSAProofs.Proofs.Foundations.Carrier
public import AvailableChainFGSARun.Proofs.Reachable
public import AvailableChainGeneric.Proofs.V2.Linked
public import AvailableChainGeneric.Statements.V2.Counts
public import AvailableChainKitFG.CausalCap
public import AvailableChainKitFG.Provenance
public import AvailableChainGeneric.Proofs.V2.Reads

public section

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

variable (p : Params) {In V : Type} [DecidableEq V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.Run V (fgsa p c))

private noncomputable def capFaulty : Finset (Fin p.n) := by
  classical
  exact Finset.univ.filter (fun i => rho.seatOf (.base (.fg 0)) i ∉ rho.honest)

private theorem cap_weight [Fintype V]
    (hL : V2.Linked (fgsaFamilies p c).linked rho)
    (hQ : Gen.Pure.FaultQ p.n (Gen.V2.faulty rho).card) :
    p.E.weightOf (capFaulty p c rho) < p.E.q := by
  classical
  have hc := Gen.V2.linked_card_le_of_holders hL
    ((capFaulty p c rho).image Fin.val) (Gen.V2.faulty rho) (by
      intro k hk
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hk
      refine ⟨.base (.fg 0), by trivial, i, rfl, ?_⟩
      rw [Gen.V2.faulty_def]
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hi).2⟩)
  rw [Finset.card_image_of_injective _ Fin.val_injective] at hc
  have hw : p.E.weightOf (capFaulty p c rho) = (capFaulty p c rho).card := by
    change (∑ _ ∈ capFaulty p c rho, (1 : Nat)) = _
    simp
  have hq : p.E.q = Gen.Pure.qF p.n :=
    (KitFG.toWeights_q p.E).symm.trans (KitFG.unit_toWeights_q p.n)
  rw [hw, hq]
  exact hc.trans_lt hQ.lt

/-- The delivery index is retained to compare a row with a later tick,
including ticks of a different node at the same wall-clock time. -/
private def CapOrigin (i : Nat) (x : V) (u : Row (Fin p.n)) : Prop :=
  ∃ (z : V) (r : Nat) (a : RowWire p.n),
    HonestRowBefore p c E rho i z r a ∧ RowSigner p c rho a z ∧
    a.toRow? = some u ∧ ∃ k o s, k < i ∧
      rho.events[k]? = some (.deliver x o s) ∧ p.actionTime r ≤ s

private theorem cap_origin_of_held
    (hL : V2.Linked (fgsaFamilies p c).linked rho) (hv : V2.ExecutionValid E rho)
    (i : Nat) (x : V) (W : FGBlock (Fin p.n)) (hW : HeldAt p c E rho i x W) :
    ∀ u ∈ chainRows W, u.signer ∉ capFaulty p c rho → CapOrigin p c E rho i x u := by
  classical
  intro u hu hf
  obtain ⟨a, r, ha, har, k, o, t, hki, hk, he⟩ := held_chain_row_origin_before
    p c E rho hv.toUnforgeableSignatures hv.toScheduleWellFormed i x W hW u hu
  let z := rho.seatOf (.base (.fg r)) u.signer
  have hz : z ∈ rho.honest := by
    have hh : rho.seatOf (.base (.fg 0)) u.signer ∈ rho.honest := by
      by_contra hn
      exact hf (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hn⟩)
    have heq := Gen.V2.linked_holder_eq hL (ℓ := .base (.fg r))
      (ℓ' := .base (.fg 0)) (by trivial) (by trivial) u.signer u.signer rfl
    change rho.seatOf (.base (.fg r)) u.signer ∈ rho.honest
    rw [heq]
    exact hh
  have hsign : RowSigner p c rho a z := (rowSigner_iff_holder p c rho a z).mpr
    ⟨⟨r, u.signer, har⟩, by
      change V2.Run.holder rho (ofAuth p a.auth) = some z
      rw [har]; rfl⟩
  exact ⟨z, r, a, (he z hsign hz).1, hsign, ha, k, o, t, hki, hk, (he z hsign hz).2⟩

/-- R-CAP, P3 App. A.4: an instance of G17 on the held-block domain.
The authentic height row was released at an index strictly below the read. -/
theorem fgsa_rCap [Fintype V]
    (hL : V2.Linked (fgsaFamilies p c).linked rho) (hv : V2.ExecutionValid E rho)
    (hQ : Gen.Pure.FaultQ p.n (Gen.V2.faulty rho).card)
    (y' i' : Nat) (x : V) (W : FGBlock (Fin p.n))
    (hW : HeldAt p c E rho i' x W) (hheight : y' + 2 ≤ (derive p.E p.cfg W).h) :
    ∃ (z : V) (r : Nat) (a : RowWire p.n) (u : Row (Fin p.n))
      (T : BlockId) (timeout : Bool),
      HonestRowBefore p c E rho i' z r a ∧ RowSigner p c rho a z ∧
      RowWire.toRow? a = some u ∧ u ∈ chainRows W ∧
      u.height_pair = .vote (y' + 1) T timeout := by
  obtain ⟨u, hu, _, ho, T, timeout, hh⟩ :=
    KitFG.causalCap_row p.E p.cfg (capFaulty p c rho) (cap_weight p c rho hL hQ)
      y' W (CapOrigin p c E rho i' x) (cap_origin_of_held p c E rho hL hv i' x W hW) hheight
  obtain ⟨z, r, a, hb, hs, hd, _⟩ := ho
  exact ⟨z, r, a, u, T, timeout, hb, hs, hd, hu, hh⟩

/-- A positive certificate on a held chain contains an authentic honest
finality row. This also applies when the finalized checkpoint is genesis:
the certificate at height 1 in KitFG/Tests/CertHeight.lean needs a finality
quorum, and strict FaultQ prevents all its signers from being faulty.

Boundary example (kernel-checked in Tests/Cap.lean before the unused-import
check rejected that example-only module; retained here per the job rule):

```lean
example (p : Params) {In V : Type} [DecidableEq V] [Fintype V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.Run V (fgsa p c))
    (hL : V2.Linked (fgsaFamilies p c).linked rho) (hv : V2.ExecutionValid E rho)
    (hQ : Gen.Pure.FaultQ p.n (Gen.V2.faulty rho).card)
    (i : Nat) (x : V) (W : FGBlock (Fin p.n)) (hW : HeldAt p c E rho i x W)
    (hgen : (derive p.E p.cfg W).F = .genesis) (hcert : (derive p.E p.cfg W).h_F = 1) :
    ∃ z r a u, HonestRowBefore p c E rho i z r a ∧ RowSigner p c rho a z ∧
      RowWire.toRow? a = some u ∧ u ∈ chainRows W ∧
      u.finality_pair = some ⟨1, genesisRoot⟩ := by
  simpa only [hcert, hgen,
    show (FGBlock.genesis : FGBlock (Fin p.n)).root = genesisRoot from rfl] using
    fgsa_finalityCap p c E rho hL hv hQ 1 i (by decide) x W hW (by rw [hcert])
```
-/
theorem fgsa_finalityCap [Fintype V]
    (hL : V2.Linked (fgsaFamilies p c).linked rho) (hv : V2.ExecutionValid E rho)
    (hQ : Gen.Pure.FaultQ p.n (Gen.V2.faulty rho).card)
    (y i : Nat) (hy : 0 < y) (x : V) (W : FGBlock (Fin p.n))
    (hW : HeldAt p c E rho i x W) (hF : y ≤ (derive p.E p.cfg W).h_F) :
    ∃ z r a u, HonestRowBefore p c E rho i z r a ∧ RowSigner p c rho a z ∧
      RowWire.toRow? a = some u ∧ u ∈ chainRows W ∧
      u.finality_pair = some ⟨(derive p.E p.cfg W).h_F, (derive p.E p.cfg W).F.root⟩ := by
  obtain ⟨u, hu, _, ho, hf⟩ :=
    KitFG.finalityCap_row p.E p.cfg (capFaulty p c rho) (cap_weight p c rho hL hQ)
      y W (CapOrigin p c E rho i x) (cap_origin_of_held p c E rho hL hv i x W hW) hy hF
  obtain ⟨z, r, a, hb, hs, hd, _⟩ := ho
  exact ⟨z, r, a, u, hb, hs, hd, hu, hf⟩

private theorem cap_tick_lt (hv : V2.ExecutionValid E rho)
    {i : Nat} {x : V} {u : Row (Fin p.n)} (ho : CapOrigin p c E rho i x u)
    {v : V} {t : Time} (hi : rho.events[i]? = some (.tick v t)) :
    ∃ z r a, HonestRowBefore p c E rho i z r a ∧ RowSigner p c rho a z ∧
      a.toRow? = some u ∧ p.actionTime r < t := by
  obtain ⟨z, r, a, hb, hs, hd, k, o, s, hki, hk, hrs⟩ := ho
  refine ⟨z, r, a, hb, hs, hd, hrs.trans_lt ?_⟩
  by_contra hn
  have hik := V2.Engine.tick_index_lt_delivery E rho hv.toScheduleWellFormed hi hk
    (le_of_not_gt hn)
  omega

/-- Time consequence of R-CAP. The cut excludes every honest row of height
at least `y' + 1`. The held block supplies a row at or after the cut. -/
theorem fgsa_rCap_time [Fintype V]
    (hL : V2.Linked (fgsaFamilies p c).linked rho) (hv : V2.ExecutionValid E rho)
    (hQ : Gen.Pure.FaultQ p.n (Gen.V2.faulty rho).card)
    (y' i' : Nat) (t : Time) (x : V) (W : FGBlock (Fin p.n))
    (hW : HeldAt p c E rho i' x W) (hheight : y' + 2 ≤ (derive p.E p.cfg W).h)
    (hcut : ∀ j z r a u h T timeout, HonestRowAt p c E rho j z r a →
      RowWire.toRow? a = some u → u.height_pair = .vote h T timeout →
      p.actionTime r < t → h < y' + 1) :
    ∃ z r a u T timeout, HonestRowBefore p c E rho i' z r a ∧
      RowSigner p c rho a z ∧ RowWire.toRow? a = some u ∧ u ∈ chainRows W ∧
      u.height_pair = .vote (y' + 1) T timeout ∧ t ≤ p.actionTime r := by
  obtain ⟨z, r, a, u, T, timeout, hb, hs, hd, hu, hh⟩ :=
    fgsa_rCap p c E rho hL hv hQ y' i' x W hW hheight
  refine ⟨z, r, a, u, T, timeout, hb, hs, hd, hu, hh, ?_⟩
  obtain ⟨j, _, hj⟩ := hb
  exact le_of_not_gt (fun hlt => (Nat.lt_irrefl _) (hcut j z r a u _ T timeout hj hd hh hlt))

/-- Before the time cut, the same held domain has height below `y' + 2`.
`i' ≤ idxBefore t` includes every read whose whole prefix is before `t`. -/
theorem fgsa_rCap_before [Fintype V]
    (hL : V2.Linked (fgsaFamilies p c).linked rho) (hv : V2.ExecutionValid E rho)
    (hQ : Gen.Pure.FaultQ p.n (Gen.V2.faulty rho).card)
    (y' i' : Nat) (t : Time) (x : V) (W : FGBlock (Fin p.n))
    (hi : i' ≤ V2.Run.idxBefore rho t) (hW : HeldAt p c E rho i' x W)
    (hcut : ∀ j z r a u h T timeout, HonestRowAt p c E rho j z r a →
      RowWire.toRow? a = some u → u.height_pair = .vote h T timeout →
      p.actionTime r < t → h < y' + 1) :
    (derive p.E p.cfg W).h < y' + 2 := by
  by_contra hn
  obtain ⟨u, _, _, ho, T, b, hh⟩ :=
    KitFG.causalCap_row p.E p.cfg (capFaulty p c rho) (cap_weight p c rho hL hQ)
      y' W (CapOrigin p c E rho i' x) (cap_origin_of_held p c E rho hL hv i' x W hW)
      (Nat.le_of_not_gt hn)
  obtain ⟨z, r, a, hb, hs, hd, k, o, s, hki, hk, hrs⟩ := ho
  have hst := (Gen.V2.index_lt_idxBefore_iff hv.toScheduleWellFormed hk t).mp (hki.trans_le hi)
  obtain ⟨j, _, hj⟩ := hb
  exact (Nat.lt_irrefl _) (hcut j z r a u _ T b hj hd hh (hrs.trans_lt hst))

private theorem cap_finality_head {j r : Nat} {z : V} {a : RowWire p.n}
    {u : Row (Fin p.n)} (ha : HonestRowAt p c E rho j z r a)
    (hs : RowSigner p c rho a z) (hd : a.toRow? = some u)
    (fp : FinalityPair) (hf : u.finality_pair = some fp) :
    ∃ H, HeldAt p c E rho j z H ∧ fp.height = (derive p.E p.cfg H).h_j ∧
      rho.events[j]? = some (.tick z (p.actionTime r)) := by
  obtain ⟨hz, hr, t, hj, hem⟩ := ha
  obtain ⟨r', seat, har, _⟩ := hs
  rcases a with ⟨auth, body⟩
  change auth = _ at har
  subst auth
  have hrr : r' = r := Option.some.inj hr
  subst r'
  have he := (fgsa_emitsAt_row E rho j z t hj r seat body).mp hem
  let st := FGSA.clock p (V2.Run.stateBefore E rho j z).st t
  let Λ := (V2.Run.stateBefore E rho j z).record
  have hdecode := fgsa_attest_decode (p := p) st Λ r seat
  have hue : (createRow p.E p.cfg Λ seat (fgInputs p st).1 (fgInputs p st).2).1 = u := by
    rw [← he.2.2.2] at hdecode
    exact Option.some.inj (hdecode.symm.trans hd)
  have hfinal : (createRow p.E p.cfg Λ seat (fgInputs p st).1
      (fgInputs p st).2).1.finality_pair = some fp := hue ▸ hf
  have hst := cstoreInv_clock p _ (storeBundle_stateBefore E rho j z).cstore t
  cases hhead : fgBlockOf st (fgHead p st) with
  | none =>
      have hh : (fgInputs p st).2 = ⟨0, genesisRoot, 0⟩ := by
        change (match fgBlockOf st (fgHead p st) with
          | some H => HeadFields.ofBlock p.E p.cfg H | none => ⟨0, genesisRoot, 0⟩) = _
        rw [hhead]
      rw [hh] at hfinal
      change (if (0 : Nat) < 0 ∧
          (Λ.target 0 = none ∨ Λ.target 0 = some genesisRoot) ∧
          Λ.timeout 0 = false ∧ (Λ.lock 0 = none ∨ Λ.lock 0 = some genesisRoot)
        then some ⟨0, genesisRoot⟩ else none) = some fp at hfinal
      rw [ite_eq_right (fun h => Nat.lt_irrefl 0 h.1)] at hfinal
      cases hfinal
  | some H =>
      have hh : (fgInputs p st).2 = HeadFields.ofBlock p.E p.cfg H := by
        change (match fgBlockOf st (fgHead p st) with
          | some H => HeadFields.ofBlock p.E p.cfg H | none => ⟨0, genesisRoot, 0⟩) = _
        rw [hhead]
      rw [hh] at hfinal
      have hp := KitFG.provenance_finalityRow p.E p.cfg Λ seat (fgInputs p st).1 H fp hfinal
      have hmem := ((fgBlockOf_spec p st hst (fgHead p st) H).mp hhead).1
      change H ∈ (FGSA.clock p _ t).fg.TF at hmem
      rw [FGSA.clock_fg] at hmem
      exact ⟨H, ⟨hz, hmem⟩, hp.1, he.2.1 ▸ hj⟩

/-- S1 G17 #19, with the lead's positive-height correction. The held read
has a prefix before `a_(q+1)`. The absence premise concerns all honest
height-y emissions strictly before `a_q`, including rows no longer held.
The result uses certificate height, including a certificate for genesis. -/
theorem fgsa_finalityLag [Fintype V]
    (hL : V2.Linked (fgsaFamilies p c).linked rho) (hv : V2.ExecutionValid E rho)
    (hQ : Gen.Pure.FaultQ p.n (Gen.V2.faulty rho).card)
    (q y i : Nat) (hy : 0 < y) (x : V) (W : FGBlock (Fin p.n))
    (hi : i ≤ V2.Run.idxBefore rho (p.actionTime (q + 1)))
    (hW : HeldAt p c E rho i x W)
    (hnone : ∀ j z r a u T timeout, HonestRowAt p c E rho j z r a →
      RowWire.toRow? a = some u → u.height_pair = .vote y T timeout →
      ¬ p.actionTime r < p.actionTime q) :
    (derive p.E p.cfg W).h_F < y := by
  by_contra hn
  obtain ⟨u, _, _, ho, hf⟩ :=
    KitFG.finalityCap_row p.E p.cfg (capFaulty p c rho) (cap_weight p c rho hL hQ)
      y W (CapOrigin p c E rho i x) (cap_origin_of_held p c E rho hL hv i x W hW)
      hy (Nat.le_of_not_gt hn)
  obtain ⟨z, r, a, hb, hs, hd, k, o, s, hki, hk, hrs⟩ := ho
  have hst := (Gen.V2.index_lt_idxBefore_iff hv.toScheduleWellFormed hk
    (p.actionTime (q + 1))).mp (hki.trans_le hi)
  have hrq : p.actionTime r < p.actionTime (q + 1) := hrs.trans_lt hst
  obtain ⟨j, _, hj⟩ := hb
  obtain ⟨H, hH, hheight, htick⟩ := cap_finality_head p c E rho hj hs hd _ hf
  have hy' : y - 1 + 1 = y := by omega
  have hjust : y - 1 + 1 ≤ (derive p.E p.cfg H).h_j := by
    change (derive p.E p.cfg W).h_F = _ at hheight
    rw [hy']
    exact (Nat.le_of_not_gt hn).trans hheight.le
  obtain ⟨v, _, _, ho, T, b, hh⟩ :=
    KitFG.causalCap_justified_row p.E p.cfg (capFaulty p c rho) (cap_weight p c rho hL hQ)
      (y - 1) H (CapOrigin p c E rho j z) (cap_origin_of_held p c E rho hL hv j z H hH) hjust
  obtain ⟨z', r', a', hb', _, hd', hlt⟩ := cap_tick_lt p c E rho hv ho htick
  obtain ⟨j', _, hj'⟩ := hb'
  rw [hy'] at hh
  apply hnone j' z' r' a' v T b hj' hd' hh
  have hmono : Monotone p.actionTime := by
    intro m n hmn
    change (4 * p.Δ * ((m * p.R : Nat) : Int) + 6 * p.Δ) ≤
      (4 * p.Δ * ((n * p.R : Nat) : Int) + 6 * p.Δ)
    gcongr
    exact mul_nonneg (by decide) (le_of_lt p.deltaPos)
  have hrle : r ≤ q := by
    by_contra h
    exact (not_lt_of_ge (hmono (show q + 1 ≤ r by omega))) hrq
  exact hlt.trans_le (hmono hrle)

end AvailableChain.FGSA.Run
end
