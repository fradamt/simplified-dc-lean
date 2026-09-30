module
public import AvailableChainGeneric.Statements.AC.Lease
public import AvailableChainGeneric.Proofs.Pure.BlockOrder

public section

namespace AvailableChain.Gen.AC

open AvailableChain AvailableChain.V2 AvailableChain.V2.Engine

/-- S4b-01, Q1 A: both live targets are below the same output. -/
theorem lease_chain_statement : LeaseChainStatement := by
  rw [LeaseChainStatement_def]
  intro V In P E rho A laws i x hx l k hl hk hll hkl
  exact Pure.block_compatible_of_common
    (laws.lease_le_output i x hx l hl hll)
    (laws.lease_le_output i x hx k hk hkl)

/-- S4b-01, Q1 A. Adapted from GridCO/Proofs/Protection.lean:139–179;
expiry and output normalization follow the event-indexed gate law. -/
theorem pendingGate_harmless_statement : PendingGateHarmlessStatement := by
  rw [PendingGateHarmlessStatement_def]
  intro V In P E rho A laws i s x he B g d hr hd hB
  have gate := laws.gate_write i s x he
  have hrow : (B, g, d) ∈ (A.gateView i x s).obligations := by
    rw [ACReads.gateView_def]
    change (B, g, d) ∈ ((A.activeView i x).obligations.filter
      (fun (_, _, deadline) => SA.gateTime A.prm s < deadline))
    exact List.mem_filter.mpr
      ⟨gate.view_leases.symm ▸ hr, by simpa only [decide_eq_true_eq] using hd⟩
  rcases gate.effects with skip | run
  · rw [skip.2.1]
    exact hB
  · cases hraw : A.raw i s x with
    | none =>
        rw [(run.empty hraw).1]
        exact hB
    | some candidate =>
        classical
        by_cases hveto : ∃ lease ∈ (A.gateView i x s).obligations,
            ¬ Block.Compatible (Lease.target lease) candidate
        · rw [(run.veto candidate hraw hveto).1]
          exact hB
        · have hall : ∀ lease ∈ (A.gateView i x s).obligations,
              Block.Compatible (Lease.target lease) candidate := by
            intro lease hlease
            exact Classical.byContradiction (fun h => hveto ⟨lease, hlease, h⟩)
          have hcomp : Block.Compatible B candidate := hall (B, g, d) hrow
          have hadvance : Block.Preceq B (GridCO.advance (A.output i x) candidate) := by
            unfold GridCO.advance
            split
            · exact hB
            · rename_i hn
              rcases Bool.or_eq_true_iff.mp hcomp with hforward | hback
              · exact hforward
              · exact (hn (Pure.block_preceq_trans hback hB)).elim
          rw [(run.accept candidate hraw hall).1, normalizeOutput_def]
          split
          · exact hadvance
          · rename_i hn
            rcases Pure.block_preceq_total_of_common hB (laws.anchor_le_output i x) with
              hprefix | hanchor
            · exact hprefix
            · exact (hn (Pure.block_preceq_trans hanchor hadvance)).elim

variable {V : Type} {In : Type} {P : ProtocolSpec In}
  {E : Generic.Env V} {rho : Run V P}

/-- The live targets of two leases at an honest node are compatible. -/
theorem lease_chain (A : ACReads E rho) (laws : ACLaws A) (i : Nat) (x : V)
    (hx : x ∈ rho.honest) (l k : Block × Nat × Time)
    (hl : l ∈ A.leases i x) (hk : k ∈ A.leases i x)
    (hll : A.now i x < Lease.deadline l) (hkl : A.now i x < Lease.deadline k) :
    Block.Compatible (Lease.target l) (Lease.target k) :=
  lease_chain_statement A laws i x hx l k hl hk hll hkl

/-- A gate retains an output prefix whose lease is live at the gate time. -/
theorem pendingGate_harmless (A : ACReads E rho) (laws : ACLaws A)
    (i : Nat) (s : Slot) (x : V)
    (he : rho.events[i]? = some (.tick x (SA.gateTime A.prm s)))
    (B : Block) (g : Nat) (d : Time) (hr : (B, g, d) ∈ A.leases i x)
    (hd : SA.gateTime A.prm s < d) (hB : Block.Preceq B (A.output i x)) :
    Block.Preceq B (A.output (i + 1) x) :=
  pendingGate_harmless_statement A laws i s x he B g d hr hd hB

end AvailableChain.Gen.AC
