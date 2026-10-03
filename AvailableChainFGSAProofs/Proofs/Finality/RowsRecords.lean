module
public import AvailableChainFGSAProofs.Proofs.Finality.Middle
public import AvailableChainFGSAProofs.Proofs.Finality.RecordInv

public section

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

variable (p : Params) {In V : Type} [DecidableEq V] [Fintype V]
    (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {G ΔF : Time} {pt : KernelPt} {A : Block}
    (m : KernelMiddleWitness_W p c E rho ΔF pt A)

omit [Fintype V] in
/-- Paper 22:1224–1225,1259–1263: an event-time cut bounds earlier action rows.
DC: INTENTIONAL: the generic cut is supplied by K-MID at height d+2. -/
theorem rowsPrem_earlier_height (q y : Nat)
    (hcut : ∀ j x r a h t, HonestRowAt p c E rho j x r a → rowHeight a = some h →
      y ≤ h → eventTime rho j = some t → p.actionTime q ≤ t) :
    ∀ j x r a h, r < q →
      HonestRowAt p c E rho j x r a → rowHeight a = some h → h < y := by
  intro j x r a h hr ha hh
  by_contra hn
  have hlate := hcut j x r a h (p.actionTime r) ha hh (by omega)
    (kmid_event_time p c E rho ha)
  exact not_le_of_gt ((kmid_action_strictMono p).lt_iff_lt.mpr hr) hlate

/-- Paper 22:841–879,1256–1263: P6 supplies the seven K-ROWS record guards.
DC: INTENTIONAL: FF2 at the actual B source and strict own history at height d+2. -/
theorem rowsPrem_action_record (hK : KernelPrem_W p c G ΔF E rho pt)
    (hQC : RQCOrigin p c E rho)
    (hNames : ∀ j x r a e, HonestRowAt p c E rho j x r a →
      namedEntry a.payload.height_pair = some e →
      ∃ C, actionSourceFG p c E rho x r = some (some C) ∧
        e = ((heightView p C).h, (heightView p C).T_h.root)) :
    ∀ x nd, x ∈ rho.honest →
      postClock E rho x (p.actionTime (pt.r + 2)) = some nd →
      (nd.record.target (m.d + 1) = none ∨ nd.record.target (m.d + 1) = some m.U.root) ∧
      nd.record.timeout (m.d + 1) = false ∧
      (nd.record.lock (m.d + 1) = none ∨ nd.record.lock (m.d + 1) = some m.U.root) ∧
      nd.record.target (m.d + 2) = none ∧ nd.record.timeout (m.d + 2) = false ∧
      nd.record.lock (m.d + 2) = none ∧
      ∀ b ∈ nd.record.sent, ∀ T timeout, b.1 ≠ .vote (m.d + 2) T timeout := by
  intro x nd hx hnd
  have hg := high_record_guards_and_fresh_at_action p c E rho pt.w hK.input.t.h1 hQC hNames
    hK.set.base.valid.toScheduleWellFormed x (pt.r + 1) m.B hx (m.sourceB x hx)
    (m.d + 1) m.heightB (by have := m.highA; omega) (pt.r + 2) x hx
    (fun j r a h hr ha hh => by
      simpa only [Nat.add_assoc] using rowsPrem_earlier_height p c E rho
        (pt.r + 2) (m.d + 2) m.noSecondHeight j x r a h hr ha hh)
    nd hnd
  simpa only [m.entryB, Nat.add_assoc] using hg

end AvailableChain.FGSA.Run
end
