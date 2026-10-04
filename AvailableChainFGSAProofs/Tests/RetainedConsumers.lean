module
public import AvailableChainFGSAProofs.Proofs.Shared.RetainedConsumersH6S
public import AvailableChainFGSAProofs.Proofs.Shared.RetainedConsumersQ
public import AvailableChainFGSAProofs.Proofs.Shared.RetainedConsumersL2
public import AvailableChainFGSAProofs.Proofs.Shared.Regimes

set_option linter.privateModule false

namespace AvailableChain.FGSA.Run.Tests.RetainedConsumers

open AvailableChain.SimplexFG Gen.Pure RetainedWalk

variable {p : Params} {In V : Type} [DecidableEq V] [Fintype V] {c : AppCodec In}

/-- Blueprint 21 H.6, H.6-S, H.17, L4-R, HG.1, L2; design job 7 K6.
Class (iii). DC: INTENTIONAL; private type checks for the shared run and regime APIs. -/
private def Composes (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (ip : Nat) (x : V) (s : Slot) (D : FGBlock (Fin p.n)) (b : Block) : Prop :=
  (Gen.V2.Duty.LabelSyncOn E rho (fun o => ¬ isRowObject o)
      (SA.proposalTime p.toParams s - p.Δ) (SA.proposalTime p.toParams s) →
    Gen.V2.Duty.LabelSyncOn E rho (fun o => ¬ isRowObject o)
      (SA.proposalTime p.toParams s - p.Δ) (SA.voteTime p.toParams s) →
    RetainedExactHeadRunGeometry E rho ip x s D b) ∧
  (∀ (b₀ ΔF : Time), CleanCut₂ p c E rho b₀ ΔF → SA.voteTime p.toParams s ≤ b₀ →
    SA.voteTime p.toParams s ≤ rho.horizon →
    ∀ y ∈ rho.honest, headAtLabel p c E rho y s = some b) ∧
  (∀ (G ΔF : Time), Recovery₂ p c E rho G ΔF →
    E.t_GST ≤ SA.proposalTime p.toParams s - p.Δ →
    SA.voteTime p.toParams s ≤ rho.horizon →
    ∀ y ∈ rho.honest, headAtLabel p c E rho y s = some b)

/-- Blueprint 21 H.6, H.6-S, H.17, L4-R, HG.1, L2; design job 7 K6.
Class (iii). DC: INTENTIONAL; derive the consumer's LabelSyncOn from each regime. -/
private theorem compose
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hroots : NamedRootCollisionFree p c E rho)
    (hE : V2.D.ExecutionValid E rho) (hN : V2.D.NoRestart rho) (hDelta : E.Δ = p.Δ)
    (s : Slot) {ip : Nat} {x : V} (hx : x ∈ rho.honest)
    (hip : rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams s)))
    (hseat : rho.seatOf (.prop s) ⟨0, Nat.one_pos⟩ = x)
    (b : Block) (raw sup : List (HeadWire p.n)) (rows : List (RowWire p.n))
    (hem : (⟨.seat (.prop s) ⟨0, Nat.one_pos⟩, .proposal b raw sup rows⟩ : Obj p) ∈
      rho.emitsAt E ip)
    (D : FGBlock (Fin p.n))
    (supply : Gen.V2.Duty.LabelSyncOn E rho (fun o => ¬ isRowObject o)
      (SA.proposalTime p.toParams s - p.Δ) (SA.voteTime p.toParams s) →
      ∀ y ∈ rho.honest, ∀ ih,
        rho.events[ih]? = some (.tick y (SA.voteTime p.toParams s)) →
        ∃ Kc, RetainedReadPremises p
          (clock p (rho.stateBefore E ip x).st (SA.proposalTime p.toParams s))
          (clock p (rho.stateBefore E ih y).st (SA.voteTime p.toParams s)) s D b Kc) :
    Composes E rho ip x s D b := by
  have hpt : SA.proposalTime p.toParams s - p.Δ + E.Δ ≤ SA.proposalTime p.toParams s := by
    rw [hDelta]
    exact le_of_eq (sub_add_cancel _ _)
  have htv : SA.proposalTime p.toParams s ≤ SA.voteTime p.toParams s := by
    change 4 * p.Δ * (s : Int) ≤ 4 * p.Δ * (s : Int) + p.Δ
    linarith [p.deltaPos]
  refine ⟨?_, ?_, ?_⟩
  · intro hwalk hscore
    exact fgsa_retainedExactHead_geometry_on_run (hroots := hroots) E rho hE hN hDelta s
      hwalk hscore hx hip hseat b raw sup rows hem D (supply hscore)
  · intro b₀ ΔF h hcut
    have hscore := Gen.V2.Duty.LabelSyncOn.of_cleanCutBy E rho
      (fun o => ¬ isRowObject o) b₀ _ _ h.healthy (fgsaDelay_nonrow E.Δ _)
      (hpt.trans htv) hcut h.cut.2
    exact exactService_head_of_retained_proposal_clean E rho b₀ h s hcut
      hx hip hseat b raw sup rows hem D (supply hscore)
  · intro G ΔF h hGST hhorizon
    have hscore := Gen.V2.Duty.LabelSyncOn.of_recoveryBy E rho
      (fun o => ¬ isRowObject o) _ _ h.sync (fgsaDelay_nonrow E.Δ _)
      hGST (hpt.trans htv) hhorizon
    exact exactService_head_of_retained_proposal_recovery E rho G h s hGST
      hx hip hseat b raw sup rows hem D (supply hscore) hhorizon

/-- Blueprint 21; design job 7 K6. Class (iii).
DC: INTENTIONAL; H6 produces the exact hreads type for all three endpoints. -/
private theorem check_H6
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hroots : NamedRootCollisionFree p c E rho)
    (hE : V2.D.ExecutionValid E rho) (hN : V2.D.NoRestart rho) (hDelta : E.Δ = p.Δ)
    (s : Slot)
    {ip : Nat} {x : V} (hx : x ∈ rho.honest)
    (hip : rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams s)))
    (hseat : rho.seatOf (.prop s) ⟨0, Nat.one_pos⟩ = x)
    (b : Block) (raw sup : List (HeadWire p.n)) (rows : List (RowWire p.n))
    (hem : (⟨.seat (.prop s) ⟨0, Nat.one_pos⟩, .proposal b raw sup rows⟩ : Obj p) ∈
      rho.emitsAt E ip)
    (hinput : ∀ y ∈ rho.honest, ∀ ih,
      rho.events[ih]? = some (.tick y (SA.voteTime p.toParams s)) →
      RetainedH6Input p
        (clock p (rho.stateBefore E ip x).st (SA.proposalTime p.toParams s))
        (clock p (rho.stateBefore E ih y).st (SA.voteTime p.toParams s)) s) :
    Composes E rho ip x s
      (controls p (clock p (rho.stateBefore E ip x).st (SA.proposalTime p.toParams s))).Z b := by
  apply compose E rho hroots hE hN hDelta s hx hip hseat b raw sup rows hem
  intro hSync
  exact fgsa_retainedReads_H6 (hroots := hroots) E rho hE hN hDelta s hSync hx hip hseat b raw
      sup rows hem hinput

/-- Blueprint 21; design job 7 K6. Class (iii).
DC: INTENTIONAL; H6S produces the exact hreads type for all three endpoints. -/
private theorem check_H6S
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hroots : NamedRootCollisionFree p c E rho)
    (hE : V2.D.ExecutionValid E rho) (hN : V2.D.NoRestart rho) (hDelta : E.Δ = p.Δ)
    (s : Slot)
    {ip : Nat} {x : V} (hx : x ∈ rho.honest)
    (hip : rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams s)))
    (hseat : rho.seatOf (.prop s) ⟨0, Nat.one_pos⟩ = x)
    (b : Block) (raw sup : List (HeadWire p.n)) (rows : List (RowWire p.n))
    (hem : (⟨.seat (.prop s) ⟨0, Nat.one_pos⟩, .proposal b raw sup rows⟩ : Obj p) ∈
      rho.emitsAt E ip)
    (hinput : ∀ y ∈ rho.honest, ∀ ih,
      rho.events[ih]? = some (.tick y (SA.voteTime p.toParams s)) →
      RetainedH6Input p
        (clock p (rho.stateBefore E ip x).st (SA.proposalTime p.toParams s))
        (clock p (rho.stateBefore E ih y).st (SA.voteTime p.toParams s)) s) :
    Composes E rho ip x s
      (controls p (clock p (rho.stateBefore E ip x).st (SA.proposalTime p.toParams s))).Z b := by
  apply compose E rho hroots hE hN hDelta s hx hip hseat b raw sup rows hem
  intro hSync
  exact fgsa_retainedReads_H6S (hroots := hroots) E rho hE hN hDelta s hSync hx hip hseat b raw
      sup rows hem hinput

/-- Blueprint 21; design job 7 K6. Class (iii).
DC: INTENTIONAL; H17 produces the exact hreads type for all three endpoints. -/
private theorem check_H17
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hroots : NamedRootCollisionFree p c E rho)
    (hE : V2.D.ExecutionValid E rho) (hN : V2.D.NoRestart rho) (hDelta : E.Δ = p.Δ)
    (s : Slot)
    {ip : Nat} {x : V} (hx : x ∈ rho.honest)
    (hip : rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams s)))
    (hseat : rho.seatOf (.prop s) ⟨0, Nat.one_pos⟩ = x)
    (b : Block) (raw sup : List (HeadWire p.n)) (rows : List (RowWire p.n))
    (hem : (⟨.seat (.prop s) ⟨0, Nat.one_pos⟩, .proposal b raw sup rows⟩ : Obj p) ∈
      rho.emitsAt E ip)
    (D : FGBlock (Fin p.n))
    (hinput : ∀ y ∈ rho.honest, ∀ ih,
      rho.events[ih]? = some (.tick y (SA.voteTime p.toParams s)) →
      RetainedConeInput p
        (clock p (rho.stateBefore E ip x).st (SA.proposalTime p.toParams s))
        (clock p (rho.stateBefore E ih y).st (SA.voteTime p.toParams s)) s D) :
    Composes E rho ip x s D b := by
  apply compose E rho hroots hE hN hDelta s hx hip hseat b raw sup rows hem
  intro hSync
  exact fgsa_retainedReads_H17 (hroots := hroots) E rho hE hN hDelta s hSync hx hip hseat b raw
      sup rows hem D hinput

/-- Blueprint 21; design job 7 K6. Class (iii).
DC: INTENTIONAL; L4R produces the exact hreads type for all three endpoints. -/
private theorem check_L4R
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hroots : NamedRootCollisionFree p c E rho)
    (hE : V2.D.ExecutionValid E rho) (hN : V2.D.NoRestart rho) (hDelta : E.Δ = p.Δ)
    (s : Slot)
    {ip : Nat} {x : V} (hx : x ∈ rho.honest)
    (hip : rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams s)))
    (hseat : rho.seatOf (.prop s) ⟨0, Nat.one_pos⟩ = x)
    (b : Block) (raw sup : List (HeadWire p.n)) (rows : List (RowWire p.n))
    (hem : (⟨.seat (.prop s) ⟨0, Nat.one_pos⟩, .proposal b raw sup rows⟩ : Obj p) ∈
      rho.emitsAt E ip)
    (Q : FGBlock (Fin p.n))
    (q : Slot) (w_a w_b : Time)
    (hafter : SA.gateTime p.toParams q ≤ SA.proposalTime p.toParams s)
    (hstop : SA.gateTime p.toParams s < min w_a w_b)
    (hinput : ∀ y ∈ rho.honest, ∀ ih,
      rho.events[ih]? = some (.tick y (SA.voteTime p.toParams s)) →
      (SA.gateTime p.toParams q ≤ SA.proposalTime p.toParams s ∧
        SA.voteTime p.toParams s < min w_a w_b) →
      RetainedConeInput p
        (clock p (rho.stateBefore E ip x).st (SA.proposalTime p.toParams s))
        (clock p (rho.stateBefore E ih y).st (SA.voteTime p.toParams s)) s Q) :
    Composes E rho ip x s Q b := by
  apply compose E rho hroots hE hN hDelta s hx hip hseat b raw sup rows hem
  intro hSync
  exact fgsa_retainedReads_L4R (hroots := hroots) E rho hE hN hDelta s hSync hx hip hseat b raw
      sup rows hem
    Q q w_a w_b hafter hstop hinput

/-- Blueprint 21; design job 7 K6. Class (iii).
DC: INTENTIONAL; HG1 produces the exact hreads type for all three endpoints. -/
private theorem check_HG1
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hroots : NamedRootCollisionFree p c E rho)
    (hE : V2.D.ExecutionValid E rho) (hN : V2.D.NoRestart rho) (hDelta : E.Δ = p.Δ)
    (s : Slot)
    {ip : Nat} {x : V} (hx : x ∈ rho.honest)
    (hip : rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams s)))
    (hseat : rho.seatOf (.prop s) ⟨0, Nat.one_pos⟩ = x)
    (b : Block) (raw sup : List (HeadWire p.n)) (rows : List (RowWire p.n))
    (hem : (⟨.seat (.prop s) ⟨0, Nat.one_pos⟩, .proposal b raw sup rows⟩ : Obj p) ∈
      rho.emitsAt E ip)
    (Q : FGBlock (Fin p.n))
    (q : Slot) (stop : Time)
    (hafter : SA.gateTime p.toParams q ≤ SA.proposalTime p.toParams s)
    (hstop : SA.gateTime p.toParams s < stop)
    (hinput : ∀ y ∈ rho.honest, ∀ ih,
      rho.events[ih]? = some (.tick y (SA.voteTime p.toParams s)) →
      (SA.gateTime p.toParams q ≤ SA.proposalTime p.toParams s ∧
        SA.voteTime p.toParams s < stop) →
      RetainedConeInput p
        (clock p (rho.stateBefore E ip x).st (SA.proposalTime p.toParams s))
        (clock p (rho.stateBefore E ih y).st (SA.voteTime p.toParams s)) s Q) :
    Composes E rho ip x s Q b := by
  apply compose E rho hroots hE hN hDelta s hx hip hseat b raw sup rows hem
  intro hSync
  exact fgsa_retainedReads_HG1 (hroots := hroots) E rho hE hN hDelta s hSync hx hip hseat b raw
      sup rows hem
    Q q stop hafter hstop hinput

/-- Blueprint 21; design job 7 K6. Class (iii).
DC: INTENTIONAL; L2 produces the exact hreads type for all three endpoints. -/
private theorem check_L2
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hroots : NamedRootCollisionFree p c E rho)
    (hE : V2.D.ExecutionValid E rho) (hN : V2.D.NoRestart rho) (hDelta : E.Δ = p.Δ)
    (s : Slot)
    {ip : Nat} {x : V} (hx : x ∈ rho.honest)
    (hip : rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams s)))
    (hseat : rho.seatOf (.prop s) ⟨0, Nat.one_pos⟩ = x)
    (b : Block) (raw sup : List (HeadWire p.n)) (rows : List (RowWire p.n))
    (hem : (⟨.seat (.prop s) ⟨0, Nat.one_pos⟩, .proposal b raw sup rows⟩ : Obj p) ∈
      rho.emitsAt E ip)
    (J : FGBlock (Fin p.n))
    (rd w stop : Time)
    (hinherited : rd ≤ SA.gateTime p.toParams s)
    (hevidence : w + 2 * p.Δ ≤ SA.proposalTime p.toParams s)
    (hstop : SA.gateTime p.toParams s < stop)
    (hinput : ∀ y ∈ rho.honest, ∀ ih,
      rho.events[ih]? = some (.tick y (SA.voteTime p.toParams s)) →
      (rd ≤ SA.gateTime p.toParams s ∧
        w + 2 * p.Δ ≤ SA.proposalTime p.toParams s ∧ SA.gateTime p.toParams s < stop) →
      RetainedL2Input p
        (clock p (rho.stateBefore E ip x).st (SA.proposalTime p.toParams s))
        (clock p (rho.stateBefore E ih y).st (SA.voteTime p.toParams s)) s J) :
    Composes E rho ip x s J b := by
  apply compose E rho hroots hE hN hDelta s hx hip hseat b raw sup rows hem
  intro hSync
  exact fgsa_retainedReads_L2 (hroots := hroots) E rho hE hN hDelta s hSync hx hip hseat b raw
      sup rows hem
    J rd w stop hinherited hevidence hstop hinput

/-- Blueprint 21 HG.1:1570–1574. Class (iii).
DC: INTENTIONAL; q+1's proposal and HEAD both precede the repair gate d_q. -/
private theorem q1_before_gate (p : Params) (q : Slot) :
    SA.proposalTime p.toParams (q + 1) < SA.gateTime p.toParams q ∧
    SA.voteTime p.toParams (q + 1) < SA.gateTime p.toParams q := by
  change (4 * p.Δ * ((q + 1 : Nat) : Int) < 4 * p.Δ * (q : Int) + 6 * p.Δ) ∧
    (4 * p.Δ * ((q + 1 : Nat) : Int) + p.Δ < 4 * p.Δ * (q : Int) + 6 * p.Δ)
  push_cast
  constructor <;> nlinarith [p.deltaPos]

/-- Blueprint 21 HG.1:1570–1574; design job 7 K4/K6. Class (iii).
DC: INTENTIONAL; the boundary uses H6, with no post-d_q lease premise. -/
private theorem q1_H6
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hroots : NamedRootCollisionFree p c E rho)
    (hE : V2.D.ExecutionValid E rho) (hN : V2.D.NoRestart rho) (hDelta : E.Δ = p.Δ)
    (q : Slot)
    {ip : Nat} {x : V} (hx : x ∈ rho.honest)
    (hip : rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams (q + 1))))
    (hseat : rho.seatOf (.prop (q + 1)) ⟨0, Nat.one_pos⟩ = x)
    (b : Block) (raw sup : List (HeadWire p.n)) (rows : List (RowWire p.n))
    (hem : (⟨.seat (.prop (q + 1)) ⟨0, Nat.one_pos⟩, .proposal b raw sup rows⟩ : Obj p) ∈
      rho.emitsAt E ip)
    (hinput : ∀ y ∈ rho.honest, ∀ ih,
      rho.events[ih]? = some (.tick y (SA.voteTime p.toParams (q + 1))) →
      RetainedH6Input p
        (clock p (rho.stateBefore E ip x).st (SA.proposalTime p.toParams (q + 1)))
        (clock p (rho.stateBefore E ih y).st (SA.voteTime p.toParams (q + 1))) (q + 1)) :
    (SA.proposalTime p.toParams (q + 1) < SA.gateTime p.toParams q ∧
      SA.voteTime p.toParams (q + 1) < SA.gateTime p.toParams q) ∧
    Composes E rho ip x (q + 1)
      (controls p (clock p (rho.stateBefore E ip x).st
        (SA.proposalTime p.toParams (q + 1)))).Z b := by
  refine ⟨q1_before_gate p q, ?_⟩
  exact check_H6 E rho hroots hE hN hDelta (q + 1) hx hip hseat b raw sup rows hem hinput

/-- Blueprint 21 HG.1:1570–1574; design job 7 K4/K6. Class (iii).
DC: INTENTIONAL; the boundary uses H6S, with no post-d_q lease premise. -/
private theorem q1_H6S
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hroots : NamedRootCollisionFree p c E rho)
    (hE : V2.D.ExecutionValid E rho) (hN : V2.D.NoRestart rho) (hDelta : E.Δ = p.Δ)
    (q : Slot)
    {ip : Nat} {x : V} (hx : x ∈ rho.honest)
    (hip : rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams (q + 1))))
    (hseat : rho.seatOf (.prop (q + 1)) ⟨0, Nat.one_pos⟩ = x)
    (b : Block) (raw sup : List (HeadWire p.n)) (rows : List (RowWire p.n))
    (hem : (⟨.seat (.prop (q + 1)) ⟨0, Nat.one_pos⟩, .proposal b raw sup rows⟩ : Obj p) ∈
      rho.emitsAt E ip)
    (hinput : ∀ y ∈ rho.honest, ∀ ih,
      rho.events[ih]? = some (.tick y (SA.voteTime p.toParams (q + 1))) →
      RetainedH6Input p
        (clock p (rho.stateBefore E ip x).st (SA.proposalTime p.toParams (q + 1)))
        (clock p (rho.stateBefore E ih y).st (SA.voteTime p.toParams (q + 1))) (q + 1)) :
    (SA.proposalTime p.toParams (q + 1) < SA.gateTime p.toParams q ∧
      SA.voteTime p.toParams (q + 1) < SA.gateTime p.toParams q) ∧
    Composes E rho ip x (q + 1)
      (controls p (clock p (rho.stateBefore E ip x).st
        (SA.proposalTime p.toParams (q + 1)))).Z b := by
  refine ⟨q1_before_gate p q, ?_⟩
  exact check_H6S E rho hroots hE hN hDelta (q + 1) hx hip hseat b raw sup rows hem hinput

end AvailableChain.FGSA.Run.Tests.RetainedConsumers
