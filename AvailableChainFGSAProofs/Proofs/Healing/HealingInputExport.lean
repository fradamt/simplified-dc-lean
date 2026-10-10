module
public import AvailableChainFGSAProofs.Proofs.Healing.PostReset
public import AvailableChainFGSAProofs.Proofs.Healing.Time

public section

/-! Blueprint 21 H.18 and H.22; plan S5 J10 E1/E2; B1/B13/B17/B31.
DC: SAME frozen fields and full reset horizon. Each input supplies its
exact field type under the guards of HealingInputOfH0Statement.
The J9 and J11 statements are used without changes. -/

namespace AvailableChain.FGSA.Run

/-- Project full H0 to PostResetStart. All fields come from H0.
This is the converse of PostResetStart.toH0 with its source prefix. -/
theorem healing_postResetStart_of_h0 (p : Params) {In V : Type} [DecidableEq V]
    (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {w : HealingWitness} (h0 : H0 p c E rho w) : PostResetStart p c E rho w :=
  { toH0Reset := h0.toH0Reset
    proposal_lower := h0.proposal_lower
    proposal := h0.proposal
    proposal_first := h0.proposal_first
    after_gst := h0.after_gst }

section
variable (p : Params) (G ΔF : Time)

variable (healed : p.δt = 2 * p.R →
    ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
      (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
      HealingSet p c E rho G ΔF → LivenessBoundW p ΔF →
      recoveryStart p E + B'_resetF p ΔF G + Γ p G + 4 * p.Δ ≤ rho.horizon →
      ∀ w, H0 p c E rho w → Healed p c E rho (tstar p w))

variable (sourcePrefix : p.δt = 2 * p.R →
    ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
      (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
      HealingSet p c E rho G ΔF → LivenessBoundW p ΔF →
      recoveryStart p E + B'_resetF p ΔF G + Γ p G + 4 * p.Δ ≤ rho.horizon →
      ∀ w, H0 p c E rho w → Block.Preceq w.CStar w.QStar)

variable (tHigh : p.δt = 2 * p.R →
    ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
      (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
      HealingSet p c E rho G ΔF → LivenessBoundW p ΔF →
      recoveryStart p E + B'_resetF p ΔF G + Γ p G + 4 * p.Δ ≤ rho.horizon →
      ∀ w, H0 p c E rho w → THigh p c E rho w)

variable (tCarrier : p.δt = 2 * p.R →
    ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
      (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
      HealingSet p c E rho G ΔF → LivenessBoundW p ΔF →
      recoveryStart p E + B'_resetF p ΔF G + Γ p G + 4 * p.Δ ≤ rho.horizon →
      ∀ w, H0 p c E rho w → TCarrier p c E rho w)

variable (rows : p.δt = 2 * p.R →
    ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
      (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
      HealingSet p c E rho G ΔF → LivenessBoundW p ΔF →
      recoveryStart p E + B'_resetF p ΔF G + Γ p G + 4 * p.Δ ≤ rho.horizon →
      TRows p c E rho ΔF)

variable (h2A : p.δt = 2 * p.R →
    ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
      (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
      HealingSet p c E rho G ΔF → LivenessBoundW p ΔF →
      recoveryStart p E + B'_resetF p ΔF G + Γ p G + 4 * p.Δ ≤ rho.horizon →
      ∀ w, H0 p c E rho w → H2A p c E rho w)

variable (h2Prime : p.δt = 2 * p.R →
    ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
      (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
      HealingSet p c E rho G ΔF → LivenessBoundW p ΔF →
      recoveryStart p E + B'_resetF p ΔF G + Γ p G + 4 * p.Δ ≤ rho.horizon →
      ∀ w, H0 p c E rho w → H2Prime p c E rho w)

variable (h3 : p.δt = 2 * p.R →
    ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
      (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
      HealingSet p c E rho G ΔF → LivenessBoundW p ΔF →
      recoveryStart p E + B'_resetF p ΔF G + Γ p G + 4 * p.Δ ≤ rho.horizon →
      ∀ w, H0 p c E rho w → H3 p c E rho w)

variable (h4 : p.δt = 2 * p.R →
    ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
      (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
      HealingSet p c E rho G ΔF → LivenessBoundW p ΔF →
      recoveryStart p E + B'_resetF p ΔF G + Γ p G + 4 * p.Δ ≤ rho.horizon →
      ∀ w, H0 p c E rho w → H4 p c E rho w)

variable (h5 : p.δt = 2 * p.R →
    ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
      (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
      HealingSet p c E rho G ΔF → LivenessBoundW p ΔF →
      recoveryStart p E + B'_resetF p ΔF G + Γ p G + 4 * p.Δ ≤ rho.horizon →
      ∀ w, H0 p c E rho w → H5RawTransfer p c E rho w)

variable (h6 : p.δt = 2 * p.R →
    ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
      (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
      HealingSet p c E rho G ΔF → LivenessBoundW p ΔF →
      recoveryStart p E + B'_resetF p ΔF G + Γ p G + 4 * p.Δ ≤ rho.horizon →
      ∀ w, H0 p c E rho w → H6GateService p c E rho w)

variable (timeBound : p.δt = 2 * p.R →
    ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
      (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
      HealingSet p c E rho G ΔF → LivenessBoundW p ΔF →
      recoveryStart p E + B'_resetF p ΔF G + Γ p G + 4 * p.Δ ≤ rho.horizon →
      ∀ w, H0 p c E rho w → tstar p w ≤ p.actionTime w.rStar + Γ p G + 4 * p.Δ)

include healed sourcePrefix tHigh tCarrier rows h2A h2Prime h3 h4 h5 h6 timeBound

/-- S5 J10 E1: build J11's H.18 interface from J9 C/D.
Each remaining named input has the following planned producer job:
- `healed`: J7 H.18.
- `sourcePrefix`: J7 H.18.
- `tHigh`: J3 rest.
- `tCarrier`: J3 rest.
- `rows`: Foundations RowService.
- `h2A`: J3 rest.
- `h2Prime`: J3 rest.
- `h3`: J6-2 S1 rerun / lf-j6; healing_postReset_exactService from complete-cut PostResetService.
- `h4`: J7 H.18.
- `h5`: J5-A.
- `h6`: J6-2 / lf-j6; healing_postReset_h6GateService.
- `timeBound`: J7 H.18.
Keep h3 and h6 named for a later mechanical swap to the listed lf-j6 producers.
The Healed field supplies no upper time bound, so timeBound remains named. -/
theorem healing_healingInputOfH0 : HealingInputOfH0Statement p G ΔF := by
  rw [HealingInputOfH0Statement_def]
  intro hClock V _ _ In c E rho hSet hLive hHorizon w h0
  have start := healing_postResetStart_of_h0 p c E rho h0
  have t := healing_healT_of p c E rho
    (tHigh hClock c E rho hSet hLive hHorizon w h0)
    (tCarrier hClock c E rho hSet hLive hHorizon w h0)
    (rows hClock c E rho hSet hLive hHorizon)
  have ac := healing_healAC_of p c E rho
    (h2A hClock c E rho hSet hLive hHorizon w h0)
    (h2Prime hClock c E rho hSet hLive hHorizon w h0)
    (h3 hClock c E rho hSet hLive hHorizon w h0)
    (h4 hClock c E rho hSet hLive hHorizon w h0)
    (h5 hClock c E rho hSet hLive hHorizon w h0)
    (h6 hClock c E rho hSet hLive hHorizon w h0)
  exact ⟨healing_healingInput_of p c E rho
    (healed hClock c E rho hSet hLive hHorizon w h0) start
    (sourcePrefix hClock c E rho hSet hLive hHorizon w h0) t ac,
    timeBound hClock c E rho hSet hLive hHorizon w h0⟩

/-- S5 J10 E2: compose E1 with J11 healing_hTime_of.
The planned producer jobs for the same named inputs are:
- `healed`: J7 H.18.
- `sourcePrefix`: J7 H.18.
- `tHigh`: J3 rest.
- `tCarrier`: J3 rest.
- `rows`: Foundations RowService.
- `h2A`: J3 rest.
- `h2Prime`: J3 rest.
- `h3`: J6-2 S1 rerun / lf-j6; healing_postReset_exactService from complete-cut PostResetService.
- `h4`: J7 H.18.
- `h5`: J5-A.
- `h6`: J6-2 / lf-j6; healing_postReset_h6GateService.
- `timeBound`: J7 H.18.
The additional named input `hReset` is ResetArrivalFullStatement: J8 H-RESET (H.11, HG.5).
Keep h3 and h6 named for the later lf-j6 producer swap. -/
theorem healing_hTime_of_inputs (hReset : ResetArrivalFullStatement p G ΔF) :
    HTimeStatement p G ΔF :=
  healing_hTime_of p G ΔF hReset
    (healing_healingInputOfH0 p G ΔF
      healed sourcePrefix tHigh tCarrier rows h2A h2Prime h3 h4 h5 h6 timeBound)

end
end AvailableChain.FGSA.Run
end
