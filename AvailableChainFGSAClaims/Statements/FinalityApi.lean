module
public import AvailableChainFGSAClaims.Statements.Reads
public import AvailableChainFGSA.Statements.FinalityView
public import AvailableChainKitFG.StoreSafetyDef -- shake: keep (Claims policy for row evidence)

@[expose] public section

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

variable (p : Params) {In V : Type} (c : AppCodec In) [DecidableEq V]
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

/-- F-API, dc-align-full.md:78–129; DC L/FinalitySafety.lean:33–103; class: INTENTIONAL.
Observe the selected window carrier certificate.
FG content roots are injective; no root premise is required. -/
def FinalityFinalizedAt (K T : FGBlock (Fin p.n)) (h : Nat) : Prop :=
  (finalityView p K).F = T ∧ (finalityView p K).h_F = h

/-- F-API, dc-align-full.md:78–129; DC L/FinalitySafety.lean:33–103; class: INTENTIONAL.
FG content roots are injective; no root premise is required. -/
theorem FinalityFinalizedAt_def (K T : FGBlock (Fin p.n)) (h : Nat) : FinalityFinalizedAt p K T h =
  ((finalityView p K).F = T ∧ (finalityView p K).h_F = h) := by rfl

/-- F-API, dc-align-full.md:78–129; DC L/FinalitySafety.lean:33–103; class: INTENTIONAL.
FG content roots are injective; no root premise is required. -/
def FinalityBlock (X : FGBlock (Fin p.n)) : Prop :=
  ∃ o b raw sup rows,
    o.payload = Msg.proposal b raw sup rows ∧
    ((∃ x t, V2.D.Run.emits E rho x o t) ∨
      (∃ x t, V2.Event.deliver x o t ∈ rho.events)) ∧
    Block.Preceq (eraseFG X) b

/-- F-API, dc-align-full.md:78–129; DC L/FinalitySafety.lean:33–103; class: INTENTIONAL.
FG content roots are injective; no root premise is required. -/
theorem FinalityBlock_def (X : FGBlock (Fin p.n)) : FinalityBlock p c E rho X =
  (∃ o b raw sup rows,
    o.payload = Msg.proposal b raw sup rows ∧
    ((∃ x t, V2.D.Run.emits E rho x o t) ∨
      (∃ x t, V2.Event.deliver x o t ∈ rho.events)) ∧
    Block.Preceq (eraseFG X) b) := by rfl

/-- F-API, dc-align-full.md:78–129; DC L/FinalitySafety.lean:33–103; class: INTENTIONAL.
FG content roots are injective; no root premise is required. -/
def finalityRows (st : State p.n) : Finset (Row (Fin p.n)) :=
  st.fg.TF.biUnion chainRows

/-- F-API, dc-align-full.md:78–129; DC L/FinalitySafety.lean:33–103; class: INTENTIONAL.
FG content roots are injective; no root premise is required. -/
theorem finalityRows_def (st : State p.n) : finalityRows p st =
  (st.fg.TF.biUnion chainRows) := by rfl

/-- F-API, dc-align-full.md:78–129; DC L/FinalitySafety.lean:33–103; class: INTENTIONAL.
FG content roots are injective; no root premise is required. -/
def FinalitySlashableBound : Prop :=
  ∀ K W, FinalityBlock p c E rho K → FinalityBlock p c E rho W →
    ¬ HasSlashableWeightBetween p.E (chainRows K) (chainRows W)

/-- F-API, dc-align-full.md:78–129; DC L/FinalitySafety.lean:33–103; class: INTENTIONAL.
FG content roots are injective; no root premise is required. -/
theorem FinalitySlashableBound_def : FinalitySlashableBound p c E rho =
  (∀ K W, FinalityBlock p c E rho K → FinalityBlock p c E rho W →
    ¬ HasSlashableWeightBetween p.E (chainRows K) (chainRows W)) := by rfl

/-- F-API, dc-align-full.md:89–92; DC L/FinalitySafety.lean:103; class: INTENTIONAL.
Sorted events are retained. KitFG.rootInjectiveOn_all discharges root freedom. -/
def FinalityExecution : Prop :=
  rho.events.Pairwise (fun a b => a.key ≤ b.key)

omit [DecidableEq V] in
/-- F-API, dc-align-full.md:89–112; DC L/FinalitySafety.lean:61–118;
class: INTENTIONAL. Home equation for the FG observation contract. -/
theorem FinalityExecution_def : FinalityExecution p c rho =
  (rho.events.Pairwise (fun a b => a.key ≤ b.key)) := by rfl

/-- F-API, dc-align-full.md:94–100; DC L/FinalitySafety.lean:61; class: INTENTIONAL.
FG content roots are injective; no root premise is required. -/
def WholeRunAccountable : Prop :=
  (∀ K W T₁ T₂ h₁ h₂,
    FinalityBlock p c E rho K → FinalityBlock p c E rho W →
    FinalityFinalizedAt p K T₁ h₁ → FinalityFinalizedAt p W T₂ h₂ →
    HasSlashableWeightBetween p.E (chainRows K) (chainRows W) ∨
      FGBlock.compatible T₁ T₂ = true) ∧
  (∀ u ∈ rho.honest, ∀ v ∈ rho.honest, ∀ i j,
    HasSlashableWeightBetween p.E (finalityRows p (storeAt p c E rho i u))
      (finalityRows p (storeAt p c E rho j v)) ∨
      FGBlock.compatible (storeAt p c E rho i u).fg.F (storeAt p c E rho j v).fg.F = true) ∧
  (∀ u ∈ rho.honest, ∀ v ∈ rho.honest, ∀ t t',
    HasSlashableWeightBetween p.E (finalityRows p (V2.D.Run.readAt E rho t u).st)
      (finalityRows p (V2.D.Run.readAt E rho t' v).st) ∨
      FGBlock.compatible (V2.D.Run.readAt E rho t u).st.fg.F
        (V2.D.Run.readAt E rho t' v).st.fg.F = true)

/-- F-API, dc-align-full.md:89–112; DC L/FinalitySafety.lean:61–118;
class: INTENTIONAL. Home equation for the FG observation contract. -/
theorem WholeRunAccountable_def : WholeRunAccountable p c E rho =
  ((∀ K W T₁ T₂ h₁ h₂,
    FinalityBlock p c E rho K → FinalityBlock p c E rho W →
    FinalityFinalizedAt p K T₁ h₁ → FinalityFinalizedAt p W T₂ h₂ →
    HasSlashableWeightBetween p.E (chainRows K) (chainRows W) ∨
      FGBlock.compatible T₁ T₂ = true) ∧
  (∀ u ∈ rho.honest, ∀ v ∈ rho.honest, ∀ i j,
    HasSlashableWeightBetween p.E (finalityRows p (storeAt p c E rho i u))
      (finalityRows p (storeAt p c E rho j v)) ∨
      FGBlock.compatible (storeAt p c E rho i u).fg.F (storeAt p c E rho j v).fg.F = true) ∧
  (∀ u ∈ rho.honest, ∀ v ∈ rho.honest, ∀ t t',
    HasSlashableWeightBetween p.E (finalityRows p (V2.D.Run.readAt E rho t u).st)
      (finalityRows p (V2.D.Run.readAt E rho t' v).st) ∨
      FGBlock.compatible (V2.D.Run.readAt E rho t u).st.fg.F
        (V2.D.Run.readAt E rho t' v).st.fg.F = true)) := by rfl

/-- F-API, dc-align-full.md:104–112; DC L/FinalitySafety.lean:83; class: INTENTIONAL.
FG content roots are injective; no root premise is required. -/
def WholeRunAgreement : Prop :=
    (∀ K W T₁ T₂ h₁ h₂, FinalityBlock p c E rho K → FinalityBlock p c E rho W →
      FinalityFinalizedAt p K T₁ h₁ → FinalityFinalizedAt p W T₂ h₂ →
      FGBlock.compatible T₁ T₂ = true) ∧
    (∀ u ∈ rho.honest, ∀ v ∈ rho.honest, ∀ t t',
      FGBlock.compatible (V2.D.Run.readAt E rho t u).st.fg.F
        (V2.D.Run.readAt E rho t' v).st.fg.F = true)

/-- F-API, dc-align-full.md:89–112; DC L/FinalitySafety.lean:61–118;
class: INTENTIONAL. Home equation for the FG observation contract. -/
theorem WholeRunAgreement_def : WholeRunAgreement p c E rho =
  ((∀ K W T₁ T₂ h₁ h₂, FinalityBlock p c E rho K → FinalityBlock p c E rho W →
      FinalityFinalizedAt p K T₁ h₁ → FinalityFinalizedAt p W T₂ h₂ →
      FGBlock.compatible T₁ T₂ = true) ∧
    (∀ u ∈ rho.honest, ∀ v ∈ rho.honest, ∀ t t',
      FGBlock.compatible (V2.D.Run.readAt E rho t u).st.fg.F
        (V2.D.Run.readAt E rho t' v).st.fg.F = true)) := by rfl

end AvailableChain.FGSA.Run
end
