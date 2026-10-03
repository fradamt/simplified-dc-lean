module
public import AvailableChainFGSAClaims.Statements.Healed

@[expose] public section

namespace AvailableChain.FGSA.Run

/-- Best H-time conclusion (21:3166–3169; 00:1101–1103), P3 §4.6 D11.
This is a companion (user ruling after the re-freeze); ΔF port of the S4.6c text.
DC: INTENTIONAL family delivery uses ΔF; SA clocks stay unchanged. -/
def HTimeBestConcl (p : Params) {In V : Type} [DecidableEq V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (G ΔF : Time) (g : Nat) : Prop :=
  ∃ w, HealingInput p c E rho w ΔF ∧ tstar p w < E.t_GST + B_bestF p ΔF G g

theorem HTimeBestConcl_def (p : Params) {In V : Type} [DecidableEq V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (G ΔF : Time) (g : Nat) :
    HTimeBestConcl p c E rho G ΔF g =
      (∃ w, HealingInput p c E rho w ΔF ∧ tstar p w < E.t_GST + B_bestF p ΔF G g) := by rfl

end AvailableChain.FGSA.Run
end
