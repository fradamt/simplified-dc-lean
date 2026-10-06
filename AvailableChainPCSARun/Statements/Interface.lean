module
public import AvailableChainPCSARun.Model.Protocol
public import AvailableChainGeneric.Statements.V2.Duty.PCCompanion

@[expose] public section

/-! [PC-SA claims, W0; FG-SA Run/Statements/Interface.lean] The PC-SA output
interface. The confirmed and stable outputs are the available output
`floor(S, Σ.pc)` (pcsa34-r4 3.2, R7); the strong output is the latest PC
target. The honest-proposal premises of the lane claims and the generic PC
companion read this interface. -/

namespace AvailableChain.PCSA.Run

/-- [PC-SA claims, W0; pcsa34-r4 3.2, R7; FG-SA fgsaInterface] The output
interface of PC-SA: `confirmed` and `stable` read `get_confirmed` (the floor),
`strong` reads `get_strong`. All slots open, as in SA. -/
def pcsaInterface (p : Params) {In : Type} (c : AppCodec In) :
    Gen.V2.Duty.PCInterface (pcsa p c) where
  confirmed nd := confirmed nd.st
  stable nd := stable nd.st
  block m := match m with
    | .proposal N => some N.erase
    | _ => none
  opening _ := True
  propLabel s := .prop s
  propDuty s := .propAction s
  propDuty_label _ := rfl
  propLabel_single _ := rfl
  propLabel_injective := fun _ _ h => RunLabel.prop.inj h
  strong nd := strong nd.st

/-- [PC-SA claims, W0] The finalized output: the erasure of the stored FG block. -/
def pcsaFinalizedOut {p : Params} (nd : Node p) : Block := eraseFG nd.st.fg.F

theorem pcsaFinalizedOut_def {p : Params} (nd : Node p) :
    pcsaFinalizedOut nd = eraseFG nd.st.fg.F := rfl

end AvailableChain.PCSA.Run

end
