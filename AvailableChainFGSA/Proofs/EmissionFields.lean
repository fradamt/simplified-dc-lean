module
public import AvailableChainFGSA.Proofs.StoreLaws
public import AvailableChainKitFG.ClientOnceSafety

public section

namespace AvailableChain.FGSA

open AvailableChain.SimplexFG AvailableChain.KitFG

/-- The active head supplies the certificate head fields. J4 replaces this proof. -/
theorem fgInputs_headFields (p : Params) (st : State p.n) (Hd : FGBlock (Fin p.n))
    (hhead : fgBlockOf st (fgHead p st) = some Hd) :
    (fgInputs p st).2 = certificateHeadFields (heightView p) (finalityView p) Hd := by
  rw [heightView_eq_simplex, finalityView_eq_simplex, simplex_certificateHeadFields_eq]
  change (match fgBlockOf st (fgHead p st) with
    | some H => HeadFields.ofBlock p.E p.cfg H | none => ⟨0, genesisRoot, 0⟩) = _
  rw [hhead]

/-- A released nonempty finality pair passed the head-field guard and the finality filter. -/
theorem emitted_finality_pair_of_headFields (p : Params) (st : State p.n)
    (Λ : RecordOnce) (seat : Fin p.n) (a : Row (Fin p.n)) (fp : FinalityPair)
    (Hd : FGBlock (Fin p.n)) (hhead : fgBlockOf st (fgHead p st) = some Hd)
    (hemit : (createRowOnce p.E p.cfg Λ seat (fgInputs p st).1 (fgInputs p st).2).1 = some a)
    (hfp : a.finality_pair = some fp) :
    finality_pair Λ.toRecord (certificateHeadFields (heightView p) (finalityView p) Hd) =
      some fp := by
  obtain ⟨_, _, _, _, ha, _, _, _⟩ :=
    createRowOnce_released p.E p.cfg Λ seat (fgInputs p st).1 (fgInputs p st).2 hemit
  rw [ha] at hfp
  rw [← fgInputs_headFields p st Hd hhead]
  exact (Option.filter_eq_some_iff.mp hfp).1

end AvailableChain.FGSA
end
