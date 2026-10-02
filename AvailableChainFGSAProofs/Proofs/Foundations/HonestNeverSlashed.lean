module
public import AvailableChainFGSAProofs.Proofs.Foundations.ClientOrigin
public import AvailableChainFGSAProofs.Proofs.Foundations.Client
public import AvailableChainFGSARun.Proofs.Slashing

public section

namespace AvailableChain.FGSA.Run

/-- DC `ReviewTheorem.lean:298`, honestNeverSlashed; `Generic/Claims.lean:63`.
Port of the d35bac1 proof to W. Unforgeability traces stored rows to emissions;
Linked attributes each fixed FG seat to its holder (F-H). Client safety
excludes a slashable pair emitted by an honest holder. -/
theorem fgsa_honestNeverSlashed (p : Params) {In : Type} (c : AppCodec In)
    (E : Generic.Env (Fin p.n)) (rho : V2.D.Run (Fin p.n) (fgsa p c))
    (hU : V2.D.UnforgeableSignatures E rho)
    (hL : V2.D.Linked (fgsaFamilies p c).linked rho) :
    Gen.V2.Duty.HonestNeverSlashed (fgsaSlashing p c E) rho := by
  intro v hv hslash
  obtain ⟨e, he, hiff⟩ := fgsaSlashing_slashes_iff_of_linked hL
  obtain ⟨x, y, t, t', hpair⟩ := (hiff v).mp hslash
  obtain ⟨u, hu, u', hu', hsign, hsign', hbad⟩ := hpair
  obtain ⟨W, hW, hu⟩ := Finset.mem_biUnion.mp hu
  obtain ⟨W', hW', hu'⟩ := Finset.mem_biUnion.mp hu'
  obtain ⟨a, ha, har, horigin⟩ := readAt_chain_row_origin p c E rho hU t x W hW u hu
  obtain ⟨a', ha', har', horigin'⟩ :=
    readAt_chain_row_origin p c E rho hU t' y W' hW' u' hu'
  have signer : RowSigner p c rho a v := by
    apply (rowSigner_iff_holder p c rho a v).mpr
    refine ⟨⟨u.signer, har⟩, ?_⟩
    change V2.D.Run.holder rho (ofAuth p a.auth) = some v
    rw [har]
    exact congrArg some ((he u.signer).trans (by rw [hsign]; exact e.apply_symm_apply v))
  have signer' : RowSigner p c rho a' v := by
    apply (rowSigner_iff_holder p c rho a' v).mpr
    refine ⟨⟨u'.signer, har'⟩, ?_⟩
    change V2.D.Run.holder rho (ofAuth p a'.auth) = some v
    rw [har']
    exact congrArg some ((he u'.signer).trans (by rw [hsign']; exact e.apply_symm_apply v))
  exact fgsa_clientSafeAll p c E rho hL v hv a a'
    (horigin v signer hv) (horigin' v signer' hv) u u' ha ha' hbad

end AvailableChain.FGSA.Run
end
