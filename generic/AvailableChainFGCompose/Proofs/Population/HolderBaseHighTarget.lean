module
public import AvailableChainFGCompose.Statements.FinalityRecords
public import AvailableChainFGCompose.Proofs.RowPermission
public import AvailableChainKitFG.ProvenanceCore
public import AvailableChainKitFG.StoreSafetyDef
public import AvailableChainFGCompose.Proofs.SafetyClient
public import AvailableChainGeneric.Proofs.V2.Duty.Fields

public section

namespace AvailableChain.FGCompose
open AvailableChain.SimplexFG AvailableChain.KitFG

variable {In V : Type} {P : V2.ProtocolSpecD In} [DecidableEq V]
variable {n : Nat} {Base Proposal Wire : Type}
variable {R : FGCoreReads P n Base Proposal Wire} {S : FGSafetyReads P n Wire}
variable {O : FGObservationReads R} {T : FGTiming}
variable {E : Generic.Env V} {rho : V2.D.Run V P}
variable {D : FGHistoryWireReads S} {Ef : Electorate (Fin n)} {cfg : FGConfig}
variable {pt : FGServicePoint}
variable (hh : ∀ horizon, FGHistoricalHighChain R O T E rho pt horizon)
variable (cert : FGCertificateLaws Ef O.height O.finality)
variable (hreflect : ∀ A B, Block.Preceq (R.erase A) (R.erase B) → FGBlock.Preceq A B)
variable {storedCarrier : P.State → FGBlock (Fin n) → Wire → Prop}
variable {SourceService : V → Nat → FGBlock (Fin n) → Prop}
variable (hqc : RQCOrigin R S E rho O T storedCarrier SourceService Ef)
variable (hhead : HighRecordHead R S O E rho)
variable (hsrc : ∀ nd, (S.inputs nd).1 = R.source nd)
variable (hheight : ∀ C, ((derive Ef cfg C).h, (derive Ef cfg C).T_h.root) =
  ((O.height C).h, (O.height C).T_h.root))
variable (J : FGSafetyClientLaws S Ef cfg)
variable (emission : HighRecordEmission S T E rho Ef cfg)
variable (hown : HighRecordOwnOrigin S T E rho)
variable (hnames : HighRecordNames R S O T E rho D)

private theorem d7r_height_pair_some_def (Λ : Record) (y : Nat) (T : BlockId)
    (fp : Option FinalityPair) : height_pair Λ (some (y, T)) fp =
      if Λ.timeout y then .vote y T true else
        match own_lock Λ y fp with
        | some locked => if locked = T then .vote y T false else .empty
        | none => match Λ.target y with
          | some recorded => if recorded = T then .vote y T false else .vote y T true
          | none => .vote y T false := rfl

theorem high_record_target_choice_core (Λ : Record) (y : Nat) (T : BlockId)
    (fp : Option FinalityPair)
    (ht : Λ.target y = none ∨ Λ.target y = some T)
    (hn : Λ.timeout y = false)
    (hl : Λ.lock y = none ∨ Λ.lock y = some T)
    (hf : ∀ f, fp = some f → f.height = y → f.target = T) :
    height_pair Λ (some (y, T)) fp = .vote y T false := by
  have hol : own_lock Λ y fp = none ∨ own_lock Λ y fp = some T := by
    cases hp : fp with
    | none => simpa only [own_lock, hp] using hl
    | some f =>
      by_cases hy : f.height = y
      · right; simp only [own_lock, hy, ite_true, hf f hp hy]
      · simpa only [own_lock, hp, hy, ite_false] using hl
  rw [d7r_height_pair_some_def]
  simp only [hn, Bool.false_eq_true, ite_false]
  rcases hol with hol | hol
  · rw [hol]
    rcases ht with ht | ht <;> simp [ht]
  · simp [hol]

end AvailableChain.FGCompose
end
