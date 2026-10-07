module
public import AvailableChainFGCompose.Statements.CoreReads
public import AvailableChainKitFG.ClientOnce
public import AvailableChainSimplexFG.Evidence
public import AvailableChainKitFG.CertificateCoreDef
public import AvailableChainGeneric.Statements.V2.Duty.Slashing

@[expose] public section

/-! PROVISIONAL safety contracts. S1 does not freeze these laws. -/

namespace AvailableChain.FGCompose
open AvailableChain.SimplexFG AvailableChain.KitFG
variable {In V : Type} {P : V2.ProtocolSpecD In}
variable {n : Nat} {Base Proposal Wire : Type}
variable (R : FGCoreReads P n Base Proposal Wire)
structure FGSafetyReads (P : V2.ProtocolSpecD In) (n : Nat) (Wire : Type) where
  proposalErase : P.Object → Option Block
  proposalRows : P.Object → List Wire
  encode : Wire → P.Object
  decode : Wire → Option (Row (Fin n))
  decodeObject : P.Object → Option (Row (Fin n))
  fgLabel : P.Label
  fgSeats : Fin n ≃ Fin (P.seats fgLabel)
  record : P.State → RecordOnce
  inputs : P.State → Option (FGBlock (Fin n)) × HeadFields
  enabled : Time → Bool
  finalizedOut : P.State → Block


variable (S : FGSafetyReads P n Wire)
variable (Ef : Electorate (Fin n)) (H : FGHeightView (Fin n))
variable (f : FGFinalityView (Fin n)) (cfg : FGConfig)
variable [DecidableEq V] (E : Generic.Env V) (rho : V2.D.Run V P)

def safetyFinalizedAt (K T : FGBlock (Fin n)) (h : Nat) : Prop :=
  (f K).F = T ∧ (f K).h_F = h

theorem safetyFinalizedAt_def (K T : FGBlock (Fin n)) (h : Nat) :
    safetyFinalizedAt f K T h =
      ((f K).F = T ∧ (f K).h_F = h) := rfl

def safetyRunBlock (K : FGBlock (Fin n)) : Prop :=
  ∃ o b, S.proposalErase o = some b ∧
    ((∃ x t, V2.D.Run.emits E rho x o t) ∨
      (∃ x t, V2.Event.deliver x o t ∈ rho.events)) ∧
    Block.Preceq (R.erase K) b

theorem safetyRunBlock_def (K : FGBlock (Fin n)) :
    safetyRunBlock R S E rho K =
      (∃ o b, S.proposalErase o = some b ∧
    ((∃ x t, V2.D.Run.emits E rho x o t) ∨
      (∃ x t, V2.Event.deliver x o t ∈ rho.events)) ∧
    Block.Preceq (R.erase K) b) := rfl

def safetyRows (nd : P.State) : Finset (Row (Fin n)) :=
  (R.core nd).fg.TF.biUnion chainRows

theorem safetyRows_def (nd : P.State) :
    safetyRows R nd =
      ((R.core nd).fg.TF.biUnion chainRows) := rfl

def safetyEmits (x : V) (a : Wire) : Prop :=
  ∃ k t, rho.events[k]? = some (.tick x t) ∧
    S.encode a ∈ V2.D.Run.emitsAt E rho k

theorem safetyEmits_def (x : V) (a : Wire) :
    safetyEmits S E rho x a =
      (∃ k t, rho.events[k]? = some (.tick x t) ∧
    S.encode a ∈ V2.D.Run.emitsAt E rho k) := rfl

def safetyHolder (i : Fin n) : V := rho.seatOf S.fgLabel (S.fgSeats i)

omit [DecidableEq V] in
theorem safetyHolder_def (i : Fin n) :
    safetyHolder S rho i =
      (rho.seatOf S.fgLabel (S.fgSeats i)) := rfl

def safetyCarriage (A : Finset (Row (Fin n))) : Prop :=
  ∀ u ∈ A, ∃ a, S.decode a = some u ∧
    (safetyHolder S rho u.signer ∈ rho.honest →
      safetyEmits S E rho (safetyHolder S rho u.signer) a)

theorem safetyCarriage_def (A : Finset (Row (Fin n))) :
    safetyCarriage S E rho A =
      (∀ u ∈ A, ∃ a, S.decode a = some u ∧
    (safetyHolder S rho u.signer ∈ rho.honest →
      safetyEmits S E rho (safetyHolder S rho u.signer) a)) := rfl

def safetyNoSlash (x : V) : Prop :=
  ∀ a b, safetyEmits S E rho x a → safetyEmits S E rho x b →
    ∀ u v, S.decode a = some u → S.decode b = some v → ¬ Slashable u v

theorem safetyNoSlash_def (x : V) :
    safetyNoSlash S E rho x =
      (∀ a b, safetyEmits S E rho x a → safetyEmits S E rho x b →
    ∀ u v, S.decode a = some u → S.decode b = some v → ¬ Slashable u v) := rfl

def safetyBound : Prop :=
  ∀ K W, safetyRunBlock R S E rho K → safetyRunBlock R S E rho W →
    ¬ HasSlashableWeightBetween Ef (chainRows K) (chainRows W)

theorem safetyBound_def :
    safetyBound R S Ef E rho =
      (∀ K W, safetyRunBlock R S E rho K → safetyRunBlock R S E rho W →
    ¬ HasSlashableWeightBetween Ef (chainRows K) (chainRows W)) := rfl

def safetyInputAt (x : V) (k : Nat) :
    Option (Option (FGBlock (Fin n)) × HeadFields) :=
  match rho.events[k]? with
  | some (.tick y t) =>
      if y = x ∧ E.awake x t = true ∧ S.enabled t = true then
        some (S.inputs (P.clock (V2.D.Run.stateBefore E rho k x) t))
      else none
  | _ => none

theorem safetyInputAt_def (x : V) (k : Nat) :
    safetyInputAt S E rho x k =
      (match rho.events[k]? with
  | some (.tick y t) =>
      if y = x ∧ E.awake x t = true ∧ S.enabled t = true then
        some (S.inputs (P.clock (V2.D.Run.stateBefore E rho k x) t))
      else none
  | _ => none) := rfl

def safetyRecordStep (rec : RecordOnce) (o : P.Object) : RecordOnce :=
  match S.decodeObject o with
  | some u => record_row_once rec u
  | none => rec

theorem safetyRecordStep_def (rec : RecordOnce) (o : P.Object) :
    safetyRecordStep S rec o =
      (match S.decodeObject o with
  | some u => record_row_once rec u
  | none => rec) := rfl

/-- A decoded own object records its row. -/
theorem safetyRecordStep_some {rec : RecordOnce} {o : P.Object} {u : Row (Fin n)}
    (h : S.decodeObject o = some u) : safetyRecordStep S rec o = record_row_once rec u := by
  rw [safetyRecordStep_def, h]

/-- An own object that decodes to no row leaves the record unchanged. -/
theorem safetyRecordStep_none {rec : RecordOnce} {o : P.Object}
    (h : S.decodeObject o = none) : safetyRecordStep S rec o = rec := by
  rw [safetyRecordStep_def, h]

/-- The client input of a node at its own tick. -/
theorem safetyInputAt_tick {x : V} {k : Nat} {t : Time}
    (h : rho.events[k]? = some (.tick x t)) :
    safetyInputAt S E rho x k =
      if E.awake x t = true ∧ S.enabled t = true then
        some (S.inputs (P.clock (V2.D.Run.stateBefore E rho k x) t)) else none := by
  rw [safetyInputAt_def, h]
  dsimp only
  by_cases hc : E.awake x t = true ∧ S.enabled t = true
  · rw [ite_eq_left ⟨rfl, hc⟩, ite_eq_left hc]
  · rw [ite_eq_right (fun h' => hc h'.2), ite_eq_right hc]

/-- No client input at an index that is not a tick of the node. -/
theorem safetyInputAt_other {x : V} {k : Nat}
    (h : ∀ t, rho.events[k]? ≠ some (.tick x t)) : safetyInputAt S E rho x k = none := by
  rw [safetyInputAt_def]
  cases hk : rho.events[k]? with
  | none => rfl
  | some e =>
    cases e with
    | restart y t => rfl
    | deliver y o t => rfl
    | tick y t =>
      dsimp only
      rw [ite_eq_right]
      rintro ⟨rfl, -⟩
      exact h t hk

end AvailableChain.FGCompose
end
