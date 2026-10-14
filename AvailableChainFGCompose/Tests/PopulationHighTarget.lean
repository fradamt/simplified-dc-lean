module
public import AvailableChainFGCompose.Proofs.Population.HighTarget

set_option linter.privateModule false
noncomputable section
public section

/-! Generic ordinary event-fold controls. Both honest receivers retain the delivered row.
The first target at round 0 and the deduplicated prior target at round 1 use the same run. -/
namespace AvailableChain.FGCompose.Tests.PopulationHighTarget
open AvailableChain.SimplexFG AvailableChain.KitFG

private abbrev electorate : Electorate (Fin 1) := ⟨fun _ => 1, fun _ => by decide⟩
private abbrev cfg : FGConfig := ⟨4⟩
private abbrev head : HeadFields := ⟨0, genesisRoot, 0⟩
private abbrev row : Row (Fin 1) := ⟨0, .vote 1 genesisRoot false, none⟩
private abbrev protocol : V2.ProtocolSpecD Unit where
  State := RecordOnce × List (V2.Signed Unit (fun _ => 1) (Row (Fin 1)))
  Label := Unit
  Duty := Time
  signLabel _ := ()
  seats _ := 1
  Payload := Row (Fin 1)
  Durable := RecordOnce × List (V2.Signed Unit (fun _ => 1) (Row (Fin 1)))
  init := (RecordOnce.initial, [])
  clock st _ := st
  actTime := id
  duties t := [t]
  duties_spec := by intro d t; simp
  duties_nodup := by intro t; simp
  act st _ _ := (createRowOnce electorate cfg st.1 0 (some .genesis) head).1
  gossip _ _ := []
  process st o := (st.1, o :: st.2)
  selfVisible _ := true
  recordOwn st o := (match o.auth with
    | .none => st.1
    | .seat _ _ => record_row_once st.1 o.payload, o :: st.2)
  durable := id
  restore st _ := st
  wellFormed _ := true
  depsPresent _ _ := true
  processed _ _ := false
  excludes _ _ := false
  handles _ _ _ := False
  carries _ _ := False
private abbrev wire : protocol.Object := ⟨.seat () 0, row⟩
private abbrev old : RecordOnce := record_row_once RecordOnce.initial row
private abbrev decode (o : protocol.Object) : Option (Row (Fin 1)) :=
  match o.auth with | .none => none | .seat _ _ => some o.payload
private abbrev reads : FGSafetyReads protocol 1 protocol.Object where
  proposalErase _ := none
  proposalRows _ := []
  encode := id
  decode := decode
  decodeObject := decode
  fgLabel := ()
  fgSeats := Equiv.refl _
  record := Prod.fst
  inputs _ := (some .genesis, head)
  enabled _ := true
  finalizedOut _ := .genesis
private abbrev core : FGCoreReads protocol 1 Unit Unit protocol.Object where
  core st := ⟨(), Store.init, [], st.2⟩
  erase _ := .genesis
  source _ := some .genesis
  headVote _ _ := .genesis
  finalityHead _ := none
  proposalFG _ _ := none
private abbrev obs : FGObservationReads core where
  height := simplexHeightView electorate cfg
  finality := simplexFinalityView electorate cfg
  controls _ := ⟨.genesis, 1, 0, .genesis, false⟩
  viable _ X := X
private abbrev history : FGHistoryWireReads reads where
  heightPair a := a.payload.height_pair
  finalityPair a := a.payload.finality_pair
  signer a := some a.payload.signer
  decode_height a u hd := by
    cases a with | mk auth payload => cases auth <;> cases hd; rfl
  decode_finality a u hd := by
    cases a with | mk auth payload => cases auth <;> cases hd; rfl
  decode_signer a u hd := by
    cases a with | mk auth payload => cases auth <;> cases hd; rfl
private abbrev timing : FGTiming where
  delta := 1
  roundSlots := 2
  proposal s := 4 * s
  vote s := 4 * s + 1
  early s := 4 * s + 2
  freeze s := 4 * s + 3
  release s := 4 * s + 5
  gate s := 4 * s + 6
  action r := 4 * (r * 2 : Nat) + 6
private abbrev point : FGServicePoint := ⟨⟨0, 0, 0, 0, 0, .genesis⟩, 0, .genesis, 0⟩
private abbrev env (V : Type) : Generic.Env V where
  Δ := 1
  Δ_pos := by decide
  t_GST := 0
  t_GST_nonneg := by decide
  awake _ _ := true
private abbrev run : V2.D.Run Nat protocol where
  honest := {7, 9}
  horizon := 20
  events := [.tick 9 6, .tick 7 6, .deliver 7 wire 7, .deliver 9 wire 7,
    .tick 9 14, .tick 7 14]
  seatOf _ _ := 9
  input _ _ := ()
private abbrev frozenRun : V2.D.Run (Fin 1) protocol where
  honest := Finset.univ
  horizon := 20
  events := [.tick 0 6, .deliver 0 wire 7, .tick 0 14]
  seatOf _ _ := 0
  input _ _ := ()

private theorem global_client_premises_sat : FGSafetyClientLaws reads electorate cfg where
  initial_record := rfl
  clock_record _ _ := rfl
  process_record _ _ := rfl
  restart_record _ _ := rfl
  own_record nd o := by cases o with | mk auth payload => cases auth <;> rfl
  tick_rows E rho e he nd x t := by
    have hx : e 0 = x := by
      rw [← e.apply_symm_apply x]
      congr 1
      exact Subsingleton.elim _ _
    have hs : e.symm x = 0 := Subsingleton.elim _ _
    have hseat : rho.seatOf () 0 = x := (he 0).trans hx
    cases ha : E.awake x t <;>
      cases hr : (createRowOnce electorate cfg nd.1 0 (some .genesis) head).1 <;>
      simp [V2.D.tick, V2.D.Run.ownSeats, List.finRange_succ, ha, hs, hr, hseat]
    rename_i u
    rfl

private theorem mixed_client_premises_sat :
    FGHolderClientLaws reads electorate cfg (env Nat) run (ordinaryFGExecutionObs (env Nat) run)
      (safetyHolder reads run) where
  holder_eq _ := rfl
  holder_inj _ _ _ := Subsingleton.elim _ _
  initial_record := rfl
  record_step x k hk := by
    change k < 18 at hk
    by_cases h9 : x = 9
    · subst x; interval_cases k <;> rfl
    by_cases h7 : x = 7
    · subst x; interval_cases k <;> rfl
    interval_cases k <;>
      simp [ordinaryFGExecutionObs, ordinaryCutState, ordinaryEntry, ordinaryEntryStep,
        ordinaryReleaseStep, V2.D.Run.stateBefore, V2.D.World.step, V2.D.World.init,
        V2.D.tick, V2.D.Run.ownSeats,
        protocol, run, env, reads, h9, h7, Ne.symm h9, Ne.symm h7]
  holder_rows j x t i ht hi := by
    have hx : x = 9 := hi.symm
    subst hx
    have hj : j < 6 := (List.getElem?_eq_some_iff.mp ht).1
    have hi' : i = 0 := Subsingleton.elim _ _
    subst i
    interval_cases j <;> try simp at ht
    · have ht' : t = 6 := by simpa using ht.symm
      subst t
      decide +kernel
    · have ht' : t = 14 := by simpa using ht.symm
      subst t
      decide +kernel
  nonholder_rows j x t ht hn := by
    have hj : j < 6 := (List.getElem?_eq_some_iff.mp ht).1
    interval_cases j <;> try simp at ht
    all_goals
      rcases ht with ⟨rfl, rfl⟩
    · exact False.elim (hn 0 rfl)
    · decide +kernel
    · exact False.elim (hn 0 rfl)
    · decide +kernel

#print axioms global_client_premises_sat
#print axioms mixed_client_premises_sat
end AvailableChain.FGCompose.Tests.PopulationHighTarget
end
