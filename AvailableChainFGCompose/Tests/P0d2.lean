module
public import AvailableChainFGCompose.Proofs.RowPermission

set_option linter.privateModule false

public section
namespace AvailableChain.FGCompose.Tests.P0d2
open AvailableChain.SimplexFG AvailableChain.KitFG

private abbrev d2g_E : Electorate (Fin 1) := ⟨fun _ => 1, fun _ => by decide⟩
private abbrev d2g_cfg : FGConfig := ⟨4⟩
private abbrev d2g_hd : HeadFields := ⟨0, genesisRoot, 0⟩
private abbrev d2g_row : Row (Fin 1) := ⟨0, .vote 1 genesisRoot false, none⟩
private abbrev d2g_old : RecordOnce := record_row_once RecordOnce.initial d2g_row

-- Inhabited pure client inputs. These are not ExecutionValid protocol fixtures.
private theorem d2g_fresh_send :
    (createRowOnce d2g_E d2g_cfg RecordOnce.initial 0 (some .genesis) d2g_hd).1 =
      some d2g_row := by decide +kernel

private theorem d2g_pair_permission :
    namedEntry (height_pair Record.initial (some (1, genesisRoot)) none) =
      some (1, genesisRoot) :=
  p0d2_pair_of_lock _ _ _ _ (Or.inl rfl)

private theorem d2g_fresh_coverage :
    (∃ a, (createRowOnce d2g_E d2g_cfg RecordOnce.initial 0 (some .genesis) d2g_hd).1 =
      some a ∧ namedEntry a.height_pair = some (1, genesisRoot)) ∨
      ∃ b ∈ RecordOnce.initial.sent, namedEntry b.1 = some (1, genesisRoot) := by
  apply p0d2_once_coverage d2g_E d2g_cfg RecordOnce.initial 0 (some .genesis) d2g_hd
    1 genesisRoot recordInv_initial
  · intro g U timeout fp hm
    cases hm
  · exact d2g_pair_permission

private theorem d2g_prior_history : FGRowRecordHistory d2g_old := by
  constructor
  · exact (recordInv_createRowOnce d2g_E d2g_cfg (Λ := RecordOnce.initial) recordInv_initial
      0 (some .genesis) d2g_hd)
  · intro g U timeout fp hm
    change (.vote g U timeout, fp) ∈ [d2g_row.onceKey] at hm
    have he := List.mem_singleton.mp hm
    have hg : g = 1 := by cases he; rfl
    have hU : U = genesisRoot := by cases he; rfl
    have ht : timeout = false := by cases he; rfl
    subst g U timeout
    exact ⟨fun _ => rfl, fun h => Bool.noConfusion h⟩

private theorem d2g_prior_coverage :
    ∃ b ∈ d2g_old.sent, namedEntry b.1 = some (1, genesisRoot) := by
  have hp : namedEntry (height_pair d2g_old.toRecord (some (1, genesisRoot))
      (finality_pair d2g_old.toRecord d2g_hd)) = some (1, genesisRoot) := by
    decide +kernel
  rcases p0d2_once_coverage d2g_E d2g_cfg d2g_old 0 (some .genesis) d2g_hd
      1 genesisRoot d2g_prior_history.invariant d2g_prior_history.sent_history hp with
      ⟨a, ha, _⟩ | hold
  · have hn : (createRowOnce d2g_E d2g_cfg d2g_old 0 (some .genesis) d2g_hd).1 = none := by
      decide +kernel
    rw [hn] at ha
    cases ha
  · exact hold

-- Negative control: permission cannot imply a fresh send after a prior identical row.
private theorem d2g_prior_no_fresh :
    (createRowOnce d2g_E d2g_cfg d2g_old 0 (some .genesis) d2g_hd).1 = none := by
  decide +kernel

-- Negative control: a different lock at the selected height blocks the computed pair.
private theorem d2g_wrong_lock :
    let Λ := Record.initial.with_lock 1 ⟨9⟩
    ¬ (own_lock Λ 1 none = none ∨ own_lock Λ 1 none = some genesisRoot) ∧
      namedEntry (height_pair Λ (some (1, genesisRoot)) none) = none := by
  decide +kernel

-- A durable resume keeps the full sent key and suppresses the same entry.
private theorem d2g_durable_resume :
    clientRunOnce d2g_E d2g_cfg 0
      (clientRecordOnce d2g_E d2g_cfg 0 RecordOnce.initial [(some .genesis, d2g_hd)])
      [(some .genesis, d2g_hd)] = [] := by
  decide +kernel

#print axioms d2g_fresh_send
#print axioms d2g_pair_permission
#print axioms d2g_fresh_coverage
#print axioms d2g_prior_history
#print axioms d2g_prior_coverage
#print axioms d2g_prior_no_fresh
#print axioms d2g_wrong_lock
#print axioms d2g_durable_resume
#print axioms AvailableChain.FGCompose.rowPermission_covered

end AvailableChain.FGCompose.Tests.P0d2
end
