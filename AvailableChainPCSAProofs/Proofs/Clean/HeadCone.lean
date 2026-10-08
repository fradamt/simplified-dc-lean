module
public import AvailableChainPCSAProofs.Proofs.Clean.Export

public section

/-! The clean HEAD cone from early receipt through the next vote. -/
namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In} {m : FGMode}

/-- Every honest raw voter was awake at the preceding vote, including carried HEADs. -/
theorem pcsa_voter_honest_awake (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (hU : V2.D.UnforgeableSignatures E rho)
    (k : Nat) (x : V) (t : Time) (s : Slot) (j : Fin p.n)
    (hj : rho.seatOf (.base (.head s)) j ∈ rho.honest)
    (hm : j ∈ (GridCO.seats p.n
      (headVotes p (clock p (V2.D.Run.stateBefore E rho k x).st t) (s + 1))).toFinset) :
    E.awake (rho.seatOf (.base (.head s)) j) (SA.voteTime p.toParams s) = true := by
  obtain ⟨o, ho, hoj⟩ := (Gen.AC.Root.vote_pool_mem_seats _ j).mp hm
  have hl := pcsa_headVotes_label p _ (s + 1) o ho
  rw [Nat.add_sub_cancel] at hl
  obtain ⟨r, rfl⟩ := pcsa_count_head_shape o s j hl hoj
  obtain ⟨u, he⟩ := pcsa_voter_input_emission E rho hU k x t s j r hj ho
  exact (pcsa_head_emission_time_awake E rho _ s j r u he).2

end AvailableChain.PCSA.Run

end
