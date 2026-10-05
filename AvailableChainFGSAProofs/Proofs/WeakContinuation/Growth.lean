module
public import AvailableChainFGSAProofs.Statements.WeakContinuation
public import AvailableChainFGSAProofs.Proofs.Shared.OutputGrowth
public import AvailableChainFGSAProofs.Proofs.Shared.OutputGrowthProposal
public import AvailableChainFGSAProofs.Proofs.Shared.OutputGrowthCausal
public import AvailableChainFGSAProofs.Proofs.Shared.Reads

public section

/-! WC J3, plan §§6.12–7; DC AvailableChainGrowth.afterGST.
Blueprint 23 §17: the selected cut remains fixed before the continuation gap.
The deadline is exactly t + G' + 6Δ. Safety and inclusion are explicit inputs. -/

namespace AvailableChain.FGSA.Run

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}
    {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}

omit [DecidableEq V] in
/-- WC J3, plan §6.12; DC named public reads: include deliveries after the gate cut. -/
theorem wc_cut_publicRead {u : Slot} {iStar : Nat}
    (hschedule : V2.D.ScheduleWellFormed E rho)
    (hcut : iStar = afterTicksIdx rho (SA.gateTime p.toParams u))
    (t : Time) (ht : SA.gateTime p.toParams u ≤ t) :
    iStar ≤ timeIdx rho t ∧ timeIdx rho t ≤ rho.events.length := by
  refine ⟨?_, List.length_filter_le _ _⟩
  rw [hcut]
  exact (preIdx_le_afterTicksIdx E rho hschedule _).2.trans
    (V2.D.Engine.read_length_mono _ _ ht)

/-- WC J3, plan §7; DC AvailableChainGrowth.afterGST: one actual proposal grows
both getters at the exact deadline. Blueprint 23 §17.2 supplies the eight steps. -/
theorem wc_growth_of_safety_inclusion (ΔF : Time) (u : Slot)
    (Q : Block) (iStar : Nat) : WCGrowthStatement p c E rho ΔF u Q iStar := by
  intro hbase hcut hsafe hincl _ G' hG' hrecurrence t ht hdeadline
  have hd := p.deltaPos
  have h6 : 0 ≤ 6 * p.Δ := mul_nonneg (by decide) hd.le
  have hgap : 0 ≤ G' := (mul_nonneg (by decide : (0 : Time) ≤ 4) hd.le).trans hG'
  have hwindow : t + G' ≤ rho.horizon :=
    (le_add_of_nonneg_right h6).trans hdeadline
  have htD : t ≤ t + G' + 6 * p.Δ :=
    (le_add_of_nonneg_right hgap).trans (le_add_of_nonneg_right h6)
  obtain ⟨s, hfuture, hupper, hh, ha⟩ := hrecurrence t ht hwindow
  have hs := hbase.valid.toScheduleWellFormed
  obtain ⟨B, hprop, hslot⟩ := fgsa_honestProposal_exists_of_awake_slot E rho hs
    hbase.delta hh ha (hupper.trans hwindow)
  have hstart : u + 2 ≤ s := by
    by_contra h
    have hsu : s ≤ u + 1 := by
      simp only [Slot] at h ⊢
      omega
    have hcast : (s : Time) ≤ (u : Time) + 1 := by exact_mod_cast hsu
    have hscaled := mul_le_mul_of_nonneg_left hcast
      (mul_nonneg (by decide : (0 : Time) ≤ 4) hd.le)
    change 4 * p.Δ * (u : Time) + 6 * p.Δ ≤ t at ht
    change t < 4 * p.Δ * (s : Time) at hfuture
    nlinarith
  have hgate : SA.gateTime p.toParams s ≤ t + G' + 6 * p.Δ := by
    change 4 * p.Δ * (s : Time) + 6 * p.Δ ≤ t + G' + 6 * p.Δ
    change 4 * p.Δ * (s : Time) ≤ t + G' at hupper
    simpa only [add_comm] using add_le_add_left hupper (6 * p.Δ)
  have htzero : 0 ≤ t := by
    change 4 * p.Δ * (u : Time) + 6 * p.Δ ≤ t at ht
    exact (add_nonneg
      (mul_nonneg (mul_nonneg (by decide) hd.le) (Nat.cast_nonneg u)) h6).trans ht
  have hreadT := wc_cut_publicRead hs hcut t ht
  have hreadD := wc_cut_publicRead hs hcut (t + G' + 6 * p.Δ) (ht.trans htD)
  have hserved := hincl ⟨s, B⟩ hstart hprop (hgate.trans hdeadline)
  refine ⟨s, B, jointGrowthAt_of_inclusion
    (fun g x a => V2.D.outputAt E rho g x a)
    (fun g => g ∈ [(fgsaInterface p c).stable, (fgsaInterface p c).confirmed])
    (· ∈ rho.honest) (V2.D.proposalTime (fgsaInterface p c))
    (HonestProposal E rho (fgsaInterface p c)) s B t (t + G' + 6 * p.Δ)
    hfuture hprop ?_ ?_ ?_⟩
  · intro g x hg hx
    exact (hsafe.outputs g hg).2 t _ x hreadT.1 hreadD.1 htD hx
  · intro g x hg hx
    exact hserved g hg _ x ⟨hgate, hdeadline⟩ hx
  · intro g x hg _
    exact fgsa_output_noFuture_of_slot E rho hs htzero hfuture hslot.ge g hg x

end AvailableChain.FGSA.Run
end
