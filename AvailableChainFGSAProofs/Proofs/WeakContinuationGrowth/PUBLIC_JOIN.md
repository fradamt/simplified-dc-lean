# Public companion join: checked, pending lead approval

The theorem below passed Lean against the installed continuation 3 modules. Its axiom
set is exactly propext, Classical.choice, and Quot.sound. It has no additional
proof premise. Install it in Proofs/Assembly/Root.lean after the two named
imports in OPEN.md are approved. This document does not change checker policy.

The lane Export must expose Claims.WeakContinuationGrowth. Root then needs
Assembly.WeakContinuationGrowth and Assembly.WeakContinuationGrowthSeed.
The existing FGSAClaims structure and its frozen weak-continuation field stay
unchanged. The patch includes the component axiom audit. Rerun the full
pre-commit list after integration.

```lean
namespace AvailableChain.FGSA.Run
/-- The corruption-growth companion follows from one source witness and
both retained continuation branches. The frozen FGSAClaims field is unchanged. -/
theorem fgsa_weakContinuationGrowthClaim (p : Params) (G : Time) :
    WeakContinuationGrowthClaim p G := by
  intro V _ _ In c ΔF hδ E source hS
  obtain ⟨w, hcut, hseed⟩ := wcg_sourceWitness (healing_hTimeClaim p) hδ hS
  refine ⟨w.u, w.QStar, afterTicksIdx source (SA.gateTime p.toParams w.u), hcut, ?_⟩
  intro E' rho hc
  rcases hc.covered.lt_or_eq with hne | heq
  · exact wcg_nonemptyLive hS hc hne
      (wcg_retainedSeed hS hc hne hseed hcut.beforeEnd.le)
  · exact wcg_emptyLive hS hc heq.symm hseed hcut.beforeEnd.le
end AvailableChain.FGSA.Run
```

Validation logs before integration:
- `.lake/wcg-c3-final-public-claim.log`: complete proof passes.
- `.lake/wcg-c3-final-public-claim.log`: standard axioms only.
- `PUBLIC_JOIN.patch`: exact unapplied root and checker edits. After approval,
  apply with `git apply --unidiff-zero`.
