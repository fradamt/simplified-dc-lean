module
public import AvailableChainModel.Objects.Blocks

@[expose] public section

/-! The output-property kernel (GLY `claude-files/a0/generic-layer.md`:827–830).
P3 is `fgsa-f0-f2-plan-r3.5-2a9a5877.md`; S3a is
`a0-s3a-claim-inventory-e27f013f.md`, FS2. Both are in
`tip-stability/codex/scratch/`. The bodies below copy S3a:1835–1850;
P3:2658–2663 and :3361–3373 adopt this kernel. Step-2 item I25, D17.
The node predicate N and read predicate A describe sets. The read index
can be an event index or Time. No engine or protocol is required. -/

namespace AvailableChain.Gen.Pure

open AvailableChain

variable {V ι : Type} [Preorder ι] (N : V → Prop)

/-- Outputs of nodes in N are compatible at any two reads in A.
Source: S3a:1837–1839; P3:2660. Consumers: CleanSafety and Healed. -/
def CompatOn (out : ι → V → Block) (A : ι → Prop) : Prop :=
  ∀ i j x y, A i → A j → N x → N y → Block.Compatible (out i x) (out j y)

-- Equation export: BUILD §7.2 B3a; body as in S3a:1839.
omit [Preorder ι] in
theorem CompatOn_def (out : ι → V → Block) (A : ι → Prop) :
    CompatOn N out A =
      (∀ i j x y, A i → A j → N x → N y → Block.Compatible (out i x) (out j y)) := by
  rw [CompatOn]

/-- Outputs of nodes in N are compatible at each read in A.
Source: S3a:1840–1842. Consumer: compatOn_of_compatAt_mono (GLY:828). -/
def CompatAt (out : ι → V → Block) (A : ι → Prop) : Prop :=
  ∀ i x y, A i → N x → N y → Block.Compatible (out i x) (out i y)

-- Equation export: BUILD §7.2 B3a; body as in S3a:1842.
omit [Preorder ι] in
theorem CompatAt_def (out : ι → V → Block) (A : ι → Prop) :
    CompatAt N out A =
      (∀ i x y, A i → N x → N y → Block.Compatible (out i x) (out i y)) := by
  rw [CompatAt]

/-- Each node's output extends between ordered reads in A.
Source: S3a:1843–1844; P3:2661. Consumers: CleanSafety, Healed and SA. -/
def MonoOn (out : ι → V → Block) (A : ι → Prop) : Prop :=
  ∀ i j x, A i → A j → i ≤ j → N x → Block.Preceq (out i x) (out j x)

-- Equation export: BUILD §7.2 B3a; body as in S3a:1844.
theorem MonoOn_def (out : ι → V → Block) (A : ι → Prop) :
    MonoOn N out A =
      (∀ i j x, A i → A j → i ≤ j → N x → Block.Preceq (out i x) (out j x)) := by
  rw [MonoOn]

/-- The lower output is a prefix of the upper output at each read in A.
Source: S3a:1845–1847; P3:2662. Consumer: Healed's F ⪯ S clause. -/
def BelowOn (lo hi : ι → V → Block) (A : ι → Prop) : Prop :=
  ∀ i x, A i → N x → Block.Preceq (lo i x) (hi i x)

-- Equation export: BUILD §7.2 B3a; body as in S3a:1847.
omit [Preorder ι] in
theorem BelowOn_def (lo hi : ι → V → Block) (A : ι → Prop) :
    BelowOn N lo hi A =
      (∀ i x, A i → N x → Block.Preceq (lo i x) (hi i x)) := by
  rw [BelowOn]

/-- B is a prefix of every output of nodes in N at reads in A.
Source: S3a:1848–1850; P3:2663. Consumers: inclusion, P1 and Healed. -/
def ServedOn (out : ι → V → Block) (B : Block) (A : ι → Prop) : Prop :=
  ∀ i x, A i → N x → Block.Preceq B (out i x)

-- Equation export: BUILD §7.2 B3a; body as in S3a:1850.
omit [Preorder ι] in
theorem ServedOn_def (out : ι → V → Block) (B : Block) (A : ι → Prop) :
    ServedOn N out B A =
      (∀ i x, A i → N x → Block.Preceq B (out i x)) := by
  rw [ServedOn]

end AvailableChain.Gen.Pure
