module
public import AvailableChainFGSA.Model.Spec.Objects

@[expose] public section

namespace AvailableChain.FGSA.Spec

/-- [spec 243–247, 954–960] The pinned spec digest uses Lean's digest at app zero.
No injectivity assumption on the digest is introduced. -/
def digestSpec (p : Params) (parent : BlockId) (slot : Slot)
    (rows : List (RowWire p.n)) (raw support : List (HeadWire p.n)) : BlockId :=
  p.digest ⟨parent, slot, 0, rows, raw, support⟩

/-- [spec 249–258, 954–967] The AC payload check keeps order and duplicates. -/
def validPayload {n : Nat} (s : Slot) (raw support : List (HeadWire n)) : Bool :=
  raw.all (fun v => match v.decode? with
    | some (r, _, _) => r + 1 == s
    | none => false) && support.all (fun v => decide (v ∈ raw))

/-- [spec 249–258] Stateless input checks, including supplied digest equality.
A genesis delivery is refused. Ancestor validation remains a store obligation. -/
def wellFormed (p : Params) (o : Wire p.n) : Bool :=
  match o.decode with
  | some (.vote _ _ _) => true
  | some (.row _ a) => a.valid
  | some (.block s (.node P r root rows raw support)) =>
      s == r && decide (P.slot < r) && validPayload r raw support &&
      rows.all RowWire.valid && root == digestSpec p P.root r rows raw support
  | _ => false

-- Generate equations in their owning model module (BUILD B3a).
private theorem digestSpec_eq_1_export :
    type_of% (@digestSpec.eq_1) := @digestSpec.eq_1
private theorem validPayload_eq_1_export :
    type_of% (@validPayload.eq_1) := @validPayload.eq_1
private theorem wellFormed_eq_1_export :
    type_of% (@wellFormed.eq_1) := @wellFormed.eq_1

end AvailableChain.FGSA.Spec
end
