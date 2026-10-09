module
public import AvailableChainFGSA.Model.Spec.Codec
public import AvailableChainFGSA.Model.Handlers
public import AvailableChainFGSA.Proofs.Carrier
public import AvailableChainFGSA.Proofs.NamedProposal

@[expose] public section

namespace AvailableChain.FGSA.Spec

variable {n : Nat}

@[simp] theorem embed_root (B : Block n) : B.embed.root = B.root := by
  cases B <;> rfl

@[simp] theorem embed_slot (B : Block n) : B.embed.slot = B.slot := by
  cases B <;> rfl

@[simp] theorem embed_parent (B : Block n) : B.embed.parent = B.parent.embed := by
  cases B <;> rfl

/-- Injective on all inputs, including invalid roots, signatures and duplicate lists. -/
theorem embed_injective : Function.Injective (@Block.embed n) := by
  intro A
  induction A with
  | genesis => intro B h; cases B <;> simp_all [Block.embed]
  | node P s r rows raw support ih =>
      intro B h
      cases B with
      | genesis => simp [Block.embed] at h
      | node Q t u rs vs ss =>
          simp only [Block.embed, NamedProposal.node.injEq] at h
          rcases h with ⟨hP, rfl, rfl, _, rfl, rfl, rfl⟩
          rw [ih hP]

/-- Full named ancestry is preserved, including rejected deliveries. -/
theorem embed_preceq (A B : Block n) :
    NamedProposal.preceq A.embed B.embed = Block.preceq A B := by
  induction B with
  | genesis =>
      change decide (A.embed = Block.embed .genesis) = decide (A = .genesis)
      simp only [embed_injective.eq_iff]
  | node P s r rows raw support ih =>
      change (decide (A.embed = (Block.node P s r rows raw support).embed) ||
        NamedProposal.preceq A.embed P.embed) = _
      simp only [embed_injective.eq_iff, ih, Block.preceq]

/-- The FG carrier and named carrier have the same geometry. -/
theorem carrier_embedding (B : Block n) : eraseFG B.toFG = B.embed.erase := by
  induction B with
  | genesis => rfl
  | node P s r rows raw support ih =>
      simp only [Block.toFG, Block.embed, eraseFG, NamedProposal.erase, packBody, ih]

/-- Root order is unchanged; no hash injectivity premise is needed. -/
theorem embed_root_order (A B : Block n) :
    A.embed.root < B.embed.root ↔ A.root < B.root := by simp

/-- Signed carried lists remain byte-for-byte data, in the same order. -/
theorem embed_lists (P : Block n) (s : Slot) (r : BlockId)
    (rows : List (RowWire n)) (raw support : List (HeadWire n)) :
    let N := (Block.node P s r rows raw support).embed
    N.rows = rows ∧ N.raw = raw ∧ N.support = support := ⟨rfl, rfl, rfl⟩

theorem digest_embedding (p : Params) (P : BlockId) (s : Slot)
    (rows : List (RowWire p.n)) (raw support : List (HeadWire p.n)) :
    digestSpec p P s rows raw support = p.digest ⟨P, s, 0, rows, raw, support⟩ := rfl

/-- A supplied wrong digest is still wrong after embedding. -/
theorem content_check_embedding (p : Params) (P : Block p.n) (s : Slot) (r : BlockId)
    (rows : List (RowWire p.n)) (raw support : List (HeadWire p.n)) :
    namedContentOk p (Block.node P s r rows raw support).embed =
      (r == digestSpec p P.root s rows raw support) := by
  have hrows : rowsOk (Block.node P s r rows raw support).embed.erase rows = true := by
    simp [rowsOk, Block.embed, NamedProposal.erase, AvailableChain.Block.body]
  unfold namedContentOk contentOk
  change (rowsOk (Block.node P s r rows raw support).embed.erase rows && _) = _
  rw [hrows, Bool.true_and]
  change (r == p.digest ⟨P.embed.erase.root, s, appOf (packBody 0 rows),
    rows, raw, support⟩) = _
  rw [appOf_packBody, named_erase_root, embed_root]
  rfl


@[simp] theorem wire_embed_auth (o : Wire n) : o.embed.auth = o.auth := rfl

/-- Decoding commutes on every wire, not only well-formed wires. -/
theorem decode_embedding (o : Wire n) :
    o.embed.decode = o.decode.map Input.embed := by
  rcases o with ⟨a, m⟩
  cases a with
  | none => cases m <;> rfl
  | proposer s => cases m <;> rfl
  | seat l i => cases l <;> cases m <;> rfl

theorem wire_embed_injective : Function.Injective (@Wire.embed n) := by
  intro a b h
  rcases a with ⟨aa, am⟩
  rcases b with ⟨ba, bm⟩
  have ha := congrArg Signed.auth h
  have hm := congrArg Signed.payload h
  simp only [wire_embed_auth] at ha
  cases ha
  cases am <;> cases bm <;> simp_all [Wire.embed, embed_injective.eq_iff]

/-- The entire stateless acceptance check commutes, including refusal. -/
theorem wellFormed_embedding (p : Params) (o : Wire p.n) :
    FGSA.wellFormed p o.embed = wellFormed p o := by
  unfold FGSA.wellFormed wellFormed
  rw [decode_embedding]
  cases h : o.decode with
  | none => rfl
  | some i =>
      cases i with
      | vote s i r => rfl
      | row i a => rfl
      | block s B =>
          cases B with
          | genesis => simp [Input.embed, Block.embed, NamedProposal.erase]
          | node P t r rows raw support =>
              change (_ && _ && _ && _ && _ && _ &&
                namedContentOk p (Block.node P t r rows raw support).embed) = _
              rw [content_check_embedding]
              have hs : P.embed.erase.slot = P.slot := by
                rw [named_erase_slot, embed_slot]
              change ((P.embed.erase.node t r (packBody 0 rows) != .genesis) &&
                (s == t) && decide (P.embed.erase.slot < t) && _ && _ && _ && _) = _
              rw [hs]
              have hn : (P.embed.erase.node t r (packBody 0 rows) != .genesis) = true := by
                rfl
              rw [hn, Bool.true_and]
              simp only [validPayload, Bool.and_assoc, Block.embed, NamedProposal.raw,
                NamedProposal.support, NamedProposal.rows, NamedProposal.erase,
                AvailableChain.Block.slot]
              congr 4
              funext v
              cases v.decode? <;> simp only


theorem refusal_embedding (p : Params) (o : Wire p.n) :
    FGSA.wellFormed p o.embed = false ↔ wellFormed p o = false := by
  rw [wellFormed_embedding]

end AvailableChain.FGSA.Spec
end
