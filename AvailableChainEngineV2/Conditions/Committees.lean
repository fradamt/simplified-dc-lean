module
public import Mathlib.Data.Fintype.Card
public import AvailableChainEngineV2.Engine.Run

@[expose] public section

/-! Committee models (design §2 E2; plan 2a, Task 2). The run's seat map
`seatOf` is a function; these conditions say which label families have which
committee model. -/

namespace AvailableChain.V2

open AvailableChain

variable {V : Type} {In : Type} {P : ProtocolSpec In}

/-- The label families that a protocol declares (design §2 E2, E5).

* `ap`: the AP labels (`APLabels`). Their payloads and hooks factor through
  the base (the isolation laws).
* `fresh`: the designated fresh family. Regimes put `CStar` on it; its labels
  are never self-visible (separation).
* `linked`: the family with one validator identity across labels (for
  example FG labels). Regimes may put `Linked` on it; its labels may be
  self-visible. -/
structure LabelFamilies (P : ProtocolSpec In) where
  ap : P.Label → Prop
  fresh : P.Label → Prop
  linked : P.Label → Prop

/-- C*: every label of `F` has a bijective seat map, so its seats and the
validators correspond one to one (`CStar.seats_eq`). Seat maps of different
labels are independent. -/
def CStar (F : P.Label → Prop) (rho : Run V P) : Prop :=
  ∀ ℓ, F ℓ → Function.Bijective (rho.seatOf ℓ)

/-- Linked: one bijection `e : Fin N ≃ V` for all labels of `F`. Every label
of `F` has `N` seats, and seat `i` of it is held by `e i` (through
`Fin.cast`), so equal seat indices name one validator across labels. -/
def Linked (F : P.Label → Prop) (rho : Run V P) : Prop :=
  ∃ (N : Nat) (e : Fin N ≃ V), ∀ ℓ, F ℓ →
    ∃ h : P.seats ℓ = N, ∀ i, rho.seatOf ℓ i = e (Fin.cast h i)

/-- Every label of `F` has one seat (for example a proposal duty). The holder
of that seat is run data. -/
def SingleSeat (F : P.Label → Prop) : Prop :=
  ∀ ℓ, F ℓ → P.seats ℓ = 1

/-- `Linked` implies `CStar` on the same family. -/
theorem Linked.toCStar {F : P.Label → Prop} {rho : Run V P} (h : Linked F rho) :
    CStar F rho := by
  obtain ⟨N, e, hF⟩ := h
  intro ℓ hℓ
  obtain ⟨hN, hs⟩ := hF ℓ hℓ
  have hfun : rho.seatOf ℓ = e ∘ Fin.cast hN := funext hs
  rw [hfun]
  exact e.bijective.comp (finCongr hN).bijective

/-- Under C*, a label of `F` has one seat per validator. -/
theorem CStar.seats_eq [Fintype V] {F : P.Label → Prop} {rho : Run V P}
    (h : CStar F rho) {ℓ : P.Label} (hℓ : F ℓ) : P.seats ℓ = Fintype.card V := by
  rw [← Fintype.card_of_bijective (h ℓ hℓ), Fintype.card_fin]

end AvailableChain.V2

end
