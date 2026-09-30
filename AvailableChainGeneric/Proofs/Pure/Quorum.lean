module
public import AvailableChainGeneric.Statements.Pure.Quorum

public section

/-! G01 count facts, adopted by DC in GLY r3.15 and r3.16:
`claude-files/a0/archive/generic-layer-r3.16-4e3cf44c.md:9–32`. -/

namespace AvailableChain.Gen.Pure

/-- The recovery count bound gives an honest quorum intersection. -/
theorem count_rec {n a : Nat} (hn : 0 < n) (hf : a ≤ (n - 1) / 3) : FaultX n a := by
  constructor
  rw [qF_def]
  let q := (2 * n + 2) / 3
  have ha : a * 3 < n :=
    Nat.lt_of_le_of_lt ((Nat.le_div_iff_mul_le (by decide)).mp hf)
      (Nat.sub_lt hn (by decide))
  have hq : 2 * n ≤ 3 * q := by
    apply Nat.le_of_add_le_add_right (b := 2)
    calc
      2 * n + 2 = 3 * q + (2 * n + 2) % 3 := (Nat.div_add_mod _ _).symm
      _ ≤ 3 * q + 2 :=
        Nat.add_le_add_left (Nat.le_of_lt_succ (Nat.mod_lt _ (by decide))) _
  have hmul : (a + n) * 3 < (2 * q) * 3 := by
    calc
      (a + n) * 3 = a * 3 + n * 3 := Nat.add_mul _ _ _
      _ < n + n * 3 := Nat.add_lt_add_right ha _
      _ = (2 * n) * 2 := by
        simp [Nat.mul_succ, Nat.succ_mul, Nat.add_left_comm, Nat.add_comm]
      _ ≤ (3 * q) * 2 := Nat.mul_le_mul_right _ hq
      _ = (2 * q) * 3 := by
        simp only [Nat.mul_left_comm, Nat.mul_comm]
  exact Nat.lt_of_not_le fun hle =>
    Nat.not_le_of_gt hmul (Nat.mul_le_mul_right 3 hle)

/-- An honest count above the faulty count gives an honest quorum member. -/
theorem count_clean {n a h : Nat} (hah : a < h) (hhn : h ≤ n - a) : FaultQ n a := by
  constructor
  rw [qF_def]
  have han : a < n :=
    Nat.sub_pos_iff_lt.mp (Nat.lt_of_lt_of_le (Nat.lt_of_le_of_lt (Nat.zero_le a) hah) hhn)
  have hsum : a + a < n :=
    Nat.lt_of_lt_of_le (Nat.add_lt_add_right hah a)
      ((Nat.le_sub_iff_add_le (Nat.le_of_lt han)).mp hhn)
  apply Nat.lt_of_succ_le
  apply (Nat.le_div_iff_mul_le (by decide)).mpr
  calc
    (a + 1) * 3 ≤ (a + 1) * 4 := Nat.mul_le_mul_left _ (by decide)
    _ = 2 * (a + a + 1) + 2 := by
      simp [Nat.mul_succ, Nat.succ_mul, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
    _ ≤ 2 * n + 2 := Nat.add_le_add_right (Nat.mul_le_mul_left _ hsum) _

end AvailableChain.Gen.Pure
