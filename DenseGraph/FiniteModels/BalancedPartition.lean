import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Nat.Dist
import Mathlib.Tactic

/-!
# Canonical balanced consecutive partitions of `Fin n`

The first `n % r` parts have size `n / r + 1` and the remaining parts have
size `n / r`.  Empty parts are allowed when `r > n`; this is useful for
finite approximations, while `balancedFinPartition_nonempty` records the
usual nonempty regime.
-/

noncomputable section

open Finset
open scoped BigOperators

namespace DenseGraph

/-- The left endpoint of part `i` in the canonical balanced partition. -/
def balancedFinPartitionStart (r n i : ℕ) : ℕ :=
  i * (n / r) + min i (n % r)

@[simp] theorem balancedFinPartitionStart_zero (r n : ℕ) :
    balancedFinPartitionStart r n 0 = 0 := by
  simp [balancedFinPartitionStart]

/-- Successive endpoints differ by the quotient, with one extra vertex in
each of the first `n % r` parts. -/
theorem balancedFinPartitionStart_succ (r n i : ℕ) :
    balancedFinPartitionStart r n (i + 1) =
      balancedFinPartitionStart r n i + n / r +
        (if i < n % r then 1 else 0) := by
  unfold balancedFinPartitionStart
  rw [Nat.add_mul]
  simp only [one_mul]
  split_ifs with hi
  · rw [Nat.min_eq_left hi.le]
    have his : i + 1 ≤ n % r := Nat.succ_le_iff.mpr hi
    rw [Nat.min_eq_left his]
    omega
  · have hi' : n % r ≤ i := Nat.le_of_not_gt hi
    rw [Nat.min_eq_right hi', Nat.min_eq_right (hi'.trans (Nat.le_succ i))]
    omega

theorem balancedFinPartitionStart_mono (r n : ℕ) :
    Monotone (balancedFinPartitionStart r n) := by
  intro i j hij
  unfold balancedFinPartitionStart
  exact Nat.add_le_add (Nat.mul_le_mul_right (n / r) hij)
    (min_le_min hij le_rfl)

/-- The final endpoint is `n`. -/
@[simp] theorem balancedFinPartitionStart_eq_card
    {r n : ℕ} (hr : 0 < r) :
    balancedFinPartitionStart r n r = n := by
  have hmod : n % r < r := Nat.mod_lt n hr
  have hdiv := Nat.mod_add_div n r
  unfold balancedFinPartitionStart
  rw [Nat.min_eq_right hmod.le]
  omega

theorem balancedFinPartitionStart_le_card
    {r n i : ℕ} (hr : 0 < r) (hi : i ≤ r) :
    balancedFinPartitionStart r n i ≤ n := by
  calc
    balancedFinPartitionStart r n i ≤
        balancedFinPartitionStart r n r :=
      balancedFinPartitionStart_mono r n hi
    _ = n := balancedFinPartitionStart_eq_card hr

/-- Part `i` of the canonical balanced consecutive partition of `Fin n`. -/
def balancedFinPartition (r n : ℕ) (i : Fin r) : Finset (Fin n) :=
  Finset.univ.filter fun v ↦
    balancedFinPartitionStart r n i ≤ v.1 ∧
      v.1 < balancedFinPartitionStart r n (i.1 + 1)

@[simp] theorem mem_balancedFinPartition
    {r n : ℕ} {i : Fin r} {v : Fin n} :
    v ∈ balancedFinPartition r n i ↔
      balancedFinPartitionStart r n i ≤ v.1 ∧
        v.1 < balancedFinPartitionStart r n (i.1 + 1) := by
  simp [balancedFinPartition]

/-- The vertices in one part are canonically enumerated from zero. -/
def balancedFinPartitionEquiv
    {r n : ℕ} (hr : 0 < r) (i : Fin r) :
    ↑(balancedFinPartition r n i) ≃
      Fin (balancedFinPartitionStart r n (i.1 + 1) -
        balancedFinPartitionStart r n i) where
  toFun v := ⟨v.1.1 - balancedFinPartitionStart r n i, by
    have hv := (mem_balancedFinPartition.mp v.2)
    omega⟩
  invFun x := ⟨⟨balancedFinPartitionStart r n i + x.1, by
    have hend : balancedFinPartitionStart r n (i.1 + 1) ≤ n :=
      balancedFinPartitionStart_le_card hr (Nat.succ_le_iff.mpr i.2)
    have hx := x.2
    omega⟩, by
      rw [mem_balancedFinPartition]
      have hx := x.2
      change balancedFinPartitionStart r n i ≤
          balancedFinPartitionStart r n i + x.1 ∧
        balancedFinPartitionStart r n i + x.1 <
          balancedFinPartitionStart r n (i.1 + 1)
      omega⟩
  left_inv v := by
    apply Subtype.ext
    apply Fin.ext
    have hv := (mem_balancedFinPartition.mp v.2)
    change balancedFinPartitionStart r n i +
        (v.1.1 - balancedFinPartitionStart r n i) = v.1.1
    exact add_tsub_cancel_of_le hv.1
  right_inv x := by
    apply Fin.ext
    change balancedFinPartitionStart r n i + x.1 -
        balancedFinPartitionStart r n i = x.1
    omega

/-- Exact cardinality as a difference of consecutive endpoints. -/
theorem card_balancedFinPartition_sub
    {r n : ℕ} (hr : 0 < r) (i : Fin r) :
    (balancedFinPartition r n i).card =
      balancedFinPartitionStart r n (i.1 + 1) -
        balancedFinPartitionStart r n i := by
  rw [← Fintype.card_coe]
  simpa using Fintype.card_congr (balancedFinPartitionEquiv hr i)

/-- Exact floor/ceiling cardinality formula. -/
@[simp] theorem card_balancedFinPartition
    {r n : ℕ} (hr : 0 < r) (i : Fin r) :
    (balancedFinPartition r n i).card =
      n / r + if i.1 < n % r then 1 else 0 := by
  rw [card_balancedFinPartition_sub hr,
    balancedFinPartitionStart_succ]
  rw [Nat.add_assoc]
  exact Nat.add_sub_cancel_left _ _

private theorem div_add_one_eq_ceilDiv_of_mod_pos
    {r n : ℕ} (hr : 0 < r) (hmod : 0 < n % r) :
    n / r + 1 = n ⌈/⌉ r := by
  apply le_antisymm
  · rw [Nat.succ_le_iff]
    apply lt_of_not_ge
    intro hceil
    have hnle : n ≤ r * (n / r) :=
      (ceilDiv_le_iff_le_mul hr).mp hceil
    have hdecomp := Nat.mod_add_div n r
    omega
  · rw [ceilDiv_le_iff_le_mul hr, Nat.mul_add]
    have hmodlt := Nat.mod_lt n hr
    have hdecomp := Nat.mod_add_div n r
    omega

/-- Every balanced part has either the floor or the natural ceiling of the
exact quotient `n / r` vertices. -/
theorem card_balancedFinPartition_eq_floor_or_ceil
    {r n : ℕ} (hr : 0 < r) (i : Fin r) :
    (balancedFinPartition r n i).card = n / r ∨
      (balancedFinPartition r n i).card = n ⌈/⌉ r := by
  rw [card_balancedFinPartition hr]
  split_ifs with hi
  · exact Or.inr (div_add_one_eq_ceilDiv_of_mod_pos hr (by omega))
  · exact Or.inl rfl

/-- Exact ceiling bound for the size of every balanced part. -/
theorem card_balancedFinPartition_le_ceilDiv
    {r n : ℕ} (hr : 0 < r) (i : Fin r) :
    (balancedFinPartition r n i).card ≤ n ⌈/⌉ r := by
  rcases card_balancedFinPartition_eq_floor_or_ceil hr i with hfloor | hceil
  · rw [hfloor]
    simpa only [Nat.floorDiv_eq_div] using
      (floorDiv_le_ceilDiv (a := r) (b := n))
  · rw [hceil]

theorem card_balancedFinPartition_le_floor_add_one
    {r n : ℕ} (hr : 0 < r) (i : Fin r) :
    (balancedFinPartition r n i).card ≤ n / r + 1 := by
  rw [card_balancedFinPartition hr]
  split_ifs <;> omega

theorem balancedFinPartition_card_dist_le_one
    {r n : ℕ} (hr : 0 < r) (i j : Fin r) :
    Nat.dist (balancedFinPartition r n i).card
      (balancedFinPartition r n j).card ≤ 1 := by
  rw [card_balancedFinPartition hr, card_balancedFinPartition hr]
  split_ifs <;> simp [Nat.dist]

/-- Distinct consecutive parts are disjoint. -/
theorem balancedFinPartition_pairwiseDisjoint (r n : ℕ) :
    Set.PairwiseDisjoint (Set.univ : Set (Fin r))
      (balancedFinPartition r n) := by
  intro i _ j _ hij
  change Disjoint (balancedFinPartition r n i)
    (balancedFinPartition r n j)
  rw [Finset.disjoint_left]
  intro v hvi hvj
  rw [mem_balancedFinPartition] at hvi hvj
  rcases lt_or_gt_of_ne hij with hij' | hji'
  · have hstart : balancedFinPartitionStart r n (i.1 + 1) ≤
        balancedFinPartitionStart r n j :=
      balancedFinPartitionStart_mono r n (Nat.succ_le_iff.mpr hij')
    omega
  · have hstart : balancedFinPartitionStart r n (j.1 + 1) ≤
        balancedFinPartitionStart r n i :=
      balancedFinPartitionStart_mono r n (Nat.succ_le_iff.mpr hji')
    omega

private theorem sum_extra_balancedFinPartition
    {r n : ℕ} (hr : 0 < r) :
    ∑ i : Fin r, (if i.1 < n % r then 1 else 0) = n % r := by
  rw [← Finset.sum_filter]
  simp [Fin.card_filter_val_lt,
    Nat.min_eq_right (Nat.mod_lt n hr).le]

/-- The balanced consecutive parts cover all of `Fin n`. -/
@[simp] theorem biUnion_balancedFinPartition
    {r n : ℕ} (hr : 0 < r) :
    Finset.univ.biUnion (balancedFinPartition r n) =
      (Finset.univ : Finset (Fin n)) := by
  apply Finset.eq_univ_of_card
  rw [Finset.card_biUnion (by
    simpa using balancedFinPartition_pairwiseDisjoint r n)]
  simp_rw [card_balancedFinPartition hr]
  rw [Finset.sum_add_distrib, sum_extra_balancedFinPartition hr]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  have hdiv := Nat.mod_add_div n r
  simpa [Nat.mul_comm, Nat.add_comm] using hdiv

/-- Every part is nonempty once there are at least as many vertices as
parts. -/
theorem balancedFinPartition_nonempty
    {r n : ℕ} (hr : 0 < r) (hrn : r ≤ n) (i : Fin r) :
    (balancedFinPartition r n i).Nonempty := by
  rw [← Finset.card_pos, card_balancedFinPartition hr]
  have hq : 0 < n / r := Nat.div_pos hrn hr
  split_ifs <;> omega

end DenseGraph
