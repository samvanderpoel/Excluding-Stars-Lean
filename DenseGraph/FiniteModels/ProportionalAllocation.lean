import DenseGraph.Combinatorics.BinomialLevelShift

/-!
# Exact proportional integer allocation

Rounding a fractional allocation with an integral total needs at most one
additional unit per coordinate. No probability or asymptotic input is used.
-/

noncomputable section
open Finset
open scoped BigOperators Classical
namespace DenseGraph

/-- Distribute an exact integral total with error at most one in every
coordinate, retaining all capacity bounds. Empty index types are allowed. -/
theorem exists_proportional_allocation {I : Type*} [Fintype I]
    (N : I → ℕ) (M : ℕ) {p : ℝ} (hp : 0 ≤ p) (hp1 : p < 1)
    (hN : ∀ i, 0 < N i) (hmean : p * (∑ i, N i : ℕ) = (M : ℝ)) :
    ∃ a : I → ℕ, (∀ i, a i ≤ N i) ∧ (∑ i, a i) = M ∧
      ∀ i, |(a i : ℝ) - p * N i| ≤ 1 := by
  let f : I → ℕ := fun i ↦ Nat.floor (p * N i)
  have hf0 (i : I) : (f i : ℝ) ≤ p * N i := Nat.floor_le (by positivity)
  have hf1 (i : I) : p * N i ≤ (f i : ℝ) + 1 := (Nat.lt_floor_add_one _).le
  have hsum : (∑ i, p * (N i : ℝ)) = (M : ℝ) := by
    rw [← Finset.mul_sum, ← Nat.cast_sum]
    exact hmean
  have hlo : ∑ i, f i ≤ M := by
    exact_mod_cast (show (∑ i, (f i : ℝ)) ≤ (M : ℝ) from
      (Finset.sum_le_sum (fun i _ ↦ hf0 i)).trans_eq hsum)
  have hhi : M ≤ (∑ i, f i) + Fintype.card I := by
    have h := Finset.sum_le_sum (s := (Finset.univ : Finset I)) (fun i _ ↦ hf1 i)
    rw [hsum, Finset.sum_add_distrib] at h
    simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
      ← Nat.cast_sum, ← Nat.cast_add, Nat.cast_le] using h
  obtain ⟨a, ha, hasum⟩ := exists_allocation_of_le_sum (Finset.univ : Finset I)
    (fun _ ↦ 1) (M - ∑ i, f i) (by simpa using (show M - ∑ i, f i ≤ Fintype.card I by omega))
  refine ⟨fun i ↦ f i + a i, ?_, ?_, ?_⟩
  · intro i
    change f i + a i ≤ N i
    have hfi : f i < N i := by
      have hNi : (0 : ℝ) < N i := by exact_mod_cast hN i
      have hlt : (f i : ℝ) < N i := (hf0 i).trans_lt (by nlinarith)
      exact_mod_cast hlt
    have hai := ha i
    omega
  · rw [Finset.sum_add_distrib, hasum]
    omega
  · intro i
    rw [Nat.cast_add, abs_le]
    have hai : (a i : ℝ) ≤ 1 := by exact_mod_cast ha i
    have haz : (0 : ℝ) ≤ a i := by positivity
    constructor <;> linarith [hf0 i, hf1 i]

end DenseGraph
