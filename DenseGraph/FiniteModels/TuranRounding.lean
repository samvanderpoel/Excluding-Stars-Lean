import DenseGraph.FiniteModels.BalancedAssignments

/-!
# Finite Turán rounding and multipartite balance

The exact quotient/remainder formula gives a rounding error at most `r / 8`
in the continuous Turán edge count, without a divisibility hypothesis.  A
near-extremal multipartite cross capacity consequently bounds the variance
of the sizes of its parts.  Empty parts are permitted throughout.
-/

noncomputable section

open Finset
open scoped BigOperators

namespace DenseGraph

/-- Twice the continuous-to-finite Turán rounding error is at most `r / 4`.
No divisibility assumption on the number of vertices is required. -/
theorem turanNumber_rounding_le {n r : ℕ} (hr : 0 < r) :
    (n : ℝ) ^ 2 - (n : ℝ) ^ 2 / r -
        2 * (SimpleGraph.turanNumber n r : ℝ) ≤ (r : ℝ) / 4 := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hformula := balancedMultipartiteCrossCapacity_cast_eq (q := n) hr
  rw [balancedMultipartiteCrossCapacity_eq_turanNumber] at hformula
  rw [hformula]
  have heq : (n : ℝ) ^ 2 - (n : ℝ) ^ 2 / r -
      2 * (((r : ℝ) - 1) * (n : ℝ) ^ 2 / (2 * r) -
        ((n % r : ℕ) : ℝ) * ((r : ℝ) - ((n % r : ℕ) : ℝ)) /
          (2 * r)) =
      ((n % r : ℕ) : ℝ) * ((r : ℝ) - ((n % r : ℕ) : ℝ)) / r := by
    field_simp
    ring
  rw [heq]
  apply (div_le_iff₀ hrR).2
  nlinarith [sq_nonneg (((n % r : ℕ) : ℝ) - (r : ℝ) / 2)]

/-- The continuous Turán expression overestimates its finite value by at
most `r / 8`, including graphs whose order is not divisible by `r`. -/
theorem continuous_turanNumber_sub_rounding_le {n r : ℕ} (hr : 0 < r) :
    (n : ℝ) ^ 2 * (1 - 1 / (r : ℝ)) / 2 - (r : ℝ) / 8 ≤
      (SimpleGraph.turanNumber n r : ℝ) := by
  have h := turanNumber_rounding_le (n := n) hr
  have heq : (n : ℝ) ^ 2 * (1 - 1 / (r : ℝ)) =
      (n : ℝ) ^ 2 - (n : ℝ) ^ 2 / r := by ring
  rw [heq]
  linarith

/-- The total squared part sizes are determined by cross capacity. -/
theorem sum_sq_sizeVector_eq {n r : ℕ} (a : Fin r → ℕ)
    (hsum : ∑ i, a i = n) :
    (∑ i, (a i : ℝ) ^ 2) =
      (n : ℝ) ^ 2 - 2 * (multipartiteCrossCapacity a : ℝ) := by
  have hpairs := congrArg (fun z : ℕ ↦ (z : ℝ))
    (multipartiteCrossPairSum_add_sum_choose a)
  rw [hsum, ← multipartiteCrossCapacity_eq_pairSum] at hpairs
  push_cast at hpairs
  simp_rw [Nat.cast_choose_two] at hpairs
  have hsumR : ∑ i, (a i : ℝ) = (n : ℝ) := by exact_mod_cast hsum
  have hchoose : (∑ i, ((a i : ℝ) * ((a i : ℝ) - 1) / 2)) =
      ((∑ i, (a i : ℝ) ^ 2) - (n : ℝ)) / 2 := by
    simp_rw [show ∀ x : ℝ, x * (x - 1) / 2 = (x ^ 2 - x) / 2
      from fun x ↦ by ring]
    rw [← Finset.sum_div, Finset.sum_sub_distrib, hsumR]
  rw [hchoose] at hpairs
  nlinarith

/-- The variance identity for an arbitrary ordered multipartite size vector.
Empty parts are allowed. -/
theorem sum_sq_sub_average_eq {n r : ℕ} (hr : 0 < r)
    (a : Fin r → ℕ) (hsum : ∑ i, a i = n) :
    (∑ i, ((a i : ℝ) - (n : ℝ) / r) ^ 2) =
      (n : ℝ) ^ 2 - (n : ℝ) ^ 2 / r -
        2 * (multipartiteCrossCapacity a : ℝ) := by
  have hsumR : ∑ i, (a i : ℝ) = (n : ℝ) := by exact_mod_cast hsum
  have hrR : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
  simp_rw [sub_sq]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [show (∑ i : Fin r, 2 * (a i : ℝ) * ((n : ℝ) / r)) =
      2 * (n : ℝ) * ((n : ℝ) / r) by
    rw [← Finset.sum_mul, ← Finset.mul_sum, hsumR]]
  rw [sum_sq_sizeVector_eq a hsum]
  field_simp
  ring

/-- A cross-capacity deficit of at most twice `t` from the finite Turán
number bounds the squared deviations of all part sizes from their average.
The `r / 4` term is the exact uniform finite rounding allowance. -/
theorem sum_sq_sub_average_le_of_turan_deficit {n r : ℕ} (hr : 0 < r)
    (a : Fin r → ℕ) (hsum : ∑ i, a i = n) (t : ℕ)
    (hcap : (SimpleGraph.turanNumber n r : ℝ) - 2 * (t : ℝ) ≤
      (multipartiteCrossCapacity a : ℝ)) :
    (∑ i, ((a i : ℝ) - (n : ℝ) / r) ^ 2) ≤
      4 * (t : ℝ) + (r : ℝ) / 4 := by
  rw [sum_sq_sub_average_eq hr a hsum]
  have hround := turanNumber_rounding_le (n := n) hr
  linarith

end DenseGraph
