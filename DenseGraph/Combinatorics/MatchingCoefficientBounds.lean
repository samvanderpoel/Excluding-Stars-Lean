import DenseGraph.Combinatorics.MatchingCounting

/-!
# Elementary lower bounds for labeled matching coefficients

The product of odd integers gives a factorial lower bound, and hence an
explicit superexponential-in-the-number-of-edges gain.  No asymptotic
factorial formula is used.
-/

namespace DenseGraph

theorem labeledMatchingCoefficient_eq_descFactorial {t q : ℕ} (hq : 2 * q ≤ t) :
    labeledMatchingCoefficient t q = t.descFactorial (2 * q) / (2 ^ q * q.factorial) := by
  rw [Nat.descFactorial_eq_div hq, Nat.div_div_eq_div_mul]
  simp [labeledMatchingCoefficient, mul_comm, mul_left_comm, mul_assoc]

theorem labeledMatchingCoefficient_mono {t u q : ℕ} (ht : 2 * q ≤ t) (htu : t ≤ u) :
    labeledMatchingCoefficient t q ≤ labeledMatchingCoefficient u q := by
  rw [labeledMatchingCoefficient_eq_descFactorial ht,
    labeledMatchingCoefficient_eq_descFactorial (ht.trans htu)]
  exact Nat.div_le_div_right (Nat.descFactorial_le _ htu)

private theorem factorial_even_eq_odd_product (q : ℕ) :
    (2 * q).factorial = (2 ^ q * q.factorial) *
      ∏ i ∈ Finset.range q, (2 * i + 1) := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [show 2 * (q + 1) = (2 * q + 1) + 1 by omega,
      Nat.factorial_succ, Nat.factorial_succ, ih,
      Finset.prod_range_succ, Nat.pow_succ, Nat.factorial_succ]
    ring

theorem labeledMatchingCoefficient_perfect_eq_product (q : ℕ) :
    labeledMatchingCoefficient (2 * q) q = ∏ i ∈ Finset.range q, (2 * i + 1) := by
  simp only [labeledMatchingCoefficient, Nat.sub_self, Nat.factorial_zero, mul_one]
  rw [factorial_even_eq_odd_product, Nat.mul_div_cancel_left _ (by positivity)]

theorem factorial_le_labeledMatchingCoefficient {t q : ℕ} (hq : 2 * q ≤ t) :
    q.factorial ≤ labeledMatchingCoefficient t q := by
  have hprod : q.factorial ≤ ∏ i ∈ Finset.range q, (2 * i + 1) := by
    clear hq
    induction q with
    | zero => simp
    | succ q ih =>
      rw [Nat.factorial_succ, Finset.prod_range_succ]
      calc
        (q + 1) * q.factorial ≤ (2 * q + 1) * ∏ i ∈ Finset.range q, (2 * i + 1) :=
          Nat.mul_le_mul (by omega) ih
        _ = _ := Nat.mul_comm _ _
  calc
    _ ≤ labeledMatchingCoefficient (2 * q) q := by
      rw [labeledMatchingCoefficient_perfect_eq_product]
      exact hprod
    _ ≤ _ := labeledMatchingCoefficient_mono le_rfl hq

/-- A finite power lower bound yielding `exp(Ω(n log n))` whenever `q` is
linear in `n`.  It includes `q = 0` correctly. -/
theorem half_pow_le_labeledMatchingCoefficient {t q : ℕ} (hq : 2 * q ≤ t) :
    (q / 2) ^ (q - q / 2) ≤ labeledMatchingCoefficient t q := by
  calc
    _ ≤ (q / 2).factorial * (q / 2) ^ (q - q / 2) :=
      Nat.le_mul_of_pos_left _ (Nat.factorial_pos _)
    _ ≤ q.factorial := Nat.factorial_mul_pow_sub_le_factorial (Nat.div_le_self _ _)
    _ ≤ _ := factorial_le_labeledMatchingCoefficient hq

end DenseGraph
