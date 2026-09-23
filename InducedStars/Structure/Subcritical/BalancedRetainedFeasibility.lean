import InducedStars.Structure.Subcritical.BalancedRetainedReference
import DenseGraph.FiniteModels.ProportionalAllocation

/-!
# Exact feasible retained vectors and balanced headroom

Finite allocation in actual retained coordinates. The hypotheses below
are numerical headroom statements, not assumptions of level feasibility.
-/

noncomputable section
open Finset Set
open scoped Classical BigOperators
namespace InducedStars

theorem exists_retainedVector_near_mean {k : ℕ} {V : Type*}
    [Fintype V] [DecidableEq V] (D : SubcriticalDivision k V) (eta : ℝ) (R₀ M : ℕ)
    {p : ℝ} (hp : 0 ≤ p) (hp1 : p < 1)
    (hmean : p * retainedActiveTotalCapacity D eta R₀ = (M : ℝ)) :
    ∃ v : RetainedEdgeCountVector D eta R₀, retainedEdgeCountTotal v = M ∧
      ∀ e, |retainedEdgeCountDensity v e - p| ≤
        1 / (retainedActiveCapacity D eta R₀ e : ℝ) := by
  obtain ⟨a, ha, hsum, herr⟩ := DenseGraph.exists_proportional_allocation
    (retainedActiveCapacity D eta R₀) M hp hp1
    (retainedActiveCapacity_pos D eta R₀) hmean
  let v : RetainedEdgeCountVector D eta R₀ := ⟨a, ha⟩
  refine ⟨v, hsum, ?_⟩
  intro e
  have hN : (0 : ℝ) < retainedActiveCapacity D eta R₀ e := by
    exact_mod_cast retainedActiveCapacity_pos D eta R₀ e
  rw [retainedEdgeCountDensity, div_sub' hN.ne', abs_div, abs_of_pos hN]
  exact (div_le_div_iff_of_pos_right hN).2 (by simpa [v, mul_comm] using herr e)

/-- A centrally located integral mean gives a nonempty exact wide level
and a strictly positive partition function. -/
theorem retainedPartitionFunction_pos_of_mean_headroom {k : ℕ} {V : Type*}
    [Fintype V] [DecidableEq V] (D : SubcriticalDivision k V) (eta : ℝ)
    (R₀ m M : ℕ) (delta : ℝ) (u : ℤ) {p : ℝ}
    (hp : 0 ≤ p) (hp1 : p < 1)
    (hmean : p * retainedActiveTotalCapacity D eta R₀ = (M : ℝ))
    (hid : (retainedCliqueCapacity D eta R₀ : ℤ) + M + u = (m : ℤ))
    (hclose : |p - pK k| ≤ delta)
    (hroom : ∀ e, 1 / (retainedActiveCapacity D eta R₀ e : ℝ) ≤ delta) :
    ∃ v : RetainedEdgeCountVector D eta R₀,
      v ∈ retainedEdgeCountLevel D eta R₀ m delta u ∧
      (∀ e, |retainedEdgeCountDensity v e - pK k| ≤
        |p - pK k| + 1 / (retainedActiveCapacity D eta R₀ e : ℝ)) ∧
      0 < retainedPartitionFunction D eta R₀ m delta u := by
  obtain ⟨v, hv, he⟩ := exists_retainedVector_near_mean D eta R₀ M hp hp1 hmean
  have hbound e : |retainedEdgeCountDensity v e - pK k| ≤
      |p - pK k| + 1 / (retainedActiveCapacity D eta R₀ e : ℝ) := by
    have ht := abs_sub_le (retainedEdgeCountDensity v e) p (pK k)
    linarith [he e]
  have hmem : v ∈ retainedEdgeCountLevel D eta R₀ m delta u := by
    apply mem_retainedEdgeCountLevel.mpr
    refine ⟨by simpa only [hv] using hid, ?_⟩
    intro e
    have h := abs_le.mp ((hbound e).trans (add_le_add hclose (hroom e)))
    constructor <;> linarith
  refine ⟨v, hmem, hbound, ?_⟩
  have hpos : 0 < retainedEdgeCountMultiplicity v := by
    apply Finset.prod_pos
    intro e _
    exact Nat.choose_pos (v.count_le_capacity e)
  exact hpos.trans_le (retainedEdgeCountMultiplicity_le_partitionFunction hmem)

/-- A balanced part is at least half its ideal size once the support has
at least twice as many vertices as parts. This form avoids rounded quotients. -/
theorem balancedFinPartition_twice_card_lower {r q : ℕ} (hr : 0 < r)
    (hq : 2 * r ≤ q) (i : Fin r) :
    (q : ℝ) ≤ 2 * (r : ℝ) * (DenseGraph.balancedFinPartition r q i).card := by
  have hsize : q / r ≤ (DenseGraph.balancedFinPartition r q i).card := by
    rw [DenseGraph.card_balancedFinPartition hr]
    omega
  have hmod : q % r ≤ r := (Nat.mod_lt q hr).le
  have heq := Nat.mod_add_div q r
  have hmul := Nat.mul_le_mul_left r hsize
  have hnat : q ≤ r * (DenseGraph.balancedFinPartition r q i).card + r := by omega
  have hnat2 : 2 * r ≤ q := hq
  have hR : (q : ℝ) ≤ (r : ℝ) * (DenseGraph.balancedFinPartition r q i).card + r := by
    exact_mod_cast hnat
  have hqR : (2 : ℝ) * r ≤ q := by exact_mod_cast hnat2
  nlinarith

theorem balancedRetainedDivision_pair_capacity_lower {k n q : ℕ} (hk : 3 ≤ k)
    (hrq : k - 1 ≤ q) (hqn : q ≤ n) (hq : 2 * (k - 1) ≤ q)
    (e : RetainedActivePair (balancedRetainedDivision hk hrq hqn) 0 n) :
    (q : ℝ)^2 ≤ 4 * ((k - 1 : ℕ) : ℝ)^2 *
      retainedActiveCapacity (balancedRetainedDivision hk hrq hqn) 0 n e := by
  have hl := balancedFinPartition_twice_card_lower (by omega : 0 < k - 1) hq e.left
  have hr := balancedFinPartition_twice_card_lower (by omega : 0 < k - 1) hq e.right
  have hmul := mul_le_mul hl hr (by positivity) (by positivity)
  rw [balancedRetainedDivision_activeCapacity, Nat.cast_mul]
  nlinarith [hmul]

theorem balancedRetainedDivision_total_capacity_lower {k n q : ℕ} (hk : 3 ≤ k)
    (hrq : k - 1 ≤ q) (hqn : q ≤ n) (hq : 2 * (k - 1) ≤ q) :
    (q : ℝ)^2 / 8 ≤ retainedActiveTotalCapacity
      (balancedRetainedDivision hk hrq hqn) 0 n := by
  rw [balancedRetainedDivision_activeTotalCapacity]
  have hr : (2 : ℝ) ≤ (k - 1 : ℕ) := by exact_mod_cast (show 2 ≤ k - 1 by omega)
  have hqR : (2 : ℝ) * (k - 1 : ℕ) ≤ q := by exact_mod_cast hq
  have ha := abs_le.mp (DenseGraph.balancedMultipartiteCrossCapacity_approx
    (q := q) (by omega : 0 < k - 1))
  have hcoef : (q : ℝ)^2 / 4 ≤
      (((k - 1 : ℕ) : ℝ) - 1) * (q : ℝ)^2 / (2 * (k - 1 : ℕ)) := by
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * (k - 1 : ℕ))).2
    nlinarith [mul_nonneg (show 0 ≤ ((k - 1 : ℕ) : ℝ) - 2 by linarith)
      (sq_nonneg (q : ℝ))]
  have hqSq : (8 : ℝ) * (k - 1 : ℕ) ≤ (q : ℝ)^2 := by nlinarith
  linarith [ha.1]

end InducedStars
