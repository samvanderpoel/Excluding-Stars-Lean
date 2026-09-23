import InducedStars.Structure.Critical.BinomialExpansion

/-!
# Feasibility of critical combined binomial slices

This file isolates the elementary finite bookkeeping needed before applying
the critical second-order binomial comparison.  It records the zero-sparse
identities, proves that feasibility of the shifted selected count supplies
all missing-coordinate guards, and gives a real-valued compact-band transport
lemma for the perturbed slice.
-/

noncomputable section

open Set

namespace InducedStars

/-! ## The zero-sparse slice -/

/-- With no sparse vertices, the maximum combined capacity is the balanced
full-reference capacity. -/
@[simp] theorem criticalMaximumCombinedCapacity_zero_sparse (k n : ℕ) :
    criticalMaximumCombinedCapacity k n 0 =
      criticalTargetCapacity k n := by
  simp [criticalMaximumCombinedCapacity, criticalTargetCapacity]

/-- With no sparse vertices, the common missing-coordinate count is the
complement of the selected count in the full-reference capacity. -/
theorem criticalCombinedMissingCount_zero_sparse
    {k n : ℕ}
    (hreference :
      DenseGraph.balancedMultipartiteInternalCapacity (k - 1) n ≤
        criticalEdgeCount k n)
    (hupper : criticalTargetSelectedCount k n ≤
      criticalTargetCapacity k n) :
    criticalCombinedMissingCount k n 0 =
      criticalTargetCapacity k n - criticalTargetSelectedCount k n := by
  have htotal := DenseGraph.balancedCross_add_internal (k - 1) n
  unfold criticalCombinedMissingCount criticalTargetCapacity
    criticalTargetSelectedCount at *
  simp only [Nat.sub_zero, Nat.choose_zero_succ]
  omega

/-- With no sparse vertices, the selected count in the maximum combined
slice is exactly the selected count in the full balanced reference slice. -/
@[simp] theorem criticalMaximumCombinedSelectedCount_zero_sparse
    {k n : ℕ}
    (hreference :
      DenseGraph.balancedMultipartiteInternalCapacity (k - 1) n ≤
        criticalEdgeCount k n)
    (hupper : criticalTargetSelectedCount k n ≤
      criticalTargetCapacity k n) :
    criticalMaximumCombinedSelectedCount k n 0 =
      criticalTargetSelectedCount k n := by
  rw [criticalMaximumCombinedSelectedCount,
    criticalMaximumCombinedCapacity_zero_sparse,
    criticalCombinedMissingCount_zero_sparse hreference hupper]
  omega

/-! ## Missing-coordinate guards -/

/-- Feasibility of the shifted old selected count supplies all three natural
bookkeeping facts needed by the profile transport: the entire critical edge
count fits in the retained-plus-sparse pair universe, the common missing count
fits in the maximum capacity, and the maximum selected count is exactly
`M + L`.

Unlike `criticalTargetSelectedCount_add_increase_eq_maximum_of_nonempty`, this
result does not require an actual nonempty clean graph fiber. -/
theorem criticalCombinedSlice_missing_feasibility
    {k n s : ℕ}
    (hreference :
      DenseGraph.balancedMultipartiteInternalCapacity (k - 1) n ≤
        criticalEdgeCount k n)
    (hinternal :
      DenseGraph.balancedMultipartiteInternalCapacity (k - 1) (n - s) ≤
        DenseGraph.balancedMultipartiteInternalCapacity (k - 1) n)
    (hshift :
      criticalTargetSelectedCount k n + criticalSelectedIncrease k n s ≤
        criticalMaximumCombinedCapacity k n s) :
    criticalEdgeCount k n ≤
        Nat.choose (n - s) 2 + Nat.choose s 2 ∧
      criticalCombinedMissingCount k n s ≤
        criticalMaximumCombinedCapacity k n s ∧
      criticalMaximumCombinedSelectedCount k n s =
        criticalTargetSelectedCount k n +
          criticalSelectedIncrease k n s := by
  have htotal :=
    criticalMaximumCombinedCapacity_add_balancedInternal k n s
  unfold criticalTargetSelectedCount criticalSelectedIncrease at hshift
  constructor
  · omega
  · constructor
    · unfold criticalCombinedMissingCount
      omega
    · unfold criticalMaximumCombinedSelectedCount
        criticalCombinedMissingCount criticalTargetSelectedCount
        criticalSelectedIncrease
      omega

/-! ## Compact-band transport -/

/-- A generic finite perturbation lemma for the old binomial slice.  If the
reference selected and missing masses are each at least `3 * lambda * N`, and
the total perturbation is at most `lambda * N / 2`, then the perturbed
selected count remains in the compact band of the reduced capacity.

The hypotheses `K ≤ N` and `lambda < 1/2` expose the intended binomial
interpretation even though the polynomial inequalities use only their weaker
nonnegativity consequences. -/
theorem old_binomial_slice_mem_compact_of_triple_margin
    {lambda N M K L : ℝ}
    (hlambda : lambda ∈ Set.Ioo (0 : ℝ) (1 / 2))
    (hN : 0 ≤ N) (hK : 0 ≤ K) (hL : 0 ≤ L) (_hKN : K ≤ N)
    (hselected : 3 * lambda * N ≤ M)
    (hmissing : 3 * lambda * N ≤ N - M)
    (hperturb : 2 * (K + L) ≤ lambda * N) :
    lambda * (N - K) ≤ M + L ∧
      M + L ≤ (1 - lambda) * (N - K) := by
  have hlambda0 : 0 ≤ lambda := hlambda.1.le
  have hlambdaN : 0 ≤ lambda * N := mul_nonneg hlambda0 hN
  have hlambdaK : 0 ≤ lambda * K := mul_nonneg hlambda0 hK
  constructor <;> nlinarith

/-- Critical-natural-number specialization of
`old_binomial_slice_mem_compact_of_triple_margin`.  The exact capacity and
selected-count identities are hypotheses so this lemma remains independent
of how a caller establishes the Taylor guards. -/
theorem criticalMaximumCombinedSelectedCount_mem_compact_of_triple_margin
    {k n s : ℕ} {lambda : ℝ}
    (hlambda : lambda ∈ Set.Ioo (0 : ℝ) (1 / 2))
    (hcapacity : criticalMaximumCombinedCapacity k n s ≤
      criticalTargetCapacity k n)
    (hselectedEq : criticalMaximumCombinedSelectedCount k n s =
      criticalTargetSelectedCount k n + criticalSelectedIncrease k n s)
    (hselected : 3 * lambda * (criticalTargetCapacity k n : ℝ) ≤
      (criticalTargetSelectedCount k n : ℝ))
    (hmissing : 3 * lambda * (criticalTargetCapacity k n : ℝ) ≤
      (criticalTargetCapacity k n : ℝ) -
        (criticalTargetSelectedCount k n : ℝ))
    (hperturb :
      2 * ((criticalCapacityLoss k n s +
        criticalSelectedIncrease k n s : ℕ) : ℝ) ≤
          lambda * (criticalTargetCapacity k n : ℝ)) :
    lambda * (criticalMaximumCombinedCapacity k n s : ℝ) ≤
        (criticalMaximumCombinedSelectedCount k n s : ℝ) ∧
      (criticalMaximumCombinedSelectedCount k n s : ℝ) ≤
        (1 - lambda) *
          (criticalMaximumCombinedCapacity k n s : ℝ) := by
  have htransport := old_binomial_slice_mem_compact_of_triple_margin
    hlambda
    (show (0 : ℝ) ≤ criticalTargetCapacity k n by positivity)
    (show (0 : ℝ) ≤ criticalCapacityLoss k n s by positivity)
    (show (0 : ℝ) ≤ criticalSelectedIncrease k n s by positivity)
    (show (criticalCapacityLoss k n s : ℝ) ≤
        (criticalTargetCapacity k n : ℝ) by
      exact_mod_cast Nat.sub_le
        (criticalTargetCapacity k n)
        (criticalMaximumCombinedCapacity k n s))
    hselected hmissing (by
      simpa only [Nat.cast_add] using hperturb)
  have hcapacityEq := criticalTargetCapacity_sub_loss hcapacity
  have hKle : criticalCapacityLoss k n s ≤
      criticalTargetCapacity k n :=
    Nat.sub_le _ _
  have hcapacityCast :
      (criticalTargetCapacity k n : ℝ) -
          (criticalCapacityLoss k n s : ℝ) =
        (criticalMaximumCombinedCapacity k n s : ℝ) := by
    rw [← Nat.cast_sub hKle]
    exact_mod_cast hcapacityEq
  have hselectedCast :
      (criticalMaximumCombinedSelectedCount k n s : ℝ) =
        (criticalTargetSelectedCount k n : ℝ) +
          (criticalSelectedIncrease k n s : ℝ) := by
    exact_mod_cast hselectedEq
  simpa only [hcapacityCast, hselectedCast] using htransport

end InducedStars
