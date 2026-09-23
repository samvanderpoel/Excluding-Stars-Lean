import InducedStars.Structure.Critical.BinomialComparison
import InducedStars.Structure.Critical.DefectAggregation

/-!
# Critical shifted-profile aggregation

The actual division is transported using its division-independent missing
coordinate count.  The reference binomial slice and its compact density band
are uniform in the sparse size; either sign of a support shift is allowed.
All scalar constants depend only on the star size.  This module uses no
strict-supercritical linear absorption gap.
-/

noncomputable section

open Filter Set Topology

namespace InducedStars

/-- The stronger numerical Gaussian estimate supplies the exponent recorded
in the synchronized critical aggregation package. -/
theorem criticalCombinedSliceExponent_le_sparseAggregateExponent
    {k : ℕ} (P : CriticalAggregationParameters k) (n s : ℕ) :
    criticalCombinedSliceExponent k n s ≤ criticalSparseAggregateExponent P n s := by
  unfold criticalCombinedSliceExponent criticalSparseAggregateExponent
  rw [P.cCrit_eq, P.cleanErrorConstant_eq]
  have hnonneg := mul_nonneg (criticalSparsePenaltyConstant_pos P.rank).le
    (sq_nonneg (s : ℝ))
  nlinarith only [hnonneg]

/-- The clean numerical comparison in the exact exponent notation used by
the critical aggregation package. -/
theorem eventually_criticalCombinedSlice_le_parameterExponent
    (k : ℕ) (hk : 3 ≤ k) (P : CriticalAggregationParameters k) :
    ∀ᶠ n : ℕ in atTop, ∀ s : ℕ,
      (s : ℝ) ≤ criticalCombinedSliceDelta k * n →
      (Nat.choose (criticalMaximumCombinedCapacity k n s)
        (criticalMaximumCombinedSelectedCount k n s) : ℝ) ≤
        (criticalReferenceFiberCard k n : ℝ) *
          Real.exp (criticalSparseAggregateExponent P n s) := by
  filter_upwards [eventually_criticalCleanCombinedSlice_le_referenceFiber_with_errors k hk]
    with n hn
  intro s hs
  exact (hn s hs).trans (mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr (criticalCombinedSliceExponent_le_sparseAggregateExponent P n s))
      (by positivity))

/-- The central critical replacement for the strict-supercritical shifted
absorption estimate.  A profile witness at `u+t`, with an admissible number
`t` of sparse edges, is enough to control the entire shifted aggregate. -/
theorem criticalShiftedProfileAggregate_le_referenceFiber
    (k : ℕ) (hk : 3 ≤ k) (P : CriticalAggregationParameters k) :
    ∀ᶠ n : ℕ in atTop,
      ∀ (D : SupercriticalDivision k (Fin n)) (u : ℤ)
        (profile : SupercriticalEdgeProfile D) (t : ℕ),
      (D.sparse.card : ℝ) ≤ P.delta * n / 2 →
      SupercriticalProfileAtShift D (criticalEdgeCount k n)
        (supercriticalOffDiagonal k (gammaK k)) P.delta (u + (t : ℤ)) profile →
      t ≤ Nat.choose D.sparse.card 2 →
      (supercriticalShiftedProfileAggregate D (criticalEdgeCount k n)
        (supercriticalOffDiagonal k (gammaK k)) P.delta u : ℝ) ≤
        (criticalReferenceFiberCard k n : ℝ) *
          Real.exp (criticalShiftedAggregateExponent P n D.sparse.card u) := by
  filter_upwards [criticalShiftedCombinedSlice_le_referenceFiber k hk,
    eventually_criticalCombinedSliceFeasibility k hk] with n hshift hfeasible
  intro D u profile t hsparse hprofile ht
  have hsparseSmall : (D.sparse.card : ℝ) ≤ criticalCombinedSliceDelta k * n := by
    have hδn := mul_le_mul_of_nonneg_right P.critical_slice_delta.le
      (Nat.cast_nonneg (α := ℝ) n)
    have hδn0 := mul_nonneg P.delta_pos.le (Nat.cast_nonneg (α := ℝ) n)
    linarith
  have H := hfeasible D.sparse.card hsparseSmall
  obtain ⟨x, hactual, hdist⟩ := criticalShiftedProfileAggregate_le_maximumSlice
    D profile hprofile ht H.edge_upper H.missing_le
  have hactualReal :
      (supercriticalShiftedProfileAggregate D (criticalEdgeCount k n)
        (supercriticalOffDiagonal k (gammaK k)) P.delta u : ℝ) ≤
      (Nat.choose (criticalMaximumCombinedCapacity k n D.sparse.card) x : ℝ) := by
    exact_mod_cast hactual
  apply (hactualReal.trans (hshift D.sparse.card hsparseSmall x u hdist)).trans
  apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
  unfold criticalShiftedAggregateExponent
  rw [P.cShift_eq]
  linarith only [criticalCombinedSliceExponent_le_sparseAggregateExponent
    P n D.sparse.card]

/-- The same shifted aggregate bound written literally at the critical
cross-edge density `pK k`. -/
theorem criticalShiftedProfileAggregate_le_referenceFiber_pK
    (k : ℕ) (hk : 3 ≤ k) (P : CriticalAggregationParameters k) :
    ∀ᶠ n : ℕ in atTop,
      ∀ (D : SupercriticalDivision k (Fin n)) (u : ℤ)
        (profile : SupercriticalEdgeProfile D) (t : ℕ),
      (D.sparse.card : ℝ) ≤ P.delta * n / 2 →
      SupercriticalProfileAtShift D (criticalEdgeCount k n)
        (pK k) P.delta (u + (t : ℤ)) profile →
      t ≤ Nat.choose D.sparse.card 2 →
      (supercriticalShiftedProfileAggregate D (criticalEdgeCount k n)
        (pK k) P.delta u : ℝ) ≤
        (criticalReferenceFiberCard k n : ℝ) *
          Real.exp (criticalShiftedAggregateExponent P n D.sparse.card u) := by
  simpa only [supercriticalOffDiagonal_at_gammaK k hk] using
    criticalShiftedProfileAggregate_le_referenceFiber k hk P

end InducedStars
