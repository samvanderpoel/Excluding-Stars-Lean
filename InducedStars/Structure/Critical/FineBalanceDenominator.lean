import InducedStars.Structure.Critical.FineBalanceReferenceTransfer
import InducedStars.Structure.Critical.FineBalanceReferenceComparison

/-!
# Reference-mass normalization for conditional fine balance

These bounds compare the same fixed-sparse, fixed-remainder reference mass
with exact displayed pairs and with the far error.  Feasibility guards are
retained explicitly; no conditional probability is formed with a zero
denominator.
-/

noncomputable section

open Finset Filter Set Topology

namespace InducedStars

noncomputable local instance fineBalanceDenominatorEdgeSetFintype
    {V : Type*} [Fintype V] (G : SimpleGraph V) : Fintype G.edgeSet :=
  Fintype.ofFinite G.edgeSet

/-- The balanced reference mass is nonnegative, including infeasible early
values of the exact critical edge sequence. -/
theorem criticalFixedSparseBalancedCrossSliceMass_nonneg (k n s t : ℕ) :
    0 ≤ criticalFixedSparseBalancedCrossSliceMass k n s t := by
  unfold criticalFixedSparseBalancedCrossSliceMass
  positivity

/-- Rewriting the common missing count into the selected-coordinate count
requires both feasibility guards. -/
theorem criticalFixedSparseBalancedCrossSliceMass_eq_selected
    {k n s t : ℕ}
    (hguard : t + DenseGraph.balancedMultipartiteInternalCapacity
      (k - 1) (n - s) ≤ criticalEdgeCount k n)
    (hupper : criticalEdgeCount k n - t ≤ Nat.choose (n - s) 2) :
    criticalFixedSparseBalancedCrossSliceMass k n s t =
      (Nat.multinomial Finset.univ
        (DenseGraph.balancedPartSize (k - 1) (n - s)) : ℝ) *
      ((DenseGraph.balancedMultipartiteCrossCapacity (k - 1) (n - s)).choose
        (criticalEdgeCount k n - t -
          DenseGraph.balancedMultipartiteInternalCapacity (k - 1) (n - s)) : ℝ) := by
  have ht : t ≤ criticalEdgeCount k n := by omega
  have hmissing : criticalFixedSparseCrossMissingCount k n s t =
      Nat.choose (n - s) 2 - (criticalEdgeCount k n - t) := by
    unfold criticalFixedSparseCrossMissingCount
    omega
  unfold criticalFixedSparseBalancedCrossSliceMass
  rw [hmissing, balanced_choose_missing_eq_selected (by omega) hupper]

/-- Both factors of a feasible balanced reference mass are strictly
positive.  This is a finite statement and does not use totalized division. -/
theorem criticalFixedSparseBalancedCrossSliceMass_pos
    {k n s t : ℕ}
    (hguard : t + DenseGraph.balancedMultipartiteInternalCapacity
      (k - 1) (n - s) ≤ criticalEdgeCount k n)
    (hupper : criticalEdgeCount k n - t ≤ Nat.choose (n - s) 2) :
    0 < criticalFixedSparseBalancedCrossSliceMass k n s t := by
  rw [criticalFixedSparseBalancedCrossSliceMass_eq_selected hguard hupper]
  apply mul_pos
  · exact_mod_cast Nat.multinomial_pos (s := Finset.univ)
      (f := DenseGraph.balancedPartSize (k - 1) (n - s))
  · have htotal := DenseGraph.balancedCross_add_internal (k - 1) (n - s)
    apply Nat.cast_pos.mpr
    apply Nat.choose_pos
    omega

/-- Eventual strict positivity is uniform over the prescribed sparse set
size and every sparse-graph edge count. -/
theorem eventually_criticalFixedSparseBalancedCrossSliceMass_pos
    (k : ℕ) (hk : 3 ≤ k) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ᶠ n : ℕ in atTop,
      ∀ s : ℕ, s ≤ n → (s : ℝ) ≤ delta * n →
      ∀ t : ℕ, t ≤ Nat.choose s 2 →
        0 < criticalFixedSparseBalancedCrossSliceMass k n s t := by
  obtain ⟨delta, hdelta, hreference⟩ :=
    eventually_criticalRetainedSupport_log_choose_lower k hk (by norm_num : (0 : ℝ) < 1)
  refine ⟨delta, hdelta, ?_⟩
  filter_upwards [hreference] with n hn
  intro s hs hsSmall t ht
  obtain ⟨hguard, _hpositive, hfeasible, _hlower⟩ := hn s hs hsSmall t ht
  apply criticalFixedSparseBalancedCrossSliceMass_pos hguard
  have htotal := DenseGraph.balancedCross_add_internal (k - 1) (n - s)
  unfold criticalRetainedSupportSelectedCount criticalRetainedSupportCapacity at hfeasible
  omega

/-- The normalized reference mass is at most the exact displayed pair
family for each prescribed sparse graph. -/
theorem criticalFixedSparseReferenceMass_le_exactPairs
    {k n : ℕ} (hk : 3 ≤ k) (S : Finset (Fin n)) (beta : ℝ)
    (R : SimpleGraph ({v : Fin n | v ∈ S} : Set (Fin n)))
    (hq : k - 1 ≤ fixedSparseCoreCard S)
    (hguard : R.edgeFinset.card +
      DenseGraph.balancedMultipartiteInternalCapacity (k - 1) (n - S.card) ≤
        criticalEdgeCount k n)
    (hupper : criticalEdgeCount k n - R.edgeFinset.card ≤
      Nat.choose (n - S.card) 2)
    (hbalance : ∀ D : SupercriticalDivision k (Fin (fixedSparseCoreCard S)),
      IsExactlyBalancedFullDivision D → IsBalancedFullDivision D beta) :
    criticalFixedSparseBalancedCrossSliceMass k n S.card R.edgeFinset.card ≤
      ((fixedSparseExactlyBalancedCleanCoverPairFinset k n S beta
        (criticalEdgeCount k n - R.edgeFinset.card) R).card : ℝ) := by
  rw [criticalFixedSparseBalancedCrossSliceMass_eq_selected hguard hupper]
  have h := balancedMultinomial_mul_choose_le_fixedSparseExactPairs
    (m := criticalEdgeCount k n - R.edgeFinset.card)
    hk S beta R hq (by unfold fixedSparseCoreCard; omega) hbalance
  exact_mod_cast h

/-- The absolute far-pair bound remains exponentially small relative to the
full balanced reference mass, uniformly in the sparse set and its edge count. -/
theorem eventually_criticalFarPairs_le_fixedSparseReferenceMass
    (k : ℕ) (hk : 3 ≤ k) (tau : ℝ) (htau : 0 < tau) :
    ∃ delta c : ℝ, 0 < delta ∧ 0 < c ∧ ∀ᶠ n : ℕ in atTop,
      ∀ s : ℕ, s ≤ n → (s : ℝ) ≤ delta * n →
      ∀ t : ℕ, t ≤ Nat.choose s 2 →
        ((k ^ n : ℕ) : ℝ) * ((criticalFarGraphFinset k hk n tau).card : ℝ) ≤
          criticalFixedSparseBalancedCrossSliceMass k n s t *
            Real.exp (-(c * (n : ℝ) ^ 2)) := by
  obtain ⟨delta, c, hdelta, hc, hfar⟩ :=
    eventually_criticalFarPairs_le_retainedSupportReference k hk tau htau
  refine ⟨delta, c, hdelta, hc, ?_⟩
  filter_upwards [hfar] with n hn
  intro s hs hsSmall t ht
  apply (hn s hs hsSmall t ht).trans
  apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
  change (Nat.choose
    (DenseGraph.balancedMultipartiteCrossCapacity (k - 1) (n - s))
    (criticalFixedSparseCrossMissingCount k n s t) : ℝ) ≤ _
  unfold criticalFixedSparseBalancedCrossSliceMass
  have hmult : (1 : ℝ) ≤ Nat.multinomial Finset.univ
      (DenseGraph.balancedPartSize (k - 1) (n - s)) := by
    exact_mod_cast Nat.multinomial_pos (s := Finset.univ)
      (f := DenseGraph.balancedPartSize (k - 1) (n - s))
  nlinarith [show (0 : ℝ) ≤ Nat.choose
    (DenseGraph.balancedMultipartiteCrossCapacity (k - 1) (n - s))
    (criticalFixedSparseCrossMissingCount k n s t) by positivity]

/-- Elementary denominator absorption, valid even if the reference mass
or canonical family is empty. -/
theorem criticalFineBalance_reference_le_twice_factorial_of_errors
    {k : ℕ} {B P G E F e₁ e₂ : ℝ}
    (hB : 0 ≤ B) (hreference : B ≤ P)
    (htransfer : P ≤ (k - 1).factorial * G + E + F)
    (hnonunique : E ≤ B * e₁) (hfar : F ≤ B * e₂)
    (herror : e₁ + e₂ ≤ 1 / 2) :
    B ≤ (2 * (k - 1).factorial : ℝ) * G := by
  have habsorb := mul_le_mul_of_nonneg_left herror hB
  nlinarith

end InducedStars
