import InducedStars.Structure.Critical.FineBalanceDenominator
import InducedStars.Structure.Critical.FineBalanceNonunique
import InducedStars.Structure.Supercritical.AlmostAllLimits

/-!
# Uniform fixed-sparse reference transfer

This file completes the denominator comparison for one prescribed sparse set
and one prescribed graph on that set.  Exact balanced displayed covers give
the reference mass.  Cover uniqueness transfers all but an exponentially
small fraction to canonical clean graphs, while the rough-structure theorem
absorbs the far displayed pairs.

The close radius is chosen below an arbitrary positive cap.  The resulting
sparse-size radius is deliberately kept local to this theorem; synchronizing
it with the cleanup parameters is a later aggregation step.
-/

noncomputable section

open Filter Finset Set Topology

namespace InducedStars

noncomputable local instance fineBalanceUniformReferenceEdgeSetFintype
    {V : Type*} [Fintype V] (G : SimpleGraph V) : Fintype G.edgeSet :=
  Fintype.ofFinite G.edgeSet

/-- Uniform fixed-sparse denominator transfer.  For every prescribed
induced-star-free graph on a sufficiently small sparse set, the exactly
balanced displayed reference mass is bounded by the actual canonical clean
family with that same sparse induced graph.  The factor `2 (k-1)!` is the
ordered-cover multiplicity together with the absorbed nonunique and far
errors. -/
theorem eventually_criticalFixedSparseBalancedCrossSliceMass_le_canonical
    (k : ℕ) (hk : 3 ≤ k) {tauCap : ℝ} (hCap : 0 < tauCap) :
    ∃ tau delta : ℝ,
      0 < tau ∧ tau ≤ tauCap ∧ 0 < delta ∧
        ∀ᶠ n : ℕ in atTop,
          ∀ (hn : k - 1 ≤ n) (S : Finset (Fin n)),
            (S.card : ℝ) ≤ delta * (n : ℝ) →
            ∀ R : SimpleGraph ({v : Fin n | v ∈ S} : Set (Fin n)),
              ¬ Regularity.InducedEmbeds (inducedStar k) R →
              criticalFixedSparseBalancedCrossSliceMass
                  k n S.card R.edgeFinset.card ≤
                (2 * (k - 1).factorial : ℝ) *
                  ((criticalFixedRemainderCanonicalCleanGraphFinset
                    k hk n tau hn S R).card : ℝ) := by
  obtain ⟨tau, htau, htauCap, hcanonical⟩ :=
    eventually_fixedSparseExactPair_mem_canonical_of_close_below
      k hk hCap
  obtain ⟨deltaNonunique, hdeltaNonunique, cNonunique, hcNonunique,
      hnonunique⟩ :=
    eventually_criticalFixedSparseBalancedNonunique_le_balancedMass k hk
  obtain ⟨deltaFar, cFar, hdeltaFar, hcFar, hfar⟩ :=
    eventually_criticalFarPairs_le_fixedSparseReferenceMass
      k hk tau htau
  obtain ⟨deltaGuard, hdeltaGuard, hguard⟩ :=
    eventually_criticalRetainedSupport_log_choose_lower
      k hk (show (0 : ℝ) < 1 by norm_num)
  have hbalanced := eventually_exactlyBalanced_isBalancedFullDivision hk
  rw [eventually_atTop] at hbalanced
  obtain ⟨q₀, hq₀⟩ := hbalanced
  let delta : ℝ := min (criticalFineBalanceGeometryRadius k)
    (min deltaNonunique (min deltaFar (min deltaGuard (1 / 2))))
  have hdelta : 0 < delta := by
    dsimp [delta]
    exact lt_min (criticalFineBalanceGeometryRadius_pos hk)
      (lt_min hdeltaNonunique
        (lt_min hdeltaFar (lt_min hdeltaGuard (by norm_num))))
  have hdeltaGeometry : delta ≤ criticalFineBalanceGeometryRadius k :=
    min_le_left _ _
  have hdeltaNonuniqueLe : delta ≤ deltaNonunique :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hdeltaFarLe : delta ≤ deltaFar :=
    (min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _))
  have hdeltaGuardLe : delta ≤ deltaGuard :=
    (min_le_right _ _).trans
      ((min_le_right _ _).trans
        ((min_le_right _ _).trans (min_le_left _ _)))
  have hdeltaHalf : delta ≤ (1 : ℝ) / 2 :=
    (min_le_right _ _).trans
      ((min_le_right _ _).trans
        ((min_le_right _ _).trans (min_le_right _ _)))
  have herrorTendsto : Tendsto
      (fun n : ℕ ↦ Real.exp (-(cNonunique * (n : ℝ))) +
        Real.exp (-(cFar * (n : ℝ) ^ 2)))
      atTop (nhds 0) := by
    simpa using
      (tendsto_exp_neg_mul_natCast_zero hcNonunique).add
        (tendsto_exp_neg_mul_natCast_sq_zero hcFar)
  have herror : ∀ᶠ n : ℕ in atTop,
      Real.exp (-(cNonunique * (n : ℝ))) +
          Real.exp (-(cFar * (n : ℝ) ^ 2)) ≤ 1 / 2 := by
    exact ((tendsto_order.1 herrorTendsto).2 (1 / 2)
      (by norm_num)).mono fun _ hn ↦ hn.le
  refine ⟨tau, delta, htau, htauCap, hdelta, ?_⟩
  filter_upwards [hcanonical, hnonunique, hfar, hguard, herror,
      eventually_ge_atTop (2 * max q₀ (k - 1))] with
      n hnCanonical hnNonunique hnFar hnGuard hnError hnLarge
  intro hn S hsSmall R hR
  have hs : S.card ≤ n := by
    simpa using Finset.card_le_univ S
  have hsGeometry : (S.card : ℝ) ≤
      criticalFineBalanceGeometryRadius k * (n : ℝ) :=
    hsSmall.trans (mul_le_mul_of_nonneg_right hdeltaGeometry (by positivity))
  have hsNonunique : (S.card : ℝ) ≤
      deltaNonunique * (n : ℝ) :=
    hsSmall.trans (mul_le_mul_of_nonneg_right hdeltaNonuniqueLe (by positivity))
  have hsFar : (S.card : ℝ) ≤ deltaFar * (n : ℝ) :=
    hsSmall.trans (mul_le_mul_of_nonneg_right hdeltaFarLe (by positivity))
  have hsGuard : (S.card : ℝ) ≤ deltaGuard * (n : ℝ) :=
    hsSmall.trans (mul_le_mul_of_nonneg_right hdeltaGuardLe (by positivity))
  have hsHalfReal : (S.card : ℝ) ≤ (1 / 2 : ℝ) * (n : ℝ) :=
    hsSmall.trans (mul_le_mul_of_nonneg_right hdeltaHalf (by positivity))
  have hsHalf : 2 * S.card ≤ n := by
    exact_mod_cast (show (2 : ℝ) * S.card ≤ n by nlinarith)
  have ht : R.edgeFinset.card ≤ Nat.choose S.card 2 := by
    simpa using SimpleGraph.card_edgeFinset_le_card_choose_two (G := R)
  obtain ⟨hcriticalGuard, _hselectedPos, hselectedFeasible, _hlog⟩ :=
    hnGuard S.card hs hsGuard R.edgeFinset.card ht
  have htCritical : R.edgeFinset.card ≤ criticalEdgeCount k n := by
    omega
  have hupper : criticalEdgeCount k n - R.edgeFinset.card ≤
      Nat.choose (n - S.card) 2 := by
    have htotal := DenseGraph.balancedCross_add_internal
      (k - 1) (n - S.card)
    unfold criticalRetainedSupportSelectedCount
      criticalRetainedSupportCapacity at hselectedFeasible
    omega
  have hqLarge : max q₀ (k - 1) ≤ n - S.card := by
    omega
  have hq : k - 1 ≤ fixedSparseCoreCard S := by
    change k - 1 ≤ n - S.card
    exact (le_max_right _ _).trans hqLarge
  have hbalance :
      ∀ D : SupercriticalDivision k (Fin (fixedSparseCoreCard S)),
        IsExactlyBalancedFullDivision D →
          IsBalancedFullDivision D (supercriticalCoverBalanceRadius k) := by
    intro D hD
    exact hq₀ (fixedSparseCoreCard S)
      (by simpa only [fixedSparseCoreCard] using
        (le_max_left q₀ (k - 1)).trans hqLarge) D hD
  let m := criticalEdgeCount k n - R.edgeFinset.card
  have hm : m + R.edgeFinset.card = criticalEdgeCount k n := by
    dsimp [m]
    omega
  have hreference :
      criticalFixedSparseBalancedCrossSliceMass
          k n S.card R.edgeFinset.card ≤
        ((fixedSparseExactlyBalancedCleanCoverPairFinset k n S
          (supercriticalCoverBalanceRadius k) m R).card : ℝ) := by
    exact criticalFixedSparseReferenceMass_le_exactPairs
      hk S (supercriticalCoverBalanceRadius k) R hq hcriticalGuard hupper hbalance
  have htransferNat :=
    card_fixedSparseExactPairs_le_canonical_add_errors
      hk hn S (supercriticalCoverBalanceRadius k) tau R hR hm
        (hnCanonical hn S (supercriticalCoverBalanceRadius k) m R
          hsGeometry hR hm)
  have htransfer :
      ((fixedSparseExactlyBalancedCleanCoverPairFinset k n S
        (supercriticalCoverBalanceRadius k) m R).card : ℝ) ≤
        ((k - 1).factorial : ℝ) *
            ((criticalFixedRemainderCanonicalCleanGraphFinset
              k hk n tau hn S R).card : ℝ) +
          ((fixedSparseBalancedNonuniqueCleanCoverPairFinset k n S
            (supercriticalCoverBalanceRadius k) m R).card : ℝ) +
          ((k ^ n : ℕ) : ℝ) *
            ((criticalFarGraphFinset k hk n tau).card : ℝ) := by
    exact_mod_cast htransferNat
  have hnonuniqueBound := hnNonunique S hsNonunique R
  have hfarBound := hnFar S.card hs hsFar R.edgeFinset.card ht
  exact criticalFineBalance_reference_le_twice_factorial_of_errors
    (criticalFixedSparseBalancedCrossSliceMass_nonneg
      k n S.card R.edgeFinset.card)
    hreference htransfer
    (by simpa [m] using hnonuniqueBound)
    hfarBound hnError

end InducedStars
