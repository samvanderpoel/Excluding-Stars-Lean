import InducedStars.Structure.Critical.FineBalanceExactReference
import InducedStars.Structure.Critical.FineBalanceCanonicalGeometry
import InducedStars.Structure.Critical.FineBalanceInducedFree
import InducedStars.Structure.Critical.FineBalanceCanonical

/-!
# From exact displayed reference covers to canonical clean graphs

The transfer keeps the sparse induced graph fixed.  Induced-star-freeness
then holds for every clean reference realization, and the exact total edge
count is recovered without losing its natural-subtraction guards.
-/

noncomputable section

open Finset Filter Set Topology

namespace InducedStars

noncomputable local instance fineBalanceTransferEdgeSetFintype
    {V : Type*} [Fintype V] (G : SimpleGraph V) : Fintype G.edgeSet :=
  Fintype.ofFinite G.edgeSet

/-- Fixing an induced-star-free sparse component makes every clean displayed
realization induced-star-free.  The edge count is the exact sum of the two
components, not an asymptotic density constraint. -/
theorem fixedSparseBalancedPair_inducedFree_and_edgeCount
    {k n m : ℕ} (hk : 1 ≤ k) {S : Finset (Fin n)} {beta : ℝ}
    {R : SimpleGraph ({v : Fin n | v ∈ S} : Set (Fin n))}
    (hR : ¬ Regularity.InducedEmbeds (inducedStar k) R)
    {p : SupercriticalDivision k (Fin n) × SimpleGraph (Fin n)}
    (hp : p ∈ fixedSparseBalancedCleanCoverPairFinset k n S beta m R) :
    ¬ Regularity.InducedEmbeds (inducedStar k) p.2 ∧
      p.2.edgeFinset.card = m + R.edgeFinset.card := by
  classical
  obtain ⟨hS, hclean, _hbalanced, hcore, hrem⟩ :=
    mem_fixedSparseBalancedCleanCoverPairFinset.mp hp
  have hsparse : ¬ Regularity.InducedEmbeds (inducedStar k)
      (p.2.induce (p.1.sparse : Set (Fin n))) := by
    rw [hS]
    change ¬ Regularity.InducedEmbeds (inducedStar k)
      (fixedSparseRemainderGraph S p.2)
    rwa [hrem]
  have hfree := not_inducedEmbeds_inducedStar_of_clean_of_sparse_free
    hk p.2 p.1 hclean hsparse
  refine ⟨hfree, ?_⟩
  have hcount := card_core_add_remainder_eq_of_fixedSparse_clean hS hclean
  rw [card_finiteGraphEdges_fixedSparseCoreGraph, hcore, hrem,
    finiteGraphEdges_card_eq_edgeFinset_card] at hcount
  exact hcount.symm

/-- Exact displayed balance supplies the deterministic floor lower bound
required to preserve the sparse set under canonical minimization. -/
theorem fixedSparseExactPair_part_card_lower
    {k n m : ℕ} (hk : 3 ≤ k) {S : Finset (Fin n)} {beta : ℝ}
    {R : SimpleGraph ({v : Fin n | v ∈ S} : Set (Fin n))}
    {p : SupercriticalDivision k (Fin n) × SimpleGraph (Fin n)}
    (hp : p ∈ fixedSparseExactlyBalancedCleanCoverPairFinset k n S beta m R)
    (i : Fin (k - 1)) :
    (n - p.1.sparse.card) / (k - 1) ≤ (p.1.parts i).card := by
  have hp' := mem_fixedSparseExactlyBalancedCleanCoverPairFinset.mp hp
  have hS := (mem_fixedSparseBalancedCleanCoverPairFinset.mp hp'.1).1
  rw [hS, hp'.2 i, DenseGraph.card_balancedFinPartition (by omega)]
  unfold fixedSparseCoreCard
  split_ifs <;> omega

/-- Under the verified canonical sparse-transfer geometry, a close exact
reference pair is genuinely in the canonical clean fixed-sparse family.
This does not identify arbitrary coarse-balanced covers with canonical ones. -/
theorem fixedSparseExactPair_mem_canonical_of_close
    {k n m : ℕ} (hk : 3 ≤ k) (hn : k - 1 ≤ n)
    {S : Finset (Fin n)} {beta tau : ℝ}
    {R : SimpleGraph ({v : Fin n | v ∈ S} : Set (Fin n))}
    (hR : ¬ Regularity.InducedEmbeds (inducedStar k) R)
    (hm : m + R.edgeFinset.card = criticalEdgeCount k n)
    {p : SupercriticalDivision k (Fin n) × SimpleGraph (Fin n)}
    (hp : p ∈ fixedSparseExactlyBalancedCleanCoverPairFinset k n S beta m R)
    (hclose : cutDist (graphGraphon p.2)
      (Wstar k hk (gammaK k) (gammaK_mem_supercritical_Ico k hk)) < tau)
    (hcanonical : (canonicalSupercriticalDivision p.2
      (by simpa using hn)).sparse = p.1.sparse) :
    p.2 ∈ criticalCanonicalCleanFixedSparseGraphFinset k hk n tau hn S := by
  classical
  have hraw := (mem_fixedSparseExactlyBalancedCleanCoverPairFinset.mp hp).1
  obtain ⟨hS, hclean, _hbal, _hcore, _hrem⟩ :=
    mem_fixedSparseBalancedCleanCoverPairFinset.mp hraw
  obtain ⟨hfree, hcount⟩ := fixedSparseBalancedPair_inducedFree_and_edgeCount
    (by omega : 1 ≤ k) hR hraw
  rw [mem_criticalCanonicalCleanFixedSparseGraphFinset]
  refine ⟨mem_supercriticalCloseGraphFinset.mpr ⟨hfree, hcount.trans hm, hclose⟩,
    hcanonical.trans hS, ?_⟩
  rw [canonicalSupercriticalDefectGraph_eq_bot_of_clean_of_sparse_eq
    p.2 hn p.1 hclean hcanonical, finiteGraphEdges_card_eq_edgeFinset_card]
  simp

/-- A single close-radius works uniformly for exact displayed references.
The sparse-size restriction and eventual threshold are explicit. -/
theorem eventually_fixedSparseExactPair_mem_canonical_of_close
    (k : ℕ) (hk : 3 ≤ k) :
    ∃ tau : ℝ, 0 < tau ∧ ∀ᶠ n : ℕ in atTop,
      ∀ (hn : k - 1 ≤ n) (S : Finset (Fin n)) (beta : ℝ) (m : ℕ)
        (R : SimpleGraph ({v : Fin n | v ∈ S} : Set (Fin n))),
        (S.card : ℝ) ≤ criticalFineBalanceGeometryRadius k * n →
        ¬ Regularity.InducedEmbeds (inducedStar k) R →
        m + R.edgeFinset.card = criticalEdgeCount k n →
        ∀ p ∈ fixedSparseExactlyBalancedCleanCoverPairFinset k n S beta m R,
          cutDist (graphGraphon p.2)
            (Wstar k hk (gammaK k) (gammaK_mem_supercritical_Ico k hk)) < tau →
          p.2 ∈ criticalCanonicalCleanFixedSparseGraphFinset k hk n tau hn S := by
  obtain ⟨tau, htau, hgeometry⟩ :=
    eventually_canonical_sparse_eq_of_close_balanced_displayed k hk
  refine ⟨tau, htau, ?_⟩
  filter_upwards [hgeometry] with n hnGeom
  intro hn S beta m R hs hR hm p hp hclose
  have hraw := (mem_fixedSparseExactlyBalancedCleanCoverPairFinset.mp hp).1
  have hdata := mem_fixedSparseBalancedCleanCoverPairFinset.mp hraw
  apply fixedSparseExactPair_mem_canonical_of_close hk hn hR hm hp hclose
  exact hnGeom p.2 hn p.1 hclose hdata.2.1
    (by simpa [hdata.1] using hs)
    (fixedSparseExactPair_part_card_lower hk hp)

/-- The canonical transfer radius can be chosen below any previously fixed
positive close-radius.  The auxiliary radius is independent of the later
fixed-sparse entropy estimates. -/
theorem eventually_fixedSparseExactPair_mem_canonical_of_close_below
    (k : ℕ) (hk : 3 ≤ k) {tauCap : ℝ} (hCap : 0 < tauCap) :
    ∃ tau : ℝ, 0 < tau ∧ tau ≤ tauCap ∧ ∀ᶠ n : ℕ in atTop,
      ∀ (hn : k - 1 ≤ n) (S : Finset (Fin n)) (beta : ℝ) (m : ℕ)
        (R : SimpleGraph ({v : Fin n | v ∈ S} : Set (Fin n))),
        (S.card : ℝ) ≤ criticalFineBalanceGeometryRadius k * n →
        ¬ Regularity.InducedEmbeds (inducedStar k) R →
        m + R.edgeFinset.card = criticalEdgeCount k n →
        ∀ p ∈ fixedSparseExactlyBalancedCleanCoverPairFinset k n S beta m R,
          cutDist (graphGraphon p.2)
            (Wstar k hk (gammaK k) (gammaK_mem_supercritical_Ico k hk)) < tau →
          p.2 ∈ criticalCanonicalCleanFixedSparseGraphFinset k hk n tau hn S := by
  obtain ⟨tau₀, htau₀, htransfer⟩ :=
    eventually_fixedSparseExactPair_mem_canonical_of_close k hk
  refine ⟨min tau₀ tauCap, lt_min htau₀ hCap, min_le_right _ _, ?_⟩
  filter_upwards [htransfer] with n hnTransfer
  intro hn S beta m R hs hR hm p hp hclose
  have hlarge := mem_criticalCanonicalCleanFixedSparseGraphFinset.mp
    (hnTransfer hn S beta m R hs hR hm p hp
      (hclose.trans_le (min_le_left _ _)))
  apply mem_criticalCanonicalCleanFixedSparseGraphFinset.mpr
  refine ⟨?_, hlarge.2⟩
  obtain ⟨hfree, hedge, _⟩ := mem_supercriticalCloseGraphFinset.mp hlarge.1
  exact mem_supercriticalCloseGraphFinset.mpr ⟨hfree, hedge, hclose⟩

/-- Exact reference pairs outside the fixed-remainder canonical family are
far, provided the deterministic canonical-transfer condition holds. -/
theorem fixedSparseExactPair_far_of_not_canonical
    {k n m : ℕ} (hk : 3 ≤ k) (hn : k - 1 ≤ n)
    {S : Finset (Fin n)} {beta tau : ℝ}
    {R : SimpleGraph ({v : Fin n | v ∈ S} : Set (Fin n))}
    (hR : ¬ Regularity.InducedEmbeds (inducedStar k) R)
    (hm : m + R.edgeFinset.card = criticalEdgeCount k n)
    (htransfer : ∀ p ∈ fixedSparseExactlyBalancedCleanCoverPairFinset k n S beta m R,
      cutDist (graphGraphon p.2)
        (Wstar k hk (gammaK k) (gammaK_mem_supercritical_Ico k hk)) < tau →
      p.2 ∈ criticalCanonicalCleanFixedSparseGraphFinset k hk n tau hn S)
    {p : SupercriticalDivision k (Fin n) × SimpleGraph (Fin n)}
    (hp : p ∈ fixedSparseExactlyBalancedCleanCoverPairFinset k n S beta m R)
    (hnot : p.2 ∉ criticalFixedRemainderCanonicalCleanGraphFinset
      k hk n tau hn S R) :
    p.2 ∈ supercriticalFarGraphFinset k hk (gammaK k)
      (gammaK_mem_supercritical_Ico k hk) (criticalEdgeCount k n) n tau := by
  classical
  have hraw := (mem_fixedSparseExactlyBalancedCleanCoverPairFinset.mp hp).1
  obtain ⟨hfree, hcount⟩ := fixedSparseBalancedPair_inducedFree_and_edgeCount
    (by omega : 1 ≤ k) hR hraw
  rw [mem_supercriticalFarGraphFinset]
  refine ⟨hfree, hcount.trans hm, ?_⟩
  by_contra hfar
  have hclose := lt_of_not_ge hfar
  apply hnot
  exact mem_criticalFixedRemainderCanonicalCleanGraphFinset.mpr
    ⟨htransfer p hp hclose,
      (mem_fixedSparseBalancedCleanCoverPairFinset.mp hraw).2.2.2.2⟩

/-- Finite denominator estimate for the actual fixed-remainder canonical
family.  It accounts separately for the nonunique-cover and far errors. -/
theorem card_fixedSparseExactPairs_le_canonical_add_errors
    {k n m : ℕ} (hk : 3 ≤ k) (hn : k - 1 ≤ n)
    (S : Finset (Fin n)) (beta tau : ℝ)
    (R : SimpleGraph ({v : Fin n | v ∈ S} : Set (Fin n)))
    (hR : ¬ Regularity.InducedEmbeds (inducedStar k) R)
    (hm : m + R.edgeFinset.card = criticalEdgeCount k n)
    (htransfer : ∀ p ∈ fixedSparseExactlyBalancedCleanCoverPairFinset k n S beta m R,
      cutDist (graphGraphon p.2)
        (Wstar k hk (gammaK k) (gammaK_mem_supercritical_Ico k hk)) < tau →
      p.2 ∈ criticalCanonicalCleanFixedSparseGraphFinset k hk n tau hn S) :
    (fixedSparseExactlyBalancedCleanCoverPairFinset k n S beta m R).card ≤
      (k - 1).factorial *
          (criticalFixedRemainderCanonicalCleanGraphFinset k hk n tau hn S R).card +
        (fixedSparseBalancedNonuniqueCleanCoverPairFinset k n S beta m R).card +
        k ^ n * (supercriticalFarGraphFinset k hk (gammaK k)
          (gammaK_mem_supercritical_Ico k hk) (criticalEdgeCount k n) n tau).card := by
  apply card_fixedSparseBalancedPairSubfamily_le_factorial_mul_add_nonunique_add_pow_mul
    k n (by omega) S beta m R _ _ _
    (fixedSparseExactlyBalancedCleanCoverPairFinset_subset k n S beta m R)
  intro p hp hnot
  exact fixedSparseExactPair_far_of_not_canonical hk hn hR hm htransfer hp hnot

/-- One radius and one eventual threshold give the denominator transfer
uniformly over every sufficiently small prescribed sparse set. -/
theorem eventually_card_fixedSparseExactPairs_le_canonical_add_errors
    (k : ℕ) (hk : 3 ≤ k) :
    ∃ tau : ℝ, 0 < tau ∧ ∀ᶠ n : ℕ in atTop,
      ∀ (hn : k - 1 ≤ n) (S : Finset (Fin n)) (beta : ℝ) (m : ℕ)
        (R : SimpleGraph ({v : Fin n | v ∈ S} : Set (Fin n))),
        (S.card : ℝ) ≤ criticalFineBalanceGeometryRadius k * n →
        ¬ Regularity.InducedEmbeds (inducedStar k) R →
        m + R.edgeFinset.card = criticalEdgeCount k n →
        (fixedSparseExactlyBalancedCleanCoverPairFinset k n S beta m R).card ≤
          (k - 1).factorial *
            (criticalFixedRemainderCanonicalCleanGraphFinset k hk n tau hn S R).card +
          (fixedSparseBalancedNonuniqueCleanCoverPairFinset k n S beta m R).card +
          k ^ n * (supercriticalFarGraphFinset k hk (gammaK k)
            (gammaK_mem_supercritical_Ico k hk) (criticalEdgeCount k n) n tau).card := by
  obtain ⟨tau, htau, htransfer⟩ :=
    eventually_fixedSparseExactPair_mem_canonical_of_close k hk
  refine ⟨tau, htau, ?_⟩
  filter_upwards [htransfer] with n hnTransfer
  intro hn S beta m R hs hR hm
  exact card_fixedSparseExactPairs_le_canonical_add_errors hk hn S beta tau R
    hR hm (hnTransfer hn S beta m R hs hR hm)

end InducedStars
