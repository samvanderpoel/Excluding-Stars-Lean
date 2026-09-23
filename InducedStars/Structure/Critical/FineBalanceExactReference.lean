import InducedStars.Structure.Critical.Reference
import InducedStars.Structure.Critical.FixedSparseCoverMultiplicity

/-!
# Exactly balanced reference pairs with a prescribed sparse graph

The denominator in the fixed-sparse fine-balance argument uses exactly
balanced displayed covers.  These form a subset of the coarse balanced
family used to bound nonunique covers, but satisfy stronger deterministic
geometry.  No canonicality or closeness is asserted by these raw counts.
-/

noncomputable section

open Finset Filter
open scoped BigOperators

namespace InducedStars

/-- Exactly balanced full displayed covers, at an arbitrary edge count. -/
noncomputable def exactlyBalancedCoreCoverPairFinset (k q m : ℕ) :
    Finset (SupercriticalDivision k (Fin q) × SimpleGraph (Fin q)) := by
  classical
  exact (exactlyBalancedFullSupercriticalDivisions k q).biUnion fun D ↦
    (supercriticalCoPartiteFiber D m).image fun G ↦ (D, G)

@[simp] theorem mem_exactlyBalancedCoreCoverPairFinset
    {k q m : ℕ}
    {p : SupercriticalDivision k (Fin q) × SimpleGraph (Fin q)} :
    p ∈ exactlyBalancedCoreCoverPairFinset k q m ↔
      IsExactlyBalancedFullDivision p.1 ∧
        p.2 ∈ supercriticalCoPartiteFiber p.1 m := by
  classical
  constructor
  · intro hp
    obtain ⟨D, hD, hp⟩ := Finset.mem_biUnion.mp hp
    obtain ⟨G, hG, rfl⟩ := Finset.mem_image.mp hp
    exact ⟨mem_exactlyBalancedFullSupercriticalDivisions.mp hD, hG⟩
  · rintro ⟨hD, hG⟩
    exact Finset.mem_biUnion.mpr ⟨p.1,
      mem_exactlyBalancedFullSupercriticalDivisions.mpr hD,
      Finset.mem_image.mpr ⟨p.2, hG, Prod.eta p⟩⟩

/-- Exact size of the reference family, including the forced-edge guard. -/
theorem card_exactlyBalancedCoreCoverPairFinset
    {k q m : ℕ} (hk : 3 ≤ k) :
    (exactlyBalancedCoreCoverPairFinset k q m).card =
      (exactlyBalancedFullSupercriticalDivisions k q).card *
        if DenseGraph.balancedMultipartiteInternalCapacity (k - 1) q ≤ m then
          (DenseGraph.balancedMultipartiteCrossCapacity (k - 1) q).choose
            (m - DenseGraph.balancedMultipartiteInternalCapacity (k - 1) q)
        else 0 := by
  classical
  rw [exactlyBalancedCoreCoverPairFinset, Finset.card_biUnion]
  · have hfiber : ∀ D ∈ exactlyBalancedFullSupercriticalDivisions k q,
        ((supercriticalCoPartiteFiber D m).image fun G ↦ (D, G)).card =
          if DenseGraph.balancedMultipartiteInternalCapacity (k - 1) q ≤ m then
            (DenseGraph.balancedMultipartiteCrossCapacity (k - 1) q).choose
              (m - DenseGraph.balancedMultipartiteInternalCapacity (k - 1) q)
          else 0 := by
      intro D hD
      have h := mem_exactlyBalancedFullSupercriticalDivisions.mp hD
      rw [Finset.card_image_iff.mpr (by
        intro G _ H _ hGH
        exact (Prod.mk.inj hGH).2), card_supercriticalCoPartiteFiber D h.1,
        exactlyBalancedDivision_internalCapacity_eq hk h,
        exactlyBalancedDivision_crossCapacity_eq hk h]
    rw [Finset.sum_congr rfl hfiber]
    simp
  · intro D _ E _ hDE
    change Disjoint ((supercriticalCoPartiteFiber D m).image fun G ↦ (D, G))
      ((supercriticalCoPartiteFiber E m).image fun G ↦ (E, G))
    rw [Finset.disjoint_left]
    rintro p hpD hpE
    obtain ⟨G, _, rfl⟩ := Finset.mem_image.mp hpD
    obtain ⟨H, _, heq⟩ := Finset.mem_image.mp hpE
    exact hDE (Prod.mk.inj heq.symm).1

/-- Lower bound by the balanced multinomial times its binomial fiber. -/
theorem balancedMultinomial_mul_choose_le_exactCorePairs
    {k q m : ℕ} (hk : 3 ≤ k) (hq : k - 1 ≤ q)
    (hm : DenseGraph.balancedMultipartiteInternalCapacity (k - 1) q ≤ m) :
    Nat.multinomial Finset.univ (DenseGraph.balancedPartSize (k - 1) q) *
        (DenseGraph.balancedMultipartiteCrossCapacity (k - 1) q).choose
          (m - DenseGraph.balancedMultipartiteInternalCapacity (k - 1) q) ≤
      (exactlyBalancedCoreCoverPairFinset k q m).card := by
  rw [card_exactlyBalancedCoreCoverPairFinset hk, if_pos hm]
  exact Nat.mul_le_mul_right _
    ((DenseGraph.multinomial_le_card_balancedAssignments (by omega)).trans
      (card_balancedAssignments_le_exactlyBalancedDivisions hk hq))

/-- The exact reference subset of the coarse fixed-sparse displayed pairs. -/
noncomputable def fixedSparseExactlyBalancedCleanCoverPairFinset
    (k n : ℕ) (S : Finset (Fin n)) (beta : ℝ) (m : ℕ)
    (R : SimpleGraph ({v : Fin n | v ∈ S} : Set (Fin n))) :
    Finset (SupercriticalDivision k (Fin n) × SimpleGraph (Fin n)) := by
  classical
  exact (fixedSparseBalancedCleanCoverPairFinset k n S beta m R).filter fun p ↦
    ∀ i, (p.1.parts i).card =
      (DenseGraph.balancedFinPartition (k - 1) (fixedSparseCoreCard S) i).card

@[simp] theorem mem_fixedSparseExactlyBalancedCleanCoverPairFinset
    {k n m : ℕ} {S : Finset (Fin n)} {beta : ℝ}
    {R : SimpleGraph ({v : Fin n | v ∈ S} : Set (Fin n))}
    {p : SupercriticalDivision k (Fin n) × SimpleGraph (Fin n)} :
    p ∈ fixedSparseExactlyBalancedCleanCoverPairFinset k n S beta m R ↔
      p ∈ fixedSparseBalancedCleanCoverPairFinset k n S beta m R ∧
        ∀ i, (p.1.parts i).card =
          (DenseGraph.balancedFinPartition (k - 1) (fixedSparseCoreCard S) i).card := by
  classical
  simp [fixedSparseExactlyBalancedCleanCoverPairFinset]

theorem fixedSparseExactlyBalancedCleanCoverPairFinset_subset
    (k n : ℕ) (S : Finset (Fin n)) (beta : ℝ) (m : ℕ)
    (R : SimpleGraph ({v : Fin n | v ∈ S} : Set (Fin n))) :
    fixedSparseExactlyBalancedCleanCoverPairFinset k n S beta m R ⊆
      fixedSparseBalancedCleanCoverPairFinset k n S beta m R := by
  classical
  exact Finset.filter_subset _ _

/-- Each exactly balanced core pair can be assembled with any prescribed
sparse graph, without identifying distinct ordered covers. -/
theorem card_exactCorePairs_le_fixedSparseExactPairs
    {k n m : ℕ} (S : Finset (Fin n)) (beta : ℝ)
    (R : SimpleGraph ({v : Fin n | v ∈ S} : Set (Fin n)))
    (hbalance : ∀ D : SupercriticalDivision k (Fin (fixedSparseCoreCard S)),
      IsExactlyBalancedFullDivision D → IsBalancedFullDivision D beta) :
    (exactlyBalancedCoreCoverPairFinset k (fixedSparseCoreCard S) m).card ≤
      (fixedSparseExactlyBalancedCleanCoverPairFinset k n S beta m R).card := by
  classical
  let source := exactlyBalancedCoreCoverPairFinset k (fixedSparseCoreCard S) m
  let target := fixedSparseExactlyBalancedCleanCoverPairFinset k n S beta m R
  have hmaps (p : ↑source) :
      (extendFixedSparseCoreDivision S p.1.1,
        fixedSparseAssembledGraph S p.1.2 R) ∈ target := by
    obtain ⟨hD, hG⟩ := mem_exactlyBalancedCoreCoverPairFinset.mp p.2
    rw [mem_fixedSparseExactlyBalancedCleanCoverPairFinset]
    refine ⟨fixedSparseAssembledPair_mem R
      (mem_balancedCoMultipartiteCoverPairFinset.mpr ⟨hbalance _ hD, hG⟩), ?_⟩
    intro i
    simpa [extendFixedSparseCoreDivision] using hD.2 i
  let f : ↑source → ↑target := fun p ↦ ⟨_, hmaps p⟩
  have hf : Function.Injective f := by
    intro p q hpq
    have hp := (mem_exactlyBalancedCoreCoverPairFinset.mp p.2).1
    have hq := (mem_exactlyBalancedCoreCoverPairFinset.mp q.2).1
    have hval := congrArg Subtype.val hpq
    have hdivision : p.1.1 = q.1.1 :=
      extendFixedSparseCoreDivision_injective_of_full hp.1 hq.1
        (congrArg Prod.fst hval)
    have hgraph : p.1.2 = q.1.2 := by
      have h := congrArg (fun x ↦ fixedSparseCoreGraph S x.2) hval
      simpa [f] using h
    exact Subtype.ext (Prod.ext hdivision hgraph)
  simpa only [Fintype.card_coe] using Fintype.card_le_of_injective f hf

/-- Uniform fixed-sparse reference-mass lower bound.  The only geometric
hypothesis here is inclusion of exactly balanced covers in the coarse window. -/
theorem balancedMultinomial_mul_choose_le_fixedSparseExactPairs
    {k n m : ℕ} (hk : 3 ≤ k) (S : Finset (Fin n)) (beta : ℝ)
    (R : SimpleGraph ({v : Fin n | v ∈ S} : Set (Fin n)))
    (hq : k - 1 ≤ fixedSparseCoreCard S)
    (hm : DenseGraph.balancedMultipartiteInternalCapacity (k - 1)
      (fixedSparseCoreCard S) ≤ m)
    (hbalance : ∀ D : SupercriticalDivision k (Fin (fixedSparseCoreCard S)),
      IsExactlyBalancedFullDivision D → IsBalancedFullDivision D beta) :
    Nat.multinomial Finset.univ
        (DenseGraph.balancedPartSize (k - 1) (fixedSparseCoreCard S)) *
        (DenseGraph.balancedMultipartiteCrossCapacity (k - 1)
          (fixedSparseCoreCard S)).choose
          (m - DenseGraph.balancedMultipartiteInternalCapacity (k - 1)
            (fixedSparseCoreCard S)) ≤
      (fixedSparseExactlyBalancedCleanCoverPairFinset k n S beta m R).card :=
  (balancedMultinomial_mul_choose_le_exactCorePairs hk hq hm).trans
    (card_exactCorePairs_le_fixedSparseExactPairs S beta R hbalance)

end InducedStars
