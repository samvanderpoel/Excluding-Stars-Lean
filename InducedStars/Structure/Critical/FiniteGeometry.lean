import InducedStars.Structure.Critical.Basic
import InducedStars.Structure.Supercritical.AlmostAll
import InducedStars.Structure.Supercritical.CountingSetup

/-!
# Finite geometry at the critical density

This file turns the zero-defect geometry of a supercritical division into the
literal critical decomposition recorded by `CriticalStructureWitness`.  It
also specializes the endpoint-valid optimizer-far estimate to the canonical
critical edge-count sequence.
-/

noncomputable section

open Filter Set Topology

namespace InducedStars

/-! ## Zero defect gives a literal core--remainder decomposition -/

variable {k : ℕ} {V : Type*} [Fintype V] [DecidableEq V]

/-- If the ordinary division defect graph is empty, every main part is a
clique in the original graph. -/
theorem mainParts_clique_of_supercriticalDefectGraph_eq_bot
    (G : SimpleGraph V) (D : SupercriticalDivision k V)
    (hdefect : supercriticalDefectGraph G D = ⊥)
    (i : Fin (k - 1)) {x y : V}
    (hx : x ∈ D.parts i) (hy : y ∈ D.parts i) (hxy : x ≠ y) :
    G.Adj x y := by
  by_contra hnot
  have hmissing : (supercriticalDefectGraph G D).Adj x y :=
    (supercriticalDefectGraph_adj_of_mem_same_part G D i hx hy).2
      ⟨hxy, hnot⟩
  rw [hdefect] at hmissing
  exact hmissing

/-- If the ordinary division defect graph is empty, there are no graph edges
between the main support and the sparse set. -/
theorem not_adj_support_sparse_of_supercriticalDefectGraph_eq_bot
    (G : SimpleGraph V) (D : SupercriticalDivision k V)
    (hdefect : supercriticalDefectGraph G D = ⊥)
    {x y : V} (hx : x ∈ D.support) (hy : y ∈ D.sparse) :
    ¬G.Adj x y := by
  intro hxy
  have hcross : (supercriticalDefectGraph G D).Adj x y :=
    (supercriticalDefectGraph_adj_support_sparse G D hx hy).2 hxy
  rw [hdefect] at hcross
  exact hcross

omit [DecidableEq V] in
/-- A finite graph with no neutral finite edges is the bottom graph. -/
theorem simpleGraph_eq_bot_of_finiteGraphEdges_card_eq_zero
    (G : SimpleGraph V) (hzero : (finiteGraphEdges G).card = 0) :
    G = ⊥ := by
  have hempty : finiteGraphEdges G = ∅ := Finset.card_eq_zero.mp hzero
  ext x y
  constructor
  · intro hxy
    have hmem : s(x, y) ∈ finiteGraphEdges G := by simpa using hxy
    rw [hempty] at hmem
    simp at hmem
  · simp

/-- The main parts of a division, restricted to the complementary subtype of
its sparse set. -/
def criticalCoreParts (D : SupercriticalDivision k V)
    (i : Fin (k - 1)) :
    Finset ({v : V | v ∉ D.sparse} : Set V) :=
  Finset.univ.filter fun v ↦ v.1 ∈ D.parts i

/-- The restricted main parts cover the core subtype. -/
theorem criticalCoreParts_cover (D : SupercriticalDivision k V) :
    Finset.univ.biUnion (criticalCoreParts D) = Finset.univ := by
  apply Finset.eq_univ_of_forall
  intro v
  have hvSupport : v.1 ∈ D.support := by
    simpa using v.2
  obtain ⟨i, hi⟩ := SupercriticalDivision.mem_support.mp hvSupport
  apply Finset.mem_biUnion.mpr
  exact ⟨i, Finset.mem_univ i, by simp [criticalCoreParts, hi]⟩

/-- The restricted main parts remain pairwise disjoint. -/
theorem criticalCoreParts_pairwiseDisjoint
    (D : SupercriticalDivision k V) :
    Set.PairwiseDisjoint (Set.univ : Set (Fin (k - 1)))
      (criticalCoreParts D) := by
  intro i _hi j _hj hij
  change Disjoint (criticalCoreParts D i) (criticalCoreParts D j)
  rw [Finset.disjoint_left]
  intro v hvi hvj
  have hvi' : v.1 ∈ D.parts i := by
    simpa [criticalCoreParts] using hvi
  have hvj' : v.1 ∈ D.parts j := by
    simpa [criticalCoreParts] using hvj
  exact (Finset.disjoint_left.mp
    (D.parts_pairwiseDisjoint (Set.mem_univ i) (Set.mem_univ j) hij))
      hvi' hvj'

/-- Under zero defect, every restricted main part is a clique in the induced
core graph. -/
theorem criticalCoreParts_isClique_of_defectGraph_eq_bot
    (G : SimpleGraph V) (D : SupercriticalDivision k V)
    (hdefect : supercriticalDefectGraph G D = ⊥)
    (i : Fin (k - 1)) :
    (G.induce ({v : V | v ∉ D.sparse} : Set V)).IsClique
      (criticalCoreParts D i : Set ({v : V | v ∉ D.sparse} : Set V)) := by
  rw [SimpleGraph.isClique_iff]
  intro x hx y hy hxy
  have hxPart : x.1 ∈ D.parts i := by
    simpa [criticalCoreParts] using hx
  have hyPart : y.1 ∈ D.parts i := by
    simpa [criticalCoreParts] using hy
  exact mainParts_clique_of_supercriticalDefectGraph_eq_bot G D hdefect i
    hxPart hyPart (fun h ↦ hxy (Subtype.ext h))

/-- The induced graph on the main support is co-`(k-1)`-partite whenever the
ordinary division defect graph is empty. -/
theorem criticalCore_isCoMultipartite_of_defectGraph_eq_bot
    (G : SimpleGraph V) (D : SupercriticalDivision k V)
    (hdefect : supercriticalDefectGraph G D = ⊥) :
    DenseGraph.IsCoMultipartite
      (G.induce ({v : V | v ∉ D.sparse} : Set V)) (k - 1) :=
  ⟨{
    parts := criticalCoreParts D
    cover := criticalCoreParts_cover D
    pairwiseDisjoint := criticalCoreParts_pairwiseDisjoint D
    isClique := criticalCoreParts_isClique_of_defectGraph_eq_bot G D hdefect
  }⟩

/-- With zero ordinary defect, the original graph is exactly the supremum of
its induced support and sparse components.  The key content is the absence of
cross edges, not merely an edit-distance statement. -/
theorem graph_eq_core_induce_sup_sparse_induce_of_defectGraph_eq_bot
    (G : SimpleGraph V) (D : SupercriticalDivision k V)
    (hdefect : supercriticalDefectGraph G D = ⊥) :
    G =
      (G.induce ({v : V | v ∉ D.sparse} : Set V)).spanningCoe ⊔
        (G.induce (D.sparse : Set V)).spanningCoe := by
  apply le_antisymm
  · intro x y hxy
    by_cases hx : x ∈ D.sparse
    · have hy : y ∈ D.sparse := by
        by_contra hyn
        have hySupport : y ∈ D.support := by simpa using hyn
        exact (not_adj_support_sparse_of_supercriticalDefectGraph_eq_bot
          G D hdefect hySupport hx) hxy.symm
      apply (SimpleGraph.sup_adj _ _ x y).2
      right
      rw [SimpleGraph.map_adj]
      exact ⟨⟨x, hx⟩, ⟨y, hy⟩, hxy, rfl, rfl⟩
    · have hxSupport : x ∈ D.support := by simpa using hx
      have hy : y ∉ D.sparse := by
        intro hys
        exact (not_adj_support_sparse_of_supercriticalDefectGraph_eq_bot
          G D hdefect hxSupport hys) hxy
      apply (SimpleGraph.sup_adj _ _ x y).2
      left
      rw [SimpleGraph.map_adj]
      exact ⟨⟨x, hx⟩, ⟨y, hy⟩, hxy, rfl, rfl⟩
  · apply sup_le
    · exact G.spanningCoe_induce_le
        ({v : V | v ∉ D.sparse} : Set V)
    · exact G.spanningCoe_induce_le (D.sparse : Set V)

/-! ## Critical witnesses from clean canonical divisions -/

/-- A zero-defect division gives the transparent literal critical structure
witness, with its sparse set as the exceptional vertex set. -/
def criticalStructureWitnessOfCleanDivision
    {n : ℕ} (G : SimpleGraph (Fin n))
    (D : SupercriticalDivision k (Fin n))
    (hdefect : supercriticalDefectGraph G D = ⊥) :
    CriticalStructureWitness k n G where
  exceptionalVertices := D.sparse
  core := G.induce ({v : Fin n | v ∉ D.sparse} : Set (Fin n))
  remainder := G.induce (D.sparse : Set (Fin n))
  coreCoMultipartite :=
    criticalCore_isCoMultipartite_of_defectGraph_eq_bot G D hdefect
  decomposition :=
    graph_eq_core_induce_sup_sparse_induce_of_defectGraph_eq_bot G D hdefect

/-- Membership in a clean canonical-division family, together with a bound on
the sparse set, produces the corresponding critical structure property. -/
theorem hasCriticalStructure_of_mem_supercriticalCleanDivisionGraphFinset
    {n m : ℕ} {hk : 3 ≤ k} {gamma : ℝ}
    {hgamma : gamma ∈ Set.Ico (gammaK k) 1}
    {tau : ℝ} {hn : k - 1 ≤ n}
    {D : SupercriticalDivision k (Fin n)} {G : SimpleGraph (Fin n)}
    {exceptionalBound : ℕ}
    (hG : G ∈ supercriticalCleanDivisionGraphFinset
      k hk gamma hgamma m n tau hn D)
    (hsparse : D.sparse.card ≤ exceptionalBound) :
    HasCriticalStructure k exceptionalBound G := by
  have hcanonical :=
    (mem_supercriticalCleanDivisionGraphFinset.mp hG).2.1
  have hzeroCanonical :=
    (mem_supercriticalCleanDivisionGraphFinset.mp hG).2.2
  have hzero :
      (finiteGraphEdges (supercriticalDefectGraph G D)).card = 0 := by
    simpa [canonicalSupercriticalDefectGraph, hcanonical] using hzeroCanonical
  have hdefect : supercriticalDefectGraph G D = ⊥ :=
    simpleGraph_eq_bot_of_finiteGraphEdges_card_eq_zero _ hzero
  exact ⟨criticalStructureWitnessOfCleanDivision G D hdefect, hsparse⟩

/-! ## Endpoint-valid optimizer-far specialization -/

/-- The critical density belongs to the closed supercritical interval. -/
theorem gammaK_mem_supercritical_Ico (k : ℕ) (hk : 3 ≤ k) :
    gammaK k ∈ Set.Ico (gammaK k) 1 :=
  ⟨le_rfl, gammaK_lt_one hk⟩

/-- Exact critical-edge graphs which remain at least `tau` in cut distance
from the distinguished endpoint optimizer. -/
noncomputable def criticalFarGraphFinset
    (k : ℕ) (hk : 3 ≤ k) (n : ℕ) (tau : ℝ) :
    Finset (SimpleGraph (Fin n)) :=
  supercriticalFarGraphFinset k hk (gammaK k)
    (gammaK_mem_supercritical_Ico k hk) (criticalEdgeCount k n) n tau

@[simp] theorem mem_criticalFarGraphFinset
    {k n : ℕ} {hk : 3 ≤ k} {tau : ℝ}
    {G : SimpleGraph (Fin n)} :
    G ∈ criticalFarGraphFinset k hk n tau ↔
      G ∈ criticalInducedStarFreeGraphFinset k n ∧
        tau ≤ cutDist (graphGraphon G)
          (Wstar k hk (gammaK k) (gammaK_mem_supercritical_Ico k hk)) := by
  rw [criticalFarGraphFinset, mem_supercriticalFarGraphFinset,
    mem_criticalInducedStarFreeGraphFinset]
  tauto

/-- The optimizer-far critical family has an eventual quadratic exponential
penalty.  This is the exact-endpoint specialization of the endpoint-valid
rough-structure theorem. -/
theorem eventually_criticalFarTotal_le
    (k : ℕ) (hk : 3 ≤ k) (tau : ℝ) (htau : 0 < tau) :
    ∃ cFar : ℝ, 0 < cFar ∧
      ∀ᶠ n in atTop,
        ((criticalFarGraphFinset k hk n tau).card : ℝ) ≤
          (criticalInducedStarFreeGraphCount k n : ℝ) *
            Real.exp (-cFar * (n : ℝ) ^ 2) := by
  obtain ⟨cFar, hcFar, hfar⟩ :=
    eventually_supercriticalFarTotal_le k hk (gammaK k)
      (gammaK_mem_supercritical_Ico k hk) tau htau
  refine ⟨cFar, hcFar, ?_⟩
  have hbound := hfar (criticalEdgeCount k)
    (criticalEdgeCount_hasAsymptoticEdgeDensity hk)
  filter_upwards [hbound] with n hn
  change
    ((supercriticalFarGraphFinset k hk (gammaK k)
      (gammaK_mem_supercritical_Ico k hk)
      (criticalEdgeCount k n) n tau).card : ℝ) ≤
        (inducedStarFreeGraphCountWithEdges k n
          (criticalEdgeCount k n) : ℝ) *
          Real.exp (-cFar * (n : ℝ) ^ 2)
  exact hn

end InducedStars
