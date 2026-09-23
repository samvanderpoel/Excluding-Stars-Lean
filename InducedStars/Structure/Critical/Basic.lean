import InducedStars.Asymptotics.GnpDensity
import InducedStars.Structure.Supercritical.CoPartiteFamilies

/-!
# Finite critical families and structure witnesses

This file fixes the exact edge-count sequence at `gammaK k`, the corresponding
labeled induced-star-free sample space, and a transparent finite witness for
the critical structural conclusion.  The size bound on the exceptional
vertex set is kept as a natural-number parameter; the later critical cleanup
will specialize it to a logarithmic bound.
-/

noncomputable section

open Filter Set Topology

namespace InducedStars

noncomputable local instance criticalEdgeSetFintype
    {n : ℕ} (G : SimpleGraph (Fin n)) : Fintype G.edgeSet :=
  Fintype.ofFinite G.edgeSet

noncomputable local instance criticalSimpleGraphDecidableEq
    (n : ℕ) : DecidableEq (SimpleGraph (Fin n)) :=
  Classical.decEq _

/-! ## The canonical critical edge count -/

/-- The exact edge count in the critical clause of the main theorem. -/
def criticalEdgeCount (k n : ℕ) : ℕ :=
  floorEdgeCountSequence (gammaK k) n

/-- The critical edge count never exceeds the number of available unordered
vertex pairs. -/
theorem criticalEdgeCount_le_completeEdgeCount
    {k : ℕ} (hk : 3 ≤ k) (n : ℕ) :
    criticalEdgeCount k n ≤ completeEdgeCount n := by
  exact floorEdgeCountSequence_le_completeEdgeCount
    ⟨(gammaK_pos hk).le, (gammaK_lt_one hk).le⟩ n

/-- The real-valued critical edge count is below its unrounded target. -/
theorem criticalEdgeCount_cast_le
    {k : ℕ} (hk : 3 ≤ k) (n : ℕ) :
    (criticalEdgeCount k n : ℝ) ≤
      gammaK k * (completeEdgeCount n : ℝ) := by
  unfold criticalEdgeCount floorEdgeCountSequence
  exact Nat.floor_le (mul_nonneg (gammaK_pos hk).le (Nat.cast_nonneg _))

/-- Flooring changes the critical edge target by a nonnegative amount less
than one. -/
theorem criticalEdgeCount_floor_error
    {k : ℕ} (hk : 3 ≤ k) (n : ℕ) :
    0 ≤ gammaK k * (completeEdgeCount n : ℝ) -
        (criticalEdgeCount k n : ℝ) ∧
      gammaK k * (completeEdgeCount n : ℝ) -
        (criticalEdgeCount k n : ℝ) < 1 := by
  constructor
  · exact sub_nonneg.mpr (criticalEdgeCount_cast_le hk n)
  · have hfloor :=
      Nat.lt_floor_add_one (gammaK k * (completeEdgeCount n : ℝ))
    unfold criticalEdgeCount floorEdgeCountSequence
    linarith

/-- The canonical critical edge-count sequence has asymptotic density
`gammaK k`. -/
theorem criticalEdgeCount_hasAsymptoticEdgeDensity
    {k : ℕ} (hk : 3 ≤ k) :
    HasAsymptoticEdgeDensity (criticalEdgeCount k) (gammaK k) := by
  exact floorEdgeCountSequence_hasAsymptoticEdgeDensity
    ⟨(gammaK_pos hk).le, (gammaK_lt_one hk).le⟩

/-! ## The exact critical sample space -/

/-- Labeled induced-`K₁,ₖ`-free graphs with the canonical critical number of
edges. -/
noncomputable def criticalInducedStarFreeGraphFinset
    (k n : ℕ) : Finset (SimpleGraph (Fin n)) :=
  inducedStarFreeGraphFinsetWithEdges k n (criticalEdgeCount k n)

@[simp] theorem mem_criticalInducedStarFreeGraphFinset
    {k n : ℕ} {G : SimpleGraph (Fin n)} :
    G ∈ criticalInducedStarFreeGraphFinset k n ↔
      ¬Regularity.InducedEmbeds (inducedStar k) G ∧
        G.edgeFinset.card = criticalEdgeCount k n := by
  exact mem_inducedStarFreeGraphFinsetWithEdges

/-- The number of labeled graphs in the exact critical sample space. -/
noncomputable def criticalInducedStarFreeGraphCount (k n : ℕ) : ℕ :=
  (criticalInducedStarFreeGraphFinset k n).card

@[simp] theorem criticalInducedStarFreeGraphCount_eq_card (k n : ℕ) :
    criticalInducedStarFreeGraphCount k n =
      (criticalInducedStarFreeGraphFinset k n).card :=
  rfl

/-- Uniform mass of a finite event relative to the exact critical
induced-star-free sample space. -/
noncomputable def criticalUniformProbability
    (k n : ℕ) (A : Finset (SimpleGraph (Fin n))) : ℝ :=
  uniformSubfamilyProbability (criticalInducedStarFreeGraphFinset k n) A

theorem criticalUniformProbability_eq_card_ratio
    (k n : ℕ) (A : Finset (SimpleGraph (Fin n))) :
    criticalUniformProbability k n A =
      (A.card : ℝ) / (criticalInducedStarFreeGraphCount k n : ℝ) :=
  rfl

/-! ## A literal critical decomposition witness -/

/-- A witness that `G` is a disjoint union of a co-`(k-1)`-partite graph and
a graph on an exceptional vertex set.

The two component graphs live on complementary subtype vertex sets.  Their
spanning coercions therefore contain no cross edges, and `decomposition`
asserts literal equality with `G`, rather than equality only up to graph
isomorphism. -/
structure CriticalStructureWitness
    (k n : ℕ) (G : SimpleGraph (Fin n)) where
  exceptionalVertices : Finset (Fin n)
  core : SimpleGraph ({v : Fin n | v ∉ exceptionalVertices} : Set (Fin n))
  remainder : SimpleGraph ({v : Fin n | v ∈ exceptionalVertices} : Set (Fin n))
  coreCoMultipartite : DenseGraph.IsCoMultipartite core (k - 1)
  decomposition : G = core.spanningCoe ⊔ remainder.spanningCoe

namespace CriticalStructureWitness

variable {k n : ℕ} {G : SimpleGraph (Fin n)}
    (W : CriticalStructureWitness k n G)

/-- The core component, viewed as a spanning graph on `Fin n`. -/
def coreSpanning : SimpleGraph (Fin n) :=
  W.core.spanningCoe

/-- The exceptional component, viewed as a spanning graph on `Fin n`. -/
def remainderSpanning : SimpleGraph (Fin n) :=
  W.remainder.spanningCoe

/-- The witness gives a literal union decomposition on the ambient labeled
vertex set. -/
theorem graph_eq_coreSpanning_sup_remainderSpanning :
    G = W.coreSpanning ⊔ W.remainderSpanning :=
  W.decomposition

/-- Every vertex incident to a core edge is outside the exceptional set. -/
theorem coreSpanning_support_subset :
    W.coreSpanning.support ⊆
      {v : Fin n | v ∉ W.exceptionalVertices} := by
  intro v hv
  rw [coreSpanning,
    SimpleGraph.support_spanningCoe
      (s := {v : Fin n | v ∉ W.exceptionalVertices}) W.core] at hv
  obtain ⟨u, _hu, rfl⟩ := hv
  exact u.property

/-- Every vertex incident to a remainder edge lies in the exceptional set. -/
theorem remainderSpanning_support_subset :
    W.remainderSpanning.support ⊆
      {v : Fin n | v ∈ W.exceptionalVertices} := by
  intro v hv
  rw [remainderSpanning,
    SimpleGraph.support_spanningCoe
      (s := {v : Fin n | v ∈ W.exceptionalVertices}) W.remainder] at hv
  obtain ⟨u, _hu, rfl⟩ := hv
  exact u.property

/-- The two spanning components are edge-disjoint. -/
theorem coreSpanning_disjoint_remainderSpanning :
    Disjoint W.coreSpanning W.remainderSpanning := by
  apply SimpleGraph.disjoint_of_disjoint_support
  rw [Set.disjoint_left]
  intro v hvCore hvRemainder
  exact (W.coreSpanning_support_subset hvCore)
    (W.remainderSpanning_support_subset hvRemainder)

/-- The core spanning component is a subgraph of `G`. -/
theorem coreSpanning_le_graph : W.coreSpanning ≤ G := by
  intro u v huv
  have hsup : (W.coreSpanning ⊔ W.remainderSpanning).Adj u v :=
    (SimpleGraph.sup_adj W.coreSpanning W.remainderSpanning u v).2 (Or.inl huv)
  have hdecomp := congrArg (fun H : SimpleGraph (Fin n) ↦ H.Adj u v)
    W.graph_eq_coreSpanning_sup_remainderSpanning
  exact hdecomp.symm.mp hsup

/-- The exceptional spanning component is a subgraph of `G`. -/
theorem remainderSpanning_le_graph : W.remainderSpanning ≤ G := by
  intro u v huv
  have hsup : (W.coreSpanning ⊔ W.remainderSpanning).Adj u v :=
    (SimpleGraph.sup_adj W.coreSpanning W.remainderSpanning u v).2 (Or.inr huv)
  have hdecomp := congrArg (fun H : SimpleGraph (Fin n) ↦ H.Adj u v)
    W.graph_eq_coreSpanning_sup_remainderSpanning
  exact hdecomp.symm.mp hsup

/-- There are no edges of `G` between the exceptional set and its
complement. -/
theorem not_adj_of_mem_exceptional_of_not_mem
    {u v : Fin n} (hu : u ∈ W.exceptionalVertices)
    (hv : v ∉ W.exceptionalVertices) : ¬G.Adj u v := by
  intro huv
  have hdecomp := congrArg (fun H : SimpleGraph (Fin n) ↦ H.Adj u v)
    W.graph_eq_coreSpanning_sup_remainderSpanning
  have hsup : (W.coreSpanning ⊔ W.remainderSpanning).Adj u v :=
    hdecomp.mp huv
  rcases (SimpleGraph.sup_adj W.coreSpanning W.remainderSpanning u v).mp hsup with
    hcore | hremainder
  · exact (W.coreSpanning_support_subset hcore.left_mem_support) hu
  · exact hv (W.remainderSpanning_support_subset
      hremainder.right_mem_support)

/-- The core stored by a critical witness is exactly the graph induced by
the complement of its exceptional set. -/
theorem induce_complement_eq_core :
    G.induce ({v : Fin n | v ∉ W.exceptionalVertices} : Set (Fin n)) =
      W.core := by
  apply le_antisymm
  · intro x y hxy
    change G.Adj x.1 y.1 at hxy
    have hsup : (W.coreSpanning ⊔ W.remainderSpanning).Adj x.1 y.1 := by
      rw [← W.graph_eq_coreSpanning_sup_remainderSpanning]
      exact hxy
    rcases (SimpleGraph.sup_adj W.coreSpanning W.remainderSpanning
      x.1 y.1).mp hsup with hcore | hremainder
    · unfold coreSpanning at hcore
      rw [SimpleGraph.map_adj] at hcore
      obtain ⟨a, b, hab, ha, hb⟩ := hcore
      have hax : a = x := Subtype.ext ha
      have hby : b = y := Subtype.ext hb
      simpa [hax, hby] using hab
    · exact (x.2 (W.remainderSpanning_support_subset
        hremainder.left_mem_support)).elim
  · intro x y hxy
    change G.Adj x.1 y.1
    apply W.coreSpanning_le_graph
    unfold coreSpanning
    rw [SimpleGraph.map_adj]
    exact ⟨x, y, hxy, rfl, rfl⟩

end CriticalStructureWitness

/-! ## Direct vertex-set form of the decomposition -/

/-- If a finite graph has no edge across a set and its complement, it is
literally the supremum of the two induced spanning subgraphs. -/
theorem graph_eq_complement_induce_sup_induce_of_noCross
    {V : Type*} [Fintype V] (G : SimpleGraph V) (S : Set V)
    (hcross : ∀ x, x ∈ S → ∀ y, y ∉ S → ¬G.Adj x y) :
    G = (G.induce ({v : V | v ∉ S} : Set V)).spanningCoe ⊔
      (G.induce S).spanningCoe := by
  apply le_antisymm
  · intro x y hxy
    by_cases hx : x ∈ S
    · have hy : y ∈ S := by
        by_contra hyn
        exact hcross x hx y hyn hxy
      apply (SimpleGraph.sup_adj _ _ x y).2
      right
      rw [SimpleGraph.map_adj]
      exact ⟨⟨x, hx⟩, ⟨y, hy⟩, hxy, rfl, rfl⟩
    · have hy : y ∉ S := by
        intro hys
        exact hcross y hys x hx hxy.symm
      apply (SimpleGraph.sup_adj _ _ x y).2
      left
      rw [SimpleGraph.map_adj]
      exact ⟨⟨x, hx⟩, ⟨y, hy⟩, hxy, rfl, rfl⟩
  · apply sup_le
    · exact G.spanningCoe_induce_le ({v : V | v ∉ S} : Set V)
    · exact G.spanningCoe_induce_le S

/-! ## Structured and unstructured critical families -/

/-- `G` has the critical structure with at most `exceptionalBound`
exceptional vertices. -/
def HasCriticalStructure
    (k exceptionalBound : ℕ) {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∃ W : CriticalStructureWitness k n G,
    W.exceptionalVertices.card ≤ exceptionalBound

/-- Direct vertex-set formulation of the critical conclusion: the displayed
set is small, no graph edge crosses its boundary, and the induced graph on
its complement is co-`(k-1)`-partite. -/
def HasCriticalVertexSetStructure
    (k exceptionalBound : ℕ) {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∃ S : Finset (Fin n),
    S.card ≤ exceptionalBound ∧
      (∀ x, x ∈ S → ∀ y, y ∉ S → ¬G.Adj x y) ∧
      DenseGraph.IsCoMultipartite
        (G.induce ({v : Fin n | v ∉ S} : Set (Fin n))) (k - 1)

/-- The transparent witness and direct vertex-set formulations are exactly
equivalent, including the literal no-cross-edge condition. -/
theorem hasCriticalStructure_iff_vertexSet
    {k exceptionalBound n : ℕ} {G : SimpleGraph (Fin n)} :
    HasCriticalStructure k exceptionalBound G ↔
      HasCriticalVertexSetStructure k exceptionalBound G := by
  constructor
  · rintro ⟨W, hcard⟩
    refine ⟨W.exceptionalVertices, hcard, ?_, ?_⟩
    · intro x hx y hy
      exact W.not_adj_of_mem_exceptional_of_not_mem hx hy
    · rw [W.induce_complement_eq_core]
      exact W.coreCoMultipartite
  · rintro ⟨S, hcard, hcross, hcore⟩
    refine ⟨{
      exceptionalVertices := S
      core := G.induce ({v : Fin n | v ∉ S} : Set (Fin n))
      remainder := G.induce (S : Set (Fin n))
      coreCoMultipartite := hcore
      decomposition :=
        graph_eq_complement_induce_sup_induce_of_noCross G S hcross
    }, hcard⟩

theorem HasCriticalStructure.mono
    {k n a b : ℕ} {G : SimpleGraph (Fin n)}
    (h : HasCriticalStructure k a G) (hab : a ≤ b) :
    HasCriticalStructure k b G := by
  obtain ⟨W, hW⟩ := h
  exact ⟨W, hW.trans hab⟩

/-- Critical induced-star-free graphs admitting a critical structure witness
with the displayed exceptional-vertex bound. -/
noncomputable def criticalStructuredGraphFinset
    (k n exceptionalBound : ℕ) : Finset (SimpleGraph (Fin n)) := by
  classical
  exact (criticalInducedStarFreeGraphFinset k n).filter fun G ↦
    HasCriticalStructure k exceptionalBound G

@[simp] theorem mem_criticalStructuredGraphFinset
    {k n exceptionalBound : ℕ} {G : SimpleGraph (Fin n)} :
    G ∈ criticalStructuredGraphFinset k n exceptionalBound ↔
      G ∈ criticalInducedStarFreeGraphFinset k n ∧
        HasCriticalStructure k exceptionalBound G := by
  classical
  simp [criticalStructuredGraphFinset]

/-- Membership in the structured family, stated with the literal exceptional
vertex set rather than the bundled witness. -/
theorem mem_criticalStructuredGraphFinset_iff_vertexSet
    {k n exceptionalBound : ℕ} {G : SimpleGraph (Fin n)} :
    G ∈ criticalStructuredGraphFinset k n exceptionalBound ↔
      G ∈ criticalInducedStarFreeGraphFinset k n ∧
        HasCriticalVertexSetStructure k exceptionalBound G := by
  rw [mem_criticalStructuredGraphFinset,
    hasCriticalStructure_iff_vertexSet]

/-- Critical induced-star-free graphs with no critical structure witness at
the displayed exceptional-vertex bound. -/
noncomputable def criticalUnstructuredGraphFinset
    (k n exceptionalBound : ℕ) : Finset (SimpleGraph (Fin n)) :=
  criticalInducedStarFreeGraphFinset k n \
    criticalStructuredGraphFinset k n exceptionalBound

@[simp] theorem mem_criticalUnstructuredGraphFinset
    {k n exceptionalBound : ℕ} {G : SimpleGraph (Fin n)} :
    G ∈ criticalUnstructuredGraphFinset k n exceptionalBound ↔
      G ∈ criticalInducedStarFreeGraphFinset k n ∧
        ¬HasCriticalStructure k exceptionalBound G := by
  classical
  rw [criticalUnstructuredGraphFinset, Finset.mem_sdiff]
  constructor
  · intro h
    exact ⟨h.1, fun hstructure ↦
      h.2 (mem_criticalStructuredGraphFinset.mpr ⟨h.1, hstructure⟩)⟩
  · intro h
    exact ⟨h.1, fun hstructured ↦
      h.2 (mem_criticalStructuredGraphFinset.mp hstructured).2⟩

theorem criticalStructuredGraphFinset_subset
    (k n exceptionalBound : ℕ) :
    criticalStructuredGraphFinset k n exceptionalBound ⊆
      criticalInducedStarFreeGraphFinset k n := by
  intro G hG
  exact (mem_criticalStructuredGraphFinset.mp hG).1

theorem criticalUnstructuredGraphFinset_subset
    (k n exceptionalBound : ℕ) :
    criticalUnstructuredGraphFinset k n exceptionalBound ⊆
      criticalInducedStarFreeGraphFinset k n :=
  Finset.sdiff_subset

theorem criticalStructuredGraphFinset_mono
    {k n a b : ℕ} (hab : a ≤ b) :
    criticalStructuredGraphFinset k n a ⊆
      criticalStructuredGraphFinset k n b := by
  intro G hG
  rw [mem_criticalStructuredGraphFinset] at hG ⊢
  exact ⟨hG.1, hG.2.mono hab⟩

/-- Exact partition of the critical family into structured and unstructured
subfamilies. -/
theorem criticalStructured_union_unstructured
    (k n exceptionalBound : ℕ) :
    criticalStructuredGraphFinset k n exceptionalBound ∪
        criticalUnstructuredGraphFinset k n exceptionalBound =
      criticalInducedStarFreeGraphFinset k n := by
  exact Finset.union_sdiff_of_subset
    (criticalStructuredGraphFinset_subset k n exceptionalBound)

/-- The structured and unstructured critical subfamilies are disjoint. -/
theorem criticalStructured_disjoint_unstructured
    (k n exceptionalBound : ℕ) :
    Disjoint (criticalStructuredGraphFinset k n exceptionalBound)
      (criticalUnstructuredGraphFinset k n exceptionalBound) := by
  classical
  rw [Finset.disjoint_left]
  intro G hstructured hunstructured
  exact (Finset.mem_sdiff.mp hunstructured).2 hstructured

/-- Exact cardinality decomposition of the critical sample space. -/
theorem criticalInducedStarFreeGraphCount_eq_structured_add_unstructured
    (k n exceptionalBound : ℕ) :
    criticalInducedStarFreeGraphCount k n =
      (criticalStructuredGraphFinset k n exceptionalBound).card +
        (criticalUnstructuredGraphFinset k n exceptionalBound).card := by
  have hsub := criticalStructuredGraphFinset_subset k n exceptionalBound
  simpa [criticalInducedStarFreeGraphCount,
    criticalUnstructuredGraphFinset, Nat.add_comm] using
      (Finset.card_sdiff_add_card_eq_card hsub).symm

/-- Uniform probability of the structured critical subfamily. -/
noncomputable def criticalStructuredProbability
    (k n exceptionalBound : ℕ) : ℝ :=
  criticalUniformProbability k n
    (criticalStructuredGraphFinset k n exceptionalBound)

/-- Uniform probability of the complementary unstructured critical
subfamily. -/
noncomputable def criticalUnstructuredProbability
    (k n exceptionalBound : ℕ) : ℝ :=
  criticalUniformProbability k n
    (criticalUnstructuredGraphFinset k n exceptionalBound)

theorem criticalStructuredProbability_eq_card_ratio
    (k n exceptionalBound : ℕ) :
    criticalStructuredProbability k n exceptionalBound =
      ((criticalStructuredGraphFinset k n exceptionalBound).card : ℝ) /
        (criticalInducedStarFreeGraphCount k n : ℝ) :=
  rfl

theorem criticalUnstructuredProbability_eq_card_ratio
    (k n exceptionalBound : ℕ) :
    criticalUnstructuredProbability k n exceptionalBound =
      ((criticalUnstructuredGraphFinset k n exceptionalBound).card : ℝ) /
        (criticalInducedStarFreeGraphCount k n : ℝ) :=
  rfl

/-- Whenever the critical sample space is nonempty, the two complementary
probabilities sum to one. -/
theorem criticalStructuredProbability_add_unstructuredProbability
    {k n exceptionalBound : ℕ}
    (hne : (criticalInducedStarFreeGraphFinset k n).Nonempty) :
    criticalStructuredProbability k n exceptionalBound +
        criticalUnstructuredProbability k n exceptionalBound = 1 := by
  rw [criticalStructuredProbability_eq_card_ratio,
    criticalUnstructuredProbability_eq_card_ratio, ← add_div]
  have hcount :
      (criticalInducedStarFreeGraphCount k n : ℝ) =
        ((criticalStructuredGraphFinset k n exceptionalBound).card : ℝ) +
          ((criticalUnstructuredGraphFinset k n exceptionalBound).card : ℝ) := by
    exact_mod_cast
      criticalInducedStarFreeGraphCount_eq_structured_add_unstructured
        k n exceptionalBound
  rw [← hcount]
  exact div_self (by
    exact_mod_cast (Finset.card_pos.mpr hne).ne')

end InducedStars
