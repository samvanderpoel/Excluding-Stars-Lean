import InducedStars.Structure.Subcritical.StructureWitness
import InducedStars.Structure.Subcritical.ActiveModels

/-!
# Exact component structure from an empty retained-incident defect

These are deterministic implications. No random-model concentration or
uniqueness statement is assumed in constructing the actual induced core.
-/

noncomputable section
open Finset Set
open scoped Classical
namespace InducedStars

variable {k : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} {D : SubcriticalDivision k V} {eta : ℝ} {R₀ : ℕ}

theorem subcriticalIncidentClean_model_adj_iff
    (hclean : subcriticalRetainedIncidentDefectGraph G D eta R₀ = ⊥)
    {x y : V} (hx : x ∈ D.retainedVertices eta R₀) :
    G.Adj x y ↔ (subcriticalDivisionModelGraph G D).Adj x y := by
  have hxs : x ∉ D.sparse := by
    intro hs
    exact (D.mem_sparse.mp hs) (D.retainedVertices_subset_support eta R₀ hx)
  have heq : G.Adj x y = (subcriticalDivisionModelGraph G D).Adj x y := by
    by_contra h
    have hdef : (subcriticalDefectGraph G D).Adj x y :=
      (subcriticalDefectGraph_adj G D x y).mpr
        ⟨(subcriticalCombinedDefectGraph_adj G D x y).mpr h, fun h ↦ hxs h.1⟩
    have hi : (subcriticalRetainedIncidentDefectGraph G D eta R₀).Adj x y := ⟨hdef, Or.inl hx⟩
    simpa only [hclean, SimpleGraph.bot_adj] using hi
  exact heq.to_iff

theorem subcriticalIncidentClean_component_noCross
    (hclean : subcriticalRetainedIncidentDefectGraph G D eta R₀ = ⊥)
    (i : Fin D.componentCount) (hi : i ∈ D.retainedComponentIndices eta R₀) :
    ∀ x ∈ D.componentSupport i, ∀ y ∉ D.componentSupport i, ¬G.Adj x y := by
  intro x hx y hy hxy
  have hxret := (D.mem_retainedVertices eta R₀ x).mpr ⟨i, hi, hx⟩
  have hmodel := (subcriticalIncidentClean_model_adj_iff hclean hxret).mp hxy
  rcases (subcriticalDivisionModelGraph_adj G D x y).mp hmodel |>.2 with hs | ha
  · obtain ⟨a, hxa, hya⟩ := hs
    have hxi : x ∈ D.componentSupport a.1 := D.mem_componentSupport.mpr ⟨a.2, hxa⟩
    have heq : i = a.1 := by
      by_contra hne
      exact (Finset.disjoint_left.mp (D.componentSupport_disjoint hne)) hx hxi
    apply hy
    rw [heq]
    exact D.mem_componentSupport.mpr ⟨a.2, hya⟩
  · obtain ⟨j, a, b, _, hxa, hyb⟩ := ha.1
    have hxj : x ∈ D.componentSupport j := D.mem_componentSupport.mpr ⟨a, hxa⟩
    have heq : i = j := by
      by_contra hne
      exact (Finset.disjoint_left.mp (D.componentSupport_disjoint hne)) hx hxj
    apply hy
    rw [heq]
    exact D.mem_componentSupport.mpr ⟨b, hyb⟩

/-- The actual original parts partition the induced retained component into
cliques. No balance assumption or abstract coloring replaces these parts. -/
def subcriticalIncidentClean_componentCliqueCover
    (hclean : subcriticalRetainedIncidentDefectGraph G D eta R₀ = ⊥)
    (i : Fin D.componentCount) (hi : i ∈ D.retainedComponentIndices eta R₀) :
    DenseGraph.CoMultipartiteWitness (G.induce (D.componentSupport i : Set V))
      (D.core i).order where
  parts a := Finset.univ.filter fun v ↦ v.val ∈ D.parts i a
  cover := by
    ext v
    simp only [Finset.mem_biUnion, Finset.mem_univ, Finset.mem_filter, true_and, iff_true]
    exact D.mem_componentSupport.mp v.property
  pairwiseDisjoint := by
    intro a _ b _ hab
    apply Finset.disjoint_left.mpr
    intro v hva hvb
    have heq := D.mem_part_unique (a := ⟨i, a⟩) (b := ⟨i, b⟩)
      (Finset.mem_filter.mp hva).2 (Finset.mem_filter.mp hvb).2
    have hab' : a = b := by simpa only [Sigma.mk.inj_iff, heq_eq_eq, true_and] using heq
    exact hab hab'
  isClique := by
    intro a x hx y hy hne
    have hxa : x.val ∈ D.parts i a := (Finset.mem_filter.mp hx).2
    have hya : y.val ∈ D.parts i a := (Finset.mem_filter.mp hy).2
    have hxret := (D.mem_retainedVertices eta R₀ x.val).mpr ⟨i, hi, x.property⟩
    apply (subcriticalIncidentClean_model_adj_iff hclean hxret).mpr
    exact (subcriticalDivisionModelGraph_adj G D x.val y.val).mpr
      ⟨fun h ↦ hne (Subtype.ext h), Or.inl ⟨⟨i, a⟩, hxa, hya⟩⟩

/-- A retained component with core order k-1 supplies a literal structural
witness. Other components, if present, are part of the induced remainder. -/
def subcriticalStructureWitness_of_incidentClean
    {n : ℕ} {G : SimpleGraph (Fin n)} {D : SubcriticalDivision k (Fin n)}
    (hclean : subcriticalRetainedIncidentDefectGraph G D eta R₀ = ⊥)
    (i : Fin D.componentCount) (hi : i ∈ D.retainedComponentIndices eta R₀)
    (horder : (D.core i).order = k - 1) : SubcriticalStructureWitness k n G where
  coreVertices := D.componentSupport i
  noCross := subcriticalIncidentClean_component_noCross hclean i hi
  coreCoMultipartite := by
    rw [← horder]
    exact ⟨subcriticalIncidentClean_componentCliqueCover hclean i hi⟩

end InducedStars
