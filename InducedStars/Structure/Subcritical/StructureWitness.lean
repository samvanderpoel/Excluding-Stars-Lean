import InducedStars.Structure.Critical.Basic
import InducedStars.Structure.Subcritical.DistinguishedReference

/-!
# Literal subcritical decompositions and their exact finite events

The same vertex set witnesses every size and edge inequality. The lower
edge coefficient is a separate parameter, to be chosen before the accuracy.
-/

noncomputable section
open Finset Set
open scoped Classical
namespace InducedStars

/-- An actual co-multipartite induced core disconnected from its induced
remainder. This is stronger than a cut-distance or edit-distance witness. -/
structure SubcriticalStructureWitness (k n : ℕ) (G : SimpleGraph (Fin n)) where
  coreVertices : Finset (Fin n)
  noCross : ∀ x ∈ coreVertices, ∀ y ∉ coreVertices, ¬G.Adj x y
  coreCoMultipartite : DenseGraph.IsCoMultipartite
    (G.induce (coreVertices : Set (Fin n))) (k - 1)

namespace SubcriticalStructureWitness

variable {k n : ℕ} {G : SimpleGraph (Fin n)} (W : SubcriticalStructureWitness k n G)

def coreGraph : SimpleGraph (W.coreVertices : Set (Fin n)) :=
  G.induce (W.coreVertices : Set (Fin n))

def remainderGraph : SimpleGraph ({v : Fin n | v ∉ W.coreVertices} : Set (Fin n)) :=
  G.induce ({v : Fin n | v ∉ W.coreVertices} : Set (Fin n))

/-- Literal disjoint union on complementary induced vertex sets. -/
theorem disjointUnion : G = W.coreGraph.spanningCoe ⊔ W.remainderGraph.spanningCoe := by
  rw [sup_comm]
  exact graph_eq_complement_induce_sup_induce_of_noCross G
    (W.coreVertices : Set (Fin n)) W.noCross

def remainderEdgeCount : ℕ := (finiteGraphEdges W.remainderGraph).card

def SatisfiesBounds (gamma cLower xi : ℝ) : Prop :=
  |(W.coreVertices.card : ℝ) / n - subcriticalOneBlockLength k gamma| ≤ xi ∧
    cLower * n ≤ W.remainderEdgeCount ∧ W.remainderEdgeCount ≤ xi * (n : ℝ) ^ 2

end SubcriticalStructureWitness

/-- The simultaneous subcritical structural event. Its existential vertex
set cannot vary between the upper and lower remainder-edge bounds. -/
def HasSubcriticalStructure {n : ℕ} (k : ℕ) (gamma cLower xi : ℝ)
    (G : SimpleGraph (Fin n)) : Prop :=
  ∃ W : SubcriticalStructureWitness k n G, W.SatisfiesBounds gamma cLower xi

def subcriticalStructuredGraphFinset (k n m : ℕ) (gamma cLower xi : ℝ) :
    Finset (SimpleGraph (Fin n)) :=
  (inducedStarFreeGraphFinsetWithEdges k n m).filter (HasSubcriticalStructure k gamma cLower xi)

def subcriticalUnstructuredGraphFinset (k n m : ℕ) (gamma cLower xi : ℝ) :
    Finset (SimpleGraph (Fin n)) :=
  inducedStarFreeGraphFinsetWithEdges k n m \ subcriticalStructuredGraphFinset k n m gamma cLower xi

@[simp] theorem mem_subcriticalStructuredGraphFinset
    {k n m : ℕ} {gamma cLower xi : ℝ} {G : SimpleGraph (Fin n)} :
    G ∈ subcriticalStructuredGraphFinset k n m gamma cLower xi ↔
      G ∈ inducedStarFreeGraphFinsetWithEdges k n m ∧ HasSubcriticalStructure k gamma cLower xi G := by
  simp only [subcriticalStructuredGraphFinset, Finset.mem_filter]

@[simp] theorem mem_subcriticalUnstructuredGraphFinset
    {k n m : ℕ} {gamma cLower xi : ℝ} {G : SimpleGraph (Fin n)} :
    G ∈ subcriticalUnstructuredGraphFinset k n m gamma cLower xi ↔
      G ∈ inducedStarFreeGraphFinsetWithEdges k n m ∧ ¬HasSubcriticalStructure k gamma cLower xi G := by
  simp only [subcriticalUnstructuredGraphFinset, Finset.mem_sdiff,
    mem_subcriticalStructuredGraphFinset]
  tauto

theorem subcriticalStructuredGraphFinset_subset (k n m : ℕ) (gamma cLower xi : ℝ) :
    subcriticalStructuredGraphFinset k n m gamma cLower xi ⊆
      inducedStarFreeGraphFinsetWithEdges k n m := Finset.filter_subset _ _

theorem subcriticalStructured_disjoint_unstructured (k n m : ℕ) (gamma cLower xi : ℝ) :
    Disjoint (subcriticalStructuredGraphFinset k n m gamma cLower xi)
      (subcriticalUnstructuredGraphFinset k n m gamma cLower xi) := by
  apply Finset.disjoint_left.mpr
  intro G hgood hbad
  exact (Finset.mem_sdiff.mp hbad).2 hgood

theorem subcriticalStructured_union_unstructured (k n m : ℕ) (gamma cLower xi : ℝ) :
    subcriticalStructuredGraphFinset k n m gamma cLower xi ∪
      subcriticalUnstructuredGraphFinset k n m gamma cLower xi =
      inducedStarFreeGraphFinsetWithEdges k n m :=
  Finset.union_sdiff_of_subset (subcriticalStructuredGraphFinset_subset k n m gamma cLower xi)

def subcriticalStructuredProbability (k : ℕ) (gamma cLower xi : ℝ) (n m : ℕ) : ℝ :=
  uniformSubfamilyProbability (inducedStarFreeGraphFinsetWithEdges k n m)
    (subcriticalStructuredGraphFinset k n m gamma cLower xi)

def subcriticalUnstructuredProbability (k : ℕ) (gamma cLower xi : ℝ) (n m : ℕ) : ℝ :=
  uniformSubfamilyProbability (inducedStarFreeGraphFinsetWithEdges k n m)
    (subcriticalUnstructuredGraphFinset k n m gamma cLower xi)

theorem subcriticalStructuredProbability_add_unstructuredProbability
    (k n m : ℕ) (gamma cLower xi : ℝ)
    (hpos : 0 < (inducedStarFreeGraphFinsetWithEdges k n m).card) :
    subcriticalStructuredProbability k gamma cLower xi n m +
      subcriticalUnstructuredProbability k gamma cLower xi n m = 1 := by
  have hcard := Finset.card_union_of_disjoint
    (subcriticalStructured_disjoint_unstructured k n m gamma cLower xi)
  rw [subcriticalStructured_union_unstructured] at hcard
  have hcardR : ((subcriticalStructuredGraphFinset k n m gamma cLower xi).card : ℝ) +
      (subcriticalUnstructuredGraphFinset k n m gamma cLower xi).card =
      (inducedStarFreeGraphFinsetWithEdges k n m).card := by exact_mod_cast hcard.symm
  change (_ : ℝ) / _ + _ / _ = 1
  rw [← add_div, hcardR, div_self (by exact_mod_cast hpos.ne')]

end InducedStars
