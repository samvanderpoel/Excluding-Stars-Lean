import InducedStars.C4.Basic
import DenseGraph.FiniteModels.GraphEdit

/-!
# Ordered split divisions and their exact defects

Paper: `paper/c4-free.tex`, beginning of the final counting argument.
The independent side determines the complementary clique side. Empty sides
are allowed, and the canonical minimization ranges over every division.
-/

noncomputable section

open Finset Set

namespace InducedStars

universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

/-- An ordered split division, encoded by its independent side. -/
abbrev C4Division (V : Type u) := Finset V

namespace C4Division

def independentPart (D : C4Division V) : Finset V := D
def cliquePart (D : C4Division V) : Finset V := Finset.univ \ D

@[simp] theorem mem_cliquePart (D : C4Division V) (v : V) :
    v ∈ D.cliquePart ↔ v ∉ D.independentPart := by
  simp [cliquePart, independentPart]

theorem disjoint (D : C4Division V) : Disjoint D.independentPart D.cliquePart := by
  exact Finset.disjoint_left.mpr fun v hv hw ↦ (D.mem_cliquePart v).mp hw hv

theorem cover (D : C4Division V) : D.independentPart ∪ D.cliquePart = Finset.univ := by
  ext v
  simp [independentPart, cliquePart]

theorem mem_or_mem (D : C4Division V) (v : V) :
    v ∈ D.independentPart ∨ v ∈ D.cliquePart := by
  classical
  rw [mem_cliquePart]
  exact Classical.em _

theorem card_add (D : C4Division V) :
    D.independentPart.card + D.cliquePart.card = Fintype.card V := by
  rw [← Finset.card_union_of_disjoint D.disjoint, D.cover, Finset.card_univ]

end C4Division

/-- A graph restricted to a vertex set, retaining the ambient vertex type
and making the other vertices isolated. -/
def c4WithinGraph (G : SimpleGraph V) (S : Finset V) : SimpleGraph V where
  Adj x y := x ∈ S ∧ y ∈ S ∧ G.Adj x y
  symm := ⟨by rintro x y ⟨hx, hy, hxy⟩; exact ⟨hy, hx, hxy.symm⟩⟩
  loopless := ⟨by intro x h; exact h.2.2.ne rfl⟩

@[simp] theorem c4WithinGraph_adj (G : SimpleGraph V) (S : Finset V) (x y : V) :
    (c4WithinGraph G S).Adj x y ↔ x ∈ S ∧ y ∈ S ∧ G.Adj x y := Iff.rfl

theorem finiteGraphEdges_c4WithinGraph (G : SimpleGraph V) (S : Finset V) :
    finiteGraphEdges (c4WithinGraph G S) =
      (finiteGraphEdges G).filter fun e ↦ e.toFinset ⊆ S := by
  classical
  ext e
  induction e using Sym2.inductionOn with
  | _ x y =>
      simp [c4WithinGraph, Sym2.toFinset_mk_eq, Finset.insert_subset_iff,
        Finset.singleton_subset_iff, and_comm, and_left_comm, and_assoc]

/-- The ambient restriction has exactly the edge count of the actual
induced graph; isolated ambient vertices contribute no edges. -/
theorem card_finiteGraphEdges_c4WithinGraph (G : SimpleGraph V) (S : Finset V) :
    (finiteGraphEdges (c4WithinGraph G S)).card =
      (finiteGraphEdges (G.induce (S : Set V))).card := by
  classical
  rw [finiteGraphEdges_c4WithinGraph]
  unfold finiteGraphEdges
  convert (SimpleGraph.card_filter_edgeFinset_toFinset_subset (G := G) S) using 1 <;> congr
  all_goals exact Subsingleton.elim _ _

/-- Positive defects in the independent side and missing clique edges in
the clique side, with no cross edges. -/
def c4DefectGraph (G : SimpleGraph V) (D : C4Division V) : SimpleGraph V :=
  c4WithinGraph G D.independentPart ⊔ c4WithinGraph Gᶜ D.cliquePart

@[simp] theorem c4DefectGraph_adj (G : SimpleGraph V) (D : C4Division V) (x y : V) :
    (c4DefectGraph G D).Adj x y ↔
      (x ∈ D.independentPart ∧ y ∈ D.independentPart ∧ G.Adj x y) ∨
      (x ∈ D.cliquePart ∧ y ∈ D.cliquePart ∧ x ≠ y ∧ ¬G.Adj x y) := by
  simp [c4DefectGraph, SimpleGraph.compl_adj]

theorem c4DefectGraph_not_adj_cross (G : SimpleGraph V) (D : C4Division V)
    {x y : V} (hx : x ∈ D.independentPart) (hy : y ∈ D.cliquePart) :
    ¬(c4DefectGraph G D).Adj x y := by
  rw [c4DefectGraph_adj]
  have hxn : x ∉ D.cliquePart := fun h ↦ Finset.disjoint_left.mp D.disjoint hx h
  have hyn : y ∉ D.independentPart := fun h ↦ Finset.disjoint_left.mp D.disjoint h hy
  simp [hxn, hyn]

/-- Number of unordered defect edges. -/
def c4DefectCost (G : SimpleGraph V) (D : C4Division V) : ℕ :=
  (finiteGraphEdges (c4DefectGraph G D)).card

/-- The defect cost is literally the paper's sum of the two induced edge
counts, including when one or both sides are empty. -/
theorem c4DefectCost_eq_induced_edgeCounts (G : SimpleGraph V) (D : C4Division V) :
    c4DefectCost G D =
      (finiteGraphEdges (G.induce (D.independentPart : Set V))).card +
      (finiteGraphEdges (Gᶜ.induce (D.cliquePart : Set V))).card := by
  classical
  have hedges : finiteGraphEdges (c4DefectGraph G D) =
      finiteGraphEdges (c4WithinGraph G D.independentPart) ∪
        finiteGraphEdges (c4WithinGraph Gᶜ D.cliquePart) := by
    ext e
    induction e using Sym2.inductionOn with
    | _ x y => simp [c4DefectGraph]
  have hdis : Disjoint (finiteGraphEdges (c4WithinGraph G D.independentPart))
      (finiteGraphEdges (c4WithinGraph Gᶜ D.cliquePart)) := by
    apply Finset.disjoint_left.mpr
    intro e he hf
    induction e using Sym2.inductionOn with
    | _ x y =>
      have hx := (mk_mem_finiteGraphEdges _ _ _).mp he
      have hy := (mk_mem_finiteGraphEdges _ _ _).mp hf
      exact Finset.disjoint_left.mp D.disjoint hx.1 hy.1
  rw [c4DefectCost, hedges, Finset.card_union_of_disjoint hdis,
    card_finiteGraphEdges_c4WithinGraph, card_finiteGraphEdges_c4WithinGraph]

theorem c4DefectCost_eq_zero_iff (G : SimpleGraph V) (D : C4Division V) :
    c4DefectCost G D = 0 ↔ c4DefectGraph G D = ⊥ := by
  constructor
  · intro h
    have hempty := Finset.card_eq_zero.mp h
    ext x y
    simp only [SimpleGraph.bot_adj, iff_false]
    intro hxy
    have hmem := (mk_mem_finiteGraphEdges (c4DefectGraph G D) x y).mpr hxy
    rw [hempty] at hmem
    exact Finset.notMem_empty _ hmem
  · intro h
    simp [c4DefectCost, h, finiteGraphEdges]

/-- Vanishing defects mean exactly that this division is an
independent/clique partition. -/
theorem c4DefectGraph_eq_bot_iff (G : SimpleGraph V) (D : C4Division V) :
    c4DefectGraph G D = ⊥ ↔
      G.IsIndepSet (D.independentPart : Set V) ∧ G.IsClique (D.cliquePart : Set V) := by
  constructor
  · intro h
    constructor
    · intro x hx y hy hne hxy
      have hd : (c4DefectGraph G D).Adj x y :=
        (c4DefectGraph_adj G D x y).mpr (Or.inl ⟨hx, hy, hxy⟩)
      simpa only [h, SimpleGraph.bot_adj] using hd
    · intro x hx y hy hne
      by_contra hxy
      have hd : (c4DefectGraph G D).Adj x y :=
        (c4DefectGraph_adj G D x y).mpr (Or.inr ⟨hx, hy, hne, hxy⟩)
      simpa only [h, SimpleGraph.bot_adj] using hd
  · rintro ⟨hA, hB⟩
    ext x y
    simp only [SimpleGraph.bot_adj, iff_false]
    intro hxy
    rcases (c4DefectGraph_adj G D x y).mp hxy with ⟨hx, hy, hxy⟩ | ⟨hx, hy, hne, hxy⟩
    · exact hA hx hy hxy.ne hxy
    · exact hxy (hB hx hy hne)

/-- A zero-defect division gives the actual transparent split witness. -/
def c4SplitWitnessOfDefectZero (G : SimpleGraph V) (D : C4Division V)
    (h : c4DefectCost G D = 0) : DenseGraph.SplitGraphWitness G where
  independentPart := D.independentPart
  cliquePart := D.cliquePart
  disjoint := D.disjoint
  cover := D.cover
  independent := ((c4DefectGraph_eq_bot_iff G D).mp ((c4DefectCost_eq_zero_iff G D).mp h)).1
  clique := ((c4DefectGraph_eq_bot_iff G D).mp ((c4DefectCost_eq_zero_iff G D).mp h)).2

private theorem exists_c4DefectCost_minimizer (G : SimpleGraph V) :
    ∃ D : C4Division V, ∀ E : C4Division V, c4DefectCost G D ≤ c4DefectCost G E := by
  classical
  obtain ⟨D, _, hD⟩ := Finset.exists_min_image Finset.univ (c4DefectCost G)
    ⟨∅, Finset.mem_univ _⟩
  exact ⟨D, fun E ↦ hD E (Finset.mem_univ _)⟩

/-- One fixed choice among all minimizing ordered divisions. It minimizes
over every independent side, including the empty set and the whole space. -/
def canonicalC4Division (G : SimpleGraph V) : C4Division V :=
  Classical.choose (exists_c4DefectCost_minimizer G)

theorem canonicalC4Division_minimal (G : SimpleGraph V) (D : C4Division V) :
    c4DefectCost G (canonicalC4Division G) ≤ c4DefectCost G D :=
  Classical.choose_spec (exists_c4DefectCost_minimizer G) D

/-- The optimal defect cost is zero precisely for split graphs. -/
theorem canonicalC4Division_defect_zero_iff (G : SimpleGraph V) :
    c4DefectCost G (canonicalC4Division G) = 0 ↔ DenseGraph.IsSplitGraph G := by
  constructor
  · intro h
    exact ⟨c4SplitWitnessOfDefectZero G _ h⟩
  · rintro ⟨P⟩
    let D : C4Division V := P.independentPart
    have hzero : c4DefectCost G D = 0 := by
      rw [c4DefectCost_eq_zero_iff, c4DefectGraph_eq_bot_iff]
      have hB : D.cliquePart = P.cliquePart := P.cliquePart_eq_compl.symm
      exact ⟨P.independent, by rw [hB]; exact P.clique⟩
    exact Nat.eq_zero_of_le_zero (hzero ▸ canonicalC4Division_minimal G D)

end InducedStars
