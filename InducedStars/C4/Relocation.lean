import InducedStars.C4.Divisions
import InducedStars.Structure.Supercritical.Division

/-!
# Single-vertex optimality for split divisions

Moving a vertex to the other side changes only its incident defect edges.
The exact finite edge-count identity therefore proves both relocation
inequalities used in the high-defect-degree arguments of `paper/c4-free.tex`.
The reused restricted complement degree is loopless: it never counts the
vertex itself.
-/

noncomputable section

open Finset Set

namespace InducedStars

universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

namespace C4Division

/-- Move a vertex to the clique side, allowing either part to become empty. -/
def moveToClique (D : C4Division V) (v : V) : C4Division V := D.erase v

/-- Move a vertex to the independent side. -/
def moveToIndependent (D : C4Division V) (v : V) : C4Division V := insert v D

@[simp] theorem independentPart_moveToClique (D : C4Division V) (v : V) :
    (D.moveToClique v).independentPart = D.independentPart.erase v := rfl

@[simp] theorem cliquePart_moveToClique (D : C4Division V) (v : V) :
    (D.moveToClique v).cliquePart = insert v D.cliquePart := by
  ext x
  simp only [mem_cliquePart, independentPart_moveToClique, Finset.mem_erase,
    Finset.mem_insert]
  tauto

@[simp] theorem independentPart_moveToIndependent (D : C4Division V) (v : V) :
    (D.moveToIndependent v).independentPart = insert v D.independentPart := rfl

@[simp] theorem cliquePart_moveToIndependent (D : C4Division V) (v : V) :
    (D.moveToIndependent v).cliquePart = D.cliquePart.erase v := by
  ext x
  simp only [mem_cliquePart, independentPart_moveToIndependent, Finset.mem_erase,
    Finset.mem_insert]
  tauto

end C4Division

theorem c4DefectGraph_degree_of_mem_independent (G : SimpleGraph V)
    (D : C4Division V) {v : V} (hv : v ∈ D.independentPart) :
    degreeInFinset (c4DefectGraph G D) v Finset.univ =
      degreeInFinset G v D.independentPart := by
  classical
  unfold degreeInFinset
  congr 1
  ext w
  simp [c4DefectGraph_adj, C4Division.mem_cliquePart, hv]

theorem c4DefectGraph_degree_of_mem_clique (G : SimpleGraph V)
    (D : C4Division V) {v : V} (hv : v ∈ D.cliquePart) :
    degreeInFinset (c4DefectGraph G D) v Finset.univ =
      complementDegreeInFinset G v D.cliquePart := by
  classical
  have hvA : v ∉ D.independentPart := (D.mem_cliquePart v).mp hv
  unfold degreeInFinset complementDegreeInFinset
  congr 1
  ext w
  simp [c4DefectGraph_adj, hv, hvA, ne_comm]

/-- Exact cost change when the side assignment is unchanged away from `v`.
Both terms use loopless degrees, so no diagonal correction is needed. -/
theorem c4DefectCost_add_degree_eq_of_off_vertex (G : SimpleGraph V)
    (D E : C4Division V) (v : V)
    (hparts : ∀ x, x ≠ v → (x ∈ E.independentPart ↔ x ∈ D.independentPart)) :
    c4DefectCost G E + degreeInFinset (c4DefectGraph G D) v Finset.univ =
      c4DefectCost G D + degreeInFinset (c4DefectGraph G E) v Finset.univ := by
  have hdel : (c4DefectGraph G E).deleteIncidenceSet v =
      (c4DefectGraph G D).deleteIncidenceSet v := by
    ext x y
    simp only [SimpleGraph.deleteIncidenceSet_adj]
    by_cases hx : x = v
    · subst x
      simp
    by_cases hy : y = v
    · subst y
      simp
    simp only [c4DefectGraph_adj, C4Division.mem_cliquePart, hparts x hx, hparts y hy]
  have hE := card_finiteGraphEdges_eq_deleteIncidence_add_degree (c4DefectGraph G E) v
  have hD := card_finiteGraphEdges_eq_deleteIncidence_add_degree (c4DefectGraph G D) v
  rw [hdel] at hE
  unfold c4DefectCost
  omega

/-- Optimality against moving `v ∈ A` to `B` gives the first source
relocation inequality. -/
theorem c4Relocation_of_mem_independent (G : SimpleGraph V) (D : C4Division V)
    (hmin : ∀ E : C4Division V, c4DefectCost G D ≤ c4DefectCost G E)
    {v : V} (hv : v ∈ D.independentPart) :
    degreeInFinset G v D.independentPart ≤ complementDegreeInFinset G v D.cliquePart := by
  have hchange := c4DefectCost_add_degree_eq_of_off_vertex G D (D.moveToClique v) v
    (by intro x hx; simp [hx])
  have hvE : v ∈ (D.moveToClique v).cliquePart := by simp
  rw [c4DefectGraph_degree_of_mem_independent G D hv,
    c4DefectGraph_degree_of_mem_clique G _ hvE,
    C4Division.cliquePart_moveToClique, complementDegreeInFinset_insert_self] at hchange
  have hle := hmin (D.moveToClique v)
  omega

/-- Optimality against moving `v ∈ B` to `A` gives the second source
relocation inequality. -/
theorem c4Relocation_of_mem_clique (G : SimpleGraph V) (D : C4Division V)
    (hmin : ∀ E : C4Division V, c4DefectCost G D ≤ c4DefectCost G E)
    {v : V} (hv : v ∈ D.cliquePart) :
    complementDegreeInFinset G v D.cliquePart ≤ degreeInFinset G v D.independentPart := by
  have hchange := c4DefectCost_add_degree_eq_of_off_vertex G D (D.moveToIndependent v) v
    (by intro x hx; simp [hx])
  have hvE : v ∈ (D.moveToIndependent v).independentPart := by simp
  rw [c4DefectGraph_degree_of_mem_clique G D hv,
    c4DefectGraph_degree_of_mem_independent G _ hvE,
    C4Division.independentPart_moveToIndependent, degreeInFinset_insert_self] at hchange
  have hle := hmin (D.moveToIndependent v)
  omega

theorem canonicalC4Division_relocation_independent (G : SimpleGraph V) {v : V}
    (hv : v ∈ (canonicalC4Division G).independentPart) :
    degreeInFinset G v (canonicalC4Division G).independentPart ≤
      complementDegreeInFinset G v (canonicalC4Division G).cliquePart :=
  c4Relocation_of_mem_independent G _ (canonicalC4Division_minimal G) hv

theorem canonicalC4Division_relocation_clique (G : SimpleGraph V) {v : V}
    (hv : v ∈ (canonicalC4Division G).cliquePart) :
    complementDegreeInFinset G v (canonicalC4Division G).cliquePart ≤
      degreeInFinset G v (canonicalC4Division G).independentPart :=
  c4Relocation_of_mem_clique G _ (canonicalC4Division_minimal G) hv

end InducedStars
