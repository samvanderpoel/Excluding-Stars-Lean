import InducedStars.Structure.Subcritical.ProfileGeometry
import Mathlib.Combinatorics.SimpleGraph.Bipartite

/-!
# Rooted and residual profile defects

The rooted graph records only the high rows and own-part missing edges
specified in the profile definition. Its edges join a bad root to a vertex
outside the bad-root set; it does not include all defects meeting that set.
-/

noncomputable section

open Finset
open scoped BigOperators Classical

namespace InducedStars

variable {k : ℕ} {V : Type*} [Fintype V] [DecidableEq V]

/-- The spanning subgraph `T(G)[V_*,V]`: ordinary defects having at least
one retained endpoint, with a retained--retained edge counted only once. -/
def subcriticalRetainedIncidentDefectGraph (G : SimpleGraph V)
    (D : SubcriticalDivision k V) (eta : ℝ) (R₀ : ℕ) : SimpleGraph V where
  Adj x y := (subcriticalDefectGraph G D).Adj x y ∧
    (x ∈ D.retainedVertices eta R₀ ∨ y ∈ D.retainedVertices eta R₀)
  symm := ⟨by rintro x y ⟨hxy, hret⟩; exact ⟨hxy.symm, hret.symm⟩⟩
  loopless := ⟨by intro x h; exact h.1.ne rfl⟩

@[simp] theorem subcriticalRetainedIncidentDefectGraph_adj
    (G : SimpleGraph V) (D : SubcriticalDivision k V) (eta : ℝ) (R₀ : ℕ)
    (x y : V) :
    (subcriticalRetainedIncidentDefectGraph G D eta R₀).Adj x y ↔
      (subcriticalDefectGraph G D).Adj x y ∧
        (x ∈ D.retainedVertices eta R₀ ∨ y ∈ D.retainedVertices eta R₀) := Iff.rfl

theorem subcriticalRetainedIncidentDefectGraph_le (G : SimpleGraph V)
    (D : SubcriticalDivision k V) (eta : ℝ) (R₀ : ℕ) :
    subcriticalRetainedIncidentDefectGraph G D eta R₀ ≤ subcriticalDefectGraph G D :=
  fun _ _ h ↦ h.1

/-- Delete every edge incident with any actual bad root. -/
def subcriticalResidualDefectGraph (G : SimpleGraph V)
    (D : SubcriticalDivision k V) (eta : ℝ) (R₀ : ℕ) (theta alpha : ℝ) :
    SimpleGraph V where
  Adj x y := (subcriticalRetainedIncidentDefectGraph G D eta R₀).Adj x y ∧
    x ∉ subcriticalBadRoots G D eta R₀ theta alpha ∧
    y ∉ subcriticalBadRoots G D eta R₀ theta alpha
  symm := ⟨by rintro x y ⟨hxy, hx, hy⟩; exact ⟨hxy.symm, hy, hx⟩⟩
  loopless := ⟨by intro x h; exact h.1.ne rfl⟩

@[simp] theorem subcriticalResidualDefectGraph_adj
    (G : SimpleGraph V) (D : SubcriticalDivision k V) (eta : ℝ) (R₀ : ℕ)
    (theta alpha : ℝ) (x y : V) :
    (subcriticalResidualDefectGraph G D eta R₀ theta alpha).Adj x y ↔
      (subcriticalRetainedIncidentDefectGraph G D eta R₀).Adj x y ∧
        x ∉ subcriticalBadRoots G D eta R₀ theta alpha ∧
        y ∉ subcriticalBadRoots G D eta R₀ theta alpha := Iff.rfl

theorem subcriticalResidualDefectGraph_le (G : SimpleGraph V)
    (D : SubcriticalDivision k V) (eta : ℝ) (R₀ : ℕ) (theta alpha : ℝ) :
    subcriticalResidualDefectGraph G D eta R₀ theta alpha ≤
      subcriticalRetainedIncidentDefectGraph G D eta R₀ := fun _ _ h ↦ h.1

/-- Actual recorded neighbors, with the root orientation retained. Eligible
rows and retained-target rows are selected by the full-target threshold;
their neighbors are then trimmed outside all bad roots. Every bad retained
root also records all missing own-part edges, even when that own row is low.
Tail labels add no edges. -/
def subcriticalRecordedRootNeighbors (G : SimpleGraph V)
    (D : SubcriticalDivision k V) (eta : ℝ) (R₀ : ℕ) (theta alpha : ℝ)
    (v : V) : Finset V :=
  Finset.univ.filter fun y ↦ y ∉ subcriticalBadRoots G D eta R₀ theta alpha ∧
    ((v ∈ subcriticalBadRetainedRoots G D eta R₀ theta alpha ∧
      ((∃ hv : v ∈ D.retainedVertices eta R₀,
        y ∈ D.part (D.retainedVertexPart eta R₀ v hv) ∧ y ≠ v ∧ ¬ G.Adj v y) ∨
      ∃ a : D.PartIndex, D.EligibleProfileTarget eta R₀ theta v a ∧
        4 * alpha * (D.part a).card ≤ (degreeInFinset G v (D.part a) : ℝ) ∧
        y ∈ D.part a ∧ G.Adj v y)) ∨
    (v ∈ subcriticalBadOutsideRoots G D eta R₀ theta alpha ∧
      ∃ a ∈ D.retainedPartIndices eta R₀,
        4 * alpha * (D.part a).card ≤ (degreeInFinset G v (D.part a) : ℝ) ∧
        y ∈ D.part a ∧ G.Adj v y))

theorem subcriticalRecordedRootNeighbors_root_and_nonroot
    (G : SimpleGraph V) (D : SubcriticalDivision k V) (eta : ℝ) (R₀ : ℕ)
    (theta alpha : ℝ) (v y : V)
    (hy : y ∈ subcriticalRecordedRootNeighbors G D eta R₀ theta alpha v) :
    v ∈ subcriticalBadRoots G D eta R₀ theta alpha ∧
      y ∉ subcriticalBadRoots G D eta R₀ theta alpha := by
  obtain ⟨hy, h⟩ := (Finset.mem_filter.mp hy).2
  exact ⟨Finset.mem_union.mpr (h.elim (fun h ↦ Or.inl h.1) (fun h ↦ Or.inr h.1)), hy⟩

theorem subcriticalRecordedRootNeighbors_is_defect
    (G : SimpleGraph V) (D : SubcriticalDivision k V) (eta : ℝ) (R₀ : ℕ)
    (theta alpha : ℝ) (v y : V)
    (hy : y ∈ subcriticalRecordedRootNeighbors G D eta R₀ theta alpha v) :
    (subcriticalRetainedIncidentDefectGraph G D eta R₀).Adj v y := by
  rcases (Finset.mem_filter.mp hy).2.2 with ⟨hv, hown | hrows⟩ | ⟨hv, hrows⟩
  · obtain ⟨hvret, hypart, hne, hG⟩ := hown
    exact ⟨retainedOwn_missing_edge_is_defect G D eta R₀ v hvret hypart hne hG,
      Or.inl hvret⟩
  · obtain ⟨a, ⟨hvret, ha⟩, _, hypart, hG⟩ := hrows
    exact ⟨eligibleVisibleTarget_edge_is_defect G D eta R₀ theta v hvret ha hypart hG,
      Or.inl hvret⟩
  · obtain ⟨a, ha, _, hypart, hG⟩ := hrows
    have hvout := subcriticalBadOutsideRoots_subset G D eta R₀ theta alpha hv
    exact ⟨outside_retainedTarget_edge_is_defect G D eta R₀ hvout ha hypart hG,
      Or.inr (D.part_subset_retainedVertices ha hypart)⟩

/-- The undirected graph of exactly the recorded root-neighbor edges. -/
def subcriticalRootedDefectGraph (G : SimpleGraph V)
    (D : SubcriticalDivision k V) (eta : ℝ) (R₀ : ℕ) (theta alpha : ℝ) :
    SimpleGraph V where
  Adj x y := y ∈ subcriticalRecordedRootNeighbors G D eta R₀ theta alpha x ∨
    x ∈ subcriticalRecordedRootNeighbors G D eta R₀ theta alpha y
  symm := ⟨by intro x y h; exact h.symm⟩
  loopless := ⟨by
    intro x hx
    have h := subcriticalRecordedRootNeighbors_root_and_nonroot
      G D eta R₀ theta alpha x x (hx.elim id id)
    exact h.2 h.1⟩

@[simp] theorem subcriticalRootedDefectGraph_adj
    (G : SimpleGraph V) (D : SubcriticalDivision k V) (eta : ℝ) (R₀ : ℕ)
    (theta alpha : ℝ) (x y : V) :
    (subcriticalRootedDefectGraph G D eta R₀ theta alpha).Adj x y ↔
      y ∈ subcriticalRecordedRootNeighbors G D eta R₀ theta alpha x ∨
        x ∈ subcriticalRecordedRootNeighbors G D eta R₀ theta alpha y := Iff.rfl

theorem subcriticalRootedDefectGraph_le (G : SimpleGraph V)
    (D : SubcriticalDivision k V) (eta : ℝ) (R₀ : ℕ) (theta alpha : ℝ) :
    subcriticalRootedDefectGraph G D eta R₀ theta alpha ≤
      subcriticalRetainedIncidentDefectGraph G D eta R₀ := by
  intro x y h
  exact h.elim (subcriticalRecordedRootNeighbors_is_defect G D eta R₀ theta alpha x y)
    (fun h ↦ (subcriticalRecordedRootNeighbors_is_defect G D eta R₀ theta alpha y x h).symm)

theorem subcriticalRootedDefectGraph_exactly_one_bad_endpoint
    (G : SimpleGraph V) (D : SubcriticalDivision k V) (eta : ℝ) (R₀ : ℕ)
    (theta alpha : ℝ) {x y : V}
    (h : (subcriticalRootedDefectGraph G D eta R₀ theta alpha).Adj x y) :
    (x ∈ subcriticalBadRoots G D eta R₀ theta alpha ∧
      y ∉ subcriticalBadRoots G D eta R₀ theta alpha) ∨
    (y ∈ subcriticalBadRoots G D eta R₀ theta alpha ∧
      x ∉ subcriticalBadRoots G D eta R₀ theta alpha) :=
  h.elim
    (fun h ↦ Or.inl (subcriticalRecordedRootNeighbors_root_and_nonroot G D eta R₀ theta alpha x y h))
    (fun h ↦ Or.inr (subcriticalRecordedRootNeighbors_root_and_nonroot G D eta R₀ theta alpha y x h))

theorem subcriticalResidualDefectGraph_no_bad_endpoint
    (G : SimpleGraph V) (D : SubcriticalDivision k V) (eta : ℝ) (R₀ : ℕ)
    (theta alpha : ℝ) {x y : V}
    (h : (subcriticalResidualDefectGraph G D eta R₀ theta alpha).Adj x y) :
    x ∉ subcriticalBadRoots G D eta R₀ theta alpha ∧
      y ∉ subcriticalBadRoots G D eta R₀ theta alpha := h.2

/-- Rooted and residual edge sets are disjoint. Their union need not contain
defects between bad roots or low unrecorded rows meeting bad roots. -/
theorem subcriticalRooted_residual_edge_disjoint
    (G : SimpleGraph V) (D : SubcriticalDivision k V) (eta : ℝ) (R₀ : ℕ)
    (theta alpha : ℝ) :
    Disjoint (finiteGraphEdges (subcriticalRootedDefectGraph G D eta R₀ theta alpha))
      (finiteGraphEdges (subcriticalResidualDefectGraph G D eta R₀ theta alpha)) := by
  apply Finset.disjoint_left.mpr
  intro e he hr
  induction e using Sym2.inductionOn with
  | _ x y =>
    rw [mk_mem_finiteGraphEdges] at he hr
    obtain h | h := subcriticalRootedDefectGraph_exactly_one_bad_endpoint
      G D eta R₀ theta alpha he
    · exact hr.2.1 h.1
    · exact hr.2.2 h.1

/-- An undirected graph whose edges are oriented uniquely from a finite root
set has exactly the sum of its recorded neighbor counts. Mathlib's bipartite
degree-sum identity supplies the unordered-edge normalization. -/
theorem card_finiteGraphEdges_eq_sum_recordedNeighbors
    (H : SimpleGraph V) (B : Finset V) (N : V → Finset V)
    (hN : ∀ x y, y ∈ N x → x ∈ B ∧ y ∉ B)
    (hAdj : ∀ x y, H.Adj x y ↔ y ∈ N x ∨ x ∈ N y) :
    (finiteGraphEdges H).card = ∑ x ∈ B, (N x).card := by
  classical
  letI : DecidableRel H.Adj := Classical.decRel _
  letI : Fintype H.edgeSet := H.fintypeEdgeSet
  have hbi : H.IsBipartiteWith (B : Set V) ((B : Set V)ᶜ) := by
    refine ⟨disjoint_compl_right, ?_⟩
    intro x y hxy
    rcases (hAdj x y).mp hxy with h | h
    · exact Or.inl (hN x y h)
    · exact Or.inr ⟨(hN y x h).2, (hN y x h).1⟩
  have hedge : finiteGraphEdges H = H.edgeFinset := by
    ext e
    rw [mem_finiteGraphEdges, SimpleGraph.mem_edgeFinset]
  rw [hedge, ← H.isBipartiteWith_sum_degrees_eq_card_edges
    (s := B) (t := Bᶜ) (by simpa using hbi)]
  apply Finset.sum_congr rfl
  intro x hx
  rw [← H.card_neighborFinset_eq_degree]
  congr 1
  ext y
  simp only [SimpleGraph.mem_neighborFinset, hAdj]
  exact or_iff_left (fun hy ↦ (hN y x hy).2 hx)

/-- Every unordered rooted edge contributes once, at its unique bad endpoint. -/
theorem subcriticalRootedDefectGraph_card_eq_sum_neighbors
    (G : SimpleGraph V) (D : SubcriticalDivision k V) (eta : ℝ) (R₀ : ℕ)
    (theta alpha : ℝ) :
    (finiteGraphEdges (subcriticalRootedDefectGraph G D eta R₀ theta alpha)).card =
      ∑ v ∈ subcriticalBadRoots G D eta R₀ theta alpha,
        (subcriticalRecordedRootNeighbors G D eta R₀ theta alpha v).card :=
  card_finiteGraphEdges_eq_sum_recordedNeighbors _ _ _
    (subcriticalRecordedRootNeighbors_root_and_nonroot G D eta R₀ theta alpha)
    (subcriticalRootedDefectGraph_adj G D eta R₀ theta alpha)

end InducedStars
