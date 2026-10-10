import InducedStars.C4.DefectModels
import DenseGraph.FiniteModels.BernoulliEvents

/-!
# Paired matching coordinates for induced C4 patterns

Each side is an injectively indexed collection of oriented edges. Different
pairs of designated matching edges may share vertices, but their four cross
coordinates are disjoint. This is the precise independence mechanism in
Lemma `lemma:c4-matching`.
-/

noncomputable section
open Finset
open scoped Classical

namespace InducedStars
open Regularity

variable {V : Type*} [Fintype V] [DecidableEq V]

structure C4MatchingSides (D : C4Division V) (q ell : ℕ) where
  left : (Fin q × Fin 2) ↪ V
  right : (Fin ell × Fin 2) ↪ V
  left_mem : ∀ i a, left (i, a) ∈ D.independentPart
  right_mem : ∀ j b, right (j, b) ∈ D.cliquePart

namespace C4MatchingSides

variable {D : C4Division V} {q ell : ℕ} (W : C4MatchingSides D q ell)

theorem left_ne_right (i : Fin q) (a : Fin 2) (j : Fin ell) (b : Fin 2) :
    W.left (i, a) ≠ W.right (j, b) := by
  intro h
  exact Finset.disjoint_left.mp D.disjoint (h ▸ W.left_mem i a) (W.right_mem j b)

def coordinate (ia : Fin q × Fin 2) (jb : Fin ell × Fin 2) : C4CrossCoordinate D :=
  ⟨(), ⟨s(W.left ia, W.right jb), (mk_mem_c4CrossPotentialEdges D _ _).mpr
    (Or.inl ⟨W.left_mem ia.1 ia.2, W.right_mem jb.1 jb.2⟩)⟩⟩

theorem coordinate_injective :
    Function.Injective (fun p : (Fin q × Fin 2) × (Fin ell × Fin 2) ↦ W.coordinate p.1 p.2) := by
  intro p r h
  have he := congrArg (fun e : C4CrossCoordinate D ↦ e.2.val) h
  change s(W.left p.1, W.right p.2) = s(W.left r.1, W.right r.2) at he
  rcases Sym2.eq_iff.mp he with ⟨hleft, hright⟩ | ⟨hcross, _⟩
  · exact Prod.ext (W.left.injective hleft) (W.right.injective hright)
  · exact False.elim (W.left_ne_right p.1.1 p.1.2 r.2.1 r.2.2 hcross)

def support (ij : Fin q × Fin ell) : Finset (C4CrossCoordinate D) :=
  univ.image fun ab : Fin 2 × Fin 2 ↦ W.coordinate (ij.1, ab.1) (ij.2, ab.2)

theorem coordinate_mem_support (ij : Fin q × Fin ell) (a b : Fin 2) :
    W.coordinate (ij.1, a) (ij.2, b) ∈ W.support ij :=
  Finset.mem_image.mpr ⟨(a, b), Finset.mem_univ _, rfl⟩

@[simp] theorem card_support (ij : Fin q × Fin ell) : (W.support ij).card = 4 := by
  rw [support, Finset.card_image_iff.mpr]
  · simp
  · intro a ha b hb he
    have h : ((ij.1, a.1), (ij.2, a.2)) = ((ij.1, b.1), (ij.2, b.2)) :=
      W.coordinate_injective he
    exact Prod.ext (congrArg (fun p ↦ p.1.2) h) (congrArg (fun p ↦ p.2.2) h)

theorem supports_pairwiseDisjoint :
    Set.PairwiseDisjoint (Set.univ : Set (Fin q × Fin ell)) W.support := by
  intro ij _ kl _ hne
  apply Finset.disjoint_left.mpr
  intro e he hf
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp he
  obtain ⟨b, hb, heq⟩ := Finset.mem_image.mp hf
  have h : ((kl.1, b.1), (kl.2, b.2)) = ((ij.1, a.1), (ij.2, a.2)) :=
    W.coordinate_injective heq
  exact hne (Prod.ext (congrArg (fun p ↦ p.1.1) h).symm
    (congrArg (fun p ↦ p.2.1) h).symm)

/-- If the two internal pairs are present, require the two diagonal cross
edges and forbid the other two. If they are absent, require all four. -/
def pattern (present : Bool) (ij : Fin q × Fin ell) : Finset (C4CrossCoordinate D) :=
  if present then {W.coordinate (ij.1, 0) (ij.2, 0), W.coordinate (ij.1, 1) (ij.2, 1)}
  else W.support ij

theorem pattern_subset_support (present : Bool) (ij : Fin q × Fin ell) :
    W.pattern present ij ⊆ W.support ij := by
  cases present
  · exact Finset.Subset.refl _
  · intro e he
    simp only [pattern, Bool.true_eq, ↓reduceIte, Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl <;> exact W.coordinate_mem_support ij _ _

theorem coordinate_mem_pattern (present : Bool) (ij : Fin q × Fin ell) (a b : Fin 2) :
    W.coordinate (ij.1, a) (ij.2, b) ∈ W.pattern present ij ↔
      (present = false ∨ a = b) := by
  have heq (c d : Fin 2) :
      W.coordinate (ij.1, a) (ij.2, b) = W.coordinate (ij.1, c) (ij.2, d) ↔
        a = c ∧ b = d := by
    constructor
    · intro h
      have h : ((ij.1, a), (ij.2, b)) = ((ij.1, c), (ij.2, d)) :=
        W.coordinate_injective h
      exact ⟨congrArg (fun p ↦ p.1.2) h, congrArg (fun p ↦ p.2.2) h⟩
    · rintro ⟨rfl, rfl⟩; rfl
  cases present
  · simp [pattern, W.coordinate_mem_support]
  · simp only [pattern, Bool.true_eq, ↓reduceIte, Finset.mem_insert,
      Finset.mem_singleton, heq]
    fin_cases a <;> fin_cases b <;> decide

def event (present : Bool) (ij : Fin q × Fin ell) : Finset (Finset (C4CrossCoordinate D)) :=
  DenseGraph.FiniteBernoulliProduct.cylinderEvent (W.support ij) (W.pattern present ij)

theorem event_coordinate_iff (present : Bool) (ij : Fin q × Fin ell)
    {outcome : Finset (C4CrossCoordinate D)} (houtcome : outcome ∈ W.event present ij)
    (a b : Fin 2) :
    W.coordinate (ij.1, a) (ij.2, b) ∈ outcome ↔ (present = false ∨ a = b) := by
  have h := congrArg (fun S : Finset (C4CrossCoordinate D) ↦
    W.coordinate (ij.1, a) (ij.2, b) ∈ S)
    ((DenseGraph.FiniteBernoulliProduct.mem_cylinderEvent _ _ _).mp houtcome)
  simpa [W.coordinate_mem_support, W.coordinate_mem_pattern] using h

theorem coordinate_mem_outcome_iff (ia : Fin q × Fin 2) (jb : Fin ell × Fin 2)
    (outcome : Finset (C4CrossCoordinate D)) :
    s(W.left ia, W.right jb) ∈ c4CrossChoiceOfOutcome D outcome ↔
      W.coordinate ia jb ∈ outcome := by
  change (c4CrossCoordinateEmbedding D) (W.coordinate ia jb) ∈
      outcome.map (c4CrossCoordinateEmbedding D) ↔ _
  exact Finset.mem_map' _

theorem outcomeGraph_adj_cross (T : SimpleGraph V) (outcome : Finset (C4CrossCoordinate D))
    (ia : Fin q × Fin 2) (jb : Fin ell × Fin 2) :
    (c4DefectOutcomeGraph D T outcome).Adj (W.left ia) (W.right jb) ↔
      W.coordinate ia jb ∈ outcome := by
  rw [c4DefectOutcomeGraph, c4DefectGraphOfCrossChoice_adj_cross D T _
    (W.left_mem ia.1 ia.2) (W.right_mem jb.1 jb.2), W.coordinate_mem_outcome_iff]

end C4MatchingSides

/-- Checking all six unordered pairs proves actual induced containment.
The embedding hypothesis keeps all four vertices distinct. -/
theorem c4_inducedEmbeds_of_sixPairs (G : SimpleGraph V) (f : Fin 4 ↪ V)
    (h01 : G.Adj (f 0) (f 1)) (h12 : G.Adj (f 1) (f 2))
    (h23 : G.Adj (f 2) (f 3)) (h30 : G.Adj (f 3) (f 0))
    (h02 : ¬G.Adj (f 0) (f 2)) (h13 : ¬G.Adj (f 1) (f 3)) :
    InducedEmbeds inducedC4 G := by
  refine ⟨{ toEmbedding := f, map_rel_iff' := ?_ }⟩
  intro i j
  have h10 := h01.symm
  have h21 := h12.symm
  have h32 := h23.symm
  have h03 := h30.symm
  have h20 : ¬G.Adj (f 2) (f 0) := fun h ↦ h02 h.symm
  have h31 : ¬G.Adj (f 3) (f 1) := fun h ↦ h13 h.symm
  fin_cases i <;> fin_cases j <;> simp_all [inducedC4, SimpleGraph.cycleGraph_adj] <;> decide

namespace C4MatchingSides

variable {D : C4Division V} {q ell : ℕ} (W : C4MatchingSides D q ell)

/-- The required fixed internal statuses. Present mode pairs a positive
independent-side defect with a genuine clique-side edge. Absent mode pairs
an independent-side nonedge with a missing clique edge. -/
def InternalStatus (T : SimpleGraph V) (present : Bool) : Prop :=
  (∀ i, T.Adj (W.left (i, 0)) (W.left (i, 1)) ↔ present = true) ∧
    (∀ j, T.Adj (W.right (j, 0)) (W.right (j, 1)) ↔ present = false)

def cycleMap (present : Bool) (ij : Fin q × Fin ell) : Fin 4 → V :=
  if present then ![W.left (ij.1, 0), W.left (ij.1, 1), W.right (ij.2, 1), W.right (ij.2, 0)]
  else ![W.left (ij.1, 0), W.right (ij.2, 0), W.left (ij.1, 1), W.right (ij.2, 1)]

theorem cycleMap_injective (present : Bool) (ij : Fin q × Fin ell) :
    Function.Injective (W.cycleMap present ij) := by
  have ha : W.left (ij.1, 0) ≠ W.left (ij.1, 1) := W.left.injective.ne (by simp)
  have hb : W.right (ij.2, 0) ≠ W.right (ij.2, 1) := W.right.injective.ne (by simp)
  have hab00 := W.left_ne_right ij.1 0 ij.2 0
  have hab01 := W.left_ne_right ij.1 0 ij.2 1
  have hab10 := W.left_ne_right ij.1 1 ij.2 0
  have hab11 := W.left_ne_right ij.1 1 ij.2 1
  cases present <;> intro a b h <;> fin_cases a <;> fin_cases b <;>
    simp_all [cycleMap, ne_comm]

/-- Each prescribed cylinder really creates an induced four-cycle in the
actual fixed-defect graph; the construction is injective on its four vertices. -/
theorem event_forces_inducedC4 (T : SimpleGraph V) (present : Bool)
    (hstatus : W.InternalStatus T present) (ij : Fin q × Fin ell)
    {outcome : Finset (C4CrossCoordinate D)} (houtcome : outcome ∈ W.event present ij) :
    InducedEmbeds inducedC4 (c4DefectOutcomeGraph D T outcome) := by
  let G := c4DefectOutcomeGraph D T outcome
  have hcross (a b : Fin 2) :
      G.Adj (W.left (ij.1, a)) (W.right (ij.2, b)) ↔ present = false ∨ a = b :=
    (W.outcomeGraph_adj_cross T outcome (ij.1, a) (ij.2, b)).trans
      (W.event_coordinate_iff present ij houtcome a b)
  have hA : G.Adj (W.left (ij.1, 0)) (W.left (ij.1, 1)) ↔ present = true :=
    (c4DefectGraphOfCrossChoice_adj_independent D T (c4CrossChoiceOfOutcome_subset D outcome)
      (W.left_mem ij.1 0) (W.left_mem ij.1 1)).trans (hstatus.1 ij.1)
  have hB : G.Adj (W.right (ij.2, 0)) (W.right (ij.2, 1)) ↔ present = true := by
    have hb : W.right (ij.2, 0) ≠ W.right (ij.2, 1) := W.right.injective.ne (by simp)
    change (c4DefectGraphOfCrossChoice D T _).Adj _ _ ↔ _
    rw [c4DefectGraphOfCrossChoice_adj_clique D T (c4CrossChoiceOfOutcome_subset D outcome)
      (W.right_mem ij.2 0) (W.right_mem ij.2 1), hstatus.2 ij.2]
    cases present <;> simp [hb]
  cases present
  · refine c4_inducedEmbeds_of_sixPairs G
      ⟨W.cycleMap false ij, W.cycleMap_injective false ij⟩ ?_ ?_ ?_ ?_ ?_ ?_
    · exact (hcross 0 0).mpr (Or.inl rfl)
    · exact ((hcross 1 0).mpr (Or.inl rfl)).symm
    · exact (hcross 1 1).mpr (Or.inl rfl)
    · exact ((hcross 0 1).mpr (Or.inl rfl)).symm
    · exact fun h ↦ (by decide : (false : Bool) ≠ true) (hA.mp h)
    · exact fun h ↦ (by decide : (false : Bool) ≠ true) (hB.mp h)
  · refine c4_inducedEmbeds_of_sixPairs G
      ⟨W.cycleMap true ij, W.cycleMap_injective true ij⟩ ?_ ?_ ?_ ?_ ?_ ?_
    · exact hA.mpr rfl
    · exact (hcross 1 1).mpr (Or.inr rfl)
    · exact (hB.mpr rfl).symm
    · exact ((hcross 0 0).mpr (Or.inr rfl)).symm
    · intro h
      simpa using (hcross 0 1).mp h
    · intro h
      simpa using (hcross 1 0).mp h

theorem freeEvent_subset_avoidance (T : SimpleGraph V) (present : Bool)
    (hstatus : W.InternalStatus T present) :
    c4DefectFreeOutcomeEvent D T ⊆
      DenseGraph.FiniteBernoulliProduct.eventIntersection univ
        (fun ij : Fin q × Fin ell ↦ (W.event present ij)ᶜ) := by
  intro outcome houtcome
  rw [DenseGraph.FiniteBernoulliProduct.mem_eventIntersection]
  intro ij hij
  rw [Finset.mem_compl]
  intro hevent
  exact (mem_c4DefectFreeOutcomeEvent D T outcome).mp houtcome
    (W.event_forces_inducedC4 T present hstatus ij hevent)

end C4MatchingSides

end InducedStars
