import InducedStars.FiniteModels.GraphFamilies
import InducedStars.Graphon.Candidates
import Mathlib.Tactic

/-!
# Exact-edge graphs far from the supercritical optimizer

This module isolates the finite family used on the exceptional side of the
supercritical rough-structure theorem.  The far and close families form an
exact complementary partition of the labeled induced-star-free graphs with
the prescribed edge count.  No asymptotic or counting input is used here.
-/

noncomputable section

open Set

namespace InducedStars

attribute [local instance] graphFamiliesEdgeSetFintype

noncomputable local instance supercriticalGraphDecidableEq (n : ℕ) :
    DecidableEq (SimpleGraph (Fin n)) :=
  Classical.decEq _

/-- Exact-edge induced-star-free graphs whose adjacency graphons are at
least `τ` in cut distance from the distinguished supercritical graphon. -/
def supercriticalFarGraphFinset
    (k : ℕ) (hk : 3 ≤ k) (γ : ℝ) (hγ : γ ∈ Ico (gammaK k) 1)
    (m n : ℕ) (τ : ℝ) : Finset (SimpleGraph (Fin n)) := by
  classical
  exact
    (inducedFreeGraphFinsetWithEdges (inducedStar k) n m).filter fun G ↦
      τ ≤ cutDist (graphGraphon G) (Wstar k hk γ hγ)

/-- The complementary exact-edge family lying strictly within cut distance
`τ` of the distinguished supercritical graphon. -/
def supercriticalCloseGraphFinset
    (k : ℕ) (hk : 3 ≤ k) (γ : ℝ) (hγ : γ ∈ Ico (gammaK k) 1)
    (m n : ℕ) (τ : ℝ) : Finset (SimpleGraph (Fin n)) := by
  classical
  exact
    (inducedFreeGraphFinsetWithEdges (inducedStar k) n m).filter fun G ↦
      cutDist (graphGraphon G) (Wstar k hk γ hγ) < τ

@[simp] theorem mem_supercriticalFarGraphFinset
    {k : ℕ} {hk : 3 ≤ k} {γ : ℝ} {hγ : γ ∈ Ico (gammaK k) 1}
    {m n : ℕ} {τ : ℝ} {G : SimpleGraph (Fin n)} :
    G ∈ supercriticalFarGraphFinset k hk γ hγ m n τ ↔
      ¬Regularity.InducedEmbeds (inducedStar k) G ∧
        G.edgeFinset.card = m ∧
        τ ≤ cutDist (graphGraphon G) (Wstar k hk γ hγ) := by
  classical
  simp [supercriticalFarGraphFinset, and_assoc]

@[simp] theorem mem_supercriticalCloseGraphFinset
    {k : ℕ} {hk : 3 ≤ k} {γ : ℝ} {hγ : γ ∈ Ico (gammaK k) 1}
    {m n : ℕ} {τ : ℝ} {G : SimpleGraph (Fin n)} :
    G ∈ supercriticalCloseGraphFinset k hk γ hγ m n τ ↔
      ¬Regularity.InducedEmbeds (inducedStar k) G ∧
        G.edgeFinset.card = m ∧
        cutDist (graphGraphon G) (Wstar k hk γ hγ) < τ := by
  classical
  simp [supercriticalCloseGraphFinset, and_assoc]

theorem supercriticalFarGraphFinset_subset
    (k : ℕ) (hk : 3 ≤ k) (γ : ℝ) (hγ : γ ∈ Ico (gammaK k) 1)
    (m n : ℕ) (τ : ℝ) :
    supercriticalFarGraphFinset k hk γ hγ m n τ ⊆
      inducedFreeGraphFinsetWithEdges (inducedStar k) n m := by
  classical
  exact Finset.filter_subset _ _

theorem supercriticalCloseGraphFinset_subset
    (k : ℕ) (hk : 3 ≤ k) (γ : ℝ) (hγ : γ ∈ Ico (gammaK k) 1)
    (m n : ℕ) (τ : ℝ) :
    supercriticalCloseGraphFinset k hk γ hγ m n τ ⊆
      inducedFreeGraphFinsetWithEdges (inducedStar k) n m := by
  classical
  exact Finset.filter_subset _ _

/-- The far and close sides are disjoint, including at the threshold where
equality belongs to the far side. -/
theorem supercriticalFarGraphFinset_disjoint_close
    (k : ℕ) (hk : 3 ≤ k) (γ : ℝ) (hγ : γ ∈ Ico (gammaK k) 1)
    (m n : ℕ) (τ : ℝ) :
    Disjoint (supercriticalFarGraphFinset k hk γ hγ m n τ)
      (supercriticalCloseGraphFinset k hk γ hγ m n τ) := by
  classical
  rw [Finset.disjoint_left]
  intro G hfar hclose
  rw [mem_supercriticalFarGraphFinset] at hfar
  rw [mem_supercriticalCloseGraphFinset] at hclose
  exact (not_lt_of_ge hfar.2.2) hclose.2.2

/-- The two threshold sides exhaust the exact-edge induced-star-free
family. -/
theorem supercriticalFarGraphFinset_union_close
    (k : ℕ) (hk : 3 ≤ k) (γ : ℝ) (hγ : γ ∈ Ico (gammaK k) 1)
    (m n : ℕ) (τ : ℝ) :
    supercriticalFarGraphFinset k hk γ hγ m n τ ∪
        supercriticalCloseGraphFinset k hk γ hγ m n τ =
      inducedFreeGraphFinsetWithEdges (inducedStar k) n m := by
  classical
  ext G
  simp only [Finset.mem_union, mem_supercriticalFarGraphFinset,
    mem_supercriticalCloseGraphFinset,
    mem_inducedFreeGraphFinsetWithEdges]
  constructor
  · rintro (⟨hfree, hm, _⟩ | ⟨hfree, hm, _⟩)
    · exact ⟨hfree, hm⟩
    · exact ⟨hfree, hm⟩
  · rintro ⟨hfree, hm⟩
    by_cases hfar : τ ≤ cutDist (graphGraphon G) (Wstar k hk γ hγ)
    · exact Or.inl ⟨hfree, hm, hfar⟩
    · exact Or.inr ⟨hfree, hm, lt_of_not_ge hfar⟩

/-- The close family is literally the complement of the far family inside
the prescribed exact-edge induced-star-free family. -/
theorem supercriticalCloseGraphFinset_eq_sdiff_far
    (k : ℕ) (hk : 3 ≤ k) (γ : ℝ) (hγ : γ ∈ Ico (gammaK k) 1)
    (m n : ℕ) (τ : ℝ) :
    supercriticalCloseGraphFinset k hk γ hγ m n τ =
      inducedFreeGraphFinsetWithEdges (inducedStar k) n m \
        supercriticalFarGraphFinset k hk γ hγ m n τ := by
  classical
  ext G
  simp only [Finset.mem_sdiff, mem_supercriticalFarGraphFinset,
    mem_supercriticalCloseGraphFinset,
    mem_inducedFreeGraphFinsetWithEdges]
  constructor
  · rintro ⟨hfree, hm, hclose⟩
    exact ⟨⟨hfree, hm⟩, fun hfar ↦ (not_lt_of_ge hfar.2.2) hclose⟩
  · rintro ⟨⟨hfree, hm⟩, hnotfar⟩
    refine ⟨hfree, hm, ?_⟩
    by_contra hnotclose
    exact hnotfar ⟨hfree, hm, le_of_not_gt hnotclose⟩

/-- Symmetrically, the far family is the complement of the close family
inside the prescribed exact-edge induced-star-free family. -/
theorem supercriticalFarGraphFinset_eq_sdiff_close
    (k : ℕ) (hk : 3 ≤ k) (γ : ℝ) (hγ : γ ∈ Ico (gammaK k) 1)
    (m n : ℕ) (τ : ℝ) :
    supercriticalFarGraphFinset k hk γ hγ m n τ =
      inducedFreeGraphFinsetWithEdges (inducedStar k) n m \
        supercriticalCloseGraphFinset k hk γ hγ m n τ := by
  classical
  ext G
  simp only [Finset.mem_sdiff, mem_supercriticalFarGraphFinset,
    mem_supercriticalCloseGraphFinset,
    mem_inducedFreeGraphFinsetWithEdges]
  constructor
  · rintro ⟨hfree, hm, hfar⟩
    exact ⟨⟨hfree, hm⟩, fun hclose ↦ (not_lt_of_ge hfar) hclose.2.2⟩
  · rintro ⟨⟨hfree, hm⟩, hnotclose⟩
    refine ⟨hfree, hm, ?_⟩
    exact le_of_not_gt fun hclose ↦ hnotclose ⟨hfree, hm, hclose⟩

/-- Cardinal decomposition associated with the exact far/close partition. -/
theorem card_supercriticalFarGraphFinset_add_close
    (k : ℕ) (hk : 3 ≤ k) (γ : ℝ) (hγ : γ ∈ Ico (gammaK k) 1)
    (m n : ℕ) (τ : ℝ) :
    (supercriticalFarGraphFinset k hk γ hγ m n τ).card +
        (supercriticalCloseGraphFinset k hk γ hγ m n τ).card =
      (inducedFreeGraphFinsetWithEdges (inducedStar k) n m).card := by
  rw [← supercriticalFarGraphFinset_union_close k hk γ hγ m n τ,
    Finset.card_union_of_disjoint
      (supercriticalFarGraphFinset_disjoint_close k hk γ hγ m n τ)]

end InducedStars
