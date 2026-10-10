import InducedStars.Structure.Subcritical.Division

/-!
# Subcritical weighted models and explicit candidate compatibility

Paper: Definitions `dfn:division` and `dfn:D-reg-blowup` and the compatibility
paragraph following them. Compatibility retains the chosen block sequence:
its lengths are `L.alpha`, not the cumulative endpoints. No assertion about
compatibility of the canonical division is made here.
-/

noncomputable section

open Finset Set
open scoped BigOperators Classical

namespace InducedStars

variable {k : ℕ} {V : Type*} [Fintype V] [DecidableEq V]

/-- The paper's `H_Π`: this is not the simple graph obtained by editing a
given graph. In particular, an active pair has weight `pK k` regardless of
which actual edges a repaired simple graph keeps. -/
def subcriticalDivisionWeightedGraph (hk : 3 ≤ k)
    (D : SubcriticalDivision k V) : DenseGraph.FiniteWeightedGraph V where
  weight x y := if D.SamePart x y then 1 else if D.ActivePair x y then pK k else 0
  symmetric x y := by rw [D.samePart_comm x y, D.activePair_comm x y]
  nonneg x y := by
    split_ifs
    · exact zero_le_one
    · exact (pK_pos (by omega : 2 ≤ k)).le
    · exact le_rfl
  le_one x y := by
    split_ifs
    · exact le_rfl
    · exact (pK_lt_one (by omega : 2 ≤ k)).le
    · exact zero_le_one

@[simp] theorem subcriticalDivisionWeightedGraph_weight_of_samePart
    (hk : 3 ≤ k) (D : SubcriticalDivision k V) {x y : V}
    (h : D.SamePart x y) :
    (subcriticalDivisionWeightedGraph hk D).weight x y = 1 := by
  simp [subcriticalDivisionWeightedGraph, h]

theorem subcriticalDivisionWeightedGraph_weight_of_activePair
    (hk : 3 ≤ k) (D : SubcriticalDivision k V) {x y : V}
    (h : D.ActivePair x y) :
    (subcriticalDivisionWeightedGraph hk D).weight x y = pK k := by
  have hs : ¬ D.SamePart x y := fun hs ↦ D.not_activePair_of_samePart hs h
  simp [subcriticalDivisionWeightedGraph, hs, h]

theorem subcriticalDivisionWeightedGraph_weight_of_forbidden
    (hk : 3 ≤ k) (D : SubcriticalDivision k V) {x y : V}
    (hs : ¬ D.SamePart x y) (ha : ¬ D.ActivePair x y) :
    (subcriticalDivisionWeightedGraph hk D).weight x y = 0 := by
  simp [subcriticalDivisionWeightedGraph, hs, ha]

theorem subcriticalDivisionWeightedGraph_weight_of_mem_parts
    (hk : 3 ≤ k) (D : SubcriticalDivision k V)
    {a b : D.PartIndex} {x y : V}
    (hx : x ∈ D.part a) (hy : y ∈ D.part b) :
    (subcriticalDivisionWeightedGraph hk D).weight x y =
      if a = b then 1 else if D.ActivePart a b then pK k else 0 := by
  simp only [subcriticalDivisionWeightedGraph,
    D.samePart_iff_of_mem_parts hx hy, D.activePair_iff_of_mem_parts hx hy]

theorem subcriticalDivisionWeightedGraph_weight_of_distinct_components
    (hk : 3 ≤ k) (D : SubcriticalDivision k V)
    {a b : D.PartIndex} (hab : a.1 ≠ b.1) {x y : V}
    (hx : x ∈ D.part a) (hy : y ∈ D.part b) :
    (subcriticalDivisionWeightedGraph hk D).weight x y = 0 := by
  rw [subcriticalDivisionWeightedGraph_weight_of_mem_parts hk D hx hy]
  have hne : a ≠ b := fun h ↦ hab (congrArg Sigma.fst h)
  have hna : ¬ D.ActivePart a b := fun h ↦ hab (SubcriticalDivision.activePart_same_component h)
  simp [hne, hna]

@[simp] theorem subcriticalDivisionWeightedGraph_weight_of_sparse_left
    (hk : 3 ≤ k) (D : SubcriticalDivision k V) {x y : V}
    (hx : x ∈ D.sparse) :
    (subcriticalDivisionWeightedGraph hk D).weight x y = 0 := by
  apply subcriticalDivisionWeightedGraph_weight_of_forbidden
  · exact fun h ↦ (D.mem_sparse.mp hx) (SubcriticalDivision.samePart_imp_support h).1
  · exact fun h ↦ (D.mem_sparse.mp hx) (SubcriticalDivision.activePair_imp_support h).1

@[simp] theorem subcriticalDivisionWeightedGraph_weight_of_sparse_right
    (hk : 3 ≤ k) (D : SubcriticalDivision k V) {x y : V}
    (hy : y ∈ D.sparse) :
    (subcriticalDivisionWeightedGraph hk D).weight x y = 0 := by
  rw [(subcriticalDivisionWeightedGraph hk D).symmetric]
  exact subcriticalDivisionWeightedGraph_weight_of_sparse_left hk D hy

@[simp] theorem subcriticalDivisionWeightedGraph_weight_self
    (hk : 3 ≤ k) (D : SubcriticalDivision k V) (x : V) :
    (subcriticalDivisionWeightedGraph hk D).weight x x =
      if x ∈ D.support then 1 else 0 := by
  simp [subcriticalDivisionWeightedGraph]

/-- Reindexing components changes no weighted geometry. -/
@[simp] theorem subcriticalDivisionWeightedGraph_reindex
    (hk : 3 ≤ k) (D : SubcriticalDivision k V)
    (e : Equiv.Perm (Fin D.componentCount)) :
    subcriticalDivisionWeightedGraph hk (D.reindex e) =
      subcriticalDivisionWeightedGraph hk D := by
  ext x y
  simp [subcriticalDivisionWeightedGraph]

/-- The pullback weighted model uses the same actual vertex permutation as
the transported division. This does not assert equivariance of a selector. -/
theorem subcriticalDivisionWeightedGraph_relabel_symm
    (hk : 3 ≤ k) (D : SubcriticalDivision k V) (e : Equiv.Perm V) :
    subcriticalDivisionWeightedGraph hk (D.relabel e.symm) =
      (subcriticalDivisionWeightedGraph hk D).permute e := by
  ext x y
  simp [subcriticalDivisionWeightedGraph]

namespace SubcriticalDivision

/-- The components that must be matched in the paper's compatibility
definition. The cutoff is a natural number, as in `IsOrderedByCutoff`. -/
def compatibilityComponentIndices (D : SubcriticalDivision k V)
    (eta : ℝ) (R₀ : ℕ) : Finset (Fin D.componentCount) :=
  Finset.univ.filter fun i ↦
    eta * Fintype.card V / 2 ≤ (D.componentSupport i).card ∧
      (D.core i).order ≤ R₀

@[simp] theorem mem_compatibilityComponentIndices
    (D : SubcriticalDivision k V) (eta : ℝ) (R₀ : ℕ)
    (i : Fin D.componentCount) :
    i ∈ D.compatibilityComponentIndices eta R₀ ↔
      eta * Fintype.card V / 2 ≤ (D.componentSupport i).card ∧
        (D.core i).order ≤ R₀ := by simp [compatibilityComponentIndices]

/-- An actual injection into the active indices of a specified candidate
representation, retaining graph isomorphisms and the unmatched-block clause.
No representation-independence or canonical-division theorem is implicit. -/
structure CandidateCompatibility (D : SubcriticalDivision k V)
    (L : AdmissibleBlockSequence k) (eta delta : ℝ) (R₀ : ℕ) where
  assignment : {i // i ∈ D.compatibilityComponentIndices eta R₀} ↪
    {j : ℕ // blockIndexActive L.count j}
  coreIso : ∀ i, (D.core i.val).graph ≃g (L.core (assignment i).val).graph
  size_error : ∀ i,
    |((D.componentSupport i.val).card : ℝ) -
      L.alpha (assignment i).val * Fintype.card V| ≤ delta * Fintype.card V
  unmatched : ∀ j : {j : ℕ // blockIndexActive L.count j},
    (∀ i, assignment i ≠ j) → L.alpha j.val < eta ∨ R₀ < (L.core j.val).order

namespace CandidateCompatibility

variable {D : SubcriticalDivision k V} {L : AdmissibleBlockSequence k}
  {eta delta : ℝ} {R₀ : ℕ}

theorem assigned_active (C : D.CandidateCompatibility L eta delta R₀)
    (i : {i // i ∈ D.compatibilityComponentIndices eta R₀}) :
    blockIndexActive L.count (C.assignment i).val := (C.assignment i).property

theorem large_smallOrder_block_matched
    (C : D.CandidateCompatibility L eta delta R₀)
    (j : {j : ℕ // blockIndexActive L.count j})
    (hlarge : eta ≤ L.alpha j.val) (horder : (L.core j.val).order ≤ R₀) :
    ∃ i, C.assignment i = j := by
  by_contra h
  have hn : ∀ i, C.assignment i ≠ j := by simpa using h
  rcases C.unmatched j hn with h | h
  · exact (not_lt_of_ge hlarge) h
  · exact (not_lt_of_ge horder) h

end CandidateCompatibility
end SubcriticalDivision
end InducedStars
