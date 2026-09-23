import InducedStars.Structure.Critical.WindowAssemblies
import InducedStars.Structure.Critical.WindowCoarseFamilies

/-!
# Finite event inclusions for the critical window

The same literal witness supplies the logarithmic cutoff and the exceptional
size used in the sharp row estimates.
-/

noncomputable section
open Filter Finset Set
open scoped BigOperators Classical
namespace InducedStars

private instance windowEventGraphDecidableEq (n : ℕ) :
    DecidableEq (SimpleGraph (Fin n)) := Classical.decEq _

/-- Failure of the sharp literal-structure event in its exact sample space. -/
def criticalWindowBadStructureFinset (k n : ℕ) (a epsilon : ℝ) :
    Finset (SimpleGraph (Fin n)) :=
  (criticalWindowInducedStarFreeGraphFinset k n a).filter
    fun G ↦ ¬HasCriticalWindowStructure k a epsilon G

/-- A graph with a small assembly but without the sharp size conclusion occurs
in a bounded-logarithmic off-peak exact-size row. -/
theorem criticalWindowBadStructure_subset
    {k n q : ℕ} {a L epsilon : ℝ}
    (hlog : 0 < Real.log (n : ℝ))
    (hq : (q : ℝ) / Real.log (n : ℝ) ≤ L) :
    criticalWindowBadStructureFinset k n a epsilon ⊆
      criticalNoSmallAssemblyGraphFinset k n (criticalWindowEdgeCount k a n) q ∪
        (((Finset.range (n + 1)).filter (fun s : ℕ ↦
          (s : ℝ) / Real.log (n : ℝ) ≤ L ∧
            epsilon ≤ |(s : ℝ) / Real.log (n : ℝ) - criticalWindowRemainderCoefficient k a|)).biUnion
          fun s ↦ exactCriticalAssemblyFinset k n (criticalWindowEdgeCount k a n) s) := by
  intro G hG
  obtain ⟨hfree, hbad⟩ := Finset.mem_filter.mp hG
  by_cases hnone : G ∈ criticalNoSmallAssemblyGraphFinset k n (criticalWindowEdgeCount k a n) q
  · exact Finset.mem_union_left _ hnone
  have hsmall : HasCriticalStructure k q G := by
    by_contra hnot
    exact hnone (Finset.mem_filter.mpr ⟨hfree, hnot⟩)
  obtain ⟨W, hW⟩ := hsmall
  have hsn : W.exceptionalVertices.card ≤ n := by
    simpa using Finset.card_le_univ W.exceptionalVertices
  have hsize : (W.exceptionalVertices.card : ℝ) / Real.log (n : ℝ) ≤ L :=
    (div_le_div_of_nonneg_right (by exact_mod_cast hW) hlog.le).trans hq
  have haway : epsilon ≤
      |(W.exceptionalVertices.card : ℝ) / Real.log (n : ℝ) - criticalWindowRemainderCoefficient k a| := by
    exact (lt_of_not_ge (fun h ↦ hbad ⟨W, h⟩)).le
  apply Finset.mem_union_right
  apply Finset.mem_biUnion.mpr
  refine ⟨W.exceptionalVertices.card, Finset.mem_filter.mpr
    ⟨Finset.mem_range.mpr (by omega), hsize, haway⟩, ?_⟩
  exact mem_exactCriticalAssemblyFinset.mpr ⟨hfree, W, rfl⟩

/-- Cardinal form of the off-peak event inclusion. -/
theorem card_criticalWindowBadStructure_le
    {k n q : ℕ} {a L epsilon : ℝ}
    (hlog : 0 < Real.log (n : ℝ))
    (hq : (q : ℝ) / Real.log (n : ℝ) ≤ L) :
    ((criticalWindowBadStructureFinset k n a epsilon).card : ℝ) ≤
      ((criticalNoSmallAssemblyGraphFinset k n (criticalWindowEdgeCount k a n) q).card : ℝ) +
        ∑ s ∈ (Finset.range (n + 1)).filter (fun s : ℕ ↦
          (s : ℝ) / Real.log (n : ℝ) ≤ L ∧
            epsilon ≤ |(s : ℝ) / Real.log (n : ℝ) - criticalWindowRemainderCoefficient k a|),
          ((exactCriticalAssemblyFinset k n (criticalWindowEdgeCount k a n) s).card : ℝ) := by
  have h := (Finset.card_le_card (criticalWindowBadStructure_subset (k := k) (a := a) (epsilon := epsilon) hlog hq)).trans
    ((Finset.card_union_le _ _).trans (Nat.add_le_add_left Finset.card_biUnion_le _))
  exact_mod_cast h

/-- A non-co-partite graph with a small literal assembly has positive
exceptional size, in the same bounded logarithmic range. -/
theorem criticalWindowNonCoMultipartite_subset
    {k n q : ℕ} {a L : ℝ}
    (hlog : 0 < Real.log (n : ℝ))
    (hq : (q : ℝ) / Real.log (n : ℝ) ≤ L) :
    supercriticalNonCoMultipartiteGraphFinset k n (criticalWindowEdgeCount k a n) ⊆
      criticalNoSmallAssemblyGraphFinset k n (criticalWindowEdgeCount k a n) q ∪
        (((Finset.range (n + 1)).filter (fun s : ℕ ↦
          1 ≤ s ∧ (s : ℝ) / Real.log (n : ℝ) ≤ L)).biUnion
            fun s ↦ exactCriticalAssemblyFinset k n (criticalWindowEdgeCount k a n) s) := by
  intro G hG
  obtain ⟨hfree, hnotco⟩ := mem_supercriticalNonCoMultipartiteGraphFinset.mp hG
  by_cases hnone : G ∈ criticalNoSmallAssemblyGraphFinset k n (criticalWindowEdgeCount k a n) q
  · exact Finset.mem_union_left _ hnone
  have hsmall : HasCriticalStructure k q G := by
    by_contra hnot
    exact hnone (Finset.mem_filter.mpr ⟨hfree, hnot⟩)
  obtain ⟨W, hW⟩ := hsmall
  have hsn : W.exceptionalVertices.card ≤ n := by
    simpa using Finset.card_le_univ W.exceptionalVertices
  have hpos : 1 ≤ W.exceptionalVertices.card := by
    by_contra hnot
    have hz : W.exceptionalVertices.card = 0 := by omega
    exact hnotco (hasExactCriticalStructure_zero_iff.mp ⟨W, hz⟩)
  have hsize : (W.exceptionalVertices.card : ℝ) / Real.log (n : ℝ) ≤ L :=
    (div_le_div_of_nonneg_right (by exact_mod_cast hW) hlog.le).trans hq
  apply Finset.mem_union_right
  apply Finset.mem_biUnion.mpr
  refine ⟨W.exceptionalVertices.card, Finset.mem_filter.mpr
    ⟨Finset.mem_range.mpr (by omega), hpos, hsize⟩, ?_⟩
  exact mem_exactCriticalAssemblyFinset.mpr ⟨hfree, W, rfl⟩

/-- Cardinal form using the union of actual positive-size assembly families. -/
theorem card_criticalWindowNonCoMultipartite_le
    {k n q : ℕ} {a L : ℝ}
    (hlog : 0 < Real.log (n : ℝ))
    (hq : (q : ℝ) / Real.log (n : ℝ) ≤ L) :
    ((supercriticalNonCoMultipartiteGraphFinset k n (criticalWindowEdgeCount k a n)).card : ℝ) ≤
      ((criticalNoSmallAssemblyGraphFinset k n (criticalWindowEdgeCount k a n) q).card : ℝ) +
        ((((Finset.range (n + 1)).filter (fun s : ℕ ↦
          1 ≤ s ∧ (s : ℝ) / Real.log (n : ℝ) ≤ L)).biUnion
            fun s ↦ exactCriticalAssemblyFinset k n (criticalWindowEdgeCount k a n) s).card : ℝ) := by
  exact_mod_cast (Finset.card_le_card (criticalWindowNonCoMultipartite_subset (k := k) (a := a) hlog hq)).trans
    (Finset.card_union_le _ _)

end InducedStars
