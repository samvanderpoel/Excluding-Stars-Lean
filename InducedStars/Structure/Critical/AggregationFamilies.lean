import InducedStars.Structure.Critical.FiniteGeometry
import InducedStars.Structure.Supercritical.GlobalAggregation

/-!
# Deterministic aggregation families at the critical density

This file specializes the four finite exceptional families from the
supercritical aggregation to the exact critical edge count.  The clean
branch is refined at a logarithmic sparse-set cutoff: a clean canonical
division below the cutoff already supplies a `CriticalStructureWitness`, so
only clean divisions above the cutoff occur in the unstructured family.

No asymptotic estimate is used here.  The main results are the finite master
inclusion and its associated union-bound inequality.
-/

noncomputable section

open Finset Set
open scoped BigOperators

namespace InducedStars

noncomputable local instance criticalAggregationGraphDecidableEq (n : ℕ) :
    DecidableEq (SimpleGraph (Fin n)) := Classical.decEq _

/-! ## Critical specializations of the finite exceptional families -/

/-- The integer logarithmic cutoff used for the critical exceptional set. -/
noncomputable def criticalLogarithmicSparseCutoff
    (L : ℝ) (n : ℕ) : ℕ :=
  Nat.ceil (L * Real.log ((n + 1 : ℕ) : ℝ))

/-- Union of clean critical canonical-division families whose sparse set has
cardinality at least the displayed logarithmic cutoff. -/
noncomputable def criticalCleanLargeSparseGraphFinset
    (k : ℕ) (hk : 3 ≤ k) (n : ℕ) (tau L : ℝ) :
    Finset (SimpleGraph (Fin n)) := by
  classical
  exact if hn : k - 1 ≤ n then
    (allSupercriticalDivisions k n).biUnion fun D ↦
      if criticalLogarithmicSparseCutoff L n ≤ D.sparse.card then
        supercriticalCleanDivisionGraphFinset
          k hk (gammaK k) (gammaK_mem_supercritical_Ico k hk)
            (criticalEdgeCount k n) n tau hn D
      else ∅
  else ∅

/-- Union of all medium-degree critical canonical-division families. -/
noncomputable abbrev criticalMediumTotalGraphFinset
    (k : ℕ) (hk : 3 ≤ k) (alpha : ℝ) (n : ℕ) (tau : ℝ) :
    Finset (SimpleGraph (Fin n)) :=
  supercriticalMediumTotalGraphFinset
    k hk (gammaK k) (gammaK_mem_supercritical_Ico k hk) alpha
      (criticalEdgeCount k n) n tau

/-- Union of all nonmedium critical fixed combined-defect fibers. -/
noncomputable abbrev criticalFixedDefectTotalGraphFinset
    (k : ℕ) (hk : 3 ≤ k) (alpha : ℝ) (n : ℕ) (tau : ℝ) :
    Finset (SimpleGraph (Fin n)) :=
  supercriticalFixedDefectTotalGraphFinset
    k hk (gammaK k) (gammaK_mem_supercritical_Ico k hk) alpha
      (criticalEdgeCount k n) n tau

/-- Exact sum of the clean critical division-fiber cardinalities above the
logarithmic sparse-set cutoff.  This is intentionally a sum rather than the
cardinality of their union, as required by the later counting argument. -/
noncomputable def criticalCleanLargeSparseTotal
    (k : ℕ) (hk : 3 ≤ k) (n : ℕ) (tau L : ℝ) : ℕ := by
  classical
  exact if hn : k - 1 ≤ n then
    ∑ D ∈ allSupercriticalDivisions k n,
      if criticalLogarithmicSparseCutoff L n ≤ D.sparse.card then
        (supercriticalCleanDivisionGraphFinset
          k hk (gammaK k) (gammaK_mem_supercritical_Ico k hk)
            (criticalEdgeCount k n) n tau hn D).card
      else 0
  else 0

/-- The four-way deterministic exceptional union at the exact critical edge
count. -/
noncomputable def criticalAggregatedExceptionalGraphFinset
    (k : ℕ) (hk : 3 ≤ k) (alpha : ℝ) (n : ℕ) (tau L : ℝ) :
    Finset (SimpleGraph (Fin n)) :=
  criticalFarGraphFinset k hk n tau ∪
    criticalCleanLargeSparseGraphFinset k hk n tau L ∪
    criticalMediumTotalGraphFinset k hk alpha n tau ∪
    criticalFixedDefectTotalGraphFinset k hk alpha n tau

/-! ## The deterministic critical master decomposition -/

/-- Every critical graph without a structure witness at the displayed
logarithmic cutoff is either graphon-far, clean with a large canonical sparse
set, medium-degree, or in its own nonmedium fixed combined-defect fiber.

This is the finite master decomposition used by the critical aggregation.
It contains no analytic estimate and is valid for every choice of `alpha`,
`tau`, and `L`. -/
theorem criticalUnstructuredGraphFinset_subset_aggregated
    (k : ℕ) (hk : 3 ≤ k) (alpha : ℝ) (n : ℕ) (tau L : ℝ)
    (hn : k - 1 ≤ n) :
    criticalUnstructuredGraphFinset k n
        (criticalLogarithmicSparseCutoff L n) ⊆
      criticalAggregatedExceptionalGraphFinset
        k hk alpha n tau L := by
  classical
  intro G hG
  have hbad := mem_criticalUnstructuredGraphFinset.mp hG
  let hgamma : gammaK k ∈ Set.Ico (gammaK k) 1 :=
    gammaK_mem_supercritical_Ico k hk
  by_cases hfar : G ∈ criticalFarGraphFinset k hk n tau
  · simp [criticalAggregatedExceptionalGraphFinset, hfar]
  have hclose : G ∈ supercriticalCloseGraphFinset
      k hk (gammaK k) hgamma (criticalEdgeCount k n) n tau := by
    rw [supercriticalCloseGraphFinset_eq_sdiff_far]
    rw [Finset.mem_sdiff]
    exact ⟨by simpa [criticalInducedStarFreeGraphFinset] using hbad.1,
      by simpa [criticalFarGraphFinset, hgamma] using hfar⟩
  let D := canonicalSupercriticalDivision G (by simpa using hn)
  have hdivision : G ∈ supercriticalDivisionGraphFinset
      k hk (gammaK k) hgamma (criticalEdgeCount k n) n tau hn D := by
    rw [mem_supercriticalDivisionGraphFinset]
    exact ⟨hclose, rfl⟩
  by_cases hzero : (finiteGraphEdges
      (canonicalSupercriticalDefectGraph G (by simpa using hn))).card = 0
  · have hclean : G ∈ supercriticalCleanDivisionGraphFinset
        k hk (gammaK k) hgamma (criticalEdgeCount k n) n tau hn D := by
      rw [mem_supercriticalCleanDivisionGraphFinset]
      exact ⟨hclose, rfl, hzero⟩
    by_cases hsparse :
        D.sparse.card ≤ criticalLogarithmicSparseCutoff L n
    · exact (hbad.2
        (hasCriticalStructure_of_mem_supercriticalCleanDivisionGraphFinset
          hclean hsparse)).elim
    · have hlarge :
          criticalLogarithmicSparseCutoff L n ≤ D.sparse.card := by
        omega
      have hcleanUnion :
          G ∈ criticalCleanLargeSparseGraphFinset k hk n tau L := by
        rw [criticalCleanLargeSparseGraphFinset, dif_pos hn,
          Finset.mem_biUnion]
        refine ⟨D, mem_allSupercriticalDivisions D, ?_⟩
        rw [if_pos hlarge]
        simpa [hgamma] using hclean
      simp [criticalAggregatedExceptionalGraphFinset, hcleanUnion]
  · have hdefectNonempty : (finiteGraphEdges
        (canonicalSupercriticalDefectGraph G (by simpa using hn))).Nonempty :=
      Finset.card_ne_zero.mp hzero
    have hdefect : G ∈ supercriticalDivisionDefectGraphFinset
        k hk (gammaK k) hgamma (criticalEdgeCount k n) n tau hn D := by
      rw [mem_supercriticalDivisionDefectGraphFinset]
      exact ⟨hclose, rfl, hdefectNonempty⟩
    by_cases hmedium : ∃ v i, HasMediumDegreeInPart
        (canonicalCombinedDefectGraph G (by simpa using hn)) alpha D v i
    · have hmediumUnion : G ∈ criticalMediumTotalGraphFinset
          k hk alpha n tau := by
        rw [criticalMediumTotalGraphFinset,
          supercriticalMediumTotalGraphFinset, dif_pos hn,
          Finset.mem_biUnion]
        refine ⟨D, mem_allSupercriticalDivisions D, ?_⟩
        rw [mem_supercriticalMediumDegreeGraphFinset]
        simpa [hgamma] using And.intro hdefect hmedium
      simp [criticalAggregatedExceptionalGraphFinset, hmediumUnion]
    · let T := canonicalCombinedDefectGraph G (by simpa using hn)
      have hT : T ∈ supercriticalCombinedDefectPatternFinset
          k hk (gammaK k) hgamma (criticalEdgeCount k n) n tau hn D := by
        rw [mem_supercriticalCombinedDefectPatternFinset]
        exact ⟨G, hdefect, rfl⟩
      have hfixed : G ∈ supercriticalFixedDefectGraphFinset
          k hk (gammaK k) hgamma alpha (criticalEdgeCount k n) n tau hn D T := by
        rw [mem_supercriticalFixedDefectGraphFinset]
        exact ⟨hdefect, rfl, hmedium⟩
      have hfixedUnion : G ∈ criticalFixedDefectTotalGraphFinset
          k hk alpha n tau := by
        rw [criticalFixedDefectTotalGraphFinset,
          supercriticalFixedDefectTotalGraphFinset, dif_pos hn,
          Finset.mem_biUnion]
        refine ⟨D, mem_allSupercriticalDivisions D, ?_⟩
        rw [Finset.mem_biUnion]
        exact ⟨T, by simpa [hgamma] using hT,
          by simpa [hgamma] using hfixed⟩
      simp [criticalAggregatedExceptionalGraphFinset, hfixedUnion]

/-! ## Cardinality bounds for the four finite unions -/

/-- The cardinality of the clean large-sparse union is bounded by the exact
sum of its division-fiber cardinalities. -/
theorem card_criticalCleanLargeSparseGraphFinset_le_total
    (k : ℕ) (hk : 3 ≤ k) (n : ℕ) (tau L : ℝ) :
    (criticalCleanLargeSparseGraphFinset k hk n tau L).card ≤
      criticalCleanLargeSparseTotal k hk n tau L := by
  classical
  by_cases hn : k - 1 ≤ n
  · rw [criticalCleanLargeSparseGraphFinset,
      criticalCleanLargeSparseTotal, dif_pos hn, dif_pos hn]
    have h := (Finset.card_biUnion_le :
      ((allSupercriticalDivisions k n).biUnion fun D ↦
        if criticalLogarithmicSparseCutoff L n ≤ D.sparse.card then
          supercriticalCleanDivisionGraphFinset
            k hk (gammaK k) (gammaK_mem_supercritical_Ico k hk)
              (criticalEdgeCount k n) n tau hn D
        else ∅).card ≤
        ∑ D ∈ allSupercriticalDivisions k n,
          (if criticalLogarithmicSparseCutoff L n ≤ D.sparse.card then
            supercriticalCleanDivisionGraphFinset
              k hk (gammaK k) (gammaK_mem_supercritical_Ico k hk)
                (criticalEdgeCount k n) n tau hn D
          else ∅).card)
    refine h.trans_eq ?_
    apply Finset.sum_congr rfl
    intro D _hD
    by_cases hsparse :
        criticalLogarithmicSparseCutoff L n ≤ D.sparse.card <;>
      simp [hsparse]
  · simp [criticalCleanLargeSparseGraphFinset,
      criticalCleanLargeSparseTotal, hn]

/-- The critical medium union is bounded by the corresponding exact sum over
canonical divisions. -/
theorem card_criticalMediumTotalGraphFinset_le_total
    (k : ℕ) (hk : 3 ≤ k) (alpha : ℝ) (n : ℕ) (tau : ℝ) :
    (criticalMediumTotalGraphFinset k hk alpha n tau).card ≤
      supercriticalMediumTotal k hk (gammaK k)
        (gammaK_mem_supercritical_Ico k hk) alpha
          (criticalEdgeCount k n) n tau := by
  exact card_supercriticalMediumTotalGraphFinset_le_total
    k hk (gammaK k) (gammaK_mem_supercritical_Ico k hk) alpha
      (criticalEdgeCount k n) n tau

/-- The critical fixed-defect union is bounded by the corresponding exact
iterated sum over divisions and displayed defect patterns. -/
theorem card_criticalFixedDefectTotalGraphFinset_le_total
    (k : ℕ) (hk : 3 ≤ k) (alpha : ℝ) (n : ℕ) (tau : ℝ) :
    (criticalFixedDefectTotalGraphFinset k hk alpha n tau).card ≤
      supercriticalFixedDefectTotal k hk (gammaK k)
        (gammaK_mem_supercritical_Ico k hk) alpha
          (criticalEdgeCount k n) n tau := by
  exact card_supercriticalFixedDefectTotalGraphFinset_le_total
    k hk (gammaK k) (gammaK_mem_supercritical_Ico k hk) alpha
      (criticalEdgeCount k n) n tau

/-- Cardinal union bound associated with the critical master decomposition.
The four right-hand terms are exactly the far cardinality, clean
large-sparse sum, medium sum, and fixed-defect sum consumed by the later
analytic aggregation. -/
theorem card_criticalUnstructuredGraphFinset_le_aggregationTotals
    (k : ℕ) (hk : 3 ≤ k) (alpha : ℝ) (n : ℕ) (tau L : ℝ)
    (hn : k - 1 ≤ n) :
    (criticalUnstructuredGraphFinset k n
      (criticalLogarithmicSparseCutoff L n)).card ≤
        (criticalFarGraphFinset k hk n tau).card +
        criticalCleanLargeSparseTotal k hk n tau L +
        supercriticalMediumTotal k hk (gammaK k)
          (gammaK_mem_supercritical_Ico k hk) alpha
            (criticalEdgeCount k n) n tau +
        supercriticalFixedDefectTotal k hk (gammaK k)
          (gammaK_mem_supercritical_Ico k hk) alpha
            (criticalEdgeCount k n) n tau := by
  classical
  have hsubset := criticalUnstructuredGraphFinset_subset_aggregated
    k hk alpha n tau L hn
  have hclean := card_criticalCleanLargeSparseGraphFinset_le_total
    k hk n tau L
  have hmedium := card_criticalMediumTotalGraphFinset_le_total
    k hk alpha n tau
  have hfixed := card_criticalFixedDefectTotalGraphFinset_le_total
    k hk alpha n tau
  have hfarClean := Finset.card_union_le
    (criticalFarGraphFinset k hk n tau)
    (criticalCleanLargeSparseGraphFinset k hk n tau L)
  have hwithMedium := Finset.card_union_le
    (criticalFarGraphFinset k hk n tau ∪
      criticalCleanLargeSparseGraphFinset k hk n tau L)
    (criticalMediumTotalGraphFinset k hk alpha n tau)
  have hwithFixed := Finset.card_union_le
    (criticalFarGraphFinset k hk n tau ∪
      criticalCleanLargeSparseGraphFinset k hk n tau L ∪
      criticalMediumTotalGraphFinset k hk alpha n tau)
    (criticalFixedDefectTotalGraphFinset k hk alpha n tau)
  have haggregate :
      (criticalAggregatedExceptionalGraphFinset
        k hk alpha n tau L).card ≤
        (criticalFarGraphFinset k hk n tau).card +
        (criticalCleanLargeSparseGraphFinset k hk n tau L).card +
        (criticalMediumTotalGraphFinset k hk alpha n tau).card +
        (criticalFixedDefectTotalGraphFinset k hk alpha n tau).card := by
    unfold criticalAggregatedExceptionalGraphFinset
    omega
  exact (Finset.card_le_card hsubset).trans
    (haggregate.trans (by omega))

end InducedStars
