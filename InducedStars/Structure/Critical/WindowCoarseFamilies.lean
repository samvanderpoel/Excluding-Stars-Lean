import InducedStars.Structure.Critical.WindowBasic
import InducedStars.Structure.Critical.AggregationFamilies

/-!
# Actual graph families for the coarse critical-window reduction

Every graph outside the small literal-assembly family is far from the endpoint
optimizer, has a nonzero canonical defect, or has a clean canonical division
whose sparse set exceeds the cutoff.
-/

noncomputable section
open Filter Finset Set
open scoped BigOperators Topology Classical
namespace InducedStars

private instance coarseFamilyGraphDecidableEq (n : ℕ) :
    DecidableEq (SimpleGraph (Fin n)) := Classical.decEq _

/-- The exact-edge family without a literal assembly of size at most q. -/
def criticalNoSmallAssemblyGraphFinset (k n m q : ℕ) :
    Finset (SimpleGraph (Fin n)) :=
  (inducedStarFreeGraphFinsetWithEdges k n m).filter
    fun G ↦ ¬HasCriticalStructure k q G

/-- The total size of the canonical nonclean fibers at an arbitrary edge count. -/
def criticalWindowDefectTotal
    (k : ℕ) (hk : 3 ≤ k) (n m : ℕ) (tau : ℝ) : ℕ :=
  if hn : k - 1 ≤ n then
    ∑ D ∈ allSupercriticalDivisions k n,
      (supercriticalDivisionDefectGraphFinset k hk (gammaK k)
        (gammaK_mem_supercritical_Ico k hk) m n tau hn D).card
  else 0

/-- The sum of clean canonical fibers above a natural-number sparse cutoff. -/
def criticalWindowCleanTailTotal
    (k : ℕ) (hk : 3 ≤ k) (n m q : ℕ) (tau : ℝ) : ℕ :=
  if hn : k - 1 ≤ n then
    ∑ D ∈ allSupercriticalDivisions k n,
      if q < D.sparse.card then
        (supercriticalCleanDivisionGraphFinset k hk (gammaK k)
          (gammaK_mem_supercritical_Ico k hk) m n tau hn D).card
      else 0
  else 0

/-- Finite three-way decomposition, before any asymptotic estimate. -/
theorem card_criticalNoSmallAssemblyGraphFinset_le
    (k : ℕ) (hk : 3 ≤ k) (n m q : ℕ) (tau : ℝ) (hn : k - 1 ≤ n) :
    (criticalNoSmallAssemblyGraphFinset k n m q).card ≤
      (supercriticalFarGraphFinset k hk (gammaK k)
        (gammaK_mem_supercritical_Ico k hk) m n tau).card +
        criticalWindowCleanTailTotal k hk n m q tau +
          criticalWindowDefectTotal k hk n m tau := by
  classical
  let hgamma := gammaK_mem_supercritical_Ico k hk
  let far := supercriticalFarGraphFinset k hk (gammaK k) hgamma m n tau
  let clean : SupercriticalDivision k (Fin n) → Finset (SimpleGraph (Fin n)) :=
    fun D ↦ if q < D.sparse.card then
      supercriticalCleanDivisionGraphFinset k hk (gammaK k) hgamma m n tau hn D else ∅
  let defect : SupercriticalDivision k (Fin n) → Finset (SimpleGraph (Fin n)) :=
    supercriticalDivisionDefectGraphFinset k hk (gammaK k) hgamma m n tau hn
  have hcover : criticalNoSmallAssemblyGraphFinset k n m q ⊆
      far ∪ (allSupercriticalDivisions k n).biUnion (fun D ↦ clean D ∪ defect D) := by
    intro G hG
    obtain ⟨hfree, hbad⟩ := Finset.mem_filter.mp hG
    by_cases hfar : G ∈ far
    · exact Finset.mem_union_left _ hfar
    have hclose : G ∈ supercriticalCloseGraphFinset
        k hk (gammaK k) hgamma m n tau := by
      rw [supercriticalCloseGraphFinset_eq_sdiff_far]
      exact Finset.mem_sdiff.mpr ⟨hfree, hfar⟩
    let D := canonicalSupercriticalDivision G (by simpa using hn)
    apply Finset.mem_union_right
    apply Finset.mem_biUnion.mpr
    refine ⟨D, mem_allSupercriticalDivisions D, ?_⟩
    by_cases hzero : (finiteGraphEdges
        (canonicalSupercriticalDefectGraph G (by simpa using hn))).card = 0
    · have hclean : G ∈ supercriticalCleanDivisionGraphFinset
          k hk (gammaK k) hgamma m n tau hn D :=
        mem_supercriticalCleanDivisionGraphFinset.mpr ⟨hclose, rfl, hzero⟩
      have hlarge : q < D.sparse.card := by
        by_contra hnot
        exact hbad (hasCriticalStructure_of_mem_supercriticalCleanDivisionGraphFinset
          hclean (by omega))
      exact Finset.mem_union_left _ (by simpa [clean, hlarge] using hclean)
    · exact Finset.mem_union_right _ (mem_supercriticalDivisionDefectGraphFinset.mpr
        ⟨hclose, rfl, Finset.card_ne_zero.mp hzero⟩)
  have hcard : (criticalNoSmallAssemblyGraphFinset k n m q).card ≤
      far.card + ∑ D ∈ allSupercriticalDivisions k n, (clean D ∪ defect D).card :=
    (Finset.card_le_card hcover).trans
      ((Finset.card_union_le _ _).trans (Nat.add_le_add_left Finset.card_biUnion_le _))
  calc
    _ ≤ far.card + ∑ D ∈ allSupercriticalDivisions k n, (clean D ∪ defect D).card :=
      hcard
    _ ≤ far.card + ∑ D ∈ allSupercriticalDivisions k n,
        ((clean D).card + (defect D).card) :=
      Nat.add_le_add_left (Finset.sum_le_sum (fun _ _ ↦ Finset.card_union_le _ _)) _
    _ = _ := by
      rw [Finset.sum_add_distrib]
      simp only [criticalWindowCleanTailTotal, criticalWindowDefectTotal, dite_eq_left hn]
      dsimp only [far, clean, defect, hgamma]
      simp only [apply_ite, Finset.card_empty]
      omega

/-- The far term remains quadratically negligible for every fixed signed
logarithmic displacement, since the exact floor sequence has limiting density
gammaK k. -/
theorem eventually_criticalWindowFar_le
    (k : ℕ) (hk : 3 ≤ k) (a tau : ℝ) (htau : 0 < tau) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop,
      ((supercriticalFarGraphFinset k hk (gammaK k)
        (gammaK_mem_supercritical_Ico k hk) (criticalWindowEdgeCount k a n) n tau).card : ℝ) ≤
      (inducedStarFreeGraphCountWithEdges k n (criticalWindowEdgeCount k a n) : ℝ) *
        Real.exp (-c * (n : ℝ) ^ 2) := by
  obtain ⟨c, hc, hbound⟩ := eventually_supercriticalFarTotal_le k hk (gammaK k)
    (gammaK_mem_supercritical_Ico k hk) tau htau
  exact ⟨c, hc, hbound (criticalWindowEdgeCount k a)
    (criticalWindowEdgeCount_hasAsymptoticEdgeDensity hk a)⟩

end InducedStars
