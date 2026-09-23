import InducedStars.Structure.Critical.Reference
import InducedStars.Structure.Supercritical.AggregateBounds
import Mathlib.Tactic

/-!
# Capacity bookkeeping at the critical density

This file separates the number of available coordinates from the number of
selected coordinates in a clean critical division.  The sparse--sparse coordinates are
combined with all old cross coordinates, so the complementary (missing)
coordinate count is independent of the ordered main-part sizes.
-/

noncomputable section

open Finset Set
open scoped BigOperators

namespace InducedStars

variable {k n : ℕ}

/-! ## Total critical coordinate counts -/

/-- The old variable-coordinate capacity: all pairs between distinct main
parts together with all pairs internal to the sparse set. -/
def criticalCombinedVariableCapacity
    (D : SupercriticalDivision k (Fin n)) : ℕ :=
  supercriticalTotalCrossCapacity D + Nat.choose D.sparse.card 2

/-- The number of variable coordinates selected by a critical clean graph.
Its edge-budget formula is distinct from the available-coordinate capacity. -/
def criticalCombinedSelectedCount
    (k n : ℕ) (D : SupercriticalDivision k (Fin n)) : ℕ :=
  criticalEdgeCount k n - divisionInternalCliqueCapacity D

/-- The division-independent number of missing old coordinates for sparse
size `s`.  Natural subtraction supplies the total finite guard outside the
feasible range. -/
def criticalCombinedMissingCount (k n s : ℕ) : ℕ :=
  Nat.choose (n - s) 2 + Nat.choose s 2 - criticalEdgeCount k n

/-- The largest possible old variable capacity among divisions with sparse
size `s`: balance the `n-s` main vertices and retain every sparse pair. -/
def criticalMaximumCombinedCapacity (k n s : ℕ) : ℕ :=
  DenseGraph.balancedMultipartiteCrossCapacity (k - 1) (n - s) +
    Nat.choose s 2

/-- Paper-facing name for the combined-coordinate capacity before the sparse
vertices are absorbed into the balanced full reference division. -/
abbrev criticalMaximumOldCapacity (k n s : ℕ) : ℕ :=
  criticalMaximumCombinedCapacity k n s

/-- The selected count in the maximum-capacity slice with the common missing
count. -/
def criticalMaximumCombinedSelectedCount (k n s : ℕ) : ℕ :=
  criticalMaximumCombinedCapacity k n s -
    criticalCombinedMissingCount k n s

/-- The clean canonical fiber at the exact critical edge count. -/
noncomputable abbrev criticalCleanDivisionGraphFinset
    (k : ℕ) (hk : 3 ≤ k) (n : ℕ) (tau : ℝ) (hn : k - 1 ≤ n)
    (D : SupercriticalDivision k (Fin n)) :
    Finset (SimpleGraph (Fin n)) :=
  supercriticalCleanDivisionGraphFinset k hk (gammaK k)
    (gammaK_mem_supercritical_Ico k hk) (criticalEdgeCount k n) n tau hn D

@[simp] theorem criticalCombinedVariableCapacity_eq_preAbsorption
    (D : SupercriticalDivision k (Fin n)) :
    criticalCombinedVariableCapacity D =
      supercriticalPreAbsorptionVariableCapacity D := by
  rfl

/-- The variable capacity plus the forced clique capacity counts every pair
inside the support and every pair inside the sparse set. -/
theorem criticalCombinedVariableCapacity_add_internal
    (D : SupercriticalDivision k (Fin n)) :
    criticalCombinedVariableCapacity D + divisionInternalCliqueCapacity D =
      Nat.choose D.support.card 2 + Nat.choose D.sparse.card 2 := by
  have h := supercriticalTotalCrossCapacity_add_internal D
  unfold criticalCombinedVariableCapacity
  omega

/-- Version of the preceding identity expressed only through `n` and the
sparse size. -/
theorem criticalCombinedVariableCapacity_add_internal_eq
    (D : SupercriticalDivision k (Fin n)) :
    criticalCombinedVariableCapacity D + divisionInternalCliqueCapacity D =
      Nat.choose (n - D.sparse.card) 2 + Nat.choose D.sparse.card 2 := by
  rw [criticalCombinedVariableCapacity_add_internal]
  congr 2
  have h := D.card_support_add_card_sparse
  simp only [Fintype.card_fin] at h
  omega

/-! ## Balanced extremality -/

/-- The supercritical cross capacity is the generic multipartite cross
capacity of the main-part size vector. -/
theorem supercriticalTotalCrossCapacity_eq_multipartiteCrossCapacity
    (D : SupercriticalDivision k (Fin n)) :
    supercriticalTotalCrossCapacity D =
      DenseGraph.multipartiteCrossCapacity
        (fun i : Fin (k - 1) ↦ (D.parts i).card) := by
  rw [DenseGraph.multipartiteCrossCapacity_eq_pairSum]
  have hparts := DenseGraph.multipartiteCrossPairSum_add_sum_choose
    (fun i : Fin (k - 1) ↦ (D.parts i).card)
  have hdivision := supercriticalTotalCrossCapacity_add_internal D
  rw [D.card_support] at hdivision
  unfold divisionInternalCliqueCapacity at hdivision
  omega

/-- Balanced multipartite capacity is the maximum combined capacity at fixed
sparse size. -/
theorem criticalCombinedVariableCapacity_le_maximum
    (D : SupercriticalDivision k (Fin n)) :
    criticalCombinedVariableCapacity D ≤
      criticalMaximumCombinedCapacity k n D.sparse.card := by
  have hcross : supercriticalTotalCrossCapacity D ≤
      DenseGraph.balancedMultipartiteCrossCapacity (k - 1) D.support.card := by
    rw [supercriticalTotalCrossCapacity_eq_multipartiteCrossCapacity]
    simpa [D.card_support] using
      (DenseGraph.multipartiteCrossCapacity_le_balanced
        (fun i : Fin (k - 1) ↦ (D.parts i).card))
  have hsupport : D.support.card = n - D.sparse.card := by
    have h := D.card_support_add_card_sparse
    simp only [Fintype.card_fin] at h
    omega
  simpa [criticalCombinedVariableCapacity,
    criticalMaximumCombinedCapacity, hsupport] using
      Nat.add_le_add_right hcross (Nat.choose D.sparse.card 2)

/-- Fixed-sparse-size formulation of balanced extremality. -/
theorem criticalCombinedVariableCapacity_le_maximum_of_sparse_card
    (D : SupercriticalDivision k (Fin n)) {s : ℕ}
    (hs : D.sparse.card = s) :
    criticalCombinedVariableCapacity D ≤
      criticalMaximumCombinedCapacity k n s := by
  simpa [hs] using criticalCombinedVariableCapacity_le_maximum D

/-- The maximum variable capacity and the balanced forced-clique capacity
partition the same division-independent pair universe. -/
theorem criticalMaximumCombinedCapacity_add_balancedInternal
    (k n s : ℕ) :
    criticalMaximumCombinedCapacity k n s +
        DenseGraph.balancedMultipartiteInternalCapacity (k - 1) (n - s) =
      Nat.choose (n - s) 2 + Nat.choose s 2 := by
  have htotal := DenseGraph.balancedCross_add_internal (k - 1) (n - s)
  unfold criticalMaximumCombinedCapacity
  omega

/-! ## Feasibility and the division-independent missing count -/

/-- A member of a clean critical fiber proves both lower and upper
feasibility of its selected-coordinate slice. -/
theorem criticalCombinedSelectedCount_feasible_of_mem_clean
    {k n : ℕ} {hk : 3 ≤ k} {tau : ℝ} {hn : k - 1 ≤ n}
    {D : SupercriticalDivision k (Fin n)} {G : SimpleGraph (Fin n)}
    (hG : G ∈ criticalCleanDivisionGraphFinset k hk n tau hn D) :
    divisionInternalCliqueCapacity D ≤ criticalEdgeCount k n ∧
      criticalCombinedSelectedCount k n D ≤
        criticalCombinedVariableCapacity D := by
  have hGprofile :
      G ∈ supercriticalCleanDivisionProfileGraphFinset
        k hk (gammaK k) (gammaK_mem_supercritical_Ico k hk)
          (criticalEdgeCount k n) n tau hn D (crossEdgeProfile G D) := by
    rw [mem_supercriticalCleanDivisionProfileGraphFinset]
    exact ⟨hG, rfl⟩
  have hedge := supercriticalDefectShift_edgeCount_identity G D
  rw [finiteGraphEdges_card_eq_of_mem_cleanProfile hGprofile,
    supercriticalDefectShift_clean_eq_inducedEdgeCount hGprofile] at hedge
  have hedgeNat :
      criticalEdgeCount k n = divisionInternalCliqueCapacity D +
        profileTotal (crossEdgeProfile G D) + inducedEdgeCount G D.sparse := by
    exact_mod_cast hedge
  constructor
  · omega
  · have hmem := supercriticalCleanCombinedChoiceOfGraph_mem_layer hG
    have hsubset := (mem_supercriticalCombinedChoiceLayer D
      (criticalEdgeCount k n - divisionInternalCliqueCapacity D)
      (supercriticalCleanCombinedChoiceOfGraph D G)).mp hmem
    have hcard := Finset.card_le_card hsubset.1
    rw [hsubset.2, card_supercriticalCombinedChoiceUniverse] at hcard
    simpa only [criticalCombinedSelectedCount,
      criticalCombinedVariableCapacity,
      supercriticalPreAbsorptionVariableCapacity,
      supercriticalSparsePotentialCapacity,
      supercriticalCombinedChoiceCapacity,
      supercriticalSparseChoiceCapacity] using hcard

/-- Nonemptiness is the precise guard needed for the clean one-slice
bookkeeping. -/
theorem criticalCombinedSelectedCount_feasible_of_nonempty
    {k n : ℕ} {hk : 3 ≤ k} {tau : ℝ} {hn : k - 1 ≤ n}
    {D : SupercriticalDivision k (Fin n)}
    (hD : (criticalCleanDivisionGraphFinset k hk n tau hn D).Nonempty) :
    divisionInternalCliqueCapacity D ≤ criticalEdgeCount k n ∧
      criticalCombinedSelectedCount k n D ≤
        criticalCombinedVariableCapacity D := by
  obtain ⟨G, hG⟩ := hD
  exact criticalCombinedSelectedCount_feasible_of_mem_clean hG

/-- Exact identity between the capacity minus the selected count and the
number of missing coordinates. -/
theorem criticalCombinedVariableCapacity_sub_selected_eq_missing
    (D : SupercriticalDivision k (Fin n))
    (hlower : divisionInternalCliqueCapacity D ≤ criticalEdgeCount k n)
    (_hupper : criticalCombinedSelectedCount k n D ≤
      criticalCombinedVariableCapacity D) :
    criticalCombinedVariableCapacity D -
        criticalCombinedSelectedCount k n D =
      criticalCombinedMissingCount k n D.sparse.card := by
  have htotal := criticalCombinedVariableCapacity_add_internal_eq D
  unfold criticalCombinedSelectedCount criticalCombinedMissingCount
  omega

/-- The exact division-independent missing-coordinate identity, guarded by
nonemptiness of the clean fiber. -/
theorem criticalCombinedVariableCapacity_sub_selected_eq_missing_of_nonempty
    {k n : ℕ} {hk : 3 ≤ k} {tau : ℝ} {hn : k - 1 ≤ n}
    {D : SupercriticalDivision k (Fin n)}
    (hD : (criticalCleanDivisionGraphFinset k hk n tau hn D).Nonempty) :
    criticalCombinedVariableCapacity D -
        criticalCombinedSelectedCount k n D =
      criticalCombinedMissingCount k n D.sparse.card := by
  obtain ⟨hlower, hupper⟩ :=
    criticalCombinedSelectedCount_feasible_of_nonempty hD
  exact criticalCombinedVariableCapacity_sub_selected_eq_missing
    D hlower hupper

/-- Feasibility also places the common missing count below the balanced
maximum capacity. -/
theorem criticalCombinedMissingCount_le_maximum_of_nonempty
    {k n : ℕ} {hk : 3 ≤ k} {tau : ℝ} {hn : k - 1 ≤ n}
    {D : SupercriticalDivision k (Fin n)}
    (hD : (criticalCleanDivisionGraphFinset k hk n tau hn D).Nonempty) :
    criticalCombinedMissingCount k n D.sparse.card ≤
      criticalMaximumCombinedCapacity k n D.sparse.card := by
  have hidentity :=
    criticalCombinedVariableCapacity_sub_selected_eq_missing_of_nonempty hD
  have hsub : criticalCombinedVariableCapacity D -
      criticalCombinedSelectedCount k n D ≤
        criticalCombinedVariableCapacity D := Nat.sub_le _ _
  rw [hidentity] at hsub
  exact hsub.trans (criticalCombinedVariableCapacity_le_maximum D)

/-- On every nonempty clean fiber, the maximum selected count has the
expected edge-count-minus-balanced-internal-capacity formula.  This is the
selected-count companion to the capacity identity. -/
theorem criticalMaximumCombinedSelectedCount_eq_of_nonempty
    {k n : ℕ} {hk : 3 ≤ k} {tau : ℝ} {hn : k - 1 ≤ n}
    {D : SupercriticalDivision k (Fin n)}
    (hD : (criticalCleanDivisionGraphFinset k hk n tau hn D).Nonempty) :
    criticalMaximumCombinedSelectedCount k n D.sparse.card =
      criticalEdgeCount k n -
        DenseGraph.balancedMultipartiteInternalCapacity
          (k - 1) (n - D.sparse.card) := by
  obtain ⟨hlower, hselected⟩ :=
    criticalCombinedSelectedCount_feasible_of_nonempty hD
  have holdTotal := criticalCombinedVariableCapacity_add_internal_eq D
  have hmaxTotal := criticalMaximumCombinedCapacity_add_balancedInternal
    k n D.sparse.card
  have hcap := criticalCombinedVariableCapacity_le_maximum D
  have hbalancedLower :
      DenseGraph.balancedMultipartiteInternalCapacity
          (k - 1) (n - D.sparse.card) ≤
        divisionInternalCliqueCapacity D := by
    omega
  have hedgeUpper : criticalEdgeCount k n ≤
      Nat.choose (n - D.sparse.card) 2 + Nat.choose D.sparse.card 2 := by
    unfold criticalCombinedSelectedCount at hselected
    omega
  unfold criticalMaximumCombinedSelectedCount criticalCombinedMissingCount
  omega

/-! ## The maximum selected slice and clean-family bounds -/

/-- At feasible sparse size the maximum selected count and the common
missing count partition the maximum capacity. -/
theorem criticalMaximumSelected_add_missing
    {k n s : ℕ}
    (hmissing : criticalCombinedMissingCount k n s ≤
      criticalMaximumCombinedCapacity k n s) :
    criticalMaximumCombinedSelectedCount k n s +
        criticalCombinedMissingCount k n s =
      criticalMaximumCombinedCapacity k n s := by
  unfold criticalMaximumCombinedSelectedCount
  omega

/-- The maximum slice may equivalently be indexed by its selected or missing
coordinate count. -/
theorem choose_maximumSelected_eq_choose_missing
    {k n s : ℕ}
    (hmissing : criticalCombinedMissingCount k n s ≤
      criticalMaximumCombinedCapacity k n s) :
    Nat.choose (criticalMaximumCombinedCapacity k n s)
        (criticalMaximumCombinedSelectedCount k n s) =
      Nat.choose (criticalMaximumCombinedCapacity k n s)
        (criticalCombinedMissingCount k n s) := by
  exact Nat.choose_symm_of_eq_add
    (criticalMaximumSelected_add_missing hmissing).symm

/-- Every nonempty clean critical division fiber is bounded by one binomial
slice at the balanced maximum capacity, indexed by the common missing count. -/
theorem card_criticalCleanDivisionGraphFinset_le_choose_maximum_missing
    {k n : ℕ} {hk : 3 ≤ k} {tau : ℝ} {hn : k - 1 ≤ n}
    {D : SupercriticalDivision k (Fin n)}
    (hD : (criticalCleanDivisionGraphFinset k hk n tau hn D).Nonempty) :
    (criticalCleanDivisionGraphFinset k hk n tau hn D).card ≤
      Nat.choose (criticalMaximumCombinedCapacity k n D.sparse.card)
        (criticalCombinedMissingCount k n D.sparse.card) := by
  obtain ⟨_hlower, hselected⟩ :=
    criticalCombinedSelectedCount_feasible_of_nonempty hD
  have hidentity :=
    criticalCombinedVariableCapacity_sub_selected_eq_missing_of_nonempty hD
  calc
    (criticalCleanDivisionGraphFinset k hk n tau hn D).card ≤
        Nat.choose (criticalCombinedVariableCapacity D)
          (criticalCombinedSelectedCount k n D) := by
      simpa only [criticalCleanDivisionGraphFinset,
        criticalCombinedVariableCapacity, criticalCombinedSelectedCount,
        supercriticalPreAbsorptionVariableCapacity,
        supercriticalSparsePotentialCapacity] using
          (card_supercriticalCleanDivisionGraphFinset_le_preAbsorptionChoose
            (hk := hk) (hgamma := gammaK_mem_supercritical_Ico k hk)
              (m := criticalEdgeCount k n) (tau := tau) (hn := hn) D)
    _ = Nat.choose (criticalCombinedVariableCapacity D)
          (criticalCombinedMissingCount k n D.sparse.card) := by
      rw [← hidentity]
      exact (Nat.choose_symm hselected).symm
    _ ≤ Nat.choose (criticalMaximumCombinedCapacity k n D.sparse.card)
          (criticalCombinedMissingCount k n D.sparse.card) :=
      Nat.choose_le_choose _ (criticalCombinedVariableCapacity_le_maximum D)

/-- Selected-count form of the same balanced one-binomial-slice bound. -/
theorem card_criticalCleanDivisionGraphFinset_le_choose_maximum_selected
    {k n : ℕ} {hk : 3 ≤ k} {tau : ℝ} {hn : k - 1 ≤ n}
    {D : SupercriticalDivision k (Fin n)}
    (hD : (criticalCleanDivisionGraphFinset k hk n tau hn D).Nonempty) :
    (criticalCleanDivisionGraphFinset k hk n tau hn D).card ≤
      Nat.choose (criticalMaximumCombinedCapacity k n D.sparse.card)
        (criticalMaximumCombinedSelectedCount k n D.sparse.card) := by
  rw [choose_maximumSelected_eq_choose_missing
    (criticalCombinedMissingCount_le_maximum_of_nonempty hD)]
  exact card_criticalCleanDivisionGraphFinset_le_choose_maximum_missing hD

/-- Total missing-coordinate form of the clean-fiber slice bound.  The
nonempty case is the substantive estimate above; an empty fiber is bounded
trivially. -/
theorem card_criticalCleanDivisionGraphFinset_le_choose_maximum_missing_total
    {k n : ℕ} {hk : 3 ≤ k} {tau : ℝ} {hn : k - 1 ≤ n}
    (D : SupercriticalDivision k (Fin n)) :
    (criticalCleanDivisionGraphFinset k hk n tau hn D).card ≤
      Nat.choose (criticalMaximumCombinedCapacity k n D.sparse.card)
        (criticalCombinedMissingCount k n D.sparse.card) := by
  by_cases hD :
      (criticalCleanDivisionGraphFinset k hk n tau hn D).Nonempty
  · exact card_criticalCleanDivisionGraphFinset_le_choose_maximum_missing hD
  · rw [Finset.not_nonempty_iff_eq_empty.mp hD]
    simp

/-- Total selected-coordinate form of the clean-fiber slice bound. -/
theorem card_criticalCleanDivisionGraphFinset_le_choose_maximum_selected_total
    {k n : ℕ} {hk : 3 ≤ k} {tau : ℝ} {hn : k - 1 ≤ n}
    (D : SupercriticalDivision k (Fin n)) :
    (criticalCleanDivisionGraphFinset k hk n tau hn D).card ≤
      Nat.choose (criticalMaximumCombinedCapacity k n D.sparse.card)
        (criticalMaximumCombinedSelectedCount k n D.sparse.card) := by
  by_cases hD :
      (criticalCleanDivisionGraphFinset k hk n tau hn D).Nonempty
  · exact card_criticalCleanDivisionGraphFinset_le_choose_maximum_selected hD
  · rw [Finset.not_nonempty_iff_eq_empty.mp hD]
    simp

end InducedStars
