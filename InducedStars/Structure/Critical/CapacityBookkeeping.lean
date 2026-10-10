import InducedStars.Structure.Critical.Reference
import Mathlib.Tactic

/-!
# Combined capacities at the critical density

The combined variable set consists of cross pairs between the main parts and
pairs inside the remainder. Balancing the main parts maximizes its capacity.
-/

noncomputable section
open Finset Set
open scoped BigOperators
namespace InducedStars
variable {k n : ℕ}

/-- Pairs between distinct main parts together with pairs inside the remainder. -/
def criticalCombinedVariableCapacity
    (D : SupercriticalDivision k (Fin n)) : ℕ :=
  supercriticalTotalCrossCapacity D + Nat.choose D.sparse.card 2

/-- The maximum combined variable capacity for a remainder of size s. -/
def criticalMaximumCombinedCapacity (k n s : ℕ) : ℕ :=
  DenseGraph.balancedMultipartiteCrossCapacity (k - 1) (n - s) +
    Nat.choose s 2

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

end InducedStars
