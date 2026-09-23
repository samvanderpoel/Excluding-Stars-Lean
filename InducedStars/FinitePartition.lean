import InducedStars.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-!
# Finite indexed partitions

Generic lemmas for a finite family of pairwise-disjoint finite subsets.  The
historical declarations live in `InducedStars.ColoredGraph`; the namespace is
retained so existing clients keep exactly the same public names and types.
Nothing in this module depends on colored graphs or on the induced-star
problem.
-/

open Finset

namespace InducedStars
namespace ColoredGraph

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- Union of a finite indexed cluster family. -/
def clusterUnion {I : Type*} [Fintype I] [DecidableEq I]
    (clusters : I → Finset V) : Finset V :=
  (Finset.univ : Finset I).biUnion clusters

/-- Every cluster lies in the cluster union. -/
theorem cluster_subset_clusterUnion {I : Type*} [Fintype I] [DecidableEq I]
    (clusters : I → Finset V) (i : I) :
    clusters i ⊆ clusterUnion clusters := by
  exact Finset.subset_biUnion_of_mem clusters (Finset.mem_univ i)

/-- The cardinality of a pairwise-disjoint cluster union is the sum of the
cluster cardinalities. -/
theorem card_clusterUnion {I : Type*} [Fintype I] [DecidableEq I]
    (clusters : I → Finset V)
    (hdisj : Set.PairwiseDisjoint (Set.univ : Set I) clusters) :
    (clusterUnion clusters).card = ∑ i, (clusters i).card := by
  have hdisj' :
      ((Finset.univ : Finset I) : Set I).PairwiseDisjoint clusters := by
    simpa using hdisj
  simpa [clusterUnion] using
    (Finset.card_biUnion (s := (Finset.univ : Finset I)) hdisj')

/-- Pairwise-disjoint clusters occupy at most the ambient finite type. -/
theorem sum_cluster_card_le_card {I : Type*} [Fintype I] [DecidableEq I]
    (clusters : I → Finset V)
    (hdisj : Set.PairwiseDisjoint (Set.univ : Set I) clusters) :
    ∑ i, (clusters i).card ≤ Fintype.card V := by
  rw [← card_clusterUnion clusters hdisj, ← Finset.card_univ]
  exact Finset.card_le_card (Finset.subset_univ _)

/-- If every pairwise-disjoint cluster has real cardinality at least `a`,
then the number of clusters times `a` is at most the ambient cardinality. -/
theorem card_mul_clusterLower_le_card {I : Type*} [Fintype I] [DecidableEq I]
    (clusters : I → Finset V) (a : ℝ)
    (hdisj : Set.PairwiseDisjoint (Set.univ : Set I) clusters)
    (hmin : ∀ i, a ≤ ((clusters i).card : ℝ)) :
    (Fintype.card I : ℝ) * a ≤ (Fintype.card V : ℝ) := by
  calc
    (Fintype.card I : ℝ) * a = ∑ _i : I, a := by simp
    _ ≤ ∑ i : I, ((clusters i).card : ℝ) :=
      Finset.sum_le_sum fun i _ ↦ hmin i
    _ = ((∑ i : I, (clusters i).card : ℕ) : ℝ) := by push_cast; rfl
    _ ≤ (Fintype.card V : ℝ) := by
      exact_mod_cast sum_cluster_card_le_card clusters hdisj

end ColoredGraph
end InducedStars
