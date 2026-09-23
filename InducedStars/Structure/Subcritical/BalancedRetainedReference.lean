import InducedStars.Structure.Subcritical.RetainedKeyCounts
import InducedStars.Structure.Subcritical.ActiveLevelComparison
import InducedStars.Structure.Supercritical.AggregateChoices
import DenseGraph.FiniteModels.BalancedAssignments

/-!
# Literal balanced one-core retained reference keys

Paper: the reference templates following `eqn:sub-gamma-b-K1k`.
This constructs one retained key, not a family of independently
decorated full divisions. The support size is an explicit integer parameter.
-/

noncomputable section
open Finset Set
open scoped Classical BigOperators
namespace InducedStars

def balancedRetainedSupportEmbedding {q n : ℕ} (hqn : q ≤ n) : Fin q ↪ Fin n :=
  ⟨fun v ↦ ⟨v.val, v.isLt.trans_le hqn⟩,
    fun _ _ h ↦ Fin.ext (congrArg (fun v : Fin n ↦ v.val) h)⟩

def balancedRetainedSuperdivision {k n q : ℕ} (hk : 3 ≤ k)
    (hrq : k - 1 ≤ q) (hqn : q ≤ n) : SupercriticalDivision k (Fin n) where
  parts i := (DenseGraph.balancedFinPartition (k - 1) q i).map
    (balancedRetainedSupportEmbedding hqn)
  parts_nonempty i := (DenseGraph.balancedFinPartition_nonempty (by omega) hrq i).map
  parts_pairwiseDisjoint := by
    intro i _ j _ hij
    apply (Finset.disjoint_map _).mpr
    exact DenseGraph.balancedFinPartition_pairwiseDisjoint _ _ (Set.mem_univ i)
      (Set.mem_univ j) hij

def balancedRetainedDivision {k n q : ℕ} (hk : 3 ≤ k)
    (hrq : k - 1 ≤ q) (hqn : q ≤ n) : SubcriticalDivision k (Fin n) :=
  SubcriticalDivision.ofSupercritical hk (balancedRetainedSuperdivision hk hrq hqn)

def balancedRetainedReferenceKey {k n q : ℕ} (hk : 3 ≤ k)
    (hrq : k - 1 ≤ q) (hqn : q ≤ n) : SubcriticalRetainedKey k (Fin n) :=
  retainedKey (balancedRetainedDivision hk hrq hqn) 0 n

@[simp] theorem balancedRetainedDivision_part_card {k n q : ℕ} (hk : 3 ≤ k)
    (hrq : k - 1 ≤ q) (hqn : q ≤ n)
    (i : Fin 1) (j : Fin (k - 1)) :
    ((balancedRetainedDivision hk hrq hqn).parts i j).card =
      (DenseGraph.balancedFinPartition (k - 1) q j).card := by
  exact Finset.card_map _

@[simp] theorem balancedRetainedSuperdivision_support_card {k n q : ℕ} (hk : 3 ≤ k)
    (hrq : k - 1 ≤ q) (hqn : q ≤ n) :
    (balancedRetainedSuperdivision hk hrq hqn).support.card = q := by
  rw [SupercriticalDivision.card_support]
  simp only [balancedRetainedSuperdivision, Finset.card_map]
  simpa only [DenseGraph.balancedPartSize_eq_card_balancedFinPartition
    (show 0 < k - 1 by omega)] using
    (DenseGraph.sum_balancedPartSize (r := k - 1) (q := q) (by omega))

@[simp] theorem balancedRetainedDivision_support_card {k n q : ℕ} (hk : 3 ≤ k)
    (hrq : k - 1 ≤ q) (hqn : q ≤ n) :
    (balancedRetainedDivision hk hrq hqn).support.card = q := by
  rw [SubcriticalDivision.card_support]
  change (∑ a : (Σ _ : Fin 1, Fin (k - 1)),
    ((balancedRetainedDivision hk hrq hqn).parts a.1 a.2).card) = q
  rw [Fintype.sum_sigma]
  simp only [balancedRetainedDivision_part_card, Fin.sum_univ_one]
  simpa only [DenseGraph.balancedPartSize_eq_card_balancedFinPartition
    (show 0 < k - 1 by omega)] using
    (DenseGraph.sum_balancedPartSize (r := k - 1) (q := q) (by omega))

@[simp] theorem balancedRetainedReferenceKey_support_card {k n q : ℕ} (hk : 3 ≤ k)
    (hrq : k - 1 ≤ q) (hqn : q ≤ n) :
    (balancedRetainedReferenceKey hk hrq hqn).support.card = q := by
  rw [balancedRetainedReferenceKey, retainedKey_support]
  have ha := (balancedRetainedDivision hk hrq hqn).retainedVertices_all
  simp only [Fintype.card_fin] at ha
  rw [ha, balancedRetainedDivision_support_card]

@[simp] theorem balancedRetainedReferenceKey_remainder_card {k n q : ℕ} (hk : 3 ≤ k)
    (hrq : k - 1 ≤ q) (hqn : q ≤ n) :
    (balancedRetainedReferenceKey hk hrq hqn).remainder.card = n - q := by
  rw [SubcriticalRetainedKey.remainder, Finset.card_sdiff_of_subset (Finset.subset_univ _),
    Finset.card_univ, Fintype.card_fin, balancedRetainedReferenceKey_support_card]

private theorem all_retainedPartIndices {k : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    (D : SubcriticalDivision k V) :
    D.retainedPartIndices 0 (Fintype.card V) = Finset.univ := by
  ext a
  simp only [D.mem_retainedPartIndices, D.retainedComponentIndices_all, Finset.mem_univ]

theorem balancedRetainedDivision_cliqueCapacity {k n q : ℕ} (hk : 3 ≤ k)
    (hrq : k - 1 ≤ q) (hqn : q ≤ n) :
    retainedCliqueCapacity (balancedRetainedDivision hk hrq hqn) 0 n =
      DenseGraph.balancedMultipartiteInternalCapacity (k - 1) q := by
  rw [retainedCliqueCapacity]
  have ha := all_retainedPartIndices (balancedRetainedDivision hk hrq hqn)
  simp only [Fintype.card_fin] at ha
  rw [ha]
  change (∑ a : (Σ _ : Fin 1, Fin (k - 1)),
    (((balancedRetainedDivision hk hrq hqn).parts a.1 a.2).card).choose 2) = _
  rw [Fintype.sum_sigma]
  simp only [balancedRetainedDivision_part_card, Fin.sum_univ_one]
  exact (DenseGraph.balancedMultipartiteInternalCapacity_eq_sum_choose (by omega)).symm

private def completeRetainedPairEquiv {k : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    (hk : 3 ≤ k) (D : SupercriticalDivision k V) :
    RetainedActivePair (SubcriticalDivision.ofSupercritical hk D) 0 (Fintype.card V) ≃
      SupercriticalPartPair k where
  toFun e := ⟨e.left, e.right, e.left_lt_right⟩
  invFun e := {
    component := ⟨0, Nat.zero_lt_one⟩
    component_retained := by rw [SubcriticalDivision.retainedComponentIndices_all]; simp
    left := e.left
    right := e.right
    left_lt_right := e.left_lt_right
    active := e.left_ne_right }
  left_inv e := by
    rcases e with ⟨i, hi, a, b, hab, hadj⟩
    have hi0 : i = ⟨0, Nat.zero_lt_one⟩ := by
      apply Fin.ext
      change i.val = 0
      have hi := i.isLt
      change i.val < 1 at hi
      omega
    subst i
    rfl
  right_inv e := by cases e; rfl

theorem balancedRetainedDivision_activeCapacity {k n q : ℕ} (hk : 3 ≤ k)
    (hrq : k - 1 ≤ q) (hqn : q ≤ n)
    (e : RetainedActivePair (balancedRetainedDivision hk hrq hqn) 0 n) :
    retainedActiveCapacity (balancedRetainedDivision hk hrq hqn) 0 n e =
      (DenseGraph.balancedFinPartition (k - 1) q e.left).card *
        (DenseGraph.balancedFinPartition (k - 1) q e.right).card := by
  simp only [retainedActiveCapacity, SubcriticalDivision.part, RetainedActivePair.leftPart,
    RetainedActivePair.rightPart, balancedRetainedDivision, SubcriticalDivision.ofSupercritical,
    balancedRetainedSuperdivision, Finset.card_map]

theorem balancedRetainedDivision_activeTotalCapacity {k n q : ℕ} (hk : 3 ≤ k)
    (hrq : k - 1 ≤ q) (hqn : q ≤ n) :
    retainedActiveTotalCapacity (balancedRetainedDivision hk hrq hqn) 0 n =
      DenseGraph.balancedMultipartiteCrossCapacity (k - 1) q := by
  let D := balancedRetainedSuperdivision hk hrq hqn
  have hsum : retainedActiveTotalCapacity (SubcriticalDivision.ofSupercritical hk D)
      0 n = supercriticalTotalCrossCapacity D := by
    have h := (completeRetainedPairEquiv hk D).sum_comp (crossEdgeCapacity D)
    change retainedActiveTotalCapacity (SubcriticalDivision.ofSupercritical hk D)
      0 (Fintype.card (Fin n)) = supercriticalTotalCrossCapacity D at h
    simpa only [Fintype.card_fin] using h
  have hi : divisionInternalCliqueCapacity D =
      DenseGraph.balancedMultipartiteInternalCapacity (k - 1) q := by
    unfold divisionInternalCliqueCapacity
    simp only [D, balancedRetainedSuperdivision, Finset.card_map]
    exact (DenseGraph.balancedMultipartiteInternalCapacity_eq_sum_choose (by omega)).symm
  have ht := supercriticalTotalCrossCapacity_add_internal D
  rw [hi, balancedRetainedSuperdivision_support_card] at ht
  have hb := DenseGraph.balancedCross_add_internal (k - 1) q
  change retainedActiveTotalCapacity (SubcriticalDivision.ofSupercritical hk D)
    0 n = _
  omega

theorem balancedRetainedReferenceKey_cliqueCapacity {k n q : ℕ} (hk : 3 ≤ k)
    (hrq : k - 1 ≤ q) (hqn : q ≤ n) :
    (balancedRetainedReferenceKey hk hrq hqn).cliqueCapacity =
      DenseGraph.balancedMultipartiteInternalCapacity (k - 1) q := by
  rw [balancedRetainedReferenceKey, retainedKey_cliqueCapacity,
    balancedRetainedDivision_cliqueCapacity]

end InducedStars
