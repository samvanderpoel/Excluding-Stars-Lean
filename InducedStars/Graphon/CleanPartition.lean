import InducedStars.Graphon.Approximation
import InducedStars.Regularity.Reindex
import InducedStars.Regularity.TypeLemma
import Mathlib.Data.Int.CardIntervalMod

/-!
# Clean partitions and their density matrices

This file carries out the finite bookkeeping used in the proof of the Type
Graphon Sequence Lemma.  A clean partition is obtained from a Type partition
by distributing the exceptional vertices among the nonexceptional classes,
inside their prescribed initial parents.  The allocation pieces are allowed
to be empty; the resulting clean classes are not, since they contain the Type
clusters.

The final section compares exact size-weighted density averaging under a
uniform refinement with the unweighted consecutive block average used by
Lovasz--Szegedy.
-/

noncomputable section

open Finset Fintype Function
open scoped BigOperators SimpleGraph

namespace InducedStars

namespace Regularity

universe u

/-! ## Balanced allocations which allow empty pieces -/

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- The canonical enumeration of a finite set, used only to make the balanced
allocation below a definition rather than an existential witness. -/
def finsetEnumeration (A : Finset V) : Fin A.card ≃ A :=
  (finCongr (Fintype.card_coe A).symm).trans (Fintype.equivFin A).symm

/-- Split `A` among `r` labelled bins by the residue of a fixed enumeration.

Unlike a `Finpartition`, the individual bins are permitted to be empty. -/
def balancedAllocation (A : Finset V) (r : ℕ) (a : Fin r) : Finset V :=
  ((Finset.univ.filter fun x : Fin A.card => x.1 % r = a.1).map
    ((finsetEnumeration A).toEmbedding.trans (Function.Embedding.subtype _)))

@[simp]
theorem mem_balancedAllocation {A : Finset V} {r : ℕ} {a : Fin r} {x : V} :
    x ∈ balancedAllocation A r a ↔
      ∃ y : Fin A.card, y.1 % r = a.1 ∧ (finsetEnumeration A y : V) = x := by
  simp [balancedAllocation]

theorem balancedAllocation_subset (A : Finset V) (r : ℕ) (a : Fin r) :
    balancedAllocation A r a ⊆ A := by
  intro x hx
  rw [mem_balancedAllocation] at hx
  obtain ⟨y, -, rfl⟩ := hx
  exact (finsetEnumeration A y).2

theorem balancedAllocation_pairwiseDisjoint (A : Finset V) (r : ℕ) :
    Set.PairwiseDisjoint (Set.univ : Set (Fin r)) (balancedAllocation A r) := by
  intro a _ b _ hab
  change Disjoint (balancedAllocation A r a) (balancedAllocation A r b)
  rw [Finset.disjoint_left]
  intro x hxa hxb
  rw [mem_balancedAllocation] at hxa hxb
  obtain ⟨ya, hya, hyax⟩ := hxa
  obtain ⟨yb, hyb, hybx⟩ := hxb
  have hy : ya = yb := by
    apply (finsetEnumeration A).injective
    apply Subtype.ext
    exact hyax.trans hybx.symm
  subst yb
  apply hab
  apply Fin.ext
  omega

@[simp]
theorem biUnion_balancedAllocation (A : Finset V) (r : ℕ) (hr : 0 < r) :
    Finset.univ.biUnion (balancedAllocation A r) = A := by
  apply Finset.Subset.antisymm
  · intro x hx
    rw [Finset.mem_biUnion] at hx
    obtain ⟨a, -, hxa⟩ := hx
    exact balancedAllocation_subset A r a hxa
  · intro x hx
    let y : Fin A.card := (finsetEnumeration A).symm ⟨x, hx⟩
    let a : Fin r := ⟨y.1 % r, Nat.mod_lt _ hr⟩
    rw [Finset.mem_biUnion]
    refine ⟨a, Finset.mem_univ _, ?_⟩
    rw [mem_balancedAllocation]
    refine ⟨y, rfl, ?_⟩
    change (((finsetEnumeration A) ((finsetEnumeration A).symm ⟨x, hx⟩) : A) : V) = x
    simp

private theorem card_filter_fin_mod (n r : ℕ) (a : Fin r) :
    (Finset.univ.filter fun x : Fin n => x.1 % r = a.1).card =
      Nat.count (fun x => x % r = a.1) n := by
  rw [Nat.count_eq_card_filter_range]
  apply Finset.card_bij (fun x _ => x.1)
  · intro x hx
    rw [Finset.mem_filter] at hx ⊢
    exact ⟨Finset.mem_range.mpr x.2, hx.2⟩
  · intro x hx y hy hxy
    exact Fin.ext hxy
  · intro x hx
    rw [Finset.mem_filter] at hx
    exact ⟨⟨x, Finset.mem_range.mp hx.1⟩, by simp [hx.2], rfl⟩

/-- Exact size of one balanced allocation bin. -/
theorem card_balancedAllocation (A : Finset V) {r : ℕ} (hr : 0 < r) (a : Fin r) :
    (balancedAllocation A r a).card =
      A.card / r + if a.1 < A.card % r then 1 else 0 := by
  rw [balancedAllocation, Finset.card_map, card_filter_fin_mod]
  have h := Nat.count_modEq_card (b := A.card) (r := r) hr a.1
  simpa only [Nat.ModEq, Nat.mod_eq_of_lt a.2] using h

/-- The sizes of any two allocation bins differ by at most one. -/
theorem balancedAllocation_card_dist_le_one (A : Finset V) {r : ℕ} (hr : 0 < r)
    (a b : Fin r) :
    Nat.dist (balancedAllocation A r a).card (balancedAllocation A r b).card ≤ 1 := by
  rw [card_balancedAllocation A hr, card_balancedAllocation A hr]
  split_ifs <;> simp [Nat.dist] <;> omega

/-- Every allocation bin has size at most the average plus one. -/
theorem card_balancedAllocation_le_average_add_one (A : Finset V) {r : ℕ}
    (hr : 0 < r) (a : Fin r) :
    (balancedAllocation A r a).card ≤ A.card / r + 1 := by
  rw [card_balancedAllocation A hr]
  split_ifs <;> omega

/-- If the source sets have sizes differing by at most one, then every pair
of bins in their balanced allocations also has sizes differing by at most
one.  This is the global equity calculation used for clean children lying
under distinct parent classes. -/
theorem balancedAllocation_card_dist_le_one_of_card_dist_le_one
    (A B : Finset V) {r : ℕ} (hr : 0 < r)
    (hAB : Nat.dist A.card B.card ≤ 1) (a b : Fin r) :
    Nat.dist (balancedAllocation A r a).card
      (balancedAllocation B r b).card ≤ 1 := by
  have hcases : A.card = B.card ∨ A.card + 1 = B.card ∨ B.card + 1 = A.card := by
    simp only [Nat.dist] at hAB
    omega
  rw [card_balancedAllocation A hr, card_balancedAllocation B hr]
  rcases hcases with h | h | h
  · rw [h]
    split_ifs <;> simp [Nat.dist] <;> omega
  · rw [← h]
    by_cases hdvd : r ∣ A.card + 1
    · rw [Nat.succ_div_of_dvd hdvd, Nat.mod_eq_zero_of_dvd hdvd]
      split_ifs <;> simp [Nat.dist] <;> omega
    · rw [Nat.succ_div_of_not_dvd hdvd]
      split_ifs <;> simp [Nat.dist] <;> omega
  · rw [← h]
    by_cases hdvd : r ∣ B.card + 1
    · rw [Nat.succ_div_of_dvd hdvd, Nat.mod_eq_zero_of_dvd hdvd]
      split_ifs <;> simp [Nat.dist] <;> omega
    · rw [Nat.succ_div_of_not_dvd hdvd]
      split_ifs <;> simp [Nat.dist] <;> omega

/-! ## Abstract clean Type partitions -/

variable {G : SimpleGraph V} [DecidableRel G.Adj]
  {epsilon delta : ℝ} {ell : ℕ}

/-- An equitable partition of the whole host obtained by enlarging every
nonexceptional Type cluster only with exceptional vertices.  The Type and
clean classes have literally the same index type, which is what the later
equal-cell `L¹` comparison needs. -/
structure CleanTypePartition (T : RegularityType G epsilon delta ell) where
  partition : EquitableInitialPartition V T.partition.clusterCount
  cluster_subset : ∀ i, T.partition.clusters i ⊆ partition.parts i
  added_subset_exceptional :
    ∀ i, partition.parts i \ T.partition.clusters i ⊆ T.partition.exceptional

namespace CleanTypePartition

variable {T : RegularityType G epsilon delta ell}

/-- Every clean class is contained in the union of its Type cluster and the
Type exceptional set. -/
theorem part_subset_cluster_union_exceptional (P : CleanTypePartition T)
    (i : Fin T.partition.clusterCount) :
    P.partition.parts i ⊆ T.partition.clusters i ∪ T.partition.exceptional := by
  intro x hx
  by_cases hxc : x ∈ T.partition.clusters i
  · exact Finset.mem_union_left _ hxc
  · exact Finset.mem_union_right _ (P.added_subset_exceptional i <|
      Finset.mem_sdiff.mpr ⟨hx, hxc⟩)

/-- The vertices added to a Type cluster are exactly its clean-class
difference. -/
def addedVertices (P : CleanTypePartition T)
    (i : Fin T.partition.clusterCount) : Finset V :=
  P.partition.parts i \ T.partition.clusters i

theorem addedVertices_subset_exceptional (P : CleanTypePartition T)
    (i : Fin T.partition.clusterCount) :
    P.addedVertices i ⊆ T.partition.exceptional :=
  P.added_subset_exceptional i

theorem cluster_disjoint_addedVertices (P : CleanTypePartition T)
    (i : Fin T.partition.clusterCount) :
    Disjoint (T.partition.clusters i) (P.addedVertices i) := by
  rw [Finset.disjoint_left]
  intro x hxc hxa
  exact (Finset.mem_sdiff.mp hxa).2 hxc

@[simp]
theorem cluster_union_addedVertices (P : CleanTypePartition T)
    (i : Fin T.partition.clusterCount) :
    T.partition.clusters i ∪ P.addedVertices i = P.partition.parts i := by
  rw [addedVertices, Finset.union_sdiff_of_subset (P.cluster_subset i)]

theorem card_part_eq_cluster_add_added (P : CleanTypePartition T)
    (i : Fin T.partition.clusterCount) :
    (P.partition.parts i).card =
      (T.partition.clusters i).card + (P.addedVertices i).card := by
  rw [← P.cluster_union_addedVertices i,
    Finset.card_union_of_disjoint (P.cluster_disjoint_addedVertices i)]

end CleanTypePartition

/-! ## Cleaning a canonically reindexed Type Lemma output -/

namespace TypeLemmaResult

variable {eta delta' : ℝ} {ell' s L U : ℕ}
  {initial : EquitableInitialPartition V s}
  (R : TypeLemmaResult G eta delta' ell' initial L U)

/-- Exceptional vertices lying in one prescribed initial parent. -/
def parentExceptional (i : Fin s) : Finset V :=
  initial.parts i ∩ R.regularityType.partition.exceptional

/-- The exceptional vertices assigned to one canonical child. -/
def allocatedExceptional (i : Fin s) (a : Fin R.childCount) : Finset V :=
  balancedAllocation (R.parentExceptional i) R.childCount a

/-- One clean child, before bundling all children into an equitable
partition. -/
def cleanChildAt (i : Fin s) (a : Fin R.childCount) : Finset V :=
  R.canonicalType.partition.clusters (finProdFinEquiv (i, a)) ∪
    R.allocatedExceptional i a

/-- The clean children indexed consecutively by parent and then child. -/
def cleanChild (x : Fin (s * R.childCount)) : Finset V :=
  let ia := finProdFinEquiv.symm x
  R.cleanChildAt ia.1 ia.2

@[simp]
theorem cleanChild_finProdFinEquiv (i : Fin s) (a : Fin R.childCount) :
    R.cleanChild (finProdFinEquiv (i, a)) = R.cleanChildAt i a := by
  simp [cleanChild]

theorem parentExceptional_subset_initial (i : Fin s) :
    R.parentExceptional i ⊆ initial.parts i :=
  Finset.inter_subset_left

theorem parentExceptional_subset_exceptional (i : Fin s) :
    R.parentExceptional i ⊆ R.regularityType.partition.exceptional :=
  Finset.inter_subset_right

theorem parentExceptional_pairwiseDisjoint :
    Set.PairwiseDisjoint (Set.univ : Set (Fin s)) R.parentExceptional := by
  intro i _ j _ hij
  apply (initial.parts_disjoint hij).mono
  · exact R.parentExceptional_subset_initial i
  · exact R.parentExceptional_subset_initial j

@[simp]
theorem biUnion_parentExceptional :
    Finset.univ.biUnion R.parentExceptional =
      R.regularityType.partition.exceptional := by
  apply Finset.Subset.antisymm
  · intro x hx
    obtain ⟨i, -, hxi⟩ := Finset.mem_biUnion.mp hx
    exact R.parentExceptional_subset_exceptional i hxi
  · intro x hx
    obtain ⟨i, hxi⟩ := initial.exists_mem_part x
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _,
      Finset.mem_inter.mpr ⟨hxi, hx⟩⟩

theorem sum_card_parentExceptional :
    ∑ i : Fin s, (R.parentExceptional i).card =
      R.regularityType.partition.exceptional.card := by
  rw [← R.biUnion_parentExceptional, Finset.card_biUnion]
  intro i _ j _ hij
  exact R.parentExceptional_pairwiseDisjoint
    (Set.mem_univ i) (Set.mem_univ j) hij

theorem allocatedExceptional_subset_initial (i : Fin s)
    (a : Fin R.childCount) :
    R.allocatedExceptional i a ⊆ initial.parts i :=
  (balancedAllocation_subset _ _ _).trans
    (R.parentExceptional_subset_initial i)

theorem allocatedExceptional_subset_exceptional (i : Fin s)
    (a : Fin R.childCount) :
    R.allocatedExceptional i a ⊆
      R.regularityType.partition.exceptional :=
  (balancedAllocation_subset _ _ _).trans
    (R.parentExceptional_subset_exceptional i)

@[simp]
theorem biUnion_allocatedExceptional (i : Fin s) :
    Finset.univ.biUnion (R.allocatedExceptional i) =
      R.parentExceptional i := by
  exact biUnion_balancedAllocation _ _ R.childCount_pos

/-- Every prescribed parent has the same number of nonexceptional vertices:
`childCount` times the common cluster size. -/
theorem card_parent_sdiff_exception (i : Fin s) :
    (initial.parts i \ R.regularityType.partition.exceptional).card =
      R.childCount * R.regularityType.partition.clusterSize := by
  classical
  rw [R.parent_sdiff_exception_eq_biUnion, Finset.card_biUnion]
  · simp [R.regularityType.partition.cluster_card_eq,
      R.parentBlock_card]
  · intro j hj k hk hjk
    exact R.regularityType.partition.clusters_disjoint hjk

/-- The exceptional counts inside prescribed parents differ by at most one.
This is where equity of the initial partition and equality of all Type
cluster sizes are combined. -/
theorem parentExceptional_card_dist_le_one (i j : Fin s) :
    Nat.dist (R.parentExceptional i).card
      (R.parentExceptional j).card ≤ 1 := by
  have hi := Finset.card_inter_add_card_sdiff
    (initial.parts i) R.regularityType.partition.exceptional
  have hj := Finset.card_inter_add_card_sdiff
    (initial.parts j) R.regularityType.partition.exceptional
  change (R.parentExceptional i).card +
    (initial.parts i \ R.regularityType.partition.exceptional).card =
      (initial.parts i).card at hi
  change (R.parentExceptional j).card +
    (initial.parts j \ R.regularityType.partition.exceptional).card =
      (initial.parts j).card at hj
  rw [R.card_parent_sdiff_exception] at hi
  rw [R.card_parent_sdiff_exception] at hj
  have hbalanced := initial.balanced i j
  simp only [Nat.dist] at hbalanced ⊢
  omega

/-- A parent exceptional set is no larger than the average exceptional count
plus one.  The statement is over `ℝ`, which is the useful form for the later
density estimate. -/
theorem parentExceptional_card_le_average_add_one (i : Fin s) :
    ((R.parentExceptional i).card : ℝ) ≤
      (R.regularityType.partition.exceptional.card : ℝ) / (s : ℝ) + 1 := by
  have hs : 0 < s := Nat.zero_lt_of_lt i.isLt
  have hsReal : 0 < (s : ℝ) := by exact_mod_cast hs
  have hpoint : ∀ j : Fin s,
      (R.parentExceptional i).card ≤ (R.parentExceptional j).card + 1 := by
    intro j
    have h := R.parentExceptional_card_dist_le_one i j
    simp only [Nat.dist] at h
    omega
  have hsum :
      ∑ j : Fin s, ((R.parentExceptional i).card : ℝ) ≤
        ∑ j : Fin s, (((R.parentExceptional j).card : ℝ) + 1) := by
    apply Finset.sum_le_sum
    intro j _
    exact_mod_cast hpoint j
  have hsum' :
      (s : ℝ) * (R.parentExceptional i).card ≤
        (R.regularityType.partition.exceptional.card : ℝ) + s := by
    rw [Finset.sum_add_distrib] at hsum
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul] at hsum
    rw [← Nat.cast_sum, R.sum_card_parentExceptional] at hsum
    norm_num at hsum ⊢
    exact hsum
  calc
    ((R.parentExceptional i).card : ℝ) ≤
        ((R.regularityType.partition.exceptional.card : ℝ) + s) / s :=
      (le_div_iff₀ hsReal).2 (by simpa [mul_comm] using hsum')
    _ = (R.regularityType.partition.exceptional.card : ℝ) / s + 1 := by
      field_simp

/-- Allocation pieces are globally equitable, even when their source parent
exceptional sets are distinct. -/
theorem allocatedExceptional_card_dist_le_one
    (i j : Fin s) (a b : Fin R.childCount) :
    Nat.dist (R.allocatedExceptional i a).card
      (R.allocatedExceptional j b).card ≤ 1 := by
  exact balancedAllocation_card_dist_le_one_of_card_dist_le_one _ _
    R.childCount_pos (R.parentExceptional_card_dist_le_one i j) a b

/-- The canonical Type children below one parent partition the
nonexceptional part of that parent. -/
theorem parent_sdiff_exception_eq_biUnion_canonicalChildren (i : Fin s) :
    initial.parts i \ R.regularityType.partition.exceptional =
      Finset.univ.biUnion fun a : Fin R.childCount =>
        R.canonicalType.partition.clusters (finProdFinEquiv (i, a)) := by
  rw [R.parent_sdiff_exception_eq_biUnion]
  ext x
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨j, hj, hxj⟩
    obtain ⟨a, ha⟩ := (R.childEquiv i).surjective ⟨j, hj⟩
    refine ⟨a, ?_⟩
    rw [R.canonicalType_cluster_finProdFinEquiv]
    simpa only [congrArg Subtype.val ha] using hxj
  · rintro ⟨a, hxa⟩
    refine ⟨(R.childEquiv i a).1, (R.childEquiv i a).2, ?_⟩
    simpa using hxa

theorem cleanChildAt_subset_initial (i : Fin s) (a : Fin R.childCount) :
    R.cleanChildAt i a ⊆ initial.parts i := by
  rw [cleanChildAt]
  exact Finset.union_subset
    (R.canonicalType_cluster_subset_initial i a)
    (R.allocatedExceptional_subset_initial i a)

theorem canonicalCluster_subset_cleanChildAt (i : Fin s)
    (a : Fin R.childCount) :
    R.canonicalType.partition.clusters (finProdFinEquiv (i, a)) ⊆
      R.cleanChildAt i a := by
  exact Finset.subset_union_left

theorem cleanChildAt_sdiff_cluster_subset_exceptional (i : Fin s)
    (a : Fin R.childCount) :
    R.cleanChildAt i a \
        R.canonicalType.partition.clusters (finProdFinEquiv (i, a)) ⊆
      R.canonicalType.partition.exceptional := by
  intro x hx
  have halloc : x ∈ R.allocatedExceptional i a := by
    rcases Finset.mem_sdiff.mp hx with ⟨hxclean, hxcluster⟩
    exact (Finset.mem_union.mp hxclean).resolve_left hxcluster
  exact R.allocatedExceptional_subset_exceptional i a halloc

/-- The clean children below a parent partition that parent exactly. -/
@[simp]
theorem biUnion_cleanChildAt (i : Fin s) :
    Finset.univ.biUnion (R.cleanChildAt i) = initial.parts i := by
  apply Finset.Subset.antisymm
  · intro x hx
    obtain ⟨a, -, hxa⟩ := Finset.mem_biUnion.mp hx
    exact R.cleanChildAt_subset_initial i a hxa
  · intro x hxi
    by_cases hxE : x ∈ R.regularityType.partition.exceptional
    · have hxParentE : x ∈ R.parentExceptional i :=
        Finset.mem_inter.mpr ⟨hxi, hxE⟩
      have hxUnion : x ∈ Finset.univ.biUnion (R.allocatedExceptional i) := by
        rw [R.biUnion_allocatedExceptional]
        exact hxParentE
      obtain ⟨a, -, hxa⟩ := Finset.mem_biUnion.mp hxUnion
      exact Finset.mem_biUnion.mpr ⟨a, Finset.mem_univ _,
        Finset.mem_union_right _ hxa⟩
    · have hxSdiff :
          x ∈ initial.parts i \ R.regularityType.partition.exceptional :=
        Finset.mem_sdiff.mpr ⟨hxi, hxE⟩
      have hxUnion : x ∈ Finset.univ.biUnion fun a : Fin R.childCount =>
          R.canonicalType.partition.clusters (finProdFinEquiv (i, a)) := by
        rw [← R.parent_sdiff_exception_eq_biUnion_canonicalChildren]
        exact hxSdiff
      obtain ⟨a, -, hxa⟩ := Finset.mem_biUnion.mp hxUnion
      exact Finset.mem_biUnion.mpr ⟨a, Finset.mem_univ _,
        Finset.mem_union_left _ hxa⟩

/-- Every canonical Type cluster produced by a Type Lemma result is
nonempty.  This follows from the positive initial parent containing it and
the strict exceptional bound `eta < 1/2`. -/
theorem canonicalCluster_nonempty (i : Fin s) (a : Fin R.childCount) :
    (R.canonicalType.partition.clusters
      (finProdFinEquiv (i, a))).Nonempty := by
  by_contra hnonempty
  have hempty : R.canonicalType.partition.clusters
      (finProdFinEquiv (i, a)) = ∅ :=
    Finset.not_nonempty_iff_eq_empty.mp hnonempty
  have hallEmpty : ∀ j, R.canonicalType.partition.clusters j = ∅ := by
    intro j
    apply Finset.card_eq_zero.mp
    rw [R.canonicalType.partition.equal_card j (finProdFinEquiv (i, a)),
      hempty]
    simp
  have hExceptional : R.canonicalType.partition.exceptional =
      (Finset.univ : Finset V) := by
    have hcover := R.canonicalType.partition.cover
    apply Finset.Subset.antisymm (Finset.subset_univ _)
    intro x _
    have hxCover : x ∈ R.canonicalType.partition.exceptional ∪
        Finset.univ.biUnion R.canonicalType.partition.clusters := by
      rw [hcover]
      exact Finset.mem_univ x
    rcases Finset.mem_union.mp hxCover with hxE | hxCluster
    · exact hxE
    · obtain ⟨j, -, hxj⟩ := Finset.mem_biUnion.mp hxCluster
      rw [hallEmpty j] at hxj
      simp at hxj
  have hpartPos : 0 < (initial.parts i).card :=
    Finset.card_pos.mpr (initial.parts_nonempty i)
  have hhostPos : 0 < Fintype.card V := by
    have hle : (initial.parts i).card ≤ Fintype.card V := by
      simpa only [Finset.card_univ] using
        Finset.card_le_card (initial.parts_subset_univ i)
    omega
  have hhostPosReal : 0 < (Fintype.card V : ℝ) := by
    exact_mod_cast hhostPos
  have hExceptionalBound := R.canonicalType.partition.exceptional_card_le
  rw [hExceptional, Finset.card_univ] at hExceptionalBound
  nlinarith [hExceptionalBound, hhostPosReal,
    R.canonicalType.epsilon_lt_half]

theorem cleanChildAt_nonempty (i : Fin s) (a : Fin R.childCount) :
    (R.cleanChildAt i a).Nonempty :=
  (R.canonicalCluster_nonempty i a).mono
    (R.canonicalCluster_subset_cleanChildAt i a)

/-- A Type cluster is disjoint from every allocated exceptional piece. -/
theorem canonicalCluster_disjoint_allocatedExceptional
    (i j : Fin s) (a : Fin R.childCount) (b : Fin R.childCount) :
    Disjoint
      (R.canonicalType.partition.clusters (finProdFinEquiv (i, a)))
      (R.allocatedExceptional j b) := by
  rw [Finset.disjoint_left]
  intro x hxCluster hxAllocated
  have hxExceptional : x ∈ R.canonicalType.partition.exceptional :=
    R.allocatedExceptional_subset_exceptional j b hxAllocated
  exact Finset.disjoint_left.mp
    (R.canonicalType.partition.exceptional_disjoint
      (finProdFinEquiv (i, a))) hxExceptional hxCluster

/-- Distinct children below one parent are disjoint. -/
theorem cleanChildAt_disjoint (i : Fin s) {a b : Fin R.childCount}
    (hab : a ≠ b) : Disjoint (R.cleanChildAt i a) (R.cleanChildAt i b) := by
  rw [Finset.disjoint_left]
  intro x hxa hxb
  rcases Finset.mem_union.mp hxa with hxca | hxaa
  · rcases Finset.mem_union.mp hxb with hxcb | hxab
    · have hindex : finProdFinEquiv (i, a) ≠ finProdFinEquiv (i, b) := by
        intro h
        exact hab (congrArg Prod.snd (finProdFinEquiv.injective h))
      exact Finset.disjoint_left.mp
        (R.canonicalType.partition.clusters_disjoint hindex) hxca hxcb
    · exact Finset.disjoint_left.mp
        (R.canonicalCluster_disjoint_allocatedExceptional i i a b)
        hxca hxab
  · rcases Finset.mem_union.mp hxb with hxcb | hxab
    · exact Finset.disjoint_left.mp
        (R.canonicalCluster_disjoint_allocatedExceptional i i b a)
        hxcb hxaa
    · exact Finset.disjoint_left.mp
        (balancedAllocation_pairwiseDisjoint (R.parentExceptional i)
          R.childCount (Set.mem_univ a) (Set.mem_univ b) hab) hxaa hxab

/-- The canonically indexed clean children are pairwise disjoint globally. -/
theorem cleanChild_pairwiseDisjoint :
    Set.PairwiseDisjoint (Set.univ : Set (Fin (s * R.childCount)))
      R.cleanChild := by
  intro x _ y _ hxy
  obtain ⟨⟨i, a⟩, rfl⟩ := finProdFinEquiv.surjective x
  obtain ⟨⟨j, b⟩, rfl⟩ := finProdFinEquiv.surjective y
  change Disjoint (R.cleanChild (finProdFinEquiv (i, a)))
    (R.cleanChild (finProdFinEquiv (j, b)))
  rw [R.cleanChild_finProdFinEquiv, R.cleanChild_finProdFinEquiv]
  by_cases hij : i = j
  · subst j
    apply R.cleanChildAt_disjoint i
    intro hab
    subst b
    exact hxy rfl
  · apply Finset.disjoint_left.mpr
    intro z hzi hzj
    exact Finset.disjoint_left.mp (initial.parts_disjoint hij)
      (R.cleanChildAt_subset_initial i a hzi)
      (R.cleanChildAt_subset_initial j b hzj)

/-- The clean children cover the whole host. -/
@[simp]
theorem biUnion_cleanChild :
    Finset.univ.biUnion R.cleanChild = (Finset.univ : Finset V) := by
  apply Finset.Subset.antisymm (Finset.subset_univ _)
  intro x _
  obtain ⟨i, hxi⟩ := initial.exists_mem_part x
  have hxUnion : x ∈ Finset.univ.biUnion (R.cleanChildAt i) := by
    rw [R.biUnion_cleanChildAt]
    exact hxi
  obtain ⟨a, -, hxa⟩ := Finset.mem_biUnion.mp hxUnion
  exact Finset.mem_biUnion.mpr
    ⟨finProdFinEquiv (i, a), Finset.mem_univ _, by simpa using hxa⟩

/-- Exact cardinality of a clean child. -/
theorem card_cleanChildAt (i : Fin s) (a : Fin R.childCount) :
    (R.cleanChildAt i a).card =
      R.canonicalType.partition.clusterSize +
        (R.allocatedExceptional i a).card := by
  rw [cleanChildAt, Finset.card_union_of_disjoint
    (R.canonicalCluster_disjoint_allocatedExceptional i i a a)]
  congr 1
  simpa [TypeLemmaResult.canonicalType] using
    R.regularityType.partition.cluster_card_eq (R.childEquiv i a)

/-- All clean children have cardinalities differing by at most one. -/
theorem cleanChildAt_card_dist_le_one
    (i j : Fin s) (a b : Fin R.childCount) :
    Nat.dist (R.cleanChildAt i a).card (R.cleanChildAt j b).card ≤ 1 := by
  rw [R.card_cleanChildAt, R.card_cleanChildAt,
    Nat.dist_add_add_left]
  exact R.allocatedExceptional_card_dist_le_one i j a b

theorem cleanChild_card_dist_le_one
    (x y : Fin (s * R.childCount)) :
    Nat.dist (R.cleanChild x).card (R.cleanChild y).card ≤ 1 := by
  obtain ⟨⟨i, a⟩, rfl⟩ := finProdFinEquiv.surjective x
  obtain ⟨⟨j, b⟩, rfl⟩ := finProdFinEquiv.surjective y
  simpa using R.cleanChildAt_card_dist_le_one i j a b

theorem cleanChild_nonempty (x : Fin (s * R.childCount)) :
    (R.cleanChild x).Nonempty := by
  obtain ⟨⟨i, a⟩, rfl⟩ := finProdFinEquiv.surjective x
  simpa using R.cleanChildAt_nonempty i a

/-- The equitable whole-host partition obtained by parent-local exceptional
redistribution. -/
noncomputable def cleanEquitablePartition :
    EquitableInitialPartition V (s * R.childCount) :=
  EquitableInitialPartition.ofParts R.cleanChild R.cleanChild_nonempty
    R.cleanChild_pairwiseDisjoint R.biUnion_cleanChild
    R.cleanChild_card_dist_le_one

@[simp]
theorem cleanEquitablePartition_parts (x : Fin (s * R.childCount)) :
    R.cleanEquitablePartition.parts x = R.cleanChild x := by
  rfl

/-- The bundled clean partition of the canonical Type. -/
noncomputable def cleanTypePartition : CleanTypePartition R.canonicalType where
  partition := R.cleanEquitablePartition
  cluster_subset := by
    intro x
    obtain ⟨⟨i, a⟩, rfl⟩ := finProdFinEquiv.surjective x
    simpa using R.canonicalCluster_subset_cleanChildAt i a
  added_subset_exceptional := by
    intro x
    obtain ⟨⟨i, a⟩, rfl⟩ := finProdFinEquiv.surjective x
    simpa using R.cleanChildAt_sdiff_cluster_subset_exceptional i a

@[simp]
theorem cleanTypePartition_parts (x : Fin (s * R.childCount)) :
    R.cleanTypePartition.partition.parts x = R.cleanChild x := by
  rfl

/-- Every prescribed initial parent is exactly the union of its consecutive
clean children. -/
theorem initialPart_eq_biUnion_cleanPartition (i : Fin s) :
    initial.parts i = Finset.univ.biUnion fun a : Fin R.childCount =>
      R.cleanTypePartition.partition.parts (finProdFinEquiv (i, a)) := by
  rw [← R.biUnion_cleanChildAt]
  apply Finset.biUnion_congr rfl
  intro a _
  rw [R.cleanTypePartition_parts, R.cleanChild_finProdFinEquiv]

end TypeLemmaResult

/-! ## A local density perturbation estimate -/

/-- Enlarging both sides of a density pair by at most a `theta` proportion
changes the density by at most `2 * theta`.  Mathlib's theorem applies without
any disjointness assumption and therefore also covers diagonal blocks. -/
theorem abs_graphDensity_sub_graphDensity_le_two_mul
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {A A' B B' : Finset V} {theta : ℝ}
    (hA : A ⊆ A') (hB : B ⊆ B') (htheta : 0 ≤ theta)
    (hAcard : (1 - theta) * (A'.card : ℝ) ≤ A.card)
    (hBcard : (1 - theta) * (B'.card : ℝ) ≤ B.card) :
    |graphDensity G A B - graphDensity G A' B'| ≤ 2 * theta := by
  change |((Rel.edgeDensity G.Adj A B : ℚ) : ℝ) -
    ((Rel.edgeDensity G.Adj A' B' : ℚ) : ℝ)| ≤ 2 * theta
  exact Rel.abs_edgeDensity_sub_edgeDensity_le_two_mul (𝕜 := ℝ)
    G.Adj hA hB htheta hAcard hBcard

/-! ## Type graphons under cluster reindexing -/

/-- Reindexing a Type by a permutation reindexes both coordinates of its
density matrix by the same permutation. -/
@[simp] theorem typeDensityMatrix_reindexClusters_perm
    (T : RegularityType G epsilon delta ell)
    (e : Equiv.Perm (Fin T.partition.clusterCount)) :
    typeDensityMatrix (T.reindexClusters e) =
      permuteMatrix e (typeDensityMatrix T) := by
  rfl

/-- Reindexing a Type by a permutation is exactly the corresponding
measure-preserving equal-cell relabeling of its Type graphon. -/
theorem typeGraphon_reindexClusters_perm_eq_relabel
    (T : RegularityType G epsilon delta ell)
    (e : Equiv.Perm (Fin T.partition.clusterCount)) :
    typeGraphon (T.reindexClusters e) =
      (typeGraphon T).relabel (cellPermRelabeling e) := by
  unfold typeGraphon
  change matrixGraphon (permuteMatrix e (typeDensityMatrix T)) _ _ _ = _
  exact matrixGraphon_permuteMatrix_eq_relabel e (typeDensityMatrix T)
    (typeDensityMatrix_isSymm T) (typeDensityMatrix_nonneg T)
    (typeDensityMatrix_le_one T)

/-! ## Density matrices of equitable partitions -/

/-- The density matrix of an indexed equitable partition of the whole host. -/
def cleanDensityMatrix {q : ℕ} (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : EquitableInitialPartition V q) : Matrix (Fin q) (Fin q) ℝ :=
  fun i j => graphDensity G (P.parts i) (P.parts j)

theorem cleanDensityMatrix_isSymm {q : ℕ} (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : EquitableInitialPartition V q) :
    (cleanDensityMatrix G P).IsSymm := by
  apply Matrix.IsSymm.ext
  intro i j
  exact graphDensity_comm G _ _

theorem cleanDensityMatrix_nonneg {q : ℕ} (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : EquitableInitialPartition V q) (i j : Fin q) :
    0 ≤ cleanDensityMatrix G P i j :=
  graphDensity_nonneg G _ _

theorem cleanDensityMatrix_le_one {q : ℕ} (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : EquitableInitialPartition V q) (i j : Fin q) :
    cleanDensityMatrix G P i j ≤ 1 :=
  graphDensity_le_one G _ _

/-- The equal-cell graphon associated with an equitable partition. -/
def cleanPartitionGraphon {q : ℕ} (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : EquitableInitialPartition V q) : Graphon :=
  matrixGraphon (cleanDensityMatrix G P) (cleanDensityMatrix_isSymm G P)
    (cleanDensityMatrix_nonneg G P) (cleanDensityMatrix_le_one G P)

/-- On the diagonal, the clean density matrix uses ordered adjacent pairs,
so every undirected internal edge contributes twice. -/
theorem cleanDensityMatrix_diag_eq_orderedEdgeCount {q : ℕ}
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : EquitableInitialPartition V q) (i : Fin q) :
    cleanDensityMatrix G P i i =
      ((G.interedges (P.parts i) (P.parts i)).card : ℝ) /
        ((P.parts i).card : ℝ) ^ 2 := by
  rw [cleanDensityMatrix, graphDensity_eq]
  ring_nf

/-- Cell formula for the graphon of an equitable partition. -/
theorem cleanPartitionGraphon_ae_eq_on_cell {q : ℕ}
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : EquitableInitialPartition V q)
    (i j : Fin q) :
    ∀ᵐ z ∂unitSquareMeasure, z ∈ equalCell i ×ˢ equalCell j →
      cleanPartitionGraphon G P z = graphDensity G (P.parts i) (P.parts j) := by
  simpa [cleanPartitionGraphon, cleanDensityMatrix] using
    matrixGraphon_ae_eq_on_cell (cleanDensityMatrix G P)
      (cleanDensityMatrix_isSymm G P) (cleanDensityMatrix_nonneg G P)
      (cleanDensityMatrix_le_one G P) i j

/-! ## Type-versus-clean estimates -/

namespace CleanTypePartition

variable {T : RegularityType G epsilon delta ell}

/-- Entrywise density control from a uniform retained-proportion bound. -/
theorem abs_cleanDensityMatrix_sub_typeDensityMatrix_le
    (P : CleanTypePartition T) {theta : ℝ} (htheta : 0 ≤ theta)
    (hcard : ∀ i,
      (1 - theta) * ((P.partition.parts i).card : ℝ) ≤
        (T.partition.clusters i).card)
    (i j : Fin T.partition.clusterCount) :
    |cleanDensityMatrix G P.partition i j - typeDensityMatrix T i j| ≤
      2 * theta := by
  rw [abs_sub_comm]
  exact abs_graphDensity_sub_graphDensity_le_two_mul G
    (P.cluster_subset i) (P.cluster_subset j) htheta (hcard i) (hcard j)

/-- The corresponding explicit `L¹` estimate for the two equal-cell
graphons. -/
theorem graphonL1Dist_cleanPartitionGraphon_typeGraphon_le
    (P : CleanTypePartition T) {theta : ℝ} (htheta : 0 ≤ theta)
    (hcard : ∀ i,
      (1 - theta) * ((P.partition.parts i).card : ℝ) ≤
        (T.partition.clusters i).card) :
    graphonL1Dist (cleanPartitionGraphon G P.partition) (typeGraphon T) ≤
      2 * theta := by
  simpa [cleanPartitionGraphon, typeGraphon] using
    graphonL1Dist_matrixGraphon_le
      (cleanDensityMatrix G P.partition) (typeDensityMatrix T)
      (cleanDensityMatrix_isSymm G P.partition) (typeDensityMatrix_isSymm T)
      (cleanDensityMatrix_nonneg G P.partition)
      (cleanDensityMatrix_le_one G P.partition)
      (typeDensityMatrix_nonneg T) (typeDensityMatrix_le_one T)
      (mul_nonneg (by norm_num) htheta)
      (P.abs_cleanDensityMatrix_sub_typeDensityMatrix_le htheta hcard)

end CleanTypePartition

/-! ### Explicit estimates for the canonical cleaning -/

namespace TypeLemmaResult

variable {eta delta' : ℝ} {ell' s L U : ℕ}
  {initial : EquitableInitialPartition V s}
  (R : TypeLemmaResult G eta delta' ell' initial L U)

/-- A uniform upper bound for the proportion added to each canonical Type
cluster.  The second term is the finite-size rounding loss for the
`s * childCount` clean classes. -/
def cleaningProportion : ℝ :=
  2 * eta +
    2 * ((s * R.childCount : ℕ) : ℝ) / (Fintype.card V : ℝ)

theorem cleaningProportion_nonneg : 0 ≤ R.cleaningProportion := by
  have heta : 0 ≤ eta := R.canonicalType.epsilon_pos.le
  unfold cleaningProportion
  positivity

/-- Every canonical Type cluster retains at least a
`1 - cleaningProportion` fraction of its clean class. -/
theorem cleanTypePartition_retained_proportion
    (x : Fin (s * R.childCount)) :
    (1 - R.cleaningProportion) *
        ((R.cleanTypePartition.partition.parts x).card : ℝ) ≤
      (R.canonicalType.partition.clusters x).card := by
  let qn : ℕ := s * R.childCount
  have hqn : 0 < qn := by
    exact Nat.zero_lt_of_lt x.isLt
  have hq : 0 < (qn : ℝ) := by
    exact_mod_cast hqn
  have hqn_le : qn ≤ Fintype.card V := by
    simpa only [qn, R.canonicalType_clusterCount] using
      R.cleanTypePartition.partition.partCount_le_card
  have hnNat : 0 < Fintype.card V := hqn.trans_le hqn_le
  have hn : 0 < (Fintype.card V : ℝ) := by
    exact_mod_cast hnNat
  have hpartNat :=
    R.cleanTypePartition.partition.card_part_le_average_add_one x
  have hpart :
      ((R.cleanTypePartition.partition.parts x).card : ℝ) ≤
        (Fintype.card V : ℝ) / (qn : ℝ) + 1 := by
    calc
      ((R.cleanTypePartition.partition.parts x).card : ℝ) ≤
          (((Fintype.card V / qn : ℕ) : ℝ) + 1) := by
        exact_mod_cast hpartNat
      _ ≤ (Fintype.card V : ℝ) / (qn : ℝ) + 1 := by
        gcongr
        exact Nat.cast_div_le
  have hqpart :
      (qn : ℝ) *
          ((R.cleanTypePartition.partition.parts x).card : ℝ) ≤
        (Fintype.card V : ℝ) + qn := by
    calc
      (qn : ℝ) *
          ((R.cleanTypePartition.partition.parts x).card : ℝ) ≤
          (qn : ℝ) * ((Fintype.card V : ℝ) / qn + 1) :=
        mul_le_mul_of_nonneg_left hpart hq.le
      _ = (Fintype.card V : ℝ) + qn := by
        field_simp
  have hdecompNat :=
    R.cleanTypePartition.card_part_eq_cluster_add_added x
  have hclusterCard :
      (R.canonicalType.partition.clusters x).card =
        R.canonicalType.partition.clusterSize :=
    R.canonicalType.partition.cluster_card_eq x
  rw [hclusterCard] at hdecompNat
  have hdecomp :
      ((R.cleanTypePartition.partition.parts x).card : ℝ) =
        (R.canonicalType.partition.clusterSize : ℝ) +
          ((R.cleanTypePartition.addedVertices x).card : ℝ) := by
    exact_mod_cast hdecompNat
  have htotalNat :=
    R.canonicalType.partition.exceptional_card_add_mul_clusterSize
  simp only [R.canonicalType_clusterCount] at htotalNat
  have htotal :
      (R.canonicalType.partition.exceptional.card : ℝ) +
          (qn : ℝ) * R.canonicalType.partition.clusterSize =
        (Fintype.card V : ℝ) := by
    exact_mod_cast htotalNat
  have hexception := R.canonicalType.partition.exceptional_card_le
  have hetaHost :
      eta * (Fintype.card V : ℝ) <
        (1 / 2 : ℝ) * (Fintype.card V : ℝ) :=
    mul_lt_mul_of_pos_right R.canonicalType.epsilon_lt_half hn
  have hclusterLower :
      (Fintype.card V : ℝ) / 2 ≤
        (qn : ℝ) * R.canonicalType.partition.clusterSize := by
    nlinarith
  have hqAdded :
      (qn : ℝ) *
          ((R.cleanTypePartition.addedVertices x).card : ℝ) ≤
        eta * (Fintype.card V : ℝ) + qn := by
    have hqDecomp :
        (qn : ℝ) *
            ((R.cleanTypePartition.partition.parts x).card : ℝ) =
          (qn : ℝ) * R.canonicalType.partition.clusterSize +
            (qn : ℝ) *
              ((R.cleanTypePartition.addedVertices x).card : ℝ) := by
      rw [hdecomp]
      ring
    nlinarith
  have hscale :
      R.cleaningProportion * ((Fintype.card V : ℝ) / 2) =
        eta * (Fintype.card V : ℝ) + qn := by
    unfold cleaningProportion
    simp only [qn]
    field_simp
  have haddedCluster :
      ((R.cleanTypePartition.addedVertices x).card : ℝ) ≤
        R.cleaningProportion *
          (R.canonicalType.partition.clusterSize : ℝ) := by
    apply (mul_le_mul_iff_of_pos_left hq).mp
    calc
      (qn : ℝ) *
          ((R.cleanTypePartition.addedVertices x).card : ℝ) ≤
          eta * (Fintype.card V : ℝ) + qn := hqAdded
      _ = R.cleaningProportion * ((Fintype.card V : ℝ) / 2) :=
        hscale.symm
      _ ≤ R.cleaningProportion *
          ((qn : ℝ) * R.canonicalType.partition.clusterSize) :=
        mul_le_mul_of_nonneg_left hclusterLower
          R.cleaningProportion_nonneg
      _ = (qn : ℝ) *
          (R.cleaningProportion *
            (R.canonicalType.partition.clusterSize : ℝ)) := by ring
  have hthetaAdded : 0 ≤
      R.cleaningProportion *
        ((R.cleanTypePartition.addedVertices x).card : ℝ) :=
    mul_nonneg R.cleaningProportion_nonneg (by positivity)
  calc
    (1 - R.cleaningProportion) *
        ((R.cleanTypePartition.partition.parts x).card : ℝ) ≤
        (R.canonicalType.partition.clusterSize : ℝ) := by
      nlinarith
    _ = ((R.canonicalType.partition.clusters x).card : ℝ) := by
      exact_mod_cast hclusterCard.symm

/-- Entrywise Type-versus-clean density error with all finite-size losses
made explicit. -/
theorem abs_cleanDensityMatrix_sub_typeDensityMatrix_le_explicit
    (i j : Fin (s * R.childCount)) :
    |cleanDensityMatrix G R.cleanTypePartition.partition i j -
        typeDensityMatrix R.canonicalType i j| ≤
      4 * eta +
        4 * ((s * R.childCount : ℕ) : ℝ) /
          (Fintype.card V : ℝ) := by
  have h := R.cleanTypePartition.abs_cleanDensityMatrix_sub_typeDensityMatrix_le
    R.cleaningProportion_nonneg R.cleanTypePartition_retained_proportion i j
  convert h using 1 <;> unfold cleaningProportion <;> ring

/-- Direct equal-cell `L¹` error between the canonical Type graphon and the
graphon of its clean whole-host partition. -/
theorem graphonL1Dist_cleanPartitionGraphon_canonicalType_le :
    graphonL1Dist
        (cleanPartitionGraphon G R.cleanTypePartition.partition)
        (typeGraphon R.canonicalType) ≤
      4 * eta +
        4 * ((s * R.childCount : ℕ) : ℝ) /
          (Fintype.card V : ℝ) := by
  have h :=
    R.cleanTypePartition.graphonL1Dist_cleanPartitionGraphon_typeGraphon_le
      R.cleaningProportion_nonneg R.cleanTypePartition_retained_proportion
  convert h using 1 <;> unfold cleaningProportion <;> ring

end TypeLemmaResult

/-! ## Uniform refinements and block averaging -/

/-- An exact consecutive uniform refinement of one equitable whole-host
partition by another.  The quotient `K / s` is the number of children below
each coarse class, and `Graphon.refinementIndex` is used in the data so the
structure feeds directly into `matrixBlockAverage`. -/
structure UniformEquitableRefinement {s K : ℕ} (h : s ∣ K)
    (coarse : EquitableInitialPartition V s)
    (fine : EquitableInitialPartition V K) where
  coarseCount_pos : 0 < s
  factor_pos : 0 < K / s
  child_subset : ∀ i a,
    fine.parts (Graphon.refinementIndex h i a) ⊆ coarse.parts i
  parent_eq_biUnion : ∀ i,
    coarse.parts i = Finset.univ.biUnion fun a : Fin (K / s) =>
      fine.parts (Graphon.refinementIndex h i a)

namespace UniformEquitableRefinement

variable {s K : ℕ} {h : s ∣ K}
  {coarse : EquitableInitialPartition V s}
  {fine : EquitableInitialPartition V K}

/-- Ordered adjacent-pair counts split exactly over the fine rectangles.
This is valid also when the two coarse indices coincide. -/
theorem card_interedges_eq_sum_children
    (Q : UniformEquitableRefinement h coarse fine)
    (G : SimpleGraph V) [DecidableRel G.Adj] (i j : Fin s) :
    (G.interedges (coarse.parts i) (coarse.parts j)).card =
      ∑ a : Fin (K / s), ∑ b : Fin (K / s),
        (G.interedges
          (fine.parts (Graphon.refinementIndex h i a))
          (fine.parts (Graphon.refinementIndex h j b))).card := by
  classical
  rw [Q.parent_eq_biUnion i, Q.parent_eq_biUnion j,
    G.interedges_biUnion_left, Finset.card_biUnion]
  · apply Finset.sum_congr rfl
    intro a _
    rw [G.interedges_biUnion_right, Finset.card_biUnion]
    intro b _ b' _ hbb'
    exact G.interedges_disjoint_right _ <|
      fine.parts_disjoint fun heq =>
        hbb' (refinementIndex_injective h j heq)
  · intro a _ a' _ haa'
    exact G.interedges_disjoint_left
      (fine.parts_disjoint fun heq =>
        haa' (refinementIndex_injective h i heq)) _

/-- Exact unnormalized size-weighted density identity.  Multiplication by
the parent cardinalities avoids divisions and is often the most convenient
form for finite algebra. -/
theorem weightedDensityIdentity_mul
    (Q : UniformEquitableRefinement h coarse fine)
    (G : SimpleGraph V) [DecidableRel G.Adj] (i j : Fin s) :
    ((coarse.parts i).card : ℝ) * ((coarse.parts j).card : ℝ) *
        graphDensity G (coarse.parts i) (coarse.parts j) =
      ∑ a : Fin (K / s), ∑ b : Fin (K / s),
        ((fine.parts (Graphon.refinementIndex h i a)).card : ℝ) *
          ((fine.parts (Graphon.refinementIndex h j b)).card : ℝ) *
          graphDensity G
            (fine.parts (Graphon.refinementIndex h i a))
            (fine.parts (Graphon.refinementIndex h j b)) := by
  classical
  have hparent :
      ((coarse.parts i).card : ℝ) * ((coarse.parts j).card : ℝ) *
          graphDensity G (coarse.parts i) (coarse.parts j) =
        ((G.interedges (coarse.parts i) (coarse.parts j)).card : ℝ) := by
    rw [graphDensity_eq]
    have hi : ((coarse.parts i).card : ℝ) ≠ 0 := by
      exact_mod_cast (coarse.parts_nonempty i).card_pos.ne'
    have hj : ((coarse.parts j).card : ℝ) ≠ 0 := by
      exact_mod_cast (coarse.parts_nonempty j).card_pos.ne'
    field_simp
  have hchild (a b : Fin (K / s)) :
      ((fine.parts (Graphon.refinementIndex h i a)).card : ℝ) *
            ((fine.parts (Graphon.refinementIndex h j b)).card : ℝ) *
            graphDensity G
              (fine.parts (Graphon.refinementIndex h i a))
              (fine.parts (Graphon.refinementIndex h j b)) =
        ((G.interedges
          (fine.parts (Graphon.refinementIndex h i a))
          (fine.parts (Graphon.refinementIndex h j b))).card : ℝ) := by
    rw [graphDensity_eq]
    have ha :
        ((fine.parts (Graphon.refinementIndex h i a)).card : ℝ) ≠ 0 := by
      exact_mod_cast
        (fine.parts_nonempty (Graphon.refinementIndex h i a)).card_pos.ne'
    have hb :
        ((fine.parts (Graphon.refinementIndex h j b)).card : ℝ) ≠ 0 := by
      exact_mod_cast
        (fine.parts_nonempty (Graphon.refinementIndex h j b)).card_pos.ne'
    field_simp
  rw [hparent]
  simp_rw [hchild]
  exact_mod_cast Q.card_interedges_eq_sum_children G i j

/-- Exact normalized size-weighted density identity.  In particular, this
uses ordered adjacent pairs on diagonal blocks, exactly as `graphDensity`
does. -/
theorem weightedDensityIdentity
    (Q : UniformEquitableRefinement h coarse fine)
    (G : SimpleGraph V) [DecidableRel G.Adj] (i j : Fin s) :
    graphDensity G (coarse.parts i) (coarse.parts j) =
      ∑ a : Fin (K / s), ∑ b : Fin (K / s),
        (((fine.parts (Graphon.refinementIndex h i a)).card : ℝ) *
            ((fine.parts (Graphon.refinementIndex h j b)).card : ℝ) /
          (((coarse.parts i).card : ℝ) *
            ((coarse.parts j).card : ℝ))) *
          graphDensity G
            (fine.parts (Graphon.refinementIndex h i a))
            (fine.parts (Graphon.refinementIndex h j b)) := by
  classical
  have hi : ((coarse.parts i).card : ℝ) ≠ 0 := by
    exact_mod_cast (coarse.parts_nonempty i).card_pos.ne'
  have hj : ((coarse.parts j).card : ℝ) ≠ 0 := by
    exact_mod_cast (coarse.parts_nonempty j).card_pos.ne'
  calc
    graphDensity G (coarse.parts i) (coarse.parts j) =
        (((coarse.parts i).card : ℝ) *
            ((coarse.parts j).card : ℝ) *
          graphDensity G (coarse.parts i) (coarse.parts j)) /
          (((coarse.parts i).card : ℝ) *
            ((coarse.parts j).card : ℝ)) := by
      field_simp
    _ = (∑ a : Fin (K / s), ∑ b : Fin (K / s),
        ((fine.parts (Graphon.refinementIndex h i a)).card : ℝ) *
          ((fine.parts (Graphon.refinementIndex h j b)).card : ℝ) *
          graphDensity G
            (fine.parts (Graphon.refinementIndex h i a))
            (fine.parts (Graphon.refinementIndex h j b))) /
          (((coarse.parts i).card : ℝ) *
            ((coarse.parts j).card : ℝ)) := by
      rw [Q.weightedDensityIdentity_mul G i j]
    _ = _ := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro b _
      ring

theorem sum_card_children
    (Q : UniformEquitableRefinement h coarse fine) (i : Fin s) :
    ∑ a : Fin (K / s),
        (fine.parts (Graphon.refinementIndex h i a)).card =
      (coarse.parts i).card := by
  rw [Q.parent_eq_biUnion i, Finset.card_biUnion]
  intro a _ a' _ haa'
  exact fine.parts_disjoint fun heq =>
    haa' (refinementIndex_injective h i heq)

/-- A child cardinality differs from the within-parent arithmetic mean by
at most one child.  This is the key finite equity estimate. -/
theorem abs_factor_mul_childCard_sub_parentCard_le
    (Q : UniformEquitableRefinement h coarse fine)
    (i : Fin s) (a : Fin (K / s)) :
    |((K / s : ℕ) : ℝ) *
        ((fine.parts (Graphon.refinementIndex h i a)).card : ℝ) -
      ((coarse.parts i).card : ℝ)| ≤ (K / s : ℕ) := by
  classical
  have hsumNat := Q.sum_card_children i
  have hsum :
      ∑ b : Fin (K / s),
          ((fine.parts (Graphon.refinementIndex h i b)).card : ℝ) =
        ((coarse.parts i).card : ℝ) := by
    exact_mod_cast hsumNat
  have hdiff (b : Fin (K / s)) :
      |((fine.parts (Graphon.refinementIndex h i a)).card : ℝ) -
        ((fine.parts (Graphon.refinementIndex h i b)).card : ℝ)| ≤ 1 := by
    have hd := fine.balanced
      (Graphon.refinementIndex h i a) (Graphon.refinementIndex h i b)
    have hab :
        (fine.parts (Graphon.refinementIndex h i a)).card ≤
          (fine.parts (Graphon.refinementIndex h i b)).card + 1 := by
      simp only [Nat.dist] at hd
      omega
    have hba :
        (fine.parts (Graphon.refinementIndex h i b)).card ≤
          (fine.parts (Graphon.refinementIndex h i a)).card + 1 := by
      simp only [Nat.dist] at hd
      omega
    have hab' :
        ((fine.parts (Graphon.refinementIndex h i a)).card : ℝ) ≤
          (fine.parts (Graphon.refinementIndex h i b)).card + 1 := by
      exact_mod_cast hab
    have hba' :
        ((fine.parts (Graphon.refinementIndex h i b)).card : ℝ) ≤
          (fine.parts (Graphon.refinementIndex h i a)).card + 1 := by
      exact_mod_cast hba
    rw [abs_le]
    constructor <;> nlinarith
  have hrearrange :
      ((K / s : ℕ) : ℝ) *
          ((fine.parts (Graphon.refinementIndex h i a)).card : ℝ) -
        ((coarse.parts i).card : ℝ) =
      ∑ b : Fin (K / s),
        (((fine.parts (Graphon.refinementIndex h i a)).card : ℝ) -
          ((fine.parts (Graphon.refinementIndex h i b)).card : ℝ)) := by
    rw [Finset.sum_sub_distrib, hsum]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
  rw [hrearrange]
  calc
    |∑ b : Fin (K / s),
        (((fine.parts (Graphon.refinementIndex h i a)).card : ℝ) -
          ((fine.parts (Graphon.refinementIndex h i b)).card : ℝ))| ≤
        ∑ b : Fin (K / s),
          |((fine.parts (Graphon.refinementIndex h i a)).card : ℝ) -
            ((fine.parts (Graphon.refinementIndex h i b)).card : ℝ)| :=
      Finset.abs_sum_le_sum_abs _ Finset.univ
    _ ≤ ∑ _b : Fin (K / s), (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro b _
      exact hdiff b
    _ = (K / s : ℕ) := by simp

/-- Every coarse class has reciprocal cardinality at most twice the coarse
cell count divided by the host order. -/
theorem one_div_parentCard_le
    (Q : UniformEquitableRefinement h coarse fine) (i : Fin s) :
    1 / ((coarse.parts i).card : ℝ) ≤
      2 * (s : ℝ) / (Fintype.card V : ℝ) := by
  have hs := Q.coarseCount_pos
  have hpartPos := (coarse.parts_nonempty i).card_pos
  have hnPos : 0 < Fintype.card V := by
    exact lt_of_lt_of_le hs coarse.partCount_le_card
  have havg := coarse.average_le_card_part i
  have hNlt :
      Fintype.card V < ((coarse.parts i).card + 1) * s :=
    (Nat.div_lt_iff_lt_mul hs).mp (Nat.lt_succ_of_le havg)
  have hplus : (coarse.parts i).card + 1 ≤
      2 * (coarse.parts i).card := by
    omega
  have hnat :
      Fintype.card V ≤ 2 * s * (coarse.parts i).card := by
    calc
      Fintype.card V ≤ ((coarse.parts i).card + 1) * s := hNlt.le
      _ ≤ (2 * (coarse.parts i).card) * s :=
        Nat.mul_le_mul_right s hplus
      _ = 2 * s * (coarse.parts i).card := by
        ac_rfl
  have hreal :
      (Fintype.card V : ℝ) ≤
        2 * (s : ℝ) * ((coarse.parts i).card : ℝ) := by
    exact_mod_cast hnat
  rw [div_le_div_iff₀ (by exact_mod_cast hpartPos)
    (by exact_mod_cast hnPos)]
  nlinarith

/-- The normalized size of a child differs from the uniform weight by an
explicit host-order error. -/
theorem abs_childFraction_sub_uniform_le
    (Q : UniformEquitableRefinement h coarse fine)
    (i : Fin s) (a : Fin (K / s)) :
    |((fine.parts (Graphon.refinementIndex h i a)).card : ℝ) /
          ((coarse.parts i).card : ℝ) -
        1 / ((K / s : ℕ) : ℝ)| ≤
      2 * (s : ℝ) / (Fintype.card V : ℝ) := by
  have hr : 0 < ((K / s : ℕ) : ℝ) := by
    exact_mod_cast Q.factor_pos
  have hp : 0 < ((coarse.parts i).card : ℝ) := by
    exact_mod_cast (coarse.parts_nonempty i).card_pos
  have hrearrange :
      ((fine.parts (Graphon.refinementIndex h i a)).card : ℝ) /
            ((coarse.parts i).card : ℝ) -
          1 / ((K / s : ℕ) : ℝ) =
        (((K / s : ℕ) : ℝ) *
            ((fine.parts (Graphon.refinementIndex h i a)).card : ℝ) -
          ((coarse.parts i).card : ℝ)) /
          (((K / s : ℕ) : ℝ) *
            ((coarse.parts i).card : ℝ)) := by
    field_simp
  rw [hrearrange, abs_div, abs_of_pos (mul_pos hr hp)]
  calc
    |((K / s : ℕ) : ℝ) *
          ((fine.parts (Graphon.refinementIndex h i a)).card : ℝ) -
        ((coarse.parts i).card : ℝ)| /
          (((K / s : ℕ) : ℝ) *
            ((coarse.parts i).card : ℝ)) ≤
        ((K / s : ℕ) : ℝ) /
          (((K / s : ℕ) : ℝ) *
            ((coarse.parts i).card : ℝ)) := by
      exact div_le_div_of_nonneg_right
        (Q.abs_factor_mul_childCard_sub_parentCard_le i a)
        (mul_nonneg hr.le hp.le)
    _ = 1 / ((coarse.parts i).card : ℝ) := by field_simp
    _ ≤ 2 * (s : ℝ) / (Fintype.card V : ℝ) :=
      Q.one_div_parentCard_le i

/-- The unweighted consecutive block average differs from the exact coarse
density by an explicit rounding error.  The deliberately coarse quadratic
factor in the fixed child count is harmless in the tower application and
makes the estimate robust on diagonal blocks as well. -/
theorem abs_cleanDensityMatrix_sub_matrixBlockAverage_le
    (Q : UniformEquitableRefinement h coarse fine)
    (G : SimpleGraph V) [DecidableRel G.Adj] (i j : Fin s) :
    |cleanDensityMatrix G coarse i j -
        Graphon.matrixBlockAverage h (cleanDensityMatrix G fine) i j| ≤
      4 * (s : ℝ) * ((K / s : ℕ) : ℝ) ^ 2 /
        (Fintype.card V : ℝ) := by
  classical
  let r : ℝ := ((K / s : ℕ) : ℝ)
  let child (u : Fin s) (a : Fin (K / s)) : Finset V :=
    fine.parts (Graphon.refinementIndex h u a)
  let p (u : Fin s) (a : Fin (K / s)) : ℝ :=
    ((child u a).card : ℝ) / ((coarse.parts u).card : ℝ)
  let d (a b : Fin (K / s)) : ℝ := graphDensity G (child i a) (child j b)
  let e : ℝ := 2 * (s : ℝ) / (Fintype.card V : ℝ)
  have hr : 0 < r := by
    dsimp only [r]
    exact_mod_cast Q.factor_pos
  have hn : 0 < (Fintype.card V : ℝ) := by
    have hsCard : s ≤ Fintype.card V := coarse.partCount_le_card
    exact_mod_cast Q.coarseCount_pos.trans_le hsCard
  have he : 0 ≤ e := by
    dsimp only [e]
    positivity
  have hp_nonneg (u : Fin s) (a : Fin (K / s)) : 0 ≤ p u a := by
    dsimp only [p]
    positivity
  have hp_le_one (u : Fin s) (a : Fin (K / s)) : p u a ≤ 1 := by
    have hparent : 0 < ((coarse.parts u).card : ℝ) := by
      exact_mod_cast (coarse.parts_nonempty u).card_pos
    apply (div_le_iff₀ hparent).2
    simp only [one_mul, p, child]
    exact_mod_cast Finset.card_le_card (Q.child_subset u a)
  have hu_nonneg : 0 ≤ 1 / r := by positivity
  have hu_le_one : 1 / r ≤ 1 := by
    rw [div_le_one hr]
    change (1 : ℝ) ≤ ((K / s : ℕ) : ℝ)
    exact_mod_cast (Nat.succ_le_iff.mpr Q.factor_pos)
  have hp_error (u : Fin s) (a : Fin (K / s)) :
      |p u a - 1 / r| ≤ e := by
    simpa only [p, child, r, e] using
      Q.abs_childFraction_sub_uniform_le u a
  have hweight (a b : Fin (K / s)) :
      |p i a * p j b - (1 / r) ^ 2| ≤ 2 * e := by
    have hrearrange :
        p i a * p j b - (1 / r) ^ 2 =
          (p i a - 1 / r) * p j b +
            (1 / r) * (p j b - 1 / r) := by ring
    rw [hrearrange]
    calc
      |(p i a - 1 / r) * p j b +
          (1 / r) * (p j b - 1 / r)| ≤
          |(p i a - 1 / r) * p j b| +
            |(1 / r) * (p j b - 1 / r)| := abs_add_le _ _
      _ = |p i a - 1 / r| * p j b +
          (1 / r) * |p j b - 1 / r| := by
        rw [abs_mul, abs_mul, abs_of_nonneg (hp_nonneg j b),
          abs_of_nonneg hu_nonneg]
      _ ≤ e * 1 + 1 * e := by
        apply add_le_add
        · exact mul_le_mul (hp_error i a) (hp_le_one j b)
            (hp_nonneg j b) he
        · exact mul_le_mul hu_le_one (hp_error j b)
            (abs_nonneg _) (by norm_num)
      _ = 2 * e := by ring
  have hunweighted :
      (∑ a : Fin (K / s), ∑ b : Fin (K / s), d a b) / r ^ 2 =
        ∑ a : Fin (K / s), ∑ b : Fin (K / s),
          (1 / r) ^ 2 * d a b := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro b _
    ring
  have hweightedForm :
      (∑ a : Fin (K / s), ∑ b : Fin (K / s),
        (((fine.parts (Graphon.refinementIndex h i a)).card : ℝ) *
            ((fine.parts (Graphon.refinementIndex h j b)).card : ℝ) /
          (((coarse.parts i).card : ℝ) *
            ((coarse.parts j).card : ℝ))) *
          graphDensity G
            (fine.parts (Graphon.refinementIndex h i a))
            (fine.parts (Graphon.refinementIndex h j b))) =
        ∑ a : Fin (K / s), ∑ b : Fin (K / s),
          p i a * p j b * d a b := by
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    dsimp only [p, child, d]
    ring
  have hfineForm :
      (∑ a : Fin (K / s), ∑ b : Fin (K / s),
        cleanDensityMatrix G fine
          (Graphon.refinementIndex h i a)
          (Graphon.refinementIndex h j b)) =
        ∑ a : Fin (K / s), ∑ b : Fin (K / s), d a b := by
    rfl
  have hrearrange :
      cleanDensityMatrix G coarse i j -
          Graphon.matrixBlockAverage h (cleanDensityMatrix G fine) i j =
        ∑ a : Fin (K / s), ∑ b : Fin (K / s),
          (p i a * p j b - (1 / r) ^ 2) * d a b := by
    change graphDensity G (coarse.parts i) (coarse.parts j) -
        Graphon.matrixBlockAverage h (cleanDensityMatrix G fine) i j = _
    rw [Q.weightedDensityIdentity G i j]
    unfold Graphon.matrixBlockAverage
    rw [hweightedForm, hfineForm]
    change (∑ a : Fin (K / s), ∑ b : Fin (K / s),
          p i a * p j b * d a b) -
        (∑ a : Fin (K / s), ∑ b : Fin (K / s), d a b) / r ^ 2 = _
    rw [hunweighted, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro a _
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro b _
    ring
  rw [hrearrange]
  calc
    |∑ a : Fin (K / s), ∑ b : Fin (K / s),
        (p i a * p j b - (1 / r) ^ 2) * d a b| ≤
        ∑ a : Fin (K / s),
          |∑ b : Fin (K / s),
            (p i a * p j b - (1 / r) ^ 2) * d a b| :=
      Finset.abs_sum_le_sum_abs _ Finset.univ
    _ ≤ ∑ a : Fin (K / s), ∑ b : Fin (K / s),
        |(p i a * p j b - (1 / r) ^ 2) * d a b| := by
      apply Finset.sum_le_sum
      intro a _
      exact Finset.abs_sum_le_sum_abs _ Finset.univ
    _ ≤ ∑ _a : Fin (K / s), ∑ _b : Fin (K / s), 2 * e := by
      apply Finset.sum_le_sum
      intro a _
      apply Finset.sum_le_sum
      intro b _
      rw [abs_mul, abs_of_nonneg (graphDensity_nonneg G _ _)]
      calc
        |p i a * p j b - (1 / r) ^ 2| * d a b ≤
            (2 * e) * 1 := by
          exact mul_le_mul (hweight a b) (graphDensity_le_one G _ _)
            (graphDensity_nonneg G _ _) (mul_nonneg (by norm_num) he)
        _ = 2 * e := by ring
    _ = 4 * (s : ℝ) * ((K / s : ℕ) : ℝ) ^ 2 /
        (Fintype.card V : ℝ) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, e]
      ring

end UniformEquitableRefinement

namespace TypeLemmaResult

variable {eta delta' : ℝ} {ell' s L U : ℕ}
  {initial : EquitableInitialPartition V s}
  (R : TypeLemmaResult G eta delta' ell' initial L U)

private theorem cleanRefinement_quotient (hs : 0 < s) :
    s * R.childCount / s = R.childCount := by
  simpa [Nat.mul_comm] using Nat.mul_div_left R.childCount hs

private theorem cleanRefinement_index (hs : 0 < s) (i : Fin s)
    (a : Fin ((s * R.childCount) / s)) :
    Graphon.refinementIndex (dvd_mul_right s R.childCount) i a =
      finProdFinEquiv
        (i, finCongr (R.cleanRefinement_quotient hs) a) := by
  apply Fin.ext
  simp [Graphon.refinementIndex, finProdFinEquiv,
    R.cleanRefinement_quotient hs, Nat.add_comm, Nat.mul_comm]

/-- The clean partition constructed from a Type Lemma result is an exact
consecutive uniform refinement of the prescribed initial partition. -/
noncomputable def cleanUniformEquitableRefinement (hs : 0 < s) :
    UniformEquitableRefinement (dvd_mul_right s R.childCount)
      initial R.cleanEquitablePartition where
  coarseCount_pos := hs
  factor_pos := by
    rw [R.cleanRefinement_quotient hs]
    exact R.childCount_pos
  child_subset := by
    intro i a
    rw [R.cleanRefinement_index hs]
    simp only [R.cleanEquitablePartition_parts,
      R.cleanChild_finProdFinEquiv]
    exact R.cleanChildAt_subset_initial i _
  parent_eq_biUnion := by
    intro i
    rw [R.initialPart_eq_biUnion_cleanPartition i]
    ext x
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨a, hxa⟩
      let a' : Fin ((s * R.childCount) / s) :=
        (finCongr (R.cleanRefinement_quotient hs)).symm a
      refine ⟨a', ?_⟩
      rw [R.cleanRefinement_index hs]
      simpa only [a', Equiv.apply_symm_apply]
    · rintro ⟨a, hxa⟩
      refine ⟨finCongr (R.cleanRefinement_quotient hs) a, ?_⟩
      rw [R.cleanRefinement_index hs] at hxa
      exact hxa

end TypeLemmaResult

end Regularity

end InducedStars
