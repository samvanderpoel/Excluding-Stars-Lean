import InducedStars.Regularity.Basic
import Mathlib.Order.Partition.Equipartition
import Mathlib.Tactic.Linarith

/-!
# Trimming a uniform equipartition

Mathlib's regularity lemma produces an equipartition: its classes can differ
in size by one.  The paper's `RegularPartition`, on the other hand, asks for
exactly equal nonexceptional classes and permits an exceptional class.  This
file gives the elementary adapter between those two conventions.

Every part is trimmed to the floor average.  Thus at most one vertex per part
is moved to the exceptional class.  A trimmed part is at least half of its
parent when the floor average is positive, so the project's slicing lemma
transfers uniformity of the original pair to regularity of the trimmed pair.
-/

open Finset
open scoped SimpleGraph

namespace InducedStars.Regularity

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- The data retained by the equipartition-trimming construction.

Besides the resulting ambient regular partition, this records an enumeration
of the original parts and the chosen equal-sized subpart inside each of them.
The equality `cluster_eq_lift` is the precise correspondence between a
subtype-level child and its ambient cluster. -/
structure EquipartitionTrimResult (G : SimpleGraph V) [DecidableRel G.Adj]
    (retained : Finset V)
    (Q : Finpartition (Finset.univ : Finset {x // x ∈ retained}))
    (η : ℝ) where
  partition : RegularPartition G η
  clusterCount_eq : partition.clusterCount = Q.parts.card
  partsEquiv : Fin partition.clusterCount ≃ Q.parts
  subparts : Fin partition.clusterCount → Finset {x // x ∈ retained}
  subparts_subset : ∀ i, subparts i ⊆ (partsEquiv i).1
  subparts_card_eq_average : ∀ i,
    (subparts i).card = retained.card / Q.parts.card
  cluster_eq_lift : ∀ i,
    partition.clusters i = liftFinset retained (subparts i)
  exceptional_eq_compl :
    partition.exceptional = Finset.univ \ Finset.univ.biUnion partition.clusters

/-- Trim a Mathlib uniform equipartition of an induced retained set to an
exactly equal ambient regular partition.

The exceptional-budget hypothesis pays for all ambient vertices outside
`retained` and, conservatively, one discarded vertex from each part.  The
condition `ε₀ ≤ η / 4` pays both for slicing the original regular pairs and
for converting Mathlib's ordered nonuniform-pair count to the project's
unordered irregular-pair bound. -/
noncomputable def equipartitionTrim
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (retained : Finset V)
    (Q : Finpartition (Finset.univ : Finset {x // x ∈ retained}))
    {ε₀ η : ℝ}
    (hEquip : Q.IsEquipartition)
    (hUniform : Q.IsUniform (G.induce (↑retained : Set V)) ε₀)
    (hη : 0 < η)
    (hε₀η : ε₀ ≤ η / 4)
    (hparts : 0 < Q.parts.card)
    (haverage : 0 < retained.card / Q.parts.card)
    (hbudget :
      ((((Fintype.card V - retained.card) + Q.parts.card : ℕ) : ℝ)) ≤
        η * (Fintype.card V : ℝ)) :
    EquipartitionTrimResult G retained Q η := by
  classical
  let k : ℕ := Q.parts.card
  let m : ℕ := retained.card / k
  let e : Fin k ≃ Q.parts := hEquip.exists_partsEquiv.choose.symm
  have hk : 0 < k := by
    simpa only [k] using hparts
  have hm : 0 < m := by
    simpa only [m, k] using haverage
  have havg_le (i : Fin k) : m ≤ (e i).1.card := by
    simpa only [m, k, Finset.card_univ, Fintype.card_coe] using
      hEquip.average_le_card_part (e i).2
  let child : Fin k → Finset {x // x ∈ retained} := fun i =>
    (Finset.exists_subset_card_eq (havg_le i)).choose
  have hchild_subset (i : Fin k) : child i ⊆ (e i).1 := by
    simpa only [child] using
      (Finset.exists_subset_card_eq (havg_le i)).choose_spec.1
  have hchild_card (i : Fin k) : (child i).card = m := by
    simpa only [child] using
      (Finset.exists_subset_card_eq (havg_le i)).choose_spec.2
  let clusters : Fin k → Finset V := fun i => liftFinset retained (child i)
  have hcluster_card (i : Fin k) : (clusters i).card = m := by
    simp only [clusters, card_liftFinset, hchild_card]
  have hchildren_disjoint :
      Set.PairwiseDisjoint (Set.univ : Set (Fin k)) child := by
    intro i _ j _ hij
    have heij : e i ≠ e j := e.injective.ne hij
    have hparts_ne : (e i).1 ≠ (e j).1 := by
      intro h
      exact heij (Subtype.ext h)
    exact (Q.disjoint (e i).2 (e j).2 hparts_ne).mono
      (hchild_subset i) (hchild_subset j)
  have hclusters_disjoint :
      Set.PairwiseDisjoint (Set.univ : Set (Fin k)) clusters := by
    intro i _ j _ hij
    change Disjoint
      ((child i).map (parentEmbedding retained))
      ((child j).map (parentEmbedding retained))
    rw [Finset.disjoint_map]
    exact hchildren_disjoint (Set.mem_univ i) (Set.mem_univ j) hij
  let covered : Finset V := Finset.univ.biUnion clusters
  let exceptional : Finset V := Finset.univ \ covered
  have hcovered_card : covered.card = k * m := by
    dsimp only [covered]
    rw [Finset.card_biUnion (by simpa using hclusters_disjoint)]
    simp only [hcluster_card, sum_const_nat, card_univ, Fintype.card_fin]
  have hretained_le : retained.card ≤ Fintype.card V := retained.card_le_univ
  have hretained_loss : retained.card ≤ k * m + k := by
    calc
      retained.card = m * k + retained.card % k := by
        simpa only [m] using (Nat.div_add_mod' retained.card k).symm
      _ ≤ m * k + k := Nat.add_le_add_left (Nat.le_of_lt (Nat.mod_lt _ hk)) _
      _ = k * m + k := by ac_rfl
  have hexceptional_card_nat :
      exceptional.card ≤ (Fintype.card V - retained.card) + k := by
    have hcard : exceptional.card = Fintype.card V - covered.card := by
      dsimp only [exceptional]
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ covered), Finset.card_univ]
    rw [hcard, hcovered_card]
    omega
  have hhalf (i : Fin k) :
      (1 / 2 : ℝ) * ((e i).1.card : ℝ) ≤ (child i).card := by
    have hupper : (e i).1.card ≤ m + 1 := by
      simpa only [m, k, Finset.card_univ, Fintype.card_coe] using
        hEquip.card_part_le_average_add_one (e i).2
    have hupper_real : ((e i).1.card : ℝ) ≤ (m : ℝ) + 1 := by
      exact_mod_cast hupper
    have hm_real : (1 : ℝ) ≤ m := by
      exact_mod_cast hm
    rw [hchild_card]
    norm_num
    linarith
  have hirregular_card :
      (irregularPairs G η clusters).card ≤
        (Q.nonUniforms (G.induce (↑retained : Set V)) ε₀).card := by
    let pairMap : Fin k × Fin k →
        Finset {x // x ∈ retained} × Finset {x // x ∈ retained} :=
      fun ij => ((e ij.1).1, (e ij.2).1)
    apply Finset.card_le_card_of_injOn pairMap
    · rintro ⟨i, j⟩ hij
      change (i, j) ∈ irregularPairs G η clusters at hij
      change pairMap (i, j) ∈
        Q.nonUniforms (G.induce (↑retained : Set V)) ε₀
      rw [irregularPairs, Finset.mem_filter] at hij
      rw [Finpartition.mk_mem_nonUniforms]
      have hijlt : i < j := hij.2.1
      have hparts_ne : (e i).1 ≠ (e j).1 := by
        intro h
        have heq : e i = e j := Subtype.ext h
        exact (ne_of_lt hijlt) (e.injective heq)
      refine ⟨(e i).2, (e j).2, hparts_ne, ?_⟩
      intro hu
      apply hij.2.2
      have hparent :
          IsRegularPair (G.induce (↑retained : Set V)) ε₀ (e i).1 (e j).1 :=
        IsRegularPair.of_isUniform _ hu
      have hslice :
          IsRegularPair (G.induce (↑retained : Set V)) η (child i) (child j) := by
        refine IsRegularPair.slice _ hparent
          (hchild_subset i) (hchild_subset j) (hhalf i) (hhalf j)
          (by norm_num) hη.le ?_ ?_
        · linarith
        · linarith
      exact (isRegularPair_induce_lift_iff G retained η (child i) (child j)).mp hslice
    · rintro ⟨i, j⟩ _ ⟨i', j'⟩ _ hpairs
      change ((e i).1, (e j).1) = ((e i').1, (e j').1) at hpairs
      have hi_part : (e i).1 = (e i').1 := congrArg Prod.fst hpairs
      have hj_part : (e j).1 = (e j').1 := congrArg Prod.snd hpairs
      have hi : i = i' := e.injective (Subtype.ext hi_part)
      have hj : j = j' := e.injective (Subtype.ext hj_part)
      subst i'
      subst j'
      rfl
  have hnonuniform_bound :
      ((Q.nonUniforms (G.induce (↑retained : Set V)) ε₀).card : ℝ) ≤
        (((k * (k - 1) : ℕ) : ℝ)) * ε₀ := by
    simpa only [Finpartition.IsUniform, k] using hUniform
  have hordered_eq_twice_choose :
      (((k * (k - 1) : ℕ) : ℝ)) = 2 * (Nat.choose k 2 : ℝ) := by
    rw [Nat.cast_choose_two]
    simp only [Nat.cast_mul, Nat.cast_sub hk, Nat.cast_one]
    ring
  have hirregular_bound :
      ((irregularPairs G η clusters).card : ℝ) ≤
        η * (Nat.choose k 2 : ℝ) := by
    calc
      ((irregularPairs G η clusters).card : ℝ) ≤
          (Q.nonUniforms (G.induce (↑retained : Set V)) ε₀).card := by
        exact_mod_cast hirregular_card
      _ ≤ (((k * (k - 1) : ℕ) : ℝ)) * ε₀ := hnonuniform_bound
      _ = (2 * ε₀) * (Nat.choose k 2 : ℝ) := by
        rw [hordered_eq_twice_choose]
        ring
      _ ≤ η * (Nat.choose k 2 : ℝ) :=
        mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg _)
  let P : RegularPartition G η :=
    { clusterCount := k
      exceptional := exceptional
      clusters := clusters
      clusters_pairwiseDisjoint := hclusters_disjoint
      exceptional_disjoint := by
        intro i
        rw [Finset.disjoint_left]
        intro x hxExceptional hxCluster
        have hxCovered : x ∈ covered := by
          exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hxCluster⟩
        exact (Finset.mem_sdiff.mp hxExceptional).2 hxCovered
      cover := by
        change exceptional ∪ covered = Finset.univ
        ext x
        simp [exceptional]
      equal_card := by
        intro i j
        rw [hcluster_card, hcluster_card]
      exceptional_card_le := by
        calc
          (exceptional.card : ℝ) ≤
              (((Fintype.card V - retained.card) + k : ℕ) : ℝ) := by
            exact_mod_cast hexceptional_card_nat
          _ ≤ η * (Fintype.card V : ℝ) := by
            simpa only [k] using hbudget
      irregular_pair_card_le := hirregular_bound }
  refine
    { partition := P
      clusterCount_eq := by rfl
      partsEquiv := e
      subparts := child
      subparts_subset := hchild_subset
      subparts_card_eq_average := by
        intro i
        simpa only [m, k] using hchild_card i
      cluster_eq_lift := by
        intro i
        rfl
      exceptional_eq_compl := by
        rfl }

end InducedStars.Regularity
