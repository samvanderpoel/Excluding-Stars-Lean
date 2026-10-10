import InducedStars.Regularity.InitialPartition
import InducedStars.Regularity.FinpartitionRefinement
import InducedStars.Regularity.PrescribedCore
import InducedStars.Regularity.EquipartitionTrim

/-!
# Regular partitions uniformly refining a prescribed partition

This module combines the equal-core construction, the seeded Mathlib energy
iteration, and equipartition trimming.  The result is the purely finite
regularity statement used by the paper's Type Lemma; it does not mention
density colors or induced embeddings.
-/

open Finset Fintype Function
open scoped SimpleGraph

namespace InducedStars.Regularity

universe u

/-- Internal tolerance reserved for the Mathlib energy iteration. -/
noncomputable def refinementTolerance (η : ℝ) : ℝ :=
  min (η / 4) (1 / 2)

theorem refinementTolerance_pos {η : ℝ} (hη : 0 < η) :
    0 < refinementTolerance η := by
  rw [refinementTolerance, lt_min_iff]
  constructor <;> positivity

theorem refinementTolerance_le_one (η : ℝ) : refinementTolerance η ≤ 1 := by
  calc
    refinementTolerance η ≤ 1 / 2 := min_le_right _ _
    _ ≤ 1 := by norm_num

theorem refinementTolerance_le_quarter (η : ℝ) :
    refinementTolerance η ≤ η / 4 :=
  min_le_left _ _

/-- Number of children used below every prescribed parent before starting
the energy iteration. -/
noncomputable def refinementSeedCount (η : ℝ) (L : ℕ) : ℕ :=
  SzemerediRegularity.initialBound (refinementTolerance η) L

theorem refinementSeedCount_pos (η : ℝ) (L : ℕ) :
    0 < refinementSeedCount η L :=
  SzemerediRegularity.initialBound_pos _ _

theorem seven_le_refinementSeedCount (η : ℝ) (L : ℕ) :
    7 ≤ refinementSeedCount η L :=
  SzemerediRegularity.seven_le_initialBound _ _

theorem le_refinementSeedCount (η : ℝ) (L : ℕ) :
    L ≤ refinementSeedCount η L :=
  SzemerediRegularity.le_initialBound _ _

theorem hundred_lt_pow_refinementSeedCount_mul {η : ℝ} (hη : 0 < η) (L : ℕ) :
    100 < (4 : ℝ) ^ refinementSeedCount η L * refinementTolerance η ^ 5 :=
  SzemerediRegularity.hundred_lt_pow_initialBound_mul
    (refinementTolerance_pos hη) L

/-- Uniform upper bound for the number of nonexceptional classes. -/
noncomputable def refinementPartBound (η : ℝ) (L t : ℕ) : ℕ :=
  uniformRefinementBound (refinementTolerance η)
    (t * refinementSeedCount η L)

theorem refinementPartBound_pos (η : ℝ) (L : ℕ) {t : ℕ} (ht : 0 < t) :
    0 < refinementPartBound η L t :=
  uniformRefinementBound_pos _ <|
    Nat.mul_pos ht (refinementSeedCount_pos η L)

/-- A sufficient vertex threshold.  The three summands respectively pay for
the prescribed-core loss, the requested final cluster size, and the real
exceptional-set budget. -/
noncomputable def refinementVertexThreshold (η : ℝ) (L t M : ℕ) : ℕ :=
  let q := refinementSeedCount η L
  let U := refinementPartBound η L t
  t * q + (M + 1) * U +
    ⌈(((t * q + U : ℕ) : ℝ) / η)⌉₊

/-- The complete witness that an exact-equal regular partition uniformly
refines an indexed equitable initial partition after deleting its exceptional
vertices. -/
structure UniformRefiningRegularPartitionResult
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (η : ℝ) {s : ℕ} (initial : EquitableInitialPartition V s)
    (L U M : ℕ) where
  partition : RegularPartition G η
  childCount : ℕ
  childCount_pos : 0 < childCount
  lower_clusterCount : L ≤ partition.clusterCount
  upper_clusterCount : partition.clusterCount ≤ U
  min_clusterSize : M ≤ partition.clusterSize
  clusterCount_eq : partition.clusterCount = s * childCount
  parentBlocks : Fin s → Finset (Fin partition.clusterCount)
  parentBlocks_pairwiseDisjoint :
    Set.PairwiseDisjoint (Set.univ : Set (Fin s)) parentBlocks
  parentBlocks_cover :
    Finset.univ.biUnion parentBlocks =
      (Finset.univ : Finset (Fin partition.clusterCount))
  parentBlock_card : ∀ i, (parentBlocks i).card = childCount
  cluster_subset_parent :
    ∀ i j, j ∈ parentBlocks i → partition.clusters j ⊆ initial.parts i
  parent_sdiff_exception_eq_biUnion :
    ∀ i, initial.parts i \ partition.exceptional =
      (parentBlocks i).biUnion partition.clusters

section UniformRefinementBlocks

variable {W : Type u} [Fintype W] [DecidableEq W]
  {s k r : ℕ} (P : EquitableInitialPartition W s)
  {Q : Finpartition (Finset.univ : Finset W)}

/-- The final indices whose corresponding `Q`-part lies below parent `i`. -/
def uniformRefinementBlocks (e : Fin k ≃ Q.parts) (i : Fin s) : Finset (Fin k) :=
  Finset.univ.filter fun j ↦ (e j).1 ⊆ P.parts i

@[simp]
theorem mem_uniformRefinementBlocks (e : Fin k ≃ Q.parts) (i : Fin s) (j : Fin k) :
    j ∈ uniformRefinementBlocks P e i ↔ (e j).1 ⊆ P.parts i := by
  simp [uniformRefinementBlocks]

theorem card_uniformRefinementBlocks (e : Fin k ≃ Q.parts)
    (hQ : Q.UniformRefines P.partition r) (i : Fin s) :
    (uniformRefinementBlocks P e i).card = r := by
  let target := {A ∈ Q.parts | A ⊆ P.parts i}
  calc
    (uniformRefinementBlocks P e i).card = target.card := by
      apply Finset.card_bij (fun j _ ↦ (e j).1)
      · intro j hj
        exact Finset.mem_filter.mpr
          ⟨(e j).2, (mem_uniformRefinementBlocks P e i j).mp hj⟩
      · intro j₁ _ j₂ _ hj
        exact e.injective (Subtype.ext hj)
      · intro A hA
        obtain ⟨hAQ, hAi⟩ := Finset.mem_filter.mp hA
        let a : Q.parts := ⟨A, hAQ⟩
        refine ⟨e.symm a, ?_, ?_⟩
        · exact (mem_uniformRefinementBlocks P e i _).mpr <| by
            simpa only [Equiv.apply_symm_apply] using hAi
        · simp only [a, Equiv.apply_symm_apply]
    _ = r := hQ.card_parts_subset (P.parts i) (P.parts_mem_partition i)

theorem uniformRefinementBlocks_pairwiseDisjoint (e : Fin k ≃ Q.parts) :
    Set.PairwiseDisjoint (Set.univ : Set (Fin s))
      (uniformRefinementBlocks P e) := by
  intro i _ j _ hij
  rw [Function.onFun, Finset.disjoint_left]
  intro a hai haj
  have hai' := (mem_uniformRefinementBlocks P e i a).mp hai
  have haj' := (mem_uniformRefinementBlocks P e j a).mp haj
  obtain ⟨x, hx⟩ := Q.nonempty_of_mem_parts (e a).2
  exact hij <| P.parts_injective <|
    P.partition.eq_of_mem_parts (P.parts_mem_partition i)
      (P.parts_mem_partition j) (hai' hx) (haj' hx)

@[simp]
theorem uniformRefinementBlocks_cover (e : Fin k ≃ Q.parts)
    (hQ : Q.UniformRefines P.partition r) :
    Finset.univ.biUnion (uniformRefinementBlocks P e) = Finset.univ := by
  ext j
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
  constructor
  · exact fun _ ↦ trivial
  · intro _
    obtain ⟨A, hAP, hsub⟩ := hQ.le (e j).2
    obtain ⟨i, hi⟩ := P.mem_partition_iff A |>.mp hAP
    refine ⟨i, (mem_uniformRefinementBlocks P e i j).mpr ?_⟩
    simpa only [hi] using hsub

end UniformRefinementBlocks

/-! ### The enhanced prescribed-partition regularity theorem -/

/-- A strengthened form of the prescribed-partition regularity theorem in
which the final common cluster size is required to be at least `M`.

The part-count bound `U` is selected before `M`; only the sufficiently-large
threshold is enlarged to pay for `M`. -/
theorem exists_uniformRefiningRegularPartition_with_minClusterSize
    (η : ℝ) (hη : 0 < η) (L t : ℕ) (_hL : 0 < L) (ht : 0 < t) :
    ∃ U : ℕ, ∀ M : ℕ, ∃ n₀ : ℕ,
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G : SimpleGraph V) [DecidableRel G.Adj]
        {s : ℕ} (_hs : 0 < s) (_hst : s ≤ t)
        (initial : EquitableInitialPartition V s),
        n₀ ≤ Fintype.card V →
          Nonempty (UniformRefiningRegularPartitionResult G η initial L U M) := by
  let q := refinementSeedCount η L
  let U := refinementPartBound η L t
  refine ⟨U, fun M ↦ ⟨refinementVertexThreshold η L t M, ?_⟩⟩
  intro V _ _ G _ s hs hst initial hn
  have hq : 0 < q := by simpa only [q] using refinementSeedCount_pos η L
  have hU : 0 < U := by simpa only [U] using refinementPartBound_pos η L ht
  change
    t * q + (M + 1) * U +
      ⌈(((t * q + U : ℕ) : ℝ) / η)⌉₊ ≤ Fintype.card V at hn
  have htq_le_n : t * q ≤ Fintype.card V := by omega
  have hsq_le_tq : s * q ≤ t * q := Nat.mul_le_mul_right q hst
  have hsq_le_n : s * q ≤ Fintype.card V := hsq_le_tq.trans htq_le_n
  have hq_le_average : q ≤ Fintype.card V / s := by
    rw [Nat.le_div_iff_mul_le hs]
    simpa only [Nat.mul_comm] using hsq_le_n
  have hc : 0 < PrescribedCore.coreSize initial q := by
    rw [PrescribedCore.coreSize]
    exact Nat.div_pos hq_le_average hq
  let retained := PrescribedCore.retained initial q
  have hloss : ((Finset.univ : Finset V) \ retained).card ≤ t * q := by
    exact (PrescribedCore.card_compl_retained_le initial q hs hq).trans hsq_le_tq
  have hretained_subset : retained ⊆ (Finset.univ : Finset V) :=
    PrescribedCore.retained_subset_univ initial q
  have hdecomp :
      ((Finset.univ : Finset V) \ retained).card + retained.card = Fintype.card V := by
    simpa only [Finset.card_univ] using
      Finset.card_sdiff_add_card_eq_card hretained_subset
  have hlargeRetained : (M + 1) * U ≤ retained.card := by omega
  have hUretained : U ≤ retained.card := by
    have hOne : 1 ≤ M + 1 := by omega
    have hUmul : U ≤ (M + 1) * U := by
      simpa only [one_mul] using Nat.mul_le_mul_right U hOne
    exact hUmul.trans hlargeRetained
  let ε₀ := refinementTolerance η
  let P₀ := PrescribedCore.startingPartition initial q hq hc
  have hq_le_sq : q ≤ s * q := by
    exact Nat.le_mul_of_pos_left q hs
  have hP₀seven : 7 ≤ #P₀.parts := by
    simpa only [P₀, PrescribedCore.card_startingPartition_parts] using
      (seven_le_refinementSeedCount η L).trans hq_le_sq
  have hP₀ε : 100 ≤ (4 : ℝ) ^ #P₀.parts * ε₀ ^ 5 := by
    simpa only [P₀, ε₀, PrescribedCore.card_startingPartition_parts] using
      (hundred_lt_pow_refinementSeedCount_mul hη L).le.trans
        (mul_le_mul_of_nonneg_right (pow_right_mono₀ (by simp) hq_le_sq)
          (pow_nonneg (refinementTolerance_pos hη).le 5))
  have hP₀K : #P₀.parts ≤ t * q := by
    simpa only [P₀, PrescribedCore.card_startingPartition_parts] using hsq_le_tq
  have hambient :
      uniformRefinementBound ε₀ (t * q) ≤
        Fintype.card (PrescribedCore.Vertex initial q) := by
    simpa only [ε₀, q, U, refinementPartBound, Fintype.card_coe] using hUretained
  obtain ⟨Q, r, hQequip, hr, hQstart, hQcard, hQuniform⟩ :=
    exists_uniform_equipartition_uniformRefines
      (G.induce (↑retained : Set V)) ε₀ (t * q) P₀
      (by simpa only [ε₀] using refinementTolerance_pos hη)
      (by simpa only [ε₀] using refinementTolerance_le_one η)
      (PrescribedCore.startingPartition_isEquipartition initial q hq hc)
      hP₀seven hP₀ε hP₀K hambient
  let parent := PrescribedCore.parentPartition initial q hq hc
  have hQparent : Q.UniformRefines parent.partition (r * q) :=
    hQstart.trans (PrescribedCore.startingPartition_uniformRefines initial q hq hc)
  have hQparts : 0 < Q.parts.card := by
    have hseed_le : s * q ≤ Q.parts.card := by
      rw [← PrescribedCore.card_startingPartition_parts initial q hq hc]
      exact Finpartition.card_mono hQstart.le
    exact (Nat.mul_pos hs hq).trans_le hseed_le
  have hQcardU : Q.parts.card ≤ U := by
    simpa only [ε₀, q, U, refinementPartBound] using hQcard
  have hQcardRetained : Q.parts.card ≤ retained.card := hQcardU.trans hUretained
  have haverage : 0 < retained.card / Q.parts.card :=
    Nat.div_pos hQcardRetained hQparts
  have hMaverage : M ≤ retained.card / Q.parts.card := by
    rw [Nat.le_div_iff_mul_le hQparts]
    calc
      M * Q.parts.card ≤ M * U := Nat.mul_le_mul_left M hQcardU
      _ ≤ (M + 1) * U := Nat.mul_le_mul_right U (Nat.le_succ M)
      _ ≤ retained.card := hlargeRetained
  have hceil_le_n :
      ⌈(((t * q + U : ℕ) : ℝ) / η)⌉₊ ≤ Fintype.card V := by
    omega
  have hratio_le_n :
      (((t * q + U : ℕ) : ℝ) / η) ≤ (Fintype.card V : ℝ) := by
    calc
      (((t * q + U : ℕ) : ℝ) / η) ≤
          (⌈(((t * q + U : ℕ) : ℝ) / η)⌉₊ : ℝ) := Nat.le_ceil _
      _ ≤ (Fintype.card V : ℝ) := by exact_mod_cast hceil_le_n
  have hcapBudget :
      ((t * q + U : ℕ) : ℝ) ≤ η * (Fintype.card V : ℝ) := by
    rw [mul_comm η (Fintype.card V : ℝ), ← div_le_iff₀ hη]
    exact hratio_le_n
  have hbudgetNat :
      (Fintype.card V - retained.card) + Q.parts.card ≤ t * q + U := by
    rw [← Finset.card_univ, ← Finset.card_sdiff_of_subset hretained_subset]
    exact Nat.add_le_add hloss hQcardU
  have hbudget :
      ((((Fintype.card V - retained.card) + Q.parts.card : ℕ) : ℝ)) ≤
        η * (Fintype.card V : ℝ) := by
    exact (by exact_mod_cast hbudgetNat :
      ((((Fintype.card V - retained.card) + Q.parts.card : ℕ) : ℝ)) ≤
        ((t * q + U : ℕ) : ℝ)).trans hcapBudget
  let trim := equipartitionTrim G retained Q hQequip hQuniform hη
    (by simpa only [ε₀] using refinementTolerance_le_quarter η)
    hQparts haverage hbudget
  let blocks : Fin s → Finset (Fin trim.partition.clusterCount) :=
    uniformRefinementBlocks parent trim.partsEquiv
  have hblocksCard (i : Fin s) : (blocks i).card = r * q := by
    simpa only [blocks] using
      card_uniformRefinementBlocks parent trim.partsEquiv hQparent i
  have hblocksDisjoint :
      Set.PairwiseDisjoint (Set.univ : Set (Fin s)) blocks := by
    simpa only [blocks] using
      uniformRefinementBlocks_pairwiseDisjoint parent trim.partsEquiv
  have hblocksCover :
      Finset.univ.biUnion blocks =
        (Finset.univ : Finset (Fin trim.partition.clusterCount)) := by
    simpa only [blocks] using
      uniformRefinementBlocks_cover parent trim.partsEquiv hQparent
  have hclusterCount : trim.partition.clusterCount = s * (r * q) := by
    have hcard := congrArg Finset.card hblocksCover
    have hblocksDisjoint' :
        ((Finset.univ : Finset (Fin s)) : Set (Fin s)).PairwiseDisjoint blocks := by
      simpa only [Finset.coe_univ] using hblocksDisjoint
    rw [Finset.card_biUnion hblocksDisjoint'] at hcard
    simp only [hblocksCard, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul] at hcard
    exact hcard.symm
  have hclusterSubset :
      ∀ i j, j ∈ blocks i → trim.partition.clusters j ⊆ initial.parts i := by
    intro i j hj x hx
    have hpartSubset : (trim.partsEquiv j).1 ⊆ parent.parts i := by
      exact (mem_uniformRefinementBlocks parent trim.partsEquiv i j).mp hj
    rw [trim.cluster_eq_lift, mem_liftFinset] at hx
    obtain ⟨hxretained, hxsubpart⟩ := hx
    have hxQpart := trim.subparts_subset j hxsubpart
    have hxCorePart := hpartSubset hxQpart
    simp only [parent, PrescribedCore.parentPartition_parts] at hxCorePart
    have hxCore : x ∈ PrescribedCore.core initial q i :=
      (PrescribedCore.mem_corePart initial q i ⟨x, hxretained⟩).mp hxCorePart
    exact PrescribedCore.core_subset_part initial q i hxCore
  have hparentExact :
      ∀ i, initial.parts i \ trim.partition.exceptional =
        (blocks i).biUnion trim.partition.clusters := by
    intro i
    ext x
    constructor
    · intro hx
      obtain ⟨hxInitial, hxNotExceptional⟩ := Finset.mem_sdiff.mp hx
      have hxCover : x ∈ trim.partition.exceptional ∪
          Finset.univ.biUnion trim.partition.clusters := by
        rw [trim.partition.cover]
        exact Finset.mem_univ x
      obtain hxExceptional | hxClusters := Finset.mem_union.mp hxCover
      · exact (hxNotExceptional hxExceptional).elim
      · obtain ⟨j, _, hxj⟩ := Finset.mem_biUnion.mp hxClusters
        have hjCover : j ∈ Finset.univ.biUnion blocks := by
          rw [hblocksCover]
          exact Finset.mem_univ j
        obtain ⟨i', _, hji'⟩ := Finset.mem_biUnion.mp hjCover
        have hxInitial' := hclusterSubset i' j hji' hxj
        have hii : i' = i := initial.parts_injective <|
          initial.partition.eq_of_mem_parts
            (initial.parts_mem_partition i') (initial.parts_mem_partition i)
            hxInitial' hxInitial
        subst i'
        exact Finset.mem_biUnion.mpr ⟨j, hji', hxj⟩
    · intro hx
      obtain ⟨j, hj, hxj⟩ := Finset.mem_biUnion.mp hx
      refine Finset.mem_sdiff.mpr ⟨hclusterSubset i j hj hxj, ?_⟩
      intro hxExceptional
      exact Finset.disjoint_left.mp (trim.partition.exceptional_disjoint j)
        hxExceptional hxj
  have hclusterSize : trim.partition.clusterSize = retained.card / Q.parts.card := by
    let j : Fin trim.partition.clusterCount := ⟨0, by
      rw [trim.clusterCount_eq]
      exact hQparts⟩
    calc
      trim.partition.clusterSize = (trim.partition.clusters j).card :=
        (trim.partition.cluster_card_eq j).symm
      _ = (trim.subparts j).card := by
        rw [trim.cluster_eq_lift, card_liftFinset]
      _ = retained.card / Q.parts.card := trim.subparts_card_eq_average j
  refine ⟨?_⟩
  refine
    { partition := trim.partition
      childCount := r * q
      childCount_pos := Nat.mul_pos hr hq
      lower_clusterCount := ?_
      upper_clusterCount := ?_
      min_clusterSize := hclusterSize ▸ hMaverage
      clusterCount_eq := hclusterCount
      parentBlocks := blocks
      parentBlocks_pairwiseDisjoint := hblocksDisjoint
      parentBlocks_cover := hblocksCover
      parentBlock_card := hblocksCard
      cluster_subset_parent := hclusterSubset
      parent_sdiff_exception_eq_biUnion := hparentExact }
  · calc
      L ≤ q := by simpa only [q] using le_refinementSeedCount η L
      _ ≤ s * q := hq_le_sq
      _ = #P₀.parts := by
        simp only [P₀, PrescribedCore.card_startingPartition_parts]
      _ ≤ Q.parts.card := Finpartition.card_mono hQstart.le
      _ = trim.partition.clusterCount := trim.clusterCount_eq.symm
  · rw [trim.clusterCount_eq]
    exact hQcardU

/-- Pure enhanced regularity with a prescribed equitable initial partition.

For fixed `η`, `L`, and `t`, the witnesses `U` and `n₀` are selected before
the finite vertex type, graph, actual parent count `s`, and initial
partition.  Every parent has the same positive number of children, and the
parent-minus-exception identities expose the exact refinement required by
the paper. -/
theorem exists_uniformRefiningRegularPartition
    (η : ℝ) (hη : 0 < η) (L t : ℕ) (hL : 0 < L) (ht : 0 < t) :
    ∃ U n₀ : ℕ,
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G : SimpleGraph V) [DecidableRel G.Adj]
        {s : ℕ} (_hs : 0 < s) (_hst : s ≤ t)
        (initial : EquitableInitialPartition V s),
        n₀ ≤ Fintype.card V →
          Nonempty (UniformRefiningRegularPartitionResult G η initial L U 1) := by
  obtain ⟨U, hU⟩ :=
    exists_uniformRefiningRegularPartition_with_minClusterSize η hη L t hL ht
  obtain ⟨n₀, hn₀⟩ := hU 1
  exact ⟨U, n₀, hn₀⟩

end InducedStars.Regularity
