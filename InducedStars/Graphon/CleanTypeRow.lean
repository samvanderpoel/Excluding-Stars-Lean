import InducedStars.Graphon.CleanPartition
import InducedStars.Graphon.FixedTypeRow
import InducedStars.Graphon.TypeTower
import Mathlib.Tactic

/-!
# Fixed clean rows for the type tower

This file packages one row of enhanced-Type-Lemma outputs with a single
canonical cluster index type.  Exceptional vertices are redistributed by the
canonical clean construction, and fixed-dimensional compactness is then used
to retain an entrywise limiting density matrix.  The last section isolates
the exact cross-level data needed by the tower assembly.
-/

noncomputable section

open Filter Finset Set
open scoped BigOperators Topology

namespace InducedStars

open Regularity

attribute [local instance] Classical.propDecidable

namespace EquitablePartitionRow

/-- Restrict a row of equitable partitions along a further subsequence. -/
def subsequence {s : ℕ} (P : EquitablePartitionRow s)
    (phi : ℕ → ℕ) (hphi : StrictMono phi) : EquitablePartitionRow s where
  extraction := P.extraction ∘ phi
  extraction_strictMono := P.extraction_strictMono.comp hphi
  partition n := P.partition (phi n)

@[simp] theorem subsequence_extraction {s : ℕ} (P : EquitablePartitionRow s)
    (phi : ℕ → ℕ) (hphi : StrictMono phi) (n : ℕ) :
    (P.subsequence phi hphi).extraction n = P.extraction (phi n) :=
  rfl

@[simp] theorem subsequence_partition {s : ℕ} (P : EquitablePartitionRow s)
    (phi : ℕ → ℕ) (hphi : StrictMono phi) (n : ℕ) :
    (P.subsequence phi hphi).partition n = P.partition (phi n) :=
  rfl

/-- The coordinate-preserving identification of host vertex types when one
row's extraction is a subsequence of another. -/
def subsequenceHostEquiv {s S : ℕ}
    (parent : EquitablePartitionRow s) (child : EquitablePartitionRow S)
    (phi : ℕ → ℕ) (hrow : child.extraction = parent.extraction ∘ phi)
    (n : ℕ) :
    Fin (child.extraction n + 1) ≃ Fin (parent.extraction (phi n) + 1) :=
  finCongr <| by
    have hn := congrFun hrow n
    simpa only [Function.comp_apply] using congrArg (fun k ↦ k + 1) hn

@[simp] theorem subsequenceHostEquiv_val {s S : ℕ}
    (parent : EquitablePartitionRow s) (child : EquitablePartitionRow S)
    (phi : ℕ → ℕ) (hrow : child.extraction = parent.extraction ∘ phi)
    (n : ℕ) (x : Fin (child.extraction n + 1)) :
    ((subsequenceHostEquiv parent child phi hrow n x :
      Fin (parent.extraction (phi n) + 1)) : ℕ) = x := by
  simp [subsequenceHostEquiv]

end EquitablePartitionRow

namespace Regularity.EquitableInitialPartition

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Reindex an equitable indexed partition.  The equivalence sends each new
index to the old index carrying the same part. -/
def reindexParts {q Q : ℕ} (P : EquitableInitialPartition V Q)
    (e : Fin q ≃ Fin Q) : EquitableInitialPartition V q :=
  EquitableInitialPartition.ofParts (fun i ↦ P.parts (e i))
    (fun i ↦ P.parts_nonempty (e i))
    (by
      intro i _ j _ hij
      exact P.parts_disjoint (fun h ↦ hij (e.injective h)))
    (by
      apply Finset.Subset.antisymm (Finset.subset_univ _)
      intro x _
      obtain ⟨j, hj⟩ := P.exists_mem_part x
      exact Finset.mem_biUnion.mpr
        ⟨e.symm j, Finset.mem_univ _, by simpa using hj⟩)
    (fun i j ↦ P.balanced (e i) (e j))

@[simp] theorem reindexParts_parts {q Q : ℕ}
    (P : EquitableInitialPartition V Q) (e : Fin q ≃ Fin Q) (i : Fin q) :
    (P.reindexParts e).parts i = P.parts (e i) :=
  rfl

end Regularity.EquitableInitialPartition

namespace TypeLemmaRowResult

variable {f s : ℕ} {G : (n : ℕ) → SimpleGraph (Fin (n + 1))}
  {parent : EquitablePartitionRow s} {eta delta : ℝ} {L : ℕ}

/-- The canonical clean partition of the `n`th Type-Lemma output, transported
to the row-independent cluster index `Fin (s * childCount)`. -/
def fixedCleanTypePartition
    (R : TypeLemmaRowResult (f := f) G parent eta delta L) (n : ℕ) :
    @CleanTypePartition (Fin (parent.extraction (R.factor n) + 1))
      inferInstance inferInstance
      (G (parent.extraction (R.factor n))) (Classical.decRel _)
      eta delta f (R.fixedCanonicalType n) where
  partition := ((R.result n).cleanTypePartition.partition).reindexParts
    (R.fixedCanonicalIndexEquiv n)
  cluster_subset := by
    intro x
    change (R.result n).canonicalType.partition.clusters
        (R.fixedCanonicalIndexEquiv n x) ⊆
      (R.result n).cleanTypePartition.partition.parts
        (R.fixedCanonicalIndexEquiv n x)
    exact (R.result n).cleanTypePartition.cluster_subset _
  added_subset_exceptional := by
    intro x
    change (R.result n).cleanTypePartition.partition.parts
          (R.fixedCanonicalIndexEquiv n x) \
        (R.result n).canonicalType.partition.clusters
          (R.fixedCanonicalIndexEquiv n x) ⊆
      (R.result n).canonicalType.partition.exceptional
    exact (R.result n).cleanTypePartition.added_subset_exceptional _

@[simp] theorem fixedCleanTypePartition_parts
    (R : TypeLemmaRowResult (f := f) G parent eta delta L)
    (n : ℕ) (x : Fin (s * R.childCount)) :
    (R.fixedCleanTypePartition n).partition.parts x =
      (R.result n).cleanTypePartition.partition.parts
        (R.fixedCanonicalIndexEquiv n x) :=
  rfl

/-- The row of fixed-index clean partitions underlying a Type-Lemma row. -/
def fixedCleanRow (R : TypeLemmaRowResult (f := f) G parent eta delta L) :
    EquitablePartitionRow (s * R.childCount) where
  extraction := R.extraction
  extraction_strictMono := R.extraction_strictMono
  partition n := (R.fixedCleanTypePartition n).partition

@[simp] theorem fixedCleanRow_extraction
    (R : TypeLemmaRowResult (f := f) G parent eta delta L) (n : ℕ) :
    R.fixedCleanRow.extraction n = R.extraction n :=
  rfl

@[simp] theorem fixedCleanRow_partition
    (R : TypeLemmaRowResult (f := f) G parent eta delta L) (n : ℕ) :
    R.fixedCleanRow.partition n = (R.fixedCleanTypePartition n).partition :=
  rfl

/-- Fixed-index clean density matrices for a Type-Lemma row. -/
def fixedCleanMatrix
    (R : TypeLemmaRowResult (f := f) G parent eta delta L) (n : ℕ) :
    Matrix (Fin (s * R.childCount)) (Fin (s * R.childCount)) ℝ :=
  @cleanDensityMatrix (Fin (R.extraction n + 1)) inferInstance inferInstance
    _ (G (R.extraction n)) (Classical.decRel _) (R.fixedCleanRow.partition n)

/-- Fixed-index clean graphons for a Type-Lemma row. -/
def fixedCleanGraphon
    (R : TypeLemmaRowResult (f := f) G parent eta delta L) (n : ℕ) : Graphon :=
  @cleanPartitionGraphon (Fin (R.extraction n + 1)) inferInstance inferInstance
    _ (G (R.extraction n)) (Classical.decRel _) (R.fixedCleanRow.partition n)

/-- The retained-proportion estimate for the canonical cleaning, transported
to the fixed cluster index used throughout a row. -/
theorem fixedCleanTypePartition_retained_proportion
    (R : TypeLemmaRowResult (f := f) G parent eta delta L)
    (n : ℕ) (x : Fin (s * R.childCount)) :
    (1 - (R.result n).cleaningProportion) *
        (((R.fixedCleanTypePartition n).partition.parts x).card : ℝ) ≤
      ((R.fixedCanonicalType n).partition.clusters x).card := by
  change (1 - (R.result n).cleaningProportion) *
      (((R.result n).cleanTypePartition.partition.parts
        (R.fixedCanonicalIndexEquiv n x)).card : ℝ) ≤
    ((R.result n).canonicalType.partition.clusters
      (R.fixedCanonicalIndexEquiv n x)).card
  exact (R.result n).cleanTypePartition_retained_proportion
    (R.fixedCanonicalIndexEquiv n x)

/-- Direct quantitative `L¹` control between a fixed canonical Type and its
fixed-index clean partition graphon.  The deliberately relaxed rounding term
is the one stored by `CleanTypeSequenceLevel`. -/
theorem graphonL1Dist_fixedCanonicalType_fixedCleanGraphon_le
    (R : TypeLemmaRowResult (f := f) G parent eta delta L) (n : ℕ) :
    graphonL1Dist (typeGraphon (R.fixedCanonicalType n))
        (R.fixedCleanGraphon n) ≤
      4 * eta +
        8 * (((s * R.childCount : ℕ) : ℝ) /
          ((R.extraction n + 1 : ℕ) : ℝ)) := by
  have hclean :=
    Regularity.CleanTypePartition.graphonL1Dist_cleanPartitionGraphon_typeGraphon_le
        (R.fixedCleanTypePartition n)
        (R.result n).cleaningProportion_nonneg
        (R.fixedCleanTypePartition_retained_proportion n)
  change graphonL1Dist
      (cleanPartitionGraphon (G (R.extraction n))
        (R.fixedCleanTypePartition n).partition)
      (typeGraphon (R.fixedCanonicalType n)) ≤
    2 * (R.result n).cleaningProportion at hclean
  calc
    graphonL1Dist (typeGraphon (R.fixedCanonicalType n))
        (R.fixedCleanGraphon n) =
        graphonL1Dist (R.fixedCleanGraphon n)
          (typeGraphon (R.fixedCanonicalType n)) :=
      graphonL1Dist_comm _ _
    _ ≤ 2 * (R.result n).cleaningProportion := by
      unfold fixedCleanGraphon
      change graphonL1Dist
          (cleanPartitionGraphon (G (R.extraction n))
            (R.fixedCleanTypePartition n).partition)
          (typeGraphon (R.fixedCanonicalType n)) ≤
        2 * (R.result n).cleaningProportion
      exact hclean
    _ ≤ 4 * eta +
        8 * (((s * R.childCount : ℕ) : ℝ) /
          ((R.extraction n + 1 : ℕ) : ℝ)) := by
      unfold Regularity.TypeLemmaResult.cleaningProportion
      rw [R.result_childCount n]
      simp only [Fintype.card_fin]
      rw [show R.extraction n = parent.extraction (R.factor n) from rfl]
      have hratio : 0 ≤
          ((s * R.childCount : ℕ) : ℝ) /
            (((parent.extraction (R.factor n) + 1 : ℕ) : ℝ)) := by
        positivity
      calc
        _ = 4 * eta +
              4 * (((s * R.childCount : ℕ) : ℝ) /
                ((parent.extraction (R.factor n) + 1 : ℕ) : ℝ)) := by ring
        _ ≤ 4 * eta +
            8 * (((s * R.childCount : ℕ) : ℝ) /
              ((parent.extraction (R.factor n) + 1 : ℕ) : ℝ)) := by
          have hmul := mul_le_mul_of_nonneg_right
            (show (4 : ℝ) ≤ 8 by norm_num) hratio
          linarith

private theorem fixedCleanRefinement_quotient
    (R : TypeLemmaRowResult (f := f) G parent eta delta L)
    (hs : 0 < s) :
    s * R.childCount / s = R.childCount := by
  simpa [Nat.mul_comm] using Nat.mul_div_left R.childCount hs

private theorem fixedCleanRefinement_index
    (R : TypeLemmaRowResult (f := f) G parent eta delta L)
    (hs : 0 < s) (i : Fin s)
    (a : Fin ((s * R.childCount) / s)) :
    Graphon.refinementIndex (dvd_mul_right s R.childCount) i a =
      finProdFinEquiv
        (i, finCongr (R.fixedCleanRefinement_quotient hs) a) := by
  apply Fin.ext
  simp [Graphon.refinementIndex, finProdFinEquiv,
    R.fixedCleanRefinement_quotient hs, Nat.add_comm, Nat.mul_comm]

/-- The fixed-index clean partition in row `n` is an exact consecutive
uniform refinement of the prescribed parent partition. -/
noncomputable def fixedCleanUniformEquitableRefinement
    (R : TypeLemmaRowResult (f := f) G parent eta delta L)
    (n : ℕ) (hs : 0 < s) :
    UniformEquitableRefinement (dvd_mul_right s R.childCount)
      (parent.partition (R.factor n))
      (R.fixedCleanRow.partition n) where
  coarseCount_pos := hs
  factor_pos := by
    rw [R.fixedCleanRefinement_quotient hs]
    exact R.childCount_pos
  child_subset := by
    intro i a
    rw [fixedCleanRow_partition]
    change (R.result n).cleanTypePartition.partition.parts
        (R.fixedCanonicalIndexEquiv n
          (Graphon.refinementIndex
            (dvd_mul_right s R.childCount) i a)) ⊆
      (parent.partition (R.factor n)).parts i
    rw [R.fixedCleanRefinement_index hs,
      R.fixedCanonicalIndexEquiv_finProdFinEquiv,
      (R.result n).cleanTypePartition_parts,
      (R.result n).cleanChild_finProdFinEquiv]
    exact (R.result n).cleanChildAt_subset_initial i _
  parent_eq_biUnion := by
    intro i
    rw [(R.result n).initialPart_eq_biUnion_cleanPartition i]
    ext x
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
    let e : Fin ((s * R.childCount) / s) ≃
        Fin (R.result n).childCount :=
      (finCongr (R.fixedCleanRefinement_quotient hs)).trans
        (R.fixedChildIndexEquiv n)
    constructor
    · rintro ⟨a, hxa⟩
      refine ⟨e.symm a, ?_⟩
      rw [R.fixedCleanRefinement_index hs]
      change x ∈ (R.result n).cleanTypePartition.partition.parts
        (R.fixedCanonicalIndexEquiv n
          (finProdFinEquiv
            (i, finCongr (R.fixedCleanRefinement_quotient hs) (e.symm a))))
      rw [
        R.fixedCanonicalIndexEquiv_finProdFinEquiv,
        (R.result n).cleanTypePartition_parts,
        (R.result n).cleanChild_finProdFinEquiv]
      have heq :
          R.fixedChildIndexEquiv n
              (finCongr (R.fixedCleanRefinement_quotient hs) (e.symm a)) = a := by
        change e (e.symm a) = a
        exact e.apply_symm_apply a
      rw [heq]
      simpa only [(R.result n).cleanTypePartition_parts,
        (R.result n).cleanChild_finProdFinEquiv] using hxa
    · rintro ⟨a, hxa⟩
      refine ⟨e a, ?_⟩
      rw [R.fixedCleanRefinement_index hs] at hxa
      change x ∈ (R.result n).cleanTypePartition.partition.parts
        (R.fixedCanonicalIndexEquiv n
          (finProdFinEquiv
            (i, finCongr (R.fixedCleanRefinement_quotient hs) a))) at hxa
      rw [
        R.fixedCanonicalIndexEquiv_finProdFinEquiv,
        (R.result n).cleanTypePartition_parts,
        (R.result n).cleanChild_finProdFinEquiv] at hxa
      rw [(R.result n).cleanTypePartition_parts,
        (R.result n).cleanChild_finProdFinEquiv]
      have heq : e a =
          R.fixedChildIndexEquiv n
            (finCongr (R.fixedCleanRefinement_quotient hs) a) := rfl
      rw [heq]
      exact hxa

end TypeLemmaRowResult

/-! ## A compact fixed-size clean level -/

/-- One completed level of the clean Type tower.  It retains actual Types,
their clean relation to an equitable row, the clean matrices and graphons,
and a common fixed-dimensional entrywise matrix limit. -/
structure CleanTypeSequenceLevel
    {f : ℕ} (G : (n : ℕ) → SimpleGraph (Fin (n + 1)))
    (eta delta : ℝ) where
  clusterCount : ℕ
  clusterCount_pos : 0 < clusterCount
  row : EquitablePartitionRow clusterCount
  hostAdjDecidable : ∀ n, DecidableRel (G (row.extraction n)).Adj
  typeData : (n : ℕ) →
    @RegularityType (Fin (row.extraction n + 1)) inferInstance inferInstance
      (G (row.extraction n)) (hostAdjDecidable n) eta delta f
  typeData_clusterCount :
    ∀ n, (typeData n).partition.clusterCount = clusterCount
  cleanData : (n : ℕ) →
    @CleanTypePartition (Fin (row.extraction n + 1))
      inferInstance inferInstance (G (row.extraction n))
      (hostAdjDecidable n) eta delta f (typeData n)
  cleanIndexEquiv :
    ∀ n, Fin clusterCount ≃ Fin (typeData n).partition.clusterCount
  clean_parts_eq : ∀ n i,
    (cleanData n).partition.parts (cleanIndexEquiv n i) =
      (row.partition n).parts i
  typeGraphon : ℕ → Graphon
  typeGraphon_eq : ∀ n,
    typeGraphon n =
      @InducedStars.typeGraphon (Fin (row.extraction n + 1))
        inferInstance inferInstance (G (row.extraction n))
        (hostAdjDecidable n) eta delta f (typeData n)
  cleanMatrix : ℕ → Matrix (Fin clusterCount) (Fin clusterCount) ℝ
  cleanMatrix_eq : ∀ n,
    cleanMatrix n =
      @cleanDensityMatrix (Fin (row.extraction n + 1))
        inferInstance inferInstance clusterCount (G (row.extraction n))
        (hostAdjDecidable n) (row.partition n)
  cleanGraphon : ℕ → Graphon
  cleanGraphon_eq : ∀ n,
    cleanGraphon n =
      @cleanPartitionGraphon (Fin (row.extraction n + 1))
        inferInstance inferInstance clusterCount (G (row.extraction n))
        (hostAdjDecidable n) (row.partition n)
  typeCleanError : ℕ → ℝ
  typeCleanError_eq : ∀ n,
    typeCleanError n =
      4 * eta + 8 * ((clusterCount : ℝ) / ((row.extraction n + 1 : ℕ) : ℝ))
  typeCleanError_nonneg : ∀ n, 0 ≤ typeCleanError n
  type_to_clean_l1_le : ∀ n,
    graphonL1Dist (typeGraphon n) (cleanGraphon n) ≤ typeCleanError n
  limitMatrix : Matrix (Fin clusterCount) (Fin clusterCount) ℝ
  limitMatrix_symmetric : limitMatrix.IsSymm
  limitMatrix_mem_Icc : ∀ i j, limitMatrix i j ∈ Icc (0 : ℝ) 1
  cleanMatrix_tendsto : ∀ i j,
    Tendsto (fun n ↦ cleanMatrix n i j) atTop (nhds (limitMatrix i j))

namespace CleanTypeSequenceLevel

variable {f : ℕ} {G : (n : ℕ) → SimpleGraph (Fin (n + 1))}
  {eta delta : ℝ}

/-- The number of vertices in the host selected at row index `n`. -/
def hostSize (D : CleanTypeSequenceLevel (f := f) G eta delta) (n : ℕ) : ℕ :=
  D.row.extraction n + 1

theorem hostSize_pos (D : CleanTypeSequenceLevel (f := f) G eta delta)
    (n : ℕ) : 0 < D.hostSize n := by
  simp [hostSize]

/-- Host sizes along a level tend to infinity. -/
theorem hostSize_tendsto_atTop
    (D : CleanTypeSequenceLevel (f := f) G eta delta) :
    Tendsto D.hostSize atTop atTop := by
  apply StrictMono.tendsto_atTop
  intro a b hab
  exact Nat.add_lt_add_right (D.row.extraction_strictMono hab) 1

/-- A fixed cluster count is negligible compared with the growing host
size.  This is the ratio used in the quantitative clean-partition error. -/
theorem clusterCount_div_hostSize_tendsto_zero
    (D : CleanTypeSequenceLevel (f := f) G eta delta) :
    Tendsto (fun n ↦ (D.clusterCount : ℝ) / (D.hostSize n : ℝ))
      atTop (nhds 0) := by
  have hreal : Tendsto (fun n ↦ (D.hostSize n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp D.hostSize_tendsto_atTop
  have hinv : Tendsto (fun n ↦ ((D.hostSize n : ℝ))⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp hreal
  simpa only [div_eq_mul_inv, mul_zero] using
    (tendsto_const_nhds.mul hinv :
      Tendsto (fun n ↦ (D.clusterCount : ℝ) * ((D.hostSize n : ℝ))⁻¹)
        atTop (nhds ((D.clusterCount : ℝ) * 0)))

/-- Any fixed real numerator divided by the growing host order tends to
zero. -/
theorem const_div_hostSize_tendsto_zero
    (D : CleanTypeSequenceLevel (f := f) G eta delta) (c : ℝ) :
    Tendsto (fun n ↦ c / (D.hostSize n : ℝ)) atTop (nhds 0) := by
  have hreal : Tendsto (fun n ↦ (D.hostSize n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp D.hostSize_tendsto_atTop
  have hinv : Tendsto (fun n ↦ ((D.hostSize n : ℝ))⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp hreal
  simpa only [div_eq_mul_inv, mul_zero] using
    (tendsto_const_nhds.mul hinv :
      Tendsto (fun n ↦ c * ((D.hostSize n : ℝ))⁻¹)
        atTop (nhds (c * 0)))

/-- Along a fixed level the finite-host correction vanishes, leaving the
uniform error `4 * eta`. -/
theorem typeCleanError_tendsto
    (D : CleanTypeSequenceLevel (f := f) G eta delta) :
    Tendsto D.typeCleanError atTop (nhds (4 * eta)) := by
  have hratio := D.clusterCount_div_hostSize_tendsto_zero.const_mul (8 : ℝ)
  have hsum := (tendsto_const_nhds :
      Tendsto (fun _ : ℕ ↦ 4 * eta) atTop (nhds (4 * eta))).add hratio
  simpa only [mul_zero, add_zero] using hsum.congr'
    (Eventually.of_forall fun n ↦ (D.typeCleanError_eq n).symm)

/-- Restrict a completed clean level along a further subsequence. -/
def subsequence (D : CleanTypeSequenceLevel (f := f) G eta delta)
    (phi : ℕ → ℕ) (hphi : StrictMono phi) :
    CleanTypeSequenceLevel (f := f) G eta delta where
  clusterCount := D.clusterCount
  clusterCount_pos := D.clusterCount_pos
  row := D.row.subsequence phi hphi
  hostAdjDecidable n := D.hostAdjDecidable (phi n)
  typeData n := D.typeData (phi n)
  typeData_clusterCount n := D.typeData_clusterCount (phi n)
  cleanData n := D.cleanData (phi n)
  cleanIndexEquiv n := D.cleanIndexEquiv (phi n)
  clean_parts_eq n i := D.clean_parts_eq (phi n) i
  typeGraphon n := D.typeGraphon (phi n)
  typeGraphon_eq n := D.typeGraphon_eq (phi n)
  cleanMatrix n := D.cleanMatrix (phi n)
  cleanMatrix_eq n := D.cleanMatrix_eq (phi n)
  cleanGraphon n := D.cleanGraphon (phi n)
  cleanGraphon_eq n := D.cleanGraphon_eq (phi n)
  typeCleanError n := D.typeCleanError (phi n)
  typeCleanError_eq n := D.typeCleanError_eq (phi n)
  typeCleanError_nonneg n := D.typeCleanError_nonneg (phi n)
  type_to_clean_l1_le n := D.type_to_clean_l1_le (phi n)
  limitMatrix := D.limitMatrix
  limitMatrix_symmetric := D.limitMatrix_symmetric
  limitMatrix_mem_Icc := D.limitMatrix_mem_Icc
  cleanMatrix_tendsto i j :=
    (D.cleanMatrix_tendsto i j).comp hphi.tendsto_atTop

@[simp] theorem subsequence_row_extraction
    (D : CleanTypeSequenceLevel (f := f) G eta delta)
    (phi : ℕ → ℕ) (hphi : StrictMono phi) (n : ℕ) :
    (D.subsequence phi hphi).row.extraction n = D.row.extraction (phi n) :=
  rfl

@[simp] theorem subsequence_cleanMatrix
    (D : CleanTypeSequenceLevel (f := f) G eta delta)
    (phi : ℕ → ℕ) (hphi : StrictMono phi) (n : ℕ) :
    (D.subsequence phi hphi).cleanMatrix n = D.cleanMatrix (phi n) :=
  rfl

@[simp] theorem subsequence_typeGraphon
    (D : CleanTypeSequenceLevel (f := f) G eta delta)
    (phi : ℕ → ℕ) (hphi : StrictMono phi) (n : ℕ) :
    (D.subsequence phi hphi).typeGraphon n = D.typeGraphon (phi n) :=
  rfl

@[simp] theorem subsequence_cleanGraphon
    (D : CleanTypeSequenceLevel (f := f) G eta delta)
    (phi : ℕ → ℕ) (hphi : StrictMono phi) (n : ℕ) :
    (D.subsequence phi hphi).cleanGraphon n = D.cleanGraphon (phi n) :=
  rfl

end CleanTypeSequenceLevel

/-! ## Fixed-dimensional compactness for a Type-Lemma row -/

/-- The compactness choices needed to turn a `TypeLemmaRowResult` into one
completed clean level.  Keeping the selector explicit is important when this
level is later installed as a child of its prescribed parent row. -/
structure CompactCleanTypeRowResult
    {f s : ℕ} {G : (n : ℕ) → SimpleGraph (Fin (n + 1))}
    {parent : EquitablePartitionRow s} {eta delta : ℝ} {L : ℕ}
    (R : TypeLemmaRowResult (f := f) G parent eta delta L) where
  selection : ℕ → ℕ
  selection_strictMono : StrictMono selection
  limitMatrix : Matrix (Fin (s * R.childCount))
    (Fin (s * R.childCount)) ℝ
  limitMatrix_symmetric : limitMatrix.IsSymm
  limitMatrix_mem_Icc : ∀ i j, limitMatrix i j ∈ Icc (0 : ℝ) 1
  cleanMatrix_tendsto : ∀ i j,
    Tendsto (fun n ↦ R.fixedCleanMatrix (selection n) i j)
      atTop (nhds (limitMatrix i j))

namespace CompactCleanTypeRowResult

variable {f s : ℕ} {G : (n : ℕ) → SimpleGraph (Fin (n + 1))}
  {parent : EquitablePartitionRow s} {eta delta : ℝ} {L : ℕ}
  {R : TypeLemmaRowResult (f := f) G parent eta delta L}

/-- The completed clean level determined by the compactness data.  Its row
and all finite objects are definitionally the selected fixed clean row. -/
def toCleanTypeSequenceLevel (C : CompactCleanTypeRowResult R) :
    CleanTypeSequenceLevel (f := f) G eta delta where
  clusterCount := s * R.childCount
  clusterCount_pos := (R.fixedCleanRow.partition 0).partCount_pos
  row := R.fixedCleanRow.subsequence C.selection C.selection_strictMono
  hostAdjDecidable _ := Classical.decRel _
  typeData n := R.fixedCanonicalType (C.selection n)
  typeData_clusterCount _ := rfl
  cleanData n := R.fixedCleanTypePartition (C.selection n)
  cleanIndexEquiv _ := Equiv.refl _
  clean_parts_eq _ _ := rfl
  typeGraphon n := typeGraphon (R.fixedCanonicalType (C.selection n))
  typeGraphon_eq _ := rfl
  cleanMatrix n := R.fixedCleanMatrix (C.selection n)
  cleanMatrix_eq _ := rfl
  cleanGraphon n := R.fixedCleanGraphon (C.selection n)
  cleanGraphon_eq _ := rfl
  typeCleanError n :=
    4 * eta +
      8 * (((s * R.childCount : ℕ) : ℝ) /
        ((R.extraction (C.selection n) + 1 : ℕ) : ℝ))
  typeCleanError_eq _ := rfl
  typeCleanError_nonneg _ := by
    have heta : 0 ≤ eta := (R.fixedCanonicalType 0).epsilon_pos.le
    positivity
  type_to_clean_l1_le n :=
    R.graphonL1Dist_fixedCanonicalType_fixedCleanGraphon_le (C.selection n)
  limitMatrix := C.limitMatrix
  limitMatrix_symmetric := C.limitMatrix_symmetric
  limitMatrix_mem_Icc := C.limitMatrix_mem_Icc
  cleanMatrix_tendsto := C.cleanMatrix_tendsto

@[simp] theorem toCleanTypeSequenceLevel_clusterCount
    (C : CompactCleanTypeRowResult R) :
    C.toCleanTypeSequenceLevel.clusterCount = s * R.childCount :=
  rfl

@[simp] theorem toCleanTypeSequenceLevel_row_extraction
    (C : CompactCleanTypeRowResult R) (n : ℕ) :
    C.toCleanTypeSequenceLevel.row.extraction n =
      R.extraction (C.selection n) :=
  rfl

@[simp] theorem toCleanTypeSequenceLevel_typeData
    (C : CompactCleanTypeRowResult R) (n : ℕ) :
    C.toCleanTypeSequenceLevel.typeData n =
      R.fixedCanonicalType (C.selection n) :=
  rfl

@[simp] theorem toCleanTypeSequenceLevel_cleanData
    (C : CompactCleanTypeRowResult R) (n : ℕ) :
    C.toCleanTypeSequenceLevel.cleanData n =
      R.fixedCleanTypePartition (C.selection n) :=
  rfl

@[simp] theorem toCleanTypeSequenceLevel_cleanMatrix
    (C : CompactCleanTypeRowResult R) (n : ℕ) :
    C.toCleanTypeSequenceLevel.cleanMatrix n =
      R.fixedCleanMatrix (C.selection n) :=
  rfl

end CompactCleanTypeRowResult

namespace TypeLemmaRowResult

variable {f s : ℕ} {G : (n : ℕ) → SimpleGraph (Fin (n + 1))}
  {parent : EquitablePartitionRow s} {eta delta : ℝ} {L : ℕ}

/-- Extract a common entrywise limit from the fixed clean density matrices
of a Type-Lemma row. -/
theorem exists_compactCleanTypeRowResult
    (R : TypeLemmaRowResult (f := f) G parent eta delta L) :
    Nonempty (CompactCleanTypeRowResult R) := by
  have hmem : ∀ n i j, R.fixedCleanMatrix n i j ∈ Icc (0 : ℝ) 1 := by
    intro n i j
    exact ⟨cleanDensityMatrix_nonneg _ _ i j,
      cleanDensityMatrix_le_one _ _ i j⟩
  have hsymm : ∀ n, (R.fixedCleanMatrix n).IsSymm := by
    intro n
    exact cleanDensityMatrix_isSymm _ _
  obtain ⟨M, hM_symm, hM_Icc, phi, hphi, hlim⟩ :=
    Graphon.symmetricMatrix_mem_Icc_tendsto_subsequence
      (s * R.childCount) R.fixedCleanMatrix hmem hsymm
  exact ⟨{
    selection := phi
    selection_strictMono := hphi
    limitMatrix := M
    limitMatrix_symmetric := hM_symm
    limitMatrix_mem_Icc := hM_Icc
    cleanMatrix_tendsto := hlim }⟩

/-- Compactness constructor producing a completed clean Type-sequence level
from a rowwise enhanced-Type-Lemma result. -/
theorem exists_cleanTypeSequenceLevel
    (R : TypeLemmaRowResult (f := f) G parent eta delta L) :
    ∃ C : CompactCleanTypeRowResult R,
      Nonempty (CleanTypeSequenceLevel (f := f) G eta delta) := by
  obtain ⟨C⟩ := R.exists_compactCleanTypeRowResult
  exact ⟨C, ⟨C.toCleanTypeSequenceLevel⟩⟩

end TypeLemmaRowResult

/-- Apply the enhanced Type Lemma along a prescribed row, make its child
count constant, and then perform the fixed-dimensional compactness
extraction.  This is the one-call constructor used at each tower level. -/
theorem exists_compactCleanTypeRowResult_of_typeLemma
    {f s : ℕ} (hf : 0 < f)
    (G : (n : ℕ) → SimpleGraph (Fin (n + 1)))
    (parent : EquitablePartitionRow s) (hs : 0 < s)
    (delta : ℝ) (hdelta : 0 < delta) (hdeltaHalf : delta < 1 / 2)
    {epsilonStar eta : ℝ} (hStar :
      ∀ L t : ℕ, 0 < L → 0 < t →
        ∀ eta : ℝ, 0 < eta → eta < epsilonStar →
          ∃ U n0 : ℕ,
            ∀ {V : Type} [Fintype V] [DecidableEq V]
              (H : SimpleGraph V) [DecidableRel H.Adj]
              {q : ℕ} (_hq : 0 < q) (_hqt : q ≤ t)
              (initial : EquitableInitialPartition V q),
                n0 ≤ Fintype.card V →
                  Nonempty (TypeLemmaResult H eta delta f initial L U))
    (heta : 0 < eta) (hetaStar : eta < epsilonStar)
    (L t : ℕ) (hL : 0 < L) (ht : 0 < t) (hst : s ≤ t) :
    ∃ R : TypeLemmaRowResult (f := f) G parent eta delta L,
      Nonempty (CompactCleanTypeRowResult R) := by
  obtain ⟨R⟩ := exists_typeLemmaRowResult hf G parent hs delta hdelta
    hdeltaHalf hStar heta hetaStar L t hL ht hst
  exact ⟨R, R.exists_compactCleanTypeRowResult⟩

/-! ## Exact cross-level assembly data -/

/-- A child clean level refining a parent level.  Besides the nested row, the
package retains the quantitative block-average error.  The exact finite
partition equation is exposed by `fixedCleanUniformEquitableRefinement`; the
final field here is the exact identity between limiting matrices obtained by
sending the error to zero. -/
structure CleanTypeSequenceExtension
    {f : ℕ} {G : (n : ℕ) → SimpleGraph (Fin (n + 1))}
    {parentEta childEta delta : ℝ}
    (parent : CleanTypeSequenceLevel (f := f) G parentEta delta)
    (child : CleanTypeSequenceLevel (f := f) G childEta delta) where
  factor : ℕ → ℕ
  factor_strictMono : StrictMono factor
  row_extraction : child.row.extraction = parent.row.extraction ∘ factor
  clusterCount_dvd : parent.clusterCount ∣ child.clusterCount
  blockError : ℕ → ℝ
  blockError_nonneg : ∀ n, 0 ≤ blockError n
  blockError_tendsto : Tendsto blockError atTop (nhds 0)
  cleanMatrix_blockError : ∀ n i j,
    |parent.cleanMatrix (factor n) i j -
        Graphon.matrixBlockAverage clusterCount_dvd (child.cleanMatrix n) i j| ≤
      blockError n
  limitMatrix_blockAverage : ∀ i j,
    parent.limitMatrix i j =
      Graphon.matrixBlockAverage clusterCount_dvd child.limitMatrix i j

namespace CleanTypeSequenceExtension

variable {f : ℕ} {G : (n : ℕ) → SimpleGraph (Fin (n + 1))}
  {parentEta childEta delta : ℝ}
  {parent : CleanTypeSequenceLevel (f := f) G parentEta delta}
  {child : CleanTypeSequenceLevel (f := f) G childEta delta}

/-- Build an exact extension from a strict row extraction and a block-average
error tending to zero. -/
def ofBlockError
    (factor : ℕ → ℕ) (hfactor : StrictMono factor)
    (hrow : child.row.extraction = parent.row.extraction ∘ factor)
    (hdvd : parent.clusterCount ∣ child.clusterCount)
    (error : ℕ → ℝ) (herror_nonneg : ∀ n, 0 ≤ error n)
    (herror : Tendsto error atTop (nhds 0))
    (hblock : ∀ n i j,
      |parent.cleanMatrix (factor n) i j -
          Graphon.matrixBlockAverage hdvd (child.cleanMatrix n) i j| ≤ error n) :
    CleanTypeSequenceExtension parent child where
  factor := factor
  factor_strictMono := hfactor
  row_extraction := hrow
  clusterCount_dvd := hdvd
  blockError := error
  blockError_nonneg := herror_nonneg
  blockError_tendsto := herror
  cleanMatrix_blockError := hblock
  limitMatrix_blockAverage := by
    exact Graphon.matrixBlockAverage_eq_of_tendsto_of_abs_sub_le hdvd
      (fun n ↦ parent.cleanMatrix (factor n)) child.cleanMatrix
      parent.limitMatrix child.limitMatrix
      (fun i j ↦ (parent.cleanMatrix_tendsto i j).comp hfactor.tendsto_atTop)
      child.cleanMatrix_tendsto error herror hblock

end CleanTypeSequenceExtension

namespace CompactCleanTypeRowResult

variable {f : ℕ} {G : (n : ℕ) → SimpleGraph (Fin (n + 1))}
  {parentEta childEta delta : ℝ} {L : ℕ}

/-- Install a compacted Type-Lemma row as an exact child of its prescribed
clean parent level.  The finite block error is the explicit equitable
rounding term `4 * s * r² / N`; its vanishing yields the exact limiting block
identity stored in `CleanTypeSequenceExtension`. -/
noncomputable def toCleanTypeSequenceExtension
    (parentLevel : CleanTypeSequenceLevel (f := f) G parentEta delta)
    (R : TypeLemmaRowResult (f := f) G parentLevel.row childEta delta L)
    (C : CompactCleanTypeRowResult R) :
    CleanTypeSequenceExtension parentLevel
      C.toCleanTypeSequenceLevel := by
  let child := C.toCleanTypeSequenceLevel
  let factor : ℕ → ℕ := R.factor ∘ C.selection
  have hfactor : StrictMono factor :=
    R.factor_strictMono.comp C.selection_strictMono
  have hrow : child.row.extraction =
      parentLevel.row.extraction ∘ factor := by
    funext n
    rfl
  have hdvd : parentLevel.clusterCount ∣ child.clusterCount := by
    exact dvd_mul_right parentLevel.clusterCount R.childCount
  let error : ℕ → ℝ := fun n ↦
    4 * (parentLevel.clusterCount : ℝ) *
        (((parentLevel.clusterCount * R.childCount /
          parentLevel.clusterCount : ℕ) : ℝ) ^ 2) /
      (child.hostSize n : ℝ)
  refine CleanTypeSequenceExtension.ofBlockError factor hfactor hrow hdvd
    error ?_ ?_ ?_
  · intro n
    dsimp only [error]
    positivity
  · exact child.const_div_hostSize_tendsto_zero
      (4 * (parentLevel.clusterCount : ℝ) *
        (((parentLevel.clusterCount * R.childCount /
          parentLevel.clusterCount : ℕ) : ℝ) ^ 2))
  · intro n i j
    let Q := R.fixedCleanUniformEquitableRefinement (C.selection n)
      parentLevel.clusterCount_pos
    letI : DecidableRel
        (G (parentLevel.row.extraction (R.factor (C.selection n)))).Adj :=
      Classical.decRel _
    have hdec : parentLevel.hostAdjDecidable
          (R.factor (C.selection n)) =
        (inferInstance : DecidableRel
          (G (parentLevel.row.extraction
            (R.factor (C.selection n)))).Adj) :=
      Subsingleton.elim _ _
    have hblock := Q.abs_cleanDensityMatrix_sub_matrixBlockAverage_le
      (G (parentLevel.row.extraction (R.factor (C.selection n)))) i j
    dsimp only [error]
    simp only [child, factor, Function.comp_apply,
      CleanTypeSequenceLevel.hostSize, Fintype.card_fin,
      CompactCleanTypeRowResult.toCleanTypeSequenceLevel_row_extraction,
      CompactCleanTypeRowResult.toCleanTypeSequenceLevel_cleanMatrix,
      TypeLemmaRowResult.fixedCleanMatrix,
      TypeLemmaRowResult.extraction,
      parentLevel.cleanMatrix_eq]
    rw [hdec]
    have hproof : hdvd =
        dvd_mul_right parentLevel.clusterCount R.childCount :=
      Subsingleton.elim _ _
    rw [hproof]
    convert hblock using 1
    · rfl
    · simp only [Fintype.card_fin]

end CompactCleanTypeRowResult

end InducedStars
