import InducedStars.Graphon.Approximation
import InducedStars.Graphon.TypeTowerConstruction
import InducedStars.Regularity.Reindex
import Mathlib.Tactic

/-!
# Fixed canonical indexing along a row of Types

`TypeLemmaRowResult` makes the number of children independent of the row
index, but its individual `TypeLemmaResult`s still expose that equality only
propositionally.  This file transports the canonical parent/child indexing of
each result to the single fixed index type `Fin (s * R.childCount)`.
-/

noncomputable section

open Finset

namespace InducedStars

open Regularity

attribute [local instance] Classical.propDecidable

namespace TypeLemmaRowResult

variable {f s : ℕ} {G : (n : ℕ) → SimpleGraph (Fin (n + 1))}
  {parent : EquitablePartitionRow s} {eta delta : ℝ} {L : ℕ}

variable (R : TypeLemmaRowResult (f := f) G parent eta delta L)

/-- Cast the row's fixed child index type to the child index type carried by
the `n`th Type-Lemma result. -/
noncomputable def fixedChildIndexEquiv (n : ℕ) :
    Fin R.childCount ≃ Fin (R.result n).childCount :=
  finCongr (R.result_childCount n).symm

/-- The coordinate-preserving cast from the fixed parent/child index type to
the parent/child index type native to the `n`th result. -/
noncomputable def fixedCanonicalIndexEquiv (n : ℕ) :
    Fin (s * R.childCount) ≃ Fin (s * (R.result n).childCount) :=
  finProdFinEquiv.symm |>.trans
    ((Equiv.refl (Fin s)).prodCongr (R.fixedChildIndexEquiv n)) |>.trans
      finProdFinEquiv

@[simp] theorem fixedCanonicalIndexEquiv_finProdFinEquiv
    (n : ℕ) (i : Fin s) (a : Fin R.childCount) :
    R.fixedCanonicalIndexEquiv n (finProdFinEquiv (i, a)) =
      finProdFinEquiv (i, R.fixedChildIndexEquiv n a) := by
  simp [fixedCanonicalIndexEquiv]

/-- The fixed parent/child coordinates sent to the original cluster indices
of the `n`th Type-Lemma result. -/
noncomputable def fixedCanonicalClusterEquiv (n : ℕ) :
    Fin (s * R.childCount) ≃
      Fin (R.result n).regularityType.partition.clusterCount :=
  (R.fixedCanonicalIndexEquiv n).trans
    (R.result n).canonicalClusterEquiv

@[simp] theorem fixedCanonicalClusterEquiv_finProdFinEquiv
    (n : ℕ) (i : Fin s) (a : Fin R.childCount) :
    R.fixedCanonicalClusterEquiv n (finProdFinEquiv (i, a)) =
      ((R.result n).childEquiv i (R.fixedChildIndexEquiv n a)).1 := by
  simp [fixedCanonicalClusterEquiv]

@[simp] theorem fixedCanonicalClusterEquiv_mem_parentBlock
    (n : ℕ) (i : Fin s) (a : Fin R.childCount) :
    R.fixedCanonicalClusterEquiv n (finProdFinEquiv (i, a)) ∈
      (R.result n).parentBlocks i := by
  rw [R.fixedCanonicalClusterEquiv_finProdFinEquiv]
  exact ((R.result n).childEquiv i (R.fixedChildIndexEquiv n a)).property

/-- A fixed cluster index belongs to parent block `i` exactly when its first
canonical coordinate is `i`. -/
theorem fixedCanonicalClusterEquiv_mem_parentBlock_iff
    (n : ℕ) (x : Fin (s * R.childCount)) (i : Fin s) :
    R.fixedCanonicalClusterEquiv n x ∈ (R.result n).parentBlocks i ↔
      (finProdFinEquiv.symm x).1 = i := by
  change (R.result n).canonicalClusterEquiv
      (R.fixedCanonicalIndexEquiv n x) ∈ (R.result n).parentBlocks i ↔ _
  rw [(R.result n).canonicalClusterEquiv_mem_parentBlock_iff]
  let ia := finProdFinEquiv.symm x
  have hx : finProdFinEquiv ia = x := finProdFinEquiv.apply_symm_apply x
  rcases ia with ⟨j, a⟩
  subst x
  simp

/-- The `n`th Type, reindexed on the row-independent cluster type
`Fin (s * R.childCount)`. -/
noncomputable def fixedCanonicalType (n : ℕ) :=
  (R.result n).regularityType.reindexClusters
    (R.fixedCanonicalClusterEquiv n)

@[simp] theorem fixedCanonicalType_clusterCount (n : ℕ) :
    (R.fixedCanonicalType n).partition.clusterCount = s * R.childCount :=
  rfl

@[simp] theorem fixedCanonicalType_clusters
    (n : ℕ) (x : Fin (s * R.childCount)) :
    (R.fixedCanonicalType n).partition.clusters x =
      (R.result n).regularityType.partition.clusters
        (R.fixedCanonicalClusterEquiv n x) :=
  rfl

@[simp] theorem fixedCanonicalType_cluster_finProdFinEquiv
    (n : ℕ) (i : Fin s) (a : Fin R.childCount) :
    (R.fixedCanonicalType n).partition.clusters
        (finProdFinEquiv (i, a)) =
      (R.result n).regularityType.partition.clusters
        ((R.result n).childEquiv i (R.fixedChildIndexEquiv n a)) := by
  rw [R.fixedCanonicalType_clusters,
    R.fixedCanonicalClusterEquiv_finProdFinEquiv]

/-- Every fixed canonical child remains inside its prescribed parent part. -/
theorem fixedCanonicalType_cluster_subset_parent
    (n : ℕ) (i : Fin s) (a : Fin R.childCount) :
    (R.fixedCanonicalType n).partition.clusters
        (finProdFinEquiv (i, a)) ⊆
      (parent.partition (R.factor n)).parts i := by
  rw [R.fixedCanonicalType_cluster_finProdFinEquiv]
  exact (R.result n).cluster_subset_initial i
    ((R.result n).childEquiv i (R.fixedChildIndexEquiv n a))
    ((R.result n).childEquiv i (R.fixedChildIndexEquiv n a)).property

/-- Density entries of the fixed Type are the old cluster densities selected
by the fixed canonical equivalence. -/
@[simp] theorem typeDensityMatrix_fixedCanonicalType
    (n : ℕ) (x y : Fin (s * R.childCount)) :
    typeDensityMatrix (R.fixedCanonicalType n) x y =
      graphDensity (G (parent.extraction (R.factor n)))
        ((R.result n).regularityType.partition.clusters
          (R.fixedCanonicalClusterEquiv n x))
        ((R.result n).regularityType.partition.clusters
          (R.fixedCanonicalClusterEquiv n y)) :=
  rfl

/-- The fixed density matrix is the native canonical density matrix after
the coordinate-preserving child-count cast. -/
theorem typeDensityMatrix_fixedCanonicalType_eq_canonicalType
    (n : ℕ) (x y : Fin (s * R.childCount)) :
    typeDensityMatrix (R.fixedCanonicalType n) x y =
      typeDensityMatrix (R.result n).canonicalType
        (R.fixedCanonicalIndexEquiv n x)
        (R.fixedCanonicalIndexEquiv n y) :=
  rfl

/-- Parent/child-coordinate form of the fixed density matrix. -/
@[simp] theorem typeDensityMatrix_fixedCanonicalType_finProdFinEquiv
    (n : ℕ) (i j : Fin s) (a b : Fin R.childCount) :
    typeDensityMatrix (R.fixedCanonicalType n)
        (finProdFinEquiv (i, a)) (finProdFinEquiv (j, b)) =
      graphDensity (G (parent.extraction (R.factor n)))
        ((R.result n).regularityType.partition.clusters
          ((R.result n).childEquiv i (R.fixedChildIndexEquiv n a)))
        ((R.result n).regularityType.partition.clusters
          ((R.result n).childEquiv j (R.fixedChildIndexEquiv n b))) := by
  change graphDensity (G (parent.extraction (R.factor n)))
      ((R.fixedCanonicalType n).partition.clusters
        (finProdFinEquiv (i, a)))
      ((R.fixedCanonicalType n).partition.clusters
        (finProdFinEquiv (j, b))) = _
  rw [R.fixedCanonicalType_cluster_finProdFinEquiv,
    R.fixedCanonicalType_cluster_finProdFinEquiv]

end TypeLemmaRowResult

end InducedStars
