import InducedStars.Structure.Critical.FiniteGeometry
import InducedStars.FiniteModels.CoMultipartiteStar

/-!
# The induced-free condition in a fixed-sparse reference fiber

A displayed zero-defect division is a disjoint union of its co-multipartite
support and its sparse induced graph.  An induced star cannot straddle those
two components, and the support already excludes the star.  Consequently
fixing one induced-star-free sparse graph leaves every admissible choice of
cross coordinates available.  No factor counting arbitrary sparse graphs is
introduced into the fine-balance comparison.
-/

noncomputable section

namespace InducedStars

variable {k : ℕ} {V : Type*} [Fintype V] [DecidableEq V]

/-- All induced stars of a clean displayed graph lie in its sparse induced
component: the complementary component is co-`(k-1)`-partite. -/
theorem inducedEmbeds_inducedStar_iff_sparse_of_clean
    (hk : 1 ≤ k) (G : SimpleGraph V) (D : SupercriticalDivision k V)
    (hclean : supercriticalDefectGraph G D = ⊥) :
    Regularity.InducedEmbeds (inducedStar k) G ↔
      Regularity.InducedEmbeds (inducedStar k)
        (G.induce (D.sparse : Set V)) := by
  constructor
  · rintro ⟨f⟩
    by_cases hcenter : f 0 ∈ D.sparse
    · have hvertices : ∀ v : Fin (k + 1), f v ∈ D.sparse := by
        intro v
        by_cases hv : v = 0
        · simpa [hv] using hcenter
        · by_contra hnot
          have hsupp : f v ∈ D.support := by simpa using hnot
          exact (not_adj_support_sparse_of_supercriticalDefectGraph_eq_bot
            G D hclean hsupp hcenter)
              (f.map_rel_iff.mpr (inducedStar_center_adj_of_ne hv)).symm
      refine ⟨{
        toFun := fun v ↦ ⟨f v, hvertices v⟩
        inj' := ?_
        map_rel_iff' := ?_ }⟩
      · intro v w h
        exact f.injective (congrArg Subtype.val h)
      · intro v w
        exact f.map_rel_iff
    · have hsupp : f 0 ∈ D.support := by simpa using hcenter
      have hvertices : ∀ v : Fin (k + 1), f v ∉ D.sparse := by
        intro v
        by_cases hv : v = 0
        · simpa [hv] using hcenter
        · intro hvsparse
          exact (not_adj_support_sparse_of_supercriticalDefectGraph_eq_bot
            G D hclean hsupp hvsparse)
              (f.map_rel_iff.mpr (inducedStar_center_adj_of_ne hv))
      have hcore : Regularity.InducedEmbeds (inducedStar k)
          (G.induce ({v : V | v ∉ D.sparse} : Set V)) := by
        refine ⟨{
          toFun := fun v ↦ ⟨f v, hvertices v⟩
          inj' := ?_
          map_rel_iff' := ?_ }⟩
        · intro v w h
          exact f.injective (congrArg Subtype.val h)
        · intro v w
          exact f.map_rel_iff
      exact False.elim
        (coMultipartite_not_inducedEmbeds_inducedStar hk
          (criticalCore_isCoMultipartite_of_defectGraph_eq_bot G D hclean) hcore)
  · rintro ⟨f⟩
    refine ⟨{
      toFun := fun v ↦ (f v).1
      inj' := ?_
      map_rel_iff' := ?_ }⟩
    · intro v w h
      exact f.injective (Subtype.ext h)
    · intro v w
      exact f.map_rel_iff

/-- Every clean realization of one fixed induced-star-free sparse graph is
induced-star-free, independently of its retained cross-edge choices. -/
theorem not_inducedEmbeds_inducedStar_of_clean_of_sparse_free
    (hk : 1 ≤ k) (G : SimpleGraph V) (D : SupercriticalDivision k V)
    (hclean : supercriticalDefectGraph G D = ⊥)
    (hsparse : ¬ Regularity.InducedEmbeds (inducedStar k)
      (G.induce (D.sparse : Set V))) :
    ¬ Regularity.InducedEmbeds (inducedStar k) G :=
  fun h ↦ hsparse ((inducedEmbeds_inducedStar_iff_sparse_of_clean hk G D hclean).mp h)

end InducedStars
