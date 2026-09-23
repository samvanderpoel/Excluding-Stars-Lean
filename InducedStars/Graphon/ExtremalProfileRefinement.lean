import InducedStars.Graphon.BlockEqualization
import Mathlib.Tactic

/-!
# The ambient profile on the common core refinement

This module compares the uniform fine-cell refinement of an exact extremal
coloring's profile matrix with the sparse matrix obtained by summing its
literal reduced-core profiles.  The two matrices agree away from diagonal
coarse cells belonging to uncovered ambient vertices.  Consequently their
ordered entrywise discrepancy is at most `q * P^2`, where `P` is the common
refinement factor.
-/

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace InducedStars

open ColoredGraph

namespace FiniteExtremalBlockModel

variable {k q : ℕ} {C : ColoredGraph (Fin q)}
    (M : FiniteExtremalBlockModel k q C)

/-- The profile matrix of the ambient coloring, uniformly copied to the
common fine-cell refinement. -/
def refinedProfileColorMatrix (p : ℝ) :
    Matrix (Fin M.refinementOrder) (Fin M.refinementOrder) ℝ :=
  typeUniformRefinementMatrix (n := M.refinementFactor)
    (profileColorMatrix p C)

theorem refinedProfileColorMatrix_isSymm (p : ℝ) :
    (M.refinedProfileColorMatrix p).IsSymm :=
  typeUniformRefinementMatrix_isSymm
    (profileColorMatrix_isSymm p C)

theorem refinedProfileColorMatrix_nonneg {p : ℝ} (hp : 0 ≤ p) :
    ∀ x y, 0 ≤ M.refinedProfileColorMatrix p x y :=
  typeUniformRefinementMatrix_nonneg
    (profileColorMatrix_nonneg C hp)

theorem refinedProfileColorMatrix_le_one {p : ℝ} (hp : p ≤ 1) :
    ∀ x y, M.refinedProfileColorMatrix p x y ≤ 1 :=
  typeUniformRefinementMatrix_le_one
    (profileColorMatrix_le_one C hp)

@[simp] theorem refinedProfileColorMatrix_apply (p : ℝ)
    (x y : Fin M.refinementOrder) :
    M.refinedProfileColorMatrix p x y =
      profileColorMatrix p C (M.refinedCoarseVertex x)
        (M.refinedCoarseVertex y) := by
  rfl

/-- On two literal clusters of the same exact component, the ambient color
profile is exactly the corresponding reduced-core profile value. -/
theorem profileColorMatrix_eq_profileXiMatrix_of_mem_orderedAmbientCluster
    (p : ℝ) (a : Fin M.componentCount)
    {i j : Fin (M.orderedCore a).order} {x y : Fin q}
    (hx : x ∈ M.orderedAmbientCluster a i)
    (hy : y ∈ M.orderedAmbientCluster a j) :
    profileColorMatrix p C x y =
      profileXiMatrix p (M.orderedCore a) i j := by
  by_cases hij : i = j
  · subst j
    rw [profileXiMatrix_apply_eq]
    by_cases hxy : x = y
    · subst y
      exact profileColorMatrix_diagonal p C x
    · have hblue : C.color x y = .blue := by
        apply M.witness.ambientCoreCluster_internalBlue
          (M.orderedIndex a) i
        · simpa [orderedAmbientCluster] using hx
        · simpa [orderedAmbientCluster] using hy
        · exact hxy
      simp [profileColorMatrix, hblue]
  · by_cases hadj : (M.orderedCore a).graph.Adj i j
    · rw [profileXiMatrix_apply_of_adj p (M.orderedCore a) hadj]
      have hadj' :
          (M.witness.coreRegular (M.orderedIndex a)).reducedGraph.Adj i j := by
        exact hadj
      have hred : C.color x y = .red := by
        apply M.witness.ambientCoreCluster_redBetween
          (M.orderedIndex a) hadj'
        · simpa [orderedAmbientCluster] using hx
        · simpa [orderedAmbientCluster] using hy
      simp [profileColorMatrix, hred]
    · rw [profileXiMatrix_apply_of_ne_of_not_adj p (M.orderedCore a)
        hij hadj]
      have hnadj' :
          ¬ (M.witness.coreRegular
            (M.orderedIndex a)).reducedGraph.Adj i j := by
        exact hadj
      have hgreen : C.color x y = .green := by
        apply M.witness.ambientCoreCluster_greenBetween
          (M.orderedIndex a) hij hnadj'
        · simpa [orderedAmbientCluster] using hx
        · simpa [orderedAmbientCluster] using hy
      simp [profileColorMatrix, hgreen]

/-- Exact evaluation of the literal refined-core sum when both fine cells
belong to specified clusters of one component. -/
theorem refinedExtremalCoreMatrix_eq_profileXiMatrix_of_mem
    (p : ℝ) (a : Fin M.componentCount)
    {i j : Fin (M.orderedCore a).order}
    {x y : Fin M.refinementOrder}
    (hx : x ∈ M.refinedCoreCluster a i)
    (hy : y ∈ M.refinedCoreCluster a j) :
    M.refinedExtremalCoreMatrix p x y =
      profileXiMatrix p (M.orderedCore a) i j := by
  classical
  have hxa : x ∈ clusterUnion (M.refinedCoreCluster a) :=
    mem_clusterUnion_iff.mpr ⟨i, hx⟩
  rw [refinedExtremalCoreMatrix, Matrix.sum_apply,
    Finset.sum_eq_single a]
  · apply clusterProfileMatrix_of_mem
    · intro u _ v _ huv
      exact disjoint_uniformRefinementFinset
        (M.orderedAmbientCluster_pairwiseDisjoint a
          (Set.mem_univ u) (Set.mem_univ v) huv)
    · exact hx
    · exact hy
  · intro b _ hba
    apply clusterProfileMatrix_eq_zero_of_not_mem
    intro hxb
    exact Finset.disjoint_left.mp
      (M.refinedCoreSupports_pairwiseDisjoint
        (Set.mem_univ a) (Set.mem_univ b) hba.symm) hxa hxb
  · simp

/-- If no exact component contains both coarse endpoints, the literal
refined-core sum vanishes. -/
theorem refinedExtremalCoreMatrix_eq_zero_of_no_common_core
    (p : ℝ) {x y : Fin M.refinementOrder}
    (hnone : ∀ a : Fin M.componentCount,
      ¬ (M.refinedCoarseVertex x ∈
          M.witness.coreVertices (M.orderedIndex a) ∧
        M.refinedCoarseVertex y ∈
          M.witness.coreVertices (M.orderedIndex a))) :
    M.refinedExtremalCoreMatrix p x y = 0 := by
  classical
  rw [refinedExtremalCoreMatrix, Matrix.sum_apply]
  apply Finset.sum_eq_zero
  intro a _
  by_cases hx : M.refinedCoarseVertex x ∈
      M.witness.coreVertices (M.orderedIndex a)
  · have hy : M.refinedCoarseVertex y ∉
        M.witness.coreVertices (M.orderedIndex a) :=
      fun hy ↦ hnone a ⟨hx, hy⟩
    have hy' : y ∉ clusterUnion (M.refinedCoreCluster a) := by
      simpa [M.refinedCoarseVertex_mem_core_iff a y] using hy
    calc
      clusterProfileMatrix p (M.orderedCore a)
          (M.refinedCoreCluster a) x y =
          clusterProfileMatrix p (M.orderedCore a)
            (M.refinedCoreCluster a) y x := by
            exact (Matrix.IsSymm.apply
              (clusterProfileMatrix_isSymm p (M.orderedCore a)
                (M.refinedCoreCluster a)) x y).symm
      _ = 0 := clusterProfileMatrix_eq_zero_of_not_mem
        p (M.orderedCore a) (M.refinedCoreCluster a) hy'
  · have hx' : x ∉ clusterUnion (M.refinedCoreCluster a) := by
      simpa [M.refinedCoarseVertex_mem_core_iff a x] using hx
    exact clusterProfileMatrix_eq_zero_of_not_mem
      p (M.orderedCore a) (M.refinedCoreCluster a) hx'

/-- The uniformly refined ambient profile and the literal refined-core
profile agree everywhere except possibly on a diagonal coarse cell whose
ambient vertex lies outside every exact core support. -/
theorem refinedProfileColorMatrix_eq_refinedExtremalCoreMatrix_of_not_uncoveredDiagonal
    (p : ℝ) {x y : Fin M.refinementOrder}
    (hgood : ¬ (M.refinedCoarseVertex x = M.refinedCoarseVertex y ∧
      M.refinedCoarseVertex x ∈ M.witness.uncoveredVertices)) :
    M.refinedProfileColorMatrix p x y =
      M.refinedExtremalCoreMatrix p x y := by
  classical
  let u := M.refinedCoarseVertex x
  let v := M.refinedCoarseVertex y
  by_cases hcommon : ∃ a : Fin M.componentCount,
      u ∈ M.witness.coreVertices (M.orderedIndex a) ∧
        v ∈ M.witness.coreVertices (M.orderedIndex a)
  · obtain ⟨a, hua, hva⟩ := hcommon
    have huUnion : u ∈ clusterUnion (M.orderedAmbientCluster a) := by
      rw [M.orderedAmbientCluster_cover a]
      exact hua
    have hvUnion : v ∈ clusterUnion (M.orderedAmbientCluster a) := by
      rw [M.orderedAmbientCluster_cover a]
      exact hva
    rw [mem_clusterUnion_iff] at huUnion hvUnion
    obtain ⟨i, hui⟩ := huUnion
    obtain ⟨j, hvj⟩ := hvUnion
    have hxi : x ∈ M.refinedCoreCluster a i := by
      rw [M.mem_refinedCoreCluster_iff a i x]
      exact hui
    have hyj : y ∈ M.refinedCoreCluster a j := by
      rw [M.mem_refinedCoreCluster_iff a j y]
      exact hvj
    calc
      M.refinedProfileColorMatrix p x y =
          profileXiMatrix p (M.orderedCore a) i j := by
            rw [M.refinedProfileColorMatrix_apply]
            exact M.profileColorMatrix_eq_profileXiMatrix_of_mem_orderedAmbientCluster
              p a hui hvj
      _ = M.refinedExtremalCoreMatrix p x y :=
        (M.refinedExtremalCoreMatrix_eq_profileXiMatrix_of_mem
          p a hxi hyj).symm
  · have huv : u ≠ v := by
      intro huv
      have huNone : ∀ a : Fin M.componentCount,
          u ∉ M.witness.coreVertices (M.orderedIndex a) := by
        intro a hua
        exact hcommon ⟨a, hua, by simpa [huv] using hua⟩
      have huUncovered : u ∈ M.witness.uncoveredVertices :=
        (M.not_exists_orderedIndex_mem_iff_uncovered u).mp (by
          simpa only [not_exists] using huNone)
      exact hgood ⟨huv, huUncovered⟩
    have hgreen : C.color u v = .green := by
      apply M.witness.offCoreGreen u v huv
      intro b hb
      obtain ⟨a, ha⟩ := M.componentOrder.surjective b
      have hindex : M.orderedIndex a = b := by
        change M.witness.componentOrder a = b
        change M.witness.componentOrder a = b at ha
        exact ha
      apply hcommon
      refine ⟨a, ?_, ?_⟩
      · simpa [hindex] using hb.1
      · simpa [hindex] using hb.2
    have hzero := M.refinedExtremalCoreMatrix_eq_zero_of_no_common_core
      p (x := x) (y := y) (by
        intro a ha
        exact hcommon ⟨a, by simpa only [u, v] using ha⟩)
    rw [M.refinedProfileColorMatrix_apply, hzero]
    simpa [profileColorMatrix, u, v, hgreen]

/-- A pointwise discrepancy can occur only when the two fine cells refine
the same coarse ambient vertex. -/
theorem abs_refinedProfileColorMatrix_sub_refinedExtremalCoreMatrix_le
    {p : ℝ} (hp : p ∈ Set.Icc (0 : ℝ) 1)
    (x y : Fin M.refinementOrder) :
    |M.refinedProfileColorMatrix p x y -
        M.refinedExtremalCoreMatrix p x y| ≤
      if M.refinedCoarseVertex x = M.refinedCoarseVertex y
      then (1 : ℝ) else 0 := by
  by_cases hxy : M.refinedCoarseVertex x = M.refinedCoarseVertex y
  · simp only [hxy, ↓reduceIte]
    rw [abs_le]
    have hA0 := M.refinedProfileColorMatrix_nonneg hp.1 x y
    have hA1 := M.refinedProfileColorMatrix_le_one hp.2 x y
    have hB0 := M.refinedExtremalCoreMatrix_nonneg hp.1 x y
    have hB1 := M.refinedExtremalCoreMatrix_le_one hp.2 x y
    constructor <;> linarith
  · have heq :=
      M.refinedProfileColorMatrix_eq_refinedExtremalCoreMatrix_of_not_uncoveredDiagonal
        p (x := x) (y := y) (by simp [hxy])
    rw [heq, sub_self, abs_zero]
    simp [hxy]

/-- There are exactly `q * P²` ordered pairs of fine cells whose two
coordinates refine the same coarse ambient vertex. -/
theorem sum_refinedCoarseVertex_eq_indicator :
    (∑ x : Fin M.refinementOrder, ∑ y : Fin M.refinementOrder,
      if M.refinedCoarseVertex x = M.refinedCoarseVertex y
      then (1 : ℝ) else 0) =
      ((q * M.refinementFactor ^ 2 : ℕ) : ℝ) := by
  classical
  unfold refinementOrder refinedCoarseVertex
  rw [← Equiv.sum_comp (typeFineCellEquiv q M.refinementFactor)]
  simp_rw [Equiv.symm_apply_apply]
  rw [show ((q * M.refinementFactor ^ 2 : ℕ) : ℝ) =
      ∑ _x : Fin q × Fin M.refinementFactor,
        (M.refinementFactor : ℝ) by
    simp [pow_two]
    ring]
  apply Fintype.sum_congr
  intro x
  rw [← Equiv.sum_comp (typeFineCellEquiv q M.refinementFactor)]
  simp_rw [Equiv.symm_apply_apply]
  rw [Fintype.sum_prod_type]
  calc
    (∑ a : Fin q, ∑ _b : Fin M.refinementFactor,
        if x.1 = a then (1 : ℝ) else 0) =
        ∑ a : Fin q,
          if x.1 = a then (M.refinementFactor : ℝ) else 0 := by
      apply Fintype.sum_congr
      intro a
      by_cases ha : x.1 = a <;> simp [ha]
    _ = (M.refinementFactor : ℝ) := by
      simpa using Fintype.sum_ite_eq x.1
        (fun _ : Fin q ↦ (M.refinementFactor : ℝ))

/-- The ambient-profile-to-literal-core discrepancy costs at most the
`q` exceptional coarse diagonal cells, each containing `P²` fine pairs. -/
theorem sum_abs_refinedProfileColorMatrix_refinedExtremalCoreMatrix_le
    {p : ℝ} (hp : p ∈ Set.Icc (0 : ℝ) 1) :
    (∑ x : Fin M.refinementOrder, ∑ y : Fin M.refinementOrder,
      |M.refinedProfileColorMatrix p x y -
        M.refinedExtremalCoreMatrix p x y|) ≤
      ((q * M.refinementFactor ^ 2 : ℕ) : ℝ) := by
  calc
    (∑ x : Fin M.refinementOrder, ∑ y : Fin M.refinementOrder,
      |M.refinedProfileColorMatrix p x y -
        M.refinedExtremalCoreMatrix p x y|) ≤
        ∑ x : Fin M.refinementOrder, ∑ y : Fin M.refinementOrder,
          if M.refinedCoarseVertex x = M.refinedCoarseVertex y
          then (1 : ℝ) else 0 := by
      apply Finset.sum_le_sum
      intro x _
      apply Finset.sum_le_sum
      intro y _
      exact M.abs_refinedProfileColorMatrix_sub_refinedExtremalCoreMatrix_le
        hp x y
    _ = ((q * M.refinementFactor ^ 2 : ℕ) : ℝ) :=
      M.sum_refinedCoarseVertex_eq_indicator

/-! ## Matrix-graphon consequences -/

/-- Matrix graphon of the uniformly refined ambient profile. -/
def refinedProfileColorGraphon (p : ℝ) (hp : p ∈ Set.Icc (0 : ℝ) 1) :
    Graphon :=
  matrixGraphon (M.refinedProfileColorMatrix p)
    (M.refinedProfileColorMatrix_isSymm p)
    (M.refinedProfileColorMatrix_nonneg hp.1)
    (M.refinedProfileColorMatrix_le_one hp.2)

/-- Matrix graphon of the literal, not-yet-equalized component profiles. -/
def refinedExtremalCoreGraphon (p : ℝ) (hp : p ∈ Set.Icc (0 : ℝ) 1) :
    Graphon :=
  matrixGraphon (M.refinedExtremalCoreMatrix p)
    (M.refinedExtremalCoreMatrix_isSymm p)
    (M.refinedExtremalCoreMatrix_nonneg hp.1)
    (M.refinedExtremalCoreMatrix_le_one hp.2)

/-- Uniform copying of the ambient profile matrix leaves its matrix graphon
literally unchanged. -/
theorem refinedProfileColorGraphon_eq_profileColoringGraphon
    (p : ℝ) (hp : p ∈ Set.Icc (0 : ℝ) 1) :
    M.refinedProfileColorGraphon p hp = profileColoringGraphon p C hp := by
  simpa [refinedProfileColorGraphon, refinedProfileColorMatrix,
    refinementOrder, profileColoringGraphon] using
    (matrixGraphon_typeUniformRefinement_eq M.ambientOrder_pos
      M.refinementFactor_pos (profileColorMatrix p C)
      (profileColorMatrix_isSymm p C)
      (profileColorMatrix_nonneg C hp.1)
      (profileColorMatrix_le_one C hp.2))

/-- The literal refined-core graphon is within `1/q` in `L¹` of the
uniformly refined ambient profile. -/
theorem graphonL1Dist_refinedProfileColorGraphon_refinedExtremalCoreGraphon_le
    {p : ℝ} (hp : p ∈ Set.Icc (0 : ℝ) 1) :
    graphonL1Dist (M.refinedProfileColorGraphon p hp)
        (M.refinedExtremalCoreGraphon p hp) ≤ 1 / (q : ℝ) := by
  unfold refinedProfileColorGraphon refinedExtremalCoreGraphon
  rw [graphonL1Dist_matrixGraphon_eq_entrySum M.refinementOrder_pos
    (M.refinedProfileColorMatrix p) (M.refinedExtremalCoreMatrix p)
    (M.refinedProfileColorMatrix_isSymm p)
    (M.refinedExtremalCoreMatrix_isSymm p)
    (M.refinedProfileColorMatrix_nonneg hp.1)
    (M.refinedProfileColorMatrix_le_one hp.2)
    (M.refinedExtremalCoreMatrix_nonneg hp.1)
    (M.refinedExtremalCoreMatrix_le_one hp.2)]
  calc
    (1 / (M.refinementOrder : ℝ)) ^ 2 *
        ∑ x : Fin M.refinementOrder, ∑ y : Fin M.refinementOrder,
          |M.refinedProfileColorMatrix p x y -
            M.refinedExtremalCoreMatrix p x y| ≤
        (1 / (M.refinementOrder : ℝ)) ^ 2 *
          ((q * M.refinementFactor ^ 2 : ℕ) : ℝ) := by
      exact mul_le_mul_of_nonneg_left
        (M.sum_abs_refinedProfileColorMatrix_refinedExtremalCoreMatrix_le hp)
        (sq_nonneg _)
    _ = 1 / (q : ℝ) := by
      have hq : (q : ℝ) ≠ 0 := by
        exact_mod_cast (ne_of_gt M.ambientOrder_pos)
      have hP : (M.refinementFactor : ℝ) ≠ 0 := by
        exact_mod_cast (ne_of_gt M.refinementFactor_pos)
      unfold refinementOrder
      push_cast
      field_simp

/-- Coordinate-free spelling of the preceding estimate: the original
ambient coloring profile is within `1/q` of the literal refined-core
matrix graphon. -/
theorem graphonL1Dist_profileColoringGraphon_refinedExtremalCoreGraphon_le
    {p : ℝ} (hp : p ∈ Set.Icc (0 : ℝ) 1) :
    graphonL1Dist (profileColoringGraphon p C hp)
        (M.refinedExtremalCoreGraphon p hp) ≤ 1 / (q : ℝ) := by
  rw [← M.refinedProfileColorGraphon_eq_profileColoringGraphon p hp]
  exact M.graphonL1Dist_refinedProfileColorGraphon_refinedExtremalCoreGraphon_le
    hp

end FiniteExtremalBlockModel

end InducedStars
