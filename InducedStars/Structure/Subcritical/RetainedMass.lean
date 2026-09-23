import InducedStars.Structure.Subcritical.RetainedDivision
import InducedStars.Structure.Subcritical.ReferenceConvergence
import InducedStars.Graphon.Counting

/-!
# Ordered mass of retained and residual candidate cells

Exact finite cell sums are kept separate from the division constructor, so
their limits also cover an empty retained set and early empty sampled cells.
-/

noncomputable section

open Filter Finset Set
open scoped BigOperators Classical Topology

namespace InducedStars

variable {k n : ℕ} (L : AdmissibleBlockSequence k)

private theorem referenceCells_disjoint (i : ℕ) :
    (Set.univ : Set (Fin (L.core i).order)).PairwiseDisjoint
      (subcriticalReferenceCellVertices L n i) := by
  intro v _ w _ hvw
  exact subcriticalReferenceCellVertices_disjoint_of_ne L hvw

private theorem referenceCellUnion_subset_block (i : ℕ) :
    (Finset.univ.biUnion (subcriticalReferenceCellVertices L n i)) ⊆
      subcriticalReferenceBlockVertices L n i := by
  intro x hx
  obtain ⟨v, _, hxv⟩ := Finset.mem_biUnion.mp hx
  exact subcriticalReferenceCellVertices_subset_blockVertices L v hxv

private theorem referenceCellUnions_disjoint :
    (Set.univ : Set ℕ).PairwiseDisjoint
      (fun i ↦ Finset.univ.biUnion (subcriticalReferenceCellVertices L n i)) := by
  intro i _ j _ hij
  exact (subcriticalReferenceBlockVertices_disjoint L hij).mono
    (referenceCellUnion_subset_block L i) (referenceCellUnion_subset_block L j)

/-- Exact finite row mass at a vertex in a literal core cell. -/
theorem subcriticalReference_row_sum_of_mem_cell (hk : 3 ≤ k)
    (i : ℕ) (v : Fin (L.core i).order) {x : Fin n}
    (hx : x ∈ subcriticalReferenceCellVertices L n i v) :
    (∑ y, (subcriticalReferenceWeightedGraph hk L n).weight x y) =
      ∑ w : Fin (L.core i).order,
        (subcriticalReferenceCellVertices L n i w).card *
          profileXiMatrix (pK k) (L.core i) v w := by
  let U := Finset.univ.biUnion (subcriticalReferenceCellVertices L n i)
  have hrestrict :
      (∑ y ∈ U, (subcriticalReferenceWeightedGraph hk L n).weight x y) =
        ∑ y, (subcriticalReferenceWeightedGraph hk L n).weight x y := by
    apply Finset.sum_subset (Finset.subset_univ U)
    intro y _ hy
    apply subcriticalReference_weight_zero_of_retained_sparse L {i} hk
    · exact mem_subcriticalRetainedCellSupport.mpr ⟨i, by simp, v, hx⟩
    · simpa [subcriticalRetainedCellSupport, U] using hy
  rw [← hrestrict]
  change (∑ y ∈ Finset.univ.biUnion (subcriticalReferenceCellVertices L n i), _) = _
  rw [Finset.sum_biUnion]
  · apply Finset.sum_congr rfl
    intro w _
    calc
      (∑ y ∈ subcriticalReferenceCellVertices L n i w,
          (subcriticalReferenceWeightedGraph hk L n).weight x y) =
          ∑ _y ∈ subcriticalReferenceCellVertices L n i w,
            profileXiMatrix (pK k) (L.core i) v w := by
        apply Finset.sum_congr rfl
        intro y hy
        exact subcriticalReferenceWeightedGraph_weight_of_mem_cells hk L v w hx hy
      _ = _ := by simp
  · simpa using referenceCells_disjoint (n := n) L i

/-- Exact expansion of all reference rows belonging to retained cells. -/
theorem subcriticalReference_retained_sum_eq (hk : 3 ≤ k) (I : Finset ℕ) :
    (∑ x ∈ subcriticalRetainedCellSupport L n I,
      ∑ y, (subcriticalReferenceWeightedGraph hk L n).weight x y) =
      ∑ i ∈ I, ∑ v : Fin (L.core i).order, ∑ w : Fin (L.core i).order,
        (subcriticalReferenceCellVertices L n i v).card *
          (subcriticalReferenceCellVertices L n i w).card *
            profileXiMatrix (pK k) (L.core i) v w := by
  unfold subcriticalRetainedCellSupport
  rw [Finset.sum_biUnion]
  · apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_biUnion]
    · apply Finset.sum_congr rfl
      intro v _
      calc
        (∑ x ∈ subcriticalReferenceCellVertices L n i v,
            ∑ y, (subcriticalReferenceWeightedGraph hk L n).weight x y) =
            ∑ _x ∈ subcriticalReferenceCellVertices L n i v,
              ∑ w : Fin (L.core i).order,
                (subcriticalReferenceCellVertices L n i w).card *
                  profileXiMatrix (pK k) (L.core i) v w := by
          apply Finset.sum_congr rfl
          intro x hx
          exact subcriticalReference_row_sum_of_mem_cell L hk i v hx
        _ = _ := by
          simp only [Finset.sum_const, nsmul_eq_mul, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro w _
          ring
    · simpa using referenceCells_disjoint (n := n) L i
  · intro i _ j _ hij
    exact referenceCellUnions_disjoint L (Set.mem_univ _) (Set.mem_univ _) hij

/-- Ordered weight in the residual rows of the full sampled reference. -/
def subcriticalReferenceResidualOrderedWeight (hk : 3 ≤ k) (n : ℕ) (I : Finset ℕ) : ℝ :=
  ∑ x ∈ Finset.univ \ subcriticalRetainedCellSupport L n I,
    ∑ y, (subcriticalReferenceWeightedGraph hk L n).weight x y

theorem subcriticalReference_residual_add_retained (hk : 3 ≤ k) (I : Finset ℕ) :
    subcriticalReferenceResidualOrderedWeight L hk n I +
      (∑ x ∈ subcriticalRetainedCellSupport L n I,
        ∑ y, (subcriticalReferenceWeightedGraph hk L n).weight x y) =
      ∑ x, ∑ y, (subcriticalReferenceWeightedGraph hk L n).weight x y := by
  unfold subcriticalReferenceResidualOrderedWeight
  exact Finset.sum_sdiff (Finset.subset_univ _)

theorem subcriticalReference_retained_sum_div_eq (hk : 3 ≤ k) (I : Finset ℕ) :
    (∑ x ∈ subcriticalRetainedCellSupport L n I,
      ∑ y, (subcriticalReferenceWeightedGraph hk L n).weight x y) / (n : ℝ) ^ 2 =
      ∑ i ∈ I, ∑ v : Fin (L.core i).order, ∑ w : Fin (L.core i).order,
        ((subcriticalReferenceCellVertices L n i v).card / (n : ℝ)) *
          ((subcriticalReferenceCellVertices L n i w).card / (n : ℝ)) *
            profileXiMatrix (pK k) (L.core i) v w := by
  rw [subcriticalReference_retained_sum_eq]
  simp only [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro v _
  apply Finset.sum_congr rfl
  intro w _
  simp only [div_pow, div_eq_mul_inv, inv_pow]
  ring

set_option backward.isDefEq.respectTransparency false in
private theorem retainedMass_coefficient (i : ℕ) :
    (∑ v : Fin (L.core i).order, ∑ w : Fin (L.core i).order,
      (L.alpha i / (L.core i).order) * (L.alpha i / (L.core i).order) *
        profileXiMatrix (pK k) (L.core i) v w) =
      (1 + ((k - 2 : ℕ) : ℝ) * pK k) * L.massTerm i := by
  simp_rw [← Finset.mul_sum]
  rw [sum_profileXiMatrix]
  unfold AdmissibleBlockSequence.massTerm
  have hq : ((L.core i).order : ℝ) ≠ 0 := by exact_mod_cast (L.core i).order_pos.ne'
  field_simp [hq]

/-- Finite retained blocks have their exact continuum ordered mass.  Empty
retained sets and early empty cells are included. -/
theorem tendsto_subcriticalReference_retained_sum_div (hk : 3 ≤ k) (I : Finset ℕ) :
    Tendsto (fun n ↦
      (∑ x ∈ subcriticalRetainedCellSupport L n I,
        ∑ y, (subcriticalReferenceWeightedGraph hk L n).weight x y) / (n : ℝ) ^ 2)
      atTop (nhds ((1 + ((k - 2 : ℕ) : ℝ) * pK k) * ∑ i ∈ I, L.massTerm i)) := by
  have ht := tendsto_finset_sum I fun i _ ↦
    tendsto_finset_sum Finset.univ fun v _ ↦
      tendsto_finset_sum Finset.univ fun w _ ↦
        ((tendsto_card_subcriticalReferenceCellVertices_div L v).mul
          (tendsto_card_subcriticalReferenceCellVertices_div L w)).mul_const
            (profileXiMatrix (pK k) (L.core i) v w)
  have hlimit :
      (∑ i ∈ I, ∑ v : Fin (L.core i).order, ∑ w : Fin (L.core i).order,
        (L.alpha i / (L.core i).order) * (L.alpha i / (L.core i).order) *
          profileXiMatrix (pK k) (L.core i) v w) =
        (1 + ((k - 2 : ℕ) : ℝ) * pK k) * ∑ i ∈ I, L.massTerm i := by
    simp_rw [retainedMass_coefficient]
    rw [Finset.mul_sum]
  rw [hlimit] at ht
  exact ht.congr' (Eventually.of_forall fun n ↦
    (subcriticalReference_retained_sum_div_eq L hk I).symm)

theorem subcritical_mass_sub_retained_eq (I : Finset ℕ) :
    L.mass - ∑ i ∈ I, L.massTerm i =
      ∑' i : ℕ, if i ∈ I then 0 else L.massTerm i := by
  have hsplit := L.summable_massTerm.sum_add_tsum_compl (s := I)
  rw [_root_.tsum_subtype] at hsplit
  have hterms : (fun i ↦ ((↑I : Set ℕ)ᶜ).indicator L.massTerm i) =
      fun i ↦ if i ∈ I then 0 else L.massTerm i := by
    funext i
    by_cases hi : i ∈ I <;> simp [hi]
  rw [hterms] at hsplit
  unfold AdmissibleBlockSequence.mass
  linarith

private theorem reference_density_eq_sum_div (hk : 3 ≤ k) (hn : 0 < n) :
    graphonEdgeDensity (subcriticalReferenceGraphon hk L n) =
      (∑ x, ∑ y, (subcriticalReferenceWeightedGraph hk L n).weight x y) / (n : ℝ) ^ 2 := by
  unfold subcriticalReferenceGraphon DenseGraph.FiniteWeightedGraph.toGraphon
  rw [graphonEdgeDensity_matrixGraphon hn]
  simp only [one_div, div_eq_mul_inv, inv_pow]
  ring

/-- The actual residual ordered mass converges to the mass of the omitted
candidate blocks, not merely to an unspecified upper bound. -/
theorem tendsto_subcriticalReferenceResidualOrderedWeight_div
    (hk : 3 ≤ k) (I : Finset ℕ) :
    Tendsto (fun n ↦ subcriticalReferenceResidualOrderedWeight L hk n I / (n : ℝ) ^ 2)
      atTop (nhds ((1 + ((k - 2 : ℕ) : ℝ) * pK k) *
        ∑' i : ℕ, if i ∈ I then 0 else L.massTerm i)) := by
  have htotal := graphonEdgeDensity_tendsto_of_cutDist_tendsto_zero
    (fun n ↦ subcriticalReferenceGraphon hk L n) (WLambda hk L)
    (subcriticalReferenceGraphon_tendsto_WLambda hk L)
  have hretained := tendsto_subcriticalReference_retained_sum_div L hk I
  have ht := htotal.sub hretained
  have hlimit : graphonEdgeDensity (WLambda hk L) -
      (1 + ((k - 2 : ℕ) : ℝ) * pK k) * ∑ i ∈ I, L.massTerm i =
      (1 + ((k - 2 : ℕ) : ℝ) * pK k) *
        ∑' i : ℕ, if i ∈ I then 0 else L.massTerm i := by
    rw [show graphonEdgeDensity (WLambda hk L) =
      (1 + ((k - 2 : ℕ) : ℝ) * pK k) * L.mass from L.graphon_edgeDensity hk]
    rw [← mul_sub, subcritical_mass_sub_retained_eq]
  rw [hlimit] at ht
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  rw [reference_density_eq_sum_div L hk hn,
    ← subcriticalReference_residual_add_retained L hk I, add_div]
  ring

/-- Uniform eventual residual weight bound; the finite threshold may
depend on the candidate representation, but the coefficient does not. -/
theorem eventually_subcriticalReferenceResidualOrderedWeight_le
    (hk : 3 ≤ k) (I : Finset ℕ) {eta : ℝ} (heta : 0 < eta)
    {R : ℕ} (hR : 0 < R)
    (homitted : ∀ i ∉ I, L.alpha i < eta ∨ R < (L.core i).order) :
    ∀ᶠ n in atTop, subcriticalReferenceResidualOrderedWeight L hk n I ≤
      2 * (1 + ((k - 2 : ℕ) : ℝ) * pK k) * (eta + 1 / (R : ℝ)) * (n : ℝ) ^ 2 := by
  let c : ℝ := 1 + ((k - 2 : ℕ) : ℝ) * pK k
  have hc : 0 < c := by
    dsimp [c]
    have hp := (pK_pos (by omega : 2 ≤ k)).le
    positivity
  have hband : 0 < eta + 1 / (R : ℝ) := by positivity
  have hbound := mul_le_mul_of_nonneg_left
    (subcriticalDiscardedMass_le L I heta.le hR homitted) hc.le
  have hstrict : c * (∑' i : ℕ, if i ∈ I then 0 else L.massTerm i) <
      2 * c * (eta + 1 / (R : ℝ)) := by
    have hp := mul_pos hc hband
    nlinarith
  have ht := tendsto_subcriticalReferenceResidualOrderedWeight_div L hk I
  have he := ht.eventually (gt_mem_nhds hstrict)
  filter_upwards [he, eventually_gt_atTop (0 : ℕ)] with n hn hnpos
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
  exact (div_le_iff₀ (sq_pos_of_pos hnR)).mp hn.le

/-- The finite range in the retained-index definition loses no block
above the positive mass cutoff. -/
theorem subcriticalRetainedBlockIndices_omitted {eta : ℝ} (heta : 0 < eta)
    (R i : ℕ) (hi : i ∉ subcriticalRetainedBlockIndices L eta R) :
    L.alpha i < eta ∨ R < (L.core i).order := by
  by_cases hlarge : eta ≤ L.alpha i
  · right
    by_contra hR
    apply hi
    rw [mem_subcriticalRetainedBlockIndices]
    refine ⟨?_, hlarge, Nat.le_of_not_gt hR⟩
    by_contra hirange
    have hceil : Nat.ceil (1 / eta) ≤ i := Nat.le_of_not_gt hirange
    have hiR : (1 / eta : ℝ) ≤ i :=
      (Nat.le_ceil (1 / eta)).trans (by exact_mod_cast hceil)
    have hprod : (1 : ℝ) ≤ i * eta := (div_le_iff₀ heta).mp hiR
    have hir : (0 : ℝ) < ((i + 1 : ℕ) : ℝ) := by positivity
    have hsmall : 1 / ((i + 1 : ℕ) : ℝ) < eta := by
      apply (div_lt_iff₀ hir).mpr
      push_cast
      nlinarith
    exact (not_lt_of_ge hlarge) ((L.alpha_le_inv_succ i).trans_lt hsmall)
  · exact Or.inl (lt_of_not_ge hlarge)

theorem eventually_subcriticalReferenceRetainedResidual_le
    (hk : 3 ≤ k) {eta : ℝ} (heta : 0 < eta) {R : ℕ} (hR : 0 < R) :
    ∀ᶠ n in atTop, subcriticalReferenceResidualOrderedWeight L hk n
        (subcriticalRetainedBlockIndices L eta R) ≤
      2 * (1 + ((k - 2 : ℕ) : ℝ) * pK k) * (eta + 1 / (R : ℝ)) * (n : ℝ) ^ 2 :=
  eventually_subcriticalReferenceResidualOrderedWeight_le L hk _ heta hR
    (subcriticalRetainedBlockIndices_omitted L heta R)

/-- One threshold makes every cell of every retained component nonempty. -/
theorem eventually_subcriticalReferenceRetainedCells_nonempty
    {eta : ℝ} (heta : 0 < eta) (R : ℕ) :
    ∀ᶠ n in atTop, ∀ i ∈ subcriticalRetainedBlockIndices L eta R,
      ∀ v, (subcriticalReferenceCellVertices L n i v).Nonempty := by
  apply (Filter.eventually_all_finset _).mpr
  intro i hi
  apply Filter.eventually_all.mpr
  intro v
  exact eventually_subcriticalReferenceCellVertices_nonempty L
    (heta.trans_le (mem_subcriticalRetainedBlockIndices.mp hi).2.1) v

theorem subcriticalRetainedDivision_uniform_card_partIndex
    {eta : ℝ} (heta : 0 < eta) (R : ℕ)
    (hI : (subcriticalRetainedBlockIndices L eta R).Nonempty)
    (hcells : ∀ i ∈ subcriticalRetainedBlockIndices L eta R, ∀ v,
      (subcriticalReferenceCellVertices L n i v).Nonempty) :
    Fintype.card (subcriticalRetainedDivision L _ hI hcells).PartIndex ≤
      Nat.ceil (1 / eta) * R := by
  apply (subcriticalRetainedDivision_card_partIndex_le L _ hI hcells R
    (fun i hi ↦ (mem_subcriticalRetainedBlockIndices.mp hi).2.2)).trans
  apply Nat.mul_le_mul_right
  exact subcriticalRetained_card_le_ceil_inv L _ heta
    (fun i hi ↦ (mem_subcriticalRetainedBlockIndices.mp hi).2.1)

end InducedStars
