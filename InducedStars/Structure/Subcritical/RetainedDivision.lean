import InducedStars.Structure.Subcritical.Reference
import InducedStars.Structure.Subcritical.Compatibility

/-!
# Divisions carried by retained candidate cells

The full finite reference is aligned before selecting these components.
This file retains an arbitrary nonempty finite set of literal candidate
blocks, assuming their sampled cells are nonempty.  Its division agrees
exactly with the reference on all pairs incident with the retained support;
the residual square is deliberately left to the analytic tail estimate.
-/

noncomputable section

open Finset Set
open scoped BigOperators Classical

namespace InducedStars

/-- Enumerate a finite set of original candidate labels without identifying
their regular cores only up to isomorphism. -/
def subcriticalRetainedIndexEquiv (I : Finset ℕ) :
    Fin I.card ≃ {i // i ∈ I} :=
  (Fintype.equivFinOfCardEq (by simp : Fintype.card {i // i ∈ I} = I.card)).symm

/-- Explicit-order spelling of the shared retained vertex set. -/
abbrev subcriticalRetainedCellSupport {k : ℕ} (L : AdmissibleBlockSequence k)
    (n : ℕ) (I : Finset ℕ) : Finset (Fin n) :=
  I.biUnion fun i ↦ Finset.univ.biUnion (subcriticalReferenceCellVertices L n i)

@[simp] theorem mem_subcriticalRetainedCellSupport {k n : ℕ}
    {L : AdmissibleBlockSequence k} {I : Finset ℕ} {x : Fin n} :
    x ∈ subcriticalRetainedCellSupport L n I ↔
      ∃ i ∈ I, ∃ v, x ∈ subcriticalReferenceCellVertices L n i v := by
  simp [subcriticalRetainedCellSupport]

/-- The literal retained-cell division.  It has no equitability hypothesis;
all finite rounding error remains visible in the actual part sizes. -/
def subcriticalRetainedDivision {k n : ℕ} (L : AdmissibleBlockSequence k)
    (I : Finset ℕ) (hI : I.Nonempty)
    (hcells : ∀ i ∈ I, ∀ v, (subcriticalReferenceCellVertices L n i v).Nonempty) :
    SubcriticalDivision k (Fin n) where
  componentCount := I.card
  componentCount_pos := hI.card_pos
  core a := L.core (subcriticalRetainedIndexEquiv I a).val
  parts a v := subcriticalReferenceCellVertices L n
    (subcriticalRetainedIndexEquiv I a).val v
  parts_nonempty a v := hcells _ (subcriticalRetainedIndexEquiv I a).property v
  parts_pairwiseDisjoint := by
    intro a _ b _ hab
    by_cases hi : a.1 = b.1
    · rcases a with ⟨i, a⟩
      rcases b with ⟨j, b⟩
      dsimp at hi
      subst j
      exact subcriticalReferenceCellVertices_disjoint_of_ne L (by simpa using hab)
    · apply Finset.disjoint_of_subset_left
        (subcriticalReferenceCellVertices_subset_blockVertices L a.2)
      apply Finset.disjoint_of_subset_right
        (subcriticalReferenceCellVertices_subset_blockVertices L b.2)
      apply subcriticalReferenceBlockVertices_disjoint L
      intro h
      exact hi ((subcriticalRetainedIndexEquiv I).injective (Subtype.ext h))

variable {k n : ℕ} (L : AdmissibleBlockSequence k) (I : Finset ℕ)
  (hI : I.Nonempty)
  (hcells : ∀ i ∈ I, ∀ v, (subcriticalReferenceCellVertices L n i v).Nonempty)

@[simp] theorem subcriticalRetainedDivision_support :
    (subcriticalRetainedDivision L I hI hcells).support =
      subcriticalRetainedCellSupport L n I := by
  ext x
  rw [SubcriticalDivision.mem_support_iff, mem_subcriticalRetainedCellSupport]
  constructor
  · rintro ⟨i, v, hx⟩
    exact ⟨_, (subcriticalRetainedIndexEquiv I i).property, v, hx⟩
  · rintro ⟨i, hi, v, hx⟩
    obtain ⟨a, ha⟩ := (subcriticalRetainedIndexEquiv I).surjective ⟨i, hi⟩
    have hv := congrArg Subtype.val ha
    refine ⟨a, ?_⟩
    change ∃ w, x ∈ subcriticalReferenceCellVertices L n
      (subcriticalRetainedIndexEquiv I a).val w
    rw [hv]
    exact ⟨v, hx⟩

@[simp] theorem subcriticalRetainedDivision_sparse :
    (subcriticalRetainedDivision L I hI hcells).sparse =
      Finset.univ \ subcriticalRetainedCellSupport L n I := by
  simp [SubcriticalDivision.sparse]

theorem subcriticalRetainedDivision_card_partIndex :
    Fintype.card (subcriticalRetainedDivision L I hI hcells).PartIndex =
      ∑ i ∈ I, (L.core i).order := by
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin]
  change (∑ i : Fin I.card, (L.core (subcriticalRetainedIndexEquiv I i).val).order) = _
  rw [Equiv.sum_comp (subcriticalRetainedIndexEquiv I)
    (fun i : {i // i ∈ I} ↦ (L.core i.val).order)]
  simp
  exact Finset.sum_attach I (fun i ↦ (L.core i).order)

theorem subcriticalRetainedDivision_card_partIndex_le (R : ℕ)
    (hR : ∀ i ∈ I, (L.core i).order ≤ R) :
    Fintype.card (subcriticalRetainedDivision L I hI hcells).PartIndex ≤ I.card * R := by
  rw [subcriticalRetainedDivision_card_partIndex]
  calc
    ∑ i ∈ I, (L.core i).order ≤ ∑ _i ∈ I, R := Finset.sum_le_sum hR
    _ = I.card * R := by simp

/-- Exact agreement on any two retained cells, even from different cores. -/
theorem subcriticalRetainedDivision_weight_eq_reference_of_mem_support
    (hk : 3 ≤ k) {x y : Fin n}
    (hx : x ∈ (subcriticalRetainedDivision L I hI hcells).support)
    (hy : y ∈ (subcriticalRetainedDivision L I hI hcells).support) :
    (subcriticalDivisionWeightedGraph hk (subcriticalRetainedDivision L I hI hcells)).weight x y =
      (subcriticalReferenceWeightedGraph hk L n).weight x y := by
  let D := subcriticalRetainedDivision L I hI hcells
  obtain ⟨a, hxa⟩ := SubcriticalDivision.mem_support.mp hx
  obtain ⟨b, hyb⟩ := SubcriticalDivision.mem_support.mp hy
  by_cases hi : a.1 = b.1
  · rcases a with ⟨i, a⟩
    rcases b with ⟨j, b⟩
    dsimp at hi
    subst j
    rw [subcriticalDivisionWeightedGraph_weight_of_mem_parts hk D hxa hyb]
    rw [subcriticalReferenceWeightedGraph_weight_of_mem_cells hk L a b hxa hyb]
    simp only [Sigma.mk.inj_iff, heq_eq_eq, true_and,
      SubcriticalDivision.activePart_mk_mk, profileXiMatrix]
    rfl
  · rw [subcriticalDivisionWeightedGraph_weight_of_distinct_components hk D hi hxa hyb]
    symm
    apply subcriticalReferenceWeightedGraph_weight_of_mem_distinct_blocks hk L
      (i := (subcriticalRetainedIndexEquiv I a.1).val)
      (j := (subcriticalRetainedIndexEquiv I b.1).val)
    · intro h
      exact hi ((subcriticalRetainedIndexEquiv I).injective (Subtype.ext h))
    · exact subcriticalReferenceCellVertices_subset_blockVertices L a.2 hxa
    · exact subcriticalReferenceCellVertices_subset_blockVertices L b.2 hyb

/-- The full reference has no edges from retained cells to their residual.
The proof uses the finite core-cell sum, so it does not silently replace a
pointwise statement by almost-everywhere coverage. -/
theorem subcriticalReference_weight_zero_of_retained_sparse
    (hk : 3 ≤ k) {x y : Fin n}
    (hx : x ∈ subcriticalRetainedCellSupport L n I)
    (hy : y ∉ subcriticalRetainedCellSupport L n I) :
    (subcriticalReferenceWeightedGraph hk L n).weight x y = 0 := by
  obtain ⟨i, hi, v, hxv⟩ := mem_subcriticalRetainedCellSupport.mp hx
  have hycell (w : Fin (L.core i).order) :
      subcriticalReferenceSamplePoint y ∉ L.blockCell i w := by
    intro hw
    exact hy (mem_subcriticalRetainedCellSupport.mpr
      ⟨i, hi, w, mem_subcriticalReferenceCellVertices.mpr hw⟩)
  change L.profileKernel (pK k)
    (subcriticalReferenceSamplePoint x, subcriticalReferenceSamplePoint y) = 0
  rw [AdmissibleBlockSequence.profileKernel,
    L.kernel_eq_blockKernel_of_mem i _
      (L.blockCell_subset_interval i v (mem_subcriticalReferenceCellVertices.mp hxv))]
  have hb : L.blockKernel i
      (subcriticalReferenceSamplePoint x, subcriticalReferenceSamplePoint y) = 0 := by
    unfold AdmissibleBlockSequence.blockKernel
    apply Finset.sum_eq_zero
    intro a _
    apply Finset.sum_eq_zero
    intro b _
    apply Set.indicator_of_notMem
    exact fun h ↦ hycell b h.2
  rw [hb, profileRecolor_zero]

/-- Exact reference agreement everywhere outside the residual square. -/
theorem subcriticalRetainedDivision_weight_eq_reference_of_support_incident
    (hk : 3 ≤ k) {x y : Fin n}
    (h : x ∈ (subcriticalRetainedDivision L I hI hcells).support ∨
      y ∈ (subcriticalRetainedDivision L I hI hcells).support) :
    (subcriticalDivisionWeightedGraph hk (subcriticalRetainedDivision L I hI hcells)).weight x y =
      (subcriticalReferenceWeightedGraph hk L n).weight x y := by
  have left {x y : Fin n}
      (hx : x ∈ (subcriticalRetainedDivision L I hI hcells).support) :
      (subcriticalDivisionWeightedGraph hk (subcriticalRetainedDivision L I hI hcells)).weight x y =
        (subcriticalReferenceWeightedGraph hk L n).weight x y := by
    by_cases hy : y ∈ (subcriticalRetainedDivision L I hI hcells).support
    · exact subcriticalRetainedDivision_weight_eq_reference_of_mem_support L I hI hcells hk hx hy
    · rw [subcriticalDivisionWeightedGraph_weight_of_sparse_right hk _
        (SubcriticalDivision.mem_sparse.mpr hy)]
      symm
      apply subcriticalReference_weight_zero_of_retained_sparse L I hk
      · simpa using hx
      · simpa using hy
  rcases h with hx | hy
  · exact left hx
  · rw [(subcriticalDivisionWeightedGraph hk _).symmetric,
      (subcriticalReferenceWeightedGraph hk L n).symmetric]
    exact left hy

/-- Transporting the retained division uses the same actual permutation
as the aligned reference. -/
theorem subcriticalRetainedDivision_relabel_weight_eq_reference
    (hk : 3 ≤ k) (e : Equiv.Perm (Fin n)) {x y : Fin n}
    (h : e x ∈ (subcriticalRetainedDivision L I hI hcells).support ∨
      e y ∈ (subcriticalRetainedDivision L I hI hcells).support) :
    (subcriticalDivisionWeightedGraph hk
      ((subcriticalRetainedDivision L I hI hcells).relabel e.symm)).weight x y =
      ((subcriticalReferenceWeightedGraph hk L n).permute e).weight x y := by
  rw [subcriticalDivisionWeightedGraph_relabel_symm]
  exact subcriticalRetainedDivision_weight_eq_reference_of_support_incident L I hI hcells hk h

/-- The residual ordered weight uses actual vertex relabeling, not an
equivariance assertion about canonical choices. -/
theorem subcritical_sparse_weight_sum_relabel
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SubcriticalDivision k V) (A : DenseGraph.FiniteWeightedGraph V)
    (e : Equiv.Perm V) :
    (∑ x ∈ (D.relabel e.symm).sparse, ∑ y, (A.permute e).weight x y) =
      ∑ x ∈ D.sparse, ∑ y, A.weight x y := by
  calc
    (∑ x ∈ (D.relabel e.symm).sparse, ∑ y, (A.permute e).weight x y) =
        ∑ x ∈ (D.relabel e.symm).sparse, ∑ y, A.weight (e x) y := by
      apply Finset.sum_congr rfl
      intro x _
      exact Equiv.sum_comp e (fun y ↦ A.weight (e x) y)
    _ = ∑ x ∈ D.sparse, ∑ y, A.weight x y := by
      apply Finset.sum_equiv e
      · intro x
        rw [SubcriticalDivision.mem_relabel_sparse]
        rfl
      · intro x _
        rfl

/-! ## Uniform retained complexity and discarded continuum mass -/

/-- There are uniformly few blocks above a fixed positive length cutoff. -/
theorem subcriticalRetained_card_le_ceil_inv {eta : ℝ} (heta : 0 < eta)
    (hlarge : ∀ i ∈ I, eta ≤ L.alpha i) : I.card ≤ Nat.ceil (1 / eta) := by
  have hsum : (I.card : ℝ) * eta ≤ 1 := by
    calc
      (I.card : ℝ) * eta = ∑ _i ∈ I, eta := by simp
      _ ≤ ∑ i ∈ I, L.alpha i := Finset.sum_le_sum hlarge
      _ ≤ ∑' i, L.alpha i := L.summable_alpha.sum_le_tsum I
        (fun i _ ↦ L.alpha_nonneg i)
      _ ≤ 1 := L.tsum_alpha_le_one
  have hcard := (le_div_iff₀ heta).mpr hsum
  exact_mod_cast hcard.trans (Nat.le_ceil (1 / eta))

/-- Crude uniform mass control for all omitted blocks: small blocks cost
at most `eta`, and high-order blocks at most `1/R`. -/
theorem subcriticalDiscardedMass_le {eta : ℝ} (heta : 0 ≤ eta)
    {R : ℕ} (hR : 0 < R)
    (homitted : ∀ i ∉ I, L.alpha i < eta ∨ R < (L.core i).order) :
    (∑' i : ℕ, if i ∈ I then 0 else L.massTerm i) ≤ eta + 1 / (R : ℝ) := by
  let f : ℕ → ℝ := fun i ↦ if i ∈ I then 0 else L.massTerm i
  have hRr : (0 : ℝ) < R := by exact_mod_cast hR
  have hcoef : 0 ≤ eta + 1 / (R : ℝ) := by positivity
  have hf_nonneg (i : ℕ) : 0 ≤ f i := by
    dsimp [f]
    split_ifs
    · exact le_rfl
    · exact L.massTerm_nonneg i
  have hf_le (i : ℕ) : f i ≤ (eta + 1 / (R : ℝ)) * L.alpha i := by
    by_cases hi : i ∈ I
    · simp only [f, hi, ite_true]
      exact mul_nonneg hcoef (L.alpha_nonneg i)
    · simp only [f, hi, ite_false]
      rcases homitted i hi with ha | hq
      · calc
          L.massTerm i ≤ L.alpha i ^ 2 :=
            div_le_self (sq_nonneg _) (by exact_mod_cast (L.core i).order_pos)
          _ ≤ eta * L.alpha i := by nlinarith [L.alpha_nonneg i]
          _ ≤ (eta + 1 / (R : ℝ)) * L.alpha i :=
            mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (by positivity))
              (L.alpha_nonneg i)
      · have hqr : (R : ℝ) ≤ (L.core i).order := by exact_mod_cast hq.le
        calc
          L.massTerm i ≤ L.alpha i ^ 2 / R :=
            div_le_div_of_nonneg_left (sq_nonneg _) hRr hqr
          _ ≤ L.alpha i / R := by
            apply div_le_div_of_nonneg_right _ hRr.le
            nlinarith [L.alpha_nonneg i, L.alpha_le_one i]
          _ ≤ (eta + 1 / (R : ℝ)) * L.alpha i := by
            rw [div_eq_mul_one_div, mul_comm (L.alpha i)]
            exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_left heta)
              (L.alpha_nonneg i)
  have hsum : Summable f := Summable.of_nonneg_of_le hf_nonneg hf_le
    (L.summable_alpha.mul_left _)
  calc
    (∑' i, f i) ≤ ∑' i, (eta + 1 / (R : ℝ)) * L.alpha i :=
      hsum.tsum_le_tsum hf_le (L.summable_alpha.mul_left _)
    _ = (eta + 1 / (R : ℝ)) * ∑' i, L.alpha i := tsum_mul_left
    _ ≤ (eta + 1 / (R : ℝ)) * 1 :=
      mul_le_mul_of_nonneg_left L.tsum_alpha_le_one hcoef
    _ = eta + 1 / (R : ℝ) := mul_one _

end InducedStars
