import InducedStars.Structure.Subcritical.AlignmentWitness
import InducedStars.Structure.Subcritical.AlignmentBalance
import InducedStars.Structure.Subcritical.VisibleCut

/-!
# Finite consequences of an explicit subcritical component alignment

This file turns a constructed `SubcriticalComponentAlignment` into the two
finite estimates used by the subcritical bridge: density control on arbitrary
large subsets of two visible parts, and same-label cut control after restricting
to any finite family of visible parts.  Every good set comes from the same
candidate sequence and the same vertex permutation.
-/

noncomputable section

open Finset Set DenseGraph DenseGraph.FiniteWeightedGraph
open scoped BigOperators Classical

namespace InducedStars

universe u

variable {k n : ℕ}

namespace SubcriticalDivision

/-- Raising the visibility threshold can only remove visible components. -/
theorem visibleComponentIndices_mono
    (D : SubcriticalDivision k (Fin n)) {t theta : ℝ}
    (hcutoff : t ≤ theta) :
    D.visibleComponentIndices theta ⊆ D.visibleComponentIndices t := by
  intro i hi
  obtain ⟨v, hv⟩ := (D.mem_visibleComponentIndices theta i).mp hi
  simp only [Fintype.card_fin] at hv
  apply (D.mem_visibleComponentIndices t i).mpr
  refine ⟨v, ?_⟩
  simpa only [Fintype.card_fin] using
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    (mul_le_mul_of_nonneg_right hcutoff hn).trans hv

/-- Raising the visibility threshold can only remove visible parts. -/
theorem visiblePartIndices_mono
    (D : SubcriticalDivision k (Fin n)) {t theta : ℝ}
    (hcutoff : t ≤ theta) :
    D.visiblePartIndices theta ⊆ D.visiblePartIndices t := by
  intro a ha
  exact (D.mem_visiblePartIndices t a).mpr
    (D.visibleComponentIndices_mono hcutoff
      ((D.mem_visiblePartIndices theta a).mp ha))

/-- The identity embedding of visible parts from a higher cutoff into a lower
cutoff. -/
def visiblePartEmbeddingAtLowerCutoff
    (D : SubcriticalDivision k (Fin n)) {t theta : ℝ}
    (hcutoff : t ≤ theta) :
    {a : D.PartIndex // a ∈ D.visiblePartIndices theta} ↪
      {a : D.PartIndex // a ∈ D.visiblePartIndices t} where
  toFun a := ⟨a.val, D.visiblePartIndices_mono hcutoff a.property⟩
  inj' a b h := by
    apply Subtype.ext
    exact congrArg
      (fun z : {a : D.PartIndex // a ∈ D.visiblePartIndices t} ↦ z.val) h

@[simp] theorem visiblePartEmbeddingAtLowerCutoff_val
    (D : SubcriticalDivision k (Fin n)) {t theta : ℝ}
    (hcutoff : t ≤ theta)
    (a : {a : D.PartIndex // a ∈ D.visiblePartIndices theta}) :
    (D.visiblePartEmbeddingAtLowerCutoff hcutoff a).val = a.val := rfl

end SubcriticalDivision

/-- The palette value prescribed by a division on a pair of its parts. -/
def subcriticalDivisionPartWeight
    (D : SubcriticalDivision k (Fin n)) (a b : D.PartIndex) : ℝ :=
  if a = b then 1 else if D.ActivePart a b then pK k else 0

theorem subcriticalDivisionWeightedGraph_weight_eq_partWeight
    (hk : 3 ≤ k) (D : SubcriticalDivision k (Fin n))
    {a b : D.PartIndex} {x y : Fin n}
    (hx : x ∈ D.part a) (hy : y ∈ D.part b) :
    (subcriticalDivisionWeightedGraph hk D).weight x y =
      subcriticalDivisionPartWeight D a b := by
  simpa only [subcriticalDivisionPartWeight] using
    subcriticalDivisionWeightedGraph_weight_of_mem_parts hk D hx hy

namespace SubcriticalComponentAlignment

variable {D : SubcriticalDivision k (Fin n)}
  {L : AdmissibleBlockSequence k} {pi : Equiv.Perm (Fin n)}
  {t m : ℝ} {B : ℕ}

/-- A part visible at the paper cutoff, regarded as a part visible at the
possibly smaller construction cutoff. -/
abbrev lowerCutoffPart
    (A : SubcriticalComponentAlignment D L pi t m B)
    {theta : ℝ} (hcutoff : t ≤ theta)
    (a : {a : D.PartIndex // a ∈ D.visiblePartIndices theta}) :
    {a : D.PartIndex // a ∈ D.visiblePartIndices t} :=
  D.visiblePartEmbeddingAtLowerCutoff hcutoff a

/-- The good portion of an arbitrary subset of a visible part. -/
def subsetGoodVertices
    (A : SubcriticalComponentAlignment D L pi t m B)
    {theta : ℝ} (hcutoff : t ≤ theta)
    (a : {a : D.PartIndex // a ∈ D.visiblePartIndices theta})
    (X : Finset (Fin n)) : Finset (Fin n) :=
  X ∩ A.goodVertices (A.lowerCutoffPart hcutoff a)

theorem subsetGoodVertices_subset
    (A : SubcriticalComponentAlignment D L pi t m B)
    {theta : ℝ} (hcutoff : t ≤ theta)
    (a : {a : D.PartIndex // a ∈ D.visiblePartIndices theta})
    (X : Finset (Fin n)) :
    A.subsetGoodVertices hcutoff a X ⊆ X := Finset.inter_subset_left

theorem subset_sdiff_subsetGoodVertices_card_le
    (A : SubcriticalComponentAlignment D L pi t m B)
    {theta error : ℝ} (hcutoff : t ≤ theta)
    (a : {a : D.PartIndex // a ∈ D.visiblePartIndices theta})
    (X : Finset (Fin n)) (hX : X ⊆ D.part a.val)
    (hm : m ≤ error * n) :
    ((X \ A.subsetGoodVertices hcutoff a X).card : ℝ) ≤ error * n := by
  have hsub : X \ A.subsetGoodVertices hcutoff a X ⊆
      D.part (A.lowerCutoffPart hcutoff a).val \
        A.goodVertices (A.lowerCutoffPart hcutoff a) := by
    intro x hx
    have hxX := (Finset.mem_sdiff.mp hx).1
    have hxNot := (Finset.mem_sdiff.mp hx).2
    refine Finset.mem_sdiff.mpr ⟨hX hxX, ?_⟩
    intro hxGood
    exact hxNot (Finset.mem_inter.mpr ⟨hxX, hxGood⟩)
  have hcard : ((X \ A.subsetGoodVertices hcutoff a X).card : ℝ) ≤
      ((D.part (A.lowerCutoffPart hcutoff a).val \
        A.goodVertices (A.lowerCutoffPart hcutoff a)).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  exact hcard.trans ((A.card_part_sdiff_goodVertices_le
    (A.lowerCutoffPart hcutoff a)).trans hm)

/-- Density on arbitrary disjoint large subsets of two visible division
parts is close to the division's exact palette value. -/
theorem abs_graphDensity_sub_partWeight_le
    (hk : 3 ≤ k) (hn : 0 < n)
    (A : SubcriticalComponentAlignment D L pi t m B)
    (G : SimpleGraph (Fin n))
    {theta alpha beta error : ℝ}
    (hcutoff : t ≤ theta) (htheta : 0 < theta) (halpha : 0 < alpha)
    (hbeta : 0 ≤ beta) (herror : 0 ≤ error)
    (hm : m ≤ error * n)
    (hcut : finiteLabeledCutDist (ofSimpleGraph G)
      ((subcriticalReferenceWeightedGraph hk L n).permute pi) ≤ beta)
    (a b : {a : D.PartIndex // a ∈ D.visiblePartIndices theta})
    (X Y : Finset (Fin n)) (hXY : Disjoint X Y)
    (hX : X ⊆ D.part a.val) (hY : Y ⊆ D.part b.val)
    (hXsize : alpha * theta * n / 4 ≤ (X.card : ℝ))
    (hYsize : alpha * theta * n / 4 ≤ (Y.card : ℝ)) :
    |Regularity.graphDensity G X Y -
        subcriticalDivisionPartWeight D a.val b.val| ≤
      beta / (alpha * theta / 4) ^ 2 +
        2 * error / (alpha * theta / 4) := by
  let a0 : ℝ := alpha * theta / 4
  let Xgood := A.subsetGoodVertices hcutoff a X
  let Ygood := A.subsetGoodVertices hcutoff b Y
  have ha0 : 0 < a0 := by positivity
  have hV : 0 < Fintype.card (Fin n) := by simpa using hn
  have hXgood : Xgood ⊆ X := A.subsetGoodVertices_subset hcutoff a X
  have hYgood : Ygood ⊆ Y := A.subsetGoodVertices_subset hcutoff b Y
  have hXloss : ((X \ Xgood).card : ℝ) ≤ error * Fintype.card (Fin n) := by
    simpa [Xgood] using A.subset_sdiff_subsetGoodVertices_card_le
      hcutoff a X hX hm
  have hYloss : ((Y \ Ygood).card : ℝ) ≤ error * Fintype.card (Fin n) := by
    simpa [Ygood] using A.subset_sdiff_subsetGoodVertices_card_le
      hcutoff b Y hY hm
  have hagree : ∀ x ∈ Xgood, ∀ y ∈ Ygood,
      ((subcriticalReferenceWeightedGraph hk L n).permute pi).weight x y =
        subcriticalDivisionPartWeight D a.val b.val := by
    intro x hx y hy
    have hxA : x ∈ A.goodVertices (A.lowerCutoffPart hcutoff a) :=
      (Finset.mem_inter.mp hx).2
    have hyA : y ∈ A.goodVertices (A.lowerCutoffPart hcutoff b) :=
      (Finset.mem_inter.mp hy).2
    calc
      ((subcriticalReferenceWeightedGraph hk L n).permute pi).weight x y =
          (subcriticalDivisionWeightedGraph hk D).weight x y :=
        A.reference_weight_eq_divisionWeight_of_mem_goodVertices hk
          (A.lowerCutoffPart hcutoff a) (A.lowerCutoffPart hcutoff b) hxA hyA
      _ = subcriticalDivisionPartWeight D a.val b.val :=
        subcriticalDivisionWeightedGraph_weight_eq_partWeight hk D
          (hX (Finset.mem_inter.mp hx).1) (hY (Finset.mem_inter.mp hy).1)
  have hw0 : 0 ≤ subcriticalDivisionPartWeight D a.val b.val := by
    simp only [subcriticalDivisionPartWeight]
    split_ifs
    · norm_num
    · exact (pK_mem_Icc k).1
    · norm_num
  have hw1 : subcriticalDivisionPartWeight D a.val b.val ≤ 1 := by
    simp only [subcriticalDivisionPartWeight]
    split_ifs
    · norm_num
    · exact (pK_mem_Icc k).2
    · norm_num
  have hbase := abs_graphDensity_sub_constant_le_of_referenceAgreement
    G ((subcriticalReferenceWeightedGraph hk L n).permute pi)
    X Y Xgood Ygood hXY hw0 hw1 hbeta herror ha0 hV hXgood hYgood
    (by
      have : a0 * n ≤ (X.card : ℝ) := by dsimp [a0]; nlinarith
      simpa only [Fintype.card_fin] using this)
    (by
      have : a0 * n ≤ (Y.card : ℝ) := by dsimp [a0]; nlinarith
      simpa only [Fintype.card_fin] using this)
    hXloss hYloss hagree hcut
  simpa only [a0] using hbase

section FiniteFamily

variable {I : Type u} [Fintype I] [DecidableEq I]

/-- The selected subsets of a finite injected family of visible parts. -/
abbrev selectedVisiblePartUnion
    {theta : ℝ}
    (partIndex : I ↪ {a : D.PartIndex // a ∈ D.visiblePartIndices theta})
    (part : I → Finset (Fin n)) : Finset (Fin n) :=
  visibleCutPartUnion part

/-- Same-label cut control on the union of arbitrary large subsets of any
finite injected family of visible parts. -/
theorem selectedVisibleParts_restrictedLabeledCutDist_le
    (hk : 3 ≤ k)
    (A : SubcriticalComponentAlignment D L pi t m B)
    (G : SimpleGraph (Fin n))
    {theta beta error a0 : ℝ}
    (hcutoff : t ≤ theta) (hbeta : 0 ≤ beta)
    (herror : 0 ≤ error) (ha0 : 0 < a0)
    (hm : m ≤ error * n)
    (hcut : finiteLabeledCutDist (ofSimpleGraph G)
      ((subcriticalReferenceWeightedGraph hk L n).permute pi) ≤ beta)
    (partIndex : I ↪ {a : D.PartIndex // a ∈ D.visiblePartIndices theta})
    (part : I → Finset (Fin n))
    (hpart : ∀ q, part q ⊆ D.part (partIndex q).val)
    (hsize : ∀ q, a0 * n ≤ ((part q).card : ℝ)) :
    finiteLabeledCutDist
        ((ofSimpleGraph G).restrictToFinset (visibleCutPartUnion part))
        ((subcriticalDivisionWeightedGraph hk D).restrictToFinset
          (visibleCutPartUnion part)) ≤
      beta / a0 ^ 2 + 2 * error / a0 := by
  let lowerPart (q : I) := A.lowerCutoffPart hcutoff (partIndex q)
  let good (q : I) := part q ∩ A.goodVertices (lowerPart q)
  have hdisjoint : Set.PairwiseDisjoint (Set.univ : Set I) part := by
    intro q _ r _ hqr
    have hindex : (partIndex q).val ≠ (partIndex r).val := by
      intro h
      apply hqr
      apply partIndex.injective
      exact Subtype.ext h
    exact (D.part_disjoint hindex).mono (hpart q) (hpart r)
  have hgood : ∀ q, good q ⊆ part q := fun _ ↦ Finset.inter_subset_left
  have hloss : ∀ q, (((part q \ good q).card : ℕ) : ℝ) ≤
      error * Fintype.card (Fin n) := by
    intro q
    simpa only [good, lowerPart, subsetGoodVertices,
      Finset.sdiff_inter_self_left, Fintype.card_fin] using
      A.subset_sdiff_subsetGoodVertices_card_le hcutoff (partIndex q)
        (part q) (hpart q) hm
  have hagree : ∀ x ∈ visibleCutGoodUnion good,
      ∀ y ∈ visibleCutGoodUnion good,
        ((subcriticalReferenceWeightedGraph hk L n).permute pi).weight x y =
          (subcriticalDivisionWeightedGraph hk D).weight x y := by
    intro x hx y hy
    obtain ⟨q, _, hxq⟩ := Finset.mem_biUnion.mp hx
    obtain ⟨r, _, hyr⟩ := Finset.mem_biUnion.mp hy
    exact A.reference_weight_eq_divisionWeight_of_mem_goodVertices hk
      (lowerPart q) (lowerPart r) (Finset.mem_inter.mp hxq).2
      (Finset.mem_inter.mp hyr).2
  apply visibleParts_restrictedLabeledCutDist_le
    (ofSimpleGraph G) ((subcriticalReferenceWeightedGraph hk L n).permute pi)
    (subcriticalDivisionWeightedGraph hk D) part good
    hbeta herror ha0 hdisjoint hgood
  · simpa using hsize
  · exact hloss
  · exact hagree
  · exact hcut

/-- Tolerance form of the same-label visible-union restriction estimate. -/
theorem selectedVisibleParts_restrictedLabeledCutDist_le_tolerance
    (hk : 3 ≤ k)
    (A : SubcriticalComponentAlignment D L pi t m B)
    (G : SimpleGraph (Fin n))
    {theta beta error a0 tolerance : ℝ}
    (hcutoff : t ≤ theta) (hbeta : 0 ≤ beta)
    (herror : 0 ≤ error) (ha0 : 0 < a0)
    (htolerance : 0 ≤ tolerance)
    (hbetaSmall : beta ≤ tolerance * a0 ^ 2 / 2)
    (herrorSmall : error ≤ tolerance * a0 / 4)
    (hm : m ≤ error * n)
    (hcut : finiteLabeledCutDist (ofSimpleGraph G)
      ((subcriticalReferenceWeightedGraph hk L n).permute pi) ≤ beta)
    (partIndex : I ↪ {a : D.PartIndex // a ∈ D.visiblePartIndices theta})
    (part : I → Finset (Fin n))
    (hpart : ∀ q, part q ⊆ D.part (partIndex q).val)
    (hsize : ∀ q, a0 * n ≤ ((part q).card : ℝ)) :
    finiteLabeledCutDist
        ((ofSimpleGraph G).restrictToFinset (visibleCutPartUnion part))
        ((subcriticalDivisionWeightedGraph hk D).restrictToFinset
          (visibleCutPartUnion part)) ≤ tolerance := by
  have hmain := A.selectedVisibleParts_restrictedLabeledCutDist_le hk G
    hcutoff hbeta herror ha0 hm hcut partIndex part hpart hsize
  have hb : beta / a0 ^ 2 ≤ tolerance / 2 := by
    calc
      beta / a0 ^ 2 ≤ (tolerance * a0 ^ 2 / 2) / a0 ^ 2 := by gcongr
      _ = tolerance / 2 := by field_simp [ha0.ne']
  have he : 2 * error / a0 ≤ tolerance / 2 := by
    calc
      2 * error / a0 ≤ 2 * (tolerance * a0 / 4) / a0 := by gcongr
      _ = tolerance / 2 := by field_simp [ha0.ne']; ring
  exact hmain.trans (by linarith)

end FiniteFamily

end SubcriticalComponentAlignment

end InducedStars
