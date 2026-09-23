import DenseGraph.FiniteModels.WeightedRestriction
import InducedStars.Regularity.WeightedCut

/-!
# Finite cut control on visible subcritical parts

This file isolates the finite calculation used in the visible-set conclusion
of the subcritical cut-to-division bridge.  A global same-label cut estimate
is restricted to a union of selected parts, while the vertices lost from the
aligned reference cells are charged explicitly.
-/

noncomputable section

open Finset Set DenseGraph DenseGraph.FiniteWeightedGraph
open scoped BigOperators SimpleGraph

namespace InducedStars

universe u v

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {I : Type v} [Fintype I] [DecidableEq I]

/-- The union of a finite indexed family of selected parts. -/
def visibleCutPartUnion (part : I → Finset V) : Finset V :=
  Finset.univ.biUnion part

/-- The union of the good, reference-aligned subsets of selected parts. -/
def visibleCutGoodUnion (good : I → Finset V) : Finset V :=
  Finset.univ.biUnion good

theorem visibleCutGoodUnion_subset (part good : I → Finset V)
    (hgood : ∀ i, good i ⊆ part i) :
    visibleCutGoodUnion good ⊆ visibleCutPartUnion part := by
  intro x hx
  obtain ⟨i, _, hxi⟩ := Finset.mem_biUnion.mp hx
  exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hgood i hxi⟩

/-- The total number of bad selected vertices is bounded by the sum of the
per-part losses.  Disjointness is not needed for this direction. -/
theorem card_visibleCutPartUnion_sdiff_good_le
    (part good : I → Finset V) (hgood : ∀ i, good i ⊆ part i)
    {error : ℝ} (hloss : ∀ i,
      (((part i \ good i).card : ℕ) : ℝ) ≤
        error * Fintype.card V) :
    (((visibleCutPartUnion part \ visibleCutGoodUnion good).card : ℕ) : ℝ) ≤
      (Fintype.card I : ℝ) * error * Fintype.card V := by
  have hsub : visibleCutPartUnion part \ visibleCutGoodUnion good ⊆
      Finset.univ.biUnion fun i ↦ part i \ good i := by
    intro x hx
    obtain ⟨i, _, hxi⟩ := Finset.mem_biUnion.mp
      (Finset.mem_sdiff.mp hx).1
    have hxgood : x ∉ good i := by
      intro hxiGood
      exact (Finset.mem_sdiff.mp hx).2
        (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hxiGood⟩)
    exact Finset.mem_biUnion.mpr
      ⟨i, Finset.mem_univ i, Finset.mem_sdiff.mpr ⟨hxi, hxgood⟩⟩
  have hcard : ((visibleCutPartUnion part \ visibleCutGoodUnion good).card : ℝ) ≤
      ((Finset.univ.biUnion fun i ↦ part i \ good i).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  have hbi : ((Finset.univ.biUnion fun i ↦ part i \ good i).card : ℝ) ≤
      ∑ i : I, (((part i \ good i).card : ℕ) : ℝ) := by
    exact_mod_cast (Finset.card_biUnion_le :
      (Finset.univ.biUnion fun i ↦ part i \ good i).card ≤
        ∑ i : I, (part i \ good i).card)
  calc
    _ ≤ ∑ i : I, (((part i \ good i).card : ℕ) : ℝ) := hcard.trans hbi
    _ ≤ ∑ _i : I, error * Fintype.card V :=
      Finset.sum_le_sum fun i _ ↦ hloss i
    _ = (Fintype.card I : ℝ) * error * Fintype.card V := by simp; ring

/-- Pairwise-disjoint selected parts have union size at least the sum of any
common per-part lower bound. -/
theorem card_visibleCutPartUnion_ge
    (part : I → Finset V)
    (hdisjoint : Set.PairwiseDisjoint (Set.univ : Set I) part)
    {a : ℝ} (hsize : ∀ i,
      a * Fintype.card V ≤ (((part i).card : ℕ) : ℝ)) :
    (Fintype.card I : ℝ) * a * Fintype.card V ≤
      (((visibleCutPartUnion part).card : ℕ) : ℝ) := by
  have hdisjoint' : Set.PairwiseDisjoint
      ((Finset.univ : Finset I) : Set I) part := by
    simpa using hdisjoint
  rw [visibleCutPartUnion, Finset.card_biUnion hdisjoint']
  push_cast
  calc
    (Fintype.card I : ℝ) * a * Fintype.card V =
        ∑ _i : I, a * Fintype.card V := by simp; ring
    _ ≤ ∑ i : I, ((part i).card : ℝ) :=
      Finset.sum_le_sum fun i _ ↦ hsize i

/-- Quantitative finite form of the visible-set cut restriction.  The number
of selected parts cancels between their total size and their total alignment
loss, so the bound is independent of the selected family.  The empty union
is handled by the totalized finite cut distance. -/
theorem visibleParts_restrictedLabeledCutDist_le
    (G R P : FiniteWeightedGraph V) (part good : I → Finset V)
    {beta error a : ℝ}
    (hbeta : 0 ≤ beta) (herror : 0 ≤ error) (ha : 0 < a)
    (hdisjoint : Set.PairwiseDisjoint (Set.univ : Set I) part)
    (hgood : ∀ i, good i ⊆ part i)
    (hsize : ∀ i, a * Fintype.card V ≤ (((part i).card : ℕ) : ℝ))
    (hloss : ∀ i, (((part i \ good i).card : ℕ) : ℝ) ≤
      error * Fintype.card V)
    (hagree : ∀ x ∈ visibleCutGoodUnion good,
      ∀ y ∈ visibleCutGoodUnion good, R.weight x y = P.weight x y)
    (hcut : finiteLabeledCutDist G R ≤ beta) :
    finiteLabeledCutDist
        (G.restrictToFinset (visibleCutPartUnion part))
        (P.restrictToFinset (visibleCutPartUnion part)) ≤
      beta / a ^ 2 + 2 * error / a := by
  let U := visibleCutPartUnion part
  let Good := visibleCutGoodUnion good
  have hGood : Good ⊆ U := visibleCutGoodUnion_subset part good hgood
  have hbase := finiteLabeledCutDist_restrictToFinset_le_cut_add_bad
    G R P U Good hGood hagree hcut
  by_cases hU : U.card = 0
  · have hzero : finiteLabeledCutDist (G.restrictToFinset U)
        (P.restrictToFinset U) = 0 := by
      have hUempty : U = ∅ := Finset.card_eq_zero.mp hU
      have hGP : G.restrictToFinset U = P.restrictToFinset U := by
        ext x
        have hx : False := by simpa [hUempty] using x.property
        exact hx.elim
      simp [hGP]
    rw [hzero]
    exact add_nonneg (div_nonneg hbeta (sq_nonneg a))
      (div_nonneg (mul_nonneg (by norm_num) herror) ha.le)
  · have hUne : U.Nonempty := Finset.card_ne_zero.mp hU
    obtain ⟨x, hxU⟩ := hUne
    obtain ⟨i, _, hxi⟩ := Finset.mem_biUnion.mp hxU
    have hIposNat : 0 < Fintype.card I := Fintype.card_pos_iff.mpr ⟨i⟩
    have hIpos : 0 < (Fintype.card I : ℝ) := by exact_mod_cast hIposNat
    have hVposNat : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨x⟩
    have hVpos : 0 < (Fintype.card V : ℝ) := by exact_mod_cast hVposNat
    have hUpos : 0 < (U.card : ℝ) := by
      exact_mod_cast (Nat.pos_of_ne_zero hU)
    have hUlower : (Fintype.card I : ℝ) * a * Fintype.card V ≤
        (U.card : ℝ) := by
      exact card_visibleCutPartUnion_ge part hdisjoint hsize
    have hIone : (1 : ℝ) ≤ Fintype.card I := by exact_mod_cast hIposNat
    have haVnonneg : 0 ≤ a * (Fintype.card V : ℝ) :=
      mul_nonneg ha.le hVpos.le
    have haVleU : a * (Fintype.card V : ℝ) ≤ U.card := by
      calc
        a * (Fintype.card V : ℝ) = 1 * (a * Fintype.card V) := by ring
        _ ≤ (Fintype.card I : ℝ) * (a * Fintype.card V) := by gcongr
        _ = (Fintype.card I : ℝ) * a * Fintype.card V := by ring
        _ ≤ U.card := hUlower
    have hbad : (((U \ Good).card : ℕ) : ℝ) ≤
        (Fintype.card I : ℝ) * error * Fintype.card V := by
      exact card_visibleCutPartUnion_sdiff_good_le part good hgood hloss
    have hbadRatio : (((U \ Good).card : ℕ) : ℝ) ≤
        (error / a) * U.card := by
      calc
        _ ≤ (Fintype.card I : ℝ) * error * Fintype.card V := hbad
        _ = (error / a) * ((Fintype.card I : ℝ) * a * Fintype.card V) := by
          field_simp [ha.ne']
        _ ≤ (error / a) * U.card := by
          gcongr
    have hfirst : beta * (Fintype.card V : ℝ) ^ 2 / (U.card : ℝ) ^ 2 ≤
        beta / a ^ 2 := by
      apply (div_le_iff₀ (sq_pos_of_pos hUpos)).2
      calc
        beta * (Fintype.card V : ℝ) ^ 2 =
            (beta / a ^ 2) * (a * Fintype.card V) ^ 2 := by
          field_simp [ha.ne']
        _ ≤ (beta / a ^ 2) * (U.card : ℝ) ^ 2 := by
          gcongr
    have hsecond : 2 * (((U \ Good).card : ℕ) : ℝ) / U.card ≤
        2 * error / a := by
      apply (div_le_iff₀ hUpos).2
      calc
        2 * (((U \ Good).card : ℕ) : ℝ) ≤
            2 * ((error / a) * U.card) := by gcongr
        _ = (2 * error / a) * U.card := by ring
    exact hbase.trans (add_le_add hfirst hsecond)

/-- A convenient tolerance form of the quantitative restriction bound. -/
theorem visibleParts_restrictedLabeledCutDist_le_tolerance
    (G R P : FiniteWeightedGraph V) (part good : I → Finset V)
    {beta error a tolerance : ℝ}
    (hbeta : 0 ≤ beta) (herror : 0 ≤ error) (ha : 0 < a)
    (htolerance : 0 ≤ tolerance)
    (hbetaSmall : beta ≤ tolerance * a ^ 2 / 2)
    (herrorSmall : error ≤ tolerance * a / 4)
    (hdisjoint : Set.PairwiseDisjoint (Set.univ : Set I) part)
    (hgood : ∀ i, good i ⊆ part i)
    (hsize : ∀ i, a * Fintype.card V ≤ (((part i).card : ℕ) : ℝ))
    (hloss : ∀ i, (((part i \ good i).card : ℕ) : ℝ) ≤
      error * Fintype.card V)
    (hagree : ∀ x ∈ visibleCutGoodUnion good,
      ∀ y ∈ visibleCutGoodUnion good, R.weight x y = P.weight x y)
    (hcut : finiteLabeledCutDist G R ≤ beta) :
    finiteLabeledCutDist
        (G.restrictToFinset (visibleCutPartUnion part))
        (P.restrictToFinset (visibleCutPartUnion part)) ≤ tolerance := by
  have hmain := visibleParts_restrictedLabeledCutDist_le G R P part good
    hbeta herror ha hdisjoint hgood hsize hloss hagree hcut
  have ha2 : 0 < a ^ 2 := sq_pos_of_pos ha
  have hb : beta / a ^ 2 ≤ tolerance / 2 := by
    calc
      beta / a ^ 2 ≤ (tolerance * a ^ 2 / 2) / a ^ 2 := by gcongr
      _ = tolerance / 2 := by field_simp [ha.ne']
  have he : 2 * error / a ≤ tolerance / 2 := by
    calc
      2 * error / a ≤ 2 * (tolerance * a / 4) / a := by gcongr
      _ = tolerance / 2 := by field_simp [ha.ne']; ring
  exact hmain.trans (by linarith)

/-! ## Density on one visible rectangle -/

local instance visibleCutAdjDecidable (G : SimpleGraph V) : DecidableRel G.Adj :=
  Classical.decRel _

/-- If a reference has constant weight on trimmed subsets of a rectangle,
the original graph's density differs from that constant by the global cut
error plus the two vertex-loss terms.  This is the exact normalization used
for visible parts in `lemma:WtoWtildeMetricsK1k`. -/
theorem abs_graphDensity_sub_constant_le_of_referenceAgreement
    (G : SimpleGraph V) (R : FiniteWeightedGraph V)
    (X Y Xgood Ygood : Finset V) {w beta error a : ℝ}
    (_hXY : Disjoint X Y)
    (hw₀ : 0 ≤ w) (hw₁ : w ≤ 1)
    (hbeta : 0 ≤ beta) (herror : 0 ≤ error) (ha : 0 < a)
    (hV : 0 < Fintype.card V)
    (hXgood : Xgood ⊆ X) (hYgood : Ygood ⊆ Y)
    (hXsize : a * Fintype.card V ≤ (((X.card : ℕ) : ℝ)))
    (hYsize : a * Fintype.card V ≤ (((Y.card : ℕ) : ℝ)))
    (hXloss : (((X \ Xgood).card : ℕ) : ℝ) ≤ error * Fintype.card V)
    (hYloss : (((Y \ Ygood).card : ℕ) : ℝ) ≤ error * Fintype.card V)
    (hagree : ∀ x ∈ Xgood, ∀ y ∈ Ygood, R.weight x y = w)
    (hcut : finiteLabeledCutDist (FiniteWeightedGraph.ofSimpleGraph G) R ≤ beta) :
    |Regularity.graphDensity G X Y - w| ≤ beta / a ^ 2 + 2 * error / a := by
  let C : FiniteWeightedGraph V := FiniteWeightedGraph.constant w hw₀ hw₁
  have hGR : |rectangleDiscrepancy (FiniteWeightedGraph.ofSimpleGraph G) R X Y| ≤
      beta * (Fintype.card V : ℝ) ^ 2 :=
    (abs_rectangleDiscrepancy_le_finiteLabeledCutDist_mul_card_sq
      (FiniteWeightedGraph.ofSimpleGraph G) R X Y).trans
      (mul_le_mul_of_nonneg_right hcut (sq_nonneg _))
  have hRC : |rectangleDiscrepancy R C X Y| ≤
      (((X \ Xgood).card : ℕ) : ℝ) * Y.card +
        (X.card : ℝ) * (((Y \ Ygood).card : ℕ) : ℝ) := by
    apply abs_rectangleDiscrepancy_le_deleted_rows_cols R C X Y Xgood Ygood
      hXgood hYgood
    intro x hx y hy
    simpa [C] using hagree x hx y hy
  have hcenter : |((G.interedges X Y).card : ℝ) -
      w * (X.card : ℝ) * Y.card| ≤
      beta * (Fintype.card V : ℝ) ^ 2 +
        (((X \ Xgood).card : ℕ) : ℝ) * Y.card +
        (X.card : ℝ) * (((Y \ Ygood).card : ℕ) : ℝ) := by
    have hadd : rectangleDiscrepancy (FiniteWeightedGraph.ofSimpleGraph G) C X Y =
        rectangleDiscrepancy (FiniteWeightedGraph.ofSimpleGraph G) R X Y +
          rectangleDiscrepancy R C X Y := by
      simp only [rectangleDiscrepancy]
      simp_rw [show ∀ x y,
        (FiniteWeightedGraph.ofSimpleGraph G).weight x y - C.weight x y =
          ((FiniteWeightedGraph.ofSimpleGraph G).weight x y - R.weight x y) +
            (R.weight x y - C.weight x y) by intros; ring]
      simp only [Finset.sum_add_distrib]
    have hGC : rectangleDiscrepancy (FiniteWeightedGraph.ofSimpleGraph G) C X Y =
        ((G.interedges X Y).card : ℝ) - w * (X.card : ℝ) * Y.card := by
      simp only [rectangleDiscrepancy, FiniteWeightedGraph.ofSimpleGraph_weight,
        FiniteWeightedGraph.constant_weight, Finset.sum_sub_distrib]
      rw [Regularity.sum_adjIndicator_eq_card_interedges]
      simp [C]
      ring
    rw [← hGC, hadd]
    calc
      |rectangleDiscrepancy (FiniteWeightedGraph.ofSimpleGraph G) R X Y +
          rectangleDiscrepancy R C X Y| ≤
          |rectangleDiscrepancy (FiniteWeightedGraph.ofSimpleGraph G) R X Y| +
            |rectangleDiscrepancy R C X Y| := abs_add_le _ _
      _ ≤ beta * (Fintype.card V : ℝ) ^ 2 +
          ((((X \ Xgood).card : ℕ) : ℝ) * Y.card +
            (X.card : ℝ) * (((Y \ Ygood).card : ℕ) : ℝ)) :=
        add_le_add hGR hRC
      _ = _ := by ring
  have hVℝ : 0 < (Fintype.card V : ℝ) := by exact_mod_cast hV
  have hXpos : 0 < (X.card : ℝ) :=
    lt_of_lt_of_le (mul_pos ha hVℝ) hXsize
  have hYpos : 0 < (Y.card : ℝ) :=
    lt_of_lt_of_le (mul_pos ha hVℝ) hYsize
  have hXYpos : 0 < (X.card : ℝ) * Y.card := mul_pos hXpos hYpos
  have hbetaTerm : beta * (Fintype.card V : ℝ) ^ 2 ≤
      (beta / a ^ 2) * ((X.card : ℝ) * Y.card) := by
    calc
      beta * (Fintype.card V : ℝ) ^ 2 =
          (beta / a ^ 2) *
            ((a * Fintype.card V) * (a * Fintype.card V)) := by
        field_simp [ha.ne']
      _ ≤ (beta / a ^ 2) * ((X.card : ℝ) * Y.card) := by
        gcongr
  have hXterm : (((X \ Xgood).card : ℕ) : ℝ) * Y.card ≤
      (error / a) * ((X.card : ℝ) * Y.card) := by
    calc
      _ ≤ (error * Fintype.card V) * (Y.card : ℝ) := by gcongr
      _ = (error / a) * ((a * Fintype.card V) * (Y.card : ℝ)) := by
        field_simp [ha.ne']
      _ ≤ (error / a) * ((X.card : ℝ) * Y.card) := by
        gcongr
  have hYterm : (X.card : ℝ) * (((Y \ Ygood).card : ℕ) : ℝ) ≤
      (error / a) * ((X.card : ℝ) * Y.card) := by
    calc
      _ ≤ (X.card : ℝ) * (error * Fintype.card V) := by gcongr
      _ = (error / a) * ((X.card : ℝ) * (a * Fintype.card V)) := by
        field_simp [ha.ne']
      _ ≤ (error / a) * ((X.card : ℝ) * Y.card) := by
        gcongr
  rw [Regularity.graphDensity_eq]
  have hrearrange :
      (G.interedges X Y).card / ((X.card : ℝ) * Y.card) - w =
        (((G.interedges X Y).card : ℝ) - w * X.card * Y.card) /
          ((X.card : ℝ) * Y.card) := by
    field_simp
  rw [hrearrange, abs_div, abs_of_pos hXYpos]
  apply (div_le_iff₀ hXYpos).2
  calc
    |((G.interedges X Y).card : ℝ) - w * (X.card : ℝ) * Y.card| ≤
        beta * (Fintype.card V : ℝ) ^ 2 +
          (((X \ Xgood).card : ℕ) : ℝ) * Y.card +
          (X.card : ℝ) * (((Y \ Ygood).card : ℕ) : ℝ) := hcenter
    _ ≤ (beta / a ^ 2) * ((X.card : ℝ) * Y.card) +
          (error / a) * ((X.card : ℝ) * Y.card) +
          (error / a) * ((X.card : ℝ) * Y.card) := by
      gcongr
    _ = (beta / a ^ 2 + 2 * error / a) *
          ((X.card : ℝ) * Y.card) := by ring

end InducedStars
