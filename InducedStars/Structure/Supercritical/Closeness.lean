import DenseGraph.Graphon.Inputs
import InducedStars.FiniteModels.CoMultipartiteStar
import InducedStars.Graphon.CleanPartition
import InducedStars.PriorInstances
import InducedStars.Regularity.WeightedCut
import InducedStars.Structure.Supercritical.Alignment
import InducedStars.Structure.Supercritical.FarFamily
import Mathlib.Tactic

/-!
# Deterministic supercritical close structure

This module transfers cut closeness to the explicit supercritical reference
matrix into the five finite conclusions used by the later counting argument.
The generic core takes the published finite-alignment capability as an
explicit argument; the induced-star instance is supplied only in the
paper-facing facade.
-/

noncomputable section

open Finset Set
open scoped BigOperators
open Filter Topology

namespace InducedStars

noncomputable local instance closenessDecidableRel {n : ℕ}
    (G : SimpleGraph (Fin n)) : DecidableRel G.Adj :=
  Classical.decRel _

noncomputable local instance closenessGraphDecidableEq (n : ℕ) :
    DecidableEq (SimpleGraph (Fin n)) :=
  Classical.decEq _

/-! ## Completing the aligned reference blocks -/

private theorem card_compl_interedges_le_abs_rectangleDiscrepancy_of_weight_one
    {n : ℕ} (G : SimpleGraph (Fin n))
    (R : DenseGraph.FiniteWeightedGraph (Fin n))
    (B : Finset (Fin n))
    (hR : ∀ x ∈ B, ∀ y ∈ B, R.weight x y = 1) :
    (((Gᶜ).interedges B B).card : ℝ) ≤
      |DenseGraph.FiniteWeightedGraph.rectangleDiscrepancy
        (DenseGraph.FiniteWeightedGraph.ofSimpleGraph G) R B B| := by
  classical
  let Q : Finset (Fin n × Fin n) :=
    Rel.interedges (fun x y ↦ ¬ G.Adj x y) B B
  have hsubset : (Gᶜ).interedges B B ⊆ Q := by
    intro p hp
    rw [SimpleGraph.mem_interedges_iff] at hp
    rw [Rel.mem_interedges_iff]
    exact ⟨hp.1, hp.2.1, hp.2.2.2⟩
  have hcard : ((Gᶜ).interedges B B).card ≤ Q.card :=
    Finset.card_le_card hsubset
  have hpartition :
      (G.interedges B B).card + Q.card = B.card * B.card := by
    change (Rel.interedges G.Adj B B).card + Q.card = B.card * B.card
    simpa [Q] using
      Rel.card_interedges_add_card_interedges_compl G.Adj B B
  have hrect :
      DenseGraph.FiniteWeightedGraph.rectangleDiscrepancy
          (DenseGraph.FiniteWeightedGraph.ofSimpleGraph G) R B B =
        ((G.interedges B B).card : ℝ) -
          (B.card : ℝ) * (B.card : ℝ) := by
    rw [DenseGraph.FiniteWeightedGraph.rectangleDiscrepancy]
    calc
      ∑ x ∈ B, ∑ y ∈ B,
          ((DenseGraph.FiniteWeightedGraph.ofSimpleGraph G).weight x y -
            R.weight x y) =
          ∑ x ∈ B, ∑ y ∈ B,
            ((if G.Adj x y then (1 : ℝ) else 0) - 1) := by
              apply Finset.sum_congr rfl
              intro x hx
              apply Finset.sum_congr rfl
              intro y hy
              rw [DenseGraph.FiniteWeightedGraph.ofSimpleGraph_weight,
                hR x hx y hy]
      _ = ((G.interedges B B).card : ℝ) -
          1 * (B.card : ℝ) * (B.card : ℝ) :=
            Regularity.sum_centered_adjIndicator_eq G B B 1
      _ = ((G.interedges B B).card : ℝ) -
          (B.card : ℝ) * (B.card : ℝ) := by ring
  have hedge : ((G.interedges B B).card : ℝ) ≤
      (B.card : ℝ) * (B.card : ℝ) := by
    exact_mod_cast (G.card_interedges_le_mul B B)
  rw [hrect, abs_of_nonpos (sub_nonpos.mpr hedge)]
  have hcardReal : (((Gᶜ).interedges B B).card : ℝ) ≤ Q.card := by
    exact_mod_cast hcard
  have hpartitionReal :
      ((G.interedges B B).card : ℝ) + Q.card =
        (B.card : ℝ) * (B.card : ℝ) := by
    exact_mod_cast hpartition
  linarith

/-- Completing the pulled-back balanced reference blocks costs at most the
sum of their labeled-cut rectangle errors.  Matrix cells are oriented, so
the left side contains the explicit factor two. -/
theorem two_mul_editDistance_complete_alignedReferenceParts_le
    {k n : ℕ} (hk : 3 ≤ k) {γ η : ℝ}
    (hγ : γ ∈ Set.Ico (gammaK k) 1) (G : SimpleGraph (Fin n))
    (π : Equiv.Perm (Fin n))
    (hcut : DenseGraph.FiniteWeightedGraph.finiteLabeledCutDist
        (DenseGraph.FiniteWeightedGraph.ofSimpleGraph G)
        ((supercriticalReferenceWeightedGraph k hk γ hγ n).permute π) ≤ η) :
    2 * (DenseGraph.simpleGraphEditDistance G
        (DenseGraph.completeWithinParts G
          (alignedSupercriticalReferencePart k n π)) : ℝ) ≤
      (k - 1 : ℝ) * η * (n : ℝ) ^ 2 := by
  classical
  let R := (supercriticalReferenceWeightedGraph k hk γ hγ n).permute π
  let B := alignedSupercriticalReferencePart k n π
  have heditNat := DenseGraph.two_mul_simpleGraphEditDistance_completeWithinParts
    G B (alignedSupercriticalReferenceParts_pairwiseDisjoint k n π)
  have hedit :
      2 * (DenseGraph.simpleGraphEditDistance G
          (DenseGraph.completeWithinParts G B) : ℝ) =
        ∑ i : Fin (k - 1), (((Gᶜ).interedges (B i) (B i)).card : ℝ) := by
    exact_mod_cast heditNat
  rw [hedit]
  calc
    ∑ i : Fin (k - 1), (((Gᶜ).interedges (B i) (B i)).card : ℝ) ≤
        ∑ i : Fin (k - 1),
          |DenseGraph.FiniteWeightedGraph.rectangleDiscrepancy
            (DenseGraph.FiniteWeightedGraph.ofSimpleGraph G) R (B i) (B i)| := by
      exact Finset.sum_le_sum fun i _ ↦
        card_compl_interedges_le_abs_rectangleDiscrepancy_of_weight_one
          G R (B i) (fun x hx y hy ↦ by
            exact permutedReference_weight_of_mem_same_alignedPart
              hk hγ π i hx hy)
    _ ≤ ∑ _i : Fin (k - 1), η * (n : ℝ) ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      calc
        |DenseGraph.FiniteWeightedGraph.rectangleDiscrepancy
            (DenseGraph.FiniteWeightedGraph.ofSimpleGraph G) R (B i) (B i)| ≤
            DenseGraph.FiniteWeightedGraph.finiteLabeledCutDist
              (DenseGraph.FiniteWeightedGraph.ofSimpleGraph G) R *
                (Fintype.card (Fin n) : ℝ) ^ 2 :=
          DenseGraph.FiniteWeightedGraph.finiteLabeledCutDist_rectangle_le
            _ _ _ _
        _ ≤ η * (n : ℝ) ^ 2 := by
          rw [Fintype.card_fin]
          exact mul_le_mul_of_nonneg_right hcut (sq_nonneg _)
    _ = (k - 1 : ℝ) * η * (n : ℝ) ^ 2 := by
      norm_num [Nat.cast_sub (by omega : 1 ≤ k), mul_assoc]

/-! ## Cross densities from a retained matching -/

/-- Once the canonical parts have been matched to distinct aligned
reference blocks, one good subrectangle controls the full cross-density.
The parameters `θ` and `ξ` expose, respectively, the loss from deleting the
unmatched vertices and the normalized finite rectangle error. -/
theorem crossDensity_close_of_alignedReferenceParts
    {k n : ℕ} (hk : 3 ≤ k) {γ η θ ξ : ℝ}
    (hγ : γ ∈ Set.Ico (gammaK k) 1) (G : SimpleGraph (Fin n))
    (D : SupercriticalDivision k (Fin n)) (π : Equiv.Perm (Fin n))
    (σ : Equiv.Perm (Fin (k - 1)))
    (hcut : DenseGraph.FiniteWeightedGraph.finiteLabeledCutDist
        (DenseGraph.FiniteWeightedGraph.ofSimpleGraph
          (supercriticalDivisionModelGraph G D))
        ((supercriticalReferenceWeightedGraph k hk γ hγ n).permute π) ≤ η)
    (hθ : 0 ≤ θ)
    (hrelative : ∀ i,
      (1 - θ) * (D.parts i).card ≤
        ((D.parts i ∩ alignedSupercriticalReferencePart k n π (σ i)).card : ℝ))
    (hgood : ∀ i,
      (D.parts i ∩ alignedSupercriticalReferencePart k n π (σ i)).Nonempty)
    (hscaled : ∀ i j, i ≠ j →
      η * (n : ℝ) ^ 2 ≤
        ξ *
          ((D.parts i ∩
            alignedSupercriticalReferencePart k n π (σ i)).card : ℝ) *
          ((D.parts j ∩
            alignedSupercriticalReferencePart k n π (σ j)).card : ℝ)) :
    ∀ i j, i ≠ j →
      |Regularity.graphDensity G (D.parts i) (D.parts j) -
          supercriticalOffDiagonal k γ| ≤ 2 * θ + ξ := by
  classical
  intro i j hij
  let A := D.parts i ∩ alignedSupercriticalReferencePart k n π (σ i)
  let B := D.parts j ∩ alignedSupercriticalReferencePart k n π (σ j)
  let H := DenseGraph.FiniteWeightedGraph.ofSimpleGraph
    (supercriticalDivisionModelGraph G D)
  let R := (supercriticalReferenceWeightedGraph k hk γ hγ n).permute π
  have hrect : DenseGraph.FiniteWeightedGraph.rectangleDiscrepancy H R A B =
      ((G.interedges A B).card : ℝ) -
        supercriticalOffDiagonal k γ * (A.card : ℝ) * (B.card : ℝ) := by
    rw [DenseGraph.FiniteWeightedGraph.rectangleDiscrepancy]
    calc
      ∑ x ∈ A, ∑ y ∈ B, (H.weight x y - R.weight x y) =
          ∑ x ∈ A, ∑ y ∈ B,
            ((if G.Adj x y then (1 : ℝ) else 0) -
              supercriticalOffDiagonal k γ) := by
        apply Finset.sum_congr rfl
        intro x hx
        apply Finset.sum_congr rfl
        intro y hy
        have hxP : x ∈ D.parts i := (Finset.mem_inter.mp hx).1
        have hxR : x ∈ alignedSupercriticalReferencePart k n π (σ i) :=
          (Finset.mem_inter.mp hx).2
        have hyP : y ∈ D.parts j := (Finset.mem_inter.mp hy).1
        have hyR : y ∈ alignedSupercriticalReferencePart k n π (σ j) :=
          (Finset.mem_inter.mp hy).2
        have hσij : σ i ≠ σ j := σ.injective.ne hij
        have hmodel := supercriticalDivisionModelGraph_adj_of_mem_distinct_parts
          G D hij hxP hyP
        have href := permutedReference_weight_of_mem_distinct_alignedParts
          hk hγ π hσij hxR hyR
        change (if (supercriticalDivisionModelGraph G D).Adj x y then 1 else 0) -
          R.weight x y = (if G.Adj x y then 1 else 0) -
            supercriticalOffDiagonal k γ
        rw [href]
        by_cases hG : G.Adj x y
        · rw [if_pos hG, if_pos (hmodel.mpr hG)]
        · have hM : ¬ (supercriticalDivisionModelGraph G D).Adj x y :=
            fun h ↦ hG (hmodel.mp h)
          rw [if_neg hG, if_neg hM]
      _ = ((G.interedges A B).card : ℝ) -
          supercriticalOffDiagonal k γ * (A.card : ℝ) * (B.card : ℝ) :=
        Regularity.sum_centered_adjIndicator_eq G A B
          (supercriticalOffDiagonal k γ)
  have hrectBound :
      |((G.interedges A B).card : ℝ) -
          supercriticalOffDiagonal k γ * (A.card : ℝ) * (B.card : ℝ)| ≤
        η * (n : ℝ) ^ 2 := by
    rw [← hrect]
    calc
      |DenseGraph.FiniteWeightedGraph.rectangleDiscrepancy H R A B| ≤
          DenseGraph.FiniteWeightedGraph.finiteLabeledCutDist H R *
            (Fintype.card (Fin n) : ℝ) ^ 2 :=
        DenseGraph.FiniteWeightedGraph.finiteLabeledCutDist_rectangle_le
          H R A B
      _ ≤ η * (n : ℝ) ^ 2 := by
        rw [Fintype.card_fin]
        exact mul_le_mul_of_nonneg_right hcut (sq_nonneg _)
  have hApos : 0 < (A.card : ℝ) := by
    exact_mod_cast (hgood i).card_pos
  have hBpos : 0 < (B.card : ℝ) := by
    exact_mod_cast (hgood j).card_pos
  have hgoodDensity :
      |Regularity.graphDensity G A B - supercriticalOffDiagonal k γ| ≤ ξ := by
    have hfactor : Regularity.graphDensity G A B -
        supercriticalOffDiagonal k γ =
      (((G.interedges A B).card : ℝ) -
          supercriticalOffDiagonal k γ * (A.card : ℝ) * (B.card : ℝ)) /
        ((A.card : ℝ) * (B.card : ℝ)) := by
      rw [Regularity.graphDensity_eq]
      field_simp
    rw [hfactor, abs_div, abs_of_pos (mul_pos hApos hBpos)]
    apply (div_le_iff₀ (mul_pos hApos hBpos)).2
    exact hrectBound.trans (by simpa [A, B, mul_assoc] using hscaled i j hij)
  have hperturb :
      |Regularity.graphDensity G A B -
          Regularity.graphDensity G (D.parts i) (D.parts j)| ≤ 2 * θ := by
    exact Regularity.abs_graphDensity_sub_graphDensity_le_two_mul
      G Finset.inter_subset_left Finset.inter_subset_left hθ
        (hrelative i) (hrelative j)
  calc
    |Regularity.graphDensity G (D.parts i) (D.parts j) -
        supercriticalOffDiagonal k γ| ≤
      |Regularity.graphDensity G (D.parts i) (D.parts j) -
          Regularity.graphDensity G A B| +
        |Regularity.graphDensity G A B - supercriticalOffDiagonal k γ| :=
      abs_sub_le _ _ _
    _ ≤ 2 * θ + ξ := by
      gcongr
      simpa [abs_sub_comm] using hperturb

/-! ## The canonical model stays aligned -/

/-- Passing from `G` to its canonical division model multiplies the retained
labeled reference error by at most `k`.  The proof uses the exact factor two
between unordered edits and oriented matrix cells. -/
theorem finiteLabeledCutDist_canonicalModel_reference_le
    {k n : ℕ} (hk : 3 ≤ k) {γ η : ℝ}
    (hγ : γ ∈ Set.Ico (gammaK k) 1) (hn : k - 1 ≤ n)
    (G : SimpleGraph (Fin n)) (π : Equiv.Perm (Fin n))
    (hcut : DenseGraph.FiniteWeightedGraph.finiteLabeledCutDist
        (DenseGraph.FiniteWeightedGraph.ofSimpleGraph G)
        ((supercriticalReferenceWeightedGraph k hk γ hγ n).permute π) ≤ η) :
    DenseGraph.FiniteWeightedGraph.finiteLabeledCutDist
        (DenseGraph.FiniteWeightedGraph.ofSimpleGraph
          (supercriticalDivisionModelGraph G
            (canonicalSupercriticalDivision G (by simpa using hn))))
        ((supercriticalReferenceWeightedGraph k hk γ hγ n).permute π) ≤
      (k : ℝ) * η := by
  classical
  let D := canonicalSupercriticalDivision G (by simpa using hn)
  let C := DenseGraph.completeWithinParts G
    (alignedSupercriticalReferencePart k n π)
  have hnpos : 0 < n := by omega
  have hpartsNonempty : ∀ i,
      (alignedSupercriticalReferencePart k n π i).Nonempty := by
    intro i
    rw [alignedSupercriticalReferencePart]
    exact Finset.map_nonempty.mpr
      (supercriticalReferencePart_nonempty hk hn i)
  have hbNat : supercriticalDefectCost G D ≤
      DenseGraph.simpleGraphEditDistance G C := by
    exact canonicalSupercriticalDefectCost_le_completeWithinParts
      G (by simpa using hn) (alignedSupercriticalReferencePart k n π)
        hpartsNonempty (biUnion_alignedSupercriticalReferencePart hk π)
        (alignedSupercriticalReferenceParts_pairwiseDisjoint k n π)
  have hedit := two_mul_editDistance_complete_alignedReferenceParts_le
    hk hγ G π hcut
  have hb : 2 * (supercriticalDefectCost G D : ℝ) ≤
      (k - 1 : ℝ) * η * (n : ℝ) ^ 2 := by
    calc
      2 * (supercriticalDefectCost G D : ℝ) ≤
          2 * (DenseGraph.simpleGraphEditDistance G C : ℝ) := by
        exact_mod_cast Nat.mul_le_mul_left 2 hbNat
      _ ≤ (k - 1 : ℝ) * η * (n : ℝ) ^ 2 := by
        simpa [C] using hedit
  have hmodelGraph :
      DenseGraph.FiniteWeightedGraph.finiteLabeledCutDist
          (DenseGraph.FiniteWeightedGraph.ofSimpleGraph G)
          (DenseGraph.FiniteWeightedGraph.ofSimpleGraph
            (supercriticalDivisionModelGraph G D)) ≤
        (k - 1 : ℝ) * η := by
    calc
      DenseGraph.FiniteWeightedGraph.finiteLabeledCutDist
          (DenseGraph.FiniteWeightedGraph.ofSimpleGraph G)
          (DenseGraph.FiniteWeightedGraph.ofSimpleGraph
            (supercriticalDivisionModelGraph G D)) ≤
          2 * (supercriticalDefectCost G D : ℝ) / (n : ℝ) ^ 2 :=
        finiteLabeledCutDist_divisionModel_le G D
      _ ≤ (k - 1 : ℝ) * η := by
        apply (div_le_iff₀ (sq_pos_of_pos (by exact_mod_cast hnpos))).2
        simpa [mul_assoc] using hb
  calc
    DenseGraph.FiniteWeightedGraph.finiteLabeledCutDist
        (DenseGraph.FiniteWeightedGraph.ofSimpleGraph
          (supercriticalDivisionModelGraph G D))
        ((supercriticalReferenceWeightedGraph k hk γ hγ n).permute π) ≤
      DenseGraph.FiniteWeightedGraph.finiteLabeledCutDist
          (DenseGraph.FiniteWeightedGraph.ofSimpleGraph
            (supercriticalDivisionModelGraph G D))
          (DenseGraph.FiniteWeightedGraph.ofSimpleGraph G) +
        DenseGraph.FiniteWeightedGraph.finiteLabeledCutDist
          (DenseGraph.FiniteWeightedGraph.ofSimpleGraph G)
          ((supercriticalReferenceWeightedGraph k hk γ hγ n).permute π) :=
      DenseGraph.FiniteWeightedGraph.finiteLabeledCutDist_triangle _ _ _
    _ ≤ (k - 1 : ℝ) * η + η := by
      gcongr
      simpa [DenseGraph.FiniteWeightedGraph.finiteLabeledCutDist_comm]
        using hmodelGraph
    _ = (k : ℝ) * η := by
      ring

/-! ## The no-high conclusion from a quantitative balance bound -/

/-- The explicit auxiliary balance tolerance used below leaves ample room
in the corrected `k`-term vertex-move inequality. -/
theorem one_lt_supercritical_noHigh_coefficient
    {k : ℕ} (hk : 3 ≤ k) {α ζ : ℝ}
    (hα₀ : 0 < α) (hα₁ : α < 1 / (100 * k : ℝ))
    (hζ₀ : 0 ≤ ζ) (hζ₁ : ζ ≤ α / (100 * (k : ℝ) ^ 2)) :
    1 < (k : ℝ) * (1 - α) * (1 / (k - 1 : ℝ) - ζ) := by
  have hkR : 3 ≤ (k : ℝ) := by exact_mod_cast hk
  have hkpos : 0 < (k : ℝ) := by positivity
  have hrpos : 0 < (k : ℝ) - 1 := by linarith
  have h100k : 0 < (100 : ℝ) * k := by positivity
  have h100k2 : 0 < (100 : ℝ) * (k : ℝ) ^ 2 := by positivity
  have hka : (100 : ℝ) * k * α < 1 := by
    have h := (lt_div_iff₀ h100k).mp hα₁
    nlinarith
  have hk2z : (100 : ℝ) * (k : ℝ) ^ 2 * ζ ≤ α := by
    have h := (le_div_iff₀ h100k2).mp hζ₁
    nlinarith
  have hkrz : (k : ℝ) * ((k : ℝ) - 1) * ζ ≤
      (k : ℝ) ^ 2 * ζ := by
    nlinarith
  have hmargin :
      0 < 1 - (k : ℝ) * α -
        (k : ℝ) * ((k : ℝ) - 1) * ζ := by
    nlinarith
  have hpositiveTerm : 0 ≤
      (k : ℝ) * α * ((k : ℝ) - 1) * ζ := by positivity
  have htarget :
      (k : ℝ) - 1 <
        (k : ℝ) * (1 - α) *
          (1 - ((k : ℝ) - 1) * ζ) := by
    nlinarith
  have heq :
      (k : ℝ) * (1 - α) * (1 / ((k : ℝ) - 1) - ζ) =
        ((k : ℝ) * (1 - α) *
          (1 - ((k : ℝ) - 1) * ζ)) / ((k : ℝ) - 1) := by
    field_simp
  rw [heq]
  exact (lt_div_iff₀ hrpos).2 (by simpa using htarget)

/-- A balance error `ζ` is small enough for the vertex-move argument exactly
when the displayed scalar coefficient exceeds one.  This wrapper turns that
transparent scalar condition into conclusion (v). -/
theorem canonicalCombinedDefectGraph_no_high_degree_of_part_card_close
    {k n : ℕ} (hk : 3 ≤ k) (G : SimpleGraph (Fin n))
    (hn : k - 1 ≤ n) {α ζ : ℝ} (hα : α < 1 / 2)
    (hcoefficient :
      1 < (k : ℝ) * (1 - α) * (1 / (k - 1 : ℝ) - ζ))
    (hparts : ∀ i : Fin (k - 1),
      |(((canonicalSupercriticalDivision G (by simpa using hn)).parts i).card : ℝ) -
          (n : ℝ) / (k - 1 : ℝ)| ≤ ζ * n) :
    ∀ v : Fin n, ∀ i : Fin (k - 1),
      ¬ HasHighDegreeInPart
          (canonicalCombinedDefectGraph G (by simpa using hn)) α
          (canonicalSupercriticalDivision G (by simpa using hn)) v i := by
  classical
  have hnpos : 0 < (n : ℝ) := by
    exact_mod_cast (show 0 < n by omega)
  refine canonicalCombinedDefectGraph_no_high_degree_of_card_lt G hk
    (by simpa using hn) hα ?_
  intro i
  have hlower := (abs_le.mp (hparts i)).1
  have hlower' :
      (n : ℝ) / (k - 1 : ℝ) - ζ * n ≤
        (((canonicalSupercriticalDivision G (by simpa using hn)).parts i).card : ℝ) := by
    linarith
  have hn_lt :
      (n : ℝ) < (k : ℝ) * (1 - α) *
        (((canonicalSupercriticalDivision G (by simpa using hn)).parts i).card : ℝ) := by
    calc
    (n : ℝ) <
        ((k : ℝ) * (1 - α) * (1 / (k - 1 : ℝ) - ζ)) * n := by
      nlinarith
    _ = (k : ℝ) * (1 - α) *
        ((n : ℝ) / (k - 1 : ℝ) - ζ * n) := by ring
    _ ≤ (k : ℝ) * (1 - α) *
        (((canonicalSupercriticalDivision G (by simpa using hn)).parts i).card : ℝ) := by
      have hfactor : 0 ≤ (k : ℝ) * (1 - α) := by
        have : 0 < 1 - α := by linarith
        positivity
      exact mul_le_mul_of_nonneg_left hlower' hfactor
  simpa only [Fintype.card_fin] using hn_lt

/-- The five conclusions of the paper's supercritical close-structure lemma,
packaged together with the actual co-multipartite approximation. -/
structure SupercriticalCloseStructureResult
    (k : ℕ) (hk : 3 ≤ k) (gamma alpha delta epsilon : ℝ)
    (hgamma : gamma ∈ Set.Ico (gammaK k) 1)
    {n : ℕ} (G : SimpleGraph (Fin n)) (hn : k - 1 ≤ n) where
  /-- The graph obtained by completing an aligned covering partition. -/
  coMultipartiteApprox : SimpleGraph (Fin n)
  /-- Conclusion (i), structural half. -/
  coMultipartiteApprox_isCoMultipartite :
    DenseGraph.IsCoMultipartite coMultipartiteApprox (k - 1)
  /-- Conclusion (i), quantitative half. -/
  editDistance_le :
    (DenseGraph.simpleGraphEditDistance G coMultipartiteApprox : ℝ) ≤
      epsilon * (n : ℝ) ^ 2
  /-- The canonical cost bound retained for the later counting classes. -/
  canonicalDefectCost_le :
    (canonicalSupercriticalDefectCost G (by simpa using hn) : ℝ) ≤
      epsilon * (n : ℝ) ^ 2
  /-- Conclusion (ii): every canonical main part is balanced. -/
  part_card_close :
    ∀ i : Fin (k - 1),
      |(((canonicalSupercriticalDivision G (by simpa using hn)).parts i).card : ℝ) -
          (n : ℝ) / (k - 1 : ℝ)| ≤ delta * n
  /-- Conclusion (iii): the canonical sparse set is small. -/
  sparse_card_le :
    (((canonicalSupercriticalDivision G (by simpa using hn)).sparse.card : ℕ) : ℝ) ≤
      delta * n / 2
  /-- Conclusion (iv): every cross-density is close to `rho`. -/
  cross_density_close :
    ∀ i j : Fin (k - 1), i ≠ j →
      |Regularity.graphDensity G
          ((canonicalSupercriticalDivision G (by simpa using hn)).parts i)
          ((canonicalSupercriticalDivision G (by simpa using hn)).parts j) -
          supercriticalOffDiagonal k gamma| ≤ delta
  /-- Conclusion (v): no vertex has high combined-defect degree in any
  canonical main part. -/
  no_high_defect_degree :
    ∀ v : Fin n, ∀ i : Fin (k - 1),
      ¬ HasHighDegreeInPart
          (canonicalCombinedDefectGraph G (by simpa using hn)) alpha
          (canonicalSupercriticalDivision G (by simpa using hn)) v i

/-! ## Assembly from a finite aligned model -/

/-- Assemble the five deterministic conclusions once the finite BCLSV
alignment and overlap-matrix argument have supplied a real-tolerance
matching.  This theorem is entirely finite and uses no published input. -/
noncomputable def supercriticalCloseStructureResult_of_realAlignment
    {k n : ℕ} (hk : 3 ≤ k) {gamma alpha delta epsilon eta zeta : ℝ}
    (hgamma : gamma ∈ Set.Ico (gammaK k) 1)
    (halpha : alpha < 1 / 2) (hn : k - 1 ≤ n)
    (heta : 0 ≤ eta) (hzeta : 0 ≤ zeta)
    (hzetaSmall : zeta ≤ 1 / (4 * ((k - 1 : ℕ) : ℝ)))
    (hpart : zeta ≤ delta) (hsparse : zeta ≤ delta / 2)
    (hedit : ((k - 1 : ℕ) : ℝ) * eta ≤ 2 * epsilon)
    (hdensity :
      4 * ((k - 1 : ℕ) : ℝ) * zeta +
          4 * ((k - 1 : ℕ) : ℝ) ^ 2 * (k : ℝ) * eta ≤ delta)
    (hcoefficient :
      1 < (k : ℝ) * (1 - alpha) *
        (1 / ((k - 1 : ℕ) : ℝ) - zeta))
    (G : SimpleGraph (Fin n)) (pi : Equiv.Perm (Fin n))
    (hcut : DenseGraph.FiniteWeightedGraph.finiteLabeledCutDist
        (DenseGraph.FiniteWeightedGraph.ofSimpleGraph G)
        ((supercriticalReferenceWeightedGraph k hk gamma hgamma n).permute pi) ≤ eta)
    (A : SupercriticalRealPartitionAlignment
      (canonicalSupercriticalDivision G (by simpa using hn)) pi zeta) :
    SupercriticalCloseStructureResult k hk gamma alpha delta epsilon hgamma
      G hn := by
  classical
  let D := canonicalSupercriticalDivision G (by simpa using hn)
  let B := alignedSupercriticalReferencePart k n pi
  let C := DenseGraph.completeWithinParts G B
  have hnposNat : 0 < n := by omega
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hnposNat
  have hrNat : 0 < k - 1 := by omega
  have hr : 0 < (((k - 1 : ℕ) : ℝ)) := by exact_mod_cast hrNat
  have hkR : 0 < (k : ℝ) := by positivity
  have hcastSub : (((k - 1 : ℕ) : ℝ)) = (k : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_one]
  have hpartsNonempty : ∀ i, (B i).Nonempty := by
    intro i
    exact Finset.map_nonempty.mpr
      (supercriticalReferencePart_nonempty hk hn i)
  have htwoEdit := two_mul_editDistance_complete_alignedReferenceParts_le
    hk hgamma G pi hcut
  have hEditReal : (DenseGraph.simpleGraphEditDistance G C : ℝ) ≤
      epsilon * (n : ℝ) ^ 2 := by
    have hscaled : ((k - 1 : ℕ) : ℝ) * eta * (n : ℝ) ^ 2 ≤
        2 * epsilon * (n : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_right hedit (sq_nonneg (n : ℝ))
    have htwo : 2 * (DenseGraph.simpleGraphEditDistance G C : ℝ) ≤
        2 * epsilon * (n : ℝ) ^ 2 := by
      have htwo' : 2 * (DenseGraph.simpleGraphEditDistance G C : ℝ) ≤
          ((k - 1 : ℕ) : ℝ) * eta * (n : ℝ) ^ 2 := by
        simpa [B, C, hcastSub] using htwoEdit
      exact htwo'.trans hscaled
    linarith
  have hCostNat : supercriticalDefectCost G D ≤
      DenseGraph.simpleGraphEditDistance G C :=
    canonicalSupercriticalDefectCost_le_completeWithinParts G
      (by simpa using hn) B hpartsNonempty
      (biUnion_alignedSupercriticalReferencePart hk pi)
      (alignedSupercriticalReferenceParts_pairwiseDisjoint k n pi)
  have hCostReal : (supercriticalDefectCost G D : ℝ) ≤
      epsilon * (n : ℝ) ^ 2 := by
    have hcast : (supercriticalDefectCost G D : ℝ) ≤
        (DenseGraph.simpleGraphEditDistance G C : ℝ) := by exact_mod_cast hCostNat
    exact hcast.trans hEditReal
  have hmodelCut :
      DenseGraph.FiniteWeightedGraph.finiteLabeledCutDist
          (DenseGraph.FiniteWeightedGraph.ofSimpleGraph
            (supercriticalDivisionModelGraph G D))
          ((supercriticalReferenceWeightedGraph k hk gamma hgamma n).permute pi) ≤
        (k : ℝ) * eta := by
    simpa [D] using finiteLabeledCutDist_canonicalModel_reference_le
      hk hgamma hn G pi hcut
  have hpartLower : ∀ i : Fin (k - 1),
      (n : ℝ) / (((k - 1 : ℕ) : ℝ)) - zeta * n ≤
        ((D.parts i).card : ℝ) := by
    intro i
    have hi := (abs_le.mp (A.part_card_close i)).1
    simpa [D] using hi
  have hzetaHalf : zeta ≤ 1 / (2 * (((k - 1 : ℕ) : ℝ))) := by
    have hfour : (0 : ℝ) < 4 * (((k - 1 : ℕ) : ℝ)) := by positivity
    have htwo : (0 : ℝ) < 2 * (((k - 1 : ℕ) : ℝ)) := by positivity
    have : 1 / (4 * (((k - 1 : ℕ) : ℝ))) ≤
        1 / (2 * (((k - 1 : ℕ) : ℝ))) := by
      exact one_div_le_one_div_of_le htwo (by nlinarith)
    exact hzetaSmall.trans this
  have hpartHalf : ∀ i : Fin (k - 1),
      (n : ℝ) / (2 * (((k - 1 : ℕ) : ℝ))) ≤
        ((D.parts i).card : ℝ) := by
    intro i
    have hi := hpartLower i
    have hzscaled : zeta * n ≤
        (1 / (2 * (((k - 1 : ℕ) : ℝ)))) * n :=
      mul_le_mul_of_nonneg_right hzetaHalf hnpos.le
    have havg : (n : ℝ) / (((k - 1 : ℕ) : ℝ)) -
          (1 / (2 * (((k - 1 : ℕ) : ℝ)))) * n =
        (n : ℝ) / (2 * (((k - 1 : ℕ) : ℝ))) := by
      field_simp
      ring
    rw [← havg]
    linarith
  let theta : ℝ := 2 * (((k - 1 : ℕ) : ℝ)) * zeta
  let xi : ℝ := 4 * (((k - 1 : ℕ) : ℝ)) ^ 2 * (k : ℝ) * eta
  have htheta : 0 ≤ theta := by positivity
  have hoverlapLower : ∀ i : Fin (k - 1),
      (n : ℝ) / (2 * (((k - 1 : ℕ) : ℝ))) ≤
        ((D.parts i ∩ B (A.partPermutation i)).card : ℝ) := by
    intro i
    have hdecomp := Finset.card_sdiff_add_card_inter
      (D.parts i) (B (A.partPermutation i))
    have hdecompReal :
        (((D.parts i \ B (A.partPermutation i)).card : ℕ) : ℝ) +
            (((D.parts i ∩ B (A.partPermutation i)).card : ℕ) : ℝ) =
          ((D.parts i).card : ℝ) := by exact_mod_cast hdecomp
    have hmiss :
        (((D.parts i \ B (A.partPermutation i)).card : ℕ) : ℝ) ≤ zeta * n := by
      simpa [D, B] using A.main_sdiff_reference_le i
    have hp := hpartLower i
    have hquarter : zeta * n ≤
        (n : ℝ) / (4 * (((k - 1 : ℕ) : ℝ))) := by
      have := mul_le_mul_of_nonneg_right hzetaSmall hnpos.le
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using this
    have htarget : (n : ℝ) / (2 * (((k - 1 : ℕ) : ℝ))) ≤
        (n : ℝ) / (((k - 1 : ℕ) : ℝ)) - 2 * (zeta * n) := by
      calc
        (n : ℝ) / (2 * (((k - 1 : ℕ) : ℝ))) =
            (n : ℝ) / (((k - 1 : ℕ) : ℝ)) -
              2 * ((n : ℝ) / (4 * (((k - 1 : ℕ) : ℝ)))) := by
          field_simp
          ring
        _ ≤ (n : ℝ) / (((k - 1 : ℕ) : ℝ)) - 2 * (zeta * n) := by
          linarith
    linarith
  have hrelative : ∀ i : Fin (k - 1),
      (1 - theta) * (D.parts i).card ≤
        ((D.parts i ∩ B (A.partPermutation i)).card : ℝ) := by
    intro i
    have hdecomp := Finset.card_sdiff_add_card_inter
      (D.parts i) (B (A.partPermutation i))
    have hdecompReal :
        (((D.parts i \ B (A.partPermutation i)).card : ℕ) : ℝ) +
            (((D.parts i ∩ B (A.partPermutation i)).card : ℕ) : ℝ) =
          ((D.parts i).card : ℝ) := by exact_mod_cast hdecomp
    have hmiss :
        (((D.parts i \ B (A.partPermutation i)).card : ℕ) : ℝ) ≤ zeta * n := by
      simpa [D, B] using A.main_sdiff_reference_le i
    have hthetaPart : zeta * n ≤ theta * (D.parts i).card := by
      have hp := hpartHalf i
      have hfac : 0 ≤ 2 * (((k - 1 : ℕ) : ℝ)) * zeta := by positivity
      have hm := mul_le_mul_of_nonneg_left hp hfac
      calc
        zeta * n = theta *
            ((n : ℝ) / (2 * (((k - 1 : ℕ) : ℝ)))) := by
          dsimp [theta]
          field_simp
        _ ≤ theta * (D.parts i).card := by
          simpa [theta] using hm
    nlinarith
  have hgood : ∀ i : Fin (k - 1),
      (D.parts i ∩ B (A.partPermutation i)).Nonempty := by
    intro i
    rw [← Finset.card_pos]
    have hposReal : 0 <
        (((D.parts i ∩ B (A.partPermutation i)).card : ℕ) : ℝ) :=
      (by positivity : 0 < (n : ℝ) / (2 * (((k - 1 : ℕ) : ℝ)))) |>.trans_le
        (hoverlapLower i)
    exact_mod_cast hposReal
  have hscaled : ∀ i j : Fin (k - 1), i ≠ j →
      ((k : ℝ) * eta) * (n : ℝ) ^ 2 ≤
        xi *
          ((D.parts i ∩ B (A.partPermutation i)).card : ℝ) *
          ((D.parts j ∩ B (A.partPermutation j)).card : ℝ) := by
    intro i j _hij
    let q : ℝ := (n : ℝ) / (2 * (((k - 1 : ℕ) : ℝ)))
    have hq : 0 ≤ q := by positivity
    have hp : q * q ≤
        ((D.parts i ∩ B (A.partPermutation i)).card : ℝ) *
          ((D.parts j ∩ B (A.partPermutation j)).card : ℝ) :=
      mul_le_mul (hoverlapLower i) (hoverlapLower j) hq
        (by positivity)
    have hfac : 0 ≤ 4 * (((k - 1 : ℕ) : ℝ)) ^ 2 * (k : ℝ) * eta := by
      positivity
    calc
      ((k : ℝ) * eta) * (n : ℝ) ^ 2 = xi * q * q := by
        dsimp [xi, q]
        field_simp
        ring
      _ ≤ xi *
          ((D.parts i ∩ B (A.partPermutation i)).card : ℝ) *
          ((D.parts j ∩ B (A.partPermutation j)).card : ℝ) := by
        simpa [xi, mul_assoc] using mul_le_mul_of_nonneg_left hp hfac
  have hcross := crossDensity_close_of_alignedReferenceParts
    hk hgamma G D pi A.partPermutation hmodelCut htheta hrelative hgood hscaled
  refine {
    coMultipartiteApprox := C
    coMultipartiteApprox_isCoMultipartite := ?_
    editDistance_le := hEditReal
    canonicalDefectCost_le := ?_
    part_card_close := ?_
    sparse_card_le := ?_
    cross_density_close := ?_
    no_high_defect_degree := ?_ }
  · exact DenseGraph.completeWithinParts_isCoMultipartite G B
      (biUnion_alignedSupercriticalReferencePart hk pi)
      (alignedSupercriticalReferenceParts_pairwiseDisjoint k n pi)
  · change (supercriticalDefectCost G
        (canonicalSupercriticalDivision G (by simpa using hn)) : ℝ) ≤
      epsilon * (n : ℝ) ^ 2
    simpa [D] using hCostReal
  · intro i
    simpa [hcastSub] using
      (A.part_card_close i).trans
        (mul_le_mul_of_nonneg_right hpart hnpos.le)
  · have hs := (A.sparse_card_le).trans
        (mul_le_mul_of_nonneg_right hsparse hnpos.le)
    nlinarith
  · intro i j hij
    apply (hcross i j hij).trans
    dsimp [theta, xi]
    nlinarith [hdensity]
  · exact canonicalCombinedDefectGraph_no_high_degree_of_part_card_close
      hk G hn halpha (by simpa [hcastSub] using hcoefficient)
        (fun i ↦ by simpa [D, hcastSub] using A.part_card_close i)

/-! ## Cut-distance thresholds -/

/-- Axiomatic-input-free form of the supercritical close-structure theorem.
The sole graph-limit ingredient is passed as an explicit capability.  The
finite proof supplies the cut-rectangle, alignment, and support-degree estimates
of `lemma:SuperCloseStructureK1k`. -/
theorem exists_supercriticalCloseStructureThresholdsCore
    (alignment : DenseGraph.FiniteWeightedAlignmentInput)
    (k : ℕ) (hk : 3 ≤ k) (gamma : ℝ)
    (hgamma : gamma ∈ Set.Ico (gammaK k) 1)
    (alpha : ℝ)
    (halpha : alpha ∈ Set.Ioo (0 : ℝ) (1 / (100 * k : ℝ)))
    (delta : ℝ) (hdelta : 0 < delta) (hdeltaAlpha : delta < alpha / 100)
    (hrhoLower : 3 * delta < supercriticalOffDiagonal k gamma)
    (hrhoUpper : supercriticalOffDiagonal k gamma + 3 * delta < 1)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ tau > 0, ∃ n0 : ℕ, ∃ hn0 : k - 1 ≤ n0, ∀ {n : ℕ}, (hn : n0 ≤ n) →
      ∀ G : SimpleGraph (Fin n),
        cutDist (graphGraphon G) (Wstar k hk gamma hgamma) < tau →
          Nonempty
            (SupercriticalCloseStructureResult k hk gamma alpha delta epsilon
              hgamma G (hn0.trans hn)) := by
  let r : ℝ := ((k - 1 : ℕ) : ℝ)
  let zeta : ℝ := min (delta / (16 * (k : ℝ)))
    (min (alpha / (100 * (k : ℝ) ^ 2)) (1 / (8 * (k : ℝ))))
  have hkR : 3 ≤ (k : ℝ) := by exact_mod_cast hk
  have hkpos : 0 < (k : ℝ) := by positivity
  have hrNat : 0 < k - 1 := by omega
  have hrpos : 0 < r := by
    dsimp [r]
    exact_mod_cast hrNat
  have hrle : r ≤ (k : ℝ) := by
    dsimp [r]
    exact_mod_cast (Nat.sub_le k 1)
  have halphaPos : 0 < alpha := by linarith [hdeltaAlpha]
  have hzeta : 0 < zeta := by
    dsimp [zeta]
    apply lt_min
    · positivity
    · apply lt_min
      · exact div_pos halphaPos (by positivity)
      · positivity
  have hzetaDelta : zeta ≤ delta / (16 * (k : ℝ)) := by
    exact min_le_left _ _
  have hzetaAlpha : zeta ≤ alpha / (100 * (k : ℝ) ^ 2) := by
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hzetaK : zeta ≤ 1 / (8 * (k : ℝ)) := by
    exact (min_le_right _ _).trans (min_le_right _ _)
  have hzetaSmall : zeta ≤ 1 / (4 * r) := by
    apply hzetaK.trans
    apply one_div_le_one_div_of_le (by positivity : 0 < 4 * r)
    nlinarith
  have hzetaPart : zeta ≤ delta := by
    have h := (le_div_iff₀ (by positivity : 0 < 16 * (k : ℝ))).mp
      hzetaDelta
    nlinarith
  have hzetaSparse : zeta ≤ delta / 2 := by
    have h := (le_div_iff₀ (by positivity : 0 < 16 * (k : ℝ))).mp
      hzetaDelta
    nlinarith
  have halphaHalf : alpha < 1 / 2 := by
    have hdenom : (2 : ℝ) < 100 * (k : ℝ) := by nlinarith
    have hone : 1 / (100 * (k : ℝ)) < 1 / 2 := by
      rw [div_lt_div_iff₀ (by positivity : 0 < 100 * (k : ℝ))
        (by norm_num : (0 : ℝ) < 2)]
      nlinarith
    exact halpha.2.trans hone
  have hcoefficient :
      1 < (k : ℝ) * (1 - alpha) * (1 / r - zeta) := by
    simpa [r, Nat.cast_sub (by omega : 1 ≤ k)] using
      one_lt_supercritical_noHigh_coefficient hk
      halpha.1 halpha.2 hzeta.le hzetaAlpha
  obtain ⟨etaAlign, hetaAlign, nAlign, hAlign⟩ :=
    eventually_supercriticalRealPartitionAlignment hk hgamma hzeta
  let eta : ℝ := min (etaAlign / (2 * (k : ℝ)))
    (min (epsilon / (2 * (k : ℝ)))
      (delta / (32 * (k : ℝ) ^ 3)))
  have heta : 0 < eta := by
    dsimp [eta]
    apply lt_min
    · positivity
    · apply lt_min <;> positivity
  have hetaAlignBound : eta ≤ etaAlign / (2 * (k : ℝ)) :=
    min_le_left _ _
  have hetaEditBound : eta ≤ epsilon / (2 * (k : ℝ)) :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hetaDensityBound : eta ≤ delta / (32 * (k : ℝ) ^ 3) :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hkEtaAlign : (k : ℝ) * eta ≤ etaAlign := by
    have h := (le_div_iff₀ (by positivity : 0 < 2 * (k : ℝ))).mp
      hetaAlignBound
    nlinarith
  have hEditScale : r * eta ≤ 2 * epsilon := by
    have h := (le_div_iff₀ (by positivity : 0 < 2 * (k : ℝ))).mp
      hetaEditBound
    have hrEta : r * eta ≤ (k : ℝ) * eta :=
      mul_le_mul_of_nonneg_right hrle heta.le
    nlinarith
  have hDensityScale :
      4 * r * zeta + 4 * r ^ 2 * (k : ℝ) * eta ≤ delta := by
    have hz := (le_div_iff₀ (by positivity : 0 < 16 * (k : ℝ))).mp
      hzetaDelta
    have he := (le_div_iff₀ (by positivity : 0 < 32 * (k : ℝ) ^ 3)).mp
      hetaDensityBound
    have hzmono : 4 * r * zeta ≤ 4 * (k : ℝ) * zeta := by
      gcongr
    have hrsq : r ^ 2 ≤ (k : ℝ) ^ 2 := by nlinarith
    have hemono : 4 * r ^ 2 * (k : ℝ) * eta ≤
        4 * (k : ℝ) ^ 3 * eta := by
      calc
        4 * r ^ 2 * (k : ℝ) * eta ≤
            4 * (k : ℝ) ^ 2 * (k : ℝ) * eta := by gcongr
        _ = 4 * (k : ℝ) ^ 3 * eta := by ring
    nlinarith
  obtain ⟨tauAlign, htauAlign, hPermutationAlign⟩ :=
    alignment.align eta heta
  have hrefEventually : ∀ᶠ n in atTop,
      cutDist (supercriticalReferenceGraphon k hk gamma hgamma n)
        (Wstar k hk gamma hgamma) < tauAlign / 2 :=
    (tendsto_order.1
      (supercriticalReferenceGraphon_tendsto_Wstar hk hgamma)).2
        _ (half_pos htauAlign)
  obtain ⟨nReference, hnReference⟩ := eventually_atTop.1 hrefEventually
  refine ⟨tauAlign / 2, half_pos htauAlign,
    max (k - 1) (max nAlign nReference),
    Nat.le_max_left _ _, ?_⟩
  intro n hn G hclose
  have hnSize : k - 1 ≤ n :=
    (Nat.le_max_left (k - 1) (max nAlign nReference)).trans hn
  have hnAlign : nAlign ≤ n :=
    (Nat.le_max_left nAlign nReference).trans
      ((Nat.le_max_right (k - 1) (max nAlign nReference)).trans hn)
  have hnReference' : nReference ≤ n :=
    (Nat.le_max_right nAlign nReference).trans
      ((Nat.le_max_right (k - 1) (max nAlign nReference)).trans hn)
  have href := hnReference n hnReference'
  have hrefComm :
      cutDist (Wstar k hk gamma hgamma)
        (supercriticalReferenceGraphon k hk gamma hgamma n) < tauAlign / 2 := by
    simpa only [cutDist_comm] using href
  have hGraphReference :
      cutDist (graphGraphon G)
        (supercriticalReferenceGraphon k hk gamma hgamma n) < tauAlign := by
    exact (cutDist_triangle (graphGraphon G) (Wstar k hk gamma hgamma)
      (supercriticalReferenceGraphon k hk gamma hgamma n)).trans_lt (by linarith)
  obtain ⟨pi, hpi⟩ := hPermutationAlign
    (DenseGraph.FiniteWeightedGraph.ofSimpleGraph G)
    (supercriticalReferenceWeightedGraph k hk gamma hgamma n)
    (by simpa only [DenseGraph.FiniteWeightedGraph.toGraphon_ofSimpleGraph,
        supercriticalReferenceGraphon] using hGraphReference)
  let D := canonicalSupercriticalDivision G (by simpa using hnSize)
  have hmodelCut :
      DenseGraph.FiniteWeightedGraph.finiteLabeledCutDist
          (DenseGraph.FiniteWeightedGraph.ofSimpleGraph
            (supercriticalDivisionModelGraph G D))
          ((supercriticalReferenceWeightedGraph k hk gamma hgamma n).permute pi) ≤
        (k : ℝ) * eta := by
    simpa [D] using finiteLabeledCutDist_canonicalModel_reference_le
      hk hgamma hnSize G pi hpi.le
  obtain ⟨A⟩ := hAlign hnAlign G D pi (hmodelCut.trans hkEtaAlign)
  refine ⟨supercriticalCloseStructureResult_of_realAlignment hk hgamma
    halphaHalf hnSize heta.le hzeta.le ?_ hzetaPart hzetaSparse ?_ ?_ ?_
      G pi hpi.le ?_⟩
  · simpa [r] using hzetaSmall
  · simpa [r] using hEditScale
  · simpa [r] using hDensityScale
  · simpa [r] using hcoefficient
  · simpa [D] using A

/-! ## Stable project-facing thresholds -/

/-- The chosen radius and vertex threshold, together with their full
uniform guarantee.  Packaging the choices once makes the far-family wrapper
use exactly the same cut radius as the direct theorem. -/
structure SupercriticalCloseStructureThresholds
    (k : ℕ) (hk : 3 ≤ k) (gamma : ℝ)
    (hgamma : gamma ∈ Set.Ico (gammaK k) 1)
    (alpha delta epsilon : ℝ) where
  cutRadius : ℝ
  cutRadius_pos : 0 < cutRadius
  vertexThreshold : ℕ
  vertexThreshold_large : k - 1 ≤ vertexThreshold
  closeStructure : ∀ {n : ℕ}, (hn : vertexThreshold ≤ n) →
    ∀ G : SimpleGraph (Fin n),
      cutDist (graphGraphon G) (Wstar k hk gamma hgamma) < cutRadius →
        Nonempty
          (SupercriticalCloseStructureResult k hk gamma alpha delta epsilon
            hgamma G (vertexThreshold_large.trans hn))

/-- Canonical project-level choice of the thresholds supplied by the
published BCLSV finite-alignment input and the finite proof above. -/
noncomputable def supercriticalCloseStructureThresholds
    (k : ℕ) (hk : 3 ≤ k) (gamma : ℝ)
    (hgamma : gamma ∈ Set.Ico (gammaK k) 1)
    (alpha : ℝ)
    (halpha : alpha ∈ Set.Ioo (0 : ℝ) (1 / (100 * k : ℝ)))
    (delta : ℝ) (hdelta : 0 < delta) (hdeltaAlpha : delta < alpha / 100)
    (hrhoLower : 3 * delta < supercriticalOffDiagonal k gamma)
    (hrhoUpper : supercriticalOffDiagonal k gamma + 3 * delta < 1)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    SupercriticalCloseStructureThresholds k hk gamma hgamma alpha delta epsilon := by
  let hExists := exists_supercriticalCloseStructureThresholdsCore
      PriorInstances.finiteWeightedAlignmentInput k hk gamma hgamma alpha halpha
        delta hdelta hdeltaAlpha hrhoLower hrhoUpper epsilon hepsilon
  let tau := Classical.choose hExists
  have htauSpec := Classical.choose_spec hExists
  let n0 := Classical.choose htauSpec.2
  have hn0Exists := Classical.choose_spec htauSpec.2
  let hn0 := Classical.choose hn0Exists
  have hclose : ∀ {n : ℕ}, (hn : n0 ≤ n) →
      ∀ G : SimpleGraph (Fin n),
        cutDist (graphGraphon G) (Wstar k hk gamma hgamma) < tau →
          Nonempty
            (SupercriticalCloseStructureResult k hk gamma alpha delta epsilon
              hgamma G (hn0.trans hn)) := by
    exact Classical.choose_spec hn0Exists
  exact {
    cutRadius := tau
    cutRadius_pos := htauSpec.1
    vertexThreshold := n0
    vertexThreshold_large := hn0
    closeStructure := hclose }

/-- The selected positive cut radius for the supercritical close-structure
theorem. -/
noncomputable def supercriticalCloseStructureCutRadius
    (k : ℕ) (hk : 3 ≤ k) (gamma : ℝ)
    (hgamma : gamma ∈ Set.Ico (gammaK k) 1)
    (alpha : ℝ)
    (halpha : alpha ∈ Set.Ioo (0 : ℝ) (1 / (100 * k : ℝ)))
    (delta : ℝ) (hdelta : 0 < delta) (hdeltaAlpha : delta < alpha / 100)
    (hrhoLower : 3 * delta < supercriticalOffDiagonal k gamma)
    (hrhoUpper : supercriticalOffDiagonal k gamma + 3 * delta < 1)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) : ℝ :=
  (supercriticalCloseStructureThresholds k hk gamma hgamma alpha halpha
    delta hdelta hdeltaAlpha hrhoLower hrhoUpper epsilon hepsilon).cutRadius

/-- The selected vertex threshold paired with
`supercriticalCloseStructureCutRadius`. -/
noncomputable def supercriticalCloseStructureVertexThreshold
    (k : ℕ) (hk : 3 ≤ k) (gamma : ℝ)
    (hgamma : gamma ∈ Set.Ico (gammaK k) 1)
    (alpha : ℝ)
    (halpha : alpha ∈ Set.Ioo (0 : ℝ) (1 / (100 * k : ℝ)))
    (delta : ℝ) (hdelta : 0 < delta) (hdeltaAlpha : delta < alpha / 100)
    (hrhoLower : 3 * delta < supercriticalOffDiagonal k gamma)
    (hrhoUpper : supercriticalOffDiagonal k gamma + 3 * delta < 1)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) : ℕ :=
  (supercriticalCloseStructureThresholds k hk gamma hgamma alpha halpha
    delta hdelta hdeltaAlpha hrhoLower hrhoUpper epsilon hepsilon).vertexThreshold

theorem supercriticalCloseStructureCutRadius_pos
    (k : ℕ) (hk : 3 ≤ k) (gamma : ℝ)
    (hgamma : gamma ∈ Set.Ico (gammaK k) 1)
    (alpha : ℝ)
    (halpha : alpha ∈ Set.Ioo (0 : ℝ) (1 / (100 * k : ℝ)))
    (delta : ℝ) (hdelta : 0 < delta) (hdeltaAlpha : delta < alpha / 100)
    (hrhoLower : 3 * delta < supercriticalOffDiagonal k gamma)
    (hrhoUpper : supercriticalOffDiagonal k gamma + 3 * delta < 1)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    0 < supercriticalCloseStructureCutRadius k hk gamma hgamma alpha halpha
      delta hdelta hdeltaAlpha hrhoLower hrhoUpper epsilon hepsilon :=
  (supercriticalCloseStructureThresholds k hk gamma hgamma alpha halpha
    delta hdelta hdeltaAlpha hrhoLower hrhoUpper epsilon hepsilon).cutRadius_pos

theorem supercriticalCloseStructureVertexThreshold_large
    (k : ℕ) (hk : 3 ≤ k) (gamma : ℝ)
    (hgamma : gamma ∈ Set.Ico (gammaK k) 1)
    (alpha : ℝ)
    (halpha : alpha ∈ Set.Ioo (0 : ℝ) (1 / (100 * k : ℝ)))
    (delta : ℝ) (hdelta : 0 < delta) (hdeltaAlpha : delta < alpha / 100)
    (hrhoLower : 3 * delta < supercriticalOffDiagonal k gamma)
    (hrhoUpper : supercriticalOffDiagonal k gamma + 3 * delta < 1)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    k - 1 ≤ supercriticalCloseStructureVertexThreshold k hk gamma hgamma
      alpha halpha delta hdelta hdeltaAlpha hrhoLower hrhoUpper epsilon
        hepsilon :=
  (supercriticalCloseStructureThresholds k hk gamma hgamma alpha halpha
    delta hdelta hdeltaAlpha hrhoLower hrhoUpper epsilon hepsilon).vertexThreshold_large

/-- Every sufficiently large finite graph cut-close to `Wstar` satisfies all
five deterministic supercritical conclusions.  No induced-freeness or edge
count hypothesis is used. -/
theorem supercriticalCloseStructure
    (k : ℕ) (hk : 3 ≤ k) (gamma : ℝ)
    (hgamma : gamma ∈ Set.Ico (gammaK k) 1)
    (alpha : ℝ)
    (halpha : alpha ∈ Set.Ioo (0 : ℝ) (1 / (100 * k : ℝ)))
    (delta : ℝ) (hdelta : 0 < delta) (hdeltaAlpha : delta < alpha / 100)
    (hrhoLower : 3 * delta < supercriticalOffDiagonal k gamma)
    (hrhoUpper : supercriticalOffDiagonal k gamma + 3 * delta < 1)
    (epsilon : ℝ) (hepsilon : 0 < epsilon)
    {n : ℕ}
    (hn : supercriticalCloseStructureVertexThreshold k hk gamma hgamma
      alpha halpha delta hdelta hdeltaAlpha hrhoLower hrhoUpper epsilon
        hepsilon ≤ n)
    (G : SimpleGraph (Fin n))
    (hclose : cutDist (graphGraphon G) (Wstar k hk gamma hgamma) <
      supercriticalCloseStructureCutRadius k hk gamma hgamma alpha halpha
        delta hdelta hdeltaAlpha hrhoLower hrhoUpper epsilon hepsilon) :
    Nonempty
      (SupercriticalCloseStructureResult k hk gamma alpha delta epsilon
        hgamma G
          ((supercriticalCloseStructureVertexThreshold_large k hk gamma
            hgamma alpha halpha delta hdelta hdeltaAlpha hrhoLower hrhoUpper
              epsilon hepsilon).trans hn)) := by
  exact (supercriticalCloseStructureThresholds k hk gamma hgamma alpha halpha
    delta hdelta hdeltaAlpha hrhoLower hrhoUpper epsilon hepsilon).closeStructure
      hn G hclose

/-- Paper: Lemma `lemma:SuperCloseStructureK1k`.

This exact-edge induced-star-free wrapper is deterministic: family
membership is used only to turn nonmembership in the far family into the
strict cut-distance hypothesis of `supercriticalCloseStructure`. -/
theorem superCloseStructureK1k
    (k : ℕ) (hk : 3 ≤ k) (gamma : ℝ)
    (hgamma : gamma ∈ Set.Ico (gammaK k) 1)
    (alpha : ℝ)
    (halpha : alpha ∈ Set.Ioo (0 : ℝ) (1 / (100 * k : ℝ)))
    (delta : ℝ) (hdelta : 0 < delta) (hdeltaAlpha : delta < alpha / 100)
    (hrhoLower : 3 * delta < supercriticalOffDiagonal k gamma)
    (hrhoUpper : supercriticalOffDiagonal k gamma + 3 * delta < 1)
    (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (m : ℕ) {n : ℕ}
    (hn : supercriticalCloseStructureVertexThreshold k hk gamma hgamma
      alpha halpha delta hdelta hdeltaAlpha hrhoLower hrhoUpper epsilon
        hepsilon ≤ n)
    (G : SimpleGraph (Fin n))
    (hfamily : G ∈ inducedFreeGraphFinsetWithEdges (inducedStar k) n m \
      supercriticalFarGraphFinset k hk gamma hgamma m n
        (supercriticalCloseStructureCutRadius k hk gamma hgamma alpha halpha
          delta hdelta hdeltaAlpha hrhoLower hrhoUpper epsilon hepsilon)) :
    Nonempty
      (SupercriticalCloseStructureResult k hk gamma alpha delta epsilon
        hgamma G
          ((supercriticalCloseStructureVertexThreshold_large k hk gamma
            hgamma alpha halpha delta hdelta hdeltaAlpha hrhoLower hrhoUpper
              epsilon hepsilon).trans hn)) := by
  apply supercriticalCloseStructure k hk gamma hgamma alpha halpha delta hdelta
    hdeltaAlpha hrhoLower hrhoUpper epsilon hepsilon hn G
  have hcloseMem : G ∈ supercriticalCloseGraphFinset k hk gamma hgamma m n
      (supercriticalCloseStructureCutRadius k hk gamma hgamma alpha halpha
        delta hdelta hdeltaAlpha hrhoLower hrhoUpper epsilon hepsilon) := by
    rw [supercriticalCloseGraphFinset_eq_sdiff_far]
    exact hfamily
  exact (mem_supercriticalCloseGraphFinset.mp hcloseMem).2.2

end InducedStars
