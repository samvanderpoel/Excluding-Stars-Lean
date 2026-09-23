import InducedStars.C4.FrozenCrossModels
import InducedStars.C4.MatchingUniform
import DenseGraph.Combinatorics.BinomialJointShift

/-!
# Feasibility and binomial comparison for frozen cross models

Both high-degree polarities use the same exact signed internal correction.
Frozen successes are subtracted before passing to natural-number quotas.
The reference slice is feasible before any binomial ratio is applied.
-/

noncomputable section
open Finset Set
open scoped Classical
namespace InducedStars

theorem c4FixedDefectInternalCount_sub_choose_eq_shift {n : ℕ}
    (D : C4Division (Fin n)) (T : SimpleGraph (Fin n)) :
    (c4FixedDefectInternalCount D T : ℝ) - (D.cliquePart.card.choose 2 : ℝ) =
      (c4MatchingSignedShift D T : ℝ) := by
  have h := c4FixedDefectInternalCount_signed D T
  have hR := congrArg (fun x : ℕ => (x : ℝ)) h
  dsimp [c4MatchingSignedShift]
  push_cast at hR ⊢
  linarith only [hR]

/-- Removing frozen coordinates and their prescribed successes preserves
the exact feasible compact band supplied by nondegeneracy. -/
theorem c4Frozen_quotaBand_of_samplingBounds {n m z : ℕ} {D : C4Division (Fin n)}
    (W : C4FrozenCrossData D) (T : SimpleGraph (Fin n)) {beta : ℝ}
    (hF : W.frozen.card = z) (hP : W.present.card = 0 ∨ W.present.card = z)
    (h : C4NondegenerateSamplingBounds n m D.cliquePart.card z
      (c4MatchingSignedShift D T) beta) :
    c4FixedDefectInternalCount D T + W.present.card ≤ m ∧
      W.quota T m ≤ W.optional.card ∧
      beta ≤ DenseGraph.FixedCardinalityBlockModel.quotaParameter W.optional.card (W.quota T m) ∧
      DenseGraph.FixedCardinalityBlockModel.quotaParameter W.optional.card (W.quota T m) ≤ 1-beta := by
  have hparts := D.card_add
  simp only [Fintype.card_fin] at hparts
  have hA : D.independentPart.card = n-D.cliquePart.card := by omega
  have hcap : (W.optional.card : ℝ) =
      ((D.cliquePart.card*(n-D.cliquePart.card) : ℕ) : ℝ)-z := by
    have hNat := W.optional_card_add_frozen
    rw [hF, card_c4CrossPotentialEdges, hA, Nat.mul_comm] at hNat
    have hh := congrArg (fun x : ℕ => (x : ℝ)) hNat
    push_cast at hh ⊢
    linarith only [hh]
  have hshift := c4FixedDefectInternalCount_sub_choose_eq_shift D T
  have hselected : 0 < (m : ℝ)-c4FixedDefectInternalCount D T-W.present.card ∧
      (m : ℝ)-c4FixedDefectInternalCount D T-W.present.card < W.optional.card ∧
      ((m : ℝ)-c4FixedDefectInternalCount D T-W.present.card)/(W.optional.card : ℝ) ∈
        Icc beta (1-beta) := by
    rw [hcap]
    rcases hP with hP | hP
    · rw [hP, Nat.cast_zero, sub_zero]
      have heq : (m : ℝ)-c4FixedDefectInternalCount D T =
          (m : ℝ)-(D.cliquePart.card.choose 2 : ℝ)-(c4MatchingSignedShift D T : ℝ) := by
        linarith only [hshift]
      rw [heq]
      exact ⟨h.selected_pos, h.selected_lt_capacity, h.ratio_mem⟩
    · rw [hP]
      have heq : (m : ℝ)-c4FixedDefectInternalCount D T-z =
          (m : ℝ)-(D.cliquePart.card.choose 2 : ℝ)-(c4MatchingSignedShift D T : ℝ)-z := by
        linarith only [hshift]
      rw [heq]
      exact ⟨h.forced_selected_pos, h.forced_selected_lt_capacity, h.forced_ratio_mem⟩
  have hmR : (c4FixedDefectInternalCount D T : ℝ)+W.present.card ≤ m := by
    linarith only [hselected.1]
  have hm : c4FixedDefectInternalCount D T+W.present.card ≤ m := by exact_mod_cast hmR
  have hq : (W.quota T m : ℝ) = (m : ℝ)-c4FixedDefectInternalCount D T-W.present.card := by
    rw [C4FrozenCrossData.quota, Nat.cast_sub (show W.present.card ≤ m-c4FixedDefectInternalCount D T by omega),
      Nat.cast_sub (show c4FixedDefectInternalCount D T ≤ m by omega)]
  refine ⟨hm, ?_, ?_⟩
  · have hqle : (W.quota T m : ℝ) ≤ W.optional.card := by rw [hq]; exact hselected.2.1.le
    exact_mod_cast hqle
  · simpa only [DenseGraph.FixedCardinalityBlockModel.quotaParameter, hq, Set.mem_Icc]
      using hselected.2.2

/-- Feasible compact band for the unshifted full split reference slice. -/
theorem c4Split_quotaBand_of_samplingBounds {n m : ℕ} (D : C4Division (Fin n)) {beta : ℝ}
    (h : C4NondegenerateSamplingBounds n m D.cliquePart.card 0 0 beta) :
    D.cliquePart.card.choose 2 ≤ m ∧
      m-D.cliquePart.card.choose 2 ≤ (c4CrossPotentialEdges D).card ∧
      beta*(c4CrossPotentialEdges D).card ≤ ((m-D.cliquePart.card.choose 2 : ℕ) : ℝ) ∧
      ((m-D.cliquePart.card.choose 2 : ℕ) : ℝ) ≤ (1-beta)*(c4CrossPotentialEdges D).card := by
  have hparts := D.card_add
  simp only [Fintype.card_fin] at hparts
  have hA : D.independentPart.card = n-D.cliquePart.card := by omega
  have hcap : ((c4CrossPotentialEdges D).card : ℝ) =
      ((D.cliquePart.card*(n-D.cliquePart.card) : ℕ) : ℝ) := by
    rw [card_c4CrossPotentialEdges, hA, Nat.mul_comm]
  have hpos : (0 : ℝ) < (c4CrossPotentialEdges D).card := by
    simpa only [hcap, Nat.cast_zero, sub_zero] using h.capacity_pos
  have hmR : (D.cliquePart.card.choose 2 : ℝ) ≤ m := by
    have hh := h.selected_pos
    simp only [Int.cast_zero, sub_zero] at hh
    linarith only [hh]
  have hm : D.cliquePart.card.choose 2 ≤ m := by exact_mod_cast hmR
  have hq : ((m-D.cliquePart.card.choose 2 : ℕ) : ℝ) = (m : ℝ)-(D.cliquePart.card.choose 2 : ℝ) :=
    Nat.cast_sub hm
  have hband : beta ≤ ((m-D.cliquePart.card.choose 2 : ℕ) : ℝ)/(c4CrossPotentialEdges D).card ∧
      ((m-D.cliquePart.card.choose 2 : ℕ) : ℝ)/(c4CrossPotentialEdges D).card ≤ 1-beta := by
    simpa only [hq, hcap, Int.cast_zero, Nat.cast_zero, sub_zero, Set.mem_Icc] using h.ratio_mem
  refine ⟨hm, ?_, (le_div_iff₀ hpos).mp hband.1, (div_le_iff₀ hpos).mp hband.2⟩
  have hh : ((m-D.cliquePart.card.choose 2 : ℕ) : ℝ) ≤ (c4CrossPotentialEdges D).card := by
    rw [hq, hcap]
    simpa only [Int.cast_zero, Nat.cast_zero, sub_zero] using h.selected_lt_capacity.le
  exact_mod_cast hh

/-- A reduced slice is controlled by the genuine unshifted split fiber.
The cost is linear in the defect edge count and frozen-success count. -/
theorem c4Frozen_choose_le_splitFiber {n m : ℕ} {D : C4Division (Fin n)}
    (W : C4FrozenCrossData D) (T : SimpleGraph (Fin n)) {beta : ℝ}
    (hbeta : 0 < beta) (hbetaHalf : beta < 1/2)
    (hm : c4FixedDefectInternalCount D T+W.present.card ≤ m)
    (hq : W.quota T m ≤ W.optional.card)
    (hreference : C4NondegenerateSamplingBounds n m D.cliquePart.card 0 0 beta) :
    (W.optional.card.choose (W.quota T m) : ℝ) ≤ ((c4SplitFiber D m).card : ℝ)*
      Real.exp (DenseGraph.binomialCompactBandShiftConstant beta*
        ((finiteGraphEdges T).card+W.present.card)) := by
  obtain ⟨hmB,hq0,hlower,hupper⟩ := c4Split_quotaBand_of_samplingBounds D hreference
  have hcap : W.optional.card ≤ (c4CrossPotentialEdges D).card := Finset.card_le_card W.optional_subset
  have hdist : (Nat.dist (W.quota T m) (m-D.cliquePart.card.choose 2) : ℝ) ≤
      (finiteGraphEdges T).card+W.present.card := by
    have hqcast : (W.quota T m : ℝ) = (m : ℝ)-c4FixedDefectInternalCount D T-W.present.card := by
      rw [C4FrozenCrossData.quota, Nat.cast_sub (show W.present.card ≤ m-c4FixedDefectInternalCount D T by omega),
        Nat.cast_sub (show c4FixedDefectInternalCount D T ≤ m by omega)]
    have hdistEq : (Nat.dist (W.quota T m) (m-D.cliquePart.card.choose 2) : ℝ) =
        |(W.quota T m : ℝ)-((m-D.cliquePart.card.choose 2 : ℕ) : ℝ)| := by
      rcases le_total (W.quota T m) (m-D.cliquePart.card.choose 2) with hh | hh
      · have hhr : (W.quota T m : ℝ) ≤ ((m-D.cliquePart.card.choose 2 : ℕ) : ℝ) := by
          exact_mod_cast hh
        rw [Nat.dist_eq_sub_of_le hh, Nat.cast_sub hh, abs_of_nonpos (sub_nonpos.mpr hhr)]
        ring
      · have hhr : ((m-D.cliquePart.card.choose 2 : ℕ) : ℝ) ≤ (W.quota T m : ℝ) := by
          exact_mod_cast hh
        rw [Nat.dist_eq_sub_of_le_right hh, Nat.cast_sub hh, abs_of_nonneg (sub_nonneg.mpr hhr)]
    rw [hdistEq, hqcast, Nat.cast_sub hmB]
    have heq : (m : ℝ)-c4FixedDefectInternalCount D T-W.present.card-
        ((m : ℝ)-(D.cliquePart.card.choose 2 : ℝ)) =
        -((c4MatchingSignedShift D T : ℝ)+W.present.card) := by
      have hh := c4FixedDefectInternalCount_sub_choose_eq_shift D T
      linarith only [hh]
    rw [heq, abs_neg]
    exact (abs_add_le _ _).trans (by
      rw [abs_of_nonneg (Nat.cast_nonneg (α := ℝ) W.present.card)]
      have hh := c4MatchingSignedShift_abs_le D T
      linarith only [hh])
  have hchoose := DenseGraph.choose_le_choose_mul_exp_abs_shift_of_compact_band
    (hq.trans hcap) hq0 hbeta hbetaHalf hlower hupper
  have hC := (DenseGraph.binomialCompactBandShiftConstant_pos hbeta hbetaHalf).le
  calc
    _ ≤ (Nat.choose (c4CrossPotentialEdges D).card (W.quota T m) : ℝ) := by
      exact_mod_cast Nat.choose_le_choose (W.quota T m) hcap
    _ ≤ _ := hchoose.trans (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hdist hC)) (by positivity))
    _ = _ := by rw [card_c4SplitFiber, if_pos hmB, card_c4CrossPotentialEdges]

end InducedStars
