import InducedStars.C4.LowDegreeCounting

/-!
# Shifted binomial sums for the low-degree matching classes

Paper: `eqn:c4-fmat-sum`. The exact signed defect shift is bounded by the
actual defect edge count. A compact-band adjacent-ratio bound charges that
shift through the weighted pattern count; the remaining matching penalty
then sums to a linear exponential bound.
-/

noncomputable section
open Finset Filter
open scoped Classical Topology
namespace InducedStars

theorem c4FixedDefectQuota_dist_reference_le {n m : ℕ} {D : C4Division (Fin n)}
    {T : SimpleGraph (Fin n)} (hT : C4DefectSupported D T)
    (hforced : c4FixedDefectInternalCount D T ≤ m) (hbase : D.cliquePart.card.choose 2 ≤ m) :
    Nat.dist (c4FixedDefectQuota D T m) (m-D.cliquePart.card.choose 2) ≤
      (finiteGraphEdges T).card := by
  have hsigned := c4FixedDefectInternalCount_signed D T
  have hedge := hT.edgeCount_eq
  rw [card_finiteGraphEdges_c4WithinGraph, card_finiteGraphEdges_c4WithinGraph] at hedge
  unfold c4FixedDefectQuota
  rcases le_total (m-c4FixedDefectInternalCount D T) (m-D.cliquePart.card.choose 2) with h | h
  · rw [Nat.dist_eq_sub_of_le h]
    omega
  · rw [Nat.dist_eq_sub_of_le_right h]
    omega

/-- Both signs of the defect shift are paid by one actual edge-count cost.
Infeasible fixed-defect fibers have cardinality zero. -/
theorem c4FixedDefectFiber_card_le_reference_mul_exp_edges {n m : ℕ}
    (D : C4Division (Fin n)) (T : SimpleGraph (Fin n))
    (hT : C4DefectSupported D T) {beta : ℝ}
    (hbeta : 0 < beta) (hhalf : beta < 1/2)
    (hbase : D.cliquePart.card.choose 2 ≤ m)
    (href : m-D.cliquePart.card.choose 2 ≤ D.independentPart.card*D.cliquePart.card)
    (hlo : beta*(D.independentPart.card*D.cliquePart.card : ℕ) ≤
      (m-D.cliquePart.card.choose 2 : ℕ))
    (hhi : ((m-D.cliquePart.card.choose 2 : ℕ) : ℝ) ≤
      (1-beta)*(D.independentPart.card*D.cliquePart.card : ℕ)) :
    ((c4FixedDefectFiber D T m).card : ℝ) ≤
      (Nat.choose (D.independentPart.card*D.cliquePart.card)
        (m-D.cliquePart.card.choose 2) : ℝ)*
        Real.exp (DenseGraph.binomialCompactBandShiftConstant beta*(finiteGraphEdges T).card) := by
  rw [card_c4FixedDefectFiber D T hT]
  split_ifs with hforced
  · by_cases hcap : c4FixedDefectQuota D T m ≤ D.independentPart.card*D.cliquePart.card
    · apply (DenseGraph.choose_le_choose_mul_exp_abs_shift_of_compact_band
        hcap href hbeta hhalf hlo hhi).trans
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Real.exp_le_exp.mpr
      apply mul_le_mul_of_nonneg_left _
        (DenseGraph.binomialCompactBandShiftConstant_pos hbeta hhalf).le
      exact_mod_cast c4FixedDefectQuota_dist_reference_le hT hforced hbase
    · rw [Nat.choose_eq_zero_of_lt (lt_of_not_ge hcap), Nat.cast_zero]
      positivity
  · simp only [Nat.cast_zero]
    positivity

def c4LowDegreeMatchingSliceSum {n : ℕ} (D : C4Division (Fin n))
    (m : ℕ) (alpha : ℝ) (k : ℕ) : ℝ :=
  ∑ T ∈ c4LowDegreeDefectPatternFinset D alpha k, ((c4FixedDefectFiber D T m).card : ℝ)

theorem c4LowDegreeMatchingSliceSum_le {n m : ℕ} (D : C4Division (Fin n)) (k : ℕ)
    {alpha beta : ℝ} (halpha : 0 ≤ alpha) (hahalf : alpha ≤ 1/2)
    (hbeta : 0 < beta) (hhalf : beta < 1/2)
    (hbase : D.cliquePart.card.choose 2 ≤ m)
    (href : m-D.cliquePart.card.choose 2 ≤ D.independentPart.card*D.cliquePart.card)
    (hlo : beta*(D.independentPart.card*D.cliquePart.card : ℕ) ≤
      (m-D.cliquePart.card.choose 2 : ℕ))
    (hhi : ((m-D.cliquePart.card.choose 2 : ℕ) : ℝ) ≤
      (1-beta)*(D.independentPart.card*D.cliquePart.card : ℕ)) :
    c4LowDegreeMatchingSliceSum D m alpha k ≤
      (Nat.choose (D.independentPart.card*D.cliquePart.card)
        (m-D.cliquePart.card.choose 2) : ℝ)*
        Real.exp (4*(k : ℝ)*((n : ℝ)*(Real.binEntropy alpha+
          DenseGraph.binomialCompactBandShiftConstant beta*alpha)+Real.log (n+1))+2*k) := by
  unfold c4LowDegreeMatchingSliceSum
  calc
    _ ≤ ∑ T ∈ c4LowDegreeDefectPatternFinset D alpha k,
        (Nat.choose (D.independentPart.card*D.cliquePart.card)
          (m-D.cliquePart.card.choose 2) : ℝ)*
          Real.exp (DenseGraph.binomialCompactBandShiftConstant beta*(finiteGraphEdges T).card) :=
      sum_le_sum fun T hT ↦ c4FixedDefectFiber_card_le_reference_mul_exp_edges D T
        (mem_c4LowDegreeDefectPatternFinset.mp hT).1 hbeta hhalf hbase href hlo hhi
    _ = (Nat.choose (D.independentPart.card*D.cliquePart.card)
        (m-D.cliquePart.card.choose 2) : ℝ)*
        ∑ T ∈ c4LowDegreeDefectPatternFinset D alpha k,
          Real.exp (DenseGraph.binomialCompactBandShiftConstant beta*(finiteGraphEdges T).card) :=
      (mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (sum_c4LowDegreeDefectPattern_exp_edges_le D k halpha hahalf
        (DenseGraph.binomialCompactBandShiftConstant_pos hbeta hhalf).le) (by positivity)

/-- The actual shifted slices, multiplied by a proved matching penalty,
sum to a linear exponential times the reference split fiber. This is a
finite numerical summation theorem, not an assumed counting estimate. -/
theorem exists_alpha0_c4LowDegree_matching_sum {beta c : ℝ}
    (hbeta : 0 < beta) (hhalf : beta < 1/2) (hc : 0 < c) :
    ∃ alpha0 : ℝ, 0 < alpha0 ∧ alpha0 ≤ 1/2 ∧
      ∀ᶠ n : ℕ in atTop, ∀ alpha ∈ Set.Icc (0 : ℝ) alpha0,
        ∀ D : C4Division (Fin n), ∀ m : ℕ,
          D.cliquePart.card.choose 2 ≤ m →
          m-D.cliquePart.card.choose 2 ≤ D.independentPart.card*D.cliquePart.card →
          beta*(D.independentPart.card*D.cliquePart.card : ℕ) ≤
            (m-D.cliquePart.card.choose 2 : ℕ) →
          ((m-D.cliquePart.card.choose 2 : ℕ) : ℝ) ≤
            (1-beta)*(D.independentPart.card*D.cliquePart.card : ℕ) →
          (∑ k ∈ Icc 1 n, Real.exp (-c*k*n)*c4LowDegreeMatchingSliceSum D m alpha k) ≤
            (Nat.choose (D.independentPart.card*D.cliquePart.card)
              (m-D.cliquePart.card.choose 2) : ℝ)*Real.exp (-(c/4)*n) := by
  let C := DenseGraph.binomialCompactBandShiftConstant beta
  have hC : 0 ≤ C := (DenseGraph.binomialCompactBandShiftConstant_pos hbeta hhalf).le
  obtain ⟨alpha0,ha0,hahalf,hcount⟩ :=
    exists_alpha0_c4LowDegree_weighted_count hC (show 0 < c/2 by positivity)
  refine ⟨alpha0,ha0,hahalf,?_⟩
  filter_upwards [hcount,DenseGraph.eventually_sum_Icc_exp_neg_mul_le
    (show 0 < c/2 by positivity)] with n hcount hsum alpha ha D m hbase href hlo hhi
  let B : ℝ := Nat.choose (D.independentPart.card*D.cliquePart.card)
    (m-D.cliquePart.card.choose 2)
  have hpoint (k : ℕ) : c4LowDegreeMatchingSliceSum D m alpha k ≤ B*Real.exp ((c/2)*k*n) := by
    unfold c4LowDegreeMatchingSliceSum
    calc
      _ ≤ ∑ T ∈ c4LowDegreeDefectPatternFinset D alpha k,
          B*Real.exp (C*(finiteGraphEdges T).card) :=
        sum_le_sum fun T hT ↦ c4FixedDefectFiber_card_le_reference_mul_exp_edges D T
          (mem_c4LowDegreeDefectPatternFinset.mp hT).1 hbeta hhalf hbase href hlo hhi
      _ = B*∑ T ∈ c4LowDegreeDefectPatternFinset D alpha k,
          Real.exp (C*(finiteGraphEdges T).card) := (mul_sum _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left (hcount alpha ha D k) (by positivity)
  calc
    _ ≤ ∑ k ∈ Icc 1 n, B*Real.exp (-((c/2)*(k : ℝ)*(n : ℝ))) := by
      apply sum_le_sum
      intro k hk
      calc
        _ ≤ Real.exp (-c*k*n)*(B*Real.exp ((c/2)*k*n)) :=
          mul_le_mul_of_nonneg_left (hpoint k) (Real.exp_pos _).le
        _ = B*(Real.exp (-c*k*n)*Real.exp ((c/2)*k*n)) := by ring
        _ = _ := by rw [← Real.exp_add]; congr 2 <;> ring
    _ = B*∑ k ∈ Icc 1 n, Real.exp (-((c/2)*(k : ℝ)*(n : ℝ))) := (mul_sum _ _ _).symm
    _ ≤ B*Real.exp (-((c/2/2)*(n : ℝ))) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by congr 2 <;> ring

end InducedStars
