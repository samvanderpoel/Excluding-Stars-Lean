import InducedStars.FiniteModels.EntropyAsymptotics
import InducedStars.FiniteModels.Gnp
import InducedStars.FiniteModels.GnpFamilySlices
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# Maximum edge slices and their exact exponents

This file compares the full labeled induced-free `G(n,p)` event with its
largest exact-edge slice.  There are exactly `n.choose 2 + 1` possible
unordered edge counts, so the discrepancy between the sum and its largest
term is only this polynomial factor.

The maximizing index is total: `Fin (completeEdgeCount n + 1)` is nonempty
even when the graph family is empty.  In that case every slice has weight
zero and the selected index is harmless.
-/

noncomputable section

open Filter Finset Set
open scoped BigOperators Topology

namespace InducedStars

/-! ## Specialization of the arbitrary-family slice API -/

@[simp] private theorem graphFamilyEdgeSlice_inducedFree
    {h : ℕ} (H : SimpleGraph (Fin h)) (n m : ℕ) :
    graphFamilyEdgeSlice (inducedFreeGraphFinset H n) m =
      inducedFreeGraphFinsetWithEdges H n m := by
  ext G
  simp [graphFamilyEdgeSlice, inducedFreeGraphFinsetWithEdges]

@[simp] private theorem gnpGraphFamilySliceWeight_inducedFree
    {h : ℕ} (H : SimpleGraph (Fin h)) (n m : ℕ) (p : ℝ) :
    gnpGraphFamilySliceWeight (inducedFreeGraphFinset H n) m p =
      gnpInducedFreeSliceWeight H n m p := by
  unfold gnpGraphFamilySliceWeight gnpInducedFreeSliceWeight
  rw [graphFamilyEdgeSlice_inducedFree]
  rfl

/-- An edge count at which the exact induced-free slice weight is largest.

The definition is meaningful for every real `p`.  Probability estimates
below impose `p ∈ [0,1]` when nonnegativity of every summand is needed. -/
noncomputable def maximizingInducedFreeEdgeCount
    {h : ℕ} (H : SimpleGraph (Fin h)) (n : ℕ) (p : ℝ) :
    Fin (completeEdgeCount n + 1) :=
  maximizingGraphFamilyEdgeCount (inducedFreeGraphFinset H n) p

/-- The selected edge count dominates every admissible slice exactly. -/
theorem maximizingInducedFreeEdgeCount_spec
    {h : ℕ} (H : SimpleGraph (Fin h)) (n : ℕ) (p : ℝ)
    (j : Fin (completeEdgeCount n + 1)) :
    gnpInducedFreeSliceWeight H n j p ≤
    gnpInducedFreeSliceWeight H n
        (maximizingInducedFreeEdgeCount H n p) p := by
  simpa only [gnpGraphFamilySliceWeight_inducedFree,
    maximizingInducedFreeEdgeCount] using
    maximizingGraphFamilyEdgeCount_spec
      (inducedFreeGraphFinset H n) p j

/-- The selected edge count is a genuine graph edge count. -/
theorem maximizingInducedFreeEdgeCount_le_completeEdgeCount
    {h : ℕ} (H : SimpleGraph (Fin h)) (n : ℕ) (p : ℝ) :
    (maximizingInducedFreeEdgeCount H n p : ℕ) ≤
      completeEdgeCount n :=
  maximizingGraphFamilyEdgeCount_le_completeEdgeCount
    (inducedFreeGraphFinset H n) p

/-- The largest exact-edge induced-free `G(n,p)` slice weight. -/
noncomputable def maximalInducedFreeSliceWeight
    {h : ℕ} (H : SimpleGraph (Fin h)) (n : ℕ) (p : ℝ) : ℝ :=
  maximalGnpGraphFamilySliceWeight (inducedFreeGraphFinset H n) p

/-- The arbitrary-family maximum specializes to the weight of the selected
induced-free edge slice. -/
theorem maximalInducedFreeSliceWeight_eq_selected
    {h : ℕ} (H : SimpleGraph (Fin h)) (n : ℕ) (p : ℝ) :
    maximalInducedFreeSliceWeight H n p =
      gnpInducedFreeSliceWeight H n
        (maximizingInducedFreeEdgeCount H n p) p := by
  unfold maximalInducedFreeSliceWeight maximalGnpGraphFamilySliceWeight
    maximizingInducedFreeEdgeCount
  exact gnpGraphFamilySliceWeight_inducedFree H n _ p

/-- Every admissible exact-edge slice is bounded by the selected maximum. -/
theorem gnpInducedFreeSliceWeight_le_maximal
    {h : ℕ} (H : SimpleGraph (Fin h)) (n : ℕ) (p : ℝ)
    {m : ℕ} (hm : m ≤ completeEdgeCount n) :
    gnpInducedFreeSliceWeight H n m p ≤
      maximalInducedFreeSliceWeight H n p := by
  rw [← gnpGraphFamilySliceWeight_inducedFree]
  exact gnpGraphFamilySliceWeight_le_maximal
    (inducedFreeGraphFinset H n) p hm

/-- Exact attainment of the maximum by an ordinary natural edge count. -/
theorem maximalInducedFreeSliceWeight_attained
    {h : ℕ} (H : SimpleGraph (Fin h)) (n : ℕ) (p : ℝ) :
    ∃ m ≤ completeEdgeCount n,
      gnpInducedFreeSliceWeight H n m p =
        maximalInducedFreeSliceWeight H n p := by
  simpa only [gnpGraphFamilySliceWeight_inducedFree,
    maximalInducedFreeSliceWeight] using
    maximalGnpGraphFamilySliceWeight_attained
      (inducedFreeGraphFinset H n) p

/-- Every exact-edge slice weight is nonnegative on the probability domain. -/
theorem gnpInducedFreeSliceWeight_nonneg
    {h : ℕ} (H : SimpleGraph (Fin h)) (n m : ℕ) {p : ℝ}
    (hp : p ∈ Set.Icc (0 : ℝ) 1) :
    0 ≤ gnpInducedFreeSliceWeight H n m p := by
  rw [← gnpGraphFamilySliceWeight_inducedFree]
  exact gnpGraphFamilySliceWeight_nonneg (inducedFreeGraphFinset H n) hp

/-- The maximum slice is nonnegative on the probability domain. -/
theorem maximalInducedFreeSliceWeight_nonneg
    {h : ℕ} (H : SimpleGraph (Fin h)) (n : ℕ) {p : ℝ}
    (hp : p ∈ Set.Icc (0 : ℝ) 1) :
    0 ≤ maximalInducedFreeSliceWeight H n p :=
  gnpInducedFreeSliceWeight_nonneg H n _ hp

/-- On the open probability domain, a slice has positive mass exactly when
its labeled graph count is positive. -/
theorem gnpInducedFreeSliceWeight_pos_iff_count_pos
    {h : ℕ} (H : SimpleGraph (Fin h)) (n m : ℕ) {p : ℝ}
    (hp : p ∈ Set.Ioo (0 : ℝ) 1) :
    0 < gnpInducedFreeSliceWeight H n m p ↔
      0 < inducedFreeGraphCountWithEdges H n m := by
  rw [← gnpGraphFamilySliceWeight_inducedFree,
    gnpGraphFamilySliceWeight_pos_iff_nonempty
      (inducedFreeGraphFinset H n) hp,
    graphFamilyEdgeSlice_inducedFree,
    ← Finset.card_pos, ← inducedFreeGraphCountWithEdges_eq_card]

/-- If the whole induced-free family is empty, the total maximizing
construction has value zero for every real `p`. -/
theorem maximalInducedFreeSliceWeight_eq_zero_of_family_eq_empty
    {h : ℕ} (H : SimpleGraph (Fin h)) (n : ℕ) (p : ℝ)
    (hempty : inducedFreeGraphFinset H n = ∅) :
    maximalInducedFreeSliceWeight H n p = 0 :=
  maximalGnpGraphFamilySliceWeight_eq_zero_of_family_eq_empty
    (inducedFreeGraphFinset H n) p hempty

/-! ## Comparing the sum with its maximum -/

/-- The maximum exact-edge slice is at most the full induced-free event
probability. -/
theorem maximalInducedFreeSliceWeight_le_probability
    {h : ℕ} (H : SimpleGraph (Fin h)) (n : ℕ) {p : ℝ}
    (hp : p ∈ Set.Icc (0 : ℝ) 1) :
    maximalInducedFreeSliceWeight H n p ≤
      gnpInducedFreeProbability H n p :=
  maximalGnpGraphFamilySliceWeight_le_probability
    (inducedFreeGraphFinset H n) hp

/-- The full induced-free event is at most the number of edge levels times
its largest exact-edge slice.  This order estimate is algebraic and does not
need a hypothesis on `p`. -/
theorem gnpInducedFreeProbability_le_card_mul_maximalSlice
    {h : ℕ} (H : SimpleGraph (Fin h)) (n : ℕ) (p : ℝ) :
    gnpInducedFreeProbability H n p ≤
      ((completeEdgeCount n + 1 : ℕ) : ℝ) *
        maximalInducedFreeSliceWeight H n p :=
  gnpGraphEventProbability_le_card_mul_maximalFamilySlice
    (inducedFreeGraphFinset H n) p

/-- Positive event probability forces a positive maximizing slice. -/
theorem maximalInducedFreeSliceWeight_pos_of_probability_pos
    {h : ℕ} (H : SimpleGraph (Fin h)) (n : ℕ) (p : ℝ)
    (hprob : 0 < gnpInducedFreeProbability H n p) :
    0 < maximalInducedFreeSliceWeight H n p :=
  maximalGnpGraphFamilySliceWeight_pos_of_probability_pos
    (inducedFreeGraphFinset H n) p hprob

/-- On `[0,1]`, positivity of the maximum and positivity of the full event
are equivalent. -/
theorem maximalInducedFreeSliceWeight_pos_iff_probability_pos
    {h : ℕ} (H : SimpleGraph (Fin h)) (n : ℕ) {p : ℝ}
    (hp : p ∈ Set.Icc (0 : ℝ) 1) :
    0 < maximalInducedFreeSliceWeight H n p ↔
      0 < gnpInducedFreeProbability H n p := by
  constructor
  · exact fun hmax ↦ hmax.trans_le
      (maximalInducedFreeSliceWeight_le_probability H n hp)
  · exact maximalInducedFreeSliceWeight_pos_of_probability_pos H n p

/-- On `(0,1)`, a positive event makes the selected slice count positive. -/
theorem maximizingInducedFreeSlice_count_pos_of_probability_pos
    {h : ℕ} (H : SimpleGraph (Fin h)) (n : ℕ) {p : ℝ}
    (hp : p ∈ Set.Ioo (0 : ℝ) 1)
    (hprob : 0 < gnpInducedFreeProbability H n p) :
    0 < inducedFreeGraphCountWithEdges H n
      (maximizingInducedFreeEdgeCount H n p) := by
  rw [← gnpInducedFreeSliceWeight_pos_iff_count_pos H n _ hp]
  exact maximalInducedFreeSliceWeight_pos_of_probability_pos H n p hprob

/-- Hence a positive event supplies an actual graph in its maximizing
exact-edge slice. -/
theorem maximizingInducedFreeSlice_nonempty_of_probability_pos
    {h : ℕ} (H : SimpleGraph (Fin h)) (n : ℕ) {p : ℝ}
    (hp : p ∈ Set.Ioo (0 : ℝ) 1)
    (hprob : 0 < gnpInducedFreeProbability H n p) :
    (inducedFreeGraphFinsetWithEdges H n
      (maximizingInducedFreeEdgeCount H n p)).Nonempty := by
  rw [← graphFamilyEdgeSlice_inducedFree]
  exact maximizingGraphFamilyEdgeSlice_nonempty_of_probability_pos
    (inducedFreeGraphFinset H n) hp hprob

/-- The requested two-sided maximum-slice comparison. -/
theorem gnpInducedFreeMaximumSlice_bounds
    {h : ℕ} (H : SimpleGraph (Fin h)) (n : ℕ) {p : ℝ}
    (hp : p ∈ Set.Icc (0 : ℝ) 1) :
    maximalInducedFreeSliceWeight H n p ≤
        gnpInducedFreeProbability H n p ∧
      gnpInducedFreeProbability H n p ≤
        ((completeEdgeCount n + 1 : ℕ) : ℝ) *
          maximalInducedFreeSliceWeight H n p :=
  gnpGraphFamilyMaximumSlice_bounds (inducedFreeGraphFinset H n) hp

/-! ## Exact normalized slice exponents -/

/-- Exact normalized logarithm of a positive count times its binomial
edge-weight, in the entropy-plus-two-edge-terms form.  Every nonzero premise
used by `log2_mul` is established explicitly in the proof. -/
theorem normalizedLogExactSliceWeight_eq
    (n m count : ℕ) (p : ℝ)
    (hp : p ∈ Set.Ioo (0 : ℝ) 1)
    (hm : m ≤ completeEdgeCount n) (hcount : 0 < count)
    (hn : 2 ≤ n) :
    normalizedLogProbability n
        ((count : ℝ) * p ^ m *
          (1 - p) ^ (completeEdgeCount n - m)) =
      normalizedLogGraphCount n count +
        (m : ℝ) / (completeEdgeCount n : ℝ) * log2 p +
        (1 - (m : ℝ) / (completeEdgeCount n : ℝ)) *
          log2 (1 - p) := by
  have hcount0 : (count : ℝ) ≠ 0 := by
    exact_mod_cast hcount.ne'
  have hp0 : p ≠ 0 := hp.1.ne'
  have hq0 : 1 - p ≠ 0 := (sub_pos.mpr hp.2).ne'
  have hN0 : (completeEdgeCount n : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hn).ne'
  unfold normalizedLogProbability normalizedLogGraphCount normalizedLogAtGraphOrder
  rw [log2_mul (mul_ne_zero hcount0 (pow_ne_zero m hp0))
      (pow_ne_zero _ hq0),
    log2_mul hcount0 (pow_ne_zero m hp0),
    log2_pow, log2_pow, Nat.cast_sub hm]
  field_simp [hN0]

/-- The equivalent exact normalized exponent using the edge log-odds. -/
theorem normalizedLogExactSliceWeight_eq_odds
    (n m count : ℕ) (p : ℝ)
    (hp : p ∈ Set.Ioo (0 : ℝ) 1)
    (hm : m ≤ completeEdgeCount n) (hcount : 0 < count)
    (hn : 2 ≤ n) :
    normalizedLogProbability n
        ((count : ℝ) * p ^ m *
          (1 - p) ^ (completeEdgeCount n - m)) =
      normalizedLogGraphCount n count +
        (m : ℝ) / (completeEdgeCount n : ℝ) *
          log2 (p / (1 - p)) + log2 (1 - p) := by
  rw [normalizedLogExactSliceWeight_eq n m count p hp hm hcount hn,
    log2_div hp.1.ne' (sub_pos.mpr hp.2).ne']
  ring

/-- Exact exponent formula specialized to the induced-free slice count. -/
theorem normalizedLogGnpInducedFreeSliceWeight_eq
    {h : ℕ} (H : SimpleGraph (Fin h)) (n m : ℕ) (p : ℝ)
    (hp : p ∈ Set.Ioo (0 : ℝ) 1)
    (hm : m ≤ completeEdgeCount n)
    (hcount : 0 < inducedFreeGraphCountWithEdges H n m)
    (hn : 2 ≤ n) :
    normalizedLogProbability n (gnpInducedFreeSliceWeight H n m p) =
      normalizedLogGraphCount n
          (inducedFreeGraphCountWithEdges H n m) +
        (m : ℝ) / (completeEdgeCount n : ℝ) * log2 p +
        (1 - (m : ℝ) / (completeEdgeCount n : ℝ)) *
          log2 (1 - p) := by
  unfold gnpInducedFreeSliceWeight
  exact normalizedLogExactSliceWeight_eq n m
    (inducedFreeGraphCountWithEdges H n m) p hp hm hcount hn

/-- Log-odds form specialized to the induced-free slice count. -/
theorem normalizedLogGnpInducedFreeSliceWeight_eq_odds
    {h : ℕ} (H : SimpleGraph (Fin h)) (n m : ℕ) (p : ℝ)
    (hp : p ∈ Set.Ioo (0 : ℝ) 1)
    (hm : m ≤ completeEdgeCount n)
    (hcount : 0 < inducedFreeGraphCountWithEdges H n m)
    (hn : 2 ≤ n) :
    normalizedLogProbability n (gnpInducedFreeSliceWeight H n m p) =
      normalizedLogGraphCount n
          (inducedFreeGraphCountWithEdges H n m) +
        (m : ℝ) / (completeEdgeCount n : ℝ) *
          log2 (p / (1 - p)) + log2 (1 - p) := by
  unfold gnpInducedFreeSliceWeight
  exact normalizedLogExactSliceWeight_eq_odds n m
    (inducedFreeGraphCountWithEdges H n m) p hp hm hcount hn

/-! ## The polynomial number of edge levels is negligible -/

/-- The normalized base-two logarithm of the `completeEdgeCount n + 1`
possible edge levels tends to zero. -/
theorem normalizedLog_completeEdgeCount_add_one_tendsto_zero :
    Tendsto
      (fun n ↦ log2 ((completeEdgeCount n : ℝ) + 1) /
        (completeEdgeCount n : ℝ))
      Filter.atTop (nhds 0) := by
  have harg : Tendsto (fun n ↦ (completeEdgeCount n : ℝ) + 1)
      Filter.atTop Filter.atTop :=
    tendsto_atTop_add_const_right Filter.atTop 1
      tendsto_completeEdgeCount_cast_atTop
  have hraw :=
    (Real.tendsto_pow_log_div_mul_add_atTop
      (1 : ℝ) (-1) 1 one_ne_zero).comp harg
  have hscaled := hraw.div_const (Real.log 2)
  convert hscaled using 1 <;>
    simp only [Function.comp_apply, pow_one, one_mul, zero_div]
  funext n
  simp only [Function.comp_apply, log2, add_comm]
  ring

/-- The same negligible-factor statement through the public normalized-log
probability wrapper. -/
theorem normalizedLogPolynomialSliceFactor_tendsto_zero :
    Tendsto
      (fun n ↦ normalizedLogProbability n
        ((completeEdgeCount n : ℝ) + 1))
      Filter.atTop (nhds 0) := by
  simpa only [normalizedLogProbability] using
    normalizedLog_completeEdgeCount_add_one_tendsto_zero

end InducedStars
