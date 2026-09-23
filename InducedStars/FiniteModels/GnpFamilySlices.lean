import InducedStars.FiniteModels.GnpCore
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# Exact-edge slices of arbitrary labeled graph families

This file partitions an arbitrary finite family of labeled graphs by its
unordered edge count and compares its full `G(n,p)` mass with a maximizing
slice.  There are `completeEdgeCount n + 1` possible edge counts, including
all zero and empty-family cases.  The maximizing index is therefore total;
when the family is empty, every slice and every slice weight is zero.
-/

noncomputable section

open Finset Set
open scoped BigOperators

namespace InducedStars

attribute [local instance] Classical.propDecidable

/-- Use the project's canonical finite edge-set choice while reasoning with
Mathlib's `edgeFinset`. -/
noncomputable local instance gnpFamilySlicesEdgeSetFintype {n : ℕ}
    (G : SimpleGraph (Fin n)) : Fintype G.edgeSet :=
  graphFamiliesEdgeSetFintype G

/-! ## Exact-edge slices -/

/-- The members of `Q` having exactly `m` unordered edges. -/
noncomputable def graphFamilyEdgeSlice {n : ℕ}
    (Q : Finset (SimpleGraph (Fin n))) (m : ℕ) :
    Finset (SimpleGraph (Fin n)) := by
  classical
  exact Q.filter fun G ↦ G.edgeFinset.card = m

@[simp] theorem mem_graphFamilyEdgeSlice {n m : ℕ}
    {Q : Finset (SimpleGraph (Fin n))} {G : SimpleGraph (Fin n)} :
    G ∈ graphFamilyEdgeSlice Q m ↔
      G ∈ Q ∧ G.edgeFinset.card = m := by
  classical
  simp [graphFamilyEdgeSlice]

/-- Instance-independent membership form using the graphon layer's neutral
finite edge set. -/
theorem mem_graphFamilyEdgeSlice_iff_finiteGraphEdges {n m : ℕ}
    {Q : Finset (SimpleGraph (Fin n))} {G : SimpleGraph (Fin n)} :
    G ∈ graphFamilyEdgeSlice Q m ↔
      G ∈ Q ∧ (finiteGraphEdges G).card = m := by
  rw [mem_graphFamilyEdgeSlice]
  have hedge : finiteGraphEdges G = G.edgeFinset := by
    ext e
    rw [mem_finiteGraphEdges, SimpleGraph.mem_edgeFinset]
  constructor
  · rintro ⟨hQ, hcard⟩
    exact ⟨hQ, by rw [hedge]; exact hcard⟩
  · rintro ⟨hQ, hcard⟩
    exact ⟨hQ, by rw [← hedge]; exact hcard⟩

/-- An impossible edge-count slice is empty, independently of `Q`. -/
theorem graphFamilyEdgeSlice_eq_empty_of_completeEdgeCount_lt
    {n m : ℕ} (Q : Finset (SimpleGraph (Fin n)))
    (hm : completeEdgeCount n < m) :
    graphFamilyEdgeSlice Q m = ∅ := by
  apply Finset.not_nonempty_iff_eq_empty.mp
  rintro ⟨G, hG⟩
  have hcount := (mem_graphFamilyEdgeSlice.mp hG).2
  have hle := card_edgeFinset_le_completeEdgeCount G
  omega

/-- The exact `G(n,p)` weight of the `m`-edge slice of `Q`.  If the slice is
empty (in particular if `Q` is empty or `m` is impossible), its value is
zero for every real `p`. -/
noncomputable def gnpGraphFamilySliceWeight {n : ℕ}
    (Q : Finset (SimpleGraph (Fin n))) (m : ℕ) (p : ℝ) : ℝ :=
  ((graphFamilyEdgeSlice Q m).card : ℝ) * p ^ m *
    (1 - p) ^ (completeEdgeCount n - m)

/-- The finite event probability of an exact-edge slice is its cardinality
times the common graph weight on that slice. -/
theorem gnpGraphEventProbability_graphFamilyEdgeSlice {n : ℕ}
    (Q : Finset (SimpleGraph (Fin n))) (m : ℕ) (p : ℝ) :
    gnpGraphEventProbability p (graphFamilyEdgeSlice Q m) =
      gnpGraphFamilySliceWeight Q m p := by
  classical
  unfold gnpGraphEventProbability gnpGraphFamilySliceWeight
  rw [show (∑ G ∈ graphFamilyEdgeSlice Q m, gnpGraphWeight p G) =
      ∑ _G ∈ graphFamilyEdgeSlice Q m,
        p ^ m * (1 - p) ^ (completeEdgeCount n - m) by
    apply Finset.sum_congr rfl
    intro G hG
    have hcount : G.edgeFinset.card = m :=
      (mem_graphFamilyEdgeSlice.mp hG).2
    unfold gnpGraphWeight
    rw [hcount]]
  simp [mul_assoc]

/-- A slice above the complete graph's edge count has weight zero. -/
theorem gnpGraphFamilySliceWeight_eq_zero_of_completeEdgeCount_lt
    {n m : ℕ} (Q : Finset (SimpleGraph (Fin n))) (p : ℝ)
    (hm : completeEdgeCount n < m) :
    gnpGraphFamilySliceWeight Q m p = 0 := by
  rw [← gnpGraphEventProbability_graphFamilyEdgeSlice,
    graphFamilyEdgeSlice_eq_empty_of_completeEdgeCount_lt Q hm]
  simp [gnpGraphEventProbability]

/-- The full event is the disjoint sum of its admissible edge-count slices.
Every labeled graph in `Q` occurs in exactly one summand. -/
theorem gnpGraphEventProbability_eq_sum_graphFamilySliceWeights {n : ℕ}
    (Q : Finset (SimpleGraph (Fin n))) (p : ℝ) :
    gnpGraphEventProbability p Q =
      ∑ m ∈ Finset.range (completeEdgeCount n + 1),
        gnpGraphFamilySliceWeight Q m p := by
  classical
  unfold gnpGraphEventProbability
  rw [show (∑ G ∈ Q, gnpGraphWeight p G) =
      ∑ m ∈ Finset.range (completeEdgeCount n + 1),
        ∑ G ∈ graphFamilyEdgeSlice Q m, gnpGraphWeight p G by
    symm
    simp only [graphFamilyEdgeSlice]
    apply Finset.sum_fiberwise_of_maps_to
    intro G hG
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le
      (card_edgeFinset_le_completeEdgeCount G))]
  apply Finset.sum_congr rfl
  intro m _hm
  exact gnpGraphEventProbability_graphFamilyEdgeSlice Q m p

/-! ## A maximizing slice -/

private theorem exists_maximizingGraphFamilyEdgeCount {n : ℕ}
    (Q : Finset (SimpleGraph (Fin n))) (p : ℝ) :
    ∃ m : Fin (completeEdgeCount n + 1),
      ∀ j : Fin (completeEdgeCount n + 1),
        gnpGraphFamilySliceWeight Q j p ≤
          gnpGraphFamilySliceWeight Q m p := by
  let s : Finset (Fin (completeEdgeCount n + 1)) := Finset.univ
  have hs : s.Nonempty := by
    refine ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
  obtain ⟨m, _hm, hmax⟩ := Finset.exists_max_image s
    (fun j ↦ gnpGraphFamilySliceWeight Q j p) hs
  exact ⟨m, fun j ↦ hmax j (Finset.mem_univ j)⟩

/-- An admissible edge count maximizing the `G(n,p)` weight of a slice of
`Q`.  For an empty family, the arbitrary selected index still has weight
zero. -/
noncomputable def maximizingGraphFamilyEdgeCount {n : ℕ}
    (Q : Finset (SimpleGraph (Fin n))) (p : ℝ) :
    Fin (completeEdgeCount n + 1) :=
  Classical.choose (exists_maximizingGraphFamilyEdgeCount Q p)

/-- The selected edge count dominates every admissible slice. -/
theorem maximizingGraphFamilyEdgeCount_spec {n : ℕ}
    (Q : Finset (SimpleGraph (Fin n))) (p : ℝ)
    (j : Fin (completeEdgeCount n + 1)) :
    gnpGraphFamilySliceWeight Q j p ≤
      gnpGraphFamilySliceWeight Q
        (maximizingGraphFamilyEdgeCount Q p) p :=
  (Classical.choose_spec
    (exists_maximizingGraphFamilyEdgeCount Q p)) j

/-- The selected index is an ordinary feasible edge count. -/
theorem maximizingGraphFamilyEdgeCount_le_completeEdgeCount {n : ℕ}
    (Q : Finset (SimpleGraph (Fin n))) (p : ℝ) :
    (maximizingGraphFamilyEdgeCount Q p : ℕ) ≤
      completeEdgeCount n :=
  Nat.le_of_lt_succ (maximizingGraphFamilyEdgeCount Q p).isLt

/-- The maximum exact-edge slice weight of `Q`. -/
noncomputable def maximalGnpGraphFamilySliceWeight {n : ℕ}
    (Q : Finset (SimpleGraph (Fin n))) (p : ℝ) : ℝ :=
  gnpGraphFamilySliceWeight Q (maximizingGraphFamilyEdgeCount Q p) p

/-- Every admissible exact-edge slice is bounded by the selected maximum. -/
theorem gnpGraphFamilySliceWeight_le_maximal {n : ℕ}
    (Q : Finset (SimpleGraph (Fin n))) (p : ℝ)
    {m : ℕ} (hm : m ≤ completeEdgeCount n) :
    gnpGraphFamilySliceWeight Q m p ≤
      maximalGnpGraphFamilySliceWeight Q p := by
  exact maximizingGraphFamilyEdgeCount_spec Q p
    ⟨m, Nat.lt_succ_of_le hm⟩

/-- Exact attainment of the maximum by a natural edge count. -/
theorem maximalGnpGraphFamilySliceWeight_attained {n : ℕ}
    (Q : Finset (SimpleGraph (Fin n))) (p : ℝ) :
    ∃ m ≤ completeEdgeCount n,
      gnpGraphFamilySliceWeight Q m p =
        maximalGnpGraphFamilySliceWeight Q p :=
  ⟨maximizingGraphFamilyEdgeCount Q p,
    maximizingGraphFamilyEdgeCount_le_completeEdgeCount Q p, rfl⟩

/-- Every slice weight is nonnegative on the probability domain. -/
theorem gnpGraphFamilySliceWeight_nonneg {n m : ℕ}
    (Q : Finset (SimpleGraph (Fin n))) {p : ℝ}
    (hp : p ∈ Set.Icc (0 : ℝ) 1) :
    0 ≤ gnpGraphFamilySliceWeight Q m p := by
  unfold gnpGraphFamilySliceWeight
  exact mul_nonneg
    (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hp.1 _))
    (pow_nonneg (sub_nonneg.mpr hp.2) _)

/-- On the open probability domain, a slice has positive mass exactly when
it contains a graph. -/
theorem gnpGraphFamilySliceWeight_pos_iff_nonempty {n m : ℕ}
    (Q : Finset (SimpleGraph (Fin n))) {p : ℝ}
    (hp : p ∈ Set.Ioo (0 : ℝ) 1) :
    0 < gnpGraphFamilySliceWeight Q m p ↔
      (graphFamilyEdgeSlice Q m).Nonempty := by
  unfold gnpGraphFamilySliceWeight
  constructor
  · intro hweight
    rw [← Finset.card_pos]
    by_contra hcard
    have hcard0 : (graphFamilyEdgeSlice Q m).card = 0 :=
      Nat.eq_zero_of_not_pos hcard
    simp [hcard0] at hweight
  · intro hne
    exact mul_pos
      (mul_pos (Nat.cast_pos.mpr (Finset.card_pos.mpr hne))
        (pow_pos hp.1 _))
      (pow_pos (sub_pos.mpr hp.2) _)

/-- For an empty family every slice, including the selected maximum, has
weight zero for every real `p`. -/
theorem maximalGnpGraphFamilySliceWeight_eq_zero_of_family_eq_empty
    {n : ℕ} (Q : Finset (SimpleGraph (Fin n))) (p : ℝ)
    (hempty : Q = ∅) :
    maximalGnpGraphFamilySliceWeight Q p = 0 := by
  subst Q
  simp [maximalGnpGraphFamilySliceWeight, gnpGraphFamilySliceWeight,
    graphFamilyEdgeSlice]

/-! ## Comparing the sum with its maximum -/

/-- On `[0,1]`, the maximum slice is at most the full event probability. -/
theorem maximalGnpGraphFamilySliceWeight_le_probability {n : ℕ}
    (Q : Finset (SimpleGraph (Fin n))) {p : ℝ}
    (hp : p ∈ Set.Icc (0 : ℝ) 1) :
    maximalGnpGraphFamilySliceWeight Q p ≤
      gnpGraphEventProbability p Q := by
  rw [gnpGraphEventProbability_eq_sum_graphFamilySliceWeights]
  unfold maximalGnpGraphFamilySliceWeight
  exact Finset.single_le_sum
    (s := Finset.range (completeEdgeCount n + 1))
    (f := fun m ↦ gnpGraphFamilySliceWeight Q m p)
    (fun m _hm ↦ gnpGraphFamilySliceWeight_nonneg Q hp)
    (Finset.mem_range.mpr (maximizingGraphFamilyEdgeCount Q p).isLt)

/-- The full event mass is at most the number of edge levels times its
largest slice.  This algebraic estimate remains valid for every real `p`. -/
theorem gnpGraphEventProbability_le_card_mul_maximalFamilySlice {n : ℕ}
    (Q : Finset (SimpleGraph (Fin n))) (p : ℝ) :
    gnpGraphEventProbability p Q ≤
      ((completeEdgeCount n + 1 : ℕ) : ℝ) *
        maximalGnpGraphFamilySliceWeight Q p := by
  rw [gnpGraphEventProbability_eq_sum_graphFamilySliceWeights]
  calc
    (∑ m ∈ Finset.range (completeEdgeCount n + 1),
        gnpGraphFamilySliceWeight Q m p) ≤
        ∑ _m ∈ Finset.range (completeEdgeCount n + 1),
          maximalGnpGraphFamilySliceWeight Q p := by
      apply Finset.sum_le_sum
      intro m hm
      exact gnpGraphFamilySliceWeight_le_maximal Q p
        (Nat.le_of_lt_succ (Finset.mem_range.mp hm))
    _ = ((completeEdgeCount n + 1 : ℕ) : ℝ) *
        maximalGnpGraphFamilySliceWeight Q p := by simp

/-- A positive full event mass forces the selected maximum to be positive,
without an additional assumption on `p`. -/
theorem maximalGnpGraphFamilySliceWeight_pos_of_probability_pos {n : ℕ}
    (Q : Finset (SimpleGraph (Fin n))) (p : ℝ)
    (hprob : 0 < gnpGraphEventProbability p Q) :
    0 < maximalGnpGraphFamilySliceWeight Q p := by
  have hupper :=
    gnpGraphEventProbability_le_card_mul_maximalFamilySlice Q p
  have hfactor : 0 < (((completeEdgeCount n + 1 : ℕ) : ℝ)) := by
    positivity
  nlinarith

/-- On `(0,1)`, a positive event supplies an actual member in the selected
maximizing slice. -/
theorem maximizingGraphFamilyEdgeSlice_nonempty_of_probability_pos
    {n : ℕ} (Q : Finset (SimpleGraph (Fin n))) {p : ℝ}
    (hp : p ∈ Set.Ioo (0 : ℝ) 1)
    (hprob : 0 < gnpGraphEventProbability p Q) :
    (graphFamilyEdgeSlice Q (maximizingGraphFamilyEdgeCount Q p)).Nonempty := by
  rw [← gnpGraphFamilySliceWeight_pos_iff_nonempty Q hp]
  exact maximalGnpGraphFamilySliceWeight_pos_of_probability_pos Q p hprob

/-- The two-sided maximum-slice comparison, including the polynomial
`completeEdgeCount n + 1` factor. -/
theorem gnpGraphFamilyMaximumSlice_bounds {n : ℕ}
    (Q : Finset (SimpleGraph (Fin n))) {p : ℝ}
    (hp : p ∈ Set.Icc (0 : ℝ) 1) :
    maximalGnpGraphFamilySliceWeight Q p ≤
        gnpGraphEventProbability p Q ∧
      gnpGraphEventProbability p Q ≤
        ((completeEdgeCount n + 1 : ℕ) : ℝ) *
          maximalGnpGraphFamilySliceWeight Q p :=
  ⟨maximalGnpGraphFamilySliceWeight_le_probability Q hp,
    gnpGraphEventProbability_le_card_mul_maximalFamilySlice Q p⟩

/-! ## Exact normalized slice exponent -/

/-- Exact normalized exponent of a positive arbitrary-family slice.  This
is kept in the finite-model layer so later generic weighted upper bounds do
not need to import the induced-free asymptotic specialization. -/
theorem normalizedLogGnpGraphFamilySliceWeight_eq {n m : ℕ}
    (Q : Finset (SimpleGraph (Fin n))) (p : ℝ)
    (hp : p ∈ Set.Ioo (0 : ℝ) 1)
    (hm : m ≤ completeEdgeCount n)
    (hcount : 0 < (graphFamilyEdgeSlice Q m).card)
    (hn : 2 ≤ n) :
    normalizedLogProbability n (gnpGraphFamilySliceWeight Q m p) =
      normalizedLogGraphCount n (graphFamilyEdgeSlice Q m).card +
        (m : ℝ) / (completeEdgeCount n : ℝ) * log2 p +
        (1 - (m : ℝ) / (completeEdgeCount n : ℝ)) *
          log2 (1 - p) := by
  have hcount0 : ((graphFamilyEdgeSlice Q m).card : ℝ) ≠ 0 := by
    exact_mod_cast hcount.ne'
  have hp0 : p ≠ 0 := hp.1.ne'
  have hq0 : 1 - p ≠ 0 := (sub_pos.mpr hp.2).ne'
  have hN0 : (completeEdgeCount n : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hn).ne'
  unfold gnpGraphFamilySliceWeight normalizedLogProbability
    normalizedLogGraphCount normalizedLogAtGraphOrder
  rw [log2_mul (mul_ne_zero hcount0 (pow_ne_zero m hp0))
      (pow_ne_zero _ hq0),
    log2_mul hcount0 (pow_ne_zero m hp0),
    log2_pow, log2_pow, Nat.cast_sub hm]
  field_simp [hN0]

/-- The same exact exponent written with the edge log-odds. -/
theorem normalizedLogGnpGraphFamilySliceWeight_eq_odds {n m : ℕ}
    (Q : Finset (SimpleGraph (Fin n))) (p : ℝ)
    (hp : p ∈ Set.Ioo (0 : ℝ) 1)
    (hm : m ≤ completeEdgeCount n)
    (hcount : 0 < (graphFamilyEdgeSlice Q m).card)
    (hn : 2 ≤ n) :
    normalizedLogProbability n (gnpGraphFamilySliceWeight Q m p) =
      normalizedLogGraphCount n (graphFamilyEdgeSlice Q m).card +
        (m : ℝ) / (completeEdgeCount n : ℝ) *
          log2 (p / (1 - p)) + log2 (1 - p) := by
  rw [normalizedLogGnpGraphFamilySliceWeight_eq Q p hp hm hcount hn,
    log2_div hp.1.ne' (sub_pos.mpr hp.2).ne']
  ring

end InducedStars
