import InducedStars.Structure.Supercritical.AggregationParameters
import InducedStars.Structure.Supercritical.CoPartiteFamilies
import InducedStars.Structure.Supercritical.CoverMultiplicity
import DenseGraph.Combinatorics.ExponentialSums

/-!
# Finite and asymptotic aggregation in the strictly supercritical regime

The definitions in this file are exact finite sums.  The first main theorem
is the deterministic four-way decomposition into far, clean nonempty-sparse,
medium-degree, and fixed-defect families.  The final results are composition
lemmas: once the four separately proved estimates are supplied, no hidden
uniformity or asymptotic bookkeeping remains.
-/

noncomputable section

open Filter Finset Set
open scoped BigOperators

namespace InducedStars

noncomputable local instance globalAggregationGraphDecidableEq (n : ℕ) :
    DecidableEq (SimpleGraph (Fin n)) := Classical.decEq _

/-! ## Exact finite totals -/

/-- Union of clean canonical-division families whose sparse set is nonempty.
For the finitely many `n < k - 1` it is defined to be empty. -/
noncomputable def supercriticalCleanNonemptySparseGraphFinset
    (k : ℕ) (hk : 3 ≤ k) (gamma : ℝ)
    (hgamma : gamma ∈ Set.Ico (gammaK k) 1)
    (m n : ℕ) (tau : ℝ) : Finset (SimpleGraph (Fin n)) := by
  classical
  exact if hn : k - 1 ≤ n then
    (allSupercriticalDivisions k n).biUnion fun D ↦
      if D.sparse.Nonempty then
        supercriticalCleanDivisionGraphFinset
          k hk gamma hgamma m n tau hn D
      else ∅
  else ∅

/-- Union of the medium-degree canonical-division families. -/
noncomputable def supercriticalMediumTotalGraphFinset
    (k : ℕ) (hk : 3 ≤ k) (gamma : ℝ)
    (hgamma : gamma ∈ Set.Ico (gammaK k) 1)
    (alpha : ℝ) (m n : ℕ) (tau : ℝ) :
    Finset (SimpleGraph (Fin n)) := by
  classical
  exact if hn : k - 1 ≤ n then
    (allSupercriticalDivisions k n).biUnion fun D ↦
      supercriticalMediumDegreeGraphFinset
        k hk gamma hgamma alpha m n tau hn D
  else ∅

/-- Union of every nonmedium fixed combined-defect fiber. -/
noncomputable def supercriticalFixedDefectTotalGraphFinset
    (k : ℕ) (hk : 3 ≤ k) (gamma : ℝ)
    (hgamma : gamma ∈ Set.Ico (gammaK k) 1)
    (alpha : ℝ) (m n : ℕ) (tau : ℝ) :
    Finset (SimpleGraph (Fin n)) := by
  classical
  exact if hn : k - 1 ≤ n then
    (allSupercriticalDivisions k n).biUnion fun D ↦
      (supercriticalCombinedDefectPatternFinset
        k hk gamma hgamma m n tau hn D).biUnion fun T ↦
          supercriticalFixedDefectGraphFinset
            k hk gamma hgamma alpha m n tau hn D T
  else ∅

/-- Exact sum of clean nonempty-sparse fiber cardinalities.  This is a sum,
not the cardinality of the union; canonicality later makes the summands
disjoint, while the union-bound arguments only need the displayed sum. -/
noncomputable def supercriticalCleanTotal
    (k : ℕ) (hk : 3 ≤ k) (gamma : ℝ)
    (hgamma : gamma ∈ Set.Ico (gammaK k) 1)
    (m n : ℕ) (tau : ℝ) : ℕ := by
  classical
  exact if hn : k - 1 ≤ n then
    ∑ D ∈ allSupercriticalDivisions k n,
      if D.sparse.Nonempty then
        (supercriticalCleanDivisionGraphFinset
          k hk gamma hgamma m n tau hn D).card
      else 0
  else 0

/-- Exact sum of medium-degree fiber cardinalities over every division. -/
noncomputable def supercriticalMediumTotal
    (k : ℕ) (hk : 3 ≤ k) (gamma : ℝ)
    (hgamma : gamma ∈ Set.Ico (gammaK k) 1)
    (alpha : ℝ) (m n : ℕ) (tau : ℝ) : ℕ := by
  classical
  exact if hn : k - 1 ≤ n then
    ∑ D ∈ allSupercriticalDivisions k n,
      (supercriticalMediumDegreeGraphFinset
        k hk gamma hgamma alpha m n tau hn D).card
  else 0

/-- Exact iterated sum over divisions and their displayed combined-defect
patterns. -/
noncomputable def supercriticalFixedDefectTotal
    (k : ℕ) (hk : 3 ≤ k) (gamma : ℝ)
    (hgamma : gamma ∈ Set.Ico (gammaK k) 1)
    (alpha : ℝ) (m n : ℕ) (tau : ℝ) : ℕ := by
  classical
  exact if hn : k - 1 ≤ n then
    ∑ D ∈ allSupercriticalDivisions k n,
      ∑ T ∈ supercriticalCombinedDefectPatternFinset
          k hk gamma hgamma m n tau hn D,
        (supercriticalFixedDefectGraphFinset
          k hk gamma hgamma alpha m n tau hn D T).card
  else 0

/-- Exact cardinality of the graphon-far family. -/
noncomputable def supercriticalFarTotal
    (k : ℕ) (hk : 3 ≤ k) (gamma : ℝ)
    (hgamma : gamma ∈ Set.Ico (gammaK k) 1)
    (m n : ℕ) (tau : ℝ) : ℕ :=
  (supercriticalFarGraphFinset k hk gamma hgamma m n tau).card

/-! ## The exact four-way exceptional family -/

/-- The union used by the master deterministic decomposition. -/
noncomputable def supercriticalAggregatedExceptionalGraphFinset
    (k : ℕ) (hk : 3 ≤ k) (gamma : ℝ)
    (hgamma : gamma ∈ Set.Ico (gammaK k) 1)
    (alpha : ℝ) (m n : ℕ) (tau : ℝ) :
    Finset (SimpleGraph (Fin n)) :=
  supercriticalFarGraphFinset k hk gamma hgamma m n tau ∪
    supercriticalCleanNonemptySparseGraphFinset
      k hk gamma hgamma m n tau ∪
    supercriticalMediumTotalGraphFinset
      k hk gamma hgamma alpha m n tau ∪
    supercriticalFixedDefectTotalGraphFinset
      k hk gamma hgamma alpha m n tau

/-- Every exceptional exact-edge graph is far, clean with a nonempty sparse
set, medium-degree, or in its own fixed combined-defect fiber.  This theorem
is purely finite: the only size hypothesis is the one required to define the
canonical `k - 1`-part division. -/
theorem supercriticalNonCoMultipartiteGraphFinset_subset_union
    (k : ℕ) (hk : 3 ≤ k) (gamma : ℝ)
    (hgamma : gamma ∈ Set.Ico (gammaK k) 1)
    (alpha : ℝ) (m n : ℕ) (tau : ℝ) (hn : k - 1 ≤ n) :
    supercriticalNonCoMultipartiteGraphFinset k n m ⊆
      supercriticalAggregatedExceptionalGraphFinset
        k hk gamma hgamma alpha m n tau := by
  classical
  intro G hG
  have hbad := mem_supercriticalNonCoMultipartiteGraphFinset.mp hG
  by_cases hfar : G ∈ supercriticalFarGraphFinset
      k hk gamma hgamma m n tau
  · simp [supercriticalAggregatedExceptionalGraphFinset, hfar]
  have hclose : G ∈ supercriticalCloseGraphFinset
      k hk gamma hgamma m n tau := by
    rw [supercriticalCloseGraphFinset_eq_sdiff_far]
    rw [Finset.mem_sdiff]
    exact ⟨by simpa using hbad.1, hfar⟩
  let D := canonicalSupercriticalDivision G (by simpa using hn)
  have hdivision : G ∈ supercriticalDivisionGraphFinset
      k hk gamma hgamma m n tau hn D := by
    rw [mem_supercriticalDivisionGraphFinset]
    exact ⟨hclose, rfl⟩
  by_cases hzero : (finiteGraphEdges
      (canonicalSupercriticalDefectGraph G (by simpa using hn))).card = 0
  · have hclean : G ∈ supercriticalCleanDivisionGraphFinset
        k hk gamma hgamma m n tau hn D := by
      rw [mem_supercriticalCleanDivisionGraphFinset]
      exact ⟨hclose, rfl, hzero⟩
    by_cases hsparse : D.sparse.Nonempty
    · have hcleanUnion :
          G ∈ supercriticalCleanNonemptySparseGraphFinset
            k hk gamma hgamma m n tau := by
        rw [supercriticalCleanNonemptySparseGraphFinset, dif_pos hn,
          Finset.mem_biUnion]
        exact ⟨D, mem_allSupercriticalDivisions D, by simp [hsparse, hclean]⟩
      simp [supercriticalAggregatedExceptionalGraphFinset, hcleanUnion]
    · have hfull : D.IsFull := by
        exact Finset.not_nonempty_iff_eq_empty.mp hsparse
      let profile := crossEdgeProfile G D
      have hprofile : G ∈ supercriticalCleanDivisionProfileGraphFinset
          k hk gamma hgamma m n tau hn D profile := by
        rw [mem_supercriticalCleanDivisionProfileGraphFinset]
        exact ⟨hclean, rfl⟩
      have hclique : ∀ i : Fin (k - 1),
          G.IsClique (D.parts i : Set (Fin n)) := by
        intro i x hx y hy hxy
        exact mainParts_clique_of_mem_cleanProfile
          hprofile i hx hy hxy
      exact False.elim (hbad.2
        (D.isCoMultipartite_of_isFull_of_isClique G hfull hclique))
  · have hdefectNonempty : (finiteGraphEdges
        (canonicalSupercriticalDefectGraph G (by simpa using hn))).Nonempty :=
      Finset.card_ne_zero.mp hzero
    have hdefect : G ∈ supercriticalDivisionDefectGraphFinset
        k hk gamma hgamma m n tau hn D := by
      rw [mem_supercriticalDivisionDefectGraphFinset]
      exact ⟨hclose, rfl, hdefectNonempty⟩
    by_cases hmedium : ∃ v i, HasMediumDegreeInPart
        (canonicalCombinedDefectGraph G (by simpa using hn)) alpha D v i
    · have hmediumUnion : G ∈ supercriticalMediumTotalGraphFinset
          k hk gamma hgamma alpha m n tau := by
        rw [supercriticalMediumTotalGraphFinset, dif_pos hn,
          Finset.mem_biUnion]
        refine ⟨D, mem_allSupercriticalDivisions D, ?_⟩
        rw [mem_supercriticalMediumDegreeGraphFinset]
        exact ⟨hdefect, hmedium⟩
      simp [supercriticalAggregatedExceptionalGraphFinset, hmediumUnion]
    · let T := canonicalCombinedDefectGraph G (by simpa using hn)
      have hT : T ∈ supercriticalCombinedDefectPatternFinset
          k hk gamma hgamma m n tau hn D := by
        rw [mem_supercriticalCombinedDefectPatternFinset]
        exact ⟨G, hdefect, rfl⟩
      have hfixed : G ∈ supercriticalFixedDefectGraphFinset
          k hk gamma hgamma alpha m n tau hn D T := by
        rw [mem_supercriticalFixedDefectGraphFinset]
        exact ⟨hdefect, rfl, hmedium⟩
      have hfixedUnion : G ∈ supercriticalFixedDefectTotalGraphFinset
          k hk gamma hgamma alpha m n tau := by
        rw [supercriticalFixedDefectTotalGraphFinset, dif_pos hn,
          Finset.mem_biUnion]
        refine ⟨D, mem_allSupercriticalDivisions D, ?_⟩
        rw [Finset.mem_biUnion]
        exact ⟨T, hT, hfixed⟩
      simp [supercriticalAggregatedExceptionalGraphFinset, hfixedUnion]

/-! ## Cardinal bounds for the exact unions -/

theorem card_supercriticalCleanNonemptySparseGraphFinset_le_total
    (k : ℕ) (hk : 3 ≤ k) (gamma : ℝ)
    (hgamma : gamma ∈ Set.Ico (gammaK k) 1)
    (m n : ℕ) (tau : ℝ) :
    (supercriticalCleanNonemptySparseGraphFinset
      k hk gamma hgamma m n tau).card ≤
        supercriticalCleanTotal k hk gamma hgamma m n tau := by
  classical
  by_cases hn : k - 1 ≤ n
  · rw [supercriticalCleanNonemptySparseGraphFinset,
      supercriticalCleanTotal, dif_pos hn, dif_pos hn]
    have h := (Finset.card_biUnion_le :
      ((allSupercriticalDivisions k n).biUnion fun D ↦
        if D.sparse.Nonempty then
          supercriticalCleanDivisionGraphFinset
            k hk gamma hgamma m n tau hn D
        else ∅).card ≤
        ∑ D ∈ allSupercriticalDivisions k n,
          (if D.sparse.Nonempty then
            supercriticalCleanDivisionGraphFinset
              k hk gamma hgamma m n tau hn D
          else ∅).card)
    refine h.trans_eq ?_
    apply Finset.sum_congr rfl
    intro D _hD
    by_cases hsparse : D.sparse.Nonempty <;> simp [hsparse]
  · simp [supercriticalCleanNonemptySparseGraphFinset,
      supercriticalCleanTotal, hn]

theorem card_supercriticalMediumTotalGraphFinset_le_total
    (k : ℕ) (hk : 3 ≤ k) (gamma : ℝ)
    (hgamma : gamma ∈ Set.Ico (gammaK k) 1)
    (alpha : ℝ) (m n : ℕ) (tau : ℝ) :
    (supercriticalMediumTotalGraphFinset
      k hk gamma hgamma alpha m n tau).card ≤
        supercriticalMediumTotal k hk gamma hgamma alpha m n tau := by
  classical
  by_cases hn : k - 1 ≤ n
  · rw [supercriticalMediumTotalGraphFinset,
      supercriticalMediumTotal, dif_pos hn, dif_pos hn]
    exact Finset.card_biUnion_le
  · simp [supercriticalMediumTotalGraphFinset,
      supercriticalMediumTotal, hn]

theorem card_supercriticalFixedDefectTotalGraphFinset_le_total
    (k : ℕ) (hk : 3 ≤ k) (gamma : ℝ)
    (hgamma : gamma ∈ Set.Ico (gammaK k) 1)
    (alpha : ℝ) (m n : ℕ) (tau : ℝ) :
    (supercriticalFixedDefectTotalGraphFinset
      k hk gamma hgamma alpha m n tau).card ≤
        supercriticalFixedDefectTotal k hk gamma hgamma alpha m n tau := by
  classical
  by_cases hn : k - 1 ≤ n
  · rw [supercriticalFixedDefectTotalGraphFinset,
      supercriticalFixedDefectTotal, dif_pos hn, dif_pos hn]
    refine Finset.card_biUnion_le.trans ?_
    exact Finset.sum_le_sum fun D _hD ↦ Finset.card_biUnion_le
  · simp [supercriticalFixedDefectTotalGraphFinset,
      supercriticalFixedDefectTotal, hn]

/-- Cardinal union bound associated with the master decomposition. -/
theorem card_supercriticalNonCoMultipartiteGraphFinset_le_totals
    (k : ℕ) (hk : 3 ≤ k) (gamma : ℝ)
    (hgamma : gamma ∈ Set.Ico (gammaK k) 1)
    (alpha : ℝ) (m n : ℕ) (tau : ℝ) (hn : k - 1 ≤ n) :
    (supercriticalNonCoMultipartiteGraphFinset k n m).card ≤
      supercriticalFarTotal k hk gamma hgamma m n tau +
      supercriticalCleanTotal k hk gamma hgamma m n tau +
      supercriticalMediumTotal k hk gamma hgamma alpha m n tau +
      supercriticalFixedDefectTotal k hk gamma hgamma alpha m n tau := by
  classical
  have hsubset := supercriticalNonCoMultipartiteGraphFinset_subset_union
    k hk gamma hgamma alpha m n tau hn
  have hclean := card_supercriticalCleanNonemptySparseGraphFinset_le_total
    k hk gamma hgamma m n tau
  have hmedium := card_supercriticalMediumTotalGraphFinset_le_total
    k hk gamma hgamma alpha m n tau
  have hfixed := card_supercriticalFixedDefectTotalGraphFinset_le_total
    k hk gamma hgamma alpha m n tau
  have hfarClean := Finset.card_union_le
    (supercriticalFarGraphFinset k hk gamma hgamma m n tau)
    (supercriticalCleanNonemptySparseGraphFinset
      k hk gamma hgamma m n tau)
  have hwithMedium := Finset.card_union_le
    (supercriticalFarGraphFinset k hk gamma hgamma m n tau ∪
      supercriticalCleanNonemptySparseGraphFinset
        k hk gamma hgamma m n tau)
    (supercriticalMediumTotalGraphFinset
      k hk gamma hgamma alpha m n tau)
  have hwithFixed := Finset.card_union_le
    (supercriticalFarGraphFinset k hk gamma hgamma m n tau ∪
      supercriticalCleanNonemptySparseGraphFinset
        k hk gamma hgamma m n tau ∪
      supercriticalMediumTotalGraphFinset
        k hk gamma hgamma alpha m n tau)
    (supercriticalFixedDefectTotalGraphFinset
      k hk gamma hgamma alpha m n tau)
  have haggregate :
      (supercriticalAggregatedExceptionalGraphFinset
        k hk gamma hgamma alpha m n tau).card ≤
        (supercriticalFarGraphFinset k hk gamma hgamma m n tau).card +
        (supercriticalCleanNonemptySparseGraphFinset
          k hk gamma hgamma m n tau).card +
        (supercriticalMediumTotalGraphFinset
          k hk gamma hgamma alpha m n tau).card +
        (supercriticalFixedDefectTotalGraphFinset
          k hk gamma hgamma alpha m n tau).card := by
    unfold supercriticalAggregatedExceptionalGraphFinset
    omega
  exact (Finset.card_le_card hsubset).trans
    (haggregate.trans (by
      dsimp [supercriticalFarTotal]
      omega))

/-! ## Eventual composition -/

/-- Convergence of the exact edge density gives every fixed positive
two-sided error tolerance in the form used by the finite cover estimates. -/
theorem eventually_edgeDensity_error_lt
    {m : ℕ → ℕ} {gamma tolerance : ℝ}
    (hm : HasAsymptoticEdgeDensity m gamma) (htolerance : 0 < tolerance) :
    ∀ᶠ n : ℕ in Filter.atTop,
      |(m n : ℝ) / (completeEdgeCount n : ℝ) - gamma| < tolerance := by
  have hlower : gamma - tolerance < gamma := by linarith
  have hupper : gamma < gamma + tolerance := by linarith
  filter_upwards [(tendsto_order.1 hm).1 _ hlower,
      (tendsto_order.1 hm).2 _ hupper] with n hnLower hnUpper
  rw [abs_lt]
  constructor <;> linarith

/-- Multiplicity two can be absorbed by losing half of any positive linear
exponential rate. -/
theorem eventually_two_mul_exp_neg_linear_le
    {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n : ℕ in Filter.atTop,
      2 * Real.exp (-(c * (n : ℝ))) ≤
        Real.exp (-((c / 2) * (n : ℝ))) := by
  filter_upwards
      [DenseGraph.eventually_natCast_mul_le_exp_mul 2 (half_pos hc),
       eventually_ge_atTop (1 : ℕ)]
      with n hexp hn
  have htwo : (2 : ℝ) ≤ Real.exp ((c / 2) * (n : ℝ)) := by
    calc
      (2 : ℝ) ≤ 2 * (n : ℝ) := by
        exact le_mul_of_one_le_right (by norm_num) (by exact_mod_cast hn)
      _ ≤ Real.exp ((c / 2) * (n : ℝ)) := by simpa using hexp
  calc
    2 * Real.exp (-(c * (n : ℝ))) ≤
        Real.exp ((c / 2) * (n : ℝ)) *
          Real.exp (-(c * (n : ℝ))) := by
      exact mul_le_mul_of_nonneg_right htwo (Real.exp_nonneg _)
    _ = Real.exp (-((c / 2) * (n : ℝ))) := by
      rw [← Real.exp_add]
      congr 1
      ring

/-- Any fixed natural multiplicity can be absorbed by losing half of a
positive linear exponential rate. -/
theorem eventually_natCast_mul_exp_neg_linear_le
    (r : ℕ) {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n : ℕ in Filter.atTop,
      (r : ℝ) * Real.exp (-(c * (n : ℝ))) ≤
        Real.exp (-((c / 2) * (n : ℝ))) := by
  filter_upwards
      [DenseGraph.eventually_natCast_mul_le_exp_mul r (half_pos hc),
       eventually_ge_atTop (1 : ℕ)]
      with n hexp hn
  have hr : (r : ℝ) ≤ Real.exp ((c / 2) * (n : ℝ)) := by
    calc
      (r : ℝ) ≤ (r : ℝ) * (n : ℝ) := by
        exact le_mul_of_one_le_right (by positivity) (by exact_mod_cast hn)
      _ ≤ Real.exp ((c / 2) * (n : ℝ)) := by simpa using hexp
  calc
    (r : ℝ) * Real.exp (-(c * (n : ℝ))) ≤
        Real.exp ((c / 2) * (n : ℝ)) *
          Real.exp (-(c * (n : ℝ))) := by
      exact mul_le_mul_of_nonneg_right hr (Real.exp_nonneg _)
    _ = Real.exp (-((c / 2) * (n : ℝ))) := by
      rw [← Real.exp_add]
      congr 1
      ring

/-- The analogous absorption lemma at quadratic scale. -/
theorem eventually_two_mul_exp_neg_quadratic_le
    {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n : ℕ in Filter.atTop,
      2 * Real.exp (-(c * (n : ℝ) ^ 2)) ≤
        Real.exp (-((c / 2) * (n : ℝ) ^ 2)) := by
  filter_upwards
      [DenseGraph.eventually_natCast_mul_le_exp_mul 2 (half_pos hc),
       eventually_ge_atTop (1 : ℕ)]
      with n hexp hn
  have hnReal : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have htwoLinear : (2 : ℝ) ≤
      Real.exp ((c / 2) * (n : ℝ)) := by
    calc
      (2 : ℝ) ≤ 2 * (n : ℝ) := by
        exact le_mul_of_one_le_right (by norm_num) hnReal
      _ ≤ Real.exp ((c / 2) * (n : ℝ)) := by simpa using hexp
  have hlinearQuadratic :
      (c / 2) * (n : ℝ) ≤ (c / 2) * (n : ℝ) ^ 2 := by
    have hn0 : (0 : ℝ) ≤ n := by positivity
    have hnn : (n : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
    exact mul_le_mul_of_nonneg_left hnn (half_pos hc).le
  have htwo : (2 : ℝ) ≤
      Real.exp ((c / 2) * (n : ℝ) ^ 2) :=
    htwoLinear.trans (Real.exp_le_exp.mpr hlinearQuadratic)
  calc
    2 * Real.exp (-(c * (n : ℝ) ^ 2)) ≤
        Real.exp ((c / 2) * (n : ℝ) ^ 2) *
          Real.exp (-(c * (n : ℝ) ^ 2)) := by
      exact mul_le_mul_of_nonneg_right htwo (Real.exp_nonneg _)
    _ = Real.exp (-((c / 2) * (n : ℝ) ^ 2)) := by
      rw [← Real.exp_add]
      congr 1
      ring

/-- Direct four-term composition of the deterministic union bound with the
clean, fixed-defect, medium, and far estimates.  Every rate and every local
estimate is fixed before the edge-count sequence is introduced. -/
theorem eventually_supercriticalGlobalExceptional_four_term_of_total_bounds
    (k : ℕ) (hk : 3 ≤ k) (gamma : ℝ)
    (hgamma : gamma ∈ Set.Ioo (gammaK k) 1)
    (P : SupercriticalAggregationParameters k gamma)
    (cClean cFixed cMedium cFar : ℝ)
    (hclean : ∀ m : ℕ → ℕ, HasAsymptoticEdgeDensity m gamma →
      ∀ᶠ n in Filter.atTop,
        (supercriticalCleanTotal k hk gamma
          ⟨hgamma.1.le, hgamma.2⟩ (m n) n P.tau : ℝ) ≤
          (coMultipartiteGraphCountWithEdges (k - 1) n (m n) : ℝ) *
            Real.exp (-cClean * (n : ℝ)))
    (hfixed : ∀ m : ℕ → ℕ, HasAsymptoticEdgeDensity m gamma →
      ∀ᶠ n in Filter.atTop,
        (supercriticalFixedDefectTotal k hk gamma
          ⟨hgamma.1.le, hgamma.2⟩ P.alpha (m n) n P.tau : ℝ) ≤
          (coMultipartiteGraphCountWithEdges (k - 1) n (m n) : ℝ) *
            Real.exp (-cFixed * (n : ℝ)))
    (hmedium : ∀ m : ℕ → ℕ, HasAsymptoticEdgeDensity m gamma →
      ∀ᶠ n in Filter.atTop,
        (supercriticalMediumTotal k hk gamma
          ⟨hgamma.1.le, hgamma.2⟩ P.alpha (m n) n P.tau : ℝ) ≤
          (coMultipartiteGraphCountWithEdges (k - 1) n (m n) : ℝ) *
            Real.exp (-cMedium * (n : ℝ) ^ 2))
    (hfar : ∀ m : ℕ → ℕ, HasAsymptoticEdgeDensity m gamma →
      ∀ᶠ n in Filter.atTop,
        (supercriticalFarTotal k hk gamma
          ⟨hgamma.1.le, hgamma.2⟩ (m n) n P.tau : ℝ) ≤
          (inducedStarFreeGraphCountWithEdges k n (m n) : ℝ) *
            Real.exp (-cFar * (n : ℝ) ^ 2)) :
    ∀ m : ℕ → ℕ, HasAsymptoticEdgeDensity m gamma →
      ∀ᶠ n in Filter.atTop,
        ((supercriticalNonCoMultipartiteGraphFinset
          k n (m n)).card : ℝ) ≤
          (coMultipartiteGraphCountWithEdges (k - 1) n (m n) : ℝ) *
            (Real.exp (-cClean * (n : ℝ)) +
              Real.exp (-cFixed * (n : ℝ)) +
              Real.exp (-cMedium * (n : ℝ) ^ 2)) +
          (inducedStarFreeGraphCountWithEdges k n (m n) : ℝ) *
            Real.exp (-cFar * (n : ℝ) ^ 2) := by
  intro m hm
  filter_upwards [eventually_ge_atTop (k - 1), hclean m hm,
      hfixed m hm, hmedium m hm, hfar m hm]
      with n hn hnClean hnFixed hnMedium hnFar
  have hfiniteNat := card_supercriticalNonCoMultipartiteGraphFinset_le_totals
    k hk gamma ⟨hgamma.1.le, hgamma.2⟩ P.alpha (m n) n P.tau hn
  have hfinite :
      ((supercriticalNonCoMultipartiteGraphFinset k n (m n)).card : ℝ) ≤
        (supercriticalFarTotal k hk gamma
          ⟨hgamma.1.le, hgamma.2⟩ (m n) n P.tau : ℝ) +
        (supercriticalCleanTotal k hk gamma
          ⟨hgamma.1.le, hgamma.2⟩ (m n) n P.tau : ℝ) +
        (supercriticalMediumTotal k hk gamma
          ⟨hgamma.1.le, hgamma.2⟩ P.alpha (m n) n P.tau : ℝ) +
        (supercriticalFixedDefectTotal k hk gamma
          ⟨hgamma.1.le, hgamma.2⟩ P.alpha (m n) n P.tau : ℝ) := by
    exact_mod_cast hfiniteNat
  calc
    ((supercriticalNonCoMultipartiteGraphFinset k n (m n)).card : ℝ) ≤
        (supercriticalFarTotal k hk gamma
          ⟨hgamma.1.le, hgamma.2⟩ (m n) n P.tau : ℝ) +
        (supercriticalCleanTotal k hk gamma
          ⟨hgamma.1.le, hgamma.2⟩ (m n) n P.tau : ℝ) +
        (supercriticalMediumTotal k hk gamma
          ⟨hgamma.1.le, hgamma.2⟩ P.alpha (m n) n P.tau : ℝ) +
        (supercriticalFixedDefectTotal k hk gamma
          ⟨hgamma.1.le, hgamma.2⟩ P.alpha (m n) n P.tau : ℝ) :=
      hfinite
    _ ≤ (coMultipartiteGraphCountWithEdges (k - 1) n (m n) : ℝ) *
            (Real.exp (-cClean * (n : ℝ)) +
              Real.exp (-cFixed * (n : ℝ)) +
              Real.exp (-cMedium * (n : ℝ) ^ 2)) +
          (inducedStarFreeGraphCountWithEdges k n (m n) : ℝ) *
            Real.exp (-cFar * (n : ℝ) ^ 2) := by
      linarith

end InducedStars
