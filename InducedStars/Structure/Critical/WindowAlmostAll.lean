import InducedStars.Structure.Critical.WindowConcentration
import InducedStars.Structure.Critical.WindowAboveThreshold
import InducedStars.Structure.Critical.WindowEventInclusions
import InducedStars.Structure.Critical.WindowCutoff

/-!
# The natural-log critical-window theorem

This auxiliary theorem uses natural logarithms.  `WindowBase2` provides the
paper-facing interface by an exact parameter and event conversion.
The edge count is the exact floor at every fixed signed window parameter.
Below and at the transition, one literal disjoint-union witness carries
both the structural conclusion and the sharp exceptional-set size.  Above
the transition, the co-partite family has limiting probability one.
-/

noncomputable section

open Filter Set Topology

namespace InducedStars

theorem criticalWindowBadStructureProbability_tendsto_zero
    {k : ℕ} (hk : 3 ≤ k) {a epsilon : ℝ}
    (ha : a ≤ criticalWindowThreshold k) (hepsilon : 0 < epsilon) :
    Tendsto (fun n ↦ ((criticalWindowBadStructureFinset k n a epsilon).card : ℝ) /
      ((criticalWindowInducedStarFreeGraphFinset k n a).card : ℝ)) atTop (𝓝 0) := by
  obtain ⟨L, hL, hcoarse⟩ := exists_criticalWindowSmallAssemblyFailureRatio_tendsto_zero k hk a
  have htail := criticalWindowOffPeakAssemblyMass_div_total_tendsto_zero hk ha
    (by linarith : 0 ≤ L + 1) hepsilon
  have hsum := hcoarse.add htail
  simp only [add_zero] at hsum
  apply squeeze_zero' (Eventually.of_forall fun _ ↦ by positivity) ?_ hsum
  filter_upwards [eventually_criticalWindowCutoff_div_log_le hL.le,
    criticalWindowLog_nat_tendsto_atTop.eventually (eventually_gt_atTop (0 : ℝ))] with n hq hl
  have h := card_criticalWindowBadStructure_le (k := k) (a := a) (epsilon := epsilon) hl hq
  change ((criticalWindowBadStructureFinset k n a epsilon).card : ℝ) / _ ≤
    ((criticalNoSmallAssemblyGraphFinset k n (criticalWindowEdgeCount k a n)
      (criticalLogarithmicSparseCutoff L n)).card : ℝ) / _ +
        criticalWindowOffPeakAssemblyMass k a (L + 1) epsilon n / _
  change _ ≤ _ / ((criticalWindowInducedStarFreeGraphFinset k n a).card : ℝ) +
    _ / ((criticalWindowInducedStarFreeGraphFinset k n a).card : ℝ)
  rw [← add_div]
  exact div_le_div_of_nonneg_right h (Nat.cast_nonneg _)

/-- Sharp logarithmic exceptional-set size below and at the transition. -/
theorem inducedStarCriticalWindowAlmostAll_structured
    (k : ℕ) (hk : 3 ≤ k) (a : ℝ) (ha : a ≤ criticalWindowThreshold k)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    Tendsto (criticalWindowStructuredProbability k a epsilon) atTop (𝓝 1) := by
  classical
  have hbad := criticalWindowBadStructureProbability_tendsto_zero hk ha hepsilon
  have h := (tendsto_const_nhds (x := (1 : ℝ))).sub hbad
  simp only [sub_zero] at h
  apply h.congr'
  filter_upwards [eventually_criticalWindowFullCount_pos k hk a] with n hn
  have hcard :
      (((criticalWindowInducedStarFreeGraphFinset k n a).filter (HasCriticalWindowStructure k a epsilon)).card : ℝ) +
        ((criticalWindowBadStructureFinset k n a epsilon).card : ℝ) =
          ((criticalWindowInducedStarFreeGraphFinset k n a).card : ℝ) := by
    exact_mod_cast (Finset.card_filter_add_card_filter_not
      (s := criticalWindowInducedStarFreeGraphFinset k n a) (HasCriticalWindowStructure k a epsilon))
  have htotal : ((criticalWindowInducedStarFreeGraphFinset k n a).card : ℝ) ≠ 0 := by
    exact_mod_cast hn.ne'
  unfold criticalWindowStructuredProbability uniformSubfamilyProbability
  apply (sub_eq_iff_eq_add).mpr
  rw [← add_div, hcard, div_self htotal]

/-- Above the logarithmic-window transition, every positive remainder size
is negligible, including bounded sizes. -/
theorem inducedStarCriticalWindowAlmostAll_coMultipartite
    (k : ℕ) (hk : 3 ≤ k) (a : ℝ) (ha : criticalWindowThreshold k < a) :
    Tendsto (fun n ↦ supercriticalCoMultipartiteProbability k n (criticalWindowEdgeCount k a n))
      atTop (𝓝 1) := by
  obtain ⟨L, hL, hcoarse⟩ := exists_criticalWindowSmallAssemblyFailureRatio_tendsto_zero k hk a
  have htail := criticalWindowAbove_positive_assembly_probability_tendsto_zero hk a ha
    (L + 1) (by linarith)
  have hsum := hcoarse.add htail
  simp only [add_zero] at hsum
  have hbad : Tendsto
      (fun n ↦ supercriticalNonCoMultipartiteProbability k n (criticalWindowEdgeCount k a n))
      atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall fun _ ↦ by
      unfold supercriticalNonCoMultipartiteProbability uniformSubfamilyProbability
      positivity) ?_ hsum
    filter_upwards [eventually_criticalWindowCutoff_div_log_le hL.le,
      criticalWindowLog_nat_tendsto_atTop.eventually (eventually_gt_atTop (0 : ℝ))] with n hq hl
    have h := card_criticalWindowNonCoMultipartite_le (k := k) (a := a) hl hq
    unfold supercriticalNonCoMultipartiteProbability uniformSubfamilyProbability
    change ((supercriticalNonCoMultipartiteGraphFinset k n (criticalWindowEdgeCount k a n)).card : ℝ) / _ ≤
      ((criticalNoSmallAssemblyGraphFinset k n (criticalWindowEdgeCount k a n)
        (criticalLogarithmicSparseCutoff L n)).card : ℝ) / _ +
          ((criticalWindowPositiveAssemblyFinset k n a (L + 1)).card : ℝ) / _
    rw [← add_div]
    exact div_le_div_of_nonneg_right h (Nat.cast_nonneg _)
  have h := (tendsto_const_nhds (x := (1 : ℝ))).sub hbad
  simp only [sub_zero] at h
  apply h.congr'
  filter_upwards [eventually_criticalWindowFullCount_pos k hk a] with n hn
  have hne : (inducedStarFreeGraphFinsetWithEdges k n (criticalWindowEdgeCount k a n)).Nonempty :=
    Finset.card_pos.mp hn
  have hh := supercriticalCoMultipartiteProbability_add_nonCoMultipartiteProbability
    (k := k) (n := n) (m := criticalWindowEdgeCount k a n) (by omega) hne
  linarith

/-- The full natural-log critical-window theorem, retained as the proved
analytic interface.  `inducedStarCriticalWindowBase2AlmostAll` expresses the
paper's base-two convention. -/
theorem inducedStarCriticalWindowAlmostAll (k : ℕ) (hk : 3 ≤ k) :
    ∀ a : ℝ,
      (a ≤ criticalWindowThreshold k → ∀ epsilon : ℝ, 0 < epsilon →
        Tendsto (criticalWindowStructuredProbability k a epsilon) atTop (𝓝 1)) ∧
      (criticalWindowThreshold k < a →
        Tendsto (fun n ↦ supercriticalCoMultipartiteProbability k n (criticalWindowEdgeCount k a n))
          atTop (𝓝 1)) := by
  intro a
  exact ⟨fun ha epsilon hepsilon ↦ inducedStarCriticalWindowAlmostAll_structured k hk a ha epsilon hepsilon,
    fun ha ↦ inducedStarCriticalWindowAlmostAll_coMultipartite k hk a ha⟩

end InducedStars
