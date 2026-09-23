import InducedStars.Structure.Gnp.CriticalBallComparison
import InducedStars.Structure.Gnp.CriticalOptimizerCover
import InducedStars.Structure.Gnp.RoughConsequences
import DenseGraph.Combinatorics.LogarithmicGain

/-!
# Critical conditioned graphs have vanishing quadratic edge mass

Paper: the critical branch of Theorem `thm:gnp-typ-struc` in `paper/gnp.tex`.
The finite optimizer cover is chosen after the common comparison radius and
before combining the finitely many order thresholds. All estimates concern
the actual weighted induced-free conditional law, with its positive finite
denominator. The retained-key count enters through the proved weighted comparison.
-/

noncomputable section
open Filter Finset Set Topology
open scoped Classical BigOperators
namespace InducedStars

private theorem criticalTypical_probability_union_le {n : ℕ} {p : ℝ}
    (hp : p ∈ Icc (0 : ℝ) 1) (Q R : Finset (SimpleGraph (Fin n))) :
    gnpGraphEventProbability p (Q ∪ R) ≤
      gnpGraphEventProbability p Q + gnpGraphEventProbability p R := by
  have heq := Finset.sum_union_inter (s₁ := Q) (s₂ := R) (f := gnpGraphWeight p)
  have hnonneg := gnpGraphEventProbability_nonneg hp (Q ∩ R)
  unfold gnpGraphEventProbability at *
  linarith

private theorem criticalTypical_probability_biUnion_le {ι : Type*} {n : ℕ} {p : ℝ}
    (hp : p ∈ Icc (0 : ℝ) 1) (F : Finset ι)
    (Q : ι → Finset (SimpleGraph (Fin n))) :
    gnpGraphEventProbability p (F.biUnion Q) ≤
      ∑ i ∈ F, gnpGraphEventProbability p (Q i) := by
  induction F using Finset.induction_on with
  | empty => simp [gnpGraphEventProbability]
  | @insert i F hi ih =>
    rw [Finset.biUnion_insert, Finset.sum_insert hi]
    exact (criticalTypical_probability_union_le hp _ _).trans (add_le_add le_rfl ih)

/-- A finite family of separated optimizer balls, together with the optimizer
far event, covers every nonsparse induced-free graph. This is a deterministic
finite statement; no conditional probability is used in the containment. -/
theorem gnpCriticalNonSparse_subset_far_union_balls
    {k n : ℕ} (hk : 3 ≤ k) (hn : 0 < n) {ξ tau : ℝ} (hξ : 0 < ξ)
    (F : Finset (AdmissibleBlockSequence k))
    (hcover : ∀ X : Graphon, ξ ≤ cutDist X zeroGraphon →
      cutDistToSet X (gnpGraphonOptimizers k (pK k)) < tau / 4 →
      ∃ L ∈ F, cutDist X (WLambda hk L) < tau) :
    inducedFreeGraphFinset (inducedStar k) n ∩
        (Finset.univ \ gnpSparseGraphFinset n ξ) ⊆
      gnpOptimizerFarInducedStarFinset k (pK k) (tau / 4) n ∪
        F.biUnion (fun L ↦ gnpInducedStarCutBallFinset k (WLambda hk L) tau n) := by
  intro G hG
  obtain ⟨hfree, hbad⟩ := Finset.mem_inter.mp hG
  have hlarge : ξ * (n : ℝ)^2 < (finiteGraphEdges G).card := by
    simpa [gnpSparseGraphFinset] using (Finset.mem_sdiff.mp hbad).2
  have hzero : ξ ≤ cutDist (graphGraphon G) zeroGraphon := by
    rw [DenseGraph.cutDist_zeroGraphon, graphonEdgeDensity_graphGraphon hn]
    have hnsq : (0 : ℝ) < (n : ℝ)^2 := by positivity
    apply (le_div_iff₀ hnsq).mpr
    have he : (0 : ℝ) ≤ (finiteGraphEdges G).card := Nat.cast_nonneg _
    linarith
  by_cases hfar : tau / 4 ≤ cutDistToSet (graphGraphon G)
      (gnpGraphonOptimizers k (pK k))
  · exact Finset.mem_union_left _ (mem_gnpOptimizerFarInducedStarFinset.mpr
      ⟨mem_inducedFreeGraphFinset.mp hfree, hfar⟩)
  · obtain ⟨L, hL, hcut⟩ := hcover (graphGraphon G) hzero (lt_of_not_ge hfar)
    exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
      ⟨L, hL, mem_gnpInducedStarCutBallFinset.mpr
        ⟨mem_inducedFreeGraphFinset.mp hfree, hcut⟩⟩)

/-- The critical conditioned nonsparse event has vanishing probability.
The argument includes all critical optimizers, including the full-length
complete-core endpoint. -/
theorem gnpConditionedNonSparseProbability_tendsto_zero_at_pK
    (k : ℕ) (hk : 3 ≤ k) (ξ : ℝ) (hξ : 0 < ξ) :
    Tendsto (fun n ↦ gnpConditionedInducedStarProbability k n (pK k)
      (Finset.univ \ gnpSparseGraphFinset n ξ)) atTop (𝓝 0) := by
  have hp := pK_mem_Ioo (show 2 ≤ k by omega)
  have hpClosed : pK k ∈ Icc (0 : ℝ) 1 := ⟨hp.1.le, hp.2.le⟩
  let omega := min ξ 1
  have homega : 0 < omega := lt_min hξ zero_lt_one
  obtain ⟨nu, tau, hnu, htau, htauSep, _htauOmega, hcompare⟩ :=
    criticalGnpComparison k hk (half_pos hξ) homega (min_le_right ξ 1)
  obtain ⟨F, hF, hcover⟩ := criticalGnpSeparatedOptimizerFiniteCover k hk hξ htau
    (show tau ≤ ξ by linarith)
  have hbounds : ∀ᶠ n : ℕ in atTop, ∀ L ∈ F,
      gnpInducedStarCutBallMass k n (pK k) (WLambda hk L) tau ≤
        Real.exp (-nu * n * Real.log n) *
          gnpInducedStarCutBallMass k n (pK k) zeroGraphon omega := by
    apply (Filter.eventually_all_finset F).mpr
    intro L hL
    exact hcompare L (hF L hL)
  have hbound : ∀ᶠ n : ℕ in atTop,
      gnpConditionedInducedStarProbability k n (pK k)
          (Finset.univ \ gnpSparseGraphFinset n ξ) ≤
        gnpConditionedOptimizerFarProbability k n (pK k) (tau / 4) +
          (F.card : ℝ) * Real.exp (-nu * n * Real.log n) := by
    filter_upwards [hbounds, eventually_ge_atTop 1] with n hbounds hn
    let Z := gnpInducedStarFreeProbability k n (pK k)
    let Far := gnpOptimizerFarInducedStarFinset k (pK k) (tau / 4) n
    let Bad := inducedFreeGraphFinset (inducedStar k) n ∩
      (Finset.univ \ gnpSparseGraphFinset n ξ)
    let e := Real.exp (-nu * n * Real.log n)
    have hZ : 0 < Z := gnpInducedStarFreeProbability_pos (by omega) hp
    have hcovern := gnpCriticalNonSparse_subset_far_union_balls (n := n)
      hk (by omega) hξ F hcover
    have hraw : gnpGraphEventProbability (pK k) Bad ≤
        gnpGraphEventProbability (pK k) Far + ((F.card : ℝ) * e) * Z := by
      calc
        _ ≤ gnpGraphEventProbability (pK k)
            (Far ∪ F.biUnion (fun L ↦
              gnpInducedStarCutBallFinset k (WLambda hk L) tau n)) :=
          gnpGraphEventProbability_mono hpClosed hcovern
        _ ≤ gnpGraphEventProbability (pK k) Far +
            gnpGraphEventProbability (pK k) (F.biUnion (fun L ↦
              gnpInducedStarCutBallFinset k (WLambda hk L) tau n)) :=
          criticalTypical_probability_union_le hpClosed _ _
        _ ≤ gnpGraphEventProbability (pK k) Far +
            ∑ L ∈ F, gnpInducedStarCutBallMass k n (pK k) (WLambda hk L) tau :=
          add_le_add le_rfl (criticalTypical_probability_biUnion_le hpClosed F
            (fun L ↦ gnpInducedStarCutBallFinset k (WLambda hk L) tau n))
        _ ≤ gnpGraphEventProbability (pK k) Far + ∑ _L ∈ F, e * Z := by
          apply add_le_add le_rfl
          apply Finset.sum_le_sum
          intro L hL
          exact (hbounds L hL).trans (mul_le_mul_of_nonneg_left
            (gnpInducedStarCutBallMass_le_probability k n hpClosed zeroGraphon omega)
            (Real.exp_pos _).le)
        _ = _ := by simp [mul_assoc]
    change gnpGraphEventProbability (pK k) Bad / Z ≤ _
    calc
      _ ≤ (gnpGraphEventProbability (pK k) Far + ((F.card : ℝ) * e) * Z) / Z :=
        div_le_div_of_nonneg_right hraw hZ.le
      _ = _ := by
        rw [add_div, mul_div_cancel_right₀ _ hZ.ne']
        rfl
  have hdecay : Tendsto (fun n : ℕ ↦ (F.card : ℝ) *
      Real.exp (-nu * n * Real.log n)) atTop (𝓝 0) := by
    have h := (DenseGraph.tendsto_polynomial_mul_exp_linear_sub_mul_log hnu 0 0).const_mul
      (F.card : ℝ)
    simpa only [pow_zero, zero_mul, zero_sub, one_mul, neg_mul, mul_zero] using h
  have hfar := gnpConditionedOptimizerFarProbability_tendsto_zero k hk (pK k) hp
    (tau / 4) (by positivity)
  apply squeeze_zero'
    (Eventually.of_forall fun n ↦
      gnpConditionedInducedStarProbability_nonneg k n hpClosed _)
    hbound
  simpa only [add_zero] using hfar.add hdecay

/-- Paper: Theorem `thm:gnp-typ-struc`, critical branch `p = p_k`.
Conditioned induced-star-free graphs have `o(n²)` unordered edges, expressed
using their exact finite weighted conditional probability. -/
theorem inducedStarGnpSparse_at_pK
    (k : ℕ) (hk : 3 ≤ k) (ξ : ℝ) (hξ : 0 < ξ) :
    Tendsto (fun n ↦ gnpConditionedInducedStarProbability k n (pK k)
      (gnpSparseGraphFinset n ξ)) atTop (𝓝 1) := by
  have hp := pK_mem_Ioo (show 2 ≤ k by omega)
  have hbad := gnpConditionedNonSparseProbability_tendsto_zero_at_pK k hk ξ hξ
  have hsum (n : ℕ) :
      gnpConditionedInducedStarProbability k n (pK k) (gnpSparseGraphFinset n ξ) +
        gnpConditionedInducedStarProbability k n (pK k)
          (Finset.univ \ gnpSparseGraphFinset n ξ) = 1 := by
    have heq : (Finset.univ \ gnpSparseGraphFinset n ξ) =
        Finset.univ.filter (fun G : SimpleGraph (Fin n) ↦
          ¬((finiteGraphEdges G).card : ℝ) ≤ ξ * (n : ℝ)^2) := by
      ext G
      simp [gnpSparseGraphFinset]
    rw [heq]
    exact gnpConditionedGraphProbability_filter_add_filter_not
      (gnpConditionedInducedStarProbability_denominator_pos (by omega) hp) _
  have hlim :=
    (show Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (𝓝 1) from tendsto_const_nhds).sub hbad
  simp only [sub_zero] at hlim
  apply hlim.congr
  intro n
  linarith [hsum n]

end InducedStars
