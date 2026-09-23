import InducedStars.Structure.Gnp.FixedDensityUniformity
import InducedStars.Structure.Gnp.RoughConsequences

/-!
# Co-multipartite structure in the strictly supercritical conditioned law

The local density window is chosen after the desired probability error.
The exact finite edge-count mixture transfers its uniform fixed-density
bound, while conditioned density concentration controls the complementary
levels. This does not assume uniform convergence on a previously fixed
density interval.
-/

noncomputable section

open Filter Set Topology
open scoped BigOperators

namespace InducedStars

attribute [local instance] Classical.propDecidable

noncomputable local instance transferEdgeSetFintype {n : ℕ}
    (G : SimpleGraph (Fin n)) : Fintype G.edgeSet :=
  graphFamiliesEdgeSetFintype G

/-- The co-`(k-1)`-partite event without conditioning on an edge count. -/
noncomputable def gnpCoMultipartiteGraphFinset (k n : ℕ) :
    Finset (SimpleGraph (Fin n)) :=
  Finset.univ.filter fun G ↦ DenseGraph.IsCoMultipartite G (k - 1)

/-- The complementary structural event, again with no fixed edge count. -/
noncomputable def gnpNonCoMultipartiteGraphFinset (k n : ℕ) :
    Finset (SimpleGraph (Fin n)) :=
  Finset.univ.filter fun G ↦ ¬DenseGraph.IsCoMultipartite G (k - 1)

private theorem nonCoMultipartite_exactSlice (k n m : ℕ) :
    inducedStarFreeGraphFinsetWithEdges k n m ∩ gnpNonCoMultipartiteGraphFinset k n =
      supercriticalNonCoMultipartiteGraphFinset k n m := by
  ext G
  simp [gnpNonCoMultipartiteGraphFinset]

/-- Above `pK k`, the actual induced-star-conditioned binomial graph is
asymptotically co-`(k-1)`-partite.  This is the vanishing exceptional form. -/
theorem gnpConditionedNonCoMultipartiteProbability_tendsto_zero
    (k : ℕ) (hk : 3 ≤ k) (p : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1)
    (hsuper : pK k < p) :
    Tendsto (fun n ↦ gnpConditionedInducedStarProbability k n p
      (gnpNonCoMultipartiteGraphFinset k n)) atTop (𝓝 0) := by
  refine tendsto_order.mpr ⟨?_, ?_⟩
  · intro a ha
    exact Eventually.of_forall fun n ↦ ha.trans_le
      (gnpConditionedInducedStarProbability_nonneg k n ⟨hp.1.le, hp.2.le⟩ _)
  · intro ε hε
    obtain ⟨δ, hδ, n₀, hn₀⟩ :=
      exists_supercriticalNonCoMultipartiteProbability_densityWindow k hk
        (gammaFromProbability k p) (gammaFromProbability_mem_Ioo hk hsuper hp.2)
        (half_pos hε)
    have hdev := (tendsto_order.mp
      (gnpConditionedEdgeDensity_tendsto_gammaFromProbability k hk p hp hsuper δ hδ)).2
      (ε / 2) (half_pos hε)
    filter_upwards [eventually_ge_atTop n₀, hdev] with n hn hdevn
    let Ω := inducedFreeGraphFinset (inducedStar k) n
    let B : Finset ℕ := (Finset.range (completeEdgeCount n + 1)).filter fun m : ℕ ↦
      |(m : ℝ) / completeEdgeCount n - gammaFromProbability k p| < δ
    have hband : ∀ m ∈ B, (graphFamilyEdgeSlice Ω m).Nonempty →
        uniformSubfamilyProbability (graphFamilyEdgeSlice Ω m)
          (graphFamilyEdgeSlice Ω m ∩ gnpNonCoMultipartiteGraphFinset k n) ≤ ε / 2 := by
      intro m hm _hne
      obtain ⟨hmcap, hmdensity⟩ := Finset.mem_filter.mp hm
      have hmle : m ≤ completeEdgeCount n := Nat.le_of_lt_succ (Finset.mem_range.mp hmcap)
      have hlocal := (hn₀ n hn m hmle hmdensity).le
      simpa only [Ω, graphFamilyEdgeSlice_inducedFree, nonCoMultipartite_exactSlice,
        supercriticalNonCoMultipartiteProbability] using hlocal
    have hΩ : Ω.Nonempty := ⟨⊥, bot_mem_inducedStarFreeGraphFinset (by omega)⟩
    have hbound := gnpConditionedGraphProbability_le_band_error hp (half_pos hε).le
      Ω (gnpNonCoMultipartiteGraphFinset k n) hΩ B hband
    have hout : (Ω.filter fun G ↦ G.edgeFinset.card ∉ B) ⊆
        gnpEdgeDensityDeviationFinset n (gammaFromProbability k p) δ := by
      intro G hG
      have hnot := (Finset.mem_filter.mp hG).2
      have hcap : G.edgeFinset.card ∈ Finset.range (completeEdgeCount n + 1) :=
        Finset.mem_range.mpr (Nat.lt_succ_of_le (card_edgeFinset_le_completeEdgeCount G))
      have hdensity : δ ≤ |(G.edgeFinset.card : ℝ) / completeEdgeCount n -
          gammaFromProbability k p| := by
        apply le_of_not_gt
        intro hsmall
        exact hnot (Finset.mem_filter.mpr ⟨hcap, hsmall⟩)
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _, by
        simpa only [finiteGraphEdges_card_eq_edgeFinset_card] using hdensity⟩
    have hmono := gnpConditionedGraphProbability_mono ⟨hp.1.le, hp.2.le⟩ Ω hout
    change gnpConditionedGraphProbability p Ω
      (gnpEdgeDensityDeviationFinset n (gammaFromProbability k p) δ) < ε / 2 at hdevn
    change gnpConditionedGraphProbability p Ω (gnpNonCoMultipartiteGraphFinset k n) < ε
    linarith

/-- Paper: Theorem `thm:gnp-typ-struc`, strict supercritical structural
assertion. The probability is the actual weighted conditional `G(n,p)` law. -/
theorem gnpConditionedCoMultipartiteProbability_tendsto_one
    (k : ℕ) (hk : 3 ≤ k) (p : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1)
    (hsuper : pK k < p) :
    Tendsto (fun n ↦ gnpConditionedInducedStarProbability k n p
      (gnpCoMultipartiteGraphFinset k n)) atTop (𝓝 1) := by
  have hbad := gnpConditionedNonCoMultipartiteProbability_tendsto_zero k hk p hp hsuper
  have heq (n : ℕ) : gnpConditionedInducedStarProbability k n p
      (gnpCoMultipartiteGraphFinset k n) =
      1 - gnpConditionedInducedStarProbability k n p
        (gnpNonCoMultipartiteGraphFinset k n) := by
    have hsum := gnpConditionedGraphProbability_filter_add_filter_not
      (gnpConditionedInducedStarProbability_denominator_pos (k := k) (n := n) (by omega) hp)
      (fun G ↦ DenseGraph.IsCoMultipartite G (k - 1))
    change gnpConditionedInducedStarProbability k n p (gnpCoMultipartiteGraphFinset k n) +
      gnpConditionedInducedStarProbability k n p (gnpNonCoMultipartiteGraphFinset k n) = 1
      at hsum
    linarith
  simp_rw [heq]
  simpa only [sub_zero] using
    (show Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (𝓝 1) from tendsto_const_nhds).sub hbad

private theorem gnpConditionedGraphProbability_union_le {n : ℕ} {p : ℝ}
    (hp : p ∈ Icc (0 : ℝ) 1) (Ω Q R : Finset (SimpleGraph (Fin n))) :
    gnpConditionedGraphProbability p Ω (Q ∪ R) ≤
      gnpConditionedGraphProbability p Ω Q + gnpConditionedGraphProbability p Ω R := by
  have hsum :
      gnpGraphEventProbability p ((Ω ∩ Q) ∪ (Ω ∩ R)) +
        gnpGraphEventProbability p ((Ω ∩ Q) ∩ (Ω ∩ R)) =
      gnpGraphEventProbability p (Ω ∩ Q) + gnpGraphEventProbability p (Ω ∩ R) :=
    Finset.sum_union_inter
  have hnon := gnpGraphEventProbability_nonneg hp ((Ω ∩ Q) ∩ (Ω ∩ R))
  unfold gnpConditionedGraphProbability
  rw [← add_div, Finset.inter_union_distrib_left]
  exact div_le_div_of_nonneg_right (by linarith) (gnpGraphEventProbability_nonneg hp Ω)

/-- Simultaneous co-multipartite structure and the correct limiting
unordered-edge density, expressed as a single finite graph event. -/
noncomputable def gnpSupercriticalStructuredGraphFinset (k n : ℕ) (p ε : ℝ) :
    Finset (SimpleGraph (Fin n)) :=
  Finset.univ.filter fun G ↦ DenseGraph.IsCoMultipartite G (k - 1) ∧
    |((finiteGraphEdges G).card : ℝ) / completeEdgeCount n - gammaFromProbability k p| < ε

/-- Paper: Theorem `thm:gnp-typ-struc`, strict supercritical branch jointly
with edge-density concentration. For every positive accuracy, both conclusions
hold on the same graph with conditional probability tending to one. -/
theorem inducedStarGnpSupercriticalTypicalStructure
    (k : ℕ) (hk : 3 ≤ k) (p : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1)
    (hsuper : pK k < p) (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n ↦ gnpConditionedInducedStarProbability k n p
      (gnpSupercriticalStructuredGraphFinset k n p ε)) atTop (𝓝 1) := by
  let bad := fun n ↦ gnpNonCoMultipartiteGraphFinset k n ∪
    gnpEdgeDensityDeviationFinset n (gammaFromProbability k p) ε
  have hbad : Tendsto (fun n ↦ gnpConditionedInducedStarProbability k n p (bad n))
      atTop (𝓝 0) := by
    apply squeeze_zero'
      (Eventually.of_forall fun n ↦
        gnpConditionedInducedStarProbability_nonneg k n ⟨hp.1.le, hp.2.le⟩ (bad n))
      (Eventually.of_forall fun n ↦
        gnpConditionedGraphProbability_union_le ⟨hp.1.le, hp.2.le⟩
          (inducedFreeGraphFinset (inducedStar k) n) _ _)
    simpa only [add_zero, gnpConditionedInducedStarProbability] using
      (gnpConditionedNonCoMultipartiteProbability_tendsto_zero k hk p hp hsuper).add
        (gnpConditionedEdgeDensity_tendsto_gammaFromProbability k hk p hp hsuper ε hε)
  have heq (n : ℕ) :
      gnpConditionedInducedStarProbability k n p
        (gnpSupercriticalStructuredGraphFinset k n p ε) =
      1 - gnpConditionedInducedStarProbability k n p (bad n) := by
    let P : SimpleGraph (Fin n) → Prop := fun G ↦
      DenseGraph.IsCoMultipartite G (k - 1) ∧
        |((finiteGraphEdges G).card : ℝ) / completeEdgeCount n -
          gammaFromProbability k p| < ε
    have hsum := gnpConditionedGraphProbability_filter_add_filter_not
      (gnpConditionedInducedStarProbability_denominator_pos (k := k) (n := n) (by omega) hp)
      P
    have hcompl : (Finset.univ.filter fun G : SimpleGraph (Fin n) ↦ ¬P G) = bad n := by
      ext G
      simp only [P, bad, gnpNonCoMultipartiteGraphFinset, gnpEdgeDensityDeviationFinset,
        Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
        not_and_or, not_lt]
    have hsum' : gnpConditionedGraphProbability p (inducedFreeGraphFinset (inducedStar k) n)
        (Finset.univ.filter P) +
      gnpConditionedGraphProbability p (inducedFreeGraphFinset (inducedStar k) n)
        (Finset.univ.filter fun G : SimpleGraph (Fin n) ↦ ¬P G) = 1 := by
      convert hsum using 1 <;> congr
    rw [hcompl] at hsum'
    change gnpConditionedInducedStarProbability k n p
      (gnpSupercriticalStructuredGraphFinset k n p ε) +
      gnpConditionedInducedStarProbability k n p (bad n) = 1 at hsum'
    linarith
  simp_rw [heq]
  simpa only [sub_zero] using
    (show Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (𝓝 1) from tendsto_const_nhds).sub hbad

end InducedStars
