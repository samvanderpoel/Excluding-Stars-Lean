import InducedStars.C4.TypeCountingData
import InducedStars.C4.TypeLiftConsistency
import InducedStars.C4.ColoredStability
import InducedStars.C4.TemplateSlices
import InducedStars.Regularity.TypeLemma
import DenseGraph.Combinatorics.ExponentialSums

/-!
# Bounded type grouping for C4 rough structure

Paper: the regularity and grouping steps in `lemma:c4-rough-struc`.
All constants precede the ambient graph. The counting objects are actual
partial templates, with missing pairs and realization errors kept separate.
-/

noncomputable section
open Finset Filter InducedStars.Regularity InducedStars.Regularity.RegularityColoredGraph
open scoped Classical
namespace InducedStars

/-- The one-part initial partition, used only at positive ambient order. -/
def c4TrivialInitialPartition (n : ℕ) (hn : 0 < n) :
    EquitableInitialPartition (Fin n) 1 :=
  EquitableInitialPartition.ofParts (fun _ ↦ univ)
    (fun _ ↦ ⟨⟨0, hn⟩, mem_univ _⟩)
    (by intro i _ j _ hij; exact (hij (Subsingleton.elim i j)).elim)
    (by simp) (by simp [Nat.dist_self])

/-- Every sufficiently large induced-C4-free graph has a bounded lifted
template with the required missing-pair and realization budgets. -/
theorem exists_c4BoundedLift_for_every_graph {tau etaMax : ℝ}
    (htau : 0 < tau) (htauHalf : tau < 1/2) (hetaMax : 0 < etaMax) :
    ∃ eta : ℝ, 0 < eta ∧ eta ≤ etaMax ∧ ∃ u n0 : ℕ, 0 < u ∧
      ∀ n ≥ n0, ∀ G : SimpleGraph (Fin n), ¬InducedEmbeds inducedC4 G →
        ∃ J ∈ c4BoundedLiftTemplateFamily n u,
          ¬ColoredHomExists inducedC4 J ∧
            ((finiteGraphEdges J.graphᶜ).card : ℝ) ≤ 3*eta*(n : ℝ)^2 ∧
              (DenseGraph.coloredInconsistency G J : ℝ) ≤ 3*tau*(n : ℝ)^2 := by
  obtain ⟨estar, hestar, _, htype⟩ := typeLemma tau 4 htau htauHalf (by decide)
  let eta := min etaMax (estar/2)
  have heta : 0 < eta := lt_min hetaMax (half_pos hestar)
  have hsmall : eta < estar := (min_le_right _ _).trans_lt (by linarith)
  have hL : 0 < Nat.ceil (1/tau) := Nat.ceil_pos.mpr (by positivity)
  obtain ⟨u, n0, hu⟩ := htype (Nat.ceil (1/tau)) 1 hL (by decide) eta heta hsmall
  refine ⟨eta, heta, min_le_left _ _, max u 1, max n0 1, by omega, ?_⟩
  intro n hn G hfree
  have hnpos : 0 < n := by omega
  obtain ⟨T⟩ := hu G (by decide : 0 < 1) le_rfl
    (c4TrivialInitialPartition n hnpos) (by simpa using (show n0 ≤ n by omega))
  have hk : 0 < T.regularityType.partition.clusterCount :=
    hL.trans_le T.lower_clusterCount
  refine ⟨c4LiftedType T.regularityType hk,
    c4LiftedType_mem_boundedFamily _ hk (T.upper_clusterCount.trans (le_max_left _ _)),
    c4LiftedType_no_coloredHom _ hk hfree, c4LiftedType_missing_le _ hk, ?_⟩
  exact c4LiftedType_inconsistency_le_of_ceil _ hk T.lower_clusterCount

/-- Exponential in the vertex order, hence negligible on the quadratic
entropy scale. This bound also covers a zero-sized reduced universe. -/
theorem eventually_card_c4BoundedLift_le_exp (u : ℕ) {a : ℝ} (ha : 0 < a) :
    ∀ᶠ n : ℕ in atTop,
      ((c4BoundedLiftTemplateFamily n u).card : ℝ) ≤ Real.exp (a*(n : ℝ)^2) := by
  let C : ℕ := (u+1)*(2^u*4^(u*u))
  have hC : 1 ≤ C := by
    have : 0 < C := by dsimp [C]; positivity
    omega
  filter_upwards [DenseGraph.eventually_pow_mul_exp_neg_sq_le (C*(2*u)) ha,
    eventually_ge_atTop 1] with n hbound hn
  have hcard : (c4BoundedLiftTemplateFamily n u).card ≤ (C*(2*u))^n := by
    apply (card_c4BoundedLiftTemplateFamily_le n u).trans
    change C*(2*u)^n ≤ _
    calc
      C*(2*u)^n ≤ C^n*(2*u)^n := Nat.mul_le_mul_right _ (by
        calc C = C^1 := by simp
             _ ≤ C^n := Nat.pow_le_pow_right hC hn)
      _ = _ := (mul_pow _ _ _).symm
  have hb : ((C*(2*u))^n : ℕ) ≤ Real.exp (a*(n : ℝ)^2) := by
    have hb := hbound.trans (show Real.exp (-(a/2*(n : ℝ)^2)) ≤ 1 from
      Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg (n : ℝ)]))
    have hh := mul_le_mul_of_nonneg_right hb (Real.exp_pos (a*(n : ℝ)^2)).le
    simpa only [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero,
      mul_one, one_mul] using hh
  exact (by exact_mod_cast hcard : ((c4BoundedLiftTemplateFamily n u).card : ℝ) ≤
    ((C*(2*u))^n : ℕ)).trans hb

/-- Actual induced-free graphs whose minimum split edit distance is at
least the prescribed quadratic cutoff. -/
def c4FarGraphFinset (n m : ℕ) (epsilon : ℝ) : Finset (SimpleGraph (Fin n)) :=
  (inducedC4FreeGraphFinsetWithEdges n m).filter fun G ↦
    epsilon*(n : ℝ)^2 ≤ c4DefectCost G (canonicalC4Division G)

@[simp] theorem mem_c4FarGraphFinset {n m : ℕ} {epsilon : ℝ}
    {G : SimpleGraph (Fin n)} : G ∈ c4FarGraphFinset n m epsilon ↔
      G ∈ inducedC4FreeGraphFinsetWithEdges n m ∧
        epsilon*(n : ℝ)^2 ≤ c4DefectCost G (canonicalC4Division G) := by
  simp [c4FarGraphFinset]

/-- The canonical defect cost is a lower bound on the actual edit distance
to every split graph, not just to the chosen split completion. -/
theorem canonicalC4Defect_le_editDistance_of_split {n : ℕ}
    (G H : SimpleGraph (Fin n)) (hH : DenseGraph.IsSplitGraph H) :
    c4DefectCost G (canonicalC4Division G) ≤ DenseGraph.simpleGraphEditDistance G H := by
  obtain ⟨P⟩ := hH
  let D : C4Division (Fin n) := P.independentPart
  have hzero : c4DefectCost H D = 0 := by
    rw [c4DefectCost_eq_zero_iff, c4DefectGraph_eq_bot_iff]
    have hB : D.cliquePart = P.cliquePart := P.cliquePart_eq_compl.symm
    exact ⟨P.independent, by rw [hB]; exact P.clique⟩
  apply (canonicalC4Division_minimal G D).trans
  have h := DenseGraph.coloredInconsistency_le_graphEdit_add G H (c4SplitColoring D)
  simpa only [c4SplitColoring_inconsistency_eq_defect, hzero, add_zero] using h

/-- Literal edit-distance interpretation of the far-family predicate. -/
theorem mem_c4FarGraphFinset_iff_editDistance {n m : ℕ} {epsilon : ℝ}
    {G : SimpleGraph (Fin n)} : G ∈ c4FarGraphFinset n m epsilon ↔
      G ∈ inducedC4FreeGraphFinsetWithEdges n m ∧
        ∀ H : SimpleGraph (Fin n), DenseGraph.IsSplitGraph H →
          epsilon*(n : ℝ)^2 ≤ DenseGraph.simpleGraphEditDistance G H := by
  rw [mem_c4FarGraphFinset]
  constructor
  · rintro ⟨hG, hfar⟩
    exact ⟨hG, fun H hH ↦ hfar.trans (by
      exact_mod_cast canonicalC4Defect_le_editDistance_of_split G H hH)⟩
  · rintro ⟨hG, hfar⟩
    refine ⟨hG, ?_⟩
    have h := hfar (c4SplitCompletion G (canonicalC4Division G))
      (c4SplitCompletion_isSplit G _)
    simpa only [← c4DefectCost_eq_splitCompletion_editDistance] using h

theorem c4_template_distance_of_far {n m : ℕ} {epsilon rho : ℝ}
    {G : SimpleGraph (Fin n)} (hG : G ∈ c4FarGraphFinset n m epsilon)
    (J : RegularityColoredGraph (Fin n))
    (herror : (DenseGraph.coloredInconsistency G J : ℝ) ≤ rho*(n : ℝ)^2)
    (D : C4Division (Fin n)) :
    (epsilon-rho)*(n : ℝ)^2 ≤ DenseGraph.coloredEditDistance J (c4SplitColoring D) := by
  have hmin := (Nat.cast_le (α := ℝ)).mpr (canonicalC4Division_minimal G D)
  have hdist := (Nat.cast_le (α := ℝ)).mpr
    (c4DefectCost_le_inconsistency_add_coloredEdit G J D)
  push_cast at hdist
  have hfar := (mem_c4FarGraphFinset.mp hG).2
  nlinarith

/-- Templates with a genuine positive separation from every split coloring. -/
def c4FarLiftTemplateFamily (n u : ℕ) (eta epsilon : ℝ) :
    Finset (RegularityColoredGraph (Fin n)) :=
  (c4BoundedLiftTemplateFamily n u).filter fun J ↦
    ¬ColoredHomExists inducedC4 J ∧
      ((finiteGraphEdges J.graphᶜ).card : ℝ) ≤ eta*(n : ℝ)^2 ∧
        ∀ D : C4Division (Fin n),
          epsilon*(n : ℝ)^2 ≤ DenseGraph.coloredEditDistance J (c4SplitColoring D)

/-- Finite union bound by actual near-realization slices, without a
graph-dependent type being incorrectly treated as fixed. -/
theorem c4FarGraph_card_le_template_sum {n m u : ℕ} {epsilon rho eta : ℝ}
    (hlift : ∀ G ∈ c4FarGraphFinset n m epsilon,
      ∃ J ∈ c4BoundedLiftTemplateFamily n u,
        ¬ColoredHomExists inducedC4 J ∧
          ((finiteGraphEdges J.graphᶜ).card : ℝ) ≤ eta*(n : ℝ)^2 ∧
            (DenseGraph.coloredInconsistency G J : ℝ) ≤ rho*(n : ℝ)^2) :
    (c4FarGraphFinset n m epsilon).card ≤
      ∑ J ∈ c4FarLiftTemplateFamily n u eta (epsilon-rho),
        (c4TemplateNearSlice J m ⌊rho*(n : ℝ)^2⌋₊).card := by
  apply (card_le_card (t := (c4FarLiftTemplateFamily n u eta (epsilon-rho)).biUnion
    (fun J ↦ c4TemplateNearSlice J m ⌊rho*(n : ℝ)^2⌋₊)) ?_).trans card_biUnion_le
  intro G hG
  obtain ⟨J, hJ, hfree, hmissing, herror⟩ := hlift G hG
  apply mem_biUnion.mpr
  refine ⟨J, mem_filter.mpr ⟨hJ, hfree, hmissing,
    c4_template_distance_of_far hG J herror⟩, ?_⟩
  have hm := (mem_inducedC4FreeGraphFinsetWithEdges.mp
    (mem_c4FarGraphFinset.mp hG).1).2
  exact (mem_c4TemplateNearSlice J G _ _).mpr ⟨hm, Nat.le_floor herror⟩

end InducedStars
