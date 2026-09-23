import InducedStars.FiniteModels.GnpFamilySlices
import InducedStars.FiniteModels.Uniform

/-!
# Exact finite conditioning of the labeled binomial graph law

Conditioning is an event intersection divided by the mass of the ambient
family.  The edge-count mixture below retains every feasible level and is
uniform within each such level.  Empty levels have zero mixing weight.
There are no labeling, automorphism, or orientation factors.
-/

noncomputable section

open Finset Set
open scoped BigOperators

namespace InducedStars

attribute [local instance] Classical.propDecidable

noncomputable local instance conditionedEdgeSetFintype {n : ℕ}
    (G : SimpleGraph (Fin n)) : Fintype G.edgeSet :=
  graphFamiliesEdgeSetFintype G

/-- A nonempty finite graph family has positive `G(n,p)` mass for `0 < p < 1`. -/
theorem gnpGraphEventProbability_pos {n : ℕ} {p : ℝ}
    (hp : p ∈ Ioo (0 : ℝ) 1) {Ω : Finset (SimpleGraph (Fin n))}
    (hΩ : Ω.Nonempty) : 0 < gnpGraphEventProbability p Ω := by
  obtain ⟨G, hG⟩ := hΩ
  have hmono := gnpGraphEventProbability_mono ⟨hp.1.le, hp.2.le⟩
    (Finset.singleton_subset_iff.mpr hG)
  rw [gnpGraphEventProbability_singleton] at hmono
  exact (gnpGraphWeight_pos hp G).trans_le hmono

/-- The exact probability of an arbitrary event `Q` conditional on the
ambient finite graph family `Ω`.  Probability interpretations require a
positive conditioning mass; the algebraic definition is total. -/
noncomputable def gnpConditionedGraphProbability {n : ℕ}
    (p : ℝ) (Ω Q : Finset (SimpleGraph (Fin n))) : ℝ :=
  gnpGraphEventProbability p (Ω ∩ Q) / gnpGraphEventProbability p Ω

/-- For a subfamily the intersection in the conditional law is redundant. -/
theorem gnpConditionedGraphProbability_eq_ratio {n : ℕ} (p : ℝ)
    {Ω Q : Finset (SimpleGraph (Fin n))} (hQ : Q ⊆ Ω) :
    gnpConditionedGraphProbability p Ω Q =
      gnpGraphEventProbability p Q / gnpGraphEventProbability p Ω := by
  rw [gnpConditionedGraphProbability, Finset.inter_eq_right.mpr hQ]

theorem gnpConditionedGraphProbability_nonneg {n : ℕ} {p : ℝ}
    (hp : p ∈ Icc (0 : ℝ) 1) (Ω Q : Finset (SimpleGraph (Fin n))) :
    0 ≤ gnpConditionedGraphProbability p Ω Q :=
  div_nonneg (gnpGraphEventProbability_nonneg hp _)
    (gnpGraphEventProbability_nonneg hp _)

theorem gnpConditionedGraphProbability_mono {n : ℕ} {p : ℝ}
    (hp : p ∈ Icc (0 : ℝ) 1) (Ω : Finset (SimpleGraph (Fin n)))
    {Q R : Finset (SimpleGraph (Fin n))} (hQR : Q ⊆ R) :
    gnpConditionedGraphProbability p Ω Q ≤
      gnpConditionedGraphProbability p Ω R := by
  exact div_le_div_of_nonneg_right
    (gnpGraphEventProbability_mono hp (Finset.inter_subset_inter_left hQR))
    (gnpGraphEventProbability_nonneg hp _)

theorem gnpConditionedGraphProbability_le_one {n : ℕ} {p : ℝ}
    (hp : p ∈ Icc (0 : ℝ) 1) {Ω : Finset (SimpleGraph (Fin n))}
    (hΩ : 0 < gnpGraphEventProbability p Ω)
    (Q : Finset (SimpleGraph (Fin n))) :
    gnpConditionedGraphProbability p Ω Q ≤ 1 := by
  apply (div_le_one hΩ).mpr
  exact gnpGraphEventProbability_mono hp Finset.inter_subset_left

@[simp] theorem gnpConditionedGraphProbability_empty {n : ℕ} (p : ℝ)
    (Ω : Finset (SimpleGraph (Fin n))) :
    gnpConditionedGraphProbability p Ω ∅ = 0 := by
  simp [gnpConditionedGraphProbability, gnpGraphEventProbability]

theorem gnpConditionedGraphProbability_self {n : ℕ} {p : ℝ}
    {Ω : Finset (SimpleGraph (Fin n))}
    (hΩ : 0 < gnpGraphEventProbability p Ω) :
    gnpConditionedGraphProbability p Ω Ω = 1 := by
  simp [gnpConditionedGraphProbability, hΩ.ne']

/-- Complementation is exact whenever the conditioning event has positive
mass.  The complement is taken within the ambient family, not at a fixed
edge count. -/
theorem gnpConditionedGraphProbability_sdiff {n : ℕ} {p : ℝ}
    {Ω : Finset (SimpleGraph (Fin n))}
    (hΩ : 0 < gnpGraphEventProbability p Ω)
    (Q : Finset (SimpleGraph (Fin n))) :
    gnpConditionedGraphProbability p Ω (Ω \ Q) =
      1 - gnpConditionedGraphProbability p Ω Q := by
  have hdis : Disjoint (Ω ∩ Q) (Ω \ Q) := by
    apply Finset.disjoint_left.mpr
    intro G hG hG'
    exact (Finset.mem_sdiff.mp hG').2 (Finset.mem_inter.mp hG).2
  have hunion : (Ω ∩ Q) ∪ (Ω \ Q) = Ω := by
    ext G
    simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
    tauto
  have hsum := gnpGraphEventProbability_union p hdis
  rw [hunion] at hsum
  rw [gnpConditionedGraphProbability_eq_ratio p Finset.sdiff_subset,
    gnpConditionedGraphProbability]
  apply (div_eq_iff hΩ.ne').mpr
  field_simp
  linarith

/-- Predicate complementation under positive conditioning mass. -/
theorem gnpConditionedGraphProbability_filter_not {n : ℕ} {p : ℝ}
    {Ω : Finset (SimpleGraph (Fin n))}
    (hΩ : 0 < gnpGraphEventProbability p Ω)
    (P : SimpleGraph (Fin n) → Prop) :
    gnpConditionedGraphProbability p Ω (Finset.univ.filter fun G ↦ ¬P G) =
      1 - gnpConditionedGraphProbability p Ω (Finset.univ.filter P) := by
  have heq : Ω ∩ (Finset.univ.filter fun G ↦ ¬P G) =
      Ω ∩ (Ω \ Finset.univ.filter P) := by
    ext G
    simp
  unfold gnpConditionedGraphProbability
  rw [heq]
  exact gnpConditionedGraphProbability_sdiff hΩ (Finset.univ.filter P)

/-- An event and its predicate complement have conditional probabilities
summing to one, not merely at most one. -/
theorem gnpConditionedGraphProbability_filter_add_filter_not {n : ℕ} {p : ℝ}
    {Ω : Finset (SimpleGraph (Fin n))}
    (hΩ : 0 < gnpGraphEventProbability p Ω)
    (P : SimpleGraph (Fin n) → Prop) :
    gnpConditionedGraphProbability p Ω (Finset.univ.filter P) +
      gnpConditionedGraphProbability p Ω (Finset.univ.filter fun G ↦ ¬P G) = 1 := by
  rw [gnpConditionedGraphProbability_filter_not hΩ P]
  ring

/-- The `m`-edge slice of an intersection is the intersection of that slice
of the ambient family with the event. -/
theorem graphFamilyEdgeSlice_inter {n m : ℕ}
    (Ω Q : Finset (SimpleGraph (Fin n))) :
    graphFamilyEdgeSlice (Ω ∩ Q) m = graphFamilyEdgeSlice Ω m ∩ Q := by
  ext G
  simp only [mem_graphFamilyEdgeSlice, Finset.mem_inter]
  tauto

/-- All members of a feasible exact-edge slice have the same strictly
positive weight, hence conditioning on that slice gives its uniform law. -/
theorem gnpConditionedGraphProbability_edgeSlice_eq_uniform {n m : ℕ}
    {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1)
    (Ω Q : Finset (SimpleGraph (Fin n)))
    (_hΩ : (graphFamilyEdgeSlice Ω m).Nonempty) :
    gnpConditionedGraphProbability p (graphFamilyEdgeSlice Ω m) Q =
      uniformSubfamilyProbability (graphFamilyEdgeSlice Ω m)
        (graphFamilyEdgeSlice (Ω ∩ Q) m) := by
  unfold gnpConditionedGraphProbability
  rw [← graphFamilyEdgeSlice_inter, gnpGraphEventProbability_graphFamilyEdgeSlice,
    gnpGraphEventProbability_graphFamilyEdgeSlice]
  unfold gnpGraphFamilySliceWeight uniformSubfamilyProbability
  have hp0 : p ^ m ≠ 0 := (pow_pos hp.1 _).ne'
  have hq0 : (1 - p) ^ (completeEdgeCount n - m) ≠ 0 :=
    (pow_pos (sub_pos.mpr hp.2) _).ne'
  simp only [mul_div_mul_right _ _ hq0, mul_div_mul_right _ _ hp0]

private theorem gnpGraphFamilySliceWeight_inter {n m : ℕ}
    (p : ℝ) (Ω Q : Finset (SimpleGraph (Fin n))) :
    gnpGraphFamilySliceWeight (Ω ∩ Q) m p =
      gnpGraphFamilySliceWeight Ω m p *
        uniformSubfamilyProbability (graphFamilyEdgeSlice Ω m)
          (graphFamilyEdgeSlice (Ω ∩ Q) m) := by
  have hsub : graphFamilyEdgeSlice (Ω ∩ Q) m ⊆ graphFamilyEdgeSlice Ω m := by
    intro G hG
    have h := mem_graphFamilyEdgeSlice.mp hG
    exact mem_graphFamilyEdgeSlice.mpr ⟨(Finset.mem_inter.mp h.1).1, h.2⟩
  by_cases hzero : (graphFamilyEdgeSlice Ω m).card = 0
  · have hevent : (graphFamilyEdgeSlice (Ω ∩ Q) m).card = 0 :=
      Nat.eq_zero_of_le_zero (hzero ▸ Finset.card_le_card hsub)
    simp [gnpGraphFamilySliceWeight, uniformSubfamilyProbability, hzero, hevent]
  · have hreal : ((graphFamilyEdgeSlice Ω m).card : ℝ) ≠ 0 := by
      exact_mod_cast hzero
    unfold gnpGraphFamilySliceWeight uniformSubfamilyProbability
    field_simp

/-- The exact edge-count mixture of the conditional graph law.  Each
mixing weight is the conditional mass of the edge-count level, and the
event law inside that level is uniform.  Empty levels contribute zero. -/
theorem gnpConditionedGraphProbability_eq_edgeCount_mixture {n : ℕ}
    (p : ℝ) (Ω Q : Finset (SimpleGraph (Fin n))) :
    gnpConditionedGraphProbability p Ω Q =
      ∑ m ∈ Finset.range (completeEdgeCount n + 1),
        (gnpGraphFamilySliceWeight Ω m p / gnpGraphEventProbability p Ω) *
          uniformSubfamilyProbability (graphFamilyEdgeSlice Ω m)
            (graphFamilyEdgeSlice (Ω ∩ Q) m) := by
  unfold gnpConditionedGraphProbability
  rw [gnpGraphEventProbability_eq_sum_graphFamilySliceWeights, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro m _hm
  rw [gnpGraphFamilySliceWeight_inter]
  ring

/-- Under positive conditioning mass, the mixing weights sum to one. -/
theorem gnpConditionedGraphProbability_edgeCount_weights_sum {n : ℕ}
    {p : ℝ} {Ω : Finset (SimpleGraph (Fin n))}
    (hΩ : 0 < gnpGraphEventProbability p Ω) :
    (∑ m ∈ Finset.range (completeEdgeCount n + 1),
      gnpGraphFamilySliceWeight Ω m p / gnpGraphEventProbability p Ω) = 1 := by
  rw [← Finset.sum_div, ← gnpGraphEventProbability_eq_sum_graphFamilySliceWeights]
  exact div_self hΩ.ne'

/-- A finite uniform estimate on all feasible edge levels in a band
transfers to the conditioned law, at the cost of the probability of leaving
that band.  No hypothesis is imposed on infeasible levels. -/
theorem gnpConditionedGraphProbability_le_band_error {n : ℕ} {p ε : ℝ}
    (hp : p ∈ Ioo (0 : ℝ) 1) (hε : 0 ≤ ε)
    (Ω Q : Finset (SimpleGraph (Fin n))) (hΩ : Ω.Nonempty)
    (B : Finset ℕ)
    (hband : ∀ m ∈ B, (graphFamilyEdgeSlice Ω m).Nonempty →
      uniformSubfamilyProbability (graphFamilyEdgeSlice Ω m)
        (graphFamilyEdgeSlice Ω m ∩ Q) ≤ ε) :
    gnpConditionedGraphProbability p Ω Q ≤ ε +
      gnpConditionedGraphProbability p Ω
        (Ω.filter fun G ↦ G.edgeFinset.card ∉ B) := by
  let R := Ω.filter fun G ↦ G.edgeFinset.card ∉ B
  let w := fun m ↦ gnpGraphFamilySliceWeight Ω m p / gnpGraphEventProbability p Ω
  have hw : ∀ m, 0 ≤ w m := fun m ↦
    div_nonneg (gnpGraphFamilySliceWeight_nonneg Ω ⟨hp.1.le, hp.2.le⟩)
      (gnpGraphEventProbability_nonneg ⟨hp.1.le, hp.2.le⟩ Ω)
  have hsum : (∑ m ∈ Finset.range (completeEdgeCount n + 1), w m) = 1 :=
    gnpConditionedGraphProbability_edgeCount_weights_sum
      (gnpGraphEventProbability_pos hp hΩ)
  have hlevel (m : ℕ) :
      uniformSubfamilyProbability (graphFamilyEdgeSlice Ω m)
          (graphFamilyEdgeSlice (Ω ∩ Q) m) ≤ ε +
        uniformSubfamilyProbability (graphFamilyEdgeSlice Ω m)
          (graphFamilyEdgeSlice (Ω ∩ R) m) := by
    by_cases hne : (graphFamilyEdgeSlice Ω m).Nonempty
    · by_cases hm : m ∈ B
      · rw [graphFamilyEdgeSlice_inter]
        exact (hband m hm hne).trans (le_add_of_nonneg_right (by
          unfold uniformSubfamilyProbability
          positivity))
      · have heq : graphFamilyEdgeSlice (Ω ∩ R) m = graphFamilyEdgeSlice Ω m := by
          ext G
          simp only [mem_graphFamilyEdgeSlice, Finset.mem_inter, R, Finset.mem_filter]
          constructor
          · tauto
          · rintro ⟨hG, hcard⟩
            exact ⟨⟨hG, hG, by simpa only [hcard] using hm⟩, hcard⟩
        rw [heq]
        have hself : uniformSubfamilyProbability (graphFamilyEdgeSlice Ω m)
            (graphFamilyEdgeSlice Ω m) = 1 := by
          unfold uniformSubfamilyProbability
          exact div_self (by exact_mod_cast (Finset.card_pos.mpr hne).ne')
        rw [hself, graphFamilyEdgeSlice_inter]
        exact (uniformSubfamilyProbability_le_one hne Finset.inter_subset_left).trans
          (le_add_of_nonneg_left hε)
    · have hempty := Finset.not_nonempty_iff_eq_empty.mp hne
      simp only [uniformSubfamilyProbability, hempty, Finset.card_empty,
        Nat.cast_zero, div_zero, add_zero]
      exact hε
  change gnpConditionedGraphProbability p Ω Q ≤ ε + gnpConditionedGraphProbability p Ω R
  rw [gnpConditionedGraphProbability_eq_edgeCount_mixture,
    gnpConditionedGraphProbability_eq_edgeCount_mixture]
  calc
    _ ≤ ∑ m ∈ Finset.range (completeEdgeCount n + 1),
        (w m * ε + w m * uniformSubfamilyProbability (graphFamilyEdgeSlice Ω m)
          (graphFamilyEdgeSlice (Ω ∩ R) m)) := by
      apply Finset.sum_le_sum
      intro m _hm
      simpa only [mul_add] using mul_le_mul_of_nonneg_left (hlevel m) (hw m)
    _ = _ := by rw [Finset.sum_add_distrib, ← Finset.sum_mul, hsum, one_mul]

/-- The arbitrary event `Q` under the actual induced-star-free conditioned
`G(n,p)` law.  This is not a uniform graph law before the edge count is fixed. -/
noncomputable def gnpConditionedInducedStarProbability (k n : ℕ) (p : ℝ)
    (Q : Finset (SimpleGraph (Fin n))) : ℝ :=
  gnpConditionedGraphProbability p (inducedFreeGraphFinset (inducedStar k) n) Q

/-- The empty graph supplies positivity for every order, including zero. -/
theorem gnpConditionedInducedStarProbability_denominator_pos {k n : ℕ}
    (hk : 1 ≤ k) {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) :
    0 < gnpGraphEventProbability p (inducedFreeGraphFinset (inducedStar k) n) :=
  gnpInducedStarFreeProbability_pos hk hp

theorem gnpConditionedInducedStarProbability_eq_ratio {k n : ℕ} (p : ℝ)
    {Q : Finset (SimpleGraph (Fin n))}
    (hQ : Q ⊆ inducedFreeGraphFinset (inducedStar k) n) :
    gnpConditionedInducedStarProbability k n p Q =
      gnpGraphEventProbability p Q / gnpInducedStarFreeProbability k n p :=
  gnpConditionedGraphProbability_eq_ratio p hQ

theorem gnpConditionedInducedStarProbability_nonneg (k n : ℕ) {p : ℝ}
    (hp : p ∈ Icc (0 : ℝ) 1) (Q : Finset (SimpleGraph (Fin n))) :
    0 ≤ gnpConditionedInducedStarProbability k n p Q :=
  gnpConditionedGraphProbability_nonneg hp _ _

theorem gnpConditionedInducedStarProbability_le_one {k n : ℕ} (hk : 1 ≤ k)
    {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) (Q : Finset (SimpleGraph (Fin n))) :
    gnpConditionedInducedStarProbability k n p Q ≤ 1 :=
  gnpConditionedGraphProbability_le_one ⟨hp.1.le, hp.2.le⟩
    (gnpConditionedInducedStarProbability_denominator_pos hk hp) Q

/-- Compatibility with the already formalized conditioned optimizer-far
event: the new general interface denotes exactly the same probability. -/
theorem gnpConditionedInducedStarProbability_optimizerFar (k n : ℕ) (p ε : ℝ) :
    gnpConditionedInducedStarProbability k n p
        (gnpOptimizerFarInducedStarFinset k p ε n) =
      gnpConditionedOptimizerFarProbability k n p ε :=
  gnpConditionedInducedStarProbability_eq_ratio p
    (gnpOptimizerFarInducedStarFinset_subset k n p ε)

/-- The existing exact-edge induced-free family is precisely the edge-count
slice used in the finite mixture. -/
theorem graphFamilyEdgeSlice_inducedFree {h n : ℕ}
    (H : SimpleGraph (Fin h)) (m : ℕ) :
    graphFamilyEdgeSlice (inducedFreeGraphFinset H n) m =
      inducedFreeGraphFinsetWithEdges H n m := by
  ext G
  simp

/-- Conditional on induced-star-freeness and any feasible exact edge count,
the finite graph is uniform on the project's existing exact-edge family. -/
theorem gnpConditionedInducedStar_exactEdge_eq_uniform {k n m : ℕ} {p : ℝ}
    (hp : p ∈ Ioo (0 : ℝ) 1) (Q : Finset (SimpleGraph (Fin n)))
    (hne : (inducedStarFreeGraphFinsetWithEdges k n m).Nonempty) :
    gnpConditionedGraphProbability p (inducedStarFreeGraphFinsetWithEdges k n m) Q =
      uniformSubfamilyProbability (inducedStarFreeGraphFinsetWithEdges k n m)
        (inducedStarFreeGraphFinsetWithEdges k n m ∩ Q) := by
  have h := gnpConditionedGraphProbability_edgeSlice_eq_uniform hp
    (inducedFreeGraphFinset (inducedStar k) n) Q
    (by simpa only [graphFamilyEdgeSlice_inducedFree] using hne)
  simpa only [graphFamilyEdgeSlice_inter, graphFamilyEdgeSlice_inducedFree] using h

/-- The induced-star-free conditioned law as its exact finite mixture over
all admissible unordered edge counts. -/
theorem gnpConditionedInducedStarProbability_eq_edgeCount_mixture
    (k n : ℕ) (p : ℝ) (Q : Finset (SimpleGraph (Fin n))) :
    gnpConditionedInducedStarProbability k n p Q =
      ∑ m ∈ Finset.range (completeEdgeCount n + 1),
        (gnpInducedFreeSliceWeight (inducedStar k) n m p /
          gnpInducedStarFreeProbability k n p) *
          uniformSubfamilyProbability (inducedStarFreeGraphFinsetWithEdges k n m)
            (inducedStarFreeGraphFinsetWithEdges k n m ∩ Q) := by
  unfold gnpConditionedInducedStarProbability
  rw [gnpConditionedGraphProbability_eq_edgeCount_mixture]
  apply Finset.sum_congr rfl
  intro m _hm
  rw [graphFamilyEdgeSlice_inter, graphFamilyEdgeSlice_inducedFree]
  rfl

/-! ## Unconditioned weighted cut-ball masses -/

/-- The open cut ball, restricted to induced-star-free labeled graphs.
This is the finite family denoted `B_n(W,τ)` in `paper/gnp.tex`. -/
noncomputable def gnpInducedStarCutBallFinset (k : ℕ) (W : Graphon)
    (τ : ℝ) (n : ℕ) : Finset (SimpleGraph (Fin n)) :=
  (inducedFreeGraphFinset (inducedStar k) n).filter fun G ↦ cutDist (graphGraphon G) W < τ

@[simp] theorem mem_gnpInducedStarCutBallFinset {k n : ℕ} {W : Graphon} {τ : ℝ}
    {G : SimpleGraph (Fin n)} :
    G ∈ gnpInducedStarCutBallFinset k W τ n ↔
      ¬Regularity.InducedEmbeds (inducedStar k) G ∧ cutDist (graphGraphon G) W < τ := by
  simp [gnpInducedStarCutBallFinset]

theorem gnpInducedStarCutBallFinset_subset (k n : ℕ) (W : Graphon) (τ : ℝ) :
    gnpInducedStarCutBallFinset k W τ n ⊆ inducedFreeGraphFinset (inducedStar k) n :=
  Finset.filter_subset _ _

/-- The unconditioned `G(n,p)` mass of the induced-star-free cut ball.
Unlike a conditioned probability, this includes the full induced-free
event cost.  Paper: the quantity `Z_p(B_n(W,τ))` in
Lemma `lemma:critical-gnp-comparison-K1k`. -/
noncomputable def gnpInducedStarCutBallMass (k n : ℕ) (p : ℝ) (W : Graphon)
    (τ : ℝ) : ℝ :=
  gnpGraphEventProbability p (gnpInducedStarCutBallFinset k W τ n)

theorem gnpInducedStarCutBallMass_nonneg (k n : ℕ) {p : ℝ}
    (hp : p ∈ Icc (0 : ℝ) 1) (W : Graphon) (τ : ℝ) :
    0 ≤ gnpInducedStarCutBallMass k n p W τ :=
  gnpGraphEventProbability_nonneg hp _

theorem gnpInducedStarCutBallMass_le_probability (k n : ℕ) {p : ℝ}
    (hp : p ∈ Icc (0 : ℝ) 1) (W : Graphon) (τ : ℝ) :
    gnpInducedStarCutBallMass k n p W τ ≤ gnpInducedStarFreeProbability k n p :=
  gnpGraphEventProbability_mono hp (gnpInducedStarCutBallFinset_subset k n W τ)

/-- Exact conversion from an unconditioned cut-ball mass to its conditioned
probability, without changing the graph family or its edge normalization. -/
theorem gnpConditionedInducedStarProbability_cutBall (k n : ℕ) (p : ℝ)
    (W : Graphon) (τ : ℝ) :
    gnpConditionedInducedStarProbability k n p (gnpInducedStarCutBallFinset k W τ n) =
      gnpInducedStarCutBallMass k n p W τ / gnpInducedStarFreeProbability k n p :=
  gnpConditionedInducedStarProbability_eq_ratio p
    (gnpInducedStarCutBallFinset_subset k n W τ)

end InducedStars
