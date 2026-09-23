import InducedStars.FiniteModels.ExactEdgeRepair
import InducedStars.FiniteModels.EntropyAsymptotics
import Mathlib.Tactic

/-!
# Conditional concentration of flexible edge counts

At fixed latent positions the edge coordinates in a graphon sample are
independent Bernoulli variables.  This file proves the finite first- and
second-moment identities directly from the conditional graph weights, then
uses the resulting Chebyshev estimate for the present and absent flexible
pairs needed by exact-edge repair.
-/

noncomputable section

open Filter MeasureTheory Set Topology
open scoped BigOperators ENNReal Classical

namespace InducedStars

/-! ## Finite coordinate sums -/

/-- The real-valued indicator that an unordered pair is an edge. -/
def conditionalEdgeIndicator {n : ℕ} (e : Sym2 (Fin n))
    (G : SimpleGraph (Fin n)) : ℝ :=
  if e ∈ finiteGraphEdges G then 1 else 0

/-- Number of edges of `G` in the specified finite pair set, viewed in `ℝ`. -/
def conditionalEdgeCount {n : ℕ} (s : Finset (Sym2 (Fin n)))
    (G : SimpleGraph (Fin n)) : ℝ :=
  ∑ e ∈ s, conditionalEdgeIndicator e G

/-- Conditional mean of the edge count on a finite pair set. -/
def conditionalEdgeCountMean {n : ℕ} (W : Graphon)
    (x : Fin n → UnitInterval) (s : Finset (Sym2 (Fin n))) : ℝ :=
  ∑ e ∈ s, graphonPairValue W x e

@[simp]
theorem conditionalEdgeIndicator_sq {n : ℕ} (e : Sym2 (Fin n))
    (G : SimpleGraph (Fin n)) :
    conditionalEdgeIndicator e G ^ 2 = conditionalEdgeIndicator e G := by
  by_cases he : e ∈ finiteGraphEdges G <;>
    simp [conditionalEdgeIndicator, he]

theorem conditionalEdgeCount_eq_card_inter {n : ℕ}
    (s : Finset (Sym2 (Fin n))) (G : SimpleGraph (Fin n)) :
    conditionalEdgeCount s G = ((s ∩ finiteGraphEdges G).card : ℝ) := by
  classical
  unfold conditionalEdgeCount conditionalEdgeIndicator
  rw [Finset.sum_boole]
  congr 2

/-- Exact first moment of a finite conditional edge count. -/
theorem sum_weight_mul_conditionalEdgeCount {n : ℕ} (W : Graphon)
    (x : Fin n → UnitInterval) (s : Finset (Sym2 (Fin n)))
    (hNonDiag : ∀ e ∈ s, ¬e.IsDiag) :
    (∑ G : SimpleGraph (Fin n), wRandomConditionalWeight W x G *
      conditionalEdgeCount s G) = conditionalEdgeCountMean W x s := by
  classical
  unfold conditionalEdgeCount conditionalEdgeCountMean
  calc
    (∑ G : SimpleGraph (Fin n), wRandomConditionalWeight W x G *
        ∑ e ∈ s, conditionalEdgeIndicator e G) =
        ∑ e ∈ s, ∑ G : SimpleGraph (Fin n),
          wRandomConditionalWeight W x G * conditionalEdgeIndicator e G := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
    _ = ∑ e ∈ s, graphonPairValue W x e := by
      apply Finset.sum_congr rfl
      intro e he
      exact sum_wRandomConditionalWeight_indicator_edge W x e (hNonDiag e he)

/-- Exact conditional joint moment of two edge indicators. -/
theorem sum_weight_mul_two_conditionalEdgeIndicators {n : ℕ} (W : Graphon)
    (x : Fin n → UnitInterval) (e f : Sym2 (Fin n))
    (he : ¬e.IsDiag) (hf : ¬f.IsDiag) :
    (∑ G : SimpleGraph (Fin n), wRandomConditionalWeight W x G *
      conditionalEdgeIndicator e G * conditionalEdgeIndicator f G) =
      if e = f then graphonPairValue W x e
      else graphonPairValue W x e * graphonPairValue W x f := by
  classical
  by_cases hef : e = f
  · subst f
    rw [if_pos rfl]
    convert sum_wRandomConditionalWeight_indicator_edge W x e he using 1
    apply Finset.sum_congr rfl
    intro G _hG
    unfold conditionalEdgeIndicator
    by_cases hG : e ∈ finiteGraphEdges G <;> simp [hG]
  · rw [if_neg hef]
    exact sum_wRandomConditionalWeight_indicator_two_edges
      W x e f he hf hef

private theorem sum_pairMoment_eq_square_add_variance
    {α : Type*} [DecidableEq α] (s : Finset α) (p : α → ℝ) :
    (∑ e ∈ s, ∑ f ∈ s, if e = f then p e else p e * p f) =
      (∑ e ∈ s, p e) ^ 2 + ∑ e ∈ s, p e * (1 - p e) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      have hax (x : α) (hx : x ∈ s) : a ≠ x := by
        intro h
        exact ha (h ▸ hx)
      have hxa (x : α) (hx : x ∈ s) : x ≠ a := (hax x hx).symm
      have hleft :
          (∑ x ∈ s, if a = x then p a else p a * p x) =
            ∑ x ∈ s, p a * p x := by
        apply Finset.sum_congr rfl
        intro x hx
        simp [hax x hx]
      have houter :
          (∑ x ∈ s, ((if x = a then p x else p x * p a) +
            ∑ y ∈ s, if x = y then p x else p x * p y)) =
          (∑ x ∈ s, p a * p x) +
            ∑ x ∈ s, ∑ y ∈ s,
              if x = y then p x else p x * p y := by
        rw [Finset.sum_add_distrib]
        congr 1
        apply Finset.sum_congr rfl
        intro x hx
        simp [hxa x hx, mul_comm]
      simp only [Finset.sum_insert ha]
      rw [hleft, houter, ih]
      simp only [if_true]
      rw [← Finset.mul_sum]
      ring

/-- Exact conditional second moment of a finite edge count. -/
theorem sum_weight_mul_conditionalEdgeCount_sq {n : ℕ} (W : Graphon)
    (x : Fin n → UnitInterval) (s : Finset (Sym2 (Fin n)))
    (hNonDiag : ∀ e ∈ s, ¬e.IsDiag) :
    (∑ G : SimpleGraph (Fin n), wRandomConditionalWeight W x G *
      conditionalEdgeCount s G ^ 2) =
      conditionalEdgeCountMean W x s ^ 2 +
        ∑ e ∈ s, graphonPairValue W x e *
          (1 - graphonPairValue W x e) := by
  classical
  calc
    (∑ G : SimpleGraph (Fin n), wRandomConditionalWeight W x G *
        conditionalEdgeCount s G ^ 2) =
        ∑ e ∈ s, ∑ f ∈ s, ∑ G : SimpleGraph (Fin n),
          wRandomConditionalWeight W x G *
            conditionalEdgeIndicator e G * conditionalEdgeIndicator f G := by
      unfold conditionalEdgeCount
      simp_rw [pow_two, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro e _he
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro f _hf
      apply Finset.sum_congr rfl
      intro G _hG
      ring
    _ = ∑ e ∈ s, ∑ f ∈ s,
          if e = f then graphonPairValue W x e
          else graphonPairValue W x e * graphonPairValue W x f := by
      apply Finset.sum_congr rfl
      intro e he
      apply Finset.sum_congr rfl
      intro f hf
      exact sum_weight_mul_two_conditionalEdgeIndicators W x e f
        (hNonDiag e he) (hNonDiag f hf)
    _ = conditionalEdgeCountMean W x s ^ 2 +
          ∑ e ∈ s, graphonPairValue W x e *
            (1 - graphonPairValue W x e) := by
      exact sum_pairMoment_eq_square_add_variance s
        (graphonPairValue W x)

/-- The centered conditional second moment is the sum of the Bernoulli
coordinate variances. -/
theorem sum_weight_mul_conditionalEdgeCount_centered_sq {n : ℕ}
    (W : Graphon) (x : Fin n → UnitInterval)
    (s : Finset (Sym2 (Fin n))) (hNonDiag : ∀ e ∈ s, ¬e.IsDiag) :
    (∑ G : SimpleGraph (Fin n), wRandomConditionalWeight W x G *
      (conditionalEdgeCount s G - conditionalEdgeCountMean W x s) ^ 2) =
      ∑ e ∈ s, graphonPairValue W x e *
        (1 - graphonPairValue W x e) := by
  classical
  let μ := conditionalEdgeCountMean W x s
  calc
    (∑ G : SimpleGraph (Fin n), wRandomConditionalWeight W x G *
        (conditionalEdgeCount s G - μ) ^ 2) =
        (∑ G : SimpleGraph (Fin n), wRandomConditionalWeight W x G *
          conditionalEdgeCount s G ^ 2) -
        2 * μ * (∑ G : SimpleGraph (Fin n),
          wRandomConditionalWeight W x G * conditionalEdgeCount s G) +
        μ ^ 2 * (∑ G : SimpleGraph (Fin n),
          wRandomConditionalWeight W x G) := by
      calc
        (∑ G : SimpleGraph (Fin n), wRandomConditionalWeight W x G *
            (conditionalEdgeCount s G - μ) ^ 2) =
            ∑ G : SimpleGraph (Fin n),
              (wRandomConditionalWeight W x G * conditionalEdgeCount s G ^ 2 -
                2 * μ * (wRandomConditionalWeight W x G *
                  conditionalEdgeCount s G) +
                μ ^ 2 * wRandomConditionalWeight W x G) := by
          apply Finset.sum_congr rfl
          intro G _hG
          ring
        _ = _ := by
          rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
            ← Finset.mul_sum, ← Finset.mul_sum]
    _ = (μ ^ 2 + ∑ e ∈ s, graphonPairValue W x e *
          (1 - graphonPairValue W x e)) - 2 * μ * μ + μ ^ 2 := by
      rw [sum_wRandomConditionalWeight,
        sum_weight_mul_conditionalEdgeCount W x s hNonDiag,
        sum_weight_mul_conditionalEdgeCount_sq W x s hNonDiag]
      dsimp only [μ]
      ring
    _ = ∑ e ∈ s, graphonPairValue W x e *
          (1 - graphonPairValue W x e) := by ring

/-- Conditional probability of a graph event at fixed latent positions. -/
def wRandomConditionalGraphEventProbability {n : ℕ} (W : Graphon)
    (x : Fin n → UnitInterval) (A : Set (SimpleGraph (Fin n))) : ℝ :=
  ∑ G : SimpleGraph (Fin n),
    if G ∈ A then wRandomConditionalWeight W x G else 0

theorem wRandomConditionalGraphEventProbability_nonneg {n : ℕ}
    (W : Graphon) (x : Fin n → UnitInterval)
    (A : Set (SimpleGraph (Fin n))) :
    0 ≤ wRandomConditionalGraphEventProbability W x A := by
  classical
  unfold wRandomConditionalGraphEventProbability
  apply Finset.sum_nonneg
  intro G _hG
  by_cases hA : G ∈ A <;> simp [hA, wRandomConditionalWeight_nonneg W x G]

theorem wRandomConditionalGraphEventProbability_le_one {n : ℕ}
    (W : Graphon) (x : Fin n → UnitInterval)
    (A : Set (SimpleGraph (Fin n))) :
    wRandomConditionalGraphEventProbability W x A ≤ 1 := by
  classical
  calc
    wRandomConditionalGraphEventProbability W x A ≤
        ∑ G : SimpleGraph (Fin n), wRandomConditionalWeight W x G := by
      unfold wRandomConditionalGraphEventProbability
      apply Finset.sum_le_sum
      intro G _hG
      by_cases hA : G ∈ A
      · simp [hA]
      · simp [hA, wRandomConditionalWeight_nonneg W x G]
    _ = 1 := sum_wRandomConditionalWeight W x

theorem wRandomConditionalGraphEventProbability_mono {n : ℕ}
    (W : Graphon) (x : Fin n → UnitInterval)
    {A B : Set (SimpleGraph (Fin n))} (hAB : A ⊆ B) :
    wRandomConditionalGraphEventProbability W x A ≤
      wRandomConditionalGraphEventProbability W x B := by
  classical
  unfold wRandomConditionalGraphEventProbability
  apply Finset.sum_le_sum
  intro G _hG
  by_cases hA : G ∈ A
  · have hB := hAB hA
    simp [hA, hB]
  · by_cases hB : G ∈ B
    · simp [hA, hB, wRandomConditionalWeight_nonneg W x G]
    · simp [hA, hB]

/-- The sum of the conditional Bernoulli variances on `s` is at most
`|s|`.  This deliberately uses the coarse bound `p(1-p) ≤ 1`, which is
enough for a uniform tail tending to zero. -/
theorem conditionalEdgeCount_variance_le_card {n : ℕ} (W : Graphon)
    (x : Fin n → UnitInterval) (s : Finset (Sym2 (Fin n))) :
    (∑ e ∈ s, graphonPairValue W x e *
      (1 - graphonPairValue W x e)) ≤ (s.card : ℝ) := by
  calc
    (∑ e ∈ s, graphonPairValue W x e *
        (1 - graphonPairValue W x e)) ≤ ∑ _e ∈ s, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro e _he
      have hp0 := graphonPairValue_nonneg W x e
      have hp1 := graphonPairValue_le_one W x e
      nlinarith
    _ = (s.card : ℝ) := by simp

/-- Finite Chebyshev bound for a conditional edge count. -/
theorem wRandomConditionalGraphEventProbability_edgeCount_deviation_le
    {n : ℕ} (W : Graphon) (x : Fin n → UnitInterval)
    (s : Finset (Sym2 (Fin n))) (hNonDiag : ∀ e ∈ s, ¬e.IsDiag)
    (a : ℝ) (ha : 0 < a) :
    wRandomConditionalGraphEventProbability W x
        {G | a ≤ |conditionalEdgeCount s G -
          conditionalEdgeCountMean W x s|} ≤
      (s.card : ℝ) / a ^ 2 := by
  classical
  have hWeighted :
      a ^ 2 * wRandomConditionalGraphEventProbability W x
          {G | a ≤ |conditionalEdgeCount s G -
            conditionalEdgeCountMean W x s|} ≤
        ∑ G : SimpleGraph (Fin n), wRandomConditionalWeight W x G *
          (conditionalEdgeCount s G - conditionalEdgeCountMean W x s) ^ 2 := by
    unfold wRandomConditionalGraphEventProbability
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro G _hG
    by_cases hbad : a ≤ |conditionalEdgeCount s G -
        conditionalEdgeCountMean W x s|
    · have hmem : G ∈ {G | a ≤ |conditionalEdgeCount s G -
          conditionalEdgeCountMean W x s|} := hbad
      rw [if_pos hmem]
      have hsquare : a ^ 2 ≤
          (conditionalEdgeCount s G - conditionalEdgeCountMean W x s) ^ 2 := by
        simpa only [sq_abs] using
          (sq_le_sq₀ (le_of_lt ha) (abs_nonneg _)).2 hbad
      simpa only [mul_assoc, mul_comm, mul_left_comm] using
        mul_le_mul_of_nonneg_left hsquare
          (wRandomConditionalWeight_nonneg W x G)
    · have hmem : G ∉ {G | a ≤ |conditionalEdgeCount s G -
          conditionalEdgeCountMean W x s|} := hbad
      rw [if_neg hmem]
      rw [mul_zero]
      exact mul_nonneg (wRandomConditionalWeight_nonneg W x G) (sq_nonneg _)
  have hSecond :
      (∑ G : SimpleGraph (Fin n), wRandomConditionalWeight W x G *
          (conditionalEdgeCount s G - conditionalEdgeCountMean W x s) ^ 2) ≤
        (s.card : ℝ) := by
    rw [sum_weight_mul_conditionalEdgeCount_centered_sq W x s hNonDiag]
    exact conditionalEdgeCount_variance_le_card W x s
  apply (le_div_iff₀ (sq_pos_of_pos ha)).2
  nlinarith [hWeighted.trans hSecond]

/-! ## Flexible-pair lower tails -/

theorem conditionalEdgeCountMean_flexiblePairFinset_ge {n : ℕ}
    (W : Graphon) (x : Fin n → UnitInterval) (L U : ℝ) :
    L * (flexiblePairCount W L U x : ℝ) ≤
      conditionalEdgeCountMean W x (flexiblePairFinset W L U x) := by
  unfold conditionalEdgeCountMean flexiblePairCount
  calc
    L * ((flexiblePairFinset W L U x).card : ℝ) =
        ∑ _e ∈ flexiblePairFinset W L U x, L := by simp [mul_comm]
    _ ≤ ∑ e ∈ flexiblePairFinset W L U x, graphonPairValue W x e := by
      apply Finset.sum_le_sum
      intro e he
      exact (mem_flexiblePairFinset_iff W L U x e).mp he |>.2.1

theorem conditionalEdgeCountMean_flexiblePairFinset_le {n : ℕ}
    (W : Graphon) (x : Fin n → UnitInterval) (L U : ℝ) :
    conditionalEdgeCountMean W x (flexiblePairFinset W L U x) ≤
      U * (flexiblePairCount W L U x : ℝ) := by
  unfold conditionalEdgeCountMean flexiblePairCount
  calc
    (∑ e ∈ flexiblePairFinset W L U x, graphonPairValue W x e) ≤
        ∑ _e ∈ flexiblePairFinset W L U x, U := by
      apply Finset.sum_le_sum
      intro e he
      exact (mem_flexiblePairFinset_iff W L U x e).mp he |>.2.2
    _ = U * ((flexiblePairFinset W L U x).card : ℝ) := by simp [mul_comm]

theorem conditionalEdgeCount_flexiblePairFinset_eq_present_card {n : ℕ}
    (W : Graphon) (x : Fin n → UnitInterval) (L U : ℝ)
    (G : SimpleGraph (Fin n)) :
    conditionalEdgeCount (flexiblePairFinset W L U x) G =
      ((presentFlexibleEdgeFinset W x L U G).card : ℝ) := by
  rw [conditionalEdgeCount_eq_card_inter]
  rfl

theorem absent_card_add_conditionalEdgeCount_eq_flexiblePairCount {n : ℕ}
    (W : Graphon) (x : Fin n → UnitInterval) (L U : ℝ)
    (G : SimpleGraph (Fin n)) :
    ((absentFlexibleEdgeFinset W x L U G).card : ℝ) +
        conditionalEdgeCount (flexiblePairFinset W L U x) G =
      (flexiblePairCount W L U x : ℝ) := by
  rw [conditionalEdgeCount_eq_card_inter]
  exact_mod_cast Finset.card_sdiff_add_card_inter
    (flexiblePairFinset W L U x) (finiteGraphEdges G)

/-- Conditional probability that fewer than half the guaranteed `L`-fraction
of flexible pairs are present. -/
theorem wRandomConditional_presentFlexible_deficit_le {n : ℕ}
    (W : Graphon) (x : Fin n → UnitInterval) (L U : ℝ)
    (hL : 0 < L) (hCount : 0 < flexiblePairCount W L U x) :
    wRandomConditionalGraphEventProbability W x
        {G | ((presentFlexibleEdgeFinset W x L U G).card : ℝ) <
          L / 2 * (flexiblePairCount W L U x : ℝ)} ≤
      (flexiblePairCount W L U x : ℝ) /
        (L / 2 * (flexiblePairCount W L U x : ℝ)) ^ 2 := by
  let s := flexiblePairFinset W L U x
  let F : ℝ := flexiblePairCount W L U x
  have hF : 0 < F := by
    dsimp only [F]
    exact_mod_cast hCount
  have ha : 0 < L / 2 * F := mul_pos (half_pos hL) hF
  calc
    wRandomConditionalGraphEventProbability W x
        {G | ((presentFlexibleEdgeFinset W x L U G).card : ℝ) < L / 2 * F} ≤
        wRandomConditionalGraphEventProbability W x
          {G | L / 2 * F ≤ |conditionalEdgeCount s G -
            conditionalEdgeCountMean W x s|} := by
      apply wRandomConditionalGraphEventProbability_mono W x
      intro G hG
      change ((presentFlexibleEdgeFinset W x L U G).card : ℝ) <
        L / 2 * F at hG
      have hMean := conditionalEdgeCountMean_flexiblePairFinset_ge W x L U
      have hCountEq :=
        conditionalEdgeCount_flexiblePairFinset_eq_present_card W x L U G
      change L * F ≤ conditionalEdgeCountMean W x s at hMean
      change conditionalEdgeCount s G =
        ((presentFlexibleEdgeFinset W x L U G).card : ℝ) at hCountEq
      have hneg : conditionalEdgeCount s G -
          conditionalEdgeCountMean W x s < 0 := by linarith
      change L / 2 * F ≤ |conditionalEdgeCount s G -
        conditionalEdgeCountMean W x s|
      rw [abs_of_neg hneg]
      linarith
    _ ≤ (s.card : ℝ) / (L / 2 * F) ^ 2 :=
      wRandomConditionalGraphEventProbability_edgeCount_deviation_le
        W x s (fun e he ↦ (mem_flexiblePairFinset_iff W L U x e).mp he |>.1)
        (L / 2 * F) ha
    _ = F / (L / 2 * F) ^ 2 := rfl

/-- Conditional probability that fewer than half the guaranteed
`(1-U)`-fraction of flexible pairs are absent. -/
theorem wRandomConditional_absentFlexible_deficit_le {n : ℕ}
    (W : Graphon) (x : Fin n → UnitInterval) (L U : ℝ)
    (hU : U < 1) (hCount : 0 < flexiblePairCount W L U x) :
    wRandomConditionalGraphEventProbability W x
        {G | ((absentFlexibleEdgeFinset W x L U G).card : ℝ) <
          (1 - U) / 2 * (flexiblePairCount W L U x : ℝ)} ≤
      (flexiblePairCount W L U x : ℝ) /
        ((1 - U) / 2 * (flexiblePairCount W L U x : ℝ)) ^ 2 := by
  let s := flexiblePairFinset W L U x
  let F : ℝ := flexiblePairCount W L U x
  have hF : 0 < F := by
    dsimp only [F]
    exact_mod_cast hCount
  have hc : 0 < 1 - U := sub_pos.mpr hU
  have ha : 0 < (1 - U) / 2 * F := mul_pos (half_pos hc) hF
  calc
    wRandomConditionalGraphEventProbability W x
        {G | ((absentFlexibleEdgeFinset W x L U G).card : ℝ) <
          (1 - U) / 2 * F} ≤
        wRandomConditionalGraphEventProbability W x
          {G | (1 - U) / 2 * F ≤ |conditionalEdgeCount s G -
            conditionalEdgeCountMean W x s|} := by
      apply wRandomConditionalGraphEventProbability_mono W x
      intro G hG
      change ((absentFlexibleEdgeFinset W x L U G).card : ℝ) <
        (1 - U) / 2 * F at hG
      have hMean := conditionalEdgeCountMean_flexiblePairFinset_le W x L U
      have hPartition :=
        absent_card_add_conditionalEdgeCount_eq_flexiblePairCount W x L U G
      change conditionalEdgeCountMean W x s ≤ U * F at hMean
      change ((absentFlexibleEdgeFinset W x L U G).card : ℝ) +
        conditionalEdgeCount s G = F at hPartition
      have hpos : 0 < conditionalEdgeCount s G -
          conditionalEdgeCountMean W x s := by linarith
      change (1 - U) / 2 * F ≤ |conditionalEdgeCount s G -
        conditionalEdgeCountMean W x s|
      rw [abs_of_pos hpos]
      linarith
    _ ≤ (s.card : ℝ) / ((1 - U) / 2 * F) ^ 2 :=
      wRandomConditionalGraphEventProbability_edgeCount_deviation_le
        W x s (fun e he ↦ (mem_flexiblePairFinset_iff W L U x e).mp he |>.1)
        ((1 - U) / 2 * F) ha
    _ = F / ((1 - U) / 2 * F) ^ 2 := rfl

/-! ## Measurable joint capacity events -/

@[measurability, fun_prop]
theorem measurable_presentFlexibleEdgeCount {n : ℕ} (W : Graphon)
    (L U : ℝ) (G : SimpleGraph (Fin n)) :
    Measurable (fun x : Fin n → UnitInterval ↦
      (presentFlexibleEdgeFinset W x L U G).card) := by
  exact (measurable_of_countable (fun s : Finset (Sym2 (Fin n)) ↦
    (s ∩ finiteGraphEdges G).card)).comp (measurable_flexiblePairFinset W L U)

@[measurability, fun_prop]
theorem measurable_absentFlexibleEdgeCount {n : ℕ} (W : Graphon)
    (L U : ℝ) (G : SimpleGraph (Fin n)) :
    Measurable (fun x : Fin n → UnitInterval ↦
      (absentFlexibleEdgeFinset W x L U G).card) := by
  exact (measurable_of_countable (fun s : Finset (Sym2 (Fin n)) ↦
    (s \ finiteGraphEdges G).card)).comp (measurable_flexiblePairFinset W L U)

/-- Latent configurations with the fixed positive fraction of flexible pairs
provided by the band-abundance theorem. -/
def flexiblePairAbundantSet (n : ℕ) (W : Graphon) (L U : ℝ) :
    Set (Fin n → UnitInterval) :=
  {x | graphonClosedBandMass W L U / 2 <
    normalizedFlexiblePairCount W L U x}

theorem measurableSet_flexiblePairAbundantSet (n : ℕ) (W : Graphon)
    (L U : ℝ) : MeasurableSet (flexiblePairAbundantSet n W L U) := by
  unfold flexiblePairAbundantSet
  measurability

/-- Joint event that the sampled graph has too few present flexible pairs. -/
def presentFlexibleDeficitJointEvent (n : ℕ) (W : Graphon) (L U : ℝ) :
    WRandomJointEvent n where
  Holds x G := ((presentFlexibleEdgeFinset W x L U G).card : ℝ) <
    L / 2 * (flexiblePairCount W L U x : ℝ)
  measurableSet_holds G := by measurability

/-- Joint event that the sampled graph has too few absent flexible pairs. -/
def absentFlexibleDeficitJointEvent (n : ℕ) (W : Graphon) (L U : ℝ) :
    WRandomJointEvent n where
  Holds x G := ((absentFlexibleEdgeFinset W x L U G).card : ℝ) <
    (1 - U) / 2 * (flexiblePairCount W L U x : ℝ)
  measurableSet_holds G := by measurability

/-- Present-flexible deficit restricted to abundant latent configurations. -/
def presentFlexibleDeficitOnAbundanceJointEvent (n : ℕ) (W : Graphon)
    (L U : ℝ) : WRandomJointEvent n where
  Holds x G := x ∈ flexiblePairAbundantSet n W L U ∧
    (presentFlexibleDeficitJointEvent n W L U).Holds x G
  measurableSet_holds G :=
    (measurableSet_flexiblePairAbundantSet n W L U).inter
      ((presentFlexibleDeficitJointEvent n W L U).measurableSet_holds G)

/-- Absent-flexible deficit restricted to abundant latent configurations. -/
def absentFlexibleDeficitOnAbundanceJointEvent (n : ℕ) (W : Graphon)
    (L U : ℝ) : WRandomJointEvent n where
  Holds x G := x ∈ flexiblePairAbundantSet n W L U ∧
    (absentFlexibleDeficitJointEvent n W L U).Holds x G
  measurableSet_holds G :=
    (measurableSet_flexiblePairAbundantSet n W L U).inter
      ((absentFlexibleDeficitJointEvent n W L U).measurableSet_holds G)

theorem wRandomJointEventIntegrand_presentFlexibleDeficit {n : ℕ}
    (W : Graphon) (L U : ℝ) (x : Fin n → UnitInterval) :
    wRandomJointEventIntegrand W (presentFlexibleDeficitJointEvent n W L U) x =
      wRandomConditionalGraphEventProbability W x
        {G | ((presentFlexibleEdgeFinset W x L U G).card : ℝ) <
          L / 2 * (flexiblePairCount W L U x : ℝ)} :=
  rfl

theorem wRandomJointEventIntegrand_absentFlexibleDeficit {n : ℕ}
    (W : Graphon) (L U : ℝ) (x : Fin n → UnitInterval) :
    wRandomJointEventIntegrand W (absentFlexibleDeficitJointEvent n W L U) x =
      wRandomConditionalGraphEventProbability W x
        {G | ((absentFlexibleEdgeFinset W x L U G).card : ℝ) <
          (1 - U) / 2 * (flexiblePairCount W L U x : ℝ)} :=
  rfl

theorem wRandomJointEventIntegrand_presentDeficitOnAbundance {n : ℕ}
    (W : Graphon) (L U : ℝ) (x : Fin n → UnitInterval) :
    wRandomJointEventIntegrand W
        (presentFlexibleDeficitOnAbundanceJointEvent n W L U) x =
      if x ∈ flexiblePairAbundantSet n W L U then
        wRandomJointEventIntegrand W
          (presentFlexibleDeficitJointEvent n W L U) x
      else 0 := by
  classical
  unfold wRandomJointEventIntegrand presentFlexibleDeficitOnAbundanceJointEvent
    presentFlexibleDeficitJointEvent
  by_cases hx : x ∈ flexiblePairAbundantSet n W L U <;> simp [hx]

theorem wRandomJointEventIntegrand_absentDeficitOnAbundance {n : ℕ}
    (W : Graphon) (L U : ℝ) (x : Fin n → UnitInterval) :
    wRandomJointEventIntegrand W
        (absentFlexibleDeficitOnAbundanceJointEvent n W L U) x =
      if x ∈ flexiblePairAbundantSet n W L U then
        wRandomJointEventIntegrand W
          (absentFlexibleDeficitJointEvent n W L U) x
      else 0 := by
  classical
  unfold wRandomJointEventIntegrand absentFlexibleDeficitOnAbundanceJointEvent
    absentFlexibleDeficitJointEvent
  by_cases hx : x ∈ flexiblePairAbundantSet n W L U <;> simp [hx]

private theorem conditionalChebyshevRate_le_of_abundant
    (c m F N : ℝ) (hc : 0 < c) (hm : 0 < m) (hF : 0 < F) (hN : 0 < N)
    (hAbundant : m / 2 < 2 * F / N ^ 2) :
    F / (c / 2 * F) ^ 2 ≤ (16 / (c ^ 2 * m)) / N ^ 2 := by
  have hc0 : c ≠ 0 := ne_of_gt hc
  have hm0 : m ≠ 0 := ne_of_gt hm
  have hF0 : F ≠ 0 := ne_of_gt hF
  have hN0 : N ≠ 0 := ne_of_gt hN
  have hleft : F / (c / 2 * F) ^ 2 = 4 / (c ^ 2 * F) := by
    field_simp
    ring
  have hright : (16 / (c ^ 2 * m)) / N ^ 2 =
      16 / (c ^ 2 * m * N ^ 2) := by
    field_simp
  rw [hleft, hright]
  have hN2 : 0 < N ^ 2 := sq_pos_of_pos hN
  have hCore : m * N ^ 2 ≤ 4 * F := by
    have h := (lt_div_iff₀ hN2).mp hAbundant
    nlinarith
  have hDenLeft : 0 < c ^ 2 * F := mul_pos (sq_pos_of_pos hc) hF
  have hDenRight : 0 < c ^ 2 * m * N ^ 2 :=
    mul_pos (mul_pos (sq_pos_of_pos hc) hm) hN2
  apply (div_le_div_iff₀ hDenLeft hDenRight).2
  calc
    4 * (c ^ 2 * m * N ^ 2) = 4 * c ^ 2 * (m * N ^ 2) := by ring
    _ ≤ 4 * c ^ 2 * (4 * F) :=
      mul_le_mul_of_nonneg_left hCore (by positivity)
    _ = 16 * (c ^ 2 * F) := by ring

theorem wRandomJointEventIntegrand_presentDeficitOnAbundance_le {n : ℕ}
    (hn : 0 < n) (W : Graphon) (L U : ℝ) (hL : 0 < L)
    (hMass : 0 < graphonClosedBandMass W L U)
    (x : Fin n → UnitInterval) :
    wRandomJointEventIntegrand W
        (presentFlexibleDeficitOnAbundanceJointEvent n W L U) x ≤
      (16 / (L ^ 2 * graphonClosedBandMass W L U)) / (n : ℝ) ^ 2 := by
  rw [wRandomJointEventIntegrand_presentDeficitOnAbundance]
  by_cases hx : x ∈ flexiblePairAbundantSet n W L U
  · rw [if_pos hx, wRandomJointEventIntegrand_presentFlexibleDeficit]
    let F : ℝ := flexiblePairCount W L U x
    have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
    have hAbundant : graphonClosedBandMass W L U / 2 <
        2 * F / (n : ℝ) ^ 2 := by
      change graphonClosedBandMass W L U / 2 <
        normalizedFlexiblePairCount W L U x at hx
      simpa only [normalizedFlexiblePairCount, F] using hx
    have hF : 0 < F := by
      have hN2 : 0 < (n : ℝ) ^ 2 := sq_pos_of_pos hnR
      have h := (lt_div_iff₀ hN2).mp hAbundant
      nlinarith
    have hCount : 0 < flexiblePairCount W L U x := by
      dsimp only [F] at hF
      exact_mod_cast hF
    calc
      wRandomConditionalGraphEventProbability W x
          {G | ((presentFlexibleEdgeFinset W x L U G).card : ℝ) <
            L / 2 * (flexiblePairCount W L U x : ℝ)} ≤
          F / (L / 2 * F) ^ 2 :=
        wRandomConditional_presentFlexible_deficit_le W x L U hL hCount
      _ ≤ (16 / (L ^ 2 * graphonClosedBandMass W L U)) /
          (n : ℝ) ^ 2 :=
        conditionalChebyshevRate_le_of_abundant L
          (graphonClosedBandMass W L U) F (n : ℝ)
          hL hMass hF hnR hAbundant
  · rw [if_neg hx]
    positivity

theorem wRandomJointEventIntegrand_absentDeficitOnAbundance_le {n : ℕ}
    (hn : 0 < n) (W : Graphon) (L U : ℝ) (hU : U < 1)
    (hMass : 0 < graphonClosedBandMass W L U)
    (x : Fin n → UnitInterval) :
    wRandomJointEventIntegrand W
        (absentFlexibleDeficitOnAbundanceJointEvent n W L U) x ≤
      (16 / ((1 - U) ^ 2 * graphonClosedBandMass W L U)) /
        (n : ℝ) ^ 2 := by
  rw [wRandomJointEventIntegrand_absentDeficitOnAbundance]
  by_cases hx : x ∈ flexiblePairAbundantSet n W L U
  · rw [if_pos hx, wRandomJointEventIntegrand_absentFlexibleDeficit]
    let F : ℝ := flexiblePairCount W L U x
    have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
    have hAbundant : graphonClosedBandMass W L U / 2 <
        2 * F / (n : ℝ) ^ 2 := by
      change graphonClosedBandMass W L U / 2 <
        normalizedFlexiblePairCount W L U x at hx
      simpa only [normalizedFlexiblePairCount, F] using hx
    have hF : 0 < F := by
      have hN2 : 0 < (n : ℝ) ^ 2 := sq_pos_of_pos hnR
      have h := (lt_div_iff₀ hN2).mp hAbundant
      nlinarith
    have hCount : 0 < flexiblePairCount W L U x := by
      dsimp only [F] at hF
      exact_mod_cast hF
    calc
      wRandomConditionalGraphEventProbability W x
          {G | ((absentFlexibleEdgeFinset W x L U G).card : ℝ) <
            (1 - U) / 2 * (flexiblePairCount W L U x : ℝ)} ≤
          F / ((1 - U) / 2 * F) ^ 2 :=
        wRandomConditional_absentFlexible_deficit_le W x L U hU hCount
      _ ≤ (16 / ((1 - U) ^ 2 * graphonClosedBandMass W L U)) /
          (n : ℝ) ^ 2 :=
        conditionalChebyshevRate_le_of_abundant (1 - U)
          (graphonClosedBandMass W L U) F (n : ℝ)
          (sub_pos.mpr hU) hMass hF hnR hAbundant
  · rw [if_neg hx]
    positivity

theorem wRandomJointEventProbability_presentDeficitOnAbundance_le {n : ℕ}
    (hn : 0 < n) (W : Graphon) (L U : ℝ) (hL : 0 < L)
    (hMass : 0 < graphonClosedBandMass W L U) :
    wRandomJointEventProbability W
        (presentFlexibleDeficitOnAbundanceJointEvent n W L U) ≤
      (16 / (L ^ 2 * graphonClosedBandMass W L U)) / (n : ℝ) ^ 2 := by
  unfold wRandomJointEventProbability
  calc
    (∫ x : Fin n → UnitInterval,
        wRandomJointEventIntegrand W
          (presentFlexibleDeficitOnAbundanceJointEvent n W L U) x) ≤
        ∫ _x : Fin n → UnitInterval,
          (16 / (L ^ 2 * graphonClosedBandMass W L U)) / (n : ℝ) ^ 2 :=
      integral_mono
        (integrable_wRandomJointEventIntegrand W
          (presentFlexibleDeficitOnAbundanceJointEvent n W L U))
        (integrable_const _) fun x ↦
          wRandomJointEventIntegrand_presentDeficitOnAbundance_le
            hn W L U hL hMass x
    _ = _ := by simp

theorem wRandomJointEventProbability_absentDeficitOnAbundance_le {n : ℕ}
    (hn : 0 < n) (W : Graphon) (L U : ℝ) (hU : U < 1)
    (hMass : 0 < graphonClosedBandMass W L U) :
    wRandomJointEventProbability W
        (absentFlexibleDeficitOnAbundanceJointEvent n W L U) ≤
      (16 / ((1 - U) ^ 2 * graphonClosedBandMass W L U)) /
        (n : ℝ) ^ 2 := by
  unfold wRandomJointEventProbability
  calc
    (∫ x : Fin n → UnitInterval,
        wRandomJointEventIntegrand W
          (absentFlexibleDeficitOnAbundanceJointEvent n W L U) x) ≤
        ∫ _x : Fin n → UnitInterval,
          (16 / ((1 - U) ^ 2 * graphonClosedBandMass W L U)) /
            (n : ℝ) ^ 2 :=
      integral_mono
        (integrable_wRandomJointEventIntegrand W
          (absentFlexibleDeficitOnAbundanceJointEvent n W L U))
        (integrable_const _) fun x ↦
          wRandomJointEventIntegrand_absentDeficitOnAbundance_le
            hn W L U hU hMass x
    _ = _ := by simp

/-! ## Joint high-probability capacity -/

/-- Joint event that the latent sample is not in the abundant band-pair
regime. -/
def flexiblePairNonabundanceJointEvent (n : ℕ) (W : Graphon) (L U : ℝ) :
    WRandomJointEvent n :=
  WRandomJointEvent.ofLatentSet (flexiblePairAbundantSet n W L U)ᶜ
    (measurableSet_flexiblePairAbundantSet n W L U).compl

theorem wRandomJointEventProbability_presentDeficit_le_nonabundance_add
    {n : ℕ} (W : Graphon) (L U : ℝ) :
    wRandomJointEventProbability W (presentFlexibleDeficitJointEvent n W L U) ≤
      wRandomLatentEventProbability (flexiblePairAbundantSet n W L U)ᶜ +
        wRandomJointEventProbability W
          (presentFlexibleDeficitOnAbundanceJointEvent n W L U) := by
  calc
    wRandomJointEventProbability W (presentFlexibleDeficitJointEvent n W L U) ≤
        wRandomJointEventProbability W
          ((flexiblePairNonabundanceJointEvent n W L U).union
            (presentFlexibleDeficitOnAbundanceJointEvent n W L U)) := by
      apply wRandomJointEventProbability_mono W
      intro x G hbad
      by_cases hx : x ∈ flexiblePairAbundantSet n W L U
      · exact Or.inr ⟨hx, hbad⟩
      · exact Or.inl hx
    _ ≤ wRandomJointEventProbability W
          (flexiblePairNonabundanceJointEvent n W L U) +
        wRandomJointEventProbability W
          (presentFlexibleDeficitOnAbundanceJointEvent n W L U) :=
      wRandomJointEventProbability_union_le W _ _
    _ = wRandomLatentEventProbability (flexiblePairAbundantSet n W L U)ᶜ +
        wRandomJointEventProbability W
          (presentFlexibleDeficitOnAbundanceJointEvent n W L U) := by
      congr 1
      unfold flexiblePairNonabundanceJointEvent
      exact wRandomJointEventProbability_ofLatentSet W _ _

theorem wRandomJointEventProbability_absentDeficit_le_nonabundance_add
    {n : ℕ} (W : Graphon) (L U : ℝ) :
    wRandomJointEventProbability W (absentFlexibleDeficitJointEvent n W L U) ≤
      wRandomLatentEventProbability (flexiblePairAbundantSet n W L U)ᶜ +
        wRandomJointEventProbability W
          (absentFlexibleDeficitOnAbundanceJointEvent n W L U) := by
  calc
    wRandomJointEventProbability W (absentFlexibleDeficitJointEvent n W L U) ≤
        wRandomJointEventProbability W
          ((flexiblePairNonabundanceJointEvent n W L U).union
            (absentFlexibleDeficitOnAbundanceJointEvent n W L U)) := by
      apply wRandomJointEventProbability_mono W
      intro x G hbad
      by_cases hx : x ∈ flexiblePairAbundantSet n W L U
      · exact Or.inr ⟨hx, hbad⟩
      · exact Or.inl hx
    _ ≤ wRandomJointEventProbability W
          (flexiblePairNonabundanceJointEvent n W L U) +
        wRandomJointEventProbability W
          (absentFlexibleDeficitOnAbundanceJointEvent n W L U) :=
      wRandomJointEventProbability_union_le W _ _
    _ = wRandomLatentEventProbability (flexiblePairAbundantSet n W L U)ᶜ +
        wRandomJointEventProbability W
          (absentFlexibleDeficitOnAbundanceJointEvent n W L U) := by
      congr 1
      unfold flexiblePairNonabundanceJointEvent
      exact wRandomJointEventProbability_ofLatentSet W _ _

private theorem tendsto_const_div_natCast_sq_zero (C : ℝ) :
    Tendsto (fun n : ℕ ↦ C / (n : ℝ) ^ 2) atTop (nhds 0) := by
  have h₁ : Tendsto (fun n : ℕ ↦ C / (n : ℝ)) atTop (nhds 0) :=
    tendsto_const_div_atTop_nhds_zero_nat C
  have h₂ : Tendsto (fun n : ℕ ↦ 1 / (n : ℝ)) atTop (nhds 0) :=
    tendsto_one_div_atTop_nhds_zero_nat
  have hMul : Tendsto (fun n : ℕ ↦ C / (n : ℝ) * (1 / (n : ℝ)))
      atTop (nhds 0) := by
    simpa using h₁.mul h₂
  apply hMul.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  field_simp

theorem flexiblePairNonabundance_probability_tendsto_zero
    (W : Graphon) (L U : ℝ)
    (hMass : 0 < graphonClosedBandMass W L U) :
    Tendsto
      (fun n ↦ wRandomLatentEventProbability
        (flexiblePairAbundantSet n W L U)ᶜ)
      atTop (nhds 0) := by
  have hHigh : Tendsto
      (fun n ↦ wRandomLatentEventProbability
        (flexiblePairAbundantSet n W L U)) atTop (nhds 1) := by
    simpa only [flexiblePairAbundantSet] using
      flexiblePairAbundance_probability_tendsto_one W L U hMass
  have hSub : Tendsto
      (fun n ↦ (1 : ℝ) - wRandomLatentEventProbability
        (flexiblePairAbundantSet n W L U)) atTop (nhds 0) := by
    have hConst : Tendsto (fun _n : ℕ ↦ (1 : ℝ)) atTop (nhds 1) :=
      tendsto_const_nhds
    simpa using (hConst.sub hHigh)
  apply hSub.congr'
  filter_upwards [] with n
  rw [wRandomLatentEventProbability_compl _
    (measurableSet_flexiblePairAbundantSet n W L U)]

theorem presentFlexibleDeficit_probability_tendsto_zero
    (W : Graphon) (L U : ℝ) (hL : 0 < L)
    (hMass : 0 < graphonClosedBandMass W L U) :
    Tendsto
      (fun n ↦ wRandomJointEventProbability W
        (presentFlexibleDeficitJointEvent n W L U))
      atTop (nhds 0) := by
  have hLow := flexiblePairNonabundance_probability_tendsto_zero W L U hMass
  have hRate := tendsto_const_div_natCast_sq_zero
    (16 / (L ^ 2 * graphonClosedBandMass W L U))
  apply squeeze_zero'
  · filter_upwards [] with n
    exact wRandomJointEventProbability_nonneg W _
  · filter_upwards [eventually_gt_atTop 0] with n hn
    calc
      wRandomJointEventProbability W
          (presentFlexibleDeficitJointEvent n W L U) ≤
          wRandomLatentEventProbability (flexiblePairAbundantSet n W L U)ᶜ +
            wRandomJointEventProbability W
              (presentFlexibleDeficitOnAbundanceJointEvent n W L U) :=
        wRandomJointEventProbability_presentDeficit_le_nonabundance_add W L U
      _ ≤ wRandomLatentEventProbability (flexiblePairAbundantSet n W L U)ᶜ +
          (16 / (L ^ 2 * graphonClosedBandMass W L U)) / (n : ℝ) ^ 2 :=
        add_le_add_right
          (wRandomJointEventProbability_presentDeficitOnAbundance_le
            hn W L U hL hMass) _
  · simpa using hLow.add hRate

theorem absentFlexibleDeficit_probability_tendsto_zero
    (W : Graphon) (L U : ℝ) (hU : U < 1)
    (hMass : 0 < graphonClosedBandMass W L U) :
    Tendsto
      (fun n ↦ wRandomJointEventProbability W
        (absentFlexibleDeficitJointEvent n W L U))
      atTop (nhds 0) := by
  have hLow := flexiblePairNonabundance_probability_tendsto_zero W L U hMass
  have hRate := tendsto_const_div_natCast_sq_zero
    (16 / ((1 - U) ^ 2 * graphonClosedBandMass W L U))
  apply squeeze_zero'
  · filter_upwards [] with n
    exact wRandomJointEventProbability_nonneg W _
  · filter_upwards [eventually_gt_atTop 0] with n hn
    calc
      wRandomJointEventProbability W
          (absentFlexibleDeficitJointEvent n W L U) ≤
          wRandomLatentEventProbability (flexiblePairAbundantSet n W L U)ᶜ +
            wRandomJointEventProbability W
              (absentFlexibleDeficitOnAbundanceJointEvent n W L U) :=
        wRandomJointEventProbability_absentDeficit_le_nonabundance_add W L U
      _ ≤ wRandomLatentEventProbability (flexiblePairAbundantSet n W L U)ᶜ +
          (16 / ((1 - U) ^ 2 * graphonClosedBandMass W L U)) /
            (n : ℝ) ^ 2 :=
        add_le_add_right
          (wRandomJointEventProbability_absentDeficitOnAbundance_le
            hn W L U hU hMass) _
  · simpa using hLow.add hRate

/-- Failure of the joint repair-capacity event: either flexible pairs are not
abundant, or too few of them are present, or too few are absent. -/
def flexibleRepairCapacityFailureJointEvent (n : ℕ) (W : Graphon)
    (L U : ℝ) : WRandomJointEvent n :=
  (flexiblePairNonabundanceJointEvent n W L U).union
    ((presentFlexibleDeficitJointEvent n W L U).union
      (absentFlexibleDeficitJointEvent n W L U))

/-- The full joint repair-capacity failure probability tends to zero. -/
theorem flexibleRepairCapacityFailure_probability_tendsto_zero
    (W : Graphon) (L U : ℝ) (hL : 0 < L) (hU : U < 1)
    (hMass : 0 < graphonClosedBandMass W L U) :
    Tendsto
      (fun n ↦ wRandomJointEventProbability W
        (flexibleRepairCapacityFailureJointEvent n W L U))
      atTop (nhds 0) := by
  have hLowJoint : Tendsto
      (fun n ↦ wRandomJointEventProbability W
        (flexiblePairNonabundanceJointEvent n W L U))
      atTop (nhds 0) := by
    have hLow := flexiblePairNonabundance_probability_tendsto_zero W L U hMass
    apply hLow.congr'
    filter_upwards [] with n
    exact (wRandomJointEventProbability_ofLatentSet W _ _).symm
  have hPresent := presentFlexibleDeficit_probability_tendsto_zero
    W L U hL hMass
  have hAbsent := absentFlexibleDeficit_probability_tendsto_zero
    W L U hU hMass
  apply squeeze_zero
  · intro n
    exact wRandomJointEventProbability_nonneg W _
  · intro n
    calc
      wRandomJointEventProbability W
          (flexibleRepairCapacityFailureJointEvent n W L U) ≤
          wRandomJointEventProbability W
              (flexiblePairNonabundanceJointEvent n W L U) +
            wRandomJointEventProbability W
              ((presentFlexibleDeficitJointEvent n W L U).union
                (absentFlexibleDeficitJointEvent n W L U)) :=
        wRandomJointEventProbability_union_le W _ _
      _ ≤ wRandomJointEventProbability W
              (flexiblePairNonabundanceJointEvent n W L U) +
            (wRandomJointEventProbability W
                (presentFlexibleDeficitJointEvent n W L U) +
              wRandomJointEventProbability W
                (absentFlexibleDeficitJointEvent n W L U)) :=
        add_le_add_right (wRandomJointEventProbability_union_le W _ _) _
  · simpa using hLowJoint.add (hPresent.add hAbsent)

/-- Complementary good event: abundant flexible pairs and enough of them in
both sampled states to repair a small edge-count discrepancy in either
direction. -/
def flexibleRepairCapacityGoodJointEvent (n : ℕ) (W : Graphon)
    (L U : ℝ) : WRandomJointEvent n where
  Holds x G := ¬(flexibleRepairCapacityFailureJointEvent n W L U).Holds x G
  measurableSet_holds G :=
    ((flexibleRepairCapacityFailureJointEvent n W L U).measurableSet_holds G).compl

theorem flexibleRepairCapacityGoodJointEvent_holds_iff {n : ℕ}
    (W : Graphon) (L U : ℝ) (x : Fin n → UnitInterval)
    (G : SimpleGraph (Fin n)) :
    (flexibleRepairCapacityGoodJointEvent n W L U).Holds x G ↔
      x ∈ flexiblePairAbundantSet n W L U ∧
      L / 2 * (flexiblePairCount W L U x : ℝ) ≤
        ((presentFlexibleEdgeFinset W x L U G).card : ℝ) ∧
      (1 - U) / 2 * (flexiblePairCount W L U x : ℝ) ≤
        ((absentFlexibleEdgeFinset W x L U G).card : ℝ) := by
  simp only [flexibleRepairCapacityGoodJointEvent,
    flexibleRepairCapacityFailureJointEvent,
    flexiblePairNonabundanceJointEvent,
    presentFlexibleDeficitJointEvent, absentFlexibleDeficitJointEvent,
    presentFlexibleDeficitOnAbundanceJointEvent,
    WRandomJointEvent.union,
    WRandomJointEvent.ofLatentSet, not_or, not_not, not_lt]
  simp

theorem wRandomJointEventProbability_flexibleRepairCapacityGood {n : ℕ}
    (W : Graphon) (L U : ℝ) :
    wRandomJointEventProbability W
        (flexibleRepairCapacityGoodJointEvent n W L U) =
      1 - wRandomJointEventProbability W
        (flexibleRepairCapacityFailureJointEvent n W L U) := by
  have hPoint : ∀ x : Fin n → UnitInterval,
      wRandomJointEventIntegrand W
          (flexibleRepairCapacityGoodJointEvent n W L U) x =
        1 - wRandomJointEventIntegrand W
          (flexibleRepairCapacityFailureJointEvent n W L U) x := by
    intro x
    classical
    rw [← sum_wRandomConditionalWeight W x]
    unfold wRandomJointEventIntegrand flexibleRepairCapacityGoodJointEvent
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro G _hG
    by_cases hFail :
        (flexibleRepairCapacityFailureJointEvent n W L U).Holds x G
    · simp [hFail]
    · simp [hFail]
  unfold wRandomJointEventProbability
  rw [integral_congr_ae (ae_of_all _ hPoint)]
  rw [integral_sub (integrable_const 1)
    (integrable_wRandomJointEventIntegrand W
      (flexibleRepairCapacityFailureJointEvent n W L U))]
  simp

/-- The full joint repair-capacity good event has probability tending to
one. -/
theorem flexibleRepairCapacityGood_probability_tendsto_one
    (W : Graphon) (L U : ℝ) (hL : 0 < L) (hU : U < 1)
    (hMass : 0 < graphonClosedBandMass W L U) :
    Tendsto
      (fun n ↦ wRandomJointEventProbability W
        (flexibleRepairCapacityGoodJointEvent n W L U))
      atTop (nhds 1) := by
  have hFailure := flexibleRepairCapacityFailure_probability_tendsto_zero
    W L U hL hU hMass
  have hSub : Tendsto
      (fun n ↦ (1 : ℝ) - wRandomJointEventProbability W
        (flexibleRepairCapacityFailureJointEvent n W L U))
      atTop (nhds 1) := by
    have hConst : Tendsto (fun _n : ℕ ↦ (1 : ℝ)) atTop (nhds 1) :=
      tendsto_const_nhds
    simpa using hConst.sub hFailure
  apply hSub.congr'
  filter_upwards [] with n
  exact (wRandomJointEventProbability_flexibleRepairCapacityGood W L U).symm

end InducedStars
