import InducedStars.FiniteModels.GraphFamiliesCore
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Sym.Card
import Mathlib.Tactic

/-!
# The general labeled binomial random-graph law

This file gives the exact finite `G(n,p)` model on labeled simple graphs with
vertex set `Fin n`.  Every unordered non-loop pair is sampled once.  In
particular, no graph-isomorphism quotient, automorphism factor, vertex
factorial, or ordered-edge factor occurs in any definition below.
-/

noncomputable section

open Finset Set
open scoped BigOperators

namespace InducedStars

attribute [local instance] Classical.propDecidable

/-- Use the same internal finite edge-set choice as `GraphFamilies`, so the
public edge-count APIs elaborate with a single canonical local instance. -/
noncomputable local instance gnpEdgeSetFintype {n : ℕ}
    (G : SimpleGraph (Fin n)) : Fintype G.edgeSet :=
  graphFamiliesEdgeSetFintype G

/-! ## Boolean edge patterns -/

/-- An unordered non-loop pair of vertices of `Fin n`. -/
private abbrev GnpPossibleEdge (n : ℕ) :=
  {e : Sym2 (Fin n) // ¬e.IsDiag}

/-- The edge-membership pattern of a labeled graph. -/
private def gnpEdgeIndicator {n : ℕ} (G : SimpleGraph (Fin n)) :
    GnpPossibleEdge n → Prop :=
  fun e ↦ e.1 ∈ G.edgeSet

/-- Construct a labeled graph from a choice on every possible unordered
edge. -/
private noncomputable def gnpGraphFromEdgeIndicator {n : ℕ}
    (q : GnpPossibleEdge n → Prop) : SimpleGraph (Fin n) :=
  SimpleGraph.fromEdgeSet {e | ∃ h : ¬e.IsDiag, q ⟨e, h⟩}

/-- Labeled graphs are exactly Boolean patterns on unordered non-loop
pairs. -/
private noncomputable def gnpEdgeIndicatorEquiv (n : ℕ) :
    SimpleGraph (Fin n) ≃ (GnpPossibleEdge n → Prop) where
  toFun := gnpEdgeIndicator
  invFun := gnpGraphFromEdgeIndicator
  left_inv G := by
    apply (SimpleGraph.edgeSet_inj).mp
    ext e
    constructor
    · intro he
      have hnonDiag :=
        (gnpGraphFromEdgeIndicator (gnpEdgeIndicator G)).not_isDiag_of_mem_edgeSet he
      simpa [gnpGraphFromEdgeIndicator, gnpEdgeIndicator, hnonDiag] using he
    · intro he
      have hnonDiag := G.not_isDiag_of_mem_edgeSet he
      simp [gnpGraphFromEdgeIndicator, gnpEdgeIndicator, he, hnonDiag]
  right_inv q := by
    funext e
    apply propext
    simp [gnpGraphFromEdgeIndicator, gnpEdgeIndicator, e.2]

private def gnpPresentPossibleEdgeEquiv {n : ℕ}
    (G : SimpleGraph (Fin n)) :
    {e : GnpPossibleEdge n // gnpEdgeIndicator G e} ≃ G.edgeSet where
  toFun e := ⟨e.1.1, e.2⟩
  invFun e := ⟨⟨e.1, G.not_isDiag_of_mem_edgeSet e.2⟩, e.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

private theorem card_gnpPossibleEdge (n : ℕ) :
    Fintype.card (GnpPossibleEdge n) = completeEdgeCount n := by
  change Fintype.card {e : Sym2 (Fin n) // ¬e.IsDiag} = Nat.choose n 2
  convert (@Sym2.card_subtype_not_diag (Fin n) _ _) using 1 <;> simp

private theorem card_filter_gnpEdgeIndicator {n : ℕ}
    (G : SimpleGraph (Fin n)) :
    ((Finset.univ : Finset (GnpPossibleEdge n)).filter
      (gnpEdgeIndicator G)).card = G.edgeFinset.card := by
  classical
  calc
    ((Finset.univ : Finset (GnpPossibleEdge n)).filter
        (gnpEdgeIndicator G)).card =
        Fintype.card {e : GnpPossibleEdge n // gnpEdgeIndicator G e} :=
      (Fintype.card_subtype (gnpEdgeIndicator G)).symm
    _ = Fintype.card G.edgeSet :=
      Fintype.card_congr (gnpPresentPossibleEdgeEquiv G)
    _ = G.edgeFinset.card := SimpleGraph.card_edgeSet

private theorem card_filter_not_gnpEdgeIndicator {n : ℕ}
    (G : SimpleGraph (Fin n)) :
    ((Finset.univ : Finset (GnpPossibleEdge n)).filter
      (fun e ↦ ¬gnpEdgeIndicator G e)).card =
        completeEdgeCount n - G.edgeFinset.card := by
  classical
  have hpartition := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (GnpPossibleEdge n)))
    (gnpEdgeIndicator G)
  rw [card_filter_gnpEdgeIndicator G, Finset.card_univ,
    card_gnpPossibleEdge] at hpartition
  omega

private noncomputable def gnpPatternWeight {n : ℕ} (p : ℝ)
    (q : GnpPossibleEdge n → Prop) : ℝ := by
  classical
  exact ∏ e : GnpPossibleEdge n, if q e then p else 1 - p

/-! ## Exact graph weights and normalization -/

/-- The exact labeled `G(n,p)` mass of `G`.  Its edge exponent counts each
unordered edge once. -/
noncomputable def gnpGraphWeight {n : ℕ}
    (p : ℝ) (G : SimpleGraph (Fin n)) : ℝ := by
  classical
  exact p ^ G.edgeFinset.card *
    (1 - p) ^ (completeEdgeCount n - G.edgeFinset.card)

private theorem gnpGraphWeight_eq_patternWeight {n : ℕ}
    (p : ℝ) (G : SimpleGraph (Fin n)) :
    gnpGraphWeight p G = gnpPatternWeight p (gnpEdgeIndicator G) := by
  classical
  unfold gnpGraphWeight gnpPatternWeight
  rw [Finset.prod_ite]
  simp only [Finset.prod_const]
  rw [card_filter_gnpEdgeIndicator,
    card_filter_not_gnpEdgeIndicator]

/-- Every graph weight is nonnegative when `p ∈ [0,1]`. -/
theorem gnpGraphWeight_nonneg {n : ℕ} {p : ℝ}
    (hp : p ∈ Set.Icc (0 : ℝ) 1) (G : SimpleGraph (Fin n)) :
    0 ≤ gnpGraphWeight p G := by
  unfold gnpGraphWeight
  exact mul_nonneg (pow_nonneg hp.1 _) (pow_nonneg (sub_nonneg.mpr hp.2) _)

/-- Every labeled graph has strictly positive mass when `p ∈ (0,1)`. -/
theorem gnpGraphWeight_pos {n : ℕ} {p : ℝ}
    (hp : p ∈ Set.Ioo (0 : ℝ) 1) (G : SimpleGraph (Fin n)) :
    0 < gnpGraphWeight p G := by
  unfold gnpGraphWeight
  exact mul_pos (pow_pos hp.1 _) (pow_pos (sub_pos.mpr hp.2) _)

/-- At fixed `n` and `p`, graph weight depends only on the unordered edge
count. -/
theorem gnpGraphWeight_eq_of_edgeCount_eq {n : ℕ} {p : ℝ}
    {G K : SimpleGraph (Fin n)}
    (hcount : G.edgeFinset.card = K.edgeFinset.card) :
    gnpGraphWeight p G = gnpGraphWeight p K := by
  unfold gnpGraphWeight
  rw [hcount]

/-- Exact normalization of the labeled `G(n,p)` law.  Algebraically this
identity holds for every real `p`; probability inequalities below impose
`p ∈ [0,1]`. -/
theorem gnpGraphWeight_sum_univ (n : ℕ) (p : ℝ) :
    ∑ G : SimpleGraph (Fin n), gnpGraphWeight p G = 1 := by
  classical
  calc
    (∑ G : SimpleGraph (Fin n), gnpGraphWeight p G) =
        ∑ q : GnpPossibleEdge n → Prop, gnpPatternWeight p q := by
      apply Fintype.sum_equiv (gnpEdgeIndicatorEquiv n)
      intro G
      exact gnpGraphWeight_eq_patternWeight p G
    _ = ∏ e : GnpPossibleEdge n,
          ∑ b : Prop, if b then p else 1 - p := by
      simp only [gnpPatternWeight]
      rw [Fintype.prod_sum]
    _ = 1 := by simp

/-! ## Finite graph events -/

/-- Probability of a finite labeled graph event under `G(n,p)`. -/
noncomputable def gnpGraphEventProbability {n : ℕ}
    (p : ℝ) (Q : Finset (SimpleGraph (Fin n))) : ℝ :=
  ∑ G ∈ Q, gnpGraphWeight p G

/-- A finite `G(n,p)` event has nonnegative probability. -/
theorem gnpGraphEventProbability_nonneg {n : ℕ} {p : ℝ}
    (hp : p ∈ Set.Icc (0 : ℝ) 1)
    (Q : Finset (SimpleGraph (Fin n))) :
    0 ≤ gnpGraphEventProbability p Q := by
  unfold gnpGraphEventProbability
  exact Finset.sum_nonneg fun G _ ↦ gnpGraphWeight_nonneg hp G

/-- Event probability is monotone under inclusion. -/
theorem gnpGraphEventProbability_mono {n : ℕ} {p : ℝ}
    (hp : p ∈ Set.Icc (0 : ℝ) 1)
    {Q R : Finset (SimpleGraph (Fin n))} (hQR : Q ⊆ R) :
    gnpGraphEventProbability p Q ≤ gnpGraphEventProbability p R := by
  unfold gnpGraphEventProbability
  exact Finset.sum_le_sum_of_subset_of_nonneg hQR
    (fun G _ _ ↦ gnpGraphWeight_nonneg hp G)

/-- Every finite `G(n,p)` event has probability at most one. -/
theorem gnpGraphEventProbability_le_one {n : ℕ} {p : ℝ}
    (hp : p ∈ Set.Icc (0 : ℝ) 1)
    (Q : Finset (SimpleGraph (Fin n))) :
    gnpGraphEventProbability p Q ≤ 1 := by
  rw [← gnpGraphWeight_sum_univ n p]
  exact gnpGraphEventProbability_mono hp (Finset.subset_univ Q)

theorem gnpGraphEventProbability_mem_Icc {n : ℕ} {p : ℝ}
    (hp : p ∈ Set.Icc (0 : ℝ) 1)
    (Q : Finset (SimpleGraph (Fin n))) :
    gnpGraphEventProbability p Q ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨gnpGraphEventProbability_nonneg hp Q,
    gnpGraphEventProbability_le_one hp Q⟩

@[simp] theorem gnpGraphEventProbability_univ (n : ℕ) (p : ℝ) :
    gnpGraphEventProbability p
      (Finset.univ : Finset (SimpleGraph (Fin n))) = 1 := by
  simpa only [gnpGraphEventProbability] using gnpGraphWeight_sum_univ n p

@[simp] theorem gnpGraphEventProbability_singleton {n : ℕ}
    (p : ℝ) (G : SimpleGraph (Fin n)) :
    gnpGraphEventProbability p {G} = gnpGraphWeight p G := by
  simp [gnpGraphEventProbability]

/-- Additivity on disjoint finite graph events. -/
theorem gnpGraphEventProbability_union {n : ℕ} (p : ℝ)
    {Q R : Finset (SimpleGraph (Fin n))} (hQR : Disjoint Q R) :
    gnpGraphEventProbability p (Q ∪ R) =
      gnpGraphEventProbability p Q + gnpGraphEventProbability p R := by
  unfold gnpGraphEventProbability
  exact Finset.sum_union hQR

/-! ## Induced-free events -/

/-- Probability that a labeled `G(n,p)` graph is induced-`H`-free. -/
noncomputable def gnpInducedFreeProbability {h : ℕ}
    (H : SimpleGraph (Fin h)) (n : ℕ) (p : ℝ) : ℝ :=
  gnpGraphEventProbability p (inducedFreeGraphFinset H n)

theorem gnpInducedFreeProbability_nonneg {h n : ℕ}
    (H : SimpleGraph (Fin h)) {p : ℝ}
    (hp : p ∈ Set.Icc (0 : ℝ) 1) :
    0 ≤ gnpInducedFreeProbability H n p :=
  gnpGraphEventProbability_nonneg hp _

theorem gnpInducedFreeProbability_le_one {h n : ℕ}
    (H : SimpleGraph (Fin h)) {p : ℝ}
    (hp : p ∈ Set.Icc (0 : ℝ) 1) :
    gnpInducedFreeProbability H n p ≤ 1 :=
  gnpGraphEventProbability_le_one hp _

/-- A nonempty exact-edge induced-free slice makes the full induced-free
event strictly positive whenever all graph weights are positive. -/
theorem gnpInducedFreeProbability_pos_of_exactEdge_nonempty
    {h n m : ℕ} (H : SimpleGraph (Fin h)) {p : ℝ}
    (hp : p ∈ Set.Ioo (0 : ℝ) 1)
    (hne : (inducedFreeGraphFinsetWithEdges H n m).Nonempty) :
    0 < gnpInducedFreeProbability H n p := by
  obtain ⟨G, hG⟩ := hne
  have hGfree : G ∈ inducedFreeGraphFinset H n :=
    mem_inducedFreeGraphFinset.mpr
      (mem_inducedFreeGraphFinsetWithEdges.mp hG).1
  have hsingle : ({G} : Finset (SimpleGraph (Fin n))) ⊆
      inducedFreeGraphFinset H n := by
    simpa only [Finset.singleton_subset_iff] using hGfree
  have hmono := gnpGraphEventProbability_mono
    ⟨hp.1.le, hp.2.le⟩ hsingle
  rw [gnpGraphEventProbability_singleton] at hmono
  exact (gnpGraphWeight_pos hp G).trans_le hmono

/-- Eventual nonemptiness of exact-edge slices supplies the positivity needed
before taking logarithms of general induced-free probabilities. -/
theorem eventually_gnpInducedFreeProbability_pos_of_exactEdge_nonempty
    {h : ℕ} (H : SimpleGraph (Fin h)) (m : ℕ → ℕ) {p : ℝ}
    (hp : p ∈ Set.Ioo (0 : ℝ) 1)
    (hne : ∀ᶠ n in Filter.atTop,
      (inducedFreeGraphFinsetWithEdges H n (m n)).Nonempty) :
    ∀ᶠ n in Filter.atTop, 0 < gnpInducedFreeProbability H n p := by
  filter_upwards [hne] with n hn
  exact gnpInducedFreeProbability_pos_of_exactEdge_nonempty H hp hn

/-! ## Normalized logarithmic probabilities -/

noncomputable def normalizedLogGnpInducedFreeProbability {h : ℕ}
    (H : SimpleGraph (Fin h)) (n : ℕ) (p : ℝ) : ℝ :=
  normalizedLogProbability n (gnpInducedFreeProbability H n p)

/-! ## Exact decomposition by unordered edge count -/

/-- Total `G(n,p)` weight of the induced-`H`-free graphs with exactly `m`
unordered edges.  When `m` exceeds the complete edge count, the graph count
is zero, so this expression has the harmless value zero. -/
noncomputable def gnpInducedFreeSliceWeight {h : ℕ}
    (H : SimpleGraph (Fin h)) (n m : ℕ) (p : ℝ) : ℝ :=
  (inducedFreeGraphCountWithEdges H n m : ℝ) *
    p ^ m * (1 - p) ^ (completeEdgeCount n - m)

private theorem gnpInducedFreeSliceWeight_eq_sum_filter {h n m : ℕ}
    (H : SimpleGraph (Fin h)) (p : ℝ) :
    gnpInducedFreeSliceWeight H n m p =
      ∑ G ∈ inducedFreeGraphFinsetWithEdges H n m,
        gnpGraphWeight p G := by
  classical
  unfold gnpInducedFreeSliceWeight inducedFreeGraphCountWithEdges
  rw [show (∑ G ∈ inducedFreeGraphFinsetWithEdges H n m,
      gnpGraphWeight p G) =
      ∑ _G ∈ inducedFreeGraphFinsetWithEdges H n m,
          p ^ m * (1 - p) ^ (completeEdgeCount n - m) by
    apply Finset.sum_congr rfl
    intro G hG
    have hcount : G.edgeFinset.card = m :=
      (mem_inducedFreeGraphFinsetWithEdges.mp hG).2
    unfold gnpGraphWeight
    rw [hcount]]
  simp [mul_assoc]

/-- The exact-edge induced-free event has the advertised common-weight
formula. -/
theorem gnpGraphEventProbability_inducedFreeGraphFinsetWithEdges
    {h : ℕ} (H : SimpleGraph (Fin h)) (n m : ℕ) (p : ℝ) :
    gnpGraphEventProbability p
        (inducedFreeGraphFinsetWithEdges H n m) =
      gnpInducedFreeSliceWeight H n m p := by
  unfold gnpGraphEventProbability
  exact (gnpInducedFreeSliceWeight_eq_sum_filter H p).symm

/-- An edge-count slice above the complete graph's edge count is empty and
therefore has weight zero. -/
theorem gnpInducedFreeSliceWeight_eq_zero_of_completeEdgeCount_lt
    {h : ℕ} (H : SimpleGraph (Fin h)) {n m : ℕ} (p : ℝ)
    (hm : completeEdgeCount n < m) :
    gnpInducedFreeSliceWeight H n m p = 0 := by
  have hempty : inducedFreeGraphFinsetWithEdges H n m = ∅ := by
    apply Finset.not_nonempty_iff_eq_empty.mp
    rintro ⟨G, hG⟩
    have hcount := (mem_inducedFreeGraphFinsetWithEdges.mp hG).2
    have hle := card_edgeFinset_le_completeEdgeCount G
    omega
  rw [← gnpGraphEventProbability_inducedFreeGraphFinsetWithEdges,
    hempty]
  simp [gnpGraphEventProbability]

/-- Exact partition of the induced-free probability into its unordered
edge-count slices.  Every labeled graph occurs in exactly one fiber. -/
theorem gnpInducedFreeProbability_eq_sum_edgeCounts {h : ℕ}
    (H : SimpleGraph (Fin h)) (n : ℕ) (p : ℝ) :
    gnpInducedFreeProbability H n p =
      ∑ m ∈ Finset.range (completeEdgeCount n + 1),
        gnpInducedFreeSliceWeight H n m p := by
  classical
  unfold gnpInducedFreeProbability gnpGraphEventProbability
  rw [show (∑ G ∈ inducedFreeGraphFinset H n, gnpGraphWeight p G) =
      ∑ m ∈ Finset.range (completeEdgeCount n + 1),
        ∑ G ∈ inducedFreeGraphFinsetWithEdges H n m,
          gnpGraphWeight p G by
    symm
    simp only [inducedFreeGraphFinsetWithEdges]
    apply Finset.sum_fiberwise_of_maps_to
    intro G hG
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le
      (card_edgeFinset_le_completeEdgeCount G))]
  apply Finset.sum_congr rfl
  intro m _hm
  exact (gnpInducedFreeSliceWeight_eq_sum_filter H p).symm

end InducedStars

