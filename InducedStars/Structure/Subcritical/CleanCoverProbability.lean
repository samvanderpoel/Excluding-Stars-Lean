import InducedStars.Structure.Subcritical.CleanCoverUnionBound
import InducedStars.Structure.Supercritical.ProfileProbability
import DenseGraph.FiniteModels.FixedCardinalityContainment

/-!
# Actual fixed-cell clique-cover uniqueness

Each cell is sampled independently at its own prescribed cardinality. The
second-cover event forces actual selected coordinates, and their cardinalities
sum to the already established ambient forced-edge count.
-/

noncomputable section
open Finset Set
open scoped BigOperators Classical
namespace InducedStars

variable {k : ℕ} {V : Type*} [Fintype V] [DecidableEq V]

def fixedProfileCleanGraph (D : SupercriticalDivision k V)
    (p : SupercriticalEdgeProfile D) (S : (supercriticalFixedProfileBlockModel D p).Sample) :
    SimpleGraph V :=
  supercriticalGraphFromCrossOutcome D ⊥ p
    ((supercriticalFixedProfileBlockModel D p).sampleOutcome S)

theorem fixedProfileCleanGraph_isClique (D : SupercriticalDivision k V)
    (p : SupercriticalEdgeProfile D) (S : (supercriticalFixedProfileBlockModel D p).Sample)
    (i : Fin (k - 1)) : (fixedProfileCleanGraph D p S).IsClique (D.parts i : Set V) := by
  intro x hx y hy hxy
  have hnot : ¬D.IsCrossPair x y := by
    rintro ⟨e, h | h⟩
    · exact e.left_ne_right ((D.mem_part_unique h.1 hx).trans (D.mem_part_unique hy h.2))
    · exact e.left_ne_right ((D.mem_part_unique h.1 hy).trans (D.mem_part_unique hx h.2))
  apply (supercriticalGraphFromCrossOutcome_adj_of_not_cross D ⊥ p _ hnot).mpr
  simp only [supercriticalGraphFromDefectPattern_adj, SimpleGraph.bot_adj, not_false_eq_true,
    and_true, and_false, or_false]
  exact ⟨hxy, i, hx, hy⟩

def forcedCoverBlock (D E : SupercriticalDivision k V) (e : SupercriticalPartPair k) :
    Finset (V × V) :=
  (D.parts e.left ×ˢ D.parts e.right).filter fun xy ↦
    s(xy.1, xy.2) ∈ forcedCrossEdgesBySecondCover D E

theorem sum_card_forcedCoverBlock (D E : SupercriticalDivision k V) :
    (∑ e, (forcedCoverBlock D E e).card) = (forcedCrossEdgesBySecondCover D E).card := by
  have h : Finset.univ.sigma (forcedCoverBlock D E) = forcedCrossChoicesBySecondCover D E := by
    ext z
    simp only [Finset.mem_sigma, Finset.mem_univ, forcedCoverBlock, Finset.mem_filter,
      Finset.mem_product, true_and, mem_forcedCrossChoicesBySecondCover,
      mem_supercriticalTaggedCrossChoiceUniverse, supercriticalTaggedCrossEdge]
  rw [← card_forcedCrossChoicesBySecondCover D E, ← h, Finset.card_sigma]

def fixedProfileSecondCoverEvent (D E : SupercriticalDivision k V)
    (p : SupercriticalEdgeProfile D) :
    Finset (supercriticalFixedProfileBlockModel D p).Sample :=
  Finset.univ.filter fun S ↦ ∀ i, (fixedProfileCleanGraph D p S).IsClique (E.parts i : Set V)

theorem fixedProfileSecondCoverEvent_subset_containment
    (D E : SupercriticalDivision k V) (p : SupercriticalEdgeProfile D) :
    fixedProfileSecondCoverEvent D E p ⊆
      (supercriticalFixedProfileBlockModel D p).blockContainmentEvent (forcedCoverBlock D E) := by
  intro S hS
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  intro e xy hxy
  obtain ⟨hp, hf⟩ := Finset.mem_filter.mp hxy
  have hp' := Finset.mem_product.mp hp
  have hforce := Finset.mem_inter.mp hf |>.2
  obtain ⟨hne, i, hx, hy⟩ := (mk_mem_supercriticalInternalEdgeFinset E xy.1 xy.2).mp hforce
  have hadj := (Finset.mem_filter.mp hS).2 i hx hy hne
  have hcross : D.IsCrossPair xy.1 xy.2 := ⟨e, Or.inl hp'⟩
  have hselected := (supercriticalGraphFromCrossOutcome_adj_of_cross D ⊥ p _ hcross).mp hadj
  let z : (supercriticalFixedProfileBlockModel D p).Coordinate := ⟨e, ⟨xy, hp⟩⟩
  have hz : z ∈ (supercriticalFixedProfileBlockModel D p).sampleOutcome S := by
    exact (mem_supercriticalProfileAmbientOutcome D p _ z).mp hselected
  have hz' := (supercriticalFixedProfileBlockModel D p).mem_sampleOutcome S z |>.mp hz
  exact Finset.mem_map.mpr ⟨z.2, hz', rfl⟩

/-- Fixed quotas on different part pairs are not pooled. The upper density
bound alone supplies the full forced-edge exponential cost. -/
theorem fixedProfileSecondCover_probability_le
    (D E : SupercriticalDivision k V) (p : SupercriticalEdgeProfile D)
    {c : ℝ} (hdensity : ∀ e, profileDensity p e ≤ Real.exp (-c)) :
    (supercriticalFixedProfileBlockModel D p).eventProbability
      (fixedProfileSecondCoverEvent D E p) ≤
        Real.exp (-(c * (forcedCrossEdgesBySecondCover D E).card)) := by
  have hmain := (supercriticalFixedProfileBlockModel D p).eventProbability_blockContainment_le_exp
    (c := c) (forcedCoverBlock D E) (fun _ ↦ Finset.filter_subset _ _)
    (fun e ↦ by rw [card_supercriticalFixedProfileBlockModel_block]; exact crossEdgeCapacity_pos D e)
    (by
      intro e
      rw [card_supercriticalFixedProfileBlockModel_block,
        supercriticalFixedProfileBlockModel_quota]
      exact hdensity e)
  rw [sum_card_forcedCoverBlock] at hmain
  exact ((supercriticalFixedProfileBlockModel D p).eventProbability_mono
    (fixedProfileSecondCoverEvent_subset_containment D E p)).trans hmain

def fixedProfileNonuniqueCoverEvent {n : ℕ} (D : SupercriticalDivision k (Fin n))
    (p : SupercriticalEdgeProfile D) :
    Finset (supercriticalFixedProfileBlockModel D p).Sample :=
  Finset.univ.filter fun S ↦ ¬ HasUniqueCoMultipartiteCover k (fixedProfileCleanGraph D p S)

theorem fixedProfileNonuniqueCoverEvent_subset_biUnion {n : ℕ}
    (D : SupercriticalDivision k (Fin n)) (p : SupercriticalEdgeProfile D) (hD : D.IsFull) :
    fixedProfileNonuniqueCoverEvent D p ⊆
      (competingFullSupercriticalDivisions D).biUnion fun E ↦ fixedProfileSecondCoverEvent D E p := by
  intro S hS
  have hnot := (Finset.mem_filter.mp hS).2
  by_contra h
  apply hnot
  refine ⟨D, hD, fixedProfileCleanGraph_isClique D p S, ?_⟩
  intro E hE hclique
  by_contra hne
  apply h
  exact Finset.mem_biUnion.mpr ⟨E, mem_competingFullSupercriticalDivisions.mpr ⟨hE, hne⟩,
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hclique⟩⟩

theorem fixedProfileNonuniqueCover_probability_le_sum {n : ℕ}
    (D : SupercriticalDivision k (Fin n)) (p : SupercriticalEdgeProfile D) (hD : D.IsFull) :
    (supercriticalFixedProfileBlockModel D p).eventProbability (fixedProfileNonuniqueCoverEvent D p) ≤
      ∑ E ∈ competingFullSupercriticalDivisions D,
        (supercriticalFixedProfileBlockModel D p).eventProbability (fixedProfileSecondCoverEvent D E p) := by
  let M := supercriticalFixedProfileBlockModel D p
  change M.eventProbability _ ≤ ∑ E ∈ competingFullSupercriticalDivisions D,
    M.eventProbability _
  simp only [M.eventProbability_eq_card_div, ← Finset.sum_div]
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast ((Finset.card_le_card (fixedProfileNonuniqueCoverEvent_subset_biUnion D p hD)).trans
    Finset.card_biUnion_le)

/-- Quantitative uniqueness for actual independent per-cell fixed counts. -/
theorem fixedProfileNonuniqueCover_probability_le_near_far
    {n a : ℕ} (hk : 3 ≤ k) (D : SupercriticalDivision k (Fin n))
    (p : SupercriticalEdgeProfile D) (hD : D.IsFull)
    (hpart : ∀ i, a ≤ (D.parts i).card) (hscale : n ≤ 2 * (k - 1) * a)
    {c : ℝ} (hc : 0 ≤ c) (hdensity : ∀ e, profileDensity p e ≤ Real.exp (-c)) :
    (supercriticalFixedProfileBlockModel D p).eventProbability (fixedProfileNonuniqueCoverEvent D p) ≤
      (∑ t ∈ Finset.Icc 1 n,
        (((k - 1).factorial * n.choose t * (k - 1)^t : ℕ) : ℝ) *
          Real.exp (-(c / (4 * (k - 1 : ℕ)) * t * n))) +
      (k : ℝ)^n * Real.exp (-(c / (16 * (k - 1 : ℕ)^8) * (n:ℝ)^2)) := by
  apply (fixedProfileNonuniqueCover_probability_le_sum D p hD).trans
  have h := sum_competingCoverWeights_le_near_far hk D hD hpart hscale hc zero_le_one
    (fun E ↦ (supercriticalFixedProfileBlockModel D p).eventProbability
      (fixedProfileSecondCoverEvent D E p))
    (fun E _ ↦ by simpa only [one_mul] using fixedProfileSecondCover_probability_le D E p hdensity)
  simpa only [one_mul] using h

end InducedStars
