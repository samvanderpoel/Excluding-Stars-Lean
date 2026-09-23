import DenseGraph.FiniteModels.FixedCardinalityBlocks
import DenseGraph.FiniteModels.CoverUniqueness

/-!
# Forced-coordinate bounds in independent fixed-size blocks

The proof counts actual fixed-size samples in every block. The quotas need
not coincide, and their densities need only share an upper bound.
-/

noncomputable section
open Finset
open scoped BigOperators
namespace DenseGraph
namespace FixedCardinalityBlockModel

variable {I Ω : Type*} [Fintype I] [DecidableEq I]
  [Fintype Ω] [DecidableEq Ω]

theorem selectedInBlock_injective (M : FixedCardinalityBlockModel I Ω) :
    Function.Injective (fun S : M.Sample ↦ M.selectedInBlock S) := by
  intro S T h
  funext i
  apply Subtype.ext
  apply Finset.map_injective ⟨Subtype.val, Subtype.val_injective⟩
  exact congrFun h i

/-- Simultaneous containment of a prescribed finite set in each independent
coordinate block. -/
def blockContainmentEvent (M : FixedCardinalityBlockModel I Ω) (F : I → Finset Ω) :
    Finset M.Sample := by
  classical
  exact Finset.univ.filter fun S ↦ ∀ i, F i ⊆ M.selectedInBlock S i

theorem card_blockContainmentEvent_le (M : FixedCardinalityBlockModel I Ω)
    (F : I → Finset Ω) :
    (M.blockContainmentEvent F).card ≤
      ∏ i, (fixedCardinalityContainingFinset (M.block i) (F i) (M.quota i)).card := by
  classical
  calc
    (M.blockContainmentEvent F).card =
        ((M.blockContainmentEvent F).image M.selectedInBlock).card :=
      (Finset.card_image_of_injective _ M.selectedInBlock_injective).symm
    _ ≤ (Fintype.piFinset fun i ↦
        fixedCardinalityContainingFinset (M.block i) (F i) (M.quota i)).card := by
      apply Finset.card_le_card
      rintro T hT
      obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hT
      rw [Fintype.mem_piFinset]
      intro i
      exact mem_fixedCardinalityContainingFinset.mpr
        ⟨M.selectedInBlock_subset S i, M.card_selectedInBlock S i,
          (Finset.mem_filter.mp hS).2 i⟩
    _ = _ := Fintype.card_piFinset _

/-- Product upper bound, obtained by the elementary exact hypergeometric
containment inequality separately in every actual coordinate block. -/
theorem eventProbability_blockContainment_le_prod
    (M : FixedCardinalityBlockModel I Ω) (F : I → Finset Ω)
    (hF : ∀ i, F i ⊆ M.block i) (hpos : ∀ i, 0 < (M.block i).card) :
    M.eventProbability (M.blockContainmentEvent F) ≤
      ∏ i, ((M.quota i : ℝ) / (M.block i).card) ^ (F i).card := by
  classical
  rw [M.eventProbability_eq_card_div]
  apply (div_le_iff₀ (by exact_mod_cast M.sampleSpaceCard_pos)).mpr
  calc
    ((M.blockContainmentEvent F).card : ℝ) ≤
        ∏ i, ((fixedCardinalityContainingFinset (M.block i) (F i)
          (M.quota i)).card : ℝ) := by
      exact_mod_cast M.card_blockContainmentEvent_le F
    _ ≤ ∏ i, (((M.quota i : ℝ) / (M.block i).card) ^ (F i).card *
        (Nat.choose (M.block i).card (M.quota i) : ℝ)) := by
      apply Finset.prod_le_prod
      · intro i _
        positivity
      · intro i _
        have h := fixedCardinality_probability_contains_le_density_pow
          (hF i) (M.quota_le i) (hpos i)
        rw [fixedCardinalityContainmentProbability] at h
        exact (div_le_iff₀ (by exact_mod_cast Nat.choose_pos (M.quota_le i))).mp h
    _ = (∏ i, ((M.quota i : ℝ) / (M.block i).card) ^ (F i).card) *
        (M.sampleSpaceCard : ℝ) := by
      rw [Finset.prod_mul_distrib]
      simp only [sampleSpaceCard, Nat.cast_prod]

/-- Uniform exponential containment bound. In particular this is valid for
unequal prescribed edge counts on the distinct pairs of a multipartition. -/
theorem eventProbability_blockContainment_le_exp
    (M : FixedCardinalityBlockModel I Ω) (F : I → Finset Ω)
    (hF : ∀ i, F i ⊆ M.block i) (hpos : ∀ i, 0 < (M.block i).card)
    {c : ℝ} (hdensity : ∀ i, (M.quota i : ℝ) / (M.block i).card ≤ Real.exp (-c)) :
    M.eventProbability (M.blockContainmentEvent F) ≤
      Real.exp (-(c * (∑ i, (F i).card : ℕ))) := by
  classical
  calc
    M.eventProbability (M.blockContainmentEvent F) ≤
        ∏ i, ((M.quota i : ℝ) / (M.block i).card) ^ (F i).card :=
      M.eventProbability_blockContainment_le_prod F hF hpos
    _ ≤ ∏ i, (Real.exp (-c)) ^ (F i).card := by
      apply Finset.prod_le_prod
      · intro i _
        positivity
      · intro i _
        exact pow_le_pow_left₀ (by positivity) (hdensity i) _
    _ = Real.exp (-(c * (∑ i, (F i).card : ℕ))) := by
      rw [Finset.prod_pow_eq_pow_sum, ← Real.exp_nat_mul]
      congr 1
      ring

end FixedCardinalityBlockModel
end DenseGraph
