import InducedStars.Structure.Subcritical.CleanModelCounting

/-! # Summing a uniform good fraction over exact clean-model data -/

noncomputable section
open Finset Set
open scoped Classical BigOperators
namespace InducedStars
variable {k : ℕ} {V : Type*} [Fintype V] [DecidableEq V]

private theorem card_filter_sigma {I : Type*} [Fintype I] {B : I → Type*}
    [∀ i, Fintype (B i)] (P : (Σ i, B i) → Prop) :
    (Finset.univ.filter P).card =
      ∑ i, (Finset.univ.filter fun b : B i ↦ P ⟨i, b⟩).card := by
  simp only [Finset.card_filter, Fintype.sum_sigma]

private theorem card_filter_prod {I J : Type*} [Fintype I] [Fintype J]
    (P : I × J → Prop) :
    (Finset.univ.filter P).card =
      ∑ i, (Finset.univ.filter fun j : J ↦ P (i, j)).card := by
  simp only [Finset.card_filter, Fintype.sum_prod_type]

set_option maxHeartbeats 600000 in
theorem cleanRetainedPartitionFunction_le_mul_good
    (D : SubcriticalDivision k V) (eta : ℝ) (R₀ m : ℕ) (delta : ℝ)
    (P : SimpleGraph V → Prop) (C : ℕ)
    (hgood : ∀ b, b ∈ Finset.range (Nat.floor
      (subcriticalSparseSideConstant k * eta * (Fintype.card V : ℝ)^2) + 1) →
      ∀ H, H ∈ subcriticalCleanRemainderGraphFinset D eta R₀ b →
      ∀ v, v ∈ retainedEdgeCountLevel D eta R₀ m delta (b : ℤ) →
      retainedEdgeCountMultiplicity v ≤ C *
        (Finset.univ.filter (fun S : RetainedEdgeChoices v ↦ P (subcriticalCleanGraph H S))).card) :
    cleanRetainedPartitionFunction D eta R₀ m delta ≤
      C * ((subcriticalCleanModelGraphFinset D eta R₀ m delta).filter P).card := by
  let T := SubcriticalCleanModelData D eta R₀ m delta
  have hcard : ((subcriticalCleanModelGraphFinset D eta R₀ m delta).filter P).card =
      (Finset.univ.filter fun d : T ↦ P d.graph).card := by
    rw [subcriticalCleanModelGraphFinset, Finset.filter_image,
      Finset.card_image_of_injective _ SubcriticalCleanModelData.graph_injective]
  rw [hcard, ← card_subcriticalCleanModelData]
  change Fintype.card T ≤ C * _
  have hsum : (Finset.univ.filter fun d : T ↦ P d.graph).card =
      ∑ b : ↥(Finset.range (Nat.floor
        (subcriticalSparseSideConstant k * eta * (Fintype.card V : ℝ)^2) + 1)),
        ∑ H : ↥(subcriticalCleanRemainderGraphFinset D eta R₀ b.val),
          ∑ v : ↥(retainedEdgeCountLevel D eta R₀ m delta (b.val : ℤ)),
            (Finset.univ.filter fun S : RetainedEdgeChoices v.val ↦
              P (subcriticalCleanGraph H.val S)).card := by
    rw [card_filter_sigma]
    apply Finset.sum_congr rfl
    intro b _
    rw [card_filter_prod]
    apply Finset.sum_congr rfl
    intro H _
    rw [card_filter_sigma]
    rfl
  rw [hsum]
  have hall : Fintype.card T =
      ∑ b : ↥(Finset.range (Nat.floor
        (subcriticalSparseSideConstant k * eta * (Fintype.card V : ℝ)^2) + 1)),
        ∑ _H : ↥(subcriticalCleanRemainderGraphFinset D eta R₀ b.val),
          ∑ v : ↥(retainedEdgeCountLevel D eta R₀ m delta (b.val : ℤ)),
            Fintype.card (RetainedEdgeChoices v.val) := by
    simp only [T, SubcriticalCleanModelData, Fintype.card_sigma, Fintype.card_prod,
      Finset.sum_const, Finset.card_univ, smul_eq_mul]
  rw [hall]
  simp only [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro b _
  apply Finset.sum_le_sum
  intro H _
  apply Finset.sum_le_sum
  intro v _
  rw [retainedEdgeChoices_card]
  exact hgood b.val b.property H.val H.property v.val v.property

end InducedStars
