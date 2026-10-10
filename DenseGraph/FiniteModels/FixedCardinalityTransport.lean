import DenseGraph.FiniteModels.FixedCardinalityBlocks

/-!
# Exact transport of independent fixed-cardinality samples

Relabeling blocks and their actual coordinate universes preserves every
sample, quota, event cardinality and uniform event probability.
-/

noncomputable section
open Finset
namespace DenseGraph
namespace FixedCardinalityBlockModel

variable {I J Ω Ξ : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  [Fintype Ω] [DecidableEq Ω] [Fintype Ξ] [DecidableEq Ξ]

theorem mem_selectedInBlock_subtype (M : FixedCardinalityBlockModel I Ω)
    (S : M.Sample) (i : I) (w : ↥(M.block i)) :
    w.val ∈ M.selectedInBlock S i ↔ w ∈ (S i).val := by
  rw [selectedInBlock, Finset.mem_map]
  exact ⟨fun ⟨z, hz, hzw⟩ ↦ (Subtype.ext hzw : z = w) ▸ hz,
    fun hw ↦ ⟨w, hw, rfl⟩⟩

def blockSampleEquiv (M : FixedCardinalityBlockModel I Ω)
    (N : FixedCardinalityBlockModel J Ξ) (i : I) (j : J)
    (e : ↥(M.block i) ≃ ↥(N.block j)) (hquota : M.quota i = N.quota j) :
    M.BlockSample i ≃ N.BlockSample j :=
  (Equiv.Finset.congr e).subtypeEquiv (by
    intro S
    simp only [Finset.mem_powersetCard, Finset.subset_univ, true_and,
      Equiv.Finset.congr_apply, Finset.card_map, hquota])

def sampleEquiv (M : FixedCardinalityBlockModel I Ω)
    (N : FixedCardinalityBlockModel J Ξ) (f : I ≃ J)
    (e : ∀ i, ↥(M.block i) ≃ ↥(N.block (f i)))
    (hquota : ∀ i, M.quota i = N.quota (f i)) : M.Sample ≃ N.Sample :=
  f.piCongr fun i ↦ M.blockSampleEquiv N i (f i) (e i) (hquota i)

@[simp] theorem sampleEquiv_mem (M : FixedCardinalityBlockModel I Ω)
    (N : FixedCardinalityBlockModel J Ξ) (f : I ≃ J)
    (e : ∀ i, ↥(M.block i) ≃ ↥(N.block (f i)))
    (hquota : ∀ i, M.quota i = N.quota (f i))
    (S : M.Sample) (i : I) (z : ↥(M.block i)) :
    e i z ∈ ((M.sampleEquiv N f e hquota S) (f i)).val ↔ z ∈ (S i).val := by
  classical
  simp [sampleEquiv, Equiv.piCongr_apply_apply, blockSampleEquiv, Equiv.subtypeEquiv,
    Equiv.Finset.congr_apply]

theorem sampleSpaceCard_eq_of_transport (M : FixedCardinalityBlockModel I Ω)
    (N : FixedCardinalityBlockModel J Ξ) (f : I ≃ J)
    (e : ∀ i, ↥(M.block i) ≃ ↥(N.block (f i)))
    (hquota : ∀ i, M.quota i = N.quota (f i)) : M.sampleSpaceCard = N.sampleSpaceCard := by
  rw [← M.card_sample, ← N.card_sample]
  exact Fintype.card_congr (M.sampleEquiv N f e hquota)

theorem eventProbability_image_sampleEquiv (M : FixedCardinalityBlockModel I Ω)
    (N : FixedCardinalityBlockModel J Ξ) (f : I ≃ J)
    (e : ∀ i, ↥(M.block i) ≃ ↥(N.block (f i)))
    (hquota : ∀ i, M.quota i = N.quota (f i)) (F : Finset M.Sample) :
    N.eventProbability (F.image (M.sampleEquiv N f e hquota)) = M.eventProbability F := by
  classical
  rw [N.eventProbability_eq_card_div, M.eventProbability_eq_card_div,
    Finset.card_image_of_injective _ (M.sampleEquiv N f e hquota).injective,
    M.sampleSpaceCard_eq_of_transport N f e hquota]

end FixedCardinalityBlockModel
end DenseGraph
