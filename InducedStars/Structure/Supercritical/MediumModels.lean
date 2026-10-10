import InducedStars.Structure.Supercritical.MediumCandidates
import InducedStars.Structure.Supercritical.ProfileModels
import Mathlib.Tactic

/-!
# Random cross-edge models for a supercritical medium witness

This module supplies the concrete cross-edge blocks used in the fixed-count
and independent comparison models.  A main-part witness is removed from its
sampled part because all of its incident adjacencies are fixed by the refined
data; a sparse witness leaves the main parts unchanged.
-/

noncomputable section

open Finset Set
open scoped BigOperators

namespace InducedStars

noncomputable local instance mediumModelsDecidableRel
    {n : ℕ} (G : SimpleGraph (Fin n)) : DecidableRel G.Adj :=
  Classical.decRel _

/-! ## Sampled parts and disjoint cross blocks -/

/-- The sampled version of a main part.  Only a witness lying in its
distinguished main part is removed. -/
def supercriticalMediumSampledPart
    {k n : ℕ} {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    (w : SupercriticalMediumWitness G α D) (j : Fin (k - 1)) :
    Finset (Fin n) :=
  if hj : j = w.part then
    if w.vertex ∈ D.parts w.part then (D.parts j).erase w.vertex
    else D.parts j
  else D.parts j

theorem supercriticalMediumSampledPart_subset
    {k n : ℕ} {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    (w : SupercriticalMediumWitness G α D) (j : Fin (k - 1)) :
    supercriticalMediumSampledPart w j ⊆ D.parts j := by
  classical
  unfold supercriticalMediumSampledPart
  split_ifs
  · exact Finset.erase_subset _ _
  · exact Finset.Subset.rfl
  · exact Finset.Subset.rfl

@[simp] theorem supercriticalMediumSampledPart_of_ne
    {k n : ℕ} {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    (w : SupercriticalMediumWitness G α D) {j : Fin (k - 1)}
    (hj : j ≠ w.part) :
    supercriticalMediumSampledPart w j = D.parts j := by
  simp [supercriticalMediumSampledPart, hj]

@[simp] theorem supercriticalMediumSampledPart_distinguished
    {k n : ℕ} {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    (w : SupercriticalMediumWitness G α D) :
    supercriticalMediumSampledPart w w.part =
      if w.vertex ∈ D.parts w.part then
        (D.parts w.part).erase w.vertex else D.parts w.part := by
  simp [supercriticalMediumSampledPart]

/-- The oriented coordinate block between two sampled main parts.  The
increasing orientation of `SupercriticalPartPair` ensures that each
unordered graph edge has one coordinate. -/
def supercriticalMediumCrossBlock
    {k n : ℕ} {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    (w : SupercriticalMediumWitness G α D)
    (e : SupercriticalPartPair k) : Finset (Fin n × Fin n) :=
  supercriticalMediumSampledPart w e.left ×ˢ
    supercriticalMediumSampledPart w e.right

@[simp] theorem mem_supercriticalMediumCrossBlock
    {k n : ℕ} {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    (w : SupercriticalMediumWitness G α D)
    (e : SupercriticalPartPair k) (xy : Fin n × Fin n) :
    xy ∈ supercriticalMediumCrossBlock w e ↔
      xy.1 ∈ supercriticalMediumSampledPart w e.left ∧
        xy.2 ∈ supercriticalMediumSampledPart w e.right := by
  simp [supercriticalMediumCrossBlock]

theorem supercriticalMediumCrossBlocks_pairwiseDisjoint
    {k n : ℕ} {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    (w : SupercriticalMediumWitness G α D) :
    Set.PairwiseDisjoint (Set.univ : Set (SupercriticalPartPair k))
      (supercriticalMediumCrossBlock w) := by
  change Set.PairwiseDisjoint (Set.univ : Set (SupercriticalPartPair k))
    (supercriticalPartCrossBlock (supercriticalMediumSampledPart w))
  exact supercriticalPartCrossBlocks_pairwiseDisjoint D
    (supercriticalMediumSampledPart w)
    (supercriticalMediumSampledPart_subset w)

@[simp] theorem card_supercriticalMediumCrossBlock
    {k n : ℕ} {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    (w : SupercriticalMediumWitness G α D)
    (e : SupercriticalPartPair k) :
    (supercriticalMediumCrossBlock w e).card =
      (supercriticalMediumSampledPart w e.left).card *
        (supercriticalMediumSampledPart w e.right).card := by
  simp [supercriticalMediumCrossBlock]

/-! ## Adjusted quotas from an actual refined witness graph -/

/-- The number of sampled cross edges of the exemplar graph in one adjusted
block.  Defining the quota this way avoids unsafe natural subtraction. -/
def supercriticalMediumAdjustedQuota
    {k n : ℕ} {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    (w : SupercriticalMediumWitness G α D)
    (e : SupercriticalPartPair k) : ℕ :=
  (G.interedges
    (supercriticalMediumSampledPart w e.left)
    (supercriticalMediumSampledPart w e.right)).card

/-- Cross edges of the exemplar that are fixed because they fall outside
the sampled block.  This is empty for a sparse witness and for blocks not
incident with a removed main-part witness. -/
def supercriticalMediumFixedCrossEdges
    {k n : ℕ} {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    (w : SupercriticalMediumWitness G α D)
    (e : SupercriticalPartPair k) : Finset (Fin n × Fin n) :=
  G.interedges (D.parts e.left) (D.parts e.right) \
    supercriticalMediumCrossBlock w e

theorem interedges_sampled_eq_inter_full_crossBlock
    {k n : ℕ} {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    (w : SupercriticalMediumWitness G α D)
    (e : SupercriticalPartPair k) :
    G.interedges
        (supercriticalMediumSampledPart w e.left)
        (supercriticalMediumSampledPart w e.right) =
      G.interedges (D.parts e.left) (D.parts e.right) ∩
        supercriticalMediumCrossBlock w e := by
  ext xy
  simp only [SimpleGraph.mem_interedges_iff, Finset.mem_inter,
    mem_supercriticalMediumCrossBlock]
  constructor
  · rintro ⟨hx, hy, hG⟩
    exact ⟨⟨supercriticalMediumSampledPart_subset w _ hx,
      supercriticalMediumSampledPart_subset w _ hy, hG⟩, hx, hy⟩
  · rintro ⟨⟨_, _, hG⟩, hx, hy⟩
    exact ⟨hx, hy, hG⟩

theorem supercriticalMediumCrossBlock_subset_full
    {k n : ℕ} {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    (w : SupercriticalMediumWitness G α D)
    (e : SupercriticalPartPair k) :
    supercriticalMediumCrossBlock w e ⊆
      D.parts e.left ×ˢ D.parts e.right := by
  intro xy hxy
  rw [mem_supercriticalMediumCrossBlock] at hxy
  exact Finset.mem_product.mpr
    ⟨supercriticalMediumSampledPart_subset w _ hxy.1,
      supercriticalMediumSampledPart_subset w _ hxy.2⟩

theorem supercriticalMediumFixedCrossEdges_subset_full
    {k n : ℕ} {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    (w : SupercriticalMediumWitness G α D)
    (e : SupercriticalPartPair k) :
    supercriticalMediumFixedCrossEdges w e ⊆
      D.parts e.left ×ˢ D.parts e.right := by
  intro xy hxy
  have hfull := (Finset.mem_sdiff.mp hxy).1
  rw [SimpleGraph.mem_interedges_iff] at hfull
  exact Finset.mem_product.mpr
    ⟨hfull.1, hfull.2.1⟩

theorem supercriticalMediumFixedCrossEdges_disjoint_block
    {k n : ℕ} {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    (w : SupercriticalMediumWitness G α D)
    (e : SupercriticalPartPair k) :
    Disjoint (supercriticalMediumFixedCrossEdges w e)
      (supercriticalMediumCrossBlock w e) := by
  rw [Finset.disjoint_left]
  intro xy hfixed hblock
  exact (Finset.mem_sdiff.mp hfixed).2 hblock

/-- Exact additive quota identity: sampled edges plus the fixed incident
cross edges recover the original cross-profile coordinate. -/
theorem supercriticalMediumAdjustedQuota_add_fixed_eq_profileCount
    {k n : ℕ} {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    (w : SupercriticalMediumWitness G α D)
    (e : SupercriticalPartPair k) :
    supercriticalMediumAdjustedQuota w e +
        (supercriticalMediumFixedCrossEdges w e).card =
      (crossEdgeProfile G D).count e := by
  rw [supercriticalMediumAdjustedQuota, crossEdgeProfile_count,
    interedges_sampled_eq_inter_full_crossBlock,
    supercriticalMediumFixedCrossEdges]
  exact Finset.card_inter_add_card_sdiff _ _

theorem supercriticalMediumAdjustedQuota_le_blockCapacity
    {k n : ℕ} {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    (w : SupercriticalMediumWitness G α D)
    (e : SupercriticalPartPair k) :
    supercriticalMediumAdjustedQuota w e ≤
      (supercriticalMediumCrossBlock w e).card := by
  rw [supercriticalMediumAdjustedQuota,
    card_supercriticalMediumCrossBlock]
  exact G.card_interedges_le_mul _ _

/-- The concrete independent fixed-cardinality cross-edge model attached to
an exemplar in a nonempty refined family. -/
def supercriticalMediumFixedModel
    {k n : ℕ} {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    (w : SupercriticalMediumWitness G α D) :
    DenseGraph.FixedCardinalityBlockModel
      (SupercriticalPartPair k) (Fin n × Fin n) where
  block := supercriticalMediumCrossBlock w
  pairwiseDisjoint := supercriticalMediumCrossBlocks_pairwiseDisjoint w
  quota := supercriticalMediumAdjustedQuota w
  quota_le := supercriticalMediumAdjustedQuota_le_blockCapacity w

/-- The associated independent Bernoulli comparison model on tagged cross
coordinates. -/
def supercriticalMediumBernoulliModel
    {k n : ℕ} {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    (w : SupercriticalMediumWitness G α D) :=
  (supercriticalMediumFixedModel w).associatedBernoulli

/-! ## Comparing adjusted choices with the original profile -/

private theorem powersetCard_le_powersetCard_of_union_fixed
    {X : Type*} [DecidableEq X]
    {A B F : Finset X} {a b : ℕ}
    (hA : A ⊆ B) (hF : F ⊆ B) (hdisj : Disjoint F A)
    (hb : a + F.card = b) :
    (A.powersetCard a).card ≤ (B.powersetCard b).card := by
  classical
  let source : Type _ := ↥(A.powersetCard a)
  let target : Type _ := ↥(B.powersetCard b)
  let extend : source → target := fun S ↦
    ⟨S.1 ∪ F, by
      rw [Finset.mem_powersetCard]
      have hS := Finset.mem_powersetCard.mp S.2
      refine ⟨Finset.union_subset (hS.1.trans hA) hF, ?_⟩
      rw [Finset.card_union_of_disjoint]
      · simpa [hS.2, hb, Nat.add_comm]
      · exact (hdisj.mono Finset.Subset.rfl hS.1).symm⟩
  have hinj : Function.Injective extend := by
    intro S T hST
    apply Subtype.ext
    have hunion : S.1 ∪ F = T.1 ∪ F := congrArg Subtype.val hST
    ext x
    have hSF : x ∈ S.1 → x ∉ F := by
      intro hxS hxF
      have hS := (Finset.mem_powersetCard.mp S.2).1
      exact (Finset.disjoint_left.mp
        (hdisj.mono Finset.Subset.rfl hS).symm) hxS hxF
    have hTF : x ∈ T.1 → x ∉ F := by
      intro hxT hxF
      have hT := (Finset.mem_powersetCard.mp T.2).1
      exact (Finset.disjoint_left.mp
        (hdisj.mono Finset.Subset.rfl hT).symm) hxT hxF
    constructor
    · intro hxS
      have hxU : x ∈ T.1 ∪ F := by simpa [hunion] using
        (show x ∈ S.1 ∪ F from Finset.mem_union_left F hxS)
      exact (Finset.mem_union.mp hxU).resolve_right (hSF hxS)
    · intro hxT
      have hxU : x ∈ S.1 ∪ F := by simpa [hunion] using
        (show x ∈ T.1 ∪ F from Finset.mem_union_left F hxT)
      exact (Finset.mem_union.mp hxU).resolve_right (hTF hxT)
  have hcard : Fintype.card source ≤ Fintype.card target :=
    Fintype.card_le_of_injective extend hinj
  simpa [source, target, Finset.card_powersetCard] using hcard

theorem choose_adjustedQuota_le_choose_profileCount
    {k n : ℕ} {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    (w : SupercriticalMediumWitness G α D)
    (e : SupercriticalPartPair k) :
    (supercriticalMediumCrossBlock w e).card.choose
        (supercriticalMediumAdjustedQuota w e) ≤
      (crossEdgeCapacity D e).choose ((crossEdgeProfile G D).count e) := by
  rw [crossEdgeCapacity]
  simpa only [Finset.card_powersetCard, Finset.card_product] using
    powersetCard_le_powersetCard_of_union_fixed
      (supercriticalMediumCrossBlock_subset_full w e)
      (supercriticalMediumFixedCrossEdges_subset_full w e)
      (supercriticalMediumFixedCrossEdges_disjoint_block w e)
      (supercriticalMediumAdjustedQuota_add_fixed_eq_profileCount w e)

/-- The adjusted product sample space injects into the original independent
cross-edge choice space, one block at a time. -/
theorem supercriticalMediumFixedModel_sampleSpaceCard_le_profileMultiplicity
    {k n : ℕ} {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    (w : SupercriticalMediumWitness G α D) :
    (supercriticalMediumFixedModel w).sampleSpaceCard ≤
      supercriticalProfileMultiplicity (crossEdgeProfile G D) := by
  classical
  unfold DenseGraph.FixedCardinalityBlockModel.sampleSpaceCard
    supercriticalProfileMultiplicity
  exact Finset.prod_le_prod (fun _ _ ↦ Nat.zero_le _)
    (fun e _ ↦ choose_adjustedQuota_le_choose_profileCount w e)

end InducedStars
