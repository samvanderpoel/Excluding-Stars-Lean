import DenseGraph.FiniteModels.FixedCardinalityBlocks
import InducedStars.Structure.Supercritical.CountingSetup
import Mathlib.Tactic

/-!
# Fixed-cardinality models for supercritical cross-edge profiles

This module connects the supercritical cross-edge profiles from
`CountingSetup` to the reusable fixed-cardinality block model.  The common
constructor accepts arbitrary subparts of one supercritical division; the
full-profile model and the witness-adjusted medium model are specializations
of that single construction.
-/

noncomputable section

open Finset Set
open scoped BigOperators

namespace InducedStars

variable {k : ℕ} {V : Type*} [Fintype V] [DecidableEq V]

/-! ## A shared cross-block constructor -/

/-- The oriented coordinate block between two prescribed subparts. -/
abbrev supercriticalPartCrossBlock
    (part : Fin (k - 1) → Finset V)
    (e : SupercriticalPartPair k) : Finset (V × V) :=
  part e.left ×ˢ part e.right

omit [Fintype V] [DecidableEq V] in
@[simp] theorem mem_supercriticalPartCrossBlock
    (part : Fin (k - 1) → Finset V)
    (e : SupercriticalPartPair k) (xy : V × V) :
    xy ∈ supercriticalPartCrossBlock part e ↔
      xy.1 ∈ part e.left ∧ xy.2 ∈ part e.right := by
  simp [supercriticalPartCrossBlock]

omit [Fintype V] [DecidableEq V] in
@[simp] theorem card_supercriticalPartCrossBlock
    (part : Fin (k - 1) → Finset V)
    (e : SupercriticalPartPair k) :
    (supercriticalPartCrossBlock part e).card =
      (part e.left).card * (part e.right).card := by
  simp [supercriticalPartCrossBlock]

/-- Oriented products of subparts of a supercritical division are pairwise
disjoint.  The increasing orientation on `SupercriticalPartPair` rules out
the reversed copy of an unordered pair. -/
theorem supercriticalPartCrossBlocks_pairwiseDisjoint
    (D : SupercriticalDivision k V)
    (part : Fin (k - 1) → Finset V)
    (hpart : ∀ i, part i ⊆ D.parts i) :
    Set.PairwiseDisjoint (Set.univ : Set (SupercriticalPartPair k))
      (supercriticalPartCrossBlock part) := by
  classical
  intro e _he f _hf hef
  change Disjoint (supercriticalPartCrossBlock part e)
    (supercriticalPartCrossBlock part f)
  rw [Finset.disjoint_left]
  intro xy hxe hxf
  have hxe' := (mem_supercriticalPartCrossBlock part e xy).mp hxe
  have hxf' := (mem_supercriticalPartCrossBlock part f xy).mp hxf
  have hleft : e.left = f.left :=
    D.mem_part_unique (hpart e.left hxe'.1) (hpart f.left hxf'.1)
  have hright : e.right = f.right :=
    D.mem_part_unique (hpart e.right hxe'.2) (hpart f.right hxf'.2)
  apply hef
  exact SupercriticalPartPair.ext hleft hright

/-- The single project-specific constructor for independent exact-count
sampling across oriented supercritical cross blocks. -/
abbrev supercriticalCrossBlockModel
    (D : SupercriticalDivision k V)
    (part : Fin (k - 1) → Finset V)
    (hpart : ∀ i, part i ⊆ D.parts i)
    (quota : SupercriticalPartPair k → ℕ)
    (hquota : ∀ e, quota e ≤ (supercriticalPartCrossBlock part e).card) :
    DenseGraph.FixedCardinalityBlockModel
      (SupercriticalPartPair k) (V × V) where
  block := supercriticalPartCrossBlock part
  pairwiseDisjoint :=
    supercriticalPartCrossBlocks_pairwiseDisjoint D part hpart
  quota := quota
  quota_le := hquota

@[simp] theorem supercriticalCrossBlockModel_block
    (D : SupercriticalDivision k V)
    (part : Fin (k - 1) → Finset V)
    (hpart : ∀ i, part i ⊆ D.parts i)
    (quota : SupercriticalPartPair k → ℕ)
    (hquota : ∀ e, quota e ≤ (supercriticalPartCrossBlock part e).card)
    (e : SupercriticalPartPair k) :
    (supercriticalCrossBlockModel D part hpart quota hquota).block e =
      supercriticalPartCrossBlock part e :=
  rfl

@[simp] theorem supercriticalCrossBlockModel_quota
    (D : SupercriticalDivision k V)
    (part : Fin (k - 1) → Finset V)
    (hpart : ∀ i, part i ⊆ D.parts i)
    (quota : SupercriticalPartPair k → ℕ)
    (hquota : ∀ e, quota e ≤ (supercriticalPartCrossBlock part e).card)
    (e : SupercriticalPartPair k) :
    (supercriticalCrossBlockModel D part hpart quota hquota).quota e = quota e :=
  rfl

/-! ## The exact full-profile model -/

/-- Independent uniform exact-count sampling in every full cross cell of a
supercritical division. -/
def supercriticalFixedProfileBlockModel
    (D : SupercriticalDivision k V) (profile : SupercriticalEdgeProfile D) :
    DenseGraph.FixedCardinalityBlockModel
      (SupercriticalPartPair k) (V × V) :=
  supercriticalCrossBlockModel D D.parts (fun _ ↦ Finset.Subset.rfl)
    profile.count fun e ↦ by
      rw [card_supercriticalPartCrossBlock]
      simpa [crossEdgeCapacity] using profile.count_le_capacity e

/-- Short paper-facing alias for the exact full-profile model. -/
abbrev supercriticalFixedProfileModel
    (D : SupercriticalDivision k V) (profile : SupercriticalEdgeProfile D) :
    DenseGraph.FixedCardinalityBlockModel
      (SupercriticalPartPair k) (V × V) :=
  supercriticalFixedProfileBlockModel D profile

@[simp] theorem supercriticalFixedProfileBlockModel_block
    (D : SupercriticalDivision k V) (profile : SupercriticalEdgeProfile D)
    (e : SupercriticalPartPair k) :
    (supercriticalFixedProfileBlockModel D profile).block e =
      D.parts e.left ×ˢ D.parts e.right :=
  rfl

@[simp] theorem card_supercriticalFixedProfileBlockModel_block
    (D : SupercriticalDivision k V) (profile : SupercriticalEdgeProfile D)
    (e : SupercriticalPartPair k) :
    ((supercriticalFixedProfileBlockModel D profile).block e).card =
      crossEdgeCapacity D e := by
  simp [crossEdgeCapacity]

@[simp] theorem supercriticalFixedProfileBlockModel_quota
    (D : SupercriticalDivision k V) (profile : SupercriticalEdgeProfile D)
    (e : SupercriticalPartPair k) :
    (supercriticalFixedProfileBlockModel D profile).quota e = profile.count e :=
  rfl

/-- The exact full-profile sample space has the profile multiplicity. -/
theorem supercriticalFixedProfileBlockModel_sampleSpaceCard_eq
    (D : SupercriticalDivision k V) (profile : SupercriticalEdgeProfile D) :
    (supercriticalFixedProfileBlockModel D profile).sampleSpaceCard =
      supercriticalProfileMultiplicity profile := by
  classical
  unfold DenseGraph.FixedCardinalityBlockModel.sampleSpaceCard
    supercriticalProfileMultiplicity
  apply Finset.prod_congr rfl
  intro e _he
  rw [card_supercriticalFixedProfileBlockModel_block,
    supercriticalFixedProfileBlockModel_quota]

/-- Cardinality of the concrete exact full-profile sample type. -/
theorem supercriticalFixedProfileBlockModel_card_sample
    (D : SupercriticalDivision k V) (profile : SupercriticalEdgeProfile D) :
    Fintype.card (supercriticalFixedProfileBlockModel D profile).Sample =
      supercriticalProfileMultiplicity profile := by
  rw [DenseGraph.FixedCardinalityBlockModel.card_sample,
    supercriticalFixedProfileBlockModel_sampleSpaceCard_eq]

/-! ## The associated Bernoulli comparison -/

/-- The independent Bernoulli product whose probability on cell `e` is the
exact profile density in that cell. -/
abbrev supercriticalProfileBernoulliModel
    (D : SupercriticalDivision k V) (profile : SupercriticalEdgeProfile D) :=
  (supercriticalFixedProfileBlockModel D profile).associatedBernoulli

@[simp] theorem supercriticalProfileBernoulliModel_probability_eq_profileDensity
    (D : SupercriticalDivision k V) (profile : SupercriticalEdgeProfile D)
    (c : (supercriticalFixedProfileBlockModel D profile).Coordinate) :
    (supercriticalProfileBernoulliModel D profile).probability c =
      profileDensity profile c.1 := by
  rw [DenseGraph.FixedCardinalityBlockModel.associatedBernoulli_probability]
  simp [DenseGraph.FixedCardinalityBlockModel.quotaParameter,
    profileDensity]

end InducedStars
