import InducedStars.Structure.Supercritical.MediumModels
import Mathlib.Tactic

/-!
# Finite refinement of the supercritical medium-degree family

This file carries out the exact finite-cover bookkeeping for the paper's
refined family `F'_{Π,T,v,F,m'}`.  The incident graph `F` is represented by
the full neighbor finset of the selected witness vertex.  Thus every key
records the combined defect graph, witness and distinguished part, fixed
incident pattern, and exact cross-edge profile.
-/

noncomputable section

open Finset Set
open scoped BigOperators

namespace InducedStars

noncomputable local instance mediumRefinementGraphDecidableEq (n : ℕ) :
    DecidableEq (SimpleGraph (Fin n)) :=
  Classical.decEq _

noncomputable local instance mediumRefinementDecidableRel
    {n : ℕ} (G : SimpleGraph (Fin n)) : DecidableRel G.Adj :=
  Classical.decRel _

/-! ## Raw keys and exact fibers -/

/-- The finite auxiliary data fixed in one raw medium-degree refinement. -/
structure SupercriticalMediumRefinementKey
    {k n : ℕ} (D : SupercriticalDivision k (Fin n)) where
  defect : SimpleGraph (Fin n)
  vertex : Fin n
  part : Fin (k - 1)
  incident : Finset (Fin n)
  profile : SupercriticalEdgeProfile D

@[ext] theorem SupercriticalMediumRefinementKey.ext
    {k n : ℕ} {D : SupercriticalDivision k (Fin n)}
    {a b : SupercriticalMediumRefinementKey D}
    (hdefect : a.defect = b.defect)
    (hvertex : a.vertex = b.vertex)
    (hpart : a.part = b.part)
    (hincident : a.incident = b.incident)
    (hprofile : a.profile = b.profile) : a = b := by
  cases a
  cases b
  simp_all

/-- The medium family, regarded as a finite type so its canonical selected
witness can be used in a total key function. -/
abbrev SupercriticalMediumGraph
    (k : ℕ) (hk : 3 ≤ k) (gamma : ℝ)
    (hgamma : gamma ∈ Set.Ico (gammaK k) 1)
    (alpha : ℝ) (m n : ℕ) (tau : ℝ) (hn : k - 1 ≤ n)
    (D : SupercriticalDivision k (Fin n)) :=
  ↑(supercriticalMediumDegreeGraphFinset
    k hk gamma hgamma alpha m n tau hn D)

/-- The complete adjacency pattern incident with a distinguished vertex. -/
def supercriticalMediumIncidentPattern
    {n : ℕ} (H : SimpleGraph (Fin n)) (v : Fin n) : Finset (Fin n) := by
  classical
  exact (Finset.univ : Finset (Fin n)).filter fun x ↦ H.Adj v x

@[simp] theorem mem_supercriticalMediumIncidentPattern
    {n : ℕ} {H : SimpleGraph (Fin n)} {v x : Fin n} :
    x ∈ supercriticalMediumIncidentPattern H v ↔ H.Adj v x := by
  simp [supercriticalMediumIncidentPattern]

/-- Canonical raw refinement key of one graph in the medium family. -/
def supercriticalMediumRefinementKeyOf
    {k : ℕ} {hk : 3 ≤ k} {gamma : ℝ}
    {hgamma : gamma ∈ Set.Ico (gammaK k) 1}
    {alpha : ℝ} (halpha : 0 < alpha)
    {m n : ℕ} {tau : ℝ} {hn : k - 1 ≤ n}
    {D : SupercriticalDivision k (Fin n)}
    (H : SupercriticalMediumGraph k hk gamma hgamma alpha m n tau hn D) :
    SupercriticalMediumRefinementKey D :=
  let w := supercriticalMediumWitnessOfMem halpha H.2
  { defect := combinedSupercriticalDefectGraph H.1 D
    vertex := w.vertex
    part := w.part
    incident := supercriticalMediumIncidentPattern H.1 w.vertex
    profile := crossEdgeProfile H.1 D }

/-- Literal finite set of the refinement keys which actually occur. -/
def supercriticalMediumRefinementKeyFinset
    (k : ℕ) (hk : 3 ≤ k) (gamma : ℝ)
    (hgamma : gamma ∈ Set.Ico (gammaK k) 1)
    (alpha : ℝ) (halpha : 0 < alpha)
    (m n : ℕ) (tau : ℝ) (hn : k - 1 ≤ n)
    (D : SupercriticalDivision k (Fin n)) :
    Finset (SupercriticalMediumRefinementKey D) := by
  classical
  exact (Finset.univ : Finset
    (SupercriticalMediumGraph k hk gamma hgamma alpha m n tau hn D)).image
      (supercriticalMediumRefinementKeyOf halpha)

@[simp] theorem mem_supercriticalMediumRefinementKeyFinset
    {k : ℕ} {hk : 3 ≤ k} {gamma : ℝ}
    {hgamma : gamma ∈ Set.Ico (gammaK k) 1}
    {alpha : ℝ} {halpha : 0 < alpha}
    {m n : ℕ} {tau : ℝ} {hn : k - 1 ≤ n}
    {D : SupercriticalDivision k (Fin n)}
    {key : SupercriticalMediumRefinementKey D} :
    key ∈ supercriticalMediumRefinementKeyFinset
        k hk gamma hgamma alpha halpha m n tau hn D ↔
      ∃ H : SupercriticalMediumGraph
          k hk gamma hgamma alpha m n tau hn D,
        supercriticalMediumRefinementKeyOf halpha H = key := by
  classical
  simp [supercriticalMediumRefinementKeyFinset]

/-- The fiber of the canonical key map, still represented as a subtype of
the original medium family. -/
def supercriticalMediumRefinedSubtypeFinset
    (k : ℕ) (hk : 3 ≤ k) (gamma : ℝ)
    (hgamma : gamma ∈ Set.Ico (gammaK k) 1)
    (alpha : ℝ) (halpha : 0 < alpha)
    (m n : ℕ) (tau : ℝ) (hn : k - 1 ≤ n)
    {D : SupercriticalDivision k (Fin n)}
    (key : SupercriticalMediumRefinementKey D) :
    Finset (SupercriticalMediumGraph
      k hk gamma hgamma alpha m n tau hn D) := by
  classical
  exact Finset.univ.filter fun H ↦
    supercriticalMediumRefinementKeyOf halpha H = key

@[simp] theorem mem_supercriticalMediumRefinedSubtypeFinset
    {k : ℕ} {hk : 3 ≤ k} {gamma : ℝ}
    {hgamma : gamma ∈ Set.Ico (gammaK k) 1}
    {alpha : ℝ} {halpha : 0 < alpha}
    {m n : ℕ} {tau : ℝ} {hn : k - 1 ≤ n}
    {D : SupercriticalDivision k (Fin n)}
    {key : SupercriticalMediumRefinementKey D}
    {H : SupercriticalMediumGraph
      k hk gamma hgamma alpha m n tau hn D} :
    H ∈ supercriticalMediumRefinedSubtypeFinset
        k hk gamma hgamma alpha halpha m n tau hn key ↔
      supercriticalMediumRefinementKeyOf halpha H = key := by
  classical
  simp [supercriticalMediumRefinedSubtypeFinset]

/-- The paper's raw refined graph family, as an ordinary finset of labeled
graphs. -/
def supercriticalMediumRefinedGraphFinset
    (k : ℕ) (hk : 3 ≤ k) (gamma : ℝ)
    (hgamma : gamma ∈ Set.Ico (gammaK k) 1)
    (alpha : ℝ) (halpha : 0 < alpha)
    (m n : ℕ) (tau : ℝ) (hn : k - 1 ≤ n)
    {D : SupercriticalDivision k (Fin n)}
    (key : SupercriticalMediumRefinementKey D) :
    Finset (SimpleGraph (Fin n)) :=
  (supercriticalMediumRefinedSubtypeFinset
      k hk gamma hgamma alpha halpha m n tau hn key).map
    ⟨Subtype.val, Subtype.val_injective⟩

@[simp] theorem mem_supercriticalMediumRefinedGraphFinset
    {k : ℕ} {hk : 3 ≤ k} {gamma : ℝ}
    {hgamma : gamma ∈ Set.Ico (gammaK k) 1}
    {alpha : ℝ} {halpha : 0 < alpha}
    {m n : ℕ} {tau : ℝ} {hn : k - 1 ≤ n}
    {D : SupercriticalDivision k (Fin n)}
    {key : SupercriticalMediumRefinementKey D}
    {G : SimpleGraph (Fin n)} :
    G ∈ supercriticalMediumRefinedGraphFinset
        k hk gamma hgamma alpha halpha m n tau hn key ↔
      ∃ hG : G ∈ supercriticalMediumDegreeGraphFinset
          k hk gamma hgamma alpha m n tau hn D,
        supercriticalMediumRefinementKeyOf halpha ⟨G, hG⟩ = key := by
  classical
  simp [supercriticalMediumRefinedGraphFinset]

@[simp] theorem card_supercriticalMediumRefinedGraphFinset
    {k : ℕ} {hk : 3 ≤ k} {gamma : ℝ}
    {hgamma : gamma ∈ Set.Ico (gammaK k) 1}
    {alpha : ℝ} (halpha : 0 < alpha)
    {m n : ℕ} {tau : ℝ} {hn : k - 1 ≤ n}
    {D : SupercriticalDivision k (Fin n)}
    (key : SupercriticalMediumRefinementKey D) :
    (supercriticalMediumRefinedGraphFinset
        k hk gamma hgamma alpha halpha m n tau hn key).card =
      (supercriticalMediumRefinedSubtypeFinset
        k hk gamma hgamma alpha halpha m n tau hn key).card := by
  classical
  simp [supercriticalMediumRefinedGraphFinset]

/-- The refined fibers cover the whole medium family exactly. -/
theorem supercriticalMediumRefinedGraphFinset_biUnion
    {k : ℕ} {hk : 3 ≤ k} {gamma : ℝ}
    {hgamma : gamma ∈ Set.Ico (gammaK k) 1}
    {alpha : ℝ} (halpha : 0 < alpha)
    {m n : ℕ} {tau : ℝ} {hn : k - 1 ≤ n}
    (D : SupercriticalDivision k (Fin n)) :
    (supercriticalMediumRefinementKeyFinset
        k hk gamma hgamma alpha halpha m n tau hn D).biUnion
        (supercriticalMediumRefinedGraphFinset
          k hk gamma hgamma alpha halpha m n tau hn) =
      supercriticalMediumDegreeGraphFinset
        k hk gamma hgamma alpha m n tau hn D := by
  classical
  ext G
  constructor
  · intro hG
    obtain ⟨key, _hkey, hGkey⟩ := Finset.mem_biUnion.mp hG
    exact (mem_supercriticalMediumRefinedGraphFinset.mp hGkey).choose
  · intro hG
    let H : SupercriticalMediumGraph
        k hk gamma hgamma alpha m n tau hn D := ⟨G, hG⟩
    let key := supercriticalMediumRefinementKeyOf halpha H
    apply Finset.mem_biUnion.mpr
    refine ⟨key, ?_, ?_⟩
    · exact mem_supercriticalMediumRefinementKeyFinset.mpr ⟨H, rfl⟩
    · exact mem_supercriticalMediumRefinedGraphFinset.mpr ⟨hG, rfl⟩

/-- Explicit finite cover-cardinality inequality. -/
theorem card_supercriticalMediumDegreeGraphFinset_le_sum_refined
    {k : ℕ} {hk : 3 ≤ k} {gamma : ℝ}
    {hgamma : gamma ∈ Set.Ico (gammaK k) 1}
    {alpha : ℝ} (halpha : 0 < alpha)
    {m n : ℕ} {tau : ℝ} {hn : k - 1 ≤ n}
    (D : SupercriticalDivision k (Fin n)) :
    (supercriticalMediumDegreeGraphFinset
        k hk gamma hgamma alpha m n tau hn D).card ≤
      ∑ key ∈ supercriticalMediumRefinementKeyFinset
          k hk gamma hgamma alpha halpha m n tau hn D,
        (supercriticalMediumRefinedGraphFinset
          k hk gamma hgamma alpha halpha m n tau hn key).card := by
  classical
  rw [← supercriticalMediumRefinedGraphFinset_biUnion
    (k := k) (hk := hk) (gamma := gamma) (hgamma := hgamma)
    (alpha := alpha) (m := m) (n := n) (tau := tau) (hn := hn)
    halpha D]
  exact Finset.card_biUnion_le

/-! ## Exact finite count of the auxiliary data -/

/-- Forget proof fields and retain the five finite pieces of a refinement
key. -/
def supercriticalMediumRefinementTuple
    {k n : ℕ} {D : SupercriticalDivision k (Fin n)}
    (key : SupercriticalMediumRefinementKey D) :=
  ((((key.defect, key.vertex), key.part), key.incident), key.profile.count)

theorem supercriticalMediumRefinementTuple_injective
    {k n : ℕ} {D : SupercriticalDivision k (Fin n)} :
    Function.Injective
      (supercriticalMediumRefinementTuple (D := D)) := by
  intro a b hab
  apply SupercriticalMediumRefinementKey.ext
  · exact congrArg (fun x ↦ x.1.1.1.1) hab
  · exact congrArg (fun x ↦ x.1.1.1.2) hab
  · exact congrArg (fun x ↦ x.1.1.2) hab
  · exact congrArg (fun x ↦ x.1.2) hab
  · apply SupercriticalEdgeProfile.ext
    exact congrArg (fun x ↦ x.2) hab

/-- The literal cartesian product containing every occurring refinement
tuple. -/
def supercriticalMediumAuxiliaryTupleFinset
    (k : ℕ) (hk : 3 ≤ k) (gamma : ℝ)
    (hgamma : gamma ∈ Set.Ico (gammaK k) 1)
    (m n : ℕ) (tau : ℝ) (hn : k - 1 ≤ n)
    (D : SupercriticalDivision k (Fin n)) :=
  ((((supercriticalCombinedDefectPatternFinset
      k hk gamma hgamma m n tau hn D).product
      (Finset.univ : Finset (Fin n))).product
      (Finset.univ : Finset (Fin (k - 1)))).product
      (Finset.powerset (Finset.univ : Finset (Fin n)))).product
      (supercriticalProfileCountVectorFinset D)

/-- Every occurring refinement key lands in the advertised finite product
of defect, witness, incident-pattern, and profile choices. -/
theorem supercriticalMediumRefinementTuple_mem_auxiliary
    {k : ℕ} {hk : 3 ≤ k} {gamma : ℝ}
    {hgamma : gamma ∈ Set.Ico (gammaK k) 1}
    {alpha : ℝ} {halpha : 0 < alpha}
    {m n : ℕ} {tau : ℝ} {hn : k - 1 ≤ n}
    {D : SupercriticalDivision k (Fin n)}
    {key : SupercriticalMediumRefinementKey D}
    (hkey : key ∈ supercriticalMediumRefinementKeyFinset
      k hk gamma hgamma alpha halpha m n tau hn D) :
    supercriticalMediumRefinementTuple key ∈
      supercriticalMediumAuxiliaryTupleFinset
        k hk gamma hgamma m n tau hn D := by
  classical
  obtain ⟨H, hH⟩ := mem_supercriticalMediumRefinementKeyFinset.mp hkey
  subst key
  have hdef :=
    (mem_supercriticalMediumDegreeGraphFinset.mp H.2).1
  have hdivision :=
    (mem_supercriticalDivisionDefectGraphFinset.mp hdef).2.1
  have hpattern : combinedSupercriticalDefectGraph H.1 D ∈
      supercriticalCombinedDefectPatternFinset
        k hk gamma hgamma m n tau hn D := by
    rw [mem_supercriticalCombinedDefectPatternFinset]
    refine ⟨H.1, hdef, ?_⟩
    simp [canonicalCombinedDefectGraph, hdivision]
  let w := supercriticalMediumWitnessOfMem halpha H.2
  change ((((combinedSupercriticalDefectGraph H.1 D, w.vertex), w.part),
      supercriticalMediumIncidentPattern H.1 w.vertex),
        (crossEdgeProfile H.1 D).count) ∈
    (((((supercriticalCombinedDefectPatternFinset
      k hk gamma hgamma m n tau hn D).product
        (Finset.univ : Finset (Fin n))).product
        (Finset.univ : Finset (Fin (k - 1)))).product
        (Finset.powerset (Finset.univ : Finset (Fin n)))).product
        (supercriticalProfileCountVectorFinset D))
  apply Finset.mem_product.mpr
  refine ⟨?_, (mem_supercriticalProfileCountVectorFinset D _).mpr
    (crossEdgeProfile H.1 D).count_le_capacity⟩
  apply Finset.mem_product.mpr
  refine ⟨?_, Finset.mem_powerset.mpr (Finset.subset_univ _)⟩
  apply Finset.mem_product.mpr
  refine ⟨?_, Finset.mem_univ _⟩
  exact Finset.mem_product.mpr ⟨hpattern, Finset.mem_univ _⟩

/-- Exact product bound for the number of occurring refinement keys. -/
theorem card_supercriticalMediumRefinementKeyFinset_le_auxiliary
    {k : ℕ} {hk : 3 ≤ k} {gamma : ℝ}
    {hgamma : gamma ∈ Set.Ico (gammaK k) 1}
    {alpha : ℝ} (halpha : 0 < alpha)
    {m n : ℕ} {tau : ℝ} {hn : k - 1 ≤ n}
    (D : SupercriticalDivision k (Fin n)) :
    (supercriticalMediumRefinementKeyFinset
      k hk gamma hgamma alpha halpha m n tau hn D).card ≤
      (supercriticalCombinedDefectPatternFinset
          k hk gamma hgamma m n tau hn D).card *
        n * (k - 1) * 2 ^ n *
          (supercriticalProfileCountVectorFinset D).card := by
  classical
  let keys := supercriticalMediumRefinementKeyFinset
    k hk gamma hgamma alpha halpha m n tau hn D
  let tupleImage := keys.image
    (supercriticalMediumRefinementTuple (D := D))
  have hcardImage : tupleImage.card = keys.card := by
    apply Finset.card_image_iff.mpr
    intro a _ha b _hb hab
    exact supercriticalMediumRefinementTuple_injective hab
  have hsubset : tupleImage ⊆ supercriticalMediumAuxiliaryTupleFinset
      k hk gamma hgamma m n tau hn D := by
    intro x hx
    obtain ⟨key, hkey, rfl⟩ := Finset.mem_image.mp hx
    exact supercriticalMediumRefinementTuple_mem_auxiliary hkey
  rw [← hcardImage]
  calc
    tupleImage.card ≤ (supercriticalMediumAuxiliaryTupleFinset
      k hk gamma hgamma m n tau hn D).card :=
      Finset.card_le_card hsubset
    _ = (supercriticalCombinedDefectPatternFinset
          k hk gamma hgamma m n tau hn D).card *
        n * (k - 1) * 2 ^ n *
          (supercriticalProfileCountVectorFinset D).card := by
      simp [supercriticalMediumAuxiliaryTupleFinset, Nat.mul_assoc]

/-! ## Replacing exactly the sampled cross blocks -/

/-- An unordered vertex pair belongs to one of the sampled oriented cross
blocks.  Both orientations are admitted because graph adjacency is symmetric,
whereas `supercriticalMediumCrossBlock` uses the increasing part orientation. -/
def supercriticalMediumIsSampledCrossPair
    {k n : ℕ} {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    (w : SupercriticalMediumWitness G α D) (x y : Fin n) : Prop :=
  ∃ e : SupercriticalPartPair k,
    (x, y) ∈ supercriticalMediumCrossBlock w e ∨
      (y, x) ∈ supercriticalMediumCrossBlock w e

/-- An unordered vertex pair is selected by a fixed-cardinality sample. -/
def supercriticalMediumIsSelectedCrossPair
    {k n : ℕ} {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    (w : SupercriticalMediumWitness G α D)
    (S : (supercriticalMediumFixedModel w).Sample) (x y : Fin n) : Prop :=
  ∃ e : SupercriticalPartPair k,
    (x, y) ∈ (supercriticalMediumFixedModel w).selectedInBlock S e ∨
      (y, x) ∈ (supercriticalMediumFixedModel w).selectedInBlock S e

theorem supercriticalMediumIsSampledCrossPair_comm
    {k n : ℕ} {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    (w : SupercriticalMediumWitness G α D) (x y : Fin n) :
    supercriticalMediumIsSampledCrossPair w x y ↔
      supercriticalMediumIsSampledCrossPair w y x := by
  constructor <;> rintro ⟨e, h | h⟩
  · exact ⟨e, Or.inr h⟩
  · exact ⟨e, Or.inl h⟩
  · exact ⟨e, Or.inr h⟩
  · exact ⟨e, Or.inl h⟩

theorem supercriticalMediumIsSelectedCrossPair_comm
    {k n : ℕ} {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    (w : SupercriticalMediumWitness G α D)
    (S : (supercriticalMediumFixedModel w).Sample) (x y : Fin n) :
    supercriticalMediumIsSelectedCrossPair w S x y ↔
      supercriticalMediumIsSelectedCrossPair w S y x := by
  constructor <;> rintro ⟨e, h | h⟩
  · exact ⟨e, Or.inr h⟩
  · exact ⟨e, Or.inl h⟩
  · exact ⟨e, Or.inr h⟩
  · exact ⟨e, Or.inl h⟩

theorem supercriticalMediumIsSelectedCrossPair_isSampled
    {k n : ℕ} {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    (w : SupercriticalMediumWitness G α D)
    (S : (supercriticalMediumFixedModel w).Sample) {x y : Fin n}
    (hxy : supercriticalMediumIsSelectedCrossPair w S x y) :
    supercriticalMediumIsSampledCrossPair w x y := by
  obtain ⟨e, h | h⟩ := hxy
  · exact ⟨e, Or.inl
      ((supercriticalMediumFixedModel w).selectedInBlock_subset S e h)⟩
  · exact ⟨e, Or.inr
      ((supercriticalMediumFixedModel w).selectedInBlock_subset S e h)⟩

theorem supercriticalMediumIsSampledCrossPair_ne
    {k n : ℕ} {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    (w : SupercriticalMediumWitness G α D) {x y : Fin n}
    (hxy : supercriticalMediumIsSampledCrossPair w x y) : x ≠ y := by
  obtain ⟨e, h | h⟩ := hxy
  · rw [mem_supercriticalMediumCrossBlock] at h
    intro hxy
    subst y
    exact e.left_ne_right
      (D.mem_part_unique
        (supercriticalMediumSampledPart_subset w e.left h.1)
        (supercriticalMediumSampledPart_subset w e.right h.2))
  · rw [mem_supercriticalMediumCrossBlock] at h
    intro hxy
    subst y
    exact e.left_ne_right
      (D.mem_part_unique
        (supercriticalMediumSampledPart_subset w e.left h.1)
        (supercriticalMediumSampledPart_subset w e.right h.2))

/-- Complete every edge outside the sampled cross blocks with the exemplar
graph, and put exactly the sampled edges inside those blocks. -/
def supercriticalMediumOutcomeGraph
    {k n : ℕ} {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    (w : SupercriticalMediumWitness G α D)
    (S : (supercriticalMediumFixedModel w).Sample) : SimpleGraph (Fin n) :=
  SimpleGraph.fromRel fun x y ↦
    supercriticalMediumIsSelectedCrossPair w S x y ∨
      (¬ supercriticalMediumIsSampledCrossPair w x y ∧ G.Adj x y)

@[simp] theorem supercriticalMediumOutcomeGraph_adj
    {k n : ℕ} {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    (w : SupercriticalMediumWitness G α D)
    (S : (supercriticalMediumFixedModel w).Sample) (x y : Fin n) :
    (supercriticalMediumOutcomeGraph w S).Adj x y ↔
      supercriticalMediumIsSelectedCrossPair w S x y ∨
        (¬ supercriticalMediumIsSampledCrossPair w x y ∧ G.Adj x y) := by
  rw [supercriticalMediumOutcomeGraph, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨_, h | h⟩
    · exact h
    · rcases h with h | h
      · exact Or.inl
          ((supercriticalMediumIsSelectedCrossPair_comm w S y x).mp h)
      · exact Or.inr ⟨
          fun hxy ↦ h.1
            ((supercriticalMediumIsSampledCrossPair_comm w x y).mp hxy),
          (G.adj_comm y x).mp h.2⟩
  · intro h
    have hne : x ≠ y := by
      rcases h with h | h
      · exact supercriticalMediumIsSampledCrossPair_ne w
          (supercriticalMediumIsSelectedCrossPair_isSampled w S h)
      · exact G.ne_of_adj h.2
    exact ⟨hne, Or.inl h⟩

theorem supercriticalMediumOutcomeGraph_adj_of_sampled
    {k n : ℕ} {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    (w : SupercriticalMediumWitness G α D)
    (S : (supercriticalMediumFixedModel w).Sample) {x y : Fin n}
    (hxy : supercriticalMediumIsSampledCrossPair w x y) :
    (supercriticalMediumOutcomeGraph w S).Adj x y ↔
      supercriticalMediumIsSelectedCrossPair w S x y := by
  rw [supercriticalMediumOutcomeGraph_adj]
  constructor
  · rintro (h | h)
    · exact h
    · exact False.elim (h.1 hxy)
  · exact Or.inl

theorem supercriticalMediumOutcomeGraph_adj_of_not_sampled
    {k n : ℕ} {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    (w : SupercriticalMediumWitness G α D)
    (S : (supercriticalMediumFixedModel w).Sample) {x y : Fin n}
    (hxy : ¬ supercriticalMediumIsSampledCrossPair w x y) :
    (supercriticalMediumOutcomeGraph w S).Adj x y ↔ G.Adj x y := by
  rw [supercriticalMediumOutcomeGraph_adj]
  constructor
  · rintro (h | h)
    · exact False.elim
        (hxy (supercriticalMediumIsSelectedCrossPair_isSampled w S h))
    · exact h.2
  · exact fun h ↦ Or.inr ⟨hxy, h⟩

theorem supercriticalMediumWitness_vertex_not_mem_sampledPart
    {k n : ℕ} {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    (w : SupercriticalMediumWitness G α D) (j : Fin (k - 1)) :
    w.vertex ∉ supercriticalMediumSampledPart w j := by
  intro hvj
  rcases w.location with hvpart | hvsparse
  · by_cases hj : j = w.part
    · subst j
      simpa [supercriticalMediumSampledPart, hvpart] using hvj
    · have hvj' := supercriticalMediumSampledPart_subset w j hvj
      exact hj (D.mem_part_unique hvj' hvpart)
  · have hvj' := supercriticalMediumSampledPart_subset w j hvj
    exact (Finset.disjoint_left.mp (D.part_disjoint_sparse j)) hvj' hvsparse

theorem not_supercriticalMediumIsSampledCrossPair_witness_left
    {k n : ℕ} {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    (w : SupercriticalMediumWitness G α D) (x : Fin n) :
    ¬ supercriticalMediumIsSampledCrossPair w w.vertex x := by
  rintro ⟨e, h | h⟩
  · exact supercriticalMediumWitness_vertex_not_mem_sampledPart w e.left
      ((mem_supercriticalMediumCrossBlock w e _).mp h).1
  · exact supercriticalMediumWitness_vertex_not_mem_sampledPart w e.right
      ((mem_supercriticalMediumCrossBlock w e _).mp h).2

theorem not_supercriticalMediumIsSampledCrossPair_of_mem_sparse_right
    {k n : ℕ} {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    (w : SupercriticalMediumWitness G α D) {x y : Fin n}
    (hy : y ∈ D.sparse) :
    ¬ supercriticalMediumIsSampledCrossPair w x y := by
  rintro ⟨e, h | h⟩
  · have hpart := supercriticalMediumSampledPart_subset w e.right
      ((mem_supercriticalMediumCrossBlock w e _).mp h).2
    exact (Finset.disjoint_left.mp (D.part_disjoint_sparse e.right)) hpart hy
  · have hpart := supercriticalMediumSampledPart_subset w e.left
      ((mem_supercriticalMediumCrossBlock w e _).mp h).1
    exact (Finset.disjoint_left.mp (D.part_disjoint_sparse e.left)) hpart hy

theorem not_supercriticalMediumIsSampledCrossPair_of_mem_same_part
    {k n : ℕ} {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    (w : SupercriticalMediumWitness G α D)
    (i : Fin (k - 1)) {x y : Fin n}
    (hx : x ∈ D.parts i) (hy : y ∈ D.parts i) :
    ¬ supercriticalMediumIsSampledCrossPair w x y := by
  rintro ⟨e, h | h⟩
  · have hb := (mem_supercriticalMediumCrossBlock w e _).mp h
    have hil := D.mem_part_unique hx
      (supercriticalMediumSampledPart_subset w e.left hb.1)
    have hir := D.mem_part_unique hy
      (supercriticalMediumSampledPart_subset w e.right hb.2)
    exact e.left_ne_right (hil.symm.trans hir)
  · have hb := (mem_supercriticalMediumCrossBlock w e _).mp h
    have hir := D.mem_part_unique hx
      (supercriticalMediumSampledPart_subset w e.right hb.2)
    have hil := D.mem_part_unique hy
      (supercriticalMediumSampledPart_subset w e.left hb.1)
    exact e.left_ne_right (hil.symm.trans hir)

/-- The witness incidence pattern is literally fixed by every outcome. -/
theorem supercriticalMediumOutcomeGraph_adj_witness
    {k n : ℕ} {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    (w : SupercriticalMediumWitness G α D)
    (S : (supercriticalMediumFixedModel w).Sample) (x : Fin n) :
    (supercriticalMediumOutcomeGraph w S).Adj w.vertex x ↔
      G.Adj w.vertex x :=
  supercriticalMediumOutcomeGraph_adj_of_not_sampled w S
    (not_supercriticalMediumIsSampledCrossPair_witness_left w x)

/-- Arbitrary cross-block outcomes preserve the combined defect graph
exactly; this is the formal symmetric-difference-`T` completion statement. -/
theorem combinedSupercriticalDefectGraph_supercriticalMediumOutcomeGraph
    {k n : ℕ} {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    (w : SupercriticalMediumWitness G α D)
    (S : (supercriticalMediumFixedModel w).Sample) :
    combinedSupercriticalDefectGraph
        (supercriticalMediumOutcomeGraph w S) D =
      combinedSupercriticalDefectGraph G D := by
  ext x y
  rcases D.sparse_or_existsUnique_part x with hxs | ⟨i, hxi, _⟩
  · rcases D.sparse_or_existsUnique_part y with hys | ⟨j, hyj, _⟩
    · have hout := supercriticalMediumOutcomeGraph_adj_of_not_sampled
          w S (not_supercriticalMediumIsSampledCrossPair_of_mem_sparse_right
            w (x := x) hys)
      exact (combinedSupercriticalDefectGraph_adj_of_mem_sparse
        (supercriticalMediumOutcomeGraph w S) D hxs hys).trans
          (hout.trans
            (combinedSupercriticalDefectGraph_adj_of_mem_sparse
              G D hxs hys).symm)
    · have hnot :
          ¬ supercriticalMediumIsSampledCrossPair w y x :=
        not_supercriticalMediumIsSampledCrossPair_of_mem_sparse_right w hxs
      have hout : (supercriticalMediumOutcomeGraph w S).Adj x y ↔
          G.Adj x y := by
        rw [(supercriticalMediumOutcomeGraph w S).adj_comm, G.adj_comm]
        exact supercriticalMediumOutcomeGraph_adj_of_not_sampled w S hnot
      have hleft := combinedSupercriticalDefectGraph_adj_support_sparse
        (supercriticalMediumOutcomeGraph w S) D
          (D.part_subset_support j hyj) hxs
      have hright := combinedSupercriticalDefectGraph_adj_support_sparse
        G D (D.part_subset_support j hyj) hxs
      rw [(combinedSupercriticalDefectGraph
        (supercriticalMediumOutcomeGraph w S) D).adj_comm,
        (combinedSupercriticalDefectGraph G D).adj_comm]
      have hout' : (supercriticalMediumOutcomeGraph w S).Adj y x ↔
          G.Adj y x := by
        rw [(supercriticalMediumOutcomeGraph w S).adj_comm, G.adj_comm]
        exact hout
      exact hleft.trans (hout'.trans hright.symm)
  · rcases D.sparse_or_existsUnique_part y with hys | ⟨j, hyj, _⟩
    · have hout := supercriticalMediumOutcomeGraph_adj_of_not_sampled
          w S (not_supercriticalMediumIsSampledCrossPair_of_mem_sparse_right
            w (x := x) hys)
      exact (combinedSupercriticalDefectGraph_adj_support_sparse
        (supercriticalMediumOutcomeGraph w S) D
          (D.part_subset_support i hxi) hys).trans
          (hout.trans
            (combinedSupercriticalDefectGraph_adj_support_sparse
              G D (D.part_subset_support i hxi) hys).symm)
    · by_cases hij : i = j
      · subst j
        have hnot :=
          not_supercriticalMediumIsSampledCrossPair_of_mem_same_part
            w i hxi hyj
        have hout := supercriticalMediumOutcomeGraph_adj_of_not_sampled
          w S hnot
        have hleft :=
          combinedSupercriticalDefectGraph_adj_of_mem_same_part
            (supercriticalMediumOutcomeGraph w S) D i hxi hyj
        have hright :=
          combinedSupercriticalDefectGraph_adj_of_mem_same_part
            G D i hxi hyj
        exact hleft.trans
          ((and_congr Iff.rfl (not_congr hout)).trans hright.symm)
      · constructor
        · exact fun h ↦ False.elim
            (combinedSupercriticalDefectGraph_not_adj_of_mem_distinct_parts
              (supercriticalMediumOutcomeGraph w S) D hij hxi hyj h)
        · exact fun h ↦ False.elim
            (combinedSupercriticalDefectGraph_not_adj_of_mem_distinct_parts
              G D hij hxi hyj h)

theorem supercriticalMediumIsSelectedCrossPair_iff_mem_block
    {k n : ℕ} {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    (w : SupercriticalMediumWitness G α D)
    (S : (supercriticalMediumFixedModel w).Sample)
    (e : SupercriticalPartPair k) {x y : Fin n}
    (hblock : (x, y) ∈ supercriticalMediumCrossBlock w e) :
    supercriticalMediumIsSelectedCrossPair w S x y ↔
      (x, y) ∈ (supercriticalMediumFixedModel w).selectedInBlock S e := by
  constructor
  · rintro ⟨f, h | h⟩
    · by_cases hfe : f = e
      · simpa [hfe] using h
      · have hfblock :=
          (supercriticalMediumFixedModel w).selectedInBlock_subset S f h
        have hd := supercriticalMediumCrossBlocks_pairwiseDisjoint w
          (Set.mem_univ e) (Set.mem_univ f) (Ne.symm hfe)
        exact False.elim ((Finset.disjoint_left.mp hd) hblock hfblock)
    · have he := (mem_supercriticalMediumCrossBlock w e _).mp hblock
      have hfblock :=
        (supercriticalMediumFixedModel w).selectedInBlock_subset S f h
      have hf := (mem_supercriticalMediumCrossBlock w f _).mp hfblock
      have hrightLeft : e.right = f.left := D.mem_part_unique
        (supercriticalMediumSampledPart_subset w e.right he.2)
        (supercriticalMediumSampledPart_subset w f.left hf.1)
      have hleftRight : e.left = f.right := D.mem_part_unique
        (supercriticalMediumSampledPart_subset w e.left he.1)
        (supercriticalMediumSampledPart_subset w f.right hf.2)
      exfalso
      have hback : f.right < f.left := by
        simpa [hleftRight, hrightLeft] using e.left_lt_right
      exact (lt_asymm f.left_lt_right hback)
  · exact fun h ↦ ⟨e, Or.inl h⟩

theorem supercriticalMediumOutcomeGraph_interedges_sampled
    {k n : ℕ} {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    (w : SupercriticalMediumWitness G α D)
    (S : (supercriticalMediumFixedModel w).Sample)
    (e : SupercriticalPartPair k) :
    (supercriticalMediumOutcomeGraph w S).interedges
        (supercriticalMediumSampledPart w e.left)
        (supercriticalMediumSampledPart w e.right) =
      (supercriticalMediumFixedModel w).selectedInBlock S e := by
  ext xy
  constructor
  · intro hxy
    have hmem := (SimpleGraph.mem_interedges_iff
      (supercriticalMediumOutcomeGraph w S)).mp hxy
    have hblock : xy ∈ supercriticalMediumCrossBlock w e :=
      (mem_supercriticalMediumCrossBlock w e xy).mpr
        ⟨hmem.1, hmem.2.1⟩
    have hsampled :
        supercriticalMediumIsSampledCrossPair w xy.1 xy.2 :=
      ⟨e, Or.inl hblock⟩
    have hselected :=
      (supercriticalMediumOutcomeGraph_adj_of_sampled w S hsampled).mp
        hmem.2.2
    exact (supercriticalMediumIsSelectedCrossPair_iff_mem_block
      w S e hblock).mp hselected
  · intro hxy
    have hblock :=
      (supercriticalMediumFixedModel w).selectedInBlock_subset S e hxy
    have hmem := (mem_supercriticalMediumCrossBlock w e xy).mp hblock
    have hsampled :
        supercriticalMediumIsSampledCrossPair w xy.1 xy.2 :=
      ⟨e, Or.inl hblock⟩
    refine (SimpleGraph.mem_interedges_iff
      (supercriticalMediumOutcomeGraph w S)).mpr ⟨hmem.1, hmem.2, ?_⟩
    apply (supercriticalMediumOutcomeGraph_adj_of_sampled w S hsampled).mpr
    exact (supercriticalMediumIsSelectedCrossPair_iff_mem_block
      w S e hblock).mpr hxy

@[simp] theorem card_supercriticalMediumOutcomeGraph_interedges_sampled
    {k n : ℕ} {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    (w : SupercriticalMediumWitness G α D)
    (S : (supercriticalMediumFixedModel w).Sample)
    (e : SupercriticalPartPair k) :
    ((supercriticalMediumOutcomeGraph w S).interedges
        (supercriticalMediumSampledPart w e.left)
        (supercriticalMediumSampledPart w e.right)).card =
      supercriticalMediumAdjustedQuota w e := by
  rw [supercriticalMediumOutcomeGraph_interedges_sampled,
    DenseGraph.FixedCardinalityBlockModel.card_selectedInBlock]
  rfl

theorem mem_supercriticalMediumSampledPart_of_mem_of_ne
    {k n : ℕ} {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    (w : SupercriticalMediumWitness G α D) {j : Fin (k - 1)}
    {x : Fin n} (hx : x ∈ D.parts j) (hxv : x ≠ w.vertex) :
    x ∈ supercriticalMediumSampledPart w j := by
  unfold supercriticalMediumSampledPart
  split_ifs
  · exact Finset.mem_erase.mpr ⟨hxv, hx⟩
  · exact hx
  · exact hx

theorem eq_vertex_of_mem_part_of_not_mem_sampledPart
    {k n : ℕ} {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    (w : SupercriticalMediumWitness G α D) {j : Fin (k - 1)}
    {x : Fin n} (hx : x ∈ D.parts j)
    (hxs : x ∉ supercriticalMediumSampledPart w j) :
    x = w.vertex := by
  by_contra hxv
  exact hxs (mem_supercriticalMediumSampledPart_of_mem_of_ne w hx hxv)

/-- The exact oriented cross-edge subset cut out by a graph in one sampled
block, represented in the subtype expected by the fixed-cardinality model. -/
def supercriticalMediumGraphBlockSelection
    {k n : ℕ} {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    (w : SupercriticalMediumWitness G α D)
    (H : SimpleGraph (Fin n)) (e : SupercriticalPartPair k) :
    Finset ↑((supercriticalMediumFixedModel w).block e) :=
  Finset.univ.filter fun xy ↦ H.Adj xy.1.1 xy.1.2

theorem supercriticalMediumGraphBlockSelection_map
    {k n : ℕ} {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    (w : SupercriticalMediumWitness G α D)
    (H : SimpleGraph (Fin n)) (e : SupercriticalPartPair k) :
    (supercriticalMediumGraphBlockSelection w H e).map
        ⟨Subtype.val, Subtype.val_injective⟩ =
      H.interedges
        (supercriticalMediumSampledPart w e.left)
        (supercriticalMediumSampledPart w e.right) := by
  classical
  ext xy
  simp [supercriticalMediumGraphBlockSelection,
    SimpleGraph.mem_interedges_iff]
  change (H.Adj xy.1 xy.2 ∧
      xy ∈ supercriticalMediumCrossBlock w e) ↔
    (xy.1 ∈ supercriticalMediumSampledPart w e.left ∧
      xy.2 ∈ supercriticalMediumSampledPart w e.right ∧
        H.Adj xy.1 xy.2)
  rw [mem_supercriticalMediumCrossBlock]
  tauto

@[simp] theorem card_supercriticalMediumGraphBlockSelection
    {k n : ℕ} {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    (w : SupercriticalMediumWitness G α D)
    (H : SimpleGraph (Fin n)) (e : SupercriticalPartPair k) :
    (supercriticalMediumGraphBlockSelection w H e).card =
      (H.interedges
        (supercriticalMediumSampledPart w e.left)
        (supercriticalMediumSampledPart w e.right)).card := by
  rw [← supercriticalMediumGraphBlockSelection_map w H e,
    Finset.card_map]

/-- The portion of a full cross cell which is fixed rather than sampled,
for a graph not necessarily equal to the exemplar carried by `w`. -/
def supercriticalMediumFixedCrossEdgesForGraph
    {k n : ℕ} {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    (w : SupercriticalMediumWitness G α D)
    (H : SimpleGraph (Fin n)) (e : SupercriticalPartPair k) :
    Finset (Fin n × Fin n) :=
  H.interedges (D.parts e.left) (D.parts e.right) \
    supercriticalMediumCrossBlock w e

theorem interedges_sampled_eq_inter_full_crossBlock_forGraph
    {k n : ℕ} {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    (w : SupercriticalMediumWitness G α D)
    (H : SimpleGraph (Fin n)) (e : SupercriticalPartPair k) :
    H.interedges
        (supercriticalMediumSampledPart w e.left)
        (supercriticalMediumSampledPart w e.right) =
      H.interedges (D.parts e.left) (D.parts e.right) ∩
        supercriticalMediumCrossBlock w e := by
  ext xy
  simp only [SimpleGraph.mem_interedges_iff, Finset.mem_inter,
    mem_supercriticalMediumCrossBlock]
  constructor
  · rintro ⟨hx, hy, hH⟩
    exact ⟨⟨supercriticalMediumSampledPart_subset w _ hx,
      supercriticalMediumSampledPart_subset w _ hy, hH⟩, hx, hy⟩
  · rintro ⟨⟨_, _, hH⟩, hx, hy⟩
    exact ⟨hx, hy, hH⟩

theorem card_sampled_add_card_fixedCrossEdgesForGraph
    {k n : ℕ} {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    (w : SupercriticalMediumWitness G α D)
    (H : SimpleGraph (Fin n)) (e : SupercriticalPartPair k) :
    (H.interedges
        (supercriticalMediumSampledPart w e.left)
        (supercriticalMediumSampledPart w e.right)).card +
      (supercriticalMediumFixedCrossEdgesForGraph w H e).card =
        (H.interedges (D.parts e.left) (D.parts e.right)).card := by
  rw [interedges_sampled_eq_inter_full_crossBlock_forGraph,
    supercriticalMediumFixedCrossEdgesForGraph]
  exact Finset.card_inter_add_card_sdiff _ _

theorem supercriticalMediumFixedCrossEdgesForGraph_eq_of_incident
    {k n : ℕ} {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    (w : SupercriticalMediumWitness G α D)
    (H K : SimpleGraph (Fin n))
    (hincident : ∀ x, H.Adj w.vertex x ↔ K.Adj w.vertex x)
    (e : SupercriticalPartPair k) :
    supercriticalMediumFixedCrossEdgesForGraph w H e =
      supercriticalMediumFixedCrossEdgesForGraph w K e := by
  classical
  ext xy
  by_cases hblock : xy ∈ supercriticalMediumCrossBlock w e
  · simp [supercriticalMediumFixedCrossEdgesForGraph, hblock]
  · have hnot :
        xy.1 ∉ supercriticalMediumSampledPart w e.left ∨
          xy.2 ∉ supercriticalMediumSampledPart w e.right := by
      by_cases hx : xy.1 ∈ supercriticalMediumSampledPart w e.left
      · exact Or.inr fun hy ↦ hblock
          ((mem_supercriticalMediumCrossBlock w e xy).mpr ⟨hx, hy⟩)
      · exact Or.inl hx
    simp only [supercriticalMediumFixedCrossEdgesForGraph,
      Finset.mem_sdiff, hblock, not_false_eq_true, and_true,
      SimpleGraph.mem_interedges_iff]
    constructor
    · rintro ⟨hx, hy, hH⟩
      refine ⟨hx, hy, ?_⟩
      rcases hnot with hxs | hys
      · have hxv := eq_vertex_of_mem_part_of_not_mem_sampledPart w hx hxs
        rw [hxv] at hH ⊢
        exact (hincident xy.2).mp hH
      · have hyv := eq_vertex_of_mem_part_of_not_mem_sampledPart w hy hys
        rw [hyv] at hH ⊢
        exact (K.adj_comm _ _).mpr
          ((hincident xy.1).mp ((H.adj_comm _ _).mp hH))
    · rintro ⟨hx, hy, hK⟩
      refine ⟨hx, hy, ?_⟩
      rcases hnot with hxs | hys
      · have hxv := eq_vertex_of_mem_part_of_not_mem_sampledPart w hx hxs
        rw [hxv] at hK ⊢
        exact (hincident xy.2).mpr hK
      · have hyv := eq_vertex_of_mem_part_of_not_mem_sampledPart w hy hys
        rw [hyv] at hK ⊢
        exact (H.adj_comm _ _).mpr
          ((hincident xy.1).mpr ((K.adj_comm _ _).mp hK))

/-- Arbitrary exact-size outcomes preserve the original full cross-edge
profile, including the fixed witness-incident contribution. -/
theorem crossEdgeProfile_supercriticalMediumOutcomeGraph
    {k n : ℕ} {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    (w : SupercriticalMediumWitness G α D)
    (S : (supercriticalMediumFixedModel w).Sample) :
    crossEdgeProfile (supercriticalMediumOutcomeGraph w S) D =
      crossEdgeProfile G D := by
  apply SupercriticalEdgeProfile.ext
  funext e
  simp only [crossEdgeProfile_count]
  have hfixed :=
    supercriticalMediumFixedCrossEdgesForGraph_eq_of_incident
      w (supercriticalMediumOutcomeGraph w S) G
        (supercriticalMediumOutcomeGraph_adj_witness w S) e
  have hout := card_sampled_add_card_fixedCrossEdgesForGraph
    w (supercriticalMediumOutcomeGraph w S) e
  have hG := card_sampled_add_card_fixedCrossEdgesForGraph w G e
  rw [card_supercriticalMediumOutcomeGraph_interedges_sampled, hfixed] at hout
  rw [supercriticalMediumAdjustedQuota] at hout
  omega

/-- Equal full cross profiles and equal fixed incident data force equal
adjusted quotas after the witness is removed. -/
theorem card_sampled_interedges_eq_adjustedQuota_of_profile_incident
    {k n : ℕ} {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    (w : SupercriticalMediumWitness G α D)
    (H : SimpleGraph (Fin n))
    (hprofile : crossEdgeProfile H D = crossEdgeProfile G D)
    (hincident : ∀ x, H.Adj w.vertex x ↔ G.Adj w.vertex x)
    (e : SupercriticalPartPair k) :
    (H.interedges
        (supercriticalMediumSampledPart w e.left)
        (supercriticalMediumSampledPart w e.right)).card =
      supercriticalMediumAdjustedQuota w e := by
  have hfixed :=
    supercriticalMediumFixedCrossEdgesForGraph_eq_of_incident
      w H G hincident e
  have htotal :
      (H.interedges (D.parts e.left) (D.parts e.right)).card =
        (G.interedges (D.parts e.left) (D.parts e.right)).card := by
    have h := congrArg (fun p : SupercriticalEdgeProfile D ↦ p.count e) hprofile
    simpa only [crossEdgeProfile_count] using h
  have hH := card_sampled_add_card_fixedCrossEdgesForGraph w H e
  have hG := card_sampled_add_card_fixedCrossEdgesForGraph w G e
  rw [hfixed, htotal] at hH
  rw [supercriticalMediumAdjustedQuota]
  omega

/-- Encode a graph with the exemplar's adjusted quotas as one exact
fixed-cardinality sample. -/
def supercriticalMediumSampleOfGraph
    {k n : ℕ} {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    (w : SupercriticalMediumWitness G α D)
    (H : SimpleGraph (Fin n))
    (hquota : ∀ e : SupercriticalPartPair k,
      (H.interedges
        (supercriticalMediumSampledPart w e.left)
        (supercriticalMediumSampledPart w e.right)).card =
          supercriticalMediumAdjustedQuota w e) :
    (supercriticalMediumFixedModel w).Sample :=
  fun e ↦ ⟨supercriticalMediumGraphBlockSelection w H e, by
    rw [Finset.mem_powersetCard]
    refine ⟨Finset.subset_univ _, ?_⟩
    change (supercriticalMediumGraphBlockSelection w H e).card =
      supercriticalMediumAdjustedQuota w e
    simpa using hquota e⟩

theorem supercriticalMediumFixedModel_selectedInBlock_sampleOfGraph
    {k n : ℕ} {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    (w : SupercriticalMediumWitness G α D)
    (H : SimpleGraph (Fin n))
    (hquota : ∀ e : SupercriticalPartPair k,
      (H.interedges
        (supercriticalMediumSampledPart w e.left)
        (supercriticalMediumSampledPart w e.right)).card =
          supercriticalMediumAdjustedQuota w e)
    (e : SupercriticalPartPair k) :
    (supercriticalMediumFixedModel w).selectedInBlock
        (supercriticalMediumSampleOfGraph w H hquota) e =
      H.interedges
        (supercriticalMediumSampledPart w e.left)
        (supercriticalMediumSampledPart w e.right) := by
  exact supercriticalMediumGraphBlockSelection_map w H e

theorem supercriticalMediumIsSelectedCrossPair_sampleOfGraph_iff
    {k n : ℕ} {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    (w : SupercriticalMediumWitness G α D)
    (H : SimpleGraph (Fin n))
    (hquota : ∀ e : SupercriticalPartPair k,
      (H.interedges
        (supercriticalMediumSampledPart w e.left)
        (supercriticalMediumSampledPart w e.right)).card =
          supercriticalMediumAdjustedQuota w e)
    {x y : Fin n} (hxy : supercriticalMediumIsSampledCrossPair w x y) :
    supercriticalMediumIsSelectedCrossPair w
        (supercriticalMediumSampleOfGraph w H hquota) x y ↔ H.Adj x y := by
  constructor
  · rintro ⟨e, h | h⟩
    · rw [supercriticalMediumFixedModel_selectedInBlock_sampleOfGraph]
        at h
      exact ((SimpleGraph.mem_interedges_iff H).mp h).2.2
    · rw [supercriticalMediumFixedModel_selectedInBlock_sampleOfGraph]
        at h
      exact (H.adj_comm y x).mp
        ((SimpleGraph.mem_interedges_iff H).mp h).2.2
  · intro hH
    obtain ⟨e, h | h⟩ := hxy
    · refine ⟨e, Or.inl ?_⟩
      rw [supercriticalMediumFixedModel_selectedInBlock_sampleOfGraph]
      have hb := (mem_supercriticalMediumCrossBlock w e (x, y)).mp h
      exact (SimpleGraph.mem_interedges_iff H).mpr ⟨hb.1, hb.2, hH⟩
    · refine ⟨e, Or.inr ?_⟩
      rw [supercriticalMediumFixedModel_selectedInBlock_sampleOfGraph]
      have hb := (mem_supercriticalMediumCrossBlock w e (y, x)).mp h
      exact (SimpleGraph.mem_interedges_iff H).mpr
        ⟨hb.1, hb.2, (H.adj_comm x y).mp hH⟩

/-! ## Consequences of belonging to the same raw refinement -/

theorem combinedSupercriticalDefectGraph_eq_of_mediumRefinementKey_eq
    {k : ℕ} {hk : 3 ≤ k} {gamma : ℝ}
    {hgamma : gamma ∈ Set.Ico (gammaK k) 1}
    {alpha : ℝ} {halpha : 0 < alpha}
    {m n : ℕ} {tau : ℝ} {hn : k - 1 ≤ n}
    {D : SupercriticalDivision k (Fin n)}
    (H K : SupercriticalMediumGraph
      k hk gamma hgamma alpha m n tau hn D)
    (hkey : supercriticalMediumRefinementKeyOf halpha H =
      supercriticalMediumRefinementKeyOf halpha K) :
    combinedSupercriticalDefectGraph H.1 D =
      combinedSupercriticalDefectGraph K.1 D := by
  have h := congrArg
    (SupercriticalMediumRefinementKey.defect (D := D)) hkey
  simpa [supercriticalMediumRefinementKeyOf] using h

theorem crossEdgeProfile_eq_of_mediumRefinementKey_eq
    {k : ℕ} {hk : 3 ≤ k} {gamma : ℝ}
    {hgamma : gamma ∈ Set.Ico (gammaK k) 1}
    {alpha : ℝ} {halpha : 0 < alpha}
    {m n : ℕ} {tau : ℝ} {hn : k - 1 ≤ n}
    {D : SupercriticalDivision k (Fin n)}
    (H K : SupercriticalMediumGraph
      k hk gamma hgamma alpha m n tau hn D)
    (hkey : supercriticalMediumRefinementKeyOf halpha H =
      supercriticalMediumRefinementKeyOf halpha K) :
    crossEdgeProfile H.1 D = crossEdgeProfile K.1 D := by
  have h := congrArg
    (SupercriticalMediumRefinementKey.profile (D := D)) hkey
  simpa [supercriticalMediumRefinementKeyOf] using h

theorem mediumWitness_vertex_eq_of_refinementKey_eq
    {k : ℕ} {hk : 3 ≤ k} {gamma : ℝ}
    {hgamma : gamma ∈ Set.Ico (gammaK k) 1}
    {alpha : ℝ} {halpha : 0 < alpha}
    {m n : ℕ} {tau : ℝ} {hn : k - 1 ≤ n}
    {D : SupercriticalDivision k (Fin n)}
    (H K : SupercriticalMediumGraph
      k hk gamma hgamma alpha m n tau hn D)
    (hkey : supercriticalMediumRefinementKeyOf halpha H =
      supercriticalMediumRefinementKeyOf halpha K) :
    (supercriticalMediumWitnessOfMem halpha H.2).vertex =
      (supercriticalMediumWitnessOfMem halpha K.2).vertex := by
  have h := congrArg
    (SupercriticalMediumRefinementKey.vertex (D := D)) hkey
  simpa [supercriticalMediumRefinementKeyOf] using h

theorem mediumWitness_part_eq_of_refinementKey_eq
    {k : ℕ} {hk : 3 ≤ k} {gamma : ℝ}
    {hgamma : gamma ∈ Set.Ico (gammaK k) 1}
    {alpha : ℝ} {halpha : 0 < alpha}
    {m n : ℕ} {tau : ℝ} {hn : k - 1 ≤ n}
    {D : SupercriticalDivision k (Fin n)}
    (H K : SupercriticalMediumGraph
      k hk gamma hgamma alpha m n tau hn D)
    (hkey : supercriticalMediumRefinementKeyOf halpha H =
      supercriticalMediumRefinementKeyOf halpha K) :
    (supercriticalMediumWitnessOfMem halpha H.2).part =
      (supercriticalMediumWitnessOfMem halpha K.2).part := by
  have h := congrArg
    (SupercriticalMediumRefinementKey.part (D := D)) hkey
  simpa [supercriticalMediumRefinementKeyOf] using h

theorem adj_witness_iff_of_mediumRefinementKey_eq
    {k : ℕ} {hk : 3 ≤ k} {gamma : ℝ}
    {hgamma : gamma ∈ Set.Ico (gammaK k) 1}
    {alpha : ℝ} {halpha : 0 < alpha}
    {m n : ℕ} {tau : ℝ} {hn : k - 1 ≤ n}
    {D : SupercriticalDivision k (Fin n)}
    (H K : SupercriticalMediumGraph
      k hk gamma hgamma alpha m n tau hn D)
    (hkey : supercriticalMediumRefinementKeyOf halpha H =
      supercriticalMediumRefinementKeyOf halpha K)
    (x : Fin n) :
    H.1.Adj (supercriticalMediumWitnessOfMem halpha K.2).vertex x ↔
      K.1.Adj (supercriticalMediumWitnessOfMem halpha K.2).vertex x := by
  have hv := mediumWitness_vertex_eq_of_refinementKey_eq H K hkey
  have hi := congrArg
    (SupercriticalMediumRefinementKey.incident (D := D)) hkey
  simp only [supercriticalMediumRefinementKeyOf] at hi
  rw [hv] at hi
  have hmem := Finset.ext_iff.mp hi x
  simpa only [mem_supercriticalMediumIncidentPattern] using hmem

theorem card_sampled_interedges_eq_adjustedQuota_of_refinementKey_eq
    {k : ℕ} {hk : 3 ≤ k} {gamma : ℝ}
    {hgamma : gamma ∈ Set.Ico (gammaK k) 1}
    {alpha : ℝ} {halpha : 0 < alpha}
    {m n : ℕ} {tau : ℝ} {hn : k - 1 ≤ n}
    {D : SupercriticalDivision k (Fin n)}
    (H K : SupercriticalMediumGraph
      k hk gamma hgamma alpha m n tau hn D)
    (hkey : supercriticalMediumRefinementKeyOf halpha H =
      supercriticalMediumRefinementKeyOf halpha K)
    (e : SupercriticalPartPair k) :
    let w := supercriticalMediumWitnessOfMem halpha K.2
    (H.1.interedges
        (supercriticalMediumSampledPart w e.left)
        (supercriticalMediumSampledPart w e.right)).card =
      supercriticalMediumAdjustedQuota w e := by
  apply card_sampled_interedges_eq_adjustedQuota_of_profile_incident
  · exact crossEdgeProfile_eq_of_mediumRefinementKey_eq H K hkey
  · exact adj_witness_iff_of_mediumRefinementKey_eq H K hkey

theorem adj_iff_of_combinedDefect_eq_of_mem_same_part
    {k n : ℕ} {D : SupercriticalDivision k (Fin n)}
    {H K : SimpleGraph (Fin n)}
    (hdefect : combinedSupercriticalDefectGraph H D =
      combinedSupercriticalDefectGraph K D)
    (i : Fin (k - 1)) {x y : Fin n}
    (hx : x ∈ D.parts i) (hy : y ∈ D.parts i) :
    H.Adj x y ↔ K.Adj x y := by
  have hH :=
    combinedSupercriticalDefectGraph_adj_of_mem_same_part H D i hx hy
  have hK :=
    combinedSupercriticalDefectGraph_adj_of_mem_same_part K D i hx hy
  rw [hdefect] at hH
  by_cases hxy : x = y
  · subst y
    simp
  · constructor
    · intro hHadj
      by_contra hKadj
      have hT := hK.mpr ⟨hxy, hKadj⟩
      exact (hH.mp hT).2 hHadj
    · intro hKadj
      by_contra hHadj
      have hT := hH.mpr ⟨hxy, hHadj⟩
      exact (hK.mp hT).2 hKadj

theorem adj_iff_of_combinedDefect_eq_of_support_sparse
    {k n : ℕ} {D : SupercriticalDivision k (Fin n)}
    {H K : SimpleGraph (Fin n)}
    (hdefect : combinedSupercriticalDefectGraph H D =
      combinedSupercriticalDefectGraph K D)
    {x y : Fin n} (hx : x ∈ D.support) (hy : y ∈ D.sparse) :
    H.Adj x y ↔ K.Adj x y := by
  have hH := combinedSupercriticalDefectGraph_adj_support_sparse H D hx hy
  have hK := combinedSupercriticalDefectGraph_adj_support_sparse K D hx hy
  rw [hdefect] at hH
  exact hH.symm.trans hK

theorem adj_iff_of_combinedDefect_eq_of_mem_sparse
    {k n : ℕ} {D : SupercriticalDivision k (Fin n)}
    {H K : SimpleGraph (Fin n)}
    (hdefect : combinedSupercriticalDefectGraph H D =
      combinedSupercriticalDefectGraph K D)
    {x y : Fin n} (hx : x ∈ D.sparse) (hy : y ∈ D.sparse) :
    H.Adj x y ↔ K.Adj x y := by
  have hH := combinedSupercriticalDefectGraph_adj_of_mem_sparse H D hx hy
  have hK := combinedSupercriticalDefectGraph_adj_of_mem_sparse K D hx hy
  rw [hdefect] at hH
  exact hH.symm.trans hK

/-- Once the combined defect and witness incidence are fixed, two graphs can
differ only on the sampled cross blocks. -/
theorem adj_iff_of_not_supercriticalMediumIsSampledCrossPair
    {k n : ℕ} {K : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    (w : SupercriticalMediumWitness K α D)
    (H : SimpleGraph (Fin n))
    (hdefect : combinedSupercriticalDefectGraph H D =
      combinedSupercriticalDefectGraph K D)
    (hincident : ∀ z, H.Adj w.vertex z ↔ K.Adj w.vertex z)
    {x y : Fin n} (hnot :
      ¬ supercriticalMediumIsSampledCrossPair w x y) :
    H.Adj x y ↔ K.Adj x y := by
  by_cases hxv : x = w.vertex
  · subst x
    exact hincident y
  by_cases hyv : y = w.vertex
  · subst y
    rw [H.adj_comm, K.adj_comm]
    exact hincident x
  rcases D.sparse_or_existsUnique_part x with hxs | ⟨i, hxi, _⟩
  · rcases D.sparse_or_existsUnique_part y with hys | ⟨j, hyj, _⟩
    · exact adj_iff_of_combinedDefect_eq_of_mem_sparse hdefect hxs hys
    · rw [H.adj_comm, K.adj_comm]
      exact adj_iff_of_combinedDefect_eq_of_support_sparse hdefect
        (D.part_subset_support j hyj) hxs
  · rcases D.sparse_or_existsUnique_part y with hys | ⟨j, hyj, _⟩
    · exact adj_iff_of_combinedDefect_eq_of_support_sparse hdefect
        (D.part_subset_support i hxi) hys
    · by_cases hij : i = j
      · subst j
        exact adj_iff_of_combinedDefect_eq_of_mem_same_part
          hdefect i hxi hyj
      · exfalso
        apply hnot
        by_cases hijlt : i < j
        · let e : SupercriticalPartPair k := ⟨i, j, hijlt⟩
          refine ⟨e, Or.inl ?_⟩
          rw [mem_supercriticalMediumCrossBlock]
          exact ⟨
            mem_supercriticalMediumSampledPart_of_mem_of_ne w hxi hxv,
            mem_supercriticalMediumSampledPart_of_mem_of_ne w hyj hyv⟩
        · have hji : j < i :=
            lt_of_le_of_ne (le_of_not_gt hijlt) (Ne.symm hij)
          let e : SupercriticalPartPair k := ⟨j, i, hji⟩
          refine ⟨e, Or.inr ?_⟩
          rw [mem_supercriticalMediumCrossBlock]
          exact ⟨
            mem_supercriticalMediumSampledPart_of_mem_of_ne w hyj hyv,
            mem_supercriticalMediumSampledPart_of_mem_of_ne w hxi hxv⟩

/-- Exact reconstruction: changing the selected cross coordinates and
retaining all fixed data recovers the target graph. -/
theorem supercriticalMediumOutcomeGraph_eq_of_fixedData
    {k n : ℕ} {K : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    (w : SupercriticalMediumWitness K α D)
    (H : SimpleGraph (Fin n))
    (S : (supercriticalMediumFixedModel w).Sample)
    (hdefect : combinedSupercriticalDefectGraph H D =
      combinedSupercriticalDefectGraph K D)
    (hincident : ∀ z, H.Adj w.vertex z ↔ K.Adj w.vertex z)
    (hselected : ∀ {x y : Fin n},
      supercriticalMediumIsSampledCrossPair w x y →
      (supercriticalMediumIsSelectedCrossPair w S x y ↔ H.Adj x y)) :
    supercriticalMediumOutcomeGraph w S = H := by
  ext x y
  by_cases hxy : supercriticalMediumIsSampledCrossPair w x y
  · exact (supercriticalMediumOutcomeGraph_adj_of_sampled w S hxy).trans
      (hselected hxy)
  · exact (supercriticalMediumOutcomeGraph_adj_of_not_sampled w S hxy).trans
      (adj_iff_of_not_supercriticalMediumIsSampledCrossPair
        w H hdefect hincident hxy).symm

/-! ## Encoding each nonempty refined family -/

/-- The subtype fiber attached to the raw key of a chosen exemplar. -/
abbrev SupercriticalMediumRefinedGraph
    (k : ℕ) (hk : 3 ≤ k) (gamma : ℝ)
    (hgamma : gamma ∈ Set.Ico (gammaK k) 1)
    (alpha : ℝ) (halpha : 0 < alpha)
    (m n : ℕ) (tau : ℝ) (hn : k - 1 ≤ n)
    (D : SupercriticalDivision k (Fin n))
    (K : SupercriticalMediumGraph
      k hk gamma hgamma alpha m n tau hn D) :=
  ↑(supercriticalMediumRefinedSubtypeFinset
    k hk gamma hgamma alpha halpha m n tau hn
      (supercriticalMediumRefinementKeyOf halpha K))

theorem supercriticalMediumRefinedGraph_key_eq
    {k : ℕ} {hk : 3 ≤ k} {gamma : ℝ}
    {hgamma : gamma ∈ Set.Ico (gammaK k) 1}
    {alpha : ℝ} {halpha : 0 < alpha}
    {m n : ℕ} {tau : ℝ} {hn : k - 1 ≤ n}
    {D : SupercriticalDivision k (Fin n)}
    (K : SupercriticalMediumGraph
      k hk gamma hgamma alpha m n tau hn D)
    (H : SupercriticalMediumRefinedGraph
      k hk gamma hgamma alpha halpha m n tau hn D K) :
    supercriticalMediumRefinementKeyOf halpha H.1 =
      supercriticalMediumRefinementKeyOf halpha K := by
  exact mem_supercriticalMediumRefinedSubtypeFinset.mp H.2

theorem supercriticalMediumRefinedGraph_adjustedQuota
    {k : ℕ} {hk : 3 ≤ k} {gamma : ℝ}
    {hgamma : gamma ∈ Set.Ico (gammaK k) 1}
    {alpha : ℝ} {halpha : 0 < alpha}
    {m n : ℕ} {tau : ℝ} {hn : k - 1 ≤ n}
    {D : SupercriticalDivision k (Fin n)}
    (K : SupercriticalMediumGraph
      k hk gamma hgamma alpha m n tau hn D)
    (H : SupercriticalMediumRefinedGraph
      k hk gamma hgamma alpha halpha m n tau hn D K)
    (e : SupercriticalPartPair k) :
    let w := supercriticalMediumWitnessOfMem halpha K.2
    (H.1.1.interedges
        (supercriticalMediumSampledPart w e.left)
        (supercriticalMediumSampledPart w e.right)).card =
      supercriticalMediumAdjustedQuota w e := by
  exact card_sampled_interedges_eq_adjustedQuota_of_refinementKey_eq
    H.1 K (supercriticalMediumRefinedGraph_key_eq K H) e

/-- The blockwise cross-edge encoding of a graph in one fixed raw refined
family. -/
def supercriticalMediumRefinedEncoding
    {k : ℕ} {hk : 3 ≤ k} {gamma : ℝ}
    {hgamma : gamma ∈ Set.Ico (gammaK k) 1}
    {alpha : ℝ} (halpha : 0 < alpha)
    {m n : ℕ} {tau : ℝ} {hn : k - 1 ≤ n}
    {D : SupercriticalDivision k (Fin n)}
    (K : SupercriticalMediumGraph
      k hk gamma hgamma alpha m n tau hn D)
    (H : SupercriticalMediumRefinedGraph
      k hk gamma hgamma alpha halpha m n tau hn D K) :
    (supercriticalMediumFixedModel
      (supercriticalMediumWitnessOfMem halpha K.2)).Sample :=
  supercriticalMediumSampleOfGraph
    (supercriticalMediumWitnessOfMem halpha K.2) H.1.1
    (supercriticalMediumRefinedGraph_adjustedQuota K H)

/-- Every graph in a raw refined family occurs as the graph reconstructed
from its fixed-cardinality cross-block sample. -/
theorem supercriticalMediumOutcomeGraph_refinedEncoding
    {k : ℕ} {hk : 3 ≤ k} {gamma : ℝ}
    {hgamma : gamma ∈ Set.Ico (gammaK k) 1}
    {alpha : ℝ} (halpha : 0 < alpha)
    {m n : ℕ} {tau : ℝ} {hn : k - 1 ≤ n}
    {D : SupercriticalDivision k (Fin n)}
    (K : SupercriticalMediumGraph
      k hk gamma hgamma alpha m n tau hn D)
    (H : SupercriticalMediumRefinedGraph
      k hk gamma hgamma alpha halpha m n tau hn D K) :
    supercriticalMediumOutcomeGraph
        (supercriticalMediumWitnessOfMem halpha K.2)
        (supercriticalMediumRefinedEncoding halpha K H) = H.1.1 := by
  let w := supercriticalMediumWitnessOfMem halpha K.2
  let hkey := supercriticalMediumRefinedGraph_key_eq K H
  apply supercriticalMediumOutcomeGraph_eq_of_fixedData
  · exact combinedSupercriticalDefectGraph_eq_of_mediumRefinementKey_eq
      H.1 K hkey
  · exact adj_witness_iff_of_mediumRefinementKey_eq H.1 K hkey
  · intro x y hxy
    exact supercriticalMediumIsSelectedCrossPair_sampleOfGraph_iff
      w H.1.1 (supercriticalMediumRefinedGraph_adjustedQuota K H) hxy

theorem exists_supercriticalMediumOutcomeGraph_eq_of_refined
    {k : ℕ} {hk : 3 ≤ k} {gamma : ℝ}
    {hgamma : gamma ∈ Set.Ico (gammaK k) 1}
    {alpha : ℝ} (halpha : 0 < alpha)
    {m n : ℕ} {tau : ℝ} {hn : k - 1 ≤ n}
    {D : SupercriticalDivision k (Fin n)}
    (K : SupercriticalMediumGraph
      k hk gamma hgamma alpha m n tau hn D)
    (H : SupercriticalMediumRefinedGraph
      k hk gamma hgamma alpha halpha m n tau hn D K) :
    ∃ S : (supercriticalMediumFixedModel
        (supercriticalMediumWitnessOfMem halpha K.2)).Sample,
      supercriticalMediumOutcomeGraph
        (supercriticalMediumWitnessOfMem halpha K.2) S = H.1.1 := by
  exact ⟨supercriticalMediumRefinedEncoding halpha K H,
    supercriticalMediumOutcomeGraph_refinedEncoding halpha K H⟩

theorem supercriticalMediumRefinedEncoding_injective
    {k : ℕ} {hk : 3 ≤ k} {gamma : ℝ}
    {hgamma : gamma ∈ Set.Ico (gammaK k) 1}
    {alpha : ℝ} (halpha : 0 < alpha)
    {m n : ℕ} {tau : ℝ} {hn : k - 1 ≤ n}
    {D : SupercriticalDivision k (Fin n)}
    (K : SupercriticalMediumGraph
      k hk gamma hgamma alpha m n tau hn D) :
    Function.Injective (supercriticalMediumRefinedEncoding halpha K) := by
  intro H H' hHH'
  apply Subtype.ext
  apply Subtype.ext
  rw [← supercriticalMediumOutcomeGraph_refinedEncoding halpha K H,
    ← supercriticalMediumOutcomeGraph_refinedEncoding halpha K H', hHH']

/-- The exact fixed-count event that the completed graph is induced-star
free.  No probability space is hidden here: this is a literal finite filter
of the exact sample type. -/
def supercriticalMediumInducedFreeSampleEvent
    {k : ℕ} {hk : 3 ≤ k} {gamma : ℝ}
    {hgamma : gamma ∈ Set.Ico (gammaK k) 1}
    {alpha : ℝ} (halpha : 0 < alpha)
    {m n : ℕ} {tau : ℝ} {hn : k - 1 ≤ n}
    {D : SupercriticalDivision k (Fin n)}
    (K : SupercriticalMediumGraph
      k hk gamma hgamma alpha m n tau hn D) :
    Finset (supercriticalMediumFixedModel
      (supercriticalMediumWitnessOfMem halpha K.2)).Sample := by
  classical
  exact Finset.univ.filter fun S ↦
    ¬ Regularity.InducedEmbeds (inducedStar k)
      (supercriticalMediumOutcomeGraph
        (supercriticalMediumWitnessOfMem halpha K.2) S)

@[simp] theorem mem_supercriticalMediumInducedFreeSampleEvent
    {k : ℕ} {hk : 3 ≤ k} {gamma : ℝ}
    {hgamma : gamma ∈ Set.Ico (gammaK k) 1}
    {alpha : ℝ} {halpha : 0 < alpha}
    {m n : ℕ} {tau : ℝ} {hn : k - 1 ≤ n}
    {D : SupercriticalDivision k (Fin n)}
    (K : SupercriticalMediumGraph
      k hk gamma hgamma alpha m n tau hn D)
    {S : (supercriticalMediumFixedModel
      (supercriticalMediumWitnessOfMem halpha K.2)).Sample} :
    S ∈ supercriticalMediumInducedFreeSampleEvent halpha K ↔
      ¬ Regularity.InducedEmbeds (inducedStar k)
        (supercriticalMediumOutcomeGraph
          (supercriticalMediumWitnessOfMem halpha K.2) S) := by
  classical
  simp [supercriticalMediumInducedFreeSampleEvent]

theorem supercriticalMediumRefinedEncoding_mem_inducedFreeEvent
    {k : ℕ} {hk : 3 ≤ k} {gamma : ℝ}
    {hgamma : gamma ∈ Set.Ico (gammaK k) 1}
    {alpha : ℝ} (halpha : 0 < alpha)
    {m n : ℕ} {tau : ℝ} {hn : k - 1 ≤ n}
    {D : SupercriticalDivision k (Fin n)}
    (K : SupercriticalMediumGraph
      k hk gamma hgamma alpha m n tau hn D)
    (H : SupercriticalMediumRefinedGraph
      k hk gamma hgamma alpha halpha m n tau hn D K) :
    supercriticalMediumRefinedEncoding halpha K H ∈
      supercriticalMediumInducedFreeSampleEvent halpha K := by
  rw [mem_supercriticalMediumInducedFreeSampleEvent,
    supercriticalMediumOutcomeGraph_refinedEncoding halpha K H]
  have hdivision :=
    (mem_supercriticalMediumDegreeGraphFinset.mp H.1.2).1
  have hclose :=
    (mem_supercriticalDivisionDefectGraphFinset.mp hdivision).1
  exact (mem_supercriticalCloseGraphFinset.mp hclose).1

/-- Injection of the entire subtype fiber into the exact induced-free
fixed-cardinality event. -/
theorem card_supercriticalMediumRefinedSubtypeFinset_le_inducedFreeEvent
    {k : ℕ} {hk : 3 ≤ k} {gamma : ℝ}
    {hgamma : gamma ∈ Set.Ico (gammaK k) 1}
    {alpha : ℝ} (halpha : 0 < alpha)
    {m n : ℕ} {tau : ℝ} {hn : k - 1 ≤ n}
    {D : SupercriticalDivision k (Fin n)}
    (K : SupercriticalMediumGraph
      k hk gamma hgamma alpha m n tau hn D) :
    (supercriticalMediumRefinedSubtypeFinset
      k hk gamma hgamma alpha halpha m n tau hn
        (supercriticalMediumRefinementKeyOf halpha K)).card ≤
      (supercriticalMediumInducedFreeSampleEvent halpha K).card := by
  classical
  let f : SupercriticalMediumRefinedGraph
      k hk gamma hgamma alpha halpha m n tau hn D K →
      ↑(supercriticalMediumInducedFreeSampleEvent halpha K) :=
    fun H ↦ ⟨supercriticalMediumRefinedEncoding halpha K H,
      supercriticalMediumRefinedEncoding_mem_inducedFreeEvent halpha K H⟩
  have hf : Function.Injective f := by
    intro H H' hHH'
    apply supercriticalMediumRefinedEncoding_injective halpha K
    exact congrArg Subtype.val hHH'
  simpa only [Fintype.card_coe] using Fintype.card_le_of_injective f hf

theorem card_supercriticalMediumRefinedGraphFinset_le_inducedFreeEvent
    {k : ℕ} {hk : 3 ≤ k} {gamma : ℝ}
    {hgamma : gamma ∈ Set.Ico (gammaK k) 1}
    {alpha : ℝ} (halpha : 0 < alpha)
    {m n : ℕ} {tau : ℝ} {hn : k - 1 ≤ n}
    {D : SupercriticalDivision k (Fin n)}
    (K : SupercriticalMediumGraph
      k hk gamma hgamma alpha m n tau hn D) :
    (supercriticalMediumRefinedGraphFinset
      k hk gamma hgamma alpha halpha m n tau hn
        (supercriticalMediumRefinementKeyOf halpha K)).card ≤
      (supercriticalMediumInducedFreeSampleEvent halpha K).card := by
  rw [card_supercriticalMediumRefinedGraphFinset]
  exact card_supercriticalMediumRefinedSubtypeFinset_le_inducedFreeEvent
    halpha K

/-- Exact refined-family counting bound: the original cross-profile
multiplicity times the fixed-cardinality induced-free event probability. -/
theorem card_supercriticalMediumRefinedGraphFinset_le_profileMultiplicity_mul_probability
    {k : ℕ} {hk : 3 ≤ k} {gamma : ℝ}
    {hgamma : gamma ∈ Set.Ico (gammaK k) 1}
    {alpha : ℝ} (halpha : 0 < alpha)
    {m n : ℕ} {tau : ℝ} {hn : k - 1 ≤ n}
    {D : SupercriticalDivision k (Fin n)}
    (K : SupercriticalMediumGraph
      k hk gamma hgamma alpha m n tau hn D) :
    ((supercriticalMediumRefinedGraphFinset
      k hk gamma hgamma alpha halpha m n tau hn
        (supercriticalMediumRefinementKeyOf halpha K)).card : ℝ) ≤
      (supercriticalProfileMultiplicity (crossEdgeProfile K.1 D) : ℝ) *
        (supercriticalMediumFixedModel
          (supercriticalMediumWitnessOfMem halpha K.2)).eventProbability
            (supercriticalMediumInducedFreeSampleEvent halpha K) := by
  let w := supercriticalMediumWitnessOfMem halpha K.2
  let M := supercriticalMediumFixedModel w
  let E := supercriticalMediumInducedFreeSampleEvent halpha K
  have hcard :
      (supercriticalMediumRefinedGraphFinset
        k hk gamma hgamma alpha halpha m n tau hn
          (supercriticalMediumRefinementKeyOf halpha K)).card ≤ E.card :=
    card_supercriticalMediumRefinedGraphFinset_le_inducedFreeEvent halpha K
  have hspace : M.sampleSpaceCard ≤
      supercriticalProfileMultiplicity (crossEdgeProfile K.1 D) :=
    supercriticalMediumFixedModel_sampleSpaceCard_le_profileMultiplicity w
  have hprob : 0 ≤ M.eventProbability E := M.eventProbability_nonneg E
  have hcardpos : (M.sampleSpaceCard : ℝ) ≠ 0 := by
    exact_mod_cast M.sampleSpaceCard_ne_zero
  have hidentity :
      (E.card : ℝ) = (M.sampleSpaceCard : ℝ) * M.eventProbability E := by
    rw [M.eventProbability_eq_card_div]
    field_simp
  calc
    ((supercriticalMediumRefinedGraphFinset
      k hk gamma hgamma alpha halpha m n tau hn
        (supercriticalMediumRefinementKeyOf halpha K)).card : ℝ) ≤
        (E.card : ℝ) := by exact_mod_cast hcard
    _ = (M.sampleSpaceCard : ℝ) * M.eventProbability E := hidentity
    _ ≤ (supercriticalProfileMultiplicity (crossEdgeProfile K.1 D) : ℝ) *
        M.eventProbability E := by
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hspace) hprob

end InducedStars
