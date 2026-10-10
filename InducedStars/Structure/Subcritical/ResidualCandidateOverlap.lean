import InducedStars.Structure.Supercritical.MediumCandidateCounting
import DenseGraph.FiniteModels.Janson

/-!
# Role-adapted coordinate overlap for residual candidates

An injective `k`-entry vector records a matching anchor endpoint and all
`k-1` free vertices.  Its choice of anchor endpoint may depend on the
coordinate role.  A shared random coordinate fixes two distinct entries,
leaving at most `2*n^(k-2)` candidate vectors.  This reuses the established
finite two-coordinate fiber count and requires no graphon or probability
input.
-/

noncomputable section

open Finset

namespace InducedStars

/-- Finite data needed for the coordinate-fiber argument.  A coordinate role
can be inactive on a candidate.  The encoding vector may depend on the role,
so a role involving the second matching endpoint uses that endpoint to
recover the matching anchor. -/
structure SubcriticalResidualCoordinateEncoding
    (Candidate Role Coordinate : Type*) (k n : ℕ) where
  required : Candidate → Finset Coordinate
  coordinate : Candidate → Role → Option Coordinate
  vector : Role → Candidate → (Fin k → Fin n)
  vector_injective : ∀ r, Function.Injective (vector r)
  positions : Role → Fin k × Fin k
  positions_ne : ∀ r, (positions r).1 ≠ (positions r).2
  value : Coordinate → Sym2 (Fin n)
  coordinate_eq : ∀ c r e, coordinate c r = some e →
    value e = s(vector r c (positions r).1, vector r c (positions r).2)
  required_has_role : ∀ c e, e ∈ required c → ∃ r, coordinate c r = some e

namespace SubcriticalResidualCoordinateEncoding

variable {Candidate Role Coordinate : Type*} {k n : ℕ}
  [Fintype Candidate] [DecidableEq Candidate]
  [Fintype Role] [DecidableEq Role] [DecidableEq Coordinate]
  (K : SubcriticalResidualCoordinateEncoding Candidate Role Coordinate k n)

/-- Target candidates sharing the source's coordinate through specified
source and target roles. -/
def roleFiber (c : Candidate) (r s : Role) : Finset Candidate :=
  Finset.univ.filter fun d ↦ ∃ e,
    K.coordinate c r = some e ∧ K.coordinate d s = some e

@[simp] theorem mem_roleFiber (c d : Candidate) (r s : Role) :
    d ∈ K.roleFiber c r s ↔ ∃ e,
      K.coordinate c r = some e ∧ K.coordinate d s = some e := by
  simp [roleFiber]

/-- Fixing one unordered random coordinate fixes two distinct vector entries. -/
theorem roleFiber_card_le (c : Candidate) (r s : Role) :
    (K.roleFiber c r s).card ≤ 2 * n ^ (k - 2) := by
  classical
  cases hsource : K.coordinate c r with
  | none => simp [roleFiber, hsource]
  | some e =>
      let a := (K.positions s).1
      let b := (K.positions s).2
      let x := K.vector r c (K.positions r).1
      let y := K.vector r c (K.positions r).2
      have hmem : ∀ d ∈ K.roleFiber c r s,
          K.vector s d ∈ unorderedPairFunctionFinset a b x y := by
        intro d hd
        obtain ⟨f, hf, hdf⟩ := (K.mem_roleFiber c d r s).mp hd
        have hef : e = f := by simpa [hsource] using hf
        subst f
        exact (mem_unorderedPairFunctionFinset a b x y (K.vector s d)).mpr
          ((K.coordinate_eq d s e hdf).symm.trans
            (K.coordinate_eq c r e hsource))
      calc
        (K.roleFiber c r s).card ≤ (unorderedPairFunctionFinset a b x y).card :=
          Finset.card_le_card_of_injOn (K.vector s) hmem (K.vector_injective s).injOn
        _ ≤ 2 * n ^ (k - 2) :=
          unorderedPairFunctionFinset_card_le a b x y (K.positions_ne s)

/-- All candidates sharing at least one required coordinate, including the
source itself if its required support is nonempty. -/
def overlappingCandidates (c : Candidate) : Finset Candidate :=
  Finset.univ.filter fun d ↦ ¬Disjoint (K.required c) (K.required d)

@[simp] theorem mem_overlappingCandidates (c d : Candidate) :
    d ∈ K.overlappingCandidates c ↔ ¬Disjoint (K.required c) (K.required d) := by
  simp [overlappingCandidates]

theorem overlappingCandidates_subset_roleFibers (c : Candidate) :
    K.overlappingCandidates c ⊆
      Finset.univ.biUnion (fun r ↦ Finset.univ.biUnion (K.roleFiber c r)) := by
  intro d hd
  have hover := (K.mem_overlappingCandidates c d).mp hd
  obtain ⟨e, hec, hed⟩ := Finset.not_disjoint_iff.mp hover
  obtain ⟨r, hr⟩ := K.required_has_role c e hec
  obtain ⟨s, hs⟩ := K.required_has_role d e hed
  exact Finset.mem_biUnion.mpr ⟨r, Finset.mem_univ _,
    Finset.mem_biUnion.mpr ⟨s, Finset.mem_univ _,
      (K.mem_roleFiber c d r s).mpr ⟨e, hr, hs⟩⟩⟩

/-- Uniform per-candidate overlap degree. -/
theorem overlappingCandidates_card_le (c : Candidate) :
    (K.overlappingCandidates c).card ≤
      2 * Fintype.card Role ^ 2 * n ^ (k - 2) := by
  calc
    _ ≤ ∑ r : Role, ∑ s : Role, (K.roleFiber c r s).card :=
      (Finset.card_le_card (K.overlappingCandidates_subset_roleFibers c)).trans
        (Finset.card_biUnion_le.trans
          (Finset.sum_le_sum fun _ _ ↦ Finset.card_biUnion_le))
    _ ≤ ∑ _r : Role, ∑ _s : Role, 2 * n ^ (k - 2) :=
      Finset.sum_le_sum fun r _ ↦ Finset.sum_le_sum fun s _ ↦ K.roleFiber_card_le c r s
    _ = _ := by simp; ring

/-- The unordered Janson overlap count is bounded by the ordered incidence
sum.  No factor two is lost in the definition of the Janson dependency sum. -/
theorem unorderedOverlappingPairs_card_le [LinearOrder Candidate] :
    (DenseGraph.FiniteBernoulliProduct.unorderedOverlappingPairs K.required).card ≤
      2 * Fintype.card Role ^ 2 * Fintype.card Candidate * n ^ (k - 2) := by
  classical
  let E : Finset (Candidate × Candidate) := Finset.univ.biUnion fun c ↦
    (K.overlappingCandidates c).map ⟨fun d ↦ (c, d), fun _ _ h ↦ (Prod.mk.inj h).2⟩
  have hsubset : DenseGraph.FiniteBernoulliProduct.unorderedOverlappingPairs K.required ⊆ E := by
    intro cd hcd
    have hover : ¬Disjoint (K.required cd.1) (K.required cd.2) :=
      (Finset.mem_filter.mp hcd).2.2
    exact Finset.mem_biUnion.mpr ⟨cd.1, Finset.mem_univ _,
      Finset.mem_map.mpr ⟨cd.2, (K.mem_overlappingCandidates cd.1 cd.2).mpr hover, rfl⟩⟩
  calc
    _ ≤ E.card := Finset.card_le_card hsubset
    _ ≤ ∑ c : Candidate, (K.overlappingCandidates c).card := by
      simpa [E] using (Finset.card_biUnion_le (s := (Finset.univ : Finset Candidate))
        (t := fun c ↦ (K.overlappingCandidates c).map
          ⟨fun d ↦ (c, d), fun _ _ h ↦ (Prod.mk.inj h).2⟩))
    _ ≤ ∑ _c : Candidate, 2 * Fintype.card Role ^ 2 * n ^ (k - 2) :=
      Finset.sum_le_sum fun c _ ↦ K.overlappingCandidates_card_le c
    _ = _ := by simp; ring

/-- The total dependency-pair count has the matching scale `t*n^(2*k-3)`
when there are at most `t*n^(k-1)` candidates. -/
theorem unorderedOverlappingPairs_card_le_matchingScale [LinearOrder Candidate]
    (hk : 3 ≤ k) {t : ℕ}
    (hcard : Fintype.card Candidate ≤ t * n ^ (k - 1)) :
    (DenseGraph.FiniteBernoulliProduct.unorderedOverlappingPairs K.required).card ≤
      2 * Fintype.card Role ^ 2 * t * n ^ (2 * k - 3) := by
  calc
    _ ≤ 2 * Fintype.card Role ^ 2 * Fintype.card Candidate * n ^ (k - 2) :=
      K.unorderedOverlappingPairs_card_le
    _ ≤ 2 * Fintype.card Role ^ 2 * (t * n ^ (k - 1)) * n ^ (k - 2) := by gcongr
    _ = _ := by
      rw [show 2 * k - 3 = (k - 1) + (k - 2) by omega, pow_add]
      ring

end SubcriticalResidualCoordinateEncoding

end InducedStars
