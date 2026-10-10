import InducedStars.Structure.Supercritical.MatchingFamilies
import InducedStars.Structure.Supercritical.ProfileProbability
import Mathlib.Tactic

/-!
# Exact encoding of fixed-defect profile fibers

Every graph in the matching fiber is encoded by the cross-edge choices of
the full-profile fixed-cardinality model.  The combined defect pattern fixes
all remaining adjacencies, so the encoding is injective and its image lies in
the literal induced-star-free sample event.
-/

noncomputable section

open Finset Set

namespace InducedStars

noncomputable local instance matchingEncodingGraphDecidableEq (n : ℕ) :
    DecidableEq (SimpleGraph (Fin n)) :=
  Classical.decEq _

/-! ## Fixed and tagged induced-free events -/

/-- Exact fixed-cardinality samples whose decoded graph is induced-star
free. -/
def supercriticalFixedProfileInducedFreeSampleEvent
    (k : ℕ) {n : ℕ} (D : SupercriticalDivision k (Fin n))
    (T : SimpleGraph (Fin n)) (profile : SupercriticalEdgeProfile D) :
    Finset (supercriticalFixedProfileBlockModel D profile).Sample := by
  classical
  exact Finset.univ.filter fun S ↦
    ¬ Regularity.InducedEmbeds (inducedStar k)
      (supercriticalGraphFromCrossOutcome D T profile
        ((supercriticalFixedProfileBlockModel D profile).sampleOutcome S))

@[simp] theorem mem_supercriticalFixedProfileInducedFreeSampleEvent
    {k n : ℕ} {D : SupercriticalDivision k (Fin n)}
    {T : SimpleGraph (Fin n)} {profile : SupercriticalEdgeProfile D}
    {S : (supercriticalFixedProfileBlockModel D profile).Sample} :
    S ∈ supercriticalFixedProfileInducedFreeSampleEvent k D T profile ↔
      ¬ Regularity.InducedEmbeds (inducedStar k)
        (supercriticalGraphFromCrossOutcome D T profile
          ((supercriticalFixedProfileBlockModel D profile).sampleOutcome S)) := by
  classical
  simp [supercriticalFixedProfileInducedFreeSampleEvent]

/-- Tagged Bernoulli outcomes whose decoded graph is induced-star free. -/
def supercriticalProfileTaggedInducedFreeEvent
    (k : ℕ) {n : ℕ} (D : SupercriticalDivision k (Fin n))
    (T : SimpleGraph (Fin n)) (profile : SupercriticalEdgeProfile D) :
    Finset (Finset (supercriticalFixedProfileBlockModel D profile).Coordinate) := by
  classical
  exact Finset.univ.filter fun outcome ↦
    ¬ Regularity.InducedEmbeds (inducedStar k)
      (supercriticalGraphFromCrossOutcome D T profile outcome)

@[simp] theorem mem_supercriticalProfileTaggedInducedFreeEvent
    {k n : ℕ} {D : SupercriticalDivision k (Fin n)}
    {T : SimpleGraph (Fin n)} {profile : SupercriticalEdgeProfile D}
    {outcome : Finset
      (supercriticalFixedProfileBlockModel D profile).Coordinate} :
    outcome ∈ supercriticalProfileTaggedInducedFreeEvent k D T profile ↔
      ¬ Regularity.InducedEmbeds (inducedStar k)
        (supercriticalGraphFromCrossOutcome D T profile outcome) := by
  classical
  simp [supercriticalProfileTaggedInducedFreeEvent]

theorem supercriticalFixedProfileInducedFreeSampleEvent_eq_sampleEvent
    (k : ℕ) {n : ℕ} (D : SupercriticalDivision k (Fin n))
    (T : SimpleGraph (Fin n)) (profile : SupercriticalEdgeProfile D) :
    supercriticalFixedProfileInducedFreeSampleEvent k D T profile =
      (supercriticalFixedProfileBlockModel D profile).sampleEvent
        (supercriticalProfileTaggedInducedFreeEvent k D T profile) := by
  classical
  ext S
  simp [DenseGraph.FixedCardinalityBlockModel.mem_sampleEvent]

/-! ## Fiber encoding and recovery -/

theorem combinedSupercriticalDefectGraph_eq_of_mem_fixedDefectProfile
    {k : ℕ} {hk : 3 ≤ k} {gamma : ℝ}
    {hgamma : gamma ∈ Set.Ico (gammaK k) 1}
    {alpha : ℝ} {m n : ℕ} {tau : ℝ} {hn : k - 1 ≤ n}
    {D : SupercriticalDivision k (Fin n)} {T G : SimpleGraph (Fin n)}
    {profile : SupercriticalEdgeProfile D}
    (hG : G ∈ supercriticalFixedDefectProfileGraphFinset
      k hk gamma hgamma alpha m n tau hn D T profile) :
    combinedSupercriticalDefectGraph G D = T := by
  have hD := canonicalSupercriticalDivision_eq_of_mem_fixedDefectProfile hG
  have hT := canonicalCombinedDefectGraph_eq_of_mem_fixedDefectProfile hG
  simpa [canonicalCombinedDefectGraph, hD] using hT

/-- Encode a graph in the exact fiber by its full-profile cross-edge sample. -/
def supercriticalFixedDefectProfileEncoding
    (k : ℕ) (hk : 3 ≤ k) (gamma : ℝ)
    (hgamma : gamma ∈ Set.Ico (gammaK k) 1)
    (alpha : ℝ) (m n : ℕ) (tau : ℝ) (hn : k - 1 ≤ n)
    (D : SupercriticalDivision k (Fin n)) (T : SimpleGraph (Fin n))
    (profile : SupercriticalEdgeProfile D) :
    ↑(supercriticalFixedDefectProfileGraphFinset
        k hk gamma hgamma alpha m n tau hn D T profile) →
      (supercriticalFixedProfileBlockModel D profile).Sample :=
  fun G ↦ supercriticalFixedProfileSampleOfGraph D profile G.1
    (crossEdgeProfile_eq_of_mem_supercriticalFixedDefectProfileGraphFinset G.2)

theorem supercriticalFixedDefectProfileEncoding_recovery
    (k : ℕ) (hk : 3 ≤ k) (gamma : ℝ)
    (hgamma : gamma ∈ Set.Ico (gammaK k) 1)
    (alpha : ℝ) (m n : ℕ) (tau : ℝ) (hn : k - 1 ≤ n)
    (D : SupercriticalDivision k (Fin n)) (T : SimpleGraph (Fin n))
    (profile : SupercriticalEdgeProfile D)
    (G : ↑(supercriticalFixedDefectProfileGraphFinset
      k hk gamma hgamma alpha m n tau hn D T profile)) :
    supercriticalGraphFromCrossOutcome D T profile
        ((supercriticalFixedProfileBlockModel D profile).sampleOutcome
          (supercriticalFixedDefectProfileEncoding
            k hk gamma hgamma alpha m n tau hn D T profile G)) = G.1 := by
  exact supercriticalGraphFromCrossOutcome_sampleOfGraph D G.1 T profile
    (combinedSupercriticalDefectGraph_eq_of_mem_fixedDefectProfile G.2)
    (crossEdgeProfile_eq_of_mem_supercriticalFixedDefectProfileGraphFinset G.2)

theorem supercriticalFixedDefectProfileEncoding_injective
    (k : ℕ) (hk : 3 ≤ k) (gamma : ℝ)
    (hgamma : gamma ∈ Set.Ico (gammaK k) 1)
    (alpha : ℝ) (m n : ℕ) (tau : ℝ) (hn : k - 1 ≤ n)
    (D : SupercriticalDivision k (Fin n)) (T : SimpleGraph (Fin n))
    (profile : SupercriticalEdgeProfile D) :
    Function.Injective (supercriticalFixedDefectProfileEncoding
      k hk gamma hgamma alpha m n tau hn D T profile) := by
  intro G H hGH
  apply Subtype.ext
  rw [← supercriticalFixedDefectProfileEncoding_recovery
      k hk gamma hgamma alpha m n tau hn D T profile G,
    ← supercriticalFixedDefectProfileEncoding_recovery
      k hk gamma hgamma alpha m n tau hn D T profile H,
    hGH]

/-- Embedding form of the exact fiber encoder. -/
def supercriticalFixedDefectProfileEncodingEmbedding
    (k : ℕ) (hk : 3 ≤ k) (gamma : ℝ)
    (hgamma : gamma ∈ Set.Ico (gammaK k) 1)
    (alpha : ℝ) (m n : ℕ) (tau : ℝ) (hn : k - 1 ≤ n)
    (D : SupercriticalDivision k (Fin n)) (T : SimpleGraph (Fin n))
    (profile : SupercriticalEdgeProfile D) :
    ↑(supercriticalFixedDefectProfileGraphFinset
        k hk gamma hgamma alpha m n tau hn D T profile) ↪
      (supercriticalFixedProfileBlockModel D profile).Sample :=
  ⟨supercriticalFixedDefectProfileEncoding
      k hk gamma hgamma alpha m n tau hn D T profile,
    supercriticalFixedDefectProfileEncoding_injective
      k hk gamma hgamma alpha m n tau hn D T profile⟩

theorem supercriticalFixedDefectProfileEncoding_mem_inducedFreeEvent
    (k : ℕ) (hk : 3 ≤ k) (gamma : ℝ)
    (hgamma : gamma ∈ Set.Ico (gammaK k) 1)
    (alpha : ℝ) (m n : ℕ) (tau : ℝ) (hn : k - 1 ≤ n)
    (D : SupercriticalDivision k (Fin n)) (T : SimpleGraph (Fin n))
    (profile : SupercriticalEdgeProfile D)
    (G : ↑(supercriticalFixedDefectProfileGraphFinset
      k hk gamma hgamma alpha m n tau hn D T profile)) :
    supercriticalFixedDefectProfileEncoding
        k hk gamma hgamma alpha m n tau hn D T profile G ∈
      supercriticalFixedProfileInducedFreeSampleEvent k D T profile := by
  rw [mem_supercriticalFixedProfileInducedFreeSampleEvent,
    supercriticalFixedDefectProfileEncoding_recovery]
  have hfixed :=
    (mem_supercriticalFixedDefectProfileGraphFinset.mp G.2).1
  have hdivision := (mem_supercriticalFixedDefectGraphFinset.mp hfixed).1
  have hclose := (mem_supercriticalDivisionDefectGraphFinset.mp hdivision).1
  exact (mem_supercriticalCloseGraphFinset.mp hclose).1

/-! ## Exact cardinality comparison -/

theorem card_supercriticalFixedDefectProfileGraphFinset_le_inducedFreeEvent
    (k : ℕ) (hk : 3 ≤ k) (gamma : ℝ)
    (hgamma : gamma ∈ Set.Ico (gammaK k) 1)
    (alpha : ℝ) (m n : ℕ) (tau : ℝ) (hn : k - 1 ≤ n)
    (D : SupercriticalDivision k (Fin n)) (T : SimpleGraph (Fin n))
    (profile : SupercriticalEdgeProfile D) :
    (supercriticalFixedDefectProfileGraphFinset
        k hk gamma hgamma alpha m n tau hn D T profile).card ≤
      (supercriticalFixedProfileInducedFreeSampleEvent
        k D T profile).card := by
  classical
  let f : ↑(supercriticalFixedDefectProfileGraphFinset
      k hk gamma hgamma alpha m n tau hn D T profile) →
      ↑(supercriticalFixedProfileInducedFreeSampleEvent k D T profile) :=
    fun G ↦ ⟨supercriticalFixedDefectProfileEncoding
        k hk gamma hgamma alpha m n tau hn D T profile G,
      supercriticalFixedDefectProfileEncoding_mem_inducedFreeEvent
        k hk gamma hgamma alpha m n tau hn D T profile G⟩
  have hf : Function.Injective f := by
    intro G H hGH
    apply supercriticalFixedDefectProfileEncoding_injective
      k hk gamma hgamma alpha m n tau hn D T profile
    exact congrArg Subtype.val hGH
  simpa only [Fintype.card_coe] using Fintype.card_le_of_injective f hf

/-- The exact profile-fiber count is at most profile multiplicity times its
fixed-cardinality induced-free probability. -/
theorem card_supercriticalFixedDefectProfileGraphFinset_le_profileMultiplicity_mul_probability
    (k : ℕ) (hk : 3 ≤ k) (gamma : ℝ)
    (hgamma : gamma ∈ Set.Ico (gammaK k) 1)
    (alpha : ℝ) (m n : ℕ) (tau : ℝ) (hn : k - 1 ≤ n)
    (D : SupercriticalDivision k (Fin n)) (T : SimpleGraph (Fin n))
    (profile : SupercriticalEdgeProfile D) :
    ((supercriticalFixedDefectProfileGraphFinset
        k hk gamma hgamma alpha m n tau hn D T profile).card : ℝ) ≤
      (supercriticalProfileMultiplicity profile : ℝ) *
        (supercriticalFixedProfileBlockModel D profile).eventProbability
          (supercriticalFixedProfileInducedFreeSampleEvent k D T profile) := by
  let M := supercriticalFixedProfileBlockModel D profile
  let E := supercriticalFixedProfileInducedFreeSampleEvent k D T profile
  have hcard := card_supercriticalFixedDefectProfileGraphFinset_le_inducedFreeEvent
    k hk gamma hgamma alpha m n tau hn D T profile
  have hprob : 0 ≤ M.eventProbability E := M.eventProbability_nonneg E
  have hspace : M.sampleSpaceCard = supercriticalProfileMultiplicity profile :=
    supercriticalFixedProfileBlockModel_sampleSpaceCard_eq D profile
  have hcardpos : (M.sampleSpaceCard : ℝ) ≠ 0 := by
    exact_mod_cast M.sampleSpaceCard_ne_zero
  have hidentity :
      (E.card : ℝ) = (M.sampleSpaceCard : ℝ) * M.eventProbability E := by
    rw [M.eventProbability_eq_card_div]
    field_simp
  calc
    ((supercriticalFixedDefectProfileGraphFinset
        k hk gamma hgamma alpha m n tau hn D T profile).card : ℝ) ≤
        (E.card : ℝ) := by exact_mod_cast hcard
    _ = (M.sampleSpaceCard : ℝ) * M.eventProbability E := hidentity
    _ = (supercriticalProfileMultiplicity profile : ℝ) *
        M.eventProbability E := by rw [hspace]

end InducedStars

