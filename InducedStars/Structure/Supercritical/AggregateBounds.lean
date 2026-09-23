import InducedStars.Structure.Supercritical.AggregateChoices
import Mathlib.Tactic

/-!
# Aggregate bounds for clean supercritical profile families

This file turns the literal profile/sparse-edge fibers into one numerical
aggregate and compares it with the fixed-cardinality pre-absorption choice
space.  The shift is kept as an integer: this is important when the aggregate
is reused after a deterministic edge correction.
-/

noncomputable section

open Finset Set
open scoped BigOperators

namespace InducedStars

variable {k : ℕ} {V : Type*} [Fintype V] [DecidableEq V]

/-! ## The shifted numerical aggregate -/

/-- Sum of the exact profile multiplicities and sparse-edge choices over all
feasible nonnegative sparse shifts.  Density-window membership is part of the
summand, rather than an existence hypothesis on the whole aggregate. -/
def supercriticalShiftedProfileAggregate
    (D : SupercriticalDivision k V) (m : ℕ) (rho delta : ℝ)
    (u : ℤ) : ℕ := by
  classical
  exact
    ∑ t ∈ Finset.range (supercriticalSparsePotentialCapacity D + 1),
      ∑ profile ∈ supercriticalAllEdgeProfilesFinset D,
        if SupercriticalProfileAtShift D m rho delta
            (u + (t : ℤ)) profile then
          supercriticalProfileMultiplicity profile *
            Nat.choose (supercriticalSparsePotentialCapacity D) t
        else 0

/-- All profiles selected by one shifted aggregate have the same total number
of old variable edges. -/
theorem supercriticalProfileAtShift_add_common_count
    (D : SupercriticalDivision k V) (m L t : ℕ)
    (rho delta : ℝ) (u : ℤ)
    (profile : SupercriticalEdgeProfile D)
    (hL : (L : ℤ) + (divisionInternalCliqueCapacity D : ℤ) + u = m)
    (hprofile : SupercriticalProfileAtShift D m rho delta
      (u + (t : ℤ)) profile) :
    profileTotal profile + t = L := by
  have hprofileCount := hprofile.1
  omega

/-- A shifted aggregate is a sub-sum of the exact finite Vandermonde
decomposition.  No profile at zero shift, or indeed any profile at all, is
assumed to exist. -/
theorem supercriticalShiftedProfileAggregate_le_choose
    (D : SupercriticalDivision k V) (m L : ℕ)
    (rho delta : ℝ) (u : ℤ)
    (hL : (L : ℤ) + (divisionInternalCliqueCapacity D : ℤ) + u = m) :
    supercriticalShiftedProfileAggregate D m rho delta u ≤
      Nat.choose (supercriticalPreAbsorptionVariableCapacity D) L := by
  classical
  rw [supercriticalProfileVandermondeDecomposition]
  unfold supercriticalShiftedProfileAggregate
  apply Finset.sum_le_sum
  intro t _ht
  apply Finset.sum_le_sum
  intro profile _hprofileAll
  by_cases hprofile : SupercriticalProfileAtShift D m rho delta
      (u + (t : ℤ)) profile
  · rw [if_pos hprofile, if_pos]
    exact supercriticalProfileAtShift_add_common_count
      D m L t rho delta u profile hL hprofile
  · simp [hprofile]

/-! ## A direct encoding of the complete clean family -/

/-- Retain exactly the variable edges of a clean graph: tagged edges between
main parts and unordered edges internal to the sparse set. -/
def supercriticalCleanCombinedChoiceOfGraph
    (D : SupercriticalDivision k V) (G : SimpleGraph V) :
    Finset (SupercriticalCombinedChoice k V) :=
  supercriticalCombineProfileSparseChoice
    (supercriticalCleanCrossChoiceOfGraph D G)
    (supercriticalSparseInducedEdges G D)

/-- The variable-edge selection of a clean graph lies in the one fixed layer
forced by its total edge count. -/
theorem supercriticalCleanCombinedChoiceOfGraph_mem_layer
    {k : ℕ} {hk : 3 ≤ k} {gamma : ℝ}
    {hgamma : gamma ∈ Set.Ico (gammaK k) 1}
    {m n : ℕ} {tau : ℝ} {hn : k - 1 ≤ n}
    {D : SupercriticalDivision k (Fin n)} {G : SimpleGraph (Fin n)}
    (hG : G ∈ supercriticalCleanDivisionGraphFinset
      k hk gamma hgamma m n tau hn D) :
    supercriticalCleanCombinedChoiceOfGraph D G ∈
      supercriticalCombinedChoiceLayer D
        (m - divisionInternalCliqueCapacity D) := by
  classical
  rw [mem_supercriticalCombinedChoiceLayer]
  constructor
  · rw [supercriticalCleanCombinedChoiceOfGraph,
      supercriticalCombinedChoiceUniverse, Finset.subset_disjSum]
    constructor
    · intro z hz
      rw [supercriticalCombineProfileSparseChoice_toLeft,
        Finset.mem_sigma] at hz
      rw [mem_supercriticalTaggedCrossChoiceUniverse]
      have hxy := hz.2
      rw [supercriticalCleanCrossChoiceOfGraph,
        SimpleGraph.mem_interedges_iff] at hxy
      exact ⟨hxy.1, hxy.2.1⟩
    · rw [supercriticalCombineProfileSparseChoice_toRight]
      exact supercriticalSparseInducedEdges_subset_potential G D
  · have hGprofile :
        G ∈ supercriticalCleanDivisionProfileGraphFinset
          k hk gamma hgamma m n tau hn D (crossEdgeProfile G D) := by
      rw [mem_supercriticalCleanDivisionProfileGraphFinset]
      exact ⟨hG, rfl⟩
    have hidentity := supercriticalDefectShift_edgeCount_identity G D
    rw [finiteGraphEdges_card_eq_of_mem_cleanProfile hGprofile,
      supercriticalDefectShift_clean_eq_inducedEdgeCount hGprofile] at hidentity
    have hidentityNat :
        m = divisionInternalCliqueCapacity D +
          profileTotal (crossEdgeProfile G D) +
          inducedEdgeCount G D.sparse := by
      exact_mod_cast hidentity
    rw [supercriticalCleanCombinedChoiceOfGraph,
      supercriticalCombineProfileSparseChoice, Finset.card_disjSum,
      Finset.card_sigma, card_supercriticalSparseInducedEdges]
    have hcross :
        (∑ e : SupercriticalPartPair k,
          (supercriticalCleanCrossChoiceOfGraph D G e).card) =
            profileTotal (crossEdgeProfile G D) := by
      unfold profileTotal supercriticalCleanCrossChoiceOfGraph
      simp only [crossEdgeProfile_count]
    rw [hcross]
    omega

/-- For a fixed clean division, the selected variable edges determine the
whole graph.  The proof recovers adjacency in the four possible locations. -/
theorem supercriticalCleanCombinedChoiceOfGraph_injective
    {k : ℕ} {hk : 3 ≤ k} {gamma : ℝ}
    {hgamma : gamma ∈ Set.Ico (gammaK k) 1}
    {m n : ℕ} {tau : ℝ} {hn : k - 1 ≤ n}
    {D : SupercriticalDivision k (Fin n)} :
    Function.Injective
      (fun G : ↑(supercriticalCleanDivisionGraphFinset
          k hk gamma hgamma m n tau hn D) ↦
        supercriticalCleanCombinedChoiceOfGraph D G.1) := by
  classical
  intro G H hchoice
  change supercriticalCombineProfileSparseChoice
      (supercriticalCleanCrossChoiceOfGraph D G.1)
        (supercriticalSparseInducedEdges G.1 D) =
    supercriticalCombineProfileSparseChoice
      (supercriticalCleanCrossChoiceOfGraph D H.1)
        (supercriticalSparseInducedEdges H.1 D) at hchoice
  have hleft := congrArg Finset.toLeft hchoice
  have hright := congrArg Finset.toRight hchoice
  simp only [supercriticalCombineProfileSparseChoice_toLeft] at hleft
  simp only [supercriticalCombineProfileSparseChoice_toRight] at hright
  have hcross : supercriticalCleanCrossChoiceOfGraph D G.1 =
      supercriticalCleanCrossChoiceOfGraph D H.1 := by
    funext e
    ext xy
    have hmem := congrArg
      (fun A : Finset (SupercriticalTaggedCrossChoice k (Fin n)) ↦
        (⟨e, xy⟩ : SupercriticalTaggedCrossChoice k (Fin n)) ∈ A) hleft
    simpa using hmem
  have hsparse : supercriticalSparseInducedEdges G.1 D =
      supercriticalSparseInducedEdges H.1 D := hright
  have hGprofile :
      G.1 ∈ supercriticalCleanDivisionProfileGraphFinset
        k hk gamma hgamma m n tau hn D (crossEdgeProfile G.1 D) := by
    rw [mem_supercriticalCleanDivisionProfileGraphFinset]
    exact ⟨G.2, rfl⟩
  have hHprofile :
      H.1 ∈ supercriticalCleanDivisionProfileGraphFinset
        k hk gamma hgamma m n tau hn D (crossEdgeProfile H.1 D) := by
    rw [mem_supercriticalCleanDivisionProfileGraphFinset]
    exact ⟨H.2, rfl⟩
  apply Subtype.ext
  ext x y
  by_cases hxy : x = y
  · subst y
    simp
  rcases D.sparse_or_existsUnique_part x with hxSparse | ⟨i, hxi, _⟩
  · rcases D.sparse_or_existsUnique_part y with hySparse | ⟨j, hyj, _⟩
    · have hmem := congrArg (fun E ↦ s(x, y) ∈ E) hsparse
      simpa [hxSparse, hySparse] using hmem
    · have hySupport : y ∈ D.support := D.part_subset_support j hyj
      constructor
      · intro hGxy
        exact False.elim
          ((not_adj_support_sparse_of_mem_cleanProfile hGprofile
            hySupport hxSparse) ((G.1.adj_comm y x).mpr hGxy))
      · intro hHxy
        exact False.elim
          ((not_adj_support_sparse_of_mem_cleanProfile hHprofile
            hySupport hxSparse) ((H.1.adj_comm y x).mpr hHxy))
  · rcases D.sparse_or_existsUnique_part y with hySparse | ⟨j, hyj, _⟩
    · have hxSupport : x ∈ D.support := D.part_subset_support i hxi
      constructor
      · intro hGxy
        exact False.elim
          ((not_adj_support_sparse_of_mem_cleanProfile hGprofile
            hxSupport hySparse) hGxy)
      · intro hHxy
        exact False.elim
          ((not_adj_support_sparse_of_mem_cleanProfile hHprofile
            hxSupport hySparse) hHxy)
    · by_cases hij : i = j
      · subst j
        constructor
        · intro _
          exact mainParts_clique_of_mem_cleanProfile hHprofile i hxi hyj hxy
        · intro _
          exact mainParts_clique_of_mem_cleanProfile hGprofile i hxi hyj hxy
      · by_cases hlt : i < j
        · let e : SupercriticalPartPair k := ⟨i, j, hlt⟩
          have heq := congrFun hcross e
          have hmem := congrArg (fun E ↦ (x, y) ∈ E) heq
          simpa [supercriticalCleanCrossChoiceOfGraph,
            SimpleGraph.mem_interedges_iff, e, hxi, hyj] using hmem
        · have hji : j < i := lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm hij)
          let e : SupercriticalPartPair k := ⟨j, i, hji⟩
          have heq := congrFun hcross e
          have hmem := congrArg (fun E ↦ (y, x) ∈ E) heq
          simpa [supercriticalCleanCrossChoiceOfGraph,
            SimpleGraph.mem_interedges_iff, e, hxi, hyj,
            G.1.adj_comm, H.1.adj_comm] using hmem

/-- The direct finite embedding of the full clean family into its one
pre-absorption choice layer. -/
def supercriticalCleanCombinedChoiceEmbedding
    {k : ℕ} {hk : 3 ≤ k} {gamma : ℝ}
    {hgamma : gamma ∈ Set.Ico (gammaK k) 1}
    {m n : ℕ} {tau : ℝ} {hn : k - 1 ≤ n}
    (D : SupercriticalDivision k (Fin n)) :
    ↑(supercriticalCleanDivisionGraphFinset
        k hk gamma hgamma m n tau hn D) →
      ↑(supercriticalCombinedChoiceLayer D
        (m - divisionInternalCliqueCapacity D)) :=
  fun G ↦ ⟨supercriticalCleanCombinedChoiceOfGraph D G.1,
    supercriticalCleanCombinedChoiceOfGraph_mem_layer G.2⟩

theorem supercriticalCleanCombinedChoiceEmbedding_injective
    {k : ℕ} {hk : 3 ≤ k} {gamma : ℝ}
    {hgamma : gamma ∈ Set.Ico (gammaK k) 1}
    {m n : ℕ} {tau : ℝ} {hn : k - 1 ≤ n}
    (D : SupercriticalDivision k (Fin n)) :
    Function.Injective
      (supercriticalCleanCombinedChoiceEmbedding
        (hk := hk) (hgamma := hgamma) (m := m) (n := n)
        (tau := tau) (hn := hn) D) := by
  intro G H h
  apply supercriticalCleanCombinedChoiceOfGraph_injective
  exact congrArg Subtype.val h

/-- The whole clean family is bounded directly by the binomial coefficient
for all old variable coordinates; no profile-window hypothesis is needed. -/
theorem card_supercriticalCleanDivisionGraphFinset_le_preAbsorptionChoose
    {k : ℕ} {hk : 3 ≤ k} {gamma : ℝ}
    {hgamma : gamma ∈ Set.Ico (gammaK k) 1}
    {m n : ℕ} {tau : ℝ} {hn : k - 1 ≤ n}
    (D : SupercriticalDivision k (Fin n)) :
    (supercriticalCleanDivisionGraphFinset
      k hk gamma hgamma m n tau hn D).card ≤
      Nat.choose (supercriticalPreAbsorptionVariableCapacity D)
        (m - divisionInternalCliqueCapacity D) := by
  classical
  have hcard := Finset.card_le_card_of_injective
    (supercriticalCleanCombinedChoiceEmbedding_injective
      (hk := hk) (hgamma := hgamma) (m := m) (n := n)
      (tau := tau) (hn := hn) D)
  simpa using hcard

/-! ## The clean family inside the zero-shift aggregate -/

/-- A clean graph's actual cross profile is admissible at the shift given by
the number of its sparse--sparse edges, provided its cross densities satisfy
the stated window. -/
theorem crossEdgeProfile_atShift_inducedEdgeCount_of_mem_clean
    {k : ℕ} {hk : 3 ≤ k} {gamma : ℝ}
    {hgamma : gamma ∈ Set.Ico (gammaK k) 1}
    {m n : ℕ} {tau rho delta : ℝ} {hn : k - 1 ≤ n}
    {D : SupercriticalDivision k (Fin n)} {G : SimpleGraph (Fin n)}
    (hG : G ∈ supercriticalCleanDivisionGraphFinset
      k hk gamma hgamma m n tau hn D)
    (hdensity : ∀ e : SupercriticalPartPair k,
      rho - delta ≤ profileDensity (crossEdgeProfile G D) e ∧
        profileDensity (crossEdgeProfile G D) e ≤ rho + delta) :
    SupercriticalProfileAtShift D m rho delta
      (inducedEdgeCount G D.sparse : ℤ) (crossEdgeProfile G D) := by
  have hGprofile :
      G ∈ supercriticalCleanDivisionProfileGraphFinset
        k hk gamma hgamma m n tau hn D (crossEdgeProfile G D) := by
    rw [mem_supercriticalCleanDivisionProfileGraphFinset]
    exact ⟨hG, rfl⟩
  constructor
  · have hidentity := supercriticalDefectShift_edgeCount_identity G D
    rw [finiteGraphEdges_card_eq_of_mem_cleanProfile hGprofile,
      supercriticalDefectShift_clean_eq_inducedEdgeCount hGprofile] at hidentity
    omega
  · intro e
    exact hdensity e

/-- The literal union of clean profile fibers which occur in the zero-shift
aggregate. -/
def supercriticalCleanAdmissibleProfileUnion
    (k : ℕ) (hk : 3 ≤ k) (gamma : ℝ)
    (hgamma : gamma ∈ Set.Ico (gammaK k) 1)
    (m n : ℕ) (tau rho delta : ℝ) (hn : k - 1 ≤ n)
    (D : SupercriticalDivision k (Fin n)) :
    Finset (SimpleGraph (Fin n)) := by
  classical
  exact
    (Finset.range (supercriticalSparsePotentialCapacity D + 1)).biUnion fun t ↦
      (supercriticalAllEdgeProfilesFinset D).biUnion fun profile ↦
        if SupercriticalProfileAtShift D m rho delta (t : ℤ) profile then
          supercriticalCleanDivisionProfileGraphFinset
            k hk gamma hgamma m n tau hn D profile
        else ∅

/-- Under the actual cross-density window, every graph in the clean division
family occurs in the corresponding zero-shift aggregate union. -/
theorem supercriticalCleanDivisionGraphFinset_subset_admissibleProfileUnion
    {k : ℕ} {hk : 3 ≤ k} {gamma : ℝ}
    {hgamma : gamma ∈ Set.Ico (gammaK k) 1}
    {m n : ℕ} {tau rho delta : ℝ} {hn : k - 1 ≤ n}
    {D : SupercriticalDivision k (Fin n)}
    (hdensity : ∀ G ∈ supercriticalCleanDivisionGraphFinset
        k hk gamma hgamma m n tau hn D,
      ∀ e : SupercriticalPartPair k,
        rho - delta ≤ profileDensity (crossEdgeProfile G D) e ∧
          profileDensity (crossEdgeProfile G D) e ≤ rho + delta) :
    supercriticalCleanDivisionGraphFinset
        k hk gamma hgamma m n tau hn D ⊆
      supercriticalCleanAdmissibleProfileUnion
        k hk gamma hgamma m n tau rho delta hn D := by
  classical
  intro G hG
  let t := inducedEdgeCount G D.sparse
  let profile := crossEdgeProfile G D
  have ht : t ≤ supercriticalSparsePotentialCapacity D := by
    dsimp [t]
    have hcard := Finset.card_le_card
      (supercriticalSparseInducedEdges_subset_potential G D)
    simpa [supercriticalSparsePotentialCapacity] using hcard
  have hprofile : SupercriticalProfileAtShift D m rho delta (t : ℤ) profile := by
    dsimp [t, profile]
    exact crossEdgeProfile_atShift_inducedEdgeCount_of_mem_clean
      hG (hdensity G hG)
  have hGprofile : G ∈ supercriticalCleanDivisionProfileGraphFinset
      k hk gamma hgamma m n tau hn D profile := by
    rw [mem_supercriticalCleanDivisionProfileGraphFinset]
    exact ⟨hG, rfl⟩
  rw [supercriticalCleanAdmissibleProfileUnion, Finset.mem_biUnion]
  refine ⟨t, by simpa using ht, ?_⟩
  rw [Finset.mem_biUnion]
  refine ⟨profile, mem_supercriticalAllEdgeProfilesFinset D profile, ?_⟩
  simp [hprofile, hGprofile]

/-- With the density conclusions supplied by close structure, the complete
clean family is bounded by the numerical zero-shift aggregate. -/
theorem card_supercriticalCleanDivisionGraphFinset_le_shiftedProfileAggregate
    {k : ℕ} {hk : 3 ≤ k} {gamma : ℝ}
    {hgamma : gamma ∈ Set.Ico (gammaK k) 1}
    {m n : ℕ} {tau rho delta : ℝ} {hn : k - 1 ≤ n}
    (D : SupercriticalDivision k (Fin n))
    (hdensity : ∀ G ∈ supercriticalCleanDivisionGraphFinset
        k hk gamma hgamma m n tau hn D,
      ∀ e : SupercriticalPartPair k,
        rho - delta ≤ profileDensity (crossEdgeProfile G D) e ∧
          profileDensity (crossEdgeProfile G D) e ≤ rho + delta) :
    (supercriticalCleanDivisionGraphFinset
      k hk gamma hgamma m n tau hn D).card ≤
      supercriticalShiftedProfileAggregate D m rho delta 0 := by
  classical
  let U := supercriticalCleanAdmissibleProfileUnion
    k hk gamma hgamma m n tau rho delta hn D
  have hsub : supercriticalCleanDivisionGraphFinset
      k hk gamma hgamma m n tau hn D ⊆ U := by
    simpa [U] using
      (supercriticalCleanDivisionGraphFinset_subset_admissibleProfileUnion
        (D := D) hdensity)
  calc
    (supercriticalCleanDivisionGraphFinset
        k hk gamma hgamma m n tau hn D).card ≤ U.card :=
      Finset.card_le_card hsub
    _ ≤ ∑ t ∈ Finset.range (supercriticalSparsePotentialCapacity D + 1),
        ∑ profile ∈ supercriticalAllEdgeProfilesFinset D,
          (if SupercriticalProfileAtShift D m rho delta (t : ℤ) profile then
            (supercriticalCleanDivisionProfileGraphFinset
              k hk gamma hgamma m n tau hn D profile).card
          else 0) := by
      dsimp [U, supercriticalCleanAdmissibleProfileUnion]
      refine Finset.card_biUnion_le.trans ?_
      apply Finset.sum_le_sum
      intro t _ht
      calc
        #((supercriticalAllEdgeProfilesFinset D).biUnion fun profile ↦
            if SupercriticalProfileAtShift D m rho delta (t : ℤ) profile then
              supercriticalCleanDivisionProfileGraphFinset
                k hk gamma hgamma m n tau hn D profile
            else ∅) ≤
            ∑ profile ∈ supercriticalAllEdgeProfilesFinset D,
              #(if SupercriticalProfileAtShift D m rho delta (t : ℤ) profile then
                  supercriticalCleanDivisionProfileGraphFinset
                    k hk gamma hgamma m n tau hn D profile
                else ∅) := Finset.card_biUnion_le
        _ = ∑ profile ∈ supercriticalAllEdgeProfilesFinset D,
              if SupercriticalProfileAtShift D m rho delta (t : ℤ) profile then
                (supercriticalCleanDivisionProfileGraphFinset
                  k hk gamma hgamma m n tau hn D profile).card
              else 0 := by
          apply Finset.sum_congr rfl
          intro profile _hprofileAll
          by_cases hprofile :
              SupercriticalProfileAtShift D m rho delta (t : ℤ) profile <;>
            simp [hprofile]
    _ ≤ supercriticalShiftedProfileAggregate D m rho delta 0 := by
      unfold supercriticalShiftedProfileAggregate
      apply Finset.sum_le_sum
      intro t _ht
      apply Finset.sum_le_sum
      intro profile _hprofileAll
      by_cases hprofile :
          SupercriticalProfileAtShift D m rho delta (t : ℤ) profile
      · simp only [hprofile, if_true, zero_add]
        exact card_supercriticalCleanDivisionProfileGraphFinset_le hprofile
      · simp [hprofile]

end InducedStars
