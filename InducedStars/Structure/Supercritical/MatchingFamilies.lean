import InducedStars.Structure.Supercritical.ProfileRealization
import Mathlib.Tactic

/-!
# Fixed-defect profile families for the supercritical matching argument

This module refines the fixed combined-defect family by its exact cross-edge
profile.  It also records the exact defect-shift edge identity and transports
the nonmedium and no-high conclusions to the prescribed defect graph.
-/

noncomputable section

open Finset Set

namespace InducedStars

noncomputable local instance matchingFamiliesEdgeSetFintype
    {n : ℕ} (G : SimpleGraph (Fin n)) : Fintype G.edgeSet :=
  Fintype.ofFinite G.edgeSet

/-! ## The exact fixed-defect/profile fiber -/

/-- The paper's exact family `F_{Π,T,m}`: graphs with prescribed canonical
division, prescribed combined defect graph, no medium defect degree, and the
prescribed cross-edge profile. -/
def supercriticalFixedDefectProfileGraphFinset
    (k : ℕ) (hk : 3 ≤ k) (gamma : ℝ)
    (hgamma : gamma ∈ Set.Ico (gammaK k) 1)
    (alpha : ℝ) (m n : ℕ) (tau : ℝ) (hn : k - 1 ≤ n)
    (D : SupercriticalDivision k (Fin n)) (T : SimpleGraph (Fin n))
    (profile : SupercriticalEdgeProfile D) :
    Finset (SimpleGraph (Fin n)) := by
  classical
  exact (supercriticalFixedDefectGraphFinset
    k hk gamma hgamma alpha m n tau hn D T).filter fun G ↦
      crossEdgeProfile G D = profile

@[simp] theorem mem_supercriticalFixedDefectProfileGraphFinset
    {k : ℕ} {hk : 3 ≤ k} {gamma : ℝ}
    {hgamma : gamma ∈ Set.Ico (gammaK k) 1}
    {alpha : ℝ} {m n : ℕ} {tau : ℝ} {hn : k - 1 ≤ n}
    {D : SupercriticalDivision k (Fin n)} {T G : SimpleGraph (Fin n)}
    {profile : SupercriticalEdgeProfile D} :
    G ∈ supercriticalFixedDefectProfileGraphFinset
        k hk gamma hgamma alpha m n tau hn D T profile ↔
      G ∈ supercriticalFixedDefectGraphFinset
          k hk gamma hgamma alpha m n tau hn D T ∧
        crossEdgeProfile G D = profile := by
  classical
  simp [supercriticalFixedDefectProfileGraphFinset]

theorem supercriticalFixedDefectProfileGraphFinset_subset
    (k : ℕ) (hk : 3 ≤ k) (gamma : ℝ)
    (hgamma : gamma ∈ Set.Ico (gammaK k) 1)
    (alpha : ℝ) (m n : ℕ) (tau : ℝ) (hn : k - 1 ≤ n)
    (D : SupercriticalDivision k (Fin n)) (T : SimpleGraph (Fin n))
    (profile : SupercriticalEdgeProfile D) :
    supercriticalFixedDefectProfileGraphFinset
        k hk gamma hgamma alpha m n tau hn D T profile ⊆
      supercriticalFixedDefectGraphFinset
        k hk gamma hgamma alpha m n tau hn D T := by
  classical
  exact Finset.filter_subset _ _

theorem crossEdgeProfile_eq_of_mem_supercriticalFixedDefectProfileGraphFinset
    {k : ℕ} {hk : 3 ≤ k} {gamma : ℝ}
    {hgamma : gamma ∈ Set.Ico (gammaK k) 1}
    {alpha : ℝ} {m n : ℕ} {tau : ℝ} {hn : k - 1 ≤ n}
    {D : SupercriticalDivision k (Fin n)} {T G : SimpleGraph (Fin n)}
    {profile : SupercriticalEdgeProfile D}
    (hG : G ∈ supercriticalFixedDefectProfileGraphFinset
      k hk gamma hgamma alpha m n tau hn D T profile) :
    crossEdgeProfile G D = profile :=
  (mem_supercriticalFixedDefectProfileGraphFinset.mp hG).2

theorem canonicalSupercriticalDivision_eq_of_mem_fixedDefectProfile
    {k : ℕ} {hk : 3 ≤ k} {gamma : ℝ}
    {hgamma : gamma ∈ Set.Ico (gammaK k) 1}
    {alpha : ℝ} {m n : ℕ} {tau : ℝ} {hn : k - 1 ≤ n}
    {D : SupercriticalDivision k (Fin n)} {T G : SimpleGraph (Fin n)}
    {profile : SupercriticalEdgeProfile D}
    (hG : G ∈ supercriticalFixedDefectProfileGraphFinset
      k hk gamma hgamma alpha m n tau hn D T profile) :
    canonicalSupercriticalDivision G (by simpa using hn) = D := by
  have hfixed := (mem_supercriticalFixedDefectProfileGraphFinset.mp hG).1
  have hdivision := (mem_supercriticalFixedDefectGraphFinset.mp hfixed).1
  exact (mem_supercriticalDivisionDefectGraphFinset.mp hdivision).2.1

theorem canonicalCombinedDefectGraph_eq_of_mem_fixedDefectProfile
    {k : ℕ} {hk : 3 ≤ k} {gamma : ℝ}
    {hgamma : gamma ∈ Set.Ico (gammaK k) 1}
    {alpha : ℝ} {m n : ℕ} {tau : ℝ} {hn : k - 1 ≤ n}
    {D : SupercriticalDivision k (Fin n)} {T G : SimpleGraph (Fin n)}
    {profile : SupercriticalEdgeProfile D}
    (hG : G ∈ supercriticalFixedDefectProfileGraphFinset
      k hk gamma hgamma alpha m n tau hn D T profile) :
    canonicalCombinedDefectGraph G (by simpa using hn) = T := by
  have hfixed := (mem_supercriticalFixedDefectProfileGraphFinset.mp hG).1
  exact (mem_supercriticalFixedDefectGraphFinset.mp hfixed).2.1

theorem not_exists_medium_degree_of_mem_fixedDefectProfile
    {k : ℕ} {hk : 3 ≤ k} {gamma : ℝ}
    {hgamma : gamma ∈ Set.Ico (gammaK k) 1}
    {alpha : ℝ} {m n : ℕ} {tau : ℝ} {hn : k - 1 ≤ n}
    {D : SupercriticalDivision k (Fin n)} {T G : SimpleGraph (Fin n)}
    {profile : SupercriticalEdgeProfile D}
    (hG : G ∈ supercriticalFixedDefectProfileGraphFinset
      k hk gamma hgamma alpha m n tau hn D T profile) :
    ¬ ∃ v i, HasMediumDegreeInPart
      (canonicalCombinedDefectGraph G (by simpa using hn)) alpha D v i := by
  have hfixed := (mem_supercriticalFixedDefectProfileGraphFinset.mp hG).1
  exact (mem_supercriticalFixedDefectGraphFinset.mp hfixed).2.2

/-! ## Exact defect-shift and edge-count consequences -/

/-- Prescribing the canonical division, the combined defect graph, and the
cross profile turns the general edge decomposition into the paper's exact
fixed-fiber identity. -/
theorem supercriticalFixedDefectProfile_edgeCount_identity
    {k n : ℕ} {hn : k - 1 ≤ n}
    {D : SupercriticalDivision k (Fin n)}
    {T G : SimpleGraph (Fin n)} {profile : SupercriticalEdgeProfile D}
    (hD : canonicalSupercriticalDivision G (by simpa using hn) = D)
    (hT : canonicalCombinedDefectGraph G (by simpa using hn) = T)
    (hprofile : crossEdgeProfile G D = profile) :
    ((finiteGraphEdges G).card : ℤ) =
      (divisionInternalCliqueCapacity D : ℤ) +
        (profileTotal profile : ℤ) + supercriticalDefectShift T D := by
  have hcombined : combinedSupercriticalDefectGraph G D = T := by
    calc
      combinedSupercriticalDefectGraph G D =
          canonicalCombinedDefectGraph G (by simpa using hn) := by
        simp [canonicalCombinedDefectGraph, hD]
      _ = T := hT
  simpa [hprofile, hcombined] using
    (supercriticalDefectShift_edgeCount_identity G D)

/-- The literal shift equation for `profile` forces the graph to have exactly
`m` edges; no enlargement to the surrounding profile window is used. -/
theorem card_finiteGraphEdges_eq_of_fixedDefect_profileAtShift
    {k m n : ℕ} {hn : k - 1 ≤ n} {rho delta : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    {T G : SimpleGraph (Fin n)} {profile : SupercriticalEdgeProfile D}
    (hD : canonicalSupercriticalDivision G (by simpa using hn) = D)
    (hT : canonicalCombinedDefectGraph G (by simpa using hn) = T)
    (hprofile : crossEdgeProfile G D = profile)
    (hatShift : SupercriticalProfileAtShift D m rho delta
      (supercriticalDefectShift T D) profile) :
    (finiteGraphEdges G).card = m := by
  have hid := supercriticalFixedDefectProfile_edgeCount_identity
    (hn := hn) hD hT hprofile
  have hm := hatShift.1
  omega

theorem card_finiteGraphEdges_eq_of_mem_fixedDefectProfile
    {k : ℕ} {hk : 3 ≤ k} {gamma : ℝ}
    {hgamma : gamma ∈ Set.Ico (gammaK k) 1}
    {alpha rho delta : ℝ} {m n : ℕ} {tau : ℝ} {hn : k - 1 ≤ n}
    {D : SupercriticalDivision k (Fin n)} {T G : SimpleGraph (Fin n)}
    {profile : SupercriticalEdgeProfile D}
    (hG : G ∈ supercriticalFixedDefectProfileGraphFinset
      k hk gamma hgamma alpha m n tau hn D T profile)
    (hatShift : SupercriticalProfileAtShift D m rho delta
      (supercriticalDefectShift T D) profile) :
    (finiteGraphEdges G).card = m := by
  exact card_finiteGraphEdges_eq_of_fixedDefect_profileAtShift
    (hn := hn)
    (canonicalSupercriticalDivision_eq_of_mem_fixedDefectProfile hG)
    (canonicalCombinedDefectGraph_eq_of_mem_fixedDefectProfile hG)
    (crossEdgeProfile_eq_of_mem_supercriticalFixedDefectProfileGraphFinset hG)
    hatShift

theorem card_edgeFinset_eq_of_mem_fixedDefectProfile
    {k : ℕ} {hk : 3 ≤ k} {gamma : ℝ}
    {hgamma : gamma ∈ Set.Ico (gammaK k) 1}
    {alpha rho delta : ℝ} {m n : ℕ} {tau : ℝ} {hn : k - 1 ≤ n}
    {D : SupercriticalDivision k (Fin n)} {T G : SimpleGraph (Fin n)}
    {profile : SupercriticalEdgeProfile D}
    (hG : G ∈ supercriticalFixedDefectProfileGraphFinset
      k hk gamma hgamma alpha m n tau hn D T profile)
    (hatShift : SupercriticalProfileAtShift D m rho delta
      (supercriticalDefectShift T D) profile) :
    G.edgeFinset.card = m := by
  rw [← finiteGraphEdges_card_eq_edgeFinset_card G]
  exact card_finiteGraphEdges_eq_of_mem_fixedDefectProfile hG hatShift

theorem profileAtShift_crossEdgeProfile_of_mem_fixedDefectProfile
    {k : ℕ} {hk : 3 ≤ k} {gamma : ℝ}
    {hgamma : gamma ∈ Set.Ico (gammaK k) 1}
    {alpha rho delta : ℝ} {m n : ℕ} {tau : ℝ} {hn : k - 1 ≤ n}
    {D : SupercriticalDivision k (Fin n)} {T G : SimpleGraph (Fin n)}
    {profile : SupercriticalEdgeProfile D}
    (hG : G ∈ supercriticalFixedDefectProfileGraphFinset
      k hk gamma hgamma alpha m n tau hn D T profile)
    (hatShift : SupercriticalProfileAtShift D m rho delta
      (supercriticalDefectShift T D) profile) :
    SupercriticalProfileAtShift D m rho delta
      (supercriticalDefectShift T D) (crossEdgeProfile G D) := by
  rw [crossEdgeProfile_eq_of_mem_supercriticalFixedDefectProfileGraphFinset hG]
  exact hatShift

/-! ## Nonmedium plus no-high gives low degree -/

/-- The three existing degree regimes are exhaustive, so excluding the
middle and upper regimes leaves the low regime. -/
theorem low_of_not_medium_of_not_high
    {k : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (alpha : ℝ) (D : SupercriticalDivision k V)
    (v : V) (i : Fin (k - 1))
    (hmedium : ¬ HasMediumDegreeInPart G alpha D v i)
    (hhigh : ¬ HasHighDegreeInPart G alpha D v i) :
    HasLowDegreeInPart G alpha D v i := by
  rcases low_or_medium_or_high_degree_in_part G alpha D v i with
    hlow | hmiddle | hupper
  · exact hlow
  · exact False.elim (hmedium hmiddle)
  · exact False.elim (hhigh hupper)

/-- A member of the fixed-defect nonmedium family is low into every prescribed
main part once its close-structure witness supplies the no-high conclusion.
The canonical equalities in the fiber transport both conclusions to `T` and
`D`. -/
theorem low_degree_everywhere_of_mem_fixedDefect
    {k : ℕ} {hk : 3 ≤ k} {gamma : ℝ}
    {hgamma : gamma ∈ Set.Ico (gammaK k) 1}
    {alpha delta epsilon : ℝ} {m n : ℕ} {tau : ℝ}
    {hn : k - 1 ≤ n} {D : SupercriticalDivision k (Fin n)}
    {T G : SimpleGraph (Fin n)}
    (hG : G ∈ supercriticalFixedDefectGraphFinset
      k hk gamma hgamma alpha m n tau hn D T)
    (R : SupercriticalCloseStructureResult
      k hk gamma alpha delta epsilon hgamma G hn) :
    ∀ v : Fin n, ∀ i : Fin (k - 1),
      HasLowDegreeInPart T alpha D v i := by
  have hfixed := mem_supercriticalFixedDefectGraphFinset.mp hG
  have hdivision := mem_supercriticalDivisionDefectGraphFinset.mp hfixed.1
  have hD := hdivision.2.1
  have hT := hfixed.2.1
  have hnotMedium := hfixed.2.2
  intro v i
  have hmedium : ¬ HasMediumDegreeInPart
      (canonicalCombinedDefectGraph G (by simpa using hn)) alpha D v i :=
    fun hm ↦ hnotMedium ⟨v, i, hm⟩
  have hhigh : ¬ HasHighDegreeInPart
      (canonicalCombinedDefectGraph G (by simpa using hn)) alpha D v i := by
    have h := R.no_high_defect_degree v i
    rw [hD] at h
    exact h
  have hlow := low_of_not_medium_of_not_high
    (canonicalCombinedDefectGraph G (by simpa using hn)) alpha D v i
      hmedium hhigh
  rw [hT] at hlow
  exact hlow

/-- The profile-refined version of
`low_degree_everywhere_of_mem_fixedDefect`. -/
theorem low_degree_everywhere_of_mem_fixedDefectProfile
    {k : ℕ} {hk : 3 ≤ k} {gamma : ℝ}
    {hgamma : gamma ∈ Set.Ico (gammaK k) 1}
    {alpha delta epsilon : ℝ} {m n : ℕ} {tau : ℝ}
    {hn : k - 1 ≤ n} {D : SupercriticalDivision k (Fin n)}
    {T G : SimpleGraph (Fin n)} {profile : SupercriticalEdgeProfile D}
    (hG : G ∈ supercriticalFixedDefectProfileGraphFinset
      k hk gamma hgamma alpha m n tau hn D T profile)
    (R : SupercriticalCloseStructureResult
      k hk gamma alpha delta epsilon hgamma G hn) :
    ∀ v : Fin n, ∀ i : Fin (k - 1),
      HasLowDegreeInPart T alpha D v i :=
  low_degree_everywhere_of_mem_fixedDefect
    (mem_supercriticalFixedDefectProfileGraphFinset.mp hG).1 R

/-- If the fiber is nonempty, one member and its close-structure witness
supply the low-degree property of the fixed graph `T` used by the matching
construction. -/
theorem low_degree_everywhere_of_nonempty_fixedDefectProfile
    {k : ℕ} {hk : 3 ≤ k} {gamma : ℝ}
    {hgamma : gamma ∈ Set.Ico (gammaK k) 1}
    {alpha delta epsilon : ℝ} {m n : ℕ} {tau : ℝ}
    {hn : k - 1 ≤ n} {D : SupercriticalDivision k (Fin n)}
    {T : SimpleGraph (Fin n)} {profile : SupercriticalEdgeProfile D}
    (hne : (supercriticalFixedDefectProfileGraphFinset
      k hk gamma hgamma alpha m n tau hn D T profile).Nonempty)
    (hclose : ∀ G ∈ supercriticalFixedDefectProfileGraphFinset
      k hk gamma hgamma alpha m n tau hn D T profile,
      SupercriticalCloseStructureResult
        k hk gamma alpha delta epsilon hgamma G hn) :
    ∀ v : Fin n, ∀ i : Fin (k - 1),
      HasLowDegreeInPart T alpha D v i := by
  rcases hne with ⟨G, hG⟩
  exact low_degree_everywhere_of_mem_fixedDefectProfile hG (hclose G hG)

/-- The empty fiber is separated explicitly; otherwise the fixed defect graph
has low degree into every main part. -/
theorem fixedDefectProfile_empty_or_low_degree_everywhere
    {k : ℕ} {hk : 3 ≤ k} {gamma : ℝ}
    {hgamma : gamma ∈ Set.Ico (gammaK k) 1}
    {alpha delta epsilon : ℝ} {m n : ℕ} {tau : ℝ}
    {hn : k - 1 ≤ n} {D : SupercriticalDivision k (Fin n)}
    {T : SimpleGraph (Fin n)} {profile : SupercriticalEdgeProfile D}
    (hclose : ∀ G ∈ supercriticalFixedDefectProfileGraphFinset
      k hk gamma hgamma alpha m n tau hn D T profile,
      SupercriticalCloseStructureResult
        k hk gamma alpha delta epsilon hgamma G hn) :
    supercriticalFixedDefectProfileGraphFinset
        k hk gamma hgamma alpha m n tau hn D T profile = ∅ ∨
      ∀ v : Fin n, ∀ i : Fin (k - 1),
        HasLowDegreeInPart T alpha D v i := by
  by_cases hne : (supercriticalFixedDefectProfileGraphFinset
    k hk gamma hgamma alpha m n tau hn D T profile).Nonempty
  · exact Or.inr
      (low_degree_everywhere_of_nonempty_fixedDefectProfile hne hclose)
  · exact Or.inl (Finset.not_nonempty_iff_eq_empty.mp hne)

end InducedStars
