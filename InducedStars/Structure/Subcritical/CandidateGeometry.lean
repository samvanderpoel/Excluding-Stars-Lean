import InducedStars.Structure.Subcritical.ProfilePenalty

/-!
# One canonical geometry and the full compatible-division family

Compatibility is filtered as a proposition; its injection and core
isomorphisms are not counted. The family contains every ordered compatible
division, whether or not it occurs as a canonical division of a graph.
-/

noncomputable section
open Finset Set
open scoped Classical
namespace InducedStars

variable {k n R₀ m : ℕ} {omega eta theta alpha delta epsilon tau : ℝ}
  {L : AdmissibleBlockSequence k}

theorem subcriticalCandidateDivision_aggregationGeometry
    (hk : 3 ≤ k) (hn : k - 1 ≤ n) (D : SubcriticalDivision k (Fin n))
    (hbridge : ∀ G : SimpleGraph (Fin n),
      cutDist (graphGraphon G) (WLambda hk L) < tau →
        Nonempty (SubcriticalCloseStructureResult hk G
          (canonicalSubcriticalDivision G R₀ hk (by simpa using hn))
          L R₀ omega eta theta alpha delta epsilon)) :
    SubcriticalAggregationGeometry hk
      (subcriticalCandidateDivisionGraphFinset k n m (WLambda hk L) tau R₀ hk hn D)
      D L R₀ m omega eta theta alpha delta epsilon := by
  have hdata G (hG : G ∈ subcriticalCandidateDivisionGraphFinset
      k n m (WLambda hk L) tau R₀ hk hn D) :=
    mem_subcriticalCandidateDivisionGraphFinset.mp hG
  constructor
  · intro G hG
    have h := hdata G hG
    simpa only [h.2] using hbridge G (mem_subcriticalCandidateCutBallGraphFinset.mp h.1).2
  · intro G hG
    exact (mem_inducedStarFreeGraphFinsetWithEdges.mp
      (mem_subcriticalCandidateCutBallGraphFinset.mp (hdata G hG).1).1).1
  · intro G hG
    simpa only [finiteGraphEdges_card_eq_edgeFinset_card] using
      (mem_inducedStarFreeGraphFinsetWithEdges.mp
        (mem_subcriticalCandidateCutBallGraphFinset.mp (hdata G hG).1).1).2
  · intro G hG E
    simpa only [(hdata G hG).2] using
      canonicalSubcriticalDivision_minimal G R₀ hk (by simpa using hn) E

/-- The paper's full ordered compatibility family, not its realized subset. -/
def subcriticalCompatibleDivisions (k n : ℕ) (L : AdmissibleBlockSequence k)
    (eta delta : ℝ) (R₀ : ℕ) : Finset (SubcriticalDivision k (Fin n)) := by
  letI : Fintype (SubcriticalDivision k (Fin n)) := Fintype.ofFinite _
  exact Finset.univ.filter fun D ↦
    D.IsOrderedByCutoff R₀ ∧ Nonempty (D.CandidateCompatibility L eta delta R₀)

@[simp] theorem mem_subcriticalCompatibleDivisions (D : SubcriticalDivision k (Fin n)) :
    D ∈ subcriticalCompatibleDivisions k n L eta delta R₀ ↔
      D.IsOrderedByCutoff R₀ ∧ Nonempty (D.CandidateCompatibility L eta delta R₀) := by
  simp [subcriticalCompatibleDivisions]

theorem subcriticalCanonicalDivision_mem_compatible
    (hk : 3 ≤ k) (hn : k - 1 ≤ n)
    (hbridge : ∀ G : SimpleGraph (Fin n),
      cutDist (graphGraphon G) (WLambda hk L) < tau →
        Nonempty (SubcriticalCloseStructureResult hk G
          (canonicalSubcriticalDivision G R₀ hk (by simpa using hn))
          L R₀ omega eta theta alpha delta epsilon))
    {G : SimpleGraph (Fin n)}
    (hG : G ∈ subcriticalCandidateCutBallGraphFinset k n m (WLambda hk L) tau) :
    canonicalSubcriticalDivision G R₀ hk (by simpa using hn) ∈
      subcriticalCompatibleDivisions k n L eta delta R₀ := by
  refine mem_subcriticalCompatibleDivisions _ |>.mpr ⟨?_, ?_⟩
  · exact canonicalSubcriticalDivision_isOrdered G R₀ hk _
  · exact ⟨(hbridge G (mem_subcriticalCandidateCutBallGraphFinset.mp hG).2).some.compatibility⟩

theorem subcriticalCandidateCutBall_eq_biUnion_divisions
    (hk : 3 ≤ k) (hn : k - 1 ≤ n)
    (hbridge : ∀ G : SimpleGraph (Fin n),
      cutDist (graphGraphon G) (WLambda hk L) < tau →
        Nonempty (SubcriticalCloseStructureResult hk G
          (canonicalSubcriticalDivision G R₀ hk (by simpa using hn))
          L R₀ omega eta theta alpha delta epsilon)) :
    subcriticalCandidateCutBallGraphFinset k n m (WLambda hk L) tau =
      (subcriticalCompatibleDivisions k n L eta delta R₀).biUnion fun D ↦
        subcriticalCandidateDivisionGraphFinset k n m (WLambda hk L) tau R₀ hk hn D := by
  ext G
  constructor
  · intro hG
    exact Finset.mem_biUnion.mpr ⟨_, subcriticalCanonicalDivision_mem_compatible hk hn hbridge hG,
      mem_subcriticalCandidateDivisionGraphFinset.mpr ⟨hG, rfl⟩⟩
  · intro hG
    obtain ⟨D, _, hD⟩ := Finset.mem_biUnion.mp hG
    exact (mem_subcriticalCandidateDivisionGraphFinset.mp hD).1

theorem subcriticalCandidateDivision_pairwiseDisjoint
    (hk : 3 ≤ k) (hn : k - 1 ≤ n) {D E : SubcriticalDivision k (Fin n)}
    (hDE : D ≠ E) :
    Disjoint (subcriticalCandidateDivisionGraphFinset k n m (WLambda hk L) tau R₀ hk hn D)
      (subcriticalCandidateDivisionGraphFinset k n m (WLambda hk L) tau R₀ hk hn E) := by
  apply Finset.disjoint_left.mpr
  intro G hD hE
  exact hDE ((mem_subcriticalCandidateDivisionGraphFinset.mp hD).2.symm.trans
    (mem_subcriticalCandidateDivisionGraphFinset.mp hE).2)

end InducedStars
