import InducedStars.Structure.Subcritical.ProfilePenalty

/-!
# Compatible divisions that define the current retained-key family

Compatibility is filtered as a proposition; its injection and core
isomorphisms are not counted. Taking retained keys of this finite family supplies every compatible key
used in the current grouped cut-ball bound.
-/

noncomputable section
open Finset Set
open scoped Classical
namespace InducedStars

variable {k n R₀ m : ℕ} {omega eta theta alpha delta epsilon tau : ℝ}
  {L : AdmissibleBlockSequence k}

/-- Compatible ordered completions used to define the paper's retained-key family. -/
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

end InducedStars
