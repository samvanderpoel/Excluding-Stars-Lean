import InducedStars.Structure.Subcritical.FixedRemainderCompletion
import InducedStars.Structure.Subcritical.MinimizerCloseness
import InducedStars.Structure.Subcritical.ProfilePenalty

/-!
# The same division for an entire fixed-key, fixed-remainder fiber

Global minimality of the auxiliary completion supplies the existing
finite geometry to every graph of the original canonical-key fiber. The
ambient family remains unchanged in all profile probability maxima.
-/

noncomputable section
open Finset Set
open scoped Classical
namespace InducedStars

variable {k n R₀ m : ℕ} {omega eta theta alpha delta epsilon tau : ℝ}
  {L : AdmissibleBlockSequence k}

theorem subcriticalFixedKeyRemainder_aggregationGeometry
    (hk : 3 ≤ k) (hn : k - 1 ≤ n)
    (K : SubcriticalRetainedKey k (Fin n))
    (H : SimpleGraph {v : Fin n // v ∈ K.remainder})
    (hK : (subcriticalRetainedKeyCompletions K eta R₀).Nonempty)
    (hbridge : ∀ (G : SimpleGraph (Fin n)) (D : SubcriticalDivision k (Fin n)),
      (∀ E : SubcriticalDivision k (Fin n),
        subcriticalDefectCost G D ≤ subcriticalDefectCost G E) →
      cutDist (graphGraphon G) (WLambda hk L) < tau →
        Nonempty (SubcriticalCloseStructureResult hk G D
          L R₀ omega eta theta alpha delta epsilon)) :
    SubcriticalAggregationGeometry hk
      (subcriticalFixedKeyRemainderGraphFinset
        (subcriticalCandidateCutBallGraphFinset k n m (WLambda hk L) tau)
        K eta R₀ hk (by simpa using hn) H)
      (subcriticalFixedRemainderCompletion K eta R₀ H hK)
      L R₀ m omega eta theta alpha delta epsilon := by
  let F := subcriticalCandidateCutBallGraphFinset k n m (WLambda hk L) tau
  have hdata G (hG : G ∈ subcriticalFixedKeyRemainderGraphFinset
      F K eta R₀ hk (by simpa using hn) H) :=
    (mem_subcriticalFixedKeyRemainderGraphFinset F K eta R₀ hk (by simpa using hn) H G).mp hG
  have hmin G (hG : G ∈ subcriticalFixedKeyRemainderGraphFinset
      F K eta R₀ hk (by simpa using hn) H) :=
    subcriticalFixedKeyRemainder_completion_global_minimal F K eta R₀ hk
      (by simpa using hn) H hK hG
  constructor
  · intro G hG
    exact hbridge G _ (hmin G hG)
      (mem_subcriticalCandidateCutBallGraphFinset.mp (hdata G hG).1).2
  · intro G hG
    exact (mem_inducedStarFreeGraphFinsetWithEdges.mp
      (mem_subcriticalCandidateCutBallGraphFinset.mp (hdata G hG).1).1).1
  · intro G hG
    simpa only [finiteGraphEdges_card_eq_edgeFinset_card] using
      (mem_inducedStarFreeGraphFinsetWithEdges.mp
        (mem_subcriticalCandidateCutBallGraphFinset.mp (hdata G hG).1).1).2
  · exact hmin

/-- The fixed H is transported to the completion's nonretained subtype;
neither its edges nor their number is chosen again. -/
theorem subcriticalFixedKeyRemainder_remainder_eq
    (F : Finset (SimpleGraph (Fin n)))
    (hk : 3 ≤ k) (hn : k - 1 ≤ n)
    (K : SubcriticalRetainedKey k (Fin n))
    (H : SimpleGraph {v : Fin n // v ∈ K.remainder})
    (hK : (subcriticalRetainedKeyCompletions K eta R₀).Nonempty)
    {G : SimpleGraph (Fin n)}
    (hG : G ∈ subcriticalFixedKeyRemainderGraphFinset
      F K eta R₀ hk (by simpa using hn) H) :
    subcriticalRemainderGraph G (subcriticalFixedRemainderCompletion K eta R₀ H hK) eta R₀ =
      retainedKeyRemainderTransport K (subcriticalFixedRemainderCompletion K eta R₀ H hK)
        eta R₀ (subcriticalFixedRemainderCompletion_mem K eta R₀ H hK).2 H := by
  exact subcriticalRemainderGraph_eq_transport K _ eta R₀
    (subcriticalFixedRemainderCompletion_mem K eta R₀ H hK).2 H G
    ((mem_subcriticalFixedKeyRemainderGraphFinset
      F K eta R₀ hk (by simpa using hn) H G).mp hG).2.2

end InducedStars
