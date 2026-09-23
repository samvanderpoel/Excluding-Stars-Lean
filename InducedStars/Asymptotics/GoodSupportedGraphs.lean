import InducedStars.FiniteModels.ExactEdgeRepair
import InducedStars.FiniteModels.RepairCounting
import Mathlib.Tactic

/-!
# Good supported graph samples

This module packages the deterministic half of the fixed-density transfer.
A good sampled graph carries one latent configuration at which it has
positive conditional mass, the entire positive conditional support is
induced-free, enough present and absent flexible pairs are available, and
the graph is close both in edge count and cut distance to the target data.

The probabilistic layer only has to show that the resulting finite graph set
has probability tending to one.  Everything after that point is a finite
choice and counting argument.
-/

noncomputable section

open Filter MeasureTheory Set Topology
open scoped BigOperators

namespace InducedStars

/-- A latent witness certifying that a sampled graph can be repaired inside
the positive conditional support.  `q` records an explicit abundance of
flexible latent pairs, while the two separate `enough` fields are precisely
the hypotheses required for adding or deleting edges. -/
structure GoodSupportedGraphWitness {h n : ℕ}
    (H : SimpleGraph (Fin h)) (W : Graphon) (L U : ℝ)
    (m r q : ℕ) (η : ℝ) (G : SimpleGraph (Fin n)) where
  latent : Fin n → UnitInterval
  support_inducedFree : ∀ K : SimpleGraph (Fin n),
    0 < wRandomConditionalWeight W latent K →
      ¬Regularity.InducedEmbeds H K
  weight_pos : 0 < wRandomConditionalWeight W latent G
  flexiblePairCount_lower :
    q ≤ flexiblePairCount W L U latent
  enoughPresent :
    (finiteGraphEdges G).card - m ≤
      (presentFlexibleEdgeFinset W latent L U G).card
  enoughAbsent :
    m - (finiteGraphEdges G).card ≤
      (absentFlexibleEdgeFinset W latent L U G).card
  edgeDistance_le : Nat.dist (finiteGraphEdges G).card m ≤ r
  cutDist_lt : cutDist (graphGraphon G) W < η

/-- The finite graph-only event consisting of graphs which have a good
latent support witness. -/
noncomputable def goodSupportedGraphs {h : ℕ}
    (H : SimpleGraph (Fin h)) (W : Graphon) (L U : ℝ)
    (m r q : ℕ) (η : ℝ) (n : ℕ) :
    Finset (SimpleGraph (Fin n)) := by
  classical
  exact Finset.univ.filter fun G ↦
    Nonempty (GoodSupportedGraphWitness H W L U m r q η G)

@[simp] theorem mem_goodSupportedGraphs {h n : ℕ}
    {H : SimpleGraph (Fin h)} {W : Graphon} {L U : ℝ}
    {m r q : ℕ} {η : ℝ} {G : SimpleGraph (Fin n)} :
    G ∈ goodSupportedGraphs H W L U m r q η n ↔
      Nonempty (GoodSupportedGraphWitness H W L U m r q η G) := by
  classical
  simp [goodSupportedGraphs]

/-- Choice-fixed latent witness used by the deterministic repair map. -/
noncomputable def selectedGoodSupportedWitness {h n : ℕ}
    (H : SimpleGraph (Fin h)) (W : Graphon) (L U : ℝ)
    (m r q : ℕ) (η : ℝ) (G : SimpleGraph (Fin n))
    (hG : Nonempty (GoodSupportedGraphWitness H W L U m r q η G)) :
    GoodSupportedGraphWitness H W L U m r q η G :=
  Classical.choice hG

/-- Total deterministic repair map.  Outside the good graph event it is the
identity; on the good event it repairs using the selected latent witness. -/
noncomputable def repairGoodSupportedGraph {h n : ℕ}
    (H : SimpleGraph (Fin h)) (W : Graphon) (L U : ℝ)
    (m r q : ℕ) (η : ℝ) (G : SimpleGraph (Fin n)) :
    SimpleGraph (Fin n) := by
  classical
  exact if hG : Nonempty
      (GoodSupportedGraphWitness H W L U m r q η G) then
    repairToExactEdgeCount W
      (selectedGoodSupportedWitness H W L U m r q η G hG).latent
      L U G m
  else G

private theorem repairGoodSupportedGraph_eq {h n : ℕ}
    (H : SimpleGraph (Fin h)) (W : Graphon) (L U : ℝ)
    (m r q : ℕ) (η : ℝ) (G : SimpleGraph (Fin n))
    (hG : Nonempty (GoodSupportedGraphWitness H W L U m r q η G)) :
    repairGoodSupportedGraph H W L U m r q η G =
      repairToExactEdgeCount W
        (selectedGoodSupportedWitness H W L U m r q η G hG).latent
        L U G m := by
  classical
  rw [repairGoodSupportedGraph]
  simp only [dif_pos hG]

/-- A good graph is sent to the exact-edge induced-free family. -/
theorem repairGoodSupportedGraph_mem_exactFamily {h n : ℕ}
    (H : SimpleGraph (Fin h)) (W : Graphon) (L U : ℝ)
    (m r q : ℕ) (η : ℝ) (G : SimpleGraph (Fin n))
    (hG : G ∈ goodSupportedGraphs H W L U m r q η n)
    (hL : 0 < L) (hU : U < 1) :
    repairGoodSupportedGraph H W L U m r q η G ∈
      inducedFreeGraphFinsetWithEdges H n m := by
  classical
  have hG' : Nonempty
      (GoodSupportedGraphWitness H W L U m r q η G) :=
    mem_goodSupportedGraphs.mp hG
  let A := selectedGoodSupportedWitness H W L U m r q η G hG'
  have hWeight : 0 < wRandomConditionalWeight W A.latent
      (repairToExactEdgeCount W A.latent L U G m) :=
    wRandomConditionalWeight_repairToExactEdgeCount_pos
      W A.latent L U G m hL hU A.weight_pos
  have hFree : ¬Regularity.InducedEmbeds H
      (repairToExactEdgeCount W A.latent L U G m) :=
    A.support_inducedFree _ hWeight
  have hCard :
      (finiteGraphEdges
        (repairToExactEdgeCount W A.latent L U G m)).card = m :=
    repairToExactEdgeCount_edge_card W A.latent L U G m
      A.enoughPresent A.enoughAbsent
  rw [repairGoodSupportedGraph_eq H W L U m r q η G hG']
  exact mem_inducedFreeGraphFinsetWithEdges_iff_finiteGraphEdges.mpr
    ⟨hFree, hCard⟩

/-- The selected repair of a good graph stays within the prescribed
unordered-edge Hamming radius. -/
theorem graphEditDistance_repairGoodSupportedGraph_le {h n : ℕ}
    (H : SimpleGraph (Fin h)) (W : Graphon) (L U : ℝ)
    (m r q : ℕ) (η : ℝ) (G : SimpleGraph (Fin n))
    (hG : G ∈ goodSupportedGraphs H W L U m r q η n) :
    graphEditDistance G
      (repairGoodSupportedGraph H W L U m r q η G) ≤ r := by
  classical
  have hG' : Nonempty
      (GoodSupportedGraphWitness H W L U m r q η G) :=
    mem_goodSupportedGraphs.mp hG
  let A := selectedGoodSupportedWitness H W L U m r q η G hG'
  rw [repairGoodSupportedGraph_eq H W L U m r q η G hG',
    graphEditDistance_repairToExactEdgeCount W A.latent L U G m
      A.enoughPresent A.enoughAbsent]
  exact A.edgeDistance_le

/-- The repaired graph remains close to the target graphon, with the exact
finite edit penalty. -/
theorem cutDist_repairGoodSupportedGraph_lt_add {h n : ℕ}
    (hn : 0 < n) (H : SimpleGraph (Fin h)) (W : Graphon) (L U : ℝ)
    (m r q : ℕ) (η : ℝ) (G : SimpleGraph (Fin n))
    (hG : G ∈ goodSupportedGraphs H W L U m r q η n) :
    cutDist (graphGraphon
        (repairGoodSupportedGraph H W L U m r q η G)) W <
      η + 2 * (r : ℝ) / (n : ℝ) ^ 2 := by
  classical
  have hG' : Nonempty
      (GoodSupportedGraphWitness H W L U m r q η G) :=
    mem_goodSupportedGraphs.mp hG
  let A := selectedGoodSupportedWitness H W L U m r q η G hG'
  have hRepair := cutDist_graphGraphon_repairToExactEdgeCount_le
    hn W A.latent L U G m A.enoughPresent A.enoughAbsent
  have hEditCast : (Nat.dist (finiteGraphEdges G).card m : ℝ) ≤ (r : ℝ) := by
    exact_mod_cast A.edgeDistance_le
  have hDenom : 0 ≤ (n : ℝ) ^ 2 := sq_nonneg _
  have hRepair' : cutDist (graphGraphon G)
      (graphGraphon (repairToExactEdgeCount W A.latent L U G m)) ≤
        2 * (r : ℝ) / (n : ℝ) ^ 2 := by
    exact hRepair.trans (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hEditCast (by norm_num)) hDenom)
  rw [repairGoodSupportedGraph_eq H W L U m r q η G hG']
  calc
    cutDist (graphGraphon (repairToExactEdgeCount W A.latent L U G m)) W ≤
        cutDist (graphGraphon (repairToExactEdgeCount W A.latent L U G m))
          (graphGraphon G) + cutDist (graphGraphon G) W :=
      cutDist_triangle _ _ _
    _ = cutDist (graphGraphon G)
          (graphGraphon (repairToExactEdgeCount W A.latent L U G m)) +
          cutDist (graphGraphon G) W := by
      rw [cutDist_comm]
    _ < η + 2 * (r : ℝ) / (n : ℝ) ^ 2 := by
      linarith [A.cutDist_lt, hRepair']

/-- Finite bounded-fiber comparison for the selected exact-edge repair. -/
theorem goodSupportedGraphs_card_le_exactFamily_mul_hammingBall
    {h n : ℕ} (H : SimpleGraph (Fin h)) (W : Graphon) (L U : ℝ)
    (m r q : ℕ) (η : ℝ) (hL : 0 < L) (hU : U < 1) :
    (goodSupportedGraphs H W L U m r q η n).card ≤
      (inducedFreeGraphFinsetWithEdges H n m).card *
        hammingBallVolume (completeEdgeCount n) r := by
  exact card_le_card_mul_hammingBallVolume_of_graphRepair
    (goodSupportedGraphs H W L U m r q η n)
    (inducedFreeGraphFinsetWithEdges H n m)
    (repairGoodSupportedGraph H W L U m r q η)
    (fun G hG ↦ repairGoodSupportedGraph_mem_exactFamily
      H W L U m r q η G hG hL hU)
    (fun G hG ↦ graphEditDistance_repairGoodSupportedGraph_le
      H W L U m r q η G hG)

end InducedStars
