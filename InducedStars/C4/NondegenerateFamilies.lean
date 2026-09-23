import InducedStars.C4.SplitEnumeration
import InducedStars.FiniteModels.RepairCounting

/-!
# Finite families for the C4 nondegeneracy estimate

The canonical split completion encodes every close graph by a split graph
and at most its defect budget of unordered edits. Its edge count is allowed
to shift in either direction, with an explicit finite window.
-/

noncomputable section
namespace InducedStars
open Finset
open scoped Classical

/-- The exceptional family in `lemma:almost-all-nondeg`, with independent
positive closeness and nondegeneracy tolerances. -/
def c4CloseDegenerateGraphFinset (n m : ℕ) (gamma epsilon zeta : ℝ) :
    Finset (SimpleGraph (Fin n)) :=
  (inducedC4FreeGraphFinsetWithEdges n m).filter fun G ↦
    (c4DefectCost G (canonicalC4Division G) : ℝ) ≤ epsilon*(n : ℝ)^2 ∧
      zeta*n < |((canonicalC4Division G).cliquePart.card : ℝ) - c4Lambda gamma*n|

@[simp] theorem mem_c4CloseDegenerateGraphFinset {n m : ℕ} {gamma epsilon zeta : ℝ}
    {G : SimpleGraph (Fin n)} :
    G ∈ c4CloseDegenerateGraphFinset n m gamma epsilon zeta ↔
      G ∈ inducedC4FreeGraphFinsetWithEdges n m ∧
        (c4DefectCost G (canonicalC4Division G) : ℝ) ≤ epsilon*(n : ℝ)^2 ∧
          zeta*n < |((canonicalC4Division G).cliquePart.card : ℝ) - c4Lambda gamma*n| := by
  simp [c4CloseDegenerateGraphFinset]

def c4DegenerateDivisions (n : ℕ) (gamma zeta : ℝ) : Finset (C4Division (Fin n)) :=
  univ.filter fun D ↦ zeta*n < |(D.cliquePart.card : ℝ) - c4Lambda gamma*n|

def c4SplitRepairEdgeWindow (n m r : ℕ) : Finset ℕ :=
  (range (completeEdgeCount n+1)).filter fun j ↦ |(j : ℝ)-(m : ℝ)| ≤ r

def c4DegenerateSplitRepairTargets (n m r : ℕ) (gamma zeta : ℝ) :
    Finset (SimpleGraph (Fin n)) :=
  (c4DegenerateDivisions n gamma zeta).biUnion fun D ↦
    (c4SplitRepairEdgeWindow n m r).biUnion fun j ↦ c4SplitFiber D j

theorem c4SplitCompletion_edgeCount_abs_le {n : ℕ} (G : SimpleGraph (Fin n))
    (D : C4Division (Fin n)) :
    |((finiteGraphEdges (c4SplitCompletion G D)).card : ℝ) -
      (finiteGraphEdges G).card| ≤ c4DefectCost G D := by
  have h := c4EdgeCount_add_cliqueDefects G D
  have hc : (finiteGraphEdges (c4SplitCompletion G D)).card =
      Nat.choose D.cliquePart.card 2 + (c4CrossEdges G D).card :=
    card_edges_c4SplitGraphOfCrossChoice D (c4CrossEdges_subset G D)
  have hR := congrArg (fun t : ℕ ↦ (t : ℝ)) h
  have hcR := congrArg (fun t : ℕ ↦ (t : ℝ)) hc
  push_cast at hR hcR
  rw [c4DefectCost_eq_induced_edgeCounts, Nat.cast_add, abs_le]
  constructor <;> linarith [show
    (0 : ℝ) ≤ (finiteGraphEdges (G.induce (D.independentPart : Set (Fin n)))).card by positivity,
    show (0 : ℝ) ≤ (finiteGraphEdges (Gᶜ.induce (D.cliquePart : Set (Fin n)))).card by positivity]

theorem c4CloseDegenerate_card_le_repairTargets {n m : ℕ} {gamma epsilon zeta : ℝ} :
    (c4CloseDegenerateGraphFinset n m gamma epsilon zeta).card ≤
      (c4DegenerateSplitRepairTargets n m ⌊epsilon*(n : ℝ)^2⌋₊ gamma zeta).card *
        hammingBallVolume (completeEdgeCount n) ⌊epsilon*(n : ℝ)^2⌋₊ := by
  apply card_le_card_mul_hammingBallVolume_of_graphRepair _ _
    (fun G ↦ c4SplitCompletion G (canonicalC4Division G))
  · intro G hG
    obtain ⟨hG, hcost, hdeg⟩ := mem_c4CloseDegenerateGraphFinset.mp hG
    let D := canonicalC4Division G
    let H := c4SplitCompletion G D
    have hm := (mem_inducedC4FreeGraphFinsetWithEdges.mp hG).2
    have hr : c4DefectCost G D ≤ ⌊epsilon*(n : ℝ)^2⌋₊ := Nat.le_floor hcost
    have hshift := c4SplitCompletion_edgeCount_abs_le G D
    rw [hm] at hshift
    have hN : (finiteGraphEdges H).card ≤ completeEdgeCount n := by
      rw [finiteGraphEdges_card_eq_edgeFinset_card]
      exact card_edgeFinset_le_completeEdgeCount H
    apply mem_biUnion.mpr
    refine ⟨D, by simpa [c4DegenerateDivisions, D] using hdeg, mem_biUnion.mpr ?_⟩
    refine ⟨(finiteGraphEdges H).card, ?_, ?_⟩
    · simp only [c4SplitRepairEdgeWindow, mem_filter, mem_range]
      exact ⟨by omega, hshift.trans (by exact_mod_cast hr)⟩
    · exact mem_c4SplitFiber.mpr
        ⟨(c4SplitCompletion_geometry G D).1, (c4SplitCompletion_geometry G D).2, rfl⟩
  · intro G hG
    have hcost := (mem_c4CloseDegenerateGraphFinset.mp hG).2.1
    rw [← DenseGraph.simpleGraphEditDistance_eq_graphEditDistance,
      ← c4DefectCost_eq_splitCompletion_editDistance]
    exact Nat.le_floor hcost

/-- A finite, signed-shift upper bound. Counting several split covers or
several admissible edge levels only overcounts the repair target family. -/
theorem c4CloseDegenerate_card_le_sum_splitFibers {n m : ℕ} {gamma epsilon zeta : ℝ} :
    (c4CloseDegenerateGraphFinset n m gamma epsilon zeta).card ≤
      (∑ D ∈ c4DegenerateDivisions n gamma zeta,
        ∑ j ∈ c4SplitRepairEdgeWindow n m ⌊epsilon*(n : ℝ)^2⌋₊,
          (c4SplitFiber D j).card) *
        hammingBallVolume (completeEdgeCount n) ⌊epsilon*(n : ℝ)^2⌋₊ := by
  apply c4CloseDegenerate_card_le_repairTargets.trans
  apply Nat.mul_le_mul_right
  apply card_biUnion_le.trans
  exact sum_le_sum fun D _ ↦ card_biUnion_le

end InducedStars
