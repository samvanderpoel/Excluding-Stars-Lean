import InducedStars.Structure.Supercritical.MediumParameters

/-!
# Enumeration of small C4 defect patterns

Shared by the two high-degree arguments. A defect pattern is encoded by its
actual unordered edge set; the count is a Hamming-ball volume, not a new
external asymptotic counting assumption.
-/

noncomputable section
open Finset
open scoped Classical
namespace InducedStars

def c4SmallDefectGraphFinset (n : ℕ) (epsilon : ℝ) : Finset (SimpleGraph (Fin n)) :=
  univ.filter fun T => (finiteGraphEdges T).card ≤ ⌊epsilon*(n : ℝ)^2⌋₊

@[simp] theorem mem_c4SmallDefectGraphFinset {n : ℕ} {epsilon : ℝ}
    {T : SimpleGraph (Fin n)} : T ∈ c4SmallDefectGraphFinset n epsilon ↔
      (finiteGraphEdges T).card ≤ ⌊epsilon*(n : ℝ)^2⌋₊ := by
  simp only [c4SmallDefectGraphFinset, Finset.mem_filter, Finset.mem_univ, true_and]

theorem card_c4SmallDefectGraphFinset_le (n : ℕ) (epsilon : ℝ) :
    (c4SmallDefectGraphFinset n epsilon).card ≤
      hammingBallVolume (completeEdgeCount n) ⌊epsilon*(n : ℝ)^2⌋₊ := by
  apply (Finset.card_le_card (show c4SmallDefectGraphFinset n epsilon ⊆
    graphHammingBall (⊥ : SimpleGraph (Fin n)) ⌊epsilon*(n : ℝ)^2⌋₊ from ?_)).trans
    (graphHammingBall_card_le_hammingBallVolume _)
  intro T hT
  rw [mem_graphHammingBall, graphEditDistance_bot_eq_edge_count]
  exact mem_c4SmallDefectGraphFinset.mp hT

theorem c4SmallDefectGraphFinset_edgeCount_le {n : ℕ} {epsilon : ℝ}
    (hepsilon : 0 ≤ epsilon) {T : SimpleGraph (Fin n)}
    (hT : T ∈ c4SmallDefectGraphFinset n epsilon) :
    ((finiteGraphEdges T).card : ℝ) ≤ epsilon*(n : ℝ)^2 := by
  exact (Nat.cast_le.mpr (mem_c4SmallDefectGraphFinset.mp hT)).trans
    (Nat.floor_le (by positivity))

/-- Vertex choices, subset choices, one quadratic conditioning factor,
and a fixed linear shift cost have a uniform linear exponential envelope. -/
theorem c4DefectEnumeration_linearOverhead_le (n : ℕ) (C : ℝ) :
    ((n : ℝ)*(2 : ℝ)^n)*((n : ℝ)^2+1)*Real.exp (C*n) ≤
      Real.exp ((C+Real.log 2+3)*n) := by
  have hnexp : (n : ℝ) ≤ Real.exp (n : ℝ) := by linarith [Real.add_one_le_exp (n : ℝ)]
  have hpoly : (n : ℝ)^2+1 ≤ Real.exp (2*n) := by
    have hfirst : (n : ℝ)^2+1 ≤ ((n : ℝ)+1)^2 := by
      nlinarith [Nat.cast_nonneg (α := ℝ) n]
    have hn1exp : (n : ℝ)+1 ≤ Real.exp (n : ℝ) := Real.add_one_le_exp _
    calc
      _ ≤ ((n : ℝ)+1)^2 := hfirst
      _ ≤ (Real.exp (n : ℝ))^2 := by gcongr
      _ = _ := (Real.exp_nat_mul (n : ℝ) 2).symm
  have htwo : (2 : ℝ)^n = Real.exp ((n : ℝ)*Real.log 2) := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ)<2)]
  calc
    _ ≤ (Real.exp (n : ℝ)*Real.exp ((n : ℝ)*Real.log 2))*
        Real.exp (2*n)*Real.exp (C*n) := by rw [htwo]; gcongr
    _ = _ := by rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; congr 1; ring

end InducedStars
