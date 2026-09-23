import InducedStars.Structure.Gnp.CutBalls
import InducedStars.Structure.Subcritical.SparseMatchingTransfer

/-!
# Weighted matching transfer into the zero cut ball

Paper: `eqn:critical-matching-transfer-K1k` in `paper/gnp.tex`.
The already proved injective matching construction is applied at every
remainder edge count. Distinct remainder levels have distinct output edge
counts, so their full binomial-model masses can be summed without overlap.
-/

noncomputable section

open Finset Set
open scoped BigOperators

namespace InducedStars

attribute [local instance] Classical.propDecidable

noncomputable local instance weightedMatchingEdgeSetFintype {n : ℕ}
    (G : SimpleGraph (Fin n)) : Fintype G.edgeSet := graphFamiliesEdgeSetFintype G

/-- The odds-weight normalization equals the actual common `G(n,p)` weight
at every feasible exact edge count. Feasibility is essential because the
right exponent uses natural subtraction. -/
theorem gnpCommonWeight_eq_of_le {N m : ℕ} (hm : m ≤ N)
    {p : ℝ} (hp : p < 1) :
    (1 - p)^N * (p / (1 - p))^m = p^m * (1 - p)^(N - m) := by
  have hq : 1 - p ≠ 0 := (sub_pos.mpr hp).ne'
  have hpow : (1 - p)^N = (1 - p)^(N - m) * (1 - p)^m := by
    rw [← pow_add, Nat.sub_add_cancel hm]
  rw [hpow, div_pow]
  field_simp

/-- At a sufficiently small exact edge count, the entire induced-free
fiber belongs to the zero cut ball. -/
theorem graphFamilyEdgeSlice_zeroCutBall_eq_inducedStarFree
    {k n m : ℕ} (hn : 0 < n) {ω : ℝ}
    (hm : 2 * (m : ℝ) / (n : ℝ)^2 < ω) :
    graphFamilyEdgeSlice (gnpInducedStarCutBallFinset k zeroGraphon ω n) m =
      inducedStarFreeGraphFinsetWithEdges k n m := by
  ext G
  rw [mem_graphFamilyEdgeSlice, mem_gnpInducedStarCutBallFinset,
    mem_inducedStarFreeGraphFinsetWithEdges]
  constructor
  · rintro ⟨⟨hfree, _⟩, hcount⟩
    exact ⟨hfree, hcount⟩
  · rintro ⟨hfree, hcount⟩
    refine ⟨⟨hfree, ?_⟩, hcount⟩
    rw [DenseGraph.cutDist_graphGraphon_zeroGraphon hn]
    have hedge : finiteGraphEdges G = G.edgeFinset := by
      ext e
      rw [mem_finiteGraphEdges, SimpleGraph.mem_edgeFinset]
    rw [hedge, hcount]
    exact hm

/-- Adding a matching on fixed new vertices gives an exact weighted lower
bound for the zero cut ball, uniformly over any finite set of remainder
edge counts satisfying the displayed smallness condition. -/
theorem gnpSparseMatchingTransfer_zeroCutBall
    {k n s q : ℕ} (hk : 3 ≤ k) (hn : 0 < n)
    (hs : s + 2 * q ≤ n) {p ω : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1)
    (B : Finset ℕ)
    (hfeasible : ∀ b ∈ B, b + q ≤ completeEdgeCount n)
    (hsmall : ∀ b ∈ B, 2 * ((b + q : ℕ) : ℝ) / (n : ℝ)^2 < ω) :
    (((2 * q).factorial / (2 ^ q * q.factorial) : ℕ) : ℝ) *
        (p / (1 - p))^q * (1 - p)^(completeEdgeCount n) *
        (∑ b ∈ B, (inducedStarFreeGraphCountWithEdges k s b : ℝ) *
          (p / (1 - p))^b) ≤
      gnpInducedStarCutBallMass k n p zeroGraphon ω := by
  let Q := gnpInducedStarCutBallFinset k zeroGraphon ω n
  let M : ℕ := (2 * q).factorial / (2 ^ q * q.factorial)
  have hlevel (b : ℕ) (hb : b ∈ B) :
      (M : ℝ) * (inducedStarFreeGraphCountWithEdges k s b : ℝ) *
        ((1 - p)^(completeEdgeCount n) * (p / (1 - p))^(b + q)) ≤
          gnpGraphFamilySliceWeight Q (b + q) p := by
    have hcount : (M : ℝ) * (inducedStarFreeGraphCountWithEdges k s b : ℝ) ≤
        (inducedStarFreeGraphCountWithEdges k n (b + q) : ℝ) := by
      exact_mod_cast subcriticalSparseMatchingTransfer (b := b) hk hs
    rw [gnpCommonWeight_eq_of_le (hfeasible b hb) hp.2,
      gnpGraphFamilySliceWeight,
      show graphFamilyEdgeSlice Q (b + q) =
        inducedStarFreeGraphFinsetWithEdges k n (b + q) from
          graphFamilyEdgeSlice_zeroCutBall_eq_inducedStarFree hn (hsmall b hb)]
    have hweight : 0 ≤ p^(b + q) * (1 - p)^(completeEdgeCount n - (b + q)) :=
      mul_nonneg (pow_nonneg hp.1.le _) (pow_nonneg (sub_pos.mpr hp.2).le _)
    simpa only [mul_assoc, inducedStarFreeGraphCountWithEdges, inducedFreeGraphCountWithEdges]
      using mul_le_mul_of_nonneg_right hcount hweight
  calc
    _ = ∑ b ∈ B, (M : ℝ) * (inducedStarFreeGraphCountWithEdges k s b : ℝ) *
        ((1 - p)^(completeEdgeCount n) * (p / (1 - p))^(b + q)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _
      dsimp [M]
      rw [pow_add]
      ring
    _ ≤ ∑ b ∈ B, gnpGraphFamilySliceWeight Q (b + q) p :=
      Finset.sum_le_sum hlevel
    _ = ∑ m ∈ B.image (fun b ↦ b + q), gnpGraphFamilySliceWeight Q m p := by
      rw [Finset.sum_image]
      intro b _ c _ h
      exact Nat.add_right_cancel h
    _ ≤ ∑ m ∈ Finset.range (completeEdgeCount n + 1),
        gnpGraphFamilySliceWeight Q m p := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro m hm
        obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hm
        exact Finset.mem_range.mpr (Nat.lt_succ_of_le (hfeasible b hb))
      · intro m _ _
        exact gnpGraphFamilySliceWeight_nonneg Q ⟨hp.1.le, hp.2.le⟩
    _ = _ := (gnpGraphEventProbability_eq_sum_graphFamilySliceWeights Q p).symm

end InducedStars
