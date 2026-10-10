import InducedStars.Structure.Subcritical.FullRetainedSlice
import DenseGraph.Combinatorics.BinomialJointShift

/-!
# From a retained window to a full fixed-total slice

Paper: the active-level denominator comparison. The upper window
is injected into the whole fixed-total active slice before shifting. No
claim is made that the shifted vector remains in the original window.
-/

noncomputable section
open Finset Set
open scoped BigOperators Classical
namespace InducedStars

variable {k : ℕ} {V : Type*} [Fintype V] [DecidableEq V]

/-- Choosing one exact vector in the window and then its actual active
edges is injective into the full fixed-total active slice. -/
theorem retainedPartitionFunction_le_choose
    (D : SubcriticalDivision k V) (eta : ℝ) (R₀ m M b : ℕ) (delta : ℝ)
    (hm : retainedCliqueCapacity D eta R₀ + M + b = m) :
    retainedPartitionFunction D eta R₀ m delta (b : ℤ) ≤
      (retainedActiveTotalCapacity D eta R₀).choose M := by
  let T := Σ v : ↥(retainedEdgeCountLevel D eta R₀ m delta (b : ℤ)), RetainedEdgeChoices v.val
  let f : T → ↥((retainedActiveEdgeUniverse D eta R₀).powersetCard M) := fun d ↦
    ⟨subcriticalActiveSelectedEdges ((retainedEdgeChoiceModel d.1.val).sampleOutcome d.2), by
      apply Finset.mem_powersetCard.mpr
      refine ⟨subcriticalActiveSelectedEdges_subset _, ?_⟩
      rw [subcriticalActiveSelectedEdges_sample_card]
      have hid := (mem_retainedEdgeCountLevel.mp d.1.property).1
      omega⟩
  have hf : Function.Injective f := by
    rintro ⟨⟨v, hv⟩, S⟩ ⟨⟨w, hw⟩, U⟩ h
    have hA := congrArg Subtype.val h
    have hG : subcriticalCleanGraph (⊥ : SubcriticalRemainderGraph D eta R₀) S =
        subcriticalCleanGraph (⊥ : SubcriticalRemainderGraph D eta R₀) U := by
      change subcriticalGraphFromActiveEdges ⊥ ⊥ _ = subcriticalGraphFromActiveEdges ⊥ ⊥ _
      exact congrArg (fun A ↦ subcriticalGraphFromActiveEdges
        (⊥ : SubcriticalRemainderGraph D eta R₀) ⊥ A) hA
    have hvw := congrArg (fun G ↦ actualRetainedEdgeCountVector G D eta R₀) hG
    simp only [subcriticalCleanGraph_active_vector] at hvw
    subst w
    have hSU := subcriticalActiveGraphFromOutcome_injective
      (⊥ : SubcriticalRemainderGraph D eta R₀) ⊥
      (isSubcriticalRetainedDefectPattern_bot D eta R₀) v hG
    subst U
    rfl
  have hcard := Fintype.card_le_of_injective f hf
  have hleft : Fintype.card T = retainedPartitionFunction D eta R₀ m delta (b : ℤ) := by
    simp only [T, Fintype.card_sigma, retainedEdgeChoices_card, Finset.sum_coe_sort,
      retainedPartitionFunction]
  rw [hleft, Fintype.card_coe, Finset.card_powersetCard,
    ← retainedActiveTotalCapacity_eq_card] at hcard
  exact hcard

/-- Exact finite shifted-denominator estimate. The shifted count's interior
headroom is explicit here and is established uniformly for balanced
reference keys in the subsequent theorem. -/
theorem retainedPartitionFunction_mul_remainder_le_shifted_total
    {n m M b q : ℕ} (hk : 3 ≤ k) (D : SubcriticalDivision k (Fin n))
    (eta : ℝ) (R₀ : ℕ) (delta : ℝ)
    (hm : retainedCliqueCapacity D eta R₀ + M + b = m)
    (hM : M ≤ retainedActiveTotalCapacity D eta R₀) (hq : q ≤ M)
    {lambda : ℝ} (hlambda : 0 < lambda) (hlambdaHalf : lambda < 1 / 2)
    (hlo : lambda * retainedActiveTotalCapacity D eta R₀ ≤ ((M - q : ℕ) : ℝ))
    (hhi : ((M - q : ℕ) : ℝ) ≤ (1 - lambda) * retainedActiveTotalCapacity D eta R₀) :
    (retainedPartitionFunction D eta R₀ m delta (b : ℤ) : ℝ) *
        inducedStarFreeGraphCountWithEdges k (D.nonretainedVertices eta R₀).card (b + q) ≤
      (inducedStarFreeGraphCountWithEdges k n m : ℝ) *
        Real.exp (DenseGraph.binomialCompactBandShiftConstant lambda * q) := by
  have hZ := retainedPartitionFunction_le_choose D eta R₀ m M b delta hm
  have hchoose := DenseGraph.choose_le_choose_mul_exp_abs_shift_of_compact_band
    hM ((Nat.sub_le M q).trans hM) hlambda hlambdaHalf hlo hhi
  have hdist : Nat.dist M (M - q) = q := by
    rw [Nat.dist_eq_sub_of_le_right (Nat.sub_le _ _)]
    omega
  rw [hdist] at hchoose
  have hden := subcriticalFullRetainedSlice_le_total (M := M-q) (b := b+q) (m := m)
    hk D eta R₀ (by omega)
  have hN0 : (0 : ℝ) ≤ inducedStarFreeGraphCountWithEdges k
      (D.nonretainedVertices eta R₀).card (b+q) := by positivity
  calc
    _ ≤ ((retainedActiveTotalCapacity D eta R₀).choose M : ℝ) *
        inducedStarFreeGraphCountWithEdges k (D.nonretainedVertices eta R₀).card (b + q) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hZ) hN0
    _ ≤ (((retainedActiveTotalCapacity D eta R₀).choose (M-q) : ℝ) *
        Real.exp (DenseGraph.binomialCompactBandShiftConstant lambda * q)) *
        inducedStarFreeGraphCountWithEdges k (D.nonretainedVertices eta R₀).card (b + q) :=
      mul_le_mul_of_nonneg_right hchoose hN0
    _ = (((retainedActiveTotalCapacity D eta R₀).choose (M-q) : ℝ) *
        inducedStarFreeGraphCountWithEdges k (D.nonretainedVertices eta R₀).card (b + q)) *
        Real.exp (DenseGraph.binomialCompactBandShiftConstant lambda * q) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hden) (Real.exp_pos _).le

end InducedStars
