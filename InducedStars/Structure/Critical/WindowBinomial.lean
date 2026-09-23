import InducedStars.Structure.Critical.WindowBasic
import InducedStars.Structure.Critical.BinomialExpansion
import DenseGraph.Combinatorics.TwoSidedBinomial

/-!
# Exact completion slices in the critical window

Equitable capacities are independent of the displayed division.  The edge
count retains the exact logarithmic-window floor, and infeasible completion
counts are zero.  The finite identities isolate the bounded residue and
floor errors before the asymptotic expansion.
-/

noncomputable section

open Filter Set Topology

namespace InducedStars

/-- The equitable core capacity on `n-s` vertices. -/
def criticalWindowCoreCapacity (k n s : ℕ) : ℕ :=
  DenseGraph.balancedMultipartiteCrossCapacity (k - 1) (n - s)

/-- The forced edges of the equitable core. -/
def criticalWindowCoreInternal (k n s : ℕ) : ℕ :=
  DenseGraph.balancedMultipartiteInternalCapacity (k - 1) (n - s)

/-- Completion count after prescribing `t` edges in the remainder.
The feasibility guard prevents truncated natural subtraction from counting
an infeasible zero-selected slice. -/
def criticalWindowCompletionCount (k : ℕ) (a : ℝ) (n s t : ℕ) : ℕ :=
  if criticalWindowCoreInternal k n s + t ≤ criticalWindowEdgeCount k a n then
    Nat.choose (criticalWindowCoreCapacity k n s)
      (criticalWindowEdgeCount k a n - (criticalWindowCoreInternal k n s + t))
  else 0

/-- Selected cross edges in the equitable full reference. -/
def criticalWindowReferenceSelected (k : ℕ) (a : ℝ) (n : ℕ) : ℕ :=
  criticalWindowEdgeCount k a n - criticalWindowCoreInternal k n 0

/-- Exact error discarded by the floor. -/
def criticalWindowFloorError (k : ℕ) (a : ℝ) (n : ℕ) : ℝ :=
  criticalWindowDensity k a n * (completeEdgeCount n : ℝ) -
    (criticalWindowEdgeCount k a n : ℝ)

theorem criticalWindowFloorError_mem_Ico
    {k n : ℕ} {a : ℝ} (hdensity : 0 ≤ criticalWindowDensity k a n) :
    criticalWindowFloorError k a n ∈ Ico (0 : ℝ) 1 := by
  have hn : 0 ≤ criticalWindowDensity k a n * (completeEdgeCount n : ℝ) :=
    mul_nonneg hdensity (Nat.cast_nonneg _)
  constructor
  · exact sub_nonneg.mpr (Nat.floor_le hn)
  · have h := Nat.lt_floor_add_one
      (criticalWindowDensity k a n * (completeEdgeCount n : ℝ))
    change _ - (⌊criticalWindowDensity k a n * (completeEdgeCount n : ℝ)⌋₊ : ℝ) < 1
    linarith

theorem eventually_criticalWindowFloorError_mem_Ico
    {k : ℕ} (hk : 3 ≤ k) (a : ℝ) :
    ∀ᶠ n : ℕ in atTop, criticalWindowFloorError k a n ∈ Ico (0 : ℝ) 1 := by
  filter_upwards [eventually_criticalWindowDensity_mem_Ioo hk a] with n hn
  exact criticalWindowFloorError_mem_Ico hn.1.le

/-- Signed loss of available core cross pairs. -/
def criticalWindowCapacityLoss (k n s : ℕ) : ℝ :=
  (criticalWindowCoreCapacity k n 0 : ℝ) - criticalWindowCoreCapacity k n s

/-- Signed increase of selected core cross pairs. -/
def criticalWindowSelectedIncrease (k n s t : ℕ) : ℝ :=
  (criticalWindowCoreInternal k n 0 : ℝ) - criticalWindowCoreInternal k n s - t

theorem criticalWindowCapacityLoss_eq
    {k n s : ℕ} (hk : 3 ≤ k) (hsn : s ≤ n) :
    criticalWindowCapacityLoss k n s =
      ((k - 2 : ℕ) : ℝ) / (k - 1 : ℕ) * s * n -
        ((k - 2 : ℕ) : ℝ) / (2 * (k - 1 : ℕ)) * (s : ℝ) ^ 2 +
        criticalBalancedResidueError k (n - s) - criticalBalancedResidueError k n := by
  have hrel : ((k - 1 : ℕ) : ℝ) - 1 = (k - 2 : ℕ) := by
    have h : ((k - 1 : ℕ) : ℝ) = ((k - 2 : ℕ) : ℝ) + 1 := by
      exact_mod_cast (show k - 1 = k - 2 + 1 by omega)
    linarith
  unfold criticalWindowCapacityLoss criticalWindowCoreCapacity
  simp only [Nat.sub_zero]
  change (criticalTargetCapacity k n : ℝ) - criticalTargetCapacity k (n - s) = _
  rw [criticalTargetCapacity_cast_eq hk, criticalTargetCapacity_cast_eq hk,
    Nat.cast_sub hsn, hrel]
  ring

theorem criticalWindowSelectedIncrease_eq
    {k n s t : ℕ} (hk : 3 ≤ k) (hsn : s ≤ n) :
    criticalWindowSelectedIncrease k n s t =
      (s : ℝ) * n / (k - 1 : ℕ) - (s : ℝ) ^ 2 / (2 * (k - 1 : ℕ)) -
        (s : ℝ) / 2 - t +
        criticalBalancedResidueError k n - criticalBalancedResidueError k (n - s) := by
  unfold criticalWindowSelectedIncrease criticalWindowCoreInternal
  simp only [Nat.sub_zero]
  rw [criticalBalancedInternalCapacity_cast_eq hk,
    criticalBalancedInternalCapacity_cast_eq hk, Nat.cast_sub hsn]
  ring

/-- Exact first-order cancellation, with only the equitable residue left. -/
theorem criticalWindowCapacityLoss_sub_mul_selectedIncrease
    {k n s t : ℕ} (hk : 3 ≤ k) (hsn : s ≤ n) :
    criticalWindowCapacityLoss k n s -
        ((k - 2 : ℕ) : ℝ) * criticalWindowSelectedIncrease k n s t =
      ((k - 2 : ℕ) : ℝ) * ((s : ℝ) / 2 + t) +
        ((k - 1 : ℕ) : ℝ) *
          (criticalBalancedResidueError k (n - s) - criticalBalancedResidueError k n) := by
  have hrel : ((k - 1 : ℕ) : ℝ) = ((k - 2 : ℕ) : ℝ) + 1 := by
    exact_mod_cast (show k - 1 = k - 2 + 1 by omega)
  rw [criticalWindowCapacityLoss_eq hk hsn, criticalWindowSelectedIncrease_eq hk hsn]
  rw [hrel]
  ring

/-- The exact density displacement includes the signed logarithmic-window
term, the floor error, and the bounded equitable residue. -/
theorem criticalWindowReferenceSelected_sub_p_mul_capacity_eq
    {k n : ℕ} {a : ℝ} (hk : 3 ≤ k) (hn : 0 < n)
    (hfeasible : criticalWindowCoreInternal k n 0 ≤ criticalWindowEdgeCount k a n) :
    (criticalWindowReferenceSelected k a n : ℝ) -
        pK k * criticalWindowCoreCapacity k n 0 =
      a * Real.log (n : ℝ) * ((n : ℝ) - 1) / 2 +
        (1 - gammaK k) * n / 2 - criticalWindowFloorError k a n -
        (1 - pK k) * criticalBalancedResidueError k n := by
  have hr : ((k - 1 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (show k - 1 ≠ 0 by omega)
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [criticalWindowReferenceSelected, Nat.cast_sub hfeasible]
  unfold criticalWindowCoreCapacity criticalWindowCoreInternal
  simp only [Nat.sub_zero]
  change (criticalWindowEdgeCount k a n : ℝ) -
    DenseGraph.balancedMultipartiteInternalCapacity (k - 1) n -
      pK k * criticalTargetCapacity k n = _
  rw [criticalBalancedInternalCapacity_cast_eq hk, criticalTargetCapacity_cast_eq hk]
  unfold criticalWindowFloorError criticalWindowDensity completeEdgeCount gammaK
  rw [Nat.cast_choose_two]
  have hrel : ((k - 1 : ℕ) : ℝ) = ((k - 2 : ℕ) : ℝ) + 1 := by
    exact_mod_cast (show k - 1 = k - 2 + 1 by omega)
  field_simp
  rw [hrel]
  ring

end InducedStars
