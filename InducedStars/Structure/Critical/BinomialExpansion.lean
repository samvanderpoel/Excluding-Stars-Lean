import DenseGraph.Combinatorics.SecondOrderBinomial
import DenseGraph.Combinatorics.BinomialJointShift
import InducedStars.Structure.Critical.CapacityBookkeeping
import InducedStars.Structure.Critical.Scalars

/-!
# Finite binomial expansion at the critical density

This file records the exact finite arithmetic behind the critical
binomial-slice comparison.  In particular, no asymptotic equality hides the
floor in `criticalEdgeCount` or the residue classes of the balanced
partition.

The old (sparse-set) capacity and selected-count declarations live in
`Critical.CapacityBookkeeping`; the loss/increase adapters are added below
that import boundary.  The reference-density identities here depend only on
the balanced full fiber.
-/

noncomputable section

open Filter Set Topology

namespace InducedStars

/-! ## Exact finite errors in the balanced reference fiber -/

/-- The amount discarded by flooring the prescribed critical edge count. -/
noncomputable def criticalEdgeCountFloorError (k n : ℕ) : ℝ :=
  gammaK k * (completeEdgeCount n : ℝ) - (criticalEdgeCount k n : ℝ)

/-- The quotient/remainder correction to the balanced internal capacity. -/
def criticalBalancedResidueError (k n : ℕ) : ℝ :=
  ((n % (k - 1) : ℕ) : ℝ) *
      (((k - 1 : ℕ) : ℝ) - ((n % (k - 1) : ℕ) : ℝ)) /
    (2 * ((k - 1 : ℕ) : ℝ))

/-- The floor error is always in `[0,1)` for `k ≥ 3`. -/
theorem criticalEdgeCountFloorError_mem_Ico
    {k : ℕ} (hk : 3 ≤ k) (n : ℕ) :
    criticalEdgeCountFloorError k n ∈ Set.Ico (0 : ℝ) 1 := by
  simpa [criticalEdgeCountFloorError] using criticalEdgeCount_floor_error hk n

/-- The balanced residue correction is nonnegative. -/
theorem criticalBalancedResidueError_nonneg
    {k n : ℕ} (hk : 3 ≤ k) :
    0 ≤ criticalBalancedResidueError k n := by
  have hr : 0 < k - 1 := by omega
  have hmod : n % (k - 1) ≤ k - 1 := (Nat.mod_lt n hr).le
  have hrR : (0 : ℝ) < (k - 1 : ℕ) := by exact_mod_cast hr
  have hmodR : ((n % (k - 1) : ℕ) : ℝ) ≤ (k - 1 : ℕ) := by
    exact_mod_cast hmod
  unfold criticalBalancedResidueError
  exact div_nonneg
    (mul_nonneg (Nat.cast_nonneg _ ) (sub_nonneg.mpr hmodR))
    (mul_nonneg (by norm_num) hrR.le)

/-- A convenient uniform bound for the balanced residue correction. -/
theorem criticalBalancedResidueError_le
    {k n : ℕ} (hk : 3 ≤ k) :
    criticalBalancedResidueError k n ≤ (k - 1 : ℕ) := by
  have hr : 0 < k - 1 := by omega
  have happ := DenseGraph.balancedMultipartiteInternalCapacity_approx
    (r := k - 1) (q := n) hr
  have heq :
      (DenseGraph.balancedMultipartiteInternalCapacity (k - 1) n : ℝ) -
          ((n : ℝ) ^ 2 / (2 * ((k - 1 : ℕ) : ℝ)) - (n : ℝ) / 2) =
        criticalBalancedResidueError k n := by
    rw [DenseGraph.balancedMultipartiteInternalCapacity_cast_eq hr]
    simp only [criticalBalancedResidueError]
    ring
  rw [heq, abs_of_nonneg (criticalBalancedResidueError_nonneg hk)] at happ
  exact happ

/-- Exact real formula for the balanced target capacity. -/
theorem criticalTargetCapacity_cast_eq
    {k n : ℕ} (hk : 3 ≤ k) :
    (criticalTargetCapacity k n : ℝ) =
      (((k - 1 : ℕ) : ℝ) - 1) * (n : ℝ) ^ 2 /
          (2 * ((k - 1 : ℕ) : ℝ)) -
        criticalBalancedResidueError k n := by
  have hr : 0 < k - 1 := by omega
  simpa [criticalTargetCapacity, criticalBalancedResidueError] using
    (DenseGraph.balancedMultipartiteCrossCapacity_cast_eq
      (r := k - 1) (q := n) hr)

/-- Exact real formula for the balanced internal capacity. -/
theorem criticalBalancedInternalCapacity_cast_eq
    {k n : ℕ} (hk : 3 ≤ k) :
    (DenseGraph.balancedMultipartiteInternalCapacity (k - 1) n : ℝ) =
      (n : ℝ) ^ 2 / (2 * ((k - 1 : ℕ) : ℝ)) -
        (n : ℝ) / 2 + criticalBalancedResidueError k n := by
  have hr : 0 < k - 1 := by omega
  simpa [criticalBalancedResidueError] using
    (DenseGraph.balancedMultipartiteInternalCapacity_cast_eq
      (r := k - 1) (q := n) hr)

/-! ## Signed capacity loss and selected-count increase -/

/-- The exact real capacity loss when `s` vertices are separated off and
their internal pairs are added to the optional coordinate universe.  The
later natural-valued adapter is this quantity under the corresponding
capacity-order hypothesis. -/
def criticalSignedCapacityLoss (k n s : ℕ) : ℝ :=
  (criticalTargetCapacity k n : ℝ) -
    (DenseGraph.balancedMultipartiteCrossCapacity (k - 1) (n - s) : ℝ) -
    (Nat.choose s 2 : ℝ)

/-- The exact real increase in selected coordinates forced by replacing the
balanced internal capacity on `n` vertices by that on `n-s` vertices. -/
def criticalSignedSelectedIncrease (k n s : ℕ) : ℝ :=
  (DenseGraph.balancedMultipartiteInternalCapacity (k - 1) n : ℝ) -
    (DenseGraph.balancedMultipartiteInternalCapacity (k - 1) (n - s) : ℝ)

/-- Natural capacity loss from the balanced full reference slice to the
maximum combined slice with `s` sparse vertices. -/
def criticalCapacityLoss (k n s : ℕ) : ℕ :=
  criticalTargetCapacity k n - criticalMaximumCombinedCapacity k n s

/-- Natural selected-count increase from the balanced full reference slice
to the maximum combined slice with `s` sparse vertices. -/
def criticalSelectedIncrease (k n s : ℕ) : ℕ :=
  DenseGraph.balancedMultipartiteInternalCapacity (k - 1) n -
    DenseGraph.balancedMultipartiteInternalCapacity (k - 1) (n - s)

/-- Limiting fraction of `K+L` contributed by the capacity loss `K`. -/
def criticalReferenceLossFraction (k : ℕ) : ℝ :=
  ((k - 2 : ℕ) : ℝ) / ((k - 1 : ℕ) : ℝ)

/-- Under the natural capacity-order guard, the natural loss is exactly the
signed real loss used in the finite expansion. -/
theorem criticalCapacityLoss_cast_eq_signed
    {k n s : ℕ}
    (hcapacity : criticalMaximumCombinedCapacity k n s ≤
      criticalTargetCapacity k n) :
    (criticalCapacityLoss k n s : ℝ) =
      criticalSignedCapacityLoss k n s := by
  rw [criticalCapacityLoss, Nat.cast_sub hcapacity]
  unfold criticalSignedCapacityLoss criticalMaximumCombinedCapacity
  push_cast
  ring

/-- Under monotonicity of the balanced internal capacity, the natural
increase is exactly the signed real increase. -/
theorem criticalSelectedIncrease_cast_eq_signed
    {k n s : ℕ}
    (hinternal :
      DenseGraph.balancedMultipartiteInternalCapacity (k - 1) (n - s) ≤
        DenseGraph.balancedMultipartiteInternalCapacity (k - 1) n) :
    (criticalSelectedIncrease k n s : ℝ) =
      criticalSignedSelectedIncrease k n s := by
  rw [criticalSelectedIncrease, Nat.cast_sub hinternal]
  rfl

/-- Exact capacity relation for the natural loss. -/
theorem criticalTargetCapacity_sub_loss
    {k n s : ℕ}
    (hcapacity : criticalMaximumCombinedCapacity k n s ≤
      criticalTargetCapacity k n) :
    criticalTargetCapacity k n - criticalCapacityLoss k n s =
      criticalMaximumCombinedCapacity k n s := by
  unfold criticalCapacityLoss
  omega

/-- Exact selected-count relation on a nonempty clean division fiber. -/
theorem criticalTargetSelectedCount_add_increase_eq_maximum_of_nonempty
    {k n : ℕ} {hk : 3 ≤ k} {tau : ℝ} {hn : k - 1 ≤ n}
    {D : SupercriticalDivision k (Fin n)}
    (hD : (criticalCleanDivisionGraphFinset k hk n tau hn D).Nonempty)
    (hreference :
      DenseGraph.balancedMultipartiteInternalCapacity (k - 1) n ≤
        criticalEdgeCount k n)
    (hinternal :
      DenseGraph.balancedMultipartiteInternalCapacity
          (k - 1) (n - D.sparse.card) ≤
        DenseGraph.balancedMultipartiteInternalCapacity (k - 1) n) :
    criticalTargetSelectedCount k n +
        criticalSelectedIncrease k n D.sparse.card =
      criticalMaximumCombinedSelectedCount k n D.sparse.card := by
  rw [criticalMaximumCombinedSelectedCount_eq_of_nonempty hD]
  unfold criticalTargetSelectedCount criticalSelectedIncrease
  omega

/-- Main polynomial term in the critical capacity loss.  The linear `s/2`
term is retained, leaving a uniformly bounded residue error. -/
def criticalCapacityLossMainTerm (k n s : ℕ) : ℝ :=
  (((k - 2 : ℕ) : ℝ) / ((k - 1 : ℕ) : ℝ)) *
      (s : ℝ) * (n : ℝ) -
    (((2 * k - 3 : ℕ) : ℝ) /
      (2 * ((k - 1 : ℕ) : ℝ))) * (s : ℝ) ^ 2 +
    (s : ℝ) / 2

/-- Main polynomial term in the critical selected-count increase. -/
def criticalSelectedIncreaseMainTerm (k n s : ℕ) : ℝ :=
  (s : ℝ) * (n : ℝ) / ((k - 1 : ℕ) : ℝ) -
    (s : ℝ) ^ 2 / (2 * ((k - 1 : ℕ) : ℝ)) -
    (s : ℝ) / 2

/-- Exact `K+L=s(n-s)` identity for the separate capacity and selected-count
perturbations. -/
theorem criticalSignedCapacityLoss_add_selectedIncrease
    {k n s : ℕ} (hk : 3 ≤ k) (hs : s ≤ n) :
    criticalSignedCapacityLoss k n s +
        criticalSignedSelectedIncrease k n s =
      (s : ℝ) * ((n - s : ℕ) : ℝ) := by
  have hold :
      (DenseGraph.balancedMultipartiteCrossCapacity (k - 1) (n - s) : ℝ) =
        (((k - 1 : ℕ) : ℝ) - 1) * ((n - s : ℕ) : ℝ) ^ 2 /
            (2 * ((k - 1 : ℕ) : ℝ)) -
          criticalBalancedResidueError k (n - s) := by
    simpa [criticalTargetCapacity] using
      (criticalTargetCapacity_cast_eq (k := k) (n := n - s) hk)
  rw [criticalSignedCapacityLoss, criticalSignedSelectedIncrease,
    criticalTargetCapacity_cast_eq hk,
    hold]
  have hr : 0 < k - 1 := by omega
  rw [criticalBalancedInternalCapacity_cast_eq hk,
    criticalBalancedInternalCapacity_cast_eq (k := k) (n := n - s) hk,
    Nat.cast_choose_two, Nat.cast_sub hs]
  have hrR : (0 : ℝ) < (k - 1 : ℕ) := by exact_mod_cast hr
  field_simp [hrR.ne']
  norm_num [Nat.cast_sub (show 2 ≤ k by omega),
    Nat.cast_sub (show 1 ≤ k by omega)]
  ring

/-- Uniform finite remainder for the capacity-loss polynomial. -/
theorem abs_criticalSignedCapacityLoss_sub_mainTerm_le
    {k n s : ℕ} (hk : 3 ≤ k) (hs : s ≤ n) :
    |criticalSignedCapacityLoss k n s -
        criticalCapacityLossMainTerm k n s| ≤ (k - 1 : ℕ) := by
  have hr : 0 < k - 1 := by omega
  have hrR : (0 : ℝ) < (k - 1 : ℕ) := by exact_mod_cast hr
  have hold :
      (DenseGraph.balancedMultipartiteCrossCapacity (k - 1) (n - s) : ℝ) =
        (((k - 1 : ℕ) : ℝ) - 1) * ((n - s : ℕ) : ℝ) ^ 2 /
            (2 * ((k - 1 : ℕ) : ℝ)) -
          criticalBalancedResidueError k (n - s) := by
    simpa [criticalTargetCapacity] using
      (criticalTargetCapacity_cast_eq (k := k) (n := n - s) hk)
  have hk2 :
      ((k - 2 : ℕ) : ℝ) = ((k - 1 : ℕ) : ℝ) - 1 := by
    norm_num [Nat.cast_sub (show 2 ≤ k by omega),
      Nat.cast_sub (show 1 ≤ k by omega)]
    ring
  have h2k3 :
      ((2 * k - 3 : ℕ) : ℝ) =
        2 * ((k - 1 : ℕ) : ℝ) - 1 := by
    norm_num [Nat.cast_sub (show 3 ≤ 2 * k by omega),
      Nat.cast_sub (show 1 ≤ k by omega)]
    ring
  have heq :
      criticalSignedCapacityLoss k n s -
          criticalCapacityLossMainTerm k n s =
        criticalBalancedResidueError k (n - s) -
          criticalBalancedResidueError k n := by
    rw [criticalSignedCapacityLoss, criticalCapacityLossMainTerm,
      criticalTargetCapacity_cast_eq hk,
      hold, Nat.cast_choose_two, Nat.cast_sub hs, hk2, h2k3]
    field_simp [hrR.ne']
    ring
  rw [heq, abs_le]
  have hn0 := criticalBalancedResidueError_nonneg (k := k) (n := n) hk
  have hnle := criticalBalancedResidueError_le (k := k) (n := n) hk
  have hq0 := criticalBalancedResidueError_nonneg
    (k := k) (n := n - s) hk
  have hqle := criticalBalancedResidueError_le
    (k := k) (n := n - s) hk
  constructor <;> linarith

/-- Uniform finite remainder for the selected-increase polynomial. -/
theorem abs_criticalSignedSelectedIncrease_sub_mainTerm_le
    {k n s : ℕ} (hk : 3 ≤ k) (hs : s ≤ n) :
    |criticalSignedSelectedIncrease k n s -
        criticalSelectedIncreaseMainTerm k n s| ≤ (k - 1 : ℕ) := by
  have hr : 0 < k - 1 := by omega
  have hrR : (0 : ℝ) < (k - 1 : ℕ) := by exact_mod_cast hr
  have heq :
      criticalSignedSelectedIncrease k n s -
          criticalSelectedIncreaseMainTerm k n s =
        criticalBalancedResidueError k n -
          criticalBalancedResidueError k (n - s) := by
    rw [criticalSignedSelectedIncrease, criticalSelectedIncreaseMainTerm,
      criticalBalancedInternalCapacity_cast_eq hk,
      criticalBalancedInternalCapacity_cast_eq (k := k) (n := n - s) hk,
      Nat.cast_sub hs]
    norm_num [Nat.cast_sub (show 1 ≤ k by omega)]
    field_simp [hrR.ne']
    ring
  rw [heq, abs_le]
  have hn0 := criticalBalancedResidueError_nonneg (k := k) (n := n) hk
  have hnle := criticalBalancedResidueError_le (k := k) (n := n) hk
  have hq0 := criticalBalancedResidueError_nonneg
    (k := k) (n := n - s) hk
  have hqle := criticalBalancedResidueError_le
    (k := k) (n := n - s) hk
  constructor <;> linarith

/-! ## Positivity and exact natural bookkeeping in the sparse range -/

/-- In the uniform sparse range used below, deleting `s` vertices and
retaining their internal coordinates genuinely decreases the balanced
variable capacity. -/
theorem criticalSignedCapacityLoss_nonneg
    {k n s : ℕ} (hk : 3 ≤ k) (hs : 1 ≤ s)
    (hsmall : 16 * s ≤ n) (hn : 4 * (k - 1) ^ 2 ≤ n) :
    0 ≤ criticalSignedCapacityLoss k n s := by
  have hsle : s ≤ n := by omega
  have hrem := abs_criticalSignedCapacityLoss_sub_mainTerm_le hk hsle
  have hlower := neg_le_of_abs_le hrem
  have hrNat : 2 ≤ k - 1 := by omega
  have hr : (2 : ℝ) ≤ (k - 1 : ℕ) := by exact_mod_cast hrNat
  have hsR : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have hsmallR : (16 : ℝ) * (s : ℝ) ≤ n := by exact_mod_cast hsmall
  have hnR : (4 : ℝ) * ((k - 1 : ℕ) : ℝ) ^ 2 ≤ n := by
    exact_mod_cast hn
  have hx : (1 / 2 : ℝ) ≤
      ((k - 2 : ℕ) : ℝ) / ((k - 1 : ℕ) : ℝ) := by
    have hrel : ((k - 2 : ℕ) : ℝ) = ((k - 1 : ℕ) : ℝ) - 1 := by
      norm_num [Nat.cast_sub (show 2 ≤ k by omega),
        Nat.cast_sub (show 1 ≤ k by omega)]
      ring
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < (k - 1 : ℕ)), hrel]
    nlinarith
  have hc : ((2 * k - 3 : ℕ) : ℝ) /
      (2 * ((k - 1 : ℕ) : ℝ)) ≤ 1 := by
    rw [div_le_one (by positivity : (0 : ℝ) < 2 * ((k - 1 : ℕ) : ℝ))]
    norm_num [Nat.cast_sub (show 3 ≤ 2 * k by omega),
      Nat.cast_sub (show 1 ≤ k by omega)]
    linarith
  have hsSq : (s : ℝ) ^ 2 ≤ (s : ℝ) * (n : ℝ) / 16 := by
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ s by positivity)
      (sub_nonneg.mpr hsmallR)]
  have hrLinear : ((k - 1 : ℕ) : ℝ) ≤
      7 / 16 * (s : ℝ) * (n : ℝ) := by
    have hr0 : (0 : ℝ) ≤ (k - 1 : ℕ) := by positivity
    have hrSq : ((k - 1 : ℕ) : ℝ) ≤ ((k - 1 : ℕ) : ℝ) ^ 2 := by
      nlinarith
    nlinarith [mul_le_mul_of_nonneg_right hnR
      (show (0 : ℝ) ≤ s by positivity)]
  unfold criticalCapacityLossMainTerm at hlower
  have hsn : 0 ≤ (s : ℝ) * (n : ℝ) := by positivity
  have hsSq0 : 0 ≤ (s : ℝ) ^ 2 := sq_nonneg _
  have hxmul := mul_le_mul_of_nonneg_right hx hsn
  have hcmul := mul_le_mul_of_nonneg_right hc hsSq0
  nlinarith

/-- In the same sparse range the balanced forced internal capacity decreases,
so the selected-coordinate perturbation is a genuine natural increase. -/
theorem criticalSignedSelectedIncrease_nonneg
    {k n s : ℕ} (hk : 3 ≤ k) (hs : 1 ≤ s)
    (hsmall : 16 * s ≤ n) (hn : 4 * (k - 1) ^ 2 ≤ n) :
    0 ≤ criticalSignedSelectedIncrease k n s := by
  have hsle : s ≤ n := by omega
  have hrem := abs_criticalSignedSelectedIncrease_sub_mainTerm_le hk hsle
  have hlower := neg_le_of_abs_le hrem
  have hrNat : 2 ≤ k - 1 := by omega
  have hr : (2 : ℝ) ≤ (k - 1 : ℕ) := by exact_mod_cast hrNat
  have hrPos : (0 : ℝ) < (k - 1 : ℕ) := by positivity
  have hsR : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have hsmallR : (16 : ℝ) * (s : ℝ) ≤ n := by exact_mod_cast hsmall
  have hnR : (4 : ℝ) * ((k - 1 : ℕ) : ℝ) ^ 2 ≤ n := by
    exact_mod_cast hn
  have hsSq : (s : ℝ) ^ 2 ≤ (s : ℝ) * (n : ℝ) / 16 := by
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ s by positivity)
      (sub_nonneg.mpr hsmallR)]
  have hrs : ((k - 1 : ℕ) : ℝ) * (s : ℝ) ≤
      (s : ℝ) * (n : ℝ) / 4 := by
    have hrLeSq : ((k - 1 : ℕ) : ℝ) ≤
        ((k - 1 : ℕ) : ℝ) ^ 2 := by nlinarith
    have hnQuarter : ((k - 1 : ℕ) : ℝ) ≤ (n : ℝ) / 4 := by
      nlinarith
    nlinarith [mul_le_mul_of_nonneg_right hnQuarter
      (show (0 : ℝ) ≤ s by positivity)]
  have hmainEq :
      2 * ((k - 1 : ℕ) : ℝ) *
          criticalSelectedIncreaseMainTerm k n s =
        2 * (s : ℝ) * (n : ℝ) - (s : ℝ) ^ 2 -
          ((k - 1 : ℕ) : ℝ) * (s : ℝ) := by
    unfold criticalSelectedIncreaseMainTerm
    field_simp [hrPos.ne']
  have hmainLower : ((k - 1 : ℕ) : ℝ) ≤
      criticalSelectedIncreaseMainTerm k n s := by
    rw [← mul_le_mul_iff_of_pos_left
      (mul_pos (by norm_num : (0 : ℝ) < 2) hrPos), hmainEq]
    nlinarith [mul_le_mul_of_nonneg_right hnR
      (show (0 : ℝ) ≤ s by positivity)]
  linarith

theorem criticalMaximumCombinedCapacity_le_target
    {k n s : ℕ} (hk : 3 ≤ k) (hs : 1 ≤ s)
    (hsmall : 16 * s ≤ n) (hn : 4 * (k - 1) ^ 2 ≤ n) :
    criticalMaximumCombinedCapacity k n s ≤ criticalTargetCapacity k n := by
  have h := criticalSignedCapacityLoss_nonneg hk hs hsmall hn
  unfold criticalSignedCapacityLoss at h
  have hR :
      (criticalMaximumCombinedCapacity k n s : ℝ) ≤
        (criticalTargetCapacity k n : ℝ) := by
    unfold criticalMaximumCombinedCapacity
    push_cast
    linarith
  exact_mod_cast hR

theorem criticalBalancedInternalCapacity_mono_sparse
    {k n s : ℕ} (hk : 3 ≤ k) (hs : 1 ≤ s)
    (hsmall : 16 * s ≤ n) (hn : 4 * (k - 1) ^ 2 ≤ n) :
    DenseGraph.balancedMultipartiteInternalCapacity (k - 1) (n - s) ≤
      DenseGraph.balancedMultipartiteInternalCapacity (k - 1) n := by
  have h := criticalSignedSelectedIncrease_nonneg hk hs hsmall hn
  unfold criticalSignedSelectedIncrease at h
  exact_mod_cast (sub_nonneg.mp h)

/-- Natural form of the exact `K+L=s(n-s)` identity. -/
theorem criticalCapacityLoss_add_selectedIncrease
    {k n s : ℕ} (hk : 3 ≤ k) (hs : s ≤ n)
    (hcapacity : criticalMaximumCombinedCapacity k n s ≤
      criticalTargetCapacity k n)
    (hinternal :
      DenseGraph.balancedMultipartiteInternalCapacity (k - 1) (n - s) ≤
        DenseGraph.balancedMultipartiteInternalCapacity (k - 1) n) :
    criticalCapacityLoss k n s + criticalSelectedIncrease k n s =
      s * (n - s) := by
  have hreal := criticalSignedCapacityLoss_add_selectedIncrease hk hs
  rw [← criticalCapacityLoss_cast_eq_signed hcapacity,
    ← criticalSelectedIncrease_cast_eq_signed hinternal] at hreal
  exact_mod_cast hreal

theorem criticalCapacityLoss_add_selectedIncrease_of_sparse_range
    {k n s : ℕ} (hk : 3 ≤ k) (hs : 1 ≤ s)
    (hsmall : 16 * s ≤ n) (hn : 4 * (k - 1) ^ 2 ≤ n) :
    criticalCapacityLoss k n s + criticalSelectedIncrease k n s =
      s * (n - s) := by
  exact criticalCapacityLoss_add_selectedIncrease hk (by omega)
    (criticalMaximumCombinedCapacity_le_target hk hs hsmall hn)
    (criticalBalancedInternalCapacity_mono_sparse hk hs hsmall hn)

/-- The exact deviation of the capacity-loss main polynomial from its
limiting fraction of `s(n-s)`. -/
theorem criticalCapacityLossMainTerm_sub_fraction_mul_eq
    {k n s : ℕ} (hk : 3 ≤ k) (hs : s ≤ n) :
    criticalCapacityLossMainTerm k n s -
        criticalReferenceLossFraction k *
          ((s : ℝ) * ((n - s : ℕ) : ℝ)) =
      -(s : ℝ) ^ 2 / (2 * ((k - 1 : ℕ) : ℝ)) + (s : ℝ) / 2 := by
  have hr : (0 : ℝ) < (k - 1 : ℕ) := by
    exact_mod_cast (show 0 < k - 1 by omega)
  unfold criticalCapacityLossMainTerm criticalReferenceLossFraction
  rw [Nat.cast_sub hs]
  norm_num [Nat.cast_sub (show 2 ≤ k by omega),
    Nat.cast_sub (show 1 ≤ k by omega),
    Nat.cast_sub (show 3 ≤ 2 * k by omega)]
  field_simp [hr.ne']
  ring

/-- Uniform finite control of the loss fraction.  The bound is deliberately
simple: it is strong enough to make the normalized loss coordinate converge
uniformly whenever `s=o(n)` and `s≥1`. -/
theorem abs_criticalCapacityLoss_sub_fraction_mul_le
    {k n s : ℕ} (hk : 3 ≤ k) (hs : s ≤ n)
    (hcapacity : criticalMaximumCombinedCapacity k n s ≤
      criticalTargetCapacity k n) :
    |(criticalCapacityLoss k n s : ℝ) -
        criticalReferenceLossFraction k *
          ((s : ℝ) * ((n - s : ℕ) : ℝ))| ≤
      (s : ℝ) ^ 2 / 2 + (s : ℝ) / 2 + (k - 1 : ℕ) := by
  have hrem := abs_criticalSignedCapacityLoss_sub_mainTerm_le hk hs
  rw [← criticalCapacityLoss_cast_eq_signed hcapacity] at hrem
  have hexact := criticalCapacityLossMainTerm_sub_fraction_mul_eq hk hs
  have hr : (1 : ℝ) ≤ (k - 1 : ℕ) := by
    exact_mod_cast (show 1 ≤ k - 1 by omega)
  have hsq : 0 ≤ (s : ℝ) ^ 2 := sq_nonneg _
  have hden : 0 < 2 * ((k - 1 : ℕ) : ℝ) := by positivity
  have hfrac : (s : ℝ) ^ 2 /
      (2 * ((k - 1 : ℕ) : ℝ)) ≤ (s : ℝ) ^ 2 / 2 := by
    apply (div_le_div_iff₀ hden (by norm_num)).2
    nlinarith
  calc
    |(criticalCapacityLoss k n s : ℝ) -
        criticalReferenceLossFraction k *
          ((s : ℝ) * ((n - s : ℕ) : ℝ))| =
        |((criticalCapacityLoss k n s : ℝ) -
            criticalCapacityLossMainTerm k n s) +
          (criticalCapacityLossMainTerm k n s -
            criticalReferenceLossFraction k *
              ((s : ℝ) * ((n - s : ℕ) : ℝ)))| := by ring
    _ ≤ |(criticalCapacityLoss k n s : ℝ) -
            criticalCapacityLossMainTerm k n s| +
          |criticalCapacityLossMainTerm k n s -
            criticalReferenceLossFraction k *
              ((s : ℝ) * ((n - s : ℕ) : ℝ))| := abs_add_le _ _
    _ ≤ ((k - 1 : ℕ) : ℝ) +
        |-(s : ℝ) ^ 2 / (2 * ((k - 1 : ℕ) : ℝ)) + (s : ℝ) / 2| := by
      apply add_le_add hrem
      rw [hexact]
    _ ≤ ((k - 1 : ℕ) : ℝ) +
        ((s : ℝ) ^ 2 / (2 * ((k - 1 : ℕ) : ℝ)) + (s : ℝ) / 2) := by
      have habs :
          |-(s : ℝ) ^ 2 / (2 * ((k - 1 : ℕ) : ℝ)) + (s : ℝ) / 2| ≤
            (s : ℝ) ^ 2 / (2 * ((k - 1 : ℕ) : ℝ)) + (s : ℝ) / 2 := by
        calc
        |-(s : ℝ) ^ 2 / (2 * ((k - 1 : ℕ) : ℝ)) + (s : ℝ) / 2| ≤
            |-(s : ℝ) ^ 2 / (2 * ((k - 1 : ℕ) : ℝ))| +
              |(s : ℝ) / 2| := abs_add_le _ _
        _ = (s : ℝ) ^ 2 / (2 * ((k - 1 : ℕ) : ℝ)) + (s : ℝ) / 2 := by
          rw [abs_of_nonpos (div_nonpos_of_nonpos_of_nonneg
              (neg_nonpos.mpr hsq) hden.le),
            abs_of_nonneg (by positivity : (0 : ℝ) ≤ (s : ℝ) / 2)]
          ring
      linarith
    _ ≤ (s : ℝ) ^ 2 / 2 + (s : ℝ) / 2 + (k - 1 : ℕ) := by
      linarith

/-! ## Exact first-order cancellation at the limiting density -/

/-- First-order Taylor term with the finite main polynomials and limiting
critical density `p_k`. -/
noncomputable def criticalFirstOrderMainExponent (k n s : ℕ) : ℝ :=
  criticalCapacityLossMainTerm k n s * Real.log (1 - pK k) +
    criticalSelectedIncreaseMainTerm k n s *
      Real.log ((1 - pK k) / pK k)

/-- The `sn` terms cancel exactly by `p_k=(1-p_k)^(k-1)`. -/
theorem criticalFirstOrderMainExponent_eq
    {k n s : ℕ} (hk : 3 ≤ k) :
    criticalFirstOrderMainExponent k n s =
      ((s : ℝ) ^ 2 / 2 -
          ((k - 1 : ℕ) : ℝ) * (s : ℝ) / 2) *
        Real.log (1 / (1 - pK k)) := by
  have hr : 0 < k - 1 := by omega
  have hrR : (0 : ℝ) < (k - 1 : ℕ) := by exact_mod_cast hr
  rw [criticalFirstOrderMainExponent, log_one_sub_div_pK (by omega),
    one_div, Real.log_inv]
  unfold criticalCapacityLossMainTerm criticalSelectedIncreaseMainTerm
  field_simp [hrR.ne']
  norm_num [Nat.cast_sub (show 2 ≤ k by omega),
    Nat.cast_sub (show 1 ≤ k by omega),
    Nat.cast_sub (show 3 ≤ 2 * k by omega)]
  ring

/-- The exact limiting first-order term is at most the positive quadratic
sparse-edge contribution; its remaining linear term is favorable. -/
theorem criticalFirstOrderMainExponent_le_quadratic
    {k n s : ℕ} (hk : 3 ≤ k) :
    criticalFirstOrderMainExponent k n s ≤
      (s : ℝ) ^ 2 / 2 * Real.log (1 / (1 - pK k)) := by
  rw [criticalFirstOrderMainExponent_eq hk]
  have hp : 0 < pK k := pK_pos (by omega)
  have hpOne : pK k < 1 := pK_lt_one (by omega)
  have hinv : 1 < 1 / (1 - pK k) := by
    rw [lt_div_iff₀ (sub_pos.mpr hpOne)]
    linarith
  have hlog : 0 < Real.log (1 / (1 - pK k)) := Real.log_pos hinv
  have hr : (0 : ℝ) ≤ (k - 1 : ℕ) := by positivity
  have hs : (0 : ℝ) ≤ s := by positivity
  nlinarith [mul_nonneg (mul_nonneg hr hs) hlog.le]

/-- The exact signed first-order term before replacing the balanced
quotient/remainder errors by their polynomial main terms. -/
noncomputable def criticalFirstOrderSignedExponent (k n s : ℕ) : ℝ :=
  criticalSignedCapacityLoss k n s * Real.log (1 - pK k) +
    criticalSignedSelectedIncrease k n s *
      Real.log ((1 - pK k) / pK k)

/-- Quotient/remainder errors change the limiting first-order exponent by a
constant depending only on `k` (and not on `n` or `s`). -/
theorem abs_criticalFirstOrderSignedExponent_sub_main_le
    {k n s : ℕ} (hk : 3 ≤ k) (hs : s ≤ n) :
    |criticalFirstOrderSignedExponent k n s -
        criticalFirstOrderMainExponent k n s| ≤
      ((k - 1 : ℕ) : ℝ) *
        (|Real.log (1 - pK k)| +
          |Real.log ((1 - pK k) / pK k)|) := by
  have hK := abs_criticalSignedCapacityLoss_sub_mainTerm_le hk hs
  have hL := abs_criticalSignedSelectedIncrease_sub_mainTerm_le hk hs
  rw [criticalFirstOrderSignedExponent, criticalFirstOrderMainExponent]
  have heq :
      criticalSignedCapacityLoss k n s * Real.log (1 - pK k) +
          criticalSignedSelectedIncrease k n s *
            Real.log ((1 - pK k) / pK k) -
        (criticalCapacityLossMainTerm k n s * Real.log (1 - pK k) +
          criticalSelectedIncreaseMainTerm k n s *
            Real.log ((1 - pK k) / pK k)) =
      (criticalSignedCapacityLoss k n s -
          criticalCapacityLossMainTerm k n s) * Real.log (1 - pK k) +
        (criticalSignedSelectedIncrease k n s -
          criticalSelectedIncreaseMainTerm k n s) *
            Real.log ((1 - pK k) / pK k) := by ring
  rw [heq]
  calc
    |(criticalSignedCapacityLoss k n s -
          criticalCapacityLossMainTerm k n s) * Real.log (1 - pK k) +
        (criticalSignedSelectedIncrease k n s -
          criticalSelectedIncreaseMainTerm k n s) *
            Real.log ((1 - pK k) / pK k)| ≤
        |criticalSignedCapacityLoss k n s -
          criticalCapacityLossMainTerm k n s| * |Real.log (1 - pK k)| +
        |criticalSignedSelectedIncrease k n s -
          criticalSelectedIncreaseMainTerm k n s| *
            |Real.log ((1 - pK k) / pK k)| := by
      simpa only [abs_mul] using abs_add_le
        ((criticalSignedCapacityLoss k n s -
          criticalCapacityLossMainTerm k n s) * Real.log (1 - pK k))
        ((criticalSignedSelectedIncrease k n s -
          criticalSelectedIncreaseMainTerm k n s) *
            Real.log ((1 - pK k) / pK k))
    _ ≤ ((k - 1 : ℕ) : ℝ) * |Real.log (1 - pK k)| +
        ((k - 1 : ℕ) : ℝ) *
          |Real.log ((1 - pK k) / pK k)| := by
      exact add_le_add
        (mul_le_mul_of_nonneg_right hK (abs_nonneg _))
        (mul_le_mul_of_nonneg_right hL (abs_nonneg _))
    _ = _ := by ring

/-- Exact finite discrepancy between the selected count and `p_k` times the
balanced capacity.  This is the `O_k(n)` term used before the critical
first-order cancellation. -/
theorem criticalTargetSelectedCount_sub_p_mul_capacity_eq
    {k n : ℕ} (hk : 3 ≤ k)
    (hfeasible :
      DenseGraph.balancedMultipartiteInternalCapacity (k - 1) n ≤
        criticalEdgeCount k n) :
    (criticalTargetSelectedCount k n : ℝ) -
        pK k * (criticalTargetCapacity k n : ℝ) =
      (1 - gammaK k) * (n : ℝ) / 2 -
        criticalEdgeCountFloorError k n -
        (1 - pK k) * criticalBalancedResidueError k n := by
  have hr : 0 < k - 1 := by omega
  have hrR : (0 : ℝ) < (k - 1 : ℕ) := by exact_mod_cast hr
  rw [criticalTargetSelectedCount, Nat.cast_sub hfeasible,
    criticalTargetCapacity_cast_eq hk,
    criticalBalancedInternalCapacity_cast_eq hk]
  unfold criticalEdgeCountFloorError completeEdgeCount gammaK
  rw [Nat.cast_choose_two]
  norm_num [Nat.cast_sub (show 1 ≤ k by omega),
    Nat.cast_sub (show 2 ≤ k by omega)]
  field_simp [hrR.ne']
  ring

/-- An explicit `O_k(n)` bound for the preceding exact discrepancy. -/
theorem abs_criticalTargetSelectedCount_sub_p_mul_capacity_le
    {k n : ℕ} (hk : 3 ≤ k)
    (hfeasible :
      DenseGraph.balancedMultipartiteInternalCapacity (k - 1) n ≤
        criticalEdgeCount k n) :
    |(criticalTargetSelectedCount k n : ℝ) -
        pK k * (criticalTargetCapacity k n : ℝ)| ≤
      (n : ℝ) / 2 + (k - 1 : ℕ) + 1 := by
  rw [criticalTargetSelectedCount_sub_p_mul_capacity_eq hk hfeasible]
  have hfloor := criticalEdgeCountFloorError_mem_Ico hk n
  have hfloor0 : 0 ≤ criticalEdgeCountFloorError k n := hfloor.1
  have hfloor1 : criticalEdgeCountFloorError k n ≤ 1 := hfloor.2.le
  have hres0 := criticalBalancedResidueError_nonneg (k := k) (n := n) hk
  have hres := criticalBalancedResidueError_le (k := k) (n := n) hk
  have hp0 := (pK_pos (show 2 ≤ k by omega)).le
  have hp1 := (pK_lt_one (show 2 ≤ k by omega)).le
  have hg0 := (gammaK_pos hk).le
  have hg1 := (gammaK_lt_one hk).le
  have hlead0 : 0 ≤ (1 - gammaK k) * (n : ℝ) / 2 := by positivity
  have hleadLe : (1 - gammaK k) * (n : ℝ) / 2 ≤ (n : ℝ) / 2 := by
    have := mul_le_mul_of_nonneg_right (show 1 - gammaK k ≤ 1 by linarith)
      (Nat.cast_nonneg n)
    nlinarith
  have hweighted0 :
      0 ≤ (1 - pK k) * criticalBalancedResidueError k n := by positivity
  have hweightedLe :
      (1 - pK k) * criticalBalancedResidueError k n ≤
        criticalBalancedResidueError k n := by
    have honepLe : 1 - pK k ≤ 1 := by linarith
    simpa using mul_le_mul_of_nonneg_right honepLe hres0
  rw [abs_le]
  constructor <;> nlinarith

/-- The target capacity has a simple quadratic lower bound once
`n ≥ 4(k-1)`. -/
theorem criticalTargetCapacity_quadratic_lower
    {k n : ℕ} (hk : 3 ≤ k) (hn : 4 * (k - 1) ≤ n) :
    (n : ℝ) ^ 2 / 8 ≤ (criticalTargetCapacity k n : ℝ) := by
  have hr : 0 < k - 1 := by omega
  have hrTwo : 2 ≤ k - 1 := by omega
  have hnEight : 8 ≤ n := by omega
  have happ := DenseGraph.balancedMultipartiteCrossCapacity_approx
    (r := k - 1) (q := n) hr
  have hmain :
      (n : ℝ) ^ 2 / 4 ≤
        (((k - 1 : ℕ) : ℝ) - 1) * (n : ℝ) ^ 2 /
          (2 * ((k - 1 : ℕ) : ℝ)) := by
    have hrR : (2 : ℝ) ≤ (k - 1 : ℕ) := by exact_mod_cast hrTwo
    have hnSq : 0 ≤ (n : ℝ) ^ 2 := sq_nonneg _
    field_simp
    nlinarith
  have herror :
      (((k - 1 : ℕ) : ℝ) - 1) * (n : ℝ) ^ 2 /
          (2 * ((k - 1 : ℕ) : ℝ)) -
        (k - 1 : ℕ) ≤
      (criticalTargetCapacity k n : ℝ) := by
    have hneg := neg_le_of_abs_le happ
    simpa [criticalTargetCapacity] using hneg
  have hrQuarter : ((k - 1 : ℕ) : ℝ) ≤ (n : ℝ) / 4 := by
    have hnR : (4 : ℝ) * ((k - 1 : ℕ) : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast hn
    linarith
  have hnlin : (n : ℝ) / 4 ≤ (n : ℝ) ^ 2 / 8 := by
    have hnR : (8 : ℝ) ≤ n := by exact_mod_cast hnEight
    nlinarith
  linarith

/-- Explicit finite `O(1/n)` control of the selected density. -/
theorem criticalBalancedSelectedDensity_error_le
    {k n : ℕ} (hk : 3 ≤ k) (hn : 4 * (k - 1) ≤ n)
    (hfeasible :
      DenseGraph.balancedMultipartiteInternalCapacity (k - 1) n ≤
        criticalEdgeCount k n) :
    |criticalBalancedSelectedDensity k n - pK k| ≤ 8 / (n : ℝ) := by
  have hnEight : 8 ≤ n := by omega
  have hnPos : (0 : ℝ) < n := by positivity
  have hcapacity := criticalTargetCapacity_quadratic_lower hk hn
  have hcapacityPos : (0 : ℝ) < criticalTargetCapacity k n := by
    have : (0 : ℝ) < (n : ℝ) ^ 2 / 8 := by positivity
    linarith
  have hnum :=
    abs_criticalTargetSelectedCount_sub_p_mul_capacity_le hk hfeasible
  have hrQuarter : ((k - 1 : ℕ) : ℝ) ≤ (n : ℝ) / 4 := by
    have hnR : (4 : ℝ) * ((k - 1 : ℕ) : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast hn
    linarith
  have hone : (1 : ℝ) ≤ (n : ℝ) / 8 := by
    have hnR : (8 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnEight
    linarith
  have hnum' :
      |(criticalTargetSelectedCount k n : ℝ) -
          pK k * (criticalTargetCapacity k n : ℝ)| ≤ (n : ℝ) := by
    linarith
  unfold criticalBalancedSelectedDensity
  rw [show
      (criticalTargetSelectedCount k n : ℝ) /
            (criticalTargetCapacity k n : ℝ) - pK k =
          ((criticalTargetSelectedCount k n : ℝ) -
            pK k * (criticalTargetCapacity k n : ℝ)) /
              (criticalTargetCapacity k n : ℝ) by
        field_simp]
  rw [abs_div, abs_of_pos hcapacityPos]
  apply (div_le_iff₀ hcapacityPos).2
  have hmul := mul_le_mul_of_nonneg_left hcapacity
    (show 0 ≤ 8 / (n : ℝ) by positivity)
  calc
    |(criticalTargetSelectedCount k n : ℝ) -
        pK k * (criticalTargetCapacity k n : ℝ)| ≤ (n : ℝ) := hnum'
    _ = (8 / (n : ℝ)) * ((n : ℝ) ^ 2 / 8) := by field_simp
    _ ≤ (8 / (n : ℝ)) * (criticalTargetCapacity k n : ℝ) := hmul

/-! ## Uniform Taylor parameters -/

/-- Limiting balanced cross capacity divided by `n²`. -/
def criticalReferenceCapacityScale (k : ℕ) : ℝ :=
  (((k - 2 : ℕ) : ℝ) / ((k - 1 : ℕ) : ℝ)) / 2

/-- Dimensionless quadratic Taylor coefficient.  Coordinates are grouped as
`((capacityScale, selectedDensity), (lossFraction, remainingVertexRatio))`.
The four-variable form makes uniformity in a moving sparse size explicit. -/
def criticalNormalizedQuadratic
    (z : (ℝ × ℝ) × (ℝ × ℝ)) : ℝ :=
  -(z.2.2 ^ 2) / (2 * z.1.1 * (1 - z.1.2)) +
    z.2.2 ^ 2 * z.2.1 ^ 2 / (2 * z.1.1) -
    z.2.2 ^ 2 * (1 - z.2.1) ^ 2 / (2 * z.1.1 * z.1.2)

/-- The limiting normalized quadratic coefficient is exactly `-q_k`. -/
theorem criticalNormalizedQuadratic_at_limit
    {k : ℕ} (hk : 3 ≤ k) :
    criticalNormalizedQuadratic
        ((criticalReferenceCapacityScale k, pK k),
          (criticalReferenceLossFraction k, 1)) =
      -criticalQuadraticCoefficient k := by
  have hr : 0 < k - 1 := by omega
  have hd : 0 < k - 2 := by omega
  have hrR : (0 : ℝ) < (k - 1 : ℕ) := by exact_mod_cast hr
  have hdR : (0 : ℝ) < (k - 2 : ℕ) := by exact_mod_cast hd
  have hp : 0 < pK k := pK_pos (by omega)
  have hq : 0 < 1 - pK k := sub_pos.mpr (pK_lt_one (by omega))
  have hrel : ((k - 1 : ℕ) : ℝ) = ((k - 2 : ℕ) : ℝ) + 1 := by
    norm_num [Nat.cast_sub (show 1 ≤ k by omega),
      Nat.cast_sub (show 2 ≤ k by omega)]
    ring
  unfold criticalNormalizedQuadratic criticalReferenceCapacityScale
    criticalReferenceLossFraction criticalQuadraticCoefficient
  rw [hrel]
  field_simp [hrR.ne', hdR.ne', hp.ne', hq.ne']
  ring

/-- The normalized quadratic coefficient is continuous at its critical
reference point. -/
theorem continuousAt_criticalNormalizedQuadratic_limit
    {k : ℕ} (hk : 3 ≤ k) :
    ContinuousAt criticalNormalizedQuadratic
      ((criticalReferenceCapacityScale k, pK k),
        (criticalReferenceLossFraction k, 1)) := by
  have hr : 0 < k - 1 := by omega
  have hd : 0 < k - 2 := by omega
  have ha : 0 < criticalReferenceCapacityScale k := by
    unfold criticalReferenceCapacityScale
    positivity
  have hp : 0 < pK k := pK_pos (by omega)
  have hq : 0 < 1 - pK k := sub_pos.mpr (pK_lt_one (by omega))
  unfold criticalNormalizedQuadratic
  fun_prop (disch := positivity)

/-- Uniform neighborhood in which the normalized quadratic coefficient
retains all but one sixteenth of the positive critical gap. -/
theorem exists_criticalQuadraticContinuityRadius
    {k : ℕ} (hk : 3 ≤ k) :
    ∃ epsilon : ℝ, 0 < epsilon ∧
      ∀ {a d x y : ℝ},
        |a - criticalReferenceCapacityScale k| < epsilon →
        |d - pK k| < epsilon →
        |x - criticalReferenceLossFraction k| < epsilon →
        |y - 1| < epsilon →
        criticalNormalizedQuadratic ((a, d), (x, y)) ≤
          -criticalQuadraticCoefficient k +
            criticalSparseQuadraticGap k / 16 := by
  have hgap : 0 < criticalSparseQuadraticGap k / 16 := by
    positivity [criticalSparseQuadraticGap_pos hk]
  obtain ⟨epsilon, hepsilon, hcontrol⟩ :=
    (Metric.continuousAt_iff.mp
      (continuousAt_criticalNormalizedQuadratic_limit hk))
      (criticalSparseQuadraticGap k / 16) hgap
  refine ⟨epsilon, hepsilon, ?_⟩
  intro a d x y ha hd hx hy
  have hdist :
      dist ((a, d), (x, y))
          ((criticalReferenceCapacityScale k, pK k),
            (criticalReferenceLossFraction k, 1)) < epsilon := by
    simpa only [Prod.dist_eq, Real.dist_eq, max_lt_iff] using
      ⟨⟨ha, hd⟩, hx, hy⟩
  have hclose := hcontrol hdist
  rw [criticalNormalizedQuadratic_at_limit hk, Real.dist_eq] at hclose
  simpa [add_comm] using
    (sub_lt_iff_lt_add.mp ((abs_lt.mp hclose).2)).le

/-- A canonical positive continuity radius for the critical normalized
quadratic form.  The irrelevant small-`k` branch makes the definition total. -/
noncomputable def criticalQuadraticContinuityRadius (k : ℕ) : ℝ :=
  if hk : 3 ≤ k then
    Classical.choose (exists_criticalQuadraticContinuityRadius hk)
  else 1

theorem criticalQuadraticContinuityRadius_pos
    {k : ℕ} (hk : 3 ≤ k) :
    0 < criticalQuadraticContinuityRadius k := by
  rw [criticalQuadraticContinuityRadius, dif_pos hk]
  exact (Classical.choose_spec
    (exists_criticalQuadraticContinuityRadius hk)).1

/-- The chosen radius retains all but one sixteenth of the critical
quadratic gap.  This continuity estimate is one ingredient of the paper's
second-order critical calculation. -/
theorem criticalQuadraticContinuityRadius_spec
    {k : ℕ} (hk : 3 ≤ k) :
    ∀ {a d x y : ℝ},
      |a - criticalReferenceCapacityScale k| <
          criticalQuadraticContinuityRadius k →
      |d - pK k| < criticalQuadraticContinuityRadius k →
      |x - criticalReferenceLossFraction k| <
          criticalQuadraticContinuityRadius k →
      |y - 1| < criticalQuadraticContinuityRadius k →
      criticalNormalizedQuadratic ((a, d), (x, y)) ≤
        -criticalQuadraticCoefficient k +
          criticalSparseQuadraticGap k / 16 := by
  rw [criticalQuadraticContinuityRadius, dif_pos hk]
  exact (Classical.choose_spec
    (exists_criticalQuadraticContinuityRadius hk)).2

/-! ## The exact finite quadratic term -/

/-- Quadratic part of the reusable second-order binomial comparison at the
critical reference slice. -/
def criticalQuadraticExponent (k n s : ℕ) : ℝ :=
  -((criticalCapacityLoss k n s +
        criticalSelectedIncrease k n s : ℕ) : ℝ) ^ 2 /
      (2 * ((criticalTargetCapacity k n -
        criticalTargetSelectedCount k n : ℕ) : ℝ)) +
    (criticalCapacityLoss k n s : ℝ) ^ 2 /
      (2 * (criticalTargetCapacity k n : ℝ)) -
    (criticalSelectedIncrease k n s : ℝ) ^ 2 /
      (2 * (criticalTargetSelectedCount k n : ℝ))

/-- The four dimensionless coordinates which turn the finite quadratic term
into `s²` times `criticalNormalizedQuadratic`. -/
def criticalQuadraticCoordinates (k n s : ℕ) :
    (ℝ × ℝ) × (ℝ × ℝ) :=
  (((criticalTargetCapacity k n : ℝ) / (n : ℝ) ^ 2,
      (criticalTargetSelectedCount k n : ℝ) /
        (criticalTargetCapacity k n : ℝ)),
    ((criticalCapacityLoss k n s : ℝ) /
        ((criticalCapacityLoss k n s +
          criticalSelectedIncrease k n s : ℕ) : ℝ),
      ((n - s : ℕ) : ℝ) / (n : ℝ)))

/-- Exact normalization identity for the finite quadratic expression. -/
theorem criticalQuadraticExponent_eq_normalized
    {k n s : ℕ} (hn : 0 < n) (hs : 0 < s) (hsn : s < n)
    (hM : 0 < criticalTargetSelectedCount k n)
    (hMN : criticalTargetSelectedCount k n < criticalTargetCapacity k n)
    (hsum : criticalCapacityLoss k n s +
        criticalSelectedIncrease k n s = s * (n - s)) :
    criticalQuadraticExponent k n s =
      (s : ℝ) ^ 2 *
        criticalNormalizedQuadratic (criticalQuadraticCoordinates k n s) := by
  have hN : (0 : ℝ) < criticalTargetCapacity k n := by
    exact_mod_cast hM.trans hMN
  have hMR : (0 : ℝ) < criticalTargetSelectedCount k n := by
    exact_mod_cast hM
  have hA : (0 : ℝ) < (criticalTargetCapacity k n : ℝ) -
      (criticalTargetSelectedCount k n : ℝ) := by
    exact sub_pos.mpr (by exact_mod_cast hMN)
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hnsR : (0 : ℝ) < (n : ℝ) - (s : ℝ) := by
    exact sub_pos.mpr (by exact_mod_cast hsn)
  have hsumPos : 0 < criticalCapacityLoss k n s +
      criticalSelectedIncrease k n s := by
    rw [hsum]
    exact Nat.mul_pos hs (Nat.sub_pos_of_lt hsn)
  have hsumR : (0 : ℝ) <
      ((criticalCapacityLoss k n s +
        criticalSelectedIncrease k n s : ℕ) : ℝ) := by
    exact_mod_cast hsumPos
  have hsumCast :
      (criticalCapacityLoss k n s : ℝ) +
          (criticalSelectedIncrease k n s : ℝ) =
        (s : ℝ) * ((n - s : ℕ) : ℝ) := by
    exact_mod_cast hsum
  have hLcast : (criticalSelectedIncrease k n s : ℝ) =
      (s : ℝ) * ((n - s : ℕ) : ℝ) -
        (criticalCapacityLoss k n s : ℝ) := by
    linarith
  unfold criticalQuadraticExponent criticalQuadraticCoordinates
    criticalNormalizedQuadratic
  rw [hsum, Nat.cast_mul, Nat.cast_sub hsn.le,
    Nat.cast_sub hMN.le]
  rw [hLcast, Nat.cast_sub hsn.le]
  field_simp [hN.ne', hMR.ne', hA.ne', hnR.ne', hsR.ne', hnsR.ne',
    hsumR.ne']

/-- Continuity turns coordinatewise finite control into the desired
quadratic penalty. -/
theorem criticalQuadraticExponent_le_of_close
    {k n s : ℕ} (hk : 3 ≤ k) (hn : 0 < n) (hs : 0 < s) (hsn : s < n)
    (hM : 0 < criticalTargetSelectedCount k n)
    (hMN : criticalTargetSelectedCount k n < criticalTargetCapacity k n)
    (hsum : criticalCapacityLoss k n s +
        criticalSelectedIncrease k n s = s * (n - s))
    {epsilon : ℝ}
    (hclose : ∀ {a d x y : ℝ},
      |a - criticalReferenceCapacityScale k| < epsilon →
      |d - pK k| < epsilon →
      |x - criticalReferenceLossFraction k| < epsilon →
      |y - 1| < epsilon →
      criticalNormalizedQuadratic ((a, d), (x, y)) ≤
        -criticalQuadraticCoefficient k +
          criticalSparseQuadraticGap k / 16)
    (ha : |(criticalQuadraticCoordinates k n s).1.1 -
        criticalReferenceCapacityScale k| < epsilon)
    (hd : |(criticalQuadraticCoordinates k n s).1.2 - pK k| < epsilon)
    (hx : |(criticalQuadraticCoordinates k n s).2.1 -
        criticalReferenceLossFraction k| < epsilon)
    (hy : |(criticalQuadraticCoordinates k n s).2.2 - 1| < epsilon) :
    criticalQuadraticExponent k n s ≤
      (-criticalQuadraticCoefficient k +
        criticalSparseQuadraticGap k / 16) * (s : ℝ) ^ 2 := by
  rw [criticalQuadraticExponent_eq_normalized hn hs hsn hM hMN hsum]
  have hnorm := hclose ha hd hx hy
  nlinarith [sq_nonneg (s : ℝ)]

/-- The normalized balanced target capacity converges to its critical scale. -/
theorem criticalTargetCapacity_scale_tendsto
    (k : ℕ) (hk : 3 ≤ k) :
    Tendsto
      (fun n : ℕ ↦
        (criticalTargetCapacity k n : ℝ) / (n : ℝ) ^ 2)
      atTop (nhds (criticalReferenceCapacityScale k)) := by
  have h :=
    (criticalTargetCapacity_orderedSquare_tendsto k hk).const_mul (1 / 2 : ℝ)
  convert h using 1
  · funext n
    ring
  · unfold criticalReferenceCapacityScale
    ring

/-- Exact error of the remaining-vertex coordinate. -/
theorem abs_criticalRemainingVertexRatio_sub_one
    {n s : ℕ} (hn : 0 < n) (hs : s ≤ n) :
    |((n - s : ℕ) : ℝ) / (n : ℝ) - 1| = (s : ℝ) / (n : ℝ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  rw [Nat.cast_sub hs]
  have heq : ((n : ℝ) - (s : ℝ)) / (n : ℝ) - 1 =
      -(s : ℝ) / (n : ℝ) := by
    field_simp
    ring
  have hs0 : (0 : ℝ) ≤ s := by positivity
  rw [heq, abs_of_nonpos (div_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr hs0) hnR.le)]
  ring

/-- Explicit uniform estimate for the normalized capacity-loss coordinate. -/
theorem abs_criticalCapacityLossRatio_sub_reference_le
    {k n s : ℕ} (hk : 3 ≤ k) (hs : 1 ≤ s) (hsn : 2 * s ≤ n)
    (hcapacity : criticalMaximumCombinedCapacity k n s ≤
      criticalTargetCapacity k n)
    (hinternal :
      DenseGraph.balancedMultipartiteInternalCapacity (k - 1) (n - s) ≤
        DenseGraph.balancedMultipartiteInternalCapacity (k - 1) n) :
    |(criticalCapacityLoss k n s : ℝ) /
          ((criticalCapacityLoss k n s +
            criticalSelectedIncrease k n s : ℕ) : ℝ) -
        criticalReferenceLossFraction k| ≤
      ((s : ℝ) + 2 * ((k - 1 : ℕ) : ℝ) + 1) / (n : ℝ) := by
  have hsle : s ≤ n := by omega
  have hsnlt : s < n := by omega
  have hn : 0 < n := by omega
  have hsum := criticalCapacityLoss_add_selectedIncrease hk hsle hcapacity hinternal
  have hsumPos : 0 < s * (n - s) :=
    Nat.mul_pos (by omega) (Nat.sub_pos_of_lt hsnlt)
  have hdenR : (0 : ℝ) < (s : ℝ) * ((n - s : ℕ) : ℝ) := by
    exact_mod_cast hsumPos
  have hsR0 : (0 : ℝ) < s := by exact_mod_cast hs
  have hnsR : (0 : ℝ) < (n - s : ℕ) := by
    exact_mod_cast Nat.sub_pos_of_lt hsnlt
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hraw := abs_criticalCapacityLoss_sub_fraction_mul_le hk hsle hcapacity
  have heq :
      (criticalCapacityLoss k n s : ℝ) /
          ((criticalCapacityLoss k n s +
            criticalSelectedIncrease k n s : ℕ) : ℝ) -
        criticalReferenceLossFraction k =
      ((criticalCapacityLoss k n s : ℝ) -
          criticalReferenceLossFraction k *
            ((s : ℝ) * ((n - s : ℕ) : ℝ))) /
        ((s : ℝ) * ((n - s : ℕ) : ℝ)) := by
    rw [hsum, Nat.cast_mul]
    field_simp [hsR0.ne', hnsR.ne']
  rw [heq, abs_div, abs_of_pos hdenR]
  have hhalf : (n : ℝ) / 2 ≤ ((n - s : ℕ) : ℝ) := by
    rw [Nat.cast_sub hsle]
    have hsnR : (2 : ℝ) * (s : ℝ) ≤ n := by exact_mod_cast hsn
    linarith
  have hsR : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have hr0 : (0 : ℝ) ≤ (k - 1 : ℕ) := by positivity
  have hnum :
      (s : ℝ) ^ 2 / 2 + (s : ℝ) / 2 + (k - 1 : ℕ) ≤
        (s : ℝ) *
          ((s : ℝ) + 2 * ((k - 1 : ℕ) : ℝ) + 1) / 2 := by
    have hrs := mul_le_mul_of_nonneg_left hsR hr0
    nlinarith
  apply (div_le_iff₀ hdenR).2
  calc
    |(criticalCapacityLoss k n s : ℝ) -
          criticalReferenceLossFraction k *
            ((s : ℝ) * ((n - s : ℕ) : ℝ))| ≤
        (s : ℝ) ^ 2 / 2 + (s : ℝ) / 2 + (k - 1 : ℕ) := hraw
    _ ≤ (s : ℝ) *
          ((s : ℝ) + 2 * ((k - 1 : ℕ) : ℝ) + 1) / 2 := hnum
    _ ≤ (((s : ℝ) + 2 * ((k - 1 : ℕ) : ℝ) + 1) / (n : ℝ)) *
          ((s : ℝ) * ((n - s : ℕ) : ℝ)) := by
      have hc0 : 0 ≤ (s : ℝ) + 2 * ((k - 1 : ℕ) : ℝ) + 1 := by positivity
      rw [div_mul_eq_mul_div]
      apply (le_div_iff₀ hnR).2
      have hmul := mul_le_mul_of_nonneg_left hhalf
        (mul_nonneg (show (0 : ℝ) ≤ s by positivity) hc0)
      nlinarith

/-- A fixed compact-density margin around the critical selected density. -/
noncomputable def criticalDensityMargin (k : ℕ) : ℝ :=
  min (pK k) (1 - pK k) / 4

/-- The explicit cubic constant supplied by the reusable compact-band
second-order estimate. -/
noncomputable def criticalSecondOrderCubicConstant (k : ℕ) : ℝ :=
  3 + 6 / criticalDensityMargin k ^ 2

/-- A positive smallness threshold which simultaneously supplies the three
half-range conditions in the second-order estimate and makes its cubic error
at most one eighth of the natural-log critical gap. -/
noncomputable def criticalTaylorDeltaBound (k : ℕ) : ℝ :=
  min (1 / 16 : ℝ)
    (min (criticalDensityMargin k / 16)
      (criticalSparseQuadraticGap k /
        (512 * criticalSecondOrderCubicConstant k)))

/-- The single k-only smallness bound used by the clean critical slice.  It
combines the explicit Taylor restrictions with the continuity neighborhood
for the normalized quadratic coefficient. -/
noncomputable def criticalCombinedSliceDelta (k : ℕ) : ℝ :=
  min (criticalTaylorDeltaBound k)
    (criticalQuadraticContinuityRadius k / 16)

theorem criticalDensityMargin_pos
    {k : ℕ} (hk : 3 ≤ k) :
    0 < criticalDensityMargin k := by
  unfold criticalDensityMargin
  have hp : 0 < pK k := pK_pos (by omega)
  have hq : 0 < 1 - pK k := sub_pos.mpr (pK_lt_one (by omega))
  positivity

theorem criticalDensityMargin_le_pK_div_four (k : ℕ) :
    criticalDensityMargin k ≤ pK k / 4 := by
  unfold criticalDensityMargin
  exact div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)

theorem criticalDensityMargin_le_one_sub_pK_div_four (k : ℕ) :
    criticalDensityMargin k ≤ (1 - pK k) / 4 := by
  unfold criticalDensityMargin
  exact div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)

/-- Once the explicit `8/n` error is below the fixed margin, the exact
reference density lies in the compact band required by the reusable Taylor
estimate. -/
theorem criticalBalancedSelectedDensity_mem_compact
    {k n : ℕ} (hk : 3 ≤ k) (hn : 4 * (k - 1) ≤ n)
    (hfeasible :
      DenseGraph.balancedMultipartiteInternalCapacity (k - 1) n ≤
        criticalEdgeCount k n)
    (hmargin : 8 / (n : ℝ) ≤ criticalDensityMargin k) :
    criticalBalancedSelectedDensity k n ∈
      Set.Icc (criticalDensityMargin k) (1 - criticalDensityMargin k) := by
  have herr := criticalBalancedSelectedDensity_error_le hk hn hfeasible
  have hlambda0 := (criticalDensityMargin_pos hk).le
  have hlambdaP := criticalDensityMargin_le_pK_div_four k
  have hlambdaQ := criticalDensityMargin_le_one_sub_pK_div_four k
  rw [abs_le] at herr
  constructor <;> nlinarith

/-- On the critical compact band, the capacity derivative
`log (1-d)` differs from its limiting value by at most
`|d-p_k| / criticalDensityMargin`. -/
theorem abs_log_one_sub_density_sub_critical_le
    {k : ℕ} (hk : 3 ≤ k) {d : ℝ}
    (hd : d ∈ Set.Icc (criticalDensityMargin k)
      (1 - criticalDensityMargin k)) :
    |Real.log (1 - d) - Real.log (1 - pK k)| ≤
      |d - pK k| / criticalDensityMargin k := by
  have hlambda := criticalDensityMargin_pos hk
  have hp := pK_pos (k := k) (by omega)
  have hpOne := pK_lt_one (k := k) (by omega)
  have hlambdaQ := criticalDensityMargin_le_one_sub_pK_div_four k
  have hq : criticalDensityMargin k ≤ 1 - pK k := by
    nlinarith [hlambda.le]
  have hOneD : criticalDensityMargin k ≤ 1 - d := by linarith [hd.2]
  have hlog := DenseGraph.abs_log_sub_log_le_div_of_lower
    hlambda hOneD hq
  simpa [abs_sub_comm] using hlog

/-- On the critical compact band, the selected-count derivative
`log ((1-d)/d)` has the corresponding explicit Lipschitz bound. -/
theorem abs_log_one_sub_div_density_sub_critical_le
    {k : ℕ} (hk : 3 ≤ k) {d : ℝ}
    (hd : d ∈ Set.Icc (criticalDensityMargin k)
      (1 - criticalDensityMargin k)) :
    |Real.log ((1 - d) / d) -
        Real.log ((1 - pK k) / pK k)| ≤
      2 * |d - pK k| / criticalDensityMargin k := by
  have hlambda := criticalDensityMargin_pos hk
  have hp := pK_pos (k := k) (by omega)
  have hpOne := pK_lt_one (k := k) (by omega)
  have hd0 : 0 < d := hlambda.trans_le hd.1
  have hOneD0 : 0 < 1 - d := by linarith [hd.2, hlambda]
  have hcap := abs_log_one_sub_density_sub_critical_le hk hd
  have hlambdaP := criticalDensityMargin_le_pK_div_four k
  have hlambdaP' : criticalDensityMargin k ≤ pK k := by
    nlinarith [hlambda.le]
  have hsel := DenseGraph.abs_log_sub_log_le_div_of_lower
    hlambda hd.1 hlambdaP'
  rw [Real.log_div hOneD0.ne' hd0.ne',
    Real.log_div (sub_pos.mpr hpOne).ne' hp.ne']
  calc
    |(Real.log (1 - d) - Real.log d) -
        (Real.log (1 - pK k) - Real.log (pK k))| =
        |(Real.log (1 - d) - Real.log (1 - pK k)) -
          (Real.log d - Real.log (pK k))| := by ring
    _ ≤ |Real.log (1 - d) - Real.log (1 - pK k)| +
        |Real.log d - Real.log (pK k)| := abs_sub _ _
    _ ≤ |d - pK k| / criticalDensityMargin k +
        |d - pK k| / criticalDensityMargin k := add_le_add hcap hsel
    _ = 2 * |d - pK k| / criticalDensityMargin k := by ring

/-- First-order exponent evaluated at an arbitrary exact selected density. -/
noncomputable def criticalFirstOrderAtDensityExponent
    (k n s : ℕ) (d : ℝ) : ℝ :=
  criticalSignedCapacityLoss k n s * Real.log (1 - d) +
    criticalSignedSelectedIncrease k n s * Real.log ((1 - d) / d)

/-- Uniform perturbation of the first-order exponent across the critical
compact density band. -/
theorem abs_criticalFirstOrderAtDensityExponent_sub_signed_le
    {k n s : ℕ} (hk : 3 ≤ k) {d : ℝ}
    (hd : d ∈ Set.Icc (criticalDensityMargin k)
      (1 - criticalDensityMargin k)) :
    |criticalFirstOrderAtDensityExponent k n s d -
        criticalFirstOrderSignedExponent k n s| ≤
      (|criticalSignedCapacityLoss k n s| +
          2 * |criticalSignedSelectedIncrease k n s|) *
        |d - pK k| / criticalDensityMargin k := by
  have hK := abs_log_one_sub_density_sub_critical_le hk hd
  have hL := abs_log_one_sub_div_density_sub_critical_le hk hd
  rw [criticalFirstOrderAtDensityExponent, criticalFirstOrderSignedExponent]
  have heq :
      criticalSignedCapacityLoss k n s * Real.log (1 - d) +
          criticalSignedSelectedIncrease k n s * Real.log ((1 - d) / d) -
        (criticalSignedCapacityLoss k n s * Real.log (1 - pK k) +
          criticalSignedSelectedIncrease k n s *
            Real.log ((1 - pK k) / pK k)) =
      criticalSignedCapacityLoss k n s *
          (Real.log (1 - d) - Real.log (1 - pK k)) +
        criticalSignedSelectedIncrease k n s *
          (Real.log ((1 - d) / d) -
            Real.log ((1 - pK k) / pK k)) := by ring
  rw [heq]
  calc
    |criticalSignedCapacityLoss k n s *
          (Real.log (1 - d) - Real.log (1 - pK k)) +
        criticalSignedSelectedIncrease k n s *
          (Real.log ((1 - d) / d) -
            Real.log ((1 - pK k) / pK k))| ≤
        |criticalSignedCapacityLoss k n s| *
            |Real.log (1 - d) - Real.log (1 - pK k)| +
          |criticalSignedSelectedIncrease k n s| *
            |Real.log ((1 - d) / d) -
              Real.log ((1 - pK k) / pK k)| := by
      simpa only [abs_mul] using abs_add_le
        (criticalSignedCapacityLoss k n s *
          (Real.log (1 - d) - Real.log (1 - pK k)))
        (criticalSignedSelectedIncrease k n s *
          (Real.log ((1 - d) / d) -
            Real.log ((1 - pK k) / pK k)))
    _ ≤ |criticalSignedCapacityLoss k n s| *
          (|d - pK k| / criticalDensityMargin k) +
        |criticalSignedSelectedIncrease k n s| *
          (2 * |d - pK k| / criticalDensityMargin k) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left hK (abs_nonneg _))
        (mul_le_mul_of_nonneg_left hL (abs_nonneg _))
    _ = (|criticalSignedCapacityLoss k n s| +
          2 * |criticalSignedSelectedIncrease k n s|) *
        |d - pK k| / criticalDensityMargin k := by ring

/-- The fixed quotient/remainder contribution to the critical first-order
bound. -/
noncomputable def criticalFirstOrderResidueBound (k : ℕ) : ℝ :=
  ((k - 1 : ℕ) : ℝ) *
    (|Real.log (1 - pK k)| +
      |Real.log ((1 - pK k) / pK k)|)

/-- First-order cancellation with an explicit density-perturbation term.
Nonnegativity of the signed loss/increase is exactly what the later natural
capacity bookkeeping supplies in the sparse regime. -/
theorem criticalFirstOrderAtDensityExponent_le
    {k n s : ℕ} (hk : 3 ≤ k) (hs : s ≤ n) {d : ℝ}
    (hK : 0 ≤ criticalSignedCapacityLoss k n s)
    (hL : 0 ≤ criticalSignedSelectedIncrease k n s)
    (hd : d ∈ Set.Icc (criticalDensityMargin k)
      (1 - criticalDensityMargin k)) :
    criticalFirstOrderAtDensityExponent k n s d ≤
      (s : ℝ) ^ 2 / 2 * Real.log (1 / (1 - pK k)) +
        criticalFirstOrderResidueBound k +
        (2 * (s : ℝ) * ((n - s : ℕ) : ℝ)) *
          |d - pK k| / criticalDensityMargin k := by
  have hpert :=
    abs_criticalFirstOrderAtDensityExponent_sub_signed_le
      (n := n) (s := s) hk hd
  have hpertUpper :=
    (le_abs_self
      (criticalFirstOrderAtDensityExponent k n s d -
        criticalFirstOrderSignedExponent k n s)).trans hpert
  have hres := abs_criticalFirstOrderSignedExponent_sub_main_le hk hs
  have hresUpper :=
    (le_abs_self
      (criticalFirstOrderSignedExponent k n s -
        criticalFirstOrderMainExponent k n s)).trans hres
  have hmain := criticalFirstOrderMainExponent_le_quadratic
    (k := k) (n := n) (s := s) hk
  have hsum := criticalSignedCapacityLoss_add_selectedIncrease hk hs
  have hcoeff :
      |criticalSignedCapacityLoss k n s| +
          2 * |criticalSignedSelectedIncrease k n s| ≤
        2 * (s : ℝ) * ((n - s : ℕ) : ℝ) := by
    rw [abs_of_nonneg hK, abs_of_nonneg hL]
    nlinarith
  have hlambda := criticalDensityMargin_pos hk
  have hscale : 0 ≤ |d - pK k| / criticalDensityMargin k :=
    div_nonneg (abs_nonneg _) hlambda.le
  have hcoeffScaled := mul_le_mul_of_nonneg_right hcoeff hscale
  have hcoeffScaled' :
      (|criticalSignedCapacityLoss k n s| +
          2 * |criticalSignedSelectedIncrease k n s|) *
          |d - pK k| / criticalDensityMargin k ≤
        (2 * (s : ℝ) * ((n - s : ℕ) : ℝ)) *
          |d - pK k| / criticalDensityMargin k := by
    calc
      (|criticalSignedCapacityLoss k n s| +
          2 * |criticalSignedSelectedIncrease k n s|) *
          |d - pK k| / criticalDensityMargin k =
        (|criticalSignedCapacityLoss k n s| +
          2 * |criticalSignedSelectedIncrease k n s|) *
            (|d - pK k| / criticalDensityMargin k) := by ring
      _ ≤ (2 * (s : ℝ) * ((n - s : ℕ) : ℝ)) *
          (|d - pK k| / criticalDensityMargin k) := hcoeffScaled
      _ = _ := by ring
  unfold criticalFirstOrderResidueBound
  linarith

/-- Fully finite form of the critical first-order cancellation: the exact
balanced density incurs only an explicit linear error in `s`. -/
theorem criticalFirstOrderAtTargetDensity_le
    {k n s : ℕ} (hk : 3 ≤ k) (hs : s ≤ n)
    (hn : 4 * (k - 1) ≤ n)
    (hfeasible :
      DenseGraph.balancedMultipartiteInternalCapacity (k - 1) n ≤
        criticalEdgeCount k n)
    (hmargin : 8 / (n : ℝ) ≤ criticalDensityMargin k)
    (hK : 0 ≤ criticalSignedCapacityLoss k n s)
    (hL : 0 ≤ criticalSignedSelectedIncrease k n s) :
    criticalFirstOrderAtDensityExponent k n s
        (criticalBalancedSelectedDensity k n) ≤
      (s : ℝ) ^ 2 / 2 * Real.log (1 / (1 - pK k)) +
        criticalFirstOrderResidueBound k +
        (16 / criticalDensityMargin k) * (s : ℝ) := by
  have hd := criticalBalancedSelectedDensity_mem_compact
    hk hn hfeasible hmargin
  have hbase := criticalFirstOrderAtDensityExponent_le hk hs hK hL hd
  have herr := criticalBalancedSelectedDensity_error_le hk hn hfeasible
  have hnNat : 0 < n := by omega
  have hnPos : (0 : ℝ) < n := by exact_mod_cast hnNat
  have hlambda := criticalDensityMargin_pos hk
  have hq : ((n - s : ℕ) : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast Nat.sub_le n s
  have hs0 : (0 : ℝ) ≤ s := by positivity
  have hq0 : (0 : ℝ) ≤ (n - s : ℕ) := by positivity
  have hpert :
      (2 * (s : ℝ) * ((n - s : ℕ) : ℝ)) *
          |criticalBalancedSelectedDensity k n - pK k| /
            criticalDensityMargin k ≤
        (16 / criticalDensityMargin k) * (s : ℝ) := by
    calc
      (2 * (s : ℝ) * ((n - s : ℕ) : ℝ)) *
          |criticalBalancedSelectedDensity k n - pK k| /
            criticalDensityMargin k ≤
        (2 * (s : ℝ) * (n : ℝ)) * (8 / (n : ℝ)) /
            criticalDensityMargin k := by
          gcongr
      _ = (16 / criticalDensityMargin k) * (s : ℝ) := by
        field_simp
        ring
  linarith

theorem criticalSecondOrderCubicConstant_pos
    {k : ℕ} (hk : 3 ≤ k) :
    0 < criticalSecondOrderCubicConstant k := by
  have hlambda := criticalDensityMargin_pos hk
  unfold criticalSecondOrderCubicConstant
  positivity

theorem criticalTaylorDeltaBound_pos
    {k : ℕ} (hk : 3 ≤ k) :
    0 < criticalTaylorDeltaBound k := by
  unfold criticalTaylorDeltaBound
  exact lt_min (by norm_num)
    (lt_min
      (div_pos (criticalDensityMargin_pos hk) (by norm_num))
      (div_pos (criticalSparseQuadraticGap_pos hk)
        (mul_pos (by norm_num) (criticalSecondOrderCubicConstant_pos hk))))

theorem criticalCombinedSliceDelta_pos
    {k : ℕ} (hk : 3 ≤ k) :
    0 < criticalCombinedSliceDelta k := by
  exact lt_min (criticalTaylorDeltaBound_pos hk)
    (div_pos (criticalQuadraticContinuityRadius_pos hk) (by norm_num))

theorem criticalCombinedSliceDelta_le_taylor (k : ℕ) :
    criticalCombinedSliceDelta k ≤ criticalTaylorDeltaBound k :=
  min_le_left _ _

theorem criticalCombinedSliceDelta_le_continuity (k : ℕ) :
    criticalCombinedSliceDelta k ≤
      criticalQuadraticContinuityRadius k / 16 :=
  min_le_right _ _

theorem criticalTaylorDeltaBound_le_one_sixteenth (k : ℕ) :
    criticalTaylorDeltaBound k ≤ (1 / 16 : ℝ) := by
  exact min_le_left _ _

theorem criticalTaylorDeltaBound_le_densityMargin_div (k : ℕ) :
    criticalTaylorDeltaBound k ≤ criticalDensityMargin k / 16 := by
  exact (min_le_right _ _).trans (min_le_left _ _)

theorem criticalTaylorDeltaBound_cubic_control
    {k : ℕ} (hk : 3 ≤ k) :
    512 * criticalSecondOrderCubicConstant k *
        criticalTaylorDeltaBound k ≤
      criticalSparseQuadraticGap k := by
  have hdelta :
      criticalTaylorDeltaBound k ≤
        criticalSparseQuadraticGap k /
          (512 * criticalSecondOrderCubicConstant k) :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hden : 0 < 512 * criticalSecondOrderCubicConstant k :=
    mul_pos (by norm_num) (criticalSecondOrderCubicConstant_pos hk)
  have hmul := (le_div_iff₀ hden).mp hdelta
  nlinarith

/-! ## Canonical error constants for aggregation -/

/-- A single nonnegative constant, depending only on `k`, which absorbs the
finite quotient/remainder contribution, the exact-density first-order error,
and the logarithmic entropy-sandwich loss in the clean critical slice. -/
noncomputable def criticalCombinedSliceErrorConstant (k : ℕ) : ℝ :=
  |criticalFirstOrderResidueBound k| +
    16 / criticalDensityMargin k + 2

theorem criticalCombinedSliceErrorConstant_nonneg (k : ℕ) :
    0 ≤ criticalCombinedSliceErrorConstant k := by
  have hp := pK_mem_Icc k
  have hmargin : 0 ≤ criticalDensityMargin k := by
    unfold criticalDensityMargin
    exact div_nonneg (le_min hp.1 (sub_nonneg.mpr hp.2)) (by norm_num)
  unfold criticalCombinedSliceErrorConstant
  exact add_nonneg (add_nonneg (abs_nonneg _)
    (div_nonneg (by norm_num) hmargin)) (by norm_num)

/-- The compact-band adjacent-binomial-ratio constant used for signed
selected-count shifts. -/
noncomputable def criticalShiftErrorConstant (k : ℕ) : ℝ :=
  DenseGraph.binomialCompactBandShiftConstant (criticalDensityMargin k)

theorem criticalDensityMargin_lt_half
    {k : ℕ} (hk : 3 ≤ k) :
    criticalDensityMargin k < 1 / 2 := by
  have hp := pK_lt_one (k := k) (by omega : 2 ≤ k)
  have hle := criticalDensityMargin_le_pK_div_four k
  linarith

theorem criticalShiftErrorConstant_pos
    {k : ℕ} (hk : 3 ≤ k) :
    0 < criticalShiftErrorConstant k := by
  exact DenseGraph.binomialCompactBandShiftConstant_pos
    (criticalDensityMargin_pos hk) (criticalDensityMargin_lt_half hk)

end InducedStars
