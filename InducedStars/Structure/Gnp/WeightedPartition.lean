import InducedStars.Structure.Subcritical.RetainedKeyCounts
import InducedStars.Structure.Gnp.RetainedCapacity

/-!
# Weighted retained-key partition functions

The common ambient factor is always `(1-p)^choose(n,2)`, including for the
sparse-side term. Sums are indexed by actual retained keys, not by
decorations of their complement. Exact edge levels are summed before any
estimate; no truncated subtraction is used to identify an edge level.
-/

noncomputable section
open Finset
open scoped Classical BigOperators
namespace InducedStars

variable {k n : ℕ}

/-- The permitted count band on one retained active block. -/
def retainedKeyWeightedBand (K : SubcriticalRetainedKey k (Fin n))
    (delta : ℝ) (e : K.ActiveIndex) : Finset (Fin (K.activeCapacity e + 1)) :=
  univ.filter fun a ↦ pK k - 2 * delta ≤ (a.val : ℝ) / K.activeCapacity e ∧
    (a.val : ℝ) / K.activeCapacity e ≤ pK k + 2 * delta

/-- The actual product of band-restricted binomial generating functions. -/
def retainedKeyWeightedActiveProduct (K : SubcriticalRetainedKey k (Fin n))
    (delta z : ℝ) : ℝ :=
  ∏ e, ∑ a ∈ retainedKeyWeightedBand K delta e,
    (Nat.choose (K.activeCapacity e) a.val : ℝ) * z ^ a.val

/-- Sparse induced-free graph sum, keeping the full ambient empty-graph weight. -/
def retainedKeyWeightedSparseSum (K : SubcriticalRetainedKey k (Fin n))
    (eta p : ℝ) : ℝ :=
  (1 - p) ^ completeEdgeCount n *
    ∑ b ∈ range (Nat.floor (subcriticalSparseSideConstant k * eta * (n : ℝ)^2) + 1),
      (inducedStarFreeGraphCountWithEdges k K.remainder.card b : ℝ) *
        (p / (1 - p)) ^ b

/-- The weighted clean partition function from the critical `G(n,p)` proof. -/
def retainedKeyWeightedCleanPartitionFunction
    (K : SubcriticalRetainedKey k (Fin n)) (eta delta p : ℝ) : ℝ :=
  (1 - p) ^ completeEdgeCount n *
    ∑ b ∈ range (Nat.floor (subcriticalSparseSideConstant k * eta * (n : ℝ)^2) + 1),
      (inducedStarFreeGraphCountWithEdges k K.remainder.card b : ℝ) *
        (p / (1 - p)) ^ (K.cliqueCapacity + b) *
        retainedKeyWeightedActiveProduct K delta (p / (1 - p))

theorem retainedKeyWeightedActiveProduct_nonneg
    (K : SubcriticalRetainedKey k (Fin n)) (delta : ℝ) {z : ℝ} (hz : 0 ≤ z) :
    0 ≤ retainedKeyWeightedActiveProduct K delta z := by
  unfold retainedKeyWeightedActiveProduct
  exact prod_nonneg fun _ _ ↦ sum_nonneg fun _ _ ↦ by positivity

theorem retainedKeyWeightedActiveProduct_le
    (K : SubcriticalRetainedKey k (Fin n)) (delta : ℝ) {z : ℝ} (hz : 0 ≤ z) :
    retainedKeyWeightedActiveProduct K delta z ≤
      (1 + z) ^ (∑ e, K.activeCapacity e) := by
  unfold retainedKeyWeightedActiveProduct
  rw [← prod_pow_eq_pow_sum]
  apply prod_le_prod
  · intro e _
    exact sum_nonneg fun _ _ ↦ by positivity
  · intro e _
    calc
      _ ≤ ∑ a : Fin (K.activeCapacity e + 1),
          (Nat.choose (K.activeCapacity e) a.val : ℝ) * z ^ a.val :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ ↦ by positivity)
      _ = (1 + z) ^ K.activeCapacity e := by
        rw [Fin.sum_univ_eq_sum_range (fun a ↦
          (Nat.choose (K.activeCapacity e) a : ℝ) * z ^ a), add_comm (1 : ℝ) z, add_pow]
        apply sum_congr rfl
        intro a _
        simp [mul_comm]

theorem retainedKeyWeightedActiveProduct_eq_sum
    (K : SubcriticalRetainedKey k (Fin n)) (delta z : ℝ) :
    retainedKeyWeightedActiveProduct K delta z =
      ∑ v ∈ Fintype.piFinset (retainedKeyWeightedBand K delta),
        (retainedKeyEdgeCountMultiplicity v : ℝ) * z ^ retainedKeyEdgeCountTotal v := by
  rw [retainedKeyWeightedActiveProduct, prod_univ_sum]
  apply sum_congr rfl
  intro v _
  simp only [retainedKeyEdgeCountMultiplicity, retainedKeyEdgeCountTotal,
    Nat.cast_prod, prod_mul_distrib, prod_pow_eq_pow_sum]

/-- Summing any finite set of exact levels is bounded by the unrestricted
weighted retained sum. This also handles empty and infeasible slices. -/
theorem sum_retainedKeyPartitionFunction_mul_pow_le
    (K : SubcriticalRetainedKey k (Fin n)) (delta : ℝ) (b : ℕ)
    (ms : Finset ℕ) {z : ℝ} (hz : 0 ≤ z) :
    ∑ m ∈ ms, (retainedKeyPartitionFunction K m delta (b : ℤ) : ℝ) * z ^ m ≤
      z ^ (K.cliqueCapacity + b) * retainedKeyWeightedActiveProduct K delta z := by
  let vs := Fintype.piFinset (retainedKeyWeightedBand K delta)
  let total (v : RetainedKeyEdgeCountVector K) :=
    K.cliqueCapacity + retainedKeyEdgeCountTotal v + b
  have hlevel (m : ℕ) : retainedKeyEdgeCountLevel K m delta (b : ℤ) =
      vs.filter (fun v ↦ total v = m) := by
    ext v
    constructor
    · intro hv
      have hh := (Finset.mem_filter.mp hv).2
      apply Finset.mem_filter.mpr
      refine ⟨Fintype.mem_piFinset.mpr (fun e ↦ ?_), ?_⟩
      · exact Finset.mem_filter.mpr ⟨mem_univ _, hh.2 e⟩
      · dsimp [total]
        exact_mod_cast hh.1
    · intro hv
      have hh := Finset.mem_filter.mp hv
      apply Finset.mem_filter.mpr
      refine ⟨mem_univ _, ?_, ?_⟩
      · have hm := hh.2
        dsimp [total] at hm
        exact_mod_cast hm
      · intro e
        exact (Finset.mem_filter.mp (Fintype.mem_piFinset.mp hh.1 e)).2
  have hrewrite (m : ℕ) :
      (retainedKeyPartitionFunction K m delta (b : ℤ) : ℝ) * z ^ m =
        ∑ v ∈ vs.filter (fun v ↦ total v = m),
          (retainedKeyEdgeCountMultiplicity v : ℝ) * z ^ total v := by
    simp only [retainedKeyPartitionFunction, Nat.cast_sum, hlevel, sum_mul]
    exact sum_congr rfl fun v hv ↦ by rw [(mem_filter.mp hv).2]
  simp_rw [hrewrite]
  calc
    _ ≤ ∑ v ∈ vs, (retainedKeyEdgeCountMultiplicity v : ℝ) * z ^ total v := by
      apply sum_fiberwise_le_sum_of_sum_fiber_nonneg
      intro _ _
      exact sum_nonneg fun _ _ ↦ by positivity
    _ = z ^ (K.cliqueCapacity + b) * retainedKeyWeightedActiveProduct K delta z := by
      rw [retainedKeyWeightedActiveProduct_eq_sum, mul_sum]
      apply sum_congr rfl
      intro v _
      dsimp [total]
      rw [show K.cliqueCapacity + retainedKeyEdgeCountTotal v + b =
        (K.cliqueCapacity + b) + retainedKeyEdgeCountTotal v by omega, pow_add]
      ring

/-- The fixed-count clean sums can be summed with their actual `G(n,p)`
weights, without replacing the common ambient factor by the sparse one. -/
theorem sum_retainedKeyCleanPartitionFunction_weight_le
    (K : SubcriticalRetainedKey k (Fin n)) (eta delta : ℝ)
    (ms : Finset ℕ) {p : ℝ} (hp : p ∈ Set.Icc (0 : ℝ) 1) :
    ∑ m ∈ ms, (1 - p) ^ completeEdgeCount n * (p / (1 - p)) ^ m *
      (retainedKeyCleanPartitionFunction K eta m delta : ℝ) ≤
        retainedKeyWeightedCleanPartitionFunction K eta delta p := by
  let z := p / (1 - p)
  have hz : 0 ≤ z := div_nonneg hp.1 (sub_nonneg.mpr hp.2)
  have hamb : 0 ≤ (1 - p) ^ completeEdgeCount n := pow_nonneg (sub_nonneg.mpr hp.2) _
  simp only [retainedKeyCleanPartitionFunction, Fintype.card_fin, Nat.cast_sum,
    Nat.cast_mul, mul_sum, retainedKeyWeightedCleanPartitionFunction]
  simp_rw [mul_assoc, ← mul_sum]
  apply mul_le_mul_of_nonneg_left _ hamb
  simp only [mul_sum]
  rw [sum_comm]
  apply sum_le_sum
  intro b _
  calc
    _ = (inducedStarFreeGraphCountWithEdges k K.remainder.card b : ℝ) *
        ∑ m ∈ ms, (retainedKeyPartitionFunction K m delta (b : ℤ) : ℝ) * z ^ m := by
      rw [mul_sum]
      apply sum_congr rfl
      intro m _
      dsimp [z]
      ring
    _ ≤ (inducedStarFreeGraphCountWithEdges k K.remainder.card b : ℝ) *
        (z ^ (K.cliqueCapacity + b) * retainedKeyWeightedActiveProduct K delta z) :=
      mul_le_mul_of_nonneg_left (sum_retainedKeyPartitionFunction_mul_pow_le K delta b ms hz)
        (Nat.cast_nonneg _)
    _ = _ := by dsimp [z]

/-- Critical odds cancellation, in natural logarithms. -/
theorem criticalRetainedOdds_log (k : ℕ) (hk : 3 ≤ k) :
    Real.log (pK k / (1 - pK k)) = (k - 2 : ℕ) * Real.log (1 - pK k) := by
  rw [Real.log_div (pK_pos (by omega)).ne'
    (sub_pos.mpr (pK_lt_one (by omega))).ne', log_pK_eq]
  have h : ((k - 1 : ℕ) : ℝ) = (k - 2 : ℕ) + 1 := by
    exact_mod_cast (show k - 1 = (k - 2) + 1 by omega)
  rw [h]
  ring

/-- The regular-core capacity bound cancels the quadratic retained weight.
The hypothesis is a finite algebraic capacity inequality, proved separately
from regularity of the actual retained cores. -/
theorem criticalRetainedFactor_le_exp_of_capacity
    (k : ℕ) (hk : 3 ≤ k) (C A v : ℕ)
    (hcap : (A : ℝ) ≤ (k - 2 : ℕ) * C + (k - 2 : ℕ) * v / 2) :
    (pK k / (1 - pK k)) ^ C * (1 + pK k / (1 - pK k)) ^ A ≤
      Real.exp (-((k - 2 : ℕ) : ℝ) * Real.log (1 - pK k) / 2 * v) := by
  have hp : 0 < pK k := pK_pos (by omega)
  have hq : 0 < 1 - pK k := sub_pos.mpr (pK_lt_one (by omega))
  have hz : 0 < pK k / (1 - pK k) := div_pos hp hq
  have hsum : 1 + pK k / (1 - pK k) = (1 - pK k)⁻¹ := by
    field_simp
    ring
  apply (Real.log_le_iff_le_exp (mul_pos (pow_pos hz _) (pow_pos (by linarith) _))).mp
  rw [Real.log_mul (pow_pos hz _).ne' (pow_pos (by linarith) _).ne',
    Real.log_pow, Real.log_pow, criticalRetainedOdds_log k hk, hsum, Real.log_inv]
  have hlog : Real.log (1 - pK k) ≤ 0 := Real.log_nonpos hq.le (by linarith)
  have h := mul_le_mul_of_nonpos_right hcap hlog
  nlinarith

theorem retainedKeyWeightedCleanPartitionFunction_factor
    (K : SubcriticalRetainedKey k (Fin n)) (eta delta p : ℝ) :
    retainedKeyWeightedCleanPartitionFunction K eta delta p =
      ((p / (1 - p)) ^ K.cliqueCapacity *
        retainedKeyWeightedActiveProduct K delta (p / (1 - p))) *
      retainedKeyWeightedSparseSum K eta p := by
  unfold retainedKeyWeightedCleanPartitionFunction retainedKeyWeightedSparseSum
  simp_rw [pow_add]
  rw [mul_left_comm]
  simp only [mul_sum]
  apply sum_congr rfl
  intro b _
  ring

theorem retainedKeyWeightedCleanPartitionFunction_le_sparse_of_capacity
    (K : SubcriticalRetainedKey k (Fin n)) (hk : 3 ≤ k) (eta delta : ℝ)
    (hcap : (∑ e, K.activeCapacity e : ℕ) ≤
      ((k - 2 : ℕ) : ℝ) * K.cliqueCapacity +
        (k - 2 : ℕ) * K.support.card / 2) :
    retainedKeyWeightedCleanPartitionFunction K eta delta (pK k) ≤
      Real.exp (-((k - 2 : ℕ) : ℝ) * Real.log (1 - pK k) / 2 *
        K.support.card) * retainedKeyWeightedSparseSum K eta (pK k) := by
  have hp := pK_mem_Ioo (show 2 ≤ k by omega)
  have hz : 0 ≤ pK k / (1 - pK k) := div_nonneg hp.1.le (sub_nonneg.mpr hp.2.le)
  rw [retainedKeyWeightedCleanPartitionFunction_factor]
  apply mul_le_mul_of_nonneg_right _
    (show 0 ≤ retainedKeyWeightedSparseSum K eta (pK k) from by
      unfold retainedKeyWeightedSparseSum
      apply mul_nonneg (pow_nonneg (sub_nonneg.mpr hp.2.le) _)
      exact sum_nonneg fun _ _ ↦ mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hz _))
  exact (mul_le_mul_of_nonneg_left
    (retainedKeyWeightedActiveProduct_le K delta hz) (pow_nonneg hz _)).trans
    (criticalRetainedFactor_le_exp_of_capacity k hk _ _ _ hcap)

/-- The explicit linear loss in the retained contribution at critical odds. -/
def criticalRetainedWeightConstant (k : ℕ) : ℝ :=
  -((k - 2 : ℕ) : ℝ) * Real.log (1 - pK k) / 2

theorem criticalRetainedWeightConstant_pos (k : ℕ) (hk : 3 ≤ k) :
    0 < criticalRetainedWeightConstant k := by
  have hd : (0 : ℝ) < (k - 2 : ℕ) := by exact_mod_cast (show 0 < k - 2 by omega)
  have hlog : Real.log (1 - pK k) < 0 :=
    Real.log_neg (sub_pos.mpr (pK_lt_one (by omega)))
      (by linarith [pK_pos (k := k) (by omega)])
  unfold criticalRetainedWeightConstant
  nlinarith [mul_pos hd (neg_pos.mpr hlog)]

/-- Paper: `eqn:critical-clean-sparse-side-K1k`. Actual regular retained cores
give the capacity estimate; no capacity or counting conclusion is assumed. -/
theorem retainedKeyWeightedCleanPartitionFunction_le_sparse
    (K : SubcriticalRetainedKey k (Fin n)) (hk : 3 ≤ k) (eta delta : ℝ) :
    retainedKeyWeightedCleanPartitionFunction K eta delta (pK k) ≤
      Real.exp (criticalRetainedWeightConstant k * n) *
        retainedKeyWeightedSparseSum K eta (pK k) := by
  have hcap := retainedKey_activeCapacity_le_cliqueCapacity_add_linear K
  have hcap' : ((∑ e, K.activeCapacity e : ℕ) : ℝ) ≤
      ((k - 2 : ℕ) : ℝ) * K.cliqueCapacity +
        (k - 2 : ℕ) * K.support.card / 2 := by
    simpa only [Nat.cast_sum, div_mul_eq_mul_div] using hcap
  apply (retainedKeyWeightedCleanPartitionFunction_le_sparse_of_capacity
    K hk eta delta hcap').trans
  apply mul_le_mul_of_nonneg_right
  · apply Real.exp_le_exp.mpr
    change criticalRetainedWeightConstant k * (K.support.card : ℝ) ≤ _
    apply mul_le_mul_of_nonneg_left _ (criticalRetainedWeightConstant_pos k hk).le
    exact_mod_cast (show K.support.card ≤ n from by
      simpa using K.support.card_le_univ)
  · have hp := pK_mem_Ioo (show 2 ≤ k by omega)
    have hz : 0 ≤ pK k / (1 - pK k) :=
      div_nonneg hp.1.le (sub_nonneg.mpr hp.2.le)
    unfold retainedKeyWeightedSparseSum
    exact mul_nonneg (pow_nonneg (sub_nonneg.mpr hp.2.le) _)
      (sum_nonneg fun _ _ ↦ mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hz _))

end InducedStars
