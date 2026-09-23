import InducedStars.Structure.Critical.WindowScales
import InducedStars.Main.AsymptoticConsequences

/-!
# The critical remainder partition function

The critical binomial rate theorem implies that the weighted number of
induced-star-free remainder graphs has subquadratic logarithm.  This uses
the actual induced-free finite graph counts, summed over every edge count.
-/

noncomputable section

open Filter Set Topology
open scoped BigOperators

namespace InducedStars

/-- The weighted number of possible induced-star-free remainder graphs. -/
def criticalRemainderPartitionFunction (k s : ℕ) : ℝ :=
  ∑ t ∈ Finset.range (completeEdgeCount s + 1),
    (inducedFreeGraphCountWithEdges (inducedStar k) s t : ℝ) *
      (pK k / (1 - pK k)) ^ t

/-- Exact probability/partition-function identity, before taking logarithms. -/
theorem criticalRemainderPartitionFunction_probability
    {k : ℕ} (hk : 3 ≤ k) (s : ℕ) :
    gnpInducedStarFreeProbability k s (pK k) =
      (1 - pK k) ^ completeEdgeCount s * criticalRemainderPartitionFunction k s := by
  have hq : 1 - pK k ≠ 0 := (sub_pos.mpr (pK_lt_one (by omega))).ne'
  rw [gnpInducedStarFreeProbability, gnpInducedFreeProbability_eq_sum_edgeCounts, criticalRemainderPartitionFunction,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t ht
  have htN : t ≤ completeEdgeCount s := by have h := Finset.mem_range.mp ht; omega
  unfold gnpInducedFreeSliceWeight
  rw [div_pow, pow_sub₀ (1 - pK k) hq htN]
  field_simp

/-- The partition function is positive at every order. -/
theorem criticalRemainderPartitionFunction_pos
    {k : ℕ} (hk : 3 ≤ k) (s : ℕ) :
    0 < criticalRemainderPartitionFunction k s := by
  have hp : pK k ∈ Ioo (0 : ℝ) 1 := ⟨pK_pos (by omega), pK_lt_one (by omega)⟩
  have h := gnpInducedStarFreeProbability_pos (n := s) (by omega : 1 ≤ k) hp
  rw [criticalRemainderPartitionFunction_probability hk] at h
  exact (mul_pos_iff_of_pos_left (pow_pos (sub_pos.mpr hp.2) _)).mp h

/-- Exact logarithmic form of the partition-function identity. -/
theorem log_criticalRemainderPartitionFunction
    {k : ℕ} (hk : 3 ≤ k) (s : ℕ) :
    Real.log (criticalRemainderPartitionFunction k s) =
      Real.log (gnpInducedStarFreeProbability k s (pK k)) -
        (completeEdgeCount s : ℝ) * Real.log (1 - pK k) := by
  have hq : 1 - pK k ≠ 0 := (sub_pos.mpr (pK_lt_one (by omega))).ne'
  rw [criticalRemainderPartitionFunction_probability hk,
    Real.log_mul (pow_ne_zero _ hq) (criticalRemainderPartitionFunction_pos hk s).ne',
    Real.log_pow]
  ring

/-- The rate theorem at `pK k`, stated in natural logarithms. -/
theorem criticalGnpLogProbability_per_pair_tendsto
    {k : ℕ} (hk : 3 ≤ k) :
    Tendsto (fun s ↦ Real.log (gnpInducedStarFreeProbability k s (pK k)) /
      (completeEdgeCount s : ℝ)) atTop (𝓝 (Real.log (1 - pK k))) := by
  have hp : pK k ∈ Ioo (0 : ℝ) 1 := ⟨pK_pos (by omega), pK_lt_one (by omega)⟩
  have h := (inducedStarGnpLargeDeviationRate k hk (pK k) hp).mul_const (Real.log 2)
  rw [rateFunction_at_pK_eq_neg_log2_one_sub, neg_neg] at h
  convert h using 1
  · ext s
    simp only [normalizedLogProbability, normalizedLogAtGraphOrder, log2]
    field_simp [realLogTwo_ne_zero]
  · unfold log2
    field_simp [realLogTwo_ne_zero]

/-- The weighted remainder count has natural logarithm `o(s²)`. Dividing
by `Real.log 2` gives the paper's `eqn:critical-remainder-partition`. -/
theorem criticalRemainderPartitionFunction_log_sq_tendsto_zero
    {k : ℕ} (hk : 3 ≤ k) :
    Tendsto (fun s ↦ Real.log (criticalRemainderPartitionFunction k s) / (s : ℝ) ^ 2)
      atTop (𝓝 0) := by
  have hpair : Tendsto (fun s ↦ (completeEdgeCount s : ℝ) / (s : ℝ) ^ 2)
      atTop (𝓝 (1 / 2 : ℝ)) := by
    convert completeEdgeCount_orderedSquareFactor_tendsto_one.div_const 2 using 1 <;>
      simp only [div_div]
    ext s
    ring
  have hprob := (criticalGnpLogProbability_per_pair_tendsto hk).mul hpair
  have hprob' : Tendsto (fun s ↦ Real.log (gnpInducedStarFreeProbability k s (pK k)) /
      (s : ℝ) ^ 2) atTop (𝓝 (Real.log (1 - pK k) * (1 / 2))) := by
    apply hprob.congr'
    filter_upwards [tendsto_completeEdgeCount_cast_atTop.eventually (eventually_gt_atTop 0)]
      with s hs
    field_simp
  have h := hprob'.sub ((tendsto_const_nhds (x := Real.log (1 - pK k))).mul hpair)
  convert h using 1
  · ext s
    rw [log_criticalRemainderPartitionFunction hk]
    ring
  · ring

/-- The weighted remainder count stays negligible on the squared-logarithm
scale for every bounded logarithmic remainder-size sequence. -/
theorem criticalRemainderPartitionFunction_log_logSq_tendsto_zero
    {k : ℕ} (hk : 3 ≤ k) {s : ℕ → ℕ} {x : ℝ}
    (hs : Tendsto (fun n ↦ (s n : ℝ) / Real.log (n : ℝ)) atTop (𝓝 x)) :
    Tendsto (fun n ↦ Real.log (criticalRemainderPartitionFunction k (s n)) /
      Real.log (n : ℝ) ^ 2) atTop (𝓝 0) :=
  subquadratic_comp_logarithmicScale_tendsto_zero
    (criticalRemainderPartitionFunction_log_sq_tendsto_zero hk) hs

end InducedStars
