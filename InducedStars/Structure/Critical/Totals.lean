import InducedStars.Structure.Critical.DivisionBounds
import InducedStars.Structure.Critical.Families
import InducedStars.Structure.Critical.GaussianSums

/-!
# Global counts at the exact critical density

The uniform division estimates are summed over their actual finite families.
Sparse-vertex choices cost at most exp(s log(n+1)); the full ordered-division
factor is compared with the actual co-partite denominator.
-/

noncomputable section
open Filter Finset Set
open scoped BigOperators Topology Classical
namespace InducedStars

/-- Choosing sparse vertices contributes at most one s log(n+1) term. -/
theorem choose_mul_criticalRemainderExponent_le
    (k n s : ℕ) (C : ℝ) :
    (Nat.choose n s : ℝ) * Real.exp (criticalRemainderExponent k C n s) ≤
      criticalRemainderSeriesTerm (criticalSparsePenaltyConstant k) C n s := by
  have hchoose : (Nat.choose n s : ℝ) ≤
      Real.exp ((s : ℝ) * Real.log ((n + 1 : ℕ) : ℝ)) := by
    rw [Real.exp_nat_mul, Real.exp_log (by positivity : (0 : ℝ) < ((n + 1 : ℕ) : ℝ))]
    exact_mod_cast (Nat.choose_le_pow n s).trans (Nat.pow_le_pow_left (by omega) s)
  calc
    _ ≤ Real.exp ((s : ℝ) * Real.log ((n + 1 : ℕ) : ℝ)) *
        Real.exp (criticalRemainderExponent k C n s) :=
      mul_le_mul_of_nonneg_right hchoose (Real.exp_pos _).le
    _ = _ := by
      rw [← Real.exp_add]
      unfold criticalRemainderExponent criticalRemainderSeriesTerm
      congr 1
      ring

/-- Real-valued sum of the paper's Q_s over the small-remainder range. -/
def criticalRemainderCompletionSum (k : ℕ) (xi : ℝ) (n : ℕ) : ℝ :=
  ∑ s ∈ (Finset.range (n + 1)).filter (fun s : ℕ ↦ (s : ℝ) ≤ xi * n),
    (criticalRemainderCompletionCount k n s : ℝ)

/-- The Q_s tail with the paper's base-two logarithmic cutoff. -/
def criticalRemainderCompletionTail (k : ℕ) (xi L : ℝ) (n : ℕ) : ℝ :=
  ∑ s ∈ (Finset.range (n + 1)).filter
    (fun s : ℕ ↦ L * Real.logb 2 (n : ℝ) ≤ (s : ℝ) ∧ (s : ℝ) ≤ xi * n),
    (criticalRemainderCompletionCount k n s : ℝ)

/-- On the eventual range used by the paper, the forced-edge guard is
always satisfied. Thus the total definition agrees with the displayed Q_s,
including its unguarded binomial coefficient. -/
theorem eventually_criticalRemainderCompletionCount_eq
    (k : ℕ) (hk : 3 ≤ k) :
    ∀ᶠ n : ℕ in atTop, ∀ s : ℕ,
      (s : ℝ) ≤ criticalCombinedSliceDelta k * n →
      criticalRemainderCompletionCount k n s =
        Nat.choose n s * (k - 1)^(n - s) *
          Nat.choose (criticalMaximumCombinedCapacity k n s)
            (criticalEdgeCount k n -
              DenseGraph.balancedMultipartiteInternalCapacity (k - 1) (n - s)) := by
  filter_upwards [eventually_balancedInternalCapacity_le_criticalEdgeCount k hk,
    eventually_ge_atTop (4 * (k - 1)^2)] with n hfeas hn
  intro s hs
  have hsmall : 16 * s ≤ n := by
    have h := hs.trans (mul_le_mul_of_nonneg_right
      (criticalCombinedSliceDelta_le_one_sixteenth k) (Nat.cast_nonneg n))
    exact_mod_cast (show (16 : ℝ) * s ≤ n by linarith)
  have hmono : DenseGraph.balancedMultipartiteInternalCapacity (k - 1) (n - s) ≤
      DenseGraph.balancedMultipartiteInternalCapacity (k - 1) n := by
    by_cases hz : s = 0
    · simp [hz]
    · exact criticalBalancedInternalCapacity_mono_sparse hk (by omega) hsmall hn
  simp only [criticalRemainderCompletionCount, ite_eq_left (hmono.trans hfeas)]

/-- Summing Q_s over any part of the permitted range is bounded by the
corresponding polynomially weighted Gaussian series. -/
theorem eventually_criticalCompletionSum_le
    (k : ℕ) (hk : 3 ≤ k) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      ∀ (S : Finset ℕ),
        (∀ s ∈ S, (s : ℝ) ≤ criticalCombinedSliceDelta k * n) →
        (∑ s ∈ S, (criticalRemainderCompletionCount k n s : ℝ)) ≤
          (coMultipartiteGraphCountWithEdges (k - 1) n (criticalEdgeCount k n) : ℝ) *
            ((n + 1 : ℕ) : ℝ)^(k - 1) * ((2 * (k - 1).factorial : ℕ) : ℝ) *
              ∑ s ∈ S, criticalRemainderSeriesTerm (criticalSparsePenaltyConstant k) C n s := by
  obtain ⟨C, hC, hslice⟩ := eventually_criticalCombinedSlice_le_reference k hk
  refine ⟨C, hC, ?_⟩
  filter_upwards [hslice, eventually_criticalCoMultipartiteCount_lower k hk,
    eventually_balancedInternalCapacity_le_criticalEdgeCount k hk,
    eventually_ge_atTop (4 * (k - 1)^2)] with n hslices href hfeas hn
  intro S hS
  let J : ℝ := ((n + 1 : ℕ) : ℝ)^(k - 1) * ((2 * (k - 1).factorial : ℕ) : ℝ)
  let Co : ℝ := coMultipartiteGraphCountWithEdges (k - 1) n (criticalEdgeCount k n)
  have hterm (s : ℕ) (hs : s ∈ S) :
      (criticalRemainderCompletionCount k n s : ℝ) ≤
        Co * J * criticalRemainderSeriesTerm (criticalSparsePenaltyConstant k) C n s := by
    have hbin := hslices s (hS s hs)
    change (Nat.choose (criticalMaximumCombinedCapacity k n s)
      (criticalTargetSelectedCount k n + criticalSelectedIncrease k n s) : ℝ) ≤
        (criticalReferenceFiberCard k n : ℝ) * Real.exp (criticalRemainderExponent k C n s)
      at hbin
    have hpow : (((k - 1 : ℕ) : ℝ)^(n - s)) ≤ ((k - 1 : ℕ) : ℝ)^n := by
      exact_mod_cast Nat.pow_le_pow_right (show 0 < k - 1 by omega) (Nat.sub_le n s)
    have hcoef : (0 : ℝ) ≤ (Nat.choose n s : ℝ) * ((k - 1 : ℕ) : ℝ)^(n - s) := by
      positivity
    have hmain : (Nat.choose n s : ℝ) * Real.exp (criticalRemainderExponent k C n s) ≤
        criticalRemainderSeriesTerm (criticalSparsePenaltyConstant k) C n s :=
      choose_mul_criticalRemainderExponent_le k n s C
    calc
      _ = (Nat.choose n s : ℝ) * ((k - 1 : ℕ) : ℝ)^(n - s) *
          (Nat.choose (criticalMaximumCombinedCapacity k n s)
            (criticalTargetSelectedCount k n + criticalSelectedIncrease k n s) : ℝ) := by
        rw [criticalRemainderCompletionCount, critical_balanced_reference_eq hk hn (hS s hs) hfeas]
        push_cast <;> rfl
      _ ≤ (Nat.choose n s : ℝ) * ((k - 1 : ℕ) : ℝ)^(n - s) *
          ((criticalReferenceFiberCard k n : ℝ) * Real.exp (criticalRemainderExponent k C n s)) :=
        mul_le_mul_of_nonneg_left hbin hcoef
      _ ≤ (Nat.choose n s : ℝ) * ((k - 1 : ℕ) : ℝ)^n *
          ((criticalReferenceFiberCard k n : ℝ) * Real.exp (criticalRemainderExponent k C n s)) := by
        gcongr
      _ = (((k - 1 : ℕ) : ℝ)^n * (criticalReferenceFiberCard k n : ℝ)) *
          ((Nat.choose n s : ℝ) * Real.exp (criticalRemainderExponent k C n s)) := by ring
      _ ≤ (J * Co) * criticalRemainderSeriesTerm (criticalSparsePenaltyConstant k) C n s :=
        mul_le_mul href hmain (by positivity) (by dsimp [J, Co]; positivity)
      _ = _ := by ring
  calc
    _ ≤ ∑ s ∈ S, Co * J *
        criticalRemainderSeriesTerm (criticalSparsePenaltyConstant k) C n s :=
      Finset.sum_le_sum hterm
    _ = _ := by rw [← Finset.mul_sum]; dsimp [Co, J]; ring

/-- Paper: lemma:critical-large-remainders. The Q_s tail is negligible
relative to the actual co-partite count, and the full small-remainder sum
has the paper's base-two quadratic-logarithmic bound. -/
theorem criticalLargeRemainders (k : ℕ) (hk : 3 ≤ k) :
    ∃ xi L C : ℝ, 0 < xi ∧ 0 < L ∧ 0 < C ∧
      Tendsto (fun n ↦ criticalRemainderCompletionTail k xi L n /
        (coMultipartiteGraphCountWithEdges (k - 1) n (criticalEdgeCount k n) : ℝ))
          atTop (𝓝 0) ∧
      ∀ᶠ n : ℕ in atTop,
        criticalRemainderCompletionSum k xi n ≤
          (2 : ℝ)^(C * (Real.logb 2 (n : ℝ))^2) *
            (coMultipartiteGraphCountWithEdges (k - 1) n (criticalEdgeCount k n) : ℝ) := by
  obtain ⟨A, hA, hsum⟩ := eventually_criticalCompletionSum_le k hk
  let c := criticalSparsePenaltyConstant k
  let K : ℝ := (2 * (k - 1).factorial : ℕ)
  have hc : 0 < c := criticalSparsePenaltyConstant_pos hk
  have hK : 0 < K := by dsimp [K]; positivity
  obtain ⟨B, hB, hfull⟩ := exists_eventually_criticalRemainderSeries_le hc hA (k - 1) hK
  obtain ⟨L, hL, htail⟩ := exists_eventually_criticalRemainderTail_le hc hA (k - 1) hK
  have hcoPos : ∀ᶠ n : ℕ in atTop,
      0 < coMultipartiteGraphCountWithEdges (k - 1) n (criticalEdgeCount k n) :=
    eventually_coMultipartiteGraphCountWithEdges_pos k hk (gammaK k)
      ⟨one_div_parts_lt_gammaK hk, gammaK_lt_one hk⟩
        (criticalEdgeCount k) (criticalEdgeCount_hasAsymptoticEdgeDensity hk)
  refine ⟨criticalCombinedSliceDelta k, 2 * L * Real.log 2, 4 * B * Real.log 2,
    criticalCombinedSliceDelta_pos hk, by positivity, by positivity, ?_, ?_⟩
  · apply squeeze_zero' (Eventually.of_forall fun n ↦ by
      dsimp [criticalRemainderCompletionTail]; positivity) ?_
        (criticalRemainderGaussian_tendsto_zero hc)
    filter_upwards [hsum, htail, hcoPos, eventually_ge_atTop 2] with n hsumN htailN hpos hn
    let S := (Finset.range (n + 1)).filter
      (fun s : ℕ ↦ (2 * L * Real.log 2) * Real.logb 2 (n : ℝ) ≤ (s : ℝ) ∧
        (s : ℝ) ≤ criticalCombinedSliceDelta k * n)
    let T := (Finset.range (n + 1)).filter
      (fun s : ℕ ↦ L * Real.log ((n + 1 : ℕ) : ℝ) ≤ (s : ℝ))
    have hST : S ⊆ T := by
      intro s hs
      obtain ⟨hsn, hlo, hhi⟩ := Finset.mem_filter.mp hs
      exact Finset.mem_filter.mpr ⟨hsn, (criticalLog_succ_mul_le_baseTwo hL.le hn).trans hlo⟩
    have hbound := hsumN S (fun s hs ↦ (Finset.mem_filter.mp hs).2.2)
    have hseries : (∑ s ∈ S, criticalRemainderSeriesTerm c A n s) ≤
        ∑ s ∈ T, criticalRemainderSeriesTerm c A n s :=
      Finset.sum_le_sum_of_subset_of_nonneg hST (fun _ _ _ ↦ (Real.exp_pos _).le)
    have hCo : (0 : ℝ) < coMultipartiteGraphCountWithEdges (k - 1) n (criticalEdgeCount k n) := by
      exact_mod_cast hpos
    apply (div_le_iff₀ hCo).mpr
    calc
      _ ≤ _ := hbound
      _ ≤ (coMultipartiteGraphCountWithEdges (k - 1) n (criticalEdgeCount k n) : ℝ) *
          criticalRemainderTail c A (k - 1) K L n := by
        dsimp [criticalRemainderTail]
        simpa only [mul_assoc, K, c, T, coMultipartiteGraphCountWithEdges] using
          mul_le_mul_of_nonneg_left hseries
          (show 0 ≤ (coMultipartiteGraphCountWithEdges (k - 1) n (criticalEdgeCount k n) : ℝ) *
            ((n + 1 : ℕ) : ℝ)^(k - 1) * K by positivity)
      _ ≤ _ := by
        simpa only [mul_comm] using mul_le_mul_of_nonneg_left htailN hCo.le
  · filter_upwards [hsum, hfull, eventually_ge_atTop 2] with n hsumN hfullN hn
    let S := (Finset.range (n + 1)).filter
      (fun s : ℕ ↦ (s : ℝ) ≤ criticalCombinedSliceDelta k * n)
    have hbound := hsumN S (fun s hs ↦ (Finset.mem_filter.mp hs).2)
    have hseries : (∑ s ∈ S, criticalRemainderSeriesTerm c A n s) ≤
        ∑ s ∈ Finset.range (n + 1), criticalRemainderSeriesTerm c A n s :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun _ _ _ ↦ (Real.exp_pos _).le)
    have hCo : (0 : ℝ) ≤ coMultipartiteGraphCountWithEdges (k - 1) n (criticalEdgeCount k n) :=
      Nat.cast_nonneg _
    calc
      _ ≤ _ := hbound
      _ ≤ (coMultipartiteGraphCountWithEdges (k - 1) n (criticalEdgeCount k n) : ℝ) *
          criticalRemainderSeries c A (k - 1) K n := by
        dsimp [criticalRemainderSeries]
        simpa only [mul_assoc, K, c, coMultipartiteGraphCountWithEdges] using
          mul_le_mul_of_nonneg_left hseries
          (show 0 ≤ (coMultipartiteGraphCountWithEdges (k - 1) n (criticalEdgeCount k n) : ℝ) *
            ((n + 1 : ℕ) : ℝ)^(k - 1) * K by positivity)
      _ ≤ (coMultipartiteGraphCountWithEdges (k - 1) n (criticalEdgeCount k n) : ℝ) *
          Real.exp (B * (Real.log ((n + 1 : ℕ) : ℝ))^2) :=
        mul_le_mul_of_nonneg_left hfullN hCo
      _ ≤ _ := by
        simpa only [mul_comm] using
          mul_le_mul_of_nonneg_left (criticalExp_log_succ_sq_le_baseTwo hB.le hn) hCo

/-- A uniform weighted comparison for any set of divisions and allowed sparse
sizes. It retains the exact ordered-cover and polynomial factors. -/
theorem eventually_criticalDivisionSum_le
    (k : ℕ) (hk : 3 ≤ k) (C : ℝ) :
    ∀ᶠ n : ℕ in atTop,
      ∀ (A : Finset (SupercriticalDivision k (Fin n))) (S : Finset ℕ),
        (∀ D ∈ A, D.sparse.card ∈ S) →
        (∀ s ∈ S, s ≤ n) →
        (∑ D ∈ A,
          (criticalReferenceFiberCard k n : ℝ) *
            Real.exp (criticalRemainderExponent k C n D.sparse.card)) ≤
        (coMultipartiteGraphCountWithEdges (k - 1) n (criticalEdgeCount k n) : ℝ) *
          ((n + 1 : ℕ) : ℝ) ^ (k - 1) * ((2 * (k - 1).factorial : ℕ) : ℝ) *
            ∑ s ∈ S, criticalRemainderSeriesTerm (criticalSparsePenaltyConstant k) C n s := by
  filter_upwards [eventually_card_supercriticalDivisionsWithSparseCard_mul_reference_le k hk]
    with n hdiv A S hmaps hsn
  let B : ℝ := criticalReferenceFiberCard k n
  let good : ℝ := coMultipartiteGraphCountWithEdges (k - 1) n (criticalEdgeCount k n)
  let J : ℝ := ((n + 1 : ℕ) : ℝ) ^ (k - 1) * ((2 * (k - 1).factorial : ℕ) : ℝ)
  have hregroup := sum_division_sparse_weights_le A S
    (fun s ↦ B * Real.exp (criticalRemainderExponent k C n s))
      hmaps (fun _ _ ↦ by dsimp [B]; positivity)
  have hterm (s : ℕ) (hs : s ∈ S) :
      ((supercriticalDivisionsWithSparseCard k n s).card : ℝ) *
          (B * Real.exp (criticalRemainderExponent k C n s)) ≤
        good * J * criticalRemainderSeriesTerm (criticalSparsePenaltyConstant k) C n s := by
    calc
      _ = (((supercriticalDivisionsWithSparseCard k n s).card : ℝ) * B) *
          Real.exp (criticalRemainderExponent k C n s) := by ring
      _ ≤ (J * (Nat.choose n s : ℝ) * good) *
          Real.exp (criticalRemainderExponent k C n s) :=
        mul_le_mul_of_nonneg_right (hdiv s (hsn s hs)) (Real.exp_pos _).le
      _ = good * J * ((Nat.choose n s : ℝ) *
          Real.exp (criticalRemainderExponent k C n s)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (choose_mul_criticalRemainderExponent_le k n s C) (by dsimp [good, J]; positivity)
  calc
    _ ≤ ∑ s ∈ S, ((supercriticalDivisionsWithSparseCard k n s).card : ℝ) *
        (B * Real.exp (criticalRemainderExponent k C n s)) := hregroup
    _ ≤ ∑ s ∈ S, good * J *
        criticalRemainderSeriesTerm (criticalSparsePenaltyConstant k) C n s :=
      Finset.sum_le_sum hterm
    _ = _ := by rw [← Finset.mul_sum]; dsimp [good, J]; ring

/-- Both actual totals are controlled by the proved numerical series. -/
theorem eventually_criticalTotals_le
    (k : ℕ) (hk : 3 ≤ k) (P : CriticalAggregationParameters k)
    (hdelta : P.delta < criticalCombinedSliceDelta k) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      (criticalDefectTotal k hk n (criticalEdgeCount k n) P.tau : ℝ) ≤
        (coMultipartiteGraphCountWithEdges (k - 1) n (criticalEdgeCount k n) : ℝ) *
          criticalRemainderSeries (criticalSparsePenaltyConstant k) C (k - 1)
            ((2 * (k - 1).factorial : ℕ) : ℝ) n * Real.exp (-(P.cMat / 4) * n) ∧
      ∀ L : ℝ,
        (criticalCleanTailTotal k hk n (criticalEdgeCount k n)
          (Nat.ceil (L * Real.log ((n + 1 : ℕ) : ℝ))) P.tau : ℝ) ≤
        (coMultipartiteGraphCountWithEdges (k - 1) n (criticalEdgeCount k n) : ℝ) *
          criticalRemainderTail (criticalSparsePenaltyConstant k) C (k - 1)
            ((2 * (k - 1).factorial : ℕ) : ℝ) L n := by
  obtain ⟨C, hC, hbounds⟩ := eventually_criticalDivisionBounds k hk P hdelta
  refine ⟨C, hC, ?_⟩
  filter_upwards [hbounds, eventually_criticalDivisionSum_le k hk C,
    eventually_ge_atTop (k - 1)] with n hboundsN hsumN hn
  let w : ℕ → ℝ := fun s ↦
    (criticalReferenceFiberCard k n : ℝ) *
      Real.exp (criticalRemainderExponent k C n s)
  let good : ℝ := coMultipartiteGraphCountWithEdges (k - 1) n (criticalEdgeCount k n)
  have hsparse (D : SupercriticalDivision k (Fin n)) : D.sparse.card ≤ n := by
    simpa using Finset.card_le_univ D.sparse
  constructor
  · rw [criticalDefectTotal, dite_eq_left hn, Nat.cast_sum]
    calc
      _ ≤ ∑ D ∈ allSupercriticalDivisions k n,
          w D.sparse.card * Real.exp (-(P.cMat / 4) * n) :=
        Finset.sum_le_sum (fun D _ ↦ (hboundsN hn D).2)
      _ = (∑ D ∈ allSupercriticalDivisions k n, w D.sparse.card) *
          Real.exp (-(P.cMat / 4) * n) := by rw [Finset.sum_mul]
      _ ≤ (good * ((n + 1 : ℕ) : ℝ) ^ (k - 1) *
          ((2 * (k - 1).factorial : ℕ) : ℝ) *
            ∑ s ∈ Finset.range (n + 1),
              criticalRemainderSeriesTerm (criticalSparsePenaltyConstant k) C n s) *
          Real.exp (-(P.cMat / 4) * n) := by
        apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
        exact hsumN (allSupercriticalDivisions k n) (Finset.range (n + 1))
          (fun D _ ↦ Finset.mem_range.mpr (by have := hsparse D; omega))
          (fun s hs ↦ by have := Finset.mem_range.mp hs; omega)
      _ = _ := by dsimp [good, criticalRemainderSeries]; ring
  · intro L
    let q := Nat.ceil (L * Real.log ((n + 1 : ℕ) : ℝ))
    let A := (allSupercriticalDivisions k n).filter fun D ↦ q < D.sparse.card
    let S := (Finset.range (n + 1)).filter fun s : ℕ ↦
      L * Real.log ((n + 1 : ℕ) : ℝ) ≤ (s : ℝ)
    have hmaps : ∀ D ∈ A, D.sparse.card ∈ S := by
      intro D hD
      have hq := (Finset.mem_filter.mp hD).2
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_range.mpr (by have := hsparse D; omega), ?_⟩
      exact (Nat.le_ceil _).trans (by exact_mod_cast hq.le)
    rw [criticalCleanTailTotal, dite_eq_left hn, Nat.cast_sum]
    have hfirst :
        (∑ D ∈ allSupercriticalDivisions k n,
          ((if q < D.sparse.card then
            (supercriticalCleanDivisionGraphFinset k hk (gammaK k)
              (gammaK_mem_supercritical_Ico k hk) (criticalEdgeCount k n)
                n P.tau hn D).card else 0 : ℕ) : ℝ)) ≤
          ∑ D ∈ A, w D.sparse.card := by
      rw [show (∑ D ∈ A, w D.sparse.card) =
          ∑ D ∈ allSupercriticalDivisions k n,
            if q < D.sparse.card then w D.sparse.card else 0 by
        exact Finset.sum_filter _ _]
      apply Finset.sum_le_sum
      intro D _
      split_ifs with hq
      · exact (hboundsN hn D).1
      · simp
    apply hfirst.trans
    have hsum := hsumN A S hmaps
      (fun s hs ↦ by have := Finset.mem_range.mp (Finset.mem_filter.mp hs).1; omega)
    simpa only [criticalRemainderTail, mul_assoc] using hsum

end InducedStars
