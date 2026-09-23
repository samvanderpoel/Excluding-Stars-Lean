import InducedStars.Structure.Critical.WindowCoarseBounds
import InducedStars.Structure.Critical.WindowCoarseFamilies
import InducedStars.Structure.Critical.WindowCoarseSeries

/-!
# Coarse global counts in the logarithmic critical window

The uniform division estimates are summed over their actual finite families.
Sparse-vertex choices cost at most exp(s log(n+1)); the full ordered-division
factor is compared with the actual co-partite denominator.
-/

noncomputable section
open Filter Finset Set
open scoped BigOperators Topology Classical
namespace InducedStars

/-- Choosing sparse vertices contributes at most one s log(n+1) term. -/
theorem choose_mul_criticalWindowCoarseExponent_le
    (k n s : ℕ) (C : ℝ) :
    (Nat.choose n s : ℝ) * Real.exp (criticalWindowCoarseExponent k C n s) ≤
      criticalWindowCoarseSeriesTerm (criticalSparsePenaltyConstant k) C n s := by
  have hchoose : (Nat.choose n s : ℝ) ≤
      Real.exp ((s : ℝ) * Real.log ((n + 1 : ℕ) : ℝ)) := by
    rw [Real.exp_nat_mul, Real.exp_log (by positivity : (0 : ℝ) < ((n + 1 : ℕ) : ℝ))]
    exact_mod_cast (Nat.choose_le_pow n s).trans (Nat.pow_le_pow_left (by omega) s)
  calc
    _ ≤ Real.exp ((s : ℝ) * Real.log ((n + 1 : ℕ) : ℝ)) *
        Real.exp (criticalWindowCoarseExponent k C n s) :=
      mul_le_mul_of_nonneg_right hchoose (Real.exp_pos _).le
    _ = _ := by
      rw [← Real.exp_add]
      unfold criticalWindowCoarseExponent criticalWindowCoarseSeriesTerm
      congr 1
      ring

/-- A uniform weighted comparison for any set of divisions and allowed sparse
sizes. It retains the exact ordered-cover and polynomial factors. -/
theorem eventually_criticalWindowDivisionSum_le
    (k : ℕ) (hk : 3 ≤ k) (a C : ℝ) :
    ∀ᶠ n : ℕ in atTop,
      ∀ (A : Finset (SupercriticalDivision k (Fin n))) (S : Finset ℕ),
        (∀ D ∈ A, D.sparse.card ∈ S) →
        (∀ s ∈ S, s ≤ n) →
        (∑ D ∈ A,
          (Nat.choose (criticalTargetCapacity k n) (criticalWindowReferenceSelected k a n) : ℝ) *
            Real.exp (criticalWindowCoarseExponent k C n D.sparse.card)) ≤
        (coMultipartiteGraphCountWithEdges (k - 1) n (criticalWindowEdgeCount k a n) : ℝ) *
          ((n + 1 : ℕ) : ℝ) ^ (k - 1) * ((2 * (k - 1).factorial : ℕ) : ℝ) *
            ∑ s ∈ S, criticalWindowCoarseSeriesTerm (criticalSparsePenaltyConstant k) C n s := by
  filter_upwards [eventually_card_supercriticalDivisionsWithSparseCard_mul_windowReference_le k hk a]
    with n hdiv A S hmaps hsn
  let B : ℝ := Nat.choose (criticalTargetCapacity k n) (criticalWindowReferenceSelected k a n)
  let good : ℝ := coMultipartiteGraphCountWithEdges (k - 1) n (criticalWindowEdgeCount k a n)
  let J : ℝ := ((n + 1 : ℕ) : ℝ) ^ (k - 1) * ((2 * (k - 1).factorial : ℕ) : ℝ)
  have hregroup := sum_division_sparse_weights_le A S
    (fun s ↦ B * Real.exp (criticalWindowCoarseExponent k C n s))
      hmaps (fun _ _ ↦ by dsimp [B]; positivity)
  have hterm (s : ℕ) (hs : s ∈ S) :
      ((supercriticalDivisionsWithSparseCard k n s).card : ℝ) *
          (B * Real.exp (criticalWindowCoarseExponent k C n s)) ≤
        good * J * criticalWindowCoarseSeriesTerm (criticalSparsePenaltyConstant k) C n s := by
    calc
      _ = (((supercriticalDivisionsWithSparseCard k n s).card : ℝ) * B) *
          Real.exp (criticalWindowCoarseExponent k C n s) := by ring
      _ ≤ (J * (Nat.choose n s : ℝ) * good) *
          Real.exp (criticalWindowCoarseExponent k C n s) :=
        mul_le_mul_of_nonneg_right (hdiv s (hsn s hs)) (Real.exp_pos _).le
      _ = good * J * ((Nat.choose n s : ℝ) *
          Real.exp (criticalWindowCoarseExponent k C n s)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (choose_mul_criticalWindowCoarseExponent_le k n s C) (by dsimp [good, J]; positivity)
  calc
    _ ≤ ∑ s ∈ S, ((supercriticalDivisionsWithSparseCard k n s).card : ℝ) *
        (B * Real.exp (criticalWindowCoarseExponent k C n s)) := hregroup
    _ ≤ ∑ s ∈ S, good * J *
        criticalWindowCoarseSeriesTerm (criticalSparsePenaltyConstant k) C n s :=
      Finset.sum_le_sum hterm
    _ = _ := by rw [← Finset.mul_sum]; dsimp [good, J]; ring

/-- Both actual totals are controlled by the proved numerical series. -/
theorem eventually_criticalWindowTotals_le
    (k : ℕ) (hk : 3 ≤ k) (a : ℝ) (P : CriticalAggregationParameters k) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      (criticalWindowDefectTotal k hk n (criticalWindowEdgeCount k a n) P.tau : ℝ) ≤
        (coMultipartiteGraphCountWithEdges (k - 1) n (criticalWindowEdgeCount k a n) : ℝ) *
          criticalWindowCoarseSeries (criticalSparsePenaltyConstant k) C (k - 1)
            ((2 * (k - 1).factorial : ℕ) : ℝ) n * Real.exp (-(P.cMat / 4) * n) ∧
      ∀ L : ℝ,
        (criticalWindowCleanTailTotal k hk n (criticalWindowEdgeCount k a n)
          (Nat.ceil (L * Real.log ((n + 1 : ℕ) : ℝ))) P.tau : ℝ) ≤
        (coMultipartiteGraphCountWithEdges (k - 1) n (criticalWindowEdgeCount k a n) : ℝ) *
          criticalWindowCoarseTail (criticalSparsePenaltyConstant k) C (k - 1)
            ((2 * (k - 1).factorial : ℕ) : ℝ) L n := by
  obtain ⟨C, hC, hbounds⟩ := eventually_criticalWindowDivisionBounds k hk a P
  refine ⟨C, hC, ?_⟩
  filter_upwards [hbounds, eventually_criticalWindowDivisionSum_le k hk a C,
    eventually_ge_atTop (k - 1)] with n hboundsN hsumN hn
  let w : ℕ → ℝ := fun s ↦
    (Nat.choose (criticalTargetCapacity k n) (criticalWindowReferenceSelected k a n) : ℝ) *
      Real.exp (criticalWindowCoarseExponent k C n s)
  let good : ℝ := coMultipartiteGraphCountWithEdges (k - 1) n (criticalWindowEdgeCount k a n)
  have hsparse (D : SupercriticalDivision k (Fin n)) : D.sparse.card ≤ n := by
    simpa using Finset.card_le_univ D.sparse
  constructor
  · rw [criticalWindowDefectTotal, dite_eq_left hn, Nat.cast_sum]
    calc
      _ ≤ ∑ D ∈ allSupercriticalDivisions k n,
          w D.sparse.card * Real.exp (-(P.cMat / 4) * n) :=
        Finset.sum_le_sum (fun D _ ↦ (hboundsN hn D).2)
      _ = (∑ D ∈ allSupercriticalDivisions k n, w D.sparse.card) *
          Real.exp (-(P.cMat / 4) * n) := by rw [Finset.sum_mul]
      _ ≤ (good * ((n + 1 : ℕ) : ℝ) ^ (k - 1) *
          ((2 * (k - 1).factorial : ℕ) : ℝ) *
            ∑ s ∈ Finset.range (n + 1),
              criticalWindowCoarseSeriesTerm (criticalSparsePenaltyConstant k) C n s) *
          Real.exp (-(P.cMat / 4) * n) := by
        apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
        exact hsumN (allSupercriticalDivisions k n) (Finset.range (n + 1))
          (fun D _ ↦ Finset.mem_range.mpr (by have := hsparse D; omega))
          (fun s hs ↦ by have := Finset.mem_range.mp hs; omega)
      _ = _ := by dsimp [good, criticalWindowCoarseSeries]; ring
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
    rw [criticalWindowCleanTailTotal, dite_eq_left hn, Nat.cast_sum]
    have hfirst :
        (∑ D ∈ allSupercriticalDivisions k n,
          ((if q < D.sparse.card then
            (supercriticalCleanDivisionGraphFinset k hk (gammaK k)
              (gammaK_mem_supercritical_Ico k hk) (criticalWindowEdgeCount k a n)
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
    simpa only [criticalWindowCoarseTail, mul_assoc] using hsum

end InducedStars
