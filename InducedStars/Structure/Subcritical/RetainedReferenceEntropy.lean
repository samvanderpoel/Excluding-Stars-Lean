import InducedStars.Structure.Subcritical.RetainedEntropyComparison
import InducedStars.Structure.Subcritical.DistinguishedFiniteReference

/-!
# Lower entropy estimate for the balanced retained reference

Paper: `lemma:clean-retained-comparison-K1k`. Exact binomial
entropy bounds and a summed count-error estimate give an explicit linear
plus logarithmic loss. The reference density is the actual finite density.
-/

noncomputable section
open Finset Set
open scoped BigOperators Classical
namespace InducedStars

def subcriticalRetainedEntropyLoss (k : ℕ) : ℝ :=
  Real.binEntropy (pK k) / pK k + Real.binEntropy (pK k) / (1 - pK k)

theorem subcriticalRetainedEntropyLoss_nonneg {k : ℕ} (hk : 3 ≤ k) :
    0 ≤ subcriticalRetainedEntropyLoss k := by
  have hp := pK_pos (by omega : 2 ≤ k)
  have hq : 0 < 1 - pK k := sub_pos.mpr (pK_lt_one (by omega : 2 ≤ k))
  have hh := Real.binEntropy_nonneg hp.le (by linarith)
  unfold subcriticalRetainedEntropyLoss
  positivity

theorem retainedEdgeCountMultiplicity_log_lower {k n : ℕ} (hk : 3 ≤ k)
    {D : SubcriticalDivision k (Fin n)} {eta : ℝ} {R₀ : ℕ}
    (v : RetainedEdgeCountVector D eta R₀) :
    Real.binEntropy (pK k) * retainedActiveTotalCapacity D eta R₀ -
        subcriticalRetainedEntropyLoss k *
          (∑ e, |(v.count e : ℝ) - pK k * retainedActiveCapacity D eta R₀ e|) -
        2 * Fintype.card (RetainedActivePair D eta R₀) * Real.log ((n : ℝ) + 1) ≤
      Real.log (retainedEdgeCountMultiplicity v : ℝ) := by
  have hp : pK k ∈ Ioo (0 : ℝ) 1 :=
    ⟨pK_pos (by omega : 2 ≤ k), pK_lt_one (by omega : 2 ≤ k)⟩
  have hlog (e : RetainedActivePair D eta R₀) :
      Real.log ((retainedActiveCapacity D eta R₀ e + 1 : ℕ) : ℝ) ≤
        2 * Real.log ((n : ℝ) + 1) := by
    have hcap : retainedActiveCapacity D eta R₀ e ≤ n^2 := by
      rw [retainedActiveCapacity, pow_two]
      exact Nat.mul_le_mul (by simpa using Finset.card_le_univ (D.part e.leftPart))
        (by simpa using Finset.card_le_univ (D.part e.rightPart))
    have hc : ((retainedActiveCapacity D eta R₀ e + 1 : ℕ) : ℝ) ≤ ((n : ℝ) + 1)^2 := by
      have hc' : (retainedActiveCapacity D eta R₀ e : ℝ) ≤ (n : ℝ)^2 := by exact_mod_cast hcap
      push_cast
      nlinarith [show (0 : ℝ) ≤ n by positivity]
    calc
      _ ≤ Real.log (((n : ℝ) + 1)^2) := Real.log_le_log (by positivity) hc
      _ = _ := by rw [Real.log_pow]; norm_num
  rw [retainedEdgeCountMultiplicity, Nat.cast_prod, Real.log_prod (by
    intro e he
    exact (by exact_mod_cast Nat.choose_pos (v.count_le_capacity e) :
      (0 : ℝ) < Nat.choose (retainedActiveCapacity D eta R₀ e) (v.count e)).ne')]
  have hterm (e : RetainedActivePair D eta R₀) :
      (retainedActiveCapacity D eta R₀ e : ℝ) * Real.binEntropy (pK k) -
        subcriticalRetainedEntropyLoss k * |(v.count e : ℝ) - pK k * retainedActiveCapacity D eta R₀ e| -
        2 * Real.log ((n : ℝ) + 1) ≤
      Real.log (Nat.choose (retainedActiveCapacity D eta R₀ e) (v.count e) : ℝ) := by
    have h₁ := DenseGraph.binomialEntropyPerspective_lower_of_count_error
      (v.count_le_capacity e) hp
    have h₂ := DenseGraph.log_choose_lower_binEntropy (v.count_le_capacity e)
    have h₃ := hlog e
    dsimp [subcriticalRetainedEntropyLoss]
    linarith
  have hsum := Finset.sum_le_sum (fun e (_ : e ∈ (Finset.univ : Finset
    (RetainedActivePair D eta R₀))) ↦ hterm e)
  calc
    _ = ∑ e : RetainedActivePair D eta R₀,
        ((retainedActiveCapacity D eta R₀ e : ℝ) * Real.binEntropy (pK k) -
          subcriticalRetainedEntropyLoss k * |(v.count e : ℝ) - pK k *
            retainedActiveCapacity D eta R₀ e| - 2 * Real.log ((n : ℝ) + 1)) := by
      simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        ← Finset.sum_mul, ← Finset.mul_sum, retainedActiveTotalCapacity, Nat.cast_sum]
      ring
    _ ≤ _ := hsum

/-- Loss in passing from a balanced support capacity to the actual retained
edge count. The rounding contribution is explicit and independent of `n`. -/
theorem balancedRetained_entropy_capacity_lower {k q : ℕ} (hk : 3 ≤ k) :
    subcriticalRetainedEntropySlope k *
        ((DenseGraph.balancedMultipartiteInternalCapacity (k - 1) q : ℝ) +
          pK k * DenseGraph.balancedMultipartiteCrossCapacity (k - 1) q) -
        Real.binEntropy (pK k) / (1 + ((k - 2 : ℕ) : ℝ) * pK k) *
          ((k - 1 : ℕ) : ℝ)^2 ≤
      Real.binEntropy (pK k) * DenseGraph.balancedMultipartiteCrossCapacity (k - 1) q := by
  have hr : 0 < k - 1 := by omega
  have hp := pK_pos (by omega : 2 ≤ k)
  have hh := Real.binEntropy_nonneg hp.le (pK_lt_one (by omega : 2 ≤ k)).le
  have hd0 : (0 : ℝ) ≤ (k - 2 : ℕ) := by positivity
  have hden : 0 < 1 + ((k - 2 : ℕ) : ℝ) * pK k := by positivity
  have hd : ((k - 2 : ℕ) : ℝ) + 1 = (k - 1 : ℕ) := by
    exact_mod_cast (show k - 2 + 1 = k - 1 by omega)
  have hi := (abs_le.mp (DenseGraph.balancedMultipartiteInternalCapacity_approx
    (q := q) hr)).2
  have ha := (abs_le.mp (DenseGraph.balancedMultipartiteCrossCapacity_approx
    (q := q) hr)).1
  have hraw : -((k - 1 : ℕ) : ℝ)^2 ≤
      (DenseGraph.balancedMultipartiteCrossCapacity (k - 1) q : ℝ) -
        ((k - 2 : ℕ) : ℝ) * DenseGraph.balancedMultipartiteInternalCapacity (k - 1) q := by
    have hm := mul_le_mul_of_nonneg_left hi hd0
    have hq : 0 ≤ ((k - 2 : ℕ) : ℝ) * (q : ℝ) / 2 := by positivity
    have heq : ((((k - 1 : ℕ) : ℝ) - 1) * (q : ℝ)^2 / (2 * (k - 1 : ℕ))) =
        ((k - 2 : ℕ) : ℝ) * ((q : ℝ)^2 / (2 * (k - 1 : ℕ))) := by rw [← hd]; ring
    rw [heq] at ha
    nlinarith
  have hm := mul_le_mul_of_nonneg_left hraw (div_nonneg hh hden.le)
  have hid : Real.binEntropy (pK k) * DenseGraph.balancedMultipartiteCrossCapacity (k - 1) q -
      subcriticalRetainedEntropySlope k *
        ((DenseGraph.balancedMultipartiteInternalCapacity (k - 1) q : ℝ) +
          pK k * DenseGraph.balancedMultipartiteCrossCapacity (k - 1) q) =
      Real.binEntropy (pK k) / (1 + ((k - 2 : ℕ) : ℝ) * pK k) *
        ((DenseGraph.balancedMultipartiteCrossCapacity (k - 1) q : ℝ) -
          ((k - 2 : ℕ) : ℝ) * DenseGraph.balancedMultipartiteInternalCapacity (k - 1) q) := by
    unfold subcriticalRetainedEntropySlope
    field_simp
    <;> ring
  linarith

/-- The complete reference core has at most `k²` active coordinates. -/
theorem balancedRetainedDivision_activeIndex_card_le {k n q : ℕ} (hk : 3 ≤ k)
    (hrq : k - 1 ≤ q) (hqn : q ≤ n) :
    Fintype.card (RetainedActivePair (balancedRetainedDivision hk hrq hqn) 0 n) ≤ k^2 := by
  let D := balancedRetainedDivision hk hrq hqn
  have hpart : Fintype.card D.PartIndex = k - 1 := by
    change Fintype.card ((_ : Fin 1) × Fin (k - 1)) = k - 1
    rw [Fintype.card_sigma]
    simp
  calc
    _ ≤ (D.retainedPartIndices 0 n).card^2 := card_retainedActivePair_le_sq_retainedParts D 0 n
    _ ≤ (Fintype.card D.PartIndex)^2 := Nat.pow_le_pow_left (Finset.card_le_univ _) 2
    _ = (k - 1)^2 := by rw [hpart]
    _ ≤ k^2 := Nat.pow_le_pow_left (Nat.sub_le _ _) 2

/-- One explicit linear loss, depending only on the forbidden-star order. -/
def subcriticalReferenceEntropyLinearConstant (k : ℕ) : ℝ :=
  4 * k * (subcriticalRetainedEntropySlope k + subcriticalRetainedEntropyLoss k) +
    Real.binEntropy (pK k) / (1 + ((k - 2 : ℕ) : ℝ) * pK k) * ((k - 1 : ℕ) : ℝ)^2 +
    subcriticalRetainedEntropyLoss k * (k : ℝ)^2

theorem subcriticalReferenceEntropyLinearConstant_nonneg {k : ℕ} (hk : 3 ≤ k) :
    0 ≤ subcriticalReferenceEntropyLinearConstant k := by
  have hs := subcriticalRetainedEntropySlope_nonneg hk
  have hl := subcriticalRetainedEntropyLoss_nonneg hk
  have hp := pK_pos (by omega : 2 ≤ k)
  have hh := Real.binEntropy_nonneg hp.le (pK_lt_one (by omega : 2 ≤ k)).le
  unfold subcriticalReferenceEntropyLinearConstant
  positivity

/-- The actual reference vector is exponentially large at its exact finite
edge density. Inputs are its integral allocation errors, not a lower bound
on a graph family. -/
theorem balancedRetainedVector_entropy_lower {k n q : ℕ} (hk : 3 ≤ k)
    (hn : 1 ≤ n) (hrq : k - 1 ≤ q) (hqn : q ≤ n)
    (v : RetainedEdgeCountVector (balancedRetainedDivision hk hrq hqn) 0 n)
    (t : ℝ)
    (hexpected : |t - ((DenseGraph.balancedMultipartiteInternalCapacity (k - 1) q : ℝ) +
        pK k * DenseGraph.balancedMultipartiteCrossCapacity (k - 1) q)| ≤ 4 * k * n)
    (hcount : (∑ e, |(v.count e : ℝ) - pK k *
          retainedActiveCapacity (balancedRetainedDivision hk hrq hqn) 0 n e|) ≤
        4 * k * n + Fintype.card (RetainedActivePair (balancedRetainedDivision hk hrq hqn) 0 n)) :
    Real.exp (subcriticalRetainedEntropySlope k * t -
      subcriticalReferenceEntropyLinearConstant k * n -
      2 * (k : ℝ)^2 * Real.log ((n : ℝ) + 1)) ≤ (retainedEdgeCountMultiplicity v : ℝ) := by
  let D := balancedRetainedDivision hk hrq hqn
  have hs := subcriticalRetainedEntropySlope_nonneg hk
  have hl := subcriticalRetainedEntropyLoss_nonneg hk
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hQ : (Fintype.card (RetainedActivePair D 0 n) : ℝ) ≤ (k : ℝ)^2 := by
    exact_mod_cast balancedRetainedDivision_activeIndex_card_le hk hrq hqn
  have hlog0 : 0 ≤ Real.log ((n : ℝ) + 1) := Real.log_nonneg (by linarith)
  have hlog := retainedEdgeCountMultiplicity_log_lower hk v
  rw [balancedRetainedDivision_activeTotalCapacity] at hlog
  have hcapacity := balancedRetained_entropy_capacity_lower (q := q) hk
  have hex := mul_le_mul_of_nonneg_left (abs_le.mp hexpected).2 hs
  have hct := mul_le_mul_of_nonneg_left (hcount.trans (add_le_add le_rfl hQ)) hl
  have hQt := mul_le_mul_of_nonneg_right hQ (show 0 ≤ 2 * Real.log ((n : ℝ) + 1) by positivity)
  have hr0 : 0 ≤ Real.binEntropy (pK k) /
      (1 + ((k - 2 : ℕ) : ℝ) * pK k) * ((k - 1 : ℕ) : ℝ)^2 := by
    have hp := pK_pos (by omega : 2 ≤ k)
    have hh := Real.binEntropy_nonneg hp.le (pK_lt_one (by omega : 2 ≤ k)).le
    positivity
  have hround := mul_le_mul_of_nonneg_left hnR hr0
  have hQn := mul_le_mul_of_nonneg_left hnR (mul_nonneg hl (sq_nonneg (k : ℝ)))
  have hbound : subcriticalRetainedEntropySlope k * t -
      subcriticalReferenceEntropyLinearConstant k * n -
      2 * (k : ℝ)^2 * Real.log ((n : ℝ) + 1) ≤
        Real.log (retainedEdgeCountMultiplicity v : ℝ) := by
    unfold subcriticalReferenceEntropyLinearConstant
    dsimp [D] at hQt
    nlinarith
  have hpos : (0 : ℝ) < retainedEdgeCountMultiplicity v := by
    rw [retainedEdgeCountMultiplicity, Nat.cast_prod]
    exact Finset.prod_pos fun e he ↦ by exact_mod_cast Nat.choose_pos (v.count_le_capacity e)
  exact (Real.le_log_iff_exp_le hpos).mp hbound

theorem balancedRetainedReferencePartitionFunction_lower {k n q m b : ℕ}
    (hk : 3 ≤ k) (hn : 1 ≤ n) (hrq : k - 1 ≤ q) (hqn : q ≤ n) {delta : ℝ}
    (v : RetainedEdgeCountVector (balancedRetainedDivision hk hrq hqn) 0 n)
    (hv : v ∈ retainedEdgeCountLevel (balancedRetainedDivision hk hrq hqn) 0 n m delta (b : ℤ))
    (hexpected : |((m : ℝ) - b) - ((DenseGraph.balancedMultipartiteInternalCapacity (k - 1) q : ℝ) +
        pK k * DenseGraph.balancedMultipartiteCrossCapacity (k - 1) q)| ≤ 4 * k * n)
    (hcount : (∑ e, |(v.count e : ℝ) - pK k *
          retainedActiveCapacity (balancedRetainedDivision hk hrq hqn) 0 n e|) ≤
        4 * k * n + Fintype.card (RetainedActivePair (balancedRetainedDivision hk hrq hqn) 0 n)) :
    Real.exp (subcriticalRetainedEntropySlope k * ((m : ℝ) - b) -
      subcriticalReferenceEntropyLinearConstant k * n -
      2 * (k : ℝ)^2 * Real.log ((n : ℝ) + 1)) ≤
      (retainedKeyPartitionFunction (balancedRetainedReferenceKey hk hrq hqn) m delta (b : ℤ) : ℝ) := by
  apply (balancedRetainedVector_entropy_lower hk hn hrq hqn v _ hexpected hcount).trans
  rw [balancedRetainedReferenceKey, retainedKeyPartitionFunction_retainedKey,
    retainedPartitionFunction]
  exact_mod_cast Finset.single_le_sum (fun w hw ↦ Nat.zero_le (retainedEdgeCountMultiplicity w)) hv

end InducedStars
