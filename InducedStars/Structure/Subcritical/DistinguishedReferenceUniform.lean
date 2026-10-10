import InducedStars.Structure.Subcritical.DistinguishedReferenceHeadroom

/-!
# Uniform nonzero balanced reference fibers

One explicit floor-sized retained key works for every exact finite density
in a fixed compact subinterval of the subcritical regime. The density error
of its actual integral vector is bounded by a displayed constant over `n`.
-/

noncomputable section
open Filter Finset Set Topology
open scoped Classical BigOperators
namespace InducedStars

/-- Summed count error for the actual integral vector. This retains the
linear error rather than losing a factor through minimum block capacity. -/
theorem retainedVector_count_error_sum_le {k : ℕ} {V : Type*}
    [Fintype V] [DecidableEq V] {D : SubcriticalDivision k V} {eta : ℝ} {R₀ : ℕ}
    (v : RetainedEdgeCountVector D eta R₀) {p E : ℝ}
    (hA : 0 < retainedActiveTotalCapacity D eta R₀)
    (herr : ∀ e, |retainedEdgeCountDensity v e - p| ≤
      E / retainedActiveTotalCapacity D eta R₀ +
        1 / (retainedActiveCapacity D eta R₀ e : ℝ)) :
    (∑ e, |(v.count e : ℝ) - p * retainedActiveCapacity D eta R₀ e|) ≤
      E + Fintype.card (RetainedActivePair D eta R₀) := by
  have hAR : (0 : ℝ) < retainedActiveTotalCapacity D eta R₀ := by exact_mod_cast hA
  calc
    _ ≤ ∑ e, ((E / retainedActiveTotalCapacity D eta R₀) *
        retainedActiveCapacity D eta R₀ e + 1) := by
      apply Finset.sum_le_sum
      intro e _
      have hN : (0 : ℝ) < retainedActiveCapacity D eta R₀ e := by
        exact_mod_cast retainedActiveCapacity_pos D eta R₀ e
      have heq : |(v.count e : ℝ) - p * retainedActiveCapacity D eta R₀ e| =
          |retainedEdgeCountDensity v e - p| * retainedActiveCapacity D eta R₀ e := by
        calc
          _ = |(retainedEdgeCountDensity v e - p) *
              retainedActiveCapacity D eta R₀ e| := by
            congr 1
            rw [retainedEdgeCountDensity]
            field_simp
          _ = _ := by rw [abs_mul, abs_of_pos hN]
      rw [heq]
      have h := mul_le_mul_of_nonneg_right (herr e) hN.le
      simpa only [add_mul, one_div_mul_cancel hN.ne'] using h
    _ = _ := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      have hs : (∑ e, (retainedActiveCapacity D eta R₀ e : ℝ)) =
          retainedActiveTotalCapacity D eta R₀ := by
        simp only [retainedActiveTotalCapacity, Nat.cast_sum]
      rw [hs, div_mul_cancel₀ _ hAR.ne']
      simp

def subcriticalReferenceDensityErrorConstant (k : ℕ) (a : ℝ) : ℝ :=
  (128 * k + 16 * ((k - 1 : ℕ) : ℝ)^2) / a^2

theorem subcriticalReferenceDensityErrorConstant_pos {k : ℕ} (hk : 3 ≤ k)
    {a : ℝ} (ha : 0 < a) : 0 < subcriticalReferenceDensityErrorConstant k a := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  unfold subcriticalReferenceDensityErrorConstant
  positivity

theorem subcriticalReference_density_error_bound {k n : ℕ} (hk : 3 ≤ k)
    (hn : 1 ≤ n) {a A N : ℝ} (ha : 0 < a) (hA : 0 < A) (hN : 0 < N)
    (hAlow : a^2 * (n : ℝ)^2 ≤ 32 * A)
    (hNlow : a^2 * (n : ℝ)^2 ≤ 16 * ((k - 1 : ℕ) : ℝ)^2 * N) :
    (4 : ℝ) * k * n / A + 1 / N ≤ subcriticalReferenceDensityErrorConstant k a / n := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hden : 0 < a^2 * (n : ℝ) := by positivity
  have hfirst : (4 : ℝ) * k * n / A ≤ (128 : ℝ) * k / (a^2 * n) := by
    apply (div_le_div_iff₀ hA hden).2
    have h := mul_le_mul_of_nonneg_left hAlow (show (0 : ℝ) ≤ 4 * k by positivity)
    nlinarith [h]
  have hsecond : 1 / N ≤ (16 : ℝ) * ((k - 1 : ℕ) : ℝ)^2 / (a^2 * n) := by
    apply (div_le_div_iff₀ hN hden).2
    have hs := mul_nonneg (sq_nonneg a) (show 0 ≤ (n : ℝ)^2 - n by nlinarith)
    nlinarith
  calc
    _ ≤ (128 : ℝ) * k / (a^2 * n) +
        16 * ((k - 1 : ℕ) : ℝ)^2 / (a^2 * n) := add_le_add hfirst hsecond
    _ = _ := by unfold subcriticalReferenceDensityErrorConstant; ring

/-- Uniform finite reference theorem. The constant and threshold depend
only on `k`, the density band and the fixed window, not on `m` or `b`. -/
theorem eventually_subcriticalReference_fiber {k : ℕ} (hk : 3 ≤ k)
    {gLower gUpper delta : ℝ} (hgLower : 0 < gLower) (hband : gLower ≤ gUpper)
    (hgUpper : gUpper < gammaK k) (hd : 0 < delta)
    (hdp : delta ≤ pK k / 2) (hdq : delta ≤ (1 - pK k) / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop, ∀ m b : ℕ,
      gLower ≤ subcriticalReferenceDensity n m b →
      subcriticalReferenceDensity n m b ≤ gUpper →
      ∃ hrq : k - 1 ≤ subcriticalReferenceSupportSize k n m b,
        ∃ hqn : subcriticalReferenceSupportSize k n m b ≤ n,
          ∃ v : RetainedEdgeCountVector (balancedRetainedDivision hk hrq hqn) 0 n,
            v ∈ retainedEdgeCountLevel (balancedRetainedDivision hk hrq hqn)
              0 n m delta (b : ℤ) ∧
            (∀ e, |retainedEdgeCountDensity v e - pK k| ≤ C / n) ∧
            (∑ e, |(v.count e : ℝ) - pK k * retainedActiveCapacity
              (balancedRetainedDivision hk hrq hqn) 0 n e|) ≤
              (4 : ℝ) * k * n + Fintype.card
                (RetainedActivePair (balancedRetainedDivision hk hrq hqn) 0 n) ∧
            0 < retainedKeyPartitionFunction (subcriticalDistinguishedReferenceKey hk n m b)
              m delta (b : ℤ) ∧
            (1 - Real.sqrt (gUpper / gammaK k)) * n ≤
              ((subcriticalDistinguishedReferenceKey hk n m b).remainder.card : ℝ) := by
  let a := Real.sqrt (gLower / gammaK k)
  have ha : 0 < a := Real.sqrt_pos.2 (div_pos hgLower (gammaK_pos hk))
  refine ⟨subcriticalReferenceDensityErrorConstant k a,
    subcriticalReferenceDensityErrorConstant_pos hk ha, ?_⟩
  filter_upwards [eventually_subcriticalReference_scale (k := k) ha hd] with n hn
  intro m b hgl hgu
  have hgamma : subcriticalReferenceDensity n m b ∈ Ioo (0 : ℝ) (gammaK k) :=
    ⟨hgLower.trans_le hgl, hgu.trans_lt hgUpper⟩
  have hmu : a ≤ subcriticalReferenceMass k n m b :=
    Real.sqrt_le_sqrt ((div_le_div_iff_of_pos_right (gammaK_pos hk)).2 hgl)
  obtain ⟨hrq, hqn, hroom, hpair, hAlow, hNlow⟩ :=
    subcriticalReference_headroom_of_scale hk hn.1 hgamma ha hd.le hmu
      hn.2.1 hn.2.2.1 hn.2.2.2
  obtain ⟨v, hv, herr, hpos⟩ := subcriticalReferenceVector_exists hk hn.1 hgamma
    hrq hqn delta hd.le hdp hdq hroom hpair
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hA : (0 : ℝ) < retainedActiveTotalCapacity
      (balancedRetainedDivision hk hrq hqn) 0 n := by
    have ht : 0 < a^2 * (n : ℝ)^2 := by positivity
    nlinarith [hAlow]
  refine ⟨hrq, hqn, v, hv, ?_, ?_, hpos, ?_⟩
  · intro e
    apply (herr e).trans
    have hN : (0 : ℝ) < retainedActiveCapacity
        (balancedRetainedDivision hk hrq hqn) 0 n e := by
      exact_mod_cast retainedActiveCapacity_pos _ 0 n e
    exact subcriticalReference_density_error_bound hk (by omega) ha hA hN hAlow (hNlow e)
  · exact retainedVector_count_error_sum_le v (by exact_mod_cast hA) herr
  · unfold subcriticalDistinguishedReferenceKey
    rw [dif_pos ⟨hrq, hqn⟩, balancedRetainedReferenceKey_remainder_card, Nat.cast_sub hqn]
    have hmuUpper : subcriticalReferenceMass k n m b ≤ Real.sqrt (gUpper / gammaK k) :=
      Real.sqrt_le_sqrt ((div_le_div_iff_of_pos_right (gammaK_pos hk)).2 hgu)
    have hf := (subcriticalReferenceSupportSize_floor_bounds k n m b).1
    have hm := mul_le_mul_of_nonneg_right hmuUpper (show (0 : ℝ) ≤ n by positivity)
    linarith

end InducedStars
