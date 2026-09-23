import InducedStars.Structure.Critical.FineBalanceReferenceEntropy
import InducedStars.Structure.Critical.FineBalanceFarComparison

/-!
# Uniform reference counts for fixed sparse graphs

The normalized retained capacity and selected count give a binomial entropy
lower bound uniform in the prescribed sparse set and its induced graph.
Comparing this bound with the absolute far-family entropy loss retains the
paper's close-family restriction in the fine-balance counting argument.
-/

noncomputable section

open Filter Set Topology

namespace InducedStars

/-- A fixed retained-support reference slice has almost the full critical
entropy exponent, uniformly over every sufficiently small sparse set and
every admissible edge count on that set.  All natural-subtraction guards are
included in the conclusion. -/
theorem eventually_criticalRetainedSupport_log_choose_lower
    (k : ℕ) (hk : 3 ≤ k) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ n : ℕ in atTop,
      ∀ s : ℕ, s ≤ n → (s : ℝ) ≤ δ * n →
      ∀ t : ℕ, t ≤ Nat.choose s 2 →
        t + DenseGraph.balancedMultipartiteInternalCapacity (k - 1) (n - s) ≤
            criticalEdgeCount k n ∧
        0 < criticalRetainedSupportSelectedCount k n s t ∧
        criticalRetainedSupportSelectedCount k n s t ≤
            criticalRetainedSupportCapacity k n s ∧
        (criticalNaturalEntropyExponent k - ε) * (n : ℝ) ^ 2 ≤
          Real.log (Nat.choose (criticalRetainedSupportCapacity k n s)
            (criticalRetainedSupportSelectedCount k n s t) : ℝ) := by
  let b := criticalReferenceCapacitySquareDensity k
  let a := criticalReferenceSelectedSquareDensity k
  have hb : 0 < b := criticalReferenceCapacitySquareDensity_pos hk
  have ha : 0 < a := criticalReferenceSelectedSquareDensity_pos hk
  have hab : a < b := criticalReferenceSelectedSquareDensity_lt_capacity hk
  obtain ⟨η, hη, hcontrol⟩ := Metric.continuousAt_iff.mp
    (criticalNormalizedBinomialEntropy_continuousAt (x := b) (y := a) hb.ne')
      (ε / 2) (half_pos hε)
  let ζ : ℝ := min (η / 2) (min (a / 8) ((b - a) / 8))
  have hζ : 0 < ζ := by dsimp [ζ]; positivity
  have hζη : ζ < η := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hζa : 4 * ζ < a := by
    have := (min_le_right (η / 2) (min (a / 8) ((b - a) / 8))).trans
      (min_le_left _ _)
    change ζ ≤ a / 8 at this
    linarith
  have hζgap : 4 * ζ < b - a := by
    have := (min_le_right (η / 2) (min (a / 8) ((b - a) / 8))).trans
      (min_le_right _ _)
    change ζ ≤ (b - a) / 8 at this
    linarith
  obtain ⟨δ, hδ, huniform⟩ := eventually_criticalRetainedSupport_normalized_close
    k hk hζ hζa hζgap
  refine ⟨δ, hδ, ?_⟩
  filter_upwards [huniform, eventually_ge_atTop 1,
      eventually_ge_atTop (Nat.ceil (4 / ε))] with n hnUniform hnPos hnLarge
  intro s hs hsSmall t ht
  obtain ⟨hMpos, hMN, hNclose, hMclose⟩ := hnUniform s hs hsSmall t ht
  have hguard : t + DenseGraph.balancedMultipartiteInternalCapacity
      (k - 1) (n - s) ≤ criticalEdgeCount k n := by
    unfold criticalRetainedSupportSelectedCount at hMpos
    omega
  refine ⟨hguard, hMpos, hMN, ?_⟩
  let N := criticalRetainedSupportCapacity k n s
  let M := criticalRetainedSupportSelectedCount k n s t
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hnSq : (0 : ℝ) < (n : ℝ) ^ 2 := by positivity
  have hdist : dist ((N : ℝ) / (n : ℝ) ^ 2, (M : ℝ) / (n : ℝ) ^ 2)
      (b, a) < η := by
    simpa only [Prod.dist_eq, Real.dist_eq, max_lt_iff] using
      And.intro (hNclose.trans hζη) (hMclose.trans hζη)
  have hentropy := hcontrol hdist
  rw [criticalNormalizedBinomialEntropy_at_reference hk, Real.dist_eq] at hentropy
  change |criticalNormalizedBinomialEntropy ((N : ℝ) / (n : ℝ) ^ 2)
      ((M : ℝ) / (n : ℝ) ^ 2) - criticalNaturalEntropyExponent k| < ε / 2 at hentropy
  have hnormalize : criticalNormalizedBinomialEntropy
      ((N : ℝ) / (n : ℝ) ^ 2) ((M : ℝ) / (n : ℝ) ^ 2) =
      DenseGraph.binomialEntropyPerspective N M / (n : ℝ) ^ 2 := by
    rw [criticalNormalizedBinomialEntropy,
      div_div_div_cancel_right₀ hnSq.ne']
    unfold DenseGraph.binomialEntropyPerspective
    ring
  rw [hnormalize] at hentropy
  have hmain : (criticalNaturalEntropyExponent k - ε / 2) * (n : ℝ) ^ 2 ≤
      DenseGraph.binomialEntropyPerspective N M := by
    apply (le_div_iff₀ hnSq).mp
    linarith [(abs_lt.mp hentropy).1]
  have hNle : N ≤ n ^ 2 := by
    have htotal := DenseGraph.balancedCross_add_internal (k - 1) (n - s)
    have hcap : N ≤ (n - s).choose 2 := by
      change DenseGraph.balancedMultipartiteCrossCapacity (k - 1) (n - s) ≤ _
      omega
    exact hcap.trans ((Nat.choose_le_pow (n - s) 2).trans
      (Nat.pow_le_pow_left (Nat.sub_le n s) 2))
  have hlog : Real.log ((N + 1 : ℕ) : ℝ) ≤ 2 * (n : ℝ) := by
    have hNleR : (N : ℝ) ≤ (n : ℝ) ^ 2 := by exact_mod_cast hNle
    have hmono : Real.log ((N + 1 : ℕ) : ℝ) ≤
        Real.log (((n : ℝ) + 1) ^ 2) :=
      Real.log_le_log (by positivity) (by push_cast; nlinarith)
    rw [Real.log_pow] at hmono
    have hlinear := Real.log_le_sub_one_of_pos (show (0 : ℝ) < (n : ℝ) + 1 by positivity)
    norm_num at hmono
    push_cast
    linarith
  have hlarge : 4 / ε ≤ (n : ℝ) :=
    (Nat.le_ceil (4 / ε)).trans (by exact_mod_cast hnLarge)
  have hlinear : (2 : ℝ) * n ≤ (ε / 2) * (n : ℝ) ^ 2 := by
    have hlarge' := (div_le_iff₀ hε).mp hlarge
    nlinarith [mul_le_mul_of_nonneg_right hlarge' hnR.le]
  have hsandwich := DenseGraph.log_choose_lower_binEntropy hMN
  change DenseGraph.binomialEntropyPerspective N M - Real.log ((N + 1 : ℕ) : ℝ) ≤
    Real.log (Nat.choose N M : ℝ) at hsandwich
  change _ ≤ Real.log (Nat.choose N M : ℝ)
  nlinarith

/-- Selected and missing retained cross coordinates give the same reference
slice.  This exact identity is what connects the entropy estimate to the
division-independent missing count in the fine-balance calculation. -/
theorem criticalRetainedSupport_choose_eq_missing
    {k n s t : ℕ}
    (hguard : t + DenseGraph.balancedMultipartiteInternalCapacity
      (k - 1) (n - s) ≤ criticalEdgeCount k n)
    (hfeasible : criticalRetainedSupportSelectedCount k n s t ≤
      criticalRetainedSupportCapacity k n s) :
    Nat.choose (criticalRetainedSupportCapacity k n s)
        (criticalRetainedSupportSelectedCount k n s t) =
      Nat.choose (criticalRetainedSupportCapacity k n s)
        ((n - s).choose 2 + t - criticalEdgeCount k n) := by
  apply Nat.choose_symm_of_eq_add
  have htotal := DenseGraph.balancedCross_add_internal (k - 1) (n - s)
  unfold criticalRetainedSupportSelectedCount criticalRetainedSupportCapacity at *
  omega

/-- Far graphs are negligible relative to every feasible balanced retained
slice, even after multiplying their number by the number of all divisions.
The cut radius is fixed first; the positive sparse-size radius is then
chosen uniformly in both the sparse set and its prescribed graph. -/
theorem eventually_criticalFarPairs_le_retainedSupportReference
    (k : ℕ) (hk : 3 ≤ k) (τ : ℝ) (hτ : 0 < τ) :
    ∃ δ c : ℝ, 0 < δ ∧ 0 < c ∧ ∀ᶠ n : ℕ in atTop,
      ∀ s : ℕ, s ≤ n → (s : ℝ) ≤ δ * n →
      ∀ t : ℕ, t ≤ Nat.choose s 2 →
        ((k ^ n : ℕ) : ℝ) * ((criticalFarGraphFinset k hk n τ).card : ℝ) ≤
          (Nat.choose (criticalRetainedSupportCapacity k n s)
            ((n - s).choose 2 + t - criticalEdgeCount k n) : ℝ) *
              Real.exp (-(c * (n : ℝ) ^ 2)) := by
  obtain ⟨c, hc, hfar⟩ := eventually_criticalFarPairs_le_reference_of_entropy k hk τ hτ
  obtain ⟨δ, hδ, hreference⟩ := eventually_criticalRetainedSupport_log_choose_lower
    k hk (show 0 < 2 * c by positivity)
  refine ⟨δ, c, hδ, hc, ?_⟩
  filter_upwards [hfar, hreference] with n hnFar hnReference
  intro s hs hsSmall t ht
  obtain ⟨hguard, _hpos, hfeasible, hlower⟩ := hnReference s hs hsSmall t ht
  have hchoosePos : (0 : ℝ) < Nat.choose (criticalRetainedSupportCapacity k n s)
      (criticalRetainedSupportSelectedCount k n s t) := by
    exact_mod_cast Nat.choose_pos hfeasible
  have hB := Real.exp_le_exp.mpr hlower
  rw [Real.exp_log hchoosePos] at hB
  have hbound := hnFar _ hB
  rw [criticalRetainedSupport_choose_eq_missing hguard hfeasible] at hbound
  exact hbound

end InducedStars
