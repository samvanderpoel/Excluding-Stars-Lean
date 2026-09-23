import InducedStars.Structure.Subcritical.RetainedReferenceEntropy
import InducedStars.Structure.Subcritical.DistinguishedReferenceUniform

/-!
# Uniform retained-key partition-function comparison

Paper: `lemma:clean-retained-comparison-K1k`. The retained key is
arbitrary, the balanced comparison key uses the exact density of `m-b`,
and the loss is explicitly linear plus logarithmic in the graph order.
-/

noncomputable section
open Filter Finset Set Topology
open scoped BigOperators Classical
namespace InducedStars

/-- The finite graphon diagonal reserve follows uniformly from a compact
band for the actual finite density. -/
theorem subcriticalReferenceDensity_entropy_reserve {k n m b : ℕ}
    (hn : 2 ≤ n) {gUpper : ℝ}
    (hg : 0 < subcriticalReferenceDensity n m b)
    (hgu : subcriticalReferenceDensity n m b ≤ gUpper)
    (hnGap : 1 ≤ (gammaK k - gUpper) * n) :
    b < m ∧ 2 * ((m : ℝ) - b) + n ≤ gammaK k * (n : ℝ)^2 := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hchoose : (0 : ℝ) < Nat.choose n 2 := by exact_mod_cast Nat.choose_pos hn
  have ht : 0 < (m : ℝ) - b :=
    ((div_pos_iff.mp hg).resolve_right (fun h ↦ (not_lt_of_ge hchoose.le) h.2)).1
  have hbm : b < m := by exact_mod_cast (sub_pos.mp ht)
  have hupper := (div_le_iff₀ hchoose).mp hgu
  have hgu0 : 0 < gUpper := hg.trans_le hgu
  rw [Nat.cast_choose_two] at hupper
  have hmul := mul_le_mul_of_nonneg_right hnGap (show (0 : ℝ) ≤ n by positivity)
  constructor
  · exact hbm
  · nlinarith [mul_nonneg hgu0.le (show (0 : ℝ) ≤ n by positivity)]

/-- Entropy loss from one arbitrary bounded-index key to the actual balanced
reference key. No asymptotic rate for `m(n)` is assumed. -/
theorem eventually_retainedKeyPartitionFunction_le_reference
    {k : ℕ} (hk : 3 ≤ k) (Q : ℕ) {gLower gUpper delta : ℝ}
    (hgLower : 0 < gLower) (hband : gLower ≤ gUpper)
    (hgUpper : gUpper < gammaK k) (hd : 0 < delta)
    (hdp : delta ≤ pK k / 2) (hdq : delta ≤ (1 - pK k) / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop, ∀ m b : ℕ,
      gLower ≤ subcriticalReferenceDensity n m b →
      subcriticalReferenceDensity n m b ≤ gUpper →
      ∀ K : SubcriticalRetainedKey k (Fin n), Fintype.card K.ActiveIndex ≤ Q →
        (retainedKeyPartitionFunction K m delta (b : ℤ) : ℝ) ≤
          (retainedKeyPartitionFunction (subcriticalDistinguishedReferenceKey hk n m b)
            m delta (b : ℤ) : ℝ) *
            Real.exp (C * n + C * Real.log ((n : ℝ) + 1)) := by
  obtain ⟨C₀, hC₀, hreference⟩ := eventually_subcriticalReference_fiber
    hk hgLower hband hgUpper hd hdp hdq
  let C : ℝ := subcriticalRetainedEntropySlope k / 2 +
    subcriticalReferenceEntropyLinearConstant k + 2 * Q + 2 * (k : ℝ)^2 + 1
  have hs := subcriticalRetainedEntropySlope_nonneg hk
  have hr := subcriticalReferenceEntropyLinearConstant_nonneg hk
  have hC : 0 < C := by dsimp [C]; positivity
  have hgap : 0 < gammaK k - gUpper := sub_pos.mpr hgUpper
  have hlarge : ∀ᶠ n : ℕ in atTop, 2 ≤ n ∧ 1 ≤ (gammaK k - gUpper) * n := by
    filter_upwards [eventually_ge_atTop 2,
      (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop).eventually
        (eventually_ge_atTop (1 / (gammaK k - gUpper)))] with n hn hnR
    exact ⟨hn, by have h := mul_le_mul_of_nonneg_left hnR hgap.le
                  rw [mul_one_div_cancel hgap.ne'] at h
                  exact h⟩
  refine ⟨C, hC, ?_⟩
  filter_upwards [hreference, hlarge] with n href hn
  intro m b hgl hgu K hQ
  have hgamma : subcriticalReferenceDensity n m b ∈ Ioo (0 : ℝ) (gammaK k) :=
    ⟨hgLower.trans_le hgl, hgu.trans_lt hgUpper⟩
  obtain ⟨hrq, hqn, v, hv, hvdens, hvcount, hrefpos, hremsize⟩ := href m b hgl hgu
  have hlower := balancedRetainedReferencePartitionFunction_lower hk (by omega) hrq hqn v hv
    (subcriticalReference_expectedCapacity_error hk hn.1 hgamma) hvcount
  have hkey : subcriticalDistinguishedReferenceKey hk n m b =
      balancedRetainedReferenceKey hk hrq hqn := by
    unfold subcriticalDistinguishedReferenceKey
    rw [dif_pos ⟨hrq, hqn⟩]
  rw [← hkey] at hlower
  obtain ⟨hbm, hcap⟩ := subcriticalReferenceDensity_entropy_reserve hn.1 hgamma.1 hgu hn.2
  have hupper := retainedKeyPartitionFunction_le_exp_entropy hk (by omega) K hbm hcap hQ delta
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hlog0 : 0 ≤ Real.log ((n : ℝ) + 1) := Real.log_nonneg (by linarith)
  have herr : subcriticalRetainedEntropySlope k / 2 * n +
      (2 * Q : ℕ) * Real.log ((n : ℝ) + 1) +
      subcriticalReferenceEntropyLinearConstant k * n +
      2 * (k : ℝ)^2 * Real.log ((n : ℝ) + 1) ≤
        C * n + C * Real.log ((n : ℝ) + 1) := by
    have h₁ : subcriticalRetainedEntropySlope k / 2 +
        subcriticalReferenceEntropyLinearConstant k ≤ C := by
      dsimp [C]
      have hq : (0 : ℝ) ≤ Q := by positivity
      nlinarith [sq_nonneg (k : ℝ)]
    have h₂ : (2 * Q : ℕ) + 2 * (k : ℝ)^2 ≤ C := by
      dsimp [C]
      push_cast
      linarith
    have h₃ := mul_le_mul_of_nonneg_right h₁ hn0
    have h₄ := mul_le_mul_of_nonneg_right h₂ hlog0
    push_cast at h₃ h₄ ⊢
    nlinarith
  apply hupper.trans
  calc
    _ ≤ Real.exp (subcriticalRetainedEntropySlope k * ((m : ℝ) - b) -
          subcriticalReferenceEntropyLinearConstant k * n -
          2 * (k : ℝ)^2 * Real.log ((n : ℝ) + 1)) *
        Real.exp (C * n + C * Real.log ((n : ℝ) + 1)) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      linarith
    _ ≤ _ := mul_le_mul_of_nonneg_right hlower (Real.exp_pos _).le

end InducedStars
