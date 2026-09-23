import InducedStars.Structure.Subcritical.RetainedMassConcentration

/-!
# An explicit finite error budget for retained mass

All constants in the near-equality argument are chosen before the candidate
representation and before its finite division. This budget controls quadratic omitted mass, without asserting small omitted total vertex length.
-/

noncomputable section
open Filter Set
open scoped Topology
namespace InducedStars

/-- The retained length error when both scalar input errors are at most t. -/
def subcriticalRetainedMassLengthError (k : ℕ) (mu t : ℝ) : ℝ :=
  t + (k - 1 : ℕ) * t / mu

/-- Upper mass if the dominant retained core were to have order at least k. -/
def subcriticalRetainedMassOrderBound (k : ℕ) (mu t : ℝ) : ℝ :=
  (mu + t) ^ 2 / ((k - 1 : ℕ) + 1 : ℝ) +
    (2 * t + (k - 1 : ℕ) * t / mu) ^ 2 / (k - 1 : ℕ) + t

/-- A positive near-equality tolerance exists for every desired positive
cut-error budget. Its choice involves only k, mu, and the desired error. -/
theorem exists_subcriticalRetainedMassTolerance
    {k : ℕ} (hk : 3 ≤ k) {mu epsilon : ℝ}
    (hmu : 0 < mu) (hepsilon : 0 < epsilon) :
    ∃ t : ℝ, 0 < t ∧ t < 1 ∧ (k - 1 : ℕ) * t < mu ^ 2 ∧
      subcriticalRetainedMassOrderBound k mu t < mu ^ 2 / (k - 1 : ℕ) ∧
      (4 * (k - 1 : ℕ) + 2) * subcriticalRetainedMassLengthError k mu t < epsilon := by
  have hr : (0 : ℝ) < (k - 1 : ℕ) := by exact_mod_cast (show 0 < k - 1 by omega)
  have hgap0 : subcriticalRetainedMassOrderBound k mu 0 < mu ^ 2 / (k - 1 : ℕ) := by
    simp only [subcriticalRetainedMassOrderBound, add_zero, mul_zero, zero_div,
      zero_add, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
    exact div_lt_div_of_pos_left (sq_pos_of_pos hmu) hr (by linarith)
  have hc : ContinuousAt (subcriticalRetainedMassOrderBound k mu) 0 := by
    unfold subcriticalRetainedMassOrderBound
    fun_prop
  have he : ContinuousAt
      (fun t ↦ (4 * (k - 1 : ℕ) + 2) * subcriticalRetainedMassLengthError k mu t) 0 := by
    unfold subcriticalRetainedMassLengthError
    fun_prop
  have h1 : ∀ᶠ t : ℝ in 𝓝 0, t < 1 := gt_mem_nhds zero_lt_one
  have h2 : ∀ᶠ t : ℝ in 𝓝 0, (k - 1 : ℕ) * t < mu ^ 2 := by
    have hc2 : ContinuousAt (fun t : ℝ ↦ (k - 1 : ℕ) * t) 0 := by fun_prop
    exact hc2.eventually (gt_mem_nhds (by simpa using sq_pos_of_pos hmu))
  have h3 : ∀ᶠ t : ℝ in 𝓝 0,
      subcriticalRetainedMassOrderBound k mu t < mu ^ 2 / (k - 1 : ℕ) :=
    hc.eventually (gt_mem_nhds hgap0)
  have h4 : ∀ᶠ t : ℝ in 𝓝 0,
      (4 * (k - 1 : ℕ) + 2) * subcriticalRetainedMassLengthError k mu t < epsilon := by
    exact he.eventually (gt_mem_nhds (by
      simpa [subcriticalRetainedMassLengthError] using hepsilon))
  have hall := h1.and (h2.and (h3.and h4))
  obtain ⟨d, hd, hball⟩ := Metric.mem_nhds_iff.mp hall
  have hmid : d / 2 ∈ Metric.ball (0 : ℝ) d := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos (by positivity)]
    linarith
  exact ⟨d / 2, by positivity, hball hmid⟩

/-- Taking eta at most t/4 and an explicit natural cutoff makes the omitted
quadratic mass at most t, uniformly over every admissible sequence. -/
theorem subcriticalOmittedBlockMass_le_tolerance
    {k : ℕ} (L : AdmissibleBlockSequence k) {eta t : ℝ} {R₀ : ℕ}
    (heta : 0 < eta) (ht : 0 < t) (hetaSmall : eta ≤ t / 4)
    (hR : Nat.ceil (2 / t) ≤ R₀) : subcriticalOmittedBlockMass L eta R₀ ≤ t := by
  have hr : (0 : ℝ) < ((R₀ + 1 : ℕ) : ℝ) := by positivity
  have hceil : 2 / t ≤ (R₀ : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hR)
  have hprod : 2 ≤ (R₀ : ℝ) * t := (div_le_iff₀ ht).mp hceil
  have hinv : 1 / ((R₀ + 1 : ℕ) : ℝ) ≤ t / 2 := by
    apply (div_le_iff₀ hr).mpr
    push_cast
    nlinarith
  exact (subcriticalOmittedBlockMass_le L heta R₀).trans (by linarith)

end InducedStars
