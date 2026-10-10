import InducedStars.Structure.Subcritical.BalancedRetainedReference
import InducedStars.Structure.Subcritical.DistinguishedReference
import DenseGraph.FiniteModels.ProportionalAllocation

/-!
# Finite-density distinguished reference parameters

Paper: `eqn:sub-gamma-b-K1k` and the reference part of
`lemma:clean-retained-comparison-K1k`. The density is calculated from the
actual finite target and remainder edge counts, never replaced by a
presumed `O(1/n)` error of an arbitrary density-convergent sequence.
-/

noncomputable section
open Filter Finset Set Topology
open scoped Classical BigOperators
namespace InducedStars

def subcriticalReferenceDensity (n m b : ℕ) : ℝ :=
  ((m : ℝ) - b) / (n.choose 2 : ℝ)

def subcriticalReferenceMass (k n m b : ℕ) : ℝ :=
  Real.sqrt (subcriticalReferenceDensity n m b / gammaK k)

/-- Explicit integer rule: no unspecified bounded adjustment. -/
def subcriticalReferenceSupportSize (k n m b : ℕ) : ℕ :=
  Nat.floor (subcriticalReferenceMass k n m b * n)

theorem subcriticalReferenceMass_sq {k n m b : ℕ} (hk : 3 ≤ k)
    (hgamma : 0 ≤ subcriticalReferenceDensity n m b) :
    subcriticalReferenceMass k n m b ^ 2 =
      subcriticalReferenceDensity n m b / gammaK k :=
  Real.sq_sqrt (div_nonneg hgamma (gammaK_pos hk).le)

theorem subcriticalReferenceMass_mem_Ioo {k n m b : ℕ} (hk : 3 ≤ k)
    (hgamma : subcriticalReferenceDensity n m b ∈ Ioo (0 : ℝ) (gammaK k)) :
    subcriticalReferenceMass k n m b ∈ Ioo (0 : ℝ) 1 := by
  constructor
  · exact Real.sqrt_pos.2 (div_pos hgamma.1 (gammaK_pos hk))
  · change Real.sqrt _ < 1
    apply (Real.sqrt_lt' (by norm_num : (0 : ℝ) < 1)).2
    simpa using ((div_lt_one (gammaK_pos hk)).2 hgamma.2)

theorem subcriticalReferenceSupportSize_floor_bounds (k n m b : ℕ) :
    (subcriticalReferenceSupportSize k n m b : ℝ) ≤ subcriticalReferenceMass k n m b * n ∧
      subcriticalReferenceMass k n m b * n <
        (subcriticalReferenceSupportSize k n m b : ℝ) + 1 :=
  ⟨Nat.floor_le (by unfold subcriticalReferenceMass; positivity), Nat.lt_floor_add_one _⟩

theorem subcriticalReferenceSupportSize_le {k n m b : ℕ}
    (hmu : subcriticalReferenceMass k n m b ≤ 1) :
    subcriticalReferenceSupportSize k n m b ≤ n := by
  have hf := (subcriticalReferenceSupportSize_floor_bounds k n m b).1
  have hn : (0 : ℝ) ≤ n := by positivity
  exact_mod_cast (hf.trans (by nlinarith : subcriticalReferenceMass k n m b * n ≤ n))

/-- A uniform compact-band estimate for the actual finite density. -/
theorem subcriticalReferenceDensity_bounds {n m b : ℕ} {a c B : ℝ}
    (hn : 2 ≤ n) (hB : 0 ≤ B) (hb : (b : ℝ) ≤ B * (n : ℝ)^2)
    (hmlo : a + 4 * B ≤ (m : ℝ) / (n.choose 2 : ℝ))
    (hmhi : (m : ℝ) / (n.choose 2 : ℝ) ≤ c) :
    a ≤ subcriticalReferenceDensity n m b ∧ subcriticalReferenceDensity n m b ≤ c := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hnm : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  have hN : (0 : ℝ) < (n.choose 2 : ℝ) := by
    rw [Nat.cast_choose_two]
    positivity
  have hNlo : (n : ℝ)^2 / 4 ≤ (n.choose 2 : ℝ) := by
    rw [Nat.cast_choose_two]
    nlinarith
  have hbr : (b : ℝ) / (n.choose 2 : ℝ) ≤ 4 * B := by
    apply (div_le_iff₀ hN).2
    nlinarith
  unfold subcriticalReferenceDensity
  rw [sub_div]
  constructor
  · linarith
  · have : (0 : ℝ) ≤ (b : ℝ) / (n.choose 2 : ℝ) := by positivity
    linarith

/-- Uniformity over all allowed `b`, with no rate imposed on convergence
of the original edge density. -/
theorem eventually_subcriticalReferenceDensity_band {k : ℕ} (hk : 3 ≤ k)
    {gamma B : ℝ} (hg : gamma ∈ Ioo (0 : ℝ) (gammaK k))
    (hB : 0 ≤ B) (hsmall : 16 * B ≤ gamma)
    (m : ℕ → ℕ) (hm : HasAsymptoticEdgeDensity m gamma) :
    ∀ᶠ n : ℕ in atTop, ∀ b : ℕ, (b : ℝ) ≤ B * (n : ℝ)^2 →
      gamma / 2 ≤ subcriticalReferenceDensity n (m n) b ∧
        subcriticalReferenceDensity n (m n) b ≤ (gamma + gammaK k) / 2 := by
  have hband := hm.eventually (Ioo_mem_nhds
    (show 3 * gamma / 4 < gamma by linarith [hg.1])
    (show gamma < (gamma + gammaK k) / 2 by linarith [hg.2]))
  filter_upwards [hband, eventually_ge_atTop 2] with n hn hn2
  intro b hb
  apply subcriticalReferenceDensity_bounds hn2 hB hb
  · have hlo : 3 * gamma / 4 < (m n : ℝ) / (n.choose 2 : ℝ) := hn.1
    linarith
  · exact hn.2.le

/-- Balanced clique plus `pK` cross capacity has its exact quadratic
leading term, with a uniform finite rounding error. -/
theorem balancedRetained_expectedCapacity_error {k q : ℕ} (hk : 3 ≤ k) :
    |(DenseGraph.balancedMultipartiteInternalCapacity (k - 1) q : ℝ) +
        pK k * DenseGraph.balancedMultipartiteCrossCapacity (k - 1) q -
        (gammaK k * (q : ℝ)^2 / 2 - q / 2)| ≤ (2 : ℝ) * (k - 1 : ℕ) := by
  have hr : 0 < k - 1 := by omega
  have hp := pK_pos (by omega : 2 ≤ k)
  have hp1 := pK_lt_one (by omega : 2 ≤ k)
  have hi := DenseGraph.balancedMultipartiteInternalCapacity_approx (q := q) hr
  have ha := DenseGraph.balancedMultipartiteCrossCapacity_approx (q := q) hr
  have hid :
      (DenseGraph.balancedMultipartiteInternalCapacity (k - 1) q : ℝ) +
        pK k * DenseGraph.balancedMultipartiteCrossCapacity (k - 1) q -
        (gammaK k * (q : ℝ)^2 / 2 - q / 2) =
      ((DenseGraph.balancedMultipartiteInternalCapacity (k - 1) q : ℝ) -
        ((q : ℝ)^2 / (2 * (k - 1 : ℕ)) - q / 2)) +
      pK k * ((DenseGraph.balancedMultipartiteCrossCapacity (k - 1) q : ℝ) -
        (((k - 1 : ℕ) : ℝ) - 1) * (q : ℝ)^2 / (2 * (k - 1 : ℕ))) := by
    have hg := gammaK_mul_denominator k hk
    have hsub : ((k - 1 : ℕ) : ℝ) - 1 = (k - 2 : ℕ) := by
      norm_num [Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_sub (by omega : 2 ≤ k)]
      ring
    rw [hsub]
    field_simp
    nlinarith [hg]
  rw [hid]
  calc
    _ ≤ |(DenseGraph.balancedMultipartiteInternalCapacity (k - 1) q : ℝ) -
          ((q : ℝ)^2 / (2 * (k - 1 : ℕ)) - q / 2)| +
        |pK k * ((DenseGraph.balancedMultipartiteCrossCapacity (k - 1) q : ℝ) -
          (((k - 1 : ℕ) : ℝ) - 1) * (q : ℝ)^2 / (2 * (k - 1 : ℕ)))| := abs_add_le _ _
    _ ≤ ((k - 1 : ℕ) : ℝ) + pK k * (k - 1 : ℕ) := by
      rw [abs_mul, abs_of_pos hp]
      exact add_le_add hi (mul_le_mul_of_nonneg_left ha hp.le)
    _ ≤ _ := by nlinarith [show (0 : ℝ) ≤ (k - 1 : ℕ) by positivity]

/-- Finite rounding error for a floor-sized reference. The target is the
exact finite density times `choose n 2`, not its limiting density. -/
theorem balancedRetained_floor_expected_error {k n q : ℕ} (hk : 3 ≤ k)
    (hn : 1 ≤ n) {mu t : ℝ} (hmu : mu ∈ Icc (0 : ℝ) 1)
    (hflo : (q : ℝ) ≤ mu * n) (hfhi : mu * n ≤ (q : ℝ) + 1)
    (ht : 2 * t = gammaK k * mu ^ 2 * n * (n - 1)) :
    |t - ((DenseGraph.balancedMultipartiteInternalCapacity (k - 1) q : ℝ) +
      pK k * DenseGraph.balancedMultipartiteCrossCapacity (k - 1) q)| ≤ (4 : ℝ) * k * n := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hq0 : (0 : ℝ) ≤ q := by positivity
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hqn : (q : ℝ) ≤ n := hflo.trans (by nlinarith [hmu.2])
  have hsq0 : 0 ≤ (mu * n)^2 - (q : ℝ)^2 := by nlinarith [hmu.1]
  have hsqhi : (mu * n)^2 - (q : ℝ)^2 ≤ 2 * n := by
    have hprod := mul_nonneg (show 0 ≤ (q : ℝ) + 1 - mu * n by linarith)
      (show 0 ≤ mu * n + q from add_nonneg (mul_nonneg hmu.1 hn0) hq0)
    nlinarith [hmu.2]
  have hmuSq : mu^2 ≤ 1 := by nlinarith [hmu.1, hmu.2]
  have hlow : -(n : ℝ) ≤ mu^2 * n * (n - 1) - (q : ℝ)^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hmuSq) hn0]
  have hhigh : mu^2 * n * (n - 1) - (q : ℝ)^2 ≤ 2 * n := by
    nlinarith [mul_nonneg (sq_nonneg mu) hn0]
  have hg0 := (gammaK_pos hk).le
  have hg1 := (gammaK_lt_one hk).le
  have hmullo := mul_le_mul_of_nonneg_left hlow hg0
  have hmulhi := mul_le_mul_of_nonneg_left hhigh hg0
  have hgn : gammaK k * n ≤ (n : ℝ) := by nlinarith
  have hround : |t - (gammaK k * (q : ℝ)^2 / 2 - q / 2)| ≤ (2 : ℝ) * n := by
    rw [abs_le]
    constructor <;> nlinarith
  have hc := balancedRetained_expectedCapacity_error (q := q) hk
  have htri := abs_sub_le t (gammaK k * (q : ℝ)^2 / 2 - q / 2)
    ((DenseGraph.balancedMultipartiteInternalCapacity (k - 1) q : ℝ) +
      pK k * DenseGraph.balancedMultipartiteCrossCapacity (k - 1) q)
  rw [abs_sub_comm (gammaK k * (q : ℝ)^2 / 2 - q / 2)] at htri
  have hrk : ((k - 1 : ℕ) : ℝ) ≤ k := by exact_mod_cast Nat.sub_le k 1
  have hkR : (3 : ℝ) ≤ k := by exact_mod_cast hk
  nlinarith [mul_nonneg (show 0 ≤ (k : ℝ) - 1 by linarith)
    (show 0 ≤ (n : ℝ) - 1 by linarith)]

theorem subcriticalReference_exact_target {k n m b : ℕ} (hk : 3 ≤ k)
    (hn : 2 ≤ n) (hgamma : 0 ≤ subcriticalReferenceDensity n m b) :
    2 * ((m : ℝ) - b) = gammaK k * subcriticalReferenceMass k n m b ^ 2 * n * (n - 1) := by
  rw [subcriticalReferenceMass_sq hk hgamma, mul_div_cancel₀ _ (gammaK_pos hk).ne']
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hnm : (n : ℝ) - 1 ≠ 0 := by linarith
  have hnz : (n : ℝ) ≠ 0 := by linarith
  unfold subcriticalReferenceDensity
  rw [Nat.cast_choose_two]
  field_simp [hnm, hnz]
  <;> ring

theorem subcriticalReference_expectedCapacity_error {k n m b : ℕ} (hk : 3 ≤ k)
    (hn : 2 ≤ n) (hgamma : subcriticalReferenceDensity n m b ∈ Ioo (0 : ℝ) (gammaK k)) :
    |((m : ℝ) - b) -
      ((DenseGraph.balancedMultipartiteInternalCapacity (k - 1)
          (subcriticalReferenceSupportSize k n m b) : ℝ) +
        pK k * DenseGraph.balancedMultipartiteCrossCapacity (k - 1)
          (subcriticalReferenceSupportSize k n m b))| ≤ (4 : ℝ) * k * n := by
  have hmu := subcriticalReferenceMass_mem_Ioo hk hgamma
  have hf := subcriticalReferenceSupportSize_floor_bounds k n m b
  exact balancedRetained_floor_expected_error hk (by omega) ⟨hmu.1.le, hmu.2.le⟩
    hf.1 hf.2.le (subcriticalReference_exact_target hk hn hgamma.1.le)

end InducedStars
