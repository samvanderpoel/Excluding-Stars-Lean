import DenseGraph.FiniteModels.FixedCardinalityBlocks
import InducedStars.Structure.Supercritical.CountingSetup
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

/-!
# Exponential overhead bounds for the supercritical medium-degree count

This module isolates the elementary asymptotic factors which are absorbed by
the quadratic Janson penalty.  The statements keep every finite factor
explicit: no `O`- or `o`-notation occurs in their public interfaces.
-/

noncomputable section

open Filter Finset Set
open scoped BigOperators

namespace InducedStars

/-! ## Fixed-degree polynomial factors -/

/-- A fixed power of `n² + 1` is eventually smaller than an arbitrarily
small positive quadratic exponential. -/
theorem eventually_nsq_add_one_pow_le_exp (r : ℕ) {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop,
      ((((n ^ 2 + 1) ^ r : ℕ) : ℝ)) ≤ Real.exp (c * (n : ℝ) ^ 2) := by
  have hlittle :
      (fun x : ℝ ↦ (2 : ℝ) ^ r * x ^ (2 * r)) =o[atTop]
        (fun x : ℝ ↦ Real.exp (c * x)) :=
    (isLittleO_pow_exp_pos_mul_atTop (2 * r) hc).const_mul_left
      ((2 : ℝ) ^ r)
  have hgrowth := (hlittle.bound (c := 1) zero_lt_one).natCast_atTop
  filter_upwards [hgrowth, eventually_ge_atTop 1] with n hnGrowth hn
  have hbase : (n : ℝ) ^ 2 + 1 ≤ 2 * (n : ℝ) ^ 2 := by
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith [sq_nonneg ((n : ℝ) - 1)]
  have hpoly :
      (2 : ℝ) ^ r * (n : ℝ) ^ (2 * r) ≤
        Real.exp (c * (n : ℝ)) := by
    simpa [Real.norm_eq_abs, abs_of_nonneg] using hnGrowth
  have hexp : Real.exp (c * (n : ℝ)) ≤
      Real.exp (c * (n : ℝ) ^ 2) := by
    apply Real.exp_le_exp.mpr
    have hnSq : (n : ℝ) ≤ (n : ℝ) ^ 2 := by
      have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
      nlinarith
    exact mul_le_mul_of_nonneg_left hnSq hc.le
  calc
    ((((n ^ 2 + 1) ^ r : ℕ) : ℝ)) = ((n : ℝ) ^ 2 + 1) ^ r := by simp
    _ ≤ (2 * (n : ℝ) ^ 2) ^ r := by gcongr
    _ = (2 : ℝ) ^ r * (n : ℝ) ^ (2 * r) := by
      rw [mul_pow, ← pow_mul]
    _ ≤ Real.exp (c * (n : ℝ)) := hpoly
    _ ≤ Real.exp (c * (n : ℝ) ^ 2) := hexp

/-- Uniform eventual exponential absorption of the exact-cardinality
conditioning factor for any fixed finite block index type. -/
theorem eventually_fixedCardinality_conditioningFactor_le_exp
    {I Ω : Type*} [Fintype I] [DecidableEq I]
    [Fintype Ω] [DecidableEq Ω]
    (M : ℕ → DenseGraph.FixedCardinalityBlockModel I Ω)
    (hblock : ∀ n i, ((M n).block i).card ≤ n ^ 2)
    {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop,
      (M n).conditioningFactor ≤ Real.exp (c * (n : ℝ) ^ 2) := by
  filter_upwards
      [eventually_nsq_add_one_pow_le_exp (Fintype.card I) hc]
      with n hn
  have hn' :
      (((n ^ 2 + 1 : ℕ) : ℝ)) ^ Fintype.card I ≤
        Real.exp (c * (n : ℝ) ^ 2) := by
    simpa using hn
  exact ((M n).conditioningFactor_le_nsq_pow n (hblock n)).trans hn'

/-! ## Vertex, incident-pattern, and profile factors -/

/-- The explicit auxiliary factor for choosing a witness vertex, a
distinguished part, its incident pattern, and a coarse cross-edge profile. -/
def supercriticalMediumAuxiliaryFactor (k n : ℕ) : ℕ :=
  n * (k - 1) * 2 ^ n * (n ^ 2 + 1) ^ ((k - 1) ^ 2)

private theorem eventually_mediumAuxiliaryPolynomial_le_exp
    (k : ℕ) {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop,
      (((n * (k - 1) * (n ^ 2 + 1) ^ ((k - 1) ^ 2) : ℕ) : ℝ)) ≤
        Real.exp (c * (n : ℝ) ^ 2) := by
  let r := (k - 1) ^ 2
  filter_upwards
      [eventually_nsq_add_one_pow_le_exp (r + 2) hc,
        eventually_ge_atTop (max k 1)] with n hnexp hn
  have hn1 : 1 ≤ n := le_trans (Nat.le_max_right _ _) hn
  have hkn : k ≤ n := le_trans (Nat.le_max_left _ _) hn
  have hnbase : n ≤ n ^ 2 + 1 := by nlinarith
  have hkbase : k - 1 ≤ n ^ 2 + 1 := by omega
  have hnat :
      n * (k - 1) * (n ^ 2 + 1) ^ r ≤ (n ^ 2 + 1) ^ (r + 2) := by
    calc
      n * (k - 1) * (n ^ 2 + 1) ^ r ≤
          (n ^ 2 + 1) * (n ^ 2 + 1) * (n ^ 2 + 1) ^ r := by
        gcongr
      _ = (n ^ 2 + 1) ^ (r + 2) := by
        simp [pow_add, pow_two, mul_assoc, mul_left_comm, mul_comm]
  have hreal :
      (((n * (k - 1) * (n ^ 2 + 1) ^ r : ℕ) : ℝ)) ≤
        ((((n ^ 2 + 1) ^ (r + 2) : ℕ) : ℝ)) := by
    exact_mod_cast hnat
  exact hreal.trans hnexp

/-- The linear factor `2ⁿ` is eventually absorbed by every positive
quadratic exponential. -/
theorem eventually_two_pow_le_exp_quadratic {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop,
      (((2 ^ n : ℕ) : ℝ)) ≤ Real.exp (c * (n : ℝ) ^ 2) := by
  have htend : Tendsto (fun n : ℕ ↦ c * (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop hc
  have hlinear : ∀ᶠ n : ℕ in atTop, Real.log 2 ≤ c * (n : ℝ) :=
    htend.eventually (eventually_ge_atTop (Real.log 2))
  filter_upwards [hlinear, eventually_ge_atTop 1] with n hnlog hn
  calc
    (((2 ^ n : ℕ) : ℝ)) = (2 : ℝ) ^ n := by norm_num
    _ = Real.exp ((n : ℝ) * Real.log 2) := by
      rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    _ ≤ Real.exp (c * (n : ℝ) ^ 2) := by
      apply Real.exp_le_exp.mpr
      have hnnonneg : (0 : ℝ) ≤ n := by positivity
      have hnSq : (n : ℝ) ≤ (n : ℝ) ^ 2 := by
        have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
        nlinarith
      calc
        (n : ℝ) * Real.log 2 ≤ (n : ℝ) * (c * (n : ℝ)) :=
          mul_le_mul_of_nonneg_left hnlog hnnonneg
        _ = c * (n : ℝ) ^ 2 := by ring

/-- The complete explicit vertex/part/incident-pattern/profile factor is
eventually smaller than any prescribed positive quadratic exponential. -/
theorem eventually_supercriticalMediumAuxiliaryFactor_le_exp
    (k : ℕ) {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop,
      (supercriticalMediumAuxiliaryFactor k n : ℝ) ≤
        Real.exp (c * (n : ℝ) ^ 2) := by
  have hc2 : 0 < c / 2 := half_pos hc
  filter_upwards
      [eventually_mediumAuxiliaryPolynomial_le_exp k hc2,
        eventually_two_pow_le_exp_quadratic hc2] with n hpoly htwo
  have hnonnegPoly :
      0 ≤ (((n * (k - 1) * (n ^ 2 + 1) ^ ((k - 1) ^ 2) : ℕ) : ℝ)) := by
    positivity
  have hnonnegTwo : 0 ≤ (((2 ^ n : ℕ) : ℝ)) := by positivity
  calc
    (supercriticalMediumAuxiliaryFactor k n : ℝ) =
        (((n * (k - 1) * (n ^ 2 + 1) ^ ((k - 1) ^ 2) : ℕ) : ℝ)) *
          (((2 ^ n : ℕ) : ℝ)) := by
      simp [supercriticalMediumAuxiliaryFactor]
      ring
    _ ≤ Real.exp ((c / 2) * (n : ℝ) ^ 2) *
        Real.exp ((c / 2) * (n : ℝ) ^ 2) :=
      mul_le_mul hpoly htwo hnonnegTwo (Real.exp_nonneg _)
    _ = Real.exp (c * (n : ℝ) ^ 2) := by
      rw [← Real.exp_add]
      congr 1
      ring

/-- The same bound with the actual cardinality of any profile window in
place of its coarse polynomial majorant. -/
theorem eventually_supercriticalMediumProfileWindowOverhead_le_exp
    (k : ℕ) {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop, ∀ (D : SupercriticalDivision k (Fin n))
      (m budget : ℕ) (rho delta : ℝ),
      (((n * (k - 1) * 2 ^ n *
          (supercriticalProfileWindowFinset D m rho delta budget).card : ℕ) : ℝ)) ≤
        Real.exp (c * (n : ℝ) ^ 2) := by
  filter_upwards [eventually_supercriticalMediumAuxiliaryFactor_le_exp k hc]
    with n hn D m budget rho delta
  have hwindow := card_supercriticalProfileWindowFinset_le_coarse
    D m rho delta budget
  have hwindow' :
      (supercriticalProfileWindowFinset D m rho delta budget).card ≤
        (n ^ 2 + 1) ^ ((k - 1) ^ 2) := by
    simpa using hwindow
  have hnat :
      n * (k - 1) * 2 ^ n *
          (supercriticalProfileWindowFinset D m rho delta budget).card ≤
        supercriticalMediumAuxiliaryFactor k n := by
    unfold supercriticalMediumAuxiliaryFactor
    exact Nat.mul_le_mul_left (n * (k - 1) * 2 ^ n) hwindow'
  exact (by exact_mod_cast hnat :
    (((n * (k - 1) * 2 ^ n *
        (supercriticalProfileWindowFinset D m rho delta budget).card : ℕ) : ℝ)) ≤
      (supercriticalMediumAuxiliaryFactor k n : ℝ)).trans hn

/-! ## Combined-defect pattern entropy -/

/-- Hamming-ball volume is monotone in its radius. -/
theorem hammingBallVolume_mono_right {N r s : ℕ} (hrs : r ≤ s) :
    hammingBallVolume N r ≤ hammingBallVolume N s := by
  unfold hammingBallVolume
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro j hj
    simp only [Finset.mem_range] at hj ⊢
    omega
  · intro j _hj _hnot
    positivity

/-- For `n ≥ 3`, a radius of `⌊εn²⌋` is bounded by the standard fractional
radius with parameter `3ε` relative to `n.choose 2`. -/
theorem floor_square_le_fractionalEditRadius_three_mul
    {epsilon : ℝ} (hepsilon : 0 ≤ epsilon) {n : ℕ} (hn : 3 ≤ n) :
    ⌊epsilon * (n : ℝ) ^ 2⌋₊ ≤
      fractionalEditRadius (3 * epsilon) (completeEdgeCount n) := by
  unfold fractionalEditRadius
  apply Nat.floor_mono
  have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
  rw [completeEdgeCount, Nat.cast_choose_two]
  nlinarith [mul_nonneg hepsilon (sq_nonneg (n : ℝ))]

/-- The explicit entropy rate used for combined defect patterns.  The
factor `3` is the elementary conversion from the ordered-square budget to
the unordered-pair normalization; the extra `epsilon` is the strict
eventual slack in the entropy estimate. -/
def supercriticalDefectPatternRate (epsilon : ℝ) : ℝ :=
  (binaryEntropy (3 * epsilon) + epsilon) * Real.log 2

theorem supercriticalDefectPatternRate_pos
    {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (hsmall : 3 * epsilon < 1 / 2) :
    0 < supercriticalDefectPatternRate epsilon := by
  have heta0 : 0 ≤ 3 * epsilon := by positivity
  have heta1 : 3 * epsilon ≤ 1 := hsmall.le.trans (by norm_num)
  have hH : 0 ≤ binaryEntropy (3 * epsilon) :=
    binaryEntropy_nonneg heta0 heta1
  unfold supercriticalDefectPatternRate
  exact mul_pos (add_pos_of_nonneg_of_pos hH hepsilon) realLogTwo_pos

/-- A defect budget `⌊εn²⌋` has an explicit entropy-rate exponential
overhead.  In particular, the displayed coefficient tends to zero with
`epsilon`; no asymptotic notation is hidden in the declaration. -/
theorem eventually_hammingBallVolume_floor_square_le_exp
    {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (hsmall : 3 * epsilon < 1 / 2) :
    ∀ᶠ n : ℕ in atTop,
      (hammingBallVolume (completeEdgeCount n)
          ⌊epsilon * (n : ℝ) ^ 2⌋₊ : ℝ) ≤
        Real.exp (supercriticalDefectPatternRate epsilon * (n : ℝ) ^ 2) := by
  have heta : 3 * epsilon ∈ Ioo (0 : ℝ) (1 / 2 : ℝ) :=
    ⟨by positivity, hsmall⟩
  have hentropy := eventually_normalizedLog_hammingBallVolume_le_add
    (3 * epsilon) heta epsilon hepsilon
  filter_upwards [hentropy, eventually_ge_atTop 3] with n hlog hn
  let N := completeEdgeCount n
  let r := fractionalEditRadius (3 * epsilon) N
  let s := ⌊epsilon * (n : ℝ) ^ 2⌋₊
  have hsr : s ≤ r := by
    exact floor_square_le_fractionalEditRadius_three_mul hepsilon.le hn
  have hvolNat : hammingBallVolume N s ≤ hammingBallVolume N r :=
    hammingBallVolume_mono_right hsr
  have hvolReal :
      (hammingBallVolume N s : ℝ) ≤ (hammingBallVolume N r : ℝ) := by
    exact_mod_cast hvolNat
  have hNnat : 0 < N := by
    unfold N completeEdgeCount
    exact Nat.choose_pos (by omega)
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hNnat
  have hlog2 :
      log2 (hammingBallVolume N r : ℝ) <
        (binaryEntropy (3 * epsilon) + epsilon) * (N : ℝ) := by
    change log2 (hammingBallVolume N r : ℝ) / (N : ℝ) <
      binaryEntropy (3 * epsilon) + epsilon at hlog
    exact (div_lt_iff₀ hNreal).mp hlog
  have hlogNatural :
      Real.log (hammingBallVolume N r : ℝ) <
        ((binaryEntropy (3 * epsilon) + epsilon) * (N : ℝ)) *
          Real.log 2 := by
    rw [log2] at hlog2
    exact (div_lt_iff₀ realLogTwo_pos).mp hlog2
  have heta0 : 0 ≤ 3 * epsilon := by positivity
  have heta1 : 3 * epsilon ≤ 1 := hsmall.le.trans (by norm_num)
  have hrate0 : 0 ≤
      (binaryEntropy (3 * epsilon) + epsilon) * Real.log 2 := by
    exact mul_nonneg
      (add_nonneg (binaryEntropy_nonneg heta0 heta1) hepsilon.le)
      realLogTwo_pos.le
  have hNle : (N : ℝ) ≤ (n : ℝ) ^ 2 := by
    change (completeEdgeCount n : ℝ) ≤ (n : ℝ) ^ 2
    exact_mod_cast Nat.choose_le_pow n 2
  have hlogRate :
      Real.log (hammingBallVolume N r : ℝ) <
        supercriticalDefectPatternRate epsilon * (n : ℝ) ^ 2 := by
    calc
      Real.log (hammingBallVolume N r : ℝ) <
          ((binaryEntropy (3 * epsilon) + epsilon) * (N : ℝ)) *
            Real.log 2 := hlogNatural
      _ = ((binaryEntropy (3 * epsilon) + epsilon) * Real.log 2) *
          (N : ℝ) := by ring
      _ ≤ ((binaryEntropy (3 * epsilon) + epsilon) * Real.log 2) *
          (n : ℝ) ^ 2 := mul_le_mul_of_nonneg_left hNle hrate0
      _ = supercriticalDefectPatternRate epsilon * (n : ℝ) ^ 2 := rfl
  have hvolPos : 0 < (hammingBallVolume N r : ℝ) := by
    exact_mod_cast hammingBallVolume_pos N r
  calc
    (hammingBallVolume (completeEdgeCount n)
        ⌊epsilon * (n : ℝ) ^ 2⌋₊ : ℝ) =
        (hammingBallVolume N s : ℝ) := rfl
    _ ≤ (hammingBallVolume N r : ℝ) := hvolReal
    _ = Real.exp (Real.log (hammingBallVolume N r : ℝ)) :=
      (Real.exp_log hvolPos).symm
    _ ≤ Real.exp
        (supercriticalDefectPatternRate epsilon * (n : ℝ) ^ 2) :=
      Real.exp_le_exp.mpr hlogRate.le

/-- The Hamming-ball pattern factor and all vertex/part/incident/profile
choices admit one explicit eventual exponential bound. -/
theorem eventually_supercriticalMediumCombinatorialOverhead_le_exp
    (k : ℕ) {epsilon c : ℝ} (hepsilon : 0 < epsilon)
    (hsmall : 3 * epsilon < 1 / 2) (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop,
      (hammingBallVolume (completeEdgeCount n)
          ⌊epsilon * (n : ℝ) ^ 2⌋₊ : ℝ) *
          (supercriticalMediumAuxiliaryFactor k n : ℝ) ≤
        Real.exp ((supercriticalDefectPatternRate epsilon + c) *
          (n : ℝ) ^ 2) := by
  filter_upwards
      [eventually_hammingBallVolume_floor_square_le_exp hepsilon hsmall,
        eventually_supercriticalMediumAuxiliaryFactor_le_exp k hc]
      with n hdefect haux
  calc
    (hammingBallVolume (completeEdgeCount n)
        ⌊epsilon * (n : ℝ) ^ 2⌋₊ : ℝ) *
        (supercriticalMediumAuxiliaryFactor k n : ℝ) ≤
      Real.exp (supercriticalDefectPatternRate epsilon * (n : ℝ) ^ 2) *
        Real.exp (c * (n : ℝ) ^ 2) := by
          exact mul_le_mul hdefect haux (by positivity) (Real.exp_nonneg _)
    _ = Real.exp ((supercriticalDefectPatternRate epsilon + c) *
        (n : ℝ) ^ 2) := by
      rw [← Real.exp_add]
      congr 1
      ring

/-- Direct family-level form of the defect-pattern entropy bound. -/
theorem eventually_card_supercriticalCombinedDefectPatternFinset_le_exp
    {k : ℕ} (hk : 3 ≤ k) {gamma : ℝ}
    (hgamma : gamma ∈ Ico (gammaK k) 1)
    {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (hsmall : 3 * epsilon < 1 / 2) :
    ∀ᶠ n : ℕ in atTop, ∀ (m : ℕ) (tau : ℝ) (hn : k - 1 ≤ n)
      (D : SupercriticalDivision k (Fin n)),
      (∀ G ∈ supercriticalDivisionDefectGraphFinset
          k hk gamma hgamma m n tau hn D,
        supercriticalDefectCost G D ≤ ⌊epsilon * (n : ℝ) ^ 2⌋₊) →
      ((supercriticalCombinedDefectPatternFinset
          k hk gamma hgamma m n tau hn D).card : ℝ) ≤
        Real.exp (supercriticalDefectPatternRate epsilon * (n : ℝ) ^ 2) := by
  filter_upwards
      [eventually_hammingBallVolume_floor_square_le_exp hepsilon hsmall]
      with n hnvolume m tau hn D hcost
  have hcard := card_supercriticalCombinedDefectPatternFinset_le_hammingBallVolume
    (k := k) (hk := hk) (gamma := gamma) (hgamma := hgamma)
    (m := m) (n := n) (tau := tau) (hn := hn) (D := D) hcost
  have hcardReal :
      ((supercriticalCombinedDefectPatternFinset
          k hk gamma hgamma m n tau hn D).card : ℝ) ≤
        (hammingBallVolume (completeEdgeCount n)
          ⌊epsilon * (n : ℝ) ^ 2⌋₊ : ℝ) := by
    exact_mod_cast hcard
  exact hcardReal.trans hnvolume

end InducedStars
