import InducedStars.C4.TemplateSlices
import InducedStars.C4.BenchmarkLower
import InducedStars.C4.BenchmarkParameters
import DenseGraph.Analysis.EntropyFeasibilityEnvelope
import Mathlib.Data.Nat.Choose.Vandermonde

/-!
# Finite entropy bounds for C4 template slices

Every actual red quota is feasible before entropy is evaluated.
The ideal target is used through the feasible entropy envelope; an
infeasible ideal target never gives a minus-infinity counting bound.
Missing pairs, the repair window, and the Hamming ball retain explicit costs.
-/

noncomputable section
open Finset Set Filter Topology InducedStars.Regularity
open scoped Classical
namespace InducedStars

/-- Vandermonde separates the missing-pair choices from genuinely feasible
red choices. Only red quotas compatible with the prescribed total are used. -/
theorem c4_choose_with_missing_le {R M a : ℕ} {E : ℝ} (hE : 0 ≤ E)
    (hred : ∀ j t : ℕ, j ≤ R → t ≤ M → j + t = a → (R.choose j : ℝ) ≤ E) :
    ((R + M).choose a : ℝ) ≤ (2 : ℝ)^M * E := by
  have hsum : (∑ t ∈ range (a + 1), M.choose t) ≤ 2^M := by
    rw [← Nat.sum_range_choose]
    apply Finset.sum_le_sum_of_ne_zero
    intro t ht hne
    exact mem_range.mpr (Nat.lt_succ_of_le (Nat.le_of_not_gt fun h =>
      hne (Nat.choose_eq_zero_of_lt h)))
  rw [Nat.add_comm R M, Nat.add_choose_eq,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [Nat.cast_sum, Nat.cast_mul]
  calc
    ∑ t ∈ range (a + 1), (M.choose t : ℝ) * (R.choose (a-t) : ℝ) ≤
        ∑ t ∈ range (a + 1), (M.choose t : ℝ) * E := by
      apply Finset.sum_le_sum
      intro t ht
      by_cases htM : t ≤ M
      · by_cases hjR : a-t ≤ R
        · exact mul_le_mul_of_nonneg_left
            (hred (a-t) t hjR htM (by have := mem_range.mp ht; omega)) (by positivity)
        · rw [Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge hjR), Nat.cast_zero, mul_zero]
          positivity
      · simp [Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge htM)]
    _ = (∑ t ∈ range (a + 1), (M.choose t : ℝ)) * E := (Finset.sum_mul ..).symm
    _ ≤ (2 : ℝ)^M * E := mul_le_mul_of_nonneg_right (by exact_mod_cast hsum) hE

theorem c4_choose_le_exp_binaryEntropy {R j : ℕ} (hj : j ≤ R) :
    (R.choose j : ℝ) ≤ Real.exp (Real.log 2 *
      ((R : ℝ) * binaryEntropy ((j : ℝ)/R))) := by
  convert DenseGraph.choose_le_exp_binomialEntropyPerspective hj using 1
  unfold DenseGraph.binomialEntropyPerspective binaryEntropy
  congr 1
  field_simp

theorem c4ColorEdgeCount_cast_le_square {n : ℕ}
    (J : RegularityColoredGraph (Fin n)) (c : EdgeColor) :
    (c4ColorEdgeCount J c : ℝ) ≤ (n : ℝ)^2 := by
  have h : (c4ColorEdgeCount J c : ℝ) ≤ (completeEdgeCount n : ℝ) := by
    exact_mod_cast c4ColorEdgeCount_le_complete J c
  rw [completeEdgeCount, Nat.cast_choose_two] at h
  nlinarith [Nat.cast_nonneg (α := ℝ) n]

/-- A repaired edge count and its missing-edge choices give a uniformly
nearby, actually feasible red quota. Natural subtraction is guarded. -/
theorem c4_redTarget_error {m r m' B j t M : ℕ} {ideal : ℝ}
    (hwindow : m' ∈ Finset.Icc (m-r) (m+r))
    (hB : B ≤ m') (hjt : j+t = m'-B) (ht : t ≤ M) :
    |((B+j : ℕ) : ℝ) - ideal| ≤ |(m : ℝ)-ideal| + r + M := by
  have hw := Finset.mem_Icc.mp hwindow
  have hm'm : m' ≤ m+r := hw.2
  have hmm' : m ≤ m'+r := by omega
  have heq : B+j+t = m' := by omega
  have hdist : |((B+j : ℕ) : ℝ) - m| ≤ (r : ℝ)+M := by
    apply abs_le.mpr
    constructor <;> push_cast <;>
      have heq' : (B : ℝ)+j+t = m' := by exact_mod_cast heq
    · have h1 : (m : ℝ) ≤ m'+r := by exact_mod_cast hmm'
      have h2 : (t : ℝ) ≤ M := by exact_mod_cast ht
      linarith
    · have h1 : (m' : ℝ) ≤ m+r := by exact_mod_cast hm'm
      have ht0 : (0 : ℝ) ≤ t := by positivity
      have hM0 : (0 : ℝ) ≤ M := by positivity
      linarith
  have htri := abs_add_le (((B+j : ℕ) : ℝ) - m) ((m : ℝ)-ideal)
  rw [sub_add_sub_cancel] at htri
  linarith

/-- Uniform finite near-template counting with a feasible ideal-target
envelope. The explicit prefactor records the edge-count window, missing-pair
choices, and Hamming repair cost separately. -/
theorem c4TemplateNearSlice_entropy_upper {epsilon : ℝ} (he : 0 < epsilon) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ (n m r : ℕ)
      (J : RegularityColoredGraph (Fin n)) (ideal : ℝ), 0 < n →
      |(m : ℝ)-ideal| + r + c4MissingEdgeCount J ≤ delta*(n : ℝ)^2 →
      ((c4TemplateNearSlice J m r).card : ℝ) ≤
        ((Finset.Icc (m-r) (m+r)).card : ℝ) *
        (2 : ℝ)^(c4MissingEdgeCount J) *
        (hammingBallVolume (completeEdgeCount n) r : ℝ) *
        Real.exp (Real.log 2 *
          (DenseGraph.feasibleEntropyEnvelope (c4ColorEdgeCount J .red)
            (c4ColorEdgeCount J .blue) ideal + epsilon*(n : ℝ)^2)) := by
  obtain ⟨delta, hd, hmod⟩ := DenseGraph.entropy_le_feasibleEnvelope_add_error he
  refine ⟨delta, hd, ?_⟩
  intro n m r J ideal hn herr
  let E := Real.exp (Real.log 2 *
    (DenseGraph.feasibleEntropyEnvelope (c4ColorEdgeCount J .red)
      (c4ColorEdgeCount J .blue) ideal + epsilon*(n : ℝ)^2))
  have hslice : ∀ m' ∈ Finset.Icc (m-r) (m+r),
      ((c4TemplateRealizationSlice J m').card : ℝ) ≤
        (2 : ℝ)^(c4MissingEdgeCount J) * E := by
    intro m' hm'
    rw [card_c4TemplateRealizationSlice]
    split_ifs with hB
    · apply c4_choose_with_missing_le (Real.exp_pos _).le
      intro j t hj ht hjt
      have hnear := (c4_redTarget_error hm' hB hjt ht).trans herr
      have hactual : ((c4ColorEdgeCount J .blue+j : ℕ) : ℝ) ∈
          Set.Icc (c4ColorEdgeCount J .blue : ℝ)
            ((c4ColorEdgeCount J .blue : ℝ)+c4ColorEdgeCount J .red) := by
        constructor
        · simp only [Nat.cast_add]; exact le_add_of_nonneg_right (by positivity)
        · exact_mod_cast Nat.add_le_add_left hj (c4ColorEdgeCount J .blue)
      have hentropy := hmod ((n : ℝ)^2) (c4ColorEdgeCount J .red)
        (c4ColorEdgeCount J .blue) ((c4ColorEdgeCount J .blue+j : ℕ) : ℝ)
        ideal (sq_pos_of_pos (by exact_mod_cast hn)) (by positivity)
        (c4ColorEdgeCount_cast_le_square J .red) hactual hnear
      simp only [Nat.cast_add, add_sub_cancel_left] at hentropy
      exact (c4_choose_le_exp_binaryEntropy hj).trans
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hentropy realLogTwo_pos.le))
    · simp only [Nat.cast_zero]
      positivity
  have hcount : ((c4TemplateNearSlice J m r).card : ℝ) ≤
      (∑ m' ∈ Finset.Icc (m-r) (m+r), ((c4TemplateRealizationSlice J m').card : ℝ)) *
      (hammingBallVolume (completeEdgeCount n) r : ℝ) := by
    exact_mod_cast card_c4TemplateNearSlice_le_slice_sum J m r
  refine hcount.trans ?_
  calc
    _ ≤ (∑ _m' ∈ Finset.Icc (m-r) (m+r),
        (2 : ℝ)^(c4MissingEdgeCount J)*E) *
          (hammingBallVolume (completeEdgeCount n) r : ℝ) :=
      mul_le_mul_of_nonneg_right (Finset.sum_le_sum hslice) (by positivity)
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]; dsimp [E]; ring

/-- Lower entropy sandwich in bits, retaining its exact finite polynomial
loss. No Stirling approximation or external estimate is used. -/
theorem c4_exp_binaryEntropy_div_succ_le_choose {R j : ℕ} (hj : j ≤ R) :
    Real.exp (Real.log 2 * ((R : ℝ) * binaryEntropy ((j : ℝ)/R))) /
      ((R : ℝ)+1) ≤ (R.choose j : ℝ) := by
  convert DenseGraph.exp_binomialEntropyPerspective_div_succ_le_choose hj using 1
  · congr 1
    · unfold DenseGraph.binomialEntropyPerspective binaryEntropy
      field_simp
    · push_cast; rfl

/-- A positive benchmark forces an interior density in its attaining complete
template. Consequently every sufficiently close actual edge count is feasible
and realizes the benchmark entropy up to a uniform quadratic error. -/
theorem c4Free_count_lower_of_positive_benchmark {kappa epsilon : ℝ}
    (hk : 0 < kappa) (he : 0 < epsilon) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ (n m : ℕ) (gamma : ℝ), 0 < n →
      kappa/4*(n : ℝ)^2 ≤ c4CompleteEntropyBenchmark n gamma →
      |(m : ℝ)-gamma*completeEdgeCount n| ≤ delta*(n : ℝ)^2 →
      Real.exp (Real.log 2*(c4CompleteEntropyBenchmark n gamma-epsilon*(n : ℝ)^2)) /
        ((completeEdgeCount n : ℝ)+1) ≤ (inducedC4FreeGraphCountWithEdges n m : ℝ) := by
  obtain ⟨alpha, ha, ha1, hband⟩ := c4_entropy_level_compact_band hk
  obtain ⟨delta, hd, hmod⟩ := DenseGraph.entropy_scaled_feasible_uniform he
  refine ⟨min delta (alpha*kappa/8), lt_min hd (by positivity), ?_⟩
  intro n m gamma hn hbench herr
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hn2 : 0 < (n : ℝ)^2 := sq_pos_of_pos hnpos
  have hbenchpos : 0 < c4CompleteEntropyBenchmark n gamma :=
    lt_of_lt_of_le (by positivity) hbench
  have hS : (c4CompleteBenchmarkPairs n gamma).Nonempty := by
    by_contra hS
    simp only [c4CompleteEntropyBenchmark, dif_neg hS] at hbenchpos
    exact (lt_irrefl _ hbenchpos)
  obtain ⟨J, hcomplete, hfree, hf, hattain⟩ := exists_completeTemplate_at_c4Benchmark hS
  let R : ℝ := c4ColorEdgeCount J .red
  let B : ℝ := c4ColorEdgeCount J .blue
  let ideal : ℝ := gamma*completeEdgeCount n
  have hRlower : kappa/4*(n : ℝ)^2 ≤ R := by
    exact hbench.trans (hattain ▸ hf.value_le_capacity)
  have hRpos : 0 < R := lt_of_lt_of_le (by positivity) hRlower
  have hRupper : R ≤ (n : ℝ)^2 := c4ColorEdgeCount_cast_le_square J .red
  have hq := hf.density_mem_Icc hRpos
  have hHnonneg := binaryEntropy_nonneg hq.1 hq.2
  have hPhi : R*binaryEntropy ((ideal-B)/R) = c4CompleteEntropyBenchmark n gamma := by
    simpa only [c4ColoredEntropy_eq] using hattain
  have hH : kappa/4 ≤ binaryEntropy ((ideal-B)/R) := by
    have hh := mul_le_mul_of_nonneg_right hRupper hHnonneg
    rw [hPhi] at hh
    nlinarith only [hbench, hh, hn2]
  have hqband := hband ((ideal-B)/R) hq hH
  have hmarginLower : alpha*R ≤ ideal-B := (le_div_iff₀ hRpos).mp hqband.1
  have hmarginUpper : ideal-B ≤ (1-alpha)*R := (div_le_iff₀ hRpos).mp hqband.2
  have herrSmall : |(m : ℝ)-ideal| ≤ alpha*R/2 := by
    have hh := mul_le_mul_of_nonneg_right (min_le_right delta (alpha*kappa/8)) hn2.le
    have hh' := mul_le_mul_of_nonneg_left hRlower (by positivity : 0 ≤ alpha/2)
    dsimp [ideal]
    nlinarith only [herr, hh, hh']
  have hmreal : (m : ℝ) ∈ Set.Icc B (B+R) := by
    have hh := abs_le.mp herrSmall
    have hmargin : 0 ≤ alpha*R := (mul_pos ha hRpos).le
    constructor <;> linarith only [hh.1, hh.2, hmarginLower, hmarginUpper, hmargin]
  have hmreal' := hmreal
  dsimp [B, R] at hmreal'
  have hmB : c4ColorEdgeCount J .blue ≤ m := by exact_mod_cast hmreal'.1
  have hmR : m-c4ColorEdgeCount J .blue ≤ c4ColorEdgeCount J .red := by
    have hh : m ≤ c4ColorEdgeCount J .blue+c4ColorEdgeCount J .red := by
      exact_mod_cast hmreal'.2
    omega
  have herrDelta : |(m : ℝ)-ideal| ≤ delta*(n : ℝ)^2 :=
    herr.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) hn2.le)
  have hentropy := hmod ((n : ℝ)^2) R B m ideal hn2 hRpos.le hRupper
    hmreal ⟨hf.lower, hf.upper⟩ herrDelta
  have hElower : c4CompleteEntropyBenchmark n gamma-epsilon*(n : ℝ)^2 ≤
      R*binaryEntropy (((m-c4ColorEdgeCount J .blue : ℕ) : ℝ)/R) := by
    rw [Nat.cast_sub hmB]
    rw [hPhi] at hentropy
    have hh := (abs_le.mp hentropy).1
    linarith only [hh]
  have hslice := c4_exp_binaryEntropy_div_succ_le_choose hmR
  have hcard : ((c4ColorEdgeCount J .red).choose (m-c4ColorEdgeCount J .blue) : ℝ) ≤
      (inducedC4FreeGraphCountWithEdges n m : ℝ) := by
    have hh := Finset.card_le_card
      (c4TemplateRealizationSlice_subset_inducedC4Free J m hcomplete hfree)
    rw [card_c4TemplateRealizationSlice_of_complete J hcomplete m, if_pos hmB] at hh
    exact_mod_cast hh
  refine le_trans ?_ (hslice.trans hcard)
  apply div_le_div₀ (Real.exp_pos _).le
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hElower realLogTwo_pos.le))
    (by positivity)
  have hcap : (c4ColorEdgeCount J .red : ℝ) ≤ (completeEdgeCount n : ℝ) := by
    exact_mod_cast c4ColorEdgeCount_le_complete J .red
  linarith only [hcap]

/-- Asymptotic edge density supplies the exact additive error on the square
scale used by finite template entropy estimates. -/
theorem c4_edgeTarget_error_eventually {m : ℕ → ℕ} {gamma delta : ℝ}
    (hm : HasAsymptoticEdgeDensity m gamma) (hd : 0 < delta) :
    ∀ᶠ n : ℕ in atTop,
      |(m n : ℝ)-gamma*completeEdgeCount n| ≤ delta*(n : ℝ)^2 := by
  have hevent := hm.eventually (Metric.ball_mem_nhds gamma hd)
  filter_upwards [hevent, eventually_ge_atTop 2] with n hn hn2
  have hN : 0 < completeEdgeCount n := by
    exact Nat.choose_pos hn2
  have hNpos : (0 : ℝ) < completeEdgeCount n := by exact_mod_cast hN
  have hdist : |(m n : ℝ)/(completeEdgeCount n : ℝ)-gamma| ≤ delta :=
    (by simpa only [Metric.mem_ball, Real.dist_eq] using hn :
      |(m n : ℝ)/(completeEdgeCount n : ℝ)-gamma| < delta).le
  have hmul := mul_le_mul_of_nonneg_right hdist hNpos.le
  have heq : ((m n : ℝ)/(completeEdgeCount n : ℝ)-gamma)*completeEdgeCount n =
      (m n : ℝ)-gamma*completeEdgeCount n := by field_simp
  rw [← abs_of_pos hNpos, ← abs_mul, abs_of_pos hNpos, heq] at hmul
  refine hmul.trans (mul_le_mul_of_nonneg_left ?_ hd.le)
  rw [completeEdgeCount, Nat.cast_choose_two]
  nlinarith [Nat.cast_nonneg (α := ℝ) n]

/-- The exact binomial lower bound for a complete benchmark maximizer,
uniformly for every edge-count sequence of the required limiting density. -/
theorem eventually_c4Free_count_lower_with_polynomial_loss
    {gamma epsilon : ℝ} (hgamma : gamma ∈ Set.Ioo 0 1) (he : 0 < epsilon)
    {m : ℕ → ℕ} (hm : HasAsymptoticEdgeDensity m gamma) :
    ∀ᶠ n : ℕ in atTop,
      Real.exp (Real.log 2*(c4CompleteEntropyBenchmark n gamma-epsilon*(n : ℝ)^2)) /
        ((completeEdgeCount n : ℝ)+1) ≤
          (inducedC4FreeGraphCountWithEdges n (m n) : ℝ) := by
  have hk : 0 < gamma*(1-gamma) := mul_pos hgamma.1 (sub_pos.mpr hgamma.2)
  obtain ⟨delta, hd, hfinite⟩ := c4Free_count_lower_of_positive_benchmark hk he
  filter_upwards [eventually_ge_atTop 1, eventually_c4CompleteEntropyBenchmark_lower hgamma,
    c4_edgeTarget_error_eventually hm hd] with n hn hbench herr
  exact hfinite n (m n) gamma (by omega) hbench herr

/-- A deliberately coarse elementary logarithmic loss bound suffices to
absorb the binomial sandwich's polynomial factor on the square scale. -/
theorem c4_log_complete_succ_le_linear (n : ℕ) :
    Real.log ((completeEdgeCount n : ℝ)+1) ≤ 2*n := by
  have hN : (completeEdgeCount n : ℝ)+1 ≤ ((n : ℝ)+1)^2 := by
    rw [completeEdgeCount, Nat.cast_choose_two]
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have hlog := Real.log_le_log (by positivity : 0 < (completeEdgeCount n : ℝ)+1) hN
  rw [Real.log_pow] at hlog
  have hnlog := Real.log_le_sub_one_of_pos (by positivity : 0 < (n : ℝ)+1)
  norm_num at hlog
  linarith only [hlog, hnlog]

/-- Complete-template lower counting at the actual edge sequence, with every
polynomial loss absorbed into an arbitrarily small quadratic entropy error. -/
theorem eventually_c4Free_count_entropy_lower
    {gamma epsilon : ℝ} (hgamma : gamma ∈ Set.Ioo 0 1) (he : 0 < epsilon)
    {m : ℕ → ℕ} (hm : HasAsymptoticEdgeDensity m gamma) :
    ∀ᶠ n : ℕ in atTop,
      Real.exp (Real.log 2*(c4CompleteEntropyBenchmark n gamma-epsilon*(n : ℝ)^2)) ≤
        (inducedC4FreeGraphCountWithEdges n (m n) : ℝ) := by
  have hc : 0 < Real.log 2*(epsilon/2) := mul_pos realLogTwo_pos (half_pos he)
  have hlarge : ∀ᶠ n : ℕ in atTop, 2/(Real.log 2*(epsilon/2)) ≤ (n : ℝ) :=
    (tendsto_natCast_atTop_atTop.eventually_ge_atTop _)
  filter_upwards [eventually_c4Free_count_lower_with_polynomial_loss hgamma (half_pos he) hm,
    hlarge] with n hlower hn
  have hh := mul_le_mul_of_nonneg_right ((div_le_iff₀ hc).mp hn) (Nat.cast_nonneg (α := ℝ) n)
  have hcost : Real.log ((completeEdgeCount n : ℝ)+1) ≤
      Real.log 2*(epsilon/2)*(n : ℝ)^2 := by
    have hlog := c4_log_complete_succ_le_linear n
    nlinarith only [hh, hlog]
  refine le_trans ?_ hlower
  rw [← Real.exp_log (by positivity : 0 < (completeEdgeCount n : ℝ)+1), ← Real.exp_sub]
  apply Real.exp_le_exp.mpr
  nlinarith only [hcost]

end InducedStars
