import InducedStars.Graphon.TypeTower
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-!
# Vanishing-error lemmas for Type graphon sequences

This file collects the elementary analytic estimates used after the finite
Type-tower construction.  In particular, the matrix dimension is allowed to
vary with the sequence index in the uniform-entrywise `L¹` lemma.
-/

noncomputable section

open Filter
open scoped Topology

namespace InducedStars.Graphon

/-! ## Squeezing finite error budgets -/

/-- A nonnegative error bounded by the sum of two vanishing terms also
vanishes. -/
theorem tendsto_zero_of_nonneg_of_le_add
    (error a b : ℕ → ℝ)
    (herror : ∀ n, 0 ≤ error n)
    (ha : Tendsto a atTop (nhds 0))
    (hb : Tendsto b atTop (nhds 0))
    (hbound : ∀ n, error n ≤ a n + b n) :
    Tendsto error atTop (nhds 0) := by
  apply squeeze_zero herror hbound
  simpa only [zero_add] using ha.add hb

/-- A ratio of natural-number sequences vanishes if it is bounded by the
standard `1 / (n + 1)` schedule.  No positivity hypothesis on the denominator
is needed: division by zero has the usual field value zero. -/
theorem tendsto_natCast_div_natCast_zero_of_le_one_div_add
    (q hostSize : ℕ → ℕ)
    (hbound : ∀ n,
      (q n : ℝ) / (hostSize n : ℝ) ≤ 1 / (((n + 1 : ℕ) : ℝ))) :
    Tendsto (fun n ↦ (q n : ℝ) / (hostSize n : ℝ))
      atTop (nhds 0) := by
  apply squeeze_zero
  · intro n
    positivity
  · exact hbound
  · simpa only [Nat.cast_add, Nat.cast_one] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

/-- A natural multiplication certificate gives the corresponding real ratio
bound.  This is the arithmetic adapter used when the selected host size is at
least `q * k`. -/
theorem natCast_div_natCast_le_one_div_natCast_of_mul_le
    {q hostSize k : ℕ} (hhost : 0 < hostSize) (hk : 0 < k)
    (h : q * k ≤ hostSize) :
    (q : ℝ) / (hostSize : ℝ) ≤ 1 / (k : ℝ) := by
  rw [div_le_div_iff₀ (Nat.cast_pos.mpr hhost) (Nat.cast_pos.mpr hk)]
  norm_num
  exact_mod_cast h

/-- A cleaning error bounded by fixed multiples of `eta` and the
cluster-count/host-size ratio vanishes as soon as those two terms do. -/
theorem tendsto_error_of_le_mul_eta_add_mul_ratio
    (cEta cRatio : ℝ) (error eta : ℕ → ℝ)
    (q hostSize : ℕ → ℕ)
    (herror : ∀ n, 0 ≤ error n)
    (heta : Tendsto eta atTop (nhds 0))
    (hratio : Tendsto (fun n ↦ (q n : ℝ) / (hostSize n : ℝ))
      atTop (nhds 0))
    (hbound : ∀ n,
      error n ≤
        cEta * eta n + cRatio * ((q n : ℝ) / (hostSize n : ℝ))) :
    Tendsto error atTop (nhds 0) := by
  apply tendsto_zero_of_nonneg_of_le_add error
      (fun n ↦ cEta * eta n)
      (fun n ↦ cRatio * ((q n : ℝ) / (hostSize n : ℝ))) herror
  · simpa only [mul_zero] using
      (tendsto_const_nhds.mul heta :
        Tendsto (fun n ↦ cEta * eta n) atTop (nhds (cEta * 0)))
  · simpa only [mul_zero] using
      (tendsto_const_nhds.mul hratio :
        Tendsto
          (fun n ↦ cRatio * ((q n : ℝ) / (hostSize n : ℝ)))
          atTop (nhds (cRatio * 0)))
  · exact hbound

/-- The `2 * eta + 4 * (q / hostSize)` cleaning budget vanishes. -/
theorem tendsto_error_of_le_two_mul_eta_add_four_mul_ratio
    (error eta : ℕ → ℝ) (q hostSize : ℕ → ℕ)
    (herror : ∀ n, 0 ≤ error n)
    (heta : Tendsto eta atTop (nhds 0))
    (hratio : Tendsto (fun n ↦ (q n : ℝ) / (hostSize n : ℝ))
      atTop (nhds 0))
    (hbound : ∀ n,
      error n ≤ 2 * eta n + 4 * ((q n : ℝ) / (hostSize n : ℝ))) :
    Tendsto error atTop (nhds 0) :=
  tendsto_error_of_le_mul_eta_add_mul_ratio 2 4 error eta q hostSize
    herror heta hratio hbound

/-- Safe cleaning-budget form used by the globally equitable construction:
`4 * eta + 8 * (q / hostSize)` also vanishes. -/
theorem tendsto_error_of_le_four_mul_eta_add_eight_mul_ratio
    (error eta : ℕ → ℝ) (q hostSize : ℕ → ℕ)
    (herror : ∀ n, 0 ≤ error n)
    (heta : Tendsto eta atTop (nhds 0))
    (hratio : Tendsto (fun n ↦ (q n : ℝ) / (hostSize n : ℝ))
      atTop (nhds 0))
    (hbound : ∀ n,
      error n ≤ 4 * eta n + 8 * ((q n : ℝ) / (hostSize n : ℝ))) :
    Tendsto error atTop (nhds 0) :=
  tendsto_error_of_le_mul_eta_add_mul_ratio 4 8 error eta q hostSize
    herror heta hratio hbound

/-- Schedule-based form of
`tendsto_error_of_le_two_mul_eta_add_four_mul_ratio`. -/
theorem tendsto_error_of_le_two_mul_eta_add_four_mul_ratio_of_schedule
    (error eta : ℕ → ℝ) (q hostSize : ℕ → ℕ)
    (herror : ∀ n, 0 ≤ error n)
    (heta : Tendsto eta atTop (nhds 0))
    (hratio : ∀ n,
      (q n : ℝ) / (hostSize n : ℝ) ≤ 1 / (((n + 1 : ℕ) : ℝ)))
    (hbound : ∀ n,
      error n ≤ 2 * eta n + 4 * ((q n : ℝ) / (hostSize n : ℝ))) :
    Tendsto error atTop (nhds 0) :=
  tendsto_error_of_le_two_mul_eta_add_four_mul_ratio error eta q hostSize
    herror heta
    (tendsto_natCast_div_natCast_zero_of_le_one_div_add q hostSize hratio)
    hbound

/-- Schedule-based form of the safe `4 * eta + 8 * (q / hostSize)` cleaning
budget. -/
theorem tendsto_error_of_le_four_mul_eta_add_eight_mul_ratio_of_schedule
    (error eta : ℕ → ℝ) (q hostSize : ℕ → ℕ)
    (herror : ∀ n, 0 ≤ error n)
    (heta : Tendsto eta atTop (nhds 0))
    (hratio : ∀ n,
      (q n : ℝ) / (hostSize n : ℝ) ≤ 1 / (((n + 1 : ℕ) : ℝ)))
    (hbound : ∀ n,
      error n ≤ 4 * eta n + 8 * ((q n : ℝ) / (hostSize n : ℝ))) :
    Tendsto error atTop (nhds 0) :=
  tendsto_error_of_le_four_mul_eta_add_eight_mul_ratio error eta q hostSize
    herror heta
    (tendsto_natCast_div_natCast_zero_of_le_one_div_add q hostSize hratio)
    hbound

/-! ## The regularity-to-cut error budget -/

/-- If `eta → 0` and a positive natural sequence at least doubles at every
step, then the regularity cut-error expression `5 * eta + 1 / q` tends to
zero. -/
theorem tendsto_five_mul_eta_add_one_div_natCast_of_two_mul_le_succ
    (eta : ℕ → ℝ) (q : ℕ → ℕ)
    (heta : Tendsto eta atTop (nhds 0))
    (hq₀ : 1 ≤ q 0) (hgrow : ∀ n, 2 * q n ≤ q (n + 1)) :
    Tendsto (fun n ↦ 5 * eta n + 1 / (q n : ℝ)) atTop (nhds 0) := by
  have hfive : Tendsto (fun n ↦ 5 * eta n) atTop (nhds 0) := by
    simpa only [mul_zero] using
      (tendsto_const_nhds.mul heta :
        Tendsto (fun n ↦ 5 * eta n) atTop (nhds (5 * 0)))
  simpa only [zero_add] using hfive.add
    (tendsto_one_div_natCast_of_two_mul_le_succ q hq₀ hgrow)

/-! ## Simultaneous tails for finite matrices -/

/-- Entrywise convergence on a fixed finite matrix admits one threshold after
which every entry is simultaneously within a prescribed positive error. -/
theorem exists_threshold_matrix_entrywise_abs_sub_lt
    {q : ℕ} (M : ℕ → Matrix (Fin q) (Fin q) ℝ)
    (L : Matrix (Fin q) (Fin q) ℝ)
    (hM : ∀ i j, Tendsto (fun n ↦ M n i j) atTop (nhds (L i j)))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n, N ≤ n → ∀ i j, |M n i j - L i j| < ε := by
  have hpair : ∀ ij : Fin q × Fin q,
      ∀ᶠ n in atTop, |M n ij.1 ij.2 - L ij.1 ij.2| < ε := by
    intro ij
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (hM ij.1 ij.2) ε hε
    filter_upwards [eventually_ge_atTop N] with n hn
    simpa only [Real.dist_eq] using hN n hn
  obtain ⟨N, hN⟩ := exists_threshold_forall_finite hpair
  refine ⟨N, fun n hn i j ↦ ?_⟩
  exact hN n hn (i, j)

/-- Tail-shift package for a convergent finite matrix sequence.  The explicit
shift `n ↦ n + N` is strictly increasing and cofinal, preserves every
entrywise limit, and lies entirely inside the simultaneous close tail. -/
theorem exists_matrix_entrywise_tail_shift
    {q : ℕ} (M : ℕ → Matrix (Fin q) (Fin q) ℝ)
    (L : Matrix (Fin q) (Fin q) ℝ)
    (hM : ∀ i j, Tendsto (fun n ↦ M n i j) atTop (nhds (L i j)))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ,
      StrictMono (fun n : ℕ ↦ n + N) ∧
      (∀ i j, Tendsto (fun n ↦ M (n + N) i j) atTop (nhds (L i j))) ∧
      (∀ n i j, |M (n + N) i j - L i j| < ε) := by
  obtain ⟨N, hN⟩ := exists_threshold_matrix_entrywise_abs_sub_lt M L hM hε
  refine ⟨N, strictMono_id.add_const N, ?_, ?_⟩
  · intro i j
    exact (hM i j).comp (strictMono_id.add_const N).tendsto_atTop
  · intro n i j
    exact hN (n + N) (by omega) i j

/-! ## Uniform matrix errors with varying dimensions -/

/-- A vanishing uniform entrywise error gives `L¹` convergence of equal-cell
matrix graphons.  The matrix size may vary with the sequence index. -/
theorem matrixGraphon_tendsto_graphonL1Dist_of_uniform_error
    {q : ℕ → ℕ}
    (M N : (n : ℕ) → Matrix (Fin (q n)) (Fin (q n)) ℝ)
    (hM_symm : ∀ n, (M n).IsSymm) (hN_symm : ∀ n, (N n).IsSymm)
    (hM_zero : ∀ n i j, 0 ≤ M n i j)
    (hM_one : ∀ n i j, M n i j ≤ 1)
    (hN_zero : ∀ n i j, 0 ≤ N n i j)
    (hN_one : ∀ n i j, N n i j ≤ 1)
    (error : ℕ → ℝ) (herror_nonneg : ∀ n, 0 ≤ error n)
    (herror : Tendsto error atTop (nhds 0))
    (hentry : ∀ n i j, |M n i j - N n i j| ≤ error n) :
    Tendsto
      (fun n ↦ graphonL1Dist
        (matrixGraphon (M n) (hM_symm n) (hM_zero n) (hM_one n))
        (matrixGraphon (N n) (hN_symm n) (hN_zero n) (hN_one n)))
      atTop (nhds 0) := by
  apply squeeze_zero
  · intro n
    exact graphonL1Dist_nonneg _ _
  · intro n
    exact graphonL1Dist_matrixGraphon_le
      (M n) (N n) (hM_symm n) (hN_symm n)
      (hM_zero n) (hM_one n) (hN_zero n) (hN_one n)
      (herror_nonneg n) (hentry n)
  · exact herror

/-- The diagonal form used in the Type tower: a uniform entrywise error at
stage `n` bounded by `1 / (n + 1)` gives `L¹` convergence, even though the
matrix dimension varies with `n`. -/
theorem matrixGraphon_tendsto_graphonL1Dist_of_entrywise_one_div_add
    {q : ℕ → ℕ}
    (M N : (n : ℕ) → Matrix (Fin (q n)) (Fin (q n)) ℝ)
    (hM_symm : ∀ n, (M n).IsSymm) (hN_symm : ∀ n, (N n).IsSymm)
    (hM_zero : ∀ n i j, 0 ≤ M n i j)
    (hM_one : ∀ n i j, M n i j ≤ 1)
    (hN_zero : ∀ n i j, 0 ≤ N n i j)
    (hN_one : ∀ n i j, N n i j ≤ 1)
    (hentry : ∀ n i j,
      |M n i j - N n i j| ≤ 1 / (((n + 1 : ℕ) : ℝ))) :
    Tendsto
      (fun n ↦ graphonL1Dist
        (matrixGraphon (M n) (hM_symm n) (hM_zero n) (hM_one n))
        (matrixGraphon (N n) (hN_symm n) (hN_zero n) (hN_one n)))
      atTop (nhds 0) := by
  apply matrixGraphon_tendsto_graphonL1Dist_of_uniform_error
    M N hM_symm hN_symm hM_zero hM_one hN_zero hN_one
    (fun n ↦ 1 / (((n + 1 : ℕ) : ℝ)))
  · intro n
    positivity
  · simpa only [Nat.cast_add, Nat.cast_one] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  · exact hentry

end InducedStars.Graphon
