import InducedStars.Structure.Subcritical.ProfileLeftoverBound
import InducedStars.Structure.Subcritical.LocalEntropy

/-!
# One-budget absorption of weighted profile leftovers

Paper: the sixth inequality in `lemma:profile-bound-K1k`. The full
nonretained graph remains fixed throughout the fixed-remainder decomposition. Natural exponential
units are used, and the existing public error constant is unchanged.
-/

noncomputable section
open Finset
open scoped BigOperators Classical
namespace InducedStars

variable {k : ℕ}

/-- Bernoulli's finite power inequality gives the elementary lower bound
`p_k ≥ 1/k`; no asymptotics of the scalar root are used. -/
theorem one_div_le_pK (hk : 3 ≤ k) : 1 / (k : ℝ) ≤ pK k := by
  have hp := pK_mem_Icc k
  have h := one_add_mul_le_pow (a := -pK k) (by linarith [hp.2] : -2 ≤ -pK k) (k - 1)
  have hpow : (1 + -pK k) ^ (k - 1) = pK k := by
    simpa only [sub_eq_add_neg] using (pK_equation k).symm
  rw [hpow] at h
  have hkcast : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]
    norm_num
  rw [hkcast] at h
  apply (div_le_iff₀ (by exact_mod_cast (show 0 < k by omega) : (0 : ℝ) < k)).mpr
  nlinarith

/-- The scalar fixed point is at most one half for every permitted `k`. -/
theorem pK_le_half (hk : 3 ≤ k) : pK k ≤ 1 / 2 := by
  have hp := pK_mem_Icc k
  have hpow : (1 - pK k) ^ (k - 2) ≤ 1 :=
    pow_le_one₀ (by linarith [hp.2]) (by linarith [hp.1])
  have heq := pK_equation k
  rw [show k - 1 = (k - 2) + 1 by omega, pow_succ] at heq
  have h := mul_le_mul_of_nonneg_right hpow (by linarith [hp.2] : 0 ≤ 1 - pK k)
  nlinarith

/-- A linear bound for the natural-log odds, sufficient for the unchanged
polynomial error coefficient. -/
theorem subcriticalLogOddsNat_le_sub_two (hk : 3 ≤ k) :
    subcriticalLogOddsNat k ≤ ((k - 2 : ℕ) : ℝ) := by
  have hp := pK_le_half hk
  have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 1 / 2)
    (show (1 / 2 : ℝ) ≤ 1 - pK k by linarith)
  have hlog2 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    exact h
  have hA : subcriticalLocalA_Nat k ≤ 1 := by
    simp only [subcriticalLocalA_Nat, one_div, Real.log_inv] at hlog ⊢
    linarith
  rw [subcriticalLogOddsNat_eq_delta_mul_A hk]
  simpa using mul_le_mul_of_nonneg_left hA (Nat.cast_nonneg (k - 2))

/-- The adjacent-ratio coefficient is at most `10k`. -/
theorem subcriticalActiveLevelConstant_le_ten_mul (hk : 3 ≤ k) :
    subcriticalActiveLevelConstant k ≤ 10 * (k : ℝ) := by
  have hp := pK_pos (show 2 ≤ k by omega)
  have hq : 0 < 1 - pK k := sub_pos.mpr (pK_lt_one (by omega))
  have hlower := (div_le_iff₀ (by exact_mod_cast (show 0 < k by omega) : (0 : ℝ) < k)).mp
    (one_div_le_pK hk)
  have hhalf := pK_le_half hk
  have hleft : 6 / pK k ≤ 6 * (k : ℝ) := (div_le_iff₀ hp).mpr (by nlinarith)
  have hright : 6 / (1 - pK k) ≤ 12 := (div_le_iff₀ hq).mpr (by linarith)
  have hkR : (3 : ℝ) ≤ k := by exact_mod_cast hk
  unfold subcriticalActiveLevelConstant DenseGraph.binomialLogOddsConstant
  apply max_le <;> linarith

/-- The same two density-band reserves already required by the level
comparison bound its entire `C_lev δ` coefficient by two. -/
theorem subcriticalActiveLevelConstant_mul_delta_le_two (hk : 3 ≤ k)
    {delta : ℝ} (hd : 0 ≤ delta)
    (hdp : 6 * delta ≤ pK k) (hdq : 6 * delta ≤ 1 - pK k) :
    subcriticalActiveLevelConstant k * delta ≤ 2 := by
  have hp := pK_pos (show 2 ≤ k by omega)
  have hq : 0 < 1 - pK k := sub_pos.mpr (pK_lt_one (by omega))
  have hleft : 6 / pK k * delta ≤ 1 := by
    rw [div_mul_eq_mul_div]
    exact (div_le_iff₀ hp).mpr (by linarith)
  have hright : 6 / (1 - pK k) * delta ≤ 1 := by
    rw [div_mul_eq_mul_div]
    exact (div_le_iff₀ hq).mpr (by linarith)
  have hp1 := (pK_mem_Icc k).2
  unfold subcriticalActiveLevelConstant
  rw [max_mul_of_nonneg _ _ hd]
  apply max_le
  · linarith
  · unfold DenseGraph.binomialLogOddsConstant
    rw [add_mul]
    linarith

/-- A leftover signed edge costs at most `k` in the weighted count. -/
theorem subcriticalLeftoverWeightCoefficient_le (hk : 3 ≤ k)
    {delta : ℝ} (hd : 0 ≤ delta)
    (hdp : 6 * delta ≤ pK k) (hdq : 6 * delta ≤ 1 - pK k) :
    |subcriticalLogOddsNat k| + subcriticalActiveLevelConstant k * delta ≤ (k : ℝ) := by
  rw [abs_of_pos (subcriticalLogOddsNat_pos hk)]
  have hL := subcriticalLogOddsNat_le_sub_two hk
  have hC := subcriticalActiveLevelConstant_mul_delta_le_two hk hd hdp hdq
  have hkcast : ((k - 2 : ℕ) : ℝ) = (k : ℝ) - 2 := by
    rw [Nat.cast_sub (by omega)]
    norm_num
  linarith

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The raw row-code exponent, before multiplication by the final error
coefficient. It keeps all four separate counting costs visible. -/
def subcriticalLeftoverCodeExponent {D : SubcriticalDivision k V}
    {eta theta : ℝ} {R₀ : ℕ} (alpha epsilon : ℝ)
    (p : SubcriticalProfile D eta R₀ theta) : ℝ :=
  (p.roots.card : ℝ) *
    (binaryEntropy (5 * alpha) * Fintype.card V +
      ((k - 1 : ℕ) : ℝ) * subcriticalSparseSideConstant k * theta * Fintype.card V +
      2 * ((k - 1 : ℕ) : ℝ) * log2 (Fintype.card V + 1) +
      subcriticalProfileRootFraction alpha theta epsilon * Fintype.card V)

/-- The unabsorbed root-row bound for the number of leftover edges. -/
def subcriticalLeftoverRawEdgeBudget {D : SubcriticalDivision k V}
    {eta theta : ℝ} {R₀ : ℕ} (alpha : ℝ)
    (p : SubcriticalProfile D eta R₀ theta) : ℝ :=
  (p.roots.card : ℝ) * (5 * alpha * Fintype.card V +
    subcriticalSparseSideConstant k * theta * Fintype.card V + p.roots.card)

private theorem weightedErrorConstant_bounds (k R₀ : ℕ) :
    (k : ℝ) + 1 ≤ subcriticalProfileErrorConstant k R₀ ∧
      (((k - 1 : ℕ) : ℝ) + k) * subcriticalSparseSideConstant k ≤
        subcriticalProfileErrorConstant k R₀ ∧
      2 * ((k - 1 : ℕ) : ℝ) ≤ subcriticalProfileErrorConstant k R₀ ∧
      10 * (k : ℝ) ≤ subcriticalProfileErrorConstant k R₀ := by
  let X : ℝ := k + 1
  have hX : 1 ≤ X := by dsimp [X]; linarith [show (0 : ℝ) ≤ k by positivity]
  have hkX : (k : ℝ) ≤ X := by dsimp [X]; linarith
  have hrX : ((k - 1 : ℕ) : ℝ) ≤ X :=
    (by exact_mod_cast Nat.sub_le k 1 : ((k - 1 : ℕ) : ℝ) ≤ k).trans hkX
  have h14 : X ≤ X ^ 4 := by simpa using pow_le_pow_right₀ hX (by omega : 1 ≤ 4)
  have h34 : X ^ 3 ≤ X ^ 4 := pow_le_pow_right₀ hX (by omega)
  have hC : 1000 * X ^ 4 ≤ subcriticalProfileErrorConstant k R₀ := by
    unfold subcriticalProfileErrorConstant
    have hR : (1 : ℝ) ≤ (R₀ + 1 : ℕ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le R₀)
    have hmul := mul_le_mul_of_nonneg_left hR (by positivity : 0 ≤ 1000 * X ^ 4)
    simpa only [mul_one, X, Nat.cast_add, Nat.cast_one] using hmul
  have hprod : (((k - 1 : ℕ) : ℝ) + k) * subcriticalSparseSideConstant k ≤ 200 * X ^ 3 := by
    unfold subcriticalSparseSideConstant
    calc
      _ ≤ (X + X) * (100 * X ^ 2) := by gcongr
      _ = _ := by ring
  have hkone : (k : ℝ) + 1 = X := rfl
  refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith

/-- Simultaneously absorb raw counting, the weighted leftover edges, and
the root delta error into one copy of the unchanged public budget. -/
theorem subcriticalWeightedLeftoverExponent_le_errorBudget
    {D : SubcriticalDivision k V} {eta theta alpha delta epsilon : ℝ} {R₀ : ℕ}
    (p : SubcriticalProfile D eta R₀ theta) (hk : 3 ≤ k)
    (ha : 0 ≤ alpha) (haHalf : 5 * alpha ≤ 1 / 2)
    (ht : 0 ≤ theta) (hd : 0 ≤ delta) (he : 0 ≤ epsilon)
    (hdp : 6 * delta ≤ pK k) (hdq : 6 * delta ≤ 1 - pK k)
    (hB : (p.roots.card : ℝ) ≤
      subcriticalProfileRootFraction alpha theta epsilon * Fintype.card V) :
    subcriticalLeftoverCodeExponent alpha epsilon p +
      (|subcriticalLogOddsNat k| + subcriticalActiveLevelConstant k * delta) *
        subcriticalLeftoverRawEdgeBudget alpha p +
      subcriticalActiveLevelConstant k * delta * p.roots.card * Fintype.card V ≤
        subcriticalProfileErrorBudget alpha delta epsilon p := by
  let w := |subcriticalLogOddsNat k| + subcriticalActiveLevelConstant k * delta
  have hw0 : 0 ≤ w := add_nonneg (abs_nonneg _) (mul_nonneg (subcriticalActiveLevelConstant_pos k).le hd)
  have hw : w ≤ (k : ℝ) := subcriticalLeftoverWeightCoefficient_le hk hd hdp hdq
  have hEnt := binaryEntropy_nonneg (by positivity : 0 ≤ 5 * alpha) (by linarith : 5 * alpha ≤ 1)
  have hEntLower := binaryEntropy_ge_self_of_le_half (by positivity : 0 ≤ 5 * alpha) haHalf
  have hRho : 0 ≤ subcriticalProfileRootFraction alpha theta epsilon := by
    unfold subcriticalProfileRootFraction
    positivity
  have hLog : 0 ≤ log2 (Fintype.card V + 1) := log2_nonneg (by norm_num)
  have hCs := (subcriticalSparseSideConstant_pos hk).le
  have hrow : 5 * alpha * Fintype.card V +
      subcriticalSparseSideConstant k * theta * Fintype.card V + p.roots.card ≤
        binaryEntropy (5 * alpha) * Fintype.card V +
          subcriticalSparseSideConstant k * theta * Fintype.card V +
          subcriticalProfileRootFraction alpha theta epsilon * Fintype.card V := by
    have h := mul_le_mul_of_nonneg_right hEntLower (Nat.cast_nonneg (Fintype.card V))
    linarith
  have hweighted := mul_le_mul hw hrow (by positivity : 0 ≤
    5 * alpha * Fintype.card V + subcriticalSparseSideConstant k * theta * Fintype.card V +
      p.roots.card) (Nat.cast_nonneg k)
  have hlevel := mul_le_mul_of_nonneg_right (subcriticalActiveLevelConstant_le_ten_mul hk)
    (mul_nonneg hd (Nat.cast_nonneg (Fintype.card V)))
  obtain ⟨hCEnt, hCTheta, hCLog, hCDelta⟩ := weightedErrorConstant_bounds k R₀
  have h1 := mul_le_mul_of_nonneg_right hCEnt (mul_nonneg hEnt (Nat.cast_nonneg (Fintype.card V)))
  have h2 := mul_le_mul_of_nonneg_right hCTheta (mul_nonneg ht (Nat.cast_nonneg (Fintype.card V)))
  have h3 := mul_le_mul_of_nonneg_right hCLog hLog
  have h4 := mul_le_mul_of_nonneg_right hCEnt (mul_nonneg hRho (Nat.cast_nonneg (Fintype.card V)))
  have h5 := mul_le_mul_of_nonneg_right hCDelta (mul_nonneg hd (Nat.cast_nonneg (Fintype.card V)))
  have htotal :
      binaryEntropy (5 * alpha) * Fintype.card V +
        ((k - 1 : ℕ) : ℝ) * subcriticalSparseSideConstant k * theta * Fintype.card V +
        2 * ((k - 1 : ℕ) : ℝ) * log2 (Fintype.card V + 1) +
        subcriticalProfileRootFraction alpha theta epsilon * Fintype.card V +
        w * (5 * alpha * Fintype.card V +
          subcriticalSparseSideConstant k * theta * Fintype.card V + p.roots.card) +
        subcriticalActiveLevelConstant k * delta * Fintype.card V ≤
      subcriticalProfileErrorConstant k R₀ *
        (binaryEntropy (5 * alpha) * Fintype.card V + theta * Fintype.card V +
          delta * Fintype.card V +
          subcriticalProfileRootFraction alpha theta epsilon * Fintype.card V +
          log2 (Fintype.card V + 1)) := by nlinarith
  have hmul := mul_le_mul_of_nonneg_left htotal (Nat.cast_nonneg p.roots.card)
  simpa only [subcriticalLeftoverCodeExponent, subcriticalLeftoverRawEdgeBudget,
    subcriticalProfileErrorBudget, w, mul_add, add_mul, mul_assoc, mul_left_comm] using hmul

/-- Convert the raw fixed-remainder row product to its unabsorbed code
exponent. Keeping this sharper endpoint leaves room for the signed weights. -/
theorem subcriticalLeftoverRawCount_le_exp_codeExponent
    {D : SubcriticalDivision k V} {eta theta alpha epsilon : ℝ} {R₀ : ℕ}
    (p : SubcriticalProfile D eta R₀ theta) (hk : 3 ≤ k) (hn : 2 ≤ Fintype.card V)
    (ha : 0 ≤ alpha) (haHalf : 5 * alpha ≤ 1 / 2) (ht : 0 ≤ theta)
    (hB : (p.roots.card : ℝ) ≤
      subcriticalProfileRootFraction alpha theta epsilon * Fintype.card V)
    (aVis : ℝ) (haVis : 0 ≤ aVis)
    (haVisBound : aVis ≤ Real.exp (Real.log 2 * binaryEntropy (5 * alpha) * Fintype.card V)) :
    (aVis * ((Fintype.card V + 1 : ℝ) ^ (k - 1) *
        (2 : ℝ) ^ ((k - 1) * (⌊subcriticalSparseSideConstant k * theta * Fintype.card V⌋₊ + 1))) *
      (2 : ℝ) ^ p.roots.card) ^ p.roots.card ≤
      Real.exp (subcriticalLeftoverCodeExponent alpha epsilon p) := by
  let N := Fintype.card V
  let B := p.roots.card
  let r := k - 1
  let d := ⌊subcriticalSparseSideConstant k * theta * N⌋₊
  have hEnt : 0 ≤ binaryEntropy (5 * alpha) :=
    binaryEntropy_nonneg (by positivity) (by linarith)
  have hCk := (subcriticalSparseSideConstant_pos hk).le
  have hdBound : (d : ℝ) ≤ subcriticalSparseSideConstant k * theta * N :=
    Nat.floor_le (by positivity)
  have hN2 : (2 : ℝ) ≤ N + 1 := by
    exact_mod_cast (show 2 ≤ N + 1 by dsimp [N]; omega)
  have hLog : 1 ≤ log2 (N + 1) := by
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hN2
    exact (le_div_iff₀ realLogTwo_pos).mpr (by simpa using h)
  have hl2 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    exact h
  have hLogNat : Real.log (N + 1) ≤ log2 (N + 1) := by
    have hid : Real.log (N + 1) = log2 (N + 1) * Real.log 2 := by
      unfold log2
      field_simp
    rw [hid]
    exact mul_le_of_le_one_right (by linarith) hl2
  have hrow : Real.log 2 * binaryEntropy (5 * alpha) * N +
      (r : ℝ) * Real.log (N + 1) + ((r * (d + 1) : ℕ) : ℝ) * Real.log 2 +
      (B : ℝ) * Real.log 2 ≤
      binaryEntropy (5 * alpha) * N +
        (r : ℝ) * subcriticalSparseSideConstant k * theta * N +
        2 * (r : ℝ) * log2 (N + 1) +
        subcriticalProfileRootFraction alpha theta epsilon * N := by
    have h1 := mul_le_mul_of_nonneg_right hl2 (mul_nonneg hEnt (Nat.cast_nonneg N))
    have h2 := mul_le_mul_of_nonneg_left hLogNat (Nat.cast_nonneg r)
    have h3 := mul_le_mul_of_nonneg_left hl2 (Nat.cast_nonneg (r * (d + 1)))
    have h4 := mul_le_mul_of_nonneg_left hl2 (Nat.cast_nonneg B)
    have h5 := mul_le_mul_of_nonneg_left hdBound (Nat.cast_nonneg r)
    have h6 := mul_le_mul_of_nonneg_left hLog (Nat.cast_nonneg r)
    push_cast at h3 ⊢
    dsimp [N, B] at *
    nlinarith
  have hpowN : (N + 1 : ℝ) ^ r = Real.exp ((r : ℝ) * Real.log (N + 1)) := by
    rw [Real.exp_nat_mul, Real.exp_log (by positivity)]
  have hpow2 (s : ℕ) : (2 : ℝ) ^ s = Real.exp ((s : ℝ) * Real.log 2) := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
  calc
    _ ≤ (Real.exp (Real.log 2 * binaryEntropy (5 * alpha) * N) *
        ((N + 1 : ℝ) ^ r * (2 : ℝ) ^ (r * (d + 1))) * (2 : ℝ) ^ B) ^ B := by
      change (aVis * _ * _) ^ B ≤ _
      gcongr
    _ = Real.exp ((B : ℝ) *
        (Real.log 2 * binaryEntropy (5 * alpha) * N +
          (r : ℝ) * Real.log (N + 1) + ((r * (d + 1) : ℕ) : ℝ) * Real.log 2 +
          (B : ℝ) * Real.log 2)) := by
      rw [hpowN, hpow2, hpow2]
      simp only [← Real.exp_add, ← Real.exp_nat_mul]
      congr 1
      ring
    _ ≤ Real.exp (subcriticalLeftoverCodeExponent alpha epsilon p) := by
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_left hrow (Nat.cast_nonneg B)

/-- The rooted graph has at most one complete vertex row per profile root. -/
theorem subcriticalRootedDefectGraph_card_le_roots_mul_order
    {D : SubcriticalDivision k V} {eta theta alpha : ℝ} {R₀ : ℕ}
    {p : SubcriticalProfile D eta R₀ theta} {G : SimpleGraph V}
    (h : RealizesSubcriticalProfile G alpha p) :
    (finiteGraphEdges (subcriticalRootedDefectGraph G D eta R₀ theta alpha)).card ≤
      p.roots.card * Fintype.card V := by
  rw [subcriticalRootedDefectGraph_card_eq_sum_neighbors, ← h.roots_eq]
  calc
    _ ≤ ∑ _v ∈ p.roots, Fintype.card V :=
      Finset.sum_le_sum (fun v _ ↦ Finset.card_le_univ _)
    _ = _ := by simp

/-- The weighted fixed-`H` leftover sum and the root delta error use only
one final `exp Err`. The profile's public error constant is unchanged.
The full remainder `H` stays fixed, and exponential weights use natural logarithms. -/
theorem subcriticalProfileLeftover_weightedSum_le_exp_errorBudget
    {D : SubcriticalDivision k V} {eta theta alpha delta epsilon : ℝ} {R₀ : ℕ}
    {p : SubcriticalProfile D eta R₀ theta}
    (F : Finset (SimpleGraph V)) (H : SubcriticalRemainderGraph D eta R₀)
    (TB R : SimpleGraph V) (hk : 3 ≤ k) (hn : 2 ≤ Fintype.card V)
    (halpha : 0 ≤ alpha) (halpha_half : 5 * alpha ≤ 1 / 2)
    (htheta : 0 ≤ theta) (hdelta : 0 ≤ delta) (hepsilon : 0 ≤ epsilon)
    (hdp : 6 * delta ≤ pK k) (hdq : 6 * delta ≤ 1 - pK k)
    (hret : D.retainedPartIndices eta R₀ ⊆ D.visiblePartIndices theta)
    (hpart : ∀ a ∈ D.visiblePartIndices theta,
      theta * Fintype.card V / 2 ≤ ((D.part a).card : ℝ))
    (hroot : (p.roots.card : ℝ) ≤
      subcriticalProfileRootFraction alpha theta epsilon * Fintype.card V)
    (hrho : subcriticalProfileRootFraction alpha theta epsilon ≤ alpha * theta / 2)
    (hfree : ∀ G ∈ subcriticalProfileClassGraphFinset F alpha p,
      ¬ Regularity.InducedEmbeds (inducedStar k) G)
    (hsmall : ∀ G ∈ subcriticalProfileClassGraphFinset F alpha p, ∀ v,
      (degreeInFinset G v (D.nonretainedSmallVertices eta R₀ theta) : ℝ) ≤
        subcriticalSparseSideConstant k * theta * Fintype.card V) :
    (∑ L ∈ subcriticalLeftoverDefectPatternFinsetWithRemainder F alpha p H TB R,
      Real.exp (-subcriticalLogOddsNat k * (subcriticalSignedDefectSize D eta R₀ L : ℝ) +
        subcriticalActiveLevelConstant k * delta * |(subcriticalSignedDefectSize D eta R₀ L : ℝ)| +
        subcriticalActiveLevelConstant k * delta * |(subcriticalSignedDefectSize D eta R₀ TB : ℝ)|)) ≤
      Real.exp (subcriticalProfileErrorBudget alpha delta epsilon p) := by
  let FL := subcriticalLeftoverDefectPatternFinsetWithRemainder F alpha p H TB R
  by_cases hEmpty : FL.Nonempty
  · obtain ⟨L₀, hL₀⟩ := hEmpty
    obtain ⟨G₀, hG₀, hH, hTB, _, _⟩ :=
      (mem_subcriticalLeftoverDefectPatternFinsetWithRemainder F alpha p H TB R L₀).mp hL₀
    have hp₀ := (mem_subcriticalProfileClassGraphFinset.mp hG₀).2
    let d := ⌊subcriticalSparseSideConstant k * theta * Fintype.card V⌋₊
    have hdeg : ∀ v ∈ D.nonretainedSmallVertices eta R₀ theta,
        degreeInFinset (subcriticalRemainderGraphSpanningCoe H) v
          (D.nonretainedSmallVertices eta R₀ theta) ≤ d := by
      intro v hv
      rw [subcriticalRemainderGraph_small_degree_eq hH hv]
      exact Nat.le_floor (hsmall G₀ hG₀ v)
    have hB : ∀ a ∈ D.visiblePartIndices theta,
        (p.roots.card : ℝ) ≤ alpha * (D.part a).card := by
      intro a ha
      exact subcriticalProfile_roots_card_le_alpha_target halpha hroot hrho (hpart a ha)
    have hc := subcriticalProfileLeftover_card_le_rowProduct F H TB R d
      halpha (by linarith) hret hB hfree hdeg
    have hEnt := subcritical_smallSubsetCard_le_exp_entropy
      (Finset.univ : Finset V) (by positivity : 0 ≤ 5 * alpha) halpha_half
    simp only [Finset.card_univ, mul_assoc] at hEnt
    have hScalar := subcriticalLeftoverRawCount_le_exp_codeExponent p hk hn
      halpha halpha_half htheta hroot
      ((finsetSubsetsAtMost (Finset.univ : Finset V) ⌊5 * alpha * Fintype.card V⌋₊).card : ℝ)
      (Nat.cast_nonneg _) (by simpa only [mul_assoc] using hEnt)
    have hcode : (FL.card : ℝ) ≤ Real.exp (subcriticalLeftoverCodeExponent alpha epsilon p) := by
      apply le_trans (by exact_mod_cast hc)
        (show ((_ : ℝ) * ((_ : ℝ) ^ (k - 1) * (2 : ℝ) ^ ((k - 1) * (d + 1))) *
          (2 : ℝ) ^ p.roots.card) ^ p.roots.card ≤ _ from hScalar)
    have hTBcard : (finiteGraphEdges TB).card ≤ p.roots.card * Fintype.card V := by
      rw [← hTB]
      exact subcriticalRootedDefectGraph_card_le_roots_mul_order hp₀
    have hTBabs : |(subcriticalSignedDefectSize D eta R₀ TB : ℝ)| ≤
        (p.roots.card : ℝ) * Fintype.card V := by
      have h := abs_subcriticalSignedDefectSize_le D eta R₀ TB
      have hcardR : ((finiteGraphEdges TB).card : ℝ) ≤ p.roots.card * Fintype.card V := by
        exact_mod_cast hTBcard
      exact (by exact_mod_cast h : |(subcriticalSignedDefectSize D eta R₀ TB : ℝ)| ≤
        (finiteGraphEdges TB).card).trans hcardR
    let w := |subcriticalLogOddsNat k| + subcriticalActiveLevelConstant k * delta
    let E := w * subcriticalLeftoverRawEdgeBudget alpha p +
      subcriticalActiveLevelConstant k * delta * p.roots.card * Fintype.card V
    have hC0 : 0 ≤ subcriticalActiveLevelConstant k * delta :=
      mul_nonneg (subcriticalActiveLevelConstant_pos k).le hdelta
    have hw0 : 0 ≤ w := add_nonneg (abs_nonneg _) hC0
    have hpoint : ∀ L ∈ FL,
        Real.exp (-subcriticalLogOddsNat k * (subcriticalSignedDefectSize D eta R₀ L : ℝ) +
          subcriticalActiveLevelConstant k * delta * |(subcriticalSignedDefectSize D eta R₀ L : ℝ)| +
          subcriticalActiveLevelConstant k * delta * |(subcriticalSignedDefectSize D eta R₀ TB : ℝ)|) ≤
            Real.exp E := by
      intro L hL
      obtain ⟨G, hG, _, _, _, hGL⟩ :=
        (mem_subcriticalLeftoverDefectPatternFinsetWithRemainder F alpha p H TB R L).mp hL
      have hpG := (mem_subcriticalProfileClassGraphFinset.mp hG).2
      have hedge := subcriticalActualLeftover_edgeCount_le hpG hret halpha (by linarith)
        hB (hsmall G hG)
      have heL : ((finiteGraphEdges L).card : ℝ) ≤ subcriticalLeftoverRawEdgeBudget alpha p := by
        simpa only [hGL, subcriticalLeftoverRawEdgeBudget] using hedge
      have hsL : |(subcriticalSignedDefectSize D eta R₀ L : ℝ)| ≤
          subcriticalLeftoverRawEdgeBudget alpha p :=
        (by exact_mod_cast abs_subcriticalSignedDefectSize_le D eta R₀ L :
          |(subcriticalSignedDefectSize D eta R₀ L : ℝ)| ≤ (finiteGraphEdges L).card).trans heL
      have hlin := neg_le_abs
        (subcriticalLogOddsNat k * (subcriticalSignedDefectSize D eta R₀ L : ℝ))
      rw [abs_mul] at hlin
      have hweight := mul_le_mul_of_nonneg_left hsL hw0
      have hrootweight := mul_le_mul_of_nonneg_left hTBabs hC0
      apply Real.exp_le_exp.mpr
      dsimp [w] at hweight
      dsimp [E, w]
      nlinarith
    calc
      _ ≤ (FL.card : ℝ) * Real.exp E := by
        simpa only [Finset.sum_const, nsmul_eq_mul] using Finset.sum_le_sum hpoint
      _ ≤ Real.exp (subcriticalLeftoverCodeExponent alpha epsilon p) * Real.exp E :=
        mul_le_mul_of_nonneg_right hcode (Real.exp_pos E).le
      _ = Real.exp (subcriticalLeftoverCodeExponent alpha epsilon p + E) := (Real.exp_add _ _).symm
      _ ≤ Real.exp (subcriticalProfileErrorBudget alpha delta epsilon p) := by
        apply Real.exp_le_exp.mpr
        simpa only [E, w, ← add_assoc] using subcriticalWeightedLeftoverExponent_le_errorBudget
          p hk halpha halpha_half htheta hdelta hepsilon hdp hdq hroot
  · have hzero : FL = ∅ := Finset.not_nonempty_iff_eq_empty.mp hEmpty
    change (∑ L ∈ FL, _) ≤ _
    rw [hzero, Finset.sum_empty]
    exact (Real.exp_pos _).le

end InducedStars
